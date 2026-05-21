//! Translate a PolyML bytecode sequence into Cranelift IR.
//!
//! Scope (intentionally tiny for now):
//! - The function takes no arguments.
//! - The "SML value stack" is tracked at *compile time* as a Rust
//!   `Vec<Value>` of Cranelift IR values. Each `INSTR_CONST_*`
//!   emits an `iconst` and pushes; `INSTR_RETURN_1` pops the top
//!   and emits `return`.
//! - This is the "stack in registers" model — fast because no
//!   memory traffic per push/pop, but only viable for functions
//!   whose stack height is statically tracked. We'll spill to a
//!   real memory-backed stack once we hit branches or
//!   calls.
//!
//! Supported opcodes (initial set):
//! - `INSTR_CONST_0..INSTR_CONST_4`, `INSTR_CONST_10`
//! - `INSTR_CONST_INT_B` (1-byte signed immediate)
//! - `INSTR_RETURN_1`

use crate::{Jit, JitError};
use cranelift::prelude::*;
use cranelift::codegen::ir::BlockArg;
use cranelift_module::{Linkage, Module};

// Opcode constants — kept in sync with
// `polyml_runtime::interpreter::opcodes`. We re-declare here so
// this module doesn't pull in the runtime crate's private modules.
const INSTR_CONST_0: u8 = 0x3b;
const INSTR_CONST_1: u8 = 0x3c;
const INSTR_CONST_2: u8 = 0x3d;
const INSTR_CONST_3: u8 = 0x3e;
const INSTR_CONST_4: u8 = 0x3f;
const INSTR_CONST_10: u8 = 0x40;
const INSTR_CONST_INT_B: u8 = 0x28;
const INSTR_RETURN_1: u8 = 0x42;
const INSTR_FIXED_ADD: u8 = 0xaa;
const INSTR_FIXED_SUB: u8 = 0xab;
const INSTR_FIXED_MULT: u8 = 0xac;
const INSTR_JUMP8: u8 = 0x02;
const INSTR_JUMP8_FALSE: u8 = 0x03;
const INSTR_JUMP8_TRUE: u8 = 0x46;

/// Errors specific to bytecode translation.
#[derive(Debug, thiserror::Error)]
pub enum TranslateError {
    #[error("truncated bytecode at offset {0}")]
    Truncated(usize),
    #[error("unsupported opcode 0x{op:02x} at offset {at}")]
    Unsupported { op: u8, at: usize },
    #[error("stack underflow at offset {0} (no value to pop)")]
    Underflow(usize),
    #[error("control left function without RETURN_1")]
    FellOffEnd,
    #[error(transparent)]
    Jit(#[from] JitError),
}

/// Compile a `bytecode` sequence into a native function that takes
/// no arguments and returns an `i64` (the raw PolyWord). Uses the
/// shared `jit` environment so the compiled bytes outlive the
/// returned pointer for as long as the `Jit` does.
pub fn compile(jit: &mut Jit, bytecode: &[u8]) -> Result<extern "C" fn() -> i64, TranslateError> {
    let mut ctx = jit.module.make_context();
    let mut func_builder_ctx = FunctionBuilderContext::new();
    let int = types::I64;
    ctx.func.signature.returns.push(AbiParam::new(int));

    // Pass 1: scan to find branch target PCs and the stack depth
    // expected at each target. Each unique target gets its own
    // Cranelift block; the block's parameters carry the stack
    // values across the branch.
    let targets = scan_branch_targets(bytecode)?;

    {
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_builder_ctx);
        let entry = builder.create_block();

        // Allocate one block per unique branch target, with as many
        // block-params as the stack depth at that PC.
        let mut block_at: std::collections::HashMap<usize, Block> =
            std::collections::HashMap::new();
        for (&target_pc, &depth) in &targets {
            let blk = builder.create_block();
            for _ in 0..depth {
                builder.append_block_param(blk, int);
            }
            block_at.insert(target_pc, blk);
        }

        builder.switch_to_block(entry);

        // Compile-time stack of in-IR values; the position in this
        // Vec corresponds to the SML stack position. `push` is just
        // `Vec::push`; `pop` is `Vec::pop`.
        let mut stack: Vec<Value> = Vec::new();
        let mut pc = 0usize;
        let mut returned = false;

        while pc < bytecode.len() {
            // If we just entered a branch-target PC, switch to its
            // block and re-seed the stack from the block params.
            if let Some(&target_blk) = block_at.get(&pc) {
                if !returned {
                    let args: Vec<BlockArg> =
                        stack.iter().copied().map(BlockArg::from).collect();
                    builder.ins().jump(target_blk, &args);
                }
                builder.switch_to_block(target_blk);
                stack.clear();
                for i in 0..builder.block_params(target_blk).len() {
                    stack.push(builder.block_params(target_blk)[i]);
                }
                returned = false;
            }
            // After an unconditional terminator (RETURN/JUMP/branch),
            // we keep walking the bytecode but the bytes are
            // unreachable unless we hit a future branch target. Skip
            // emitting IR for those bytes — but still respect opcode
            // boundaries so we don't read an immediate byte as an
            // opcode.
            if returned {
                let len = opcode_total_len(bytecode, pc)?;
                pc += len;
                continue;
            }

            let op = bytecode[pc];
            pc += 1;
            match op {
                INSTR_CONST_0 | INSTR_CONST_1 | INSTR_CONST_2 | INSTR_CONST_3 | INSTR_CONST_4 => {
                    let n = i64::from(op - INSTR_CONST_0);
                    stack.push(builder.ins().iconst(int, tag(n)));
                }
                INSTR_CONST_10 => stack.push(builder.ins().iconst(int, tag(10))),
                INSTR_CONST_INT_B => {
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let imm = bytecode[pc] as i8 as i64;
                    pc += 1;
                    stack.push(builder.ins().iconst(int, tag(imm)));
                }
                INSTR_FIXED_ADD => {
                    // bin_op_tagged in the interp pops x (top) and y;
                    // result_n = x_n + y_n; (commutative).
                    // tagged identity: (x_t + y_t) - 1
                    let x = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let y = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let sum = builder.ins().iadd(x, y);
                    let one = builder.ins().iconst(int, 1);
                    let result = builder.ins().isub(sum, one);
                    stack.push(result);
                }
                INSTR_FIXED_SUB => {
                    // Interp: result_n = y_n - x_n
                    // tagged: (y_t - x_t) + 1
                    let x = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let y = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let diff = builder.ins().isub(y, x);
                    let one = builder.ins().iconst(int, 1);
                    let result = builder.ins().iadd(diff, one);
                    stack.push(result);
                }
                INSTR_FIXED_MULT => {
                    // Interp: result_n = x_n * y_n
                    // Untag both via arithmetic shift right by 1
                    // (after subtracting the tag bit). Multiply, re-tag.
                    let x = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let y = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let one = builder.ins().iconst(int, 1);
                    let x_minus_1 = builder.ins().isub(x, one);
                    let xn = builder.ins().sshr_imm(x_minus_1, 1);
                    let y_minus_1 = builder.ins().isub(y, one);
                    let yn = builder.ins().sshr_imm(y_minus_1, 1);
                    let prod = builder.ins().imul(xn, yn);
                    // re-tag: 2 * prod + 1
                    let doubled = builder.ins().ishl_imm(prod, 1);
                    let result = builder.ins().iadd(doubled, one);
                    stack.push(result);
                }
                INSTR_RETURN_1 => {
                    let v = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    builder.ins().return_(&[v]);
                    returned = true;
                }
                INSTR_JUMP8 => {
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let off = bytecode[pc] as usize;
                    pc += 1;
                    let target_pc = pc + off;
                    let target_blk = *block_at.get(&target_pc)
                        .expect("target should be registered in pass 1");
                    let args: Vec<BlockArg> =
                        stack.iter().copied().map(BlockArg::from).collect();
                    builder.ins().jump(target_blk, &args);
                    returned = true;
                }
                INSTR_JUMP8_FALSE | INSTR_JUMP8_TRUE => {
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let off = bytecode[pc] as usize;
                    pc += 1;
                    let target_pc = pc + off;
                    let cond = stack.pop().ok_or(TranslateError::Underflow(pc - 2))?;
                    let target_blk = *block_at.get(&target_pc)
                        .expect("target should be registered in pass 1");
                    let fall_blk = *block_at.get(&pc).expect("fallthrough should be registered");
                    let zero = builder.ins().iconst(int, tag(0));
                    let is_zero = builder.ins().icmp(IntCC::Equal, cond, zero);
                    let args: Vec<BlockArg> =
                        stack.iter().copied().map(BlockArg::from).collect();
                    if op == INSTR_JUMP8_FALSE {
                        builder.ins().brif(is_zero, target_blk, &args, fall_blk, &args);
                    } else {
                        builder.ins().brif(is_zero, fall_blk, &args, target_blk, &args);
                    }
                    returned = true;
                }
                _ => {
                    return Err(TranslateError::Unsupported { op, at: pc - 1 });
                }
            }
        }

        // Seal all blocks. Note: with our pre-pass we know every
        // block's predecessors, so calling seal_all_blocks is safe
        // even on blocks that have no incoming edges (Cranelift will
        // optimise those away or treat them as unreachable).
        builder.seal_all_blocks();
        if !returned {
            return Err(TranslateError::FellOffEnd);
        }
        builder.finalize();
    }

    let name = jit.fresh_name("polyml_jit_translated");
    let func_id = jit
        .module
        .declare_function(&name, Linkage::Export, &ctx.func.signature)
        .map_err(|e| JitError::Module(e.to_string()))?;
    jit.module
        .define_function(func_id, &mut ctx)
        .map_err(|e| JitError::Module(e.to_string()))?;
    jit.module.clear_context(&mut ctx);
    jit.module
        .finalize_definitions()
        .map_err(|e| JitError::Module(e.to_string()))?;

    let code_ptr = jit.module.get_finalized_function(func_id);
    // SAFETY: signature matches; JIT memory live while `jit` is.
    let f: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
    Ok(f)
}

/// PolyWord tagging: a small int `n` is represented as `2n + 1`.
fn tag(n: i64) -> i64 {
    n.wrapping_mul(2).wrapping_add(1)
}

/// Return the total byte length of the opcode at `bc[pc]` (opcode +
/// any immediates). Used by the main loop to step over unreachable
/// bytes without misaligning to an immediate.
fn opcode_total_len(bc: &[u8], pc: usize) -> Result<usize, TranslateError> {
    if pc >= bc.len() {
        return Err(TranslateError::Truncated(pc));
    }
    Ok(match bc[pc] {
        INSTR_CONST_INT_B | INSTR_JUMP8 | INSTR_JUMP8_FALSE | INSTR_JUMP8_TRUE => 2,
        INSTR_CONST_0..=INSTR_CONST_4
        | INSTR_CONST_10
        | INSTR_RETURN_1
        | INSTR_FIXED_ADD
        | INSTR_FIXED_SUB
        | INSTR_FIXED_MULT => 1,
        op => return Err(TranslateError::Unsupported { op, at: pc }),
    })
}

/// First pass: walk the bytecode, tracking the static stack depth
/// at each PC. For every branch instruction, record both the
/// taken-target PC and (for conditional branches) the fallthrough
/// PC, along with the expected stack depth at that target. Returns
/// `target_pc -> depth`.
///
/// The depth of a conditional fallthrough is one less than the
/// pre-branch depth, because the conditional pops the test value.
/// `JUMP8` (unconditional) doesn't pop; it just jumps with the
/// same depth.
fn scan_branch_targets(
    bytecode: &[u8],
) -> Result<std::collections::BTreeMap<usize, usize>, TranslateError> {
    let mut targets: std::collections::BTreeMap<usize, usize> =
        std::collections::BTreeMap::new();
    let mut depth: usize = 0;
    let mut pc = 0usize;
    while pc < bytecode.len() {
        let op = bytecode[pc];
        pc += 1;
        match op {
            INSTR_CONST_0..=INSTR_CONST_4 => depth += 1,
            INSTR_CONST_10 => depth += 1,
            INSTR_CONST_INT_B => {
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                pc += 1;
                depth += 1;
            }
            INSTR_FIXED_ADD | INSTR_FIXED_SUB | INSTR_FIXED_MULT => {
                if depth < 2 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                depth -= 1;
            }
            INSTR_RETURN_1 => {
                if depth == 0 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                // Path ends here; subsequent bytes start a new fragment
                // — but the only way to enter them is via a branch
                // target. We don't track stack depth into unreachable
                // code.
                depth = depth.saturating_sub(1); // for clarity post-pop
            }
            INSTR_JUMP8 => {
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                let off = bytecode[pc] as usize;
                pc += 1;
                let target = pc + off;
                record_target(&mut targets, target, depth)?;
            }
            INSTR_JUMP8_FALSE | INSTR_JUMP8_TRUE => {
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                let off = bytecode[pc] as usize;
                pc += 1;
                if depth == 0 {
                    return Err(TranslateError::Underflow(pc - 2));
                }
                let post_pop = depth - 1;
                let taken = pc + off;
                record_target(&mut targets, taken, post_pop)?;
                // Fallthrough also a branch target (so both arms
                // start with the same block-param shape).
                record_target(&mut targets, pc, post_pop)?;
                depth = post_pop;
            }
            _ => {
                return Err(TranslateError::Unsupported { op, at: pc - 1 });
            }
        }
    }
    Ok(targets)
}

fn record_target(
    targets: &mut std::collections::BTreeMap<usize, usize>,
    pc: usize,
    depth: usize,
) -> Result<(), TranslateError> {
    match targets.get(&pc) {
        None => {
            targets.insert(pc, depth);
            Ok(())
        }
        Some(&existing) if existing == depth => Ok(()),
        // Mismatched stack depth at a branch target — surface as
        // an unsupported pattern; future work could spill the
        // stack to memory and unify depths.
        Some(_) => Err(TranslateError::Unsupported { op: 0xFE, at: pc }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn untag(t: i64) -> i64 {
        assert_eq!(t & 1, 1, "expected tagged int, got raw {t}");
        (t - 1) >> 1
    }

    #[test]
    fn translate_const0_return() {
        // Bytecode: INSTR_CONST_0; INSTR_RETURN_1
        let bc = vec![INSTR_CONST_0, INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(f()), 0);
    }

    #[test]
    fn translate_const_int_b_return() {
        // Bytecode: INSTR_CONST_INT_B 42; INSTR_RETURN_1
        let bc = vec![INSTR_CONST_INT_B, 42, INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(f()), 42);
    }

    #[test]
    fn translate_const_int_b_negative() {
        // -7 as a signed byte is 0xF9.
        let bc = vec![INSTR_CONST_INT_B, 0xF9, INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(f()), -7);
    }

    #[test]
    fn translate_multiple_constants_returns_top() {
        // Push 1, 2, 3, 4; return → top = 4
        let bc = vec![
            INSTR_CONST_1, INSTR_CONST_2, INSTR_CONST_3, INSTR_CONST_4, INSTR_RETURN_1,
        ];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(f()), 4);
    }

    #[test]
    fn translate_rejects_truncated_const_int_b() {
        // INSTR_CONST_INT_B with no immediate.
        let bc = vec![INSTR_CONST_INT_B];
        let mut jit = Jit::new().unwrap();
        let err = compile(&mut jit, &bc).unwrap_err();
        assert!(matches!(err, TranslateError::Truncated(_)), "got {err:?}");
    }

    #[test]
    fn translate_rejects_return_on_empty_stack() {
        let bc = vec![INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let err = compile(&mut jit, &bc).unwrap_err();
        assert!(matches!(err, TranslateError::Underflow(_)), "got {err:?}");
    }

    #[test]
    fn translate_rejects_unknown_opcode() {
        let bc = vec![0xFD, INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let err = compile(&mut jit, &bc).unwrap_err();
        assert!(matches!(err, TranslateError::Unsupported { op: 0xFD, .. }), "got {err:?}");
    }

    #[test]
    fn translate_fixed_add_1_plus_2() {
        // push 1; push 2; ADD; return → 3
        let bc = vec![INSTR_CONST_1, INSTR_CONST_2, INSTR_FIXED_ADD, INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(f()), 3);
    }

    #[test]
    fn translate_fixed_sub_4_minus_1() {
        // push 4; push 1; SUB → y_n - x_n = 4 - 1 = 3
        let bc = vec![INSTR_CONST_4, INSTR_CONST_1, INSTR_FIXED_SUB, INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(f()), 3);
    }

    #[test]
    fn translate_fixed_mult_3_times_4() {
        // push 3; push 4; MULT → 12
        let bc = vec![INSTR_CONST_3, INSTR_CONST_4, INSTR_FIXED_MULT, INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(f()), 12);
    }

    #[test]
    fn translate_polynomial_3_times_3_plus_10() {
        // 3 * 3 + 10 — push 3, push 3, MULT, push 10, ADD, return
        let bc = vec![
            INSTR_CONST_3, INSTR_CONST_3, INSTR_FIXED_MULT, INSTR_CONST_10,
            INSTR_FIXED_ADD, INSTR_RETURN_1,
        ];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(f()), 19);
    }

    #[test]
    fn translate_negative_arithmetic() {
        // -5 + 3 = -2, encoded with INSTR_CONST_INT_B
        let bc = vec![
            INSTR_CONST_INT_B, (-5i8) as u8,
            INSTR_CONST_3,
            INSTR_FIXED_ADD,
            INSTR_RETURN_1,
        ];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(f()), -2);
    }

    #[test]
    fn translate_jump_skips_over_dead_code() {
        // JUMP8 +2 → skip 2 bytes (an unreachable CONST_2)
        // After jump: push 4, return 4.
        // Layout (offsets):
        //  0: JUMP8 off=2     (after immediate, pc=2; target = 2+2 = 4)
        //  2: CONST_2         (dead — unreachable, but valid bytecode)
        //  3: RETURN_1        (dead)
        //  4: CONST_4         ← jump lands here
        //  5: RETURN_1
        // Note: dead code is allowed because the pre-pass walks
        // linearly and JUMP8 is treated as a terminator for that path.
        // To keep pass 1 happy we replace the dead bytes with no-op-
        // shaped opcodes: a CONST + RETURN_1 just tracks depth 1→0.
        let bc = vec![
            INSTR_JUMP8, 2,           // 0..2
            INSTR_CONST_2,            // 2
            INSTR_RETURN_1,           // 3
            INSTR_CONST_4,            // 4 (target)
            INSTR_RETURN_1,           // 5
        ];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(f()), 4);
    }

    #[test]
    fn translate_if_then_else_via_jump_false() {
        // Compute: if cond then 1 else 2
        // We use CONST_1 as a truthy condition (tagged 1 = raw 3).
        // Layout:
        //  0: CONST_1            (push the condition value: 1)
        //  1: JUMP8_FALSE off=3  (pop; if 0 jump fwd 3 → pc=6)
        //                        (after immediate, pc=3)
        //  3: CONST_1            (then-arm: push 1)
        //  4: JUMP8 off=1        (jump over else → pc=7)
        //  6: CONST_2            (else-arm: push 2)
        //  7: RETURN_1
        let bc = vec![
            INSTR_CONST_1,            // 0
            INSTR_JUMP8_FALSE, 3,     // 1..3, target = 3 + 3 = 6
            INSTR_CONST_1,            // 3 (then)
            INSTR_JUMP8, 1,           // 4..6, target = 6 + 1 = 7
            INSTR_CONST_2,            // 6 (else)
            INSTR_RETURN_1,           // 7
        ];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        // Condition was 1 (truthy), so we take the then-arm → 1.
        assert_eq!(untag(f()), 1);
    }

    #[test]
    fn translate_if_else_with_false_condition() {
        //  0: CONST_0            (push 0 = false)
        //  1: JUMP8_FALSE off=3  (taken: jump to 6)
        //  3: CONST_1            (then; dead this run)
        //  4: JUMP8 off=1        (skip else; dead this run)
        //  6: CONST_2            (else)
        //  7: RETURN_1
        let bc = vec![
            INSTR_CONST_0,
            INSTR_JUMP8_FALSE, 3,
            INSTR_CONST_1,
            INSTR_JUMP8, 1,
            INSTR_CONST_2,
            INSTR_RETURN_1,
        ];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(f()), 2);
    }

    #[test]
    fn translate_jump_true() {
        //  0: CONST_3            (truthy)
        //  1: JUMP8_TRUE off=3   (taken: jump to 6)
        //  3: CONST_0            (dead)
        //  4: JUMP8 off=1        (dead)
        //  6: CONST_4
        //  7: RETURN_1
        let bc = vec![
            INSTR_CONST_3,
            INSTR_JUMP8_TRUE, 3,
            INSTR_CONST_0,
            INSTR_JUMP8, 1,
            INSTR_CONST_4,
            INSTR_RETURN_1,
        ];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(f()), 4);
    }

    #[test]
    fn translate_rejects_missing_return() {
        let bc = vec![INSTR_CONST_0];
        let mut jit = Jit::new().unwrap();
        let err = compile(&mut jit, &bc).unwrap_err();
        assert!(matches!(err, TranslateError::FellOffEnd), "got {err:?}");
    }
}
