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

    {
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_builder_ctx);
        let block = builder.create_block();
        builder.switch_to_block(block);
        builder.seal_block(block);

        // Compile-time stack of in-IR values; the position in this
        // Vec corresponds to the SML stack position. `push` is just
        // `Vec::push`; `pop` is `Vec::pop`.
        let mut stack: Vec<Value> = Vec::new();
        let mut pc = 0usize;
        let mut returned = false;

        while pc < bytecode.len() {
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
                    break;
                }
                _ => {
                    return Err(TranslateError::Unsupported { op, at: pc - 1 });
                }
            }
        }

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
    fn translate_rejects_missing_return() {
        let bc = vec![INSTR_CONST_0];
        let mut jit = Jit::new().unwrap();
        let err = compile(&mut jit, &bc).unwrap_err();
        assert!(matches!(err, TranslateError::FellOffEnd), "got {err:?}");
    }
}
