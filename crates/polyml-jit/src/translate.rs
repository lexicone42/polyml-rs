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
const INSTR_EQUAL_WORD: u8 = 0xa0;
const INSTR_LESS_SIGNED: u8 = 0xa2;
const INSTR_JUMP8: u8 = 0x02;
const INSTR_JUMP8_FALSE: u8 = 0x03;
const INSTR_JUMP8_TRUE: u8 = 0x46;
const INSTR_JUMP_BACK8: u8 = 0x1e;
const INSTR_LOCAL_B: u8 = 0x22;
const INSTR_LOCAL_0: u8 = 0x29;
const INSTR_LOCAL_7: u8 = 0x30;
const INSTR_INDIRECT_LOCAL_B0: u8 = 0xc7;
const INSTR_INDIRECT_LOCAL_B1: u8 = 0xc1;
const INSTR_INDIRECT_CLOSURE_B0: u8 = 0x77;
const INSTR_INDIRECT_CLOSURE_B1: u8 = 0x7a;
const INSTR_INDIRECT_CLOSURE_B2: u8 = 0x7c;
const INSTR_ENTER_INT_X86: u8 = 0xff;
const INSTR_ENTER_INT_ARM64: u8 = 0xe9;
const INSTR_INDIRECT_LOCAL_BB: u8 = 0x21;
const INSTR_INDIRECT_CLOSURE_BB: u8 = 0x54;
const INSTR_INDIRECT_0: u8 = 0x35;
const INSTR_INDIRECT_0_LOCAL_0: u8 = 0xc6;
const INSTR_NO_OP: u8 = 0x52;
const INSTR_JUMP_TAGGED_LOCAL: u8 = 0xc4;
const INSTR_IS_TAGGED_LOCAL_B: u8 = 0xc2;
const INSTR_CONST_ADDR8_0: u8 = 0x55;
const INSTR_CONST_ADDR8_1: u8 = 0x56;
const INSTR_CALL_FAST_RTS0: u8 = 0x83;
const INSTR_CALL_FAST_RTS1: u8 = 0x84;
const INSTR_CALL_FAST_RTS2: u8 = 0x85;
const INSTR_CALL_FAST_RTS3: u8 = 0x86;
const INSTR_CALL_FAST_RTS4: u8 = 0x87;
const INSTR_CALL_FAST_RTS5: u8 = 0x88;
const INSTR_JUMP_NEQ_LOCAL: u8 = 0xc5;
const INSTR_JUMP_NEQ_LOCAL_IND: u8 = 0xc3;
const INSTR_RESET_1: u8 = 0x50;
const INSTR_RESET_2: u8 = 0x51;
const INSTR_RESET_B: u8 = 0x26;
const INSTR_RESET_R_1: u8 = 0x64;
const INSTR_RESET_R_2: u8 = 0x65;
const INSTR_RESET_R_3: u8 = 0x66;

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
/// Signature of every JIT'd function:
///   `extern "C" fn(args: *const i64) -> i64`
/// The caller passes a pointer to an array of `arg_count` PolyWords
/// (one per SML arg) — for 0-arg functions the pointer is unused
/// (still must be a valid pointer; pass null is undefined). The
/// return value is the result PolyWord.
pub type JitFn = unsafe extern "C" fn(args: *const i64) -> i64;

/// Compile bytecode where the bytecode portion is the entire slice
/// (no constant pool accessible). CONST_ADDR* opcodes will fail
/// with `Unsupported` because they read past the bytecode end.
pub fn compile(jit: &mut Jit, bytecode: &[u8]) -> Result<JitFn, TranslateError> {
    compile_with_consts(jit, bytecode, bytecode.len())
}

/// Compile a code object where `full_body` contains the entire
/// object (bytecode followed by constants area + trailer), and
/// `bytecode_end` is the byte offset where the bytecode opcodes
/// stop. CONST_ADDR* reads land in `full_body[bytecode_end..]`.
pub fn compile_with_consts(
    jit: &mut Jit,
    full_body: &[u8],
    bytecode_end: usize,
) -> Result<JitFn, TranslateError> {
    let bytecode = &full_body[..bytecode_end];
    let _full_body = full_body; // keep for CONST_ADDR reads below
    let mut ctx = jit.module.make_context();
    let mut func_builder_ctx = FunctionBuilderContext::new();
    let int = types::I64;
    // Signature: takes one pointer (treated as i64), returns one i64.
    ctx.func.signature.params.push(AbiParam::new(int));
    ctx.func.signature.returns.push(AbiParam::new(int));

    // Pass 1: scan to find branch target PCs and the stack depth
    // expected at each target. Each unique target gets its own
    // Cranelift block; the block's parameters carry the stack
    // values across the branch.
    let targets = scan_branch_targets(bytecode)?;

    let (entry_pc, prologue_arg_count) = function_prologue(bytecode);
    let arg_count = if prologue_arg_count > 0 || entry_pc > 0 {
        prologue_arg_count
    } else {
        infer_arg_count(bytecode, entry_pc).unwrap_or(0)
    };

    // Declare the RTS trampoline import for this module. Signature:
    //   fn(stub: i64, n_args: i64, args_ptr: i64) -> i64
    let mut rts_sig = jit.module.make_signature();
    rts_sig.params.push(AbiParam::new(types::I64));
    rts_sig.params.push(AbiParam::new(types::I64));
    rts_sig.params.push(AbiParam::new(types::I64));
    rts_sig.returns.push(AbiParam::new(types::I64));
    let rts_func_id = jit
        .module
        .declare_function(
            "polyml_jit_rts_trampoline",
            Linkage::Import,
            &rts_sig,
        )
        .map_err(|e| JitError::Module(e.to_string()))?;
    let rts_func_ref = jit
        .module
        .declare_func_in_func(rts_func_id, &mut ctx.func);

    {
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_builder_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);

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
        let args_ptr = builder.block_params(entry)[0];

        // Compile-time stack of in-IR values; the position in this
        // Vec corresponds to the SML stack position. `push` is just
        // `Vec::push`; `pop` is `Vec::pop`.
        // Seed the stack with the function's incoming args (loaded
        // from the args_ptr argument). PolyML's calling convention
        // puts args in stack order, so arg 0 is the bottom-of-stack
        // for the function's POV (= what LOCAL_(N-1) reads).
        let mut stack: Vec<Value> = Vec::with_capacity(arg_count);
        for i in 0..arg_count {
            let v = builder.ins().load(
                int,
                cranelift::prelude::MemFlags::trusted(),
                args_ptr,
                (i as i32) * 8,
            );
            stack.push(v);
        }
        let mut pc = entry_pc;
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
                INSTR_LOCAL_0..=INSTR_LOCAL_7 => {
                    let depth = (op - INSTR_LOCAL_0) as usize;
                    if depth >= stack.len() {
                        return Err(TranslateError::Underflow(pc - 1));
                    }
                    let v = stack[stack.len() - 1 - depth];
                    stack.push(v);
                }
                INSTR_LOCAL_B => {
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let depth = bytecode[pc] as usize;
                    pc += 1;
                    if depth >= stack.len() {
                        return Err(TranslateError::Underflow(pc - 2));
                    }
                    let v = stack[stack.len() - 1 - depth];
                    stack.push(v);
                }
                INSTR_INDIRECT_LOCAL_B0 | INSTR_INDIRECT_LOCAL_B1 => {
                    // Read sp[depth] as a pointer, push the value at
                    // offset 0 (B0) or 1 word offset (B1) within the
                    // pointed object.
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let depth = bytecode[pc] as usize;
                    pc += 1;
                    if depth >= stack.len() {
                        return Err(TranslateError::Underflow(pc - 2));
                    }
                    let base = stack[stack.len() - 1 - depth];
                    let offset_bytes =
                        if op == INSTR_INDIRECT_LOCAL_B0 { 0 } else { 8 };
                    let val = builder.ins().load(
                        int,
                        cranelift::prelude::MemFlags::trusted(),
                        base,
                        offset_bytes,
                    );
                    stack.push(val);
                }
                INSTR_NO_OP => { /* skip */ }
                INSTR_RESET_1 => {
                    stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                }
                INSTR_RESET_2 => {
                    stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                }
                INSTR_RESET_B => {
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let n = bytecode[pc] as usize;
                    pc += 1;
                    if stack.len() < n {
                        return Err(TranslateError::Underflow(pc - 2));
                    }
                    stack.truncate(stack.len() - n);
                }
                INSTR_RESET_R_1 | INSTR_RESET_R_2 | INSTR_RESET_R_3 => {
                    // Preserve top, drop N below it.
                    let n = match op {
                        INSTR_RESET_R_1 => 1,
                        INSTR_RESET_R_2 => 2,
                        _ => 3,
                    };
                    if stack.len() < n + 1 {
                        return Err(TranslateError::Underflow(pc - 1));
                    }
                    let top = stack.pop().unwrap();
                    stack.truncate(stack.len() - n);
                    stack.push(top);
                }
                INSTR_CALL_FAST_RTS0
                | INSTR_CALL_FAST_RTS1
                | INSTR_CALL_FAST_RTS2
                | INSTR_CALL_FAST_RTS3
                | INSTR_CALL_FAST_RTS4
                | INSTR_CALL_FAST_RTS5 => {
                    let n_args = (op - INSTR_CALL_FAST_RTS0) as usize;
                    // Pop stub first (top), then N args. We need
                    // args[0..N] in slot[0..N] in their original
                    // top-down order from the SML stack — which
                    // matches what the Rust trampoline expects.
                    let stub = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let mut args_vec: Vec<Value> = Vec::with_capacity(n_args);
                    for _ in 0..n_args {
                        args_vec.push(stack.pop().ok_or(TranslateError::Underflow(pc - 1))?);
                    }
                    // Allocate a stack slot for the args buffer
                    // (zero-sized slot is fine when n_args == 0).
                    let slot_size = std::cmp::max(8, (n_args * 8) as u32);
                    let slot = builder.create_sized_stack_slot(
                        cranelift::prelude::StackSlotData::new(
                            cranelift::prelude::StackSlotKind::ExplicitSlot,
                            slot_size,
                            3,
                        ),
                    );
                    for (i, v) in args_vec.iter().enumerate() {
                        builder.ins().stack_store(*v, slot, (i * 8) as i32);
                    }
                    let args_ptr = builder.ins().stack_addr(types::I64, slot, 0);
                    let n_args_v = builder.ins().iconst(types::I64, n_args as i64);
                    let _ = stub;
                    let call_inst = builder.ins().call(
                        rts_func_ref,
                        &[stub, n_args_v, args_ptr],
                    );
                    let result_val = builder.inst_results(call_inst)[0];
                    stack.push(result_val);
                }
                INSTR_CONST_ADDR8_0 | INSTR_CONST_ADDR8_1 => {
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let imm = bytecode[pc] as usize;
                    pc += 1;
                    let idx = if op == INSTR_CONST_ADDR8_0 { 3 } else { 4 };
                    // read address (bytes from start of full_body):
                    //   pc_after_imm + imm + idx * 8
                    let read_at = pc + imm + idx * 8;
                    if read_at + 8 > _full_body.len() {
                        return Err(TranslateError::Unsupported { op, at: pc - 2 });
                    }
                    let mut buf = [0u8; 8];
                    buf.copy_from_slice(&_full_body[read_at..read_at + 8]);
                    let val = i64::from_le_bytes(buf);
                    stack.push(builder.ins().iconst(int, val));
                }
                INSTR_INDIRECT_0 => {
                    // top = ptr; replace top with ptr[0]
                    let base = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let val = builder.ins().load(int, cranelift::prelude::MemFlags::trusted(), base, 0);
                    stack.push(val);
                }
                INSTR_INDIRECT_0_LOCAL_0 => {
                    // peek top (= LOCAL_0); load offset 0
                    if stack.is_empty() {
                        return Err(TranslateError::Underflow(pc - 1));
                    }
                    let base = *stack.last().unwrap();
                    let val = builder.ins().load(int, cranelift::prelude::MemFlags::trusted(), base, 0);
                    stack.push(val);
                }
                INSTR_INDIRECT_LOCAL_BB => {
                    // depth, slot (each 1 byte)
                    if pc + 1 >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let depth = bytecode[pc] as usize;
                    let slot = bytecode[pc + 1] as usize;
                    pc += 2;
                    if depth >= stack.len() {
                        return Err(TranslateError::Underflow(pc - 3));
                    }
                    let base = stack[stack.len() - 1 - depth];
                    let val = builder.ins().load(
                        int,
                        cranelift::prelude::MemFlags::trusted(),
                        base,
                        (slot * 8) as i32,
                    );
                    stack.push(val);
                }
                INSTR_JUMP_TAGGED_LOCAL => {
                    // [depth, off]; if sp[depth] is tagged (LSB=1)
                    // jump forward `off` bytes; else fallthrough.
                    if pc + 1 >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let d = bytecode[pc] as usize;
                    let off = bytecode[pc + 1] as usize;
                    pc += 2;
                    if d >= stack.len() {
                        return Err(TranslateError::Underflow(pc - 3));
                    }
                    let v = stack[stack.len() - 1 - d];
                    let one = builder.ins().iconst(int, 1);
                    let lsb = builder.ins().band(v, one);
                    let target_pc = pc + off;
                    let target_blk = *block_at.get(&target_pc)
                        .expect("JUMP_TAGGED_LOCAL target should be registered");
                    let fall_blk = *block_at.get(&pc)
                        .expect("JUMP_TAGGED_LOCAL fallthrough should be registered");
                    let args: Vec<BlockArg> =
                        stack.iter().copied().map(BlockArg::from).collect();
                    // brif: if cond ≠ 0 then then-block else else-block.
                    // LSB=1 → tagged → take the jump.
                    builder.ins().brif(lsb, target_blk, &args, fall_blk, &args);
                    returned = true;
                }
                INSTR_IS_TAGGED_LOCAL_B => {
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let d = bytecode[pc] as usize;
                    pc += 1;
                    if d >= stack.len() {
                        return Err(TranslateError::Underflow(pc - 2));
                    }
                    let v = stack[stack.len() - 1 - d];
                    let one = builder.ins().iconst(int, 1);
                    let lsb = builder.ins().band(v, one);
                    let doubled = builder.ins().ishl_imm(lsb, 1);
                    let result = builder.ins().iadd(doubled, one);
                    stack.push(result);
                }
                INSTR_JUMP_NEQ_LOCAL | INSTR_JUMP_NEQ_LOCAL_IND => {
                    // [depth, want, off]; peek sp[depth] = u
                    // (or *u for IND); if u == tag(want) fall thru
                    // else jump forward `off`.
                    if pc + 2 >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let d = bytecode[pc] as usize;
                    let want = bytecode[pc + 1] as i8 as i64;
                    let off = bytecode[pc + 2] as usize;
                    pc += 3;
                    if d >= stack.len() {
                        return Err(TranslateError::Underflow(pc - 4));
                    }
                    let local = stack[stack.len() - 1 - d];
                    let v = if op == INSTR_JUMP_NEQ_LOCAL_IND {
                        builder.ins().load(
                            int,
                            cranelift::prelude::MemFlags::trusted(),
                            local,
                            0,
                        )
                    } else {
                        local
                    };
                    let want_tagged =
                        builder.ins().iconst(int, want.wrapping_mul(2).wrapping_add(1));
                    let eq = builder.ins().icmp(IntCC::Equal, v, want_tagged);
                    let target_pc = pc + off;
                    let target_blk = *block_at.get(&target_pc)
                        .expect("JUMP_NEQ_LOCAL target should be registered");
                    let fall_blk = *block_at.get(&pc)
                        .expect("JUMP_NEQ_LOCAL fallthrough should be registered");
                    let args: Vec<BlockArg> =
                        stack.iter().copied().map(BlockArg::from).collect();
                    // eq=1 → fall through (equal). eq=0 → jump.
                    builder.ins().brif(eq, fall_blk, &args, target_blk, &args);
                    returned = true;
                }
                INSTR_INDIRECT_CLOSURE_BB => {
                    // depth, slot (each 1 byte). Closure has code at
                    // word[0]; slot 0 is the first captured.
                    if pc + 1 >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let depth = bytecode[pc] as usize;
                    let slot = bytecode[pc + 1] as usize;
                    pc += 2;
                    if depth >= stack.len() {
                        return Err(TranslateError::Underflow(pc - 3));
                    }
                    let base = stack[stack.len() - 1 - depth];
                    let val = builder.ins().load(
                        int,
                        cranelift::prelude::MemFlags::trusted(),
                        base,
                        ((1 + slot) * 8) as i32,
                    );
                    stack.push(val);
                }
                INSTR_INDIRECT_CLOSURE_B0
                | INSTR_INDIRECT_CLOSURE_B1
                | INSTR_INDIRECT_CLOSURE_B2 => {
                    // Read sp[depth] as a closure pointer; push
                    // *(ptr + (1 + slot) words). The +1 skips word[0]
                    // (the code address); slot 0 → first captured.
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let depth = bytecode[pc] as usize;
                    pc += 1;
                    if depth >= stack.len() {
                        return Err(TranslateError::Underflow(pc - 2));
                    }
                    let slot = match op {
                        INSTR_INDIRECT_CLOSURE_B0 => 0,
                        INSTR_INDIRECT_CLOSURE_B1 => 1,
                        INSTR_INDIRECT_CLOSURE_B2 => 2,
                        _ => unreachable!(),
                    };
                    let base = stack[stack.len() - 1 - depth];
                    let offset_bytes: i32 = (1 + slot) * 8;
                    let val = builder.ins().load(
                        int,
                        cranelift::prelude::MemFlags::trusted(),
                        base,
                        offset_bytes,
                    );
                    stack.push(val);
                }
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
                INSTR_EQUAL_WORD => {
                    // pop x, y; push tagged(1) if x == y else tagged(0).
                    // Since tagged ints have the same bit pattern when
                    // equal, a raw word compare is correct.
                    let x = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let y = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let cmp = builder.ins().icmp(IntCC::Equal, x, y);
                    let cmp64 = builder.ins().uextend(int, cmp);
                    let doubled = builder.ins().ishl_imm(cmp64, 1);
                    let one = builder.ins().iconst(int, 1);
                    let result = builder.ins().iadd(doubled, one);
                    stack.push(result);
                }
                INSTR_LESS_SIGNED => {
                    // Interp: bin_op_cmp(|x, y| (y as isize) < (x as isize))
                    // pop x, y; push tagged(1) if y < x else tagged(0).
                    let x = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let y = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let cmp = builder.ins().icmp(IntCC::SignedLessThan, y, x);
                    let cmp64 = builder.ins().uextend(int, cmp);
                    let doubled = builder.ins().ishl_imm(cmp64, 1);
                    let one = builder.ins().iconst(int, 1);
                    let result = builder.ins().iadd(doubled, one);
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
                INSTR_JUMP_BACK8 => {
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let off = bytecode[pc] as usize;
                    pc += 1;
                    let target_pc = pc - off - 2;
                    let target_blk = *block_at.get(&target_pc)
                        .expect("back-edge target should be registered in pass 1");
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
    let f: JitFn = unsafe { std::mem::transmute(code_ptr) };
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
        INSTR_CONST_INT_B
        | INSTR_JUMP8
        | INSTR_JUMP8_FALSE
        | INSTR_JUMP8_TRUE
        | INSTR_JUMP_BACK8
        | INSTR_LOCAL_B
        | INSTR_INDIRECT_LOCAL_B0
        | INSTR_INDIRECT_LOCAL_B1
        | INSTR_INDIRECT_CLOSURE_B0
        | INSTR_INDIRECT_CLOSURE_B1
        | INSTR_INDIRECT_CLOSURE_B2 => 2,
        INSTR_INDIRECT_LOCAL_BB
        | INSTR_INDIRECT_CLOSURE_BB
        | INSTR_JUMP_TAGGED_LOCAL
        | INSTR_JUMP_NEQ_LOCAL
        | INSTR_JUMP_NEQ_LOCAL_IND => 3,
        INSTR_CONST_ADDR8_0 | INSTR_CONST_ADDR8_1 => 2,
        INSTR_CALL_FAST_RTS0
        | INSTR_CALL_FAST_RTS1
        | INSTR_CALL_FAST_RTS2
        | INSTR_CALL_FAST_RTS3
        | INSTR_CALL_FAST_RTS4
        | INSTR_CALL_FAST_RTS5 => 1,
        INSTR_IS_TAGGED_LOCAL_B => 2,
        INSTR_CONST_0..=INSTR_CONST_4
        | INSTR_CONST_10
        | INSTR_RETURN_1
        | INSTR_FIXED_ADD
        | INSTR_FIXED_SUB
        | INSTR_FIXED_MULT
        | INSTR_EQUAL_WORD
        | INSTR_LESS_SIGNED
        | INSTR_LOCAL_0..=INSTR_LOCAL_7
        | INSTR_INDIRECT_0
        | INSTR_INDIRECT_0_LOCAL_0
        | INSTR_NO_OP
        | INSTR_RESET_1
        | INSTR_RESET_2
        | INSTR_RESET_R_1
        | INSTR_RESET_R_2
        | INSTR_RESET_R_3 => 1,
        INSTR_RESET_B => 2,
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
/// If the bytecode starts with an enter-int marker, return
/// `(body_start_pc, arg_count)`. Else `(0, 0)`. The compiler
/// emits `0xff` (X86) or `0xe9` (Arm64) followed by
/// `(arg_count | 0x80)` at every function entry.
fn function_prologue(bytecode: &[u8]) -> (usize, usize) {
    if bytecode.len() < 2 {
        return (0, 0);
    }
    match bytecode[0] {
        INSTR_ENTER_INT_X86 | INSTR_ENTER_INT_ARM64 => {
            let arg = (bytecode[1] & 0x7f) as usize;
            (2, arg)
        }
        _ => (0, 0),
    }
}

fn function_entry_pc(bytecode: &[u8]) -> usize {
    function_prologue(bytecode).0
}

/// Lightweight first-walk that determines the minimum incoming
/// stack size required by the function. Useful for bytecode that
/// has no enter-int prologue (the bootstrap image): we infer the
/// arg count by finding the largest stack-relative read.
///
/// Returns `Some(arg_count)` on a clean walk, `None` if the
/// bytecode hits unsupported opcodes during scanning (we'll
/// surface the same error later in scan_branch_targets).
fn infer_arg_count(bytecode: &[u8], start_pc: usize) -> Option<usize> {
    let mut depth: i32 = 0;
    let mut min_depth: i32 = 0;
    let mut pc = start_pc;
    while pc < bytecode.len() {
        let op = bytecode[pc];
        pc += 1;
        let (push_count, pop_count, peek_depth, immediate_bytes): (i32, i32, Option<usize>, usize) =
            match op {
                INSTR_CONST_0..=INSTR_CONST_4 | INSTR_CONST_10 => (1, 0, None, 0),
                INSTR_CONST_INT_B => (1, 0, None, 1),
                INSTR_LOCAL_0..=INSTR_LOCAL_7 => {
                    let d = (op - INSTR_LOCAL_0) as usize;
                    (1, 0, Some(d), 0)
                }
                INSTR_LOCAL_B => {
                    if pc >= bytecode.len() { return None; }
                    let d = bytecode[pc] as usize;
                    (1, 0, Some(d), 1)
                }
                INSTR_INDIRECT_LOCAL_B0
                | INSTR_INDIRECT_LOCAL_B1
                | INSTR_INDIRECT_CLOSURE_B0
                | INSTR_INDIRECT_CLOSURE_B1
                | INSTR_INDIRECT_CLOSURE_B2 => {
                    if pc >= bytecode.len() { return None; }
                    let d = bytecode[pc] as usize;
                    (1, 0, Some(d), 1)
                }
                INSTR_INDIRECT_LOCAL_BB | INSTR_INDIRECT_CLOSURE_BB => {
                    if pc + 1 >= bytecode.len() { return None; }
                    let d = bytecode[pc] as usize;
                    (1, 0, Some(d), 2)
                }
                INSTR_INDIRECT_0 => (1, 1, None, 0),
                INSTR_INDIRECT_0_LOCAL_0 => (1, 0, Some(0), 0),
                INSTR_NO_OP => (0, 0, None, 0),
                INSTR_RESET_1 => (0, 1, None, 0),
                INSTR_RESET_2 => (0, 2, None, 0),
                INSTR_RESET_B => {
                    if pc >= bytecode.len() { return None; }
                    let n = bytecode[pc] as i32;
                    (0, n, None, 1)
                }
                INSTR_RESET_R_1 => (1, 2, None, 0),
                INSTR_RESET_R_2 => (1, 3, None, 0),
                INSTR_RESET_R_3 => (1, 4, None, 0),
                INSTR_JUMP_TAGGED_LOCAL => {
                    if pc + 1 >= bytecode.len() { return None; }
                    let d = bytecode[pc] as usize;
                    (0, 0, Some(d), 2)
                }
                INSTR_JUMP_NEQ_LOCAL | INSTR_JUMP_NEQ_LOCAL_IND => {
                    if pc + 2 >= bytecode.len() { return None; }
                    let d = bytecode[pc] as usize;
                    (0, 0, Some(d), 3)
                }
                INSTR_IS_TAGGED_LOCAL_B => {
                    if pc >= bytecode.len() { return None; }
                    let d = bytecode[pc] as usize;
                    (1, 0, Some(d), 1)
                }
                INSTR_CONST_ADDR8_0 | INSTR_CONST_ADDR8_1 => (1, 0, None, 1),
                INSTR_CALL_FAST_RTS0
                | INSTR_CALL_FAST_RTS1
                | INSTR_CALL_FAST_RTS2
                | INSTR_CALL_FAST_RTS3
                | INSTR_CALL_FAST_RTS4
                | INSTR_CALL_FAST_RTS5 => {
                    let n = (op - INSTR_CALL_FAST_RTS0) as i32;
                    (1, n + 1, None, 0)
                }
                INSTR_FIXED_ADD | INSTR_FIXED_SUB | INSTR_FIXED_MULT
                | INSTR_EQUAL_WORD | INSTR_LESS_SIGNED => (1, 2, None, 0),
                INSTR_JUMP8 | INSTR_JUMP_BACK8 => (0, 0, None, 1),
                INSTR_JUMP8_FALSE | INSTR_JUMP8_TRUE => (0, 1, None, 1),
                INSTR_RETURN_1 => (0, 1, None, 0),
                _ => {
                    // Unknown opcode — stop walking but return what
                    // we inferred from the prefix we did understand.
                    return Some((-min_depth).max(0) as usize);
                }
            };
        // Effects: peek doesn't move sp; pop then push for binops.
        if let Some(d) = peek_depth {
            // depth-relative read; conceptually requires depth > d.
            let needed = (d as i32) + 1;
            if depth < needed {
                min_depth = std::cmp::min(min_depth, depth - needed);
            }
        }
        for _ in 0..pop_count {
            depth -= 1;
            min_depth = std::cmp::min(min_depth, depth);
        }
        depth += push_count;
        pc += immediate_bytes;
    }
    Some((-min_depth).max(0) as usize)
}

fn scan_branch_targets(
    bytecode: &[u8],
) -> Result<std::collections::BTreeMap<usize, usize>, TranslateError> {
    let mut targets: std::collections::BTreeMap<usize, usize> =
        std::collections::BTreeMap::new();
    // depth_at[pc] = stack depth observed at the *start* of the
    // opcode at pc, used to validate that backward jumps land at
    // a position whose recorded depth matches the depth at the
    // jump source.
    let mut depth_at: Vec<Option<usize>> = vec![None; bytecode.len()];
    let (start_pc, prologue_arg_count) = function_prologue(bytecode);
    // If there's no enter-int prologue, infer arg count from peek
    // patterns in the bytecode itself.
    let arg_count = if prologue_arg_count > 0 || start_pc > 0 {
        prologue_arg_count
    } else {
        infer_arg_count(bytecode, start_pc).unwrap_or(0)
    };
    let mut depth: usize = arg_count;
    let mut pc = start_pc;
    let mut reachable = true;
    while pc < bytecode.len() {
        // If we just exited a terminator (returned/jumped) and now
        // re-enter at a recorded branch target, adopt that target's
        // depth as our new reachable depth. If we're at an
        // unreachable PC with no recorded target, skip ahead one
        // opcode worth of bytes.
        if !reachable {
            if let Some(&recorded) = targets.get(&pc) {
                depth = recorded;
                reachable = true;
            } else {
                pc += opcode_total_len(bytecode, pc)?;
                continue;
            }
        }
        depth_at[pc] = Some(depth);
        let op = bytecode[pc];
        pc += 1;
        match op {
            INSTR_CONST_0..=INSTR_CONST_4 => depth += 1,
            INSTR_CONST_10 => depth += 1,
            INSTR_LOCAL_0..=INSTR_LOCAL_7 => {
                let d = (op - INSTR_LOCAL_0) as usize;
                if d >= depth {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                depth += 1;
            }
            INSTR_LOCAL_B => {
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                let d = bytecode[pc] as usize;
                pc += 1;
                if d >= depth {
                    return Err(TranslateError::Underflow(pc - 2));
                }
                depth += 1;
            }
            INSTR_INDIRECT_LOCAL_B0
            | INSTR_INDIRECT_LOCAL_B1
            | INSTR_INDIRECT_CLOSURE_B0
            | INSTR_INDIRECT_CLOSURE_B1
            | INSTR_INDIRECT_CLOSURE_B2 => {
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                let d = bytecode[pc] as usize;
                pc += 1;
                if d >= depth {
                    return Err(TranslateError::Underflow(pc - 2));
                }
                depth += 1;
            }
            INSTR_INDIRECT_LOCAL_BB | INSTR_INDIRECT_CLOSURE_BB => {
                if pc + 1 >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                let d = bytecode[pc] as usize;
                pc += 2;
                if d >= depth {
                    return Err(TranslateError::Underflow(pc - 3));
                }
                depth += 1;
            }
            INSTR_JUMP_TAGGED_LOCAL => {
                // depth byte + off byte; conditional branch on the
                // tag-bit of sp[depth]. No pop. Both arms continue
                // at the same depth.
                if pc + 1 >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                let d = bytecode[pc] as usize;
                let off = bytecode[pc + 1] as usize;
                pc += 2;
                if d >= depth {
                    return Err(TranslateError::Underflow(pc - 3));
                }
                let taken = pc + off;
                record_target(&mut targets, taken, depth)?;
                record_target(&mut targets, pc, depth)?;
            }
            INSTR_IS_TAGGED_LOCAL_B => {
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                let d = bytecode[pc] as usize;
                pc += 1;
                if d >= depth {
                    return Err(TranslateError::Underflow(pc - 2));
                }
                depth += 1;
            }
            INSTR_JUMP_NEQ_LOCAL | INSTR_JUMP_NEQ_LOCAL_IND => {
                // [depth, want, off]; conditional branch, no stack
                // effect (peek only). Both arms continue at same depth.
                if pc + 2 >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                let d = bytecode[pc] as usize;
                let off = bytecode[pc + 2] as usize;
                pc += 3;
                if d >= depth {
                    return Err(TranslateError::Underflow(pc - 4));
                }
                let taken = pc + off;
                record_target(&mut targets, taken, depth)?;
                record_target(&mut targets, pc, depth)?;
            }
            INSTR_INDIRECT_0 => {
                if depth == 0 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                // peek+pop+push = net 0; actually pop top + push value
            }
            INSTR_INDIRECT_0_LOCAL_0 => {
                if depth == 0 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                depth += 1;
            }
            INSTR_NO_OP => {}
            INSTR_RESET_1 => {
                if depth == 0 { return Err(TranslateError::Underflow(pc - 1)); }
                depth -= 1;
            }
            INSTR_RESET_2 => {
                if depth < 2 { return Err(TranslateError::Underflow(pc - 1)); }
                depth -= 2;
            }
            INSTR_RESET_B => {
                if pc >= bytecode.len() { return Err(TranslateError::Truncated(pc)); }
                let n = bytecode[pc] as usize;
                pc += 1;
                if depth < n { return Err(TranslateError::Underflow(pc - 2)); }
                depth -= n;
            }
            INSTR_RESET_R_1 | INSTR_RESET_R_2 | INSTR_RESET_R_3 => {
                let n = match op {
                    INSTR_RESET_R_1 => 1,
                    INSTR_RESET_R_2 => 2,
                    _ => 3,
                };
                if depth < n + 1 { return Err(TranslateError::Underflow(pc - 1)); }
                depth -= n;
            }
            INSTR_CALL_FAST_RTS0
            | INSTR_CALL_FAST_RTS1
            | INSTR_CALL_FAST_RTS2
            | INSTR_CALL_FAST_RTS3
            | INSTR_CALL_FAST_RTS4
            | INSTR_CALL_FAST_RTS5 => {
                let n = (op - INSTR_CALL_FAST_RTS0) as usize;
                // Pop stub + N args; push 1 result. Net: -(N+1)+1 = -N.
                if depth < n + 1 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                depth = depth - n - 1 + 1;
            }
            INSTR_CONST_ADDR8_0 | INSTR_CONST_ADDR8_1 => {
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                pc += 1;
                depth += 1;
            }
            INSTR_CONST_INT_B => {
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                pc += 1;
                depth += 1;
            }
            INSTR_FIXED_ADD | INSTR_FIXED_SUB | INSTR_FIXED_MULT
            | INSTR_EQUAL_WORD | INSTR_LESS_SIGNED => {
                if depth < 2 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                depth -= 1;
            }
            INSTR_RETURN_1 => {
                if depth == 0 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                // Terminator. Subsequent bytes are unreachable on
                // this linear path; we re-enter only via a branch
                // target above.
                reachable = false;
            }
            INSTR_JUMP8 => {
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                let off = bytecode[pc] as usize;
                pc += 1;
                let target = pc + off;
                record_target(&mut targets, target, depth)?;
                reachable = false;
            }
            INSTR_JUMP_BACK8 => {
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                let off = bytecode[pc] as usize;
                pc += 1;
                // Our interpreter computes:
                //   self.pc_offset_signed(-((off + 2) as isize))
                // which corresponds to landing at pc - off - 2 in the
                // "PC after immediate" frame. Equivalently the target
                // is `(pc_post_imm) - off - 2`; with `pc` already
                // advanced past both the opcode and the immediate,
                // target = pc - off - 2.
                if pc < off + 2 {
                    return Err(TranslateError::Unsupported { op, at: pc - 2 });
                }
                let target = pc - off - 2;
                // Validate: the depth at the target (recorded earlier
                // during this same linear scan) must match the depth
                // here, since both sides of the back-edge share the
                // same Block.
                let expected = depth_at[target].ok_or(TranslateError::Unsupported {
                    op,
                    at: pc - 2,
                })?;
                if expected != depth {
                    return Err(TranslateError::Unsupported { op: 0xFE, at: target });
                }
                record_target(&mut targets, target, depth)?;
                reachable = false;
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

    /// Call a JitFn with no SML args (null pointer suffices for
    /// functions that don't read from `args_ptr`).
    fn call0(f: JitFn) -> i64 {
        unsafe { f(std::ptr::null()) }
    }

    /// Call a JitFn with the given SML args.
    fn call_with(f: JitFn, args: &[i64]) -> i64 {
        unsafe { f(args.as_ptr()) }
    }

    #[test]
    fn translate_const0_return() {
        // Bytecode: INSTR_CONST_0; INSTR_RETURN_1
        let bc = vec![INSTR_CONST_0, INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(call0(f)), 0);
    }

    #[test]
    fn translate_const_int_b_return() {
        // Bytecode: INSTR_CONST_INT_B 42; INSTR_RETURN_1
        let bc = vec![INSTR_CONST_INT_B, 42, INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(call0(f)), 42);
    }

    #[test]
    fn translate_const_int_b_negative() {
        // -7 as a signed byte is 0xF9.
        let bc = vec![INSTR_CONST_INT_B, 0xF9, INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(call0(f)), -7);
    }

    #[test]
    fn translate_multiple_constants_returns_top() {
        // Push 1, 2, 3, 4; return → top = 4
        let bc = vec![
            INSTR_CONST_1, INSTR_CONST_2, INSTR_CONST_3, INSTR_CONST_4, INSTR_RETURN_1,
        ];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(call0(f)), 4);
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
    fn translate_lone_return1_is_identity_function() {
        // Bare RETURN_1 = "return arg 0". The arg-inference pass
        // figures out the function takes 1 arg.
        let bc = vec![INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        let args = [tag(99)];
        let result = call_with(f, &args);
        assert_eq!(untag(result), 99);
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
        assert_eq!(untag(call0(f)), 3);
    }

    #[test]
    fn translate_fixed_sub_4_minus_1() {
        // push 4; push 1; SUB → y_n - x_n = 4 - 1 = 3
        let bc = vec![INSTR_CONST_4, INSTR_CONST_1, INSTR_FIXED_SUB, INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(call0(f)), 3);
    }

    #[test]
    fn translate_fixed_mult_3_times_4() {
        // push 3; push 4; MULT → 12
        let bc = vec![INSTR_CONST_3, INSTR_CONST_4, INSTR_FIXED_MULT, INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(call0(f)), 12);
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
        assert_eq!(untag(call0(f)), 19);
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
        assert_eq!(untag(call0(f)), -2);
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
        assert_eq!(untag(call0(f)), 4);
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
        assert_eq!(untag(call0(f)), 1);
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
        assert_eq!(untag(call0(f)), 2);
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
        assert_eq!(untag(call0(f)), 4);
    }

    #[test]
    fn translate_equal_word_matches() {
        // push 3; push 3; EQUAL → tagged 1 (true); return
        let bc = vec![INSTR_CONST_3, INSTR_CONST_3, INSTR_EQUAL_WORD, INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(call0(f)), 1);
    }

    #[test]
    fn translate_equal_word_mismatch() {
        let bc = vec![INSTR_CONST_2, INSTR_CONST_3, INSTR_EQUAL_WORD, INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(call0(f)), 0);
    }

    #[test]
    fn translate_less_signed() {
        // push y=2, push x=4, LESS_SIGNED → y<x → 2<4 → tagged 1
        let bc = vec![INSTR_CONST_2, INSTR_CONST_4, INSTR_LESS_SIGNED, INSTR_RETURN_1];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(call0(f)), 1);
    }

    #[test]
    fn translate_countdown_loop() {
        // SML pseudocode:
        //   var i = 4
        //   loop:
        //     if i == 0: exit
        //     i = i + (-1)
        //     goto loop
        //   return i  (= 0)
        //
        // Bytecode (depth at each PC noted in comments):
        //  0: CONST_4              ; depth: → 1
        //  1: ; ── loop head, depth = 1 ──
        //  1: CONST_0              ; → 2
        //  2: EQUAL_WORD           ; → 2 → after = depth 1? Wait.
        //     Actually we need the counter back on stack after the
        //     comparison. EQUAL_WORD POPS both operands and pushes
        //     the bool. So the counter is consumed. We need to dup
        //     it first... but we don't have a DUP opcode in our
        //     translator yet.
        //
        // Alternative: load CONST_4 each iteration is meaningless.
        // The simplest loop that exercises JUMP_BACK without needing
        // any new opcode beyond what we have is a degenerate loop
        // that always exits immediately:
        //
        //  0: CONST_3 ; counter = 3
        //  1: CONST_3 ; compare with 3
        //  2: EQUAL_WORD ; counter==3 → tagged 1 → truthy
        //  3: JUMP8_TRUE +2 ; if true, exit loop (jump fwd 2 → pc=7)
        //  5: JUMP_BACK8 5  ; else go back to loop head (pc-7=5? off=5)
        //                   ; pc here = 7 after immediate, off=5 →
        //                   ; target = 7 - 5 - 2 = 0. Lands at depth
        //                   ; 0, but we want to re-enter at depth 0.
        //                   ; Then CONST_3, CONST_3, EQUAL again.
        //  7: ; exit, stack depth = 0
        //  7: CONST_4
        //  8: RETURN_1
        //
        // Since the test is always-equal, the loop exits on first iteration.
        let bc = vec![
            INSTR_CONST_3,        // 0
            INSTR_CONST_3,        // 1
            INSTR_EQUAL_WORD,     // 2
            INSTR_JUMP8_TRUE, 2,  // 3..5, target = 5 + 2 = 7
            INSTR_JUMP_BACK8, 5,  // 5..7, target = 7 - 5 - 2 = 0
            INSTR_CONST_4,        // 7
            INSTR_RETURN_1,       // 8
        ];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(call0(f)), 4);
    }

    #[test]
    fn translate_local_0_duplicates_top() {
        // push 7; LOCAL_0 (= dup top); ADD; return → 14
        let bc = vec![
            INSTR_CONST_INT_B, 7, INSTR_LOCAL_0, INSTR_FIXED_ADD, INSTR_RETURN_1,
        ];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(call0(f)), 14);
    }

    #[test]
    fn translate_local_b_with_explicit_depth() {
        // push 1, 2, 3; LOCAL_B 2 (= peek depth 2 = the "1"); return
        let bc = vec![
            INSTR_CONST_1, INSTR_CONST_2, INSTR_CONST_3,
            INSTR_LOCAL_B, 2,
            INSTR_RETURN_1,
        ];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(call0(f)), 1);
    }

    #[test]
    fn translate_local_2_skipping_two_above() {
        // push 5, 6, 7; LOCAL_2 (= peek 2 down = "5"); ADD → 12
        let bc = vec![
            INSTR_CONST_INT_B, 5, INSTR_CONST_INT_B, 6, INSTR_CONST_INT_B, 7,
            0x2b, // INSTR_LOCAL_2
            INSTR_FIXED_ADD,
            INSTR_RETURN_1,
        ];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        assert_eq!(untag(call0(f)), 12);
    }

    #[test]
    fn translate_indirect_local_b0_compiles() {
        // We can't easily synthesize a real heap pointer in
        // bytecode (CONST_INT_B is signed-byte only), so this test
        // just verifies the translation pipeline accepts the opcode
        // pattern without errors. End-to-end execution lives in
        // the integration test that runs real bootstrap code.
        let bc = vec![
            INSTR_CONST_0,         // push a value (won't be deref'd)
            INSTR_INDIRECT_LOCAL_B0, 0,
            INSTR_RETURN_1,
        ];
        let mut jit = Jit::new().unwrap();
        let _f = compile(&mut jit, &bc).expect("compile must succeed");
        // We don't call _f() — it would deref tagged(0) as a pointer
        // and segfault. Pure compile-time test.
    }

    #[test]
    fn translate_indirect_closure_compiles() {
        let bc = vec![
            INSTR_CONST_1,
            INSTR_INDIRECT_CLOSURE_B0, 0,
            INSTR_RETURN_1,
        ];
        let mut jit = Jit::new().unwrap();
        let _f = compile(&mut jit, &bc).expect("compile must succeed");
    }

    #[test]
    fn translate_rejects_missing_return() {
        let bc = vec![INSTR_CONST_0];
        let mut jit = Jit::new().unwrap();
        let err = compile(&mut jit, &bc).unwrap_err();
        assert!(matches!(err, TranslateError::FellOffEnd), "got {err:?}");
    }
}
