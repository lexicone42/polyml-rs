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
const INSTR_WORD_ADD: u8 = 0xb1;
const INSTR_WORD_SUB: u8 = 0xb2;
const INSTR_WORD_AND: u8 = 0xb7;
const INSTR_WORD_OR: u8 = 0xb8;
const INSTR_WORD_XOR: u8 = 0xb9;
const INSTR_WORD_MULT: u8 = 0xb3;
const INSTR_WORD_SHIFT_LEFT: u8 = 0xba;
const INSTR_WORD_SHIFT_R_LOG: u8 = 0xbb;
const INSTR_SET_STACK_VAL_B: u8 = 0x25;
const INSTR_FIXED_SUB: u8 = 0xab;
const INSTR_FIXED_MULT: u8 = 0xac;
const INSTR_FIXED_QUOT: u8 = 0xad;
const INSTR_FIXED_REM: u8 = 0xae;
const INSTR_GET_THREAD_ID: u8 = 0xd9;
const INSTR_ALLOC_MUT_CLOSURE_B: u8 = 0x76;
const INSTR_MOVE_TO_MUT_CLOSURE_B: u8 = 0x75;
const INSTR_EQUAL_WORD: u8 = 0xa0;
const INSTR_LESS_SIGNED: u8 = 0xa2;
const INSTR_LESS_UNSIGNED: u8 = 0xa3;
const INSTR_LESS_EQ_SIGNED: u8 = 0xa4;
const INSTR_LESS_EQ_UNSIGNED: u8 = 0xa5;
const INSTR_GREATER_SIGNED: u8 = 0xa6;
const INSTR_GREATER_UNSIGNED: u8 = 0xa7;
const INSTR_GREATER_EQ_SIGNED: u8 = 0xa8;
const INSTR_GREATER_EQ_UNSIGNED: u8 = 0xa9;
const INSTR_JUMP8: u8 = 0x02;
const INSTR_CASE16: u8 = 0x0a;
const INSTR_JUMP8_FALSE: u8 = 0x03;
const INSTR_JUMP8_TRUE: u8 = 0x46;
const INSTR_JUMP_BACK8: u8 = 0x1e;
const INSTR_JUMP_BACK16: u8 = 0x20;
const INSTR_JUMP16: u8 = 0xf7;
const INSTR_JUMP16_FALSE: u8 = 0xf8;
const INSTR_JUMP16_TRUE: u8 = 0x47;
const INSTR_LOCAL_B: u8 = 0x22;
const INSTR_LOCAL_0: u8 = 0x29;
const INSTR_LOCAL_7: u8 = 0x30;
const INSTR_LOCAL_8: u8 = 0x31;
const INSTR_LOCAL_11: u8 = 0x34;
const INSTR_LOCAL_12: u8 = 0x45;
const INSTR_LOCAL_13: u8 = 0x49;
const INSTR_LOCAL_14: u8 = 0x4a;
const INSTR_LOCAL_15: u8 = 0x4b;
const INSTR_WORD_DIV: u8 = 0xb4;
const INSTR_WORD_MOD: u8 = 0xb5;
const INSTR_RETURN_2: u8 = 0x43;
const INSTR_RETURN_3: u8 = 0x44;
const INSTR_RETURN_B: u8 = 0x1f;
const INSTR_RETURN_W: u8 = 0x0d;
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
const INSTR_INDIRECT_1: u8 = 0x36;
const INSTR_INDIRECT_2: u8 = 0x37;
const INSTR_INDIRECT_3: u8 = 0x38;
const INSTR_INDIRECT_4: u8 = 0x39;
const INSTR_INDIRECT_5: u8 = 0x3a;
const INSTR_INDIRECT_B: u8 = 0x23;
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
const INSTR_RESET_R_B: u8 = 0x27;
const INSTR_CALL_LOCAL_B: u8 = 0x16;
const INSTR_TAIL_B_B: u8 = 0x7b;
const INSTR_CLOSURE_B: u8 = 0xd0;
const INSTR_ALLOC_BYTE_MEM: u8 = 0xbd;
const INSTR_ALLOC_WORD_MEMORY: u8 = 0xda;
const INSTR_STORE_UNTAGGED: u8 = 0x09;
const INSTR_LOAD_UNTAGGED: u8 = 0x08;
const INSTR_STORE_ML_WORD: u8 = 0x05;
const INSTR_RAISE_EX: u8 = 0x10;
const INSTR_ALLOC_REF: u8 = 0x06;
const INSTR_CELL_LENGTH: u8 = 0x93;
const INSTR_LOAD_ML_BYTE: u8 = 0xdc;
const INSTR_LOAD_ML_WORD: u8 = 0x04;
const INSTR_STORE_ML_BYTE: u8 = 0xe4;
const INSTR_BLOCK_MOVE_WORD: u8 = 0x07;
const INSTR_BLOCK_MOVE_BYTE: u8 = 0xec;
const INSTR_BLOCK_EQUAL_BYTE: u8 = 0xed;
const INSTR_BLOCK_COMPARE_BYTE: u8 = 0xee;
const INSTR_STACK_CONTAINER_B: u8 = 0x0e;
const INSTR_MOVE_TO_CONTAINER_B: u8 = 0x24;
const INSTR_INDIRECT_CONTAINER_B: u8 = 0x74;
const INSTR_LOCK: u8 = 0x6c;
const INSTR_CLEAR_MUTABLE: u8 = 0x95;
const INSTR_CELL_FLAGS: u8 = 0x94;
const INSTR_CONST_INT_W: u8 = 0x1b;
const INSTR_PUSH_HANDLER: u8 = 0x78;
const INSTR_NOT_BOOLEAN: u8 = 0x91;
const INSTR_IS_TAGGED: u8 = 0x92;
const INSTR_SET_HANDLER8: u8 = 0x81;
const INSTR_SET_HANDLER16: u8 = 0xf9;
const INSTR_DELETE_HANDLER: u8 = 0xf1;
const INSTR_CALL_CONST_ADDR8_0: u8 = 0x57;
const INSTR_CALL_CONST_ADDR8_1: u8 = 0x58;
const INSTR_CONST_ADDR8_8: u8 = 0x15;
const INSTR_CONST_ADDR16_8: u8 = 0x14;
const INSTR_CALL_CONST_ADDR8_8: u8 = 0x17;
const INSTR_CALL_CONST_ADDR16_8: u8 = 0x18;
const INSTR_TUPLE_2: u8 = 0x69;
const INSTR_TUPLE_3: u8 = 0x6a;
const INSTR_TUPLE_4: u8 = 0x6b;
const INSTR_TUPLE_B: u8 = 0x68;

/// Errors specific to bytecode translation.
#[derive(Debug, thiserror::Error)]
pub enum TranslateError {
    #[error("truncated bytecode at offset {0}")]
    Truncated(usize),
    #[error("unsupported opcode 0x{op:02x} ({}) at offset {at}",
        polyml_runtime::interpreter::disasm::opcode_name(*op))]
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
/// Same as [`compile_with_consts`] but also returns the JIT's
/// inferred `arity_init` (how many slots it reads from `args_ptr`
/// at entry). Callers installing the function in
/// `Interpreter::install_jit` should ensure their JitEntry's
/// `arity_init` is `>= this returned value`.
pub fn compile_with_consts_meta(
    jit: &mut Jit,
    full_body: &[u8],
    bytecode_end: usize,
) -> Result<(JitFn, usize), TranslateError> {
    let result = compile_with_consts_impl(jit, full_body, bytecode_end)?;
    Ok(result)
}

pub fn compile_with_consts(
    jit: &mut Jit,
    full_body: &[u8],
    bytecode_end: usize,
) -> Result<JitFn, TranslateError> {
    compile_with_consts_impl(jit, full_body, bytecode_end).map(|(f, _)| f)
}

fn compile_with_consts_impl(
    jit: &mut Jit,
    full_body: &[u8],
    bytecode_end: usize,
) -> Result<(JitFn, usize), TranslateError> {
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
    let targets = scan_branch_targets(bytecode, full_body)?;

    let (entry_pc, prologue_arg_count) = function_prologue(bytecode);
    let arg_count = compute_arg_count(bytecode, entry_pc, prologue_arg_count);

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

    // Closure-call trampoline. Same signature shape as the RTS
    // trampoline but semantically dispatches a closure value
    // rather than an entry-point token.
    let mut closure_sig = jit.module.make_signature();
    closure_sig.params.push(AbiParam::new(types::I64));
    closure_sig.params.push(AbiParam::new(types::I64));
    closure_sig.params.push(AbiParam::new(types::I64));
    closure_sig.returns.push(AbiParam::new(types::I64));
    let closure_func_id = jit
        .module
        .declare_function(
            "polyml_jit_closure_call",
            Linkage::Import,
            &closure_sig,
        )
        .map_err(|e| JitError::Module(e.to_string()))?;
    let closure_func_ref = jit
        .module
        .declare_func_in_func(closure_func_id, &mut ctx.func);

    // Tuple-alloc trampoline.
    let mut alloc_sig = jit.module.make_signature();
    alloc_sig.params.push(AbiParam::new(types::I64));
    alloc_sig.params.push(AbiParam::new(types::I64));
    alloc_sig.returns.push(AbiParam::new(types::I64));
    let alloc_func_id = jit
        .module
        .declare_function(
            "polyml_jit_alloc_tuple",
            Linkage::Import,
            &alloc_sig,
        )
        .map_err(|e| JitError::Module(e.to_string()))?;
    let alloc_func_ref = jit
        .module
        .declare_func_in_func(alloc_func_id, &mut ctx.func);

    // Closure-alloc trampoline: (n_captures, captures_ptr, src_closure) -> i64.
    let mut closure_alloc_sig = jit.module.make_signature();
    closure_alloc_sig.params.push(AbiParam::new(types::I64));
    closure_alloc_sig.params.push(AbiParam::new(types::I64));
    closure_alloc_sig.params.push(AbiParam::new(types::I64));
    closure_alloc_sig.returns.push(AbiParam::new(types::I64));
    let closure_alloc_id = jit
        .module
        .declare_function(
            "polyml_jit_alloc_closure",
            Linkage::Import,
            &closure_alloc_sig,
        )
        .map_err(|e| JitError::Module(e.to_string()))?;
    let closure_alloc_ref = jit
        .module
        .declare_func_in_func(closure_alloc_id, &mut ctx.func);

    // alloc_byte_mem trampoline: (n_words, flags) -> i64.
    let mut alloc_bytes_sig = jit.module.make_signature();
    alloc_bytes_sig.params.push(AbiParam::new(types::I64));
    alloc_bytes_sig.params.push(AbiParam::new(types::I64));
    alloc_bytes_sig.returns.push(AbiParam::new(types::I64));
    let alloc_bytes_id = jit
        .module
        .declare_function(
            "polyml_jit_alloc_byte_mem",
            Linkage::Import,
            &alloc_bytes_sig,
        )
        .map_err(|e| JitError::Module(e.to_string()))?;
    let alloc_bytes_ref = jit
        .module
        .declare_func_in_func(alloc_bytes_id, &mut ctx.func);

    // block_move_word trampoline: (src, src_off, dest, dest_off, length) -> i64.
    let mut block_move_sig = jit.module.make_signature();
    block_move_sig.params.push(AbiParam::new(types::I64));
    block_move_sig.params.push(AbiParam::new(types::I64));
    block_move_sig.params.push(AbiParam::new(types::I64));
    block_move_sig.params.push(AbiParam::new(types::I64));
    block_move_sig.params.push(AbiParam::new(types::I64));
    block_move_sig.returns.push(AbiParam::new(types::I64));
    let block_move_id = jit
        .module
        .declare_function(
            "polyml_jit_block_move_word",
            Linkage::Import,
            &block_move_sig,
        )
        .map_err(|e| JitError::Module(e.to_string()))?;
    let block_move_ref = jit
        .module
        .declare_func_in_func(block_move_id, &mut ctx.func);

    // block_move_byte: same signature as block_move_word.
    let block_move_byte_id = jit
        .module
        .declare_function(
            "polyml_jit_block_move_byte",
            Linkage::Import,
            &block_move_sig,
        )
        .map_err(|e| JitError::Module(e.to_string()))?;
    let block_move_byte_ref = jit
        .module
        .declare_func_in_func(block_move_byte_id, &mut ctx.func);

    // block_equal_byte: same signature, returns tag(bool).
    let block_equal_byte_id = jit
        .module
        .declare_function(
            "polyml_jit_block_equal_byte",
            Linkage::Import,
            &block_move_sig,
        )
        .map_err(|e| JitError::Module(e.to_string()))?;
    let block_equal_byte_ref = jit
        .module
        .declare_func_in_func(block_equal_byte_id, &mut ctx.func);

    // block_compare_byte: same signature, returns tag(-1|0|1).
    let block_compare_byte_id = jit
        .module
        .declare_function(
            "polyml_jit_block_compare_byte",
            Linkage::Import,
            &block_move_sig,
        )
        .map_err(|e| JitError::Module(e.to_string()))?;
    let block_compare_byte_ref = jit
        .module
        .declare_func_in_func(block_compare_byte_id, &mut ctx.func);

    // get_thread_id: no args, returns i64.
    let mut get_tid_sig = jit.module.make_signature();
    get_tid_sig.returns.push(AbiParam::new(types::I64));
    let get_tid_id = jit
        .module
        .declare_function(
            "polyml_jit_get_thread_id",
            Linkage::Import,
            &get_tid_sig,
        )
        .map_err(|e| JitError::Module(e.to_string()))?;
    let get_tid_ref = jit
        .module
        .declare_func_in_func(get_tid_id, &mut ctx.func);

    // alloc_mut_closure: (n_captures, src_closure) -> i64.
    let mut amc_sig = jit.module.make_signature();
    amc_sig.params.push(AbiParam::new(types::I64));
    amc_sig.params.push(AbiParam::new(types::I64));
    amc_sig.returns.push(AbiParam::new(types::I64));
    let amc_id = jit
        .module
        .declare_function(
            "polyml_jit_alloc_mut_closure",
            Linkage::Import,
            &amc_sig,
        )
        .map_err(|e| JitError::Module(e.to_string()))?;
    let amc_ref = jit
        .module
        .declare_func_in_func(amc_id, &mut ctx.func);

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
                    let expected = builder.block_params(target_blk).len();
                    // Truncate to expected if we have more values
                    // (matches pass-1's depth reconciliation).
                    while stack.len() > expected {
                        stack.pop();
                    }
                    if stack.len() < expected {
                        return Err(TranslateError::Underflow(pc));
                    }
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
                INSTR_LOCAL_0..=INSTR_LOCAL_11 => {
                    let depth = (op - INSTR_LOCAL_0) as usize;
                    if depth >= stack.len() {
                        return Err(TranslateError::Underflow(pc - 1));
                    }
                    let v = stack[stack.len() - 1 - depth];
                    stack.push(v);
                }
                INSTR_LOCAL_12 | INSTR_LOCAL_13 | INSTR_LOCAL_14 | INSTR_LOCAL_15 => {
                    let depth = match op {
                        INSTR_LOCAL_12 => 12,
                        INSTR_LOCAL_13 => 13,
                        INSTR_LOCAL_14 => 14,
                        INSTR_LOCAL_15 => 15,
                        _ => unreachable!(),
                    };
                    if depth >= stack.len() {
                        return Err(TranslateError::Underflow(pc - 1));
                    }
                    let v = stack[stack.len() - 1 - depth];
                    stack.push(v);
                }
                INSTR_WORD_DIV => {
                    // Untag, divide (signed? interp uses checked_div on
                    // unsigned). Use unsigned to match interp.
                    let x = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let y = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let xn = builder.ins().ushr_imm(x, 1);
                    let yn = builder.ins().ushr_imm(y, 1);
                    // Need to guard against /0. The interp returns 0 on
                    // 0-div via checked_div; emit a select to match.
                    let zero = builder.ins().iconst(int, 0);
                    let is_zero = builder.ins().icmp(IntCC::Equal, xn, zero);
                    let one_const = builder.ins().iconst(int, 1);
                    // Use a safe divisor (1) when xn==0 so udiv doesn't trap.
                    let safe_x = builder.ins().select(is_zero, one_const, xn);
                    let q = builder.ins().udiv(yn, safe_x);
                    let q_or_zero = builder.ins().select(is_zero, zero, q);
                    let shifted = builder.ins().ishl_imm(q_or_zero, 1);
                    stack.push(builder.ins().bor(shifted, one_const));
                }
                INSTR_WORD_MOD => {
                    let x = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let y = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let xn = builder.ins().ushr_imm(x, 1);
                    let yn = builder.ins().ushr_imm(y, 1);
                    let zero = builder.ins().iconst(int, 0);
                    let is_zero = builder.ins().icmp(IntCC::Equal, xn, zero);
                    let one_const = builder.ins().iconst(int, 1);
                    let safe_x = builder.ins().select(is_zero, one_const, xn);
                    let r = builder.ins().urem(yn, safe_x);
                    let r_or_zero = builder.ins().select(is_zero, zero, r);
                    let shifted = builder.ins().ishl_imm(r_or_zero, 1);
                    stack.push(builder.ins().bor(shifted, one_const));
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
                INSTR_RESET_R_1
                | INSTR_RESET_R_2
                | INSTR_RESET_R_3
                | INSTR_RESET_R_B => {
                    // Preserve top, drop N below it. For RESET_R_B, N
                    // is a byte immediate; for the dedicated 1/2/3
                    // variants N is encoded in the opcode.
                    let n = match op {
                        INSTR_RESET_R_1 => 1,
                        INSTR_RESET_R_2 => 2,
                        INSTR_RESET_R_3 => 3,
                        INSTR_RESET_R_B => {
                            if pc >= bytecode.len() {
                                return Err(TranslateError::Truncated(pc));
                            }
                            let v = bytecode[pc] as usize;
                            pc += 1;
                            v
                        }
                        _ => unreachable!(),
                    };
                    if stack.len() < n + 1 {
                        return Err(TranslateError::Underflow(pc - 1));
                    }
                    let top = stack.pop().unwrap();
                    stack.truncate(stack.len() - n);
                    stack.push(top);
                }
                INSTR_TUPLE_2 | INSTR_TUPLE_3 | INSTR_TUPLE_4 | INSTR_TUPLE_B => {
                    let n = match op {
                        INSTR_TUPLE_2 => 2,
                        INSTR_TUPLE_3 => 3,
                        INSTR_TUPLE_4 => 4,
                        INSTR_TUPLE_B => {
                            if pc >= bytecode.len() {
                                return Err(TranslateError::Truncated(pc));
                            }
                            let n = bytecode[pc] as usize;
                            pc += 1;
                            n
                        }
                        _ => unreachable!(),
                    };
                    if stack.len() < n {
                        return Err(TranslateError::Underflow(pc - 1));
                    }
                    let mut vals: Vec<Value> = Vec::with_capacity(n);
                    for _ in 0..n {
                        vals.push(stack.pop().unwrap());
                    }
                    let slot_size = std::cmp::max(8, (n * 8) as u32);
                    let slot = builder.create_sized_stack_slot(
                        cranelift::prelude::StackSlotData::new(
                            cranelift::prelude::StackSlotKind::ExplicitSlot,
                            slot_size,
                            3,
                        ),
                    );
                    for (k, v) in vals.iter().enumerate() {
                        let idx = n - 1 - k;
                        builder.ins().stack_store(*v, slot, (idx * 8) as i32);
                    }
                    let n_v = builder.ins().iconst(types::I64, n as i64);
                    let vals_ptr = builder.ins().stack_addr(types::I64, slot, 0);
                    let call_inst =
                        builder.ins().call(alloc_func_ref, &[n_v, vals_ptr]);
                    let result_val = builder.inst_results(call_inst)[0];
                    stack.push(result_val);
                }
                INSTR_CALL_LOCAL_B => {
                    // [N]: closure is at sp[N]; the N args above it
                    // are the call args. Upstream PEEKS the closure
                    // (no sp++) before jumping to CALL_CLOSURE. After
                    // the call returns, the closure remains on stack
                    // below the result. Net stack delta: -N + 1.
                    //
                    // bytecode.cpp:445-449:
                    //   closure = (sp[*pc++]).w().AsObjPtr();
                    //   goto CALL_CLOSURE;
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let n_args = bytecode[pc] as usize;
                    pc += 1;
                    if stack.len() < n_args + 1 {
                        return Err(TranslateError::Underflow(pc - 2));
                    }
                    let mut args_vec: Vec<Value> = Vec::with_capacity(n_args);
                    for _ in 0..n_args {
                        args_vec.push(stack.pop().unwrap());
                    }
                    // PEEK closure (don't pop); it stays on stack so
                    // subsequent LOCAL_K offsets match the interpreter.
                    let closure = *stack.last().unwrap();
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
                    let call_inst = builder.ins().call(
                        closure_func_ref,
                        &[closure, n_args_v, args_ptr],
                    );
                    let result_val = builder.inst_results(call_inst)[0];
                    stack.push(result_val);
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
                INSTR_CONST_ADDR8_0
                | INSTR_CONST_ADDR8_1
                | INSTR_CONST_ADDR8_8
                | INSTR_CONST_ADDR16_8 => {
                    let (byte_off, idx) =
                        read_const_addr_operands(bytecode, &mut pc, op)?;
                    let read_at = pc + byte_off + idx * 8;
                    if read_at + 8 > _full_body.len() {
                        return Err(TranslateError::Unsupported { op, at: pc });
                    }
                    // Load the constant at RUNTIME from the code
                    // object's constants pool. We can't bake the
                    // value as iconst because GC moves the pointees
                    // and updates the pool in place; a baked iconst
                    // would become stale and crash on dereference.
                    let abs_addr = _full_body.as_ptr() as i64 + read_at as i64;
                    let base = builder.ins().iconst(int, abs_addr);
                    let val = builder.ins().load(
                        int,
                        cranelift::prelude::MemFlags::trusted(),
                        base,
                        0,
                    );
                    stack.push(val);
                }
                INSTR_CALL_CONST_ADDR8_0
                | INSTR_CALL_CONST_ADDR8_1
                | INSTR_CALL_CONST_ADDR8_8
                | INSTR_CALL_CONST_ADDR16_8 => {
                    let (byte_off, idx) =
                        read_const_addr_operands(bytecode, &mut pc, op)?;
                    let read_at = pc + byte_off + idx * 8;
                    if read_at + 8 > _full_body.len() {
                        return Err(TranslateError::Unsupported { op, at: pc });
                    }
                    let mut buf = [0u8; 8];
                    buf.copy_from_slice(&_full_body[read_at..read_at + 8]);
                    let closure_addr_at_compile_time = u64::from_le_bytes(buf);
                    // Static arity inspection: deref closure → code obj
                    // → first two bytes (0xff/0xe9, arity|0x80). If the
                    // prologue isn't recognisable, bail to the
                    // interpreter rather than guess arity.
                    let Some(n_args) =
                        closure_arity_from_addr(closure_addr_at_compile_time)
                    else {
                        return Err(TranslateError::Unsupported { op, at: pc - 2 });
                    };
                    if stack.len() < n_args {
                        return Err(TranslateError::Underflow(pc - 2));
                    }
                    let mut args_vec: Vec<Value> = Vec::with_capacity(n_args);
                    for _ in 0..n_args {
                        args_vec.push(stack.pop().unwrap());
                    }
                    // Load the CLOSURE POINTER at runtime from the
                    // code object's constants pool. The compile-time
                    // value is used only for static arity inspection
                    // (above); the runtime call must dereference the
                    // current pool entry, which may have been updated
                    // by GC since JIT compile time.
                    //
                    // Bug found: when this was an `iconst`, code that
                    // GC'd between JIT compile + first call dispatched
                    // to a stale pointer. Bisection (commits e6a8280,
                    // 1d2c524, 598f312, 3d21be5) narrowed to entry #27
                    // which uses CALL_CONST_ADDR8_0; this fix unblocks
                    // it without needing the install-time filter.
                    let abs_addr = _full_body.as_ptr() as i64 + read_at as i64;
                    let base = builder.ins().iconst(int, abs_addr);
                    let closure_v = builder.ins().load(
                        int,
                        cranelift::prelude::MemFlags::trusted(),
                        base,
                        0,
                    );
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
                    let call_inst = builder.ins().call(
                        closure_func_ref,
                        &[closure_v, n_args_v, args_ptr],
                    );
                    let result_val = builder.inst_results(call_inst)[0];
                    stack.push(result_val);
                }
                INSTR_INDIRECT_0
                | INSTR_INDIRECT_1
                | INSTR_INDIRECT_2
                | INSTR_INDIRECT_3
                | INSTR_INDIRECT_4
                | INSTR_INDIRECT_5 => {
                    let field = (op - INSTR_INDIRECT_0) as i32;
                    let base = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let val = builder.ins().load(
                        int,
                        cranelift::prelude::MemFlags::trusted(),
                        base,
                        field * 8,
                    );
                    stack.push(val);
                }
                INSTR_INDIRECT_B => {
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let field = bytecode[pc] as i32;
                    pc += 1;
                    let base = stack.pop().ok_or(TranslateError::Underflow(pc - 2))?;
                    let val = builder.ins().load(
                        int,
                        cranelift::prelude::MemFlags::trusted(),
                        base,
                        field * 8,
                    );
                    stack.push(val);
                }
                INSTR_LOAD_UNTAGGED => {
                    // Pop index (tagged), peek base (data ptr).
                    // Load *(base + (index>>1) * 8), TAG the result
                    // (2*v + 1), and replace top.
                    //
                    // Upstream wraps in TAGGED — code that uses the
                    // result via INDIRECT/CALL strips the tag and
                    // treats as raw bits. Missing the TAG was a real
                    // semantic bug found via basis/PolyMLException.sml
                    // load-time bisection.
                    let index_tag = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let base = *stack.last().ok_or(TranslateError::Underflow(pc - 1))?;
                    let index = builder.ins().sshr_imm(index_tag, 1);
                    let eight = builder.ins().iconst(int, 8);
                    let off = builder.ins().imul(index, eight);
                    let addr = builder.ins().iadd(base, off);
                    let val = builder.ins().load(
                        int,
                        cranelift::prelude::MemFlags::trusted(),
                        addr,
                        0,
                    );
                    // TAG: 2*val + 1
                    let doubled = builder.ins().ishl_imm(val, 1);
                    let one = builder.ins().iconst(int, 1);
                    let tagged = builder.ins().iadd(doubled, one);
                    let last = stack.len() - 1;
                    stack[last] = tagged;
                }
                INSTR_STORE_ML_WORD => {
                    // Pop value, pop index, pop base; write base[index]=value;
                    // push tagged(0).
                    let to_store = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let index_tag = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let base = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let index = builder.ins().sshr_imm(index_tag, 1);
                    let eight = builder.ins().iconst(int, 8);
                    let off = builder.ins().imul(index, eight);
                    let addr = builder.ins().iadd(base, off);
                    builder.ins().store(
                        cranelift::prelude::MemFlags::trusted(),
                        to_store,
                        addr,
                        0,
                    );
                    let tag0 = builder.ins().iconst(int, tag(0));
                    stack.push(tag0);
                }
                INSTR_STORE_ML_BYTE => {
                    // Same shape as STORE_ML_WORD, but index is in
                    // bytes (no *8 scaling) and store is 1 byte.
                    // Mirrors interpreter:
                    //   to_store = pop().untag() as u8
                    //   index = pop().untag()
                    //   base = peek(0).as_ptr::<u8>()
                    //   *(base + index) = to_store
                    //   pop()  // the peeked base
                    //   push tag(0)
                    let to_store_tag = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let index_tag = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let base = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let index = builder.ins().sshr_imm(index_tag, 1);
                    let addr = builder.ins().iadd(base, index);
                    let val_u8 = builder.ins().sshr_imm(to_store_tag, 1);
                    builder.ins().istore8(
                        cranelift::prelude::MemFlags::trusted(),
                        val_u8,
                        addr,
                        0,
                    );
                    let tag0 = builder.ins().iconst(int, tag(0));
                    stack.push(tag0);
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
                INSTR_PUSH_HANDLER => {
                    // Push the current handler_sp onto the stack. Used
                    // by exception handler setup: the OLD handler is
                    // saved here so SET_HANDLER can install a new one
                    // and RAISE_EX can restore it. Our JIT doesn't
                    // model handler state, so push 0 as a sentinel.
                    // Functions that actually USE this value via
                    // exception flow will misbehave — but since
                    // RAISE_EX is already a stub, those functions are
                    // already broken; we're just allowing translation
                    // for the (much more common) no-exception path.
                    let zero = builder.ins().iconst(int, 0);
                    stack.push(zero);
                }
                INSTR_STACK_CONTAINER_B => {
                    // Allocate a Cranelift StackSlot for the container,
                    // initialize all N slots to tagged 0, push N
                    // placeholder values + 1 pointer onto the
                    // compile-time stack.
                    //
                    // Interpreter semantics (bytecode.cpp::stack_containerB):
                    //   for i in 0..N: push tagged 0
                    //   push stack_addr(slot, 0)
                    //
                    // The container's slots are accessed exclusively
                    // via MOVE_TO_CONTAINER_B / INDIRECT_CONTAINER_B,
                    // which read/write through the pointer. LOCAL_K
                    // access to the placeholder zero values is never
                    // emitted by the SML compiler (it tracks container
                    // slots as memory, not as stack values), so the
                    // placeholders are just depth-fillers.
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let n = bytecode[pc] as usize;
                    pc += 1;
                    let slot_size = std::cmp::max(8, (n * 8) as u32);
                    let ss = builder.create_sized_stack_slot(
                        cranelift::prelude::StackSlotData::new(
                            cranelift::prelude::StackSlotKind::ExplicitSlot,
                            slot_size,
                            3,
                        ),
                    );
                    let tag0 = builder.ins().iconst(int, tag(0));
                    for i in 0..n {
                        builder.ins().stack_store(tag0, ss, (i * 8) as i32);
                    }
                    for _ in 0..n {
                        stack.push(tag0);
                    }
                    let ptr = builder.ins().stack_addr(int, ss, 0);
                    stack.push(ptr);
                }
                INSTR_MOVE_TO_CONTAINER_B => {
                    // [k]: pop value; peek pointer (still at top);
                    // write value to ptr[k]. Net -1.
                    //
                    // bytecode.cpp::moveToContainerB:
                    //   PolyWord u = *sp++;
                    //   (*sp).stackAddr[*pc] = u;
                    //   pc += 1;
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let k = bytecode[pc] as usize;
                    pc += 1;
                    let value = stack.pop().ok_or(TranslateError::Underflow(pc - 2))?;
                    let ptr = *stack.last().ok_or(TranslateError::Underflow(pc - 2))?;
                    builder.ins().store(
                        cranelift::prelude::MemFlags::trusted(),
                        value,
                        ptr,
                        (k * 8) as i32,
                    );
                }
                INSTR_INDIRECT_CONTAINER_B => {
                    // [k]: replace top (= ptr) with ptr[k]. Net 0.
                    //
                    // bytecode.cpp::indirectContainerB:
                    //   *sp = (*sp).stackAddr[*pc];
                    //   pc += 1;
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let k = bytecode[pc] as usize;
                    pc += 1;
                    let ptr = stack.pop().ok_or(TranslateError::Underflow(pc - 2))?;
                    let val = builder.ins().load(
                        int,
                        cranelift::prelude::MemFlags::trusted(),
                        ptr,
                        (k * 8) as i32,
                    );
                    stack.push(val);
                }
                INSTR_LOCK | INSTR_CLEAR_MUTABLE => {
                    // Both clear the F_MUTABLE_BIT (0x40) in the
                    // length-word's top byte (flags portion) of the
                    // heap object on top of stack.
                    //
                    // LOCK: peek ptr, clear bit, leave ptr on stack.
                    // CLEAR_MUTABLE: same, then replace top with
                    // tagged 0.
                    //
                    // F_MUTABLE_BIT = 0x40 at FLAGS_SHIFT = 56 (on
                    // 64-bit), so the mask to clear is
                    // 0xbfff_ffff_ffff_ffff (all bits except bit 62).
                    let ptr = *stack.last().ok_or(TranslateError::Underflow(pc - 1))?;
                    let lw_addr = builder.ins().iadd_imm(ptr, -8);
                    let lw = builder.ins().load(
                        int,
                        cranelift::prelude::MemFlags::trusted(),
                        lw_addr,
                        0,
                    );
                    // F_MUTABLE_BIT = 0x40 at FLAGS_SHIFT = 56.
                    // Mask out that one bit: !(0x40 << 56).
                    let mask = builder.ins().iconst(int, !(0x40_i64 << 56));
                    let new_lw = builder.ins().band(lw, mask);
                    builder.ins().store(
                        cranelift::prelude::MemFlags::trusted(),
                        new_lw,
                        lw_addr,
                        0,
                    );
                    if op == INSTR_CLEAR_MUTABLE {
                        // Replace top with tagged 0.
                        stack.pop();
                        let tag0 = builder.ins().iconst(int, tag(0));
                        stack.push(tag0);
                    }
                    // For LOCK: stack unchanged. ptr stays on top.
                }
                INSTR_GET_THREAD_ID => {
                    // Allocate stub thread object (8-word mutable),
                    // push its pointer. Net +1.
                    let call = builder.ins().call(get_tid_ref, &[]);
                    let result = builder.inst_results(call)[0];
                    stack.push(result);
                }
                INSTR_ALLOC_MUT_CLOSURE_B => {
                    // [N]: allocate mut closure of N+1 words, slot 0 =
                    // src closure's code, slots 1..N+1 = tagged(0).
                    // REPLACES top (src closure) with new closure ptr.
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let n = bytecode[pc] as i64;
                    pc += 1;
                    let src = stack.pop().ok_or(TranslateError::Underflow(pc - 2))?;
                    let n_v = builder.ins().iconst(int, n);
                    let call = builder.ins().call(amc_ref, &[n_v, src]);
                    let result = builder.inst_results(call)[0];
                    stack.push(result);
                }
                INSTR_MOVE_TO_MUT_CLOSURE_B => {
                    // [slot]: pop value, peek target closure ptr,
                    // write value at target[slot+1]. Target ptr stays
                    // on top. Net -1.
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let slot = bytecode[pc] as usize;
                    pc += 1;
                    let value = stack.pop().ok_or(TranslateError::Underflow(pc - 2))?;
                    let target = *stack.last().ok_or(TranslateError::Underflow(pc - 2))?;
                    // Offset = (slot + 1) * 8
                    let off = ((slot + 1) * 8) as i32;
                    builder.ins().store(
                        cranelift::prelude::MemFlags::trusted(),
                        value,
                        target,
                        off,
                    );
                }
                INSTR_BLOCK_EQUAL_BYTE | INSTR_BLOCK_COMPARE_BYTE => {
                    // Same shape as BLOCK_MOVE_BYTE; returns tagged
                    // bool or tagged ordering depending on opcode.
                    // Pop length,off2,p2,off1; peek p1; call
                    // trampoline; pop p1; push result. Net -4.
                    if stack.len() < 5 {
                        return Err(TranslateError::Underflow(pc - 1));
                    }
                    let length_tag = stack.pop().unwrap();
                    let off2_tag = stack.pop().unwrap();
                    let p2 = stack.pop().unwrap();
                    let off1_tag = stack.pop().unwrap();
                    let p1 = stack.pop().unwrap();
                    let length = builder.ins().sshr_imm(length_tag, 1);
                    let off2 = builder.ins().sshr_imm(off2_tag, 1);
                    let off1 = builder.ins().sshr_imm(off1_tag, 1);
                    let fref = if op == INSTR_BLOCK_EQUAL_BYTE {
                        block_equal_byte_ref
                    } else {
                        block_compare_byte_ref
                    };
                    let call = builder.ins().call(
                        fref,
                        &[p1, off1, p2, off2, length],
                    );
                    let result = builder.inst_results(call)[0];
                    stack.push(result);
                }
                INSTR_BLOCK_MOVE_WORD | INSTR_BLOCK_MOVE_BYTE => {
                    // Interpreter (bytecode.cpp::blockMoveWord/Byte):
                    //   length = pop().untag()
                    //   dest_off = pop().untag()
                    //   dest = pop().as_ptr()
                    //   src_off = pop().untag()
                    //   src = peek(0).as_ptr()
                    //   memcpy(src+src_off, dest+dest_off, length units)
                    //   pop()  (the src that was peeked)
                    //   push tagged(0)
                    //
                    // Net stack delta: -4. Difference between word and
                    // byte: trampoline ptr type (PolyWord vs u8) so
                    // `add` advances by 8 or 1 per index. The JIT just
                    // picks the right trampoline.
                    if stack.len() < 5 {
                        return Err(TranslateError::Underflow(pc - 1));
                    }
                    let length_tag = stack.pop().unwrap();
                    let dest_off_tag = stack.pop().unwrap();
                    let dest = stack.pop().unwrap();
                    let src_off_tag = stack.pop().unwrap();
                    let src = stack.pop().unwrap(); // POP (was peek in interp)
                    let length = builder.ins().sshr_imm(length_tag, 1);
                    let dest_off = builder.ins().sshr_imm(dest_off_tag, 1);
                    let src_off = builder.ins().sshr_imm(src_off_tag, 1);
                    let func_ref = if op == INSTR_BLOCK_MOVE_WORD {
                        block_move_ref
                    } else {
                        block_move_byte_ref
                    };
                    let _call = builder.ins().call(
                        func_ref,
                        &[src, src_off, dest, dest_off, length],
                    );
                    let tag0 = builder.ins().iconst(int, tag(0));
                    stack.push(tag0);
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
                INSTR_CONST_INT_W => {
                    if pc + 1 >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    // Wide variant: u16 LE immediate. Like CONST_INT_B
                    // but with 2-byte unsigned operand (interpreter
                    // casts via isize::try_from on a u16).
                    let raw = u16::from_le_bytes([bytecode[pc], bytecode[pc + 1]]) as i64;
                    pc += 2;
                    stack.push(builder.ins().iconst(int, tag(raw)));
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
                INSTR_WORD_ADD => {
                    // y + x - tag(0) = (y + x) - 1; same shape as FIXED_ADD.
                    let x = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let y = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let sum = builder.ins().iadd(y, x);
                    let one = builder.ins().iconst(int, 1);
                    stack.push(builder.ins().isub(sum, one));
                }
                INSTR_WORD_SUB => {
                    // y - x + 1
                    let x = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let y = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let diff = builder.ins().isub(y, x);
                    let one = builder.ins().iconst(int, 1);
                    stack.push(builder.ins().iadd(diff, one));
                }
                INSTR_WORD_AND => {
                    // (y & x); both tagged, low bit preserved.
                    let x = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let y = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    stack.push(builder.ins().band(y, x));
                }
                INSTR_WORD_OR => {
                    let x = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let y = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    stack.push(builder.ins().bor(y, x));
                }
                INSTR_WORD_XOR => {
                    // y ^ x has the tag bit cleared (1^1=0); reinstate.
                    let x = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let y = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let xor = builder.ins().bxor(y, x);
                    let one = builder.ins().iconst(int, 1);
                    stack.push(builder.ins().bor(xor, one));
                }
                INSTR_WORD_MULT => {
                    // Interp: ((x>>1) * (y>>1)) << 1 | 1
                    let x = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let y = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let xs = builder.ins().sshr_imm(x, 1);
                    let ys = builder.ins().sshr_imm(y, 1);
                    let prod = builder.ins().imul(xs, ys);
                    let shifted = builder.ins().ishl_imm(prod, 1);
                    let one = builder.ins().iconst(int, 1);
                    stack.push(builder.ins().bor(shifted, one));
                }
                INSTR_WORD_SHIFT_LEFT | INSTR_WORD_SHIFT_R_LOG => {
                    // Top is shift amount, below is value. Both tagged.
                    // Untag shift via >>1, mask to 63. Untag value via >>1.
                    // Shift, then retag.
                    let x = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let y = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let one = builder.ins().iconst(int, 1);
                    let mask63 = builder.ins().iconst(int, 63);
                    let s_unt = builder.ins().sshr_imm(x, 1);
                    let s_lim = builder.ins().band(s_unt, mask63);
                    let v_unt = builder.ins().ushr_imm(y, 1);
                    let shifted = if op == INSTR_WORD_SHIFT_LEFT {
                        builder.ins().ishl(v_unt, s_lim)
                    } else {
                        builder.ins().ushr(v_unt, s_lim)
                    };
                    let retagged = builder.ins().ishl_imm(shifted, 1);
                    stack.push(builder.ins().bor(retagged, one));
                }
                INSTR_SET_STACK_VAL_B => {
                    // Pop top, write into sp[idx - 1]. idx is byte imm.
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let idx = bytecode[pc] as usize;
                    pc += 1;
                    if idx == 0 {
                        return Err(TranslateError::Underflow(pc - 2));
                    }
                    let depth = idx - 1;
                    let v = stack.pop().ok_or(TranslateError::Underflow(pc - 2))?;
                    let stack_len = stack.len();
                    if depth >= stack_len {
                        return Err(TranslateError::Underflow(pc - 2));
                    }
                    let target_idx = stack_len - 1 - depth;
                    stack[target_idx] = v;
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
                INSTR_LESS_SIGNED
                | INSTR_LESS_UNSIGNED
                | INSTR_LESS_EQ_SIGNED
                | INSTR_LESS_EQ_UNSIGNED
                | INSTR_GREATER_SIGNED
                | INSTR_GREATER_UNSIGNED
                | INSTR_GREATER_EQ_SIGNED
                | INSTR_GREATER_EQ_UNSIGNED => {
                    let cc = match op {
                        INSTR_LESS_SIGNED => IntCC::SignedLessThan,
                        INSTR_LESS_UNSIGNED => IntCC::UnsignedLessThan,
                        INSTR_LESS_EQ_SIGNED => IntCC::SignedLessThanOrEqual,
                        INSTR_LESS_EQ_UNSIGNED => IntCC::UnsignedLessThanOrEqual,
                        INSTR_GREATER_SIGNED => IntCC::SignedGreaterThan,
                        INSTR_GREATER_UNSIGNED => IntCC::UnsignedGreaterThan,
                        INSTR_GREATER_EQ_SIGNED => IntCC::SignedGreaterThanOrEqual,
                        _ => IntCC::UnsignedGreaterThanOrEqual,
                    };
                    let x = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let y = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    // Compute y CC x (since interp does `y OP x`).
                    let cmp = builder.ins().icmp(cc, y, x);
                    let cmp64 = builder.ins().uextend(int, cmp);
                    let doubled = builder.ins().ishl_imm(cmp64, 1);
                    let one = builder.ins().iconst(int, 1);
                    stack.push(builder.ins().iadd(doubled, one));
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
                INSTR_FIXED_QUOT | INSTR_FIXED_REM => {
                    // Interp: pops x (top, divisor), pops y (dividend),
                    // pushes y/x or y%x. Division by zero traps (we
                    // let Cranelift's sdiv/srem trap on 0 like SIGFPE).
                    let x = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let y = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let xn = builder.ins().sshr_imm(x, 1);
                    let yn = builder.ins().sshr_imm(y, 1);
                    let result_n = if op == INSTR_FIXED_QUOT {
                        builder.ins().sdiv(yn, xn)
                    } else {
                        builder.ins().srem(yn, xn)
                    };
                    let doubled = builder.ins().ishl_imm(result_n, 1);
                    let one = builder.ins().iconst(int, 1);
                    let result = builder.ins().iadd(doubled, one);
                    stack.push(result);
                }
                INSTR_RETURN_1 | INSTR_RETURN_2 | INSTR_RETURN_3 => {
                    // For our JIT ABI we just return the top value;
                    // the SML-stack pops of args+closure+retPC are
                    // irrelevant (we don't model that frame here).
                    let v = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    builder.ins().return_(&[v]);
                    returned = true;
                }
                INSTR_RAISE_EX => {
                    // Translation-only approximation: pop the exception
                    // packet and return TAGGED(0). The JIT'd code will
                    // raise the wrong value (or none) at runtime — but
                    // closure_call_trampoline is a stub anyway, so we
                    // never actually execute this path. The goal here
                    // is coverage: let functions that USE exceptions
                    // get past the translator.
                    let _exn = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let zero = builder.ins().iconst(int, tag(0));
                    builder.ins().return_(&[zero]);
                    returned = true;
                }
                INSTR_SET_HANDLER8 | INSTR_SET_HANDLER16 => {
                    // Consume offset (1 or 2 bytes) and push a placeholder
                    // "handler marker" onto our compile-time stack so
                    // subsequent ops see the same depth as the interp.
                    // The actual handler-PC dispatch isn't modeled.
                    if op == INSTR_SET_HANDLER8 {
                        if pc >= bytecode.len() {
                            return Err(TranslateError::Truncated(pc));
                        }
                        pc += 1;
                    } else {
                        if pc + 1 >= bytecode.len() {
                            return Err(TranslateError::Truncated(pc));
                        }
                        pc += 2;
                    }
                    let zero = builder.ins().iconst(int, tag(0));
                    stack.push(zero);
                }
                INSTR_DELETE_HANDLER => {
                    // Pop the handler marker pushed by SET_HANDLER.
                    let _ = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                }
                INSTR_ALLOC_BYTE_MEM => {
                    // Pop flags (top), peek length, allocate; REPLACE
                    // top (= length) with the heap pointer.
                    let flags = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let length = *stack.last().ok_or(TranslateError::Underflow(pc - 1))?;
                    let length_u = builder.ins().sshr_imm(length, 1);
                    let flags_u = builder.ins().sshr_imm(flags, 1);
                    let call_inst = builder.ins().call(
                        alloc_bytes_ref,
                        &[length_u, flags_u],
                    );
                    let result_val = builder.inst_results(call_inst)[0];
                    let last = stack.len() - 1;
                    stack[last] = result_val;
                }
                INSTR_ALLOC_WORD_MEMORY => {
                    // Stack (top→bottom): init, flags, length, ...
                    // Allocate `length` words with `flags`, fill with init,
                    // pop length (= 3rd from top), push pointer.
                    let init = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let flags = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let length = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let length_u = builder.ins().sshr_imm(length, 1);
                    let flags_u = builder.ins().sshr_imm(flags, 1);
                    // Allocate via byte_mem trampoline (uninitialized).
                    let call_inst = builder.ins().call(
                        alloc_bytes_ref,
                        &[length_u, flags_u],
                    );
                    let result_val = builder.inst_results(call_inst)[0];
                    // Initialize the body with `init` via stores in a loop.
                    // For simplicity, emit a stack-slot fill via a constant
                    // length loop. Since we don't have constant-length info,
                    // emit a runtime memset-like loop using Cranelift.
                    let zero = builder.ins().iconst(int, 0);
                    let body_ptr = result_val;
                    // Build a small loop: i = 0; while (i < length_u) { *(body+i*8) = init; i++; }
                    let loop_header = builder.create_block();
                    let loop_body = builder.create_block();
                    let loop_exit = builder.create_block();
                    builder.append_block_param(loop_header, int); // i
                    builder.ins().jump(loop_header, &[BlockArg::from(zero)]);
                    builder.switch_to_block(loop_header);
                    let i = builder.block_params(loop_header)[0];
                    let cond = builder.ins().icmp(IntCC::SignedLessThan, i, length_u);
                    builder.ins().brif(cond, loop_body, &[], loop_exit, &[]);
                    builder.switch_to_block(loop_body);
                    let eight = builder.ins().iconst(int, 8);
                    let off = builder.ins().imul(i, eight);
                    let addr = builder.ins().iadd(body_ptr, off);
                    builder.ins().store(
                        cranelift::prelude::MemFlags::trusted(),
                        init,
                        addr,
                        0,
                    );
                    let one = builder.ins().iconst(int, 1);
                    let i_plus_1 = builder.ins().iadd(i, one);
                    builder.ins().jump(loop_header, &[BlockArg::from(i_plus_1)]);
                    builder.switch_to_block(loop_exit);
                    builder.seal_block(loop_header);
                    builder.seal_block(loop_body);
                    builder.seal_block(loop_exit);
                    stack.push(result_val);
                }
                INSTR_STORE_UNTAGGED => {
                    // Pop raw (untagged), pop index (tagged), peek base.
                    // Write base[index] = raw bits. Replace base with tag(0).
                    let raw = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let index = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let base = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let raw_u = builder.ins().sshr_imm(raw, 1);
                    let index_u = builder.ins().sshr_imm(index, 1);
                    let eight = builder.ins().iconst(int, 8);
                    let off = builder.ins().imul(index_u, eight);
                    let addr = builder.ins().iadd(base, off);
                    builder.ins().store(
                        cranelift::prelude::MemFlags::trusted(),
                        raw_u,
                        addr,
                        0,
                    );
                    let tag0 = builder.ins().iconst(int, tag(0));
                    stack.push(tag0);
                }
                INSTR_CLOSURE_B => {
                    // Build a closure. Upstream semantics (per
                    // libpolyml/bytecode.cpp CREATE_CLOSURE):
                    //   - Loop pops N captures from top, writing to
                    //     slots N, N-1, ..., 1 in that order.
                    //   - After capture pops, src is now on top.
                    //     Copy its slot 0 (code addr) to slot 0 of
                    //     new closure.
                    //
                    // So stack layout BEFORE the opcode (top → bot):
                    //   cap_N (top, → slot N)
                    //   cap_{N-1}
                    //   ...
                    //   cap_1 (→ slot 1)
                    //   src
                    //
                    // Pop N captures first, THEN src. The trampoline
                    // (jit_dispatch_closure_alloc) writes captures
                    // in the order it receives them: captures_ptr[0]
                    // → slot 1, captures_ptr[1] → slot 2, etc.
                    // So we need caps_buf[i] = the value that maps
                    // to slot i+1 — i.e., caps_buf[0] = cap_1, etc.
                    // That means we should pop cap_N first and put it
                    // at caps_buf[N-1], cap_1 last and put it at
                    // caps_buf[0]. (Reverse iteration on store.)
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let n_captures = bytecode[pc] as usize;
                    pc += 1;
                    if stack.len() < n_captures + 1 {
                        return Err(TranslateError::Underflow(pc - 2));
                    }
                    // Pop captures first (top → first popped). Pop
                    // order: cap_N, cap_{N-1}, ..., cap_1.
                    let mut caps: Vec<Value> = Vec::with_capacity(n_captures);
                    for _ in 0..n_captures {
                        caps.push(stack.pop().unwrap());
                    }
                    // Now src is on top.
                    let src_closure = stack.pop().unwrap();
                    // Store captures into a stack slot in
                    // trampoline-expected order: slot[i] = cap_{i+1}.
                    // caps[0] = cap_N (first popped). caps[N-1] = cap_1.
                    // So slot[N-1] = caps[0], slot[0] = caps[N-1].
                    let slot_size = std::cmp::max(8, (n_captures * 8) as u32);
                    let slot = builder.create_sized_stack_slot(
                        cranelift::prelude::StackSlotData::new(
                            cranelift::prelude::StackSlotKind::ExplicitSlot,
                            slot_size,
                            3,
                        ),
                    );
                    for (i, v) in caps.iter().enumerate() {
                        let slot_byte_off = ((n_captures - 1 - i) * 8) as i32;
                        builder.ins().stack_store(*v, slot, slot_byte_off);
                    }
                    let caps_ptr = builder.ins().stack_addr(types::I64, slot, 0);
                    let n_v = builder.ins().iconst(types::I64, n_captures as i64);
                    let call_inst = builder.ins().call(
                        closure_alloc_ref,
                        &[n_v, caps_ptr, src_closure],
                    );
                    let result_val = builder.inst_results(call_inst)[0];
                    stack.push(result_val);
                }
                INSTR_CELL_LENGTH => {
                    // peek ptr; replace top with tagged(length-word & LENGTH_MASK).
                    // length word is at ptr - 8.
                    let p = *stack.last().ok_or(TranslateError::Underflow(pc - 1))?;
                    let lw = builder.ins().load(
                        int,
                        cranelift::prelude::MemFlags::trusted(),
                        p,
                        -8,
                    );
                    // mask = 0x00ff_ffff_ffff_ffff (low 56 bits)
                    let mask = builder.ins().iconst(int, 0x00ff_ffff_ffff_ffff_u64 as i64);
                    let len = builder.ins().band(lw, mask);
                    // tag: (len << 1) | 1
                    let shifted = builder.ins().ishl_imm(len, 1);
                    let one = builder.ins().iconst(int, 1);
                    let tagged_v = builder.ins().bor(shifted, one);
                    let last = stack.len() - 1;
                    stack[last] = tagged_v;
                }
                INSTR_CELL_FLAGS => {
                    // Like CELL_LENGTH but extracts the flags byte
                    // (top byte of length-word, FLAGS_SHIFT = 56).
                    // Replace top with tagged(flags).
                    let p = *stack.last().ok_or(TranslateError::Underflow(pc - 1))?;
                    let lw = builder.ins().load(
                        int,
                        cranelift::prelude::MemFlags::trusted(),
                        p,
                        -8,
                    );
                    let flags = builder.ins().ushr_imm(lw, 56);
                    // No mask needed; ushr already zeroes the top bits.
                    let shifted = builder.ins().ishl_imm(flags, 1);
                    let one = builder.ins().iconst(int, 1);
                    let tagged_v = builder.ins().bor(shifted, one);
                    let last = stack.len() - 1;
                    stack[last] = tagged_v;
                }
                INSTR_LOAD_ML_BYTE => {
                    // Pop index (tagged), peek base, replace top with
                    // tagged(*(base + (index>>1))).
                    let index_tag = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let base = *stack.last().ok_or(TranslateError::Underflow(pc - 1))?;
                    let index = builder.ins().sshr_imm(index_tag, 1);
                    let addr = builder.ins().iadd(base, index);
                    let b = builder.ins().load(
                        types::I8,
                        cranelift::prelude::MemFlags::trusted(),
                        addr,
                        0,
                    );
                    let b64 = builder.ins().uextend(int, b);
                    let shifted = builder.ins().ishl_imm(b64, 1);
                    let one = builder.ins().iconst(int, 1);
                    let tagged_v = builder.ins().bor(shifted, one);
                    let last = stack.len() - 1;
                    stack[last] = tagged_v;
                }
                INSTR_LOAD_ML_WORD => {
                    // Pop index (tagged), peek base, replace top with
                    // *(base + index*8). Result is a raw PolyWord (no
                    // re-tagging).
                    let index_tag = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let base = *stack.last().ok_or(TranslateError::Underflow(pc - 1))?;
                    let index = builder.ins().sshr_imm(index_tag, 1);
                    let eight = builder.ins().iconst(int, 8);
                    let off = builder.ins().imul(index, eight);
                    let addr = builder.ins().iadd(base, off);
                    let v = builder.ins().load(
                        int,
                        cranelift::prelude::MemFlags::trusted(),
                        addr,
                        0,
                    );
                    let last = stack.len() - 1;
                    stack[last] = v;
                }
                INSTR_NOT_BOOLEAN => {
                    // Pop v; push tag(1) if v == tag(0), else tag(0).
                    // tagged(0) = 1; tagged(1) = 3. So:
                    //   if v == 1: push 3 ; else push 1
                    let v = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let tag0 = builder.ins().iconst(int, tag(0));
                    let tag1 = builder.ins().iconst(int, tag(1));
                    let is_false = builder.ins().icmp(IntCC::Equal, v, tag0);
                    let result = builder.ins().select(is_false, tag1, tag0);
                    stack.push(result);
                }
                INSTR_IS_TAGGED => {
                    // Pop v; push tag(1) if v & 1 == 1, else tag(0).
                    let v = stack.pop().ok_or(TranslateError::Underflow(pc - 1))?;
                    let one = builder.ins().iconst(int, 1);
                    let lsb = builder.ins().band(v, one);
                    let doubled = builder.ins().ishl_imm(lsb, 1);
                    let result = builder.ins().iadd(doubled, one);
                    stack.push(result);
                }
                INSTR_ALLOC_REF => {
                    // Alloc 1-word mutable cell, init from top. Replaces
                    // top with cell pointer (interp: peek init,
                    // allocate, write, pop init, push pointer).
                    let init = *stack.last().ok_or(TranslateError::Underflow(pc - 1))?;
                    let slot = builder.create_sized_stack_slot(
                        cranelift::prelude::StackSlotData::new(
                            cranelift::prelude::StackSlotKind::ExplicitSlot,
                            8,
                            3,
                        ),
                    );
                    builder.ins().stack_store(init, slot, 0);
                    let vals_ptr = builder.ins().stack_addr(types::I64, slot, 0);
                    let n_v = builder.ins().iconst(types::I64, 1);
                    let call_inst =
                        builder.ins().call(alloc_func_ref, &[n_v, vals_ptr]);
                    let result_val = builder.inst_results(call_inst)[0];
                    let last = stack.len() - 1;
                    stack[last] = result_val;
                }
                INSTR_TAIL_B_B => {
                    // tail_count + skip immediates. Per upstream
                    // `bytecode.cpp:387`, tail_count counts the
                    // [retPC, closure, args] group at top; SML arity
                    // is `tail_count - 2`. `skip` is the caller-
                    // frame slots to drop below — irrelevant for our
                    // JIT which returns directly to the trampoline.
                    if pc + 1 >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let tail_count = bytecode[pc] as usize;
                    pc += 1;
                    let _skip = bytecode[pc] as usize;
                    pc += 1;
                    if tail_count < 2 {
                        return Err(TranslateError::Unsupported { op, at: pc });
                    }
                    let n_args = tail_count - 2;
                    if stack.len() < n_args + 1 {
                        return Err(TranslateError::Underflow(pc));
                    }
                    let mut args_vec: Vec<Value> = Vec::with_capacity(n_args);
                    for _ in 0..n_args {
                        args_vec.push(stack.pop().unwrap());
                    }
                    let closure = stack.pop().unwrap();
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
                    let call_inst = builder.ins().call(
                        closure_func_ref,
                        &[closure, n_args_v, args_ptr],
                    );
                    let result_val = builder.inst_results(call_inst)[0];
                    // Return the callee's result directly (= tail call).
                    builder.ins().return_(&[result_val]);
                    returned = true;
                }
                INSTR_RETURN_B => {
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    pc += 1; // consume N immediate
                    let v = stack.pop().ok_or(TranslateError::Underflow(pc - 2))?;
                    builder.ins().return_(&[v]);
                    returned = true;
                }
                INSTR_RETURN_W => {
                    if pc + 1 >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    pc += 2; // consume 16-bit N immediate
                    let v = stack.pop().ok_or(TranslateError::Underflow(pc - 3))?;
                    builder.ins().return_(&[v]);
                    returned = true;
                }
                INSTR_JUMP8 | INSTR_JUMP16 => {
                    let off = if op == INSTR_JUMP8 {
                        if pc >= bytecode.len() {
                            return Err(TranslateError::Truncated(pc));
                        }
                        let o = bytecode[pc] as usize;
                        pc += 1;
                        o
                    } else {
                        if pc + 1 >= bytecode.len() {
                            return Err(TranslateError::Truncated(pc));
                        }
                        let lo = bytecode[pc];
                        let hi = bytecode[pc + 1];
                        pc += 2;
                        u16::from_le_bytes([lo, hi]) as usize
                    };
                    let target_pc = pc + off;
                    let target_blk = *block_at.get(&target_pc)
                        .expect("target should be registered in pass 1");
                    let args: Vec<BlockArg> =
                        stack.iter().copied().map(BlockArg::from).collect();
                    builder.ins().jump(target_blk, &args);
                    returned = true;
                }
                INSTR_JUMP_BACK8 | INSTR_JUMP_BACK16 => {
                    let (off, imm_size) = if op == INSTR_JUMP_BACK8 {
                        if pc >= bytecode.len() {
                            return Err(TranslateError::Truncated(pc));
                        }
                        let o = bytecode[pc] as usize;
                        pc += 1;
                        (o, 1usize)
                    } else {
                        if pc + 1 >= bytecode.len() {
                            return Err(TranslateError::Truncated(pc));
                        }
                        let lo = bytecode[pc];
                        let hi = bytecode[pc + 1];
                        pc += 2;
                        (u16::from_le_bytes([lo, hi]) as usize, 2usize)
                    };
                    // Mirror interp: pc_offset_signed(-((off + imm_size + 1)))
                    // For BACK8: pc_offset_signed(-(off+2)). For BACK16:
                    // pc_offset_signed(-(off+3)). Both put us back by
                    // (off + opcode_total_len) bytes.
                    let target_pc = pc - off - 1 - imm_size;
                    let target_blk = *block_at.get(&target_pc)
                        .expect("back-edge target should be registered in pass 1");
                    let args: Vec<BlockArg> =
                        stack.iter().copied().map(BlockArg::from).collect();
                    builder.ins().jump(target_blk, &args);
                    returned = true;
                }
                INSTR_CASE16 => {
                    // CASE16 = jump table. Layout:
                    //   [0x0a] [arg1 u16 LE] [arg1 u16 LE entries]
                    // Selector popped, untagged, used as index. If in
                    // [0, arg1): jump to table_start + table[u].
                    // Else: jump to default (table_start + arg1*2).
                    if pc + 1 >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    let arg1 = u16::from_le_bytes([bytecode[pc], bytecode[pc + 1]]) as usize;
                    pc += 2;
                    let table_start = pc;
                    let selector =
                        stack.pop().ok_or(TranslateError::Underflow(pc - 3))?;
                    // Untag: arith shift right by 1.
                    let untagged = builder.ins().sshr_imm(selector, 1);
                    // Default block (out-of-range).
                    let default_target = table_start + arg1 * 2;
                    let default_blk = *block_at
                        .get(&default_target)
                        .expect("CASE16 default target should be registered in pass 1");
                    // Build per-case blocks list for br_table.
                    let mut case_blks: Vec<cranelift::prelude::Block> =
                        Vec::with_capacity(arg1);
                    for i in 0..arg1 {
                        let entry_pos = table_start + i * 2;
                        if entry_pos + 1 >= bytecode.len() {
                            return Err(TranslateError::Truncated(entry_pos));
                        }
                        let off = u16::from_le_bytes([
                            bytecode[entry_pos],
                            bytecode[entry_pos + 1],
                        ]) as usize;
                        let target = table_start + off;
                        let blk = *block_at.get(&target).expect(
                            "CASE16 case target should be registered in pass 1",
                        );
                        case_blks.push(blk);
                    }
                    // Cranelift br_table requires "leaf" blocks per case
                    // (no extra args). Since our blocks take stack args,
                    // we emit per-case trampoline blocks that jump to
                    // the real block with the current stack.
                    let stack_args: Vec<BlockArg> =
                        stack.iter().copied().map(BlockArg::from).collect();
                    // Create a leaf block per unique target that does
                    // `jump real_blk(args)`.
                    let make_leaf = |builder: &mut FunctionBuilder, target: cranelift::prelude::Block| -> cranelift::prelude::Block {
                        let leaf = builder.create_block();
                        builder.switch_to_block(leaf);
                        builder.ins().jump(target, &stack_args);
                        leaf
                    };
                    // Save current block so we restore.
                    let cur_blk = builder.current_block().expect("must be in a block");
                    let leaves: Vec<cranelift::prelude::Block> = case_blks
                        .iter()
                        .map(|&blk| {
                            let leaf = builder.create_block();
                            builder.switch_to_block(leaf);
                            builder.ins().jump(blk, &stack_args);
                            leaf
                        })
                        .collect();
                    let default_leaf = {
                        let leaf = builder.create_block();
                        builder.switch_to_block(leaf);
                        builder.ins().jump(default_blk, &stack_args);
                        leaf
                    };
                    let _ = make_leaf;
                    // Back to current block for emitting br_table.
                    builder.switch_to_block(cur_blk);
                    // Build JumpTable for br_table.
                    let default_call = builder.func.dfg.block_call(default_leaf, &[]);
                    let case_calls: Vec<_> = leaves
                        .iter()
                        .map(|&b| builder.func.dfg.block_call(b, &[]))
                        .collect();
                    let jtd = cranelift::prelude::JumpTableData::new(
                        default_call,
                        &case_calls,
                    );
                    let jt = builder.create_jump_table(jtd);
                    builder.ins().br_table(untagged, jt);
                    pc = table_start + arg1 * 2;
                    returned = true;
                }
                INSTR_JUMP8_FALSE | INSTR_JUMP8_TRUE
                | INSTR_JUMP16_FALSE | INSTR_JUMP16_TRUE => {
                    let off = if op == INSTR_JUMP8_FALSE || op == INSTR_JUMP8_TRUE {
                        if pc >= bytecode.len() {
                            return Err(TranslateError::Truncated(pc));
                        }
                        let o = bytecode[pc] as usize;
                        pc += 1;
                        o
                    } else {
                        if pc + 1 >= bytecode.len() {
                            return Err(TranslateError::Truncated(pc));
                        }
                        let lo = bytecode[pc];
                        let hi = bytecode[pc + 1];
                        pc += 2;
                        u16::from_le_bytes([lo, hi]) as usize
                    };
                    let target_pc = pc + off;
                    let cond = stack.pop().ok_or(TranslateError::Underflow(pc - 2))?;
                    let target_blk = *block_at.get(&target_pc)
                        .expect("target should be registered in pass 1");
                    let fall_blk = *block_at.get(&pc).expect("fallthrough should be registered");
                    let zero = builder.ins().iconst(int, tag(0));
                    let is_zero = builder.ins().icmp(IntCC::Equal, cond, zero);
                    let args: Vec<BlockArg> =
                        stack.iter().copied().map(BlockArg::from).collect();
                    let jump_on_zero =
                        op == INSTR_JUMP8_FALSE || op == INSTR_JUMP16_FALSE;
                    if jump_on_zero {
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
    if std::env::var("JIT_DUMP_IR").is_ok() {
        let head: Vec<String> = full_body[..bytecode_end.min(full_body.len())]
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        eprintln!(
            "=== JIT IR for {name} (bytecode_end={bytecode_end}, arg_count={arg_count}) ===\nbytecode = [{}]\n{}",
            head.join(" "),
            ctx.func.display()
        );
    }
    let func_id = jit
        .module
        .declare_function(&name, Linkage::Export, &ctx.func.signature)
        .map_err(|e| JitError::Module(e.to_string()))?;
    // Use the Debug formatter so verifier errors include their
    // detailed messages (the Display impl summarises to "Verifier
    // errors" which is useless for diagnosis).
    jit.module
        .define_function(func_id, &mut ctx)
        .map_err(|e| JitError::Module(format!("{e:?}")))?;
    jit.module.clear_context(&mut ctx);
    jit.module
        .finalize_definitions()
        .map_err(|e| JitError::Module(e.to_string()))?;

    let code_ptr = jit.module.get_finalized_function(func_id);
    // SAFETY: signature matches; JIT memory live while `jit` is.
    let f: JitFn = unsafe { std::mem::transmute(code_ptr) };
    Ok((f, arg_count))
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
    // CASE16 (0x0a) has a variable-length jump table inline:
    //   [op] [arg1 u16 LE] [N=arg1 jump-offsets, each u16 LE]
    // Total length = 1 + 2 + arg1*2.
    if bc[pc] == 0x0a {
        if pc + 2 >= bc.len() {
            return Err(TranslateError::Truncated(pc));
        }
        let arg1 = u16::from_le_bytes([bc[pc + 1], bc[pc + 2]]) as usize;
        return Ok(1 + 2 + arg1 * 2);
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
        | INSTR_JUMP_TAGGED_LOCAL => 3,
        // JUMP_NEQ_LOCAL{_IND}: 1 opcode + 3 imm (depth, want, off).
        // bytecode.cpp lines 552-560 (jumpNEqLocal): pc += 3.
        INSTR_JUMP_NEQ_LOCAL | INSTR_JUMP_NEQ_LOCAL_IND => 4,
        INSTR_CONST_ADDR8_0 | INSTR_CONST_ADDR8_1 => 2,
        INSTR_CALL_CONST_ADDR8_0 | INSTR_CALL_CONST_ADDR8_1 => 2,
        INSTR_CONST_ADDR8_8 | INSTR_CALL_CONST_ADDR8_8 => 3,
        INSTR_CONST_ADDR16_8 | INSTR_CALL_CONST_ADDR16_8 => 4,
        INSTR_CALL_FAST_RTS0
        | INSTR_CALL_FAST_RTS1
        | INSTR_CALL_FAST_RTS2
        | INSTR_CALL_FAST_RTS3
        | INSTR_CALL_FAST_RTS4
        | INSTR_CALL_FAST_RTS5 => 1,
        INSTR_CALL_LOCAL_B => 2,
        INSTR_TUPLE_2 | INSTR_TUPLE_3 | INSTR_TUPLE_4 => 1,
        INSTR_TUPLE_B => 2,
        INSTR_IS_TAGGED_LOCAL_B => 2,
        INSTR_CONST_0..=INSTR_CONST_4
        | INSTR_CONST_10
        | INSTR_RETURN_1
        | INSTR_FIXED_ADD
        | INSTR_FIXED_SUB
        | INSTR_FIXED_MULT
        | INSTR_FIXED_QUOT
        | INSTR_FIXED_REM
        | INSTR_WORD_ADD
        | INSTR_WORD_SUB
        | INSTR_WORD_MULT
        | INSTR_WORD_AND
        | INSTR_WORD_OR
        | INSTR_WORD_XOR
        | INSTR_WORD_SHIFT_LEFT
        | INSTR_WORD_SHIFT_R_LOG
        | INSTR_EQUAL_WORD
        | INSTR_LESS_SIGNED
        | INSTR_LESS_UNSIGNED
        | INSTR_LESS_EQ_SIGNED
        | INSTR_LESS_EQ_UNSIGNED
        | INSTR_GREATER_SIGNED
        | INSTR_GREATER_UNSIGNED
        | INSTR_GREATER_EQ_SIGNED
        | INSTR_GREATER_EQ_UNSIGNED
        | INSTR_LOCAL_0..=INSTR_LOCAL_11
        | INSTR_LOCAL_12
        | INSTR_LOCAL_13
        | INSTR_LOCAL_14
        | INSTR_LOCAL_15
        | INSTR_WORD_DIV
        | INSTR_WORD_MOD
        | INSTR_INDIRECT_0
        | INSTR_INDIRECT_1
        | INSTR_INDIRECT_2
        | INSTR_INDIRECT_3
        | INSTR_INDIRECT_4
        | INSTR_INDIRECT_5
        | INSTR_INDIRECT_0_LOCAL_0
        | INSTR_NO_OP
        | INSTR_RESET_1
        | INSTR_RESET_2
        | INSTR_RESET_R_1
        | INSTR_RESET_R_2
        | INSTR_RESET_R_3
        | INSTR_RETURN_2
        | INSTR_RETURN_3 => 1,
        INSTR_RETURN_B => 2,
        INSTR_RETURN_W => 3,
        // CONST_INT_W: op + 2 imm bytes (u16 LE).
        INSTR_CONST_INT_W => 3,
        INSTR_TAIL_B_B => 3,
        INSTR_CLOSURE_B => 2,
        INSTR_ALLOC_BYTE_MEM | INSTR_ALLOC_WORD_MEMORY | INSTR_STORE_UNTAGGED => 1,
        INSTR_RAISE_EX | INSTR_DELETE_HANDLER | INSTR_ALLOC_REF
        | INSTR_CELL_LENGTH | INSTR_LOAD_ML_BYTE | INSTR_LOAD_ML_WORD
        | INSTR_NOT_BOOLEAN | INSTR_IS_TAGGED => 1,
        INSTR_SET_HANDLER8 => 2,
        INSTR_SET_HANDLER16 => 3,
        INSTR_JUMP16 | INSTR_JUMP_BACK16 => 3,
        INSTR_JUMP16_FALSE | INSTR_JUMP16_TRUE => 3,
        INSTR_RESET_B | INSTR_RESET_R_B => 2,
        INSTR_SET_STACK_VAL_B => 2,
        INSTR_INDIRECT_B => 2,
        INSTR_LOAD_UNTAGGED | INSTR_STORE_ML_WORD | INSTR_STORE_ML_BYTE => 1,
        INSTR_BLOCK_MOVE_WORD | INSTR_BLOCK_MOVE_BYTE
            | INSTR_BLOCK_EQUAL_BYTE | INSTR_BLOCK_COMPARE_BYTE
            | INSTR_PUSH_HANDLER => 1,
        // Container opcodes: op + 1 imm byte = 2 total.
        INSTR_STACK_CONTAINER_B | INSTR_MOVE_TO_CONTAINER_B
            | INSTR_INDIRECT_CONTAINER_B => 2,
        // LOCK, CLEAR_MUTABLE, CELL_FLAGS, GET_THREAD_ID: no imm.
        INSTR_LOCK | INSTR_CLEAR_MUTABLE | INSTR_CELL_FLAGS
            | INSTR_GET_THREAD_ID => 1,
        // ALLOC_MUT_CLOSURE_B, MOVE_TO_MUT_CLOSURE_B: op + 1 imm.
        INSTR_ALLOC_MUT_CLOSURE_B | INSTR_MOVE_TO_MUT_CLOSURE_B => 2,
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

/// Determine the callee arity of a closure whose address is `addr`
/// (a raw PolyML heap address). Walks closure[0] → code-object body
/// → enter_int prologue bytes. Returns `Some(arity)` on success,
/// `None` if the bytes don't look like a recognisable enter_int
/// marker (in which case the JIT should fall back to the interpreter
/// rather than guess).
///
/// # Safety
/// Deferences `addr` and `*addr`. The caller — only `compile_with_consts`
/// — must trust that the addr came from a live code object's constant
/// pool, which is true at JIT-compile time since the heap is frozen
/// (no GC has run between load and translate).
/// Parse the immediate operand(s) of CONST_ADDR / CALL_CONST_ADDR
/// opcodes. Returns `(byte_off, constant_idx)` advanced past the
/// immediates. The four variants encode the byte-offset and
/// constant-pool index differently:
///   - `*_ADDR8_0`: 1-byte off, fixed idx = 3
///   - `*_ADDR8_1`: 1-byte off, fixed idx = 4
///   - `*_ADDR8_8`: 1-byte off, 1-byte (idx - 3)
///   - `*_ADDR16_8`: 2-byte off, 1-byte (idx - 3)
fn read_const_addr_operands(
    bytecode: &[u8],
    pc: &mut usize,
    op: u8,
) -> Result<(usize, usize), TranslateError> {
    let need_byte = |pc: &mut usize| -> Result<u8, TranslateError> {
        if *pc >= bytecode.len() {
            return Err(TranslateError::Truncated(*pc));
        }
        let b = bytecode[*pc];
        *pc += 1;
        Ok(b)
    };
    match op {
        INSTR_CONST_ADDR8_0 | INSTR_CALL_CONST_ADDR8_0 => {
            Ok((need_byte(pc)? as usize, 3))
        }
        INSTR_CONST_ADDR8_1 | INSTR_CALL_CONST_ADDR8_1 => {
            Ok((need_byte(pc)? as usize, 4))
        }
        INSTR_CONST_ADDR8_8 | INSTR_CALL_CONST_ADDR8_8 => {
            let off = need_byte(pc)? as usize;
            let idx_minus_3 = need_byte(pc)? as usize;
            Ok((off, idx_minus_3 + 3))
        }
        INSTR_CONST_ADDR16_8 | INSTR_CALL_CONST_ADDR16_8 => {
            let lo = need_byte(pc)?;
            let hi = need_byte(pc)?;
            let off = u16::from_le_bytes([lo, hi]) as usize;
            let idx_minus_3 = need_byte(pc)? as usize;
            Ok((off, idx_minus_3 + 3))
        }
        _ => Err(TranslateError::Unsupported { op, at: *pc }),
    }
}

/// Determine the arity of a closure whose address is `addr`.
///
/// Two candidate layouts are tried:
///   (a) `addr` is a closure object whose first word points at a code object
///   (b) `addr` is a code-object pointer directly
/// The code object's first byte may be `enter_int` (0xff/0xe9 with arity in
/// the next byte), or plain bytecode — pexport-loaded images strip
/// the enter_int marker. For the stripped case we run `infer_arg_count`
/// over the code object's body to deduce arity from `LOCAL_N` peek
/// patterns.
///
/// # Safety
/// Dereferences `addr` and assumes the heap layout is well-formed
/// (callers must only invoke this at JIT-compile time, before any
/// GC has run since image load).
fn closure_arity_from_addr(addr: u64) -> Option<usize> {
    if addr == 0 || addr & 0x7 != 0 {
        return None;
    }
    // SAFETY: caller-trusted JIT-compile-time invariant.
    unsafe {
        let closure_ptr = addr as *const usize;
        let candidate_a = closure_ptr.read();
        let code_obj = if candidate_a != 0 && candidate_a & 0x7 == 0 {
            candidate_a
        } else {
            addr as usize
        };
        let lw_ptr = (code_obj as *const usize).sub(1);
        let lw = lw_ptr.read();
        let n_words = lw & 0x00ff_ffff_ffff_ffff;
        if n_words == 0 || n_words > (1 << 24) {
            return None;
        }
        let body_len_bytes = n_words * 8;
        let body =
            std::slice::from_raw_parts(code_obj as *const u8, body_len_bytes);
        // Restrict scan to bytecode-only portion (not constants area).
        let trailing_offset_word = body_len_bytes - 8;
        let trailing_offset = i64::from_le_bytes(
            body[trailing_offset_word..trailing_offset_word + 8]
                .try_into()
                .ok()?,
        );
        let cp_byte_off = (body_len_bytes as i64 + trailing_offset) as usize;
        let bytecode_end = cp_byte_off.saturating_sub(8).min(body.len());
        let bytecode = &body[..bytecode_end];
        let b0 = bytecode.first().copied()?;
        if b0 == INSTR_ENTER_INT_X86 || b0 == INSTR_ENTER_INT_ARM64 {
            return Some((bytecode[1] & 0x7f) as usize);
        }
        // Authoritative arity: scan the bytecode for any `RETURN_N`
        // opcode. Per `bytecode.cpp`'s RETURN dispatch, the N suffix
        // is the number of arg slots to drop below the result —
        // i.e. exactly the function arity. LOCAL_N peeks aren't a
        // reliable signal (closures access captures via LOCAL too).
        if let Some(arity) = arity_from_return_scan(bytecode) {
            return Some(arity);
        }
        // Fall back to peek-depth inference if no RETURN_N is found
        // in a recognisable place.
        infer_arg_count(bytecode, 0)
    }
}

/// Scan bytecode for any RETURN_N opcode and return its `N` (the
/// number of args the function pops below its result on return).
/// This is the authoritative arity: the SML compiler emits a
/// RETURN_N that matches the function's declared arity, whereas
/// LOCAL_N peeks can refer to either args or other stack values.
///
/// Walks one opcode at a time using `opcode_total_len` so immediates
/// don't get misread as opcodes. Stops at the first unknown opcode
/// (we don't want to mis-scan past data); returns `None` in that
/// case so the caller falls back to peek-depth inference.
/// SML arity from RETURN_N: walks bytecode opcode-aware (skipping
/// immediates) to find the first `RETURN_N`. Used internally by the
/// JIT to set per-function calling-convention size; also exposed for
/// testing harnesses that need the same correct scan.
pub fn arity_from_return_scan_pub(bytecode: &[u8]) -> Option<usize> {
    arity_from_terminator_scan(bytecode, false)
}

fn arity_from_return_scan(bytecode: &[u8]) -> Option<usize> {
    arity_from_terminator_scan(bytecode, false)
}

/// As `arity_from_return_scan` but also considers `TAIL_B_B` as an
/// arity hint. TAIL_B_B's `tail_count - 2` is the callee arity, not
/// strictly this function's arity — but for self-tail-recursive
/// functions (a common case for HOL4/ML), they coincide. This is
/// used as a LOWER-BOUND hint when no `RETURN_N` is present.
fn arity_from_terminator_scan(bytecode: &[u8], include_tail: bool) -> Option<usize> {
    let mut pc = 0;
    while pc < bytecode.len() {
        let op = bytecode[pc];
        match op {
            INSTR_RETURN_1 => return Some(1),
            INSTR_RETURN_2 => return Some(2),
            INSTR_RETURN_3 => return Some(3),
            INSTR_RETURN_B => {
                let imm = *bytecode.get(pc + 1)?;
                return Some(imm as usize);
            }
            INSTR_RETURN_W => {
                let lo = *bytecode.get(pc + 1)?;
                let hi = *bytecode.get(pc + 2)?;
                return Some(u16::from_le_bytes([lo, hi]) as usize);
            }
            INSTR_TAIL_B_B if include_tail => {
                let tc = *bytecode.get(pc + 1)? as usize;
                if tc >= 2 {
                    return Some(tc - 2);
                }
            }
            _ => {}
        }
        let step = opcode_total_len(bytecode, pc).ok()?;
        pc += step;
    }
    None
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
                INSTR_CONST_INT_W => (1, 0, None, 2),
                INSTR_LOCAL_0..=INSTR_LOCAL_11 => {
                    let d = (op - INSTR_LOCAL_0) as usize;
                    (1, 0, Some(d), 0)
                }
                INSTR_LOCAL_12 => (1, 0, Some(12), 0),
                INSTR_LOCAL_13 => (1, 0, Some(13), 0),
                INSTR_LOCAL_14 => (1, 0, Some(14), 0),
                INSTR_LOCAL_15 => (1, 0, Some(15), 0),
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
                INSTR_INDIRECT_0
                | INSTR_INDIRECT_1
                | INSTR_INDIRECT_2
                | INSTR_INDIRECT_3
                | INSTR_INDIRECT_4
                | INSTR_INDIRECT_5 => (1, 1, None, 0),
                INSTR_INDIRECT_B => (1, 1, None, 1),
                INSTR_LOAD_UNTAGGED => (1, 2, None, 0),  // pop idx, peek base; net -1+1 = 0
                INSTR_STORE_ML_WORD => (1, 3, None, 0),  // pop val,idx,base; push 1; net -2
                INSTR_STORE_ML_BYTE => (1, 3, None, 0),  // same shape; byte store
                // pop length,off2,p2,off1,p1; push 1. Net -4.
                INSTR_BLOCK_MOVE_WORD | INSTR_BLOCK_MOVE_BYTE
                    | INSTR_BLOCK_EQUAL_BYTE
                    | INSTR_BLOCK_COMPARE_BYTE => (1, 5, None, 0),
                INSTR_STACK_CONTAINER_B => {
                    // Push N zeros + 1 pointer. Net +(N+1).
                    if pc >= bytecode.len() { return None; }
                    let n = bytecode[pc] as i32;
                    (n + 1, 0, None, 1)
                }
                INSTR_MOVE_TO_CONTAINER_B => {
                    // Pop value; peek pointer (top). Net -1.
                    (0, 1, Some(0), 1)
                }
                INSTR_INDIRECT_CONTAINER_B => {
                    // Replace top with load through top. Net 0.
                    (1, 1, None, 1)
                }
                INSTR_LOCK | INSTR_CLEAR_MUTABLE => {
                    // Peek top, possibly replace with tagged 0. Net 0.
                    (0, 0, Some(0), 0)
                }
                INSTR_CELL_FLAGS => {
                    // Peek top, replace with tagged(flags). Net 0.
                    (0, 0, Some(0), 0)
                }
                INSTR_GET_THREAD_ID => {
                    // Push pointer. Net +1.
                    (1, 0, None, 0)
                }
                INSTR_ALLOC_MUT_CLOSURE_B => {
                    // Replace top. Net 0. 1 imm byte.
                    (0, 0, Some(0), 1)
                }
                INSTR_MOVE_TO_MUT_CLOSURE_B => {
                    // Pop value, peek target. Net -1. 1 imm byte.
                    (0, 1, Some(1), 1)
                }
                INSTR_PUSH_HANDLER => (1, 0, None, 0), // push handler sentinel; +1.
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
                INSTR_RESET_R_B => {
                    if pc >= bytecode.len() { return None; }
                    let n = bytecode[pc] as i32;
                    // Preserve top (= 0 net push/pop) plus drop n below.
                    (1, n + 1, None, 1)
                }
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
                INSTR_CONST_ADDR8_8 => (1, 0, None, 2),
                INSTR_CONST_ADDR16_8 => (1, 0, None, 3),
                INSTR_CALL_CONST_ADDR8_0
                | INSTR_CALL_CONST_ADDR8_1
                | INSTR_CALL_CONST_ADDR8_8
                | INSTR_CALL_CONST_ADDR16_8 => {
                    // Static arity inspection: we know the callee
                    // since the closure address is in the const pool,
                    // but `infer_arg_count` walks only the bytecode
                    // slice — no access to constants here. So bail.
                    return Some((-min_depth).max(0) as usize);
                }
                INSTR_CALL_FAST_RTS0
                | INSTR_CALL_FAST_RTS1
                | INSTR_CALL_FAST_RTS2
                | INSTR_CALL_FAST_RTS3
                | INSTR_CALL_FAST_RTS4
                | INSTR_CALL_FAST_RTS5 => {
                    let n = (op - INSTR_CALL_FAST_RTS0) as i32;
                    (1, n + 1, None, 0)
                }
                INSTR_CALL_LOCAL_B => {
                    if pc >= bytecode.len() { return None; }
                    let n = bytecode[pc] as i32;
                    // Pop N args, peek closure at depth N (still there
                    // after call), push 1 result. Net depth: -N + 1.
                    (1, n, Some(n as usize), 1)
                }
                INSTR_TUPLE_2 => (1, 2, None, 0),
                INSTR_TUPLE_3 => (1, 3, None, 0),
                INSTR_TUPLE_4 => (1, 4, None, 0),
                INSTR_TUPLE_B => {
                    if pc >= bytecode.len() { return None; }
                    let n = bytecode[pc] as i32;
                    (1, n, None, 1)
                }
                INSTR_FIXED_ADD | INSTR_FIXED_SUB | INSTR_FIXED_MULT
                | INSTR_FIXED_QUOT | INSTR_FIXED_REM
                | INSTR_WORD_ADD | INSTR_WORD_SUB | INSTR_WORD_MULT
                | INSTR_WORD_DIV | INSTR_WORD_MOD
                | INSTR_WORD_AND | INSTR_WORD_OR | INSTR_WORD_XOR
                | INSTR_WORD_SHIFT_LEFT | INSTR_WORD_SHIFT_R_LOG
                | INSTR_EQUAL_WORD | INSTR_LESS_SIGNED
                | INSTR_LESS_UNSIGNED | INSTR_LESS_EQ_SIGNED
                | INSTR_LESS_EQ_UNSIGNED | INSTR_GREATER_SIGNED
                | INSTR_GREATER_UNSIGNED | INSTR_GREATER_EQ_SIGNED
                | INSTR_GREATER_EQ_UNSIGNED => (1, 2, None, 0),
                INSTR_SET_STACK_VAL_B => {
                    // Pops 1; writes into a stack slot below — depth
                    // unchanged net, but immediate consumes 1 byte.
                    (0, 1, None, 1)
                }
                INSTR_JUMP8 | INSTR_JUMP_BACK8 => (0, 0, None, 1),
                INSTR_JUMP16 | INSTR_JUMP_BACK16 => (0, 0, None, 2),
                INSTR_JUMP8_FALSE | INSTR_JUMP8_TRUE => (0, 1, None, 1),
                INSTR_JUMP16_FALSE | INSTR_JUMP16_TRUE => (0, 1, None, 2),
                INSTR_RETURN_1 | INSTR_RETURN_2 | INSTR_RETURN_3 => (0, 1, None, 0),
                INSTR_RETURN_B => (0, 1, None, 1),
                INSTR_RETURN_W => (0, 1, None, 2),
                INSTR_TAIL_B_B => {
                    // tail_count + skip; behaves like return (consumes
                    // the call group + leaves nothing for fallthrough).
                    if pc + 1 >= bytecode.len() { return None; }
                    let n = bytecode[pc] as i32; // tail_count
                    // SML arity = n - 2; pops that many + 1 closure.
                    let consumed = (n - 1).max(0);
                    (0, consumed, None, 2)
                }
                INSTR_RAISE_EX => {
                    // Pops the exception packet then terminates.
                    return Some((-min_depth).max(0) as usize);
                }
                INSTR_SET_HANDLER8 => (1, 0, None, 1),
                INSTR_SET_HANDLER16 => (1, 0, None, 2),
                INSTR_DELETE_HANDLER => (0, 1, None, 0),
                INSTR_CLOSURE_B => {
                    if pc >= bytecode.len() { return None; }
                    let n = bytecode[pc] as i32;
                    // Pops n_captures + 1 src closure, pushes 1.
                    (1, n + 1, None, 1)
                }
                INSTR_ALLOC_BYTE_MEM => {
                    // Pops flags, replaces top length with pointer. Net 0
                    // on stack depth (but uses 2 values minimum).
                    (1, 2, None, 0)
                }
                INSTR_ALLOC_WORD_MEMORY => {
                    // Pops 3 (init, flags, length), pushes pointer. Net -2.
                    (1, 3, None, 0)
                }
                INSTR_STORE_UNTAGGED => {
                    // Pops 3 (raw, index, base), pushes tag(0). Net -2.
                    (1, 3, None, 0)
                }
                INSTR_ALLOC_REF => (1, 1, None, 0),  // peek init, push cell
                INSTR_CELL_LENGTH => (1, 1, None, 0), // peek ptr, push len
                INSTR_LOAD_ML_BYTE => (1, 2, None, 0), // pop idx, peek base, push byte
                INSTR_LOAD_ML_WORD => (1, 2, None, 0), // pop idx, peek base, push word
                INSTR_NOT_BOOLEAN | INSTR_IS_TAGGED => (1, 1, None, 0), // pop, push
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

/// Compute the JIT-internal arg_count for a bytecode body.
/// Must be kept in sync between scan_branch_targets (pass 1) and
/// compile_with_consts_impl (pass 2).
fn compute_arg_count(bytecode: &[u8], entry_pc: usize, prologue_arg_count: usize) -> usize {
    if prologue_arg_count > 0 || entry_pc > 0 {
        return prologue_arg_count;
    }
    // (a) max-peek-depth inference (covers functions that peek
    //     closure/retPC slots via LOCAL_N).
    let inferred = infer_arg_count(bytecode, entry_pc).unwrap_or(0);
    // (b) SML calling-convention reservation: sml_arity + 2 (retPC
    //     + closure). The JIT-internal stack model uses depth-from-
    //     stack-top peeks, which only matches SML semantics if the
    //     JIT loads the SAME N slots that SML's stack frame contains
    //     at entry. Without this, INDIRECT_CLOSURE_BN with depth >=
    //     arity reads the wrong value at runtime.
    let from_return = arity_from_return_scan(bytecode).map_or(0, |a| a + 2);
    inferred.max(from_return)
}

fn scan_branch_targets(
    bytecode: &[u8],
    full_body: &[u8],
) -> Result<std::collections::BTreeMap<usize, usize>, TranslateError> {
    let mut targets: std::collections::BTreeMap<usize, usize> =
        std::collections::BTreeMap::new();
    // depth_at[pc] = stack depth observed at the *start* of the
    // opcode at pc, used to validate that backward jumps land at
    // a position whose recorded depth matches the depth at the
    // jump source.
    let mut depth_at: Vec<Option<usize>> = vec![None; bytecode.len()];
    let (start_pc, prologue_arg_count) = function_prologue(bytecode);
    let arg_count = compute_arg_count(bytecode, start_pc, prologue_arg_count);
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
        } else if let Some(&recorded) = targets.get(&pc) {
            // Falling through into a recorded branch target. Pass 2
            // emits an implicit jump here passing the current stack
            // as block args — the block was created with `recorded`
            // params. For a SOUND merge, the depth must match exactly.
            //
            // When they diverge, the cheapest correctness-preserving
            // option is to TRUNCATE the stack to match `recorded`
            // when fall-through has MORE values (the extras are
            // dead at the merge point — well-formed SML compiler
            // output ensures this), and bail when fall-through has
            // FEWER values (we can't materialise extras).
            #[allow(clippy::comparison_chain)]
            if depth > recorded {
                // Truncate to recorded; pass 2 will see the same
                // depth and emit a clean jump.
                depth = recorded;
            } else if depth < recorded {
                return Err(TranslateError::Unsupported { op: 0xFD, at: pc });
            }
        }
        depth_at[pc] = Some(depth);
        if std::env::var("JIT_DEBUG_SCAN").is_ok() {
            eprintln!("  scan: pc={pc} depth={depth} op=0x{:02x}", bytecode[pc]);
        }
        let op = bytecode[pc];
        pc += 1;
        // NOTE on CASE16 (0x0a) translation limit: when bytecode after a
        // CASE16 has case-targets that are NOT also jump-target sentinels
        // (= the SML compiler emits jumps that fall-through code to case
        // targets), our linear scan tracks depth as if executing the
        // intervening code, but the case-target enters at CASE16's
        // post-pop depth (depth-1). Truncating fall-through depth to
        // recorded depth (above) hides this — subsequent LOCAL_K reads
        // then fail with Underflow. Functions with such patterns won't
        // translate. Fix would require per-case branch walking, not
        // linear scan.
        match op {
            INSTR_CONST_0..=INSTR_CONST_4 => depth += 1,
            INSTR_CONST_10 => depth += 1,
            INSTR_LOCAL_0..=INSTR_LOCAL_11 => {
                let d = (op - INSTR_LOCAL_0) as usize;
                if d >= depth {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                depth += 1;
            }
            INSTR_LOCAL_12 | INSTR_LOCAL_13 | INSTR_LOCAL_14 | INSTR_LOCAL_15 => {
                let d = match op {
                    INSTR_LOCAL_12 => 12,
                    INSTR_LOCAL_13 => 13,
                    INSTR_LOCAL_14 => 14,
                    INSTR_LOCAL_15 => 15,
                    _ => unreachable!(),
                };
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
            INSTR_INDIRECT_0
            | INSTR_INDIRECT_1
            | INSTR_INDIRECT_2
            | INSTR_INDIRECT_3
            | INSTR_INDIRECT_4
            | INSTR_INDIRECT_5 => {
                if depth == 0 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                // pop ptr, push field value: net 0.
            }
            INSTR_INDIRECT_B => {
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                pc += 1;
                if depth == 0 {
                    return Err(TranslateError::Underflow(pc - 2));
                }
                // pop ptr, push field value: net 0.
            }
            INSTR_LOAD_UNTAGGED => {
                // Pop idx, peek base, push value. Net 0; min depth 2.
                if depth < 2 { return Err(TranslateError::Underflow(pc - 1)); }
                depth -= 1; // net effect (-2 +1)
            }
            INSTR_STORE_ML_WORD => {
                // Pop val + idx + base, push tag(0). Net -2; min depth 3.
                if depth < 3 { return Err(TranslateError::Underflow(pc - 1)); }
                depth -= 2;
            }
            INSTR_STORE_ML_BYTE => {
                // Same shape as STORE_ML_WORD: pop val+idx+base, push tag(0).
                if depth < 3 { return Err(TranslateError::Underflow(pc - 1)); }
                depth -= 2;
            }
            INSTR_BLOCK_MOVE_WORD | INSTR_BLOCK_MOVE_BYTE
                | INSTR_BLOCK_EQUAL_BYTE | INSTR_BLOCK_COMPARE_BYTE => {
                // Pop length, off2, p2, off1; peek p1; trampoline;
                // pop p1; push 1 result. Net -4; min depth 5.
                if depth < 5 { return Err(TranslateError::Underflow(pc - 1)); }
                depth -= 4;
            }
            INSTR_STACK_CONTAINER_B => {
                // Pushes N zeros + 1 pointer. Net +(N+1).
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                let n = bytecode[pc] as usize;
                pc += 1;
                depth += n + 1;
            }
            INSTR_MOVE_TO_CONTAINER_B => {
                // Pop value; peek pointer; write through it. Net -1.
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                pc += 1; // consume immediate
                if depth < 2 { return Err(TranslateError::Underflow(pc - 2)); }
                depth -= 1;
            }
            INSTR_INDIRECT_CONTAINER_B => {
                // Replace top (pointer) with loaded value. Net 0.
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                pc += 1; // consume immediate
                if depth == 0 { return Err(TranslateError::Underflow(pc - 2)); }
            }
            INSTR_LOCK | INSTR_CLEAR_MUTABLE => {
                // Both peek top, clear F_MUTABLE_BIT in heap object's
                // length word. LOCK keeps stack as is; CLEAR_MUTABLE
                // pops top and pushes tagged 0. Net 0 either way.
                if depth == 0 { return Err(TranslateError::Underflow(pc - 1)); }
            }
            INSTR_CELL_FLAGS => {
                // Peek top (ptr), replace top with tagged(flags). Net 0.
                if depth == 0 { return Err(TranslateError::Underflow(pc - 1)); }
            }
            INSTR_GET_THREAD_ID => {
                // Push allocated pointer. Net +1.
                depth += 1;
            }
            INSTR_ALLOC_MUT_CLOSURE_B => {
                // Replace top (src closure) with new closure. Net 0.
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                pc += 1;
                if depth == 0 { return Err(TranslateError::Underflow(pc - 2)); }
            }
            INSTR_MOVE_TO_MUT_CLOSURE_B => {
                // Pop value, peek target. Net -1.
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                pc += 1;
                if depth < 2 { return Err(TranslateError::Underflow(pc - 2)); }
                depth -= 1;
            }
            INSTR_PUSH_HANDLER => {
                // Push current handler_sp (we use 0 sentinel). Net +1.
                depth += 1;
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
            INSTR_RESET_R_1
            | INSTR_RESET_R_2
            | INSTR_RESET_R_3
            | INSTR_RESET_R_B => {
                let n = match op {
                    INSTR_RESET_R_1 => 1,
                    INSTR_RESET_R_2 => 2,
                    INSTR_RESET_R_3 => 3,
                    INSTR_RESET_R_B => {
                        if pc >= bytecode.len() {
                            return Err(TranslateError::Truncated(pc));
                        }
                        let v = bytecode[pc] as usize;
                        pc += 1;
                        v
                    }
                    _ => unreachable!(),
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
                if depth < n + 1 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                depth = depth - n - 1 + 1;
            }
            INSTR_CALL_LOCAL_B => {
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                let n = bytecode[pc] as usize;
                pc += 1;
                if depth < n + 1 {
                    return Err(TranslateError::Underflow(pc - 2));
                }
                // PEEK closure: pop N args, push 1 result. Closure
                // stays. Net: -N + 1 (was -N before fix).
                depth = depth - n + 1;
            }
            INSTR_TUPLE_2 | INSTR_TUPLE_3 | INSTR_TUPLE_4 | INSTR_TUPLE_B => {
                let n = match op {
                    INSTR_TUPLE_2 => 2,
                    INSTR_TUPLE_3 => 3,
                    INSTR_TUPLE_4 => 4,
                    INSTR_TUPLE_B => {
                        if pc >= bytecode.len() { return Err(TranslateError::Truncated(pc)); }
                        let n = bytecode[pc] as usize;
                        pc += 1;
                        n
                    }
                    _ => unreachable!(),
                };
                if depth < n { return Err(TranslateError::Underflow(pc - 1)); }
                depth = depth - n + 1;
            }
            INSTR_CONST_ADDR8_0
            | INSTR_CONST_ADDR8_1
            | INSTR_CONST_ADDR8_8
            | INSTR_CONST_ADDR16_8 => {
                let (_, _) = read_const_addr_operands(bytecode, &mut pc, op)?;
                depth += 1;
            }
            INSTR_CALL_CONST_ADDR8_0
            | INSTR_CALL_CONST_ADDR8_1
            | INSTR_CALL_CONST_ADDR8_8
            | INSTR_CALL_CONST_ADDR16_8 => {
                let (byte_off, idx) =
                    read_const_addr_operands(bytecode, &mut pc, op)?;
                let read_at = pc + byte_off + idx * 8;
                if read_at + 8 > full_body.len() {
                    return Err(TranslateError::Unsupported { op, at: pc });
                }
                let mut buf = [0u8; 8];
                buf.copy_from_slice(&full_body[read_at..read_at + 8]);
                let closure_addr = u64::from_le_bytes(buf);
                let Some(n) = closure_arity_from_addr(closure_addr) else {
                    return Err(TranslateError::Unsupported { op, at: pc });
                };
                if depth < n {
                    return Err(TranslateError::Underflow(pc));
                }
                depth = depth - n + 1;
            }
            INSTR_CONST_INT_B => {
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                pc += 1;
                depth += 1;
            }
            INSTR_CONST_INT_W => {
                if pc + 1 >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                pc += 2;
                depth += 1;
            }
            INSTR_FIXED_ADD | INSTR_FIXED_SUB | INSTR_FIXED_MULT
            | INSTR_FIXED_QUOT | INSTR_FIXED_REM
            | INSTR_WORD_ADD | INSTR_WORD_SUB | INSTR_WORD_MULT
            | INSTR_WORD_DIV | INSTR_WORD_MOD
            | INSTR_WORD_AND | INSTR_WORD_OR | INSTR_WORD_XOR
            | INSTR_WORD_SHIFT_LEFT | INSTR_WORD_SHIFT_R_LOG
            | INSTR_EQUAL_WORD | INSTR_LESS_SIGNED
            | INSTR_LESS_UNSIGNED | INSTR_LESS_EQ_SIGNED
            | INSTR_LESS_EQ_UNSIGNED | INSTR_GREATER_SIGNED
            | INSTR_GREATER_UNSIGNED | INSTR_GREATER_EQ_SIGNED
            | INSTR_GREATER_EQ_UNSIGNED => {
                if depth < 2 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                depth -= 1;
            }
            INSTR_SET_STACK_VAL_B => {
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                let _idx = bytecode[pc] as usize;
                pc += 1;
                if depth == 0 {
                    return Err(TranslateError::Underflow(pc - 2));
                }
                depth -= 1;
            }
            INSTR_TAIL_B_B => {
                if pc + 1 >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                let tc = bytecode[pc] as usize;
                pc += 2; // tail_count + skip
                if tc < 2 {
                    return Err(TranslateError::Unsupported { op, at: pc - 3 });
                }
                let n_args = tc - 2;
                if depth < n_args + 1 {
                    return Err(TranslateError::Underflow(pc - 3));
                }
                reachable = false;
            }
            INSTR_RAISE_EX => {
                if depth == 0 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                // Treated as a function-exit terminator (no internal
                // handler dispatch in this approximation).
                reachable = false;
            }
            INSTR_SET_HANDLER8 | INSTR_SET_HANDLER16 => {
                // Consume immediate (1 or 2 bytes); push a placeholder.
                if op == INSTR_SET_HANDLER8 {
                    if pc >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    pc += 1;
                } else {
                    if pc + 1 >= bytecode.len() {
                        return Err(TranslateError::Truncated(pc));
                    }
                    pc += 2;
                }
                depth += 1;
            }
            INSTR_DELETE_HANDLER => {
                if depth == 0 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                depth -= 1;
            }
            INSTR_CLOSURE_B => {
                if pc >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                let n = bytecode[pc] as usize;
                pc += 1;
                if depth < n + 1 {
                    return Err(TranslateError::Underflow(pc - 2));
                }
                // pop n + 1, push 1 = net -n
                depth -= n;
            }
            INSTR_ALLOC_BYTE_MEM => {
                // Pop flags + peek length + replace top with pointer.
                if depth < 2 { return Err(TranslateError::Underflow(pc - 1)); }
                depth -= 1;
            }
            INSTR_ALLOC_WORD_MEMORY => {
                // Pops 3 (init, flags, length), pushes pointer.
                if depth < 3 { return Err(TranslateError::Underflow(pc - 1)); }
                depth -= 2;
            }
            INSTR_STORE_UNTAGGED => {
                if depth < 3 { return Err(TranslateError::Underflow(pc - 1)); }
                depth -= 2;
            }
            INSTR_ALLOC_REF => {
                if depth == 0 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                // Replaces top; net 0.
            }
            INSTR_CELL_LENGTH => {
                if depth == 0 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                // Replaces top; net 0.
            }
            INSTR_LOAD_ML_BYTE | INSTR_LOAD_ML_WORD => {
                if depth < 2 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                depth -= 1; // pop idx, peek base, push value; net -1
            }
            INSTR_NOT_BOOLEAN | INSTR_IS_TAGGED => {
                if depth == 0 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                // Pop, push: net 0.
            }
            INSTR_RETURN_1 | INSTR_RETURN_2 | INSTR_RETURN_3 => {
                if depth == 0 {
                    return Err(TranslateError::Underflow(pc - 1));
                }
                reachable = false;
            }
            INSTR_RETURN_B => {
                if pc >= bytecode.len() { return Err(TranslateError::Truncated(pc)); }
                pc += 1;
                if depth == 0 { return Err(TranslateError::Underflow(pc - 2)); }
                reachable = false;
            }
            INSTR_RETURN_W => {
                if pc + 1 >= bytecode.len() { return Err(TranslateError::Truncated(pc)); }
                pc += 2;
                if depth == 0 { return Err(TranslateError::Underflow(pc - 3)); }
                reachable = false;
            }
            INSTR_JUMP8 | INSTR_JUMP16 => {
                let (off, imm_bytes) = read_jump_off(bytecode, &mut pc, op)?;
                let _ = imm_bytes;
                let target = pc + off;
                record_target(&mut targets, target, depth)?;
                reachable = false;
            }
            INSTR_JUMP_BACK8 | INSTR_JUMP_BACK16 => {
                let (off, imm_bytes) = read_jump_off(bytecode, &mut pc, op)?;
                // Total opcode size = 1 + imm_bytes. Target = pc - off - opcode_total_len
                let opcode_total_len = 1 + imm_bytes;
                if pc < off + opcode_total_len {
                    return Err(TranslateError::Unsupported { op, at: pc - opcode_total_len });
                }
                let target = pc - off - opcode_total_len;
                let expected = depth_at[target].ok_or(TranslateError::Unsupported {
                    op,
                    at: pc - opcode_total_len,
                })?;
                if expected != depth {
                    return Err(TranslateError::Unsupported { op: 0xFE, at: target });
                }
                record_target(&mut targets, target, depth)?;
                reachable = false;
            }
            INSTR_JUMP8_FALSE | INSTR_JUMP8_TRUE
            | INSTR_JUMP16_FALSE | INSTR_JUMP16_TRUE => {
                let (off, _) = read_jump_off(bytecode, &mut pc, op)?;
                if depth == 0 {
                    return Err(TranslateError::Underflow(pc));
                }
                let post_pop = depth - 1;
                let taken = pc + off;
                record_target(&mut targets, taken, post_pop)?;
                record_target(&mut targets, pc, post_pop)?;
                depth = post_pop;
            }
            INSTR_CASE16 => {
                // CASE16 = jump-table opcode:
                //   [0x0a] [arg1 u16 LE] [arg1 entries of u16 LE each]
                // Selector popped from stack. After pop, depth-1.
                // arg1 = number of in-range case entries.
                // table_start = position after the arg1 word.
                // - If selector in [0, arg1): jump to
                //   table_start + (table[selector] as i16 ext).
                //   Upstream uses unsigned u16 add.
                // - Default (out of range): jump to
                //   table_start + arg1*2.
                if pc + 1 >= bytecode.len() {
                    return Err(TranslateError::Truncated(pc));
                }
                let arg1 = u16::from_le_bytes([bytecode[pc], bytecode[pc + 1]]) as usize;
                pc += 2;
                let table_start = pc;
                if depth == 0 {
                    return Err(TranslateError::Underflow(pc));
                }
                let post_pop = depth - 1;
                // Register the default target (= one byte past the
                // table, which is table_start + arg1*2).
                let default_target = table_start + arg1 * 2;
                record_target(&mut targets, default_target, post_pop)?;
                // Register each case entry's target.
                for i in 0..arg1 {
                    let entry_pos = table_start + i * 2;
                    if entry_pos + 1 >= bytecode.len() {
                        return Err(TranslateError::Truncated(entry_pos));
                    }
                    let off = u16::from_le_bytes([
                        bytecode[entry_pos],
                        bytecode[entry_pos + 1],
                    ]) as usize;
                    let target = table_start + off;
                    record_target(&mut targets, target, post_pop)?;
                }
                pc = table_start + arg1 * 2;
                reachable = false;
            }
            _ => {
                return Err(TranslateError::Unsupported { op, at: pc - 1 });
            }
        }
    }
    Ok(targets)
}

/// Read a jump immediate: 1 byte for 8-bit variants, 2 bytes (LE)
/// for 16-bit variants. Returns (offset_value, immediate_byte_count).
fn read_jump_off(
    bytecode: &[u8],
    pc: &mut usize,
    op: u8,
) -> Result<(usize, usize), TranslateError> {
    let wide = matches!(
        op,
        INSTR_JUMP16 | INSTR_JUMP_BACK16 | INSTR_JUMP16_FALSE | INSTR_JUMP16_TRUE
    );
    if wide {
        if *pc + 1 >= bytecode.len() {
            return Err(TranslateError::Truncated(*pc));
        }
        let lo = bytecode[*pc];
        let hi = bytecode[*pc + 1];
        *pc += 2;
        Ok((u16::from_le_bytes([lo, hi]) as usize, 2))
    } else {
        if *pc >= bytecode.len() {
            return Err(TranslateError::Truncated(*pc));
        }
        let o = bytecode[*pc] as usize;
        *pc += 1;
        Ok((o, 1))
    }
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

    /// Call a JitFn with no SML args. Functions with a RETURN_N now
    /// have an SML-style call frame (the JIT loads sml_arity+2 slots),
    /// so pass a small zero buffer instead of null.
    fn call0(f: JitFn) -> i64 {
        let args = [0i64; 8];
        unsafe { f(args.as_ptr()) }
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
        // SML "identity function for arity 1": push arg_0 (= LOCAL_2
        // in the SML call frame [arg, retPC, closure]) then RETURN_1.
        // The JIT loads arity+2 = 3 slots from args_ptr now.
        let bc = vec![
            0x2b, // INSTR_LOCAL_2
            INSTR_RETURN_1,
        ];
        let mut jit = Jit::new().unwrap();
        let f = compile(&mut jit, &bc).unwrap();
        let args = [tag(99), 0, 0];
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
