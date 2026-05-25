//! Cranelift-backed JIT for PolyML bytecode.
//!
//! Status: proof-of-concept stub. We compile one toy function
//! (`compile_identity`) to native code and call it from Rust to
//! prove the Cranelift build + JIT plumbing works in this
//! workspace. Real bytecode-to-IR translation comes next.
//!
//! ## Long-term plan
//!
//! - Each PolyML `Closure { code_addr }` will get a JIT'd entry
//!   point computed from the underlying code object's bytecode.
//! - The interpreter dispatches CALL into a JIT'd function by
//!   looking the closure's code pointer up in a JIT cache.
//! - Inside JIT'd code, opcodes we haven't yet translated trampoline
//!   back to the interpreter (one entry per uncompiled opcode).
//! - JIT'd code shares the same `Interpreter::stack` array as the
//!   interpreter for now; later we can spill registers more
//!   aggressively.

#![allow(clippy::missing_safety_doc)]

pub mod translate;

#[cfg(test)]
mod bench;

/// Walk all code objects in a [`polyml_runtime::LoadedImage`],
/// JIT-translate each one that the translator accepts, and install
/// every successful translation in the given interpreter's JIT
/// cache. Returns `(total_code_objects, jit_translated, installed)`.
///
/// Uses the same logic as `jit_bootstrap_run.rs` (the bisection test)
/// but with no filters: every translatable function gets installed
/// at the recommended `arity_init`.
///
/// # Safety
/// Reads code-object bytes from the loaded image — caller must ensure
/// the image is loaded and code spaces are populated.
pub fn install_all_jit_entries(
    jit: &mut Jit,
    loaded: &polyml_runtime::LoadedImage,
    interp: &mut polyml_runtime::Interpreter,
) -> (usize, usize, usize) {
    use polyml_runtime::{length_word, JitEntry, MemorySpace, PolyWord};
    let mut total = 0usize;
    let mut jit_ok = 0usize;
    let mut installed = 0usize;

    // Bisection support: env vars to narrow the install set.
    //   JIT_INSTALL_LIMIT=N — install only first N functions
    //   JIT_INSTALL_SKIP=N,M,K — skip these install indices (comma list)
    //   JIT_INSTALL_VERBOSE=1 — print each install with its index
    let install_limit: Option<usize> = std::env::var("JIT_INSTALL_LIMIT")
        .ok()
        .and_then(|s| s.parse().ok());
    let skip_indices: std::collections::HashSet<usize> = std::env::var("JIT_INSTALL_SKIP")
        .ok()
        .map(|s| {
            s.split(',')
                .filter_map(|x| x.trim().parse().ok())
                .collect()
        })
        .unwrap_or_default();
    let verbose = std::env::var("JIT_INSTALL_VERBOSE").is_ok();
    let mut install_idx = 0usize;

    fn walk_code_objects<F: FnMut(*const PolyWord, PolyWord)>(
        space: &MemorySpace,
        mut f: F,
    ) {
        let mut i = 0usize;
        let used = space.used_words();
        let Some(base) = space.iter().next().map(|w| w as *const PolyWord) else {
            return;
        };
        while i < used {
            let lw = unsafe { *base.add(i) };
            let n = length_word::length_of(lw);
            if n == 0 || i + 1 + n > used {
                break;
            }
            let body = unsafe { base.add(i + 1) };
            if length_word::is_code_object(lw) {
                f(body, lw);
            }
            i += 1 + n;
        }
    }

    for space in [&loaded.immutable, &loaded.mutable, &loaded.code] {
        walk_code_objects(space, |code_obj_ptr, lw| {
            total += 1;
            let n_words = length_word::length_of(lw);
            let (cp, _count) = unsafe { length_word::const_segment_for_code(code_obj_ptr) };
            let body_start = code_obj_ptr as usize;
            let cp_start = cp as usize;
            let bytecode_len = cp_start
                .saturating_sub(body_start)
                .saturating_sub(std::mem::size_of::<usize>());
            let max_bytes = n_words * std::mem::size_of::<usize>();
            let bytecode_len = bytecode_len.min(max_bytes);
            let full_body: &[u8] =
                unsafe { std::slice::from_raw_parts(code_obj_ptr.cast::<u8>(), max_bytes) };
            let Ok((jf, jit_arity_init)) =
                translate::compile_with_consts_meta(jit, full_body, bytecode_len)
            else {
                return;
            };
            jit_ok += 1;
            let Some(sml_arity) = translate::arity_from_return_scan_pub(&full_body[..bytecode_len])
            else {
                return;
            };
            if sml_arity > 32 {
                return;
            }
            // Skip functions whose inferred JIT arity exceeds
            // sml_arity + 2 (= closure + retPC + args). These
            // functions read positions BELOW the entry frame — i.e.,
            // they peek into the caller's "older stack" via LOCAL_K.
            // Our do_call's args_buf layout doesn't fully model this:
            // older slots are zero-padded, which causes LOCAL_K to
            // read 0 where SML's interp has real values. Subsequent
            // deref of these zeros → SEGV. Skipping → these functions
            // run in the interp, behavior matches.
            if jit_arity_init > sml_arity + 2 {
                return;
            }
            // Skip functions that contain CALL_LOCAL_B (0x16) — their
            // peek-don't-pop calling convention pushes closure_orig
            // into the call group, which our trampoline path doesn't
            // model perfectly. Easier to just let the interp handle
            // them than to risk wrong arg counts → bad retPCs.
            //
            // Also skip TAIL_B_B (0x7b) for similar reasons.
            //
            // Also skip RAISE_EX (0x10) — JIT translates it as
            // "return TAGGED(0)" instead of raising, so a function
            // whose exception path returns TAGGED(0) will silently
            // propagate that to the caller, which may then deref it
            // (= SEGV at next STORE/INDIRECT).
            //
            // Also skip SET_HANDLER (0x12/0x13) — same exception class.
            // Filter opcodes whose translation/semantics our JIT
            // doesn't fully model.
            const INSTR_CALL_LOCAL_B_OP: u8 = 0x16;
            const INSTR_TAIL_B_B_OP: u8 = 0x7b;
            const INSTR_RAISE_EX_OP: u8 = 0x10;
            const INSTR_SET_HANDLER8_OP: u8 = 0x81;
            const INSTR_SET_HANDLER16_OP: u8 = 0xf9;
            const INSTR_CLOSURE_B_OP: u8 = 0xd0;
            const INSTR_ALLOC_REF_OP: u8 = 0x06;
            const INSTR_ALLOC_BYTE_MEM_OP: u8 = 0xbd;
            const INSTR_ALLOC_WORD_MEM_OP: u8 = 0xda;
            // CONST_ADDR and CALL_CONST_ADDR variants load from a
            // PC-relative absolute address baked into the JIT code.
            // While the load itself is dynamic (GC-updated pointers
            // are seen fresh), if the code object holding the JIT
            // entry has its const pool moved, the baked absolute
            // address becomes stale.
            // Bisection narrowed first failure to entry #27 which
            // uses CALL_CONST_ADDR8_0/1.
            const INSTR_CONST_ADDR8_0_OP: u8 = 0x55;
            const INSTR_CONST_ADDR8_1_OP: u8 = 0x56;
            const INSTR_CONST_ADDR8_8_OP: u8 = 0x15;
            const INSTR_CONST_ADDR16_8_OP: u8 = 0x14;
            const INSTR_CALL_CONST_ADDR8_0_OP: u8 = 0x57;
            const INSTR_CALL_CONST_ADDR8_1_OP: u8 = 0x58;
            const INSTR_CALL_CONST_ADDR8_8_OP: u8 = 0x17;
            const INSTR_CALL_CONST_ADDR16_8_OP: u8 = 0x18;
            let bc = &full_body[..bytecode_len];
            if bc.iter().any(|&b| {
                b == INSTR_CALL_LOCAL_B_OP
                    || b == INSTR_TAIL_B_B_OP
                    || b == INSTR_RAISE_EX_OP
                    || b == INSTR_SET_HANDLER8_OP
                    || b == INSTR_SET_HANDLER16_OP
                    || b == INSTR_CLOSURE_B_OP
                    || b == INSTR_ALLOC_REF_OP
                    || b == INSTR_ALLOC_BYTE_MEM_OP
                    || b == INSTR_ALLOC_WORD_MEM_OP
                    || b == INSTR_CONST_ADDR8_0_OP
                    || b == INSTR_CONST_ADDR8_1_OP
                    || b == INSTR_CONST_ADDR8_8_OP
                    || b == INSTR_CONST_ADDR16_8_OP
                    || b == INSTR_CALL_CONST_ADDR8_0_OP
                    || b == INSTR_CALL_CONST_ADDR8_1_OP
                    || b == INSTR_CALL_CONST_ADDR8_8_OP
                    || b == INSTR_CALL_CONST_ADDR16_8_OP
            }) {
                return;
            }
            // Bisection: check limit + skip set BEFORE incrementing
            // the install index (so we count consistently).
            if let Some(lim) = install_limit
                && install_idx >= lim
            {
                install_idx += 1;
                return;
            }
            if skip_indices.contains(&install_idx) {
                install_idx += 1;
                return;
            }
            let arity_init = sml_arity + 2;
            if verbose {
                eprintln!(
                    "  install[{install_idx:4}]: code_obj=0x{body_start:016x} sml_arity={sml_arity} arity_init={arity_init}"
                );
            }
            // Dump bytecode for a specific install index.
            if let Ok(s) = std::env::var("JIT_INSTALL_DUMP_IDX")
                && let Ok(want_idx) = s.parse::<usize>()
                && install_idx == want_idx
            {
                let bc = &full_body[..bytecode_len];
                let hex: Vec<String> = bc.iter().map(|b| format!("{b:02x}")).collect();
                eprintln!(
                    "  install[{install_idx}] BYTECODE ({} bytes): {}",
                    bc.len(),
                    hex.join(" ")
                );
            }
            interp.install_jit(
                body_start,
                JitEntry {
                    func: jf,
                    arity_init,
                    sml_arity,
                },
            );
            installed += 1;
            install_idx += 1;
        });
    }
    (total, jit_ok, installed)
}

/// Trampoline that JIT'd code calls to dispatch `CALL_FAST_RTS<N>`.
/// Signature must match what `translate.rs` declares for the extern
/// symbol — `(stub: i64, n_args: i64, args: *const i64) -> i64`.
///
/// Looks up the RTS function via the thread-local interpreter handle
/// (set by `do_call` when invoking JIT'd code), invokes it, and
/// returns the result as raw PolyWord bits.
///
/// On any failure (thread-local unset, unresolved entry, alloc-space
/// missing) returns `1` = TAGGED(0) — safer than UB; the JIT'd code
/// downstream may misbehave, but at least we don't deref garbage.
///
/// # Arg layout
/// `args` is the JIT-emitted args buffer; `args[0]` = first popped
/// from stack top = LAST pushed = (per the interpreter convention)
/// LAST C-side arg. Reverse before calling the RTS function so
/// `rts_args[0]` matches the interpreter's `args[0]` (= threadId
/// for `rtsCallFullN`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rts_trampoline(
    stub_word: i64,
    n_args: i64,
    args: *const i64,
) -> i64 {
    use polyml_runtime::{
        rts::{RtsContext, RtsFn},
        PolyWord, JIT_INTERP,
    };

    let interp_ptr = JIT_INTERP.with(|c| c.get());
    if interp_ptr.is_null() {
        return 1; // TAGGED(0)
    }
    // SAFETY: JIT_INTERP non-null = caller of with_jit_interp holds
    // the borrow for this call.
    let interp = unsafe { &mut *interp_ptr };

    // stub_word is the raw PolyWord bits of an EntryPoint object.
    // Word 0 holds the RTS dispatch token (= entry index + 1).
    let stub = PolyWord::from_bits(stub_word as usize);
    if !stub.is_data_ptr() {
        return 1;
    }
    let token = unsafe { *stub.as_ptr::<PolyWord>() }.0;

    // Resolve the entry.
    let Some(entry) = interp.rts_table().entry(token).cloned() else {
        return 1;
    };
    let n = n_args as usize;
    if entry.func.arity() != n {
        return 1;
    }

    // Read N args from the JIT's buffer. JIT stored slot[0] = first
    // popped = top of stack = LAST C arg. Reverse on read.
    #[allow(clippy::cast_sign_loss)]
    let mut rts_args: [PolyWord; 5] = [PolyWord::ZERO; 5];
    for i in 0..n {
        // SAFETY: caller (JIT'd code) guarantees args[0..n] is valid.
        let v = unsafe { *args.add(i) };
        // JIT slot[i] = (n-1-i)-th C arg.
        rts_args[n - 1 - i] = PolyWord::from_bits(v as usize);
    }

    // Dispatch.
    let rts_ref = interp.rts_table_arc();
    let mut ctx = RtsContext {
        alloc_space: interp.jit_alloc_space_mut(),
        raised_exception: None,
        rts: Some(&rts_ref),
    };
    let result = match entry.func {
        RtsFn::Arity0(f) => f(&mut ctx),
        RtsFn::Arity1(f) => f(&mut ctx, rts_args[0]),
        RtsFn::Arity2(f) => f(&mut ctx, rts_args[0], rts_args[1]),
        RtsFn::Arity3(f) => f(&mut ctx, rts_args[0], rts_args[1], rts_args[2]),
        RtsFn::Arity4(f) => f(&mut ctx, rts_args[0], rts_args[1], rts_args[2], rts_args[3]),
        RtsFn::Arity5(f) => f(
            &mut ctx,
            rts_args[0],
            rts_args[1],
            rts_args[2],
            rts_args[3],
            rts_args[4],
        ),
    };
    result.0 as i64
}

/// Closure-call trampoline. Signature must match what `translate.rs`
/// declares: `(closure_word, n_args, args_ptr) -> i64`.
///
/// Real dispatch path: reads the thread-local interpreter handle
/// set by `polyml_runtime::with_jit_interp`, then invokes
/// `jit_dispatch_closure_call`. The dispatch may recurse into
/// another JIT'd function (cache hit in `Interpreter::do_call`) or
/// fall back to bytecode interpretation.
///
/// If the thread-local isn't set (e.g. JIT'd code being benchmarked
/// in isolation), returns TAGGED(0) as a safe-ish fallback.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn closure_call_trampoline(
    closure_word: i64,
    n_args: i64,
    args_ptr: *const i64,
) -> i64 {
    use polyml_runtime::PolyWord;
    let closure = PolyWord::from_bits(closure_word as usize);
    let n = n_args as usize;
    // Diagnostic dump (gated): visible when chasing trampoline-call
    // arg layout issues.
    if std::env::var("JIT_TRAMP_DUMP_ARGS").is_ok() {
        use std::io::Write;
        let _ = writeln!(std::io::stderr(),
            "  closure_call_trampoline: closure=0x{closure_word:016x} n_args={n}",
        );
        for i in 0..n {
            let v = unsafe { args_ptr.add(i).read() };
            let _ = writeln!(std::io::stderr(),
                "    raw_slot[{i}] = 0x{v:016x}",
            );
        }
        let _ = std::io::stderr().flush();
    }
    let mut args: Vec<PolyWord> = Vec::with_capacity(n);
    // SAFETY: caller (JIT'd code) guarantees args_ptr[0..n] is valid.
    // Reverse on read to match jit_dispatch_closure_call's contract
    // (`args[0]` is SML's arg_0 = deepest in pushed block). JIT stored
    // slot[0] = first popped = top of SML = SML's arg_{N-1}, so we
    // reverse to put arg_0 at args[0].
    unsafe {
        for i in 0..n {
            let v = args_ptr.add(n - 1 - i).read();
            args.push(PolyWord::from_bits(v as usize));
        }
    }
    match polyml_runtime::jit_dispatch_closure_call(closure, &args) {
        Ok(v) => v.0 as i64,
        Err(e) => {
            if std::env::var("JIT_TRAMP_PANIC_ON_ERR").is_ok() {
                eprintln!(
                    "  closure_call_trampoline ERR: closure=0x{closure_word:016x} n_args={n} err={e:?}"
                );
                std::process::abort();
            }
            1 // TAGGED(0)
        }
    }
}

/// Byte-mem allocation trampoline. `(n_words, flags) -> i64`.
/// Used by JIT'd `ALLOC_BYTE_MEM`. Body is uninitialized.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn alloc_byte_mem_trampoline(
    n_words: i64,
    flags: i64,
) -> i64 {
    #[allow(clippy::cast_sign_loss)]
    let n = n_words.max(0) as usize;
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let f = (flags & 0xff) as u8;
    match polyml_runtime::jit_dispatch_alloc_bytes(n, f) {
        Some(ptr) => ptr as i64,
        None => 1,
    }
}

/// Closure-construction trampoline. `(n_captures, captures_ptr,
/// src_closure_word) -> i64` returning the new closure pointer.
///
/// Used by JIT-translated `CLOSURE_B`: builds a heap closure whose
/// slot 0 is the source closure's code address and slots 1..N are
/// the captures.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn closure_alloc_trampoline(
    n_captures: i64,
    captures_ptr: *const i64,
    src_closure_word: i64,
) -> i64 {
    #[allow(clippy::cast_sign_loss)]
    let n = n_captures.max(0) as usize;
    match polyml_runtime::jit_dispatch_closure_alloc(n, captures_ptr, src_closure_word as u64) {
        Some(ptr) => ptr as i64,
        None => 1,
    }
}

/// Tuple-alloc trampoline. `(n_words, values_ptr) -> i64` returning
/// the new heap-object pointer.
///
/// Routes through `polyml_runtime::jit_dispatch_alloc` which uses
/// the thread-local interpreter handle set by `with_jit_interp`.
/// If the handle isn't set (e.g. JIT'd code running in isolation
/// outside an interpreter dispatch), returns TAGGED(0) as a safe
/// fallback — the JIT'd code can still run, just produces a
/// useless tuple value.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn alloc_tuple_trampoline(
    n_words: i64,
    values_ptr: *const i64,
) -> i64 {
    #[allow(clippy::cast_sign_loss)]
    let n = n_words.max(0) as usize;
    match polyml_runtime::jit_dispatch_alloc(n, 0, values_ptr) {
        Some(ptr) => ptr as i64,
        None => 1, // TAGGED(0)
    }
}

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};
use thiserror::Error;

/// Errors from constructing or running a JIT compilation.
#[derive(Debug, Error)]
pub enum JitError {
    #[error("cranelift settings: {0}")]
    Settings(String),
    #[error("ISA construction failed: {0}")]
    Isa(String),
    #[error("module operation failed: {0}")]
    Module(String),
}

/// A live JIT environment. Owns the Cranelift module that holds
/// compiled functions — drop it and the JITted memory is freed.
pub struct Jit {
    pub(crate) module: JITModule,
    /// Monotonic counter so each compile gets a unique symbol name.
    next_id: u64,
}

impl Jit {
    /// Build a default native-target JIT environment.
    pub fn new() -> Result<Self, JitError> {
        let mut flags = settings::builder();
        flags
            .set("opt_level", "speed")
            .map_err(|e| JitError::Settings(e.to_string()))?;
        let isa_builder = cranelift_native::builder()
            .map_err(|e| JitError::Isa(e.to_string()))?;
        let isa = isa_builder
            .finish(settings::Flags::new(flags))
            .map_err(|e| JitError::Isa(e.to_string()))?;
        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        // Register the RTS-call trampoline so JIT'd code can call back
        // into Rust for any opcode that needs interpreter state.
        builder.symbol("polyml_jit_rts_trampoline", rts_trampoline as *const u8);
        builder.symbol(
            "polyml_jit_closure_call",
            closure_call_trampoline as *const u8,
        );
        builder.symbol(
            "polyml_jit_alloc_tuple",
            alloc_tuple_trampoline as *const u8,
        );
        builder.symbol(
            "polyml_jit_alloc_closure",
            closure_alloc_trampoline as *const u8,
        );
        builder.symbol(
            "polyml_jit_alloc_byte_mem",
            alloc_byte_mem_trampoline as *const u8,
        );
        Ok(Self {
            module: JITModule::new(builder),
            next_id: 0,
        })
    }

    pub(crate) fn fresh_name(&mut self, prefix: &str) -> String {
        let id = self.next_id;
        self.next_id += 1;
        format!("{prefix}_{id}")
    }

    /// Compile a toy "double the tagged int" function and return a
    /// pointer to its native entry point. Signature: `fn(i64) -> i64`.
    ///
    /// The function reads the high 63 bits of `x` (which is the
    /// PolyWord representation of a tagged int `n` as `2n+1`),
    /// extracts `n` via arithmetic shift right by 1, doubles it,
    /// then re-tags. This mirrors the operation `n -> 2n` on the
    /// SML-level int while preserving the tagged-bit invariant.
    pub fn compile_double(&mut self) -> Result<extern "C" fn(i64) -> i64, JitError> {
        let mut ctx = self.module.make_context();
        let mut func_builder_ctx = FunctionBuilderContext::new();
        let int = types::I64;
        // Signature: fn(i64) -> i64
        ctx.func.signature.params.push(AbiParam::new(int));
        ctx.func.signature.returns.push(AbiParam::new(int));

        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_builder_ctx);
            let block = builder.create_block();
            builder.append_block_params_for_function_params(block);
            builder.switch_to_block(block);
            builder.seal_block(block);

            let x = builder.block_params(block)[0];
            // n = (x - 1) >> 1   (tagged int is 2n+1)
            let one = builder.ins().iconst(int, 1);
            let x_minus_1 = builder.ins().isub(x, one);
            let n = builder.ins().sshr_imm(x_minus_1, 1);
            // doubled = n + n
            let doubled = builder.ins().iadd(n, n);
            // re-tag: 2*doubled + 1
            let two = builder.ins().iconst(int, 2);
            let shifted = builder.ins().imul(doubled, two);
            let tagged = builder.ins().iadd(shifted, one);
            builder.ins().return_(&[tagged]);

            builder.finalize();
        }

        let name = self.fresh_name("polyml_jit_double");
        let func_id = self
            .module
            .declare_function(&name, Linkage::Export, &ctx.func.signature)
            .map_err(|e| JitError::Module(e.to_string()))?;
        self.module
            .define_function(func_id, &mut ctx)
            .map_err(|e| JitError::Module(e.to_string()))?;
        self.module.clear_context(&mut ctx);
        self.module
            .finalize_definitions()
            .map_err(|e| JitError::Module(e.to_string()))?;

        let code_ptr = self.module.get_finalized_function(func_id);
        // SAFETY: We just compiled this function with the matching
        // signature `fn(i64) -> i64`. The JIT memory remains valid
        // as long as `self.module` does.
        let f: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(code_ptr) };
        Ok(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cranelift_compiles_and_runs_toy_function() {
        let mut jit = Jit::new().expect("jit init");
        let f = jit.compile_double().expect("compile");
        // PolyWord tagging: n is stored as 2n+1.
        //   tag(3)  = 7
        //   tag(6)  = 13
        let tagged_3: i64 = 2 * 3 + 1;
        let tagged_6: i64 = 2 * 6 + 1;
        assert_eq!(f(tagged_3), tagged_6, "double of tagged 3 should be tagged 6");

        let tagged_neg1: i64 = 2 * (-1) + 1; // = -1
        let tagged_neg2: i64 = 2 * (-2) + 1; // = -3
        assert_eq!(f(tagged_neg1), tagged_neg2);
    }

    #[test]
    fn jit_handle_can_compile_multiple_independent_functions() {
        // The same Jit can produce more than one function. (Real
        // bytecode→native translation will rely on this — each
        // PolyML code object becomes one Cranelift function.)
        let mut jit = Jit::new().expect("jit init");
        let f1 = jit.compile_double().expect("compile #1");
        let f2 = jit.compile_double().expect("compile #2");
        assert_eq!(f1(2 * 4 + 1), 2 * 8 + 1);
        assert_eq!(f2(2 * 5 + 1), 2 * 10 + 1);
    }
}
