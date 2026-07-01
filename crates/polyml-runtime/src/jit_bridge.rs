//! Bridge between JIT'd code and the interpreter.
//!
//! When JIT'd code wants to make a closure call, allocate, etc., it
//! invokes a trampoline (registered in `polyml-jit/src/lib.rs`) that
//! needs interpreter state. That state is passed via a thread-local
//! pointer set by [`with_jit_interp`] around the JIT call.
//!
//! This is the standard "FFI host callback" pattern. Safety relies
//! on:
//! - The thread-local is non-null only inside `with_jit_interp`'s
//!   closure body.
//! - JIT'd code runs synchronously inside that body.
//! - The pointer remains valid (the caller borrows the interpreter
//!   mutably for the duration).

use std::cell::Cell;

use crate::interpreter::{InterpError, Interpreter, StepResult};
use crate::poly_word::PolyWord;

thread_local! {
    /// Pointer to the currently-active `Interpreter` for JIT
    /// trampoline callbacks. `null` outside a [`with_jit_interp`]
    /// scope.
    pub static JIT_INTERP: Cell<*mut Interpreter> =
        const { Cell::new(std::ptr::null_mut()) };

    /// Rust call-depth counter for JIT-to-JIT dispatch. Each direct
    /// `entry.func` invocation increments; on RAII drop it decrements.
    /// When the counter exceeds [`MAX_JIT_DEPTH`], we fall back to
    /// the interpreter loop to avoid blowing the OS thread stack on
    /// deeply recursive bootstrap workloads (e.g. entry [52]'s
    /// mutually-recursive callees would otherwise overflow ~8 MB of
    /// Rust thread stack).
    pub static JIT_DEPTH: Cell<usize> = const { Cell::new(0) };
}

/// Soft cap on JIT-to-JIT recursion depth (used by
/// `jit_dispatch_closure_call`). Set to 0 to disable nested JIT-to-JIT
/// entirely — nested calls from JIT'd code go back through the
/// interpreter.
///
/// STATUS (2026-06-12): nested JIT→JIT is now CORRECTNESS-CLEAN when
/// enabled — probing `MAX_JIT_DEPTH = 256` with the full 727-install
/// set runs the simple bootstrap AND the basis load (1.675B steps, deep
/// mutual recursion) to Tagged(0) with NO SEGV and NO OS-stack
/// overflow. The old "separate bug that SEGVs at install=53" was the
/// same wrong-args/wrong-pop-order family fixed by the args_buf
/// (598f312) and TAIL_B_B (88134d3) work — it no longer reproduces.
///
/// It stays 0 anyway for two reasons:
///   1. PERF-NEUTRAL on the current workload — only ~1.6% of dynamic
///      CALL dispatches hit the JIT cache (the HOT functions aren't
///      installed: they contain still-blocked opcodes — CALL_LOCAL_B,
///      CALL_CONST_ADDR, the untranslatable CASE16 tail, ESCAPE).
///      Enabling nesting measured 25.3s vs 25.2s on the basis load
///      (noise); the binding constraint is hot-function COVERAGE, not
///      dispatch depth. Turn this on only once coverage of the hot path
///      improves enough for the fast path to matter.
///   2. Each nested fast-path call adds a real Rust frame (plus a small
///      args_buf alloc); a high cap on pathologically deep recursion
///      could still approach the ~8 MB OS thread stack. A non-zero cap
///      bounds that, but the interp's managed PolyWord stack has no such
///      limit, so 0 (= always fall back to interp for nesting) is the
///      safe default until there's a perf reason to change it.
/// The outermost JIT dispatch — from `Interpreter::do_call` when the
/// interpreter's CALL opcode hits a JIT-cached function — is gated
/// separately on `JIT_INTERP` being null, so this cap doesn't disable
/// the top-level JIT.
pub const MAX_JIT_DEPTH: usize = 0;

/// Run `f` with the thread-local interpreter pointer set to
/// `&mut *interp`. Restores the previous value (typically null) on
/// exit, including on panic.
///
/// `f` typically calls into JIT'd code that may invoke trampolines
/// like [`jit_dispatch_closure_call`].
pub fn with_jit_interp<R>(interp: &mut Interpreter, f: impl FnOnce() -> R) -> R {
    struct Guard {
        prev: *mut Interpreter,
    }
    impl Drop for Guard {
        fn drop(&mut self) {
            JIT_INTERP.with(|c| c.set(self.prev));
        }
    }
    let prev = JIT_INTERP.with(|c| {
        let p = c.get();
        c.set(interp as *mut Interpreter);
        p
    });
    let _g = Guard { prev };
    f()
}

/// Trampoline-callable: allocate `n_words` of uninitialized bytes
/// with the given `flags` byte. Used by JIT'd `ALLOC_BYTE_MEM`.
///
/// The bytes are NOT initialized — the caller is expected to write
/// them before reading (`STORE_ML_BYTE`/`STORE_ML_WORD`).
pub fn jit_dispatch_alloc_bytes(n_words: usize, flags: u8) -> Option<u64> {
    let interp_ptr = JIT_INTERP.with(|c| c.get());
    if interp_ptr.is_null() {
        return None;
    }
    // SAFETY: caller invariant.
    let interp = unsafe { &mut *interp_ptr };
    let space = interp.jit_alloc_space_mut()?;
    let body = space.try_alloc(n_words)?;
    // SAFETY: just allocated n_words.
    unsafe {
        crate::space::set_length_word(body, n_words, flags);
    }
    Some(body as u64)
}

/// Trampoline-callable: dynamic CALL_CLOSURE dispatch.
///
/// The JIT'd caller has popped the closure (it's `closure_word`) and
/// spilled its remaining compile-time stack — the top of which holds
/// the N call args — into a buffer at `args_ptr` of length
/// `args_depth` PolyWord-bits values. The args are stored such that
/// `args_ptr[args_depth - N..args_depth]` is the SML's TOP N values,
/// in stack-bottom-to-top order (= args_ptr[args_depth-1] is the
/// topmost-pushed = arg_(N-1); args_ptr[args_depth-N] is arg_0).
///
/// The trampoline reads N (callee arity) from the closure's code-
/// header (`enter_int` marker + arity byte), then dispatches to the
/// existing `jit_dispatch_closure_call` machinery with exactly those
/// N args. Returns the callee's result as raw PolyWord bits.
///
/// Tail-call only: the JIT'd caller is expected to RETURN this value
/// immediately. The trampoline doesn't try to maintain caller-side
/// stack state for further bytecode execution.
pub unsafe fn jit_dispatch_dynamic_call(
    closure_word: u64,
    args_ptr: *const i64,
    args_depth: i64,
) -> Result<PolyWord, InterpError> {
    let closure = PolyWord::from_bits(closure_word as usize);
    if !closure.is_data_ptr() {
        return Err(InterpError::NotAClosure(closure));
    }
    // Read the closure's code object and inspect its enter-int header
    // to determine callee arity.
    // SAFETY: closure is a data pointer to a closure object.
    let code_word = unsafe { *closure.as_ptr::<PolyWord>() };
    if !code_word.is_data_ptr() {
        return Err(InterpError::NotAClosure(closure));
    }
    let code_ptr = code_word.as_ptr::<u8>();
    // SAFETY: code object starts with at least 2 bytes (enter-int).
    let (marker, arity_byte) = unsafe { (*code_ptr, *code_ptr.add(1)) };
    // x86-64 marker is 0xff, ARM64 is 0xe9; second byte is
    // `arity | 0x80` (the 0x80 bit distinguishes from raw opcodes).
    let n = if (marker == 0xff || marker == 0xe9) && (arity_byte & 0x80) != 0 {
        (arity_byte & 0x7f) as usize
    } else {
        // No enter-int prologue — fall back to scanning forward in
        // the code object for the first RETURN_N. Standard pattern
        // for closures whose compiler didn't emit an enter-int marker.
        //
        // The scan MUST stay inside the code object's allocated bytes:
        // the old fixed `scan_pc < 512` window read past the end of any
        // code object smaller than 512 bytes (and the RETURN_B/W arms
        // below stepped one or two bytes further still), an OOB read /
        // potential SEGV on a small object near a page boundary. Bound
        // the window to the object's true byte length (length-word in
        // words × word size) capped at 512 (real bodies are <200 bytes,
        // and this path is only the missing-enter-int fallback).
        // SAFETY: code_word is a verified data pointer to a code object,
        // so its length-word sits one word below `code_ptr`.
        let code_byte_len = unsafe {
            let lw = crate::space::MemorySpace::length_word_of(code_word.as_ptr::<PolyWord>());
            crate::length_word::length_of(lw) * std::mem::size_of::<usize>()
        };
        let window = code_byte_len.min(512);
        let mut scan_pc = 0usize;
        let mut inferred = None;
        while scan_pc < window {
            // SAFETY: scan_pc < window <= code_byte_len, so this byte is
            // within the object. The multi-byte RETURN_B/W arms guard
            // their trailing operand bytes against `code_byte_len`.
            let b = unsafe { *code_ptr.add(scan_pc) };
            match b {
                0x42 => {
                    inferred = Some(1);
                    break;
                } // RETURN_1
                0x43 => {
                    inferred = Some(2);
                    break;
                } // RETURN_2
                0x44 => {
                    inferred = Some(3);
                    break;
                } // RETURN_3
                0x1f => {
                    // RETURN_B: next byte is arity
                    if scan_pc + 1 >= code_byte_len {
                        break;
                    }
                    let n_imm = unsafe { *code_ptr.add(scan_pc + 1) };
                    inferred = Some(n_imm as usize);
                    break;
                }
                0x0d => {
                    // RETURN_W: next two bytes are u16 LE arity
                    if scan_pc + 2 >= code_byte_len {
                        break;
                    }
                    let lo = unsafe { *code_ptr.add(scan_pc + 1) } as usize;
                    let hi = unsafe { *code_ptr.add(scan_pc + 2) } as usize;
                    inferred = Some(lo | (hi << 8));
                    break;
                }
                _ => scan_pc += 1,
            }
        }
        match inferred {
            Some(n) => n,
            None => return Err(InterpError::NotAClosure(closure)),
        }
    };
    #[allow(clippy::cast_sign_loss)]
    let depth = args_depth.max(0) as usize;
    if n > depth {
        return Err(InterpError::StackUnderflow);
    }
    // Build a slice of the N topmost args (in stack-bottom-to-top
    // order: slice[0] = arg_0 = deepest pushed = args_ptr[depth-N];
    // slice[N-1] = arg_(N-1) = topmost = args_ptr[depth-1]).
    let arg_slice: Vec<PolyWord> = unsafe {
        (0..n)
            .map(|i| {
                let raw = args_ptr.add(depth - n + i).read();
                PolyWord::from_bits(raw as usize)
            })
            .collect()
    };
    // Delegate to the existing dynamic-dispatch machinery, which
    // already handles closure → code-obj → callee execution.
    jit_dispatch_closure_call(closure, &arg_slice)
}

/// Trampoline-callable: allocate a mutable closure of `n_captures + 1`
/// words. Slot 0 is copied from `src_closure[0]` (the code address);
/// slots 1..n_captures+1 are initialized to tagged(0) — they get
/// filled in later by `MOVE_TO_MUT_CLOSURE_B` instructions.
///
/// Flags: F_CLOSURE_OBJ | F_MUTABLE_BIT.
pub fn jit_dispatch_alloc_mut_closure(n_captures: usize, src_closure_word: u64) -> Option<u64> {
    let interp_ptr = JIT_INTERP.with(|c| c.get());
    if interp_ptr.is_null() {
        return None;
    }
    // SAFETY: caller invariant.
    let interp = unsafe { &mut *interp_ptr };
    let src = PolyWord::from_bits(src_closure_word as usize);
    if !src.is_data_ptr() {
        return None;
    }
    // SAFETY: source closure is a data pointer.
    let code_addr_word = unsafe { *src.as_ptr::<PolyWord>() };
    let space = interp.jit_alloc_space_mut()?;
    let n_words = n_captures + 1;
    let body = space.try_alloc(n_words)?;
    // SAFETY: body has n_words slots.
    unsafe {
        crate::space::set_length_word(
            body,
            n_words,
            crate::length_word::F_CLOSURE_OBJ | crate::length_word::F_MUTABLE_BIT,
        );
        body.write(code_addr_word);
        for i in 0..n_captures {
            body.add(1 + i).write(PolyWord::tagged(0));
        }
    }
    Some(body as u64)
}

/// Trampoline-callable: allocate a stub thread object — an 8-word
/// mutable cell with all words = tagged(0). Mirrors the interpreter's
/// `INSTR_GET_THREAD_ID` semantics.
///
/// We don't have real threads, so any read of the thread object's
/// fields returns zero. This is enough for SML code that only reads
/// the thread-id pointer for identity checks.
pub fn jit_dispatch_get_thread_id() -> Option<u64> {
    let interp_ptr = JIT_INTERP.with(|c| c.get());
    if interp_ptr.is_null() {
        return None;
    }
    // SAFETY: caller invariant.
    let interp = unsafe { &mut *interp_ptr };
    // Route through the SAME cached singleton the interpreter's INSTR_GET_THREAD_ID
    // uses, so Thread.self() identity is stable across interp/JIT and Thread.setLocal/
    // getLocal (and hence Thread_Data / Isabelle's generic context) round-trip. The
    // old code allocated a FRESH object every JIT call. The cached object is already
    // GC-forwarded as a root (interpreter mod.rs gc()).
    interp.alloc_stub_thread_object().ok().map(|w| w.0 as u64)
}

/// Trampoline-callable: build a closure object. The closure layout
/// is `[code_addr, capture_0, capture_1, ...]` where `code_addr`
/// is copied from `src_closure[0]`. Length word is `n_captures + 1`
/// with `F_CLOSURE_OBJ` flag.
///
/// # Safety
/// `src_closure_word` must be a valid PolyWord-bits value pointing
/// at a heap closure object. `captures_ptr` must point at
/// `n_captures` valid PolyWord-bits values.
pub unsafe fn jit_dispatch_closure_alloc(
    n_captures: usize,
    captures_ptr: *const i64,
    src_closure_word: u64,
) -> Option<u64> {
    let interp_ptr = JIT_INTERP.with(|c| c.get());
    if interp_ptr.is_null() {
        return None;
    }
    // SAFETY: caller invariant.
    let interp = unsafe { &mut *interp_ptr };
    let src = PolyWord::from_bits(src_closure_word as usize);
    if !src.is_data_ptr() {
        return None;
    }
    // SAFETY: source closure is a data pointer.
    let code_addr_word = unsafe { *src.as_ptr::<PolyWord>() };
    let space = interp.jit_alloc_space_mut()?;
    let n_words = n_captures + 1;
    let body = space.try_alloc(n_words)?;
    // SAFETY: body has n_words slots; captures_ptr has n_captures valid words.
    unsafe {
        crate::space::set_length_word(body, n_words, crate::length_word::F_CLOSURE_OBJ);
        // slot 0 = code address
        body.write(code_addr_word);
        // slots 1..n_captures+1 = captures
        for i in 0..n_captures {
            let cap = captures_ptr.add(i).read();
            body.add(1 + i).write(PolyWord::from_bits(cap as usize));
        }
    }
    Some(body as u64)
}

/// Trampoline-callable: allocate an `n_words` tuple/ref/closure
/// object in the interpreter's alloc space and copy `values_ptr[0..n]`
/// into the body. Returns the heap pointer as raw bits.
///
/// `flags` is the length-word flag byte (e.g. 0 for ordinary tuple,
/// 0x03 for closure, 0x01 for mutable). Default callers use 0.
///
/// # Safety
/// `values_ptr` must point at `n_words` valid `PolyWord` bits.
/// The thread-local interp must be set (via [`with_jit_interp`]).
pub unsafe fn jit_dispatch_alloc(n_words: usize, flags: u8, values_ptr: *const i64) -> Option<u64> {
    let interp_ptr = JIT_INTERP.with(|c| c.get());
    if interp_ptr.is_null() {
        return None;
    }
    // SAFETY: caller invariant.
    let interp = unsafe { &mut *interp_ptr };
    let space = interp.jit_alloc_space_mut()?;
    let body = space.try_alloc(n_words)?;
    // SAFETY: body is a freshly-allocated n_words region; values_ptr
    // contains n_words readable PolyWord bits.
    unsafe {
        crate::space::set_length_word(body, n_words, flags);
        for i in 0..n_words {
            let v = values_ptr.add(i).read();
            body.add(i).write(PolyWord::from_bits(v as usize));
        }
    }
    Some(body as u64)
}

/// Trampoline-callable: dispatch a closure call by setting up the
/// interpreter's stack and running until the call's top-level
/// return fires (sentinel retPC = 0).
///
/// `args` are passed in JIT calling convention: `args[0]` is the
/// SML-arity-0th argument (= `LOCAL_{N+1}` in the callee's frame).
///
/// Returns the closure's result as a `PolyWord` (raw bits).
///
/// # Errors
/// Forwards [`InterpError`]s from the nested interpreter run.
// `cur_depth < MAX_JIT_DEPTH` is always false while MAX_JIT_DEPTH == 0 (nested
// JIT→JIT dispatch is intentionally disabled); the comparison is the re-enable
// knob, meaningful only once MAX_JIT_DEPTH is bumped above 0.
#[allow(clippy::absurd_extreme_comparisons)]
pub fn jit_dispatch_closure_call(
    closure: PolyWord,
    args: &[PolyWord],
) -> Result<PolyWord, InterpError> {
    let interp_ptr = JIT_INTERP.with(|c| c.get());
    if interp_ptr.is_null() {
        return Err(InterpError::NotAClosure(closure));
    }
    // SAFETY: caller of `with_jit_interp` holds the borrow.
    let interp = unsafe { &mut *interp_ptr };

    // Fast path: if the closure's code object has a JIT-cached
    // entry, dispatch to it directly (no interpreter frame setup).
    // This handles JIT-to-JIT calls without wasted interp work.
    if !closure.is_data_ptr() {
        return Err(InterpError::NotAClosure(closure));
    }
    let closure_ptr_word = closure.as_ptr::<PolyWord>();
    // SAFETY: closure is a data pointer.
    let code_word = unsafe { *closure_ptr_word };
    let code_obj_addr = code_word.0;
    // Fast path: dispatch via JIT cache when there's headroom on the
    // Rust thread stack. Each direct `entry.func` invocation adds a
    // Rust call frame; without a depth cap, deeply recursive
    // bootstrap functions (entry [52] and its callees) blow ~8 MB of
    // OS thread stack via JIT-↔-interp ping-pong.
    let cur_depth = JIT_DEPTH.with(|c| c.get());
    if cur_depth < MAX_JIT_DEPTH
        && let Some(entry) = interp.jit_lookup(code_obj_addr)
    {
        if crate::env::env_flag("JIT_TRACE_CALLS") {
            eprintln!(
                "  jit_dispatch_closure_call: JIT→JIT code_obj=0x{code_obj_addr:016x} arity={} depth={cur_depth}",
                entry.sml_arity,
            );
        }
        struct DepthGuard;
        impl Drop for DepthGuard {
            fn drop(&mut self) {
                JIT_DEPTH.with(|c| c.set(c.get().saturating_sub(1)));
            }
        }
        JIT_DEPTH.with(|c| c.set(cur_depth + 1));
        let _g = DepthGuard;
        // Build args_ptr per JIT convention. Slot N+1 must be the
        // real closure pointer so `INDIRECT_CLOSURE_BN` doesn't
        // null-deref (same pattern as `Interpreter::do_call`).
        let mut args_buf: Vec<i64> = Vec::with_capacity(entry.arity_init);
        for arg in args {
            args_buf.push(arg.0 as i64);
        }
        if args_buf.len() < entry.arity_init {
            args_buf.push(0); // retPC placeholder
        }
        if args_buf.len() < entry.arity_init {
            args_buf.push(closure.0 as i64); // real closure
        }
        while args_buf.len() < entry.arity_init {
            args_buf.push(0);
        }
        // SAFETY: entry.func registered with matching ABI. sp_in
        // and stack_base are reserved for Phase-2 of the stack-
        // pointer refactor; current code ignores them.
        #[allow(clippy::cast_possible_wrap)]
        let sp_in_i64 = interp.jit_current_sp() as i64;
        let stack_base = interp.jit_stack_base_mut() as i64;
        let result = unsafe { (entry.func)(args_buf.as_ptr(), sp_in_i64, stack_base) };
        return Ok(PolyWord::from_bits(result as usize));
    }

    if crate::env::env_flag("JIT_TRACE_CALLS") {
        eprintln!(
            "  jit_dispatch_closure_call: JIT→interp code_obj=0x{code_obj_addr:016x} args={}",
            args.len(),
        );
    }
    // Save state we restore on return.
    let saved = interp.jit_state_save();

    // Push the call-frame manually (bypassing do_call so the closure's
    // RETURN_N sees our retPC=0 sentinel rather than a real PC):
    //
    //   sp_after_push (top → bottom):
    //     closure
    //     retPC = 0  (sentinel)
    //     arg_{N-1}
    //     ...
    //     arg_0
    //
    // The JIT-call convention says `args[0]` is arg_0 (the
    // first-pushed by the caller). We push them in order, so arg_0
    // ends up deepest as upstream's calling convention expects.
    for arg in args {
        interp.seed_push(*arg);
    }
    interp.seed_push(PolyWord::from_bits(0)); // retPC sentinel
    interp.seed_push(closure);
    interp.jit_set_code_segment_to_closure(closure)?;

    let trace_step = crate::env::env_flag("JIT_TRAMP_STEP_TRACE");
    let trace_each = crate::env::env_flag("JIT_TRAMP_STEP_ALL");
    let mut inner_steps = 0u64;
    if trace_step {
        use std::io::Write;
        let (cs, ce) = interp.peek_code_seg_for_debug();
        let len = (ce as usize).saturating_sub(cs as usize).min(64);
        let bytes: Vec<u8> = (0..len).map(|i| unsafe { *cs.add(i) }).collect();
        let hex = bytes
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<Vec<_>>()
            .join(" ");
        let _ = writeln!(
            std::io::stderr(),
            "    [tramp ENTER] code=0x{:016x} len={len} bytes: {hex}",
            cs as usize,
        );
        // Dump stack top 12 items at entry
        let sp = interp.peek_sp_for_debug();
        for i in 0..12usize {
            let val = interp.peek_stack_for_debug(sp + i);
            let _ = writeln!(
                std::io::stderr(),
                "    [tramp ENTER stack] sp[{i:2}] = 0x{val:016x}",
            );
        }
        let _ = std::io::stderr().flush();
    }
    let result = loop {
        if trace_step {
            inner_steps += 1;
            let should_print = trace_each || inner_steps <= 10 || inner_steps % 100 == 0;
            if should_print {
                use std::io::Write;
                let pc = interp.peek_pc_for_debug() as usize;
                let (cs, ce) = interp.peek_code_seg_for_debug();
                let opcode_byte: i64 = if pc >= cs as usize && pc < ce as usize {
                    let b: u8 = unsafe { *(pc as *const u8) };
                    b as i64
                } else {
                    -1
                };
                let sp = interp.peek_sp_for_debug();
                // Dump next 4 bytes (immediates) for context
                let next_bytes: Vec<String> = (1..=4)
                    .map(|i| {
                        if pc + i < ce as usize {
                            let b = unsafe { *((pc + i) as *const u8) };
                            format!("{b:02x}")
                        } else {
                            "--".into()
                        }
                    })
                    .collect();
                let _ = writeln!(
                    std::io::stderr(),
                    "    [tramp step {inner_steps}] sp={sp:5} pc_off=0x{:04x} op=0x{opcode_byte:02x} next={}",
                    pc.saturating_sub(cs as usize),
                    next_bytes.join(" "),
                );
                let _ = std::io::stderr().flush();
            }
        }
        match interp.step() {
            Ok(StepResult::Continue) => continue,
            Ok(StepResult::Returned(v)) => break v,
            Ok(_) => {
                interp.jit_state_restore(saved);
                return Err(InterpError::UnhandledException);
            }
            Err(e) => {
                interp.jit_state_restore(saved);
                return Err(e);
            }
        }
    };

    interp.jit_state_restore(saved);
    Ok(result)
}
