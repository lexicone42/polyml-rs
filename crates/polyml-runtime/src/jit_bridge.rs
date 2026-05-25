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
/// interpreter. This avoids:
///   1. OS thread stack overflow on deeply recursive callees (each
///      JIT call adds a real Rust frame; the interp uses our
///      managed PolyWord stack instead).
///   2. A separate bug in the JIT-to-JIT path that SEGVs on certain
///      install counts (e.g. install=53). Diagnosing that bug is
///      future work.
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

/// Trampoline-callable: build a closure object. The closure layout
/// is `[code_addr, capture_0, capture_1, ...]` where `code_addr`
/// is copied from `src_closure[0]`. Length word is `n_captures + 1`
/// with `F_CLOSURE_OBJ` flag.
///
/// # Safety
/// `src_closure_word` must be a valid PolyWord-bits value pointing
/// at a heap closure object. `captures_ptr` must point at
/// `n_captures` valid PolyWord-bits values.
pub fn jit_dispatch_closure_alloc(
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
pub fn jit_dispatch_alloc(n_words: usize, flags: u8, values_ptr: *const i64) -> Option<u64> {
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
        if std::env::var("JIT_TRACE_CALLS").is_ok() {
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
        // SAFETY: entry.func registered with matching ABI.
        let result = unsafe { (entry.func)(args_buf.as_ptr()) };
        return Ok(PolyWord::from_bits(result as usize));
    }

    if std::env::var("JIT_TRACE_CALLS").is_ok() {
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
        interp.test_seed_top(*arg);
    }
    interp.test_seed_top(PolyWord::from_bits(0)); // retPC sentinel
    interp.test_seed_top(closure);
    interp.jit_set_code_segment_to_closure(closure)?;

    let trace_step = std::env::var("JIT_TRAMP_STEP_TRACE").is_ok();
    let trace_each = std::env::var("JIT_TRAMP_STEP_ALL").is_ok();
    let mut inner_steps = 0u64;
    if trace_step {
        use std::io::Write;
        let (cs, ce) = interp.peek_code_seg_for_debug();
        let len = (ce as usize).saturating_sub(cs as usize).min(64);
        let bytes: Vec<u8> = (0..len)
            .map(|i| unsafe { *cs.add(i) })
            .collect();
        let hex = bytes.iter().map(|b| format!("{b:02x}")).collect::<Vec<_>>().join(" ");
        let _ = writeln!(std::io::stderr(),
            "    [tramp ENTER] code=0x{:016x} len={len} bytes: {hex}",
            cs as usize,
        );
        // Dump stack top 12 items at entry
        let sp = interp.peek_sp_for_debug();
        for i in 0..12usize {
            let val = interp.peek_stack_for_debug(sp + i);
            let _ = writeln!(std::io::stderr(),
                "    [tramp ENTER stack] sp[{i:2}] = 0x{val:016x}",
            );
        }
        let _ = std::io::stderr().flush();
    }
    let result = loop {
        if trace_step {
            inner_steps += 1;
            let should_print =
                trace_each || inner_steps <= 10 || inner_steps % 100 == 0;
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
                let _ = writeln!(std::io::stderr(),
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
