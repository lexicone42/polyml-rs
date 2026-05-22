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
}

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
    if let Some(entry) = interp.jit_lookup(code_obj_addr) {
        // Build args_ptr per JIT convention.
        let mut args_buf: Vec<i64> = Vec::with_capacity(entry.arity_init);
        for arg in args {
            args_buf.push(arg.0 as i64);
        }
        while args_buf.len() < entry.arity_init {
            args_buf.push(0);
        }
        // SAFETY: entry.func registered with matching ABI.
        let result = unsafe { (entry.func)(args_buf.as_ptr()) };
        return Ok(PolyWord::from_bits(result as usize));
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

    let result = loop {
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
