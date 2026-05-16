//! Runtime services (RTS) dispatch table.
//!
//! PolyML's compiler emits `CALL_FAST_RTS0..5` opcodes for fast paths
//! to built-in C functions: arbitrary-precision arithmetic, I/O,
//! threading primitives, code-object manipulation, and so on. Each
//! such function is identified by a name (e.g. `PolyAddArbitrary`)
//! and is referenced from the bytecode via a special `EntryPoint`
//! heap object.
//!
//! In upstream PolyML, the C runtime at load time resolves each name
//! to a real C function pointer and writes that pointer into the first
//! word of the entry point object. The interpreter then dereferences
//! the object to invoke the function.
//!
//! In our Rust runtime we use a similar pattern, except the "function
//! pointer" written into the entry point is an **index** into the
//! [`RtsTable`] held by the interpreter. This avoids needing to
//! convert between C and Rust ABIs, and makes dispatch fully
//! type-safe.
//!
//! ## Encoding in the entry-point object
//!
//! - Word 0 of an `EntryPoint` object is initialised by [`crate::load_image`]
//!   to zero.
//! - After load, [`patch_entry_points`] looks up each entry point's
//!   name in the supplied [`RtsTable`] and writes back an opaque
//!   token (the entry's index + 1, so 0 still means "unresolved").
//! - At dispatch time, [`Interpreter`](crate::Interpreter) reads word
//!   0 to obtain the table index and invokes the function with the
//!   appropriate arity.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};

use crate::poly_word::PolyWord;

/// When true, every RTS stub call logs to stderr. Used for debugging
/// which RTS functions are on the critical path before they're really
/// implemented.
static RTS_TRACE: AtomicBool = AtomicBool::new(false);

/// Enable or disable RTS call tracing.
pub fn set_rts_trace(on: bool) {
    RTS_TRACE.store(on, Ordering::Relaxed);
}

/// Is tracing currently enabled?
#[must_use]
pub fn is_traced() -> bool {
    RTS_TRACE.load(Ordering::Relaxed)
}

/// Public entry for the interpreter's dispatch site to log a call.
pub fn trace_call(name: &str, n_args: usize) {
    if RTS_TRACE.load(Ordering::Relaxed) {
        eprintln!("  RTS  {name}({n_args} args)");
    }
}


// ---- RtsFn ------------------------------------------------------------

/// A registered RTS function. Each variant covers one arity; the
/// interpreter dispatches to the matching variant based on which
/// `CALL_FAST_RTS<N>` opcode it's executing.
///
/// Functions receive raw `PolyWord` arguments — the interpreter does
/// no tag interpretation. The function is responsible for any
/// untagging, allocation, etc.
#[derive(Copy, Clone)]
pub enum RtsFn {
    Arity0(fn(&mut RtsContext<'_>) -> PolyWord),
    Arity1(fn(&mut RtsContext<'_>, PolyWord) -> PolyWord),
    Arity2(fn(&mut RtsContext<'_>, PolyWord, PolyWord) -> PolyWord),
    Arity3(fn(&mut RtsContext<'_>, PolyWord, PolyWord, PolyWord) -> PolyWord),
    Arity4(fn(&mut RtsContext<'_>, PolyWord, PolyWord, PolyWord, PolyWord) -> PolyWord),
    Arity5(fn(&mut RtsContext<'_>, PolyWord, PolyWord, PolyWord, PolyWord, PolyWord) -> PolyWord),
}

impl RtsFn {
    #[must_use]
    pub const fn arity(self) -> usize {
        match self {
            Self::Arity0(_) => 0,
            Self::Arity1(_) => 1,
            Self::Arity2(_) => 2,
            Self::Arity3(_) => 3,
            Self::Arity4(_) => 4,
            Self::Arity5(_) => 5,
        }
    }
}

/// Context handed to an RTS function. For now, this is just access
/// to the interpreter's allocation space, but it'll grow to include
/// I/O, threading state, etc. as we implement more functions.
pub struct RtsContext<'a> {
    pub alloc_space: Option<&'a mut crate::space::MemorySpace>,
}

// ---- RtsTable ---------------------------------------------------------

/// A registry of named RTS functions. Used by the loader to patch
/// EntryPoint objects, and by the interpreter to dispatch
/// `CALL_FAST_RTS*` opcodes.
pub struct RtsTable {
    /// Index 0 is reserved as "unresolved" — the loader writes
    /// (entry_index + 1) into entry-point objects, so reading 0 from
    /// an entry point means it was never patched.
    entries: Vec<RtsEntry>,
    /// Lookup by name.
    by_name: HashMap<&'static str, usize>,
}

#[derive(Clone)]
pub struct RtsEntry {
    pub name: &'static str,
    pub func: RtsFn,
}

impl Default for RtsTable {
    fn default() -> Self {
        Self::new()
    }
}

impl RtsTable {
    /// Empty table. Use `Self::default()` to get the built-ins
    /// preloaded.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            entries: Vec::new(),
            by_name: HashMap::new(),
        }
    }

    /// Table preloaded with the built-in implementations of the
    /// architecture-query and simplest functions. Functions we
    /// haven't implemented yet are NOT registered — the loader will
    /// leave their entry points unpatched, and the interpreter will
    /// trap when bytecode tries to call them. (Easier to get a
    /// `MissingRtsFunction` error than to silently produce wrong
    /// results.)
    #[must_use]
    pub fn new() -> Self {
        let mut t = Self::empty();
        register_builtins(&mut t);
        t
    }

    /// Register a function. Returns the assigned index (1-based;
    /// 0 is reserved for "unresolved").
    pub fn register(&mut self, name: &'static str, func: RtsFn) -> usize {
        let token = self.entries.len() + 1;
        self.entries.push(RtsEntry { name, func });
        self.by_name.insert(name, token);
        token
    }

    /// Look up a name → token. Returns `Some(token)` if registered,
    /// `None` otherwise.
    #[must_use]
    pub fn token_for(&self, name: &str) -> Option<usize> {
        self.by_name.get(name).copied()
    }

    /// Resolve a token (1-based) to its entry. `token == 0` returns
    /// None.
    #[must_use]
    pub fn entry(&self, token: usize) -> Option<&RtsEntry> {
        if token == 0 {
            None
        } else {
            self.entries.get(token - 1)
        }
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

// ---- Loader-time patching ---------------------------------------------

/// Walk `LoadedImage::entry_points` and patch each one whose name is
/// found in `table`. Returns `(patched, unmatched_names)`.
///
/// "Patched" means: word 0 of the entry-point object now holds
/// `PolyWord::from_bits(token)` where `token = table.token_for(name)`.
/// Unmatched names are left with their word 0 as zero (the loader's
/// initial value).
pub fn patch_entry_points(
    loaded: &mut crate::loader::LoadedImage,
    table: &RtsTable,
) -> (usize, Vec<String>) {
    let mut patched = 0;
    let mut missing = Vec::new();
    for (name, ptr) in &loaded.entry_points {
        if let Some(token) = table.token_for(name.as_str()) {
            // SAFETY: ptr came from our loader and points at a live
            // entry-point object; word 0 is the reserved
            // function-pointer slot.
            unsafe {
                ptr.cast::<PolyWord>().write(PolyWord::from_bits(token));
            }
            patched += 1;
        } else {
            missing.push(name.clone());
        }
    }
    (patched, missing)
}

// ---- Built-in RTS functions ------------------------------------------

fn register_builtins(t: &mut RtsTable) {
    t.register("PolyIsBigEndian", RtsFn::Arity0(poly_is_big_endian));
    t.register("PolySizeDouble", RtsFn::Arity0(poly_size_double));
    t.register("PolySizeFloat", RtsFn::Arity0(poly_size_float));
    t.register("PolyFinish", RtsFn::Arity1(poly_finish));
    t.register(
        "PolyInterpretedEnterIntMode",
        RtsFn::Arity0(poly_interpreted_enter_int_mode),
    );
    t.register(
        "PolyInterpretedGetAbiList",
        RtsFn::Arity0(poly_interpreted_get_abi_list),
    );
    t.register("PolyThreadMaxStackSize", RtsFn::Arity1(poly_thread_max_stack_size));
    t.register(
        "PolyGetCommandlineArguments",
        RtsFn::Arity1(poly_get_commandline_arguments),
    );
    t.register("PolyThreadKillSelf", RtsFn::Arity1(poly_thread_kill_self));
    t.register(
        "PolyThreadTestInterrupt",
        RtsFn::Arity1(poly_thread_test_interrupt),
    );
    t.register(
        "PolyProcessEnvErrorName",
        RtsFn::Arity1(poly_process_env_error_name),
    );
    t.register("PolyWaitForSignal", RtsFn::Arity1(poly_wait_for_signal));
    t.register("PolyGetFunctionName", RtsFn::Arity1(poly_get_function_name));

    // ----- Stubs for the rest. These return TAGGED(0) and will
    // produce *incorrect* results when actually used, but they let
    // the interpreter run past the entry-point setup phase of
    // bootstrap so we can see what other opcodes / RTS calls come
    // up. Each one will need a real implementation eventually.
    //
    // Arities are taken from upstream C signatures in:
    //   vendor/polyml/libpolyml/{arb,basicio,threads,polyffi,run_time,
    //                            poly_specific,objsize,processes,...}.cpp

    // I/O: PolyBasicIOGeneral(threadId, code, strm, arg) → 4
    t.register("PolyBasicIOGeneral", RtsFn::Arity4(zero4));

    // Arbitrary precision (all take threadId, arg1, arg2 unless noted)
    t.register("PolyAddArbitrary", RtsFn::Arity3(zero3));
    t.register("PolySubtractArbitrary", RtsFn::Arity3(zero3));
    t.register("PolyMultiplyArbitrary", RtsFn::Arity3(zero3));
    t.register("PolyDivideArbitrary", RtsFn::Arity3(zero3));
    t.register("PolyRemainderArbitrary", RtsFn::Arity3(zero3));
    t.register("PolyQuotRemArbitraryPair", RtsFn::Arity3(zero3));
    t.register("PolyQuotRemArbitrary", RtsFn::Arity4(zero4));
    t.register("PolyCompareArbitrary", RtsFn::Arity2(zero2)); // no threadId
    t.register("PolyGCDArbitrary", RtsFn::Arity3(zero3));
    t.register("PolyLCMArbitrary", RtsFn::Arity3(zero3));
    t.register("PolyAndArbitrary", RtsFn::Arity3(zero3));
    t.register("PolyOrArbitrary", RtsFn::Arity3(zero3));
    t.register("PolyXorArbitrary", RtsFn::Arity3(zero3));
    t.register("PolyShiftLeftArbitrary", RtsFn::Arity3(zero3));
    t.register("PolyShiftRightArbitrary", RtsFn::Arity3(zero3));
    t.register("PolyGetLowOrderAsLargeWord", RtsFn::Arity2(zero2));

    // Threading
    //
    // PolyThreadMutexBlock(threadId, mutex): real impl in multi-thread
    // blocks until the mutex becomes free; in single-thread we can
    // never block on it (no other thread to release it), so we
    // assume it's already free and reset the mutex object to
    // TAGGED(0) (= unlocked). The caller's subsequent tryLockMutex
    // then succeeds and the SML `lock` retry loop exits.
    t.register("PolyThreadMutexBlock", RtsFn::Arity2(poly_thread_mutex_block));
    // PolyThreadMutexUnlock(threadId, mutex): reset to unlocked.
    // Mirrors InterpreterReleaseMutex (bytecode.cpp:2465).
    t.register("PolyThreadMutexUnlock", RtsFn::Arity2(poly_thread_mutex_unlock));
    t.register("PolyThreadCondVarWake", RtsFn::Arity2(zero2));
    // PolyThreadForkThread takes (threadId, function, attrs, stack) — 4 args.
    t.register("PolyThreadForkThread", RtsFn::Arity4(zero4));
    t.register("PolyThreadInterruptThread", RtsFn::Arity2(zero2));
    t.register("PolyThreadBroadcastInterrupt", RtsFn::Arity1(zero1));

    // Compiler / code-object helpers
    //   PolySetCodeConstant(threadId, code, offset, value, flags) → 5
    t.register("PolySetCodeConstant", RtsFn::Arity5(zero5));
    //   PolyGetCodeByte(threadId, code, offset) → 3
    t.register("PolyGetCodeByte", RtsFn::Arity3(zero3));
    //   PolyCopyByteVecToClosure(threadId, byteVec) → 2
    t.register("PolyCopyByteVecToClosure", RtsFn::Arity2(zero2));
    //   PolyLockMutableClosure(threadId, closure) → 2
    t.register("PolyLockMutableClosure", RtsFn::Arity2(zero2));

    // Interpreted-mode FFI
    //   PolyInterpretedCreateCIF(threadId, abi, resType, argTypes) → 4
    t.register("PolyInterpretedCreateCIF", RtsFn::Arity4(zero4));
    //   PolyInterpretedCallFunction(threadId, cif, cfun, res, argv) → 5
    t.register("PolyInterpretedCallFunction", RtsFn::Arity5(zero5));
    //   PolyCreateEntryPointObject(threadId, name, isFunc) → 3
    t.register("PolyCreateEntryPointObject", RtsFn::Arity3(zero3));
}

// Generic 0-returning stubs. The dispatch site (Interpreter::rts_call)
// handles tracing via `trace_call`, so no need to log here.
fn zero1(_: &mut RtsContext<'_>, _: PolyWord) -> PolyWord {
    PolyWord::tagged(0)
}
fn zero2(_: &mut RtsContext<'_>, _: PolyWord, _: PolyWord) -> PolyWord {
    PolyWord::tagged(0)
}
fn zero3(_: &mut RtsContext<'_>, _: PolyWord, _: PolyWord, _: PolyWord) -> PolyWord {
    PolyWord::tagged(0)
}
fn zero4(_: &mut RtsContext<'_>, _: PolyWord, _: PolyWord, _: PolyWord, _: PolyWord) -> PolyWord {
    PolyWord::tagged(0)
}
fn zero5(
    _: &mut RtsContext<'_>,
    _: PolyWord,
    _: PolyWord,
    _: PolyWord,
    _: PolyWord,
    _: PolyWord,
) -> PolyWord {
    PolyWord::tagged(0)
}

// ---- Built-in impls (real where simple, stubbed otherwise) -----------

#[allow(clippy::needless_pass_by_value)]
fn poly_is_big_endian(_: &mut RtsContext<'_>) -> PolyWord {
    // We support little-endian targets only (x86_64, aarch64, riscv64).
    PolyWord::tagged(0)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_size_double(_: &mut RtsContext<'_>) -> PolyWord {
    PolyWord::tagged(isize::try_from(std::mem::size_of::<f64>()).unwrap_or(8))
}

#[allow(clippy::needless_pass_by_value)]
fn poly_size_float(_: &mut RtsContext<'_>) -> PolyWord {
    PolyWord::tagged(isize::try_from(std::mem::size_of::<f32>()).unwrap_or(4))
}

/// `PolyFinish(code)` — process exit. We can't actually exit here
/// (we're inside the interpreter), so we just stash the value and
/// return zero. The caller of `Interpreter::run` should treat
/// subsequent returns as program termination.
#[allow(clippy::needless_pass_by_value)]
fn poly_finish(_: &mut RtsContext<'_>, _exit_code: PolyWord) -> PolyWord {
    PolyWord::tagged(0)
}

/// `PolyInterpretedEnterIntMode()` — switches the runtime into
/// interpreted mode. We're always in interpreted mode. Returns zero.
#[allow(clippy::needless_pass_by_value)]
fn poly_interpreted_enter_int_mode(_: &mut RtsContext<'_>) -> PolyWord {
    PolyWord::tagged(0)
}

/// Returns a list of ABIs supported by the interpreted-mode FFI. We
/// don't support FFI at all yet — return an empty list (= NIL =
/// TAGGED(0)).
#[allow(clippy::needless_pass_by_value)]
fn poly_interpreted_get_abi_list(_: &mut RtsContext<'_>) -> PolyWord {
    PolyWord::tagged(0) // nil
}

/// Returns the maximum stack size for the thread. Pass through (no-op
/// stub returning the requested value).
#[allow(clippy::needless_pass_by_value)]
fn poly_thread_max_stack_size(_: &mut RtsContext<'_>, arg: PolyWord) -> PolyWord {
    arg
}

/// `PolyGetCommandlineArguments(threadId)` — returns a list of cmd-line
/// arg strings. We return `["poly"]` so the bootstrap has something to
/// chew on (an empty list trips the bootstrap's no-args codepath which
/// then SIGSEGVs trying to read past nil).
///
/// PolyML list layout (basis/General.sml etc.):
///   nil        = TAGGED(0)
///   cons(h, t) = 2-word ordinary object [head, tail]
/// PolyML string layout (`PolyStringObject` in polystring.h):
///   1-word length prefix + N bytes + zero padding to word boundary,
///   all wrapped in a byte object.
#[allow(clippy::needless_pass_by_value)]
fn poly_get_commandline_arguments(ctx: &mut RtsContext<'_>, _tid: PolyWord) -> PolyWord {
    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::tagged(0);
    };
    // Allocate the string "poly": 1 length-prefix word + 1 word for 4 bytes.
    let name = b"poly";
    let str_words = 1 + name.len().div_ceil(std::mem::size_of::<usize>());
    let str_obj = space.alloc(str_words);
    // SAFETY: just allocated `str_words` words
    unsafe {
        crate::space::set_length_word(str_obj, str_words, crate::length_word::F_BYTE_OBJ);
        // Length-prefix word: number of chars.
        str_obj.add(0).write(PolyWord::from_bits(name.len()));
        // Chars
        let chars_ptr = str_obj.add(1).cast::<u8>();
        std::ptr::copy_nonoverlapping(name.as_ptr(), chars_ptr, name.len());
        // Zero-pad remaining bytes in the final word
        let pad = str_words * std::mem::size_of::<usize>() - std::mem::size_of::<usize>() - name.len();
        if pad > 0 {
            std::ptr::write_bytes(chars_ptr.add(name.len()), 0, pad);
        }
    }
    let str_word = PolyWord::from_ptr(str_obj.cast_const());

    // Allocate cons cell [str, nil]. F_MUTABLE_BIT NOT set — this is an
    // immutable list element.
    let cons = space.alloc(2);
    // SAFETY: just allocated 2 words
    unsafe {
        crate::space::set_length_word(cons, 2, 0); // ordinary word object
        cons.add(0).write(str_word);
        cons.add(1).write(PolyWord::tagged(0)); // nil tail
    }
    PolyWord::from_ptr(cons.cast_const())
}

#[allow(clippy::needless_pass_by_value)]
fn poly_thread_kill_self(_: &mut RtsContext<'_>, _tid: PolyWord) -> PolyWord {
    PolyWord::tagged(0)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_thread_test_interrupt(_: &mut RtsContext<'_>, _tid: PolyWord) -> PolyWord {
    PolyWord::tagged(0)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_process_env_error_name(_: &mut RtsContext<'_>, _arg: PolyWord) -> PolyWord {
    PolyWord::tagged(0)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_wait_for_signal(_: &mut RtsContext<'_>, _arg: PolyWord) -> PolyWord {
    PolyWord::tagged(0)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_get_function_name(_: &mut RtsContext<'_>, _code: PolyWord) -> PolyWord {
    PolyWord::tagged(0)
}

/// `PolyThreadMutexBlock(threadId, mutex)` — single-threaded
/// emulation: reset the mutex object's first word to TAGGED(0)
/// (= unlocked), so the caller's retry loop exits on its next
/// tryLockMutex.
#[allow(clippy::needless_pass_by_value)]
fn poly_thread_mutex_block(_: &mut RtsContext<'_>, _tid: PolyWord, mutex: PolyWord) -> PolyWord {
    reset_mutex(mutex);
    PolyWord::tagged(0)
}

/// `PolyThreadMutexUnlock(threadId, mutex)` — reset mutex to
/// TAGGED(0) (= unlocked). Mirrors `InterpreterReleaseMutex` in
/// `bytecode.cpp:2465`. (In multi-thread mode this also wakes
/// waiters; single-thread has none.)
#[allow(clippy::needless_pass_by_value)]
fn poly_thread_mutex_unlock(_: &mut RtsContext<'_>, _tid: PolyWord, mutex: PolyWord) -> PolyWord {
    reset_mutex(mutex);
    PolyWord::tagged(0)
}

fn reset_mutex(mutex: PolyWord) {
    if mutex.is_data_ptr() && mutex.0 & (std::mem::size_of::<usize>() - 1) == 0 {
        let p = mutex.as_ptr::<PolyWord>().cast_mut();
        // SAFETY: pointer-aligned & is_data_ptr → valid mutex slot
        unsafe { p.write(PolyWord::tagged(0)) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builtin_lookup() {
        let t = RtsTable::new();
        // Real impls
        assert!(t.token_for("PolyIsBigEndian").is_some());
        assert!(t.token_for("PolySizeDouble").is_some());
        // Stubs
        assert!(t.token_for("PolyBasicIOGeneral").is_some());
        assert!(t.token_for("PolyAddArbitrary").is_some());
        // Not registered → None (no `Polywhatever` function in the table)
        assert!(t.token_for("DoesNotExist").is_none());
    }

    #[test]
    fn arity_call_through_dispatch() {
        let t = RtsTable::new();
        let token = t.token_for("PolyIsBigEndian").unwrap();
        let entry = t.entry(token).unwrap();
        let mut ctx = RtsContext { alloc_space: None };
        let result = match entry.func {
            RtsFn::Arity0(f) => f(&mut ctx),
            _ => panic!("arity mismatch"),
        };
        assert_eq!(result.untag(), 0); // little-endian
    }

    #[test]
    fn token_zero_is_unresolved() {
        let t = RtsTable::new();
        assert!(t.entry(0).is_none());
    }
}
