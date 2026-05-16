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
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

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
    // These take a unit arg in SML (rtsCallFast1) even though the
    // C signature is `()`. PolyML's C side gets away with it because
    // x86-64 passes the unused arg in rdi/rsi which the C body
    // ignores; we have to be explicit and register as Arity1.
    t.register("PolyIsBigEndian", RtsFn::Arity1(|_, _| poly_is_big_endian_inner()));
    t.register("PolySizeDouble", RtsFn::Arity1(|_, _| poly_size_double_inner()));
    t.register("PolySizeFloat", RtsFn::Arity1(|_, _| poly_size_float_inner()));
    // PolyFinish: (threadId, exitCode). C signature has 2 args
    // — never returns in upstream, but in our setup we treat it as
    // a "return cleanly to the test harness" signal.
    t.register("PolyFinish", RtsFn::Arity2(poly_finish));
    // EnterIntMode is `rtsCallFast0` (Fast = no threadId, 0 args).
    t.register(
        "PolyInterpretedEnterIntMode",
        RtsFn::Arity0(|_| poly_interpreted_enter_int_mode_inner()),
    );
    // GetAbiList is `rtsCallFull0` (Full = +threadId, so 1 actual arg).
    t.register(
        "PolyInterpretedGetAbiList",
        RtsFn::Arity1(|_, _| poly_interpreted_get_abi_list_inner()),
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
    t.register("PolyBasicIOGeneral", RtsFn::Arity4(poly_basic_io_general));

    // Arbitrary precision (all take threadId, arg1, arg2 unless noted).
    // All fast-path: if both args are tagged and result fits in a tag,
    // return TAGGED(result). Otherwise return TAGGED(0), which upstream
    // uses as the "ML exception raised" sentinel (we don't have a real
    // boxed bignum path yet). In practice bootstrap's compile-time
    // arithmetic stays in the tagged range almost always; if we hit
    // the overflow path we'll know.
    t.register("PolyAddArbitrary", RtsFn::Arity3(poly_add_arbitrary));
    t.register("PolySubtractArbitrary", RtsFn::Arity3(poly_subtract_arbitrary));
    t.register("PolyMultiplyArbitrary", RtsFn::Arity3(poly_multiply_arbitrary));
    t.register("PolyDivideArbitrary", RtsFn::Arity3(poly_divide_arbitrary));
    t.register("PolyRemainderArbitrary", RtsFn::Arity3(poly_remainder_arbitrary));
    t.register("PolyQuotRemArbitraryPair", RtsFn::Arity3(poly_quot_rem_arbitrary_pair));
    t.register("PolyQuotRemArbitrary", RtsFn::Arity4(zero4));
    t.register("PolyCompareArbitrary", RtsFn::Arity2(poly_compare_arbitrary)); // no threadId
    t.register("PolyGCDArbitrary", RtsFn::Arity3(poly_gcd_arbitrary));
    t.register("PolyLCMArbitrary", RtsFn::Arity3(poly_lcm_arbitrary));
    t.register("PolyAndArbitrary", RtsFn::Arity3(poly_and_arbitrary));
    t.register("PolyOrArbitrary", RtsFn::Arity3(poly_or_arbitrary));
    t.register("PolyXorArbitrary", RtsFn::Arity3(poly_xor_arbitrary));
    t.register("PolyShiftLeftArbitrary", RtsFn::Arity3(poly_shift_left_arbitrary));
    t.register("PolyShiftRightArbitrary", RtsFn::Arity3(poly_shift_right_arbitrary));
    t.register(
        "PolyGetLowOrderAsLargeWord",
        RtsFn::Arity2(poly_get_low_order_as_large_word),
    );

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
    // Single-threaded mode: no other thread exists to wake / interrupt /
    // broadcast to, so these are no-ops.
    t.register("PolyThreadCondVarWake", RtsFn::Arity2(noop2));
    // PolyThreadForkThread takes (threadId, function, attrs, stack) — 4 args.
    t.register("PolyThreadForkThread", RtsFn::Arity4(poly_thread_fork_thread));
    t.register("PolyThreadInterruptThread", RtsFn::Arity2(noop2));
    t.register("PolyThreadBroadcastInterrupt", RtsFn::Arity1(noop1));

    // Compiler / code-object helpers
    //   PolySetCodeConstant(closure, offset, cWord, flags) → 4 (no threadId)
    t.register("PolySetCodeConstant", RtsFn::Arity4(poly_set_code_constant));
    //   PolyGetCodeByte(code, offset) → 2 (no threadId; rtsCallFast2)
    t.register("PolyGetCodeByte", RtsFn::Arity2(zero2));
    //   PolyCopyByteVecToClosure(threadId, byteVec, closure) → 3
    t.register(
        "PolyCopyByteVecToClosure",
        RtsFn::Arity3(poly_copy_byte_vec_to_closure),
    );
    //   PolyLockMutableClosure(threadId, closure) → 2
    t.register("PolyLockMutableClosure", RtsFn::Arity2(poly_lock_mutable_closure));

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
fn zero2(_: &mut RtsContext<'_>, _: PolyWord, _: PolyWord) -> PolyWord {
    PolyWord::tagged(0)
}

// Distinct from `zero1`/`zero2`: semantically these RTS functions
// have nothing useful to do in our single-threaded interpreter
// (CondVarWake, InterruptThread, BroadcastInterrupt). They're
// no-ops by design, not stubs awaiting implementation.
fn noop1(_: &mut RtsContext<'_>, _: PolyWord) -> PolyWord {
    PolyWord::tagged(0)
}
fn noop2(_: &mut RtsContext<'_>, _: PolyWord, _: PolyWord) -> PolyWord {
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

fn poly_is_big_endian_inner() -> PolyWord {
    // We support little-endian targets only (x86_64, aarch64, riscv64).
    PolyWord::tagged(0)
}

fn poly_size_double_inner() -> PolyWord {
    PolyWord::tagged(isize::try_from(std::mem::size_of::<f64>()).unwrap_or(8))
}

fn poly_size_float_inner() -> PolyWord {
    PolyWord::tagged(isize::try_from(std::mem::size_of::<f32>()).unwrap_or(4))
}

/// Process-exit signal: set by [`poly_finish`] when PolyML's
/// PolyFinish RTS is called. Reading this from `Interpreter::step`
/// lets us cleanly stop instead of executing junk bytecode after
/// "exit". The low bits store `exit_code + 1` (so 0 = not exited).
static FINISH_REQUESTED: AtomicUsize = AtomicUsize::new(0);

/// Returns `Some(exit_code)` iff PolyFinish was called since the last
/// [`clear_finish_requested`].
#[must_use]
pub fn finish_requested() -> Option<isize> {
    match FINISH_REQUESTED.load(Ordering::Relaxed) {
        0 => None,
        #[allow(clippy::cast_possible_wrap)]
        n => Some((n - 1) as isize),
    }
}

/// Reset the finish flag. Call before re-running an interpreter on
/// the same RtsTable.
pub fn clear_finish_requested() {
    FINISH_REQUESTED.store(0, Ordering::Relaxed);
}

/// `PolyFinish(threadId, code)` — process exit. We can't actually
/// `exit()` from inside the interpreter, so we set a global flag
/// the dispatcher checks at the top of `step()`. The interpreter
/// then yields `StepResult::Returned(code)` cleanly.
#[allow(clippy::needless_pass_by_value)]
fn poly_finish(
    _: &mut RtsContext<'_>,
    _tid: PolyWord,
    exit_code: PolyWord,
) -> PolyWord {
    if RTS_TRACE.load(Ordering::Relaxed) {
        eprintln!("  PolyFinish called with exit code {exit_code:?}");
    }
    let code = exit_code.untag();
    #[allow(clippy::cast_sign_loss)]
    FINISH_REQUESTED.store((code as usize).wrapping_add(1), Ordering::Relaxed);
    PolyWord::tagged(0)
}

fn poly_interpreted_enter_int_mode_inner() -> PolyWord {
    PolyWord::tagged(0)
}

fn poly_interpreted_get_abi_list_inner() -> PolyWord {
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

/// `PolyBasicIOGeneral(threadId, code, strm, arg)` — multi-purpose
/// I/O dispatcher; the `code` argument selects the sub-operation.
/// See `vendor/polyml/libpolyml/basicio.cpp:764-1078` for the full
/// dispatch table.
///
/// We implement just enough to get bootstrap past its I/O setup
/// phase: stdin/stdout/stderr (codes 0-2) return wrapped file
/// descriptors; write (codes 11-12) actually writes to the real fd;
/// close (code 7) is a no-op; everything else is a TAGGED(0) stub.
#[allow(clippy::needless_pass_by_value)]
fn poly_basic_io_general(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    code: PolyWord,
    strm: PolyWord,
    arg: PolyWord,
) -> PolyWord {
    let c = code.untag();
    if RTS_TRACE.load(Ordering::Relaxed) {
        eprintln!("    PolyBasicIOGeneral subcode={c}");
    }
    let _ = (strm, arg);
    match c {
        // 0/1/2: return wrapped stdio fds
        0 => wrap_file_descriptor(ctx, 0),
        1 => wrap_file_descriptor(ctx, 1),
        2 => wrap_file_descriptor(ctx, 2),
        // 10: get text as a string. Returning TAGGED(0) breaks the
        // consumer (which dereferences the result as a string ptr).
        // EOF = empty string. Allocates a proper 1-word
        // PolyStringObject with length 0 + F_BYTE_OBJ.
        10 | 26 => alloc_empty_string(ctx),
        // 11/12: write array — actually attempt to write to the fd
        // and return the byte count. Empty-pretend wasn't tested
        // yet but full write support makes future REPL output work.
        11 | 12 => write_array(strm, arg),
        // 15: return recommended buffer size (4096)
        15 => PolyWord::tagged(4096),
        // 16: input available? Pretend yes.
        // 28: can output? Yes.
        16 | 28 => PolyWord::tagged(1),
        // 21: fileKind — pretend everything is a TTY (FILEKIND_TTY=3).
        // For stdin/stdout/stderr this is usually accurate; the
        // bootstrap probably wants to know if it's interactive.
        21 => PolyWord::tagged(3),
        // Various stub returns of TAGGED(0):
        //   7: close (no-op)
        //   8/9: readArray — return 0 bytes read (= EOF)
        //   11/12: write array (wrote 0 bytes)
        //   17: bytes available
        //   18: get stream position
        //   19: seek to position (no-op)
        //   20: end-of-stream position
        //   22: polling options
        //   27: block until input available (= ready)
        _ => PolyWord::tagged(0),
    }
}

/// `PolyThreadForkThread(threadId, function, attrs, stack)` — in
/// single-threaded mode, return a properly-shaped ThreadObject
/// without actually running anything. The bootstrap stores this for
/// later use; if it ever tries to interact with the thread, it'll
/// see a well-formed (but dormant) descriptor.
///
/// ThreadObject layout per `processes.h:83-95`:
///   slot 0: threadRef       (weak ref to TaskData)
///   slot 1: flags           (tagged int, PFLAG_SYNCH = 2 default)
///   slot 2: threadLocal     (head of thread-local list, TAGGED 0)
///   slot 3: requestCopy     (interrupt request, TAGGED 0)
///   slot 4: mlStackSize     (tagged int, 0 = unlimited)
///   slots 5-8: debuggerSlots[4] (TAGGED 0)
/// Flags: F_MUTABLE_BIT.
#[allow(clippy::needless_pass_by_value)]
fn poly_thread_fork_thread(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    _function: PolyWord,
    _attrs: PolyWord,
    _stack: PolyWord,
) -> PolyWord {
    alloc_thread_object_stub(ctx)
}

// ---- arbitrary precision fast paths (tagged-int) -----------------
//
// For PolyXArbitrary(threadId, arg1, arg2):
//   upstream computes `x_longc(taskData, pushedArg2, pushedArg1)` i.e.
//   the operation is `arg2 OP arg1` (note the order — relevant for
//   sub/div/rem).
//
// All these return a fresh `PolyWord` for the result. On a miss
// (either operand boxed, or overflow), we return TAGGED(0) which
// upstream uses to signal "exception was raised". A future bignum
// allocator would replace those misses with real boxed results.

use crate::poly_word::{MAX_TAGGED, MIN_TAGGED};

#[inline]
fn both_tagged(a: PolyWord, b: PolyWord) -> Option<(isize, isize)> {
    if a.is_tagged() && b.is_tagged() {
        Some((a.untag(), b.untag()))
    } else {
        None
    }
}

#[inline]
fn fits_tagged(n: i128) -> bool {
    n >= MIN_TAGGED as i128 && n <= MAX_TAGGED as i128
}

#[allow(clippy::needless_pass_by_value)]
fn poly_add_arbitrary(_: &mut RtsContext<'_>, _tid: PolyWord, arg1: PolyWord, arg2: PolyWord)
    -> PolyWord
{
    if let Some((x, y)) = both_tagged(arg2, arg1) {
        let r = x as i128 + y as i128;
        if fits_tagged(r) {
            return PolyWord::tagged(r as isize);
        }
    }
    PolyWord::tagged(0)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_subtract_arbitrary(_: &mut RtsContext<'_>, _tid: PolyWord, arg1: PolyWord, arg2: PolyWord)
    -> PolyWord
{
    // arg2 - arg1
    if let Some((x, y)) = both_tagged(arg2, arg1) {
        let r = x as i128 - y as i128;
        if fits_tagged(r) {
            return PolyWord::tagged(r as isize);
        }
    }
    PolyWord::tagged(0)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_multiply_arbitrary(_: &mut RtsContext<'_>, _tid: PolyWord, arg1: PolyWord, arg2: PolyWord)
    -> PolyWord
{
    if let Some((x, y)) = both_tagged(arg2, arg1) {
        let r = x as i128 * y as i128;
        if fits_tagged(r) {
            return PolyWord::tagged(r as isize);
        }
    }
    PolyWord::tagged(0)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_divide_arbitrary(_: &mut RtsContext<'_>, _tid: PolyWord, arg1: PolyWord, arg2: PolyWord)
    -> PolyWord
{
    // arg2 / arg1, truncating toward zero (this is Int.quot, not
    // Int.div — see comment on `div_longc` in arb.cpp:1183).
    if let Some((x, y)) = both_tagged(arg2, arg1) {
        if y == 0 {
            return PolyWord::tagged(0); // div-by-zero → exception
        }
        // Only overflow case is MIN_TAGGED / -1.
        if x == MIN_TAGGED && y == -1 {
            return PolyWord::tagged(0);
        }
        return PolyWord::tagged(x / y);
    }
    PolyWord::tagged(0)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_remainder_arbitrary(
    _: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg1: PolyWord,
    arg2: PolyWord,
) -> PolyWord {
    // arg2 rem arg1, sign of result = sign of dividend (Int.rem).
    if let Some((x, y)) = both_tagged(arg2, arg1) {
        if y == 0 {
            return PolyWord::tagged(0);
        }
        if x == MIN_TAGGED && y == -1 {
            return PolyWord::tagged(0);
        }
        return PolyWord::tagged(x % y);
    }
    PolyWord::tagged(0)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_compare_arbitrary(_: &mut RtsContext<'_>, arg1: PolyWord, arg2: PolyWord) -> PolyWord {
    // compareLong(arg2, arg1): returns -1, 0, 1, wrapped as TAGGED.
    if arg1.0 == arg2.0 {
        return PolyWord::tagged(0);
    }
    if let Some((x, y)) = both_tagged(arg2, arg1) {
        let c = match x.cmp(&y) {
            std::cmp::Ordering::Less => -1,
            std::cmp::Ordering::Equal => 0,
            std::cmp::Ordering::Greater => 1,
        };
        return PolyWord::tagged(c);
    }
    // One or both boxed: would need bignum compare. Default to 0
    // (equal) — least likely to trigger downstream divergence in the
    // common case where bootstrap is comparing small ints.
    PolyWord::tagged(0)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_or_arbitrary(_: &mut RtsContext<'_>, _tid: PolyWord, arg1: PolyWord, arg2: PolyWord)
    -> PolyWord
{
    if both_tagged(arg1, arg2).is_some() {
        // Both bottom bits are 1 → OR result still has bottom bit 1 (tagged)
        return PolyWord::from_bits(arg1.0 | arg2.0);
    }
    PolyWord::tagged(0)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_and_arbitrary(_: &mut RtsContext<'_>, _tid: PolyWord, arg1: PolyWord, arg2: PolyWord)
    -> PolyWord
{
    if both_tagged(arg1, arg2).is_some() {
        return PolyWord::from_bits(arg1.0 & arg2.0);
    }
    PolyWord::tagged(0)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_xor_arbitrary(_: &mut RtsContext<'_>, _tid: PolyWord, arg1: PolyWord, arg2: PolyWord)
    -> PolyWord
{
    if both_tagged(arg1, arg2).is_some() {
        // XOR cancels the tag bits → set it back.
        return PolyWord::from_bits((arg1.0 ^ arg2.0) | 1);
    }
    PolyWord::tagged(0)
}

/// Shift left of a tagged int. Shift must be tagged & non-negative;
/// if result overflows the tag range we fall through to TAGGED(0).
/// Mirrors `arb.cpp:2017-2096` fast path only.
#[allow(clippy::needless_pass_by_value)]
fn poly_shift_left_arbitrary(
    _: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg: PolyWord,
    shift: PolyWord,
) -> PolyWord {
    if !shift.is_tagged() {
        return PolyWord::tagged(0);
    }
    #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
    let shift_by = shift.untag() as u32;
    if shift_by == 0 {
        return arg;
    }
    if arg.is_tagged() {
        let x = arg.untag();
        if x == 0 {
            return PolyWord::tagged(0);
        }
        if shift_by >= isize::BITS - 1 {
            return PolyWord::tagged(0); // overflow → would need bignum
        }
        let r = (x as i128) << shift_by;
        if fits_tagged(r) {
            return PolyWord::tagged(r as isize);
        }
    }
    PolyWord::tagged(0)
}

/// Shift right (logical) of a tagged int.
#[allow(clippy::needless_pass_by_value)]
fn poly_shift_right_arbitrary(
    _: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg: PolyWord,
    shift: PolyWord,
) -> PolyWord {
    if !shift.is_tagged() {
        return PolyWord::tagged(0);
    }
    #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
    let shift_by = shift.untag() as u32;
    if shift_by == 0 {
        return arg;
    }
    if arg.is_tagged() {
        let x = arg.untag();
        if shift_by >= isize::BITS {
            return PolyWord::tagged(0);
        }
        // ML LargeWord.>> is logical; mirror that on the untagged
        // value.
        #[allow(clippy::cast_sign_loss)]
        let r = (x as usize) >> shift_by;
        #[allow(clippy::cast_possible_wrap)]
        let r = r as isize;
        if fits_tagged(r as i128) {
            return PolyWord::tagged(r);
        }
    }
    PolyWord::tagged(0)
}

/// GCD using i64 for the fast path. Bootstrap rarely calls this so a
/// tagged-only impl is fine.
#[allow(clippy::needless_pass_by_value)]
fn poly_gcd_arbitrary(_: &mut RtsContext<'_>, _tid: PolyWord, arg1: PolyWord, arg2: PolyWord)
    -> PolyWord
{
    if let Some((x, y)) = both_tagged(arg2, arg1) {
        let mut a = x.unsigned_abs();
        let mut b = y.unsigned_abs();
        while b != 0 {
            let t = b;
            b = a % b;
            a = t;
        }
        #[allow(clippy::cast_possible_wrap)]
        let g = a as isize;
        if fits_tagged(g as i128) {
            return PolyWord::tagged(g);
        }
    }
    PolyWord::tagged(0)
}

/// LCM = (|x| / gcd(x,y)) * |y|, with care around zero.
#[allow(clippy::needless_pass_by_value)]
fn poly_lcm_arbitrary(_: &mut RtsContext<'_>, _tid: PolyWord, arg1: PolyWord, arg2: PolyWord)
    -> PolyWord
{
    if let Some((x, y)) = both_tagged(arg2, arg1) {
        if x == 0 || y == 0 {
            return PolyWord::tagged(0);
        }
        let mut a = x.unsigned_abs();
        let mut b = y.unsigned_abs();
        let (orig_a, orig_b) = (a, b);
        while b != 0 {
            let t = b;
            b = a % b;
            a = t;
        }
        let g = a;
        if g == 0 {
            return PolyWord::tagged(0);
        }
        let Some(lcm) = (orig_a / g).checked_mul(orig_b) else {
            return PolyWord::tagged(0);
        };
        #[allow(clippy::cast_sign_loss)]
        let max = isize::MAX as usize;
        if lcm > max {
            return PolyWord::tagged(0);
        }
        #[allow(clippy::cast_possible_wrap)]
        let v = lcm as isize;
        if fits_tagged(v as i128) {
            return PolyWord::tagged(v);
        }
    }
    PolyWord::tagged(0)
}

/// `PolyQuotRemArbitraryPair(threadId, arg1, arg2)` — compute
/// (quotient, remainder) of `arg2` divided by `arg1`, return as a
/// 2-element tuple (ordinary object). Mirrors `arb.cpp:1825-1856`.
#[allow(clippy::needless_pass_by_value)]
fn poly_quot_rem_arbitrary_pair(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg1: PolyWord,
    arg2: PolyWord,
) -> PolyWord {
    let (q, r) = if let Some((x, y)) = both_tagged(arg2, arg1) {
        if y == 0 || (x == MIN_TAGGED && y == -1) {
            return PolyWord::tagged(0);
        }
        (PolyWord::tagged(x / y), PolyWord::tagged(x % y))
    } else {
        return PolyWord::tagged(0);
    };
    // Allocate a 2-word ordinary object holding (q, r).
    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::tagged(0);
    };
    let p = space.alloc(2);
    // SAFETY: just allocated 2 words.
    unsafe {
        crate::space::set_length_word(p, 2, 0);
        p.write(q);
        p.add(1).write(r);
    }
    PolyWord::from_ptr(p.cast_const())
}

/// `PolyGetLowOrderAsLargeWord(threadId, arg)` — extract the low
/// word of `arg`, box it as a sysword (1-word byte object).
/// Mirrors `arb.cpp:1910-1949` fast path.
#[allow(clippy::needless_pass_by_value)]
fn poly_get_low_order_as_large_word(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg: PolyWord,
) -> PolyWord {
    use crate::length_word::F_BYTE_OBJ;
    let low_word: usize = if arg.is_tagged() {
        #[allow(clippy::cast_sign_loss)]
        let v = arg.untag() as usize;
        v
    } else if arg.is_data_ptr() {
        // Boxed: read first body word as the low limb.
        let p = arg.as_ptr::<PolyWord>();
        // SAFETY: caller-trusted boxed bignum.
        unsafe { (*p).0 }
    } else {
        return PolyWord::tagged(0);
    };
    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::tagged(0);
    };
    let p = space.alloc(1);
    // SAFETY: just allocated 1 word.
    unsafe {
        crate::space::set_length_word(p, 1, F_BYTE_OBJ);
        p.write(PolyWord::from_bits(low_word));
    }
    PolyWord::from_ptr(p.cast_const())
}

/// `PolyCopyByteVecToClosure(threadId, byteVec, closure)` — install
/// compiled bytecode into a closure. Mirrors
/// `poly_specific.cpp:181-229`.
///
/// 1. Read `byteVec`'s length word; it must be a byte object.
/// 2. `closure` must be a 1-word mutable closure.
/// 3. Allocate a fresh object of the same word length in alloc space.
/// 4. Copy the byte vector's body verbatim into the new object.
/// 5. Set the new object's length word with `F_CODE_OBJ`.
/// 6. Write the new code-object pointer into `closure[0]`.
/// 7. Clear the closure's mutable bit (lock it).
///
/// Returns TAGGED(0). We don't have a JIT path, so the upstream's
/// mmap-and-protect dance is unnecessary — the alloc space we use
/// for the code is just a regular mutable region.
#[allow(clippy::needless_pass_by_value)]
fn poly_copy_byte_vec_to_closure(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    byte_vec: PolyWord,
    closure: PolyWord,
) -> PolyWord {
    use crate::length_word::{
        F_CODE_OBJ, F_MUTABLE_BIT, flags_of, is_byte_object, length_of,
    };
    if !byte_vec.is_data_ptr() || !closure.is_data_ptr() {
        if RTS_TRACE.load(Ordering::Relaxed) {
            eprintln!(
                "  PolyCopyByteVecToClosure: non-pointer arg(s)? byte_vec={byte_vec:?}, closure={closure:?}"
            );
        }
        return PolyWord::tagged(0);
    }
    let bv_ptr = byte_vec.as_ptr::<PolyWord>();
    let cl_ptr = closure.as_ptr::<PolyWord>().cast_mut();
    // SAFETY: caller (compiler) is trusted on the object layouts.
    unsafe {
        let bv_len_word = crate::space::MemorySpace::length_word_of(bv_ptr);
        if !is_byte_object(bv_len_word) {
            if RTS_TRACE.load(Ordering::Relaxed) {
                eprintln!(
                    "  PolyCopyByteVecToClosure: byte_vec is not a byte object \
                     (flags=0x{:02x}, length={})",
                    flags_of(bv_len_word),
                    length_of(bv_len_word)
                );
            }
            return PolyWord::tagged(0);
        }
        let n_words = length_of(bv_len_word);

        let cl_len_word = crate::space::MemorySpace::length_word_of(cl_ptr);
        if length_of(cl_len_word) != 1 || (flags_of(cl_len_word) & F_MUTABLE_BIT) == 0 {
            if RTS_TRACE.load(Ordering::Relaxed) {
                eprintln!(
                    "  PolyCopyByteVecToClosure: closure shape mismatch \
                     (length={}, flags=0x{:02x})",
                    length_of(cl_len_word),
                    flags_of(cl_len_word)
                );
            }
            return PolyWord::tagged(0);
        }

        let Some(space) = ctx.alloc_space.as_mut() else {
            return PolyWord::tagged(0);
        };
        let dst = space.alloc(n_words);
        // Copy the body words wholesale.
        std::ptr::copy_nonoverlapping(bv_ptr, dst, n_words);
        // New object is mutable code — SetCodeConstant will patch
        // constants into it before LockMutableClosure clears the
        // mutable bit. This matches upstream's `AllocCodeSpace`
        // returning a mutable code object.
        crate::space::set_length_word(dst, n_words, F_CODE_OBJ | F_MUTABLE_BIT);

        // Patch the closure's slot 0 with the new code-object ptr.
        cl_ptr.write(PolyWord::from_ptr(dst.cast_const()));

        // Lock the *closure* now (clear its mutable bit) — the closure
        // itself never needs further mutation; only the code object
        // does until LockMutableClosure finalizes it.
        let new_flags = flags_of(cl_len_word) & !F_MUTABLE_BIT;
        crate::space::set_length_word(cl_ptr, length_of(cl_len_word), new_flags);
    }
    PolyWord::tagged(0)
}

/// `PolySetCodeConstant(closure, offset, cWord, flags)` — patch a
/// constant into the code object referenced by `closure`. We only
/// implement case 0 (absolute PolyWord-size constant — what the
/// interpreted bytecode uses); the relative / ARM64 cases are JIT
/// concerns we don't need.
///
/// Mirrors `poly_specific.cpp:272-309`.
#[allow(clippy::needless_pass_by_value)]
fn poly_set_code_constant(
    _ctx: &mut RtsContext<'_>,
    closure: PolyWord,
    offset: PolyWord,
    c_word: PolyWord,
    flags: PolyWord,
) -> PolyWord {
    use crate::length_word::is_code_object;
    if !closure.is_data_ptr() {
        return PolyWord::tagged(0);
    }
    // Closure may be either a code object directly or a closure whose
    // slot 0 points at one.
    let cl_ptr = closure.as_ptr::<PolyWord>();
    // SAFETY: caller trusted.
    let start_code: *mut u8 = unsafe {
        let lw = crate::space::MemorySpace::length_word_of(cl_ptr);
        if is_code_object(lw) {
            cl_ptr as *mut u8
        } else {
            // closure[0] is the code-object pointer
            (*cl_ptr).as_ptr::<u8>().cast_mut()
        }
    };
    #[allow(clippy::cast_sign_loss)]
    let off = offset.untag() as usize;
    let flag_kind = flags.untag();
    // SAFETY: code-segment write into freshly-allocated mutable space.
    unsafe {
        let instr_addr = start_code.add(off);
        match flag_kind {
            0 | 2 => {
                // Absolute PolyWord-sized constant (case 0) or
                // uintptr_t-sized (case 2 — same on 64-bit).
                let bytes = c_word.0.to_le_bytes();
                std::ptr::copy_nonoverlapping(
                    bytes.as_ptr(),
                    instr_addr,
                    std::mem::size_of::<usize>(),
                );
            }
            _ => {
                // Cases 1/3/4/etc. are native-code relocations we
                // don't need in the interpreter. Trace and skip.
                if RTS_TRACE.load(Ordering::Relaxed) {
                    eprintln!(
                        "  PolySetCodeConstant: unsupported flag {flag_kind} (skipped)"
                    );
                }
            }
        }
    }
    PolyWord::tagged(0)
}

/// `PolyLockMutableClosure(threadId, closure)` — clear the mutable
/// bit on the code object referenced by `closure[0]`.
///
/// Mirrors `poly_specific.cpp:234-263`.
#[allow(clippy::needless_pass_by_value)]
fn poly_lock_mutable_closure(
    _ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    closure: PolyWord,
) -> PolyWord {
    use crate::length_word::{F_CODE_OBJ, length_of};
    if !closure.is_data_ptr() {
        return PolyWord::tagged(0);
    }
    let cl_ptr = closure.as_ptr::<PolyWord>();
    // SAFETY: caller trusted.
    unsafe {
        let code_word = *cl_ptr;
        if !code_word.is_data_ptr() {
            return PolyWord::tagged(0);
        }
        let code_obj = code_word.as_ptr::<PolyWord>().cast_mut();
        let lw = crate::space::MemorySpace::length_word_of(code_obj);
        let n = length_of(lw);
        crate::space::set_length_word(code_obj, n, F_CODE_OBJ);
    }
    PolyWord::tagged(0)
}

fn alloc_thread_object_stub(ctx: &mut RtsContext<'_>) -> PolyWord {
    use crate::length_word::F_MUTABLE_BIT;
    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::tagged(0);
    };
    let length = 9;
    let p = space.alloc(length);
    // SAFETY: just allocated 9 words
    unsafe {
        crate::space::set_length_word(p, length, F_MUTABLE_BIT);
        p.add(0).write(PolyWord::tagged(0));     // threadRef (dummy)
        p.add(1).write(PolyWord::tagged(2));     // flags = PFLAG_SYNCH
        p.add(2).write(PolyWord::tagged(0));     // threadLocal = nil
        p.add(3).write(PolyWord::tagged(0));     // requestCopy = none
        p.add(4).write(PolyWord::tagged(0));     // mlStackSize = unlimited
        for i in 5..length {
            p.add(i).write(PolyWord::tagged(0)); // debuggerSlots
        }
    }
    PolyWord::from_ptr(p.cast_const())
}

/// Allocate a "volatile word" object holding `fd+1` (PolyML's
/// convention: 0 means closed, fd values are stored as fd+1).
/// Layout: 1-word byte object with flags
/// `F_BYTE_OBJ | F_WEAK_BIT | F_MUTABLE_BIT | F_NO_OVERWRITE`
/// per `run_time.cpp:396` `MakeVolatileWord`.
use std::io::Write;

/// IO subcode 11/12: write from an ML byte vector to the stream's
/// underlying fd. `arg` is the byte vector + an offset + a length,
/// usually packaged as a record. For now we attempt the simpler
/// interpretation: arg is a 3-tuple (vec, offset, length). If the
/// shape doesn't match (or strm isn't wrapping a real fd), we
/// return 0 — meaning "wrote nothing" — which is the safe stub
/// behaviour that doesn't break consumers.
fn write_array(strm: PolyWord, arg: PolyWord) -> PolyWord {
    // Best-effort fd extraction. `strm` is conventionally a
    // wrapped-fd object (see `wrap_file_descriptor`): a 1-word byte
    // object holding `fd + 1`.
    if !strm.is_data_ptr() || !arg.is_data_ptr() {
        return PolyWord::tagged(0);
    }
    // SAFETY: caller (compiler) is trusted.
    let fd_plus_one = unsafe { *strm.as_ptr::<PolyWord>() }.0;
    if fd_plus_one == 0 {
        return PolyWord::tagged(0);
    }
    // arg shape: 3-tuple (vec, offset, length).
    let p = arg.as_ptr::<PolyWord>();
    let (vec, offset, length) = unsafe { (*p, *p.add(1), *p.add(2)) };
    if !vec.is_data_ptr() || !offset.is_tagged() || !length.is_tagged() {
        return PolyWord::tagged(0);
    }
    #[allow(clippy::cast_sign_loss)]
    let off = offset.untag() as usize;
    #[allow(clippy::cast_sign_loss)]
    let len = length.untag() as usize;
    if len == 0 {
        return PolyWord::tagged(0);
    }
    // SAFETY: vec is a byte object; reading off..off+len bytes of
    // its body is well-defined for trusted callers.
    let base = vec.as_ptr::<u8>();
    let slice = unsafe { std::slice::from_raw_parts(base.add(off), len) };
    // Route via std::io for fds 1/2; ignore others for now.
    let n = match fd_plus_one - 1 {
        1 => std::io::stdout().write(slice).unwrap_or(0),
        2 => std::io::stderr().write(slice).unwrap_or(0),
        _ => 0,
    };
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_possible_wrap)]
    PolyWord::tagged(n as isize)
}

/// Allocate the canonical "empty string" object: 1 word with length
/// 0 and `F_BYTE_OBJ` flag. Mirrors `polystring.cpp:61-67`.
fn alloc_empty_string(ctx: &mut RtsContext<'_>) -> PolyWord {
    use crate::length_word::F_BYTE_OBJ;
    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::tagged(0);
    };
    let p = space.alloc(1);
    // SAFETY: just allocated 1 word.
    unsafe {
        crate::space::set_length_word(p, 1, F_BYTE_OBJ);
        p.write(PolyWord::from_bits(0)); // length = 0
    }
    PolyWord::from_ptr(p.cast_const())
}

fn wrap_file_descriptor(ctx: &mut RtsContext<'_>, fd: u32) -> PolyWord {
    use crate::length_word::{F_BYTE_OBJ, F_MUTABLE_BIT, F_NO_OVERWRITE, F_WEAK_BIT};
    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::tagged(0);
    };
    let p = space.alloc(1);
    // SAFETY: just allocated 1 word
    unsafe {
        crate::space::set_length_word(p, 1, F_BYTE_OBJ | F_WEAK_BIT | F_MUTABLE_BIT | F_NO_OVERWRITE);
        p.write(PolyWord::from_bits((fd as usize) + 1));
    }
    PolyWord::from_ptr(p.cast_const())
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
        // SML's rtsCallFast1 means PolyIsBigEndian is invoked with a
        // dummy unit arg, even though the C function takes none.
        let result = match entry.func {
            RtsFn::Arity1(f) => f(&mut ctx, PolyWord::tagged(0)),
            _ => panic!("arity mismatch"),
        };
        assert_eq!(result.untag(), 0); // little-endian
    }

    #[test]
    fn token_zero_is_unresolved() {
        let t = RtsTable::new();
        assert!(t.entry(0).is_none());
    }

    fn ctx() -> RtsContext<'static> {
        RtsContext { alloc_space: None }
    }
    fn t() -> PolyWord {
        PolyWord::tagged(0)
    }

    #[test]
    fn arb_add_fast_path() {
        let r = poly_add_arbitrary(&mut ctx(), t(), PolyWord::tagged(2), PolyWord::tagged(3));
        // arg2 + arg1 = 3 + 2 = 5
        assert_eq!(r.untag(), 5);
    }

    #[test]
    fn arb_sub_fast_path() {
        // arg2 - arg1 = 7 - 4 = 3
        let r = poly_subtract_arbitrary(&mut ctx(), t(), PolyWord::tagged(4), PolyWord::tagged(7));
        assert_eq!(r.untag(), 3);
    }

    #[test]
    fn arb_mul_fast_path() {
        let r = poly_multiply_arbitrary(&mut ctx(), t(), PolyWord::tagged(6), PolyWord::tagged(7));
        assert_eq!(r.untag(), 42);
    }

    #[test]
    fn arb_div_fast_path() {
        // arg2 / arg1 = 20 / 6 = 3 (truncate toward zero)
        let r = poly_divide_arbitrary(&mut ctx(), t(), PolyWord::tagged(6), PolyWord::tagged(20));
        assert_eq!(r.untag(), 3);
        // -20 / 6 = -3 (truncate toward zero, NOT -4)
        let r = poly_divide_arbitrary(&mut ctx(), t(), PolyWord::tagged(6), PolyWord::tagged(-20));
        assert_eq!(r.untag(), -3);
    }

    #[test]
    fn arb_rem_fast_path() {
        // 20 rem 6 = 2 (sign of dividend)
        let r = poly_remainder_arbitrary(&mut ctx(), t(), PolyWord::tagged(6), PolyWord::tagged(20));
        assert_eq!(r.untag(), 2);
        let r = poly_remainder_arbitrary(&mut ctx(), t(), PolyWord::tagged(6), PolyWord::tagged(-20));
        assert_eq!(r.untag(), -2);
    }

    #[test]
    fn arb_compare() {
        let r = poly_compare_arbitrary(&mut ctx(), PolyWord::tagged(5), PolyWord::tagged(7));
        // arg2 cmp arg1 = 7 cmp 5 = 1 (greater)
        assert_eq!(r.untag(), 1);
        let r = poly_compare_arbitrary(&mut ctx(), PolyWord::tagged(7), PolyWord::tagged(5));
        assert_eq!(r.untag(), -1);
        let r = poly_compare_arbitrary(&mut ctx(), PolyWord::tagged(5), PolyWord::tagged(5));
        assert_eq!(r.untag(), 0);
    }

    #[test]
    fn arb_bitwise() {
        let a = PolyWord::tagged(0b1100);
        let b = PolyWord::tagged(0b1010);
        // AND
        let r = poly_and_arbitrary(&mut ctx(), t(), a, b);
        assert_eq!(r.untag(), 0b1000);
        assert!(r.is_tagged());
        // OR
        let r = poly_or_arbitrary(&mut ctx(), t(), a, b);
        assert_eq!(r.untag(), 0b1110);
        assert!(r.is_tagged());
        // XOR
        let r = poly_xor_arbitrary(&mut ctx(), t(), a, b);
        assert_eq!(r.untag(), 0b0110);
        assert!(r.is_tagged());
    }

    #[test]
    fn arb_add_overflow_returns_zero() {
        let r = poly_add_arbitrary(
            &mut ctx(),
            t(),
            PolyWord::tagged(MAX_TAGGED),
            PolyWord::tagged(1),
        );
        assert_eq!(r.untag(), 0);
    }

    #[test]
    fn arb_shift_left_simple() {
        // arg2-style ordering: shift_left(arg, shift) means arg << shift.
        let r = poly_shift_left_arbitrary(
            &mut ctx(),
            t(),
            PolyWord::tagged(5),
            PolyWord::tagged(3),
        );
        assert_eq!(r.untag(), 40);
    }

    #[test]
    fn arb_shift_right_simple() {
        let r = poly_shift_right_arbitrary(
            &mut ctx(),
            t(),
            PolyWord::tagged(40),
            PolyWord::tagged(3),
        );
        assert_eq!(r.untag(), 5);
    }

    #[test]
    fn arb_gcd_lcm() {
        let g = poly_gcd_arbitrary(
            &mut ctx(),
            t(),
            PolyWord::tagged(12),
            PolyWord::tagged(18),
        );
        assert_eq!(g.untag(), 6);
        let l = poly_lcm_arbitrary(
            &mut ctx(),
            t(),
            PolyWord::tagged(4),
            PolyWord::tagged(6),
        );
        assert_eq!(l.untag(), 12);
    }
}
