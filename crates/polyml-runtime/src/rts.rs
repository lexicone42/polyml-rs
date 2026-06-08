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
use std::sync::Mutex;

use crate::poly_word::PolyWord;

/// When true, every RTS stub call logs to stderr. Used for debugging
/// which RTS functions are on the critical path before they're really
/// implemented.
static RTS_TRACE: AtomicBool = AtomicBool::new(false);

/// Command-line arguments visible to SML via `CommandLine.arguments()`.
/// The CLI's `poly run` populates this before starting the interpreter;
/// SML's `CommandLine.arguments` reaches us via
/// `poly_get_commandline_arguments`. Defaults to empty if never set.
static COMMAND_ARGS: Mutex<Vec<String>> = Mutex::new(Vec::new());

/// Replace the command-line argument list seen by SML's
/// `CommandLine.arguments`. Pass the args you want the SML program to
/// receive — typically the image path and anything after it
/// (e.g. `-I /some/path`).
pub fn set_command_args(args: Vec<String>) {
    let mut g = COMMAND_ARGS.lock().expect("COMMAND_ARGS poisoned");
    *g = args;
}

/// Read the current command-line args. Returns a clone so callers don't
/// have to keep the mutex held while building SML-shaped values.
pub fn get_command_args() -> Vec<String> {
    COMMAND_ARGS.lock().expect("COMMAND_ARGS poisoned").clone()
}

/// Bytes that synthetic stdin reads should consume before falling
/// through to the real `std::io::stdin`. Populated by the CLI's
/// `--use FILE` option so the SML side sees the
/// `val () = Bootstrap.use "..."` line as its first input.
static SYNTHETIC_STDIN: Mutex<Vec<u8>> = Mutex::new(Vec::new());

/// Append bytes to the synthetic-stdin queue. They will be read
/// before any bytes from the real stdin.
pub fn push_synthetic_stdin(text: String) {
    let mut g = SYNTHETIC_STDIN.lock().expect("SYNTHETIC_STDIN poisoned");
    g.extend_from_slice(text.as_bytes());
}

/// Read up to `dst.len()` bytes from the synthetic-stdin queue.
/// Returns the number of bytes copied. If the queue is empty, returns
/// 0 so the caller can fall through to the real stdin.
fn read_synthetic_stdin(dst: &mut [u8]) -> usize {
    let mut g = SYNTHETIC_STDIN.lock().expect("SYNTHETIC_STDIN poisoned");
    let n = g.len().min(dst.len());
    if n == 0 {
        return 0;
    }
    dst[..n].copy_from_slice(&g[..n]);
    g.drain(..n);
    n
}

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
    /// Set by RTS functions that want to raise an SML exception
    /// instead of returning normally. Read by the dispatch site
    /// (`Interpreter::rts_call`) which routes to RAISE_EXCEPTION.
    pub raised_exception: Option<PolyWord>,
    /// Borrowed reference to the RTS table itself, so an RTS
    /// function like `PolyCreateEntryPointObject` can look up
    /// other RTS names to build runtime entry-point objects.
    pub rts: Option<&'a RtsTable>,
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

#[allow(clippy::too_many_lines)]
fn register_builtins(t: &mut RtsTable) {
    // These take a unit arg in SML (rtsCallFast1) even though the
    // C signature is `()`. PolyML's C side gets away with it because
    // x86-64 passes the unused arg in rdi/rsi which the C body
    // ignores; we have to be explicit and register as Arity1.
    t.register("PolyIsBigEndian", RtsFn::Arity1(|_, _| poly_is_big_endian_inner()));
    // These are called as `rtsCallFast0` from LibrarySupport.sml.
    // All return reasonable defaults for our environment.
    t.register("PolyGetMaxAllocationSize", RtsFn::Arity0(|_| {
        // Max object length: 1 << 24 words = plenty for any sensible alloc.
        PolyWord::tagged(1 << 24)
    }));
    t.register("PolyGetMaxStringSize", RtsFn::Arity0(|_| {
        // Same upper bound, in bytes.
        PolyWord::tagged((1isize << 24) * 8)
    }));
    t.register("PolyGetOSType", RtsFn::Arity0(|_| PolyWord::tagged(0))); // 0 = Unix
    t.register("PolyGetPolyVersionNumber", RtsFn::Arity0(|_| PolyWord::tagged(592)));
    // Compact 32-in-64 mode unit size; returns 0 in native 64-bit mode.
    t.register("PolyGetC32UnitSize", RtsFn::Arity0(|_| PolyWord::tagged(0)));
    // Stubs for PolyML.make compiling CodeArray.ML — these mutate code
    // objects in the runtime's code area. Returns unit / tagged 0.
    t.register("PolySetCodeByte", RtsFn::Arity3(poly_set_code_byte));
    t.register("PolyGetCodeConstant", RtsFn::Arity3(poly_get_code_constant));
    t.register("PolyChunkSizeArbitrary", RtsFn::Arity0(|_| PolyWord::tagged(64)));
    t.register("PolyGetUserStatsCount", RtsFn::Arity0(|_| PolyWord::tagged(0)));
    t.register("PolyThreadNumPhysicalProcessors", RtsFn::Arity0(|_| PolyWord::tagged(1)));
    t.register("PolyThreadNumProcessors", RtsFn::Arity0(|_| PolyWord::tagged(1)));
    // Real / float RTS stubs (basis layer uses these).
    t.register("PolyGetRoundingMode", RtsFn::Arity1(|_, _| PolyWord::tagged(0))); // TO_NEAREST
    t.register("PolySetRoundingMode", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyRealFrexp", RtsFn::Arity2(poly_real_frexp));
    t.register(
        "PolyRealDoubleToString",
        RtsFn::Arity4(poly_real_double_to_string),
    );
    // Real math RTS: registered as stubs so PolyCreateEntryPointObject
    // can resolve them at basis-compile time. The actual math doesn't
    // need to work at compile time — only the entry-point object's
    // shape matters. Implementations can be filled in later.
    //
    // All of these are `rtsCallFast{F_F|FF_F|RR_R|...}` style:
    // - F_F : double -> double (Arity1 — no threadId for Fast variants)
    // - FF_F: double*double -> double (Arity2)
    // DOUBLE unary math (rtsCallFastR_R: real -> real, no threadId). Previously
    // stubbed to tagged(0) — which made Real.sqrt/sin/floor/round/... silently
    // return 0 AND, crucially, made `toArbitrary o realFloor` (Real.toLargeInt,
    // and the default Real.floor under arbitrary-precision int) read the bytes of
    // a tagged int as a boxed double → wrong value / SEGV. Implement them for real.
    t.register("PolyRealSqrt", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).sqrt())));
    t.register("PolyRealSin", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).sin())));
    t.register("PolyRealCos", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).cos())));
    t.register("PolyRealTan", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).tan())));
    t.register("PolyRealArcSin", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).asin())));
    t.register("PolyRealArcCos", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).acos())));
    t.register("PolyRealArctan", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).atan())));
    t.register("PolyRealSinh", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).sinh())));
    t.register("PolyRealCosh", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).cosh())));
    t.register("PolyRealTanh", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).tanh())));
    t.register("PolyRealExp", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).exp())));
    t.register("PolyRealLog", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).ln())));
    t.register("PolyRealLog10", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).log10())));
    // floor/ceil/trunc obvious; round = round-half-to-even (matches upstream
    // PolyRealRound, reals.cpp:350-359).
    t.register("PolyRealFloor", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).floor())));
    t.register("PolyRealCeil", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).ceil())));
    t.register("PolyRealRound", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).round_ties_even())));
    t.register("PolyRealTrunc", RtsFn::Arity1(|c, x| box_real(c, read_real_word(x).trunc())));
    // FLOAT (Real32) variants still stubbed — Real32 boxing differs; not on the
    // Isabelle/HOL4 double path.
    let real_unary_stubs = [
        "PolyRealFSqrt", "PolyRealFSin", "PolyRealFCos", "PolyRealFTan",
        "PolyRealFArcSin", "PolyRealFArcCos", "PolyRealFArctan",
        "PolyRealFSinh", "PolyRealFCosh", "PolyRealFTanh",
        "PolyRealFExp", "PolyRealFLog", "PolyRealFLog10",
        "PolyRealFFloor", "PolyRealFCeil", "PolyRealFRound", "PolyRealFTrunc",
    ];
    for name in real_unary_stubs {
        t.register(name, RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    }
    // DOUBLE binary math (rtsCallFastRR_R: real*real -> real, no threadId).
    t.register("PolyRealAtan2", RtsFn::Arity2(|c, y, x| box_real(c, read_real_word(y).atan2(read_real_word(x)))));
    t.register("PolyRealPow", RtsFn::Arity2(|c, b, e| box_real(c, read_real_word(b).powf(read_real_word(e)))));
    t.register("PolyRealCopySign", RtsFn::Arity2(|c, a, b| box_real(c, read_real_word(a).copysign(read_real_word(b)))));
    t.register("PolyRealRem", RtsFn::Arity2(|c, a, b| box_real(c, read_real_word(a) % read_real_word(b))));
    // Real.nextAfter (Real.sml:480). Registered FIRST here to preserve the
    // dispatch-token ordinal it had as the head of the old stub array.
    t.register("PolyRealNextAfter", RtsFn::Arity2(|c, a, b| box_real(c, next_after(read_real_word(a), read_real_word(b)))));
    let real_binary_stubs = [
        "PolyRealFAtan2", "PolyRealFCopySign", "PolyRealFNextAfter",
        "PolyRealFPow", "PolyRealFRem",
    ];
    for name in real_binary_stubs {
        t.register(name, RtsFn::Arity2(zero2));
    }
    // Real.fromManAndExp = ldexp(man, exp) = man * 2^exp (Real.sml:265,
    // rtsCallFastRI_R: real * int -> real). exp clamped to a range beyond which
    // the result is already inf/0 in f64.
    t.register("PolyRealLdexp", RtsFn::Arity2(|c, m, e| {
        #[allow(clippy::cast_possible_truncation)]
        let exp = e.untag().clamp(-2000, 2000) as i32;
        box_real(c, read_real_word(m) * 2f64.powi(exp))
    }));
    // Real.fromLargeInt (and, under arbitrary-precision int, Real.fromInt): convert
    // an arbitrary-precision int (tagged or boxed bignum) to a boxed double.
    // reals.cpp:240 PolyFloatArbitraryPrecision(arg) -> double. Fast call, ONE arg
    // (the old Arity2 stub was both wrong-arity and returned tagged(0), which made
    // `val zero/one/four = fromInt …` in basis/Real.sml produce fake reals and SEGV
    // the load under arbitrary int).
    t.register("PolyFloatArbitraryPrecision", RtsFn::Arity1(|c, x| {
        use num_traits::ToPrimitive;
        box_real(c, poly_word_to_bigint(x).and_then(|n| n.to_f64()).unwrap_or(0.0))
    }));
    // Timing / system stubs.
    t.register("PolyTimingTicksPerMicroSec", RtsFn::Arity1(|_, _| PolyWord::tagged(1)));
    t.register("PolyTimingGetNow", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyTimingBaseYear", RtsFn::Arity1(|_, _| PolyWord::tagged(1970)));
    t.register("PolyTimingConvertDateStuct", RtsFn::Arity2(zero2));
    t.register("PolyTimingLocalOffset", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyTimingSummerApplies", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyTimingYearOffset", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyTimingGetUser", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyTimingGetSystem", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyTimingGetReal", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyTimingGetGCUser", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyTimingGetGCSystem", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyTimingGetChildUser", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyTimingGetChildSystem", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    // Process / OS / Foreign stubs.
    t.register("PolyGetProcessName", RtsFn::Arity1(|ctx, _| alloc_empty_string(ctx)));
    t.register("PolyGetEnv", RtsFn::Arity2(poly_get_env));
    t.register("PolyGetEnvironment", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyFullGC", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyGetLocalStats", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyShowHierarchy", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyShowLoadedModules", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyExport", RtsFn::Arity3(poly_export));
    // Portable variant uses the same pexport text format as our regular
    // export — both go through the same snapshot path.
    t.register("PolyExportPortable", RtsFn::Arity3(poly_export));
    t.register("PolyChDir", RtsFn::Arity2(zero2));
    t.register("PolyGetModuleDirectory", RtsFn::Arity1(|ctx, _| alloc_empty_string(ctx)));
    // FFI library loading stubs.
    t.register("PolyFFILoadExecutable", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyFFILoadLibrary", RtsFn::Arity2(zero2));
    t.register("PolyFFIUnloadLibrary", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyFFIGetSymbolAddress", RtsFn::Arity2(zero2));
    t.register("PolyFFIMalloc", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyFFICreateExtData", RtsFn::Arity2(zero2));
    t.register("PolyFFICreateExtFn", RtsFn::Arity2(zero2));
    // Network stubs (we don't support sockets).
    t.register("PolyNetworkGetFamilyFromAddress", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyNetworkGetAddrList", RtsFn::Arity1(|_, _| poly_network_get_addr_list_inner()));
    t.register("PolyNetworkGetHostName", RtsFn::Arity1(|ctx, _| alloc_empty_string(ctx)));
    t.register("PolyNetworkGetSockTypeList", RtsFn::Arity1(|_, _| poly_network_get_sock_type_list_inner()));
    t.register("PolyNetworkReturnIP4AddressAny", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyNetworkReturnIP6AddressAny", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    // Many more network stubs — all unimplemented; Socket.sml will
    // fail at runtime if you try to use them, but registration is
    // enough for compile-time.
    let net_stubs_arity1: &[&str] = &[
        "PolyNetworkBytesAvailable", "PolyNetworkCloseSocket",
        "PolyNetworkGetAtMark", "PolyNetworkGetSocketError",
        "PolyNetworkGetPeerName", "PolyNetworkGetSockName",
        "PolyNetworkGetLinger",
    ];
    for n in net_stubs_arity1 {
        t.register(n, RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    }
    let net_stubs_arity2: &[&str] = &[
        "PolyNetworkAccept", "PolyNetworkBind", "PolyNetworkConnect",
        "PolyNetworkGetProtByName", "PolyNetworkGetProtByNo",
        "PolyNetworkListen", "PolyNetworkSetLinger", "PolyNetworkShutdown",
        "PolyNetworkGetServByName", "PolyNetworkGetServByPort",
        "PolyNetworkCreateIP4Address", "PolyNetworkCreateIP6Address",
        "PolyNetworkGetAddressAndPortFromIP4",
        "PolyNetworkGetAddressAndPortFromIP6",
        "PolyNetworkGetAddrInfo", "PolyNetworkGetNameInfo",
        "PolyNetworkCreateSocket",
        "PolyNetworkStringToIP6Address", "PolyNetworkIP6AddressToString",
    ];
    for n in net_stubs_arity2 {
        t.register(n, RtsFn::Arity2(zero2));
    }
    let net_stubs_arity3: &[&str] = &[
        "PolyNetworkGetOption", "PolyNetworkSetOption",
        "PolyNetworkReceive", "PolyNetworkSend",
        "PolyNetworkGetServByNameAndProtocol",
        "PolyNetworkGetServByPortAndProtocol",
        "PolyNetworkCreateSocketPair",
    ];
    for n in net_stubs_arity3 {
        t.register(n, RtsFn::Arity3(zero3));
    }
    let net_stubs_arity4: &[&str] = &[
        "PolyNetworkReceiveFrom", "PolyNetworkSendTo",
        "PolyNetworkSelect",
    ];
    for n in net_stubs_arity4 {
        t.register(n, RtsFn::Arity4(zero4));
    }
    // process_env return values.
    t.register("PolyProcessEnvFailureValue", RtsFn::Arity1(|_, _| PolyWord::tagged(1)));
    t.register("PolyProcessEnvSuccessValue", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyProcessEnvErrorMessage", RtsFn::Arity2(|ctx, _, _| alloc_empty_string(ctx)));
    t.register("PolyProcessEnvErrorFromString", RtsFn::Arity2(|_, _, _| PolyWord::tagged(0)));
    t.register("PolyProcessEnvSystem", RtsFn::Arity2(|_, _, _| PolyWord::tagged(0)));
    t.register("PolyTerminate", RtsFn::Arity2(|_, _, _| PolyWord::tagged(0)));
    t.register("PolyPollIODescriptors", RtsFn::Arity4(zero4));
    // rtsCallFull2 → threadId + 2 args → CALL_FAST_RTS3.
    t.register("PolySetSignalHandler", RtsFn::Arity3(zero3));
    t.register("PolyOSSpecificGeneral", RtsFn::Arity3(zero3));
    t.register("PolyPosixCreatePersistentFD", RtsFn::Arity2(zero2));
    t.register("PolyPosixSleep", RtsFn::Arity3(zero3));
    t.register("PolyUnixExecute", RtsFn::Arity4(zero4));
    t.register("PolyNetworkUnixPathToSockAddr", RtsFn::Arity2(zero2));
    t.register("PolyNetworkUnixSockAddrToPath", RtsFn::Arity2(|ctx, _, _| alloc_empty_string(ctx)));
    t.register("PolyGetRemoteStats", RtsFn::Arity2(zero2));
    t.register("PolySetUserStat", RtsFn::Arity3(zero3));
    t.register("PolyObjProfile", RtsFn::Arity2(zero2));
    t.register("PolyObjSize", RtsFn::Arity2(zero2));
    t.register("PolyShowSize", RtsFn::Arity2(zero2));
    t.register("PolyShareCommonData", RtsFn::Arity2(zero2));
    t.register("PolySpecificGeneral", RtsFn::Arity3(poly_specific_general));
    t.register("PolyProfiling", RtsFn::Arity2(zero2));
    t.register("PolyLoadHierarchy", RtsFn::Arity2(zero2));
    t.register("PolyLoadModule", RtsFn::Arity2(zero2));
    t.register("PolyLoadState", RtsFn::Arity2(zero2));
    t.register("PolyReleaseModule", RtsFn::Arity2(zero2));
    t.register("PolyRenameParent", RtsFn::Arity3(zero3));
    t.register("PolySaveState", RtsFn::Arity3(zero3));
    t.register("PolyShowParent", RtsFn::Arity2(|ctx, _, _| alloc_empty_string(ctx)));
    t.register("PolyStoreModule", RtsFn::Arity3(zero3));
    t.register("PolyGetModuleInfo", RtsFn::Arity2(zero2));
    // Thread cond var stubs (no-ops in single-threaded mode).
    t.register("PolyThreadCondVarWait", RtsFn::Arity2(noop2));
    t.register("PolyThreadCondVarWaitUntil", RtsFn::Arity3(zero3));
    // FFI stubs (we don't support real FFI yet).
    t.register("PolyFFIGetError", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyFFISetError", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyFFIFree", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyFFICallbackException", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    // Threading stubs.
    t.register("PolyThreadIsActive", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyThreadKillThread", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    // Size queries (FFI). Use sizeof(T) values from the host.
    t.register("PolySizeInt", RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<i32>())));
    t.register("PolySizeShort", RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<i16>())));
    t.register("PolySizeLong", RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<isize>())));
    t.register("PolySizeLonglong", RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<i64>())));
    t.register("PolySizeIntptr", RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<isize>())));
    t.register("PolySizeUintptr", RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<usize>())));
    t.register("PolySizePtrdiff", RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<isize>())));
    t.register("PolySizeSize", RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<usize>())));
    t.register("PolySizeSsize", RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<isize>())));
    // IntInf.log2 long path (IntInf.sml:55): floor(log2(|x|)) = highest set bit
    // index = bits()-1. Was a hard stub returning 0 (silent wrong answer for any
    // value >= 2^62). The SML wrapper only calls this for boxed (large) values.
    t.register("PolyLog2Arbitrary", RtsFn::Arity1(|_, x| {
        match poly_word_to_bigint(x) {
            Some(n) if n.bits() > 0 => {
                #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
                PolyWord::tagged((n.bits() - 1) as isize)
            }
            _ => PolyWord::tagged(0),
        }
    }));
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
    // `PolyEndBootstrapMode(threadId, function)` — upstream calls
    // `function ()` and never returns. For our single-threaded run
    // the SML caller is `RunCall.rtsCallFull1 ... thirdStage`. If
    // this RTS function returned plainly, the caller's `val ()` bind
    // succeeds and Stage2.sml's local block ends — which would skip
    // Stage 3 entirely. So we record the function in a thread-local
    // slot; the interpreter checks it on RTS return and tail-calls it.
    t.register(
        "PolyEndBootstrapMode",
        RtsFn::Arity2(poly_end_bootstrap_mode),
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
    // rtsCallFull1 → CALL_FAST_RTS2 (threadId + 1 SML arg).
    t.register("PolyGetFunctionName", RtsFn::Arity2(poly_get_function_name));

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
    // Fast-path: if both args are tagged and the result fits in a tag,
    // return TAGGED(result). Otherwise fall through to a real boxed-bignum
    // path (num_bigint::BigInt; see poly_word_to_bigint / bigint_to_poly_word
    // ~line 1292) and allocate a boxed result — so e.g. IntInf.pow(2,100)
    // computes correctly, not just tagged-range arithmetic.
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
    // PolyCreateEntryPointObject(threadId, name) → 2 (rtsCallFull1)
    // PolyCreateEntryPointObject(threadId, name) → 2 (rtsCallFull1).
    // Constructs an entry-point object at runtime — same shape as
    // the ones the loader patches, but built from a name we resolve
    // against the RTS table.
    t.register(
        "PolyCreateEntryPointObject",
        RtsFn::Arity2(poly_create_entry_point_object),
    );
}

// Helper for returning a small unsigned size as a tagged int.
fn size_word(n: usize) -> PolyWord {
    #[allow(clippy::cast_possible_wrap)]
    PolyWord::tagged(n as isize)
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

/// `PolyExport(threadId, filename, root_function)` — snapshot the live
/// heap reachable from `root_function` and write a pexport text file
/// to `filename`. Mirrors `vendor/polyml/libpolyml/pexport.cpp` for the
/// interpreted-mode case.
///
/// On any I/O error or unreachable-root, sets the SML exception and
/// returns TAGGED(0). Otherwise returns TAGGED(0) (unit) successfully.
#[allow(clippy::needless_pass_by_value)]
fn poly_export(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    filename: PolyWord,
    root: PolyWord,
) -> PolyWord {
    use std::io::BufWriter;
    let Some(name) = poly_string_to_rust(filename) else {
        ctx.raised_exception = Some(make_simple_exception(
            ctx,
            "PolyExport: filename is not a string",
        ));
        return PolyWord::tagged(0);
    };
    if !root.is_data_ptr() {
        ctx.raised_exception = Some(make_simple_exception(
            ctx,
            "PolyExport: root must be a heap object (got tagged value)",
        ));
        return PolyWord::tagged(0);
    }
    let image = unsafe { crate::export::snapshot(root) };
    let file = match std::fs::File::create(&name) {
        Ok(f) => f,
        Err(e) => {
            ctx.raised_exception = Some(make_simple_exception(
                ctx,
                &format!("PolyExport: open {name:?} failed: {e}"),
            ));
            return PolyWord::tagged(0);
        }
    };
    let mut w = BufWriter::new(file);
    if let Err(e) = image.write(&mut w) {
        ctx.raised_exception = Some(make_simple_exception(
            ctx,
            &format!("PolyExport: write {name:?} failed: {e}"),
        ));
        return PolyWord::tagged(0);
    }
    if RTS_TRACE.load(Ordering::Relaxed) {
        eprintln!(
            "  PolyExport: wrote {} objects, root id 0, to {:?}",
            image.objects.len(),
            name,
        );
    }
    PolyWord::tagged(0)
}

/// Slot read by the interpreter after every RTS return. When this
/// holds a non-`ZERO` PolyWord, the interpreter treats the value as
/// a `unit -> 'a` closure to tail-call (taking the place of whatever
/// the RTS would have returned to).
static BOOTSTRAP_TAIL_CALL: AtomicUsize = AtomicUsize::new(0);

/// Used by [`crate::interpreter::Interpreter::take_tail_call`] to
/// observe and clear the slot.
#[must_use]
pub fn take_bootstrap_tail_call() -> Option<PolyWord> {
    let raw = BOOTSTRAP_TAIL_CALL.swap(0, Ordering::Relaxed);
    if raw == 0 {
        None
    } else {
        Some(PolyWord::from_bits(raw))
    }
}

/// Read the bootstrap tail-call slot without clearing it. Used by
/// the GC to forward the held PolyWord without consuming it.
#[must_use]
pub fn peek_bootstrap_tail_call() -> PolyWord {
    PolyWord::from_bits(BOOTSTRAP_TAIL_CALL.load(Ordering::Relaxed))
}

/// Read `POLYML_GC_THRESHOLD` env var as a 1-99 percentage; returns
/// `None` if unset / invalid. The interpreter's step loop triggers
/// GC when alloc-space fullness >= this percentage.
///
/// The env-var lookup is cached because this is called on every
/// bytecode step (~14M calls/sec); a fresh `std::env::var` lookup
/// per call goes through the libc env mutex and dominates the
/// dispatch loop. We read the env once on first call, store the
/// parsed value (or sentinel 0 = unset), and return from the cache
/// on subsequent calls.
///
/// Sentinel values in `GC_THRESHOLD_CACHE`:
///   0   = not yet initialised
///   1   = env unset or invalid (caller falls back to default 80%)
///   2-100 = parsed value `+ 1` (so 80% is stored as 81)
static GC_THRESHOLD_CACHE: AtomicUsize = AtomicUsize::new(0);

#[must_use]
pub fn gc_threshold_percent() -> Option<u8> {
    let cached = GC_THRESHOLD_CACHE.load(Ordering::Relaxed);
    if cached == 0 {
        let parsed = std::env::var("POLYML_GC_THRESHOLD")
            .ok()
            .and_then(|s| s.parse::<u8>().ok())
            .filter(|p| (1..=99).contains(p));
        let to_store = parsed.map_or(1, |p| usize::from(p) + 1);
        GC_THRESHOLD_CACHE.store(to_store, Ordering::Relaxed);
        return parsed;
    }
    if cached == 1 {
        None
    } else {
        #[allow(clippy::cast_possible_truncation)]
        Some((cached - 1) as u8)
    }
}

/// Overwrite the bootstrap tail-call slot. Used by the GC to write
/// back the forwarded address after copying.
pub fn set_bootstrap_tail_call(w: PolyWord) {
    BOOTSTRAP_TAIL_CALL.store(w.0, Ordering::Relaxed);
}

/// `PolyEndBootstrapMode(threadId, function)` — record `function`
/// to be invoked (with unit arg) as soon as we return from this RTS
/// call. The SML caller passes `thirdStage : unit -> unit` and
/// expects it to never return.
#[allow(clippy::needless_pass_by_value)]
fn poly_end_bootstrap_mode(
    _ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    function: PolyWord,
) -> PolyWord {
    BOOTSTRAP_TAIL_CALL.store(function.0, Ordering::Relaxed);
    PolyWord::tagged(0)
}

/// Build a static SML list `[(name, tagged_int)]` from a slice of
/// (name, int) pairs. Each call uses a fresh static cell — the
/// data is leaked but the call site usually caches the result.
fn static_string_int_list(items: &'static [(&'static str, isize)]) -> usize {
    use crate::length_word::{F_BYTE_OBJ, make_length_word};
    // For each pair: PolyString (length_word + length + chars padded)
    //               + 2-word ordinary tuple
    // For the list:  cons cells (2-word ordinary) chaining toward nil.
    //
    // Pre-compute sizes per pair: 1 (str header) + 1 (str len) +
    // ceil(name.len()/8) (chars) + 1 (tuple header) + 2 (tuple body)
    //
    // Total per cons: above + 1 (cons header) + 2 (cons body)
    //
    // Simpler: just allocate ALL words in one big Box, walking
    // sequentially.
    use std::cell::OnceCell;
    let mut words: Vec<usize> = Vec::new();
    let mut tuple_ptrs: Vec<usize> = Vec::new();
    for (name, _) in items {
        let chars_words = (name.len() + 1).div_ceil(std::mem::size_of::<usize>());
        let str_size = 1 + chars_words; // length + chars
        words.push(make_length_word(str_size, F_BYTE_OBJ).0);
        let str_ptr_idx = words.len(); // word index of length-prefix word
        words.push(name.len()); // length prefix
        // chars padded to whole words
        let mut chars: Vec<u8> = name.as_bytes().to_vec();
        while !chars.len().is_multiple_of(std::mem::size_of::<usize>()) {
            chars.push(0);
        }
        for chunk in chars.chunks_exact(std::mem::size_of::<usize>()) {
            words.push(usize::from_le_bytes(chunk.try_into().unwrap()));
        }
        // Remember string base address (resolved at finalization).
        tuple_ptrs.push(str_ptr_idx); // index into `words`
    }
    // Tuples and cons cells need to know absolute addresses. We
    // allocate the Vec first, get its base ptr, then patch.
    let base_offset_for_tuples = words.len();
    for (i, (_, v)) in items.iter().enumerate() {
        let _ = i;
        words.push(make_length_word(2, 0).0); // tuple header
        words.push(0); // placeholder for string ptr
        // The "int" field is a TAGGED int.
        words.push(PolyWord::tagged(*v).0);
    }
    let base_offset_for_conses = words.len();
    for _ in items {
        words.push(make_length_word(2, 0).0);
        words.push(0); // placeholder for tuple ptr
        words.push(0); // placeholder for tail
    }

    // Move to a Box so the address is stable.
    let storage: Box<[usize]> = words.into_boxed_slice();
    let base: *mut usize = Box::into_raw(storage).cast();
    let n = items.len();

    // Patch tuple slot 0 = string ptr, cons slot 0 = tuple ptr,
    // cons slot 1 = next cons (or nil).
    // SAFETY: just leaked Box, exclusive access; indices valid.
    unsafe {
        for (i, &str_idx) in tuple_ptrs.iter().enumerate() {
            let tuple_word_off = base_offset_for_tuples + i * 3 + 1; // slot 0
            base.add(tuple_word_off).write(base.add(str_idx) as usize);
        }
        for i in 0..n {
            let cons_off = base_offset_for_conses + i * 3;
            let tuple_off = base_offset_for_tuples + i * 3 + 1; // body[0]
            base.add(cons_off + 1).write(base.add(tuple_off) as usize); // head = tuple ptr
            if i + 1 < n {
                let next_cons_body = base_offset_for_conses + (i + 1) * 3 + 1;
                base.add(cons_off + 2).write(base.add(next_cons_body) as usize);
            } else {
                base.add(cons_off + 2).write(PolyWord::tagged(0).0); // nil
            }
        }
    }

    let _ = OnceCell::<()>::new(); // unused, satisfy import
    // Return pointer to the first cons cell's body.
    unsafe { base.add(base_offset_for_conses + 1) as usize }
}

fn poly_network_get_addr_list_inner() -> PolyWord {
    use std::sync::OnceLock;
    static LIST: OnceLock<usize> = OnceLock::new();
    let addr = *LIST.get_or_init(|| {
        // Common AF_* values on Linux x86-64.
        static ITEMS: &[(&str, isize)] = &[
            ("UNIX", 1),
            ("INET", 2),
            ("INET6", 10),
        ];
        static_string_int_list(ITEMS)
    });
    PolyWord::from_bits(addr)
}

fn poly_network_get_sock_type_list_inner() -> PolyWord {
    use std::sync::OnceLock;
    static LIST: OnceLock<usize> = OnceLock::new();
    let addr = *LIST.get_or_init(|| {
        static ITEMS: &[(&str, isize)] = &[
            ("STREAM", 1),
            ("DGRAM", 2),
            ("RAW", 3),
        ];
        static_string_int_list(ITEMS)
    });
    PolyWord::from_bits(addr)
}

/// `PolySpecificGeneral(threadId, code, arg)` — dispatch various
/// poly-specific queries (architecture, RTS version, etc.).
/// Mirrors `poly_specific.cpp:83-136`.
#[allow(clippy::needless_pass_by_value)]
fn poly_specific_general(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    code: PolyWord,
    _arg: PolyWord,
) -> PolyWord {
    let c = code.untag();
    let s: &[u8] = match c {
        9 => b"polyml-rs",          // GIT_VERSION
        10 => b"Portable-5.9.0",    // RTS version (interpreted)
        12 => b"Interpreted",       // architecture name
        19 => b"",                  // RTS arg help (empty)
        _ => return PolyWord::tagged(0),
    };
    alloc_poly_string(ctx, s)
}

fn poly_interpreted_get_abi_list_inner() -> PolyWord {
    // Returning nil ([]) causes Foreign.sml to raise Option when
    // looking for ("default", _) in the list. Build a single-element
    // list `[("default", 0)]` so that valOf succeeds. The actual
    // ABI value doesn't matter for compilation — only the structure.
    //
    // We have to allocate, but this is called without an alloc_space
    // (legacy Arity0 stub interface). Return a static-ish layout
    // by leaking a Box — only one allocation per process lifetime.
    use crate::length_word::{F_BYTE_OBJ, make_length_word};
    use std::sync::OnceLock;
    static ABI_LIST: OnceLock<usize> = OnceLock::new();
    let addr = *ABI_LIST.get_or_init(|| {
        // Manually lay out:
        //   string "default" — 1 (length word) + ceil(7/8)=1 = 2 words
        //   abi word — 1 word boxed LargeWord (value 0)
        //   tuple — 2 words [string, word]
        //   cons cell — 2 words [tuple, nil=tagged(0)]
        //
        // Total: 2 + 1 + 2 + 2 = 7 words. Lay them out contiguously
        // in a Box<[usize]> with appropriate length-word headers
        // INTERLEAVED.
        //
        // Each object needs its length word AT obj_ptr - 1.
        // Layout (each row = 1 word):
        //   [0]  string length word           ← str_ptr-1 (header)
        //   [1]  string body word 1 (length=7) ← str_ptr+0 (length prefix)
        //   [2]  string body word 2 ("default")← str_ptr+1 (chars)
        //   [3]  abi-word length word          ← abi_ptr-1
        //   [4]  abi-word body (0)             ← abi_ptr+0
        //   [5]  tuple length word             ← tup_ptr-1
        //   [6]  tuple slot 0 (str)            ← tup_ptr+0
        //   [7]  tuple slot 1 (abi)            ← tup_ptr+1
        //   [8]  cons length word              ← cons_ptr-1
        //   [9]  cons head (tup)               ← cons_ptr+0
        //   [10] cons tail (nil)               ← cons_ptr+1
        let storage: Box<[usize; 11]> = Box::new([0; 11]);
        let base: *mut usize = Box::into_raw(storage).cast();
        // SAFETY: just allocated, exclusive access.
        unsafe {
            // String "default" — 2 body words (length-prefix word + chars).
            base.add(0).write(make_length_word(2, F_BYTE_OBJ).0);
            let str_ptr = base.add(1);
            str_ptr.add(0).write(7); // byte length
            let chars: &[u8; 8] = b"default\0";
            std::ptr::copy_nonoverlapping(
                chars.as_ptr(),
                str_ptr.add(1).cast::<u8>(),
                8,
            );
            // ABI word — 1 byte-object word.
            base.add(3).write(make_length_word(1, F_BYTE_OBJ).0);
            let abi_ptr = base.add(4);
            abi_ptr.write(0);
            // Tuple [str, abi] — 2 ordinary words.
            base.add(5).write(make_length_word(2, 0).0);
            let tup_ptr = base.add(6);
            tup_ptr.add(0).write(str_ptr as usize);
            tup_ptr.add(1).write(abi_ptr as usize);
            // Cons [tup, nil] — 2 ordinary words.
            base.add(8).write(make_length_word(2, 0).0);
            let cons_ptr = base.add(9);
            cons_ptr.add(0).write(tup_ptr as usize);
            cons_ptr.add(1).write(PolyWord::tagged(0).0); // nil
            cons_ptr as usize
        }
    });
    PolyWord::from_bits(addr)
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
    let mut args = get_command_args();
    if args.is_empty() {
        args.push("poly".to_string());
    }
    build_string_list(ctx, &args)
}

/// Build an SML list-of-strings (`string list`) from a slice of Rust
/// strings, allocating into the RTS context's alloc space.
fn build_string_list(ctx: &mut RtsContext<'_>, strs: &[String]) -> PolyWord {
    let mut tail = PolyWord::tagged(0); // nil
    for s in strs.iter().rev() {
        let str_word = alloc_poly_string(ctx, s.as_bytes());
        let Some(space) = ctx.alloc_space.as_mut() else {
            return PolyWord::tagged(0);
        };
        let cons = space.alloc(2);
        // SAFETY: just allocated 2 words.
        unsafe {
            crate::space::set_length_word(cons, 2, 0);
            cons.add(0).write(str_word);
            cons.add(1).write(tail);
        }
        tail = PolyWord::from_ptr(cons.cast_const());
    }
    tail
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
fn poly_get_function_name(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    _code: PolyWord,
) -> PolyWord {
    alloc_empty_string(ctx)
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
        // 3/4: open file for text/binary input. `arg` is the filename
        //     as a PolyString.
        // 5/6: open file for text/binary output.
        // 13/14: open file for text/binary append.
        3 | 4 => open_file_input(ctx, arg),
        5 | 6 => open_file_output(ctx, arg, false),
        13 | 14 => open_file_output(ctx, arg, true),
        // 7: close the file (and mark the stream as closed).
        7 => close_file(strm),
        // 8/9: read text/binary into an array. arg is a 3-tuple
        //      (buffer, offset, length). Returns # bytes read
        //      (0 = EOF).
        8 | 9 => read_array_from_stream(strm, arg),
        // 10/26: read text/binary as a (PolyML) string. Route to
        // std::io::stdin for fd 0 so the bootstrap can actually
        // consume input from a pipe; everything else returns
        // an empty string (= EOF) which is safe.
        10 | 26 => read_string_from_stream(ctx, strm, arg),
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
        // 50: open directory; 51: read next entry; 52: close.
        // We use a global directory-state map keyed by a fresh id.
        50 => open_directory(ctx, arg),
        51 => read_directory(ctx, strm),
        52 => close_directory(strm),
        // 54: getcwd
        54 => get_current_dir(ctx),
        // 57: isDir(name) → 1 / 0
        57 => fs_is_dir(arg),
        // 60: fullPath(name) → canonicalized absolute path
        60 => fs_full_path(ctx, arg),
        // 61: modTime(name) → microseconds since epoch as tagged-or-arb int
        61 => fs_mod_time(ctx, arg),
        // 62: fileSize(name)
        62 => fs_file_size(ctx, arg),
        // 64: remove(name) — delete a file. HOL4's HolSat writes DIMACS temp
        //     files (via tmpName) and clean_delete()s them; without this they
        //     leak into the temp dir on every SAT/tautLib call.
        64 => fs_remove(arg),
        // 66: access(name, mode) → 1 / 0
        66 => fs_access(arg, strm),
        // 67: tmpName() → a fresh unique temp-file path string.
        //     HOL4's HolSat (dimacsTools) needs this before it falls
        //     through to its pure-SML DPLL prover; without it the call
        //     returns a tagged int and faults on `tmp ^ ".cnf"`.
        67 => fs_tmp_name(ctx),
        // Various stub returns of TAGGED(0):
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

// ---- arbitrary precision (real bignums via num-bigint) ----------
//
// PolyML's boxed bignum format:
//   - F_BYTE_OBJ length word; F_NEGATIVE_BIT set iff negative
//   - body is little-endian magnitude bytes (unsigned),
//     padded to whole words, with trailing zeros allowed but
//     normalised form omits leading zero limbs
//
// We convert between PolyWord ↔ num_bigint::BigInt at the boundary
// of each Poly*Arbitrary RTS function. Tagged-int fast path is
// preserved (no allocation) for the common case where both inputs
// and the result fit; on overflow or boxed inputs, we fall through
// to BigInt math and allocate a boxed result.

use num_bigint::{BigInt, Sign};

/// Read a `PolyWord` as a `BigInt`. Handles both tagged-int and
/// PolyML-boxed bignum representations.
fn poly_word_to_bigint(w: PolyWord) -> Option<BigInt> {
    if w.is_tagged() {
        return Some(BigInt::from(w.untag()));
    }
    if !w.is_data_ptr() {
        return None;
    }
    // SAFETY: caller passes a value the compiler trusts as a bignum.
    let p = w.as_ptr::<PolyWord>();
    let lw = unsafe { crate::space::MemorySpace::length_word_of(p) };
    let flags = crate::length_word::flags_of(lw);
    let n_words = crate::length_word::length_of(lw);
    let sign = if flags & crate::length_word::F_NEGATIVE_BIT != 0 {
        Sign::Minus
    } else {
        Sign::Plus
    };
    // SAFETY: body is n_words words = n_words * 8 bytes.
    let body_ptr = p.cast::<u8>();
    let body =
        unsafe { std::slice::from_raw_parts(body_ptr, n_words * std::mem::size_of::<usize>()) };
    Some(BigInt::from_bytes_le(sign, body))
}

/// Write a `BigInt` into a freshly-allocated boxed bignum object,
/// or return a tagged int when it fits.
fn bigint_to_poly_word(ctx: &mut RtsContext<'_>, n: &BigInt) -> PolyWord {
    use crate::length_word::{F_BYTE_OBJ, F_NEGATIVE_BIT};
    // Fast path: fits in tagged range.
    if let Some(v) = i64_from_bigint_in_tag_range(n) {
        #[allow(clippy::cast_possible_truncation)]
        return PolyWord::tagged(v as isize);
    }
    let (sign, mag_bytes) = n.to_bytes_le();
    if mag_bytes.is_empty() {
        return PolyWord::tagged(0);
    }
    let n_words = mag_bytes.len().div_ceil(std::mem::size_of::<usize>());
    if RTS_TRACE.load(Ordering::Relaxed) {
        eprintln!(
            "  bigint_to_poly_word: BOXED n_words={n_words} sign={sign:?} bytes={mag_bytes:?}",
        );
    }
    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::tagged(0);
    };
    let p = space.alloc(n_words);
    let mut flags = F_BYTE_OBJ;
    if sign == Sign::Minus {
        flags |= F_NEGATIVE_BIT;
    }
    // SAFETY: just allocated n_words.
    unsafe {
        crate::space::set_length_word(p, n_words, flags);
        // Zero the tail (in case mag_bytes doesn't fill the last word).
        let dst = p.cast::<u8>();
        std::ptr::copy_nonoverlapping(mag_bytes.as_ptr(), dst, mag_bytes.len());
        let zeros = n_words * std::mem::size_of::<usize>() - mag_bytes.len();
        if zeros > 0 {
            std::ptr::write_bytes(dst.add(mag_bytes.len()), 0, zeros);
        }
    }
    PolyWord::from_ptr(p.cast_const())
}

fn i64_from_bigint_in_tag_range(n: &BigInt) -> Option<i64> {
    let v: i64 = n.try_into().ok()?;
    if i128::from(v) >= MIN_TAGGED as i128 && i128::from(v) <= MAX_TAGGED as i128 {
        Some(v)
    } else {
        None
    }
}

/// Bignum-aware ARB_ADD.
///
/// Called from the interpreter when the fast path overflows or
/// one operand is already boxed. Computes `y + x` (matching
/// upstream `bytecode.cpp:1077` `INSTR_arbAdd` where y is the
/// peek and x is the pop).
pub fn arb_add_via_bigint(
    alloc: Option<&mut crate::space::MemorySpace>,
    x: PolyWord,
    y: PolyWord,
) -> PolyWord {
    let (Some(a), Some(b)) = (poly_word_to_bigint(y), poly_word_to_bigint(x)) else {
        return PolyWord::tagged(0);
    };
    let mut ctx = RtsContext {
        alloc_space: alloc,
        raised_exception: None,
        rts: None,
    };
    bigint_to_poly_word(&mut ctx, &(a + b))
}

pub fn arb_sub_via_bigint(
    alloc: Option<&mut crate::space::MemorySpace>,
    x: PolyWord,
    y: PolyWord,
) -> PolyWord {
    let (Some(a), Some(b)) = (poly_word_to_bigint(y), poly_word_to_bigint(x)) else {
        return PolyWord::tagged(0);
    };
    let mut ctx = RtsContext {
        alloc_space: alloc,
        raised_exception: None,
        rts: None,
    };
    bigint_to_poly_word(&mut ctx, &(a - b))
}

pub fn arb_mult_via_bigint(
    alloc: Option<&mut crate::space::MemorySpace>,
    x: PolyWord,
    y: PolyWord,
) -> PolyWord {
    let (Some(a), Some(b)) = (poly_word_to_bigint(y), poly_word_to_bigint(x)) else {
        return PolyWord::tagged(0);
    };
    let mut ctx = RtsContext {
        alloc_space: alloc,
        raised_exception: None,
        rts: None,
    };
    bigint_to_poly_word(&mut ctx, &(a * b))
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

/// Generic Poly*Arbitrary helper: fast-path on two tagged ints,
/// fall through to BigInt on any boxed input or overflow.
/// `op_fast` returns `None` to signal "use the slow path".
fn arb_binop<FFast, FSlow>(
    ctx: &mut RtsContext<'_>,
    arg1: PolyWord,
    arg2: PolyWord,
    op_fast: FFast,
    op_slow: FSlow,
) -> PolyWord
where
    FFast: FnOnce(i128, i128) -> Option<i128>,
    FSlow: FnOnce(&BigInt, &BigInt) -> BigInt,
{
    // Note: upstream's `arb.cpp` always computes `arg2 OP arg1`
    // (the args were pushed L→R and pulled R→L). Our both_tagged
    // helper already mirrors that.
    if let Some((x, y)) = both_tagged(arg2, arg1)
        && let Some(r) = op_fast(x as i128, y as i128)
        && fits_tagged(r)
    {
        return PolyWord::tagged(r as isize);
    }
    let (Some(a), Some(b)) = (poly_word_to_bigint(arg2), poly_word_to_bigint(arg1)) else {
        return PolyWord::tagged(0);
    };
    let r = op_slow(&a, &b);
    bigint_to_poly_word(ctx, &r)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_add_arbitrary(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg1: PolyWord,
    arg2: PolyWord,
) -> PolyWord {
    arb_binop(ctx, arg1, arg2, i128::checked_add, |a, b| a + b)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_subtract_arbitrary(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg1: PolyWord,
    arg2: PolyWord,
) -> PolyWord {
    // Upstream order: result = arg2 - arg1 (arb_binop already mirrors that).
    arb_binop(ctx, arg1, arg2, i128::checked_sub, |a, b| a - b)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_multiply_arbitrary(ctx: &mut RtsContext<'_>, _tid: PolyWord, arg1: PolyWord, arg2: PolyWord)
    -> PolyWord
{
    // Mult needs the bigint path because SML's `maxShort` loop
    // multiplies until overflow and uses `largeIntIsSmall` on the
    // result — without a boxed result, that loop never terminates.
    arb_binop(ctx, arg1, arg2, i128::checked_mul, |a, b| a * b)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_divide_arbitrary(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg1: PolyWord,
    arg2: PolyWord,
) -> PolyWord {
    // arg1 = dividend, arg2 = divisor (see PolyQuotRemArbitraryPair).
    if let Some((dvdr, dvd)) = both_tagged(arg2, arg1) {
        if dvdr == 0 {
            return PolyWord::tagged(0);
        }
        if !(dvd == MIN_TAGGED && dvdr == -1) {
            return PolyWord::tagged(dvd / dvdr);
        }
        // Fall through to bigint for MIN_TAGGED / -1 overflow.
    }
    let (Some(a), Some(b)) = (poly_word_to_bigint(arg1), poly_word_to_bigint(arg2)) else {
        return PolyWord::tagged(0);
    };
    if b == BigInt::from(0) {
        return PolyWord::tagged(0);
    }
    bigint_to_poly_word(ctx, &(a / b))
}

#[allow(clippy::needless_pass_by_value)]
fn poly_remainder_arbitrary(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg1: PolyWord,
    arg2: PolyWord,
) -> PolyWord {
    if let Some((dvdr, dvd)) = both_tagged(arg2, arg1) {
        if dvdr == 0 {
            return PolyWord::tagged(0);
        }
        if !(dvd == MIN_TAGGED && dvdr == -1) {
            return PolyWord::tagged(dvd % dvdr);
        }
    }
    let (Some(a), Some(b)) = (poly_word_to_bigint(arg1), poly_word_to_bigint(arg2)) else {
        return PolyWord::tagged(0);
    };
    if b == BigInt::from(0) {
        return PolyWord::tagged(0);
    }
    bigint_to_poly_word(ctx, &(a % b))
}

#[allow(clippy::needless_pass_by_value)]
fn poly_compare_arbitrary(_: &mut RtsContext<'_>, arg1: PolyWord, arg2: PolyWord) -> PolyWord {
    // IntInf/LargeInt compare: TAGGED sign(arg1 - arg2) ∈ {-1,0,1}.
    // arb.cpp:1858-1862 PolyCompareArbitrary = compareLong(arg2,arg1) = sign(arg1-arg2).
    // The SML side (Int.sml:84-96, InitialBasis.ML) only calls this when at least one
    // operand is BOXED (two-tagged is handled inline by the compiler), so the old code
    // — a sign-inverted tagged branch over a dead `both_tagged` plus a constant
    // tagged(0) fallback for boxed — meant EVERY real (boxed) comparison returned
    // "equal". Compare uniformly via BigInt (handles tagged + boxed, signed). Word /
    // LargeWord have their own compare opcodes, so everything here is a signed integer.
    use std::cmp::Ordering;
    if arg1.0 == arg2.0 {
        return PolyWord::tagged(0);
    }
    let ord = match (poly_word_to_bigint(arg1), poly_word_to_bigint(arg2)) {
        (Some(a), Some(b)) => a.cmp(&b),
        _ => return PolyWord::tagged(0),
    };
    PolyWord::tagged(match ord {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    })
}

// IntInf.andb/orb/xorb. The SML side (IntInf.sml:77-90) only calls these when an
// operand is BOXED, so the both-tagged fast path is a dead optimisation and the old
// tagged(0) fallback made every real call return 0. num_bigint's signed BitAnd/BitOr/
// BitXor are two's-complement, matching upstream logical_long (arb.cpp:1311-1456).
fn poly_or_arbitrary(ctx: &mut RtsContext<'_>, _tid: PolyWord, arg1: PolyWord, arg2: PolyWord)
    -> PolyWord
{
    if both_tagged(arg1, arg2).is_some() {
        return PolyWord::from_bits(arg1.0 | arg2.0);
    }
    match (poly_word_to_bigint(arg1), poly_word_to_bigint(arg2)) {
        (Some(a), Some(b)) => bigint_to_poly_word(ctx, &(a | b)),
        _ => PolyWord::tagged(0),
    }
}

fn poly_and_arbitrary(ctx: &mut RtsContext<'_>, _tid: PolyWord, arg1: PolyWord, arg2: PolyWord)
    -> PolyWord
{
    if both_tagged(arg1, arg2).is_some() {
        return PolyWord::from_bits(arg1.0 & arg2.0);
    }
    match (poly_word_to_bigint(arg1), poly_word_to_bigint(arg2)) {
        (Some(a), Some(b)) => bigint_to_poly_word(ctx, &(a & b)),
        _ => PolyWord::tagged(0),
    }
}

fn poly_xor_arbitrary(ctx: &mut RtsContext<'_>, _tid: PolyWord, arg1: PolyWord, arg2: PolyWord)
    -> PolyWord
{
    if both_tagged(arg1, arg2).is_some() {
        // XOR cancels the tag bits → set it back.
        return PolyWord::from_bits((arg1.0 ^ arg2.0) | 1);
    }
    match (poly_word_to_bigint(arg1), poly_word_to_bigint(arg2)) {
        (Some(a), Some(b)) => bigint_to_poly_word(ctx, &(a ^ b)),
        _ => PolyWord::tagged(0),
    }
}

/// `IntInf.<<` — arbitrary-precision left shift (= multiply by 2^shift).
/// Backs `PolyShiftLeftArbitrary`; the SML side only routes here when the
/// value or result doesn't fit in a short word, so we MUST handle boxed
/// bignums (the old tagged-only fast path returned TAGGED(0) for those —
/// silently producing 0 for e.g. `IntInf.<<(1, 0w70)`). Go through BigInt
/// so tagged, boxed and negative inputs all work and the result re-boxes.
fn poly_shift_left_arbitrary(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg: PolyWord,
    shift: PolyWord,
) -> PolyWord {
    if !shift.is_tagged() {
        return PolyWord::tagged(0);
    }
    let by = shift.untag();
    if by <= 0 {
        return arg; // shift 0 is identity; negatives don't occur (word arg)
    }
    let Some(n) = poly_word_to_bigint(arg) else {
        return PolyWord::tagged(0);
    };
    #[allow(clippy::cast_sign_loss)]
    let r = n << (by as usize);
    bigint_to_poly_word(ctx, &r)
}

/// `IntInf.~>>` — arbitrary-precision ARITHMETIC right shift (= floor-divide
/// by 2^shift, rounding toward negative infinity). Backs
/// `PolyShiftRightArbitrary`. The old impl did a *logical* shift on the raw
/// (two's-complement) bits of a negative tagged value and returned TAGGED(0)
/// for boxed bignums — so `IntInf.~>>` of a negative gave a huge positive
/// (breaking `Real.toLargeInt` of negatives). `num_bigint`'s `>>` is the
/// arithmetic (floor) shift, which is exactly the right semantics.
fn poly_shift_right_arbitrary(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg: PolyWord,
    shift: PolyWord,
) -> PolyWord {
    if !shift.is_tagged() {
        return PolyWord::tagged(0);
    }
    let by = shift.untag();
    if by <= 0 {
        return arg;
    }
    let Some(n) = poly_word_to_bigint(arg) else {
        return PolyWord::tagged(0);
    };
    #[allow(clippy::cast_sign_loss)]
    let r = n >> (by as usize);
    bigint_to_poly_word(ctx, &r)
}

/// GCD with an i64 tagged fast path and a BigInt fallback for boxed operands
/// (arb.cpp:1864-1904). The old tagged-only impl returned 0 for any boxed input.
#[allow(clippy::needless_pass_by_value)]
fn poly_gcd_arbitrary(ctx: &mut RtsContext<'_>, _tid: PolyWord, arg1: PolyWord, arg2: PolyWord)
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
    use num_integer::Integer;
    match (poly_word_to_bigint(arg1), poly_word_to_bigint(arg2)) {
        (Some(a), Some(b)) => bigint_to_poly_word(ctx, &a.gcd(&b)),
        _ => PolyWord::tagged(0),
    }
}

/// LCM = (|x| / gcd(x,y)) * |y|, with care around zero. Tagged fast path + BigInt
/// fallback for boxed operands / tagged-overflow results (was 0 for both before).
#[allow(clippy::needless_pass_by_value)]
fn poly_lcm_arbitrary(ctx: &mut RtsContext<'_>, _tid: PolyWord, arg1: PolyWord, arg2: PolyWord)
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
    use num_integer::Integer;
    match (poly_word_to_bigint(arg1), poly_word_to_bigint(arg2)) {
        (Some(a), Some(b)) => bigint_to_poly_word(ctx, &a.lcm(&b)),
        _ => PolyWord::tagged(0),
    }
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
    // Upstream `arb.cpp:1825` calls `quotRem(taskData, pushedArg2,
    // pushedArg1, ...)`, and `quotRem(td, y, x, ...)` computes x/y.
    // So arg1 is the dividend, arg2 is the divisor.
    // `IntInf.quot/rem` use truncated division (Rust's `/` and `%`).
    let (q_word, r_word) = if let Some((dvdr, dvd)) = both_tagged(arg2, arg1) {
        if dvdr == 0 {
            return PolyWord::tagged(0);
        }
        if dvd == MIN_TAGGED && dvdr == -1 {
            // Tagged-overflow on quotient (MIN/-1) — need bigint path.
            let a = BigInt::from(dvd);
            let b = BigInt::from(dvdr);
            let q = bigint_to_poly_word(ctx, &(&a / &b));
            let r = bigint_to_poly_word(ctx, &(&a % &b));
            (q, r)
        } else {
            (PolyWord::tagged(dvd / dvdr), PolyWord::tagged(dvd % dvdr))
        }
    } else {
        let (Some(a), Some(b)) =
            (poly_word_to_bigint(arg1), poly_word_to_bigint(arg2))
        else {
            return PolyWord::tagged(0);
        };
        // `b == 0` can't happen at the bignum level (would be tagged 0).
        if b == BigInt::from(0) {
            return PolyWord::tagged(0);
        }
        let q = bigint_to_poly_word(ctx, &(&a / &b));
        let r = bigint_to_poly_word(ctx, &(&a % &b));
        (q, r)
    };
    // Allocate a 2-word ordinary object holding (q, r).
    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::tagged(0);
    };
    let p = space.alloc(2);
    // SAFETY: just allocated 2 words.
    unsafe {
        crate::space::set_length_word(p, 2, 0);
        p.write(q_word);
        p.add(1).write(r_word);
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
        // Boxed: read first body word as the low limb of the MAGNITUDE.
        // Bignums are sign-magnitude, so for a negative-flagged object the
        // two's-complement low word is `0 - low` (arb.cpp:1936 `if(negative) p=0-p`).
        let p = arg.as_ptr::<PolyWord>();
        // SAFETY: caller-trusted boxed bignum.
        let low = unsafe { (*p).0 };
        let lw = unsafe { crate::space::MemorySpace::length_word_of(p) };
        if crate::length_word::flags_of(lw) & crate::length_word::F_NEGATIVE_BIT != 0 {
            0usize.wrapping_sub(low)
        } else {
            low
        }
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

/// `PolySetCodeByte(closure, offset, byteVal)` — write a single byte
/// into a code object referenced by a closure. Mirrors
/// `poly_specific.cpp:396-402`.
#[allow(clippy::needless_pass_by_value)]
fn poly_set_code_byte(
    _ctx: &mut RtsContext<'_>,
    closure: PolyWord,
    offset: PolyWord,
    byte_val: PolyWord,
) -> PolyWord {
    if !closure.is_data_ptr() {
        return PolyWord::tagged(0);
    }
    let cl_ptr = closure.as_ptr::<PolyWord>();
    // SAFETY: caller (compiler-generated bytecode) is trusted.
    unsafe {
        let code_word = *cl_ptr;
        if !code_word.is_data_ptr() {
            return PolyWord::tagged(0);
        }
        let code_ptr = code_word.as_ptr::<u8>().cast_mut();
        let off = offset.untag() as usize;
        let b = byte_val.untag() as u8;
        code_ptr.add(off).write(b);
    }
    PolyWord::tagged(0)
}

/// `PolyGetCodeConstant(closure, offset, flags)` — read a PolyWord-
/// sized constant from a code object at byte offset. Mirrors
/// `poly_specific.cpp:371-393`.
#[allow(clippy::needless_pass_by_value)]
fn poly_get_code_constant(
    _ctx: &mut RtsContext<'_>,
    closure: PolyWord,
    offset: PolyWord,
    _flags: PolyWord,
) -> PolyWord {
    if !closure.is_data_ptr() {
        return PolyWord::tagged(0);
    }
    let cl_ptr = closure.as_ptr::<PolyWord>();
    // SAFETY: caller trusted; assume code object pointer.
    unsafe {
        let code_word = *cl_ptr;
        if !code_word.is_data_ptr() {
            return PolyWord::tagged(0);
        }
        let code_ptr = code_word.as_ptr::<u8>();
        let off = offset.untag() as usize;
        let val_ptr = code_ptr.add(off).cast::<PolyWord>();
        val_ptr.read_unaligned()
    }
}

/// `PolyRealDoubleToString(threadId, arg, kind, prec)` — format a
/// boxed Real to an SML string. `kind` is a tagged char ('e', 'E',
/// 'f', 'F', or anything else → 'G'); `prec` is a tagged int.
/// Output uses SML conventions: '-' replaced by '~', '+' removed
/// after 'E', leading zeros after 'E' suppressed.
/// Mirrors `reals.cpp:PolyRealDoubleToString`.
#[allow(clippy::needless_pass_by_value)]
fn poly_real_double_to_string(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg: PolyWord,
    kind: PolyWord,
    prec: PolyWord,
) -> PolyWord {
    let v: f64 = if arg.is_data_ptr() {
        // SAFETY: caller passes a boxed Real (1-word byte object).
        unsafe { *arg.as_ptr::<f64>() }
    } else {
        0.0
    };
    let kind_ch = if kind.is_tagged() {
        u32::try_from(kind.untag()).ok().and_then(char::from_u32).unwrap_or('G')
    } else {
        'G'
    };
    #[allow(clippy::cast_sign_loss)]
    let p = if prec.is_tagged() {
        prec.untag().max(0) as usize
    } else {
        6
    };

    // Non-finite handled by SML wrapper, but be defensive.
    if v.is_nan() {
        return alloc_poly_string(ctx, b"nan");
    }
    if v.is_infinite() {
        let s: &[u8] = if v < 0.0 { b"~inf" } else { b"inf" };
        return alloc_poly_string(ctx, s);
    }

    let raw = match kind_ch {
        'e' | 'E' => format!("{v:.*E}", p),
        'f' | 'F' => format!("{v:.*}", p),
        // G: use %g-like semantics. Use Rust's default if precision
        // is at least the magnitude of the integer part; else fall
        // back to scientific. The post-processor below strips
        // trailing zeros.
        _ => {
            let abs = v.abs();
            let exp10 = if abs == 0.0 {
                0
            } else {
                abs.log10().floor() as i32
            };
            let prec_g = if p == 0 { 1 } else { p };
            if exp10 < -4 || exp10 >= prec_g as i32 {
                // Use scientific with prec_g - 1 fractional digits.
                let s = format!("{v:.*E}", prec_g - 1);
                strip_g_trailing(&s)
            } else {
                // Use fixed with (prec_g - 1 - exp10) fractional digits.
                let nfrac = (prec_g as i32 - 1 - exp10).max(0) as usize;
                let s = format!("{v:.*}", nfrac);
                strip_g_trailing(&s)
            }
        }
    };

    let mut out: Vec<u8> = Vec::with_capacity(raw.len() + 4);
    let bytes = raw.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'-' => out.push(b'~'),
            b'+' => {} // dropped (only appears after E)
            b'e' | b'E' => {
                out.push(b'E');
                // Skip a single + if present, then skip leading zeros
                // (but keep at least one digit).
                i += 1;
                let mut sign: Option<u8> = None;
                if i < bytes.len() && (bytes[i] == b'+' || bytes[i] == b'-') {
                    sign = Some(if bytes[i] == b'-' { b'~' } else { 0 });
                    i += 1;
                }
                // Skip leading zeros.
                let digits_start = i;
                while i < bytes.len() && bytes[i] == b'0' {
                    i += 1;
                }
                // If we consumed everything, leave one '0'.
                let no_digits_left = i >= bytes.len() || !bytes[i].is_ascii_digit();
                if let Some(s) = sign
                    && s != 0
                    && !(no_digits_left && i == digits_start)
                {
                    out.push(s);
                }
                if no_digits_left {
                    out.push(b'0');
                }
                continue;
            }
            c => out.push(c),
        }
        i += 1;
    }
    alloc_poly_string(ctx, &out)
}

fn strip_g_trailing(s: &str) -> String {
    // For %G: strip trailing zeros after decimal point, then strip a
    // dangling '.'. Don't touch the exponent suffix.
    let (mantissa, exp_part) = match s.find(['e', 'E']) {
        Some(idx) => (&s[..idx], &s[idx..]),
        None => (s, ""),
    };
    if !mantissa.contains('.') {
        return s.to_string();
    }
    let trimmed = mantissa.trim_end_matches('0');
    let trimmed = trimmed.trim_end_matches('.');
    let mut out = String::with_capacity(s.len());
    out.push_str(trimmed);
    out.push_str(exp_part);
    out
}

/// `PolyRealFrexp(threadId, x)` — split a Real `x` into
/// `(mantissa, exponent)` where `x = mantissa * 2^exponent` and
/// `mantissa ∈ [0.5, 1.0)`. SML signature: `real -> int * real`.
/// Returns a 2-word tuple `[boxed_mantissa, tagged_exponent]`.
#[allow(clippy::needless_pass_by_value)]
/// Read a `PolyWord` argument as an `f64` (boxed Real = 1-word byte object).
fn read_real_word(x: PolyWord) -> f64 {
    if x.is_data_ptr() {
        // SAFETY: caller passes a boxed Real (1-word byte object).
        unsafe { *x.as_ptr::<f64>() }
    } else {
        0.0
    }
}

/// IEEE-754 `nextafter(x, y)`: the next representable double after `x` in the
/// direction of `y`. Rust std has no stable `next_after`, so do the standard
/// bit-pattern walk (same-sign doubles order monotonically by bit pattern).
fn next_after(x: f64, y: f64) -> f64 {
    if x.is_nan() || y.is_nan() {
        return f64::NAN;
    }
    if x == y {
        return y;
    }
    if x == 0.0 {
        // Smallest subnormal toward y.
        return f64::from_bits(1).copysign(y);
    }
    let bits = x.to_bits();
    let next = if (y > x) == (x > 0.0) { bits + 1 } else { bits - 1 };
    f64::from_bits(next)
}

/// Box an `f64` as a PolyML Real (1-word byte object).
fn box_real(ctx: &mut RtsContext<'_>, v: f64) -> PolyWord {
    use crate::length_word::F_BYTE_OBJ;
    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::tagged(0);
    };
    let p = space.alloc(1);
    // SAFETY: just allocated 1 word.
    unsafe {
        crate::space::set_length_word(p, 1, F_BYTE_OBJ);
        p.cast::<f64>().write(v);
    }
    PolyWord::from_ptr(p.cast_const())
}

fn poly_real_frexp(ctx: &mut RtsContext<'_>, _tid: PolyWord, x: PolyWord) -> PolyWord {
    use crate::length_word::F_BYTE_OBJ;
    let v: f64 = if x.is_data_ptr() {
        // SAFETY: caller passes a boxed Real (1-word byte object).
        unsafe { *x.as_ptr::<f64>() }
    } else {
        0.0
    };
    // Rust doesn't have built-in frexp; use the standard
    // decomposition via integer bit pattern manipulation.
    let (mantissa, exponent) = frexp_f64(v);

    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::tagged(0);
    };
    // Allocate the mantissa (boxed Real, 1 word).
    let m_ptr = space.alloc(1);
    // SAFETY: just allocated 1 word.
    unsafe {
        crate::space::set_length_word(m_ptr, 1, F_BYTE_OBJ);
        m_ptr.cast::<f64>().write(mantissa);
    }
    // Allocate the tuple: 2 words, ordinary object.
    let t_ptr = space.alloc(2);
    // SAFETY: just allocated 2 words.
    unsafe {
        crate::space::set_length_word(t_ptr, 2, 0);
        t_ptr.write(PolyWord::tagged(exponent as isize));
        t_ptr.add(1).write(PolyWord::from_ptr(m_ptr.cast_const()));
    }
    PolyWord::from_ptr(t_ptr.cast_const())
}

/// Pure-Rust frexp for f64. Returns (mantissa, exponent) such that
/// x = mantissa * 2^exponent and 0.5 <= |mantissa| < 1.0 (or 0).
fn frexp_f64(x: f64) -> (f64, i32) {
    if x == 0.0 || x.is_nan() || x.is_infinite() {
        return (x, 0);
    }
    let bits = x.to_bits();
    let exp_field = ((bits >> 52) & 0x7ff) as i32;
    let new_exp = if exp_field == 0 {
        // Subnormal: normalise by multiplying by 2^54.
        #[allow(clippy::cast_precision_loss)]
        let scaled = x * ((1u64 << 54) as f64);
        let (m, e) = frexp_f64(scaled);
        return (m, e - 54);
    } else {
        exp_field - 1022
    };
    // Force the exponent field to 1022 (= bias-1) so the result
    // is in [0.5, 1.0) with the original sign and mantissa bits.
    let new_bits = (bits & !(0x7ff << 52)) | (1022u64 << 52);
    (f64::from_bits(new_bits), new_exp)
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
    // Route via std::io for fds 1/2; write real files via their fd.
    #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
    let fd = (fd_plus_one - 1) as i32;
    let n = match fd {
        1 => std::io::stdout().write(slice).unwrap_or(0),
        2 => std::io::stderr().write(slice).unwrap_or(0),
        0 => 0,
        _ => {
            use std::os::fd::FromRawFd;
            // SAFETY: fd is a live fd opened by open_file_output. We
            // reconstruct a File to call write, then leak it back via
            // into_raw_fd so Drop does NOT close the still-in-use fd.
            let mut f = unsafe { std::fs::File::from_raw_fd(fd) };
            let n = f.write(slice).unwrap_or(0);
            use std::os::fd::IntoRawFd;
            let _ = f.into_raw_fd();
            n
        }
    };
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_possible_wrap)]
    PolyWord::tagged(n as isize)
}

/// Global state for open directories. Each entry is a Vec of
/// remaining filenames (as bytes). Index = the "fd" stored in
/// the wrapped-stream object (we use `id + 1`, 0 = closed).
static DIR_STATE: std::sync::Mutex<Vec<Option<Vec<Vec<u8>>>>> =
    std::sync::Mutex::new(Vec::new());

/// IO subcode 50: open directory. Wraps the read-dir iterator in
/// a stream-like object keyed by an integer id.
fn open_directory(ctx: &mut RtsContext<'_>, name_arg: PolyWord) -> PolyWord {
    let Some(name) = poly_string_to_rust(name_arg) else {
        return PolyWord::tagged(0);
    };
    if RTS_TRACE.load(Ordering::Relaxed) {
        eprintln!("  openDir({name:?})");
    }
    let Ok(entries) = std::fs::read_dir(&name) else {
        // Raise OS.SysErr — but for now, return a "closed" stream
        // so reallyexists handles it gracefully via SysErr handler.
        ctx.raised_exception = Some(make_simple_exception(
            ctx,
            &format!("openDir failed: {name}"),
        ));
        return PolyWord::tagged(0);
    };
    let mut names: Vec<Vec<u8>> = entries
        .filter_map(Result::ok)
        .map(|e| e.file_name().into_encoded_bytes())
        .collect();
    // Match upstream readDirectory which skips "." and "..".
    names.retain(|b| !(b == b"." || b == b".."));
    let id = {
        let mut state = DIR_STATE.lock().unwrap();
        let id = state.iter().position(Option::is_none).unwrap_or_else(|| {
            state.push(None);
            state.len() - 1
        });
        state[id] = Some(names);
        id
    };
    // Wrap as if it were an fd. wrap_file_descriptor stores fd+1
    // so passing `id` here yields a box containing `id+1` (0 = closed).
    #[allow(clippy::cast_possible_truncation)]
    wrap_file_descriptor(ctx, id as u32)
}

/// IO subcode 51: read next directory entry. Returns "" at end.
fn read_directory(ctx: &mut RtsContext<'_>, strm: PolyWord) -> PolyWord {
    if !strm.is_data_ptr() {
        return alloc_empty_string(ctx);
    }
    // SAFETY: strm is a wrapped-fd object.
    let id_plus_one = unsafe { *strm.as_ptr::<PolyWord>() }.0;
    if id_plus_one == 0 {
        return alloc_empty_string(ctx);
    }
    let id = id_plus_one - 1;
    let popped = {
        let mut state = DIR_STATE.lock().unwrap();
        if let Some(Some(names)) = state.get_mut(id) {
            names.pop()
        } else {
            None
        }
    };
    if let Some(name) = popped {
        return alloc_poly_string(ctx, &name);
    }
    alloc_empty_string(ctx)
}

/// IO subcode 52: close directory.
fn close_directory(strm: PolyWord) -> PolyWord {
    if !strm.is_data_ptr() {
        return PolyWord::tagged(0);
    }
    let p = strm.as_ptr::<PolyWord>().cast_mut();
    // SAFETY: strm is a wrapped object.
    unsafe {
        let id_plus_one = (*p).0;
        if id_plus_one > 0 {
            let id = id_plus_one - 1;
            let mut state = DIR_STATE.lock().unwrap();
            if let Some(slot) = state.get_mut(id) {
                *slot = None;
            }
        }
        p.write(PolyWord::from_bits(0));
    }
    PolyWord::tagged(0)
}

/// IO subcode 54: `OS.FileSys.getDir`.
fn get_current_dir(ctx: &mut RtsContext<'_>) -> PolyWord {
    let bytes = std::env::current_dir()
        .map(|p| p.into_os_string().into_encoded_bytes())
        .unwrap_or_default();
    alloc_poly_string(ctx, &bytes)
}

/// IO subcode 67: `OS.FileSys.tmpName` — return a unique temporary
/// file path. The file is NOT created; callers (`TextIO.openOut`) open
/// it themselves, and HOL4 concatenates an extension first, so we hand
/// back a bare unique stem in the system temp dir. Mirrors
/// `basicio.cpp:1002`. Uniqueness = pid + a monotonic counter so the
/// repeated CNF files HolSat writes never collide.
fn fs_tmp_name(ctx: &mut RtsContext<'_>) -> PolyWord {
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let mut path = std::env::temp_dir();
    path.push(format!("polymlrs_tmp_{pid}_{n}"));
    alloc_poly_string(ctx, path.into_os_string().into_encoded_bytes().as_slice())
}

/// IO subcode 64: `OS.FileSys.remove` — delete a file. Best-effort:
/// errors are swallowed (callers like HOL4's `clean_delete` already wrap
/// this in an exception handler), and the result is unit (`TAGGED(0)`).
fn fs_remove(arg: PolyWord) -> PolyWord {
    if let Some(name) = poly_string_to_rust(arg) {
        let _ = std::fs::remove_file(&name);
    }
    PolyWord::tagged(0)
}

/// IO subcode 57: `OS.FileSys.isDir`.
fn fs_is_dir(arg: PolyWord) -> PolyWord {
    let Some(name) = poly_string_to_rust(arg) else {
        return PolyWord::tagged(0);
    };
    match std::fs::metadata(&name) {
        Ok(m) if m.is_dir() => PolyWord::tagged(1),
        _ => PolyWord::tagged(0),
    }
}

/// IO subcode 60: `OS.FileSys.fullPath` — canonicalize.
fn fs_full_path(ctx: &mut RtsContext<'_>, arg: PolyWord) -> PolyWord {
    let Some(name) = poly_string_to_rust(arg) else {
        return alloc_empty_string(ctx);
    };
    let canon = std::fs::canonicalize(&name).unwrap_or_else(|_| name.into());
    alloc_poly_string(ctx, canon.into_os_string().into_encoded_bytes().as_slice())
}

/// IO subcode 61: `OS.FileSys.modTime` — microseconds since epoch.
/// Returns a tagged or arbitrary-precision integer.
fn fs_mod_time(ctx: &mut RtsContext<'_>, arg: PolyWord) -> PolyWord {
    let Some(name) = poly_string_to_rust(arg) else {
        return PolyWord::tagged(0);
    };
    let usecs: i128 = std::fs::metadata(&name)
        .ok()
        .and_then(|m| m.modified().ok())
        .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
        .map_or(0, |d| {
            i128::from(d.as_secs()) * 1_000_000 + i128::from(d.subsec_micros())
        });
    int_to_poly_word(ctx, usecs)
}

/// IO subcode 62: `OS.FileSys.fileSize`.
fn fs_file_size(ctx: &mut RtsContext<'_>, arg: PolyWord) -> PolyWord {
    let Some(name) = poly_string_to_rust(arg) else {
        return PolyWord::tagged(0);
    };
    let size = std::fs::metadata(&name).map(|m| m.len()).unwrap_or(0);
    int_to_poly_word(ctx, i128::from(size))
}

/// IO subcode 66: `OS.FileSys.access(name, mode)`.
/// The mode is a bit-set: 1=read, 2=write, 4=exec, 8=exists.
fn fs_access(name_arg: PolyWord, mode_arg: PolyWord) -> PolyWord {
    let Some(name) = poly_string_to_rust(name_arg) else {
        return PolyWord::tagged(0);
    };
    let Ok(meta) = std::fs::metadata(&name) else {
        return PolyWord::tagged(0);
    };
    let mode = mode_arg.untag();
    let permissions = meta.permissions();
    let ok = if mode & 8 != 0 {
        true // existence
    } else {
        // For simplicity: allow read/exec; check write via permissions.
        let want_write = mode & 2 != 0;
        !(want_write && permissions.readonly())
    };
    PolyWord::tagged(if ok { 1 } else { 0 })
}

/// Helper: produce a PolyWord for a (possibly large) integer.
fn int_to_poly_word(ctx: &mut RtsContext<'_>, v: i128) -> PolyWord {
    let n = BigInt::from(v);
    bigint_to_poly_word(ctx, &n)
}

/// Extract a Rust `String` from a PolyString pointer. Returns
/// `None` for non-pointer / non-string-shaped args.
fn poly_string_to_rust(s: PolyWord) -> Option<String> {
    if !s.is_data_ptr() {
        return None;
    }
    // SAFETY: caller passes a PolyString. Layout: word 0 = byte
    // length; subsequent words hold the chars (zero-padded).
    let p = s.as_ptr::<PolyWord>();
    let len = unsafe { (*p).0 };
    if len > 1_000_000 {
        return None; // sanity bound
    }
    let chars_ptr = unsafe { p.add(1).cast::<u8>() };
    let slice = unsafe { std::slice::from_raw_parts(chars_ptr, len) };
    String::from_utf8(slice.to_vec()).ok()
}

/// IO subcodes 3/4: open a file for reading. Returns a wrapped fd
/// or a TAGGED(0) on error (caller treats that as failure).
fn open_file_input(ctx: &mut RtsContext<'_>, name_arg: PolyWord) -> PolyWord {
    use std::os::fd::IntoRawFd;
    let Some(name) = poly_string_to_rust(name_arg) else {
        if RTS_TRACE.load(Ordering::Relaxed) {
            eprintln!("  open_file_input: couldn't decode filename");
        }
        return PolyWord::tagged(0);
    };
    if RTS_TRACE.load(Ordering::Relaxed) {
        eprintln!("  open_file_input: opening {name:?}");
    }
    match std::fs::File::open(&name) {
        Ok(f) => {
            let fd = f.into_raw_fd();
            #[allow(clippy::cast_sign_loss)]
            wrap_file_descriptor(ctx, fd as u32)
        }
        Err(e) => {
            if RTS_TRACE.load(Ordering::Relaxed) {
                eprintln!("  open_file_input: {name:?} → {e}");
            }
            // SML's `TextIO.openIn` chains via `handle IO.Io _ =>
            // ...` to try alternate filenames. We need to actually
            // raise an exception for that fallback to fire. The
            // minimal exception packet is a TAGGED int that won't
            // match `IO.Io` precisely but propagates as an
            // unhandled exception until SOMETHING catches it (the
            // handle is the outermost ` handle _ =>`).
            ctx.raised_exception = Some(make_simple_exception(ctx, "Cannot open"));
            PolyWord::tagged(0)
        }
    }
}

/// Allocate a PolyML-shaped exception packet: a 4-word ordinary
/// object matching `class PolyException : public PolyObject` —
///   [ex_id, ex_name, ex_arg, ex_location]
/// (mlperror.h / save_vec.h in upstream).
///
/// ex_id is normally a unique pointer-like identifier; we use the
/// allocated object's own pointer as a stand-in (each call produces
/// a fresh address, so identity comparison treats each raise as a
/// new exception kind).
/// Public version of [`make_simple_exception`] used by the
/// interpreter when raising an exception for an unresolved RTS
/// entry point.
pub fn make_simple_exception_pub(ctx: &mut RtsContext<'_>, msg: &str) -> PolyWord {
    make_simple_exception(ctx, msg)
}

fn make_simple_exception(ctx: &mut RtsContext<'_>, msg: &str) -> PolyWord {
    let s = alloc_poly_string(ctx, msg.as_bytes());
    let Some(space) = ctx.alloc_space.as_mut() else {
        return s;
    };
    let p = space.alloc(4);
    // SAFETY: just allocated 4 words.
    unsafe {
        crate::space::set_length_word(p, 4, 0);
        // ex_id: self-pointer (so equality compares by identity).
        p.write(PolyWord::from_ptr(p.cast_const()));
        p.add(1).write(s); // ex_name
        p.add(2).write(PolyWord::tagged(0)); // ex_arg = ()
        p.add(3).write(PolyWord::tagged(0)); // ex_location = NONE
    }
    PolyWord::from_ptr(p.cast_const())
}

/// Build an `OS.SysErr` exception packet: `ex_id = TAGGED(2)`
/// (`EXC_syserr`, see `vendor/polyml/libpolyml/sys.h:27` +
/// `run_time.cpp:196`), `ex_name = "SysErr"`, `ex_arg = (msg, NONE)`.
/// The basis `SysErr` constructor is `Global(mkConst(toMachineWord 2))`
/// (`INITIALISE_.ML:538`), so a handler `handle SysErr _` matches a
/// packet whose word-0 ex_id == `TAGGED(2)`. NOTE: this is why
/// `make_simple_exception` (self-pointer ex_id) would NOT be caught as
/// `SysErr` — the identity differs.
fn make_syserr_exception(ctx: &mut RtsContext<'_>, msg: &str) -> PolyWord {
    let name = alloc_poly_string(ctx, b"SysErr");
    let msg_s = alloc_poly_string(ctx, msg.as_bytes());
    let Some(space) = ctx.alloc_space.as_mut() else {
        return msg_s;
    };
    // ex_arg = (msg, NONE) : 2-word tuple. NONE = TAGGED(0).
    let pair = space.alloc(2);
    // SAFETY: just allocated 2 words.
    let pair_w = unsafe {
        crate::space::set_length_word(pair, 2, 0);
        pair.write(msg_s);
        pair.add(1).write(PolyWord::tagged(0)); // NONE
        PolyWord::from_ptr(pair.cast_const())
    };
    let p = space.alloc(4);
    // SAFETY: just allocated 4 words. The earlier `pair` pointer stays
    // valid (bump allocator only advances).
    unsafe {
        crate::space::set_length_word(p, 4, 0);
        p.write(PolyWord::tagged(2)); // ex_id = EXC_syserr
        p.add(1).write(name); // ex_name = "SysErr"
        p.add(2).write(pair_w); // ex_arg = (msg, NONE)
        p.add(3).write(PolyWord::tagged(0)); // ex_location = NONE
    }
    PolyWord::from_ptr(p.cast_const())
}

/// `PolyGetEnv(threadId, name)` — return the real environment value, or
/// raise `SysErr` (so the basis `getEnv` returns `NONE`) when the
/// variable is unset. Mirrors `process_env.cpp:433-436`. Previously a
/// hard stub that returned `""`, which the basis wrapped as `SOME ""`
/// for *every* variable (set or not).
fn poly_get_env(ctx: &mut RtsContext<'_>, _tid: PolyWord, name_arg: PolyWord) -> PolyWord {
    let Some(name) = poly_string_to_rust(name_arg) else {
        ctx.raised_exception = Some(make_syserr_exception(ctx, "getEnv: bad argument"));
        return PolyWord::tagged(0);
    };
    match std::env::var(&name) {
        Ok(val) => alloc_poly_string(ctx, val.as_bytes()),
        Err(_) => {
            // unset or non-UTF-8: both map to NONE, matching upstream's
            // "Not Found" SysErr.
            ctx.raised_exception = Some(make_syserr_exception(ctx, "Not Found"));
            PolyWord::tagged(0)
        }
    }
}

/// IO subcodes 5/6/13/14: open a file for writing (truncating
/// unless `append`).
fn open_file_output(ctx: &mut RtsContext<'_>, name_arg: PolyWord, append: bool) -> PolyWord {
    use std::os::fd::IntoRawFd;
    let Some(name) = poly_string_to_rust(name_arg) else {
        return PolyWord::tagged(0);
    };
    let mut opts = std::fs::OpenOptions::new();
    opts.write(true).create(true);
    if append {
        opts.append(true);
    } else {
        opts.truncate(true);
    }
    opts.open(&name).map_or_else(
        |_| PolyWord::tagged(0),
        |f| {
            let fd = f.into_raw_fd();
            #[allow(clippy::cast_sign_loss)]
            wrap_file_descriptor(ctx, fd as u32)
        },
    )
}

/// IO subcode 7: close the file. Skips stdio (fds 0/1/2). After
/// close, mark the stream object as `0` (= "closed") so re-close
/// is a no-op.
fn close_file(strm: PolyWord) -> PolyWord {
    use std::os::fd::FromRawFd;
    if !strm.is_data_ptr() {
        return PolyWord::tagged(0);
    }
    let p = strm.as_ptr::<PolyWord>().cast_mut();
    // SAFETY: stream is a wrapped-fd object (1 byte-object word
    // holding fd+1).
    unsafe {
        let fd_plus_one = (*p).0;
        if fd_plus_one > 3 {
            // Reconstruct File for Drop's sake (closes fd).
            #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
            let fd = (fd_plus_one - 1) as i32;
            let _ = std::fs::File::from_raw_fd(fd);
        }
        p.write(PolyWord::from_bits(0));
    }
    PolyWord::tagged(0)
}

/// IO subcodes 8/9: read into an ML byte array at `(buffer, offset,
/// length)`. Returns the # bytes actually read (0 = EOF). `arg` is
/// the 3-tuple.
#[allow(clippy::cast_sign_loss)]
#[allow(clippy::cast_possible_wrap)]
fn read_array_from_stream(strm: PolyWord, arg: PolyWord) -> PolyWord {
    use std::io::Read;
    if !strm.is_data_ptr() || !arg.is_data_ptr() {
        return PolyWord::tagged(0);
    }
    let fd_plus_one = unsafe { *strm.as_ptr::<PolyWord>() }.0;
    if fd_plus_one == 0 {
        return PolyWord::tagged(0);
    }
    let p = arg.as_ptr::<PolyWord>();
    let (buf, offset, length) = unsafe { (*p, *p.add(1), *p.add(2)) };
    if !buf.is_data_ptr() || !offset.is_tagged() || !length.is_tagged() {
        return PolyWord::tagged(0);
    }
    let off = offset.untag() as usize;
    let len = length.untag() as usize;
    if len == 0 {
        return PolyWord::tagged(0);
    }
    // SAFETY: buf is an ML byte array; off + len bounded by caller.
    let base = buf.as_ptr::<u8>().cast_mut();
    let slice = unsafe { std::slice::from_raw_parts_mut(base.add(off), len) };
    #[allow(clippy::cast_possible_truncation)]
    let fd = (fd_plus_one - 1) as i32;
    let n = if fd == 0 {
        let syn = read_synthetic_stdin(slice);
        if syn > 0 {
            syn
        } else {
            std::io::stdin().read(slice).unwrap_or(0)
        }
    } else {
        // For non-stdio fds, reconstruct a File to read, then
        // immediately forget it so we don't close the fd.
        use std::os::fd::{FromRawFd, IntoRawFd};
        let mut f = unsafe { std::fs::File::from_raw_fd(fd) };
        let r = f.read(slice).unwrap_or(0);
        let _kept = f.into_raw_fd();
        r
    };
    PolyWord::tagged(n as isize)
}

/// IO subcode 10/26: read a chunk of bytes from a stream into a
/// fresh PolyStringObject (length-prefix word + chars).
///
/// For fd 0 (stdin) we route through `std::io::stdin().read()` so
/// piped input actually reaches the bootstrap. Other fds return an
/// empty string (= EOF) for now — extending to real file fds will
/// require a real file-open path (subcodes 3/4) first.
fn read_string_from_stream(
    ctx: &mut RtsContext<'_>,
    strm: PolyWord,
    arg: PolyWord,
) -> PolyWord {
    use std::io::Read;
    if !strm.is_data_ptr() {
        return alloc_empty_string(ctx);
    }
    // SAFETY: strm is a wrapped-fd object created by
    // `wrap_file_descriptor` (or an equivalent boxed sysword).
    let fd_plus_one = unsafe { *strm.as_ptr::<PolyWord>() }.0;
    #[allow(clippy::cast_sign_loss)]
    let want = if arg.is_tagged() {
        let n = arg.untag();
        if n <= 0 { 0 } else { n as usize }
    } else {
        4096
    };
    let want = want.min(102_400);
    if want == 0 || fd_plus_one == 0 {
        return alloc_empty_string(ctx);
    }
    let mut buf = vec![0u8; want];
    #[allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]
    let fd = (fd_plus_one - 1) as i32;
    let n = if fd == 0 {
        let syn = read_synthetic_stdin(&mut buf);
        if syn > 0 {
            syn
        } else {
            std::io::stdin().read(&mut buf).unwrap_or(0)
        }
    } else {
        // Borrow the fd without taking ownership (= no close).
        use std::os::fd::{FromRawFd, IntoRawFd};
        let mut f = unsafe { std::fs::File::from_raw_fd(fd) };
        let r = f.read(&mut buf).unwrap_or(0);
        let _kept = f.into_raw_fd();
        r
    };
    if n == 0 {
        return alloc_empty_string(ctx);
    }
    alloc_poly_string(ctx, &buf[..n])
}

/// Allocate a `PolyStringObject` (length-prefix word + chars +
/// zero-padded). Mirrors `polystring.cpp:69-84`.
fn alloc_poly_string(ctx: &mut RtsContext<'_>, bytes: &[u8]) -> PolyWord {
    use crate::length_word::F_BYTE_OBJ;
    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::tagged(0);
    };
    // 1 word for the length prefix + ceil(len/8) words for chars.
    let body_words = bytes.len().div_ceil(std::mem::size_of::<usize>());
    let total_words = 1 + body_words;
    let p = space.alloc(total_words);
    // SAFETY: just allocated total_words words.
    unsafe {
        crate::space::set_length_word(p, total_words, F_BYTE_OBJ);
        // Length word (first body word) = byte length.
        p.write(PolyWord::from_bits(bytes.len()));
        // Char bytes follow immediately after the length word.
        let chars_dst = p.add(1).cast::<u8>();
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), chars_dst, bytes.len());
        // Zero the trailing padding bytes (within the last word).
        let padding = body_words * std::mem::size_of::<usize>() - bytes.len();
        if padding > 0 {
            std::ptr::write_bytes(chars_dst.add(bytes.len()), 0, padding);
        }
    }
    PolyWord::from_ptr(p.cast_const())
}

/// `PolyCreateEntryPointObject(threadId, name)` — build a runtime
/// entry-point object for an RTS function looked up by name. Same
/// shape as load-time entry points: 1 word for the token + the
/// name bytes (NUL-terminated). Raises an exception with
/// "entry point not found: NAME" if the name doesn't resolve.
///
/// Mirrors `rtsentry.cpp:113-128` (creatEntryPointObject) +
/// `rtsentry.cpp:141-167` (setEntryPoint).
#[allow(clippy::needless_pass_by_value)]
fn poly_create_entry_point_object(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    name_arg: PolyWord,
) -> PolyWord {
    use crate::length_word::{F_BYTE_OBJ, F_MUTABLE_BIT, F_NO_OVERWRITE, F_WEAK_BIT};
    let Some(name) = poly_string_to_rust(name_arg) else {
        return PolyWord::tagged(0);
    };
    let Some(rts) = ctx.rts else {
        return PolyWord::tagged(0);
    };
    // Build a real entry-point object even if the name isn't
    // registered. Token=0 means "unresolved"; later CALL_FAST_RTS<N>
    // dispatch produces a clean `UnresolvedRts` error rather than a
    // call into the exception packet itself.
    let token = rts.token_for(name.as_str()).unwrap_or_else(|| {
        if RTS_TRACE.load(Ordering::Relaxed) {
            eprintln!("  PolyCreateEntryPointObject: entry point not found: {name}");
        }
        0
    });
    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::tagged(0);
    };
    // Layout: 1 word for token + NUL-terminated name, padded to word.
    let name_bytes_total = name.len() + 1; // include NUL
    let body_words = name_bytes_total.div_ceil(std::mem::size_of::<usize>());
    let total = 1 + body_words;
    let p = space.alloc(total);
    // SAFETY: just allocated `total` words.
    unsafe {
        crate::space::set_length_word(
            p,
            total,
            F_BYTE_OBJ | F_WEAK_BIT | F_MUTABLE_BIT | F_NO_OVERWRITE,
        );
        p.write(PolyWord::from_bits(token));
        let dst = p.add(1).cast::<u8>();
        std::ptr::copy_nonoverlapping(name.as_ptr(), dst, name.len());
        dst.add(name.len()).write(0); // NUL terminator
        // Zero padding within the last word.
        let padding = body_words * std::mem::size_of::<usize>() - name_bytes_total;
        if padding > 0 {
            std::ptr::write_bytes(dst.add(name_bytes_total), 0, padding);
        }
    }
    PolyWord::from_ptr(p.cast_const())
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
        let mut ctx = RtsContext { alloc_space: None, raised_exception: None, rts: None };
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

    #[test]
    fn set_command_args_round_trips() {
        set_command_args(vec!["-I".to_string(), "/tmp".to_string()]);
        let got = get_command_args();
        assert_eq!(got, vec!["-I".to_string(), "/tmp".to_string()]);
        // Reset so other tests don't see this state.
        set_command_args(Vec::new());
    }

    fn ctx() -> RtsContext<'static> {
        RtsContext { alloc_space: None, raised_exception: None, rts: None }
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
        // arg1 / arg2 = 20 / 6 = 3 (truncate toward zero).
        // Upstream order: arg1 = dividend, arg2 = divisor.
        let r = poly_divide_arbitrary(&mut ctx(), t(), PolyWord::tagged(20), PolyWord::tagged(6));
        assert_eq!(r.untag(), 3);
        // -20 / 6 = -3 (truncate toward zero, NOT -4)
        let r = poly_divide_arbitrary(&mut ctx(), t(), PolyWord::tagged(-20), PolyWord::tagged(6));
        assert_eq!(r.untag(), -3);
    }

    #[test]
    fn arb_rem_fast_path() {
        // 20 rem 6 = 2 (sign of dividend)
        let r = poly_remainder_arbitrary(&mut ctx(), t(), PolyWord::tagged(20), PolyWord::tagged(6));
        assert_eq!(r.untag(), 2);
        let r = poly_remainder_arbitrary(&mut ctx(), t(), PolyWord::tagged(-20), PolyWord::tagged(6));
        assert_eq!(r.untag(), -2);
    }

    #[test]
    fn arb_compare() {
        // sign(arg1 - arg2): 5 < 7 -> -1, 7 > 5 -> 1, equal -> 0.
        let r = poly_compare_arbitrary(&mut ctx(), PolyWord::tagged(5), PolyWord::tagged(7));
        assert_eq!(r.untag(), -1);
        let r = poly_compare_arbitrary(&mut ctx(), PolyWord::tagged(7), PolyWord::tagged(5));
        assert_eq!(r.untag(), 1);
        let r = poly_compare_arbitrary(&mut ctx(), PolyWord::tagged(5), PolyWord::tagged(5));
        assert_eq!(r.untag(), 0);
        // negatives
        let r = poly_compare_arbitrary(&mut ctx(), PolyWord::tagged(-3), PolyWord::tagged(2));
        assert_eq!(r.untag(), -1);
    }

    #[test]
    fn arb_compare_boxed_bignums() {
        // The reachable path: at least one operand boxed. 2^70 vs 2^70+1.
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);
        let mut c = RtsContext { alloc_space: Some(&mut space), raised_exception: None, rts: None };
        let big = bigint_to_poly_word(&mut c, &(BigInt::from(1u8) << 70u32));
        let big1 = bigint_to_poly_word(&mut c, &((BigInt::from(1u8) << 70u32) + BigInt::from(1u8)));
        assert!(big.is_data_ptr() && big1.is_data_ptr(), "2^70 should box");
        assert_eq!(poly_compare_arbitrary(&mut c, big, big1).untag(), -1, "2^70 < 2^70+1");
        assert_eq!(poly_compare_arbitrary(&mut c, big1, big).untag(), 1, "2^70+1 > 2^70");
        assert_eq!(poly_compare_arbitrary(&mut c, big, big).untag(), 0, "equal");
        // negative boxed
        let nbig = bigint_to_poly_word(&mut c, &(-(BigInt::from(1u8) << 70u32)));
        assert_eq!(poly_compare_arbitrary(&mut c, nbig, big).untag(), -1, "-2^70 < 2^70");
    }

    #[test]
    fn arb_bitwise_and_gcd_boxed() {
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);
        let mut c = RtsContext { alloc_space: Some(&mut space), raised_exception: None, rts: None };
        // (2^64 | 0xF) & 0xFF == 0xF   (boxed operand -> RTS path)
        let a = bigint_to_poly_word(&mut c, &((BigInt::from(1u8) << 64u32) | BigInt::from(0xFu8)));
        assert!(a.is_data_ptr());
        let r = poly_and_arbitrary(&mut c, t(), a, PolyWord::tagged(0xFF));
        assert_eq!(poly_word_to_bigint(r).unwrap(), BigInt::from(0xFu8));
        // gcd of two boxed multiples: gcd(2^65, 3*2^65) == 2^65
        let g1 = bigint_to_poly_word(&mut c, &(BigInt::from(1u8) << 65u32));
        let g2 = bigint_to_poly_word(&mut c, &(BigInt::from(3u8) * (BigInt::from(1u8) << 65u32)));
        let g = poly_gcd_arbitrary(&mut c, t(), g1, g2);
        assert_eq!(poly_word_to_bigint(g).unwrap(), BigInt::from(1u8) << 65u32);
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
    fn arb_shift_right_negative_is_arithmetic() {
        // `IntInf.~>>` is an ARITHMETIC (floor) shift: -40 ~>> 3 = -5, not a huge
        // positive. Regression for the logical-shift-on-negatives bug.
        let r = poly_shift_right_arbitrary(
            &mut ctx(),
            t(),
            PolyWord::tagged(-40),
            PolyWord::tagged(3),
        );
        assert_eq!(r.untag(), -5);
        // floor rounding toward -inf: -1 ~>> 1 = -1 (not 0).
        let r = poly_shift_right_arbitrary(&mut ctx(), t(), PolyWord::tagged(-1), PolyWord::tagged(1));
        assert_eq!(r.untag(), -1);
    }

    #[test]
    fn arb_shift_left_negative_preserves_sign() {
        // -5 << 3 = -40.
        let r = poly_shift_left_arbitrary(
            &mut ctx(),
            t(),
            PolyWord::tagged(-5),
            PolyWord::tagged(3),
        );
        assert_eq!(r.untag(), -40);
    }

    #[test]
    fn arb_shift_left_boxes_large_result() {
        // 1 << 70 doesn't fit in a tagged int — must box (old tagged-only path
        // returned 0). Needs an alloc space.
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);
        let mut c = RtsContext { alloc_space: Some(&mut space), raised_exception: None, rts: None };
        let r = poly_shift_left_arbitrary(&mut c, t(), PolyWord::tagged(1), PolyWord::tagged(70));
        assert!(r.is_data_ptr(), "1<<70 should be boxed");
        let bi = poly_word_to_bigint(r).expect("readable bignum");
        assert_eq!(bi, BigInt::from(1u128 << 70));
        // round-trip back down: (1<<70) ~>> 70 = 1.
        let back = poly_shift_right_arbitrary(&mut c, t(), r, PolyWord::tagged(70));
        assert_eq!(back.untag(), 1);
    }

    #[test]
    fn get_low_order_negates_negative_boxed() {
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);
        let mut c = RtsContext { alloc_space: Some(&mut space), raised_exception: None, rts: None };
        // -(2^64 + 7): magnitude needs >64 bits so it boxes; negative-flagged.
        let n = -(BigInt::from(1u128 << 64) + BigInt::from(7u8));
        let boxed = bigint_to_poly_word(&mut c, &n);
        assert!(boxed.is_data_ptr(), "value should box");
        let res = poly_get_low_order_as_large_word(&mut c, t(), boxed);
        // low limb of magnitude (2^64+7) is 7; two's-complement-negated = -7.
        let low = unsafe { (*res.as_ptr::<usize>()) };
        assert_eq!(low, 0usize.wrapping_sub(7), "negative boxed low word must be negated");
    }

    #[test]
    fn next_after_walks_one_ulp() {
        let up = next_after(1.0, 2.0);
        assert!(up > 1.0 && up == f64::from_bits(1.0f64.to_bits() + 1));
        let down = next_after(1.0, 0.0);
        assert!(down < 1.0 && down == f64::from_bits(1.0f64.to_bits() - 1));
        assert!(next_after(0.0, -1.0) < 0.0); // smallest negative subnormal
        assert!(next_after(5.0, 5.0) == 5.0); // equal -> y
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

    #[test]
    fn arb_mult_no_overflow_stays_tagged() {
        let mut ctx = ctx();
        // Both small — should stay tagged.
        let r = poly_multiply_arbitrary(
            &mut ctx, t(), PolyWord::tagged(123), PolyWord::tagged(456),
        );
        assert!(r.is_tagged());
        assert_eq!(r.untag(), 123 * 456);
    }

    #[test]
    fn arb_mult_exactly_at_max_tagged_overflows() {
        // 2^31 * 2^31 = 2^62 which is MAX_TAGGED + 1 — should box.
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);
        let mut ctx = RtsContext {
            alloc_space: Some(&mut space),
            raised_exception: None,
            rts: None,
        };
        let r = poly_multiply_arbitrary(
            &mut ctx, t(), PolyWord::tagged(1 << 31), PolyWord::tagged(1 << 31),
        );
        assert!(r.is_data_ptr(), "2^62 should be boxed (MAX_TAGGED = 2^62-1)");
        let bi = poly_word_to_bigint(r).expect("readable bignum");
        assert_eq!(bi, BigInt::from(1u64 << 62), "wrong product");
    }

    #[test]
    fn arb_mult_negative_overflow_round_trips() {
        // -2^31 * 2^32 = -2^63
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);
        let mut ctx = RtsContext {
            alloc_space: Some(&mut space),
            raised_exception: None,
            rts: None,
        };
        let a = PolyWord::tagged(-(1 << 31));
        let b = PolyWord::tagged(1 << 32);
        let r = poly_multiply_arbitrary(&mut ctx, t(), a, b);
        assert!(r.is_data_ptr(), "expected boxed");
        let bi = poly_word_to_bigint(r).expect("readable");
        let expected = -BigInt::from(1u64 << 63);
        assert_eq!(bi, expected);
    }

    /// Multiply two near-max-tagged values; result overflows i64
    /// and should come back as a boxed BigInt. Verify round-trip.
    #[test]
    fn arb_mult_overflow_round_trips_via_bigint() {
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);
        let mut ctx = RtsContext {
            alloc_space: Some(&mut space),
            raised_exception: None,
            rts: None,
        };
        // 2^31 * 2^32 = 2^63 which exceeds MAX_TAGGED.
        let a = PolyWord::tagged(1 << 31);
        let b = PolyWord::tagged(1 << 32);
        let r = poly_multiply_arbitrary(&mut ctx, PolyWord::tagged(0), a, b);
        assert!(r.is_data_ptr(), "expected boxed bignum, got {r:?}");
        // Read it back via our converter.
        let bi = poly_word_to_bigint(r).expect("readable bignum");
        assert_eq!(bi, BigInt::from(1u64 << 63), "wrong product");
    }
}
