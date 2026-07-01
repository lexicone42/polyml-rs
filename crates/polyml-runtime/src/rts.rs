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
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

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
    /// Per-thread bootstrap tail-call slot. This is PER-THREAD state
    /// (the `PolyEndBootstrapMode` argument), NOT a process-global static
    /// (it used to be one — see the per-thread hoist). The dispatch site
    /// (`Interpreter::rts_call`) seeds it from the owning interpreter's
    /// `bootstrap_tail_call` field before calling an RTS function and reads
    /// it back into that field afterwards. `PolyEndBootstrapMode` writes the
    /// `unit -> 'a` function closure here; when non-`ZERO` on RTS return the
    /// interpreter tail-calls it. A second thread therefore cannot clobber
    /// another thread's pending bootstrap tail call. Defaults to `ZERO`
    /// (= "no pending tail call") at every construction site that is not the
    /// real interpreter dispatch (tests / numeric helper contexts), matching
    /// the old static's never-set behaviour on those paths.
    pub bootstrap_tail_call: PolyWord,
    /// UNTRUSTED-MODE typed-deref validator (task #96). `None` = trusted
    /// (the default at every construction site): the RTS code-constant
    /// family follows pointers on the exact current fast path. `Some` (set
    /// ONLY by the interpreter's `rts_call` when the interpreter is in
    /// untrusted mode) carries the live image-space bounds + the live alloc
    /// range so a code-constant write/read can validate the resolved code
    /// object against real spaces BEFORE the deref — turning the R1 OOB
    /// write (and its read siblings) into a clean no-op on a forged image.
    pub safe_spaces: Option<RtsSafeSpaces>,
}

/// A snapshot of the live spaces handed to an RTS function in untrusted
/// mode so the code-constant family can validate a resolved code-object
/// pointer. A small, copyable bundle (≤ 4 ranges). Built by the
/// interpreter's `rts_call` from its `safe_deref::SafeSpaces` + live alloc
/// range; `None` (trusted) at every other construction site.
#[derive(Clone)]
pub struct RtsSafeSpaces {
    /// Half-open `[start, end)` ranges over `PolyWord` slots (as `usize`):
    /// the image immutable/mutable/code spaces plus the live alloc space.
    pub ranges: Vec<(usize, usize)>,
}

impl RtsSafeSpaces {
    /// Whether `p` lies inside a live space AND there is room for a length
    /// word at `p.sub(1)` (i.e. `p` is strictly above a space start).
    #[must_use]
    pub fn contains_with_header(&self, p: *const PolyWord) -> bool {
        let a = p as usize;
        self.ranges.iter().any(|&(start, end)| a > start && a < end)
    }

    /// The exclusive end address (`usize`) of the live space containing `p`,
    /// if any. Used to bound an object's body length against its containing
    /// space (header sanity) — e.g. the export graph walk clamps a code/word
    /// object's word count so a forged length word cannot drive a read past
    /// the space end.
    #[must_use]
    pub fn space_end_of(&self, p: *const PolyWord) -> Option<usize> {
        let a = p as usize;
        self.ranges
            .iter()
            .find(|&&(start, end)| a > start && a < end)
            .map(|&(_, end)| end)
    }

    /// UNTRUSTED header-fit validation of an image-controlled RTS argument `w`
    /// (the strong sibling of [`Self::contains_with_header`], mirroring
    /// `safe_deref::SafeSpaces::validate_obj`): confirm `w` is an aligned,
    /// in-space pointer with room for its length word, READ that length word,
    /// and verify the WHOLE object `[p, p + n_words)` fits within its
    /// containing space. Returns the validated `(body_ptr, n_words)` so a
    /// multi-word / variable-length reader can bound each access; `None` for a
    /// tagged / wild / misaligned arg or a forged length word that over-claims
    /// the object (runs past the space end).
    ///
    /// This is what makes the multi-word RTS readers robust DIRECTLY:
    /// `contains_with_header` alone only proves a single word at `p` is
    /// readable, leaning on the implicit loader-slack invariant for the rest;
    /// this proves the header-declared object actually fits.
    ///
    /// Takes a [`PolyWord`] (not a raw pointer) so the only deref is of a
    /// pointer derived + bounds-checked locally — never the caller's argument.
    #[must_use]
    pub fn validate_obj_fit(&self, w: PolyWord) -> Option<(*const PolyWord, usize)> {
        if !w.is_data_ptr() {
            return None;
        }
        let wsz = std::mem::size_of::<PolyWord>();
        let a = w.0;
        // Alignment: a misaligned pointer makes the length-word read UB.
        if a & (wsz - 1) != 0 {
            return None;
        }
        let p = w.as_ptr::<PolyWord>();
        // Find the containing space and require room for the length word at
        // `p.sub(1)`: `a` must be at least one full word above the space start
        // (independent of the start's own alignment, so this stays sound even
        // for a hypothetical unaligned space base).
        let &(_start, end) = self
            .ranges
            .iter()
            .find(|&&(start, end)| a >= start.saturating_add(wsz) && a < end)?;
        // SAFETY: `a >= start + wsz` and `a` is aligned, so `p.sub(1)` is an
        // aligned, readable length-word slot inside `[start, end)`.
        let lw = unsafe { *p.sub(1) };
        let n_words = crate::length_word::length_of(lw);
        // The body occupies `n_words` words from `p`; it must fit `[p, end)`.
        let avail_bytes = end - a; // a < end, so > 0
        let need_bytes = n_words.checked_mul(wsz)?;
        if need_bytes <= avail_bytes {
            Some((p, n_words))
        } else {
            None
        }
    }
}

/// A VALIDATED RTS-argument object handle (the header-fit twin of
/// `safe_deref::ValidObj`).
///
/// Carries the object body pointer plus the verified body word count, so a
/// multi-word / variable-length reader can bound each access (`word_in_bounds`
/// / `clamp_body_words`) BEFORE the deref.
///
/// In TRUSTED mode `n_words == usize::MAX` — the "no bound" sentinel: every
/// bound check passes and the reader trusts its own length read, EXACTLY the
/// legacy fast path (byte-identical). A real length word never reaches
/// `usize::MAX` (the length field is only the low ~56 bits), so the sentinel
/// can never collide with a genuine count.
#[derive(Clone, Copy)]
pub struct RtsValidObj {
    /// The (validated, in TRUSTED mode merely `is_data_ptr`) body pointer.
    pub ptr: *const PolyWord,
    /// Validated body word count (UNTRUSTED), or `usize::MAX` (TRUSTED =
    /// unbounded, byte-identical legacy path).
    pub n_words: usize,
}

impl RtsValidObj {
    /// Body word index `idx` is in-bounds. TRUSTED (`n_words == MAX`): always
    /// true (the legacy reader trusted its own length read).
    #[inline]
    #[must_use]
    pub fn word_in_bounds(&self, idx: usize) -> bool {
        idx < self.n_words
    }

    /// Clamp a length-word-derived body word count to the validated bound.
    /// TRUSTED (`n_words == MAX`): returns `claimed` unchanged — byte-identical
    /// (and in UNTRUSTED mode `claimed == n_words` already, since the gate read
    /// the same length word, so this is a defensive no-op that documents the
    /// bound the gate enforced).
    #[inline]
    #[must_use]
    pub fn clamp_body_words(&self, claimed: usize) -> usize {
        claimed.min(self.n_words)
    }
}

/// THE misuse-resistant gate for the FIRST deref of an image-controlled RTS
/// argument (task #96, HOLE 5). Every RTS reader free-function that derefs a
/// `PolyWord` parameter (`read_real_word`, `poly_word_to_bigint`,
/// `poly_string_to_rust`, the IO/array readers, `reset_mutex`, the byte-vec
/// copier, …) MUST obtain its body pointer through this ONE helper instead of
/// open-coding `w.is_data_ptr()` + `w.as_ptr()`. That makes the hole
/// un-reintroducible: a future reader that forgets the space check simply
/// cannot get a pointer without going through here.
///
/// Returns `Some(body_ptr)` ONLY when it is safe to deref `w` (its word0 and
/// its length word at `p.sub(1)`):
///   - TRUSTED (`spaces == None`, the default at every non-untrusted dispatch
///     site): exactly the legacy `w.is_data_ptr()` gate — byte-identical, no
///     extra cost. (Word-alignment was implied by the legacy code's deref; we
///     do not add an alignment reject here so the trusted result set is the
///     same as before.)
///   - UNTRUSTED (`spaces == Some`, set only by the interpreter's `rts_call`
///     when in untrusted mode): ALSO requires space-membership with header
///     room (`contains_with_header`), so a wild / type-confused arg yields
///     `None` and the reader falls into its existing non-pointer branch (a
///     clean tagged(0) / EOF / empty-string result), never an OOB deref.
#[inline]
#[must_use]
pub fn safe_rts_arg_ptr(spaces: Option<&RtsSafeSpaces>, w: PolyWord) -> Option<*const PolyWord> {
    if !w.is_data_ptr() {
        return None;
    }
    let p = w.as_ptr::<PolyWord>();
    match spaces {
        // Trusted: legacy behaviour (is_data_ptr only) — byte-identical.
        None => Some(p),
        // Untrusted: gate the first deref on space-membership + header room.
        Some(s) if s.contains_with_header(p) => Some(p),
        Some(_) => None,
    }
}

/// THE header-fit gate for the FIRST deref of an image-controlled RTS argument
/// whose body is then read at MULTIPLE word offsets or for a VARIABLE length.
///
/// Covers `write_array` / `read_array_from_stream`'s 3-tuple,
/// `poly_word_to_bigint`'s limbs, `poly_string_to_rust`'s chars, and
/// `poly_copy_byte_vec_to_closure`'s body. STRONGER than [`safe_rts_arg_ptr`]:
/// it returns a [`RtsValidObj`] carrying the validated body word count so the
/// reader can bound each access.
///
///   - TRUSTED (`spaces == None`, the default): exactly the legacy
///     `is_data_ptr` fast path, `n_words == usize::MAX` (unbounded) — NO header
///     read, NO check, byte-identical. (A reader that uses the handle's bound
///     helpers sees every check pass and runs its existing length-word logic.)
///   - UNTRUSTED (`spaces == Some`): ALSO reads the length word and verifies
///     the WHOLE object `[p, p + n_words)` fits its space (via
///     `RtsSafeSpaces::validate_obj_fit`), returning the validated `n_words`. A
///     wild / misaligned arg or a forged over-claiming length word yields
///     `None`, and the reader falls into its existing non-pointer branch (a
///     clean tagged(0) / EOF / empty / None result) — never an OOB deref.
///
/// Single-word readers (`read_real_word`, the wrapped-fd `*strm_p` reads, …)
/// keep using [`safe_rts_arg_ptr`]: their one in-space word at `p` is already
/// covered by `contains_with_header`.
#[inline]
#[must_use]
pub fn safe_rts_arg_obj(spaces: Option<&RtsSafeSpaces>, w: PolyWord) -> Option<RtsValidObj> {
    match spaces {
        // Trusted: legacy behaviour (is_data_ptr only), unbounded — the bound
        // helpers all pass, so the reader is byte-identical to before.
        None => {
            if !w.is_data_ptr() {
                return None;
            }
            Some(RtsValidObj {
                ptr: w.as_ptr::<PolyWord>(),
                n_words: usize::MAX,
            })
        }
        // Untrusted: space-membership + header-fit; carry the validated count.
        Some(s) => s
            .validate_obj_fit(w)
            .map(|(ptr, n_words)| RtsValidObj { ptr, n_words }),
    }
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

    /// Table preloaded with the built-in implementations. Everything the
    /// bootstrap / compiler / HOL4 / Isabelle workloads exercise is
    /// implemented faithfully — but coverage is *partial*, and NB: a
    /// substantial minority of registered entries are constant STUBS
    /// (the `Posix` structure, sockets, the C FFI, signal delivery,
    /// SaveState, `Date` local-time, ...) because the basis probes them
    /// unconditionally at startup; they return defaults instead of
    /// raising (see the per-entry comments and README §"What's not done
    /// yet"). Names not registered at all are left unpatched by the
    /// loader, and the interpreter traps with a catchable exception when
    /// bytecode calls them.
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
    t.register(
        "PolyIsBigEndian",
        RtsFn::Arity1(|_, _| poly_is_big_endian_inner()),
    );
    // These are called as `rtsCallFast0` from LibrarySupport.sml.
    // All return reasonable defaults for our environment.
    t.register(
        "PolyGetMaxAllocationSize",
        RtsFn::Arity0(|_| {
            // Max object length: 1 << 24 words = plenty for any sensible alloc.
            PolyWord::tagged(1 << 24)
        }),
    );
    t.register(
        "PolyGetMaxStringSize",
        RtsFn::Arity0(|_| {
            // Same upper bound, in bytes.
            PolyWord::tagged((1isize << 24) * 8)
        }),
    );
    t.register("PolyGetOSType", RtsFn::Arity0(|_| PolyWord::tagged(0))); // 0 = Unix
    t.register(
        "PolyGetPolyVersionNumber",
        RtsFn::Arity0(|_| PolyWord::tagged(592)),
    );
    // Compact 32-in-64 mode unit size; returns 0 in native 64-bit mode.
    t.register("PolyGetC32UnitSize", RtsFn::Arity0(|_| PolyWord::tagged(0)));
    // Stubs for PolyML.make compiling CodeArray.ML — these mutate code
    // objects in the runtime's code area. Returns unit / tagged 0.
    t.register("PolySetCodeByte", RtsFn::Arity3(poly_set_code_byte));
    t.register("PolyGetCodeConstant", RtsFn::Arity3(poly_get_code_constant));
    t.register(
        "PolyChunkSizeArbitrary",
        RtsFn::Arity0(|_| PolyWord::tagged(64)),
    );
    t.register(
        "PolyGetUserStatsCount",
        RtsFn::Arity0(|_| PolyWord::tagged(0)),
    );
    t.register(
        "PolyThreadNumPhysicalProcessors",
        RtsFn::Arity0(|_| PolyWord::tagged(1)),
    );
    t.register(
        "PolyThreadNumProcessors",
        RtsFn::Arity0(|_| PolyWord::tagged(1)),
    );
    // Real / float RTS stubs (basis layer uses these).
    t.register(
        "PolyGetRoundingMode",
        RtsFn::Arity1(|_, _| PolyWord::tagged(0)),
    ); // TO_NEAREST
    // Setting TO_NEAREST (0) matches the hardware default and is honored;
    // any other mode would be silently ignored (wrong rounding in every
    // subsequent FP op), so it raises instead.
    t.register(
        "PolySetRoundingMode",
        RtsFn::Arity1(|ctx, mode| {
            if mode == PolyWord::tagged(0) {
                PolyWord::tagged(0)
            } else {
                fail_unimpl(ctx, "IEEEReal.setRoundingMode (non-default mode)")
            }
        }),
    );
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
    t.register(
        "PolyRealSqrt",
        RtsFn::Arity1(|c, x| box_real(c, read_real_word(c.safe_spaces.as_ref(), x).sqrt())),
    );
    t.register(
        "PolyRealSin",
        RtsFn::Arity1(|c, x| box_real(c, read_real_word(c.safe_spaces.as_ref(), x).sin())),
    );
    t.register(
        "PolyRealCos",
        RtsFn::Arity1(|c, x| box_real(c, read_real_word(c.safe_spaces.as_ref(), x).cos())),
    );
    t.register(
        "PolyRealTan",
        RtsFn::Arity1(|c, x| box_real(c, read_real_word(c.safe_spaces.as_ref(), x).tan())),
    );
    t.register(
        "PolyRealArcSin",
        RtsFn::Arity1(|c, x| box_real(c, read_real_word(c.safe_spaces.as_ref(), x).asin())),
    );
    t.register(
        "PolyRealArcCos",
        RtsFn::Arity1(|c, x| box_real(c, read_real_word(c.safe_spaces.as_ref(), x).acos())),
    );
    t.register(
        "PolyRealArctan",
        RtsFn::Arity1(|c, x| box_real(c, read_real_word(c.safe_spaces.as_ref(), x).atan())),
    );
    t.register(
        "PolyRealSinh",
        RtsFn::Arity1(|c, x| box_real(c, read_real_word(c.safe_spaces.as_ref(), x).sinh())),
    );
    t.register(
        "PolyRealCosh",
        RtsFn::Arity1(|c, x| box_real(c, read_real_word(c.safe_spaces.as_ref(), x).cosh())),
    );
    t.register(
        "PolyRealTanh",
        RtsFn::Arity1(|c, x| box_real(c, read_real_word(c.safe_spaces.as_ref(), x).tanh())),
    );
    t.register(
        "PolyRealExp",
        RtsFn::Arity1(|c, x| box_real(c, read_real_word(c.safe_spaces.as_ref(), x).exp())),
    );
    t.register(
        "PolyRealLog",
        RtsFn::Arity1(|c, x| box_real(c, read_real_word(c.safe_spaces.as_ref(), x).ln())),
    );
    t.register(
        "PolyRealLog10",
        RtsFn::Arity1(|c, x| box_real(c, read_real_word(c.safe_spaces.as_ref(), x).log10())),
    );
    // floor/ceil/trunc obvious; round replicates upstream PolyRealRound's exact
    // fmod/floor(x+0.5) algorithm (reals.cpp:350-359) — round-half-to-even
    // MAGNITUDE but +0.0 (not -0.0) for arg in (-0.5, 0]. `round_ties_even`
    // would diverge on sign-of-zero; see poly_real_round_f64.
    t.register(
        "PolyRealFloor",
        RtsFn::Arity1(|c, x| box_real(c, read_real_word(c.safe_spaces.as_ref(), x).floor())),
    );
    t.register(
        "PolyRealCeil",
        RtsFn::Arity1(|c, x| box_real(c, read_real_word(c.safe_spaces.as_ref(), x).ceil())),
    );
    t.register(
        "PolyRealRound",
        RtsFn::Arity1(|c, x| {
            box_real(
                c,
                poly_real_round_f64(read_real_word(c.safe_spaces.as_ref(), x)),
            )
        }),
    );
    t.register(
        "PolyRealTrunc",
        RtsFn::Arity1(|c, x| box_real(c, read_real_word(c.safe_spaces.as_ref(), x).trunc())),
    );
    // FLOAT (Real32) unary math (rtsCallFastF_F: Real32 -> Real32, no threadId).
    // On 64-bit, Real32 args/results are TAGGED floats (f32 bits in the high 32,
    // low bit = tag). The typed fast-call path (call_fast_f_to_f, mod.rs) passes
    // the tagged arg directly and reads our result as a BOXED f64, then narrows
    // `as f32` and re-tags — so we unpack via read_f32_tagged, compute in f32, and
    // return the f32 widened to a boxed f64 via box_f32_tagged. Upstream
    // reals.cpp:445-586 (sqrtf/sinf/...; FTrunc = trunc toward zero; FRound =
    // round-half-to-even). Registration order is unchanged from the old stub array
    // so baked RTS dispatch tokens in warm checkpoints stay valid.
    t.register(
        "PolyRealFSqrt",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, read_f32_tagged(x).sqrt())),
    );
    t.register(
        "PolyRealFSin",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, read_f32_tagged(x).sin())),
    );
    t.register(
        "PolyRealFCos",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, read_f32_tagged(x).cos())),
    );
    t.register(
        "PolyRealFTan",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, read_f32_tagged(x).tan())),
    );
    t.register(
        "PolyRealFArcSin",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, read_f32_tagged(x).asin())),
    );
    t.register(
        "PolyRealFArcCos",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, read_f32_tagged(x).acos())),
    );
    t.register(
        "PolyRealFArctan",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, read_f32_tagged(x).atan())),
    );
    t.register(
        "PolyRealFSinh",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, read_f32_tagged(x).sinh())),
    );
    t.register(
        "PolyRealFCosh",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, read_f32_tagged(x).cosh())),
    );
    t.register(
        "PolyRealFTanh",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, read_f32_tagged(x).tanh())),
    );
    t.register(
        "PolyRealFExp",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, read_f32_tagged(x).exp())),
    );
    t.register(
        "PolyRealFLog",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, read_f32_tagged(x).ln())),
    );
    t.register(
        "PolyRealFLog10",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, read_f32_tagged(x).log10())),
    );
    t.register(
        "PolyRealFFloor",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, read_f32_tagged(x).floor())),
    );
    t.register(
        "PolyRealFCeil",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, read_f32_tagged(x).ceil())),
    );
    t.register(
        "PolyRealFRound",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, poly_real_round_f32(read_f32_tagged(x)))),
    );
    t.register(
        "PolyRealFTrunc",
        RtsFn::Arity1(|c, x| box_f32_tagged(c, read_f32_tagged(x).trunc())),
    );
    // DOUBLE binary math (rtsCallFastRR_R: real*real -> real, no threadId).
    t.register(
        "PolyRealAtan2",
        RtsFn::Arity2(|c, y, x| {
            box_real(
                c,
                read_real_word(c.safe_spaces.as_ref(), y)
                    .atan2(read_real_word(c.safe_spaces.as_ref(), x)),
            )
        }),
    );
    t.register(
        "PolyRealPow",
        RtsFn::Arity2(|c, b, e| {
            box_real(
                c,
                read_real_word(c.safe_spaces.as_ref(), b)
                    .powf(read_real_word(c.safe_spaces.as_ref(), e)),
            )
        }),
    );
    t.register(
        "PolyRealCopySign",
        RtsFn::Arity2(|c, a, b| {
            box_real(
                c,
                read_real_word(c.safe_spaces.as_ref(), a)
                    .copysign(read_real_word(c.safe_spaces.as_ref(), b)),
            )
        }),
    );
    t.register(
        "PolyRealRem",
        RtsFn::Arity2(|c, a, b| {
            box_real(
                c,
                read_real_word(c.safe_spaces.as_ref(), a)
                    % read_real_word(c.safe_spaces.as_ref(), b),
            )
        }),
    );
    // Real.nextAfter (Real.sml:480). Registered FIRST here to preserve the
    // dispatch-token ordinal it had as the head of the old stub array.
    t.register(
        "PolyRealNextAfter",
        RtsFn::Arity2(|c, a, b| {
            box_real(
                c,
                next_after(
                    read_real_word(c.safe_spaces.as_ref(), a),
                    read_real_word(c.safe_spaces.as_ref(), b),
                ),
            )
        }),
    );
    // FLOAT (Real32) binary math (rtsCallFastFF_F: Real32*Real32 -> Real32, no
    // threadId). Same tagged-f32 in / boxed-f64 out convention as the unary
    // F-variants above. Registration order unchanged so baked tokens stay valid.
    // Upstream reals.cpp:531-600.
    t.register(
        "PolyRealFAtan2",
        RtsFn::Arity2(|c, y, x| box_f32_tagged(c, read_f32_tagged(y).atan2(read_f32_tagged(x)))),
    );
    t.register(
        "PolyRealFCopySign",
        RtsFn::Arity2(|c, a, b| box_f32_tagged(c, read_f32_tagged(a).copysign(read_f32_tagged(b)))),
    );
    t.register(
        "PolyRealFNextAfter",
        RtsFn::Arity2(|c, a, b| {
            box_f32_tagged(c, next_after_f32(read_f32_tagged(a), read_f32_tagged(b)))
        }),
    );
    t.register(
        "PolyRealFPow",
        RtsFn::Arity2(|c, b, e| {
            box_f32_tagged(c, real_f_pow(read_f32_tagged(b), read_f32_tagged(e)))
        }),
    );
    t.register(
        "PolyRealFRem",
        RtsFn::Arity2(|c, a, b| box_f32_tagged(c, read_f32_tagged(a) % read_f32_tagged(b))),
    );
    // Real.fromManAndExp = ldexp(man, exp) = man * 2^exp (Real.sml:265,
    // rtsCallFastRI_R: real * int -> real). exp clamped to a range beyond which
    // the result is already inf/0 in f64.
    t.register(
        "PolyRealLdexp",
        RtsFn::Arity2(|c, m, e| {
            #[allow(clippy::cast_possible_truncation)]
            let exp = e.untag().clamp(-2000, 2000) as i32;
            box_real(
                c,
                read_real_word(c.safe_spaces.as_ref(), m) * 2f64.powi(exp),
            )
        }),
    );
    // Real.fromLargeInt (and, under arbitrary-precision int, Real.fromInt): convert
    // an arbitrary-precision int (tagged or boxed bignum) to a boxed double.
    // reals.cpp:240 PolyFloatArbitraryPrecision(arg) -> double. Fast call, ONE arg
    // (the old Arity2 stub was both wrong-arity and returned tagged(0), which made
    // `val zero/one/four = fromInt …` in basis/Real.sml produce fake reals and SEGV
    // the load under arbitrary int).
    t.register(
        "PolyFloatArbitraryPrecision",
        RtsFn::Arity1(|c, x| {
            use num_traits::ToPrimitive;
            box_real(
                c,
                poly_word_to_bigint(c.safe_spaces.as_ref(), x)
                    .and_then(|n| n.to_f64())
                    .unwrap_or(0.0),
            )
        }),
    );
    // Timing / system. TICKS_PER_MICROSECOND==1 on Unix (timing.cpp:149).
    t.register(
        "PolyTimingTicksPerMicroSec",
        RtsFn::Arity1(|_, _| PolyWord::tagged(1)),
    );
    // gettimeofday -> microseconds since the Unix epoch (timing.cpp:205,
    // Make_arb_from_pair_scaled(...,1000000)). Time.sml:184 getNow.
    t.register(
        "PolyTimingGetNow",
        RtsFn::Arity1(|c, _| {
            #[allow(clippy::cast_possible_wrap)]
            let us = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_micros() as i128)
                .unwrap_or(0);
            int_to_poly_word(c, us)
        }),
    );
    t.register(
        "PolyTimingBaseYear",
        RtsFn::Arity1(|_, _| PolyWord::tagged(1970)),
    );
    // REAL strftime for Date.fmt (timing.cpp:399-460; upstream's spelling).
    t.register(
        "PolyTimingConvertDateStuct",
        RtsFn::Arity2(poly_timing_convert_date_struct),
    );
    // REAL local-time conversions. NB the old tagged(0) "we are UTC" stubs
    // were also registered at the WRONG ARITY (Arity1 for rtsCallFull1 call
    // sites, which pass threadId + arg = Arity2) — a latent stack
    // corruption on any Date.fromTimeLocal/toString call.
    t.register(
        "PolyTimingLocalOffset",
        RtsFn::Arity2(poly_timing_local_offset),
    );
    t.register(
        "PolyTimingSummerApplies",
        RtsFn::Arity2(poly_timing_summer_applies),
    );
    t.register(
        "PolyTimingYearOffset",
        RtsFn::Arity1(|_, _| PolyWord::tagged(0)),
    );
    // CPU time used by this process, in microseconds (getrusage(RUSAGE_SELF);
    // timing.cpp:452/483 ru_utime / ru_stime). LargeInt.int, Arity1.
    t.register(
        "PolyTimingGetUser",
        RtsFn::Arity1(|c, _| int_to_poly_word(c, getrusage_micros(RUSAGE_SELF, true))),
    );
    t.register(
        "PolyTimingGetSystem",
        RtsFn::Arity1(|c, _| int_to_poly_word(c, getrusage_micros(RUSAGE_SELF, false))),
    );
    // Real (wall-clock) time since process start, in microseconds
    // (timing.cpp:534, gettimeofday - startTime). Baseline captured on
    // first call. Monotonic — important for the SML Timer/scheduler path.
    t.register(
        "PolyTimingGetReal",
        RtsFn::Arity1(|c, _| {
            use std::sync::OnceLock;
            static START: OnceLock<std::time::Instant> = OnceLock::new();
            let base = START.get_or_init(std::time::Instant::now);
            #[allow(clippy::cast_possible_wrap)]
            let us = base.elapsed().as_micros() as i128;
            int_to_poly_word(c, us)
        }),
    );
    t.register(
        "PolyTimingGetGCUser",
        RtsFn::Arity1(|_, _| PolyWord::tagged(0)),
    );
    t.register(
        "PolyTimingGetGCSystem",
        RtsFn::Arity1(|_, _| PolyWord::tagged(0)),
    );
    t.register(
        "PolyTimingGetChildUser",
        RtsFn::Arity1(|_, _| PolyWord::tagged(0)),
    );
    t.register(
        "PolyTimingGetChildSystem",
        RtsFn::Arity1(|_, _| PolyWord::tagged(0)),
    );
    // Process / OS / Foreign stubs.
    t.register(
        "PolyGetProcessName",
        RtsFn::Arity1(|ctx, _| alloc_empty_string(ctx)),
    );
    t.register("PolyGetEnv", RtsFn::Arity2(poly_get_env));
    t.register(
        "PolyGetEnvironment",
        RtsFn::Arity1(|_, _| PolyWord::tagged(0)),
    );
    t.register("PolyFullGC", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register(
        "PolyGetLocalStats",
        RtsFn::Arity1(|_, _| PolyWord::tagged(0)),
    );
    t.register(
        "PolyShowHierarchy",
        RtsFn::Arity1(|_, _| PolyWord::tagged(0)),
    );
    t.register(
        "PolyShowLoadedModules",
        RtsFn::Arity1(|_, _| PolyWord::tagged(0)),
    );
    t.register("PolyExport", RtsFn::Arity3(poly_export));
    // Portable variant uses the same pexport text format as our regular
    // export — both go through the same snapshot path.
    t.register("PolyExportPortable", RtsFn::Arity3(poly_export));
    t.register(
        "PolyChDir",
        RtsFn::Arity2(|ctx, _, _| syserr_unimpl(ctx, "OS.FileSys.chDir")),
    );
    t.register(
        "PolyGetModuleDirectory",
        RtsFn::Arity1(|ctx, _| alloc_empty_string(ctx)),
    );
    // FFI library loading — de-fanged: a tagged(0) "handle" from these made
    // every downstream Foreign.* use silently operate on garbage.
    t.register(
        "PolyFFILoadExecutable",
        RtsFn::Arity1(|ctx, _| fail_unimpl(ctx, "Foreign: loadExecutable (no C FFI)")),
    );
    t.register(
        "PolyFFILoadLibrary",
        RtsFn::Arity2(|ctx, _, _| fail_unimpl(ctx, "Foreign: loadLibrary (no C FFI)")),
    );
    t.register(
        "PolyFFIUnloadLibrary",
        RtsFn::Arity1(|ctx, _| fail_unimpl(ctx, "Foreign: unloadLibrary (no C FFI)")),
    );
    t.register(
        "PolyFFIGetSymbolAddress",
        RtsFn::Arity2(|ctx, _, _| fail_unimpl(ctx, "Foreign: getSymbol (no C FFI)")),
    );
    t.register(
        "PolyFFIMalloc",
        RtsFn::Arity1(|ctx, _| fail_unimpl(ctx, "Foreign.Memory.malloc (no C FFI)")),
    );
    t.register(
        "PolyFFICreateExtData",
        RtsFn::Arity2(|ctx, _, _| fail_unimpl(ctx, "Foreign: createExtData (no C FFI)")),
    );
    t.register(
        "PolyFFICreateExtFn",
        RtsFn::Arity2(|ctx, _, _| fail_unimpl(ctx, "Foreign: createExtFn (no C FFI)")),
    );
    // Network entries. The list/table queries below are REAL (the basis
    // builds the AF_/SOCK_ tables from them at load time) and INADDR_ANY=0
    // is the genuinely correct "any" IPv4 address; the operational socket
    // calls are de-fanged to raise SysErr (sockets are unimplemented —
    // a tagged(0) "socket" faked successful connections).
    t.register(
        "PolyNetworkGetFamilyFromAddress",
        RtsFn::Arity1(|ctx, _| syserr_unimpl(ctx, "sockets (getFamilyFromAddress)")),
    );
    t.register(
        "PolyNetworkGetAddrList",
        RtsFn::Arity1(|_, _| poly_network_get_addr_list_inner()),
    );
    // Real: the basis exposes this as NetHostDB.getHostName; an empty
    // string here was a silent lie and the real call is trivial.
    t.register(
        "PolyNetworkGetHostName",
        RtsFn::Arity1(|ctx, _| {
            let mut buf = [0u8; 256];
            // SAFETY: buf is a valid writable buffer of buf.len() bytes.
            let r = unsafe { libc::gethostname(buf.as_mut_ptr().cast(), buf.len()) };
            if r == 0 {
                let len = buf.iter().position(|&b| b == 0).unwrap_or(buf.len());
                alloc_poly_string(ctx, &buf[..len])
            } else {
                syserr_unimpl(ctx, "gethostname")
            }
        }),
    );
    t.register(
        "PolyNetworkGetSockTypeList",
        RtsFn::Arity1(|_, _| poly_network_get_sock_type_list_inner()),
    );
    t.register(
        "PolyNetworkReturnIP4AddressAny",
        RtsFn::Arity1(|_, _| PolyWord::tagged(0)),
    );
    t.register(
        "PolyNetworkReturnIP6AddressAny",
        RtsFn::Arity1(|_, _| PolyWord::tagged(0)),
    );
    // Sockets (Wave 1b). The operational calls below are now REAL (blocking
    // libc sockets — see the `poly_network_*` bodies in `mod socket_rts` and
    // the module note on the deliberate blocking divergence).
    // Registration ORDER is unchanged
    // from the earlier stub loops (the `registration_order_fingerprint` test
    // pins it), so warm checkpoints stay valid; only the closures + arities
    // changed. NB the earlier stub loops had WRONG arities for many of these
    // (they were never called operationally, so it never surfaced) — each
    // real fn below is wired at the SML-derived arity (`rtsCallFullN` →
    // Arity-(N+1)). Entries left raising `syserr_unimpl` keep their previous
    // arity (they are never invoked, so it is immaterial): the IPv6 address
    // ops, DNS (getAddrInfo/getNameInfo), the proto/serv DB lookups, socket
    // options (get/setsockopt beyond SO_ERROR), and SO_LINGER.
    //
    // --- rtsCallFull1 group (→ Arity2) ---
    t.register(
        "PolyNetworkBytesAvailable",
        RtsFn::Arity2(socket_rts::poly_network_bytes_available),
    );
    t.register(
        "PolyNetworkCloseSocket",
        RtsFn::Arity2(socket_rts::poly_network_close_socket),
    );
    t.register(
        "PolyNetworkGetAtMark",
        RtsFn::Arity2(socket_rts::poly_network_get_at_mark),
    );
    t.register(
        "PolyNetworkGetSocketError",
        RtsFn::Arity2(socket_rts::poly_network_get_socket_error),
    );
    t.register(
        "PolyNetworkGetPeerName",
        RtsFn::Arity2(socket_rts::poly_network_get_peer_name),
    );
    t.register(
        "PolyNetworkGetSockName",
        RtsFn::Arity2(socket_rts::poly_network_get_sock_name),
    );
    // Still raising: SO_LINGER get (previous arity preserved).
    t.register(
        "PolyNetworkGetLinger",
        RtsFn::Arity1(|ctx, _| syserr_unimpl(ctx, "sockets (getLinger)")),
    );
    // --- second stub group (Accept..IP6AddressToString) ---
    t.register(
        "PolyNetworkAccept",
        RtsFn::Arity2(socket_rts::poly_network_accept),
    );
    t.register(
        "PolyNetworkBind",
        RtsFn::Arity3(socket_rts::poly_network_bind),
    );
    t.register(
        "PolyNetworkConnect",
        RtsFn::Arity3(socket_rts::poly_network_connect),
    );
    // Still raising: NetProtDB / NetServDB / IPv6 / DNS / options.
    t.register(
        "PolyNetworkGetProtByName",
        RtsFn::Arity2(|ctx, _, _| syserr_unimpl(ctx, "sockets (getProtByName)")),
    );
    t.register(
        "PolyNetworkGetProtByNo",
        RtsFn::Arity2(|ctx, _, _| syserr_unimpl(ctx, "sockets (getProtByNo)")),
    );
    t.register(
        "PolyNetworkListen",
        RtsFn::Arity3(socket_rts::poly_network_listen),
    );
    t.register(
        "PolyNetworkSetLinger",
        RtsFn::Arity2(|ctx, _, _| syserr_unimpl(ctx, "sockets (setLinger)")),
    );
    t.register(
        "PolyNetworkShutdown",
        RtsFn::Arity3(socket_rts::poly_network_shutdown),
    );
    t.register(
        "PolyNetworkGetServByName",
        RtsFn::Arity2(|ctx, _, _| syserr_unimpl(ctx, "sockets (getServByName)")),
    );
    t.register(
        "PolyNetworkGetServByPort",
        RtsFn::Arity2(|ctx, _, _| syserr_unimpl(ctx, "sockets (getServByPort)")),
    );
    t.register(
        "PolyNetworkCreateIP4Address",
        RtsFn::Arity3(socket_rts::poly_network_create_ip4_address),
    );
    t.register(
        "PolyNetworkCreateIP6Address",
        RtsFn::Arity2(|ctx, _, _| syserr_unimpl(ctx, "sockets (IPv6)")),
    );
    t.register(
        "PolyNetworkGetAddressAndPortFromIP4",
        RtsFn::Arity2(socket_rts::poly_network_get_address_and_port_from_ip4),
    );
    t.register(
        "PolyNetworkGetAddressAndPortFromIP6",
        RtsFn::Arity2(|ctx, _, _| syserr_unimpl(ctx, "sockets (IPv6)")),
    );
    t.register(
        "PolyNetworkGetAddrInfo",
        RtsFn::Arity2(|ctx, _, _| syserr_unimpl(ctx, "sockets (getAddrInfo)")),
    );
    t.register(
        "PolyNetworkGetNameInfo",
        RtsFn::Arity2(|ctx, _, _| syserr_unimpl(ctx, "sockets (getNameInfo)")),
    );
    t.register(
        "PolyNetworkCreateSocket",
        RtsFn::Arity4(socket_rts::poly_network_create_socket),
    );
    t.register(
        "PolyNetworkStringToIP6Address",
        RtsFn::Arity2(|ctx, _, _| syserr_unimpl(ctx, "sockets (IPv6)")),
    );
    t.register(
        "PolyNetworkIP6AddressToString",
        RtsFn::Arity2(|ctx, _, _| syserr_unimpl(ctx, "sockets (IPv6)")),
    );
    // --- third stub group (GetOption..CreateSocketPair) ---
    // Still raising: get/setsockopt beyond SO_ERROR (previous arity kept).
    t.register(
        "PolyNetworkGetOption",
        RtsFn::Arity3(|ctx, _, _, _| syserr_unimpl(ctx, "sockets (getOption)")),
    );
    t.register(
        "PolyNetworkSetOption",
        RtsFn::Arity3(|ctx, _, _, _| syserr_unimpl(ctx, "sockets (setOption)")),
    );
    t.register(
        "PolyNetworkReceive",
        RtsFn::Arity2(socket_rts::poly_network_receive),
    );
    t.register(
        "PolyNetworkSend",
        RtsFn::Arity2(socket_rts::poly_network_send),
    );
    t.register(
        "PolyNetworkGetServByNameAndProtocol",
        RtsFn::Arity3(|ctx, _, _, _| syserr_unimpl(ctx, "sockets (getServByNameAndProtocol)")),
    );
    t.register(
        "PolyNetworkGetServByPortAndProtocol",
        RtsFn::Arity3(|ctx, _, _, _| syserr_unimpl(ctx, "sockets (getServByPortAndProtocol)")),
    );
    t.register(
        "PolyNetworkCreateSocketPair",
        RtsFn::Arity4(socket_rts::poly_network_create_socket_pair),
    );
    // --- fourth stub group (ReceiveFrom, SendTo, Select) ---
    t.register(
        "PolyNetworkReceiveFrom",
        RtsFn::Arity2(socket_rts::poly_network_receive_from),
    );
    t.register(
        "PolyNetworkSendTo",
        RtsFn::Arity2(socket_rts::poly_network_send_to),
    );
    t.register(
        "PolyNetworkSelect",
        RtsFn::Arity3(socket_rts::poly_network_select),
    );
    // process_env return values.
    t.register(
        "PolyProcessEnvFailureValue",
        RtsFn::Arity1(|_, _| PolyWord::tagged(1)),
    );
    t.register(
        "PolyProcessEnvSuccessValue",
        RtsFn::Arity1(|_, _| PolyWord::tagged(0)),
    );
    // REAL strerror (was an empty-string stub, which made every SysErr
    // print without its reason).
    t.register(
        "PolyProcessEnvErrorMessage",
        RtsFn::Arity2(poly_process_env_error_message),
    );
    t.register(
        "PolyProcessEnvErrorFromString",
        RtsFn::Arity2(|_, _, _| PolyWord::tagged(0)),
    );
    // REAL (was the worst silent-lie in the table — returned tagged(0),
    // which is ALSO the registered success value, so it reported success
    // without running anything; then briefly de-fanged to raise).
    t.register(
        "PolyProcessEnvSystem",
        RtsFn::Arity2(poly_process_env_system),
    );
    t.register("PolyTerminate", RtsFn::Arity2(poly_terminate));
    t.register("PolyPollIODescriptors", RtsFn::Arity4(zero4));
    // rtsCallFull2 → threadId + 2 args → CALL_FAST_RTS3.
    t.register("PolySetSignalHandler", RtsFn::Arity3(zero3));
    // The entire Posix structure dispatches through this one entry. Code 4
    // (getConst) runs ~dozens of times at BASIS LOAD to build the errno /
    // conf constant tables (Posix.sml:599 `fun getConst i =
    // osSpecificGeneral (4, i)`) — it must keep returning tagged(0), the
    // value the working basis has always been built from, or Posix.sml
    // fails to elaborate and the self-bootstrap chain dies (measured).
    // Every OPERATIONAL request raises a catchable SysErr instead of the
    // old success-shaped 0.
    t.register(
        "PolyOSSpecificGeneral",
        RtsFn::Arity3(|ctx, _tid, code, _arg| {
            if code == PolyWord::tagged(4) {
                PolyWord::tagged(0)
            } else {
                syserr_unimpl(ctx, "Posix (OSSpecificGeneral)")
            }
        }),
    );
    // LOAD-BEARING stub: Posix.sml builds Posix.FileSys.stdin/stdout/stderr
    // at structure elaboration via three persistentFD calls (Posix.sml:1048)
    // — raising here kills the basis load / self-bootstrap chain (measured:
    // exactly 3 SysErr raises at `Use: basis/Posix.sml`). Keep the
    // historical tagged(0) the working basis has always been built from.
    t.register("PolyPosixCreatePersistentFD", RtsFn::Arity2(zero2));
    t.register(
        "PolyPosixSleep",
        RtsFn::Arity3(|ctx, _, _, _| syserr_unimpl(ctx, "Posix.Process.sleep")),
    );
    t.register(
        "PolyUnixExecute",
        RtsFn::Arity4(|ctx, _, _, _, _| syserr_unimpl(ctx, "Unix.execute")),
    );
    t.register(
        "PolyNetworkUnixPathToSockAddr",
        RtsFn::Arity2(|ctx, _, _| syserr_unimpl(ctx, "UnixSock")),
    );
    t.register(
        "PolyNetworkUnixSockAddrToPath",
        RtsFn::Arity2(|ctx, _, _| syserr_unimpl(ctx, "UnixSock")),
    );
    t.register("PolyGetRemoteStats", RtsFn::Arity2(zero2));
    t.register("PolySetUserStat", RtsFn::Arity3(zero3));
    t.register("PolyObjProfile", RtsFn::Arity2(zero2));
    t.register("PolyObjSize", RtsFn::Arity2(zero2));
    t.register("PolyShowSize", RtsFn::Arity2(zero2));
    t.register("PolyShareCommonData", RtsFn::Arity2(zero2));
    t.register("PolySpecificGeneral", RtsFn::Arity3(poly_specific_general));
    t.register("PolyProfiling", RtsFn::Arity2(zero2));
    // SaveState / module hierarchy — de-fanged: PolySaveState returning 0
    // meant `PolyML.SaveState.saveState f` "succeeded" while writing
    // nothing (data loss masquerading as success).
    t.register(
        "PolyLoadHierarchy",
        RtsFn::Arity2(|ctx, _, _| fail_unimpl(ctx, "PolyML.SaveState.loadHierarchy")),
    );
    t.register(
        "PolyLoadModule",
        RtsFn::Arity2(|ctx, _, _| fail_unimpl(ctx, "PolyML.loadModule")),
    );
    t.register(
        "PolyLoadState",
        RtsFn::Arity2(|ctx, _, _| fail_unimpl(ctx, "PolyML.SaveState.loadState")),
    );
    t.register(
        "PolyReleaseModule",
        RtsFn::Arity2(|ctx, _, _| fail_unimpl(ctx, "PolyML.releaseModule")),
    );
    t.register(
        "PolyRenameParent",
        RtsFn::Arity3(|ctx, _, _, _| fail_unimpl(ctx, "PolyML.SaveState.renameParent")),
    );
    t.register(
        "PolySaveState",
        RtsFn::Arity3(|ctx, _, _, _| fail_unimpl(ctx, "PolyML.SaveState.saveState")),
    );
    t.register(
        "PolyShowParent",
        RtsFn::Arity2(|ctx, _, _| alloc_empty_string(ctx)),
    );
    t.register(
        "PolyStoreModule",
        RtsFn::Arity3(|ctx, _, _, _| fail_unimpl(ctx, "PolyML.storeModule")),
    );
    t.register(
        "PolyGetModuleInfo",
        RtsFn::Arity2(|ctx, _, _| fail_unimpl(ctx, "PolyML module info")),
    );
    // Thread cond var stubs (no-ops in single-threaded mode).
    t.register("PolyThreadCondVarWait", RtsFn::Arity2(noop2));
    t.register("PolyThreadCondVarWaitUntil", RtsFn::Arity3(zero3));
    // FFI stubs (we don't support real FFI yet).
    t.register("PolyFFIGetError", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyFFISetError", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register("PolyFFIFree", RtsFn::Arity1(|_, _| PolyWord::tagged(0)));
    t.register(
        "PolyFFICallbackException",
        RtsFn::Arity1(|_, _| PolyWord::tagged(0)),
    );
    // Threading stubs.
    t.register(
        "PolyThreadIsActive",
        RtsFn::Arity1(|_, _| PolyWord::tagged(0)),
    );
    t.register(
        "PolyThreadKillThread",
        RtsFn::Arity1(|_, _| PolyWord::tagged(0)),
    );
    // Size queries (FFI). Use sizeof(T) values from the host.
    t.register(
        "PolySizeInt",
        RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<i32>())),
    );
    t.register(
        "PolySizeShort",
        RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<i16>())),
    );
    t.register(
        "PolySizeLong",
        RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<isize>())),
    );
    t.register(
        "PolySizeLonglong",
        RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<i64>())),
    );
    t.register(
        "PolySizeIntptr",
        RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<isize>())),
    );
    t.register(
        "PolySizeUintptr",
        RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<usize>())),
    );
    t.register(
        "PolySizePtrdiff",
        RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<isize>())),
    );
    t.register(
        "PolySizeSize",
        RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<usize>())),
    );
    t.register(
        "PolySizeSsize",
        RtsFn::Arity1(|_, _| size_word(std::mem::size_of::<isize>())),
    );
    // IntInf.log2 long path (IntInf.sml:55): floor(log2(|x|)) = highest set bit
    // index = bits()-1. Was a hard stub returning 0 (silent wrong answer for any
    // value >= 2^62). The SML wrapper only calls this for boxed (large) values.
    t.register(
        "PolyLog2Arbitrary",
        RtsFn::Arity1(
            |c, x| match poly_word_to_bigint(c.safe_spaces.as_ref(), x) {
                Some(n) if n.bits() > 0 =>
                {
                    #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
                    PolyWord::tagged((n.bits() - 1) as isize)
                }
                _ => PolyWord::tagged(0),
            },
        ),
    );
    t.register(
        "PolySizeDouble",
        RtsFn::Arity1(|_, _| poly_size_double_inner()),
    );
    t.register(
        "PolySizeFloat",
        RtsFn::Arity1(|_, _| poly_size_float_inner()),
    );
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
    t.register(
        "PolyThreadMaxStackSize",
        RtsFn::Arity1(poly_thread_max_stack_size),
    );
    t.register(
        "PolyGetCommandlineArguments",
        RtsFn::Arity1(poly_get_commandline_arguments),
    );
    t.register("PolyThreadKillSelf", RtsFn::Arity1(poly_thread_kill_self));
    t.register(
        "PolyThreadTestInterrupt",
        RtsFn::Arity1(poly_thread_test_interrupt),
    );
    // rtsCallFull1 (OS.sml:178) → CALL_FAST_RTS2 (threadId + syserr). Was
    // Arity1, which fed errorName the threadId and dropped the syserr.
    t.register(
        "PolyProcessEnvErrorName",
        RtsFn::Arity2(poly_process_env_error_name),
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
    t.register(
        "PolySubtractArbitrary",
        RtsFn::Arity3(poly_subtract_arbitrary),
    );
    t.register(
        "PolyMultiplyArbitrary",
        RtsFn::Arity3(poly_multiply_arbitrary),
    );
    t.register("PolyDivideArbitrary", RtsFn::Arity3(poly_divide_arbitrary));
    t.register(
        "PolyRemainderArbitrary",
        RtsFn::Arity3(poly_remainder_arbitrary),
    );
    t.register(
        "PolyQuotRemArbitraryPair",
        RtsFn::Arity3(poly_quot_rem_arbitrary_pair),
    );
    t.register("PolyQuotRemArbitrary", RtsFn::Arity4(zero4));
    t.register(
        "PolyCompareArbitrary",
        RtsFn::Arity2(poly_compare_arbitrary),
    ); // no threadId
    t.register("PolyGCDArbitrary", RtsFn::Arity3(poly_gcd_arbitrary));
    t.register("PolyLCMArbitrary", RtsFn::Arity3(poly_lcm_arbitrary));
    t.register("PolyAndArbitrary", RtsFn::Arity3(poly_and_arbitrary));
    t.register("PolyOrArbitrary", RtsFn::Arity3(poly_or_arbitrary));
    t.register("PolyXorArbitrary", RtsFn::Arity3(poly_xor_arbitrary));
    t.register(
        "PolyShiftLeftArbitrary",
        RtsFn::Arity3(poly_shift_left_arbitrary),
    );
    t.register(
        "PolyShiftRightArbitrary",
        RtsFn::Arity3(poly_shift_right_arbitrary),
    );
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
    t.register(
        "PolyThreadMutexBlock",
        RtsFn::Arity2(poly_thread_mutex_block),
    );
    // PolyThreadMutexUnlock(threadId, mutex): reset to unlocked.
    // Mirrors InterpreterReleaseMutex (bytecode.cpp:2465).
    t.register(
        "PolyThreadMutexUnlock",
        RtsFn::Arity2(poly_thread_mutex_unlock),
    );
    // Single-threaded mode: no other thread exists to wake / interrupt /
    // broadcast to, so these are no-ops.
    t.register("PolyThreadCondVarWake", RtsFn::Arity2(noop2));
    // PolyThreadForkThread takes (threadId, function, attrs, stack) — 4 args.
    t.register(
        "PolyThreadForkThread",
        RtsFn::Arity4(poly_thread_fork_thread),
    );
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
    t.register(
        "PolyLockMutableClosure",
        RtsFn::Arity2(poly_lock_mutable_closure),
    );

    // Interpreted-mode FFI — de-fanged: a fake CIF made Foreign.call
    // silently "call" C functions that never ran.
    //   PolyInterpretedCreateCIF(threadId, abi, resType, argTypes) → 4
    t.register(
        "PolyInterpretedCreateCIF",
        RtsFn::Arity4(|ctx, _, _, _, _| fail_unimpl(ctx, "Foreign: createCIF (no C FFI)")),
    );
    //   PolyInterpretedCallFunction(threadId, cif, cfun, res, argv) → 5
    t.register(
        "PolyInterpretedCallFunction",
        RtsFn::Arity5(|ctx, _, _, _, _, _| fail_unimpl(ctx, "Foreign: callFunction (no C FFI)")),
    );
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
// (zero5 was removed when its last user, PolyInterpretedCallFunction,
// was de-fanged to raise instead of faking a successful C call.)

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
fn poly_finish(_: &mut RtsContext<'_>, _tid: PolyWord, exit_code: PolyWord) -> PolyWord {
    if RTS_TRACE.load(Ordering::Relaxed) {
        eprintln!("  PolyFinish called with exit code {exit_code:?}");
    }
    let code = exit_code.untag();
    #[allow(clippy::cast_sign_loss)]
    FINISH_REQUESTED.store((code as usize).wrapping_add(1), Ordering::Relaxed);
    PolyWord::tagged(0)
}

/// `PolyTerminate(threadId, code)` — immediate process exit. Upstream
/// (`process_env.cpp:228`) calls `_exit(i)` directly: it does NOT run
/// the `atExit` list or flush buffers, and never returns. From inside
/// the interpreter we can't `_exit`, so — exactly as for [`poly_finish`]
/// — we set the global finish flag the dispatcher checks at the top of
/// `step()`, halting cleanly with the requested code. The basis wraps
/// this as `terminate n = (doCall n; raise Fail "never")`
/// (`basis/OS.sml:1169`); because we halt, the `raise Fail "never"`
/// never executes, matching upstream's "doesn't return" semantics.
#[allow(clippy::needless_pass_by_value)]
fn poly_terminate(_: &mut RtsContext<'_>, _tid: PolyWord, exit_code: PolyWord) -> PolyWord {
    if RTS_TRACE.load(Ordering::Relaxed) {
        eprintln!("  PolyTerminate called with exit code {exit_code:?}");
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
    let Some(name) = poly_string_to_rust(ctx.safe_spaces.as_ref(), filename) else {
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
    // UNTRUSTED MODE (task #96, SURFACE 6): hand the live-space snapshot to the
    // graph walk so it never derefs a wild/type-confused root or field. `None`
    // (trusted) -> the byte-identical legacy walk.
    let image = unsafe { crate::export::snapshot_gated(root, ctx.safe_spaces.clone()) };
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

/// `PolyEndBootstrapMode(threadId, function)` — record `function`
/// to be invoked (with unit arg) as soon as we return from this RTS
/// call. The SML caller passes `thirdStage : unit -> unit` and
/// expects it to never return.
///
/// The pending closure is recorded in the PER-THREAD slot on the
/// `RtsContext` (`bootstrap_tail_call`), which the dispatch site
/// (`Interpreter::rts_call`) reads back into the owning interpreter's
/// `bootstrap_tail_call` field after this call returns. It used to be a
/// process-global static, which would let a second thread clobber another
/// thread's pending tail call once real concurrency exists.
#[allow(clippy::needless_pass_by_value)]
fn poly_end_bootstrap_mode(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    function: PolyWord,
) -> PolyWord {
    ctx.bootstrap_tail_call = function;
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
            // NATIVE byte order: the string's bytes are read back byte-by-byte
            // from memory (LOAD_ML_BYTE), so the in-memory layout must match the
            // char order on THIS host. `from_ne_bytes` == `from_le_bytes` on a
            // little-endian host (byte-identical) and is correct on big-endian.
            words.push(usize::from_ne_bytes(chunk.try_into().unwrap()));
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
                base.add(cons_off + 2)
                    .write(base.add(next_cons_body) as usize);
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
        static ITEMS: &[(&str, isize)] = &[("UNIX", 1), ("INET", 2), ("INET6", 10)];
        static_string_int_list(ITEMS)
    });
    PolyWord::from_bits(addr)
}

fn poly_network_get_sock_type_list_inner() -> PolyWord {
    use std::sync::OnceLock;
    static LIST: OnceLock<usize> = OnceLock::new();
    let addr = *LIST.get_or_init(|| {
        static ITEMS: &[(&str, isize)] = &[("STREAM", 1), ("DGRAM", 2), ("RAW", 3)];
        static_string_int_list(ITEMS)
    });
    PolyWord::from_bits(addr)
}

// ===================================================================
// Sockets (Wave 1b). Port of `libpolyml/network.cpp`.
//
// THE ADDRESS MODEL (network.cpp:1474/1483 etc.): a socket address is
// carried across the ML/RTS boundary as a `PolyStringObject` whose CHARS
// ARE THE RAW `struct sockaddr` BYTES and whose length is the sockaddr
// length. So we never parse a sockaddr into a typed Rust value: we hand
// the raw bytes straight to `libc::bind`/`connect`/`sendto`, and for
// `accept`/`getsockname`/`getpeername` we wrap the raw `sockaddr_storage`
// bytes back into a PolyString via `alloc_poly_string`. The ML basis
// (INetSock.sml etc.) owns all address construction/parsing.
//
// DIVERGENCE FROM UPSTREAM — BLOCKING SOCKETS (deliberate). Upstream sets
// every socket NON-blocking (`ioctl(FIONBIO)`) at CreateSocket and drives
// blocking semantics from ML by looping on `PolyNetworkSelect` +
// `processes->ThreadPauseForIO` (network.cpp:1147/834). That depends on
// the thread scheduler, which is OFF by default in our single-threaded
// runtime. We instead leave sockets BLOCKING, so `accept`/`connect`/
// `recv`/`send` block the one mutator thread directly — correct blocking
// server/client semantics under the default single-threaded model
// (exactly as `OS.Process.system` blocks the mutator for its child). The
// basis' `Socket.send`/`recv` still call `select` first (to wait for
// writability/readability); our `PolyNetworkSelect` is a real `poll`, so
// that path also works. We DO keep upstream's EINTR retry loop on every
// blocking syscall (network.cpp `while (... == CALLINTERRUPTED)`).
mod socket_rts {
    // The cast-heavy socklen_t / c_int / sockaddr conversions below are all
    // intentional (fixed C-ABI widths and pointer-to-sockaddr casts that the
    // kernel copies byte-wise); allow the pedantic cast lints module-wide
    // rather than peppering per-line `#[allow]`s.
    #![allow(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        clippy::cast_possible_wrap,
        clippy::cast_ptr_alignment,
        clippy::wildcard_imports
    )]
    use super::*;

    /// Read `errno` after a failed libc call (matches the `raw_os_error`
    /// idiom used by `retry_eintr_read`/`write_array` in this file).
    #[cfg(unix)]
    pub(super) fn last_errno() -> i32 {
        std::io::Error::last_os_error()
            .raw_os_error()
            .unwrap_or(libc::EIO)
    }

    /// Upstream `getStreamSocket` / `getStreamFileDescriptor`
    /// (network.cpp:633 → basicio.cpp): read the wrapped-fd object (a 1-word
    /// byte object holding `fd + 1`, created by [`wrap_file_descriptor`]) and
    /// return the raw fd. A word-0 of 0 means the socket was closed → raise
    /// `SysErr("Stream is closed", EBADF)` (`STREAMCLOSED`, network.cpp:502).
    /// Returns `None` (with `ctx.raised_exception` already set) on a closed /
    /// invalid handle so the caller bails to the exception path.
    pub(super) fn get_stream_socket(
        ctx: &mut RtsContext<'_>,
        sock: PolyWord,
    ) -> Option<libc::c_int> {
        let Some(p) = safe_rts_arg_ptr(ctx.safe_spaces.as_ref(), sock) else {
            raise_syscall(ctx, "Stream is closed", libc::EBADF);
            return None;
        };
        // SAFETY: `p` is space-validated (untrusted) / is_data_ptr (trusted); a
        // wrapped-fd object is a 1-word byte box whose word 0 is `fd + 1`.
        let fd_plus_one = unsafe { (*p).0 };
        if fd_plus_one == 0 {
            raise_syscall(ctx, "Stream is closed", libc::EBADF);
            return None;
        }
        #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
        Some((fd_plus_one - 1) as libc::c_int)
    }

    /// Read the RAW bytes of a `PolyStringObject` (a socket address is a
    /// string whose chars are raw `struct sockaddr` bytes — NOT UTF-8, so
    /// [`poly_string_to_rust`] would wrongly reject them). Same header-fit /
    /// byte-object / body-bound checks as [`poly_string_to_rust`].
    pub(super) fn poly_string_raw_bytes(
        spaces: Option<&RtsSafeSpaces>,
        s: PolyWord,
    ) -> Option<Vec<u8>> {
        use crate::length_word::{is_byte_object, length_of};
        let obj = safe_rts_arg_obj(spaces, s)?;
        let p = obj.ptr;
        // SAFETY: `p` is space-validated (untrusted) / is_data_ptr (trusted),
        // so `p - 1` is a readable length word.
        let lw = unsafe { crate::space::MemorySpace::length_word_of(p) };
        if !is_byte_object(lw) {
            return None;
        }
        let body_bytes = obj
            .clamp_body_words(length_of(lw))
            .saturating_mul(std::mem::size_of::<usize>());
        // SAFETY: `p` is a byte object of >= 1 word (just checked), so word 0
        // (the stored byte length) is in-bounds.
        let len = unsafe { (*p).0 };
        if len > 1_000_000 {
            return None; // sanity bound (mirrors poly_string_to_rust)
        }
        if std::mem::size_of::<usize>().saturating_add(len) > body_bytes {
            return None; // stored length over-runs the object body
        }
        // SAFETY: `len + size_of::<usize>() <= body_bytes`, so the `len` char
        // bytes at body word 1 are in-bounds.
        let chars = unsafe { p.add(1).cast::<u8>() };
        Some(unsafe { std::slice::from_raw_parts(chars, len) }.to_vec())
    }

    /// Read a small ML int arg (`af`/`type`/`proto`/backlog/flags — always a
    /// tagged fixed-precision int at these sites) as an `i64`. Boxed values
    /// are handled too via [`ml_int_as_i64`].
    pub(super) fn socket_int_arg(spaces: Option<&RtsSafeSpaces>, w: PolyWord) -> i64 {
        ml_int_as_i64(spaces, w).unwrap_or(0)
    }

    /// Allocate an ML pair `(a, b)` (a 2-word ordinary tuple/record object).
    pub(super) fn alloc_pair(ctx: &mut RtsContext<'_>, a: PolyWord, b: PolyWord) -> PolyWord {
        let Some(space) = ctx.alloc_space.as_mut() else {
            return PolyWord::tagged(0);
        };
        let p = space.alloc_or_exit(2);
        // SAFETY: just allocated 2 words.
        unsafe {
            crate::space::set_length_word(p, 2, 0);
            p.write(a);
            p.add(1).write(b);
            PolyWord::from_ptr(p.cast_const())
        }
    }

    /// `PolyNetworkCreateSocket(threadId, af, st, prot)` — `socket(2)`.
    /// Port of network.cpp:1127. Leaves the socket BLOCKING (see the module
    /// note: upstream's FIONBIO block is intentionally skipped). Retries
    /// EINTR like upstream's `while (GETERROR == CALLINTERRUPTED)`.
    pub(super) fn poly_network_create_socket(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        family: PolyWord,
        st: PolyWord,
        prot: PolyWord,
    ) -> PolyWord {
        let af = socket_int_arg(ctx.safe_spaces.as_ref(), family) as libc::c_int;
        let ty = socket_int_arg(ctx.safe_spaces.as_ref(), st) as libc::c_int;
        let proto = socket_int_arg(ctx.safe_spaces.as_ref(), prot) as libc::c_int;
        let skt = loop {
            // SAFETY: plain libc socket(2); no pointers.
            let s = unsafe { libc::socket(af, ty, proto) };
            if s < 0 && last_errno() == libc::EINTR {
                continue;
            }
            break s;
        };
        if skt < 0 {
            return raise_syscall(ctx, "socket failed", last_errno());
        }
        #[allow(clippy::cast_sign_loss)]
        wrap_file_descriptor(ctx, skt as u32)
    }

    /// `PolyNetworkBind(threadId, sock, addr)` — `bind(2)`. network.cpp:1474.
    /// `addr` is the raw-sockaddr-bytes PolyString. Returns unit.
    pub(super) fn poly_network_bind(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        sock: PolyWord,
        addr: PolyWord,
    ) -> PolyWord {
        let Some(fd) = get_stream_socket(ctx, sock) else {
            return PolyWord::tagged(0);
        };
        let Some(bytes) = poly_string_raw_bytes(ctx.safe_spaces.as_ref(), addr) else {
            return raise_syscall(ctx, "bind failed", libc::EINVAL);
        };
        // SAFETY: `bytes` holds a full `struct sockaddr` (its length is the
        // sockaddr length); we pass ptr+len straight to bind(2).
        let r = unsafe {
            libc::bind(
                fd,
                bytes.as_ptr().cast::<libc::sockaddr>(),
                bytes.len() as libc::socklen_t,
            )
        };
        if r != 0 {
            return raise_syscall(ctx, "bind failed", last_errno());
        }
        PolyWord::tagged(0)
    }

    /// `PolyNetworkListen(threadId, sock, backlog)` — `listen(2)`.
    /// network.cpp:1496. Returns unit.
    pub(super) fn poly_network_listen(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        sock: PolyWord,
        back: PolyWord,
    ) -> PolyWord {
        let Some(fd) = get_stream_socket(ctx, sock) else {
            return PolyWord::tagged(0);
        };
        let backlog = socket_int_arg(ctx.safe_spaces.as_ref(), back) as libc::c_int;
        // SAFETY: plain listen(2).
        if unsafe { libc::listen(fd, backlog) } != 0 {
            return raise_syscall(ctx, "listen failed", last_errno());
        }
        PolyWord::tagged(0)
    }

    /// `PolyNetworkConnect(threadId, skt, addr)` — `connect(2)`.
    /// network.cpp:859. Blocking connect (see module note): the call blocks
    /// until the connection completes. Returns unit. Retries EINTR.
    pub(super) fn poly_network_connect(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        skt: PolyWord,
        addr: PolyWord,
    ) -> PolyWord {
        let Some(fd) = get_stream_socket(ctx, skt) else {
            return PolyWord::tagged(0);
        };
        let Some(bytes) = poly_string_raw_bytes(ctx.safe_spaces.as_ref(), addr) else {
            return raise_syscall(ctx, "connect failed", libc::EINVAL);
        };
        loop {
            // SAFETY: `bytes` is a full sockaddr; ptr+len passed to connect(2).
            let r = unsafe {
                libc::connect(
                    fd,
                    bytes.as_ptr().cast::<libc::sockaddr>(),
                    bytes.len() as libc::socklen_t,
                )
            };
            if r != 0 {
                let e = last_errno();
                if e == libc::EINTR {
                    continue;
                }
                return raise_syscall(ctx, "connect failed", e);
            }
            break;
        }
        PolyWord::tagged(0)
    }

    /// `PolyNetworkAccept(threadId, skt)` — `accept(2)`. network.cpp:880.
    /// Blocking accept: blocks until a peer connects. Returns a pair
    /// `(newSocket, peerAddr)` where `peerAddr` is the raw-sockaddr-bytes
    /// PolyString. Retries EINTR.
    pub(super) fn poly_network_accept(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        skt: PolyWord,
    ) -> PolyWord {
        let Some(fd) = get_stream_socket(ctx, skt) else {
            return PolyWord::tagged(0);
        };
        let mut storage: libc::sockaddr_storage = unsafe { std::mem::zeroed() };
        let mut addr_len = std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t;
        let new_fd = loop {
            // SAFETY: `storage`/`addr_len` are valid out-params sized to
            // sockaddr_storage; accept fills at most `addr_len` bytes.
            let s = unsafe {
                libc::accept(
                    fd,
                    (&raw mut storage).cast::<libc::sockaddr>(),
                    &raw mut addr_len,
                )
            };
            if s < 0 && last_errno() == libc::EINTR {
                continue;
            }
            break s;
        };
        if new_fd < 0 {
            return raise_syscall(ctx, "accept failed", last_errno());
        }
        let cap = std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t;
        if addr_len > cap {
            addr_len = cap;
        }
        // SAFETY: the first `addr_len` bytes of `storage` were filled by accept.
        let addr_bytes = unsafe {
            std::slice::from_raw_parts((&raw const storage).cast::<u8>(), addr_len as usize)
        };
        let addr_str = alloc_poly_string(ctx, addr_bytes);
        #[allow(clippy::cast_sign_loss)]
        let res_skt = wrap_file_descriptor(ctx, new_fd as u32);
        alloc_pair(ctx, res_skt, addr_str)
    }

    /// Shared reader for the `Send`/`Receive` byte-buffer argument: read
    /// `(base, offset, length)`, bound `offset + length` against `base`'s
    /// byte-object body, and return `(base_body_ptr, offset, length)`.
    /// Mirrors the write_array/read_array_from_stream bounds discipline.
    /// Returns `None` on any shape / bounds violation (the caller then raises
    /// `EINVAL`).
    pub(super) fn socket_buf_region(
        spaces: Option<&RtsSafeSpaces>,
        base: PolyWord,
        offset: PolyWord,
        length: PolyWord,
    ) -> Option<(*mut u8, usize, usize)> {
        use crate::length_word::{is_byte_object, length_of};
        if !offset.is_tagged() || !length.is_tagged() {
            return None;
        }
        let off = offset.untag();
        let len = length.untag();
        if off < 0 || len < 0 {
            return None;
        }
        #[allow(clippy::cast_sign_loss)]
        let (off, len) = (off as usize, len as usize);
        let base_obj = safe_rts_arg_obj(spaces, base)?;
        let base_p = base_obj.ptr;
        // SAFETY: `base_p` is space-validated (untrusted) / is_data_ptr
        // (trusted), so `base_p - 1` is a readable length word.
        let lw = unsafe { crate::space::MemorySpace::length_word_of(base_p) };
        let body_bytes = base_obj
            .clamp_body_words(length_of(lw))
            .saturating_mul(std::mem::size_of::<usize>());
        if !is_byte_object(lw) || off.checked_add(len).is_none_or(|end| end > body_bytes) {
            return None;
        }
        Some((base_p.cast::<u8>().cast_mut(), off, len))
    }

    /// `PolyNetworkSend(threadId, args)` — `send(2)`. network.cpp:911.
    /// `args` is the 6-tuple `(sock, base, offset, length, dontRoute,
    /// outOfBand)`. Returns `TAGGED(bytesSent)`. Retries EINTR.
    pub(super) fn poly_network_send(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        args: PolyWord,
    ) -> PolyWord {
        let Some(obj) = safe_rts_arg_obj(ctx.safe_spaces.as_ref(), args) else {
            return raise_syscall(ctx, "send failed", libc::EINVAL);
        };
        if obj.n_words < 6 {
            return raise_syscall(ctx, "send failed", libc::EINVAL);
        }
        // SAFETY: `obj` holds >= 6 words per the gate above.
        let field = |i: usize| unsafe { *obj.ptr.add(i) };
        let Some(fd) = get_stream_socket(ctx, field(0)) else {
            return PolyWord::tagged(0);
        };
        let Some((base, off, len)) =
            socket_buf_region(ctx.safe_spaces.as_ref(), field(1), field(2), field(3))
        else {
            return raise_syscall(ctx, "send failed", libc::EINVAL);
        };
        let mut flags = 0;
        if socket_int_arg(ctx.safe_spaces.as_ref(), field(4)) != 0 {
            flags |= libc::MSG_DONTROUTE;
        }
        if socket_int_arg(ctx.safe_spaces.as_ref(), field(5)) != 0 {
            flags |= libc::MSG_OOB;
        }
        let sent = loop {
            // SAFETY: `[base+off, base+off+len)` was bounds-checked to lie
            // within the byte object's body by `socket_buf_region`.
            let r = unsafe { libc::send(fd, base.add(off).cast::<libc::c_void>(), len, flags) };
            if r < 0 && last_errno() == libc::EINTR {
                continue;
            }
            break r;
        };
        if sent < 0 {
            return raise_syscall(ctx, "send failed", last_errno());
        }
        #[allow(clippy::cast_possible_wrap)]
        PolyWord::tagged(sent as isize)
    }

    /// `PolyNetworkReceive(threadId, args)` — `recv(2)`. network.cpp:992.
    /// `args` is the 6-tuple `(sock, base, offset, length, peek, outOfBand)`
    /// where `base` is a MUTABLE byte array written in place. Returns
    /// `TAGGED(bytesReceived)` (0 = orderly shutdown). Blocking; retries EINTR.
    pub(super) fn poly_network_receive(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        args: PolyWord,
    ) -> PolyWord {
        let Some(obj) = safe_rts_arg_obj(ctx.safe_spaces.as_ref(), args) else {
            return raise_syscall(ctx, "recv failed", libc::EINVAL);
        };
        if obj.n_words < 6 {
            return raise_syscall(ctx, "recv failed", libc::EINVAL);
        }
        // SAFETY: `obj` holds >= 6 words per the gate above.
        let field = |i: usize| unsafe { *obj.ptr.add(i) };
        let Some(fd) = get_stream_socket(ctx, field(0)) else {
            return PolyWord::tagged(0);
        };
        let Some((base, off, len)) =
            socket_buf_region(ctx.safe_spaces.as_ref(), field(1), field(2), field(3))
        else {
            return raise_syscall(ctx, "recv failed", libc::EINVAL);
        };
        let mut flags = 0;
        if socket_int_arg(ctx.safe_spaces.as_ref(), field(4)) != 0 {
            flags |= libc::MSG_PEEK;
        }
        if socket_int_arg(ctx.safe_spaces.as_ref(), field(5)) != 0 {
            flags |= libc::MSG_OOB;
        }
        let recvd = loop {
            // SAFETY: `[base+off, base+off+len)` was bounds-checked to lie
            // within the byte object's body by `socket_buf_region`; recv
            // writes at most `len` bytes there.
            let r = unsafe { libc::recv(fd, base.add(off).cast::<libc::c_void>(), len, flags) };
            if r < 0 && last_errno() == libc::EINTR {
                continue;
            }
            break r;
        };
        if recvd < 0 {
            return raise_syscall(ctx, "recv failed", last_errno());
        }
        #[allow(clippy::cast_possible_wrap)]
        PolyWord::tagged(recvd as isize)
    }

    /// `PolyNetworkSendTo(threadId, args)` — `sendto(2)`. network.cpp:950.
    /// `args` is the 7-tuple `(sock, addr, base, offset, length, dontRoute,
    /// outOfBand)`. Returns `TAGGED(bytesSent)`. Retries EINTR.
    pub(super) fn poly_network_send_to(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        args: PolyWord,
    ) -> PolyWord {
        let Some(obj) = safe_rts_arg_obj(ctx.safe_spaces.as_ref(), args) else {
            return raise_syscall(ctx, "sendto failed", libc::EINVAL);
        };
        if obj.n_words < 7 {
            return raise_syscall(ctx, "sendto failed", libc::EINVAL);
        }
        // SAFETY: `obj` holds >= 7 words per the gate above.
        let field = |i: usize| unsafe { *obj.ptr.add(i) };
        let Some(fd) = get_stream_socket(ctx, field(0)) else {
            return PolyWord::tagged(0);
        };
        let Some(addr_bytes) = poly_string_raw_bytes(ctx.safe_spaces.as_ref(), field(1)) else {
            return raise_syscall(ctx, "sendto failed", libc::EINVAL);
        };
        let Some((base, off, len)) =
            socket_buf_region(ctx.safe_spaces.as_ref(), field(2), field(3), field(4))
        else {
            return raise_syscall(ctx, "sendto failed", libc::EINVAL);
        };
        let mut flags = 0;
        if socket_int_arg(ctx.safe_spaces.as_ref(), field(5)) != 0 {
            flags |= libc::MSG_DONTROUTE;
        }
        if socket_int_arg(ctx.safe_spaces.as_ref(), field(6)) != 0 {
            flags |= libc::MSG_OOB;
        }
        let sent = loop {
            // SAFETY: buffer region bounds-checked by `socket_buf_region`;
            // `addr_bytes` is a full sockaddr passed by ptr+len.
            let r = unsafe {
                libc::sendto(
                    fd,
                    base.add(off).cast::<libc::c_void>(),
                    len,
                    flags,
                    addr_bytes.as_ptr().cast::<libc::sockaddr>(),
                    addr_bytes.len() as libc::socklen_t,
                )
            };
            if r < 0 && last_errno() == libc::EINTR {
                continue;
            }
            break r;
        };
        if sent < 0 {
            return raise_syscall(ctx, "sendto failed", last_errno());
        }
        #[allow(clippy::cast_possible_wrap)]
        PolyWord::tagged(sent as isize)
    }

    /// `PolyNetworkReceiveFrom(threadId, args)` — `recvfrom(2)`.
    /// network.cpp:1031. `args` is the 6-tuple `(sock, base, offset, length,
    /// peek, outOfBand)`; returns the pair `(bytesReceived, peerAddr)` where
    /// `peerAddr` is the raw-sockaddr-bytes PolyString. Blocking; retries EINTR.
    pub(super) fn poly_network_receive_from(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        args: PolyWord,
    ) -> PolyWord {
        let Some(obj) = safe_rts_arg_obj(ctx.safe_spaces.as_ref(), args) else {
            return raise_syscall(ctx, "recvfrom failed", libc::EINVAL);
        };
        if obj.n_words < 6 {
            return raise_syscall(ctx, "recvfrom failed", libc::EINVAL);
        }
        // SAFETY: `obj` holds >= 6 words per the gate above.
        let field = |i: usize| unsafe { *obj.ptr.add(i) };
        let Some(fd) = get_stream_socket(ctx, field(0)) else {
            return PolyWord::tagged(0);
        };
        let Some((base, off, len)) =
            socket_buf_region(ctx.safe_spaces.as_ref(), field(1), field(2), field(3))
        else {
            return raise_syscall(ctx, "recvfrom failed", libc::EINVAL);
        };
        let mut flags = 0;
        if socket_int_arg(ctx.safe_spaces.as_ref(), field(4)) != 0 {
            flags |= libc::MSG_PEEK;
        }
        if socket_int_arg(ctx.safe_spaces.as_ref(), field(5)) != 0 {
            flags |= libc::MSG_OOB;
        }
        let mut storage: libc::sockaddr_storage = unsafe { std::mem::zeroed() };
        let mut addr_len = std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t;
        let recvd = loop {
            // SAFETY: buffer region bounds-checked by `socket_buf_region`;
            // `storage`/`addr_len` are valid out-params sized to sockaddr_storage.
            let r = unsafe {
                libc::recvfrom(
                    fd,
                    base.add(off).cast::<libc::c_void>(),
                    len,
                    flags,
                    (&raw mut storage).cast::<libc::sockaddr>(),
                    &raw mut addr_len,
                )
            };
            if r < 0 && last_errno() == libc::EINTR {
                continue;
            }
            break r;
        };
        if recvd < 0 {
            return raise_syscall(ctx, "recvfrom failed", last_errno());
        }
        let cap = std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t;
        if addr_len > cap {
            addr_len = cap;
        }
        // SAFETY: the first `addr_len` bytes of `storage` were filled by recvfrom.
        let addr_bytes = unsafe {
            std::slice::from_raw_parts((&raw const storage).cast::<u8>(), addr_len as usize)
        };
        let addr_str = alloc_poly_string(ctx, addr_bytes);
        #[allow(clippy::cast_possible_wrap)]
        let len_w = PolyWord::tagged(recvd as isize);
        alloc_pair(ctx, len_w, addr_str)
    }

    /// `PolyNetworkShutdown(threadId, skt, how)` — `shutdown(2)`.
    /// network.cpp:1517. `how` maps 1/2/3 → `SHUT_RD`/`SHUT_WR`/`SHUT_RDWR`.
    /// Returns unit.
    pub(super) fn poly_network_shutdown(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        skt: PolyWord,
        smode: PolyWord,
    ) -> PolyWord {
        let Some(fd) = get_stream_socket(ctx, skt) else {
            return PolyWord::tagged(0);
        };
        let mode = match socket_int_arg(ctx.safe_spaces.as_ref(), smode) {
            1 => libc::SHUT_RD,
            2 => libc::SHUT_WR,
            3 => libc::SHUT_RDWR,
            _ => 0,
        };
        // SAFETY: plain shutdown(2).
        if unsafe { libc::shutdown(fd, mode) } != 0 {
            return raise_syscall(ctx, "shutdown failed", last_errno());
        }
        PolyWord::tagged(0)
    }

    /// `PolyNetworkCloseSocket(threadId, skt)` — `close(2)` on the socket fd.
    /// A socket IS an fd, so this is exactly [`close_file`]'s behaviour;
    /// wrapped for the `(threadId, skt)` arity. network.cpp routes socket
    /// close through the general IO close.
    pub(super) fn poly_network_close_socket(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        skt: PolyWord,
    ) -> PolyWord {
        close_file(ctx.safe_spaces.as_ref(), skt)
    }

    /// `PolyNetworkGetSockName(threadId, sock)` — `getsockname(2)`.
    /// network.cpp:1388. Returns the local address as a raw-sockaddr-bytes
    /// PolyString.
    pub(super) fn poly_network_get_sock_name(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        sock: PolyWord,
    ) -> PolyWord {
        get_name_common(ctx, sock, false)
    }

    /// `PolyNetworkGetPeerName(threadId, sock)` — `getpeername(2)`.
    /// network.cpp:1361. Returns the peer address as a raw-sockaddr-bytes
    /// PolyString.
    pub(super) fn poly_network_get_peer_name(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        sock: PolyWord,
    ) -> PolyWord {
        get_name_common(ctx, sock, true)
    }

    /// Shared body of getsockname/getpeername (`peer` selects which).
    pub(super) fn get_name_common(
        ctx: &mut RtsContext<'_>,
        sock: PolyWord,
        peer: bool,
    ) -> PolyWord {
        let Some(fd) = get_stream_socket(ctx, sock) else {
            return PolyWord::tagged(0);
        };
        let mut storage: libc::sockaddr_storage = unsafe { std::mem::zeroed() };
        let mut size = std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t;
        // SAFETY: `storage`/`size` are valid out-params sized to sockaddr_storage.
        let r = unsafe {
            let sa = (&raw mut storage).cast::<libc::sockaddr>();
            if peer {
                libc::getpeername(fd, sa, &raw mut size)
            } else {
                libc::getsockname(fd, sa, &raw mut size)
            }
        };
        if r != 0 {
            let msg = if peer {
                "getpeername failed"
            } else {
                "getsockname failed"
            };
            return raise_syscall(ctx, msg, last_errno());
        }
        let cap = std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t;
        if size > cap {
            size = cap;
        }
        // SAFETY: the first `size` bytes of `storage` were filled by the call.
        let bytes =
            unsafe { std::slice::from_raw_parts((&raw const storage).cast::<u8>(), size as usize) };
        alloc_poly_string(ctx, bytes)
    }

    /// `PolyNetworkCreateIP4Address(threadId, ip4Address, portNumber)` —
    /// build a `struct sockaddr_in` and return it as a raw-bytes PolyString.
    /// network.cpp:1981. `ip4Address` is a host-order IPv4 address (an ML
    /// int; `INADDR_ANY` = 0), `portNumber` a host-order port.
    pub(super) fn poly_network_create_ip4_address(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        ip4: PolyWord,
        port: PolyWord,
    ) -> PolyWord {
        #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
        let ip = socket_int_arg(ctx.safe_spaces.as_ref(), ip4) as u32;
        #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
        let p = socket_int_arg(ctx.safe_spaces.as_ref(), port) as u16;
        let mut sa: libc::sockaddr_in = unsafe { std::mem::zeroed() };
        sa.sin_family = libc::AF_INET as libc::sa_family_t;
        sa.sin_port = p.to_be(); // htons
        sa.sin_addr.s_addr = ip.to_be(); // htonl
        // SAFETY: read the POD sockaddr_in as its raw bytes to build the
        // address PolyString (the ML side treats it as an opaque byte string).
        let bytes = unsafe {
            std::slice::from_raw_parts(
                (&raw const sa).cast::<u8>(),
                std::mem::size_of::<libc::sockaddr_in>(),
            )
        };
        alloc_poly_string(ctx, bytes)
    }

    /// `PolyNetworkGetAddressAndPortFromIP4(threadId, sockAddress)` — parse a
    /// `struct sockaddr_in` PolyString into the pair `(hostOrderIp, port)`.
    /// network.cpp:1956. The IPv4 address is a `LargeInt.int`.
    pub(super) fn poly_network_get_address_and_port_from_ip4(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        sock_addr: PolyWord,
    ) -> PolyWord {
        let Some(bytes) = poly_string_raw_bytes(ctx.safe_spaces.as_ref(), sock_addr) else {
            return raise_syscall(ctx, "getAddressAndPortFromIP4 failed", libc::EINVAL);
        };
        if bytes.len() < std::mem::size_of::<libc::sockaddr_in>() {
            return raise_syscall(ctx, "getAddressAndPortFromIP4 failed", libc::EINVAL);
        }
        // Read sin_addr / sin_port from the raw bytes (network byte order in
        // the struct); convert to host order. Copy into an aligned local to
        // avoid any alignment assumption on the PolyString body.
        let mut sa: libc::sockaddr_in = unsafe { std::mem::zeroed() };
        // SAFETY: `bytes` holds at least a full sockaddr_in (checked above);
        // copy those bytes into a properly aligned local.
        unsafe {
            std::ptr::copy_nonoverlapping(
                bytes.as_ptr(),
                (&raw mut sa).cast::<u8>(),
                std::mem::size_of::<libc::sockaddr_in>(),
            );
        }
        let ip = u32::from_be(sa.sin_addr.s_addr); // ntohl
        let port = u16::from_be(sa.sin_port); // ntohs
        let ip_w = int_to_poly_word(ctx, i128::from(ip));
        let port_w = PolyWord::tagged(port as isize);
        alloc_pair(ctx, ip_w, port_w)
    }

    /// `PolyNetworkBytesAvailable(threadId, sock)` — `ioctl(FIONREAD)`.
    /// network.cpp:1414. Returns the number of bytes readable without blocking.
    pub(super) fn poly_network_bytes_available(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        sock: PolyWord,
    ) -> PolyWord {
        let Some(fd) = get_stream_socket(ctx, sock) else {
            return PolyWord::tagged(0);
        };
        let mut readable: libc::c_int = 0;
        // SAFETY: FIONREAD writes one int into `readable`.
        if unsafe { libc::ioctl(fd, libc::FIONREAD, &raw mut readable) } < 0 {
            return raise_syscall(ctx, "ioctl failed", last_errno());
        }
        int_to_poly_word(ctx, i128::from(readable))
    }

    /// `PolyNetworkGetAtMark(threadId, sock)` — the OOB-mark test
    /// (upstream uses `ioctl(SIOCATMARK)`; we use the POSIX `sockatmark(3)`
    /// wrapper, which is portable across Unixes and not exposed by the `libc`
    /// crate). network.cpp:1444. Returns the flag as a fixed-precision 0/1.
    pub(super) fn poly_network_get_at_mark(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        sock: PolyWord,
    ) -> PolyWord {
        // `sockatmark` is POSIX (glibc >= 2.2.4, macOS) but absent from the
        // `libc` crate at this version; declare it directly.
        unsafe extern "C" {
            fn sockatmark(fd: libc::c_int) -> libc::c_int;
        }
        let Some(fd) = get_stream_socket(ctx, sock) else {
            return PolyWord::tagged(0);
        };
        // SAFETY: `fd` is a live socket fd; sockatmark takes only the fd.
        let at_mark = unsafe { sockatmark(fd) };
        if at_mark < 0 {
            return raise_syscall(ctx, "sockatmark failed", last_errno());
        }
        PolyWord::tagged(isize::from(at_mark != 0))
    }

    /// `PolyNetworkGetSocketError(threadId, skt)` — `getsockopt(SO_ERROR)`.
    /// network.cpp:745. Returns the pending socket error as a `SysWord.word`
    /// (a 1-word byte box holding the errno), matching upstream's `Make_sysword`.
    pub(super) fn poly_network_get_socket_error(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        skt: PolyWord,
    ) -> PolyWord {
        let Some(fd) = get_stream_socket(ctx, skt) else {
            return PolyWord::tagged(0);
        };
        let mut val: libc::c_int = 0;
        let mut size = std::mem::size_of::<libc::c_int>() as libc::socklen_t;
        // SAFETY: SO_ERROR writes one int into `val`; `size` is its byte length.
        let r = unsafe {
            libc::getsockopt(
                fd,
                libc::SOL_SOCKET,
                libc::SO_ERROR,
                (&raw mut val).cast::<libc::c_void>(),
                &raw mut size,
            )
        };
        if r != 0 {
            return raise_syscall(ctx, "getsockopt failed", last_errno());
        }
        make_sysword(ctx, val)
    }

    /// Build a `SysWord.word` value: a 1-word MUTABLE byte box holding the
    /// raw value. Mirrors upstream `Make_sysword` (used by GetSocketError).
    pub(super) fn make_sysword(ctx: &mut RtsContext<'_>, v: libc::c_int) -> PolyWord {
        use crate::length_word::F_BYTE_OBJ;
        let Some(space) = ctx.alloc_space.as_mut() else {
            return PolyWord::tagged(0);
        };
        let p = space.alloc_or_exit(1);
        // SAFETY: just allocated 1 word (the SysWord byte box).
        unsafe {
            crate::space::set_length_word(p, 1, F_BYTE_OBJ);
            #[allow(clippy::cast_sign_loss)]
            p.write(PolyWord::from_bits(v as usize));
            PolyWord::from_ptr(p.cast_const())
        }
    }

    /// `PolyNetworkCreateSocketPair(threadId, af, st, prot)` —
    /// `socketpair(2)`. network.cpp:1544. Returns a pair of wrapped sockets.
    /// Left BLOCKING (see module note). Retries EINTR.
    pub(super) fn poly_network_create_socket_pair(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        family: PolyWord,
        st: PolyWord,
        prot: PolyWord,
    ) -> PolyWord {
        let af = socket_int_arg(ctx.safe_spaces.as_ref(), family) as libc::c_int;
        let ty = socket_int_arg(ctx.safe_spaces.as_ref(), st) as libc::c_int;
        let proto = socket_int_arg(ctx.safe_spaces.as_ref(), prot) as libc::c_int;
        let mut fds: [libc::c_int; 2] = [0, 0];
        let rc = loop {
            // SAFETY: socketpair fills the 2-element `fds` array.
            let r = unsafe { libc::socketpair(af, ty, proto, fds.as_mut_ptr()) };
            if r != 0 && last_errno() == libc::EINTR {
                continue;
            }
            break r;
        };
        if rc != 0 {
            return raise_syscall(ctx, "socketpair failed", last_errno());
        }
        #[allow(clippy::cast_sign_loss)]
        let a = wrap_file_descriptor(ctx, fds[0] as u32);
        #[allow(clippy::cast_sign_loss)]
        let b = wrap_file_descriptor(ctx, fds[1] as u32);
        alloc_pair(ctx, a, b)
    }

    /// `PolyNetworkSelect(threadId, fdVecTriple, maxMillisecs)` — `poll(2)`.
    /// network.cpp:810. `fdVecTriple` is `(readVec, writeVec, excVec)`, each
    /// a vector of iodescs; `maxMillisecs` is a tagged timeout. Returns the
    /// triple of vectors holding only the ready iodescs. Under the default
    /// single-threaded model we do a real `poll` for up to `maxMillisecs`
    /// (upstream uses `ThreadPauseForIO`; the ML `select` wrapper already
    /// loops us to honour a longer/indefinite timeout).
    pub(super) fn poly_network_select(
        ctx: &mut RtsContext<'_>,
        _tid: PolyWord,
        fd_vec_triple: PolyWord,
        max_ms: PolyWord,
    ) -> PolyWord {
        use crate::length_word::{length_of, make_length_word};
        let timeout_ms = if max_ms.is_tagged() {
            #[allow(clippy::cast_possible_truncation)]
            {
                max_ms.untag().max(0) as libc::c_int
            }
        } else {
            0
        };
        let spaces = ctx.safe_spaces.clone();
        let Some(triple) = safe_rts_arg_obj(spaces.as_ref(), fd_vec_triple) else {
            return raise_syscall(ctx, "select failed", libc::EINVAL);
        };
        if triple.n_words < 3 {
            return raise_syscall(ctx, "select failed", libc::EINVAL);
        }
        // Read the three vector words. Each vector is an ML word-object whose
        // elements are iodesc (wrapped-fd) words.
        // SAFETY: `triple` holds >= 3 words per the gate above.
        let vec_words = [
            unsafe { *triple.ptr },
            unsafe { *triple.ptr.add(1) },
            unsafe { *triple.ptr.add(2) },
        ];
        // Collect, per vector, the list of (element-word, fd). We keep the
        // ORIGINAL element word so the result vectors contain the very same
        // iodesc objects the ML side passed (upstream preserves them too).
        let mut elems: [Vec<(PolyWord, libc::c_int)>; 3] = [Vec::new(), Vec::new(), Vec::new()];
        let mut pollfds: Vec<libc::pollfd> = Vec::new();
        // Poll events per set: read→POLLIN, write→POLLOUT, exc→POLLPRI.
        let events = [libc::POLLIN, libc::POLLOUT, libc::POLLPRI];
        for (i, &vw) in vec_words.iter().enumerate() {
            let Some(vec_obj) = safe_rts_arg_obj(spaces.as_ref(), vw) else {
                // An empty vector is a valid word-object; a non-pointer here
                // means the ML side passed `Vector.fromList []` shaped oddly —
                // skip it (treated as no descriptors in this set).
                continue;
            };
            // SAFETY: `vec_obj.ptr - 1` is the length word (validated / is_data_ptr).
            let lw = unsafe { crate::space::MemorySpace::length_word_of(vec_obj.ptr) };
            let n = vec_obj.clamp_body_words(length_of(lw));
            for j in 0..n {
                // SAFETY: j < n <= validated body word count.
                let elem = unsafe { *vec_obj.ptr.add(j) };
                let Some(fd) = get_stream_socket(ctx, elem) else {
                    // get_stream_socket set a raised exception (closed socket).
                    return PolyWord::tagged(0);
                };
                pollfds.push(libc::pollfd {
                    fd,
                    events: events[i],
                    revents: 0,
                });
                elems[i].push((elem, fd));
            }
        }
        if !pollfds.is_empty() {
            let rc = loop {
                // SAFETY: `pollfds` is a valid array of `len` pollfd entries.
                let r = unsafe {
                    libc::poll(
                        pollfds.as_mut_ptr(),
                        pollfds.len() as libc::nfds_t,
                        timeout_ms,
                    )
                };
                if r < 0 && last_errno() == libc::EINTR {
                    continue;
                }
                break r;
            };
            if rc < 0 {
                return raise_syscall(ctx, "select failed", last_errno());
            }
        }
        // Build the result: for each set, the elements whose poll revents show
        // the requested condition (or an error/hangup, which the ML side wants
        // to observe too — matches select() semantics reporting exceptional fds).
        let ready_mask = [
            libc::POLLIN | libc::POLLHUP | libc::POLLERR,
            libc::POLLOUT | libc::POLLERR,
            libc::POLLPRI | libc::POLLERR,
        ];
        let mut result_vecs = [PolyWord::tagged(0); 3];
        for i in 0..3 {
            // Gather ready element words for set i.
            let mut ready: Vec<PolyWord> = Vec::new();
            for (elem, fd) in &elems[i] {
                if let Some(pf) = pollfds
                    .iter()
                    .find(|p| p.fd == *fd && p.events == events[i])
                    && pf.revents & ready_mask[i] != 0
                {
                    ready.push(*elem);
                }
            }
            // Allocate a word-object vector of the ready elements.
            let Some(space) = ctx.alloc_space.as_mut() else {
                return PolyWord::tagged(0);
            };
            let p = space.alloc_or_exit(ready.len());
            // SAFETY: just allocated `ready.len()` words.
            unsafe {
                p.sub(1).write(make_length_word(ready.len(), 0));
                for (k, w) in ready.iter().enumerate() {
                    p.add(k).write(*w);
                }
            }
            result_vecs[i] = PolyWord::from_ptr(p.cast_const());
        }
        // Assemble the 3-tuple of result vectors.
        let Some(space) = ctx.alloc_space.as_mut() else {
            return PolyWord::tagged(0);
        };
        let p = space.alloc_or_exit(3);
        // SAFETY: just allocated 3 words.
        unsafe {
            crate::space::set_length_word(p, 3, 0);
            p.write(result_vecs[0]);
            p.add(1).write(result_vecs[1]);
            p.add(2).write(result_vecs[2]);
            PolyWord::from_ptr(p.cast_const())
        }
    }
} // mod socket_rts

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
        9 => b"polyml-rs",       // GIT_VERSION
        10 => b"Portable-5.9.0", // RTS version (interpreted)
        12 => b"Interpreted",    // architecture name
        19 => b"",               // RTS arg help (empty)
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
            std::ptr::copy_nonoverlapping(chars.as_ptr(), str_ptr.add(1).cast::<u8>(), 8);
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
        let cons = space.alloc_or_exit(2);
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

/// `PolyProcessEnvErrorName(threadId, syserr)` -> boxed string naming the
/// system error code (e.g. "ENOENT"), or "ERROR<n>" if not in the table.
/// `syserr` is a boxed `LargeWord.word` (SysWord.word); upstream reads word 0
/// as the errno. Mirrors process_env.cpp:238-265 + errors.cpp:1312.
#[allow(clippy::needless_pass_by_value)]
fn poly_process_env_error_name(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    syserr: PolyWord,
) -> PolyWord {
    // syserror = LargeWord.word (LibrarySupport.sml:220): a 1-word byte
    // object whose word 0 holds the error number. Tagged fallback for
    // safety (a small SysWord could in principle arrive untagged).
    let e: i64 = if syserr.is_tagged() {
        syserr.untag() as i64
    } else if let Some(p) = safe_rts_arg_ptr(ctx.safe_spaces.as_ref(), syserr) {
        // UNTRUSTED MODE (task #96, HOLE 5): `syserr` is image-controlled; the
        // boxed SysWord deref is gated on space-membership.
        // SAFETY: p space-validated (untrusted) / is_data_ptr (trusted).
        unsafe { (*p).0 as i64 }
    } else {
        0
    };
    match errno_name(e) {
        Some(name) => alloc_poly_string(ctx, name.as_bytes()),
        // Upstream: snprintf(buff, "ERROR%0d", e) (process_env.cpp:255).
        None => alloc_poly_string(ctx, format!("ERROR{e}").as_bytes()),
    }
}

/// errno -> canonical POSIX name, mirroring the Unix branch of `errortable`
/// in vendor/polyml/libpolyml/errors.cpp:49-1310. Returns `None` for codes
/// not in the table (caller emits the "ERROR<n>" fallback, matching
/// errors.cpp:1320 returning 0). Values are the standard Linux/glibc errno
/// numbers (EPERM=1, ENOENT=2, ...), faithful to upstream's platform errno
/// macros for our target.
fn errno_name(e: i64) -> Option<&'static str> {
    Some(match e {
        1 => "EPERM",
        2 => "ENOENT",
        3 => "ESRCH",
        4 => "EINTR",
        5 => "EIO",
        6 => "ENXIO",
        7 => "E2BIG",
        8 => "ENOEXEC",
        9 => "EBADF",
        10 => "ECHILD",
        11 => "EAGAIN",
        12 => "ENOMEM",
        13 => "EACCES",
        14 => "EFAULT",
        16 => "EBUSY",
        17 => "EEXIST",
        18 => "EXDEV",
        19 => "ENODEV",
        20 => "ENOTDIR",
        21 => "EISDIR",
        22 => "EINVAL",
        23 => "ENFILE",
        24 => "EMFILE",
        25 => "ENOTTY",
        27 => "EFBIG",
        28 => "ENOSPC",
        29 => "ESPIPE",
        30 => "EROFS",
        31 => "EMLINK",
        32 => "EPIPE",
        34 => "ERANGE",
        36 => "ENAMETOOLONG",
        40 => "ELOOP",
        62 => "ETIME",
        110 => "ETIMEDOUT",
        111 => "ECONNREFUSED",
        _ => return None,
    })
}

#[allow(clippy::needless_pass_by_value)]
fn poly_wait_for_signal(_: &mut RtsContext<'_>, _arg: PolyWord) -> PolyWord {
    PolyWord::tagged(0)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_get_function_name(ctx: &mut RtsContext<'_>, _tid: PolyWord, _code: PolyWord) -> PolyWord {
    alloc_empty_string(ctx)
}

/// `PolyThreadMutexBlock(threadId, mutex)` — single-threaded
/// emulation: reset the mutex object's first word to TAGGED(0)
/// (= unlocked), so the caller's retry loop exits on its next
/// tryLockMutex.
#[allow(clippy::needless_pass_by_value)]
fn poly_thread_mutex_block(ctx: &mut RtsContext<'_>, _tid: PolyWord, mutex: PolyWord) -> PolyWord {
    reset_mutex(ctx.safe_spaces.as_ref(), mutex);
    PolyWord::tagged(0)
}

/// `PolyThreadMutexUnlock(threadId, mutex)` — reset mutex to
/// TAGGED(0) (= unlocked). Mirrors `InterpreterReleaseMutex` in
/// `bytecode.cpp:2465`. (In multi-thread mode this also wakes
/// waiters; single-thread has none.)
#[allow(clippy::needless_pass_by_value)]
fn poly_thread_mutex_unlock(ctx: &mut RtsContext<'_>, _tid: PolyWord, mutex: PolyWord) -> PolyWord {
    reset_mutex(ctx.safe_spaces.as_ref(), mutex);
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
    // UNTRUSTED MODE (task #96, HOLE 5): snapshot the live spaces so the
    // ctx-less stream readers (write_array / read_array_from_stream /
    // close_file / close_directory) can gate their image-arg derefs without a
    // borrow conflict with the `ctx`-taking arms. `None` in trusted mode -> a
    // trivial clone, byte-identical.
    let io_spaces = ctx.safe_spaces.clone();
    let io_spaces = io_spaces.as_ref();
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
        7 => close_file(io_spaces, strm),
        // 8/9: read text/binary into an array. arg is a 3-tuple
        //      (buffer, offset, length). Returns # bytes read
        //      (0 = EOF). A REAL read error (≠ EOF) raises SysErr —
        //      upstream basicio.cpp:308.
        8 | 9 => {
            let r = read_array_from_stream(io_spaces, strm, arg);
            match io_sentinel_errno(r) {
                None => r,
                Some(errno) => raise_syscall(ctx, "Error while reading", errno),
            }
        }
        // 10/26: read text/binary as a (PolyML) string. Route to
        // std::io::stdin for fd 0 so the bootstrap can actually
        // consume input from a pipe; everything else returns
        // an empty string (= EOF) which is safe.
        10 | 26 => read_string_from_stream(ctx, strm, arg),
        // 11/12: write array — write to the fd and return the byte
        // count. A REAL write error raises SysErr instead of reporting
        // "0 bytes written" (which livelocked the basis write-all loop
        // on persistent EPIPE/ENOSPC) — upstream basicio.cpp:363.
        11 | 12 => {
            let r = write_array(io_spaces, strm, arg);
            match io_sentinel_errno(r) {
                None => r,
                Some(errno) => raise_syscall(ctx, "Error while writing", errno),
            }
        }
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
        52 => close_directory(io_spaces, strm),
        // 54: getcwd
        54 => get_current_dir(ctx),
        // 57: isDir(name) → 1 / 0
        57 => fs_is_dir(io_spaces, arg),
        // 60: fullPath(name) → canonicalized absolute path
        60 => fs_full_path(ctx, arg),
        // 61: modTime(name) → microseconds since epoch as tagged-or-arb int
        61 => fs_mod_time(ctx, arg),
        // 62: fileSize(name)
        62 => fs_file_size(ctx, arg),
        // 64: remove(name) — delete a file. HOL4's HolSat writes DIMACS temp
        //     files (via tmpName) and clean_delete()s them; without this they
        //     leak into the temp dir on every SAT/tautLib call.
        64 => fs_remove(io_spaces, arg),
        // 66: access(name, mode) → 1 / 0
        66 => fs_access(io_spaces, arg, strm),
        // 67: tmpName() → a fresh unique temp-file path string.
        //     HOL4's HolSat (dimacsTools) needs this before it falls
        //     through to its pure-SML DPLL prover; without it the call
        //     returns a tagged int and faults on `tmp ^ ".cnf"`.
        67 => fs_tmp_name(ctx),
        // 19: seek-to-position — unimplemented. A tagged(0) made seeks
        // silent no-ops (position-dependent IO silently corrupted), so it
        // raises instead. NB 18/20 (position READS) keep their tagged(0):
        // the stage-0 REPL queries stream position at startup, so raising
        // there breaks the byte-identical bootstrap (measured: −71 steps).
        19 => syserr_unimpl(ctx, "stream seek (setPos)"),
        // Various stub returns of TAGGED(0):
        //   17: bytes available
        //   18: get stream position (REPL-load-bearing, see above)
        //   20: end-of-stream position (ditto)
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
///
/// UNTRUSTED MODE (task #96, HOLE 5): `w` is an IMAGE-CONTROLLED IntInf arg;
/// the boxed branch reads its length word at `p.sub(1)` (a deref BEFORE any
/// shape check). The deref is gated by [`safe_rts_arg_ptr`] on `spaces` (None
/// in trusted mode -> byte-identical; a wild/non-member arg -> `None`, which
/// every caller turns into a clean tagged(0) / Div-handled result).
fn poly_word_to_bigint(spaces: Option<&RtsSafeSpaces>, w: PolyWord) -> Option<BigInt> {
    if w.is_tagged() {
        return Some(BigInt::from(w.untag()));
    }
    // Header-fit gate: in untrusted mode this validates that the WHOLE boxed
    // bignum object fits its space, so the variable-length limb read below is
    // bounded (trusted: is_data_ptr only, n_words == MAX — byte-identical).
    let obj = safe_rts_arg_obj(spaces, w)?;
    let p = obj.ptr;
    // SAFETY: trusted (is_data_ptr) OR untrusted-validated in-space object.
    let lw = unsafe { crate::space::MemorySpace::length_word_of(p) };
    let flags = crate::length_word::flags_of(lw);
    // Bound the limb count by the validated handle: the gate proved
    // [p, p+n_words) fits the space, so reading n_words*8 bytes is in-bounds.
    let n_words = obj.clamp_body_words(crate::length_word::length_of(lw));
    let sign = if flags & crate::length_word::F_NEGATIVE_BIT != 0 {
        Sign::Minus
    } else {
        Sign::Plus
    };
    // SAFETY: body is n_words words = n_words * 8 bytes, bounded to the space.
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
    let p = space.alloc_or_exit(n_words);
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

/// Shared body for the bignum-aware ARB_* fallbacks. Untags `y` then `x`
/// to BigInts (mirroring upstream `bytecode.cpp`'s peek-then-pop operand
/// order — `y` is the peek, `x` the pop), applies `op`, and re-tags the
/// result. The closure is monomorphized per call site (no dynamic
/// dispatch), and this is the slow boxed-overflow path, not the tagged
/// fast path.
fn arb_via_bigint(
    spaces: Option<&RtsSafeSpaces>,
    alloc: Option<&mut crate::space::MemorySpace>,
    x: PolyWord,
    y: PolyWord,
    op: impl FnOnce(BigInt, BigInt) -> BigInt,
) -> PolyWord {
    let (Some(a), Some(b)) = (
        poly_word_to_bigint(spaces, y),
        poly_word_to_bigint(spaces, x),
    ) else {
        return PolyWord::tagged(0);
    };
    let mut ctx = RtsContext {
        alloc_space: alloc,
        raised_exception: None,
        rts: None,
        bootstrap_tail_call: PolyWord::ZERO,
        safe_spaces: None,
    };
    bigint_to_poly_word(&mut ctx, &op(a, b))
}

/// Bignum-aware ARB_ADD.
///
/// Called from the interpreter when the fast path overflows or
/// one operand is already boxed. Computes `y + x` (matching
/// upstream `bytecode.cpp:1077` `INSTR_arbAdd` where y is the
/// peek and x is the pop).
pub fn arb_add_via_bigint(
    spaces: Option<&RtsSafeSpaces>,
    alloc: Option<&mut crate::space::MemorySpace>,
    x: PolyWord,
    y: PolyWord,
) -> PolyWord {
    arb_via_bigint(spaces, alloc, x, y, |a, b| a + b)
}

pub fn arb_sub_via_bigint(
    spaces: Option<&RtsSafeSpaces>,
    alloc: Option<&mut crate::space::MemorySpace>,
    x: PolyWord,
    y: PolyWord,
) -> PolyWord {
    arb_via_bigint(spaces, alloc, x, y, |a, b| a - b)
}

pub fn arb_mult_via_bigint(
    spaces: Option<&RtsSafeSpaces>,
    alloc: Option<&mut crate::space::MemorySpace>,
    x: PolyWord,
    y: PolyWord,
) -> PolyWord {
    arb_via_bigint(spaces, alloc, x, y, |a, b| a * b)
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
    let (Some(a), Some(b)) = (
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg2),
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg1),
    ) else {
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
    // Subtraction is NOT commutative. Upstream PolySubtractArbitrary(arg1, arg2)
    // computes arg1 - arg2: sub_longc(taskData, pushedArg2, pushedArg1) returns
    // x - y = pushedArg1 - pushedArg2 (arb.cpp:907/1702). Since `arb_binop(P1, P2,
    // op)` computes op(P2, P1), we must pass (arg2, arg1) to get arg1 - arg2.
    // Passing (arg1, arg2) computed arg2 - arg1 — the NEGATION — a real bug found
    // by upstream Tests/Succeed/Test101.ML (the RTS path; the bytecode opcode
    // arb_sub_pair was already correct). add/mult are commutative so their order
    // is irrelevant; div/rem hand-roll the order below.
    arb_binop(ctx, arg2, arg1, i128::checked_sub, |a, b| a - b)
}

#[allow(clippy::needless_pass_by_value)]
fn poly_multiply_arbitrary(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg1: PolyWord,
    arg2: PolyWord,
) -> PolyWord {
    // Mult needs the bigint path because SML's `maxShort` loop
    // multiplies until overflow and uses `largeIntIsSmall` on the
    // result — without a boxed result, that loop never terminates.
    arb_binop(ctx, arg1, arg2, i128::checked_mul, |a, b| a * b)
}

/// Set the pending `Div` exception on the RTS context and return a placeholder
/// (the dispatcher raises `ctx.raised_exception` and ignores the return value).
/// The bignum div/mod RTS uses this on a zero divisor so `handle Div` works —
/// previously they returned TAGGED(0), which crashed the interpreter when the
/// SML side read it as a result tuple.
fn raise_div(ctx: &mut RtsContext<'_>) -> PolyWord {
    let packet = make_div_exception(ctx);
    ctx.raised_exception = Some(packet);
    PolyWord::tagged(0)
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
            return raise_div(ctx);
        }
        if !(dvd == MIN_TAGGED && dvdr == -1) {
            return PolyWord::tagged(dvd / dvdr);
        }
        // Fall through to bigint for MIN_TAGGED / -1 overflow.
    }
    let (Some(a), Some(b)) = (
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg1),
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg2),
    ) else {
        return PolyWord::tagged(0);
    };
    if b == BigInt::from(0) {
        return raise_div(ctx);
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
            return raise_div(ctx);
        }
        if !(dvd == MIN_TAGGED && dvdr == -1) {
            return PolyWord::tagged(dvd % dvdr);
        }
    }
    let (Some(a), Some(b)) = (
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg1),
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg2),
    ) else {
        return PolyWord::tagged(0);
    };
    if b == BigInt::from(0) {
        return raise_div(ctx);
    }
    bigint_to_poly_word(ctx, &(a % b))
}

#[allow(clippy::needless_pass_by_value)]
fn poly_compare_arbitrary(ctx: &mut RtsContext<'_>, arg1: PolyWord, arg2: PolyWord) -> PolyWord {
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
    let ord = match (
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg1),
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg2),
    ) {
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
fn poly_or_arbitrary(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg1: PolyWord,
    arg2: PolyWord,
) -> PolyWord {
    if both_tagged(arg1, arg2).is_some() {
        return PolyWord::from_bits(arg1.0 | arg2.0);
    }
    match (
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg1),
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg2),
    ) {
        (Some(a), Some(b)) => bigint_to_poly_word(ctx, &(a | b)),
        _ => PolyWord::tagged(0),
    }
}

fn poly_and_arbitrary(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg1: PolyWord,
    arg2: PolyWord,
) -> PolyWord {
    if both_tagged(arg1, arg2).is_some() {
        return PolyWord::from_bits(arg1.0 & arg2.0);
    }
    match (
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg1),
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg2),
    ) {
        (Some(a), Some(b)) => bigint_to_poly_word(ctx, &(a & b)),
        _ => PolyWord::tagged(0),
    }
}

fn poly_xor_arbitrary(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg1: PolyWord,
    arg2: PolyWord,
) -> PolyWord {
    if both_tagged(arg1, arg2).is_some() {
        // XOR cancels the tag bits → set it back.
        return PolyWord::from_bits((arg1.0 ^ arg2.0) | 1);
    }
    match (
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg1),
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg2),
    ) {
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
    let Some(n) = poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg) else {
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
    let Some(n) = poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg) else {
        return PolyWord::tagged(0);
    };
    #[allow(clippy::cast_sign_loss)]
    let r = n >> (by as usize);
    bigint_to_poly_word(ctx, &r)
}

/// GCD with an i64 tagged fast path and a BigInt fallback for boxed operands
/// (arb.cpp:1864-1904). The old tagged-only impl returned 0 for any boxed input.
#[allow(clippy::needless_pass_by_value)]
fn poly_gcd_arbitrary(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg1: PolyWord,
    arg2: PolyWord,
) -> PolyWord {
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
    match (
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg1),
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg2),
    ) {
        (Some(a), Some(b)) => bigint_to_poly_word(ctx, &a.gcd(&b)),
        _ => PolyWord::tagged(0),
    }
}

/// LCM, with upstream's SIGNED convention. Upstream `lcm_arbitrary`
/// (arb.cpp:1671-1675) is `mult_longc(x, div_longc(gcd, y)) = x * (y / gcd)`
/// computed with SIGNED multiply/divide, so the result sign is
/// `sign(x) * sign(y)` (NOT the absolute value).  Differential fuzz vs upstream
/// (fuzz_core_rts_only_rts.sml, 2026-06-20) caught ours returning the absolute
/// value for mixed-sign operands: `lcm(-6,4)` should be -12, not 12.
/// `lcm(x, 0) = lcm(0, y) = 0`.  Tagged fast path stays SIGNED; falls through to
/// the BigInt path on tagged overflow.  Matches `num_integer`'s `lcm` only in
/// magnitude — we restore the sign explicitly.
#[allow(clippy::needless_pass_by_value)]
fn poly_lcm_arbitrary(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg1: PolyWord,
    arg2: PolyWord,
) -> PolyWord {
    use num_bigint::Sign;
    use num_integer::Integer;
    if let Some((x, y)) = both_tagged(arg2, arg1) {
        // Upstream lcm = x*(y/gcd); gcd(0,0)=0 so lcm(0,0) divides by zero → Div.
        // A single zero gives 0 (y/gcd = 0). (arb.cpp:1671-1675, div_longc raises Div.)
        if x == 0 && y == 0 {
            return raise_div(ctx);
        }
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
        // Both x and y are nonzero here, so g = gcd(|x|,|y|) >= 1.
        let g = a;
        // On overflow of the |lcm| product or the tagged range, DON'T return 0 —
        // fall through to the BigInt path, which computes the full (possibly
        // boxed) result.  (Earlier this path `return`ed tagged(0), silently
        // truncating large lcms to 0 — caught by fuzz_core_rts_only_rts.sml.)
        if let Some(mag) = (orig_a / g).checked_mul(orig_b) {
            #[allow(clippy::cast_sign_loss)]
            let max = isize::MAX as usize;
            if mag <= max {
                // Signed result: sign = sign(x) * sign(y) (both nonzero here).
                let negate = (x < 0) != (y < 0);
                #[allow(clippy::cast_possible_wrap)]
                let v = if negate {
                    -(mag as isize)
                } else {
                    mag as isize
                };
                if fits_tagged(v as i128) {
                    return PolyWord::tagged(v);
                }
            }
        }
        // overflow: fall through to BigInt.
    }
    // BigInt fallback: compute |lcm| then restore the signed convention.
    match (
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg1),
        poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg2),
    ) {
        (Some(a), Some(b)) => {
            let mut l = a.lcm(&b); // non-negative magnitude
            // sign(arg1) * sign(arg2): negate iff exactly one operand is negative.
            let neg = (a.sign() == Sign::Minus) != (b.sign() == Sign::Minus);
            if neg && l.sign() != Sign::NoSign {
                l = -l;
            }
            bigint_to_poly_word(ctx, &l)
        }
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
            return raise_div(ctx);
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
        let (Some(a), Some(b)) = (
            poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg1),
            poly_word_to_bigint(ctx.safe_spaces.as_ref(), arg2),
        ) else {
            return PolyWord::tagged(0);
        };
        // Zero divisor with a boxed dividend (e.g. divMod(2^70, 0)) — raise Div.
        if b == BigInt::from(0) {
            return raise_div(ctx);
        }
        let q = bigint_to_poly_word(ctx, &(&a / &b));
        let r = bigint_to_poly_word(ctx, &(&a % &b));
        (q, r)
    };
    // Allocate a 2-word ordinary object holding (q, r).
    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::tagged(0);
    };
    let p = space.alloc_or_exit(2);
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
    } else if let Some(p) = safe_rts_arg_ptr(ctx.safe_spaces.as_ref(), arg) {
        // Boxed: read first body word as the low limb of the MAGNITUDE.
        // Bignums are sign-magnitude, so for a negative-flagged object the
        // two's-complement low word is `0 - low` (arb.cpp:1936 `if(negative) p=0-p`).
        // UNTRUSTED MODE (task #96, HOLE 5): the boxed deref is gated above.
        // SAFETY: p space-validated (untrusted) / is_data_ptr (trusted).
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
    let p = space.alloc_or_exit(1);
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
    use crate::length_word::{F_CODE_OBJ, F_MUTABLE_BIT, flags_of, is_byte_object, length_of};
    // UNTRUSTED MODE (task #96, HOLE 5): byte_vec + closure are
    // image-controlled args whose length words are read below; gate both first
    // derefs on space-membership (None in trusted -> byte-identical).
    let spaces = ctx.safe_spaces.as_ref();
    // Header-fit gate: in untrusted mode this validates that BOTH the byte
    // vector and the closure objects fit their spaces, so the wholesale body
    // copy below is bounded (trusted: is_data_ptr only — byte-identical).
    let (Some(bv_obj), Some(cl_obj)) = (
        safe_rts_arg_obj(spaces, byte_vec),
        safe_rts_arg_obj(spaces, closure),
    ) else {
        if RTS_TRACE.load(Ordering::Relaxed) {
            eprintln!(
                "  PolyCopyByteVecToClosure: non-pointer / out-of-space arg(s)? byte_vec={byte_vec:?}, closure={closure:?}"
            );
        }
        return PolyWord::tagged(0);
    };
    let bv_ptr = bv_obj.ptr;
    let cl_ptr = cl_obj.ptr.cast_mut();
    // SAFETY: bv_ptr/cl_ptr space-validated (untrusted) / is_data_ptr (trusted).
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
        // Bound the body word count copied below by the validated handle: the
        // gate proved [bv_ptr, bv_ptr+n_words) fits the byte vector's space.
        let n_words = bv_obj.clamp_body_words(length_of(bv_len_word));

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
        let dst = space.alloc_or_exit(n_words);
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
    ctx: &mut RtsContext<'_>,
    closure: PolyWord,
    offset: PolyWord,
    c_word: PolyWord,
    flags: PolyWord,
) -> PolyWord {
    use crate::length_word::{is_code_object, length_of};
    if !closure.is_data_ptr() {
        return PolyWord::tagged(0);
    }
    // Closure may be either a code object directly or a closure whose
    // slot 0 points at one.
    let cl_ptr = closure.as_ptr::<PolyWord>();
    // UNTRUSTED MODE (R1): before reading cl_ptr's length word, confirm it
    // lies inside a live space (else a wild closure pointer would OOB-read
    // the length word). `safe_spaces` is None in trusted mode → skipped,
    // byte-identical.
    if let Some(spaces) = &ctx.safe_spaces
        && !spaces.contains_with_header(cl_ptr)
    {
        return PolyWord::tagged(0);
    }
    // SAFETY: caller trusted (or cl_ptr validated in-space above).
    // `code_obj` is the PolyWord-pointer to the code object's body;
    // `start_code` is the same address as a byte pointer. We derive the
    // code object's byte length from its own length word so the offset
    // can be bounds-checked below.
    let (start_code, code_byte_len): (*mut u8, usize) = unsafe {
        let lw = crate::space::MemorySpace::length_word_of(cl_ptr);
        if is_code_object(lw) {
            (
                cl_ptr as *mut u8,
                length_of(lw) * std::mem::size_of::<PolyWord>(),
            )
        } else {
            // closure[0] is the code-object pointer
            let code_word = *cl_ptr;
            if !code_word.is_data_ptr() {
                return PolyWord::tagged(0);
            }
            let code_obj = code_word.as_ptr::<PolyWord>();
            // UNTRUSTED MODE (R1): validate the resolved code object is
            // in-space BEFORE reading its length word.
            if let Some(spaces) = &ctx.safe_spaces
                && !spaces.contains_with_header(code_obj)
            {
                return PolyWord::tagged(0);
            }
            let clw = crate::space::MemorySpace::length_word_of(code_obj);
            // R1 FIX (unsafe-audit, task #96): the resolved target MUST be a
            // CODE object before we treat its length word as a code-byte
            // length and write into it. Without this, a corrupted/untrusted
            // image whose closure word0 points at a wrong-type (or wild)
            // object turns this into an OOB / wrong-type WRITE — the
            // highest-value corruption primitive (the R1 reachable OOB-write
            // the unsafe-audit flagged). The compiler always passes a real
            // code object, so this guard never rejects a legitimate call.
            if !is_code_object(clw) {
                if RTS_TRACE.load(Ordering::Relaxed) {
                    eprintln!(
                        "  PolySetCodeConstant: closure word0 is not a code object (rejected)"
                    );
                }
                return PolyWord::tagged(0);
            }
            (
                code_word.as_ptr::<u8>().cast_mut(),
                length_of(clw) * std::mem::size_of::<PolyWord>(),
            )
        }
    };
    #[allow(clippy::cast_sign_loss)]
    let off = offset.untag() as usize;
    let flag_kind = flags.untag();
    // BOUNDS CHECK (unsafe-audit finding #9): the compiler emits
    // in-bounds offsets, but a corrupted/adversarial image could drive
    // an out-of-range `off`, turning this into an OOB heap write into a
    // code object (the highest-value corruption target). Reject any
    // write whose target window [off, off+width) would fall outside the
    // code object's own body. Upstream PolyML trusts the offset; we add
    // this guard because `poly run` accepts untrusted images.
    let write_width = match flag_kind {
        0 | 2 => std::mem::size_of::<usize>(),
        // Unsupported native-code relocation cases write nothing below.
        _ => 0,
    };
    if write_width != 0 && (off > code_byte_len || off + write_width > code_byte_len) {
        if RTS_TRACE.load(Ordering::Relaxed) {
            eprintln!(
                "  PolySetCodeConstant: out-of-range offset {off} (+{write_width}) \
                 for code object of {code_byte_len} bytes (rejected)"
            );
        }
        return PolyWord::tagged(0);
    }
    // SAFETY: code-segment write into freshly-allocated mutable space;
    // the offset is now bounds-checked against the code object body.
    unsafe {
        let instr_addr = start_code.add(off);
        match flag_kind {
            0 | 2 => {
                // Absolute PolyWord-sized constant (case 0) or
                // uintptr_t-sized (case 2 — same on 64-bit).
                // NATIVE byte order: this constant is read back as a native
                // PolyWord (`read_unaligned`, mod.rs), so it must be stored in
                // the host's word byte order. `to_ne_bytes` == `to_le_bytes` on
                // little-endian (byte-identical) and is correct on big-endian.
                let bytes = c_word.0.to_ne_bytes();
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
                    eprintln!("  PolySetCodeConstant: unsupported flag {flag_kind} (skipped)");
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
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    closure: PolyWord,
) -> PolyWord {
    use crate::length_word::{F_CODE_OBJ, length_of};
    if !closure.is_data_ptr() {
        return PolyWord::tagged(0);
    }
    let cl_ptr = closure.as_ptr::<PolyWord>();
    // UNTRUSTED MODE: cl_ptr must be in-space before reading its word0.
    if let Some(spaces) = &ctx.safe_spaces
        && !spaces.contains_with_header(cl_ptr)
    {
        return PolyWord::tagged(0);
    }
    // SAFETY: caller trusted (or cl_ptr validated in-space above).
    unsafe {
        let code_word = *cl_ptr;
        if !code_word.is_data_ptr() {
            return PolyWord::tagged(0);
        }
        let code_obj = code_word.as_ptr::<PolyWord>().cast_mut();
        // UNTRUSTED MODE: validate the resolved code object in-space before
        // reading its length word.
        if let Some(spaces) = &ctx.safe_spaces
            && !spaces.contains_with_header(code_obj)
        {
            return PolyWord::tagged(0);
        }
        let lw = crate::space::MemorySpace::length_word_of(code_obj);
        // R1 sibling (D29): the resolved target must ALREADY be a code
        // object before we rewrite its length word as F_CODE_OBJ — else a
        // corrupt image could clear/forge the flags of a wrong-type object.
        if !crate::length_word::is_code_object(lw) {
            if RTS_TRACE.load(Ordering::Relaxed) {
                eprintln!("  PolyLockMutableClosure: word0 is not a code object (rejected)");
            }
            return PolyWord::tagged(0);
        }
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
    ctx: &mut RtsContext<'_>,
    closure: PolyWord,
    offset: PolyWord,
    byte_val: PolyWord,
) -> PolyWord {
    if !closure.is_data_ptr() {
        return PolyWord::tagged(0);
    }
    let cl_ptr = closure.as_ptr::<PolyWord>();
    // UNTRUSTED MODE: cl_ptr must be in-space before reading word0.
    if let Some(spaces) = &ctx.safe_spaces
        && !spaces.contains_with_header(cl_ptr)
    {
        return PolyWord::tagged(0);
    }
    // SAFETY: caller (compiler-generated bytecode) is trusted (or cl_ptr
    // validated in-space above).
    unsafe {
        let code_word = *cl_ptr;
        if !code_word.is_data_ptr() {
            return PolyWord::tagged(0);
        }
        let code_obj = code_word.as_ptr::<PolyWord>();
        // UNTRUSTED MODE: resolved code object must be in-space.
        if let Some(spaces) = &ctx.safe_spaces
            && !spaces.contains_with_header(code_obj)
        {
            return PolyWord::tagged(0);
        }
        let clw = crate::space::MemorySpace::length_word_of(code_obj);
        // R1 sibling (D10): the resolved target must be a code object before
        // we write into it (else a wrong-type/wild WRITE on a corrupt image).
        if !crate::length_word::is_code_object(clw) {
            if RTS_TRACE.load(Ordering::Relaxed) {
                eprintln!("  PolySetCodeByte: closure word0 is not a code object (rejected)");
            }
            return PolyWord::tagged(0);
        }
        let code_byte_len = crate::length_word::length_of(clw) * std::mem::size_of::<PolyWord>();
        let code_ptr = code_word.as_ptr::<u8>().cast_mut();
        let off = offset.untag() as usize;
        // BOUNDS CHECK (unsafe-audit finding #9): reject an out-of-range
        // single-byte write into the code object. See poly_set_code_constant.
        if off >= code_byte_len {
            if RTS_TRACE.load(Ordering::Relaxed) {
                eprintln!(
                    "  PolySetCodeByte: out-of-range offset {off} for code object \
                     of {code_byte_len} bytes (rejected)"
                );
            }
            return PolyWord::tagged(0);
        }
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
    ctx: &mut RtsContext<'_>,
    closure: PolyWord,
    offset: PolyWord,
    _flags: PolyWord,
) -> PolyWord {
    if !closure.is_data_ptr() {
        return PolyWord::tagged(0);
    }
    let cl_ptr = closure.as_ptr::<PolyWord>();
    // UNTRUSTED MODE: cl_ptr must be in-space before reading word0.
    if let Some(spaces) = &ctx.safe_spaces
        && !spaces.contains_with_header(cl_ptr)
    {
        return PolyWord::tagged(0);
    }
    // SAFETY: caller trusted (or cl_ptr validated in-space above).
    unsafe {
        let code_word = *cl_ptr;
        if !code_word.is_data_ptr() {
            return PolyWord::tagged(0);
        }
        let code_obj = code_word.as_ptr::<PolyWord>();
        // UNTRUSTED MODE: resolved code object must be in-space.
        if let Some(spaces) = &ctx.safe_spaces
            && !spaces.contains_with_header(code_obj)
        {
            return PolyWord::tagged(0);
        }
        let clw = crate::space::MemorySpace::length_word_of(code_obj);
        // R1 sibling (D28): the resolved target must be a code object before
        // we read from it as one (else a wrong-type / wild OOB READ).
        if !crate::length_word::is_code_object(clw) {
            return PolyWord::tagged(0);
        }
        let code_byte_len = crate::length_word::length_of(clw) * std::mem::size_of::<PolyWord>();
        let code_ptr = code_word.as_ptr::<u8>();
        let off = offset.untag() as usize;
        // BOUNDS CHECK (unsafe-audit finding #9, read sibling): reject an
        // out-of-range PolyWord-sized read past the code object body. This
        // getter is debug-only upstream, but an out-of-range offset from a
        // corrupted image is still an OOB over-read (info leak / SIGSEGV).
        if off > code_byte_len || off + std::mem::size_of::<PolyWord>() > code_byte_len {
            return PolyWord::tagged(0);
        }
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
    // HOLE 5: `arg` is the image-controlled real arg; gate via the helper.
    let v: f64 = read_real_word(ctx.safe_spaces.as_ref(), arg);
    let kind_ch = if kind.is_tagged() {
        u32::try_from(kind.untag())
            .ok()
            .and_then(char::from_u32)
            .unwrap_or('G')
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
///
/// UNTRUSTED MODE (task #96, HOLE 5): `x` is the IMAGE-CONTROLLED RTS arg of
/// every Real op (sqrt/sin/.../atan2/pow/copysign/rem/nextafter — ~30 regs);
/// a wild-but-aligned arg is an 8-byte OOB read -> SEGV. The deref is gated by
/// [`safe_rts_arg_ptr`] on `spaces` (None in trusted mode -> byte-identical;
/// a non-member pointer -> the 0.0 non-pointer branch).
fn read_real_word(spaces: Option<&RtsSafeSpaces>, x: PolyWord) -> f64 {
    if let Some(p) = safe_rts_arg_ptr(spaces, x) {
        // SAFETY: trusted (is_data_ptr) OR untrusted-validated in-space object.
        unsafe { *p.cast::<f64>() }
    } else {
        0.0
    }
}

/// Read a `PolyWord` argument as an `f32` under the 64-bit *tagged* Real32
/// representation: the f32 bit pattern lives in the high 32 bits and the low
/// bit is the tag. Mirrors upstream `float_arg` (reals.cpp:206-211,
/// FLT_SHIFT=32) and the interpreter's `unbox_float` (mod.rs): arithmetic
/// right-shift by 32 (sign-extending), then reinterpret the low 32 bits as f32.
#[allow(clippy::cast_possible_truncation)]
fn read_f32_tagged(x: PolyWord) -> f32 {
    #[cfg(target_pointer_width = "64")]
    {
        let i = ((x.0 as isize) >> 32) as i32;
        return f32::from_bits(i as u32);
    }
    // Real32 is boxed (not tagged) on 32-bit hosts — see `unbox_float`
    // (interpreter/mod.rs). Boxed-Real32 path not yet ported (task #120).
    #[cfg(not(target_pointer_width = "64"))]
    {
        let _ = x;
        unimplemented!("boxed Real32 on 32-bit hosts not yet ported (task #120)")
    }
}

/// Box an `f32` result of a Real32 RTS call as a boxed Real (1-word
/// F_BYTE_OBJ holding the value widened to f64). The typed fast-call path
/// (`dispatch_typed_fast_call`, mod.rs) reads this back as f64 and
/// `call_fast_f_to_f` narrows `as f32` + re-tags via `box_float`. The
/// f32->f64->f32 round-trip is lossless. Helper exists so the F-variant
/// registrations read clearly; it just defers to `box_real`.
fn box_f32_tagged(ctx: &mut RtsContext<'_>, v: f32) -> PolyWord {
    box_real(ctx, f64::from(v))
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
    let next = if (y > x) == (x > 0.0) {
        bits + 1
    } else {
        bits - 1
    };
    f64::from_bits(next)
}

/// IEEE-754 `nextafterf(x, y)` for f32 (mirrors `next_after` for f64).
/// Rust std has no stable f32 next_after, so walk the bit pattern.
fn next_after_f32(x: f32, y: f32) -> f32 {
    if x.is_nan() || y.is_nan() {
        return f32::NAN;
    }
    if x == y {
        return y;
    }
    if x == 0.0 {
        // Smallest subnormal toward y.
        return f32::from_bits(1).copysign(y);
    }
    let bits = x.to_bits();
    let next = if (y > x) == (x > 0.0) {
        bits + 1
    } else {
        bits - 1
    };
    f32::from_bits(next)
}

/// f32 power with PolyML's special cases (reals.cpp:536-558 PolyRealFPow):
/// nan base -> 1.0 if exp==0 else nan; nan exp -> exp; x==0 && y<0 ->
/// +inf, or -inf when x is -0.0 and y is an odd integer; else powf.
fn real_f_pow(x: f32, y: f32) -> f32 {
    if x.is_nan() {
        return if y == 0.0 { 1.0 } else { f32::NAN };
    }
    if y.is_nan() {
        return y;
    }
    if x == 0.0 && y < 0.0 {
        #[allow(clippy::cast_possible_truncation)]
        let iy = y.floor() as i64;
        #[allow(clippy::cast_precision_loss)]
        if 1.0f32.copysign(x) < 0.0 && (iy as f32) == y && (iy & 1) != 0 {
            return f32::NEG_INFINITY;
        }
        return f32::INFINITY;
    }
    x.powf(y)
}

/// Round-to-nearest-integral matching upstream `PolyRealRound`
/// (reals.cpp:350-359) BIT-FOR-BIT, including the sign of a zero result.
///
/// Upstream does NOT use C99 `rint`/`round_ties_even`: it computes
/// `drem = fmod(arg, 2.0)` and for the exact half-way ties that should round
/// toward even (`drem == 0.5` i.e. positive-even+0.5, or `drem == -1.5` i.e.
/// negative-odd-0.5) returns `ceil(arg - 0.5)`, otherwise `floor(arg + 0.5)`.
/// This produces round-half-to-EVEN magnitudes (identical to
/// `round_ties_even`) BUT — crucially — for any `arg` in `(-0.5, 0]` the
/// `floor(arg + 0.5)` branch yields `+0.0`, whereas `round_ties_even`
/// preserves the negative sign and yields `-0.0`. The sign-of-zero is
/// observable (`Real.signBit`, `Real.toString` "~0.0"), so to stay faithful
/// to the upstream oracle we replicate the exact algorithm. See the REAL32
/// RTS differential fuzz finding (tools/diff-corpus/fuzz_real32_rts.sml).
// The exact `== 0.5` / `== -1.5` comparison is load-bearing: it reproduces
// upstream's exact half-way-tie branch (reals.cpp:350-359). An epsilon
// comparison would change which inputs take the ceil(arg-0.5) vs
// floor(arg+0.5) branch and break bit-for-bit faithfulness.
#[allow(clippy::float_cmp)]
fn poly_real_round_f64(arg: f64) -> f64 {
    let drem = arg % 2.0;
    if drem == 0.5 || drem == -1.5 {
        (arg - 0.5).ceil()
    } else {
        (arg + 0.5).floor()
    }
}

/// Round-to-nearest-integral matching upstream `PolyRealFRound`
/// (reals.cpp:577-586) BIT-FOR-BIT — the f32 analogue of
/// [`poly_real_round_f64`]. Same `fmodf`/`floorf(x+0.5)` algorithm, same
/// `+0.0` sign for `arg` in `(-0.5, 0]`.
// Exact tie comparison is load-bearing — see poly_real_round_f64.
#[allow(clippy::float_cmp)]
fn poly_real_round_f32(arg: f32) -> f32 {
    let drem = arg % 2.0;
    if drem == 0.5 || drem == -1.5 {
        (arg - 0.5).ceil()
    } else {
        (arg + 0.5).floor()
    }
}

/// Box an `f64` as a PolyML Real (1-word byte object).
fn box_real(ctx: &mut RtsContext<'_>, v: f64) -> PolyWord {
    use crate::length_word::F_BYTE_OBJ;
    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::tagged(0);
    };
    let p = space.alloc_or_exit(1);
    // SAFETY: just allocated 1 word.
    unsafe {
        crate::space::set_length_word(p, 1, F_BYTE_OBJ);
        p.cast::<f64>().write(v);
    }
    PolyWord::from_ptr(p.cast_const())
}

fn poly_real_frexp(ctx: &mut RtsContext<'_>, _tid: PolyWord, x: PolyWord) -> PolyWord {
    use crate::length_word::F_BYTE_OBJ;
    // HOLE 5 (the prompt's named PoC): `x` is the image-controlled real arg;
    // gate its deref through the misuse-resistant helper (None in trusted ->
    // byte-identical; a wild/non-member arg -> the 0.0 branch).
    let v: f64 = read_real_word(ctx.safe_spaces.as_ref(), x);
    // Rust doesn't have built-in frexp; use the standard
    // decomposition via integer bit pattern manipulation.
    let (mantissa, exponent) = frexp_f64(v);

    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::tagged(0);
    };
    // Allocate the mantissa (boxed Real, 1 word).
    let m_ptr = space.alloc_or_exit(1);
    // SAFETY: just allocated 1 word.
    unsafe {
        crate::space::set_length_word(m_ptr, 1, F_BYTE_OBJ);
        m_ptr.cast::<f64>().write(mantissa);
    }
    // Allocate the tuple: 2 words, ordinary object.
    let t_ptr = space.alloc_or_exit(2);
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
    let p = space.alloc_or_exit(length);
    // SAFETY: just allocated 9 words
    unsafe {
        crate::space::set_length_word(p, length, F_MUTABLE_BIT);
        p.add(0).write(PolyWord::tagged(0)); // threadRef (dummy)
        p.add(1).write(PolyWord::tagged(2)); // flags = PFLAG_SYNCH
        p.add(2).write(PolyWord::tagged(0)); // threadLocal = nil
        p.add(3).write(PolyWord::tagged(0)); // requestCopy = none
        p.add(4).write(PolyWord::tagged(0)); // mlStackSize = unlimited
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
fn write_array(spaces: Option<&RtsSafeSpaces>, strm: PolyWord, arg: PolyWord) -> PolyWord {
    // Best-effort fd extraction. `strm` is conventionally a
    // wrapped-fd object (see `wrap_file_descriptor`): a 1-word byte
    // object holding `fd + 1`.
    // UNTRUSTED MODE (task #96/#132): `strm` and `arg` are image-controlled IO
    // args. `strm` is a single-word wrapped-fd read (safe_rts_arg_ptr); `arg`
    // is a 3-tuple read at p[0..3], so gate it on header-fit and bound the 3
    // word reads on its validated length.
    let (Some(strm_p), Some(arg_obj)) = (
        safe_rts_arg_ptr(spaces, strm),
        safe_rts_arg_obj(spaces, arg),
    ) else {
        return PolyWord::tagged(0);
    };
    // SAFETY: trusted (is_data_ptr) OR untrusted-validated in-space object.
    let fd_plus_one = unsafe { *strm_p }.0;
    if fd_plus_one == 0 {
        return PolyWord::tagged(0);
    }
    // arg shape: 3-tuple (vec, offset, length). Bound the three word reads on
    // the validated arg length (trusted: always passes — byte-identical).
    if !arg_obj.word_in_bounds(2) {
        return PolyWord::tagged(0);
    }
    let p = arg_obj.ptr;
    // SAFETY: arg has >= 3 body words (untrusted) / is_data_ptr (trusted).
    let (vec, offset, length) = unsafe { (*p, *p.add(1), *p.add(2)) };
    if !offset.is_tagged() || !length.is_tagged() {
        return PolyWord::tagged(0);
    }
    // UNTRUSTED MODE: `vec` is image-controlled; gate its deref on header-fit
    // so the body-size bound below is sound (not derived from a forged header).
    let Some(vec_obj) = safe_rts_arg_obj(spaces, vec) else {
        return PolyWord::tagged(0);
    };
    let vec_p = vec_obj.ptr;
    #[allow(clippy::cast_sign_loss)]
    let off = offset.untag() as usize;
    #[allow(clippy::cast_sign_loss)]
    let len = length.untag() as usize;
    if len == 0 {
        return PolyWord::tagged(0);
    }
    // Defence-in-depth (unsafe-audit finding #6): the trusted basis
    // (`LibraryIOSupport.writeArray`) always sends an in-bounds
    // (vec, offset, length) derived from a slice bounds-checked at
    // creation, so type-safe SML never trips this. A corrupted image (or
    // hostile `RunCall.rtsCallFull3 "PolyBasicIOGeneral"` + `unsafeCast`)
    // could forge `length` far larger than `vec`'s byte body, causing
    // `from_raw_parts(base.add(off), len)` to over-read past the object.
    // Verify vec is a byte object and `off + len` fits its body before the
    // unsafe slice; on violation return the existing "wrote nothing" stub.
    {
        use crate::length_word::{is_byte_object, length_of};
        // SAFETY: vec_p is space-validated (untrusted) / is_data_ptr (trusted),
        // so vec-1 is a readable length word.
        let lw = unsafe { crate::space::MemorySpace::length_word_of(vec_p) };
        // Bound the body size by the validated handle: in untrusted mode the
        // gate proved [vec_p, vec_p+n_words) fits the space, so `body_bytes` is
        // a SOUND upper bound (trusted: n_words == MAX — byte-identical).
        let body_bytes = vec_obj
            .clamp_body_words(length_of(lw))
            .saturating_mul(std::mem::size_of::<usize>());
        if !is_byte_object(lw) || off.checked_add(len).is_none_or(|end| end > body_bytes) {
            return PolyWord::tagged(0);
        }
    }
    // SAFETY: vec is a byte object and `off + len <= body_bytes` was just
    // verified, so reading off..off+len bytes of its body is in-bounds.
    let base = vec_p.cast::<u8>();
    let slice = unsafe { std::slice::from_raw_parts(base.add(off), len) };
    // Route via std::io for fds 1/2; write real files via their fd.
    #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
    let fd = (fd_plus_one - 1) as i32;
    let n = match fd {
        1 => retry_eintr_write(&mut std::io::stdout(), slice),
        2 => retry_eintr_write(&mut std::io::stderr(), slice),
        0 => Ok(0),
        _ => {
            use std::os::fd::FromRawFd;
            // SAFETY: fd is a live fd opened by open_file_output. We
            // reconstruct a File to call write, then leak it back via
            // into_raw_fd so Drop does NOT close the still-in-use fd.
            let mut f = unsafe { std::fs::File::from_raw_fd(fd) };
            let n = retry_eintr_write(&mut f, slice);
            use std::os::fd::IntoRawFd;
            let _ = f.into_raw_fd();
            n
        }
    };
    match n {
        #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
        Ok(n) => PolyWord::tagged(n as isize),
        // A real write error. Reporting "0 bytes written" here (the old
        // behaviour) livelocks the basis write-all loop on persistent
        // EPIPE/ENOSPC. The dispatcher turns this sentinel into
        // SysErr("Error while writing", errno) — upstream basicio.cpp:363.
        Err(errno) => io_error_sentinel(errno),
    }
}

/// Write with EINTR retry (upstream loops on EINTR); other errors carry
/// their errno out.
fn retry_eintr_write(w: &mut impl Write, slice: &[u8]) -> Result<usize, i32> {
    loop {
        match w.write(slice) {
            Ok(n) => return Ok(n),
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e.raw_os_error().unwrap_or(libc::EIO)),
        }
    }
}

/// Read with EINTR retry; other errors carry their errno out.
fn retry_eintr_read(r: &mut impl std::io::Read, buf: &mut [u8]) -> Result<usize, i32> {
    loop {
        match r.read(buf) {
            Ok(n) => return Ok(n),
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e.raw_os_error().unwrap_or(libc::EIO)),
        }
    }
}

/// In-band error sentinel for the fd-IO helpers whose callers (the
/// `poly_basic_io_general` dispatcher) hold the `ctx` needed to raise:
/// `TAGGED(-(errno + 1))` — impossible as a genuine byte count (those
/// are always >= 0), decoded by [`io_sentinel_errno`].
fn io_error_sentinel(errno: i32) -> PolyWord {
    PolyWord::tagged(-(isize::try_from(errno).unwrap_or(0) + 1))
}

/// Decode [`io_error_sentinel`]; `None` for genuine (non-negative) counts.
fn io_sentinel_errno(w: PolyWord) -> Option<i32> {
    if !w.is_tagged() {
        return None;
    }
    let v = w.untag();
    #[allow(clippy::cast_possible_truncation)]
    if v < 0 { Some((-v - 1) as i32) } else { None }
}

/// Global state for open directories. Each entry is a Vec of
/// remaining filenames (as bytes). Index = the "fd" stored in
/// the wrapped-stream object (we use `id + 1`, 0 = closed).
static DIR_STATE: std::sync::Mutex<Vec<Option<Vec<Vec<u8>>>>> = std::sync::Mutex::new(Vec::new());

/// IO subcode 50: open directory. Wraps the read-dir iterator in
/// a stream-like object keyed by an integer id.
fn open_directory(ctx: &mut RtsContext<'_>, name_arg: PolyWord) -> PolyWord {
    let Some(name) = poly_string_to_rust(ctx.safe_spaces.as_ref(), name_arg) else {
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
    // UNTRUSTED MODE: gate the strm deref on space-membership.
    let Some(strm_p) = safe_rts_arg_ptr(ctx.safe_spaces.as_ref(), strm) else {
        return alloc_empty_string(ctx);
    };
    // SAFETY: strm_p is space-validated (untrusted) / is_data_ptr (trusted).
    let id_plus_one = unsafe { *strm_p }.0;
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
fn close_directory(spaces: Option<&RtsSafeSpaces>, strm: PolyWord) -> PolyWord {
    // UNTRUSTED MODE: gate the strm deref on space-membership.
    let Some(strm_p) = safe_rts_arg_ptr(spaces, strm) else {
        return PolyWord::tagged(0);
    };
    let p = strm_p.cast_mut();
    // SAFETY: strm_p is space-validated (untrusted) / is_data_ptr (trusted).
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
fn fs_remove(spaces: Option<&RtsSafeSpaces>, arg: PolyWord) -> PolyWord {
    if let Some(name) = poly_string_to_rust(spaces, arg) {
        let _ = std::fs::remove_file(&name);
    }
    PolyWord::tagged(0)
}

/// IO subcode 57: `OS.FileSys.isDir`.
fn fs_is_dir(spaces: Option<&RtsSafeSpaces>, arg: PolyWord) -> PolyWord {
    let Some(name) = poly_string_to_rust(spaces, arg) else {
        return PolyWord::tagged(0);
    };
    match std::fs::metadata(&name) {
        Ok(m) if m.is_dir() => PolyWord::tagged(1),
        _ => PolyWord::tagged(0),
    }
}

/// IO subcode 60: `OS.FileSys.fullPath` — canonicalize.
///
/// Upstream (`basicio.cpp:648` `fullPath`) special-cases the empty
/// string by substituting `"."` before calling `realpath`, so
/// `fullPath "" = fullPath "."` = the current directory (Test196).
fn fs_full_path(ctx: &mut RtsContext<'_>, arg: PolyWord) -> PolyWord {
    let Some(name) = poly_string_to_rust(ctx.safe_spaces.as_ref(), arg) else {
        return alloc_empty_string(ctx);
    };
    // Empty path is treated as "." (the cwd), matching upstream.
    let name = if name.is_empty() {
        ".".to_owned()
    } else {
        name
    };
    let canon = std::fs::canonicalize(&name).unwrap_or_else(|_| name.into());
    alloc_poly_string(ctx, canon.into_os_string().into_encoded_bytes().as_slice())
}

/// IO subcode 61: `OS.FileSys.modTime` — microseconds since epoch.
/// Returns a tagged or arbitrary-precision integer.
fn fs_mod_time(ctx: &mut RtsContext<'_>, arg: PolyWord) -> PolyWord {
    let Some(name) = poly_string_to_rust(ctx.safe_spaces.as_ref(), arg) else {
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
    let Some(name) = poly_string_to_rust(ctx.safe_spaces.as_ref(), arg) else {
        return PolyWord::tagged(0);
    };
    let size = std::fs::metadata(&name).map(|m| m.len()).unwrap_or(0);
    int_to_poly_word(ctx, i128::from(size))
}

/// IO subcode 66: `OS.FileSys.access(name, mode)`.
/// The mode is a bit-set: 1=read, 2=write, 4=exec, 8=exists.
fn fs_access(spaces: Option<&RtsSafeSpaces>, name_arg: PolyWord, mode_arg: PolyWord) -> PolyWord {
    let Some(name) = poly_string_to_rust(spaces, name_arg) else {
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

/// CPU time used so far, in microseconds, via `getrusage`. `user` selects
/// `ru_utime` (user CPU) vs `ru_stime` (system CPU). Mirrors upstream
/// timing.cpp:452/483 (`Make_arb_from_pair_scaled(tv_sec, tv_usec, 1000000)`).
/// Returns 0 on a getrusage failure (defensive; never panics).
#[cfg(unix)]
fn getrusage_micros(who: libc::c_int, user: bool) -> i128 {
    // SAFETY: getrusage fills a caller-provided rusage; we zero it first and
    // only read POD time fields. A non-zero return means failure -> 0.
    let mut ru: libc::rusage = unsafe { std::mem::zeroed() };
    if unsafe { libc::getrusage(who, &mut ru) } != 0 {
        return 0;
    }
    let tv = if user { ru.ru_utime } else { ru.ru_stime };
    i128::from(tv.tv_sec) * 1_000_000 + i128::from(tv.tv_usec)
}

#[cfg(unix)]
use libc::RUSAGE_SELF;

/// Non-Unix fallback: no getrusage; CPU timers read as 0.
#[cfg(not(unix))]
const RUSAGE_SELF: i32 = 0;
#[cfg(not(unix))]
fn getrusage_micros(_who: i32, _user: bool) -> i128 {
    0
}

/// Extract a Rust `String` from a PolyString pointer. Returns
/// `None` for non-pointer / non-string-shaped args.
///
/// UNTRUSTED MODE (task #96, HOLE 5): `s` is an IMAGE-CONTROLLED string arg
/// (every filename / string RTS arg); its length word at `p.sub(1)` is read
/// BEFORE any shape check. The deref is gated by [`safe_rts_arg_ptr`] on
/// `spaces` (None in trusted mode -> byte-identical; a wild arg -> `None`).
fn poly_string_to_rust(spaces: Option<&RtsSafeSpaces>, s: PolyWord) -> Option<String> {
    // Header-fit gate: in untrusted mode this validates the whole string
    // object fits its space, so `body_bytes` below is a SOUND upper bound for
    // the variable-length chars read (trusted: is_data_ptr only — identical).
    let obj = safe_rts_arg_obj(spaces, s)?;
    let p = obj.ptr;
    // Defence-in-depth (unsafe-audit finding #8, sibling of finding #6's
    // write_array/read_array guards): the trusted compiler always hands a real
    // PolyStringObject (a byte object whose word 0 is the byte length and whose
    // body actually holds that many chars), so type-safe SML never trips this.
    // A corrupted image (or hostile `RunCall.rtsCallFull1 "PolyBasicIOGeneral"`
    // + `RunCall.unsafeCast` to forge a filename arg) could pass either (a) a
    // non-string pointer (e.g. a word/tuple object) whose word 0 is then
    // mis-read as a length, or (b) a byte object whose word-0 length LIES — far
    // larger than its real body — causing `from_raw_parts(chars_ptr, len)` to
    // over-read past the object. The old `len > 1_000_000` cap bounded the
    // over-read to ~1 MB but did NOT prevent it. Verify the object is a byte
    // object and `len` fits its body (matching `name_for_code_object` in
    // length_word.rs and the write_array guard).
    use crate::length_word::{is_byte_object, length_of};
    // SAFETY: p is space-validated (untrusted) / is_data_ptr (trusted), so
    // p-1 is a readable length word.
    let lw = unsafe { crate::space::MemorySpace::length_word_of(p) };
    if !is_byte_object(lw) {
        return None;
    }
    // Bound the body size by the validated handle: in untrusted mode the gate
    // proved [p, p+n_words) fits the space, so `body_bytes` is a SOUND upper
    // bound for the chars read below (trusted: n_words == MAX — byte-identical).
    let body_bytes = obj
        .clamp_body_words(length_of(lw))
        .saturating_mul(std::mem::size_of::<usize>());
    // word 0 of the body holds the byte count; the chars follow.
    // SAFETY: p is a byte object (just checked) of >= 1 word, so reading its
    // word 0 (the stored byte length) is in-bounds.
    let len = unsafe { (*p).0 };
    if len > 1_000_000 {
        return None; // sanity bound (kept as a cheap early-out)
    }
    // The length field (word 0) plus the `len` char bytes must fit the body.
    if std::mem::size_of::<usize>().saturating_add(len) > body_bytes {
        return None; // the stored length over-runs the object body
    }
    // SAFETY: `len + size_of::<usize>() <= body_bytes`, so the `len` char
    // bytes starting at body word 1 are in-bounds.
    let chars_ptr = unsafe { p.add(1).cast::<u8>() };
    let slice = unsafe { std::slice::from_raw_parts(chars_ptr, len) };
    String::from_utf8(slice.to_vec()).ok()
}

/// IO subcodes 3/4: open a file for reading. Returns a wrapped fd
/// or a TAGGED(0) on error (caller treats that as failure).
fn open_file_input(ctx: &mut RtsContext<'_>, name_arg: PolyWord) -> PolyWord {
    use std::os::fd::IntoRawFd;
    let Some(name) = poly_string_to_rust(ctx.safe_spaces.as_ref(), name_arg) else {
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
            // Upstream basicio.cpp:242: raise_syscall("Cannot open", errno).
            // A REAL SysErr (ex_id = TAGGED(2), errno in the payload) so the
            // basis wraps it into `IO.Io {cause = SysErr ...}` and both the
            // openIn alternate-filename fallback (`handle IO.Io _`) and
            // `OS.errorMsg` on the cause work. (This used to be a
            // fresh-identity packet only a wildcard handler could match.)
            raise_syscall(ctx, "Cannot open", e.raw_os_error().unwrap_or(libc::EINVAL))
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
/// Public version of `make_simple_exception` used by the
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
    let p = space.alloc_or_exit(4);
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
    let pair = space.alloc_or_exit(2);
    // SAFETY: just allocated 2 words.
    let pair_w = unsafe {
        crate::space::set_length_word(pair, 2, 0);
        pair.write(msg_s);
        pair.add(1).write(PolyWord::tagged(0)); // NONE
        PolyWord::from_ptr(pair.cast_const())
    };
    let p = space.alloc_or_exit(4);
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

/// De-fanged stub: raise a catchable `SysErr` instead of faking success.
/// For OS-level operations we don't implement, SysErr is upstream's own
/// failure shape, so `handle OS.SysErr _` code behaves sanely and code
/// that assumed success gets an honest, catchable failure — never a
/// silent success-shaped default (the old `OS.Process.system` stub
/// "succeeded" without running anything).
fn syserr_unimpl(ctx: &mut RtsContext<'_>, what: &str) -> PolyWord {
    let msg = format!("{what}: not implemented (polyml-rs)");
    let pkt = make_syserr_exception(ctx, &msg);
    ctx.raised_exception = Some(pkt);
    PolyWord::tagged(0)
}

/// De-fanged stub for non-OS entry points (FFI, SaveState, Date
/// conversion): raise a generic catchable exception. Not `SysErr` —
/// these aren't errno-shaped failures upstream.
fn fail_unimpl(ctx: &mut RtsContext<'_>, what: &str) -> PolyWord {
    let msg = format!("{what}: not implemented (polyml-rs)");
    let pkt = make_simple_exception(ctx, &msg);
    ctx.raised_exception = Some(pkt);
    PolyWord::tagged(0)
}

/// strerror text for an errno — upstream `errorMsg`
/// (`run_time.cpp:133-153`, the Unix branch: `strerror(err)`).
fn strerror_string(errno: i32) -> String {
    let mut buf = [0u8; 256];
    // SAFETY: buf is a valid writable buffer of buf.len() bytes; XSI
    // strerror_r writes a NUL-terminated message into it on success.
    let r = unsafe { libc::strerror_r(errno, buf.as_mut_ptr().cast(), buf.len()) };
    if r == 0 {
        let len = buf.iter().position(|&b| b == 0).unwrap_or(buf.len());
        String::from_utf8_lossy(&buf[..len]).into_owned()
    } else {
        format!("Unknown error {errno}")
    }
}

/// Raise `SysErr` exactly as upstream `raise_syscall`
/// (`run_time.cpp:238-262` `raiseSycallWithLocation`):
/// - `errno != 0` → `SysErr(strerror(errno), SOME errno)` — the label
///   `msg` is DISCARDED (upstream generates the message from the errno)
///   and the errno rides as a boxed SysWord (`Make_sysword` — a 1-word
///   byte object), so `OS.errorMsg`/`errorName`/SysWord ops on the
///   payload behave exactly as on upstream.
/// - `errno == 0` → `SysErr(msg, NONE)`.
fn raise_syscall(ctx: &mut RtsContext<'_>, msg: &str, errno: i32) -> PolyWord {
    use crate::length_word::F_BYTE_OBJ;
    let name = alloc_poly_string(ctx, b"SysErr");
    let msg_s = if errno == 0 {
        alloc_poly_string(ctx, msg.as_bytes())
    } else {
        alloc_poly_string(ctx, strerror_string(errno).as_bytes())
    };
    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::tagged(0);
    };
    let opt_w = if errno == 0 {
        PolyWord::tagged(0) // NONE
    } else {
        let sysword = space.alloc_or_exit(1);
        // SAFETY: just allocated 1 word (the SysWord byte box).
        let sysword_w = unsafe {
            crate::space::set_length_word(sysword, 1, F_BYTE_OBJ);
            #[allow(clippy::cast_sign_loss)]
            sysword.write(PolyWord::from_bits(errno as usize));
            PolyWord::from_ptr(sysword.cast_const())
        };
        let some_cell = space.alloc_or_exit(1);
        // SAFETY: just allocated 1 word (the SOME box); earlier pointers
        // stay valid (bump allocator only advances).
        unsafe {
            crate::space::set_length_word(some_cell, 1, 0);
            some_cell.write(sysword_w);
            PolyWord::from_ptr(some_cell.cast_const())
        }
    };
    let pair = space.alloc_or_exit(2);
    // SAFETY: just allocated 2 words.
    let pair_w = unsafe {
        crate::space::set_length_word(pair, 2, 0);
        pair.write(msg_s);
        pair.add(1).write(opt_w);
        PolyWord::from_ptr(pair.cast_const())
    };
    let p = space.alloc_or_exit(4);
    // SAFETY: just allocated 4 words.
    unsafe {
        crate::space::set_length_word(p, 4, 0);
        p.write(PolyWord::tagged(2)); // ex_id = EXC_syserr
        p.add(1).write(name);
        p.add(2).write(pair_w); // ex_arg = (msg, SOME errno | NONE)
        p.add(3).write(PolyWord::tagged(0)); // ex_location = NONE
    }
    ctx.raised_exception = Some(PolyWord::from_ptr(p.cast_const()));
    PolyWord::tagged(0)
}

/// Raise the pervasive `Size` exception (`EXC_size` = 4, sys.h) —
/// upstream `raise_exception0(taskData, EXC_size)`.
fn raise_size(ctx: &mut RtsContext<'_>) -> PolyWord {
    let pkt = make_pervasive_exn(ctx, 4, b"Size");
    ctx.raised_exception = Some(pkt);
    PolyWord::tagged(0)
}

/// Read an ML int (tagged or boxed arbitrary-precision) as i64 —
/// upstream `get_C_long`.
fn ml_int_as_i64(spaces: Option<&RtsSafeSpaces>, w: PolyWord) -> Option<i64> {
    let n = poly_word_to_bigint(spaces, w)?;
    num_traits::ToPrimitive::to_i64(&n)
}

/// `OS.Process.system` — REAL. Port of `process_env.cpp:522-640`
/// (`PolyProcessEnvSystem`): fork/exec `/bin/sh -c cmd`, wait, and
/// return the RAW waitpid status word as an ML int
/// (`Make_fixed_precision(res)` — so `exit 1` yields 256, which the
/// basis compares against `PolyProcessEnvSuccessValue` = 0). Failures
/// raise `SysErr("Function system failed", SOME errno)` like upstream's
/// `raise_syscall`. Blocks the calling ML thread for the child's
/// duration (upstream pauses it too; under the default single-threaded
/// runtime that is the whole interpreter — same as upstream's
/// interpreter mode running one mutator).
fn poly_process_env_system(ctx: &mut RtsContext<'_>, _tid: PolyWord, cmd: PolyWord) -> PolyWord {
    let Some(cmd) = poly_string_to_rust(ctx.safe_spaces.as_ref(), cmd) else {
        return raise_syscall(ctx, "Function system failed", libc::EINVAL);
    };
    match std::process::Command::new("/bin/sh")
        .arg("-c")
        .arg(&cmd)
        .status()
    {
        Ok(status) => {
            #[cfg(unix)]
            let raw = {
                use std::os::unix::process::ExitStatusExt;
                i128::from(status.into_raw())
            };
            #[cfg(not(unix))]
            let raw = i128::from(status.code().unwrap_or(1));
            int_to_poly_word(ctx, raw)
        }
        Err(e) => raise_syscall(
            ctx,
            "Function system failed",
            e.raw_os_error().unwrap_or(libc::EINVAL),
        ),
    }
}

/// `OS.errorMsg` — REAL strerror. Port of `process_env.cpp`
/// (`PolyProcessEnvErrorMessage`): map an errno to its message text.
fn poly_process_env_error_message(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    err: PolyWord,
) -> PolyWord {
    let Some(e) = ml_int_as_i64(ctx.safe_spaces.as_ref(), err) else {
        return alloc_empty_string(ctx);
    };
    #[allow(clippy::cast_possible_truncation)]
    let msg = strerror_string(e as i32);
    alloc_poly_string(ctx, msg.as_bytes())
}

/// UTC-vs-local offset in seconds at time `t` — REAL localtime. Port of
/// `timing.cpp:283-352` (`PolyTimingLocalOffset`): wall-clock seconds of
/// `gmtime(t)` minus `localtime(t)`, with the at-most-one-day `tm_yday`
/// correction; conversion failure raises `Size` like upstream's
/// `raise_exception0(EXC_size)`. (Was a tagged(0) "we are UTC" stub —
/// and registered at the WRONG ARITY: Arity1 for an rtsCallFull1 site,
/// a latent stack-corruption on any call.)
fn poly_timing_local_offset(ctx: &mut RtsContext<'_>, _tid: PolyWord, arg: PolyWord) -> PolyWord {
    let Some(t) = ml_int_as_i64(ctx.safe_spaces.as_ref(), arg) else {
        return raise_size(ctx);
    };
    let t = t as libc::time_t;
    // SAFETY: valid out-pointers; the _r variants are thread-safe.
    let (gm, loc) = unsafe {
        let mut gm: libc::tm = std::mem::zeroed();
        let mut loc: libc::tm = std::mem::zeroed();
        if libc::gmtime_r(&t, &raw mut gm).is_null()
            || libc::localtime_r(&t, &raw mut loc).is_null()
        {
            return raise_size(ctx);
        }
        (gm, loc)
    };
    let mut off = (gm.tm_hour * 60 + gm.tm_min) * 60 + gm.tm_sec;
    off -= (loc.tm_hour * 60 + loc.tm_min) * 60 + loc.tm_sec;
    if loc.tm_yday != gm.tm_yday {
        // Different day — at most one day of correction (timing.cpp:334-339).
        if gm.tm_yday == loc.tm_yday + 1 || (gm.tm_yday == 0 && loc.tm_yday >= 364) {
            off += 24 * 60 * 60;
        } else {
            off -= 24 * 60 * 60;
        }
    }
    int_to_poly_word(ctx, i128::from(off))
}

/// Daylight-saving flag at time `t` — REAL localtime. Port of
/// `timing.cpp:354-397` (`PolyTimingSummerApplies`): `tm_isdst`
/// (>0 DST, 0 not, <0 unknown). (Was a tagged(0) stub, wrong-arity.)
fn poly_timing_summer_applies(ctx: &mut RtsContext<'_>, _tid: PolyWord, arg: PolyWord) -> PolyWord {
    let Some(t) = ml_int_as_i64(ctx.safe_spaces.as_ref(), arg) else {
        return raise_size(ctx);
    };
    let t = t as libc::time_t;
    let mut loc: libc::tm = unsafe { std::mem::zeroed() };
    // SAFETY: valid out-pointer; localtime_r is thread-safe.
    if unsafe { libc::localtime_r(&t, &raw mut loc).is_null() } {
        return raise_size(ctx);
    }
    int_to_poly_word(ctx, i128::from(loc.tm_isdst))
}

/// `Date.fmt` — REAL strftime. Port of `timing.cpp:399-460`
/// (`PolyTimingConvertDateStuct` — sic, upstream's spelling): arg is the
/// 10-tuple (format, year, month, mday, hour, min, sec, wday, yday,
/// isdst); strftime under the current LC_TIME locale; empty/failed
/// formatting raises `Size` like upstream.
fn poly_timing_convert_date_struct(
    ctx: &mut RtsContext<'_>,
    _tid: PolyWord,
    arg: PolyWord,
) -> PolyWord {
    let Some(obj) = safe_rts_arg_obj(ctx.safe_spaces.as_ref(), arg) else {
        return raise_size(ctx);
    };
    // Untrusted: the tuple must genuinely hold 10 fields (trusted:
    // n_words == usize::MAX, so this is byte-identical no-op).
    if obj.n_words < 10 {
        return raise_size(ctx);
    }
    // SAFETY: obj is space-validated (untrusted) / is_data_ptr (trusted)
    // and holds >= 10 words per the gate above.
    let field = |i: usize| unsafe { *obj.ptr.add(i) };
    let Some(format) = poly_string_to_rust(ctx.safe_spaces.as_ref(), field(0)) else {
        return raise_size(ctx);
    };
    let Ok(cfmt) = std::ffi::CString::new(format) else {
        return raise_size(ctx);
    };
    let mut ints = [0i64; 9];
    for (i, slot) in ints.iter_mut().enumerate() {
        let Some(v) = ml_int_as_i64(ctx.safe_spaces.as_ref(), field(i + 1)) else {
            return raise_size(ctx);
        };
        *slot = v;
    }
    let mut tm: libc::tm = unsafe { std::mem::zeroed() };
    #[allow(clippy::cast_possible_truncation)]
    {
        tm.tm_year = (ints[0] - 1900) as i32; // field 1 is the full year
        tm.tm_mon = ints[1] as i32;
        tm.tm_mday = ints[2] as i32;
        tm.tm_hour = ints[3] as i32;
        tm.tm_min = ints[4] as i32;
        tm.tm_sec = ints[5] as i32;
        tm.tm_wday = ints[6] as i32;
        tm.tm_yday = ints[7] as i32;
        tm.tm_isdst = ints[8] as i32;
    }
    let mut buff = [0u8; 2048];
    // SAFETY: setlocale with a valid C string (upstream does the same each
    // call); strftime writes at most buff.len() bytes into the valid buffer.
    let n = unsafe {
        libc::setlocale(libc::LC_TIME, c"".as_ptr());
        libc::strftime(
            buff.as_mut_ptr().cast(),
            buff.len(),
            cfmt.as_ptr(),
            &raw const tm,
        )
    };
    if n == 0 {
        return raise_size(ctx); // upstream: strftime <= 0 → EXC_size
    }
    alloc_poly_string(ctx, &buff[..n])
}

/// Build a nullary pervasive-exception packet: a 4-word ordinary object
/// `[ex_id, ex_name, arg=(), ex_location=NoLocation]` where `ex_id =
/// TAGGED(ex_id)` is the handler match key (sys.h) and `name` is for
/// printing only (run_time.cpp:165). Mirrors upstream
/// `makeExceptionPacket(taskData, EXC_*)` (run_time.cpp:206-209 ->
/// make_exn, run_time.cpp:158-200). The single audited site for the
/// Overflow/Div packet shape (the layout `handle Overflow`/`handle Div`
/// matches on).
fn make_pervasive_exn(ctx: &mut RtsContext<'_>, ex_id: isize, name: &[u8]) -> PolyWord {
    let name_s = alloc_poly_string(ctx, name);
    let Some(space) = ctx.alloc_space.as_mut() else {
        return PolyWord::ZERO;
    };
    let p = space.alloc_or_exit(4);
    // SAFETY: just allocated 4 words.
    unsafe {
        crate::space::set_length_word(p, 4, 0);
        p.write(PolyWord::tagged(ex_id)); // ex_id = the match key
        p.add(1).write(name_s); // ex_name (for printing)
        p.add(2).write(PolyWord::tagged(0)); // arg = () (nullary exception)
        p.add(3).write(PolyWord::tagged(0)); // ex_location = NoLocation
    }
    PolyWord::from_ptr(p.cast_const())
}

/// Build the pervasive `Overflow` exception packet so that a handler
/// `handle Overflow => ...` matches it. The matching identity is
/// `ex_id == TAGGED(5)` (`EXC_overflow`, INITIALISE_.ML:512 / sys.h:32;
/// the nullary constructor is `Global(mkConst(toMachineWord 5))`).
///
/// NOTE: `make_simple_exception` would NOT be caught as `Overflow`
/// because it uses a self-pointer ex_id, not TAGGED(5).
pub fn make_overflow_exception(ctx: &mut RtsContext<'_>) -> PolyWord {
    make_pervasive_exn(ctx, 5, b"Overflow")
}

/// Build the pervasive `Interrupt` packet (`EXC_interrupt = 1`,
/// `vendor/polyml/libpolyml/sys.h:26` / `INITIALISE_.ML:524`). Raised by the
/// interpreter on an async SIGINT (see [`crate::interrupt`]).
pub fn make_interrupt_exception(ctx: &mut RtsContext<'_>) -> PolyWord {
    make_pervasive_exn(ctx, 1, b"Interrupt")
}

/// Build the pervasive `Div` exception packet so `handle Div => ...` matches.
/// Match identity is `ex_id == TAGGED(7)` (`EXC_divide`, sys.h:33). Mirrors
/// `make_overflow_exception`. Used by the IntInf div/mod/quotRem RTS on a zero
/// divisor — upstream raises Div (arb.cpp), where we previously returned
/// TAGGED(0), which the SML side then mis-read as a (q,r) tuple pointer and
/// HALTED the interpreter (found by differential test vs upstream PolyML).
pub fn make_div_exception(ctx: &mut RtsContext<'_>) -> PolyWord {
    // ex_id = TAGGED(7) = EXC_divide.
    make_pervasive_exn(ctx, 7, b"Div")
}

/// `PolyGetEnv(threadId, name)` — return the real environment value, or
/// raise `SysErr` (so the basis `getEnv` returns `NONE`) when the
/// variable is unset. Mirrors `process_env.cpp:433-436`. Previously a
/// hard stub that returned `""`, which the basis wrapped as `SOME ""`
/// for *every* variable (set or not).
fn poly_get_env(ctx: &mut RtsContext<'_>, _tid: PolyWord, name_arg: PolyWord) -> PolyWord {
    let Some(name) = poly_string_to_rust(ctx.safe_spaces.as_ref(), name_arg) else {
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
    let Some(name) = poly_string_to_rust(ctx.safe_spaces.as_ref(), name_arg) else {
        return PolyWord::tagged(0);
    };
    let mut opts = std::fs::OpenOptions::new();
    opts.write(true).create(true);
    if append {
        opts.append(true);
    } else {
        opts.truncate(true);
    }
    match opts.open(&name) {
        Ok(f) => {
            let fd = f.into_raw_fd();
            #[allow(clippy::cast_sign_loss)]
            wrap_file_descriptor(ctx, fd as u32)
        }
        // Upstream basicio.cpp:242: raise_syscall("Cannot open", errno).
        // (This used to return a silent tagged(0) "stream", making every
        // downstream write a no-op on an unopenable file.)
        Err(e) => raise_syscall(ctx, "Cannot open", e.raw_os_error().unwrap_or(libc::EINVAL)),
    }
}

/// IO subcode 7: close the file. Skips stdio (fds 0/1/2). After
/// close, mark the stream object as `0` (= "closed") so re-close
/// is a no-op.
fn close_file(spaces: Option<&RtsSafeSpaces>, strm: PolyWord) -> PolyWord {
    use std::os::fd::FromRawFd;
    // UNTRUSTED MODE: gate the strm deref on space-membership.
    let Some(strm_p) = safe_rts_arg_ptr(spaces, strm) else {
        return PolyWord::tagged(0);
    };
    let p = strm_p.cast_mut();
    // SAFETY: strm_p is space-validated (untrusted) / is_data_ptr (trusted);
    // a wrapped-fd object (1 byte-object word holding fd+1).
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
fn read_array_from_stream(
    spaces: Option<&RtsSafeSpaces>,
    strm: PolyWord,
    arg: PolyWord,
) -> PolyWord {
    // UNTRUSTED MODE (task #96/#132): `strm` is a single-word wrapped-fd read
    // (safe_rts_arg_ptr); `arg` is a 3-tuple read at p[0..3], so gate it on
    // header-fit and bound the three word reads on its validated length.
    let (Some(strm_p), Some(arg_obj)) = (
        safe_rts_arg_ptr(spaces, strm),
        safe_rts_arg_obj(spaces, arg),
    ) else {
        return PolyWord::tagged(0);
    };
    let fd_plus_one = unsafe { *strm_p }.0;
    if fd_plus_one == 0 {
        return PolyWord::tagged(0);
    }
    if !arg_obj.word_in_bounds(2) {
        return PolyWord::tagged(0);
    }
    let p = arg_obj.ptr;
    // SAFETY: arg has >= 3 body words (untrusted) / is_data_ptr (trusted).
    let (buf, offset, length) = unsafe { (*p, *p.add(1), *p.add(2)) };
    if !offset.is_tagged() || !length.is_tagged() {
        return PolyWord::tagged(0);
    }
    // UNTRUSTED MODE: gate the buf deref on header-fit so the body-size bound
    // below is sound (not derived from a forged header).
    let Some(buf_obj) = safe_rts_arg_obj(spaces, buf) else {
        return PolyWord::tagged(0);
    };
    let buf_p = buf_obj.ptr;
    let off = offset.untag() as usize;
    let len = length.untag() as usize;
    if len == 0 {
        return PolyWord::tagged(0);
    }
    // Defence-in-depth (unsafe-audit finding #6): mirror of write_array but
    // a WRITE (from_raw_parts_mut + Read::read into the slice) — the more
    // dangerous direction (heap corruption, not just over-read). The
    // trusted basis always sends an in-bounds (buf, offset, length); a
    // corrupted image / hostile RunCall could forge an over-long `length`.
    // Verify buf is a byte object and `off + len` fits its body before the
    // unsafe mutable slice; on violation return the "read nothing" stub.
    {
        use crate::length_word::{is_byte_object, length_of};
        // SAFETY: buf_p is space-validated (untrusted) / is_data_ptr (trusted).
        let lw = unsafe { crate::space::MemorySpace::length_word_of(buf_p) };
        // Bound the body size by the validated handle: in untrusted mode the
        // gate proved [buf_p, buf_p+n_words) fits the space, so `body_bytes` is
        // a SOUND upper bound (trusted: n_words == MAX — byte-identical).
        let body_bytes = buf_obj
            .clamp_body_words(length_of(lw))
            .saturating_mul(std::mem::size_of::<usize>());
        if !is_byte_object(lw) || off.checked_add(len).is_none_or(|end| end > body_bytes) {
            return PolyWord::tagged(0);
        }
    }
    // SAFETY: buf is a byte object and `off + len <= body_bytes` was just
    // verified, so writing off..off+len bytes of its body is in-bounds.
    let base = buf_p.cast::<u8>().cast_mut();
    let slice = unsafe { std::slice::from_raw_parts_mut(base.add(off), len) };
    #[allow(clippy::cast_possible_truncation)]
    let fd = (fd_plus_one - 1) as i32;
    let n = if fd == 0 {
        let syn = read_synthetic_stdin(slice);
        if syn > 0 {
            Ok(syn)
        } else {
            retry_eintr_read(&mut std::io::stdin(), slice)
        }
    } else {
        // For non-stdio fds, reconstruct a File to read, then
        // immediately forget it so we don't close the fd.
        use std::os::fd::{FromRawFd, IntoRawFd};
        let mut f = unsafe { std::fs::File::from_raw_fd(fd) };
        let r = retry_eintr_read(&mut f, slice);
        let _kept = f.into_raw_fd();
        r
    };
    match n {
        #[allow(clippy::cast_possible_wrap)]
        Ok(n) => PolyWord::tagged(n as isize),
        // A real read error is NOT end-of-stream (the old conflation made
        // errors read as silent EOF). Sentinel → the dispatcher raises
        // SysErr("Error while reading", errno) — upstream basicio.cpp:308.
        Err(errno) => io_error_sentinel(errno),
    }
}

/// IO subcode 10/26: read a chunk of bytes from a stream into a
/// fresh PolyStringObject (length-prefix word + chars).
///
/// For fd 0 (stdin) we route through `std::io::stdin().read()` so
/// piped input actually reaches the bootstrap. Other fds return an
/// empty string (= EOF) for now — extending to real file fds will
/// require a real file-open path (subcodes 3/4) first.
fn read_string_from_stream(ctx: &mut RtsContext<'_>, strm: PolyWord, arg: PolyWord) -> PolyWord {
    // UNTRUSTED MODE: gate the strm deref on space-membership.
    let Some(strm_p) = safe_rts_arg_ptr(ctx.safe_spaces.as_ref(), strm) else {
        return alloc_empty_string(ctx);
    };
    // SAFETY: strm_p is space-validated (untrusted) / is_data_ptr (trusted);
    // a wrapped-fd object created by `wrap_file_descriptor`.
    let fd_plus_one = unsafe { *strm_p }.0;
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
            Ok(syn)
        } else {
            retry_eintr_read(&mut std::io::stdin(), &mut buf)
        }
    } else {
        // Borrow the fd without taking ownership (= no close).
        use std::os::fd::{FromRawFd, IntoRawFd};
        let mut f = unsafe { std::fs::File::from_raw_fd(fd) };
        let r = retry_eintr_read(&mut f, &mut buf);
        let _kept = f.into_raw_fd();
        r
    };
    match n {
        Ok(0) => alloc_empty_string(ctx),
        Ok(n) => alloc_poly_string(ctx, &buf[..n]),
        // Real error ≠ EOF (upstream basicio.cpp:346). This fn holds ctx,
        // so raise directly.
        Err(errno) => raise_syscall(ctx, "Error while reading", errno),
    }
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
    let p = space.alloc_or_exit(total_words);
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
    let Some(name) = poly_string_to_rust(ctx.safe_spaces.as_ref(), name_arg) else {
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
    let p = space.alloc_or_exit(total);
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
    let p = space.alloc_or_exit(1);
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
    let p = space.alloc_or_exit(1);
    // SAFETY: just allocated 1 word
    unsafe {
        crate::space::set_length_word(
            p,
            1,
            F_BYTE_OBJ | F_WEAK_BIT | F_MUTABLE_BIT | F_NO_OVERWRITE,
        );
        p.write(PolyWord::from_bits((fd as usize) + 1));
    }
    PolyWord::from_ptr(p.cast_const())
}

fn reset_mutex(spaces: Option<&RtsSafeSpaces>, mutex: PolyWord) {
    // UNTRUSTED MODE (task #96, HOLE 5): `mutex` is an image-controlled arg
    // written through (`p.write`); gate it on space-membership + alignment.
    if mutex.0 & (std::mem::size_of::<usize>() - 1) != 0 {
        return;
    }
    let Some(p) = safe_rts_arg_ptr(spaces, mutex) else {
        return;
    };
    let p = p.cast_mut();
    // SAFETY: p is space-validated (untrusted) / is_data_ptr (trusted) and
    // word-aligned → a valid mutex slot.
    unsafe { p.write(PolyWord::tagged(0)) };
}

#[cfg(test)]
mod tests {
    use super::*;

    // Serializes the few tests that touch the process-global
    // `FINISH_REQUESTED` flag, since `cargo test` runs in parallel.
    static FINISH_FLAG_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

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

    /// Fingerprint of the registration ORDER. Dispatch tokens are baked into
    /// warm /tmp checkpoints by `register()` order, so a silent reorder
    /// mis-dispatches every stale checkpoint (the historical copySign→pow
    /// bug) while every other test stays green — this is the fence.
    #[test]
    fn registration_order_fingerprint() {
        let t = RtsTable::new();
        let names: Vec<&str> = t.entries.iter().map(|e| e.name).collect();
        // djb2 over the ordered names (order-sensitive by construction).
        let mut h: u64 = 5381;
        for n in &names {
            for b in n.bytes() {
                h = h.wrapping_mul(33) ^ u64::from(b);
            }
            h = h.wrapping_mul(33) ^ u64::from(b'\n');
        }
        assert_eq!(
            (names.len(), h),
            (228usize, 3_770_104_743_555_170_908u64),
            "RTS registration ORDER or COUNT changed (first: {:?}…, last: {:?}).\n\
             - APPEND-only additions are checkpoint-safe: just update the two\n\
               expected values above.\n\
             - Any REORDER or REMOVAL invalidates every warm checkpoint:\n\
               rebuild them all (tools/build-*.sh; see CLAUDE.md \"RTS calling\n\
               conventions\") before updating this fingerprint.",
            &names[..4.min(names.len())],
            names.last(),
        );
        // Positional sentinels: catch a partial reorder with a readable message.
        assert_eq!(names.first().copied(), Some("PolyIsBigEndian"));
        assert_eq!(names.last().copied(), Some("PolyCreateEntryPointObject"));
    }

    #[test]
    fn arity_call_through_dispatch() {
        let t = RtsTable::new();
        let token = t.token_for("PolyIsBigEndian").unwrap();
        let entry = t.entry(token).unwrap();
        let mut ctx = RtsContext {
            alloc_space: None,
            raised_exception: None,
            rts: None,
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: None,
        };
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
        RtsContext {
            alloc_space: None,
            raised_exception: None,
            rts: None,
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: None,
        }
    }
    fn t() -> PolyWord {
        PolyWord::tagged(0)
    }

    // ---- AUDIT REPRO (unsafe-audit finding #9): out-of-range offset
    // in PolySetCodeConstant / PolySetCodeByte performs an OOB heap
    // write. Demonstrates the missing bounds check, and (after the fix)
    // asserts the write is now rejected. -------------------------------

    /// Build a small code object in `space` and a sentinel word object
    /// immediately after it, returning (code_obj_ptr, sentinel_ptr,
    /// byte distance from code body start to sentinel body start).
    fn build_code_then_sentinel(
        space: &mut crate::space::MemorySpace,
    ) -> (*mut PolyWord, *mut PolyWord, usize) {
        use crate::length_word::{F_CODE_OBJ, F_MUTABLE_BIT};
        // A 2-word mutable code object (body = 2 words = 16 bytes).
        let code = space.alloc(2);
        unsafe {
            crate::space::set_length_word(code, 2, F_CODE_OBJ | F_MUTABLE_BIT);
            code.write(PolyWord::ZERO);
            code.add(1).write(PolyWord::ZERO);
        }
        // A sentinel ordinary word object right after it.
        let sentinel = space.alloc(1);
        unsafe {
            crate::space::set_length_word(sentinel, 1, 0);
            sentinel.write(PolyWord::tagged(0x5555));
        }
        let dist = (sentinel as usize) - (code as usize);
        (code, sentinel, dist)
    }

    #[test]
    fn set_code_constant_in_bounds_writes_correctly() {
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Code);
        let (code, _sentinel, _dist) = build_code_then_sentinel(&mut space);
        // Offset 8 (the 2nd body word) is in bounds for a 2-word object.
        // SML offsets are tagged ints; tagged(8) untags to 8.
        let r = poly_set_code_constant(
            &mut ctx(),
            PolyWord::from_ptr(code.cast_const()),
            PolyWord::tagged(8),
            PolyWord::tagged(0x1234),
            PolyWord::tagged(0), // flag 0 = absolute PolyWord constant
        );
        assert_eq!(r.untag(), 0);
        // In-bounds write landed in the 2nd body word.
        let written = unsafe { code.add(1).read() };
        assert_eq!(written.0, PolyWord::tagged(0x1234).0);
    }

    #[test]
    fn set_code_constant_out_of_range_offset_is_rejected() {
        // BEFORE the fix this test FAILS: the OOB write clobbers the
        // sentinel object that lives past the code object's 16-byte
        // body. AFTER the fix the out-of-range write is a no-op and the
        // sentinel is preserved.
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Code);
        let (code, sentinel, dist) = build_code_then_sentinel(&mut space);
        let sentinel_before = unsafe { sentinel.read() };
        // `dist` is the byte offset of the sentinel's body, well past
        // the code object's 16-byte (2-word) body — an OOB offset.
        let r = poly_set_code_constant(
            &mut ctx(),
            PolyWord::from_ptr(code.cast_const()),
            PolyWord::tagged(dist as isize),
            PolyWord::tagged(0x7777),
            PolyWord::tagged(0),
        );
        assert_eq!(r.untag(), 0);
        let sentinel_after = unsafe { sentinel.read() };
        assert_eq!(
            sentinel_after.0, sentinel_before.0,
            "OOB SetCodeConstant clobbered an adjacent heap object \
             (sentinel changed from {:#x} to {:#x}) — missing bounds check",
            sentinel_before.0, sentinel_after.0
        );
    }

    #[test]
    fn set_code_byte_out_of_range_offset_is_rejected() {
        // Same as above for PolySetCodeByte: build a closure whose
        // slot 0 points at a small code object, plus a sentinel.
        use crate::length_word::{F_CODE_OBJ, F_MUTABLE_BIT};
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Code);
        let code = space.alloc(2);
        unsafe {
            crate::space::set_length_word(code, 2, F_CODE_OBJ | F_MUTABLE_BIT);
            code.write(PolyWord::ZERO);
            code.add(1).write(PolyWord::ZERO);
        }
        let sentinel = space.alloc(1);
        unsafe {
            crate::space::set_length_word(sentinel, 1, 0);
            sentinel.write(PolyWord::tagged(0x33));
        }
        // A 1-word mutable closure whose slot 0 = code obj ptr.
        let closure = space.alloc(1);
        unsafe {
            crate::space::set_length_word(closure, 1, F_MUTABLE_BIT);
            closure.write(PolyWord::from_ptr(code.cast_const()));
        }
        let dist = (sentinel as usize) - (code as usize);
        let sentinel_before = unsafe { sentinel.read() };
        let r = poly_set_code_byte(
            &mut ctx(),
            PolyWord::from_ptr(closure.cast_const()),
            PolyWord::tagged(dist as isize),
            PolyWord::tagged(0xAB),
        );
        assert_eq!(r.untag(), 0);
        let sentinel_after = unsafe { sentinel.read() };
        assert_eq!(
            sentinel_after.0, sentinel_before.0,
            "OOB SetCodeByte clobbered an adjacent heap object — missing bounds check"
        );
    }

    #[test]
    fn arb_add_fast_path() {
        let r = poly_add_arbitrary(&mut ctx(), t(), PolyWord::tagged(2), PolyWord::tagged(3));
        // arg2 + arg1 = 3 + 2 = 5
        assert_eq!(r.untag(), 5);
    }

    #[test]
    fn arb_sub_fast_path() {
        // Upstream PolySubtractArbitrary(arg1, arg2) computes arg1 - arg2
        // (the dcdbbd4 fix; the old code computed the negation arg2 - arg1).
        // arg1 = 4, arg2 = 7 → 4 - 7 = -3.
        let r = poly_subtract_arbitrary(&mut ctx(), t(), PolyWord::tagged(4), PolyWord::tagged(7));
        assert_eq!(r.untag(), -3);
    }

    #[test]
    fn arb_mul_fast_path() {
        let r = poly_multiply_arbitrary(&mut ctx(), t(), PolyWord::tagged(6), PolyWord::tagged(7));
        assert_eq!(r.untag(), 42);
    }

    // Regression for Test190 (`OS.Process.terminate`).
    //
    // The basis wraps the RTS call as `terminate n = (doCall n; raise
    // Fail "never")` (`basis/OS.sml:1169`); upstream `process_env.cpp:228`
    // `_exit(i)`s and never returns, so the `raise` is unreachable. The old
    // stub `|_, _, _| tagged(0)` simply returned, letting control fall back
    // into the basis and fire `raise Fail "never"`. The fix sets the same
    // `FINISH_REQUESTED` flag `poly_finish` uses, which the interpreter's
    // `step()` loop checks to halt cleanly with the requested code — so the
    // `raise` never executes, matching upstream's "doesn't return".
    //
    // Asserts the function sets the finish flag to the right exit code.
    // Serialized against `poly_finish_sets_flag` via `FINISH_FLAG_LOCK`.
    #[test]
    fn terminate_sets_finish_flag() {
        let _g = FINISH_FLAG_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        clear_finish_requested();
        assert_eq!(finish_requested(), None, "flag must start clear");

        // success (exit 0)
        let r = poly_terminate(&mut ctx(), t(), PolyWord::tagged(0));
        assert_eq!(r, PolyWord::tagged(0), "terminate returns unit/tagged(0)");
        assert_eq!(
            finish_requested(),
            Some(0),
            "terminate(0) must request a clean halt with code 0"
        );

        // failure (exit 1) — exit code must propagate, not be hard-coded.
        clear_finish_requested();
        let _ = poly_terminate(&mut ctx(), t(), PolyWord::tagged(1));
        assert_eq!(
            finish_requested(),
            Some(1),
            "terminate(1) must request a halt with code 1"
        );

        clear_finish_requested();
    }

    // `poly_finish` is the sibling halt path `poly_terminate` reuses; pin it
    // too so the shared `FINISH_REQUESTED` convention can't silently drift.
    #[test]
    fn poly_finish_sets_flag() {
        let _g = FINISH_FLAG_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        clear_finish_requested();
        let _ = poly_finish(&mut ctx(), t(), PolyWord::tagged(7));
        assert_eq!(finish_requested(), Some(7));
        clear_finish_requested();
    }

    // unsafe-audit finding #6: `write_array` / `read_array_from_stream` must
    // bounds-check the forged (vec, offset, length) tuple against vec's real
    // byte body before the `from_raw_parts` slice. A corrupted image can send
    // a `length` far larger than vec; without the guard that is an OOB
    // read/write past the byte object. The guard returns the existing
    // "did nothing" stub (Tagged(0)) on an out-of-bounds tuple, and leaves
    // the legitimate in-bounds path (small slice) untouched.
    #[test]
    fn write_read_array_bounds_guard() {
        use crate::length_word::{F_BYTE_OBJ, F_MUTABLE_BIT};
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);

        // A 2-word (16-byte) byte object = `vec`.
        let n_words = 2usize;
        let p = space.alloc(n_words);
        let vec = unsafe {
            crate::space::set_length_word(p, n_words, F_BYTE_OBJ | F_MUTABLE_BIT);
            p.add(0).write(PolyWord::from_bits(0));
            p.add(1).write(PolyWord::from_bits(0));
            PolyWord::from_ptr(p.cast_const())
        };

        // The stream: a 1-word byte object holding fd+1 = 1 (=> fd 0, the
        // benign "do nothing real IO" branch in both functions).
        let sp = space.alloc(1);
        let strm = unsafe {
            crate::space::set_length_word(sp, 1, F_BYTE_OBJ | F_MUTABLE_BIT);
            sp.add(0).write(PolyWord::tagged(0)); // tagged(0) bits=1 => fd_plus_one=1
            PolyWord::from_ptr(sp.cast_const())
        };

        // Helper: build a (vec, offset, length) 3-tuple in the same space.
        let mk_tuple = |space: &mut crate::space::MemorySpace, off: isize, len: isize| {
            let tp = space.alloc(3);
            unsafe {
                crate::space::set_length_word(tp, 3, 0);
                tp.add(0).write(vec);
                tp.add(1).write(PolyWord::tagged(off));
                tp.add(2).write(PolyWord::tagged(len));
                PolyWord::from_ptr(tp.cast_const())
            }
        };

        // In-bounds: off=0, len=16 == body. Both must run without faulting.
        let ok = mk_tuple(&mut space, 0, 16);
        // fd 0 write_array returns 0 ("nothing written") by design; the point
        // is it does NOT trip the bounds guard and does NOT fault.
        let _ = write_array(None, strm, ok);
        let _ = read_array_from_stream(None, strm, ok);

        // OOB: off=0, len=1<<20 >> 16-byte body. The guard must short-circuit
        // to Tagged(0) WITHOUT constructing the over-long slice (no OOB / no
        // fault). If the guard were missing this test would SIGSEGV.
        let bad_len = mk_tuple(&mut space, 0, 1 << 20);
        assert_eq!(write_array(None, strm, bad_len), PolyWord::tagged(0));
        assert_eq!(
            read_array_from_stream(None, strm, bad_len),
            PolyWord::tagged(0)
        );

        // OOB via offset: off past the body, len small.
        let bad_off = mk_tuple(&mut space, 1000, 8);
        assert_eq!(write_array(None, strm, bad_off), PolyWord::tagged(0));
        assert_eq!(
            read_array_from_stream(None, strm, bad_off),
            PolyWord::tagged(0)
        );
    }

    // Regression for Test196 (`OS.FileSys.fullPath ""` = `fullPath "."`).
    // Upstream `basicio.cpp:648` substitutes "." for the empty path
    // before `realpath`. Our `fs_full_path` previously passed "" straight
    // to `canonicalize`, which errors → the `unwrap_or_else` fell back to
    // the empty string, so `fullPath "" = ""` ≠ `fullPath "."`.
    #[test]
    fn fullpath_empty_is_cwd() {
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Immutable);
        let mut ctx = RtsContext {
            alloc_space: Some(&mut space),
            raised_exception: None,
            rts: None,
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: None,
        };
        // Build poly-string args for "" and "." in the same space.
        let empty_arg = alloc_poly_string(&mut ctx, b"");
        let dot_arg = alloc_poly_string(&mut ctx, b".");

        let empty_res = fs_full_path(&mut ctx, empty_arg);
        let dot_res = fs_full_path(&mut ctx, dot_arg);

        let empty_str = poly_string_to_rust(None, empty_res).expect("fullPath \"\" decodes");
        let dot_str = poly_string_to_rust(None, dot_res).expect("fullPath \".\" decodes");

        // The empty path must canonicalize to the cwd, not stay empty…
        assert!(!empty_str.is_empty(), "fullPath \"\" should not be empty");
        // …and must equal fullPath "." (the actual Test196 assertion).
        assert_eq!(
            empty_str, dot_str,
            "fullPath \"\" must equal fullPath \".\""
        );
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
        let r =
            poly_remainder_arbitrary(&mut ctx(), t(), PolyWord::tagged(20), PolyWord::tagged(6));
        assert_eq!(r.untag(), 2);
        let r =
            poly_remainder_arbitrary(&mut ctx(), t(), PolyWord::tagged(-20), PolyWord::tagged(6));
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
        let mut c = RtsContext {
            alloc_space: Some(&mut space),
            raised_exception: None,
            rts: None,
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: None,
        };
        let big = bigint_to_poly_word(&mut c, &(BigInt::from(1u8) << 70u32));
        let big1 = bigint_to_poly_word(&mut c, &((BigInt::from(1u8) << 70u32) + BigInt::from(1u8)));
        assert!(big.is_data_ptr() && big1.is_data_ptr(), "2^70 should box");
        assert_eq!(
            poly_compare_arbitrary(&mut c, big, big1).untag(),
            -1,
            "2^70 < 2^70+1"
        );
        assert_eq!(
            poly_compare_arbitrary(&mut c, big1, big).untag(),
            1,
            "2^70+1 > 2^70"
        );
        assert_eq!(poly_compare_arbitrary(&mut c, big, big).untag(), 0, "equal");
        // negative boxed
        let nbig = bigint_to_poly_word(&mut c, &(-(BigInt::from(1u8) << 70u32)));
        assert_eq!(
            poly_compare_arbitrary(&mut c, nbig, big).untag(),
            -1,
            "-2^70 < 2^70"
        );
    }

    #[test]
    fn arb_bitwise_and_gcd_boxed() {
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);
        let mut c = RtsContext {
            alloc_space: Some(&mut space),
            raised_exception: None,
            rts: None,
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: None,
        };
        // (2^64 | 0xF) & 0xFF == 0xF   (boxed operand -> RTS path)
        let a = bigint_to_poly_word(
            &mut c,
            &((BigInt::from(1u8) << 64u32) | BigInt::from(0xFu8)),
        );
        assert!(a.is_data_ptr());
        let r = poly_and_arbitrary(&mut c, t(), a, PolyWord::tagged(0xFF));
        assert_eq!(poly_word_to_bigint(None, r).unwrap(), BigInt::from(0xFu8));
        // gcd of two boxed multiples: gcd(2^65, 3*2^65) == 2^65
        let g1 = bigint_to_poly_word(&mut c, &(BigInt::from(1u8) << 65u32));
        let g2 = bigint_to_poly_word(&mut c, &(BigInt::from(3u8) * (BigInt::from(1u8) << 65u32)));
        let g = poly_gcd_arbitrary(&mut c, t(), g1, g2);
        assert_eq!(
            poly_word_to_bigint(None, g).unwrap(),
            BigInt::from(1u8) << 65u32
        );
    }

    /// Pack an f32 the way the interpreter's `box_float` does: f32 bits in the
    /// high 32, low bit = tag. Used to feed the Real32 RTS readers.
    fn tf32(f: f32) -> PolyWord {
        PolyWord::from_bits(((u64::from(f.to_bits()) << 32) | 1) as usize)
    }

    #[test]
    fn real32_read_write_roundtrip() {
        // read_f32_tagged is the exact inverse of the interpreter's box_float.
        for v in [2.0f32, -3.5, 0.0, -0.0, 1e30, -1e-30, f32::INFINITY] {
            assert_eq!(read_f32_tagged(tf32(v)).to_bits(), v.to_bits());
        }
    }

    #[test]
    fn real32_sqrt_floor_ceil() {
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);
        let mut c = RtsContext {
            alloc_space: Some(&mut space),
            raised_exception: None,
            rts: None,
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: None,
        };
        // RTS result is a BOXED f64 (the live dispatch path reads as_ptr::<f64>()).
        let asf32 = |w: PolyWord| -> f32 {
            assert!(w.is_data_ptr(), "Real32 RTS result must be a boxed f64");
            unsafe { *w.as_ptr::<f64>() as f32 }
        };
        assert_eq!(
            asf32(box_f32_tagged(&mut c, read_f32_tagged(tf32(4.0)).sqrt())),
            2.0
        );
        assert_eq!(
            asf32(box_f32_tagged(&mut c, read_f32_tagged(tf32(3.7)).floor())),
            3.0
        );
        assert_eq!(
            asf32(box_f32_tagged(&mut c, read_f32_tagged(tf32(3.2)).ceil())),
            4.0
        );
        assert_eq!(
            asf32(box_f32_tagged(&mut c, read_f32_tagged(tf32(3.7)).trunc())),
            3.0
        );
    }

    #[test]
    fn real32_pow_rem_nextafter() {
        assert_eq!(real_f_pow(2.0, 10.0), 1024.0);
        assert_eq!(real_f_pow(f32::NAN, 0.0), 1.0);
        assert!(real_f_pow(f32::NAN, 2.0).is_nan());
        assert_eq!(real_f_pow(0.0, -1.0), f32::INFINITY);
        assert_eq!(real_f_pow(-0.0, -3.0), f32::NEG_INFINITY); // -0 ** odd-neg
        assert_eq!(5.0f32 % 3.0f32, 2.0); // FRem = fmod semantics
        let up = next_after_f32(1.0, 2.0);
        assert!(up > 1.0 && up == f32::from_bits(1.0f32.to_bits() + 1));
        assert!(next_after_f32(f32::NAN, 1.0).is_nan());
    }

    #[test]
    fn real32_round_half_even() {
        // Magnitudes are round-half-to-EVEN, matching upstream PolyRealFRound.
        assert_eq!(poly_real_round_f32(0.5), 0.0);
        assert_eq!(poly_real_round_f32(2.5), 2.0);
        assert_eq!(poly_real_round_f32(-1.5), -2.0);
        assert_eq!(poly_real_round_f32(-2.5), -2.0);
        assert_eq!(poly_real_round_f32(3.5), 4.0);
        // Sign-of-zero MUST be +0.0 for arg in (-0.5, 0], like upstream's
        // floor(arg + 0.5) (NOT round_ties_even, which would give -0.0).
        assert!(poly_real_round_f32(-0.3).is_sign_positive());
        assert!(poly_real_round_f32(-0.5).is_sign_positive());
        assert!(poly_real_round_f32(-0.0).is_sign_positive());
        // f64 path identical.
        assert_eq!(poly_real_round_f64(2.5), 2.0);
        assert_eq!(poly_real_round_f64(-1.5), -2.0);
        assert!(poly_real_round_f64(-0.3).is_sign_positive());
        assert!(poly_real_round_f64(-0.5).is_sign_positive());
    }

    #[test]
    fn error_name_registered_arity2() {
        // OS.errorName is rtsCallFull1 -> Arity2, matching sibling ErrorMessage.
        let t = RtsTable::new();
        let tok = t.token_for("PolyProcessEnvErrorName").unwrap();
        assert_eq!(t.entry(tok).unwrap().func.arity(), 2);
    }

    #[test]
    fn error_name_returns_string() {
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);
        let mut c = RtsContext {
            alloc_space: Some(&mut space),
            raised_exception: None,
            rts: None,
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: None,
        };
        // errno 2 == ENOENT (errors.cpp errortable). Must return a BOXED string.
        let r = poly_process_env_error_name(&mut c, t(), PolyWord::tagged(2));
        assert!(
            r.is_data_ptr(),
            "errorName must return a boxed string, not tagged(0)"
        );
        assert_eq!(poly_string_to_rust(None, r).as_deref(), Some("ENOENT"));
        // Unknown code falls back to ERROR<n> (process_env.cpp:255).
        let r = poly_process_env_error_name(&mut c, t(), PolyWord::tagged(99999));
        assert_eq!(poly_string_to_rust(None, r).as_deref(), Some("ERROR99999"));
    }

    // unsafe-audit finding #8: poly_string_to_rust used to over-read past the
    // object body if word-0 (the stored byte length) lied, and read a non-byte
    // object's word 0 as a length. The guard (is_byte_object + len fits body)
    // must reject both WITHOUT performing the OOB read.
    #[test]
    fn poly_string_to_rust_rejects_oversized_length() {
        use crate::length_word::{F_BYTE_OBJ, F_MUTABLE_BIT};
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);
        // A well-formed 2-word byte string: word0 = byte length 2, word1 holds
        // the chars 'o','k' (low bytes), like a real PolyStringObject.
        let good = space.alloc(2);
        let good_w = unsafe {
            crate::space::set_length_word(good, 2, F_BYTE_OBJ | F_MUTABLE_BIT);
            good.add(0).write(PolyWord::from_bits(2)); // byte length 2
            let chars = (b'o' as usize) | ((b'k' as usize) << 8);
            good.add(1).write(PolyWord::from_bits(chars));
            PolyWord::from_ptr(good.cast_const())
        };
        assert_eq!(
            poly_string_to_rust(None, good_w).as_deref(),
            Some("ok"),
            "a well-formed PolyString must still decode"
        );

        // (a) A 1-word byte object whose word-0 length LIES (900_000 >> 8-byte
        // body). The pre-fix code would from_raw_parts(.., 900_000) -> OOB read.
        let liar = space.alloc(1);
        let liar_w = unsafe {
            crate::space::set_length_word(liar, 1, F_BYTE_OBJ | F_MUTABLE_BIT);
            liar.add(0).write(PolyWord::from_bits(900_000));
            PolyWord::from_ptr(liar.cast_const())
        };
        assert_eq!(
            poly_string_to_rust(None, liar_w),
            None,
            "an oversized stored length must be rejected, not over-read"
        );

        // (b) A non-byte (word/tuple) object. Pre-fix, its word 0 (a pointer or
        // data slot) would be mis-read as a byte length.
        let tup = space.alloc(2);
        let tup_w = unsafe {
            crate::space::set_length_word(tup, 2, 0); // type 0 = word object
            tup.add(0).write(PolyWord::tagged(5));
            tup.add(1).write(PolyWord::tagged(7));
            PolyWord::from_ptr(tup.cast_const())
        };
        assert_eq!(
            poly_string_to_rust(None, tup_w),
            None,
            "a non-byte object must be rejected (no is_byte_object -> length confusion)"
        );

        // A tagged int is rejected by the existing is_data_ptr gate.
        assert_eq!(poly_string_to_rust(None, PolyWord::tagged(42)), None);
    }

    #[test]
    fn timing_get_now_and_real_advance() {
        let mut space = crate::space::MemorySpace::new(256, crate::space::SpaceKind::Mutable);
        let mut c = RtsContext {
            alloc_space: Some(&mut space),
            raised_exception: None,
            rts: None,
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: None,
        };
        let table = RtsTable::new();
        let call = |c: &mut RtsContext<'_>, name: &str| -> i128 {
            let tok = table.token_for(name).unwrap();
            let w = match table.entry(tok).unwrap().func {
                RtsFn::Arity1(f) => f(c, PolyWord::tagged(0)),
                _ => panic!("arity"),
            };
            poly_word_to_bigint(None, w)
                .and_then(|n| num_traits::ToPrimitive::to_i128(&n))
                .unwrap()
        };
        // GetNow is microseconds since the epoch — far larger than the old
        // tagged(0) stub, and well past year-2020 in microseconds (1.5e15).
        let now = call(&mut c, "PolyTimingGetNow");
        assert!(
            now > 1_500_000_000_000_000,
            "getNow should be epoch microseconds, got {now}"
        );
        // GetReal is monotonic non-decreasing across two reads.
        let r1 = call(&mut c, "PolyTimingGetReal");
        let r2 = call(&mut c, "PolyTimingGetReal");
        assert!(
            r2 >= r1 && r1 >= 0,
            "getReal should be monotonic, {r1} then {r2}"
        );
        // GetUser/GetSystem are non-negative CPU microseconds.
        assert!(call(&mut c, "PolyTimingGetUser") >= 0);
        assert!(call(&mut c, "PolyTimingGetSystem") >= 0);
    }

    #[test]
    fn arb_and_neg_tagged_boxed_repro() {
        // andb(~1, 2^80): ~1 is all-ones in two's complement, so the result
        // must be 2^80. Differential test vs upstream caught ours returning 0.
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);
        let mut c = RtsContext {
            alloc_space: Some(&mut space),
            raised_exception: None,
            rts: None,
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: None,
        };
        let big = bigint_to_poly_word(&mut c, &(BigInt::from(1u8) << 80u32));
        assert!(big.is_data_ptr(), "2^80 must box");
        let r = poly_and_arbitrary(&mut c, t(), PolyWord::tagged(-1), big);
        assert_eq!(
            poly_word_to_bigint(None, r).unwrap(),
            BigInt::from(1u8) << 80u32
        );
    }

    #[test]
    fn arb_and_min_tagged_boxed_repro() {
        // andb(-2^62, 2^62): -2^62 = MIN_TAGGED (tagged), 2^62 boxed.
        // Two's-complement: result must be 2^62. Differential vs upstream
        // caught ours returning -2^62 (sub_core_rts fuzz, 2026-06-20).
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);
        let mut c = RtsContext {
            alloc_space: Some(&mut space),
            raised_exception: None,
            rts: None,
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: None,
        };
        let p62 = BigInt::from(1u8) << 62u32;
        let boxed_p62 = bigint_to_poly_word(&mut c, &p62);
        assert!(boxed_p62.is_data_ptr(), "2^62 must box");
        let neg_p62 = PolyWord::tagged(MIN_TAGGED); // -2^62
        assert_eq!(BigInt::from(neg_p62.untag()), -&p62);
        let r = poly_and_arbitrary(&mut c, t(), neg_p62, boxed_p62);
        assert_eq!(
            poly_word_to_bigint(None, r).unwrap(),
            p62.clone(),
            "andb(-2^62, 2^62) should be 2^62"
        );
        // And the 0-returning case: andb(-2^62, 2^64) = 2^64.
        let p64 = BigInt::from(1u8) << 64u32;
        let boxed_p64 = bigint_to_poly_word(&mut c, &p64);
        let r2 = poly_and_arbitrary(&mut c, t(), PolyWord::tagged(MIN_TAGGED), boxed_p64);
        assert_eq!(
            poly_word_to_bigint(None, r2).unwrap(),
            p64,
            "andb(-2^62, 2^64) should be 2^64"
        );
    }

    #[test]
    fn arb_lcm_signed_convention() {
        // Upstream lcm = x * (y / gcd), SIGNED: sign(result) = sign(x)*sign(y).
        // Differential fuzz vs upstream (2026-06-20) caught ours returning |lcm|.
        let lcm = |a: isize, b: isize| {
            poly_lcm_arbitrary(&mut ctx(), t(), PolyWord::tagged(a), PolyWord::tagged(b)).untag()
        };
        assert_eq!(lcm(6, 4), 12, "lcm(6,4)");
        assert_eq!(lcm(-6, 4), -12, "lcm(-6,4)");
        assert_eq!(lcm(6, -4), -12, "lcm(6,-4)");
        assert_eq!(lcm(-6, -4), 12, "lcm(-6,-4)");
        assert_eq!(lcm(0, 5), 0, "lcm(0,5)");
        assert_eq!(lcm(5, 0), 0, "lcm(5,0)");
        // BigInt path: lcm(-2^80, 6). |lcm| = 2^80*3 = 3*2^80; signed = negative.
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);
        let mut c = RtsContext {
            alloc_space: Some(&mut space),
            raised_exception: None,
            rts: None,
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: None,
        };
        // lcm(0,0) divides by zero (gcd=0) → upstream raises Div.
        let _ = poly_lcm_arbitrary(&mut c, t(), PolyWord::tagged(0), PolyWord::tagged(0));
        assert!(c.raised_exception.is_some(), "lcm(0,0) should raise Div");
        c.raised_exception = None;
        let neg_p80 = bigint_to_poly_word(&mut c, &(-(BigInt::from(1u8) << 80u32)));
        let r = poly_lcm_arbitrary(&mut c, t(), neg_p80, PolyWord::tagged(6));
        assert_eq!(
            poly_word_to_bigint(None, r).unwrap(),
            -((BigInt::from(1u8) << 80u32) * BigInt::from(3u8)),
            "lcm(-2^80, 6) should be -(3*2^80)"
        );
        // Tagged-OVERFLOW case: lcm(2^62-1, 100). Both tagged, but |lcm| exceeds
        // usize so the tagged path must FALL THROUGH to BigInt (was returning 0).
        let max_tag = MAX_TAGGED; // 2^62 - 1
        let r2 = poly_lcm_arbitrary(
            &mut c,
            t(),
            PolyWord::tagged(max_tag),
            PolyWord::tagged(100),
        );
        use num_integer::Integer as _NumInteger;
        let mt = BigInt::from(max_tag);
        let expected = &mt / mt.gcd(&BigInt::from(100)) * BigInt::from(100);
        assert_eq!(
            poly_word_to_bigint(None, r2).unwrap(),
            expected,
            "lcm(2^62-1, 100) must not truncate to 0"
        );
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
        let r =
            poly_shift_left_arbitrary(&mut ctx(), t(), PolyWord::tagged(5), PolyWord::tagged(3));
        assert_eq!(r.untag(), 40);
    }

    #[test]
    fn arb_shift_right_simple() {
        let r =
            poly_shift_right_arbitrary(&mut ctx(), t(), PolyWord::tagged(40), PolyWord::tagged(3));
        assert_eq!(r.untag(), 5);
    }

    #[test]
    fn arb_shift_right_negative_is_arithmetic() {
        // `IntInf.~>>` is an ARITHMETIC (floor) shift: -40 ~>> 3 = -5, not a huge
        // positive. Regression for the logical-shift-on-negatives bug.
        let r =
            poly_shift_right_arbitrary(&mut ctx(), t(), PolyWord::tagged(-40), PolyWord::tagged(3));
        assert_eq!(r.untag(), -5);
        // floor rounding toward -inf: -1 ~>> 1 = -1 (not 0).
        let r =
            poly_shift_right_arbitrary(&mut ctx(), t(), PolyWord::tagged(-1), PolyWord::tagged(1));
        assert_eq!(r.untag(), -1);
    }

    #[test]
    fn arb_shift_left_negative_preserves_sign() {
        // -5 << 3 = -40.
        let r =
            poly_shift_left_arbitrary(&mut ctx(), t(), PolyWord::tagged(-5), PolyWord::tagged(3));
        assert_eq!(r.untag(), -40);
    }

    #[test]
    fn arb_shift_left_boxes_large_result() {
        // 1 << 70 doesn't fit in a tagged int — must box (old tagged-only path
        // returned 0). Needs an alloc space.
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);
        let mut c = RtsContext {
            alloc_space: Some(&mut space),
            raised_exception: None,
            rts: None,
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: None,
        };
        let r = poly_shift_left_arbitrary(&mut c, t(), PolyWord::tagged(1), PolyWord::tagged(70));
        assert!(r.is_data_ptr(), "1<<70 should be boxed");
        let bi = poly_word_to_bigint(None, r).expect("readable bignum");
        assert_eq!(bi, BigInt::from(1u128 << 70));
        // round-trip back down: (1<<70) ~>> 70 = 1.
        let back = poly_shift_right_arbitrary(&mut c, t(), r, PolyWord::tagged(70));
        assert_eq!(back.untag(), 1);
    }

    #[test]
    fn get_low_order_negates_negative_boxed() {
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Mutable);
        let mut c = RtsContext {
            alloc_space: Some(&mut space),
            raised_exception: None,
            rts: None,
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: None,
        };
        // -(2^64 + 7): magnitude needs >64 bits so it boxes; negative-flagged.
        let n = -(BigInt::from(1u128 << 64) + BigInt::from(7u8));
        let boxed = bigint_to_poly_word(&mut c, &n);
        assert!(boxed.is_data_ptr(), "value should box");
        let res = poly_get_low_order_as_large_word(&mut c, t(), boxed);
        // low limb of magnitude (2^64+7) is 7; two's-complement-negated = -7.
        let low = unsafe { *res.as_ptr::<usize>() };
        assert_eq!(
            low,
            0usize.wrapping_sub(7),
            "negative boxed low word must be negated"
        );
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
        let g = poly_gcd_arbitrary(&mut ctx(), t(), PolyWord::tagged(12), PolyWord::tagged(18));
        assert_eq!(g.untag(), 6);
        let l = poly_lcm_arbitrary(&mut ctx(), t(), PolyWord::tagged(4), PolyWord::tagged(6));
        assert_eq!(l.untag(), 12);
    }

    #[test]
    fn arb_mult_no_overflow_stays_tagged() {
        let mut ctx = ctx();
        // Both small — should stay tagged.
        let r =
            poly_multiply_arbitrary(&mut ctx, t(), PolyWord::tagged(123), PolyWord::tagged(456));
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
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: None,
        };
        let r = poly_multiply_arbitrary(
            &mut ctx,
            t(),
            PolyWord::tagged(1 << 31),
            PolyWord::tagged(1 << 31),
        );
        assert!(
            r.is_data_ptr(),
            "2^62 should be boxed (MAX_TAGGED = 2^62-1)"
        );
        let bi = poly_word_to_bigint(None, r).expect("readable bignum");
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
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: None,
        };
        let a = PolyWord::tagged(-(1 << 31));
        let b = PolyWord::tagged(1 << 32);
        let r = poly_multiply_arbitrary(&mut ctx, t(), a, b);
        assert!(r.is_data_ptr(), "expected boxed");
        let bi = poly_word_to_bigint(None, r).expect("readable");
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
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: None,
        };
        // 2^31 * 2^32 = 2^63 which exceeds MAX_TAGGED.
        let a = PolyWord::tagged(1 << 31);
        let b = PolyWord::tagged(1 << 32);
        let r = poly_multiply_arbitrary(&mut ctx, PolyWord::tagged(0), a, b);
        assert!(r.is_data_ptr(), "expected boxed bignum, got {r:?}");
        // Read it back via our converter.
        let bi = poly_word_to_bigint(None, r).expect("readable bignum");
        assert_eq!(bi, BigInt::from(1u64 << 63), "wrong product");
    }

    // ================================================================
    // task #132 — the header-fit RTS-arg gate (RtsValidObj /
    // safe_rts_arg_obj / RtsSafeSpaces::validate_obj_fit).
    // ================================================================

    /// Build an `RtsSafeSpaces` covering exactly `[storage_start,
    /// storage_start + used_words)` of a `MemorySpace` — mirroring the live
    /// snapshot the interpreter hands the RTS in untrusted mode.
    fn rts_spaces_of(space: &crate::space::MemorySpace) -> RtsSafeSpaces {
        let start = space.storage_bytes().as_ptr() as usize;
        let end = start + space.used_words() * std::mem::size_of::<PolyWord>();
        RtsSafeSpaces {
            ranges: vec![(start, end)],
        }
    }

    /// The gate ACCEPTS a legitimate in-space object and reports its true body
    /// word count; the validated handle bounds each access correctly.
    #[test]
    fn rts_arg_obj_accepts_valid_and_reports_words() {
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Immutable);
        let obj = space.alloc(3);
        // SAFETY: just allocated 3 words.
        unsafe { crate::space::set_length_word(obj, 3, 0) };
        let spaces = rts_spaces_of(&space);
        let w = PolyWord::from_ptr(obj.cast_const());

        let v = safe_rts_arg_obj(Some(&spaces), w).expect("valid object accepted");
        assert_eq!(v.n_words, 3);
        assert!(v.word_in_bounds(0) && v.word_in_bounds(2));
        assert!(!v.word_in_bounds(3), "index 3 is OOB for a 3-word object");
        assert_eq!(
            v.clamp_body_words(1_000_000),
            3,
            "clamped to validated size"
        );
        assert_eq!(v.clamp_body_words(2), 2);
    }

    /// THE CORE REJECTION: a FORGED length word that over-claims the object
    /// (so the body would run past the space end) is rejected — the gate does
    /// NOT hand back a handle a multi-word reader could over-read through.
    #[test]
    fn rts_arg_obj_rejects_forged_oversized_header() {
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Immutable);
        let obj = space.alloc(2);
        // Forge a length word claiming a million-word object that runs far past
        // the space end (the exact over-read primitive a hostile image uses).
        // SAFETY: writing the length word of a just-allocated object.
        unsafe { crate::space::set_length_word(obj, 1_000_000, 0) };
        let spaces = rts_spaces_of(&space);
        let w = PolyWord::from_ptr(obj.cast_const());
        assert!(
            safe_rts_arg_obj(Some(&spaces), w).is_none(),
            "an over-claiming header must be rejected (header-fit)"
        );
        // The string / bigint readers route the forged arg through the gate,
        // so they yield the clean non-pointer result instead of over-reading.
        assert_eq!(
            poly_word_to_bigint(Some(&spaces), w),
            None,
            "bigint reader must not over-read a forged-length object"
        );
        assert_eq!(poly_string_to_rust(Some(&spaces), w), None);
    }

    /// BOUNDARY: an object whose claimed length EXACTLY fits the space is
    /// accepted; claiming one word more (which would escape the slack) is
    /// rejected. Proves the fit check is tight, not slack-dependent.
    #[test]
    fn rts_arg_obj_boundary_exact_fit_vs_one_over() {
        // capacity = 4 words: [len][w0][w1][w2]. Allocate a 3-word object so
        // its body occupies exactly w0..w2 (the last word is the space end).
        let mut space = crate::space::MemorySpace::new(4, crate::space::SpaceKind::Immutable);
        let obj = space.alloc(3);
        let spaces = rts_spaces_of(&space); // end == start + 4 words
        let w = PolyWord::from_ptr(obj.cast_const());

        // Exact fit: length 3 -> body [p, p+3) == [w0, end). Accepted.
        // SAFETY: writing the length word of a just-allocated object.
        unsafe { crate::space::set_length_word(obj, 3, 0) };
        assert_eq!(
            safe_rts_arg_obj(Some(&spaces), w).map(|v| v.n_words),
            Some(3),
            "an object that exactly fills the space must be accepted"
        );

        // One over: length 4 -> body would run one word past the space end.
        // SAFETY: writing the length word of a just-allocated object.
        unsafe { crate::space::set_length_word(obj, 4, 0) };
        assert!(
            safe_rts_arg_obj(Some(&spaces), w).is_none(),
            "a one-word-too-long header must be rejected"
        );
    }

    /// The gate rejects non-pointer / wild / misaligned args (no deref).
    #[test]
    fn rts_arg_obj_rejects_tagged_wild_and_misaligned() {
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Immutable);
        let obj = space.alloc(2);
        // SAFETY: writing the length word of a just-allocated object.
        unsafe { crate::space::set_length_word(obj, 2, 0) };
        let spaces = rts_spaces_of(&space);

        // Tagged int: not a pointer.
        assert!(safe_rts_arg_obj(Some(&spaces), PolyWord::tagged(5)).is_none());
        // Wild pointer far outside the space.
        let wild = PolyWord::from_bits(0x4000_0000_0000_usize & !1);
        assert!(safe_rts_arg_obj(Some(&spaces), wild).is_none());
        // Misaligned but in-range: rejected before any (UB) length-word read.
        let p = obj as usize;
        let misaligned = PolyWord::from_bits(p | 0x2);
        assert!(
            safe_rts_arg_obj(Some(&spaces), misaligned).is_none(),
            "a misaligned arg must be rejected before the length-word read"
        );
    }

    /// TRUSTED MODE is byte-identical: `spaces == None` yields an UNBOUNDED
    /// handle (the legacy is_data_ptr fast path) — every bound check passes and
    /// no header is read, so the readers behave exactly as before.
    #[test]
    fn rts_arg_obj_trusted_is_unbounded_fast_path() {
        let mut space = crate::space::MemorySpace::new(64, crate::space::SpaceKind::Immutable);
        let obj = space.alloc(1);
        // SAFETY: writing the length word of a just-allocated object.
        unsafe { crate::space::set_length_word(obj, 1, 0) };
        let w = PolyWord::from_ptr(obj.cast_const());

        let v = safe_rts_arg_obj(None, w).expect("trusted accepts any data ptr");
        assert_eq!(v.n_words, usize::MAX, "trusted sentinel = unbounded");
        assert!(v.word_in_bounds(0) && v.word_in_bounds(1_000_000));
        // clamp is a no-op in trusted mode (the reader uses its own length).
        assert_eq!(v.clamp_body_words(7), 7);
        // A tagged int is still rejected (matches the legacy is_data_ptr gate).
        assert!(safe_rts_arg_obj(None, PolyWord::tagged(1)).is_none());
    }
}
