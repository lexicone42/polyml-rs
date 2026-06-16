//! PolyML bytecode interpreter.
//!
//! Faithful port of the dispatch shape in
//! `vendor/polyml/libpolyml/bytecode.cpp`. The stack grows **down**
//! (matching PolyML): `push` decrements the stack pointer, `pop`
//! increments it. `sp[N]` peeks N deep (0 = top).
//!
//! ## PC representation
//!
//! PC is a raw `*const u8` pointer into a code object's instruction
//! bytes. This is necessary because:
//!
//! - Calls move PC between code objects (each closure points at its
//!   own code's bytes).
//! - PC-relative addressing (`CONST_ADDR8_8`, `CALL_CONST_ADDR8_8`)
//!   computes constant-pool offsets via raw byte arithmetic — `pc +
//!   imm` must land in the constant pool that immediately follows the
//!   code bytes in the same heap object.
//!
//! ## Calling convention (per bytecode.cpp:411-424)
//!
//! ```text
//! Before CALL: stack top is [closure, arg_last, ..., arg_first]
//!                            ^ sp
//!
//! CALL pops closure, pushes return-PC, pushes closure:
//!
//! After CALL:  stack top is [closure, retPC, arg_last, ..., arg_first]
//!                            ^ sp
//!
//! Callee runs, possibly pushing its own locals on top.
//! ```
//!
//! On RETURN_N (bytecode.cpp:454-465):
//!
//! ```text
//!   result = pop()           ; top
//!   sp++                     ; drop closure
//!   pc = pop().codeAddr      ; restore return PC
//!   sp += N                  ; drop N args
//!   push(result)
//! ```
//!
//! ## Top-level return sentinel
//!
//! The initial return PC is set to **null** by `enter_top_level`.
//! When `RETURN_*` would restore PC to null, the interpreter yields
//! `StepResult::Returned(value)` instead of jumping.
//!
//! ## Scope
//!
//! The full bytecode opcode set used by the PolyML bootstrap and the
//! HOL4 / Isabelle workloads is implemented: see [`Interpreter::step`]
//! for the primary dispatch and `dispatch_extended` for the ESCAPE
//! (`0xfe`) extended set. This covers ALU (const/fixed/word/compare),
//! stack ops (local/indirect/reset), control flow (jump family),
//! calls/returns/tail calls, allocation, exceptions and handlers, heap
//! mutation, RTS calls, closure construction, and the float/container
//! opcodes. Genuinely unmodelled cases return `InterpError::Unimplemented`.

// Interpreter-wide allows: the signed/unsigned reinterpretation of
// PolyWord bits is intentional (matches PolyML's `UNTAGGED` casting
// pattern in bytecode.cpp). Pointer-alignment casts in the
// PC-relative const loaders are safe because we always use
// `read_unaligned()`, which clippy can't track.
#![allow(clippy::cast_sign_loss)]
#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::manual_div_ceil)]
#![allow(clippy::cast_ptr_alignment)]
#![allow(clippy::similar_names)]
#![allow(clippy::wildcard_imports)]

pub mod diag;
pub mod disasm;
pub mod opcodes;

use diag::DiagState;

use std::sync::Arc;

use crate::poly_word::PolyWord;
use crate::rts::{RtsContext, RtsFn, RtsTable};
use crate::space::{MemorySpace, SpaceKind};
use thiserror::Error;

// ---- ARBINT_DEBUG opcode ring buffer (diagnostic for the arbitrary-int basis
// load wall). Records (code_start, pc_offset, opcode, sp_depth) for the last N
// executed opcodes; dumped at the INSTR_STORE_ML_WORD imbalance crash so a PC
// desync or stack-imbalance is visible. Gated behind a cached env flag so it
// costs nothing in normal runs.
thread_local! {
    static OP_RING: std::cell::RefCell<std::collections::VecDeque<(usize, u32, u8, usize)>> =
        std::cell::RefCell::new(std::collections::VecDeque::with_capacity(192));
}
fn arbint_trace_on() -> bool {
    use std::sync::atomic::{AtomicU8, Ordering};
    static F: AtomicU8 = AtomicU8::new(0);
    match F.load(Ordering::Relaxed) {
        1 => true,
        2 => false,
        _ => {
            let on = std::env::var("ARBINT_DEBUG").is_ok();
            F.store(if on { 1 } else { 2 }, Ordering::Relaxed);
            on
        }
    }
}

/// Memoized read of `JIT_TRACE_RETURNS` (see [`arbint_trace_on`] for the
/// cache discipline). `do_return` is one of the hottest paths, so reading
/// the env var per-return (allocating a `String` + scanning the environ)
/// is exactly the regression class the GC-threshold cache fixed (6.2x);
/// this caches it the same way. The diagnostic is virtually never enabled
/// and the env is read once at process start in practice, so the observable
/// behavior is identical.
fn jit_trace_returns_on() -> bool {
    use std::sync::atomic::{AtomicU8, Ordering};
    static F: AtomicU8 = AtomicU8::new(0);
    match F.load(Ordering::Relaxed) {
        1 => true,
        2 => false,
        _ => {
            let on = std::env::var("JIT_TRACE_RETURNS").is_ok();
            F.store(if on { 1 } else { 2 }, Ordering::Relaxed);
            on
        }
    }
}

/// Memoized read of `JIT_TRACE_STORES` (see [`arbint_trace_on`]).
/// `INSTR_STORE_ML_WORD` is a hot heap-mutation opcode; a per-store
/// `String` alloc + environ scan is the same footgun the env-var cache
/// discipline exists to avoid.
fn jit_trace_stores_on() -> bool {
    use std::sync::atomic::{AtomicU8, Ordering};
    static F: AtomicU8 = AtomicU8::new(0);
    match F.load(Ordering::Relaxed) {
        1 => true,
        2 => false,
        _ => {
            let on = std::env::var("JIT_TRACE_STORES").is_ok();
            F.store(if on { 1 } else { 2 }, Ordering::Relaxed);
            on
        }
    }
}

/// Memoized read of `JIT_TRACE_CALLS` (see [`arbint_trace_on`]). Read once
/// per JIT-dispatched call instead of twice via raw `env::var`; only
/// matters when `--jit` is enabled but keeps the JIT trace path consistent
/// with the cached-flag discipline.
fn jit_trace_calls_on() -> bool {
    use std::sync::atomic::{AtomicU8, Ordering};
    static F: AtomicU8 = AtomicU8::new(0);
    match F.load(Ordering::Relaxed) {
        1 => true,
        2 => false,
        _ => {
            let on = std::env::var("JIT_TRACE_CALLS").is_ok();
            F.store(if on { 1 } else { 2 }, Ordering::Relaxed);
            on
        }
    }
}

/// Result of one (`step`) or many (`run`) interpreter steps.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StepResult {
    /// Keep going.
    Continue,
    /// A `return_*` opcode fired with a null return address (the
    /// top-level sentinel). The value carried is the popped result.
    Returned(PolyWord),
    /// The interpreter hit an opcode it doesn't know yet. PC has been
    /// rolled back to point AT the unknown op (or the ESCAPE prefix
    /// for extended opcodes — `extended` is true in that case).
    Unimplemented { op: u8, extended: bool },
}

#[derive(Debug, Clone, Error)]
pub enum InterpError {
    #[error("stack overflow")]
    StackOverflow,
    #[error("stack underflow")]
    StackUnderflow,
    #[error("pc out of bounds (offset {offset} into segment of {size} bytes)")]
    PcOutOfBounds { offset: usize, size: usize },
    #[error("division by zero")]
    DivByZero,
    #[error("call to non-closure value: {0:?}")]
    NotAClosure(PolyWord),
    #[error("interpreter has no allocation space attached")]
    NoAllocator,
    #[error("unhandled exception (no handler in scope)")]
    UnhandledException,
    #[error("CALL_FAST_RTS{n} on an unresolved entry point (token=0)")]
    UnresolvedRts { n: usize },
    #[error("CALL_FAST_RTS{op_arity} on RTS function {name} of arity {fn_arity}")]
    RtsArityMismatch {
        name: &'static str,
        op_arity: usize,
        fn_arity: usize,
    },
}

/// A bytecode interpreter operating on PolyML code objects.
///
/// The PC is a raw `*const u8` pointer; the interpreter does not own
/// the code bytes. For tests, `from_bytes` allocates a backing `Vec<u8>`
/// stored in `_owned_code` so the pointer stays valid for the
/// interpreter's lifetime.
pub struct Interpreter {
    /// Backing storage for the ML stack. Grows down. Boxed so it has
    /// a stable memory address — stack-container refs (per
    /// `bytecode.cpp`'s `stackAddr` union variant) are REAL pointers
    /// into this slice, not indices, and need addresses that don't
    /// move under us.
    stack: Box<[PolyWord]>,
    /// Index of the topmost live element. `sp == stack.len()` means
    /// "empty" (the SP is just past the end, ready for the next push
    /// to decrement-then-write).
    sp: usize,
    /// Pointer to the next byte to fetch.
    pc: *const u8,
    /// Start of the currently-executing code object's byte segment
    /// (for bounds checking and PC-rollback on Unimplemented).
    code_start: *const u8,
    /// One past the end of the code segment (exclusive bound).
    code_end: *const u8,
    /// Per-call side-stack of caller code segment bounds. PolyML's
    /// own interpreter doesn't track these because it doesn't
    /// bounds-check; we use them so safety-net errors surface
    /// instead of out-of-bounds reads.
    /// Entries are (code_start, code_end) pushed on every CALL and
    /// popped on every RETURN.
    frames: Vec<(*const u8, *const u8)>,
    /// Bump-allocation region for objects created at runtime
    /// (closures, tuples, refs). `None` means the interpreter will
    /// trap `InterpError::NoAllocator` on any allocation op.
    alloc_space: Option<MemorySpace>,
    /// Pre-computed GC threshold in words (= `alloc_space.capacity *
    /// threshold_percent / 100`). 0 = "never auto-GC", set when
    /// either `alloc_space` is None or `POLYML_GC_THRESHOLD` is
    /// configured to a value outside (1..=99). On every step we
    /// compare `alloc_space.used_words()` against this; cheaper than
    /// the previous `used * 100 >= cap * thresh`.
    gc_trigger_words: usize,
    /// "Handler register" — index into `stack` where the most-recent
    /// exception-handler frame sits. `stack.len()` (past-the-end)
    /// means no handler in scope.
    handler_sp: usize,
    /// Parallel stack tracking, for each registered handler, the
    /// call-frame depth AND the code-segment bounds at the time
    /// it was installed. RAISE_EX uses this to roll `self.frames`
    /// back to the right depth AND restore the handler's owning
    /// code segment (which is the function that did SET_HANDLER —
    /// NOT the caller, since the handler's PC lives in that
    /// function's code bytes).
    handler_frames_depth: Vec<(usize, *const u8, *const u8)>,
    /// Current exception packet (set by RAISE_EX, read by LDEXC).
    /// `None` means no exception has been raised yet.
    exception_packet: Option<PolyWord>,
    /// RTS function table — used to dispatch CALL_FAST_RTS<N> opcodes.
    /// `Arc` so it can be shared between interpreter instances (e.g.
    /// threads).
    rts: Arc<RtsTable>,
    /// For test-built interpreters: owns the code bytes so the PC
    /// pointer stays valid.
    _owned_code: Option<Vec<u8>>,
    /// Ring buffer of the last N CALL_CLOSURE target addresses,
    /// kept unconditionally with small fixed cost. Used by the
    /// LOAD_UNTAGGED bad-base diagnostic so we can see what was
    /// recently called before the failure.
    recent_call_targets: [usize; 16],
    recent_call_idx: usize,
    /// Pointer + word-length pairs identifying mutable image-space
    /// regions to scan as GC roots. Each call to
    /// `with_image_mutable_root` appends here.
    image_mutable_roots: Vec<(*const PolyWord, usize)>,
    /// Cached singleton thread object returned by `INSTR_GET_THREAD_ID`
    /// (= `Thread.self()`). Must be the SAME object every call so thread
    /// identity is stable and `Thread.setLocal`/`getLocal` (which store data
    /// in this object) work — `Thread_Data`, and hence Isabelle's generic
    /// context, depend on it. Allocated lazily; forwarded by the GC as a root.
    thread_object: Option<PolyWord>,
    /// Optional execution-profile collector. `None` = disabled (the
    /// hot path pays only a branch). Enable with
    /// [`enable_diagnostics`](Self::enable_diagnostics).
    diag: Option<DiagState>,
    /// JIT cache: maps code-object pointer (as `usize`) to a JIT'd
    /// native function. When `do_call`'s target is in this cache,
    /// it dispatches to the JIT'd version instead of interpreting.
    /// Empty = transparent fallthrough; never affects unjitted code.
    jit_cache: std::collections::HashMap<usize, JitEntry>,
}

/// A cached JIT'd function with the metadata needed to invoke it
/// using the interpreter's calling convention.
#[derive(Clone, Copy)]
pub struct JitEntry {
    /// Native entry point. ABI (matches `polyml_jit::translate::JitFn`):
    ///   `extern "C" fn(args_ptr, sp_in, stack_base) -> raw_polyword`
    /// where `args_ptr` is a `[i64; arity_init]` buffer, `sp_in` is
    /// the initial `interp.sp` value, and `stack_base` is
    /// `interp.stack.as_mut_ptr() as i64`. The two trailing params
    /// are reserved for the memory-backed translator (Phase 2 of the
    /// stack-pointer refactor); currently ignored by all generated
    /// code. Callers must still pass valid values.
    pub func: unsafe extern "C" fn(*const i64, i64, i64) -> i64,
    /// Inferred arg count (= the `args_ptr` length the JIT expects).
    /// Typically `sml_arity + 2` to cover the closure + retPC slots
    /// that `LOCAL_0`/`LOCAL_1` access.
    pub arity_init: usize,
    /// SML arity = number of args the call site pushed (excluding
    /// the closure + retPC the CALL opcode pushes). RETURN_N pops
    /// this many args after popping the result.
    pub sml_arity: usize,
}

impl Interpreter {
    /// Build an interpreter from an owned byte slice. PC starts at
    /// byte 0. The bytes are NOT a real PolyML code object — there's
    /// no constant pool, no length word — so PC-relative addressing
    /// opcodes will produce undefined results. Use this constructor
    /// for hand-crafted ALU/control-flow tests only.
    #[must_use]
    pub fn from_bytes(stack_capacity: usize, code: Vec<u8>) -> Self {
        let code = code.into_boxed_slice().into_vec(); // ensure stable alloc
        let start: *const u8 = code.as_ptr();
        // SAFETY: `code` is non-empty in normal use; for empty input
        // start == end, which is a valid (immediately-EOF) state.
        let end: *const u8 = unsafe { start.add(code.len()) };
        Self {
            stack: vec![PolyWord::ZERO; stack_capacity].into_boxed_slice(),
            sp: stack_capacity,
            pc: start,
            code_start: start,
            code_end: end,
            frames: Vec::new(),
            alloc_space: None,
            gc_trigger_words: 0,
            handler_sp: stack_capacity, // past-the-end = no handler
            handler_frames_depth: Vec::new(),
            exception_packet: None,
            recent_call_targets: [0; 16],
            recent_call_idx: 0,
            image_mutable_roots: Vec::new(),
            thread_object: None,
            rts: Arc::new(RtsTable::empty()),
            _owned_code: Some(code),
            diag: None,
            jit_cache: std::collections::HashMap::new(),
        }
    }

    /// Build an interpreter that will execute the code bytes of an
    /// existing PolyML code object. Reads the length word and the
    /// trailing-offset to figure out where the bytes end (i.e., where
    /// the constant pool begins).
    ///
    /// # Safety
    /// `code_obj` must point at a valid, fully-initialised code
    /// object as laid out by [`crate::loader`]. The object must
    /// remain live for the interpreter's lifetime.
    #[must_use]
    pub unsafe fn from_code_object(stack_capacity: usize, code_obj: *const PolyWord) -> Self {
        use crate::length_word;
        // SAFETY: caller upholds.
        let (consts_start, _consts_count) =
            unsafe { length_word::const_segment_for_code(code_obj) };
        let start: *const u8 = code_obj.cast::<u8>();
        // Constant pool begins at consts_start; bytes end one word
        // before that (the const-count word). For our bounds, accept
        // bytes up to consts_start cast to u8* — the count word is
        // word-aligned data that compiled code shouldn't try to
        // execute, but it's harmless to allow PC there.
        let end: *const u8 = consts_start.cast::<u8>();
        Self {
            stack: vec![PolyWord::ZERO; stack_capacity].into_boxed_slice(),
            sp: stack_capacity,
            pc: start,
            code_start: start,
            code_end: end,
            frames: Vec::new(),
            alloc_space: None,
            gc_trigger_words: 0,
            handler_sp: stack_capacity,
            handler_frames_depth: Vec::new(),
            exception_packet: None,
            recent_call_targets: [0; 16],
            recent_call_idx: 0,
            image_mutable_roots: Vec::new(),
            thread_object: None,
            rts: Arc::new(RtsTable::empty()),
            _owned_code: None,
            diag: None,
            jit_cache: std::collections::HashMap::new(),
        }
    }

    /// Install a JIT'd version of a code object's bytecode. When
    /// `do_call`'s target closure has `code_obj_ptr` matching one
    /// installed here, the interpreter dispatches to `entry.func`
    /// instead of stepping through bytecode.
    ///
    /// `code_obj_ptr` is the heap address of the code object body
    /// (= `closure[0]` cast to `*const PolyWord`).
    pub fn install_jit(&mut self, code_obj_ptr: usize, entry: JitEntry) {
        self.jit_cache.insert(code_obj_ptr, entry);
    }

    /// Look up a cached JIT entry for the given code-object address.
    /// Used by `jit_bridge::jit_dispatch_closure_call` for the
    /// JIT-to-JIT fast path.
    #[must_use]
    pub fn jit_lookup(&self, code_obj_ptr: usize) -> Option<JitEntry> {
        self.jit_cache.get(&code_obj_ptr).copied()
    }

    /// Iterate all installed (code_obj_ptr, JitEntry) pairs. Used by
    /// the differential tester to enumerate testable functions.
    /// Order is HashMap-iteration order (not insertion order).
    pub fn jit_cache_entries(&self) -> Vec<(usize, JitEntry)> {
        self.jit_cache.iter().map(|(k, v)| (*k, *v)).collect()
    }

    /// Clear all installed JIT entries. Used by the differential
    /// tester to ensure interp runs don't dispatch back into JIT
    /// via the cache (which would defeat the comparison purpose
    /// and let JIT bugs hang the interp run).
    pub fn jit_cache_clear(&mut self) {
        self.jit_cache.clear();
    }

    /// JIT bridge: current value of the SML stack pointer (sp).
    /// Passed to JIT entries as `sp_in` per the new ABI. The JIT
    /// trampoline path also uses this to dispatch into already-
    /// installed JIT'd code (see `jit_bridge::jit_dispatch_closure_call`).
    #[doc(hidden)]
    #[must_use]
    pub fn jit_current_sp(&self) -> usize {
        self.sp
    }

    /// JIT bridge: base address of the SML stack as a mutable raw
    /// pointer. Combined with `jit_current_sp()` it lets JIT'd code
    /// read/write `interp.stack[sp..]` directly. Reserved for Phase-2
    /// of the stack-pointer refactor.
    #[doc(hidden)]
    pub fn jit_stack_base_mut(&mut self) -> *mut PolyWord {
        self.stack.as_mut_ptr()
    }

    /// Mutable accessor to this interpreter's `alloc_space` for the
    /// JIT-bridge trampolines. Returns `None` if no alloc space has
    /// been configured (the JIT-`TUPLE` etc. paths will then fail
    /// gracefully rather than UB).
    #[doc(hidden)]
    pub fn jit_alloc_space_mut(&mut self) -> Option<&mut MemorySpace> {
        self.alloc_space.as_mut()
    }

    /// Read-only accessor to this interpreter's RTS table. Used by the
    /// JIT `rts_trampoline` to look up entries by token.
    #[doc(hidden)]
    #[must_use]
    pub fn rts_table(&self) -> &RtsTable {
        &self.rts
    }

    /// Clone the `Arc<RtsTable>` (cheap) for code paths that need
    /// to hold a reference past a `&mut self` borrow of the
    /// interpreter — e.g. building an `RtsContext` whose `rts` field
    /// outlives the borrow used to grab `alloc_space`.
    #[doc(hidden)]
    #[must_use]
    pub fn rts_table_arc(&self) -> Arc<RtsTable> {
        self.rts.clone()
    }

    /// Enable per-step execution-profile collection. After this call,
    /// every `step()` records a visit to the current `(code_start,
    /// pc_offset)` and every `do_call()` records the target. Use
    /// [`take_diagnostics`](Self::take_diagnostics) to extract.
    ///
    /// Builder pattern; returns the interpreter for chaining.
    #[must_use]
    pub fn enable_diagnostics(mut self) -> Self {
        self.diag = Some(DiagState::default());
        self
    }

    /// Extract collected diagnostics, leaving the interpreter without
    /// a collector. Returns `None` if diagnostics were never enabled.
    pub fn take_diagnostics(&mut self) -> Option<DiagState> {
        self.diag.take()
    }

    /// Attach an RTS table. Builder pattern.
    #[must_use]
    pub fn with_rts(mut self, rts: Arc<RtsTable>) -> Self {
        self.rts = rts;
        self
    }

    /// Attach an allocation space. The interpreter will bump-allocate
    /// new objects (closures, tuples, refs) from this space. Sized
    /// once at attach time — runtime growth is a future concern.
    ///
    /// Builder pattern; returns the interpreter for chaining.
    #[must_use]
    pub fn with_alloc_space(mut self, space: MemorySpace) -> Self {
        let cap = space.capacity_words();
        self.alloc_space = Some(space);
        let thresh = usize::from(crate::rts::gc_threshold_percent().unwrap_or(80));
        // gc_trigger_words = cap * thresh / 100. Saturate at 0 if
        // cap is so large that the multiply would overflow.
        self.gc_trigger_words = cap.checked_mul(thresh).map_or(0, |x| x / 100);
        self
    }

    /// Convenience: attach a freshly-created mutable allocation space
    /// sized in WORDS. A `PolyWord` is 8 bytes, so e.g. 200 million
    /// words is 1.6 GB. Use this when sizing from a known word count;
    /// use [`Self::with_default_alloc_space_bytes`] when sizing from a
    /// memory budget.
    #[must_use]
    pub fn with_default_alloc_space_words(self, capacity_words: usize) -> Self {
        self.with_alloc_space(MemorySpace::new(capacity_words, SpaceKind::Mutable))
    }

    /// Convenience: attach a freshly-created mutable allocation space
    /// sized in BYTES. Rounded down to a whole number of `PolyWord`
    /// slots (8 bytes each). Use this when sizing from a memory
    /// budget; use [`Self::with_default_alloc_space_words`] when
    /// sizing from a known word count.
    #[must_use]
    pub fn with_default_alloc_space_bytes(self, capacity_bytes: usize) -> Self {
        let capacity_words = capacity_bytes / std::mem::size_of::<crate::PolyWord>();
        self.with_default_alloc_space_words(capacity_words)
    }

    /// **Deprecated:** the unit was implicit (words), which has
    /// caused misreads — `with_default_alloc_space(3 * 1024 * 1024 * 1024)`
    /// looks like 3 GB but is actually 3 billion words = 24 GB.
    /// Use [`Self::with_default_alloc_space_words`] or
    /// [`Self::with_default_alloc_space_bytes`] instead.
    #[must_use]
    #[deprecated(
        since = "0.0.1",
        note = "ambiguous unit; use `with_default_alloc_space_words` or `with_default_alloc_space_bytes`"
    )]
    pub fn with_default_alloc_space(self, capacity_words: usize) -> Self {
        self.with_default_alloc_space_words(capacity_words)
    }

    /// Add a mutable image space to scan as a GC root. Pointers from
    /// the image's globals into alloc-space objects (e.g. the SML
    /// global namespace hashtable) must be visited so we don't
    /// collect things that are still referenced from there.
    ///
    /// Multiple calls accumulate.
    #[must_use]
    pub fn with_image_mutable_root(mut self, ptr: *const PolyWord, len_words: usize) -> Self {
        self.image_mutable_roots.push((ptr, len_words));
        self
    }

    /// Run a copying GC over the alloc space, forwarding all roots
    /// (interpreter stack, exception packet, code segment, frames,
    /// recent-call ring buffer, BOOTSTRAP_TAIL_CALL, and any
    /// configured image-mutable-root regions). Returns the new
    /// `used_words` count of the alloc space.
    pub fn gc(&mut self) -> Option<usize> {
        let alloc = self.alloc_space.as_mut()?;
        // Capture from-space range so we can audit for residual
        // pointers after the swap. Anything in interpreter state
        // (or the new to-space) that still points into this range
        // post-GC is a missed root.
        let from_range = alloc.as_ptr_range();
        let from_lo = from_range.start as usize;
        let from_hi = from_range.end as usize;
        // Capture byte offsets we need to translate post-GC.
        let pc_off = unsafe { self.pc.offset_from(self.code_start) };
        let code_end_off = unsafe { self.code_end.offset_from(self.code_start) };
        let frame_offsets: Vec<isize> = self
            .frames
            .iter()
            .map(|(s, e)| unsafe { e.offset_from(*s) })
            .collect();
        // Stash code_start as a PolyWord pointer slot.
        let mut code_start_slot = PolyWord::from_ptr(self.code_start.cast::<PolyWord>());
        let mut frame_starts: Vec<PolyWord> = self
            .frames
            .iter()
            .map(|(s, _)| PolyWord::from_ptr(s.cast::<PolyWord>()))
            .collect();
        // Handler frames depth also saves code bounds that need
        // forwarding so the handler can restore them on RAISE_EX.
        let handler_offsets: Vec<isize> = self
            .handler_frames_depth
            .iter()
            .map(|(_, s, e)| unsafe { e.offset_from(*s) })
            .collect();
        let mut handler_starts: Vec<PolyWord> = self
            .handler_frames_depth
            .iter()
            .map(|(_, s, _)| PolyWord::from_ptr(s.cast::<PolyWord>()))
            .collect();
        let mut exn_slot = self.exception_packet.unwrap_or(PolyWord::ZERO);
        let mut bootstrap_tail = crate::rts::peek_bootstrap_tail_call();
        // Cached Thread.self() object (if allocated) — a GC root: its body holds
        // thread-local data (incl. the Isabelle generic context), and its
        // identity must survive collection.
        let mut thread_obj_slot = self.thread_object.unwrap_or(PolyWord::ZERO);

        // Take ownership of the stack-slice we want the GC to forward
        // by indexing into self.stack directly via raw pointer.
        let stack_ptr = self.stack.as_mut_ptr();
        let sp = self.sp;
        let stack_len = self.stack.len();
        let handler_sp = self.handler_sp;

        let image_roots = self.image_mutable_roots.clone();

        let new_used = crate::gc::collect(alloc, |c| {
            // 1. Stack slots from sp..end. (Below sp is "free".)
            // Some of these are the handler save area which contains
            // raw PC addresses — those are NOT PolyWords pointing to
            // alloc objects, but the GC's is-in-from-space check
            // filters non-pointers, so it's safe to visit them all.
            for i in sp..stack_len {
                let slot = unsafe { stack_ptr.add(i) };
                // Stack slots may carry raw PC byte pointers whose
                // LSB happens to be 1; we can't filter by tagged-bit
                // alone, so use the byte-address variant.
                unsafe { c.forward_stack_slot(slot) };
            }
            // 2. Exception packet (might be None / TAGGED(0)).
            unsafe { c.forward(&mut exn_slot as *mut _) };
            // 3. code_start (as a PolyWord pointer to the code object).
            unsafe { c.forward(&mut code_start_slot as *mut _) };
            for fs in frame_starts.iter_mut() {
                unsafe { c.forward(fs as *mut _) };
            }
            for hs in handler_starts.iter_mut() {
                unsafe { c.forward(hs as *mut _) };
            }
            // 4. Bootstrap tail-call slot (PolyEndBootstrapMode arg).
            unsafe { c.forward(&mut bootstrap_tail as *mut _) };
            // 4b. Cached Thread.self() object.
            unsafe { c.forward(&mut thread_obj_slot as *mut _) };
            // 5. Image mutable spaces: walk object-by-object so we
            //    only forward body words (skipping length words),
            //    and dispatch by type (byte objects have no internal
            //    pointers, closures' word[0] is a raw code ptr).
            let mut img_objects_scanned = 0usize;
            for (ptr, len) in &image_roots {
                let base = *ptr as *mut PolyWord;
                let mut i = 0usize;
                while i < *len {
                    // SAFETY: i < len bounds the slice access.
                    let lw = unsafe { *base.add(i) };
                    let n = crate::length_word::length_of(lw);
                    if i + 1 + n > *len {
                        // Object body would overrun the region: genuinely
                        // malformed. Stop scanning this region.
                        break;
                    }
                    if n == 0 {
                        // Zero-length object (empty tuple/vector) is LEGAL.
                        // It occupies just its length-word slot and has no
                        // body pointers. Skip it and KEEP scanning — using
                        // `break` here truncates the whole region and leaves
                        // every later object's children un-forwarded.
                        i += 1;
                        continue;
                    }
                    let body = unsafe { base.add(i + 1) };
                    let ty = crate::length_word::type_of(lw);
                    match ty {
                        crate::length_word::F_BYTE_OBJ => {
                            // No pointers.
                        }
                        crate::length_word::F_CODE_OBJ => {
                            let (cp, count) =
                                unsafe { crate::length_word::const_segment_for_code(body) };
                            let cp_mut = cp.cast_mut();
                            for k in 0..count {
                                unsafe { c.forward(cp_mut.add(k)) };
                            }
                        }
                        crate::length_word::F_CLOSURE_OBJ => {
                            // Word 0 is a raw code-byte pointer; the
                            // collector's `forward` handles mid-body
                            // pointers via its find_object lookup
                            // (in from-space only; image code ptrs
                            // are outside from-space so left alone).
                            for k in 0..n {
                                unsafe { c.forward(body.add(k)) };
                            }
                        }
                        _ => {
                            // Ordinary word object.
                            for k in 0..n {
                                unsafe { c.forward(body.add(k)) };
                            }
                        }
                    }
                    i += 1 + n;
                    img_objects_scanned += 1;
                }
            }
            eprintln!(
                "  GC roots: image-mut objects scanned = {img_objects_scanned}, total image-mut words = {}",
                image_roots.iter().map(|(_, l)| l).sum::<usize>()
            );
            // Suppress unused
            let _ = handler_sp;
        });

        // Apply updates.
        self.exception_packet = if exn_slot.0 == 0 || exn_slot.is_tagged() {
            None
        } else {
            Some(exn_slot)
        };
        if self.thread_object.is_some() {
            self.thread_object = Some(thread_obj_slot);
        }
        let new_code_start = code_start_slot.as_ptr::<PolyWord>().cast::<u8>();
        self.code_start = new_code_start;
        // SAFETY: offsets remain valid; new code object has the same length.
        self.pc = unsafe { new_code_start.offset(pc_off) };
        self.code_end = unsafe { new_code_start.offset(code_end_off) };
        for (i, fs) in frame_starts.into_iter().enumerate() {
            let new_start = fs.as_ptr::<PolyWord>().cast::<u8>();
            self.frames[i].0 = new_start;
            self.frames[i].1 = unsafe { new_start.offset(frame_offsets[i]) };
        }
        for (i, hs) in handler_starts.into_iter().enumerate() {
            let new_start = hs.as_ptr::<PolyWord>().cast::<u8>();
            self.handler_frames_depth[i].1 = new_start;
            self.handler_frames_depth[i].2 = unsafe { new_start.offset(handler_offsets[i]) };
        }
        crate::rts::set_bootstrap_tail_call(bootstrap_tail);

        // Recent-call ring buffer: clear; not worth forwarding.
        self.recent_call_targets.fill(0);

        // ---- Audit: any pointer still in old from-space is a missed root.
        // Opt-in via POLYML_GC_AUDIT=1 — full audit is O(used+stack)
        // and meaningful overhead on the hot loop.
        if std::env::var("POLYML_GC_AUDIT").is_ok() {
            self.audit_no_residual_from_space_ptrs(from_lo, from_hi);
        }
        let _ = from_lo;
        let _ = from_hi;
        Some(new_used)
    }

    fn audit_no_residual_from_space_ptrs(&self, from_lo: usize, from_hi: usize) {
        let in_old = |addr: usize| addr >= from_lo && addr < from_hi;
        let mut residual = 0usize;
        let mut samples: Vec<(&'static str, usize, usize)> = Vec::new();
        // 1. Interpreter stack
        for i in self.sp..self.stack.len() {
            let v = self.stack[i].0;
            if in_old(v) {
                residual += 1;
                if samples.len() < 5 {
                    samples.push(("stack", i, v));
                }
            }
        }
        // 2. code_start, pc, code_end (byte ptrs)
        for (name, p) in [
            ("code_start", self.code_start as usize),
            ("pc", self.pc as usize),
            ("code_end", self.code_end as usize),
        ] {
            if in_old(p) {
                residual += 1;
                if samples.len() < 5 {
                    samples.push((name, 0, p));
                }
            }
        }
        // 3. frames
        for (idx, (s, e)) in self.frames.iter().enumerate() {
            for (name, p) in [("frame_s", *s as usize), ("frame_e", *e as usize)] {
                if in_old(p) {
                    residual += 1;
                    if samples.len() < 5 {
                        samples.push((name, idx, p));
                    }
                }
            }
        }
        // 4. handler_frames_depth
        for (idx, (_, s, e)) in self.handler_frames_depth.iter().enumerate() {
            for (name, p) in [("hf_s", *s as usize), ("hf_e", *e as usize)] {
                if in_old(p) {
                    residual += 1;
                    if samples.len() < 5 {
                        samples.push((name, idx, p));
                    }
                }
            }
        }
        // 5. exception_packet
        if let Some(w) = self.exception_packet {
            if in_old(w.0) {
                residual += 1;
                samples.push(("exn_pkt", 0, w.0));
            }
        }
        // 6. Walk the NEW alloc-space body words and look for stale
        //    inbound pointers. This is the big one — missed children
        //    of forwarded objects.
        if let Some(space) = self.alloc_space.as_ref() {
            let start = space.as_ptr_range().start;
            let used = space.used_words();
            // SAFETY: 0..used in-bounds.
            let mut i = 0usize;
            while i < used {
                let lw = unsafe { *start.add(i) };
                let n = crate::length_word::length_of(lw);
                if i + 1 + n > used {
                    break;
                }
                if n == 0 {
                    // Zero-length object is legal; skip it (do NOT break, or
                    // the walk truncates and misses every later object).
                    i += 1;
                    continue;
                }
                // Inspect body words (offset i+1 .. i+1+n).
                for k in 0..n {
                    let v = unsafe { (*start.add(i + 1 + k)).0 };
                    if in_old(v) {
                        residual += 1;
                        if samples.len() < 5 {
                            samples.push(("to_space_body", i + 1 + k, v));
                        }
                    }
                }
                i += 1 + n;
            }
        }
        // 7. Walk the registered image mutable-root regions. These hold
        //    pointers into alloc-space (the top-level namespace + runtime
        //    `ref`s allocated into image-mutable). A break-on-zero-length
        //    bug here was the source of the dangling-pointer SEGV, so the
        //    audit must scan them to catch the same class of regression.
        for (ptr, len) in &self.image_mutable_roots {
            let base = *ptr;
            let mut i = 0usize;
            while i < *len {
                let lw = unsafe { *base.add(i) };
                let n = crate::length_word::length_of(lw);
                if i + 1 + n > *len {
                    break;
                }
                if n == 0 {
                    i += 1;
                    continue;
                }
                let ty = crate::length_word::type_of(lw);
                if ty != crate::length_word::F_BYTE_OBJ {
                    for k in 0..n {
                        let v = unsafe { (*base.add(i + 1 + k)).0 };
                        if in_old(v) {
                            residual += 1;
                            if samples.len() < 5 {
                                samples.push(("image_mut_body", i + 1 + k, v));
                            }
                        }
                    }
                }
                i += 1 + n;
            }
        }
        if residual > 0 {
            eprintln!("  GC AUDIT: {residual} residual from-space pointers remain after collect:");
            for (where_, idx, addr) in samples {
                eprintln!("    {where_}[{idx}] = 0x{addr:016x}");
            }
        }
    }

    // ---- Inspection -----------------------------------------------------

    #[must_use]
    pub fn stack_height(&self) -> usize {
        self.stack.len() - self.sp
    }

    /// Snapshot the top `n` stack words (or fewer if the stack is
    /// shallower). Index 0 = current top. For debugging only.
    #[must_use]
    pub fn dump_stack_top(&self, n: usize) -> Vec<PolyWord> {
        let take = n.min(self.stack.len() - self.sp);
        (0..take).map(|i| self.stack[self.sp + i]).collect()
    }

    /// Current code-object base address (as `usize`). Useful in
    /// combination with [`pc_offset`](Self::pc_offset) for matching
    /// diagnostic hot-PC entries.
    #[must_use]
    pub fn code_start_addr(&self) -> usize {
        self.code_start as usize
    }

    /// Number of saved frames on the call side-stack. Useful for
    /// detecting CALL / RETURN events during external tracing.
    #[must_use]
    pub fn frames_depth(&self) -> usize {
        self.frames.len()
    }

    /// Byte offset of the PC from the start of the current code
    /// segment.
    #[must_use]
    pub fn pc_offset(&self) -> usize {
        // SAFETY: pc and code_start are both within (or one past) the
        // same allocation by construction.
        unsafe { self.pc.offset_from(self.code_start) as usize }
    }

    /// Snapshot of the recent-CALL-targets ring buffer, most-recent
    /// first. Stale entries are zero.
    #[must_use]
    pub fn recent_call_targets_snapshot(&self) -> Vec<usize> {
        let n = self.recent_call_targets.len();
        (0..n)
            .map(|off| {
                let idx = (self.recent_call_idx + n - 1 - off) % n;
                self.recent_call_targets[idx]
            })
            .filter(|t| *t != 0)
            .collect()
    }

    /// Return `(lo, hi, hex_dump)` of the bytecode around the current
    /// PC for diagnostic display. Reads ±`window` bytes, clamped to
    /// the code segment.
    #[must_use]
    pub fn pc_context_bytes(&self, window: usize) -> (usize, usize, String) {
        let cur = self.pc_offset();
        let segment_size = unsafe { self.code_end.offset_from(self.code_start) as usize };
        let lo = cur.saturating_sub(window);
        let hi = std::cmp::min(cur + window, segment_size);
        let bytes: Vec<u8> = (lo..hi)
            .map(|i| unsafe { *self.code_start.add(i) })
            .collect();
        let hex = bytes
            .iter()
            .enumerate()
            .map(|(i, b)| {
                let here = lo + i == cur;
                if here {
                    format!("[{b:02x}]")
                } else {
                    format!("{b:02x}")
                }
            })
            .collect::<Vec<_>>()
            .join(" ");
        (lo, hi, hex)
    }

    /// Test/debug API: push a value onto the stack.
    #[doc(hidden)]
    pub fn test_seed_top(&mut self, w: PolyWord) {
        let _ = self.push(w);
    }

    /// Reset the stack to empty (sp = stack.len()). Used by the
    /// differential tester to run multiple distinct calls on the
    /// same interpreter without re-loading the image.
    pub fn reset_stack(&mut self) {
        self.sp = self.stack.len();
        self.frames.clear();
        self.handler_sp = 0;
    }

    /// Test/debug API: push a synthetic return-to-top sentinel onto
    /// the stack so the interpreter can be used inside a hand-built
    /// call frame.
    ///
    /// Use this after `test_seed_top`s for args + closure to simulate
    /// being called: the stack layout becomes `[closure, retPC=null,
    /// args...]`. When the callee's RETURN fires, it'll find
    /// retPC=null and yield `Returned`.
    #[doc(hidden)]
    pub fn test_seed_return_sentinel(&mut self) {
        // retPC = null pointer encoded as a PolyWord bit pattern.
        let _ = self.push(PolyWord::from_bits(0));
    }

    /// Test/debug API: invoke `do_call` from outside the crate. Used
    /// to validate the JIT-dispatch fast path without needing a full
    /// bytecode-emitting caller.
    #[doc(hidden)]
    pub fn test_invoke_do_call(&mut self, closure: PolyWord) -> Result<(), InterpError> {
        self.do_call(closure)
    }

    #[doc(hidden)]
    #[must_use]
    pub fn test_sp(&self) -> usize {
        self.sp
    }

    #[doc(hidden)]
    #[must_use]
    pub fn test_peek_top(&self) -> PolyWord {
        self.stack[self.sp]
    }

    /// JIT bridge: snapshot PC + code segment so a nested
    /// `jit_dispatch_closure_call` can restore them after returning.
    #[must_use]
    #[doc(hidden)]
    pub fn jit_state_save(&self) -> (*const u8, *const u8, *const u8) {
        (self.pc, self.code_start, self.code_end)
    }

    #[doc(hidden)]
    pub fn peek_pc_for_debug(&self) -> *const u8 {
        self.pc
    }

    #[doc(hidden)]
    pub fn peek_sp_for_debug(&self) -> usize {
        self.sp
    }

    #[doc(hidden)]
    pub fn peek_stack_for_debug(&self, idx: usize) -> usize {
        if idx < self.stack.len() {
            self.stack[idx].0
        } else {
            0
        }
    }

    #[doc(hidden)]
    pub fn peek_code_seg_for_debug(&self) -> (*const u8, *const u8) {
        (self.code_start, self.code_end)
    }

    /// JIT bridge: restore PC + code segment from a snapshot.
    #[doc(hidden)]
    pub fn jit_state_restore(&mut self, snapshot: (*const u8, *const u8, *const u8)) {
        let (pc, code_start, code_end) = snapshot;
        self.pc = pc;
        self.code_start = code_start;
        self.code_end = code_end;
    }

    /// Set PC + code segment bounds directly from a code-object
    /// pointer (= the heap address of the bytecode body). Like
    /// `jit_set_code_segment_to_closure` but skips the closure
    /// indirection. Used by the differential tester to enter a
    /// function chosen from `jit_cache_entries`.
    ///
    /// # Safety
    /// `code_obj_ptr` must point at a valid PolyML code object.
    pub unsafe fn set_code_segment_to_code_obj(&mut self, code_obj_ptr: usize) {
        let code_obj = code_obj_ptr as *const PolyWord;
        let (consts_start, _) = unsafe { crate::length_word::const_segment_for_code(code_obj) };
        self.code_start = code_obj.cast::<u8>();
        self.code_end = consts_start.cast::<u8>();
        self.pc = self.code_start;
    }

    /// JIT bridge: switch the interpreter's PC + code segment bounds
    /// to point at the start of `closure`'s code object. Reads
    /// `closure[0]` (the code address) and derives the bytecode
    /// boundary from the code object's length-word + trailing-
    /// offset, the same way `from_code_object` does.
    ///
    /// # Errors
    /// Returns `NotAClosure` if `closure` isn't a data pointer.
    #[doc(hidden)]
    pub fn jit_set_code_segment_to_closure(
        &mut self,
        closure: PolyWord,
    ) -> Result<(), InterpError> {
        if !closure.is_data_ptr() {
            return Err(InterpError::NotAClosure(closure));
        }
        let closure_ptr = closure.as_ptr::<PolyWord>();
        // SAFETY: caller-trusted closure.
        let code_word = unsafe { *closure_ptr };
        if !code_word.is_data_ptr() {
            return Err(InterpError::NotAClosure(closure));
        }
        let code_obj = code_word.as_ptr::<PolyWord>();
        // SAFETY: closure points at a valid code object.
        let (consts_start, _) = unsafe { crate::length_word::const_segment_for_code(code_obj) };
        self.code_start = code_obj.cast::<u8>();
        self.code_end = consts_start.cast::<u8>();
        self.pc = self.code_start;
        Ok(())
    }

    // ---- Stack primitives ----------------------------------------------

    #[inline(always)]
    fn push(&mut self, w: PolyWord) -> Result<(), InterpError> {
        if self.sp == 0 {
            return Err(InterpError::StackOverflow);
        }
        self.sp -= 1;
        // SAFETY: sp is now in [0, len()) since we checked sp != 0 above
        // and decremented; stack is a fixed-size Box<[PolyWord]>.
        unsafe {
            *self.stack.get_unchecked_mut(self.sp) = w;
        }
        Ok(())
    }

    #[inline(always)]
    fn pop(&mut self) -> Result<PolyWord, InterpError> {
        if self.sp >= self.stack.len() {
            return Err(InterpError::StackUnderflow);
        }
        // SAFETY: sp < len(); stack is a fixed Box<[PolyWord]>.
        let w = unsafe { *self.stack.get_unchecked(self.sp) };
        self.sp += 1;
        Ok(w)
    }

    #[inline(always)]
    fn peek(&self, depth: usize) -> Result<PolyWord, InterpError> {
        // Hot path. `checked_add + filter + ok_or + bounds check on
        // indexing` was three branches; collapse to one.
        let Some(idx) = self.sp.checked_add(depth) else {
            return Err(InterpError::StackUnderflow);
        };
        if idx >= self.stack.len() {
            return Err(InterpError::StackUnderflow);
        }
        // SAFETY: idx < len() checked just above.
        Ok(unsafe { *self.stack.get_unchecked(idx) })
    }

    // ---- PC primitives -------------------------------------------------

    fn pc_in_bounds(&self) -> bool {
        // null code_start = bounds disabled (e.g. post-exception
        // unwind, where the new PC may be in any code object we
        // don't track from here).
        if self.code_start.is_null() {
            return true;
        }
        // We allow pc == code_end (about to step past the end is
        // benign until we try to fetch).
        self.pc >= self.code_start && self.pc <= self.code_end
    }

    fn pc_offset_for_err(&self) -> InterpError {
        // SAFETY: code_end - code_start is the segment size; ptr math
        // is within one allocation by construction.
        let size = unsafe { self.code_end.offset_from(self.code_start) as usize };
        let offset = unsafe { self.pc.offset_from(self.code_start) as usize };
        InterpError::PcOutOfBounds { offset, size }
    }

    #[inline(always)]
    fn fetch_u8(&mut self) -> Result<u8, InterpError> {
        if self.pc >= self.code_end {
            return Err(self.pc_offset_for_err());
        }
        // SAFETY: bounds-checked above.
        let b = unsafe { *self.pc };
        // SAFETY: bumping a pointer to within or one past the
        // allocation is well-defined.
        self.pc = unsafe { self.pc.add(1) };
        Ok(b)
    }

    fn fetch_u16_le(&mut self) -> Result<u16, InterpError> {
        let lo = self.fetch_u8()?;
        let hi = self.fetch_u8()?;
        Ok(u16::from_le_bytes([lo, hi]))
    }

    fn fetch_u32_le(&mut self) -> Result<u32, InterpError> {
        let lo = u32::from(self.fetch_u16_le()?);
        let hi = u32::from(self.fetch_u16_le()?);
        Ok(lo | (hi << 16))
    }

    /// Add a signed offset to PC. Used by jumps and PC-relative
    /// constant addressing.
    fn pc_offset_signed(&mut self, delta: isize) -> Result<(), InterpError> {
        // SAFETY: bounds checked after the offset; we deliberately do
        // not check before so backward arithmetic out of range surfaces
        // as PcOutOfBounds.
        self.pc = unsafe { self.pc.offset(delta) };
        if !self.pc_in_bounds() {
            // Roll back so the error message has a sensible offset.
            // Actually, leave PC where it is and let bounds reporting
            // reflect the failure.
            return Err(self.pc_offset_for_err());
        }
        Ok(())
    }

    // ---- Run / step ----------------------------------------------------

    /// Run until something interesting happens: a top-level return, an
    /// unimplemented opcode, or an error.
    pub fn run(&mut self) -> Result<StepResult, InterpError> {
        loop {
            match self.step()? {
                StepResult::Continue => {}
                r => return Ok(r),
            }
        }
    }

    /// Execute a single instruction.
    #[allow(clippy::too_many_lines)]
    #[allow(clippy::wildcard_imports)]
    pub fn step(&mut self) -> Result<StepResult, InterpError> {
        use opcodes::*;

        // If PolyFinish was just called, halt cleanly with the
        // requested exit code rather than executing junk bytecode
        // past the "exit" point. (Upstream's PolyFinish calls
        // `exit()` and never returns; we don't have that luxury.)
        if let Some(code) = crate::rts::finish_requested() {
            crate::rts::clear_finish_requested();
            return Ok(StepResult::Returned(PolyWord::tagged(code)));
        }

        // Auto-GC: trigger when alloc_space.used reaches the
        // pre-computed threshold. Trigger is 0 when no alloc_space or
        // when POLYML_GC_THRESHOLD selects "disable GC" — either way
        // `used >= 0` would always be true if used == 0, so we also
        // guard on `gc_trigger_words > 0`.
        if self.gc_trigger_words > 0
            && let Some(used) = self.alloc_space.as_ref().map(MemorySpace::used_words)
            && used >= self.gc_trigger_words
        {
            let before = used;
            let stack_depth = self.stack_height();
            let new_used = self.gc().unwrap_or(before);
            if std::env::var("POLYML_GC_QUIET").is_err() {
                eprintln!(
                    "  GC: {before} -> {new_used} words ({}% retained), stack={stack_depth}",
                    if before > 0 {
                        (new_used * 100) / before
                    } else {
                        0
                    }
                );
            }
        }

        let opcode_pc = self.pc;
        let op = self.fetch_u8()?;
        if arbint_trace_on() {
            #[allow(clippy::cast_possible_truncation)]
            let off = unsafe { opcode_pc.offset_from(self.code_start) as u32 };
            let code = self.code_start as usize;
            let sp_depth = self.stack_height();
            OP_RING.with(|r| {
                let mut r = r.borrow_mut();
                if r.len() >= 192 {
                    r.pop_front();
                }
                r.push_back((code, off, op, sp_depth));
            });
        }
        if let Some(d) = self.diag.as_mut() {
            #[allow(clippy::cast_possible_truncation)]
            let off = unsafe { opcode_pc.offset_from(self.code_start) as u32 };
            let code = self.code_start as usize;
            d.total_steps += 1;
            *d.pc_visits.entry((code, off)).or_insert(0) += 1;
            d.opcode_counts[op as usize] += 1;
        }
        if crate::rts::is_traced() {
            eprintln!(
                "  [{:5}] op=0x{op:02x} sp_depth={} top={:?}",
                self.pc_offset() - 1,
                self.stack_height(),
                if self.sp < self.stack.len() {
                    Some(self.stack[self.sp])
                } else {
                    None
                }
            );
        }
        match op {
            // ----- No-op
            INSTR_NO_OP => Ok(StepResult::Continue),

            // ----- Stack-size check (function prologue)
            //
            // bytecode.cpp:472-484. The compiler emits this at function
            // entry with a 16-bit immediate = stack words needed.
            // Real PolyML would grow the stack or trap; we have a
            // fixed-size stack and trust it's big enough. For now,
            // just check and surface a clean error if not.
            INSTR_STACK_SIZE16 => {
                let needed = self.fetch_u16_le()? as usize;
                if self.sp < needed {
                    return Err(InterpError::StackOverflow);
                }
                Ok(StepResult::Continue)
            }

            // ----- Constants
            INSTR_CONST_0 => self.push_continue(PolyWord::tagged(0)),
            INSTR_CONST_1 => self.push_continue(PolyWord::tagged(1)),
            INSTR_CONST_2 => self.push_continue(PolyWord::tagged(2)),
            INSTR_CONST_3 => self.push_continue(PolyWord::tagged(3)),
            INSTR_CONST_4 => self.push_continue(PolyWord::tagged(4)),
            INSTR_CONST_10 => self.push_continue(PolyWord::tagged(10)),
            INSTR_CONST_INT_B => {
                let n = isize::from(self.fetch_u8()?);
                self.push_continue(PolyWord::tagged(n))
            }
            INSTR_CONST_INT_W => {
                let raw = self.fetch_u16_le()?;
                self.push_continue(PolyWord::tagged(
                    isize::try_from(raw).expect("u16 fits in isize"),
                ))
            }

            // ----- Local access (push sp[N])
            INSTR_LOCAL_0 => self.dup_local(0),
            INSTR_LOCAL_1 => self.dup_local(1),
            INSTR_LOCAL_2 => self.dup_local(2),
            INSTR_LOCAL_3 => self.dup_local(3),
            INSTR_LOCAL_4 => self.dup_local(4),
            INSTR_LOCAL_5 => self.dup_local(5),
            INSTR_LOCAL_6 => self.dup_local(6),
            INSTR_LOCAL_7 => self.dup_local(7),
            INSTR_LOCAL_8 => self.dup_local(8),
            INSTR_LOCAL_9 => self.dup_local(9),
            INSTR_LOCAL_10 => self.dup_local(10),
            INSTR_LOCAL_11 => self.dup_local(11),
            INSTR_LOCAL_12 => self.dup_local(12),
            INSTR_LOCAL_13 => self.dup_local(13),
            INSTR_LOCAL_14 => self.dup_local(14),
            INSTR_LOCAL_15 => self.dup_local(15),
            INSTR_LOCAL_B => {
                let n = self.fetch_u8()? as usize;
                self.dup_local(n)
            }
            INSTR_LOCAL_W => {
                let n = self.fetch_u16_le()? as usize;
                self.dup_local(n)
            }

            // ----- Allocation
            INSTR_ALLOC_REF => self.do_alloc_ref(),
            INSTR_TUPLE_2 => self.do_tuple(2),
            INSTR_TUPLE_3 => self.do_tuple(3),
            INSTR_TUPLE_4 => self.do_tuple(4),
            INSTR_TUPLE_B => {
                let n = self.fetch_u8()? as usize;
                self.do_tuple(n)
            }
            INSTR_CLOSURE_B => {
                let n = self.fetch_u8()? as usize;
                self.do_create_closure(n)
            }
            INSTR_ALLOC_MUT_CLOSURE_B => {
                let n = self.fetch_u8()? as usize;
                self.do_alloc_mut_closure(n)
            }
            INSTR_MOVE_TO_MUT_CLOSURE_B => {
                let slot = self.fetch_u8()? as usize;
                self.do_move_to_mut_closure(slot)
            }
            INSTR_LOCK => self.clear_mutable_bit(false),
            INSTR_CLEAR_MUTABLE => self.clear_mutable_bit(true),

            // ----- Generic allocation (with caller-supplied length+flags)
            //
            // allocByteMem: bytecode.cpp:1155-1164. Stack: [length, flags]
            // top down (i.e., flags is top). Pops flags, peeks length,
            // allocates `length` words with `flags`, replaces top with
            // pointer.
            INSTR_ALLOC_BYTE_MEM => {
                let flags = self.pop()?.untag() as u8;
                let length = self.peek(0)?.untag() as usize;
                let p = self.allocate(length, flags)?;
                // Bytes are uninitialized — caller fills.
                self.pop()?;
                self.push_continue(PolyWord::from_ptr(p.cast_const()))
            }
            // allocWordMemory: bytecode.cpp:1171-1183. Stack:
            // [length, flags, initialiser] top down. Allocates with
            // `length` and `flags`, initialises all slots to
            // `initialiser`, replaces deepest (length) slot with pointer.
            INSTR_ALLOC_WORD_MEMORY => {
                let length = self.peek(2)?.untag() as usize;
                let init = self.pop()?;
                let flags = self.pop()?.untag() as u8;
                let p = self.allocate(length, flags)?;
                // SAFETY: just allocated `length` words
                unsafe {
                    for i in 0..length {
                        p.add(i).write(init);
                    }
                }
                self.pop()?; // pop length
                self.push_continue(PolyWord::from_ptr(p.cast_const()))
            }

            // ----- Stack-allocated containers
            //
            // PolyML compiles small non-escaping tuples directly onto
            // the stack rather than heap-allocating. STACK_CONTAINER_B N
            // pushes N zero slots + one extra "container reference"
            // word on top that points back into the stack at slot 0.
            // (bytecode.cpp:672-679)
            //
            // The reference is a REAL POINTER (stackAddr union variant
            // in upstream). The bootstrap then does pointer arithmetic
            // on it — e.g. computing `ref + offset` via WORD_ADD and
            // using that as the base for LOAD_ML_BYTE. Storing it as
            // an index would silently break those downstream uses.
            INSTR_STACK_CONTAINER_B => {
                let n = self.fetch_u8()? as usize;
                for _ in 0..n {
                    self.push(PolyWord::tagged(0))?;
                }
                // Address of slot 0 (= the most recently pushed zero).
                // SAFETY: self.stack is a Box<[PolyWord]> with stable
                // backing storage; self.sp is a valid index.
                let ref_ptr = unsafe { self.stack.as_ptr().add(self.sp) };
                self.push(PolyWord::from_bits(ref_ptr as usize))?;
                Ok(StepResult::Continue)
            }
            // moveToContainerB N: pop value u, peek container ref on
            // top, write u to container[N]. (bytecode.cpp:588-589)
            INSTR_MOVE_TO_CONTAINER_B => {
                let n = self.fetch_u8()? as usize;
                let u = self.pop()?;
                let container_ref = self.peek(0)?;
                let ref_ptr = container_ref.0 as *mut PolyWord;
                // SAFETY: ref_ptr is a real stack-slot pointer we
                // emitted in STACK_CONTAINER_B; the compiler is
                // trusted to emit valid slot offsets.
                unsafe { ref_ptr.add(n).write(u) };
                Ok(StepResult::Continue)
            }
            // indirectContainerB N: replace top (container ref) with
            // container[N]. (bytecode.cpp:598-599)
            INSTR_INDIRECT_CONTAINER_B => {
                let n = self.fetch_u8()? as usize;
                let container_ref = self.peek(0)?;
                let ref_ptr = container_ref.0 as *const PolyWord;
                // SAFETY: same as MOVE_TO_CONTAINER_B
                let val = unsafe { *ref_ptr.add(n) };
                self.pop()?;
                self.push_continue(val)
            }

            // ----- Cell introspection (length / flag-byte of a heap obj)
            INSTR_CELL_LENGTH => {
                let v = self.peek(0)?;
                let p = v.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid object reference
                let lw = unsafe { MemorySpace::length_word_of(p) };
                let len = crate::length_word::length_of(lw);
                self.pop()?;
                self.push_continue(PolyWord::tagged(len as isize))
            }
            INSTR_CELL_FLAGS => {
                let v = self.peek(0)?;
                let p = v.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid object reference
                let lw = unsafe { MemorySpace::length_word_of(p) };
                let f = crate::length_word::flags_of(lw);
                self.pop()?;
                self.push_continue(PolyWord::tagged(isize::from(f)))
            }

            // ----- Thread identity (stubbed for single-threaded interpreter)
            //
            // bytecode.cpp:1167-1168: returns `taskData->threadObject`
            // — a heap-allocated record with thread state fields. The
            // bootstrap dispatcher reads various INDIRECT offsets from
            // it; without a real one we allocate an 8-word zeroed
            // placeholder so those reads don't trap.
            //
            // TODO: real thread state once we have a scheduler.
            INSTR_GET_THREAD_ID => {
                let tid = self.alloc_stub_thread_object()?;
                self.push_continue(tid)
            }

            // ----- RTS calls (stubbed — drops args, returns tagged 0)
            //
            // The compiler emits these as fast paths for builtin C
            // functions (file I/O, arbitrary precision, etc.). The
            // stub on top of the stack is an object whose first word
            // is a raw C function pointer. We don't have an RTS yet,
            // so just consume the args and return zero.
            //
            // This WILL produce incorrect results when actually used.
            // It exists so we can see what opcodes come up further
            // down the bootstrap path.
            INSTR_CALL_FAST_RTS0 => self.rts_call(0),
            INSTR_CALL_FAST_RTS1 => self.rts_call(1),
            INSTR_CALL_FAST_RTS2 => self.rts_call(2),
            INSTR_CALL_FAST_RTS3 => self.rts_call(3),
            INSTR_CALL_FAST_RTS4 => self.rts_call(4),
            INSTR_CALL_FAST_RTS5 => self.rts_call(5),

            // ----- Tail call
            //
            // bytecode.cpp:387-395 + the TAIL_CALL label. The compiler
            // emits `tail_b_b T, L` where:
            //   T = tail-count = number of items at top that constitute
            //       the new frame (= 1 placeholder + 1 closure + N args)
            //   L = skip-count = number of stack slots to "drop" between
            //       the new frame items and the position where they get
            //       moved to (= current function's locals + 1 for its
            //       own closure slot)
            //
            // The copy moves [sp, sp+T) into [sp+L, sp+L+T), overwriting
            // any locals + the current function's closure slot. The
            // current function's retPC (which sits just below the
            // closure slot) is preserved unchanged — the tail-callee
            // inherits it as its own retPC.
            INSTR_TAIL_B_B => {
                let tail_count = self.fetch_u8()? as usize;
                let skip = self.fetch_u8()? as usize;
                self.do_tail_call(tail_count, skip)?;
                Ok(StepResult::Continue)
            }

            // ----- Heap load/store
            //
            // Load: pop index, peek base, replace top with base[index].
            // Store: pop value, pop index, peek base, base[index]=val,
            //        replace base on top with TAGGED(0).
            INSTR_LOAD_ML_WORD => {
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                let p = base.as_ptr::<PolyWord>();
                // SAFETY: caller emits valid offsets
                let v = unsafe { *p.add(index) };
                self.pop()?;
                self.push_continue(v)
            }
            INSTR_LOAD_ML_BYTE => {
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                let p = base.as_ptr::<u8>();
                // SAFETY: caller emits valid offsets
                let b = unsafe { *p.add(index) };
                self.pop()?;
                self.push_continue(PolyWord::tagged(isize::from(b)))
            }
            INSTR_LOAD_UNTAGGED => {
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                if !base.is_data_ptr() {
                    eprintln!(
                        "  LOAD_UNTAGGED: base={base:?}, index={index}, sp_depth={}, frames={}",
                        self.stack_height(),
                        self.frames.len()
                    );
                    // Print the ring of recent call targets — gives us
                    // a "what was just executing" trail back from the
                    // failure point. Most-recent first. We also try to
                    // extract function names from each code object's
                    // constant pool (first const = source-level name).
                    eprintln!("  Recent CALL targets (most recent first):");
                    let n = self.recent_call_targets.len();
                    for off in 0..n {
                        let idx = (self.recent_call_idx + n - 1 - off) % n;
                        let target = self.recent_call_targets[idx];
                        if target != 0 {
                            // SAFETY: target was recorded from a live
                            // code-object pointer; still alive now.
                            let name = unsafe {
                                crate::length_word::function_name_for_code(
                                    target as *const PolyWord,
                                )
                            }
                            .unwrap_or_else(|| "<anonymous>".to_string());
                            eprintln!("    -{off:2}: code=0x{target:016x}  {name}");
                        }
                    }
                    // Also try to name the currently-executing code.
                    let cur_name = unsafe {
                        crate::length_word::function_name_for_code(
                            self.code_start.cast::<PolyWord>(),
                        )
                    }
                    .unwrap_or_else(|| "<anonymous>".to_string());
                    eprintln!(
                        "  Current code: 0x{:016x} {cur_name}",
                        self.code_start as usize
                    );
                    let cur_off = self.pc_offset();
                    let lo = cur_off.saturating_sub(30);
                    let hi = cur_off + 4;
                    eprintln!("  Bytecode [{lo}..{hi}]:");
                    for off in lo..hi {
                        // SAFETY: within current code segment.
                        let b = unsafe { *self.code_start.add(off) };
                        let marker = if off + 1 == cur_off {
                            " ← LOAD_UNTAGGED"
                        } else {
                            ""
                        };
                        eprintln!("    +{off:5}: 0x{b:02x}{marker}");
                    }
                    return Err(InterpError::NotAClosure(base));
                }
                let p = base.as_ptr::<PolyWord>();
                // SAFETY: caller emits valid offsets
                let raw = unsafe { *p.add(index) };
                self.pop()?;
                // Re-tag: untag the raw bits as if they were already
                // a numeric value to be tagged.
                self.push_continue(PolyWord::tagged(raw.0 as isize))
            }
            INSTR_STORE_ML_WORD => {
                let to_store = self.pop()?;
                let index_word = self.pop()?;
                let index = index_word.untag() as usize;
                let base = self.peek(0)?;
                // Diagnostic: catch bad bases (non-pointer or below
                // mapped memory) and dump context. Gated on env var.
                // Also fires when the popped INDEX is itself a pointer
                // (not a tagged int) — that means a stack/PC desync upstream.
                if jit_trace_stores_on() {
                    let b = base.0;
                    let suspicious = b < 0x1000
                        || (b & 0x1) != 0
                        || index > 0x10_0000
                        || !index_word.is_tagged();
                    if suspicious {
                        let pc_off = unsafe { self.pc.offset_from(self.code_start) };
                        eprintln!(
                            "  STORE_ML_WORD BAD: base=0x{b:016x} index_word=0x{:016x} (tagged={}) index={index} to_store=0x{:016x} cur_code=0x{:016x} pc_off={pc_off} frames_depth={}",
                            index_word.0,
                            index_word.is_tagged(),
                            to_store.0,
                            self.code_start as usize,
                            self.frames.len(),
                        );
                        // Dump the bytecode stream leading up to this store so
                        // a desyncing constant-load opcode is visible.
                        if pc_off >= 0 {
                            let lo = (pc_off as usize).saturating_sub(48);
                            let hi = (pc_off as usize) + 4;
                            let bytes: Vec<String> = (lo..hi)
                                .map(|i| {
                                    let mark = if i as isize == pc_off { "[" } else { " " };
                                    let b = unsafe { *self.code_start.add(i) };
                                    format!("{mark}{b:02x}")
                                })
                                .collect();
                            eprintln!("    bc[{lo}..{hi}] = {}", bytes.join(""));
                        }
                        // Dump the opcode ring buffer (last ~192 executed ops)
                        // to expose the PC desync / stack imbalance origin.
                        if arbint_trace_on() {
                            OP_RING.with(|r| {
                                let ring = r.borrow();
                                let cur = self.code_start as usize;
                                eprintln!("    --- op ring (last {}), cur_code=0x{cur:x} ---", ring.len());
                                // Dump bytecode head of each distinct code object seen.
                                let mut seen: Vec<usize> = Vec::new();
                                for (code, _, _, _) in ring.iter() {
                                    if !seen.contains(code) {
                                        seen.push(*code);
                                        let bytes: Vec<String> = (0..20usize)
                                            .map(|i| {
                                                let b = unsafe { *(*code as *const u8).add(i) };
                                                format!("{b:02x}")
                                            })
                                            .collect();
                                        eprintln!("    codehead 0x{code:x}: {}", bytes.join(" "));
                                    }
                                }
                                for (code, off, op, sp) in ring.iter() {
                                    let same = if *code == cur { "*" } else { " " };
                                    eprintln!("    {same}code=0x{code:x} off={off:>5} op=0x{op:02x} sp={sp}");
                                }
                            });
                        }
                        let recent = self.recent_call_targets_snapshot();
                        for (i, t) in recent.iter().enumerate().take(5) {
                            eprintln!("    recent call -{i}: 0x{t:016x}");
                        }
                        // Stack window
                        let n = std::cmp::min(8, self.stack.len().saturating_sub(self.sp));
                        for d in 0..n {
                            let w = self.stack[self.sp + d];
                            eprintln!("    sp[{d:2}] = {w:?}");
                        }
                        std::process::abort();
                    }
                }
                let p = base.as_ptr::<PolyWord>().cast_mut();
                // SAFETY: caller emits valid offsets; base is mutable
                unsafe { p.add(index).write(to_store) };
                self.pop()?;
                self.push_continue(PolyWord::tagged(0))
            }
            INSTR_STORE_ML_BYTE => {
                let to_store = self.pop()?.untag() as u8;
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                let p = base.as_ptr::<u8>().cast_mut();
                // SAFETY: caller emits valid offsets; base is mutable
                unsafe { p.add(index).write(to_store) };
                self.pop()?;
                self.push_continue(PolyWord::tagged(0))
            }
            // storeUntagged: pop untagged-bits + index, peek base,
            // base[index] = bits (as raw, not re-tagged).
            // bytecode.cpp:1259-1266.
            INSTR_STORE_UNTAGGED => {
                let raw = self.pop()?.untag() as usize;
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                let p = base.as_ptr::<PolyWord>().cast_mut();
                // SAFETY: caller emits valid offset on mutable base
                unsafe { p.add(index).write(PolyWord::from_bits(raw)) };
                self.pop()?;
                self.push_continue(PolyWord::tagged(0))
            }
            // blockMoveByte: pop length, destOff, dest, srcOff, peek src,
            // memmove. Use memmove (not memcpy) — bytecode permits
            // overlapping ranges.
            // bytecode.cpp:1281-1291.
            INSTR_BLOCK_MOVE_BYTE => {
                let length = self.pop()?.untag() as usize;
                let dest_off = self.pop()?.untag() as usize;
                let dest = self.pop()?.as_ptr::<u8>().cast_mut();
                let src_off = self.pop()?.untag() as usize;
                let src = self.peek(0)?.as_ptr::<u8>();
                // SAFETY: caller emits valid offsets + lengths
                unsafe { std::ptr::copy(src.add(src_off), dest.add(dest_off), length) };
                self.pop()?;
                self.push_continue(PolyWord::tagged(0))
            }
            // blockMoveWord: same but moves length WORDS (PolyWord-sized).
            INSTR_BLOCK_MOVE_WORD => {
                let length = self.pop()?.untag() as usize;
                let dest_off = self.pop()?.untag() as usize;
                let dest = self.pop()?.as_ptr::<PolyWord>().cast_mut();
                let src_off = self.pop()?.untag() as usize;
                let src = self.peek(0)?.as_ptr::<PolyWord>();
                // SAFETY: caller emits valid offsets + lengths
                unsafe { std::ptr::copy(src.add(src_off), dest.add(dest_off), length) };
                self.pop()?;
                self.push_continue(PolyWord::tagged(0))
            }
            // blockEqualByte: like blockMoveByte but memcmp == 0.
            // bytecode.cpp:1293-1302.
            INSTR_BLOCK_EQUAL_BYTE => {
                let length = self.pop()?.untag() as usize;
                let off2 = self.pop()?.untag() as usize;
                let p2 = self.pop()?.as_ptr::<u8>();
                let off1 = self.pop()?.untag() as usize;
                let p1 = self.peek(0)?.as_ptr::<u8>();
                // SAFETY: caller emits valid offsets + lengths
                let equal = unsafe {
                    let s1 = std::slice::from_raw_parts(p1.add(off1), length);
                    let s2 = std::slice::from_raw_parts(p2.add(off2), length);
                    s1 == s2
                };
                self.pop()?;
                self.push_continue(if equal {
                    PolyWord::tagged(1)
                } else {
                    PolyWord::tagged(0)
                })
            }
            // blockCompareByte: like blockEqualByte but returns
            // TAGGED(-1)/0/+1. bytecode.cpp:1304-1316.
            INSTR_BLOCK_COMPARE_BYTE => {
                let length = self.pop()?.untag() as usize;
                let off2 = self.pop()?.untag() as usize;
                let p2 = self.pop()?.as_ptr::<u8>();
                let off1 = self.pop()?.untag() as usize;
                let p1 = self.peek(0)?.as_ptr::<u8>();
                // SAFETY: caller emits valid offsets + lengths
                let ordering = unsafe {
                    let s1 = std::slice::from_raw_parts(p1.add(off1), length);
                    let s2 = std::slice::from_raw_parts(p2.add(off2), length);
                    s1.cmp(s2)
                };
                self.pop()?;
                self.push_continue(PolyWord::tagged(match ordering {
                    std::cmp::Ordering::Equal => 0,
                    std::cmp::Ordering::Less => -1,
                    std::cmp::Ordering::Greater => 1,
                }))
            }

            // ----- Exception handling
            //
            // bytecode.cpp:338-374 (push/set/delete) + 486-498 (raise)
            // + 569 (ldexc). The model is a singly-linked chain on the
            // ML stack: each handler frame is [handler_pc, old_handler_sp]
            // pushed by PUSH_HANDLER + SET_HANDLER; `handler_sp` points
            // at the top slot of the most-recent frame.
            INSTR_PUSH_HANDLER => {
                // Save the OLD handler register on the stack.
                self.push_continue(PolyWord::from_bits(self.handler_sp))
            }
            INSTR_SET_HANDLER8 => {
                let off = self.fetch_u8()? as usize;
                // SAFETY: caller emits valid in-segment offset
                let entry = unsafe { self.pc.add(off) };
                self.push(PolyWord::from_bits(entry as usize))?;
                self.handler_sp = self.sp;
                self.handler_frames_depth
                    .push((self.frames.len(), self.code_start, self.code_end));
                Ok(StepResult::Continue)
            }
            INSTR_SET_HANDLER16 => {
                let off = self.fetch_u16_le()? as usize;
                let entry = unsafe { self.pc.add(off) };
                self.push(PolyWord::from_bits(entry as usize))?;
                self.handler_sp = self.sp;
                self.handler_frames_depth
                    .push((self.frames.len(), self.code_start, self.code_end));
                Ok(StepResult::Continue)
            }
            INSTR_DELETE_HANDLER => {
                // bytecode.cpp:366-373
                //   u = pop result
                //   sp = handler_register
                //   sp++ (skip handler_pc slot)
                //   handler_register = sp's slot (old_handler_sp)
                //   *sp = u (replace old_handler_sp slot with result)
                let result = self.pop()?;
                self.sp = self.handler_sp;
                self.sp += 1; // skip handler_pc slot
                let old_handler = self.stack[self.sp];
                self.handler_sp = old_handler.0;
                self.stack[self.sp] = result;
                self.handler_frames_depth.pop();
                Ok(StepResult::Continue)
            }
            INSTR_LDEXC => {
                // Push the current exception packet (zero if none).
                let pkt = self.exception_packet.unwrap_or_else(|| PolyWord::tagged(0));
                self.push_continue(pkt)
            }
            INSTR_RAISE_EX => {
                // bytecode.cpp:486-499. Peek (don't pop) the exception
                // on top, record it. Then unwind:
                //   sp = handler_sp
                //   pc = pop handler_pc
                //   handler_sp = pop saved_old_handler_sp
                //   frames truncated to depth recorded at SET_HANDLER
                let exn = self.peek(0)?;
                self.exception_packet = Some(exn);
                if self.handler_sp >= self.stack.len() {
                    return Err(InterpError::UnhandledException);
                }
                self.sp = self.handler_sp;
                let handler_pc_word = self.stack[self.sp];
                self.sp += 1; // past handler_pc
                let saved_old_handler = self.stack[self.sp];
                self.sp += 1; // past saved_old_handler_sp
                self.handler_sp = saved_old_handler.0;
                self.pc = handler_pc_word.0 as *const u8;
                // Roll the call-frame side stack back to the depth
                // recorded at SET_HANDLER, and restore the code
                // segment the handler lives in. The handler's PC
                // is in the function that did SET_HANDLER — NOT
                // the caller — so we must keep that function's
                // code_start/code_end, even though its CALL frame
                // is no longer on the side-stack (it's the "current"
                // function from a frames-depth perspective).
                let (target_depth, h_start, h_end) = self.handler_frames_depth.pop().unwrap_or((
                    0,
                    std::ptr::null(),
                    std::ptr::null(),
                ));
                self.frames.truncate(target_depth);
                self.code_start = h_start;
                self.code_end = h_end;
                Ok(StepResult::Continue)
            }

            // ----- Fused stack/heap access opcodes (peephole-optimised
            // sequences emitted by the PolyML compiler).
            //
            // INDIRECT_LOCAL_B0/B1/BB and INDIRECT_0_LOCAL_0 read a
            // closure-like object N words deep on the stack, then
            // fetch field [0/1] (or arbitrary) of it onto the stack.
            INSTR_INDIRECT_LOCAL_B0 => {
                let depth = self.fetch_u8()? as usize;
                let u = self.peek(depth)?;
                let p = u.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid object reference
                let val = unsafe { *p };
                self.push_continue(val)
            }
            INSTR_INDIRECT_LOCAL_B1 => {
                let depth = self.fetch_u8()? as usize;
                let u = self.peek(depth)?;
                let p = u.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid object reference
                let val = unsafe { *p.add(1) };
                self.push_continue(val)
            }
            INSTR_INDIRECT_0_LOCAL_0 => {
                let u = self.peek(0)?;
                let p = u.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid object reference
                let val = unsafe { *p };
                self.push_continue(val)
            }
            INSTR_INDIRECT_LOCAL_BB => {
                let depth = self.fetch_u8()? as usize;
                let slot = self.fetch_u8()? as usize;
                let u = self.peek(depth)?;
                let p = u.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid object reference + slot
                let val = unsafe { *p.add(slot) };
                self.push_continue(val)
            }
            INSTR_IS_TAGGED_LOCAL_B => {
                let depth = self.fetch_u8()? as usize;
                let u = self.peek(depth)?;
                self.push_continue(if u.is_tagged() {
                    PolyWord::tagged(1)
                } else {
                    PolyWord::tagged(0)
                })
            }
            // Compare a local with a small tagged constant; jump if NOT
            // equal. Immediates: pc[0]=depth, pc[1]=tagged_constant,
            // pc[2]=jump_offset_when_not_equal.
            INSTR_JUMP_NEQ_LOCAL => {
                let depth = self.fetch_u8()? as usize;
                let want = self.fetch_u8()?;
                let off = self.fetch_u8()? as usize;
                let u = self.peek(depth)?;
                if u.is_tagged() && u.untag() == isize::from(want) {
                    // fall through (equal)
                } else {
                    self.pc_offset_signed(off as isize)?;
                }
                Ok(StepResult::Continue)
            }
            // Same but reads field 0 of the local first (union-tag test).
            INSTR_JUMP_NEQ_LOCAL_IND => {
                let depth = self.fetch_u8()? as usize;
                let want = self.fetch_u8()?;
                let off = self.fetch_u8()? as usize;
                let local = self.peek(depth)?;
                let p = local.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid tuple reference
                let u = unsafe { *p };
                if u.is_tagged() && u.untag() == isize::from(want) {
                    // fall through
                } else {
                    self.pc_offset_signed(off as isize)?;
                }
                Ok(StepResult::Continue)
            }
            // Peek sp[depth]; if tagged, jump.
            INSTR_JUMP_TAGGED_LOCAL => {
                let depth = self.fetch_u8()? as usize;
                let off = self.fetch_u8()? as usize;
                let u = self.peek(depth)?;
                if u.is_tagged() {
                    self.pc_offset_signed(off as isize)?;
                }
                Ok(StepResult::Continue)
            }

            // SET_STACK_VAL_B: pop value, write into sp[imm - 1].
            // Note the "-1" — bytecode.cpp:613 reads `sp[*pc-1] = u`.
            INSTR_SET_STACK_VAL_B => {
                let idx = self.fetch_u8()? as usize;
                let u = self.pop()?;
                // sp[idx - 1] — we read with depth (idx - 1). If idx is 0
                // this would wrap; trust the compiler not to emit that.
                let target = self
                    .sp
                    .checked_add(idx.checked_sub(1).ok_or(InterpError::StackUnderflow)?)
                    .filter(|i| *i < self.stack.len())
                    .ok_or(InterpError::StackUnderflow)?;
                self.stack[target] = u;
                Ok(StepResult::Continue)
            }

            // ----- Closure field access
            INSTR_INDIRECT_CLOSURE_B0 => self.do_indirect_closure(0),
            INSTR_INDIRECT_CLOSURE_B1 => self.do_indirect_closure(1),
            INSTR_INDIRECT_CLOSURE_B2 => self.do_indirect_closure(2),
            INSTR_INDIRECT_CLOSURE_BB => {
                // depth + slot, both as 1-byte immediates
                let depth = self.fetch_u8()? as usize;
                let slot = self.fetch_u8()? as usize;
                let closure_word = self.peek(depth)?;
                let p = closure_word.as_ptr::<PolyWord>();
                // SAFETY: caller emitted valid slot index
                let val = unsafe { *p.add(1 + slot) };
                self.push_continue(val)
            }

            // ----- Indirect (heap field read)
            INSTR_INDIRECT_0 => self.indirect(0),
            INSTR_INDIRECT_1 => self.indirect(1),
            INSTR_INDIRECT_2 => self.indirect(2),
            INSTR_INDIRECT_3 => self.indirect(3),
            INSTR_INDIRECT_4 => self.indirect(4),
            INSTR_INDIRECT_5 => self.indirect(5),
            INSTR_INDIRECT_B => {
                let n = self.fetch_u8()? as usize;
                self.indirect(n)
            }

            // ----- PC-relative constants
            //
            // bytecode.cpp:529-535 + 442-: constants live AFTER the
            // bytecode in the same code object, so all PC-relative
            // offsets are forward (positive). Upstream treats the
            // immediate bytes as `unsigned char` (promoted to int),
            // so we match: read as `usize`, add forward.
            //
            // Formulas (after the handler has fetched its immediates,
            // making our `self.pc` equivalent to the upstream `pc + N`
            // where N is the number of immediate bytes):
            //
            //   const_addr8_0     val = (PolyWord*)(self.pc + imm)[3]
            //   const_addr8_1     val = (PolyWord*)(self.pc + imm)[4]
            //   const_addr8_8     val = (PolyWord*)(self.pc + imm1)[imm2 + 3]
            //   const_addr16_8    val = (PolyWord*)(self.pc + imm1_16)[imm2 + 3]
            INSTR_CONST_ADDR8_0 => {
                let imm = self.fetch_u8()? as usize;
                let w = unsafe { self.read_pc_const(imm, 3) };
                self.push_continue(w)
            }
            INSTR_CONST_ADDR8_1 => {
                let imm = self.fetch_u8()? as usize;
                let w = unsafe { self.read_pc_const(imm, 4) };
                self.push_continue(w)
            }
            INSTR_CONST_ADDR8_8 => {
                let imm1 = self.fetch_u8()? as usize;
                let imm2 = self.fetch_u8()? as usize;
                let w = unsafe { self.read_pc_const(imm1, imm2 + 3) };
                self.push_continue(w)
            }
            INSTR_CONST_ADDR16_8 => {
                let imm1 = self.fetch_u16_le()? as usize;
                let imm2 = self.fetch_u8()? as usize;
                let w = unsafe { self.read_pc_const(imm1, imm2 + 3) };
                self.push_continue(w)
            }

            // ----- Function calls
            //
            // call_closure: pop closure from top, save retPC, push
            // closure back, jump to closure's first word (which is
            // the code address).
            INSTR_CALL_CLOSURE => {
                let closure = self.pop()?;
                self.do_call(closure)?;
                Ok(StepResult::Continue)
            }
            // call_const_addr*: load a closure from the const pool
            // (same formula as const_addr*) then dispatch as CALL_CLOSURE.
            INSTR_CALL_CONST_ADDR8_0 => {
                let imm = self.fetch_u8()? as usize;
                let closure = unsafe { self.read_pc_const(imm, 3) };
                self.do_call(closure)?;
                Ok(StepResult::Continue)
            }
            INSTR_CALL_CONST_ADDR8_1 => {
                let imm = self.fetch_u8()? as usize;
                let closure = unsafe { self.read_pc_const(imm, 4) };
                self.do_call(closure)?;
                Ok(StepResult::Continue)
            }
            INSTR_CALL_CONST_ADDR8_8 => {
                let imm1 = self.fetch_u8()? as usize;
                let imm2 = self.fetch_u8()? as usize;
                let closure = unsafe { self.read_pc_const(imm1, imm2 + 3) };
                self.do_call(closure)?;
                Ok(StepResult::Continue)
            }
            INSTR_CALL_CONST_ADDR16_8 => {
                let imm1 = self.fetch_u16_le()? as usize;
                let imm2 = self.fetch_u8()? as usize;
                let closure = unsafe { self.read_pc_const(imm1, imm2 + 3) };
                self.do_call(closure)?;
                Ok(StepResult::Continue)
            }
            INSTR_CALL_LOCAL_B => {
                // closure is at sp[N]; treat the same as call_closure
                // after copying the value to top (and removing the
                // source slot? No — call_closure pops, so we push the
                // copy and let pop handle it).
                let n = self.fetch_u8()? as usize;
                let closure = self.peek(n)?;
                self.do_call(closure)?;
                Ok(StepResult::Continue)
            }

            // ----- Jumps
            INSTR_JUMP8 => {
                let off = self.fetch_u8()? as usize;
                self.pc_offset_signed(off as isize)?;
                Ok(StepResult::Continue)
            }
            INSTR_JUMP_BACK8 => {
                let off = self.fetch_u8()? as usize;
                // Compiler emits diff = ic - dest (where ic is the
                // opcode position and dest is destination). Upstream's
                // interpreter `pc -= *pc + 1` (with pc at the
                // immediate, = ic+1) lands at pc = ic+1 - diff - 1
                // = ic - diff = dest. Our self.pc is at ic+2 after
                // both fetches, so we subtract (off + 2) to land at
                // ic - off = dest.
                self.pc_offset_signed(-((off as isize) + 2))?;
                Ok(StepResult::Continue)
            }
            INSTR_JUMP16 => {
                let off = self.fetch_u16_le()? as usize;
                self.pc_offset_signed(off as isize)?;
                Ok(StepResult::Continue)
            }
            INSTR_JUMP_BACK16 => {
                let off = self.fetch_u16_le()? as usize;
                // Same shape as JUMP_BACK8 but 16-bit immediate;
                // self.pc is at ic+3 after fetches.
                self.pc_offset_signed(-((off as isize) + 3))?;
                Ok(StepResult::Continue)
            }
            // CASE16: switch dispatch with a u16 jump table inline.
            //
            //   Stack: top is the (tagged) selector.
            //   PC layout: [arg1_lo arg1_hi  off0_lo off0_hi  off1...]
            //   where arg1 is the number of cases (entries in table).
            //
            // Pop selector, untag → u. If u >= arg1 or u < 0, jump to
            // the default case at pc + 2 + arg1*2 (past the table).
            // Otherwise PC moves past the count, then adds the u16
            // offset stored at table entry u (= bytes at pc + u*2).
            //
            // See bytecode.cpp:376-385.
            INSTR_CASE16 => {
                // Selector is conventionally tagged but upstream just
                // does UNTAGGED unconditionally — we mirror that.
                let selector = self.pop()?;
                let u = selector.untag();
                // Read arg1 = u16 inline. `fetch_u16_le` advances PC
                // past it; we hold on to the "table start" position
                // afterwards.
                let table_start = self.pc;
                let arg1 = self.fetch_u16_le()? as isize;
                let table_after = self.pc; // immediately past arg1
                if u < 0 || u >= arg1 {
                    // Out of range: jump to default case at table_after + arg1*2
                    // (We've already advanced past arg1; just add arg1*2.)
                    self.pc_offset_signed(arg1 * 2)?;
                } else {
                    // SAFETY: u in [0, arg1), so table entry exists.
                    let entry_off = unsafe {
                        let entry = table_after.add((u as usize) * 2);
                        let lo = *entry as usize;
                        let hi = *entry.add(1) as usize;
                        lo + hi * 256
                    };
                    // Upstream lands at table_after + entry_off:
                    //   `pc += 2; pc += pc[u*2]+pc[u*2+1]*256;`
                    //   the second `pc += ...` reads from the table
                    //   THEN adds — base is table_after.
                    self.pc = table_after;
                    self.pc_offset_signed(entry_off as isize)?;
                }
                let _ = table_start;
                Ok(StepResult::Continue)
            }

            INSTR_JUMP8_FALSE => {
                let off = self.fetch_u8()? as usize;
                if self.pop()? == PolyWord::tagged(0) {
                    self.pc_offset_signed(off as isize)?;
                }
                Ok(StepResult::Continue)
            }
            INSTR_JUMP8_TRUE => {
                let off = self.fetch_u8()? as usize;
                if self.pop()? != PolyWord::tagged(0) {
                    self.pc_offset_signed(off as isize)?;
                }
                Ok(StepResult::Continue)
            }
            INSTR_JUMP16_FALSE => {
                let off = self.fetch_u16_le()? as usize;
                if self.pop()? == PolyWord::tagged(0) {
                    self.pc_offset_signed(off as isize)?;
                }
                Ok(StepResult::Continue)
            }
            INSTR_JUMP16_TRUE => {
                let off = self.fetch_u16_le()? as usize;
                if self.pop()? != PolyWord::tagged(0) {
                    self.pc_offset_signed(off as isize)?;
                }
                Ok(StepResult::Continue)
            }

            // ----- Fixed (tagged) integer arithmetic.
            // FixedInt is NON-boxing fixed precision: out-of-tagged-range results
            // RAISE Overflow (unlike INSTR_ARB_* which box into a bignum).
            // bytecode.cpp:926-981 range-checks the result; mult has no portable
            // signed-overflow test upstream (calls mult_longc, checks IsDataPtr),
            // so we test in i128.
            INSTR_FIXED_ADD => self.fixed_add(),
            INSTR_FIXED_SUB => self.fixed_sub(),
            INSTR_FIXED_MULT => self.fixed_mult(),
            INSTR_FIXED_QUOT => self.bin_op_tagged(|x, y| {
                if x == 0 {
                    Err(())
                } else {
                    Ok(y.wrapping_div(x))
                }
            }),
            INSTR_FIXED_REM => self.bin_op_tagged(|x, y| {
                if x == 0 {
                    Err(())
                } else {
                    Ok(y.wrapping_rem(x))
                }
            }),

            // ----- Arbitrary-precision arithmetic with tagged-int
            // fast path. Upstream falls through to add_longc /
            // sub_longc / mult_longc on overflow; we don't have a
            // bignum allocator yet, so we leave the value alone
            // (= top stays as-is) — bootstrap rarely hits overflow
            // in compile-time math.
            //
            // bytecode.cpp:1077-1148
            INSTR_ARB_ADD => self.arb_add_pair(),
            INSTR_ARB_SUBTRACT => self.arb_sub_pair(),
            INSTR_ARB_MULTIPLY => self.arb_mult_pair(),

            // ----- Word arithmetic (TAG-AWARE, per bytecode.cpp:1001-)
            //
            // PolyML stores ints as `(n << 1) | 1`. WORD_ADD on two
            // tagged ints adds the bit-patterns and SUBTRACTS one tag
            // bit to recover the right encoding:
            //   (2A+1) + (2B+1) - 1 = 2(A+B) + 1 = TAGGED(A+B).
            // Similar dance for WORD_SUB (+ instead of -). MULT/DIV/MOD/
            // SHIFT untag inputs and re-tag the result. AND/OR are bit
            // identities that preserve the tag bit naturally; XOR
            // clears it (1^1=0) so must reinstate via `| 1`.
            INSTR_WORD_ADD => {
                self.bin_op_word(|x, y| y.wrapping_add(x).wrapping_sub(PolyWord::tagged(0).0))
            }
            INSTR_WORD_SUB => {
                self.bin_op_word(|x, y| y.wrapping_sub(x).wrapping_add(PolyWord::tagged(0).0))
            }
            INSTR_WORD_MULT => self.bin_op_word(|x, y| {
                let ax = x >> 1;
                let ay = y >> 1;
                ((ax.wrapping_mul(ay)) << 1) | 1
            }),
            INSTR_WORD_AND => self.bin_op_word(|x, y| y & x),
            INSTR_WORD_OR => self.bin_op_word(|x, y| y | x),
            INSTR_WORD_XOR => self.bin_op_word(|x, y| (y ^ x) | PolyWord::tagged(0).0),
            INSTR_WORD_SHIFT_LEFT => self.bin_op_word(|x, y| {
                let s = (x >> 1) & 63;
                let v = y >> 1;
                ((v.wrapping_shl(s as u32)) << 1) | 1
            }),
            INSTR_WORD_SHIFT_R_LOG => self.bin_op_word(|x, y| {
                let s = (x >> 1) & 63;
                let v = y >> 1;
                ((v.wrapping_shr(s as u32)) << 1) | 1
            }),
            INSTR_WORD_DIV => self.bin_op_word_checked(|x, y| {
                let ax = x >> 1;
                let ay = y >> 1;
                ay.checked_div(ax).map(|q| (q << 1) | 1).ok_or(())
            }),
            INSTR_WORD_MOD => self.bin_op_word_checked(|x, y| {
                let ax = x >> 1;
                let ay = y >> 1;
                ay.checked_rem(ax).map(|r| (r << 1) | 1).ok_or(())
            }),

            // ----- Comparisons
            INSTR_EQUAL_WORD => self.bin_op_cmp(|x, y| x == y),
            INSTR_LESS_SIGNED => self.bin_op_cmp(|x, y| (y as isize) < (x as isize)),
            INSTR_LESS_UNSIGNED => self.bin_op_cmp(|x, y| y < x),
            INSTR_LESS_EQ_SIGNED => self.bin_op_cmp(|x, y| (y as isize) <= (x as isize)),
            INSTR_LESS_EQ_UNSIGNED => self.bin_op_cmp(|x, y| y <= x),
            INSTR_GREATER_SIGNED => self.bin_op_cmp(|x, y| (y as isize) > (x as isize)),
            INSTR_GREATER_UNSIGNED => self.bin_op_cmp(|x, y| y > x),
            INSTR_GREATER_EQ_SIGNED => self.bin_op_cmp(|x, y| (y as isize) >= (x as isize)),
            INSTR_GREATER_EQ_UNSIGNED => self.bin_op_cmp(|x, y| y >= x),

            // ----- Boolean / tag tests
            INSTR_NOT_BOOLEAN => {
                let v = self.pop()?;
                self.push_continue(if v == PolyWord::tagged(0) {
                    PolyWord::tagged(1)
                } else {
                    PolyWord::tagged(0)
                })
            }
            INSTR_IS_TAGGED => {
                let v = self.pop()?;
                self.push_continue(if v.is_tagged() {
                    PolyWord::tagged(1)
                } else {
                    PolyWord::tagged(0)
                })
            }

            // ----- Stack manipulation
            //
            // RESET_N: drop top N items, NO preservation
            //          (`bytecode.cpp:669: sp += *pc`).
            // RESET_R_N: pop top into u, drop N items, push u back
            //            (`bytecode.cpp:665: pop+sp+=*pc+restore`).
            // These are NOT the same — early versions of this
            // interpreter merged them, which silently corrupted any
            // loop using RESET to clean up a discarded result.
            INSTR_RESET_1 => self.drop_n(1),
            INSTR_RESET_2 => self.drop_n(2),
            INSTR_RESET_B => {
                let n = self.fetch_u8()? as usize;
                self.drop_n(n)
            }
            INSTR_RESET_R_1 => self.reset(1),
            INSTR_RESET_R_2 => self.reset(2),
            INSTR_RESET_R_3 => self.reset(3),
            INSTR_RESET_R_B => {
                let n = self.fetch_u8()? as usize;
                self.reset(n)
            }

            // ----- Legacy atomic ops on the mutex object at top
            // (bytecode.cpp:803-823). Single-threaded interpreter:
            // add/subtract 2 (= raw representation of tagged 1 with
            // the tag bit removed) to word 0, write back, replace
            // top with the new value.
            INSTR_ATOMIC_INCR => self.atomic_incr_decr(true),
            INSTR_ATOMIC_DECR => self.atomic_incr_decr(false),

            // ----- Returns
            INSTR_RETURN_1 => self.do_return(1),
            INSTR_RETURN_2 => self.do_return(2),
            INSTR_RETURN_3 => self.do_return(3),
            INSTR_RETURN_B => {
                let n = self.fetch_u8()? as usize;
                self.do_return(n)
            }
            INSTR_RETURN_W => {
                let n = self.fetch_u16_le()? as usize;
                self.do_return(n)
            }

            // ----- Extended opcodes (one-byte ESCAPE prefix)
            INSTR_ESCAPE => self.dispatch_extended(opcode_pc),

            // ----- Everything else: surface to caller
            _ => {
                // Roll back so PC points AT the unknown op.
                self.pc = opcode_pc;
                Ok(StepResult::Unimplemented {
                    op,
                    extended: false,
                })
            }
        }
    }

    /// Dispatch an extended opcode (the byte after ESCAPE / 0xfe).
    #[allow(clippy::too_many_lines)]
    fn dispatch_extended(&mut self, escape_pc: *const u8) -> Result<StepResult, InterpError> {
        use opcodes::ext::*;
        let ext = self.fetch_u8()?;
        match ext {
            // ----- Mutex (single-threaded; pessimistic semantics)
            //
            // For genuine single-thread correctness we'd accurately
            // model the counter (see bytecode.cpp:1496-1532). But the
            // bootstrap's mutex use is entangled with other stubbed
            // RTS calls (PolyBasicIOGeneral etc.) that return wrong
            // values, and "correct" mutex semantics here just exposes
            // those downstream bugs as crashes. So we run the
            // pessimistic version: every lock-attempt is "contested",
            // falling through to PolyThreadMutexBlock which returns
            // zero. Net effect: bootstrap loops in mutex-block until
            // the next non-mutex divergence happens.
            //
            // The right long-term fix is real impls of the RTS
            // functions, not better mutex stubs.
            EXTINSTR_CREATE_MUTEX => {
                use crate::length_word::{F_MUTABLE_BIT, F_NO_OVERWRITE, F_WEAK_BIT};
                let p = self.allocate(1, F_MUTABLE_BIT | F_NO_OVERWRITE | F_WEAK_BIT)?;
                // SAFETY: just allocated 1 word
                unsafe { p.add(0).write(PolyWord::tagged(0)) };
                self.push_continue(PolyWord::from_ptr(p.cast_const()))
            }
            // Real mutex semantics (bytecode.cpp:1507-1532). Single-
            // threaded so locks never actually block — but we DO track
            // the mutex's first word so the SML retry loop terminates
            // and other lock/unlock pairs work correctly.
            //
            // Defensive: bootstrap occasionally passes non-pointer
            // values as the "mutex" (probably from stubbed RTS calls
            // returning TAGGED(0)). For those we just return success
            // without touching memory.
            EXTINSTR_LOCK_MUTEX => {
                let mutex = self.peek(0)?;
                let acquired =
                    if mutex.is_data_ptr() && mutex.0 & (std::mem::size_of::<usize>() - 1) == 0 {
                        let p = mutex.as_ptr::<PolyWord>().cast_mut();
                        // SAFETY: pointer-aligned & is_data_ptr ⇒ valid mutex slot
                        let old = unsafe { *p };
                        let was_unlocked = old.0 == PolyWord::tagged(0).0;
                        // Bump counter by 2 (PolyML convention; we don't
                        // need the count in single-thread but preserve it
                        // for round-trips with unlockMutex).
                        let new_bits = old.0.wrapping_add(2);
                        // SAFETY: same
                        unsafe { p.write(PolyWord::from_bits(new_bits)) };
                        was_unlocked
                    } else {
                        true
                    };
                self.pop()?;
                self.push_continue(if acquired {
                    PolyWord::tagged(1)
                } else {
                    PolyWord::tagged(0)
                })
            }
            EXTINSTR_TRY_LOCK_MUTEX => {
                let mutex = self.peek(0)?;
                let acquired =
                    if mutex.is_data_ptr() && mutex.0 & (std::mem::size_of::<usize>() - 1) == 0 {
                        let p = mutex.as_ptr::<PolyWord>().cast_mut();
                        // SAFETY: same as above
                        let old = unsafe { *p };
                        let was_unlocked = old.0 == PolyWord::tagged(0).0;
                        if was_unlocked {
                            // SAFETY: same
                            unsafe { p.write(PolyWord::tagged(1)) };
                        }
                        was_unlocked
                    } else {
                        true
                    };
                self.pop()?;
                self.push_continue(if acquired {
                    PolyWord::tagged(1)
                } else {
                    PolyWord::tagged(0)
                })
            }
            // atomicReset (= UnlockMutex builtin): write TAGGED(0)
            // (= unlocked) into the mutex and return a BOOLEAN that is
            // True iff this thread was the only locker, i.e. iff the old
            // value was exactly TAGGED(1). bytecode.cpp:1534-1542:
            //   oldValue = p->Get(0); p->Set(0, TAGGED(0));
            //   *sp = oldValue == TAGGED(1) ? True : False;
            // True/False are TAGGED(1)/TAGGED(0) (bytecode.cpp:86-87).
            // basis/Thread.sml:556 uses the result: True => done, False =>
            // fall through to PolyThreadMutexUnlock. Always returning False
            // forced a spurious Full-RTS call on every uncontended unlock.
            EXTINSTR_ATOMIC_RESET => {
                let mutex = self.pop()?;
                let was_sole_locker =
                    if mutex.is_data_ptr() && mutex.0 & (std::mem::size_of::<usize>() - 1) == 0 {
                        let p = mutex.as_ptr::<PolyWord>().cast_mut();
                        // SAFETY: pointer-aligned & is_data_ptr
                        let old = unsafe { *p };
                        // SAFETY: same
                        unsafe { p.write(PolyWord::tagged(0)) };
                        old.0 == PolyWord::tagged(1).0
                    } else {
                        // Non-pointer/misaligned defensive case (no upstream
                        // analogue). False = conservative "contended" path,
                        // harmless single-threaded (the follow-up
                        // PolyThreadMutexUnlock is an idempotent reset).
                        false
                    };
                self.push_continue(if was_sole_locker {
                    PolyWord::tagged(1)
                } else {
                    PolyWord::tagged(0)
                })
            }
            // atomicExchAdd (LEGACY: the current PolyML compiler no longer
            // emits this — IntCodeCons.ML:255 has the opcode commented out,
            // marked "Now legacy code"). Kept for image/opcode-stream
            // compatibility. Upstream bytecode.cpp:1483-1494: pops ONE
            // addend `u`, PEEKS the object on top, returns its old word0,
            // and writes back word0 = old + u - 1 (raw-tag arithmetic).
            // Raw bits: raw(a)=2a+1, so raw(old)+raw(u)-1 = 2(a+b)+1 =
            // TAGGED(a+b) — the -1 collapses the doubled tag bit. The old
            // version popped TWO slots (underflow by one) and ignored the
            // object entirely.
            EXTINSTR_ATOMIC_EXCH_ADD => {
                let addend = self.pop()?;
                let obj = self.peek(0)?;
                let old = if obj.is_data_ptr() && obj.0 & (std::mem::size_of::<usize>() - 1) == 0 {
                    let p = obj.as_ptr::<PolyWord>().cast_mut();
                    // SAFETY: pointer-aligned & is_data_ptr
                    let old = unsafe { *p };
                    let new_bits = old.0.wrapping_add(addend.0).wrapping_sub(1);
                    // SAFETY: same
                    unsafe { p.write(PolyWord::from_bits(new_bits)) };
                    old
                } else {
                    PolyWord::tagged(0)
                };
                // Replace top (the object) with the OLD word0.
                self.pop()?;
                self.push_continue(old)
            }
            // log2(word at top), replace top. (bytecode.cpp:2359-2367.)
            EXTINSTR_LOG2_WORD => {
                let w = self.peek(0)?;
                let mut p = w.untag() as usize;
                let mut v: usize = 0;
                p >>= 1;
                while p != 0 {
                    v += 1;
                    p >>= 1;
                }
                self.pop()?;
                self.push_continue(PolyWord::tagged(v as isize))
            }

            // ----- Wide variants of the base opcodes (16-bit immediates)
            EXTINSTR_INDIRECT_W => {
                let idx = self.fetch_u16_le()? as usize;
                let v = self.peek(0)?;
                let p = v.as_ptr::<PolyWord>();
                // SAFETY: caller emits valid offset
                let field = unsafe { *p.add(idx) };
                self.pop()?;
                self.push_continue(field)
            }
            EXTINSTR_TUPLE_W => {
                let n = self.fetch_u16_le()? as usize;
                self.do_tuple(n)
            }
            EXTINSTR_ALLOC_MUT_CLOSURE_W => {
                let n = self.fetch_u16_le()? as usize;
                self.do_alloc_mut_closure(n)
            }
            EXTINSTR_MOVE_TO_MUT_CLOSURE_W => {
                let slot = self.fetch_u16_le()? as usize;
                self.do_move_to_mut_closure(slot)
            }
            EXTINSTR_CLOSURE_W => {
                let n = self.fetch_u16_le()? as usize;
                self.do_create_closure(n)
            }
            EXTINSTR_INDIRECT_CLOSURE_W => {
                // bytecode.cpp:2310-2311: *sp = (*sp).AsObjPtr()->Get(arg1 + 1).
                // The 16-bit operand is the captured-field INDEX; the closure is on
                // TOP (peek 0); word 0 is the code pointer so the field is at 1+item;
                // replace in place (net 0). The old code peeked at `depth`, hardcoded
                // field 1, and pushed (net +1) — wrong on all three, and the stack
                // leak desynced every later frame. (Mirrors EXTINSTR_INDIRECT_W.)
                let item = self.fetch_u16_le()? as usize;
                let closure_word = self.peek(0)?;
                let p = closure_word.as_ptr::<PolyWord>();
                // SAFETY: caller emits a valid closure with field index in range.
                let val = unsafe { *p.add(1 + item) };
                self.pop()?;
                self.push_continue(val)
            }
            EXTINSTR_RESET_W => {
                // Wide RESET — drop top N items, no preservation.
                // Mirrors INSTR_RESET_B's "wide" counterpart.
                let n = self.fetch_u16_le()? as usize;
                self.drop_n(n)
            }
            EXTINSTR_RESET_R_W => {
                let n = self.fetch_u16_le()? as usize;
                self.reset(n)
            }

            // longWToTagged: read the first word of a boxed long-word
            // and re-tag it (dropping the top bit). Mirrors
            // bytecode.cpp:1545-1557.
            EXTINSTR_LONG_W_TO_TAGGED => {
                let p = self.peek(0)?;
                if p.is_data_ptr() {
                    let ptr = p.as_ptr::<PolyWord>();
                    // SAFETY: caller-trusted long-word object.
                    let raw = unsafe { (*ptr).0 };
                    #[allow(clippy::cast_possible_wrap)]
                    let v = raw as isize;
                    self.stack[self.sp] = PolyWord::tagged(v);
                } else if arbint_trace_on() {
                    let pc_off = unsafe { self.pc.offset_from(self.code_start) };
                    eprintln!(
                        "  LONG_W_TO_TAGGED on NON-PTR top: 0x{:016x} (tagged={}) pc_off={pc_off}",
                        p.0,
                        p.is_tagged()
                    );
                    std::process::abort();
                }
                Ok(StepResult::Continue)
            }

            // signedToLongW: box a tagged int as a 1-word byte object
            // holding the (sign-extended) untagged value. Replaces
            // top in place. bytecode.cpp:1559-1569.
            EXTINSTR_SIGNED_TO_LONG_W => {
                let x = self.pop()?;
                let value = x.untag(); // isize, sign-preserving
                let space = self.alloc_space.as_mut().ok_or(InterpError::NoAllocator)?;
                let p = space.alloc(1);
                // SAFETY: just allocated 1 word.
                unsafe {
                    crate::space::set_length_word(p, 1, crate::length_word::F_BYTE_OBJ);
                    // Cast the untagged signed value back into a word
                    // for storage (raw bit pattern).
                    #[allow(clippy::cast_sign_loss)]
                    p.write(PolyWord::from_bits(value as usize));
                }
                self.push_continue(PolyWord::from_ptr(p.cast_const()))
            }
            // unsignedToLongW: same shape as signedToLongW but treats
            // the input as unsigned. bytecode.cpp:1572-1582.
            EXTINSTR_UNSIGNED_TO_LONG_W => {
                let x = self.pop()?;
                let value = x.0 >> 1; // untagged unsigned (drop tag bit)
                let space = self.alloc_space.as_mut().ok_or(InterpError::NoAllocator)?;
                let p = space.alloc(1);
                // SAFETY: just allocated 1 word.
                unsafe {
                    crate::space::set_length_word(p, 1, crate::length_word::F_BYTE_OBJ);
                    p.write(PolyWord::from_bits(value));
                }
                self.push_continue(PolyWord::from_ptr(p.cast_const()))
            }

            // ----- PackWord / SysWord raw array accessors. bytecode.cpp:1438-1482.
            // Treat the base as a raw word array; read/write word[index].
            // loadPolyWord/loadNativeWord: pop index, peek base, box base[index]
            // as a 1-word byte object, replace top. Net -1.
            EXTINSTR_LOAD_POLY_WORD | EXTINSTR_LOAD_NATIVE_WORD => {
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                let p = base.as_ptr::<usize>();
                // SAFETY: compiler emits a valid base + in-bounds index.
                let r = unsafe { *p.add(index) };
                let boxed = self.alloc_lg_word(r)?;
                self.stack[self.sp] = boxed;
                Ok(StepResult::Continue)
            }
            // storePolyWord: pop toStore (boxed; read its word), pop index,
            // peek base, base[index] := toStore, replace top with Zero. Net -2.
            EXTINSTR_STORE_POLY_WORD => {
                let to_store = unsafe { Self::read_lg_word(self.pop()?) };
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                let p = base.as_ptr::<usize>().cast_mut();
                // SAFETY: compiler emits a valid mutable base + in-bounds index.
                unsafe { *p.add(index) = to_store };
                self.stack[self.sp] = PolyWord::tagged(0);
                Ok(StepResult::Continue)
            }
            // storeNativeWord: same but does NOT replace top — base stays. Net -2.
            EXTINSTR_STORE_NATIVE_WORD => {
                let to_store = unsafe { Self::read_lg_word(self.pop()?) };
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                let p = base.as_ptr::<usize>().cast_mut();
                // SAFETY: compiler emits a valid mutable base + in-bounds index.
                unsafe { *p.add(index) = to_store };
                Ok(StepResult::Continue)
            }

            // ----- Float (f32) arithmetic. On 64-bit, Float values
            // are *tagged* — packed into the high 32 bits of a
            // PolyWord with the low bit set (FLT_SHIFT = 32).
            // bytecode.cpp:224-249.
            EXTINSTR_FLOAT_ABS => self.float_unop(f32::abs),
            EXTINSTR_FLOAT_NEG => self.float_unop(|v: f32| -v),
            EXTINSTR_FLOAT_ADD => self.float_binop(|y, x| y + x),
            EXTINSTR_FLOAT_SUB => self.float_binop(|y, x| y - x),
            EXTINSTR_FLOAT_MULT => self.float_binop(|y, x| y * x),
            EXTINSTR_FLOAT_DIV => self.float_binop(|y, x| y / x),
            EXTINSTR_FLOAT_EQUAL => self.float_cmp(|y, x| {
                #[allow(clippy::float_cmp)]
                {
                    y == x
                }
            }),
            EXTINSTR_FLOAT_LESS => self.float_cmp(|y, x| y < x),
            EXTINSTR_FLOAT_LESS_EQ => self.float_cmp(|y, x| y <= x),
            EXTINSTR_FLOAT_GREATER => self.float_cmp(|y, x| y > x),
            EXTINSTR_FLOAT_GREATER_EQ => self.float_cmp(|y, x| y >= x),
            EXTINSTR_FLOAT_UNORDERED => self.float_cmp(|y, x| y.is_nan() || x.is_nan()),
            EXTINSTR_FIXED_INT_TO_FLOAT => {
                let i = self.peek(0)?;
                #[allow(clippy::cast_precision_loss)]
                let f = i.untag() as f32;
                self.stack[self.sp] = Self::box_float(f);
                Ok(StepResult::Continue)
            }
            EXTINSTR_FLOAT_TO_REAL => {
                let f = Self::unbox_float(self.peek(0)?);
                let p = self.alloc_real(f64::from(f))?;
                self.stack[self.sp] = p;
                Ok(StepResult::Continue)
            }
            EXTINSTR_REAL_TO_FLOAT => {
                let r = self.peek(0)?;
                // SAFETY: peek returns a boxed Real pointer.
                let d = unsafe { Self::read_real(r) };
                // bytecode.cpp:1999 — realToFloat carries a trailing rounding-mode
                // operand byte (genDoubleToFloat emits 5 = use-current-rounding).
                // It MUST be consumed; otherwise PC lands on that byte and, since
                // 5 == INSTR_STORE_ML_WORD (0x05), we dispatch a spurious store one
                // byte early. This was the arbitrary-int basis/Real.sml load SEGV:
                // Real32.fromReal directly follows Real.fromLargeInt only on the
                // arbitrary-precision branch, so the desync surfaces there.
                let _mode = self.fetch_u8()?;
                #[allow(clippy::cast_possible_truncation)]
                let f = d as f32;
                self.stack[self.sp] = Self::box_float(f);
                Ok(StepResult::Continue)
            }
            EXTINSTR_FLOAT_TO_INT => {
                let f = f64::from(Self::unbox_float(self.peek(0)?));
                // bytecode.cpp:2018-2058 — consume the trailing rounding-mode
                // operand byte (0=nearest, 1=floor, 2=ceil, 3=trunc), else PC
                // lands on it and traps.
                let mode = self.fetch_u8()?;
                match Self::real_to_int_round(f, mode) {
                    Some(i) => {
                        self.stack[self.sp] = PolyWord::tagged(i);
                        Ok(StepResult::Continue)
                    }
                    None => self.raise_overflow(),
                }
            }

            // ----- Inline "fast call" RTS dispatch for typed FP
            // signatures. These let the SML compiler skip the
            // generic CALL_FAST_RTS<N> path for tight float loops.
            //
            // Stack: [arg(s)..., stub] (stub on top).
            // Pop stub → read word 0 (= our RTS table token) →
            // dispatch via RtsTable like CALL_FAST_RTS<N>, but the
            // signature mapping is fixed by the opcode:
            //   RtoR   : real → real   (Arity1; arg unboxed, result boxed)
            //   GtoR   : general → real
            //   RRtoR  : real,real → real
            //   RGtoR  : real,general → real
            //
            // bytecode.cpp:1423-1450 + similar.
            EXTINSTR_CALL_FAST_R_TO_R => self.call_fast_r_to_r(),
            EXTINSTR_CALL_FAST_G_TO_R => self.call_fast_g_to_r(),
            EXTINSTR_CALL_FAST_RR_TO_R => self.call_fast_rr_to_r(),
            EXTINSTR_CALL_FAST_RG_TO_R => self.call_fast_rg_to_r(),
            // Same shape but for f32 — pack/unpack via box_float.
            EXTINSTR_CALL_FAST_F_TO_F => self.call_fast_f_to_f(),
            EXTINSTR_CALL_FAST_G_TO_F => self.call_fast_g_to_f(),
            EXTINSTR_CALL_FAST_FF_TO_F => self.call_fast_ff_to_f(),
            EXTINSTR_CALL_FAST_FG_TO_F => self.call_fast_fg_to_f(),

            // ----- Real (f64) arithmetic. Each Real lives in a
            // 1-word byte object (8 bytes = sizeof(f64)). These ops
            // read the f64, do the math, write a new boxed Real.
            // bytecode.cpp:1585-1900.
            EXTINSTR_REAL_ABS => self.real_unop(f64::abs),
            EXTINSTR_REAL_NEG => self.real_unop(|v: f64| -v),
            EXTINSTR_REAL_ADD => self.real_binop(|y, x| y + x),
            EXTINSTR_REAL_SUB => self.real_binop(|y, x| y - x),
            EXTINSTR_REAL_MULT => self.real_binop(|y, x| y * x),
            EXTINSTR_REAL_DIV => self.real_binop(|y, x| y / x),
            EXTINSTR_REAL_EQUAL => self.real_cmp(|y, x| {
                #[allow(clippy::float_cmp)]
                {
                    y == x
                }
            }),
            EXTINSTR_REAL_LESS => self.real_cmp(|y, x| y < x),
            EXTINSTR_REAL_LESS_EQ => self.real_cmp(|y, x| y <= x),
            EXTINSTR_REAL_GREATER => self.real_cmp(|y, x| y > x),
            EXTINSTR_REAL_GREATER_EQ => self.real_cmp(|y, x| y >= x),
            EXTINSTR_REAL_UNORDERED => self.real_cmp(|y, x| y.is_nan() || x.is_nan()),
            EXTINSTR_FIXED_INT_TO_REAL => {
                let i = self.peek(0)?;
                #[allow(clippy::cast_precision_loss)]
                let f = i.untag() as f64;
                let p = self.alloc_real(f)?;
                self.stack[self.sp] = p;
                Ok(StepResult::Continue)
            }
            // ASR of tagged short word. bytecode.cpp:2076 (EXTINSTR_wordShiftRArith).
            // Top of stack is the shift amount; below it is the value.
            // We must arithmetic-shift the untagged value, then re-tag.
            EXTINSTR_WORD_SHIFT_R_ARITH => self.bin_op_word(|x, y| {
                let s = (x >> 1) & 63;
                // Untag WITH sign extension: cast to isize FIRST, then `>>` is
                // arithmetic (matches PolyWord::untag). The old `(y >> 1) as isize`
                // did a *logical* usize shift to untag, so the payload's top bit was
                // never sign-extended and `~>>` of a negative behaved like `>>`
                // (e.g. Real.toLargeInt of a negative gave a huge positive).
                let v = (y as isize) >> 1; // sign-extend before shift
                #[allow(clippy::cast_sign_loss)]
                let r = v.wrapping_shr(s as u32) as usize;
                (r << 1) | 1
            }),
            EXTINSTR_REAL_TO_INT => {
                // bytecode.cpp:2014-2058. The opcode is followed by a
                // rounding-mode operand byte (0=nearest, 1=floor, 2=ceil,
                // 3=trunc); it MUST be consumed or PC lands on it and traps.
                let r = self.peek(0)?;
                let f = unsafe { Self::read_real(r) };
                let mode = self.fetch_u8()?;
                match Self::real_to_int_round(f, mode) {
                    Some(i) => {
                        self.stack[self.sp] = PolyWord::tagged(i);
                        Ok(StepResult::Continue)
                    }
                    None => self.raise_overflow(),
                }
            }

            // ----- LargeWord arithmetic (boxed uintptr_t).
            //
            // Each long-word value lives in a 1-word byte object;
            // these ops read the first word, do the math, write
            // a new 1-word byte object as the result.
            // bytecode.cpp:1697-1830
            EXTINSTR_LG_WORD_ADD => self.lg_word_binop(usize::wrapping_add),
            EXTINSTR_LG_WORD_SUB => self.lg_word_binop(usize::wrapping_sub),
            EXTINSTR_LG_WORD_MULT => self.lg_word_binop(usize::wrapping_mul),
            EXTINSTR_LG_WORD_DIV => self.lg_word_binop(|y, x| y.checked_div(x).unwrap_or(0)),
            EXTINSTR_LG_WORD_MOD => self.lg_word_binop(|y, x| y.checked_rem(x).unwrap_or(0)),
            EXTINSTR_LG_WORD_AND => self.lg_word_binop(|y, x| y & x),
            EXTINSTR_LG_WORD_OR => self.lg_word_binop(|y, x| y | x),
            EXTINSTR_LG_WORD_XOR => self.lg_word_binop(|y, x| y ^ x),
            // Shift ops take a TAGGED short word (not boxed) for the shift amount.
            EXTINSTR_LG_WORD_SHIFT_LEFT =>
            {
                #[allow(clippy::cast_possible_truncation)]
                self.lg_word_shift_op(|y, s| y.wrapping_shl(s as u32))
            }
            EXTINSTR_LG_WORD_SHIFT_R_LOG =>
            {
                #[allow(clippy::cast_possible_truncation)]
                self.lg_word_shift_op(|y, s| y.wrapping_shr(s as u32))
            }
            EXTINSTR_LG_WORD_SHIFT_R_ARITH =>
            {
                #[allow(
                    clippy::cast_possible_truncation,
                    clippy::cast_possible_wrap,
                    clippy::cast_sign_loss
                )]
                self.lg_word_shift_op(|y, s| ((y as isize).wrapping_shr(s as u32)) as usize)
            }
            // Comparisons return tagged bool (1=true, 0=false).
            EXTINSTR_LG_WORD_EQUAL => self.lg_word_cmp(|y, x| y == x),
            EXTINSTR_LG_WORD_LESS => self.lg_word_cmp(|y, x| y < x),
            EXTINSTR_LG_WORD_LESS_EQ => self.lg_word_cmp(|y, x| y <= x),
            EXTINSTR_LG_WORD_GREATER => self.lg_word_cmp(|y, x| y > x),
            EXTINSTR_LG_WORD_GREATER_EQ => self.lg_word_cmp(|y, x| y >= x),

            // ----- Wider constant addressing
            //
            // CONST_ADDR32_16: PC-relative constant fetch with 32-bit
            // byte offset + 16-bit constant index.
            //   bytecode.cpp:2349-2356
            EXTINSTR_CONST_ADDR32_16 => {
                let byte_off = self.fetch_u32_le()? as usize;
                let c_num = self.fetch_u16_le()? as usize;
                // SAFETY: trusted compiler-emitted offsets.
                let w = unsafe { self.read_pc_const(byte_off, c_num + 3) };
                self.push_continue(w)
            }

            // ----- Wider jumps / case
            EXTINSTR_JUMP32 => {
                // The 32-bit offset is SIGNED — upstream sign-extends it
                // (bytecode.cpp:2236). `as i32 as isize` sign-extends so a
                // backward long jump stays negative (was zero-extended → ~4GB
                // forward jump on backward jumps in functions >64KB).
                let lo = u32::from(self.fetch_u16_le()?);
                let hi = u32::from(self.fetch_u16_le()?);
                let off = ((hi << 16) | lo) as i32 as isize;
                self.pc_offset_signed(off)?;
                Ok(StepResult::Continue)
            }
            EXTINSTR_JUMP32_FALSE => {
                let lo = u32::from(self.fetch_u16_le()?);
                let hi = u32::from(self.fetch_u16_le()?);
                let off = ((hi << 16) | lo) as i32 as isize; // signed (see JUMP32)
                if self.pop()? == PolyWord::tagged(0) {
                    self.pc_offset_signed(off)?;
                }
                Ok(StepResult::Continue)
            }
            EXTINSTR_JUMP32_TRUE => {
                let lo = u32::from(self.fetch_u16_le()?);
                let hi = u32::from(self.fetch_u16_le()?);
                let off = ((hi << 16) | lo) as i32 as isize; // signed (see JUMP32)
                if self.pop()? != PolyWord::tagged(0) {
                    self.pc_offset_signed(off)?;
                }
                Ok(StepResult::Continue)
            }

            // Extended tail call: 16-bit args, falls through to TAIL_CALL.
            EXTINSTR_TAIL => {
                let tail_count = self.fetch_u16_le()? as usize;
                let skip = self.fetch_u16_le()? as usize;
                self.do_tail_call(tail_count, skip)?;
                Ok(StepResult::Continue)
            }

            // Unknown extension — surface to caller, rolled back to ESCAPE byte.
            _ => {
                self.pc = escape_pc;
                Ok(StepResult::Unimplemented {
                    op: ext,
                    extended: true,
                })
            }
        }
    }

    // ---- Helpers ------------------------------------------------------

    #[inline(always)]
    fn push_continue(&mut self, w: PolyWord) -> Result<StepResult, InterpError> {
        self.push(w)?;
        Ok(StepResult::Continue)
    }

    #[inline(always)]
    fn dup_local(&mut self, depth: usize) -> Result<StepResult, InterpError> {
        let v = self.peek(depth)?;
        self.push_continue(v)
    }

    /// RESET_R_N: pop top, drop n below it, push top back. Net effect
    /// is "remove n stack slots while preserving the top value".
    /// Fast path: read top, bump sp by n (with bounds check), write
    /// top into new sp slot. Saves N pops.
    ///
    /// Bounds: need (n+1) items on stack at entry, i.e.,
    /// `sp + n + 1 <= len()`, i.e., `new_sp < len()`.
    #[inline(always)]
    fn reset(&mut self, n: usize) -> Result<StepResult, InterpError> {
        let Some(new_sp) = self.sp.checked_add(n) else {
            return Err(InterpError::StackUnderflow);
        };
        if new_sp >= self.stack.len() {
            return Err(InterpError::StackUnderflow);
        }
        // SAFETY: sp <= new_sp < len(), so sp < len() too — both
        // indices are valid.
        unsafe {
            let top = *self.stack.get_unchecked(self.sp);
            *self.stack.get_unchecked_mut(new_sp) = top;
        }
        self.sp = new_sp;
        Ok(StepResult::Continue)
    }

    /// Drop the top `n` items without preserving anything. The
    /// non-preserving variant of [`reset`](Self::reset).
    /// Drop the top `n` items in one go: just bump sp by n (with
    /// bounds check). The dropped PolyWord slots are left in the
    /// stack as garbage — they'll get overwritten by the next push.
    /// Hot path: RESET_1 is 3% of total dispatches.
    #[inline(always)]
    fn drop_n(&mut self, n: usize) -> Result<StepResult, InterpError> {
        let Some(new_sp) = self.sp.checked_add(n) else {
            return Err(InterpError::StackUnderflow);
        };
        if new_sp > self.stack.len() {
            return Err(InterpError::StackUnderflow);
        }
        self.sp = new_sp;
        Ok(StepResult::Continue)
    }

    /// Legacy INSTR_ATOMIC_INCR / INSTR_ATOMIC_DECR.
    ///
    /// Both read the cell at top of stack, add or subtract `2` (= the
    /// raw representation of tagged `1` with the tag bit cleared)
    /// from word 0, write back, and replace top with the new value.
    /// (bytecode.cpp:803-823.)
    fn atomic_incr_decr(&mut self, incr: bool) -> Result<StepResult, InterpError> {
        let cell = self.peek(0)?;
        if !cell.is_data_ptr() {
            return Err(InterpError::NotAClosure(cell));
        }
        let p = cell.as_ptr::<PolyWord>().cast_mut();
        // SAFETY: cell is a heap-allocated mutable ref cell.
        let new_word = unsafe {
            let cur = (*p).0;
            let new = if incr {
                cur.wrapping_add(2)
            } else {
                cur.wrapping_sub(2)
            };
            let nw = PolyWord::from_bits(new);
            p.write(nw);
            nw
        };
        // Replace top with the new value.
        self.pop()?;
        self.push_continue(new_word)
    }

    fn indirect(&mut self, n: usize) -> Result<StepResult, InterpError> {
        let obj_word = self.pop()?;
        let p = obj_word.as_ptr::<PolyWord>();
        // SAFETY: caller (compiled code) is trusted to emit valid offsets.
        let field = unsafe { *p.add(n) };
        self.push_continue(field)
    }

    // ---- Allocation ---------------------------------------------------

    /// Bump-allocate `n_words` words plus a length word, setting the
    /// length word's flag byte to `flags`. Returns a `*mut` pointer
    /// to the body's first slot.
    fn allocate(&mut self, n_words: usize, flags: u8) -> Result<*mut PolyWord, InterpError> {
        use crate::space;
        let space = self.alloc_space.as_mut().ok_or(InterpError::NoAllocator)?;
        let p = space.alloc(n_words);
        // SAFETY: alloc just returned the matching length-word slot
        unsafe {
            space::set_length_word(p, n_words, flags);
        }
        Ok(p)
    }

    /// `tuple_N`: alloc N-word ordinary object, fill with N popped
    /// values (slot 0 = first popped's neighbour, see bytecode.cpp:2283).
    fn do_tuple(&mut self, n: usize) -> Result<StepResult, InterpError> {
        let p = self.allocate(n, 0)?; // 0 = ordinary word object
        // Upstream: `for (; storeWords > 0; ) p->Set(--storeWords, *sp++)`.
        // That writes slot[n-1] first (popping the top), then slot[n-2], etc.
        for i in (0..n).rev() {
            let v = self.pop()?;
            // SAFETY: i < n_words by construction.
            unsafe { p.add(i).write(v) };
        }
        self.push_continue(PolyWord::from_ptr(p.cast_const()))
    }

    /// `closure_b`: build an immutable closure with N captures.
    /// Stack on entry (top down): source-closure (for code addr),
    /// capture[N-1], ..., capture[0]. Result replaces all of these.
    fn do_create_closure(&mut self, n_captures: usize) -> Result<StepResult, InterpError> {
        use crate::length_word::F_CLOSURE_OBJ;

        let length = n_captures + 1; // +1 for code addr at slot 0
        let p = self.allocate(length, F_CLOSURE_OBJ)?;

        // Upstream: `for (; storeWords > 0; ) t->Set(--storeWords + 1, *sp++)`.
        // So with N captures, slots [length-1, length-2, ..., 1] are
        // filled in that order, popping each from the top.
        for i in (1..length).rev() {
            let v = self.pop()?;
            // SAFETY: i < length
            unsafe { p.add(i).write(v) };
        }
        // Now the source closure is on top. Copy its first word
        // (code address) to slot 0 of the new closure.
        let src_word = self.peek(0)?;
        let src_ptr = src_word.as_ptr::<PolyWord>();
        // SAFETY: src is a valid closure
        let code_addr = unsafe { *src_ptr };
        // SAFETY: slot 0 is in bounds
        unsafe { p.add(0).write(code_addr) };
        // Replace top of stack with new closure.
        self.pop()?;
        self.push_continue(PolyWord::from_ptr(p.cast_const()))
    }

    /// `alloc_mut_closure_b N`: allocate a mutable closure with N
    /// capture slots (initialised to TAGGED(0)). Source closure on top
    /// provides the code address. Result REPLACES the source on top.
    fn do_alloc_mut_closure(&mut self, n_captures: usize) -> Result<StepResult, InterpError> {
        use crate::length_word::{F_CLOSURE_OBJ, F_MUTABLE_BIT};

        let length = n_captures + 1;
        let p = self.allocate(length, F_CLOSURE_OBJ | F_MUTABLE_BIT)?;
        // Source closure is on top: copy its first word (code addr).
        let src_word = self.peek(0)?;
        let src_ptr = src_word.as_ptr::<PolyWord>();
        // SAFETY: src closure invariant
        let code_addr = unsafe { *src_ptr };
        // SAFETY: indices < length
        unsafe {
            p.add(0).write(code_addr);
            for i in 1..length {
                p.add(i).write(PolyWord::tagged(0));
            }
        }
        // Replace top with new closure pointer.
        self.pop()?;
        self.push_continue(PolyWord::from_ptr(p.cast_const()))
    }

    /// `move_to_mut_closure_b N`: pop value `u`, write to slot (N+1)
    /// of the closure that's now on top. Leaves the closure on top
    /// (NOT popped).
    fn do_move_to_mut_closure(&mut self, slot: usize) -> Result<StepResult, InterpError> {
        let u = self.pop()?;
        let target = self.peek(0)?;
        let p = target.as_ptr::<PolyWord>();
        // We need mutable access despite holding a *const. Cast is
        // safe because the closure was allocated mutable.
        let p_mut = p.cast_mut();
        // SAFETY: caller emitted a valid slot index for a closure
        // with at least slot+2 words.
        unsafe { p_mut.add(slot + 1).write(u) };
        Ok(StepResult::Continue)
    }

    /// `alloc_ref`: allocate a 1-word mutable cell initialised to the
    /// value currently on top. REPLACES top with cell pointer (the
    /// initialiser doesn't get popped, just replaced).
    fn do_alloc_ref(&mut self) -> Result<StepResult, InterpError> {
        use crate::length_word::F_MUTABLE_BIT;

        let init = self.peek(0)?;
        let p = self.allocate(1, F_MUTABLE_BIT)?;
        // SAFETY: 1 word allocated
        unsafe { p.add(0).write(init) };
        self.pop()?;
        self.push_continue(PolyWord::from_ptr(p.cast_const()))
    }

    /// Clear the mutable bit on the length word of the object at top
    /// of stack. INSTR_LOCK leaves the object on top; INSTR_CLEAR_MUTABLE
    /// replaces it with TAGGED(0).
    fn clear_mutable_bit(&mut self, replace_with_zero: bool) -> Result<StepResult, InterpError> {
        use crate::length_word::{self, F_MUTABLE_BIT};

        let v = self.peek(0)?;
        let p = v.as_ptr::<PolyWord>().cast_mut();
        // SAFETY: caller upholds top is a mutable heap object.
        unsafe {
            let lw_ptr = p.sub(1);
            let lw = *lw_ptr;
            let new_bits = lw.0 & !((F_MUTABLE_BIT as usize) << length_word::FLAGS_SHIFT);
            lw_ptr.write(PolyWord::from_bits(new_bits));
        }
        if replace_with_zero {
            self.pop()?;
            self.push_continue(PolyWord::tagged(0))
        } else {
            Ok(StepResult::Continue)
        }
    }

    /// `indirect_closure_b{0,1,2}` with depth in pc[0]: read sp[depth]
    /// as a closure pointer, push slot `1 + slot_offset` of that closure.
    fn do_indirect_closure(&mut self, slot_offset: usize) -> Result<StepResult, InterpError> {
        let depth = self.fetch_u8()? as usize;
        let closure_word = self.peek(depth)?;
        let p = closure_word.as_ptr::<PolyWord>();
        // SAFETY: closure has at least slot_offset+2 words.
        let val = unsafe { *p.add(1 + slot_offset) };
        self.push_continue(val)
    }

    fn bin_op_tagged<F>(&mut self, f: F) -> Result<StepResult, InterpError>
    where
        F: FnOnce(isize, isize) -> Result<isize, ()>,
    {
        let x = self.pop()?;
        let y = self.pop()?;
        let r = f(x.untag(), y.untag()).map_err(|()| InterpError::DivByZero)?;
        self.push_continue(PolyWord::tagged(r))
    }

    /// `INSTR_FIXED_ADD`: tagged(x+y) or raise Overflow if out of range.
    /// bytecode.cpp:926-939.
    fn fixed_add(&mut self) -> Result<StepResult, InterpError> {
        let x = self.pop()?;
        let y = self.pop()?;
        let t = (x.untag() as i128) + (y.untag() as i128);
        if t >= crate::poly_word::MIN_TAGGED as i128 && t <= crate::poly_word::MAX_TAGGED as i128 {
            self.push_continue(PolyWord::tagged(t as isize))
        } else {
            self.raise_overflow()
        }
    }

    /// `INSTR_FIXED_SUB`: tagged(y-x) or raise Overflow. bytecode.cpp:941-954.
    fn fixed_sub(&mut self) -> Result<StepResult, InterpError> {
        let x = self.pop()?;
        let y = self.pop()?;
        let t = (y.untag() as i128) - (x.untag() as i128);
        if t >= crate::poly_word::MIN_TAGGED as i128 && t <= crate::poly_word::MAX_TAGGED as i128 {
            self.push_continue(PolyWord::tagged(t as isize))
        } else {
            self.raise_overflow()
        }
    }

    /// `INSTR_FIXED_MULT`: tagged(x*y) or raise Overflow. Upstream has no
    /// portable signed-overflow test (mult_longc + IsDataPtr check); we test in
    /// i128 — same condition ARB_MULTIPLY uses to box, but RAISE here because
    /// Int = FixedInt is non-boxing. bytecode.cpp:956-981.
    fn fixed_mult(&mut self) -> Result<StepResult, InterpError> {
        let x = self.pop()?;
        let y = self.pop()?;
        let t = (x.untag() as i128) * (y.untag() as i128);
        if t >= crate::poly_word::MIN_TAGGED as i128 && t <= crate::poly_word::MAX_TAGGED as i128 {
            self.push_continue(PolyWord::tagged(t as isize))
        } else {
            self.raise_overflow()
        }
    }

    /// On 64-bit, Float (f32) values are *tagged* — packed into the
    /// high 32 bits of a PolyWord with the low bit set. Helpers:
    fn unbox_float(w: PolyWord) -> f32 {
        // Right-shift moves the float bits to the low 32, sign-extended.
        // The reinterpret as f32 is then a no-op cast.
        #[allow(clippy::cast_possible_truncation)]
        let i = ((w.0 as isize) >> 32) as i32;
        f32::from_bits(i as u32)
    }
    fn box_float(f: f32) -> PolyWord {
        let bits = u64::from(f.to_bits());
        // Pack into high 32 bits, set tag bit.
        let raw = (bits << 32) | 1;
        #[allow(clippy::cast_possible_truncation)]
        PolyWord::from_bits(raw as usize)
    }

    fn float_unop<F: FnOnce(f32) -> f32>(&mut self, op: F) -> Result<StepResult, InterpError> {
        let v = Self::unbox_float(self.peek(0)?);
        self.stack[self.sp] = Self::box_float(op(v));
        Ok(StepResult::Continue)
    }
    fn float_binop<F: FnOnce(f32, f32) -> f32>(
        &mut self,
        op: F,
    ) -> Result<StepResult, InterpError> {
        let x = Self::unbox_float(self.pop()?);
        let y = Self::unbox_float(self.peek(0)?);
        self.stack[self.sp] = Self::box_float(op(y, x));
        Ok(StepResult::Continue)
    }
    fn float_cmp<F: FnOnce(f32, f32) -> bool>(&mut self, op: F) -> Result<StepResult, InterpError> {
        let x = Self::unbox_float(self.pop()?);
        let y = Self::unbox_float(self.peek(0)?);
        self.stack[self.sp] = PolyWord::tagged(isize::from(op(y, x)));
        Ok(StepResult::Continue)
    }

    /// Inline fast-call: real → real. Pop stub, pop arg (boxed Real),
    /// look up the RTS function via the stub's token, dispatch with
    /// the arg, allocate a boxed-Real result.
    fn call_fast_r_to_r(&mut self) -> Result<StepResult, InterpError> {
        let stub = self.pop()?;
        let arg = self.pop()?;
        let result = self.dispatch_typed_fast_call(stub, &[arg]);
        let p = self.alloc_real(result)?;
        self.push_continue(p)
    }
    fn call_fast_g_to_r(&mut self) -> Result<StepResult, InterpError> {
        // The general-arg ABI is identical to the real-arg ABI here:
        // `dispatch_typed_fast_call` ignores the arg-kind distinction.
        // Delegate so there's a single audited body (preserve the name
        // for a future faithful-port fix that needs the ABIs to diverge).
        self.call_fast_r_to_r()
    }
    fn call_fast_rr_to_r(&mut self) -> Result<StepResult, InterpError> {
        let stub = self.pop()?;
        let arg2 = self.pop()?;
        let arg1 = self.pop()?;
        let result = self.dispatch_typed_fast_call(stub, &[arg1, arg2]);
        let p = self.alloc_real(result)?;
        self.push_continue(p)
    }
    fn call_fast_rg_to_r(&mut self) -> Result<StepResult, InterpError> {
        // General-arg == real-arg ABI here (see call_fast_g_to_r).
        self.call_fast_rr_to_r()
    }
    fn call_fast_f_to_f(&mut self) -> Result<StepResult, InterpError> {
        let stub = self.pop()?;
        let arg = self.pop()?;
        let result = self.dispatch_typed_fast_call(stub, &[arg]);
        #[allow(clippy::cast_possible_truncation)]
        let f = result as f32;
        self.push_continue(Self::box_float(f))
    }
    fn call_fast_g_to_f(&mut self) -> Result<StepResult, InterpError> {
        // General-arg == real-arg ABI here (see call_fast_g_to_r).
        self.call_fast_f_to_f()
    }
    fn call_fast_ff_to_f(&mut self) -> Result<StepResult, InterpError> {
        let stub = self.pop()?;
        let arg2 = self.pop()?;
        let arg1 = self.pop()?;
        let result = self.dispatch_typed_fast_call(stub, &[arg1, arg2]);
        #[allow(clippy::cast_possible_truncation)]
        let f = result as f32;
        self.push_continue(Self::box_float(f))
    }
    fn call_fast_fg_to_f(&mut self) -> Result<StepResult, InterpError> {
        // General-arg == real-arg ABI here (see call_fast_g_to_r).
        self.call_fast_ff_to_f()
    }

    /// Dispatch a typed-FP-style fast call. The stub's word 0 is
    /// our RTS table token; we look up and invoke with the given
    /// args. Returns the result as f64 (caller boxes).
    ///
    /// For our stub Real RTS impls (which return TAGGED(0)), the
    /// "f64 result" is 0.0 — which lets compilation pass even
    /// though runtime values are garbage. Real impl can replace.
    fn dispatch_typed_fast_call(&mut self, stub: PolyWord, args: &[PolyWord]) -> f64 {
        if !stub.is_data_ptr() {
            return 0.0;
        }
        let p = stub.as_ptr::<PolyWord>();
        // SAFETY: stub is an entry-point object; word 0 is the token.
        let token = unsafe { (*p).0 };
        let Some(entry) = self.rts.entry(token) else {
            return 0.0;
        };
        let entry_func = entry.func;
        let rts_ref = self.rts.clone();
        let mut ctx = crate::rts::RtsContext {
            alloc_space: self.alloc_space.as_mut(),
            raised_exception: None,
            rts: Some(&rts_ref),
        };
        let result_word = match (args.len(), entry_func) {
            (1, crate::rts::RtsFn::Arity1(f)) => f(&mut ctx, args[0]),
            (2, crate::rts::RtsFn::Arity2(f)) => f(&mut ctx, args[0], args[1]),
            _ => PolyWord::tagged(0),
        };
        if result_word.is_data_ptr() {
            // SAFETY: result is a boxed-Real object.
            unsafe { *result_word.as_ptr::<f64>() }
        } else {
            0.0
        }
    }

    /// Real binop helper: pop x (boxed Real), peek y (boxed Real),
    /// compute `op(y, x)`, replace top with a freshly-allocated
    /// boxed Real holding the result.
    fn real_binop<F: FnOnce(f64, f64) -> f64>(&mut self, op: F) -> Result<StepResult, InterpError> {
        let x = self.pop()?;
        let y = self.peek(0)?;
        // SAFETY: caller (compiler) emits valid boxed reals.
        let fx = unsafe { Self::read_real(x) };
        let fy = unsafe { Self::read_real(y) };
        let result = op(fy, fx);
        let p = self.alloc_real(result)?;
        self.stack[self.sp] = p;
        Ok(StepResult::Continue)
    }

    fn real_unop<F: FnOnce(f64) -> f64>(&mut self, op: F) -> Result<StepResult, InterpError> {
        let r = self.peek(0)?;
        let f = unsafe { Self::read_real(r) };
        let p = self.alloc_real(op(f))?;
        self.stack[self.sp] = p;
        Ok(StepResult::Continue)
    }

    fn real_cmp<F: FnOnce(f64, f64) -> bool>(&mut self, op: F) -> Result<StepResult, InterpError> {
        let x = self.pop()?;
        let y = self.peek(0)?;
        let fx = unsafe { Self::read_real(x) };
        let fy = unsafe { Self::read_real(y) };
        self.stack[self.sp] = PolyWord::tagged(isize::from(op(fy, fx)));
        Ok(StepResult::Continue)
    }

    /// Read an f64 from a boxed Real (1-word byte object).
    ///
    /// # Safety
    /// `w` must be a valid boxed-Real pointer.
    unsafe fn read_real(w: PolyWord) -> f64 {
        if !w.is_data_ptr() {
            return 0.0;
        }
        // SAFETY: 1 word = 8 bytes = sizeof(f64); object body is
        // word-aligned per Poly invariants.
        unsafe { *w.as_ptr::<f64>() }
    }

    /// Round an f64 to an integer per PolyML's rounding-mode byte
    /// (`bytecode.cpp:2034-2049`, `reals.h:31-34`): 0=nearest, 1=floor(down),
    /// 2=ceil(up), 3/default=trunc(toward zero). Mode 0 uses Rust `round()`
    /// (half away from zero) to match upstream's C `round()`, not banker's
    /// rounding. Truncation is the C default for any unexpected mode value.
    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    fn real_to_int_round(f: f64, mode: u8) -> Option<isize> {
        // bytecode.cpp:2024-2032 — reject inputs that would overflow the
        // conversion BEFORE rounding (so rounding can't push an in-range value
        // out). Limit = MAXTAGGED + MAXTAGGED/2.
        let limit =
            (crate::poly_word::MAX_TAGGED as f64) + (crate::poly_word::MAX_TAGGED as f64) / 2.0;
        if !f.is_finite() || f > limit || f < -limit {
            return None;
        }
        let r = match mode {
            // Mode 0 = TO_NEAREST (Real.round / Real.toInt IEEEReal.TO_NEAREST /
            // Real32.round): IEEE round-half-to-EVEN, NOT Rust's f.round() which
            // is half-away-from-zero (2.5->2 not 3, 0.5->0 not 1, ~0.5->0 not ~1).
            // Differential-tested against upstream PolyML. bytecode.cpp uses the
            // FE_TONEAREST default = banker's rounding.
            0 => f.round_ties_even(),
            1 => f.floor(),
            2 => f.ceil(),
            _ => f.trunc(),
        };
        // bytecode.cpp:2051-2056 — check the rounded result is taggable.
        let p = r as isize;
        if p > crate::poly_word::MAX_TAGGED || p < crate::poly_word::MIN_TAGGED {
            return None;
        }
        Some(p)
    }

    fn alloc_real(&mut self, v: f64) -> Result<PolyWord, InterpError> {
        let space = self.alloc_space.as_mut().ok_or(InterpError::NoAllocator)?;
        let p = space.alloc(1);
        // SAFETY: just allocated 1 word (= 8 bytes), enough for f64.
        unsafe {
            crate::space::set_length_word(p, 1, crate::length_word::F_BYTE_OBJ);
            p.cast::<f64>().write(v);
        }
        Ok(PolyWord::from_ptr(p.cast_const()))
    }

    /// LargeWord binop helper: pop x (boxed LargeWord), peek y
    /// (boxed LargeWord), compute `op(y, x)`, replace top with
    /// a freshly-allocated 1-word LargeWord holding the result.
    fn lg_word_binop<F>(&mut self, op: F) -> Result<StepResult, InterpError>
    where
        F: FnOnce(usize, usize) -> usize,
    {
        let x = self.pop()?;
        let y = self.peek(0)?;
        let wx = unsafe { Self::read_lg_word(x) };
        let wy = unsafe { Self::read_lg_word(y) };
        let result_word = op(wy, wx);
        let p = self.alloc_lg_word(result_word)?;
        self.stack[self.sp] = p;
        Ok(StepResult::Continue)
    }

    /// LargeWord shift helper: pop x (TAGGED shift amount), peek y
    /// (boxed LargeWord), compute `op(y, x)`, replace top.
    fn lg_word_shift_op<F>(&mut self, op: F) -> Result<StepResult, InterpError>
    where
        F: FnOnce(usize, usize) -> usize,
    {
        let x = self.pop()?;
        let y = self.peek(0)?;
        #[allow(clippy::cast_sign_loss)]
        let shift = x.untag() as usize;
        let wy = unsafe { Self::read_lg_word(y) };
        let result_word = op(wy, shift);
        let p = self.alloc_lg_word(result_word)?;
        self.stack[self.sp] = p;
        Ok(StepResult::Continue)
    }

    /// LargeWord comparison: pop x, peek y, push tagged bool.
    fn lg_word_cmp<F>(&mut self, op: F) -> Result<StepResult, InterpError>
    where
        F: FnOnce(usize, usize) -> bool,
    {
        let x = self.pop()?;
        let y = self.peek(0)?;
        let wx = unsafe { Self::read_lg_word(x) };
        let wy = unsafe { Self::read_lg_word(y) };
        self.stack[self.sp] = PolyWord::tagged(isize::from(op(wy, wx)));
        Ok(StepResult::Continue)
    }

    /// Read the first word of a boxed LargeWord object.
    ///
    /// # Safety
    /// `w` must be a valid boxed-LargeWord pointer (1+ word byte object).
    unsafe fn read_lg_word(w: PolyWord) -> usize {
        if !w.is_data_ptr() {
            if arbint_trace_on() {
                eprintln!(
                    "  read_lg_word on NON-PTR operand: 0x{:016x} (tagged={})",
                    w.0,
                    w.is_tagged()
                );
                std::process::abort();
            }
            return 0;
        }
        unsafe { (*w.as_ptr::<PolyWord>()).0 }
    }

    fn alloc_lg_word(&mut self, word: usize) -> Result<PolyWord, InterpError> {
        let space = self.alloc_space.as_mut().ok_or(InterpError::NoAllocator)?;
        let p = space.alloc(1);
        // SAFETY: just allocated 1 word.
        unsafe {
            crate::space::set_length_word(p, 1, crate::length_word::F_BYTE_OBJ);
            p.write(PolyWord::from_bits(word));
        }
        Ok(PolyWord::from_ptr(p.cast_const()))
    }

    /// `ARB_ADD`: pop `x`, peek `y`, replace top with `y + x`.
    fn arb_add_pair(&mut self) -> Result<StepResult, InterpError> {
        let x = self.pop()?;
        let y = self.peek(0)?;
        if x.is_tagged() && y.is_tagged() {
            let t = (x.untag() as i128) + (y.untag() as i128);
            if t >= crate::poly_word::MIN_TAGGED as i128
                && t <= crate::poly_word::MAX_TAGGED as i128
            {
                self.stack[self.sp] = PolyWord::tagged(t as isize);
                return Ok(StepResult::Continue);
            }
        }
        let result = crate::rts::arb_add_via_bigint(self.alloc_space.as_mut(), x, y);
        self.stack[self.sp] = result;
        Ok(StepResult::Continue)
    }

    /// `ARB_SUBTRACT`: pop `x`, peek `y`, replace top with `y - x`.
    fn arb_sub_pair(&mut self) -> Result<StepResult, InterpError> {
        let x = self.pop()?;
        let y = self.peek(0)?;
        if x.is_tagged() && y.is_tagged() {
            let t = (y.untag() as i128) - (x.untag() as i128);
            if t >= crate::poly_word::MIN_TAGGED as i128
                && t <= crate::poly_word::MAX_TAGGED as i128
            {
                self.stack[self.sp] = PolyWord::tagged(t as isize);
                return Ok(StepResult::Continue);
            }
        }
        let result = crate::rts::arb_sub_via_bigint(self.alloc_space.as_mut(), x, y);
        self.stack[self.sp] = result;
        Ok(StepResult::Continue)
    }

    /// `ARB_MULTIPLY`: pop `x`, peek `y`, replace top with `y * x`.
    fn arb_mult_pair(&mut self) -> Result<StepResult, InterpError> {
        let x = self.pop()?;
        let y = self.peek(0)?;
        if x.is_tagged() && y.is_tagged() {
            let t = (y.untag() as i128) * (x.untag() as i128);
            if t >= crate::poly_word::MIN_TAGGED as i128
                && t <= crate::poly_word::MAX_TAGGED as i128
            {
                self.stack[self.sp] = PolyWord::tagged(t as isize);
                return Ok(StepResult::Continue);
            }
        }
        // Overflow or boxed args: defer to the bignum-aware RTS impl.
        // Critical for SML loops like LibrarySupport.maxShort that
        // use IS_TAGGED on the result to detect overflow.
        let result = crate::rts::arb_mult_via_bigint(self.alloc_space.as_mut(), x, y);
        self.stack[self.sp] = result;
        Ok(StepResult::Continue)
    }

    fn bin_op_word<F>(&mut self, f: F) -> Result<StepResult, InterpError>
    where
        F: FnOnce(usize, usize) -> usize,
    {
        let x = self.pop()?;
        let y = self.pop()?;
        self.push_continue(PolyWord::from_bits(f(x.0, y.0)))
    }

    fn bin_op_word_checked<F>(&mut self, f: F) -> Result<StepResult, InterpError>
    where
        F: FnOnce(usize, usize) -> Result<usize, ()>,
    {
        let x = self.pop()?;
        let y = self.pop()?;
        let r = f(x.0, y.0).map_err(|()| InterpError::DivByZero)?;
        self.push_continue(PolyWord::from_bits(r))
    }

    fn bin_op_cmp<F>(&mut self, f: F) -> Result<StepResult, InterpError>
    where
        F: FnOnce(usize, usize) -> bool,
    {
        let x = self.pop()?;
        let y = self.pop()?;
        self.push_continue(if f(x.0, y.0) {
            PolyWord::tagged(1)
        } else {
            PolyWord::tagged(0)
        })
    }

    // ---- Call / Return -----------------------------------------------

    /// Allocate a placeholder thread object — 8 zeroed mutable words.
    /// Real PolyML returns `taskData->threadObject`, which has known
    /// fields the bootstrap reads via INDIRECT_*. The 8-word stub
    /// gives those reads a defined (zero) value rather than crashing.
    pub(crate) fn alloc_stub_thread_object(&mut self) -> Result<PolyWord, InterpError> {
        use crate::length_word::F_MUTABLE_BIT;
        // Return the cached singleton if it exists: Thread.self() must yield a
        // STABLE object so thread identity holds and Thread.setLocal/getLocal
        // (which store into this object's slots) round-trip. Without this,
        // Thread_Data — and Isabelle's generic context (Context.put/the_generic_context)
        // — silently lose all data.
        if let Some(t) = self.thread_object {
            return Ok(t);
        }
        let length = 8;
        let p = self.allocate(length, F_MUTABLE_BIT)?;
        // SAFETY: just allocated `length` words
        unsafe {
            for i in 0..length {
                p.add(i).write(PolyWord::tagged(0));
            }
        }
        let t = PolyWord::from_ptr(p.cast_const());
        self.thread_object = Some(t);
        Ok(t)
    }

    /// Dispatch a `CALL_FAST_RTS<N>` opcode through the RTS table.
    /// Stack layout (top down): stub object, arg0, arg1, ..., arg_{n-1}
    /// — matches `bytecode.cpp:681-712`. We pop the stub, read its
    /// word 0 (the dispatch token), look up the function, pop N args,
    /// and push the result.
    fn rts_call(&mut self, n_args: usize) -> Result<StepResult, InterpError> {
        let stub = self.pop()?;
        let p = stub.as_ptr::<PolyWord>();
        // SAFETY: caller (bytecode) guarantees `stub` is a valid
        // EntryPoint object with word 0 holding the dispatch token.
        let token = unsafe { (*p).0 };
        let entry_opt = self.rts.entry(token).cloned();
        let (entry_name, entry_func) = match entry_opt {
            Some(e) => (e.name, e.func),
            None => {
                // Pop the args off the stack before raising so the
                // exception handler doesn't see them. Then build a
                // fresh exception packet via the alloc space and
                // unwind to the registered handler. The SML side
                // catches with `handle _ => false` patterns.
                for _ in 0..n_args {
                    self.pop()?;
                }
                let name_bytes = unsafe {
                    let total_words =
                        crate::length_word::length_of(crate::space::MemorySpace::length_word_of(p));
                    let name_ptr = p.add(1).cast::<u8>();
                    let max = total_words.saturating_sub(1) * std::mem::size_of::<usize>();
                    let mut end = 0;
                    while end < max && *name_ptr.add(end) != 0 {
                        end += 1;
                    }
                    std::slice::from_raw_parts(name_ptr, end).to_vec()
                };
                let pretty = String::from_utf8_lossy(&name_bytes);
                let mut ctx = crate::rts::RtsContext {
                    alloc_space: self.alloc_space.as_mut(),
                    raised_exception: None,
                    rts: None,
                };
                let pkt = crate::rts::make_simple_exception_pub(
                    &mut ctx,
                    &format!("RTS entry point not implemented: {pretty}"),
                );
                self.push(pkt)?;
                self.do_raise_ex()?;
                return Ok(StepResult::Continue);
            }
        };
        // Pop args (we already popped the stub).
        //
        // SML's rtsCallFullN emits `mkCall(f, [threadId, arg1..argN],
        // ...)` (see INITIALISE_.ML:419). The call convention pushes
        // args left-to-right, so threadId ends up DEEPEST and the last
        // SML arg ends up TOP. CALL_FAST_RTS<N> pops top-first.
        //
        // To match the C signature `Func(threadId, code, strm, arg)`
        // which expects threadId as args[0], we pop in REVERSE order
        // into the args array — first pop goes to args[N-1].
        let mut args: [PolyWord; 5] = [PolyWord::ZERO; 5];
        for i in (0..n_args).rev() {
            args[i] = self.pop()?;
        }
        // Dispatch by arity, checking it matches the opcode's expectation.
        let fn_arity = entry_func.arity();
        if fn_arity != n_args {
            return Err(InterpError::RtsArityMismatch {
                name: entry_name,
                op_arity: n_args,
                fn_arity,
            });
        }
        crate::rts::trace_call(entry_name, n_args);
        let rts_ref = self.rts.clone(); // Arc clone, cheap
        let mut ctx = RtsContext {
            alloc_space: self.alloc_space.as_mut(),
            raised_exception: None,
            rts: Some(&rts_ref),
        };
        let result = match entry_func {
            RtsFn::Arity0(f) => f(&mut ctx),
            RtsFn::Arity1(f) => f(&mut ctx, args[0]),
            RtsFn::Arity2(f) => f(&mut ctx, args[0], args[1]),
            RtsFn::Arity3(f) => f(&mut ctx, args[0], args[1], args[2]),
            RtsFn::Arity4(f) => f(&mut ctx, args[0], args[1], args[2], args[3]),
            RtsFn::Arity5(f) => f(&mut ctx, args[0], args[1], args[2], args[3], args[4]),
        };
        // If the RTS function asked to raise an exception, push the
        // packet onto the stack and unwind to the registered handler.
        // Matches upstream's CALL_FAST_RTS<N> dispatch:
        //   if (GetExceptionPacket().IsDataPtr()) goto RAISE_EXCEPTION;
        if let Some(packet) = ctx.raised_exception {
            self.push(packet)?;
            self.do_raise_ex()?;
            return Ok(StepResult::Continue);
        }
        if let Some(fn_closure) = crate::rts::take_bootstrap_tail_call() {
            self.push(PolyWord::tagged(0))?;
            self.do_call(fn_closure)?;
            return Ok(StepResult::Continue);
        }
        self.push_continue(result)
    }

    /// Common RAISE_EX path, also reachable from an RTS-raised
    /// exception. Pre-condition: the exception packet is on top of
    /// the stack.
    fn do_raise_ex(&mut self) -> Result<(), InterpError> {
        let exn = self.peek(0)?;
        self.exception_packet = Some(exn);
        if self.handler_sp >= self.stack.len() {
            return Err(InterpError::UnhandledException);
        }
        self.sp = self.handler_sp;
        let handler_pc_word = self.stack[self.sp];
        self.sp += 1;
        let saved_old_handler = self.stack[self.sp];
        self.sp += 1;
        self.handler_sp = saved_old_handler.0;
        self.pc = handler_pc_word.0 as *const u8;
        let (target_depth, h_start, h_end) =
            self.handler_frames_depth
                .pop()
                .unwrap_or((0, std::ptr::null(), std::ptr::null()));
        self.frames.truncate(target_depth);
        self.code_start = h_start;
        self.code_end = h_end;
        Ok(())
    }

    /// Build and raise the pervasive `Overflow` exception so a surrounding
    /// `handle Overflow` catches it. Shared by the FIXED_ADD/SUB/MULT and
    /// REAL_TO_INT/FLOAT_TO_INT overflow guards. Mirrors upstream's
    /// `SetException(overflowPacket); goto RAISE_EXCEPTION;`
    /// (bytecode.cpp:935-936): build the packet (ex_id == TAGGED(5),
    /// EXC_overflow), push it on TOP (the pre-condition `do_raise_ex`
    /// requires), then unwind. `do_raise_ex` returns
    /// `Err(InterpError::UnhandledException)` if no handler is installed.
    fn raise_overflow(&mut self) -> Result<StepResult, InterpError> {
        let packet = {
            let mut ctx = crate::rts::RtsContext {
                alloc_space: self.alloc_space.as_mut(),
                raised_exception: None,
                rts: None,
            };
            crate::rts::make_overflow_exception(&mut ctx)
        };
        self.push(packet)?;
        self.do_raise_ex()?;
        Ok(StepResult::Continue)
    }

    /// Implement TAIL_B_B (and its extended sibling EXTINSTR_tail).
    /// Mirrors `bytecode.cpp:387-424`. The non-mixed-code path falls
    /// through to `CALL_CLOSURE`, which re-pushes retPC + closure
    /// after popping them — the net effect is that the new callee
    /// sees the standard `[closure, retPC, args, ...]` frame layout
    /// just like a normal CALL.
    fn do_tail_call(&mut self, tail_count: usize, skip: usize) -> Result<(), InterpError> {
        use crate::length_word;

        if tail_count < 2 {
            return Err(InterpError::StackUnderflow);
        }

        // Shift `tail_count` items from [sp, sp+tail_count) to
        // [sp+skip, sp+skip+tail_count). This overwrites the current
        // function's locals + frame slots with the new call frame's
        // contents.
        let original_sp = self.sp;
        let mut tail_ptr = original_sp + tail_count;
        let mut new_sp = tail_ptr + skip;
        if new_sp > self.stack.len() {
            return Err(InterpError::StackUnderflow);
        }
        for _ in 0..tail_count {
            new_sp -= 1;
            tail_ptr -= 1;
            self.stack[new_sp] = self.stack[tail_ptr];
        }
        self.sp = new_sp; // = original_sp + skip

        // Pop the PC slot (originally a placeholder pushed by the
        // caller's tail-call sequence) and the closure to call.
        let ret_pc_slot = self.pop()?;
        let closure = self.pop()?;
        if !closure.is_data_ptr() {
            eprintln!(
                "  TAIL_CALL bad closure: {closure:?} | frames depth={} | sp_depth={} | new_sp={new_sp}",
                self.frames.len(),
                self.stack_height(),
            );
            // Stack window
            let n = std::cmp::min(40, self.stack_height());
            for d in 0..n {
                let w = self.stack[self.sp + d];
                eprintln!("    sp[{d:2}] = {w:?}");
            }
            return Err(InterpError::NotAClosure(closure));
        }

        // CRUCIAL: re-push retPC then closure (CALL_CLOSURE protocol).
        // bytecode.cpp:412-414 — after `pc = ...; closure = ...;` the
        // non-mixed path does `goto CALL_CLOSURE` which does
        // `(--sp)->codeAddr = pc; *(--sp) = (PolyWord)closure;`.
        // Without this, the new callee's stack lacks the standard
        // [closure, retPC, args] frame layout and locals end up
        // referencing wrong slots (handler-frame leakage manifested
        // here as a CALL_LOCAL_B reading a non-closure value).
        self.push(ret_pc_slot)?;
        self.push(closure)?;

        // Set PC and refresh code-segment bounds.
        let closure_ptr = closure.as_ptr::<PolyWord>();
        // SAFETY: closure invariant
        let code_word = unsafe { *closure_ptr };
        let new_code_obj = code_word.as_ptr::<PolyWord>();
        // SAFETY: code object invariant
        let (consts_start, _) = unsafe { length_word::const_segment_for_code(new_code_obj) };
        self.code_start = new_code_obj.cast::<u8>();
        self.code_end = consts_start.cast::<u8>();
        self.pc = self.code_start;

        // Do NOT push to `frames`. Tail call replaces the current
        // frame; the eventual RETURN of the tail callee should pop
        // the side-stack entry that our caller pushed.
        Ok(())
    }

    /// Implement the CALL_CLOSURE common path (bytecode.cpp:412-424).
    ///
    /// At entry, `closure` has already been popped from the stack. We:
    /// 1. push retPC (current pc, encoded as raw bits);
    /// 2. push closure;
    /// 3. jump to closure's first word (which is the code address).
    fn do_call(&mut self, closure: PolyWord) -> Result<(), InterpError> {
        use crate::length_word;

        if !closure.is_data_ptr() || closure.0 & (std::mem::size_of::<usize>() - 1) != 0 {
            // Diagnostic dump — always print since this is fatal.
            {
                let segment_size = unsafe { self.code_end.offset_from(self.code_start) as usize };
                eprintln!(
                    "  CALL bad closure: {closure:?} | frames depth={} | sp_depth={} | code_segment_bytes={}",
                    self.frames.len(),
                    self.stack_height(),
                    segment_size,
                );
                // Stack window
                let n = std::cmp::min(40, self.stack_height());
                for d in 0..n {
                    let w = self.stack[self.sp + d];
                    let marker = if w == closure { " <-- bad closure" } else { "" };
                    eprintln!("    sp[{d:2}] = {w:?}{marker}");
                }
                // Bytecode window around the failing PC (which has
                // already advanced past the opcode + immediate).
                let cur_off = self.pc_offset();
                let lo = cur_off.saturating_sub(20);
                let hi = std::cmp::min(cur_off + 5, segment_size);
                let bytes: Vec<u8> = (lo..hi)
                    .map(|i| unsafe { *self.code_start.add(i) })
                    .collect();
                let hexdump = bytes
                    .iter()
                    .map(|b| format!("{b:02x}"))
                    .collect::<Vec<_>>()
                    .join(" ");
                eprintln!("    bytes [{lo}..{hi}] = {hexdump}  (PC after fetch = {cur_off})",);
                eprintln!("  Recent CALL targets (most recent first):");
                let n = self.recent_call_targets.len();
                for off in 0..n {
                    let idx = (self.recent_call_idx + n - 1 - off) % n;
                    let target = self.recent_call_targets[idx];
                    if target != 0 {
                        eprintln!("    -{off:2}: code=0x{target:016x}");
                    }
                }
                eprintln!("  Current code: 0x{:016x}", self.code_start as usize);
            }
            return Err(InterpError::NotAClosure(closure));
        }
        // JIT fast path: if a JIT'd version of this closure's code
        // object is installed, dispatch to it directly without
        // setting up an interpreter frame. The JIT'd function reads
        // its args from the current sp window, returns a PolyWord.
        // We then unwind the call group (args + closure that the
        // caller pushed, plus the retPC slot we'd ordinarily push)
        // and push the result.
        let closure_ptr_for_jit = closure.as_ptr::<PolyWord>();
        // SAFETY: closure is a data pointer.
        let code_word_for_jit = unsafe { *closure_ptr_for_jit };
        let code_obj_ptr_for_jit = code_word_for_jit.0;
        // JIT-cache fast path. Skip when already inside a JIT call
        // (JIT_INTERP set) to avoid Rust stack growth via JIT-↔-interp
        // ping-pong. The interpreter's managed PolyWord stack handles
        // recursion fine — but a Rust frame per nested call would
        // exhaust the OS thread stack on bootstrap-scale workloads.
        //
        // Short-circuit on the cheap state-local check first: in the
        // default (non-`--jit`) configuration `jit_cache` is empty, so
        // this skips both the JIT_INTERP thread-local access AND the
        // HashMap probe on every CALL. When the JIT IS installed the
        // guard is false and the original logic runs unchanged.
        if !self.jit_cache.is_empty()
            && crate::jit_bridge::JIT_INTERP.with(|c| c.get()).is_null()
            && let Some(entry) = self.jit_cache.get(&code_obj_ptr_for_jit).copied()
        {
            if let Some(d) = self.diag.as_mut() {
                *d.jit_call_hits.entry(code_obj_ptr_for_jit).or_insert(0) += 1;
                // Also count toward total call_targets (for compare).
                *d.call_targets.entry(code_obj_ptr_for_jit).or_insert(0) += 1;
            }
            if jit_trace_calls_on() {
                let mut arg_dump = String::new();
                for i in (0..entry.sml_arity).rev() {
                    let v = self.stack[self.sp + i].0;
                    arg_dump.push_str(&format!(" arg_{}=0x{v:016x}", entry.sml_arity - 1 - i));
                }
                eprintln!(
                    "JIT call: code_obj=0x{code_obj_ptr_for_jit:016x} sml_arity={} arity_init={} sp_depth={} closure=0x{:016x}{arg_dump}",
                    entry.sml_arity,
                    entry.arity_init,
                    self.stack.len() - self.sp,
                    closure.0,
                );
                if std::env::var("JIT_TRACE_CALLS_BC").is_ok() {
                    let bc_ptr = code_obj_ptr_for_jit as *const u8;
                    let bc_len = 96usize;
                    let bytes: Vec<u8> = (0..bc_len).map(|i| unsafe { *bc_ptr.add(i) }).collect();
                    let hex = bytes
                        .iter()
                        .take(80)
                        .map(|b| format!("{b:02x}"))
                        .collect::<Vec<_>>()
                        .join(" ");
                    eprintln!("  bytecode head: {hex}");
                }
            }
            // Build the JIT args array: args_ptr[0..arity_init].
            // For SML arity N, the stack window at entry is:
            //   sp[0] = arg_{N-1}, ..., sp[N-1] = arg_0  (caller pushed)
            // The JIT expects args_ptr ordered:
            //   args_ptr[0] = arg_0, ..., args_ptr[N-1] = arg_{N-1},
            //   args_ptr[N]   = retPC slot (LOCAL_1 in SML — JIT'd code
            //                   doesn't actually call back via this so 0
            //                   is safe)
            //   args_ptr[N+1] = closure slot (LOCAL_0 in SML — SML code
            //                   accesses captures via
            //                   `INDIRECT_CLOSURE_BN` which dereferences
            //                   this, so it MUST be the real closure
            //                   pointer to avoid a null deref)
            // Build args_buf to match SML's stack-frame semantics.
            // SML interp's stack at callee entry (top to bottom):
            //   sp[0]      = closure
            //   sp[1]      = retPC
            //   sp[2..N+1] = args (top arg at sp[2], deepest at sp[N+1])
            //   sp[N+2..]  = older caller-frame items
            //
            // JIT compile-time stack mirrors this: stack[i] reads the
            // SML position sp[arity_init - 1 - i]. So args_buf layout
            // must be:
            //   args_buf[0]                = sp[arity_init-1] = deepest older
            //   ...
            //   args_buf[arity_init-N-3]   = sp[N+2]          = top older
            //   args_buf[arity_init-N-2]   = sp[N+1]          = arg_0
            //   ...
            //   args_buf[arity_init-3]     = sp[2]            = arg_{N-1}
            //   args_buf[arity_init-2]     = sp[1]            = retPC slot (0)
            //   args_buf[arity_init-1]     = sp[0]            = closure
            //
            // When arity_init == N+2 (common case), there are no older
            // items and the layout is the same as before. When the JIT
            // translator infers arity_init > N+2 (because the bytecode
            // reads LOCAL_K for K > N+1), we populate the extra slots
            // from interp.stack[interp.sp + n + j] — which is what
            // SML interp would have at those positions.
            let n = entry.sml_arity;
            let arity_init = entry.arity_init;
            assert!(
                arity_init >= n + 2,
                "arity_init must include retPC + closure slots"
            );
            let extra_older = arity_init - n - 2;
            let mut args_buf: Vec<i64> = vec![0; arity_init];
            // Older items: args_buf[0..extra_older-1].
            // args_buf[i] = sp[arity_init - 1 - i] (in SML terms).
            // After do_call's pop (sp += n), interp.stack[interp.sp + j]
            // would be SML's sp[N + 2 + j] (since CALL popped closure
            // already, and we're about to pop the args). But we want
            // to read BEFORE the pop, so it's interp.stack[interp.sp + n + j].
            for i in 0..extra_older {
                let sml_sp_pos = arity_init - 1 - i; // = N + 2 + (extra_older - 1 - i)
                let j = sml_sp_pos - (n + 2); // older-stack index from top
                let stack_pos = self.sp + n + j;
                args_buf[i] = if stack_pos < self.stack.len() {
                    self.stack[stack_pos].0 as i64
                } else {
                    0
                };
            }
            // SML args: args_buf[extra_older..extra_older+N-1].
            // args_buf[extra_older + i] = arg_i = sp[N+1-i] (in SML) = interp.stack[interp.sp + (N-1-i)]
            for i in 0..n {
                let stack_pos = self.sp + (n - 1 - i);
                args_buf[extra_older + i] = self.stack[stack_pos].0 as i64;
            }
            // retPC slot: placeholder 0. JIT'd code that reads this
            // (via LOCAL_K mapping to it) gets 0 instead of SML's real
            // retPC — functions that DEREF this value through indirect
            // ops can SEGV. We avoid that by refusing to install such
            // functions in `install_all_jit_entries` (= functions with
            // jit_arity_init > sml_arity + 2).
            args_buf[arity_init - 2] = 0;
            // Closure slot.
            args_buf[arity_init - 1] = closure.0 as i64;
            // Pop N args from the interpreter stack (they're now in
            // args_buf — the JIT'd function reads from there).
            self.sp += n;
            // Set the thread-local interpreter pointer so any
            // closure_call_trampoline / alloc_trampoline call from
            // inside the JIT'd code can reach back into this
            // interpreter via `jit_bridge`.
            //
            // We use a raw `*mut Interpreter` to avoid double-borrow.
            // The thread-local guard restores the previous value on
            // drop (including panic).
            let self_ptr: *mut Interpreter = self;
            let prev = crate::jit_bridge::JIT_INTERP.with(|c| {
                let p = c.get();
                c.set(self_ptr);
                p
            });
            // SAFETY: caller registered `entry.func` with a matching
            // ABI; args_buf has at least arity_init entries. The two
            // trailing params (sp_in, stack_base) are reserved for
            // the Phase-2 memory-backed translator; currently ignored
            // by all generated code but must be passed validly.
            #[allow(clippy::cast_possible_wrap)]
            let sp_in_i64 = self.sp as i64;
            let stack_base = self.stack.as_mut_ptr() as i64;
            let result_bits = unsafe { (entry.func)(args_buf.as_ptr(), sp_in_i64, stack_base) };
            crate::jit_bridge::JIT_INTERP.with(|c| c.set(prev));
            if jit_trace_calls_on() {
                eprintln!("  → returned 0x{:016x}", result_bits as u64);
            }
            let result = PolyWord::from_bits(result_bits as usize);
            self.push(result)?;
            return Ok(());
        }
        // Save the *current* PC as the return address. By this point
        // we've already advanced past the call opcode and its immediates,
        // so resuming at this PC after RETURN is correct.
        let ret_pc_bits = self.pc as usize;
        self.push(PolyWord::from_bits(ret_pc_bits))?;
        self.push(closure)?;

        // The closure's first word IS the code object pointer (per
        // F_CLOSURE_OBJ layout). Jump to its byte 0.
        let closure_ptr = closure.as_ptr::<PolyWord>();
        // SAFETY: caller (compiler) is trusted to emit a valid closure.
        let code_word = unsafe { *closure_ptr };
        let new_code_obj = code_word.as_ptr::<PolyWord>();
        // Defensive: detect self-pointer pattern (4-word exception
        // packets misrouted as closures). Diagnostic instead of a
        // segfault.
        if code_word.0 == closure.0 {
            eprintln!(
                "  do_call: closure {closure:?} has self-pointer word[0] — \
                 likely an exception packet being called as a closure"
            );
            // Dump heap object layout
            unsafe {
                let lw = crate::space::MemorySpace::length_word_of(closure_ptr);
                let n = length_word::length_of(lw);
                let f = length_word::flags_of(lw);
                eprintln!("  closure header: n_words={n} flags=0x{f:02x}");
                for i in 0..std::cmp::min(n, 8) {
                    let w = *closure_ptr.add(i);
                    eprintln!("    word[{i}] = {w:?}");
                }
                // Try to decode word[1] as a PolyStringObject: word[0] = byte length, then chars.
                if n >= 2 {
                    let name_word = *closure_ptr.add(1);
                    if name_word.is_data_ptr() {
                        let name_ptr = name_word.as_ptr::<PolyWord>();
                        let len_w = (*name_ptr).0;
                        if len_w > 0 && len_w < 256 {
                            let chars =
                                std::slice::from_raw_parts(name_ptr.add(1).cast::<u8>(), len_w);
                            if let Ok(s) = std::str::from_utf8(chars) {
                                eprintln!("  exception name string: {s:?}");
                            }
                        }
                    }
                }
            }
            return Err(InterpError::NotAClosure(closure));
        }

        // Save caller's bounds on the side-stack before we overwrite.
        self.frames.push((self.code_start, self.code_end));

        // Recompute code segment bounds for the new code object.
        // SAFETY: closure invariant guarantees the code address is a
        // real code object.
        let (consts_start, _) = unsafe { length_word::const_segment_for_code(new_code_obj) };
        self.code_start = new_code_obj.cast::<u8>();
        self.code_end = consts_start.cast::<u8>();
        // Record call target in ring buffer.
        self.recent_call_targets[self.recent_call_idx] = new_code_obj as usize;
        self.recent_call_idx = (self.recent_call_idx + 1) % self.recent_call_targets.len();
        self.pc = self.code_start;
        if let Some(d) = self.diag.as_mut() {
            *d.call_targets.entry(new_code_obj as usize).or_insert(0) += 1;
        }
        Ok(())
    }

    /// Implement RETURN_N (bytecode.cpp:454-465).
    ///
    /// Stack on entry (from top):  result, closure, retPC, args[N]
    ///                              ^ sp
    ///
    /// We pop result, skip closure, pop retPC, drop N args, push
    /// result. If retPC is null, we're returning from the top-level
    /// frame — yield StepResult::Returned(result).
    fn do_return(&mut self, return_count: usize) -> Result<StepResult, InterpError> {
        // Diagnostic: peek the entire frame before popping, so we can
        // see if the stack is misaligned (retPC not a code pointer).
        let pre_dump = jit_trace_returns_on() && {
            let sp = self.sp;
            let depth = self.stack.len().saturating_sub(sp);
            let need = 3 + return_count;
            if depth >= need {
                let result_peek = self.stack[sp].0;
                let closure_peek = self.stack[sp + 1].0;
                let ret_pc_peek = self.stack[sp + 2].0;
                !(self.code_start as usize <= ret_pc_peek && ret_pc_peek < self.code_end as usize)
                    && {
                        // Probably bad — dump frame.
                        eprintln!(
                            "  do_return PRE-POP: ret_count={return_count} \
                             cur_code=[0x{:016x}..0x{:016x}] sp_depth={} \
                             stack[sp..sp+need]:",
                            self.code_start as usize, self.code_end as usize, depth,
                        );
                        for i in 0..need.min(depth) {
                            let v = self.stack[sp + i].0;
                            let label = match i {
                                0 => "result",
                                1 => "closure",
                                2 => "retPC",
                                _ => "arg",
                            };
                            eprintln!("    sp[{i:2}] = 0x{v:016x}  ({label})");
                        }
                        let _ = (result_peek, closure_peek);
                        true
                    }
            } else {
                false
            }
        };
        let _ = pre_dump;
        let result = self.pop()?; // top: result
        let closure = self.pop()?; // closure
        let ret_pc_word = self.pop()?; // retPC
        for _ in 0..return_count {
            self.pop()?; // args
        }
        self.push(result)?;

        let ret_pc_bits = ret_pc_word.0;
        if ret_pc_bits == 0 {
            // Top-level return: yield to host. Result is on top.
            let result = self.pop()?;
            return Ok(StepResult::Returned(result));
        }

        // Restore the caller's code segment bounds from our side-stack.
        let (caller_start, caller_end) = self.frames.pop().ok_or(InterpError::StackUnderflow)?;

        // Diagnostic: if the retPC isn't in the caller's code segment,
        // something corrupted the stack. Print a detailed dump so we
        // can trace the source. Gated on JIT_TRACE_RETURNS to avoid
        // noise in normal runs.
        // Balance check: retPC must point into the caller's code segment.
        // If not, a callee left the stack misaligned (a one-slot leak puts the
        // real closure pointer in the retPC slot). Uses the CACHED ARBINT_DEBUG
        // flag (NOT per-call env::var, which would syscall every return), and
        // aborts at the FIRST corrupted return — that frame IS the leak culprit.
        if arbint_trace_on()
            && !(caller_start as usize <= ret_pc_bits && ret_pc_bits < caller_end as usize)
        {
            eprintln!(
                "  do_return: BAD retPC! ret_count={return_count} ret_pc=0x{ret_pc_bits:016x} \
                 caller_segment=[0x{:016x}..0x{:016x}] closure=0x{:016x} \
                 result=0x{:016x} frames_depth={}",
                caller_start as usize,
                caller_end as usize,
                closure.0,
                result.0,
                self.frames.len(),
            );
            let recent = self.recent_call_targets_snapshot();
            eprintln!("  recent CALL targets (newest first):");
            for (i, t) in recent.iter().enumerate().take(8) {
                eprintln!("    -{i}: 0x{t:016x}");
            }
            // Dump the opcode ring so the leaking callee's op sequence is visible.
            OP_RING.with(|r| {
                let ring = r.borrow();
                eprintln!("  --- op ring (last {}) at BAD return ---", ring.len());
                for (code, off, op, sp) in
                    ring.iter().rev().take(40).collect::<Vec<_>>().iter().rev()
                {
                    eprintln!("    code=0x{code:x} off={off:>5} op=0x{op:02x} sp={sp}");
                }
            });
            std::process::abort();
        }
        self.code_start = caller_start;
        self.code_end = caller_end;
        self.pc = ret_pc_bits as *const u8;
        Ok(StepResult::Continue)
    }

    // ---- PC-relative constant access -----------------------------------

    /// Load a `PolyWord` from a PC-relative byte offset plus a
    /// PolyWord-scaled index. Mirrors upstream's
    /// `((PolyWord*)(pc + imm))[idx]` pattern from `bytecode.cpp:530`
    /// (and analogous lines for the `_8_8` and `_16_8` variants).
    ///
    /// Caller is expected to have fetched all immediate bytes; the
    /// upstream `pc + pc[0] + N` becomes `self.pc + imm` in our terms,
    /// where N (the number of immediate bytes) has been absorbed by
    /// our `fetch_u8` calls.
    ///
    /// # Safety
    /// `self.pc + byte_off + idx*sizeof(PolyWord)` must land within
    /// the constant pool of the current code object.
    unsafe fn read_pc_const(&self, byte_off: usize, idx: usize) -> PolyWord {
        // SAFETY: precondition.
        unsafe {
            let base = self.pc.add(byte_off);
            base.cast::<PolyWord>().add(idx).read_unaligned()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::opcodes::*;
    use super::*;
    use crate::length_word::{F_CLOSURE_OBJ, F_CODE_OBJ};
    use crate::space::{MemorySpace, SpaceKind};

    // ---- ALU + control flow tests (carried over, adjusted for new API)

    fn run_to_int(code: Vec<u8>) -> isize {
        let mut interp = Interpreter::from_bytes(64, code);
        // For from_bytes tests we don't have a real call frame, so we
        // seed retPC=null + a dummy closure beneath any args, mimicking
        // the entry-from-top-level shape.
        interp.test_seed_return_sentinel();
        interp.test_seed_top(PolyWord::ZERO); // dummy "closure" placeholder
        // NB: this means our test bytecode runs as if it's the
        // top-level function — its RETURN_N will see retPC=null and
        // yield Returned(result).
        match interp.run() {
            Ok(StepResult::Returned(w)) => w.untag(),
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn real_to_int_round_overflow_guard() {
        // In range: Some(rounded). round(0)/floor(1)/ceil(2)/trunc(3).
        assert_eq!(Interpreter::real_to_int_round(3.7, 0), Some(4)); // round
        assert_eq!(Interpreter::real_to_int_round(3.7, 1), Some(3)); // floor
        assert_eq!(Interpreter::real_to_int_round(3.2, 2), Some(4)); // ceil
        assert_eq!(Interpreter::real_to_int_round(-3.7, 3), Some(-3)); // trunc
        // Out of tagged range / non-finite -> None (the handler raises Overflow).
        assert_eq!(Interpreter::real_to_int_round(1.0e30, 1), None);
        assert_eq!(Interpreter::real_to_int_round(-1.0e30, 1), None);
        assert_eq!(Interpreter::real_to_int_round(f64::INFINITY, 3), None);
        assert_eq!(Interpreter::real_to_int_round(f64::NAN, 0), None);
    }

    #[test]
    fn reset_vs_reset_r_differ() {
        // CLAUDE.md: "Don't merge RESET variants." RESET_R(n) preserves the TOP and
        // drops the n items BELOW it; RESET(n) drops the top n. With [A=10,B=20,C=30]
        // (C on top): RESET_R 2 -> top is C(30); RESET 2 -> top is A(10). A fence so
        // a future merge/refactor of drop_n vs reset is caught immediately.
        let mk = || {
            let mut i = Interpreter::from_bytes(64, vec![]);
            i.push(PolyWord::tagged(10)).unwrap();
            i.push(PolyWord::tagged(20)).unwrap();
            i.push(PolyWord::tagged(30)).unwrap();
            i
        };
        let mut ir = mk();
        ir.reset(2).unwrap(); // RESET_R 2: keep top, drop 2 below
        assert_eq!(
            ir.peek(0).unwrap().untag(),
            30,
            "RESET_R must preserve the top"
        );
        let mut id = mk();
        id.drop_n(2).unwrap(); // RESET 2: drop top 2
        assert_eq!(id.peek(0).unwrap().untag(), 10, "RESET must drop the top n");
    }

    #[test]
    fn atomic_reset_returns_true_only_when_sole_locker() {
        // unlockMutex (atomicReset) writes TAGGED(0) into the mutex and
        // returns True iff the old word0 was exactly TAGGED(1) (sole locker).
        // bytecode.cpp:1534-1542. Our old handler always returned False.
        for (old, expect_true) in [(1isize, true), (0isize, false), (3isize, false)] {
            let code = vec![INSTR_ESCAPE, opcodes::ext::EXTINSTR_ATOMIC_RESET];
            let mut i = Interpreter::from_bytes(64, code);
            // 1-word "mutex" cell, Box-backed (heap, word-aligned, no allocator).
            let p = Box::into_raw(Box::new([PolyWord::tagged(old)])).cast::<PolyWord>();
            i.test_seed_top(PolyWord::from_ptr(p.cast_const()));
            let _ = i.step().unwrap();
            let res = i.peek(0).unwrap();
            assert_eq!(
                unsafe { (*p).0 },
                PolyWord::tagged(0).0,
                "mutex reset to unlocked"
            );
            let want = if expect_true {
                PolyWord::tagged(1).0
            } else {
                PolyWord::tagged(0).0
            };
            assert_eq!(res.0, want, "old={old}: True iff old==TAGGED(1)");
            drop(unsafe { Box::from_raw(p.cast::<[PolyWord; 1]>()) });
        }
    }

    #[test]
    fn atomic_exch_add_legacy_semantics() {
        // LEGACY opcode (compiler no longer emits it). Pops ONE addend,
        // PEEKS the object, returns its old word0, writes word0 = old+addend
        // (tagged arithmetic). Old handler popped TWO slots (underflow) and
        // returned tagged(0). bytecode.cpp:1483-1494.
        let code = vec![INSTR_ESCAPE, opcodes::ext::EXTINSTR_ATOMIC_EXCH_ADD];
        let mut i = Interpreter::from_bytes(64, code);
        let p = Box::into_raw(Box::new([PolyWord::tagged(10)])).cast::<PolyWord>();
        i.test_seed_top(PolyWord::from_ptr(p.cast_const())); // object (deeper)
        i.test_seed_top(PolyWord::tagged(5)); // addend (top)
        let sp_before = i.test_sp();
        let _ = i.step().unwrap();
        assert_eq!(i.peek(0).unwrap().untag(), 10, "returns old word0");
        assert_eq!(unsafe { (*p).untag() }, 15, "writes back old+addend = 15");
        assert_eq!(i.test_sp(), sp_before + 1, "net stack effect -1");
        drop(unsafe { Box::from_raw(p.cast::<[PolyWord; 1]>()) });
    }

    #[test]
    fn const_and_return() {
        // RETURN_1 expects 1 word of args under the [closure, retPC]
        // pair; our test harness seeds only the pair (0 args), so we
        // use RETURN_B 0 here.
        let code = vec![INSTR_CONST_3, INSTR_RETURN_B, 0];
        assert_eq!(run_to_int(code), 3);
    }

    #[test]
    fn fixed_add() {
        let code = vec![
            INSTR_CONST_3,
            INSTR_CONST_4,
            INSTR_FIXED_ADD,
            INSTR_RETURN_B,
            0,
        ];
        assert_eq!(run_to_int(code), 7);
    }

    #[test]
    fn jump_forward_skips_const() {
        // Stack layout: [closure_dummy, retPC=null]; we PUSH 3, then
        // jump past a const_4, then RETURN_B 0.
        // Bytes:
        //   0: CONST_3
        //   1: JUMP8
        //   2: 1            (offset)
        //   3: CONST_4      (skipped)
        //   4: RETURN_B
        //   5: 0
        let code = vec![
            INSTR_CONST_3,
            INSTR_JUMP8,
            1,
            INSTR_CONST_4,
            INSTR_RETURN_B,
            0,
        ];
        assert_eq!(run_to_int(code), 3);
    }

    #[test]
    fn loop_jump_back() {
        // Tight loop: counter starts at 5, subtract 1 each iter, exit
        // when zero. JUMP_BACK8 immediate = ic - dest (= compiler's
        // diff formula): opcode at pc=10, destination at pc=2, so 8.
        let code = vec![
            INSTR_CONST_INT_B,
            5,
            // .top = pc 2
            INSTR_CONST_INT_B,
            1,
            INSTR_FIXED_SUB,
            INSTR_LOCAL_0,
            INSTR_CONST_0,
            INSTR_EQUAL_WORD,
            INSTR_JUMP8_TRUE,
            2,
            INSTR_JUMP_BACK8,
            8, // 10 - 2 = 8
            INSTR_RETURN_B,
            0,
        ];
        assert_eq!(run_to_int(code), 0);
    }

    // ---- Call / return tests using real code objects in a MemorySpace

    /// Materialise a code object into `space` with the given bytecode
    /// bytes followed by a constant pool of the given values, plus the
    /// trailing const-count + offset trailer. Returns a pointer to the
    /// new object (one word after its length word).
    fn make_code_object(
        space: &mut MemorySpace,
        code_bytes: &[u8],
        constants: &[PolyWord],
    ) -> *const PolyWord {
        let word = std::mem::size_of::<usize>();
        let code_words = code_bytes.len().div_ceil(word);
        let n_consts = constants.len();
        let total_words = code_words + n_consts + 2;
        let obj_ptr = space.alloc(total_words);
        unsafe {
            crate::space::set_length_word(obj_ptr, total_words, F_CODE_OBJ);
            // Code bytes.
            let dst = obj_ptr.cast::<u8>();
            std::ptr::copy_nonoverlapping(code_bytes.as_ptr(), dst, code_bytes.len());
            // Pad final code word with zeros.
            let pad = code_bytes.len().next_multiple_of(word) - code_bytes.len();
            if pad > 0 {
                std::ptr::write_bytes(dst.add(code_bytes.len()), 0, pad);
            }
            // const count at [code_words]
            obj_ptr.add(code_words).write(PolyWord::from_bits(n_consts));
            // constants at [code_words+1 .. total-1]
            for (i, c) in constants.iter().enumerate() {
                obj_ptr.add(code_words + 1 + i).write(*c);
            }
            // trailing offset at [total-1]: matches loader.rs
            #[allow(clippy::cast_possible_wrap)]
            let const_addr_index = (code_words + 1) as isize;
            let total_isize = total_words as isize;
            let word_isize = word as isize;
            let offset_bytes = (const_addr_index - total_isize) * word_isize;
            obj_ptr
                .add(total_words - 1)
                .write(PolyWord::from_bits(offset_bytes as usize));
        }
        obj_ptr.cast_const()
    }

    /// Materialise a closure object pointing at the given code object.
    fn make_closure(space: &mut MemorySpace, code_obj: *const PolyWord) -> *const PolyWord {
        let obj_ptr = space.alloc(1);
        unsafe {
            crate::space::set_length_word(obj_ptr, 1, F_CLOSURE_OBJ);
            obj_ptr.add(0).write(PolyWord::from_ptr(code_obj));
        }
        obj_ptr.cast_const()
    }

    #[test]
    fn synthetic_call_and_return() {
        // Build:
        //   callee: CONST_INT_B 7; RETURN_B 0  -> returns 7 with 0 args
        //   caller: <push closure>; CALL_CLOSURE; RETURN_B 0
        //
        // The caller side is built as bytecode; the closure pointer is
        // pre-seeded onto the stack so the caller's CALL_CLOSURE pops
        // it.
        let mut code_space = MemorySpace::new(64, SpaceKind::Code);
        let callee_bytes = vec![INSTR_CONST_INT_B, 7, INSTR_RETURN_B, 0];
        let callee_code = make_code_object(&mut code_space, &callee_bytes, &[]);
        let callee_closure = make_closure(&mut code_space, callee_code);

        let caller_bytes = vec![INSTR_CALL_CLOSURE, INSTR_RETURN_B, 0];
        let caller_code = make_code_object(&mut code_space, &caller_bytes, &[]);

        let mut interp = unsafe { Interpreter::from_code_object(64, caller_code) };
        // Seed top-of-stack with: [closure_for_caller=dummy,
        // retPC=null, callee_closure_ptr_to_pop_in_CALL]
        interp.test_seed_return_sentinel();
        interp.test_seed_top(PolyWord::ZERO); // caller's "self" closure
        interp.test_seed_top(PolyWord::from_ptr(callee_closure)); // top: callee closure to call

        match interp.run() {
            Ok(StepResult::Returned(v)) => assert_eq!(v.untag(), 7),
            other => panic!("expected Returned(7), got {other:?}"),
        }
    }

    #[test]
    fn const_addr_loads_from_pool() {
        // Test CONST_ADDR8_0 with unsigned-byte semantics (matches
        // upstream bytecode.cpp:529-530). The const-addr formula is
        // PC-relative-forward, so we need enough bytecode bytes
        // BEFORE the constants for the unsigned imm to reach them.
        //
        // Layout: [CONST_ADDR8_0, imm, NOP*N, RETURN_B, 0] followed by
        // the constants area.
        //
        // CONST_ADDR8_0 formula: val = (PolyWord*)(self.pc + imm)[3]
        // where self.pc is *after* fetching opcode+imm (== upstream's
        // `pc` at handler entry, when upstream does `pc + pc[0] + 1`).
        //
        // Choose layout so:
        //   - 1 word of constants (TAGGED 42 at index 0)
        //   - code_bytes occupies ceil(30/8) = 4 words = 32 bytes
        //   - const_count word at byte 32
        //   - constants start at byte 40 (slot code_words + 1)
        //   - self.pc after fetching CONST_ADDR8_0 + imm = byte 2
        //   - formula: 2 + imm + 3*8 = 40 → imm = 14
        let mut code_bytes = vec![INSTR_CONST_ADDR8_0, 14];
        // Pad to 30 bytes total (so code_words = ceil(30/8) = 4).
        // We have 2 bytes already; add 26 NOPs.
        code_bytes.resize(28, INSTR_NO_OP);
        code_bytes.push(INSTR_RETURN_B);
        code_bytes.push(0);
        assert_eq!(code_bytes.len(), 30); // sanity

        let mut code_space = MemorySpace::new(32, SpaceKind::Code);
        let code = make_code_object(&mut code_space, &code_bytes, &[PolyWord::tagged(42)]);

        let mut interp = unsafe { Interpreter::from_code_object(64, code) };
        interp.test_seed_return_sentinel();
        interp.test_seed_top(PolyWord::ZERO);

        match interp.run() {
            Ok(StepResult::Returned(v)) => assert_eq!(v.untag(), 42),
            other => panic!("expected Returned(42), got {other:?}"),
        }
    }

    #[test]
    fn unimplemented_surface() {
        // ESCAPE + an extension byte we don't handle (use a high value
        // that's not in our extension dispatch).
        // We've implemented most of the low/mid range — pick an
        // extension byte that's still unmapped (loadC* / storeC* are
        // FFI ops we haven't ported).
        let code = vec![INSTR_ESCAPE, 0xe2]; // some unimplemented ext
        let mut interp = Interpreter::from_bytes(64, code);
        match interp.run().unwrap() {
            StepResult::Unimplemented { op, extended } => {
                assert_eq!(op, 0xe2);
                assert!(extended);
            }
            other => panic!("expected Unimplemented (extended), got {other:?}"),
        }
    }
}
