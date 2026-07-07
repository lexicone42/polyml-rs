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
pub mod safe_deref;

use diag::DiagState;
use safe_deref::{DerefError, SafeSpaces, SpaceRange, ValidObj};

use std::sync::Arc;

use crate::poly_word::PolyWord;
use crate::rts::{RtsContext, RtsFn, RtsTable};

/// Dependency-free FxHash (the rustc-hash multiply-rotate algorithm),
/// used to key the `jit_cache` by code-object pointer (a `usize`).
///
/// The default `HashMap` uses SipHash, ~8.9 ns/probe (measured on the
/// 727-entry `jit_cache`) — that's a material slice of the 35.6 ns
/// interp→JIT boundary, paid on EVERY JIT call. The keys are already
/// well-distributed heap pointers, so the cryptographic mixing SipHash
/// provides is wasted; FxHash's single multiply+rotate is enough to
/// spread aligned pointers across buckets and is dramatically cheaper.
///
/// This hasher is fed exactly one `usize` per key (`write_usize`); the
/// generic `write` path exists only for completeness and is never hit
/// on the hot path.
#[derive(Default)]
pub struct FxHasher {
    hash: u64,
}

impl FxHasher {
    // The 64-bit rustc-hash constant (golden-ratio-derived odd multiplier).
    const SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;
    const ROTATE: u32 = 5;

    #[inline]
    fn add(&mut self, i: u64) {
        self.hash = (self.hash.rotate_left(Self::ROTATE) ^ i).wrapping_mul(Self::SEED);
    }
}

impl std::hash::Hasher for FxHasher {
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }

    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }

    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        // Cold fallback for non-usize keys — fold 8 bytes at a time.
        let mut chunks = bytes.chunks_exact(8);
        for c in &mut chunks {
            self.add(u64::from_le_bytes(c.try_into().unwrap()));
        }
        let rem = chunks.remainder();
        if !rem.is_empty() {
            let mut buf = [0u8; 8];
            buf[..rem.len()].copy_from_slice(rem);
            self.add(u64::from_le_bytes(buf));
        }
    }

    #[inline]
    fn finish(&self) -> u64 {
        self.hash
    }
}

/// `BuildHasher` for [`FxHasher`] over a pointer-keyed `HashMap`.
pub type FxBuildHasher = std::hash::BuildHasherDefault<FxHasher>;

/// Pointer-keyed JIT cache: code-object address (`usize`) → [`JitEntry`].
type JitCache = std::collections::HashMap<usize, JitEntry, FxBuildHasher>;

// =====================================================================
// WHOLE-REGION JIT BOUNDARY (S3b) — the live do_call hook.
//
// The interpreter cannot reference `polyml-jit` (the dependency is
// one-way: polyml-jit -> polyml-runtime). So the whole-region boundary
// is wired through a per-Interpreter REGION REGISTRY of native region
// roots, plus a single process-global DISPATCH callback the JIT installs
// at startup. The runtime defines the C-ABI mirror types (ExnCtxC /
// RegionRetC); the JIT registers a `region_dispatch` fn that performs
// the frame handshake (push retPC + closure, native-call the region
// root, interpret RegionRet) — i.e. `boundary::dispatch_region`.
//
// PROVABLY INERT WHEN OFF: with the flag off the JIT never installs the
// dispatch fn (it stays null) AND never registers any root (the per-
// Interpreter registry stays empty). The do_call hook is guarded on
// `!self.region_registry.is_empty()` — exactly the cheap state-local
// check the jit_cache fast path already uses — so the default
// interpreter path and the --jit path are byte-identical. One
// never-taken branch.
// =====================================================================

/// Mirror of `polyml_jit::region::ExnCtx` (handler_sp @ 0, exn_packet @
/// 8, interp_ptr @ 16, live_sp @ 24, gc_used_ptr @ 32, gc_trigger @ 40).
/// `#[repr(C)]` so the JIT loads/stores by fixed byte offset. The layout
/// MUST stay identical to the JIT side — the do_call hook builds this and
/// the region reinterprets the SAME memory.
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct ExnCtxC {
    /// Downward stack index of the current handler frame, or the JIT's
    /// `NO_HANDLER` sentinel.
    pub handler_sp: i64,
    /// The raised value (tagged PolyWord bits / region exn sentinel).
    pub exn_packet: i64,
    /// Raw `*mut Interpreter` (as `i64` bits) the do_call hook stores
    /// BEFORE invoking the region, so a region's DYNAMIC-call trampoline
    /// (`region_interp_call`) can re-enter `do_call` via this raw pointer
    /// WITHOUT materializing a second aliasing `&mut Interpreter`. 0 when
    /// the region needs no dynamic-call re-entry (e.g. the static-only
    /// boundary demo). See the soundness argument in the JIT boundary.
    pub interp_ptr: i64,
    /// THE GC-SAFEPOINT SP-PUBLISH SLOT (S4c). A region writes its current
    /// SSA `sp` here before taking the slow-path `region_safepoint`, so
    /// the helper can set `self.sp = live_sp` and the Cheney GC forwards
    /// the live stack `[sp, len)` exactly. Offset 24.
    pub live_sp: i64,
    /// Address (raw bits of a `*const usize`) of the LIVE heap
    /// words-allocated counter (`MemorySpace.used`) the region's inline
    /// back-edge poll reads — the SAME counter the top-of-step GC check
    /// reads. Offset 32.
    pub gc_used_ptr: i64,
    /// The GC trigger word count (`gc_trigger_words`) the region's poll
    /// compares `*gc_used_ptr` against (`i64::MAX` when GC is disabled).
    /// Offset 40.
    pub gc_trigger: i64,
}

/// Mirror of `polyml_jit::region::RegionRet` — NOT a bare tuple (tuples
/// are not FFI-safe). `new_sp` is the post-collapse downward sp; `raised`
/// is 0 (normal) or 1 (an exception is propagating).
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct RegionRetC {
    pub new_sp: i64,
    pub raised: i64,
}

/// The process-global dispatch callback installed by `polyml-jit` when
/// the whole-region path is enabled. It performs the boundary frame
/// handshake against a finalized native region root.
///
/// Args: (`region_fn_ptr`, `stack_base`, `sp_at_top_arg`, `closure_bits`,
/// `ctx`). `region_fn_ptr` is the finalized native region root pointer
/// (as a raw address); the dispatcher transmutes it to the region ABI.
pub type RegionDispatchFn =
    unsafe extern "C" fn(usize, *mut i64, i64, i64, *mut ExnCtxC) -> RegionRetC;

/// The installed dispatch callback, or null (flag off → never installed →
/// the do_call hook is never reached because the per-Interpreter registry
/// is also empty).
static REGION_DISPATCH: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Install the whole-region dispatch callback (called once by the JIT at
/// startup when the flag is on). Idempotent.
pub fn install_region_dispatch(f: RegionDispatchFn) {
    REGION_DISPATCH.store(f as usize, std::sync::atomic::Ordering::Release);
}

/// A registered native region root: the finalized native entry pointer +
/// its SML arity (the number of caller-pushed args, so the hook knows the
/// `sp_at_top_arg` frame shape and how the RETURN_N collapse lands).
#[derive(Clone, Copy, Debug)]
pub struct RegionEntry {
    /// Finalized native region-root function pointer (raw address).
    pub region_fn: usize,
    /// SML arity (caller-pushed arg count).
    pub sml_arity: usize,
}

/// Pointer-keyed region registry: code-object address (`usize`) →
/// [`RegionEntry`]. Empty by default (flag off) → the do_call hook is one
/// never-taken branch.
type RegionRegistry = std::collections::HashMap<usize, RegionEntry, FxBuildHasher>;

/// "No handler in scope" sentinel for the region ExnCtx — MUST equal
/// `polyml_jit::region::NO_HANDLER` (`i64::MIN / 2`). The interpreter's
/// own "no handler" is `handler_sp == stack.len()`; the boundary maps
/// between them.
pub const REGION_NO_HANDLER: i64 = i64::MIN / 2;

/// Region Overflow exn sentinel — MUST equal `polyml_jit::memtrans::
/// EXN_OVERFLOW`. An even (untagged) value so it can never collide with a
/// real tagged result.
pub const REGION_EXN_OVERFLOW: i64 = 0x0001_0000_0000_0002;

/// Region DivByZero exn sentinel — MUST equal `polyml_jit::memtrans::
/// EXN_DIVZERO`.
pub const REGION_EXN_DIVZERO: i64 = 0x0002_0000_0000_0002;

/// Region StackOverflow exn sentinel — MUST equal `polyml_jit::memtrans::
/// EXN_STACKOVERFLOW`. The faithful `STACK_SIZE16` lowering returns this
/// when `sp < needed`; the boundary maps it onto `InterpError::
/// StackOverflow` (a HARD error, exactly like the interpreter at
/// mod.rs:3457).
pub const REGION_EXN_STACKOVERFLOW: i64 = 0x0003_0000_0000_0002;

/// Inline (stack-allocated) capacity of the per-call JIT args buffer in
/// `do_call`. Covers `arity_init` up to this many slots (= SML arity up
/// to `JIT_ARGS_INLINE - 2 = 14`), which is every real bootstrap
/// function; larger arities spill to a heap `Vec`. Sized to dodge the
/// `vec![0; arity_init]` heap allocation that the old code paid on EVERY
/// JIT call (measured ~6.1 ns of the 35.6 ns interp→JIT boundary).
const JIT_ARGS_INLINE: usize = 16;

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
            let on = crate::env::env_flag("ARBINT_DEBUG");
            F.store(if on { 1 } else { 2 }, Ordering::Relaxed);
            on
        }
    }
}

/// Memoized read of `POLY_REAL_THREADS` (see [`arbint_trace_on`] for the
/// cache discipline). When enabled (`=1`; `=0`/unset is OFF — see
/// [`crate::env::env_flag`]), `Thread.fork`/`Mutex`/`ConditionVar`
/// dispatch to the genuine OS-thread implementation (concurrency
/// increment 3d-3f); when disabled (the default) they fall through to the
/// prior single-thread stubs, keeping every existing workload — the
/// bootstrap, the self-bootstrapped REPL, HOL4, Isabelle — byte-identical.
/// Thread-attribute flag bits, stored (tagged) in the ML thread object's
/// FLAGS word (word 1, `threadIdFlags`). The encoding is shared between
/// upstream C (`processes.h:154-160`) and the SML basis, which reads and
/// writes the word directly (`Thread.sml:309-344`, `setIstateBits`):
/// bit 0 = accept broadcast interrupts; bits 1-2 = the interrupt state.
pub(crate) mod pflag {
    /// If set, accepts a broadcast interrupt (`EnableBroadcastInterrupt`).
    pub const BROADCAST: usize = 1;
    /// Ignore interrupts completely (`InterruptDefer`).
    pub const IGNORE: usize = 0;
    /// Handle synchronously (`InterruptSynch`) — delivered only at
    /// interruption points (`testInterrupt`, the condvar waits).
    pub const SYNCH: usize = 2;
    /// Handle asynchronously (`InterruptAsynch`) — delivered at safepoints.
    pub const ASYNCH: usize = 4;
    /// First handle asynchronously then switch to synch
    /// (`InterruptAsynchOnce`).
    pub const ASYNCH_ONCE: usize = 6;
    /// Mask of the interrupt-state bits.
    pub const INTMASK: usize = 6;
}

pub(crate) fn real_threads_enabled() -> bool {
    use std::sync::atomic::{AtomicU8, Ordering};
    static F: AtomicU8 = AtomicU8::new(0);
    match F.load(Ordering::Relaxed) {
        1 => true,
        2 => false,
        _ => {
            let on = crate::env::env_flag("POLY_REAL_THREADS");
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
            let on = crate::env::env_flag("JIT_TRACE_RETURNS");
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
            let on = crate::env::env_flag("JIT_TRACE_STORES");
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
            let on = crate::env::env_flag("JIT_TRACE_CALLS");
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
    /// The runtime heap is full and the requested object doesn't fit.
    /// Terminal BY DESIGN: GC-retry-on-full is deliberately NOT attempted
    /// (`do_alloc_ref`/`ALLOC_WORD_MEMORY` cache the allocation pointer
    /// across the call, so an in-call GC would corrupt the heap — see
    /// `MemorySpace::try_alloc`). The GC already fires between steps at
    /// the threshold; reaching this means the live set outgrew the heap.
    #[error(
        "heap exhausted: requested {requested_words} word(s), heap capacity \
         {capacity_words} words — raise POLYML_HEAP_BYTES (a byte count) and rerun"
    )]
    HeapExhausted {
        requested_words: usize,
        capacity_words: usize,
    },
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
    #[error("Thread.fork: OS thread spawn failed: {0}")]
    ThreadSpawnFailed(String),
    /// An untrusted image drove a dangerous pointer-follow that the
    /// typed-deref predicate rejected. This is the CLEAN, deterministic
    /// outcome of the `--untrusted` safe mode: a controlled halt instead of
    /// the UB (OOB read/write, wild jump, non-pointer deref) the follow
    /// would otherwise have caused. The `op` names the bytecode site.
    #[error("bad untrusted image: {op}: {why}")]
    BadImage { op: &'static str, why: DerefError },
}

impl InterpError {
    /// Build the terminal heap-exhaustion error for a failed
    /// `try_alloc`. `#[cold]`: this constructor only exists on the
    /// already-failing branch — the bump-allocation fast path is
    /// untouched.
    #[cold]
    fn heap_exhausted(requested_words: usize, space: &crate::space::MemorySpace) -> Self {
        Self::HeapExhausted {
            requested_words,
            capacity_words: space.capacity_words(),
        }
    }
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
    /// The `Arc`-shared runtime: the heap (`MemorySpace`), the scheduler
    /// (giant lock + thread registry), the GC trigger, and the
    /// image-mutable roots. Concurrency increment 3b: the heap MOVED from
    /// a per-`Interpreter` `alloc_space` field into `runtime.heap_mut()`,
    /// accessed only by the current ML-memory lock-holder. This
    /// `Interpreter` is now a per-thread *ThreadContext* over the shared
    /// `Runtime`; a forked thread gets a fresh `Interpreter` cloning this
    /// `Arc<Runtime>`.
    runtime: Arc<crate::sched::Runtime>,
    /// This thread's scheduler handle (in_ml / parked_roots / requests /
    /// exited). Registered in `runtime.sched.registry` while running.
    handle: Arc<crate::sched::ThreadHandle>,
    /// Cached raw handle to THIS thread's allocation nursery in the pool
    /// (parallelism P1). The Box-pinned `MemorySpace` never moves, so the
    /// handle is stable for the interpreter's life; the fast allocation
    /// path derefs it directly (no pool lock). `null` until a nursery is
    /// attached. Sound because — under the giant lock (P1) — exactly one
    /// mutator runs, and the collector holds the STW barrier before it
    /// touches any nursery, so this `&mut` is never aliased.
    nursery: *mut crate::space::MemorySpace,
    /// Whether `handle` has been pushed into the scheduler registry. Set
    /// on first `run_until`; idempotent across repeated calls.
    registered: bool,
    /// Whether this thread ALREADY holds the giant mutator lock when it
    /// enters `run_until` — so `run_until` must NOT acquire (it would
    /// deadlock or double-acquire) and must NOT release on exit. Set only
    /// by the forked-child entry, which acquires the lock itself (to safely
    /// retract its pre-published [`ForkRoots`] and read back the forwarded
    /// closure) BEFORE seeding its stack and running. Defaults `false`, so
    /// the single-threaded floor and the REPL driver are unaffected.
    holds_lock_on_entry: bool,
    /// A leaked `ThreadRoots` box published into `handle.parked_roots` on
    /// the LAST `run_until` exit (B2: a quiescent-but-registered thread must
    /// keep published roots so a peer's GC can forward its stack). Its
    /// pointer is referenced by the published `SendRoots` for the WHOLE
    /// quiescent window, so it must outlive that window — we keep ownership
    /// here and free it only when the slot is next retracted (the next
    /// acquire) or replaced (the next quiescent release). `None` when no
    /// publication is outstanding. Per-thread, so the floor never sets it.
    published_box: Option<*mut ThreadRoots>,
    /// Pre-computed GC threshold in words (= `heap.capacity *
    /// threshold_percent / 100`). 0 = "never auto-GC", set when either
    /// there is no heap or `POLYML_GC_THRESHOLD` is configured to a value
    /// outside (1..=99). Mirrored from `runtime.gc_trigger_words` so the
    /// hot-path check is a plain field read. On every step we compare
    /// `heap.used_words()` against this; cheaper than the previous
    /// `used * 100 >= cap * thresh`.
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
    /// RTS function table — used to dispatch `CALL_FAST_RTS<N>` opcodes.
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
    /// Per-thread bootstrap tail-call slot (the `PolyEndBootstrapMode`
    /// argument). When non-`ZERO`, the interpreter tail-calls it as a
    /// `unit -> 'a` closure on RTS return (see `rts_call`). This used to be
    /// a process-global static (`rts::BOOTSTRAP_TAIL_CALL`); it is now
    /// per-thread so a second thread cannot clobber another thread's pending
    /// tail call. The `poly_end_bootstrap_mode` RTS handler writes it via the
    /// `RtsContext` (seeded from / read back into this field by `rts_call`),
    /// and the GC forwards it as a per-thread root inside `ThreadRoots`.
    bootstrap_tail_call: PolyWord,
    /// Optional execution-profile collector. `None` = disabled (the
    /// hot path pays only a branch). Enable with
    /// [`enable_diagnostics`](Self::enable_diagnostics).
    diag: Option<DiagState>,
    /// JIT cache: maps code-object pointer (as `usize`) to a JIT'd
    /// native function. When `do_call`'s target is in this cache,
    /// it dispatches to the JIT'd version instead of interpreting.
    /// Empty = transparent fallthrough; never affects unjitted code.
    jit_cache: JitCache,
    /// Whole-region JIT registry (S3b): code-object address → native
    /// region root. Empty by default (the flag is off → the JIT registers
    /// nothing → the do_call hook is one never-taken branch). When the
    /// flag is on the JIT registers each compiled region root here at
    /// startup; do_call routes a call whose target is registered through
    /// the global region-dispatch boundary instead of setting up an
    /// interpreter frame. The default + --jit paths are byte-identical.
    region_registry: RegionRegistry,
    /// UNTRUSTED MODE (the one honest memory-safety caveat, task #96):
    /// `false` by default = TRUSTED. When `false` EVERY hardened deref site
    /// takes the exact current fast path — there is no extra check, no
    /// field read of `safe_spaces`, so the trusted bootstrap / REPL / HOL4 /
    /// Isabelle paths stay byte-identical and exactly as fast. When `true`
    /// (set via [`Interpreter::with_untrusted`] + the `--untrusted` CLI
    /// flag), each dangerous pointer-follow first validates against
    /// `safe_spaces` with the typed-deref predicate; a failure produces
    /// [`InterpError::BadImage`] (a clean halt), never UB. See
    /// [`safe_deref`].
    untrusted: bool,
    /// The live image spaces consulted by the typed-deref predicate IN
    /// UNTRUSTED MODE ONLY (the alloc space is read live; see
    /// `alloc_space_range`). Default-empty + never read in trusted mode.
    /// Populated by [`Interpreter::with_untrusted_spaces`].
    safe_spaces: SafeSpaces,
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

/// Type-erased `ThreadRoots` free thunk for the blocking-syscall park
/// (`crate::rts::RtsPark`), which cannot name the private type.
///
/// # Safety
/// `p` must be a pointer produced by `Box::into_raw` on a
/// `Box<ThreadRoots>` (i.e. `make_send_roots`'s `raw`), with no live
/// published alias remaining.
unsafe fn free_thread_roots_erased(p: *mut ()) {
    // SAFETY: per the contract above.
    unsafe { drop(Box::from_raw(p.cast::<ThreadRoots>())) }
}

/// The complete GC root-set of a *single* interpreter thread, captured
/// for one collection cycle.
///
/// Today the interpreter is single-threaded, so the collector drives a
/// registry of exactly ONE `ThreadRoots` (built from the live
/// `Interpreter` via [`ThreadRoots::capture`]). The structure exists so
/// that real multi-threading is a small diff: a 2nd thread becomes a
/// 2nd `ThreadRoots` pushed onto the registry the collector iterates —
/// the root-walk reads "for each thread-root-set in registry { ... }",
/// not "the one `self`".
///
/// The capture is *self-contained*: it owns the forwardable
/// `PolyWord` slots and the byte-offsets needed to rebuild the byte
/// pointers, plus raw write-back pointers into the owning interpreter's
/// fields. So forwarding ([`forward`](Self::forward)), the post-GC
/// fixup ([`apply_fixups`](Self::apply_fixups)), and the below-`sp`
/// scrub ([`scrub_below_sp`](Self::scrub_below_sp)) all operate purely
/// off this struct — no `&mut Interpreter` borrow held across the
/// collector, which is what lets a registry of many coexist later.
///
/// # Safety
/// Every raw pointer here aliases live `Interpreter` state. A
/// `ThreadRoots` is therefore only valid for the duration of the single
/// `gc()` call that built it, and the owning interpreter must not be
/// mutated through other paths while the capture is in use.
struct ThreadRoots {
    // ---- The live stack slice and its bounds (raw, for forward + scrub).
    /// Base of the thread's stack storage.
    stack_ptr: *mut PolyWord,
    /// Stack-pointer: live slots are `[sp, stack_len)`; `[0, sp)` is the
    /// free/garbage zone scrubbed after collection.
    sp: usize,
    /// Total stack length (one past the last slot).
    stack_len: usize,

    // ---- Forwardable PolyWord slots (mutated in place by `forward`).
    /// `code_start`, stashed as a PolyWord pointer to the code object.
    code_start_slot: PolyWord,
    /// Body-start of each call frame's code segment.
    frame_starts: Vec<PolyWord>,
    /// Body-start of each handler frame's owning code segment.
    handler_starts: Vec<PolyWord>,
    /// The exception packet (TAGGED(0) when none).
    exn_slot: PolyWord,
    /// The cached `Thread.self()` object (TAGGED(0) when unallocated).
    thread_obj_slot: PolyWord,
    /// The bootstrap tail-call slot (the `PolyEndBootstrapMode` arg;
    /// TAGGED(0) when none pending). PER-THREAD — it used to be forwarded
    /// once as a process-shared root, but it is the per-thread interpreter's
    /// `bootstrap_tail_call` field, so each thread forwards its own.
    bootstrap_tail_slot: PolyWord,

    // ---- Byte-offsets captured pre-GC, used to rebuild byte pointers.
    /// `pc - code_start`.
    pc_off: isize,
    /// `code_end - code_start`.
    code_end_off: isize,
    /// `frame.end - frame.start` for each frame.
    frame_offsets: Vec<isize>,
    /// `handler.end - handler.start` for each handler frame.
    handler_offsets: Vec<isize>,

    // ---- Write-back pointers into the owning interpreter's fields.
    code_start_dst: *mut *const u8,
    pc_dst: *mut *const u8,
    code_end_dst: *mut *const u8,
    frames_dst: *mut Vec<(*const u8, *const u8)>,
    handlers_dst: *mut Vec<(usize, *const u8, *const u8)>,
    exn_dst: *mut Option<PolyWord>,
    thread_obj_dst: *mut Option<PolyWord>,
    bootstrap_tail_dst: *mut PolyWord,
    /// Whether `thread_object` was `Some` (only then do we write it back —
    /// preserving the exact `if self.thread_object.is_some()` semantics).
    thread_obj_present: bool,
    /// Recent-call ring buffer to clear post-GC (not worth forwarding).
    recent_call_targets_dst: *mut [usize; 16],
    /// The owning thread's scheduler handle, so `forward` can refresh the
    /// handle's `thread_obj_addr` MIRROR (the handle→ML-thread-object
    /// direction, upstream `TaskData::threadObject`) with the FORWARDED
    /// address on every collection. An `Arc` clone (not a raw pointer) so
    /// the handle provably outlives the capture. The store is an atomic
    /// usize write — race-free even for a QUIESCED capture whose owning
    /// thread runs lock-free driver code (it never reads the mirror there).
    mirror_handle: Arc<crate::sched::ThreadHandle>,
    /// True when this capture was taken from a QUIESCED interpreter (a
    /// thread that left `run_until` with a TERMINAL result and emptied its
    /// transient roots before publishing — see `quiesce_roots`). A quiesced
    /// thread holds no live stack/frame/code roots, so the post-GC fixup
    /// MUST NOT write back the (null) code-bounds / (empty) frame+handler /
    /// (None) exn slots: between calls the OWNING thread's lock-free driver
    /// code re-seeds exactly those fields, and a write-back would race it.
    /// Only the identity roots (thread object, bootstrap tail) — which the
    /// driver never touches — are written back when quiesced. Defaults
    /// false (the normal resumable capture writes everything back).
    quiesced: bool,
}

impl ThreadRoots {
    /// Capture the root-set of one interpreter for the upcoming
    /// collection. Mirrors exactly the per-thread roots the legacy
    /// monolithic `gc()` enumerated for `self`.
    ///
    /// # Safety
    /// The returned capture aliases `interp`'s fields by raw pointer; it
    /// must be used only within the single `gc()` call and the
    /// interpreter must not be otherwise mutated meanwhile.
    fn capture(interp: &mut Interpreter) -> Self {
        // A null `code_start` marks a QUIESCED interpreter (left `run_until`
        // with a terminal result; `quiesce_roots` nulled its transient
        // roots). Its capture is root-free and its post-GC fixup must NOT
        // write back the code-bounds / frames / handlers / exn (the owning
        // thread's lock-free driver re-seeds those between calls — see the
        // `quiesced` field). Computing `offset_from` with a null base is
        // also avoided here (both null ⇒ 0, but we keep it explicit).
        let quiesced = interp.code_start.is_null();
        let (pc_off, code_end_off) = if quiesced {
            (0, 0)
        } else {
            // SAFETY: code_start non-null ⇒ pc/code_end derive from the same
            // code allocation.
            unsafe {
                (
                    interp.pc.offset_from(interp.code_start),
                    interp.code_end.offset_from(interp.code_start),
                )
            }
        };
        let frame_offsets: Vec<isize> = interp
            .frames
            .iter()
            .map(|(s, e)| unsafe { e.offset_from(*s) })
            .collect();
        let frame_starts: Vec<PolyWord> = interp
            .frames
            .iter()
            .map(|(s, _)| PolyWord::from_ptr(s.cast::<PolyWord>()))
            .collect();
        // Handler frames depth also saves code bounds that need
        // forwarding so the handler can restore them on RAISE_EX.
        let handler_offsets: Vec<isize> = interp
            .handler_frames_depth
            .iter()
            .map(|(_, s, e)| unsafe { e.offset_from(*s) })
            .collect();
        let handler_starts: Vec<PolyWord> = interp
            .handler_frames_depth
            .iter()
            .map(|(_, s, _)| PolyWord::from_ptr(s.cast::<PolyWord>()))
            .collect();

        Self {
            stack_ptr: interp.stack.as_mut_ptr(),
            sp: interp.sp,
            stack_len: interp.stack.len(),
            code_start_slot: PolyWord::from_ptr(interp.code_start.cast::<PolyWord>()),
            frame_starts,
            handler_starts,
            exn_slot: interp.exception_packet.unwrap_or(PolyWord::ZERO),
            thread_obj_slot: interp.thread_object.unwrap_or(PolyWord::ZERO),
            bootstrap_tail_slot: interp.bootstrap_tail_call,
            pc_off,
            code_end_off,
            frame_offsets,
            handler_offsets,
            code_start_dst: std::ptr::addr_of_mut!(interp.code_start),
            pc_dst: std::ptr::addr_of_mut!(interp.pc),
            code_end_dst: std::ptr::addr_of_mut!(interp.code_end),
            frames_dst: std::ptr::addr_of_mut!(interp.frames),
            handlers_dst: std::ptr::addr_of_mut!(interp.handler_frames_depth),
            exn_dst: std::ptr::addr_of_mut!(interp.exception_packet),
            thread_obj_dst: std::ptr::addr_of_mut!(interp.thread_object),
            bootstrap_tail_dst: std::ptr::addr_of_mut!(interp.bootstrap_tail_call),
            thread_obj_present: interp.thread_object.is_some(),
            recent_call_targets_dst: std::ptr::addr_of_mut!(interp.recent_call_targets),
            mirror_handle: Arc::clone(&interp.handle),
            quiesced,
        }
    }

    /// Forward every root slot this thread owns via the collector.
    /// (The SHARED roots — image mutable spaces, bootstrap-tail — are
    /// forwarded once by the caller, NOT here, since they are not
    /// per-thread.)
    ///
    /// # Safety
    /// `self.stack_ptr` must be valid for `self.stack_len` slots and the
    /// captured write-back pointers must still alias live interpreter
    /// state.
    unsafe fn forward(&mut self, c: &mut crate::gc::Collector<'_>) {
        // 1. Stack slots from sp..end. (Below sp is "free".)
        // Some of these are the handler save area which contains
        // raw PC addresses — those are NOT PolyWords pointing to
        // alloc objects, but the GC's is-in-from-space check
        // filters non-pointers, so it's safe to visit them all.
        for i in self.sp..self.stack_len {
            let slot = unsafe { self.stack_ptr.add(i) };
            // Stack slots may carry raw PC byte pointers whose
            // LSB happens to be 1; we can't filter by tagged-bit
            // alone, so use the byte-address variant.
            unsafe { c.forward_stack_slot(slot) };
        }
        // 2. Exception packet (might be None / TAGGED(0)).
        unsafe { c.forward(std::ptr::addr_of_mut!(self.exn_slot)) };
        // 3. code_start (as a PolyWord pointer to the code object).
        unsafe { c.forward(std::ptr::addr_of_mut!(self.code_start_slot)) };
        for fs in self.frame_starts.iter_mut() {
            unsafe { c.forward(fs as *mut _) };
        }
        for hs in self.handler_starts.iter_mut() {
            unsafe { c.forward(hs as *mut _) };
        }
        // 4b. Cached Thread.self() object.
        unsafe { c.forward(std::ptr::addr_of_mut!(self.thread_obj_slot)) };
        // 4b'. Refresh the handle's thread-object address MIRROR with the
        // forwarded address (or 0 when the object was never materialized).
        // The mirror is a plain usize (never traced by the GC) that is
        // re-derived here on EVERY collection, so it can never dangle
        // across one; readers (`PolyThreadBroadcastInterrupt`) only deref
        // it as the running mutator under the giant lock, mutually
        // exclusive with any collection.
        self.mirror_handle.thread_obj_addr.store(
            if self.thread_obj_present {
                self.thread_obj_slot.0
            } else {
                0
            },
            std::sync::atomic::Ordering::SeqCst,
        );
        // 4c. Bootstrap tail-call slot (PolyEndBootstrapMode arg). PER-THREAD.
        unsafe { c.forward(std::ptr::addr_of_mut!(self.bootstrap_tail_slot)) };
    }

    /// Scrub the below-`sp` (free/garbage) region to a safe tagged
    /// sentinel, closing the dangling-from-space-pointer window after
    /// the collector freed from-space. (See the long comment at the
    /// call site in `gc()`; history: the GC-soak findings + fix,
    /// commits 77b6141 + 8756419, task #109.)
    ///
    /// # Safety
    /// `self.stack_ptr` must be valid for at least `self.sp` slots.
    unsafe fn scrub_below_sp(&mut self) {
        // A QUIESCED capture (terminal `run_until` exit) holds an empty live
        // set; there are no above-sp roots that could have left dangling
        // from-space values below sp. Scrubbing would write the WHOLE stack
        // (sp == len), racing the owning thread's lock-free driver which
        // re-seeds that same stack between calls. Skip it — there is nothing
        // dangling to scrub on a quiesced thread.
        if self.quiesced {
            return;
        }
        for i in 0..self.sp {
            unsafe { self.stack_ptr.add(i).write(PolyWord::tagged(0)) };
        }
    }

    /// Write the forwarded slots back into the owning interpreter's
    /// fields (code bounds, frames, handlers, exception packet, thread
    /// object) and clear the recent-call ring buffer. Preserves the
    /// exact semantics of the legacy inline fixup block.
    ///
    /// # Safety
    /// The captured write-back pointers must still alias live
    /// interpreter state (i.e. the interpreter has not been moved or
    /// reallocated since `capture`).
    unsafe fn apply_fixups(&self) {
        // ---- A QUIESCED capture holds no live transient roots (empty
        // stack, null code, no frames/handlers/exn). The owning thread is
        // running lock-free DRIVER code between `run_until` calls; the
        // collector must NOT reach into that thread's `self` AT ALL — not the
        // transient roots (the driver re-seeds the stack/code/frames), and
        // (LOW, round 2) not even the identity roots (thread object +
        // bootstrap tail). Writing `*self.thread_obj_dst` / `*self.
        // bootstrap_tail_dst` from the collector is a data race on the
        // parked thread's `Interpreter` struct even if those particular
        // fields are not concurrently read — it is a write the owning thread
        // does not synchronise against. So for a quiesced capture we forward
        // the identity roots IN PLACE in the published box (done by
        // `forward`) but DEFER the write-back into `self` to the owning
        // thread's NEXT acquire (which retracts the slot under the giant lock,
        // then copies the forwarded identity values out of its stashed box —
        // see `apply_quiesced_identity_writeback`). That write-back happens
        // while the thread HOLDS the lock and the collector is done, so it is
        // race-free by construction, not by trusting the driver.
        if self.quiesced {
            return;
        }

        // ---- Identity roots (resumable capture): the thread object +
        // bootstrap tail-call slot are per-thread STATE. For a RESUMABLE
        // capture the owning thread is blocked inside `run_until` (parked at
        // a safepoint / blocking wait), so it is NOT mutating `self`; writing
        // them back in place is race-free.
        // Thread object: only write back if it was present (preserving
        // the original `if self.thread_object.is_some()` guard).
        if self.thread_obj_present {
            unsafe { *self.thread_obj_dst = Some(self.thread_obj_slot) };
        }
        // Bootstrap tail-call slot: write back the forwarded value
        // (mirrors the old unconditional `set_bootstrap_tail_call`).
        unsafe { *self.bootstrap_tail_dst = self.bootstrap_tail_slot };

        // Exception packet.
        unsafe {
            *self.exn_dst = if self.exn_slot.0 == 0 || self.exn_slot.is_tagged() {
                None
            } else {
                Some(self.exn_slot)
            };
        }
        // Code bounds.
        let new_code_start = self.code_start_slot.as_ptr::<PolyWord>().cast::<u8>();
        unsafe {
            *self.code_start_dst = new_code_start;
            // SAFETY: offsets remain valid; new code object has the same length.
            *self.pc_dst = new_code_start.offset(self.pc_off);
            *self.code_end_dst = new_code_start.offset(self.code_end_off);
        }
        // Frames.
        let frames = unsafe { &mut *self.frames_dst };
        for (i, fs) in self.frame_starts.iter().enumerate() {
            let new_start = fs.as_ptr::<PolyWord>().cast::<u8>();
            frames[i].0 = new_start;
            frames[i].1 = unsafe { new_start.offset(self.frame_offsets[i]) };
        }
        // Handler frames.
        let handlers = unsafe { &mut *self.handlers_dst };
        for (i, hs) in self.handler_starts.iter().enumerate() {
            let new_start = hs.as_ptr::<PolyWord>().cast::<u8>();
            handlers[i].1 = new_start;
            handlers[i].2 = unsafe { new_start.offset(self.handler_offsets[i]) };
        }
        // Recent-call ring buffer: clear; not worth forwarding.
        unsafe { (*self.recent_call_targets_dst).fill(0) };
    }

    /// Type-erased `forward` thunk stored in a [`crate::sched::SendRoots`]
    /// so the collector can forward a PARKED thread's roots without `sched`
    /// knowing the `ThreadRoots` layout.
    ///
    /// # Safety
    /// `roots` is a `*mut ThreadRoots` (a boxed capture leaked by the
    /// parking thread); `collector` is a `*mut crate::gc::Collector<'_>`.
    /// Both alias live state owned by the (blocked) parking thread / the
    /// active collector under the giant lock.
    unsafe fn forward_thunk(roots: *mut (), collector: *mut ()) {
        let roots = roots.cast::<ThreadRoots>();
        let c = collector.cast::<crate::gc::Collector<'_>>();
        // SAFETY: caller upholds the aliasing contract.
        unsafe { (*roots).forward(&mut *c) };
    }

    /// Type-erased `fixup` thunk (scrub below-sp + write forwarded slots
    /// back) for a parked thread's roots.
    ///
    /// # Safety
    /// `roots` is a `*mut ThreadRoots`; see [`forward_thunk`].
    unsafe fn fixup_thunk(roots: *mut ()) {
        let roots = roots.cast::<ThreadRoots>();
        // SAFETY: caller upholds the aliasing contract.
        unsafe {
            (*roots).scrub_below_sp();
            (*roots).apply_fixups();
        }
    }

    /// Audit THIS captured root-set's slots for residual from-space
    /// pointers (cross-stack GC audit, B3). Scans the FULL stack
    /// `[0, stack_len)` (below-sp is scrubbed to Tagged(0) by `fixup`, so a
    /// residual there means the scrub/forward missed it) plus the code
    /// bounds, frame/handler starts, exception packet, thread object, and
    /// bootstrap-tail slot. Returns the count of residual pointers found.
    ///
    /// # Safety
    /// `self.stack_ptr` must be valid for `stack_len` slots and the captured
    /// slots must alias the (frozen, parked) thread's live state.
    unsafe fn audit_residual(&self, from_lo: usize, from_hi: usize) -> usize {
        let in_old = |addr: usize| addr >= from_lo && addr < from_hi;
        let mut residual = 0usize;
        // Full stack — below-sp included (scrubbed on a clean run). A
        // QUIESCED capture has an empty live set and the owning thread's
        // lock-free driver may be re-seeding this stack concurrently, so we
        // do NOT read it (it roots nothing the GC must forward, and reading
        // it would race the driver). The identity-root checks below still
        // run.
        if !self.quiesced {
            for i in 0..self.stack_len {
                let v = unsafe { (*self.stack_ptr.add(i)).0 };
                if in_old(v) {
                    residual += 1;
                }
            }
        }
        // Forwardable PolyWord slots (post-fixup these hold the to-space
        // addresses; a from-space value means a missed forward).
        for w in [
            self.code_start_slot.0,
            self.exn_slot.0,
            self.thread_obj_slot.0,
            self.bootstrap_tail_slot.0,
        ] {
            if in_old(w) {
                residual += 1;
            }
        }
        for fs in &self.frame_starts {
            if in_old(fs.0) {
                residual += 1;
            }
        }
        for hs in &self.handler_starts {
            if in_old(hs.0) {
                residual += 1;
            }
        }
        residual
    }

    /// Type-erased audit thunk (see [`crate::sched::SendRoots::audit`]).
    ///
    /// # Safety
    /// `roots` is a `*mut ThreadRoots`; see [`forward_thunk`].
    unsafe fn audit_thunk(roots: *mut (), from_lo: usize, from_hi: usize) -> usize {
        let roots = roots.cast::<ThreadRoots>();
        // SAFETY: caller upholds the aliasing contract.
        unsafe { (*roots).audit_residual(from_lo, from_hi) }
    }
}

/// The pre-acquire root-set of a freshly-forked child thread (B1).
///
/// Between the parent's `register_thread_published` and the child's first
/// `acquire_ml_memory`, the child interpreter does not yet own a published
/// [`ThreadRoots`] (its stack is still being seeded). During that window the
/// ONLY live heap pointers the child holds are its starting closure
/// (`function`) and its `ThreadObject` (`thread_obj`). This tiny root-set is
/// published by the PARENT into the child handle's `parked_roots` slot
/// BEFORE registration, so the invariant "registered AND not-running ⟹
/// parked_roots is Some" holds from the instant of registration — there is
/// no GC window in which the collector skips the child's live closure.
///
/// The collector forwards these two slots in place; on its first acquire the
/// child reads the (possibly forwarded) values back out of this box and
/// seeds its stack with them, then reclaims the box.
struct ForkRoots {
    function: PolyWord,
    thread_obj: PolyWord,
    /// The child's scheduler handle, so `forward_thunk` can refresh its
    /// `thread_obj_addr` MIRROR with the forwarded thread-object address
    /// (a GC can move the object between fork and the child's first
    /// acquire; a targeted interrupt/broadcast in that window must not
    /// read a stale address).
    handle: Arc<crate::sched::ThreadHandle>,
}

impl ForkRoots {
    /// Forward the two child-initial slots via the collector.
    ///
    /// # Safety
    /// `roots` is a `*mut ForkRoots` (a leaked box owned by the forking
    /// parent / child); `collector` is a `*mut crate::gc::Collector<'_>`.
    unsafe fn forward_thunk(roots: *mut (), collector: *mut ()) {
        let roots = roots.cast::<ForkRoots>();
        let c = collector.cast::<crate::gc::Collector<'_>>();
        // SAFETY: caller upholds the aliasing contract; both slots are
        // ordinary forwardable PolyWords.
        unsafe {
            (*c).forward(std::ptr::addr_of_mut!((*roots).function));
            (*c).forward(std::ptr::addr_of_mut!((*roots).thread_obj));
            // Refresh the child handle's thread-object address mirror (see
            // the field doc): atomic usize store, re-derived every GC.
            // (Explicit reference per `dangerous_implicit_autorefs`.)
            let handle: &Arc<crate::sched::ThreadHandle> = &(*roots).handle;
            handle
                .thread_obj_addr
                .store((*roots).thread_obj.0, std::sync::atomic::Ordering::SeqCst);
        }
    }

    /// Fixup is a no-op: the slots are forwarded in place and the child
    /// reads them back directly. There is no below-sp region to scrub (the
    /// child has no live stack yet).
    ///
    /// # Safety
    /// `roots` is a `*mut ForkRoots`.
    unsafe fn fixup_thunk(_roots: *mut ()) {}

    /// Audit the two child-initial slots for residual from-space pointers.
    ///
    /// # Safety
    /// `roots` is a `*mut ForkRoots`.
    unsafe fn audit_thunk(roots: *mut (), from_lo: usize, from_hi: usize) -> usize {
        let roots = roots.cast::<ForkRoots>();
        let in_old = |addr: usize| addr >= from_lo && addr < from_hi;
        // SAFETY: caller upholds the aliasing contract.
        let (f, t) = unsafe { ((*roots).function.0, (*roots).thread_obj.0) };
        usize::from(in_old(f)) + usize::from(in_old(t))
    }
}

impl Drop for Interpreter {
    /// A `ThreadContext` leaving scope (its OS thread finished, or the host
    /// interpreter is torn down) MUST remove itself from the scheduler
    /// registry and drop any published roots — otherwise its `stack` `Box`
    /// is freed while its handle is still registered with
    /// `parked_roots == Some(stale capture)`, and the next peer's GC would
    /// scrub/forward the FREED stack (a use-after-free). Deregistering and
    /// clearing the slot under the scheduler lock makes "registered ⟹ the
    /// owning ThreadContext is alive" structural. The child-fork path
    /// already calls the appropriate exit (`exit_parked` / `exit_running`)
    /// explicitly before the interpreter
    /// drops; this Drop covers the test workers + the host interpreter +
    /// any early-return / panic-unwind exit, so no registered handle ever
    /// outlives its stack.
    fn drop(&mut self) {
        if self.registered {
            // exit_parked/exit_running remove us from the registry AND set
            // parked_roots = None under the scheduler lock, so a
            // concurrent collector either sees us (before) with valid
            // published roots (we are still alive here) or not at all
            // (after). Pick the exit path by whether we currently HOLD the
            // giant lock: a normal Drop runs after `run_until` released it
            // (in_ml == false → parked exit, must NOT clobber a peer's
            // `running`); a Drop while still holding it (e.g. a panic-unwind
            // mid-run, or a test that acquired but never released) must
            // clear `running` (running exit). This is the H2 discipline:
            // `running` is cleared IFF this thread actually holds it.
            if self.handle.in_ml.load(std::sync::atomic::Ordering::SeqCst) {
                self.runtime.exit_running(&self.handle);
            } else {
                self.runtime.exit_parked(&self.handle);
            }
            self.registered = false;
        }
        // Free any box published on the last quiescent release (its slot was
        // just cleared by exit_parked/exit_running, so it is unreferenced).
        self.free_published_box();
    }
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
        let rts = Arc::new(RtsTable::empty());
        let runtime = crate::sched::Runtime::new(None, 0, Arc::clone(&rts));
        Self {
            stack: vec![PolyWord::ZERO; stack_capacity].into_boxed_slice(),
            sp: stack_capacity,
            pc: start,
            code_start: start,
            code_end: end,
            frames: Vec::new(),
            runtime,
            handle: crate::sched::ThreadHandle::new(),
            nursery: std::ptr::null_mut(),
            registered: false,
            holds_lock_on_entry: false,
            published_box: None,
            gc_trigger_words: 0,
            handler_sp: stack_capacity, // past-the-end = no handler
            handler_frames_depth: Vec::new(),
            exception_packet: None,
            recent_call_targets: [0; 16],
            recent_call_idx: 0,
            image_mutable_roots: Vec::new(),
            thread_object: None,
            bootstrap_tail_call: PolyWord::ZERO,
            rts,
            _owned_code: Some(code),
            diag: None,
            jit_cache: JitCache::default(),
            region_registry: RegionRegistry::default(),
            untrusted: false,
            safe_spaces: SafeSpaces::default(),
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
        let rts = Arc::new(RtsTable::empty());
        let runtime = crate::sched::Runtime::new(None, 0, Arc::clone(&rts));
        Self {
            stack: vec![PolyWord::ZERO; stack_capacity].into_boxed_slice(),
            sp: stack_capacity,
            pc: start,
            code_start: start,
            code_end: end,
            frames: Vec::new(),
            runtime,
            handle: crate::sched::ThreadHandle::new(),
            nursery: std::ptr::null_mut(),
            registered: false,
            holds_lock_on_entry: false,
            published_box: None,
            gc_trigger_words: 0,
            handler_sp: stack_capacity,
            handler_frames_depth: Vec::new(),
            exception_packet: None,
            recent_call_targets: [0; 16],
            recent_call_idx: 0,
            image_mutable_roots: Vec::new(),
            thread_object: None,
            bootstrap_tail_call: PolyWord::ZERO,
            rts,
            _owned_code: None,
            diag: None,
            jit_cache: JitCache::default(),
            region_registry: RegionRegistry::default(),
            untrusted: false,
            safe_spaces: SafeSpaces::default(),
        }
    }

    /// Build a per-thread `ThreadContext` for a FORKED thread (3d). Shares
    /// the parent's `Arc<Runtime>` (heap, RTS, scheduler), takes the
    /// pre-registered child `handle`, and seeds the child's cached
    /// `Thread.self()` object so `Thread.setLocal`/`getLocal` work. The
    /// child gets its OWN stack + JIT cache + bookkeeping; PC/code bounds
    /// are set by the caller via `jit_set_code_segment_to_closure`.
    fn for_child_thread(
        runtime: Arc<crate::sched::Runtime>,
        handle: Arc<crate::sched::ThreadHandle>,
        thread_obj: PolyWord,
        untrusted: bool,
        safe_spaces: SafeSpaces,
    ) -> Self {
        let stack_capacity = 1024 * 1024;
        let rts = Arc::clone(&runtime.rts);
        let gc_trigger_words = runtime.gc_trigger_words;
        // Copy the shared image-mutable roots so the child's `gc()` (which
        // reads `self.image_mutable_roots`) scans the same global-namespace
        // regions the main thread does. They are the same heap regions
        // (process-global), just mirrored into each thread's Vec.
        let image_mutable_roots: Vec<(*const PolyWord, usize)> = runtime
            .image_roots
            .lock()
            .unwrap()
            .0
            .iter()
            .map(|(p, l)| (p.0, *l))
            .collect();
        Self {
            stack: vec![PolyWord::ZERO; stack_capacity].into_boxed_slice(),
            sp: stack_capacity,
            pc: std::ptr::null(),
            code_start: std::ptr::null(),
            code_end: std::ptr::null(),
            frames: Vec::new(),
            runtime,
            handle,
            // A forked child inherits the SAME single nursery in P1 (the
            // pool has one space; the child bump-allocates from it under
            // the giant lock, exactly as before). P2 gives each thread its
            // own nursery handle here.
            nursery: std::ptr::null_mut(),
            registered: false,
            holds_lock_on_entry: false,
            published_box: None,
            gc_trigger_words,
            handler_sp: stack_capacity,
            handler_frames_depth: Vec::new(),
            exception_packet: None,
            recent_call_targets: [0; 16],
            recent_call_idx: 0,
            image_mutable_roots,
            thread_object: Some(thread_obj),
            bootstrap_tail_call: PolyWord::ZERO,
            rts,
            _owned_code: None,
            diag: None,
            jit_cache: JitCache::default(),
            region_registry: RegionRegistry::default(),
            // A forked child INHERITS the parent's trust posture (P0 fix:
            // it used to hard-code trusted, so the first fork in an
            // --untrusted session silently de-fanged the safe mode for
            // that child). The SafeSpaces ranges are the shared image +
            // alloc spaces, identical for every thread over one Runtime.
            untrusted,
            safe_spaces,
        }
    }

    /// Test/diagnostic accessor: clone the shared `Arc<Runtime>` (heap +
    /// scheduler) so a test can spawn a second `ThreadContext` over the
    /// same runtime and exercise real cross-thread GC.
    #[doc(hidden)]
    #[must_use]
    pub fn runtime_arc(&self) -> Arc<crate::sched::Runtime> {
        Arc::clone(&self.runtime)
    }

    /// Test/diagnostic constructor: build a fresh `ThreadContext` sharing
    /// an existing `Arc<Runtime>` (the heap + scheduler), with a fresh
    /// scheduler handle. PC/code bounds are unset; the caller seeds the
    /// stack + sets the code segment (e.g. via
    /// [`set_code_segment_to_code_obj`](Self::set_code_segment_to_code_obj))
    /// then drives `run_until`. Used by the concurrency integration test to
    /// run a real second mutator thread over a shared heap.
    #[doc(hidden)]
    #[must_use]
    pub fn for_shared_runtime_test(runtime: Arc<crate::sched::Runtime>) -> Self {
        let handle = crate::sched::ThreadHandle::new();
        // H1 (structural): do NOT bare-register here. A bare register leaves
        // the handle in the registry as "registered, not-running,
        // parked_roots == None" until the worker's first `run_until` acquire
        // — exactly the generic-register TOCTOU window. Instead leave
        // `registered == false`; the first `acquire_running` (inside the
        // first `run_until`) registers-and-acquires atomically.
        let mut me = Self::for_child_thread(
            runtime,
            handle,
            PolyWord::tagged(0),
            false,
            SafeSpaces::default(),
        );
        me.thread_object = None;
        me.registered = false;
        me
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

    /// Whole-region JIT (S3b): register a native region root for a code
    /// object. After registration, a `do_call` whose target closure's
    /// code object is `code_obj_ptr` is routed through the global region-
    /// dispatch boundary instead of the interpreter frame setup. Only
    /// called by `polyml-jit` when the `WHOLE_REGION_JIT` flag is on; the
    /// registry is empty otherwise.
    pub fn install_region(&mut self, code_obj_ptr: usize, entry: RegionEntry) {
        self.region_registry.insert(code_obj_ptr, entry);
    }

    /// `true` iff any region root is registered (so the cheap do_call
    /// guard can skip the lookup entirely when the flag is off).
    #[must_use]
    pub fn has_regions(&self) -> bool {
        !self.region_registry.is_empty()
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

    /// Mutable accessor to the shared heap for the JIT-bridge
    /// trampolines. Returns `None` if no heap has been configured (the
    /// JIT-`TUPLE` etc. paths will then fail gracefully rather than UB).
    ///
    /// # Concurrency
    /// Sound because the caller (the JIT trampoline) runs synchronously
    /// inside `run_until`, i.e. while this thread holds ML memory and is
    /// the sole heap accessor (the giant-lock discipline).
    #[doc(hidden)]
    pub fn jit_alloc_space_mut(&mut self) -> Option<&mut MemorySpace> {
        self.alloc_space_mut()
    }

    /// This thread's cached nursery handle, lazily resolved from the pool
    /// on first use (P1: the single shared nursery, index 0). Returns
    /// `null` if no nursery has been installed. The handle is stable for
    /// the interpreter's life (Box-pinned), so this fetch happens at most
    /// once per thread.
    #[inline]
    fn nursery_ptr(&mut self) -> *mut MemorySpace {
        if self.nursery.is_null() && self.runtime.nursery_count() > 0 {
            self.nursery = self.runtime.nursery_handle(0);
        }
        self.nursery
    }

    /// Mutable access to this thread's allocation nursery. Only valid while
    /// this thread holds ML memory (inside `run_until`'s acquire/release
    /// bracket) — under the giant lock (P1) exactly one mutator runs and
    /// the collector holds the STW barrier before touching any nursery, so
    /// this is never aliased.
    #[inline]
    fn alloc_space_mut(&mut self) -> Option<&mut MemorySpace> {
        let p = self.nursery_ptr();
        // SAFETY: `p` is either null (→ None) or a stable Box-pinned
        // nursery this thread exclusively accesses under the lock.
        unsafe { p.as_mut() }
    }

    /// Shared accessor to this thread's nursery (read-only path). Takes
    /// `&self`, so it does NOT cache — it reads the already-resolved handle
    /// (populated by the first `alloc_space_mut`/`nursery_ptr` on the hot
    /// path) or falls back to a pool lookup. The single-threaded floor
    /// resolves the handle at attach time, so the fallback is cold.
    #[inline]
    fn alloc_space_ref(&self) -> Option<&MemorySpace> {
        let p = if self.nursery.is_null() {
            if self.runtime.nursery_count() > 0 {
                self.runtime.nursery_handle(0)
            } else {
                std::ptr::null_mut()
            }
        } else {
            self.nursery
        };
        // SAFETY: `p` is null (→ None) or a stable Box-pinned nursery this
        // thread reads under the lock; we hand out a shared ref only.
        unsafe { p.as_ref() }
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

    /// Read this thread's bootstrap tail-call slot (without clearing).
    /// Used by the JIT RTS trampoline to seed an `RtsContext` so a
    /// `PolyEndBootstrapMode` call routed through JIT'd code records its
    /// pending tail call in the same per-thread slot the interpreter reads.
    #[doc(hidden)]
    #[must_use]
    pub fn bootstrap_tail_call(&self) -> PolyWord {
        self.bootstrap_tail_call
    }

    /// Write this thread's bootstrap tail-call slot. Counterpart of
    /// [`bootstrap_tail_call`](Self::bootstrap_tail_call) for the JIT RTS
    /// trampoline to write the slot back after dispatching an RTS function.
    #[doc(hidden)]
    pub fn set_bootstrap_tail_call(&mut self, w: PolyWord) {
        self.bootstrap_tail_call = w;
    }

    /// Observe and clear this thread's bootstrap tail-call slot. Returns
    /// `Some(closure)` if `PolyEndBootstrapMode` recorded a `unit -> 'a`
    /// function to tail-call on RTS return, else `None`. Replaces the old
    /// process-global `rts::take_bootstrap_tail_call`; the slot is now the
    /// per-thread `self.bootstrap_tail_call` field.
    fn take_bootstrap_tail_call(&mut self) -> Option<PolyWord> {
        let w = self.bootstrap_tail_call;
        if w.0 == 0 {
            None
        } else {
            self.bootstrap_tail_call = PolyWord::ZERO;
            Some(w)
        }
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

    /// Attach an RTS table. Builder pattern. Propagates the table into
    /// the shared `Runtime` (builders run single-threaded before any
    /// fork, so the `Arc<Runtime>` has exactly one reference here).
    #[must_use]
    pub fn with_rts(mut self, rts: Arc<RtsTable>) -> Self {
        self.rts = Arc::clone(&rts);
        // SAFETY-ADJACENT: single Arc ref at build time.
        if let Some(rt) = Arc::get_mut(&mut self.runtime) {
            rt.rts = rts;
        }
        self
    }

    /// Attach an allocation space. The interpreter will bump-allocate
    /// new objects (closures, tuples, refs) from the shared heap. Sized
    /// once at attach time — runtime growth is a future concern.
    ///
    /// Builder pattern; returns the interpreter for chaining. The heap
    /// is stored in the shared `Runtime` (increment 3b), accessed only
    /// by the current ML-memory lock-holder.
    #[must_use]
    pub fn with_alloc_space(mut self, space: MemorySpace) -> Self {
        let cap = space.capacity_words();
        let thresh = usize::from(crate::rts::gc_threshold_percent().unwrap_or(80));
        // gc_trigger_words = cap * thresh / 100. Saturate at 0 if
        // cap is so large that the multiply would overflow.
        self.gc_trigger_words = cap.checked_mul(thresh).map_or(0, |x| x / 100);
        // Install the nursery into the pool + cache this thread's handle
        // (P1: the one nursery). `install_nursery` takes the pool lock, so
        // it works whether or not we are the sole Arc holder.
        self.nursery = self.runtime.install_nursery(space);
        if let Some(rt) = Arc::get_mut(&mut self.runtime) {
            rt.gc_trigger_words = self.gc_trigger_words;
        }
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
        // Mirror into the shared Runtime so a forked thread's collector
        // can scan the same shared image roots. (The main thread's gc()
        // reads its own `image_mutable_roots`; both Vecs hold the same
        // entries.)
        self.runtime.add_image_root(ptr, len_words);
        self
    }

    /// Switch this interpreter into UNTRUSTED mode (the opt-in safe mode
    /// for explicitly-foreign images). When `on` is `true`, every hardened
    /// pointer-follow validates against the typed-deref predicate before the
    /// unsafe use; a failure halts cleanly with [`InterpError::BadImage`].
    /// DEFAULT is `false` (trusted): the hardened sites take the exact
    /// current fast path, byte-identical.
    ///
    /// You almost always want to pair this with [`Self::with_untrusted_spaces`]
    /// so the predicate has the live image spaces to validate against.
    #[must_use]
    pub fn with_untrusted(mut self, on: bool) -> Self {
        self.untrusted = on;
        self
    }

    /// Register the loaded image's spaces (immutable / mutable / code) as
    /// the live spaces the typed-deref predicate validates pointers against
    /// IN UNTRUSTED MODE. Has no effect on the trusted fast path (the
    /// predicate is never consulted there). The alloc space is NOT passed
    /// here — it is read live on each check (the GC swaps it).
    ///
    /// Pass each space's body base pointer + its `used_words`. A null/empty
    /// space is ignored.
    #[must_use]
    pub fn with_untrusted_spaces(
        mut self,
        immutable: (*const PolyWord, usize),
        mutable: (*const PolyWord, usize),
        code: (*const PolyWord, usize),
    ) -> Self {
        self.safe_spaces.push_image_space(immutable.0, immutable.1);
        self.safe_spaces.push_image_space(mutable.0, mutable.1);
        self.safe_spaces.push_image_space(code.0, code.1);
        self
    }

    /// Whether this interpreter is in untrusted (safe) mode.
    #[must_use]
    pub fn is_untrusted(&self) -> bool {
        self.untrusted
    }

    /// The live alloc-space range, read FRESH (the Cheney GC swaps the
    /// alloc space wholesale, so a cached bound would dangle). `None` if no
    /// alloc space is attached. Used ONLY by the untrusted-mode predicate.
    #[inline]
    fn alloc_space_range(&self) -> Option<SpaceRange> {
        let space = self.alloc_space_ref()?;
        let base = space
            .iter()
            .next()
            .map_or(std::ptr::null::<PolyWord>(), std::ptr::from_ref);
        let base = if base.is_null() {
            // An empty alloc space: derive the storage start so a pointer
            // freshly bump-allocated (after this check) still falls inside.
            space.storage_bytes().as_ptr().cast::<PolyWord>()
        } else {
            base
        };
        // The membership check uses the *capacity* end, not the used end:
        // an object validated here may have been allocated up to the
        // capacity bound, and the predicate's header-fit check needs the
        // full live extent. Using `used_words` would spuriously reject a
        // just-allocated object near the bump pointer.
        let cap = space.capacity_words();
        // SAFETY: base + cap is one-past-the-end of the alloc storage.
        let end = unsafe { base.add(cap) };
        Some(SpaceRange { start: base, end })
    }

    /// Validate a word as an object pointer in untrusted mode: steps
    /// (a)–(c) of the predicate (tag, space-membership, header sanity).
    /// Maps a failure to [`InterpError::BadImage`] tagged with the opcode
    /// `op`. Called ONLY behind `if self.untrusted`.
    #[inline]
    fn validate_obj(&self, w: PolyWord, op: &'static str) -> Result<ValidObj, InterpError> {
        let alloc = self.alloc_space_range();
        self.safe_spaces
            .validate_obj(w, alloc)
            .map_err(|why| InterpError::BadImage { op, why })
    }

    /// Build the live-space snapshot handed to RTS functions IN UNTRUSTED
    /// MODE (so the code-constant family — the R1 OOB-write site and its
    /// siblings — can validate a resolved code object before the deref).
    /// Returns `None` in trusted mode (the RTS path stays byte-identical).
    /// Must be called BEFORE borrowing `alloc_space_mut` for the RtsContext
    /// (it reads the alloc range immutably).
    fn rts_safe_spaces(&self) -> Option<crate::rts::RtsSafeSpaces> {
        if !self.untrusted {
            return None;
        }
        let mut ranges: Vec<(usize, usize)> = self.safe_spaces.image_ranges_usize();
        // P2b: a valid heap pointer may live in ANY pool nursery (a peer
        // thread's allocation shared through a ref), so the untrusted
        // validation ranges must cover the whole pool, not just ours.
        for i in 0..self.runtime.nursery_count() {
            let h = self.runtime.nursery_handle(i);
            // SAFETY: pinned pool nursery; we only read its range bounds
            // (start/capacity), racing nothing under the giant lock.
            let r = unsafe { (*h).as_ptr_range() };
            ranges.push((r.start as usize, r.end as usize));
        }
        Some(crate::rts::RtsSafeSpaces { ranges })
    }

    /// Untrusted-mode convenience: a container reference points INTO this
    /// interpreter's own stack (emitted by `STACK_CONTAINER_B`), not into a
    /// heap space. Validate that `container_ref` is a stack-internal pointer
    /// and that `container_ref + n` (the slot the op will touch) stays
    /// within the live stack. Returns the validated `*const PolyWord` base.
    /// Called ONLY behind `if self.untrusted`.
    #[inline]
    fn untrusted_container_ptr(
        &self,
        container_ref: PolyWord,
        n: usize,
        op: &'static str,
    ) -> Result<*const PolyWord, InterpError> {
        let bits = container_ref.0;
        // Must be word-aligned and non-tagged (a stack address).
        if container_ref.is_tagged() || bits & (std::mem::size_of::<usize>() - 1) != 0 {
            return Err(InterpError::BadImage {
                op,
                why: DerefError::NotAPointer,
            });
        }
        let base = self.stack.as_ptr();
        // SAFETY: forming the one-past-end bound of the owned stack Box.
        let end = unsafe { base.add(self.stack.len()) };
        let p = bits as *const PolyWord;
        // p must be in [base, end), and p + n must be < end (room for the
        // touched slot). Use address comparisons; n is bounded by checking
        // the touched slot lies strictly within the stack.
        if p < base || p >= end {
            return Err(InterpError::BadImage {
                op,
                why: DerefError::NotInSpace,
            });
        }
        // SAFETY: p is within the stack allocation; forming p+n for the
        // compare is in-bounds-or-one-past for the allocation since we
        // bound-check it against `end` immediately.
        let touched = unsafe { p.add(n) };
        if touched >= end {
            return Err(InterpError::BadImage {
                op,
                why: DerefError::IndexOutOfBounds,
            });
        }
        Ok(p)
    }

    /// Whether it is safe to dereference word0 of `w` as a mutable cell in
    /// the CURRENT mode. In TRUSTED mode this is just the existing
    /// `is_data_ptr` + alignment gate (byte-identical). In UNTRUSTED mode it
    /// ALSO requires space-membership + a header with at least one word, so
    /// a wild-but-aligned pointer falls through to the op's safe non-pointer
    /// branch instead of an OOB read/write. Used by the atomic / mutex
    /// builtins, whose `if is_data_ptr {…} else {safe}` shape already has a
    /// no-deref fallback.
    #[inline]
    fn word0_deref_ok(&self, w: PolyWord) -> bool {
        if !w.is_data_ptr() || w.0 & (std::mem::size_of::<usize>() - 1) != 0 {
            return false;
        }
        if self.untrusted {
            // Must be in a live space with room for word0 + its length word.
            match self.validate_obj(w, "ATOMIC") {
                Ok(v) => v.n_words >= 1,
                Err(_) => false,
            }
        } else {
            true
        }
    }

    /// Untrusted-mode convenience: validate `w` as an object, bounds-check
    /// field `idx`, and read it. Returns the field value or a clean
    /// [`InterpError::BadImage`]. Called ONLY behind `if self.untrusted`.
    #[inline]
    fn untrusted_field(
        &self,
        w: PolyWord,
        idx: usize,
        op: &'static str,
    ) -> Result<PolyWord, InterpError> {
        let v = self.validate_obj(w, op)?;
        v.check_word_index(idx)
            .map_err(|why| InterpError::BadImage { op, why })?;
        // SAFETY: validated pointer + in-bounds index.
        Ok(unsafe { *v.ptr.add(idx) })
    }

    /// Request a stop-the-world GC and run it as the collector (3c).
    ///
    /// Ports upstream's "any thread crossing the threshold requests a
    /// collection, every other thread parks at its safepoint, the
    /// requester collects" model. Sets `gc_requested`, waits until every
    /// peer has parked (`threads_in_heap == 1`), then runs `self.gc()`
    /// (which now also forwards every parked thread's published roots),
    /// clears the flag, and wakes the parked mutators.
    ///
    /// Single-threaded: `threads_in_heap == 1` already (just us), so the
    /// wait returns immediately and this is byte-identical to a direct
    /// `self.gc()`.
    fn request_gc_collect(&mut self) -> Option<usize> {
        let runtime = Arc::clone(&self.runtime);
        let handle = Arc::clone(&self.handle);
        if runtime.parallel {
            // PARALLEL (P4): collector ELECTION. If a peer is already
            // collecting we lose, park as a safepoint peer (roots
            // published across the wait), and return None — the caller
            // retries its allocation against the freshly-evacuated pool.
            let (raw, send) = self.make_send_roots();
            // SAFETY: `send` aliases live `self`; the box outlives the
            // (possible) park and `self` is not mutated while parked.
            let r = unsafe { runtime.request_gc_parallel(&handle, send, || self.gc()) };
            unsafe { drop(Box::from_raw(raw)) };
            return r.flatten();
        }
        runtime.request_gc(&handle, || self.gc())
    }

    /// Park at a safepoint because a peer requested a GC (3c). Captures
    /// this thread's roots, boxes them, publishes them under the handle's
    /// `parked_roots` slot (the collector's only route to our stack), and
    /// blocks until the collection finishes. On wake the published box is
    /// reclaimed (the collector already wrote our forwarded slots back via
    /// the `fixup` thunk while we were parked).
    ///
    /// The capture aliases `self`'s fields by raw pointer and stays valid
    /// across the park because the box outlives the wait and `self` is not
    /// mutated meanwhile (we are blocked).
    fn safepoint_park(&mut self) {
        let runtime = Arc::clone(&self.runtime);
        let handle = Arc::clone(&self.handle);
        let (raw, send) = self.make_send_roots();
        // SAFETY: `send` aliases live `self` state; the box outlives the
        // park, and `self` is not mutated while we are blocked. The
        // publish-before-release ordering is enforced inside
        // `Runtime::safepoint_park` (publish under the giant lock, THEN
        // clear `running`), so the collector never aliases a running stack.
        unsafe {
            runtime.safepoint_park(&handle, send);
            // Reclaim the box (collector already applied fixups in place).
            drop(Box::from_raw(raw));
        }
    }

    /// Cooperatively yield the giant lock at a safepoint so a waiting peer
    /// can run (3f). Publishes roots across the yield. No-op fast path
    /// when there is only one registered thread (the common case): we are
    /// the sole runner, so yielding would just re-acquire ourselves.
    fn cooperative_yield(&mut self) {
        // PARALLEL (P4): peers genuinely run concurrently — there is no
        // lock to hand over, so the cooperative yield is deleted (skip
        // before the registry_len probe, which takes the sched mutex).
        if self.runtime.parallel {
            return;
        }
        if self.runtime.registry_len() <= 1 {
            return;
        }
        let runtime = Arc::clone(&self.runtime);
        let handle = Arc::clone(&self.handle);
        let (raw, send) = self.make_send_roots();
        // SAFETY: as in `safepoint_park` — `send` aliases live `self`; the
        // box outlives the yield window; `yield_ml_memory` publishes before
        // releasing and retracts on re-acquire.
        unsafe {
            runtime.yield_ml_memory(&handle, send);
            drop(Box::from_raw(raw));
        }
    }

    /// Check + act on this thread's pending interrupt/kill request (3f) at
    /// a SAFEPOINT, honoring the thread's `InterruptState` attribute —
    /// i.e. exactly upstream's asynchronous-request check
    /// (`Processes::ProcessAsynchRequests`, processes.cpp:1622-1683,
    /// reached via the `InterruptCode`-poisoned stack-limit trap,
    /// interpreter.cpp:149). KILL ends the run by returning a sentinel
    /// (regardless of the flags word, like upstream's `KillException`);
    /// INTERRUPT is delivered only when the state is Asynch/AsynchOnce,
    /// and left PENDING (not consumed) under Defer/Synch.
    fn check_thread_requests(&mut self) -> Result<StepResult, InterpError> {
        Ok(self
            .process_asynch_requests()?
            .unwrap_or(StepResult::Continue))
    }

    /// Read word `idx` of an ML thread object, defensively (and validated
    /// in untrusted mode, mirroring `reset_mutex_word`'s posture — the
    /// object word can be image-controlled under the experimental
    /// real-threads + `--untrusted` combo). `None` = not a plausible
    /// thread object.
    fn thread_obj_read(&self, obj: PolyWord, idx: usize) -> Option<PolyWord> {
        if !obj.is_data_ptr() || obj.0 & (std::mem::size_of::<usize>() - 1) != 0 {
            return None;
        }
        if self.untrusted {
            let vo = self.validate_obj(obj, "THREAD_OBJ").ok()?;
            vo.check_word_index(idx).ok()?;
        }
        // ATOMIC load (P3): thread-object protocol words (flags word 1,
        // requestCopy word 3) are read cross-thread (BroadcastInterrupt/
        // CondVarWake/testInterrupt), so a plain read races the owner's
        // write. Relaxed is right — the request-delivery happens-before is
        // carried by the handle's AtomicU8 `requests` + the sched block_gen,
        // not by this ML-visible mirror. Not a hot path (safepoint reads).
        // SAFETY: data-pointer + aligned; trusted (runtime/compiler-built
        // thread object, >= 5 words) OR untrusted-validated in-space.
        let p = unsafe { obj.as_ptr::<PolyWord>().cast_mut().add(idx) };
        let bits = unsafe { Self::atomic_word(p).load(std::sync::atomic::Ordering::Relaxed) };
        Some(PolyWord::from_bits(bits))
    }

    /// Write word `idx` of an ML thread object (same guards as
    /// [`Self::thread_obj_read`]). The caller must be the running mutator
    /// (giant lock held) — thread-object words are ML-mutable shared heap
    /// state, and the lock is their mutual exclusion.
    fn thread_obj_write(&self, obj: PolyWord, idx: usize, w: PolyWord) {
        if !obj.is_data_ptr() || obj.0 & (std::mem::size_of::<usize>() - 1) != 0 {
            return;
        }
        if self.untrusted {
            let Ok(vo) = self.validate_obj(obj, "THREAD_OBJ") else {
                return;
            };
            if vo.check_word_index(idx).is_err() {
                return;
            }
        }
        // ATOMIC store (P3): the mirror of `thread_obj_read` — a plain
        // store would race a cross-thread read. Relaxed (see the read).
        // SAFETY: as in `thread_obj_read`.
        let p = unsafe { obj.as_ptr::<PolyWord>().cast_mut().add(idx) };
        unsafe { Self::atomic_word(p).store(w.0, std::sync::atomic::Ordering::Relaxed) };
    }

    /// The untagged FLAGS word of an ML thread object (word 1,
    /// `threadIdFlags`), or `None` if unreadable.
    fn thread_obj_flags(&self, obj: PolyWord) -> Option<usize> {
        let w = self.thread_obj_read(obj, 1)?;
        #[allow(clippy::cast_sign_loss)]
        w.is_tagged().then(|| w.untag() as usize)
    }

    /// THIS thread's current attribute flags, read FRESH from its ML
    /// thread object each time (the SML `setAttributes` writes the word
    /// directly via `RunCall.storeWord`, so no cached copy can be
    /// trusted). A thread with no materialized object (only the root can
    /// be in that state — forked children get theirs at fork) defaults to
    /// upstream's root-thread attributes, `PFLAG_BROADCAST|PFLAG_ASYNCH`
    /// (processes.cpp:1313).
    fn own_thread_flags(&self) -> usize {
        self.thread_object
            .and_then(|t| self.thread_obj_flags(t))
            .unwrap_or(pflag::BROADCAST | pflag::ASYNCH)
    }

    /// Overwrite THIS thread's flags word (the AsynchOnce → Synch
    /// downgrade, `ProcessAsynchRequests` processes.cpp:1644-1650).
    fn set_own_thread_flags(&self, flags: usize) {
        if let Some(t) = self.thread_object {
            #[allow(clippy::cast_possible_wrap)]
            self.thread_obj_write(t, 1, PolyWord::tagged(flags as isize));
        }
    }

    /// Clear THIS thread's ML-visible `requestCopy` word (word 3,
    /// `threadIdIntRequest`) after consuming a request — upstream's
    /// `threadObject->requestCopy = TAGGED(0)`.
    fn clear_own_request_copy(&self) {
        if let Some(t) = self.thread_object {
            self.thread_obj_write(t, 3, PolyWord::tagged(0));
        }
    }

    /// Map an ML thread OBJECT to its scheduler handle via the tagged
    /// thread id stored in the object's word 0 — upstream's `threadRef`
    /// C-identity slot ("Not used by ML", processes.h:84) read by
    /// `TaskForIdentifier` (processes.cpp:257). A tagged id is GC-immune
    /// (it moves with the object; an address would not survive a
    /// collection). `None` = no such live thread (the id is 0/absent, or
    /// the thread exited and left the registry — upstream zeroes the
    /// `threadRef` cell on exit, processes.cpp:1398, with the same
    /// observable result: `interrupt`/`kill` return false, `isActive`
    /// false).
    fn handle_for_thread_object(&self, obj: PolyWord) -> Option<Arc<crate::sched::ThreadHandle>> {
        let id_w = self.thread_obj_read(obj, 0)?;
        if !id_w.is_tagged() || id_w.untag() <= 0 {
            return None;
        }
        #[allow(clippy::cast_sign_loss)]
        let id = id_w.untag() as u64;
        self.runtime
            .registry_snapshot()
            .into_iter()
            .find(|h| h.thread_id == id)
    }

    /// Port of `Processes::MakeRequest` (processes.cpp:813-826): set the
    /// target's request flag ("we don't override a request to kill by an
    /// interrupt request" → `fetch_max`), mirror it into the ML-visible
    /// `requestCopy` word so the SML `testInterrupt` fast-path sees it,
    /// and wake the target if it is blocked (upstream
    /// `p->threadLock.Signal()` + `InterruptCode()`; our blocked waits sit
    /// on the block-event condvar, and the safepoint poll is the
    /// `InterruptCode` analogue). Caller must be the running mutator.
    fn make_thread_request(
        &self,
        target: &Arc<crate::sched::ThreadHandle>,
        target_obj: PolyWord,
        req: u8,
    ) {
        use std::sync::atomic::Ordering;
        let prev = target.requests.fetch_max(req, Ordering::SeqCst);
        if prev < req {
            self.thread_obj_write(target_obj, 3, PolyWord::tagged(isize::from(req)));
            self.runtime.notify_block_event();
        }
    }

    /// Port of `Processes::ProcessAsynchRequests` (processes.cpp:1622-1683)
    /// for THIS thread: deliver a pending KILL unconditionally; deliver a
    /// pending INTERRUPT only when the current interrupt state is
    /// Asynch/AsynchOnce (AsynchOnce downgrades the state to Synch before
    /// delivery); leave it PENDING (do not consume!) under Defer/Synch.
    /// Returns `Some(step)` when a request was delivered (the raise already
    /// unwound the stack to the handler, or the KILL sentinel ends the
    /// run) — the caller must NOT push an RTS result in that case — and
    /// `None` when nothing was delivered.
    fn process_asynch_requests(&mut self) -> Result<Option<StepResult>, InterpError> {
        use crate::sched::request;
        use std::sync::atomic::Ordering;
        match self.handle.requests.load(Ordering::SeqCst) {
            // kRequestKill → KillException, regardless of the flags word.
            request::KILL => {
                self.handle.requests.store(request::NONE, Ordering::SeqCst);
                // P0 exit semantics: a KILL that is part of a PolyFinish
                // broadcast must carry the EXIT CODE — this safepoint check
                // runs BEFORE the step's finish-flag check, so without
                // reading the flag here the main thread would consume the
                // broadcast and return a generic 0 while the real code
                // sits in the flag.
                let code = crate::rts::finish_requested().unwrap_or(0);
                Ok(Some(StepResult::Returned(PolyWord::tagged(code))))
            }
            request::INTERRUPT => {
                let flags = self.own_thread_flags();
                let intbits = flags & pflag::INTMASK;
                // Defer (PFLAG_IGNORE) / Synch: not deliverable here —
                // leave the request pending (do NOT consume it).
                if intbits == pflag::ASYNCH || intbits == pflag::ASYNCH_ONCE {
                    if intbits == pflag::ASYNCH_ONCE {
                        // "Set this so from now on it's synchronous."
                        self.set_own_thread_flags((flags & !pflag::INTMASK) | pflag::SYNCH);
                    }
                    // Consume the request — CAS so a racing escalation to
                    // KILL (upstream holds schedLock here; we don't) is
                    // never lost: if it fires between the load above and
                    // here, skip delivery and let the next poll see KILL.
                    if self
                        .handle
                        .requests
                        .compare_exchange(
                            request::INTERRUPT,
                            request::NONE,
                            Ordering::SeqCst,
                            Ordering::SeqCst,
                        )
                        .is_ok()
                    {
                        self.clear_own_request_copy();
                        return self.raise_interrupt().map(Some);
                    }
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    /// Port of `Processes::TestSynchronousRequests` (processes.cpp:1688-
    /// 1722) for THIS thread: deliver a pending KILL unconditionally;
    /// deliver a pending INTERRUPT only when the state is exactly Synch.
    /// Same `Some`/`None` contract as [`Self::process_asynch_requests`].
    fn test_synchronous_requests(&mut self) -> Result<Option<StepResult>, InterpError> {
        use crate::sched::request;
        use std::sync::atomic::Ordering;
        match self.handle.requests.load(Ordering::SeqCst) {
            request::KILL => {
                self.handle.requests.store(request::NONE, Ordering::SeqCst);
                // P0: carry the PolyFinish exit code, as in
                // process_asynch_requests above.
                let code = crate::rts::finish_requested().unwrap_or(0);
                Ok(Some(StepResult::Returned(PolyWord::tagged(code))))
            }
            request::INTERRUPT => {
                let intbits = self.own_thread_flags() & pflag::INTMASK;
                if intbits == pflag::SYNCH
                    && self
                        .handle
                        .requests
                        .compare_exchange(
                            request::INTERRUPT,
                            request::NONE,
                            Ordering::SeqCst,
                            Ordering::SeqCst,
                        )
                        .is_ok()
                {
                    self.clear_own_request_copy();
                    return self.raise_interrupt().map(Some);
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    /// Concurrency RTS calls that need the full `ThreadContext` (3d/3e/3f).
    /// Returns `Ok(Some(result))` if handled here, `Ok(None)` to fall
    /// through to the generic single-thread stub. `args` excludes the
    /// stub; for `rtsCallFullN` calls `args[0]` is the threadId.
    #[allow(clippy::too_many_lines)] // one arm per upstream RTS entry, each cited
    fn try_thread_rts(
        &mut self,
        name: &str,
        args: &[PolyWord],
    ) -> Result<Option<StepResult>, InterpError> {
        // Real OS-thread concurrency is OPT-IN via POLY_REAL_THREADS=1.
        //
        // Rationale (faithfulness): some images (notably the
        // self-bootstrapped `polyexport` REPL) FORK an internal
        // console/compiler thread on startup and only worked because our
        // `fork` was a dormant no-op stub (so that thread never ran and the
        // main thread did all the work). Making `fork` genuinely spawn an OS
        // thread INVERTS that architecture and breaks those images. So real
        // threading is gated: default = the prior single-thread stubs
        // (byte-identical bootstrap/REPL/HOL4/Isabelle); set
        // POLY_REAL_THREADS=1 to enable genuine fork/mutex/condvar (the
        // 2-thread mutex demo sets it). When OFF, every branch below falls
        // through (`Ok(None)`) to the generic single-thread stub.
        if !real_threads_enabled() {
            return Ok(None);
        }
        match name {
            // ForkThread(threadId, function, attrs, stack): actually spawn
            // an OS thread running `function` (a `unit -> unit` closure)
            // over a fresh ThreadContext sharing this Arc<Runtime>. The
            // ML-passed `attrs` word and `stack` size are stored into the
            // child's thread object (flags word 1, mlStackSize word 4),
            // exactly as upstream ForkThread (processes.cpp:1515-1517).
            "PolyThreadForkThread" => {
                let function = args.get(1).copied().unwrap_or(PolyWord::tagged(0));
                // Defensive defaults mirror the SML fork wrapper's own
                // (Thread.sml:471-472): no broadcast + InterruptSynch,
                // unlimited stack.
                #[allow(clippy::cast_possible_wrap)]
                let attrs = args
                    .get(2)
                    .copied()
                    .unwrap_or(PolyWord::tagged(pflag::SYNCH as isize));
                let stack = args.get(3).copied().unwrap_or(PolyWord::tagged(0));
                let thread_obj = self.fork_thread(function, attrs, stack)?;
                Ok(Some(self.push_continue(thread_obj)?))
            }
            // MutexBlock(threadId, mutex): the SML lock() couldn't acquire
            // a contended mutex; block until SOME mutex-unlock event, then
            // return (SML retries lock). Releasing ML memory (publishing
            // roots) around the wait mirrors upstream WaitInfinite.
            //
            // SINGLE-THREADED fallback: if no peer is alive (registry has
            // only us), there is no one to wake us — blocking would
            // deadlock and the old stub just reset+returned. So fall
            // through to the generic single-thread stub (which resets the
            // mutex so the SML retry-loop terminates). This keeps the
            // single-threaded REPL/bootstrap behaviour byte-identical.
            "PolyThreadMutexBlock" => {
                if self.runtime.registry_len() <= 1 {
                    return Ok(None);
                }
                // Upstream MutexBlock (processes.cpp:397-438): "We mustn't
                // block if we have been interrupted, and are processing
                // interrupts asynchronously, or we've been killed." (A
                // pending SYNCH/Deferred interrupt does NOT skip the wait.)
                let req = self
                    .handle
                    .requests
                    .load(std::sync::atomic::Ordering::SeqCst);
                let intbits = self.own_thread_flags() & pflag::INTMASK;
                let skip_wait = req == crate::sched::request::KILL
                    || (req == crate::sched::request::INTERRUPT
                        && (intbits == pflag::ASYNCH || intbits == pflag::ASYNCH_ONCE));
                if !skip_wait {
                    // LOST-WAKEUP FENCE (parallel): the owner can unlock —
                    // reset the word AND bump the generation — in the window
                    // between the SML lock-attempt failure and this block.
                    // Sample the generation FIRST, then RE-CHECK the mutex
                    // word: an unlock that landed entirely before the
                    // sample shows as an unlocked word (return; the SML
                    // loop retries the lock); one that lands after shows
                    // as a generation bump. Either way the wait cannot
                    // sleep through it. (Upstream's per-thread threadLock
                    // signal has the same effect structurally.)
                    let since = self.runtime.block_gen();
                    let still_locked = args.get(1).is_none_or(|mutex| {
                        if self.word0_deref_ok(*mutex) {
                            let p = mutex.as_ptr::<PolyWord>();
                            // SAFETY: word0_deref_ok validated word 0;
                            // atomic read (shared heap word).
                            unsafe { Self::heap_read(p).0 != PolyWord::tagged(0).0 }
                        } else {
                            true
                        }
                    });
                    if still_locked {
                        self.block_on_event_since(since);
                    }
                }
                // Upstream delivers the pending asynch interrupt/kill right
                // after MutexBlock returns, via the InterruptCode-poisoned
                // stack-limit trap → HandleStackOverflow →
                // ProcessAsynchRequests (interpreter.cpp:141-156). Deliver
                // it here — the SML caller sees the exception INSTEAD of a
                // unit return, exactly like upstream.
                if let Some(sr) = self.process_asynch_requests()? {
                    return Ok(Some(sr));
                }
                Ok(Some(self.push_continue(PolyWord::tagged(0))?))
            }
            // MutexUnlock(threadId, mutex): a contended unlock — reset the
            // mutex to unlocked and wake all blocked waiters.
            "PolyThreadMutexUnlock" => {
                if let Some(mutex) = args.get(1) {
                    self.reset_mutex_word(*mutex)?;
                }
                self.runtime.notify_block_event();
                Ok(Some(self.push_continue(PolyWord::tagged(0))?))
            }
            // CondVarWait(threadId, mutex): ATOMICALLY RELEASE the condvar's
            // internal mutex, then block until a wake event. The mutex
            // release is load-bearing (upstream WaitInfinite,
            // processes.cpp:533-560: `AtomicallyReleaseMutex` + waking any
            // threads blocked on that mutex): the SML `waitAgain` holds
            // `lock` across this call and RE-LOCKS it after we return
            // (Thread.sml:592-594) — without the release it would deadlock
            // against ITSELF on the re-lock (found by the condvar-interrupt
            // test; latent before, since nothing exercised ConditionVar
            // under real threads).
            //
            // SINGLE-THREADED fallback as for MutexBlock: with no peer to
            // wake us, defer to the generic noop stub (return immediately)
            // — preserving the prior single-thread behaviour exactly.
            "PolyThreadCondVarWait" => {
                if self.runtime.registry_len() <= 1 {
                    return Ok(None);
                }
                // LOST-WAKEUP FENCE (parallel): sample the generation
                // BEFORE releasing the condvar's internal mutex. The SML
                // waker must hold that mutex to mark our wait-list flag and
                // call CondVarWake, so every wake destined for us bumps the
                // generation AFTER this sample. We then wait past
                // `since + 1` — our own notify below accounts for exactly
                // one bump — so a destined wake that lands anywhere in the
                // release→wait window makes the wait return immediately
                // (the SML innerWait re-checks its flag; spurious returns
                // are benign). Sampling inside block_on_event instead left
                // a concurrent-peer window: upstream's strict-alternation
                // condvar ping-pong (diff-corpus-threads) hung in ~100
                // handoffs under POLY_PARALLEL.
                let since = self.runtime.block_gen();
                if let Some(mutex) = args.get(1) {
                    self.reset_mutex_word(*mutex)?;
                }
                // Wake any thread blocked (in MutexBlock) on the mutex we
                // just released — upstream signals each such waiter's
                // threadLock; ours re-check on the global block event.
                self.runtime.notify_block_event();
                // Upstream WaitInfinite: "Wait until we're woken up. Don't
                // block if we have been interrupted or killed" — ANY
                // pending request skips the wait; the exception is NOT
                // raised here (the SML `innerWait` calls `testInterrupt()`
                // after every return, which delivers the pending Synch
                // interrupt — that is how `Thread.interrupt` cancels a
                // ConditionVar.wait).
                if self
                    .handle
                    .requests
                    .load(std::sync::atomic::Ordering::SeqCst)
                    == crate::sched::request::NONE
                {
                    self.block_on_event_since(since + 1);
                }
                // The InterruptCode-poisoned trap right after the RTS
                // return (see the MutexBlock arm): delivers only when the
                // raw caller runs Asynch (the basis' doWait switched to
                // Synch first, so its path defers to testInterrupt).
                if let Some(sr) = self.process_asynch_requests()? {
                    return Ok(Some(sr));
                }
                Ok(Some(self.push_continue(PolyWord::tagged(0))?))
            }
            // CondVarWaitUntil(threadId, mutex, absTime): the TIMED variant —
            // upstream processes.cpp WaitUntil. `absTime` is an absolute
            // Time.time (microseconds, tagged or boxed). Returns unit either
            // way (wake vs timeout is indistinguishable to the caller; the
            // SML wrapper re-checks its wait list). Was a zero3 stub, which
            // made ConditionVar.waitUntil spin-hang under real threads.
            "PolyThreadCondVarWaitUntil" => {
                if self.runtime.registry_len() <= 1 {
                    return Ok(None);
                }
                // Atomically release the condvar's internal mutex + wake its
                // blocked waiters, exactly as the untimed arm above
                // (upstream WaitUntilTime has the same preamble) — including
                // the pre-release generation sample (the lost-wakeup fence;
                // see PolyThreadCondVarWait).
                let since = self.runtime.block_gen();
                if let Some(mutex) = args.get(1) {
                    self.reset_mutex_word(*mutex)?;
                }
                self.runtime.notify_block_event();
                let abs_us = args
                    .get(2)
                    .and_then(|w| crate::rts::ml_int_as_i64_pub(None, *w))
                    .unwrap_or(0);
                let now_us = i64::try_from(
                    std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .map(|d| d.as_micros())
                        .unwrap_or(0),
                )
                .unwrap_or(i64::MAX);
                #[allow(clippy::cast_sign_loss)]
                let millis = (abs_us.saturating_sub(now_us).max(0) as u64).div_ceil(1000);
                // Upstream WaitUntilTime has the same requests guard as
                // WaitInfinite (processes.cpp:577-588): any pending request
                // skips the wait; delivery is the SML testInterrupt's job.
                if self
                    .handle
                    .requests
                    .load(std::sync::atomic::Ordering::SeqCst)
                    == crate::sched::request::NONE
                {
                    self.block_on_event_timeout_since(since + 1, millis);
                }
                if let Some(sr) = self.process_asynch_requests()? {
                    return Ok(Some(sr));
                }
                Ok(Some(self.push_continue(PolyWord::tagged(0))?))
            }
            // CondVarWake(thread): wake the TARGET thread if it can still
            // consume the signal. Port of Processes::WakeThread
            // (processes.cpp:590-611): succeed only when the target exists
            // AND (has no pending request, OR its pending interrupt is
            // being IGNOREd) — "we define that if a thread is interrupted
            // before it is signalled then it raises Interrupt", so an
            // interrupted waiter reports false and the SML wakeOne moves on
            // to the next waiter. Our wake is a global block-event
            // broadcast (waiters re-check their SML wait list; spurious
            // wakes are benign), so only the RETURN VALUE is per-target.
            "PolyThreadCondVarWake" => {
                let target = args.first().copied().unwrap_or(PolyWord::ZERO);
                let ok = match self.handle_for_thread_object(target) {
                    Some(h) => {
                        let req = h.requests.load(std::sync::atomic::Ordering::SeqCst);
                        let intbits = self.thread_obj_flags(target).unwrap_or(0) & pflag::INTMASK;
                        if req == crate::sched::request::NONE
                            || (req == crate::sched::request::INTERRUPT && intbits == pflag::IGNORE)
                        {
                            self.runtime.notify_block_event();
                            true
                        } else {
                            false
                        }
                    }
                    None => false,
                };
                Ok(Some(self.push_continue(PolyWord::tagged(isize::from(ok)))?))
            }
            // InterruptThread(thread): targeted `Thread.interrupt`. Port of
            // PolyThreadInterruptThread (processes.cpp:628-641): map the ML
            // thread object to its handle (word-0 tagged id, upstream's
            // threadRef identity slot) and MakeRequest(kRequestInterrupt).
            // Returns false ("Thread does not exist" in SML) when the
            // thread already exited — upstream zeroes threadRef on exit.
            "PolyThreadInterruptThread" => {
                let target = args.first().copied().unwrap_or(PolyWord::ZERO);
                let ok = self.handle_for_thread_object(target).is_some_and(|h| {
                    self.make_thread_request(&h, target, crate::sched::request::INTERRUPT);
                    true
                });
                Ok(Some(self.push_continue(PolyWord::tagged(isize::from(ok)))?))
            }
            // KillThread(thread): targeted `Thread.kill`. Port of
            // PolyThreadKillThread (processes.cpp:643-652); the KILL is
            // delivered at the target's next safepoint / interruption point
            // regardless of its interrupt state (upstream KillException).
            "PolyThreadKillThread" => {
                let target = args.first().copied().unwrap_or(PolyWord::ZERO);
                let ok = self.handle_for_thread_object(target).is_some_and(|h| {
                    self.make_thread_request(&h, target, crate::sched::request::KILL);
                    true
                });
                Ok(Some(self.push_continue(PolyWord::tagged(isize::from(ok)))?))
            }
            // IsActive(thread): true iff the thread is still registered
            // (upstream PolyThreadIsActive, processes.cpp:617-625 — a
            // thread leaves TaskForIdentifier's reach on exit, exactly as
            // exit removes ours from the registry).
            "PolyThreadIsActive" => {
                let target = args.first().copied().unwrap_or(PolyWord::ZERO);
                let active = self
                    .handle_for_thread_object(target)
                    .is_some_and(|h| !h.exited.load(std::sync::atomic::Ordering::SeqCst));
                Ok(Some(
                    self.push_continue(PolyWord::tagged(isize::from(active)))?,
                ))
            }
            // BroadcastInterrupt(threadId): interrupt every thread whose
            // flags word has the PFLAG_BROADCAST bit — including the
            // caller. Port of Processes::BroadcastInterrupt
            // (processes.cpp:795-811). The handle→object direction uses the
            // `thread_obj_addr` mirror (upstream TaskData::threadObject),
            // refreshed by the collector on every GC; we are the running
            // mutator (giant lock held, peers parked, no GC in flight), so
            // reading each peer's flags word / writing its requestCopy is
            // race-free. A thread whose object was never materialized
            // (mirror == 0: only the root before its first Thread.self())
            // is skipped — it cannot have set EnableBroadcastInterrupt.
            "PolyThreadBroadcastInterrupt" => {
                for h in self.runtime.registry_snapshot() {
                    let addr = h.thread_obj_addr.load(std::sync::atomic::Ordering::SeqCst);
                    if addr == 0 {
                        continue;
                    }
                    let obj = PolyWord(addr);
                    if self.thread_obj_flags(obj).unwrap_or(0) & pflag::BROADCAST != 0 {
                        self.make_thread_request(&h, obj, crate::sched::request::INTERRUPT);
                    }
                }
                Ok(Some(self.push_continue(PolyWord::tagged(0))?))
            }
            // TestInterrupt(threadId): the explicit interruption point
            // (`Thread.testInterrupt`). Port of PolyThreadTestInterrupt
            // (processes.cpp:667-692): TestSynchronousRequests (delivers a
            // pending interrupt iff the state is Synch; Kill always), then
            // ProcessAsynchRequests ("if we have just switched from
            // deferring interrupts this guarantees that any deferred
            // interrupts will be handled now" — but only once the state was
            // switched OUT of Defer: under Defer/IGNORE neither test
            // delivers and the request stays pending).
            "PolyThreadTestInterrupt" => {
                if let Some(sr) = self.test_synchronous_requests()? {
                    return Ok(Some(sr));
                }
                if let Some(sr) = self.process_asynch_requests()? {
                    return Ok(Some(sr));
                }
                Ok(Some(self.push_continue(PolyWord::tagged(0))?))
            }
            // MaxStackSize(threadId, newSize): store the attribute and
            // enforce the immediate over-limit case. Port of
            // PolyThreadMaxStackSize (processes.cpp:700-731): store into
            // mlStackSize (word 4); if the new limit is non-zero and the
            // CURRENT stack usage already exceeds it, raise the Interrupt
            // exception (upstream raise_exception0(EXC_interrupt)).
            // ENFORCEMENT GAP (documented, not overreached): upstream also
            // re-checks the cap on every later stack GROWTH via the
            // stack-limit trap; our per-thread stack is a fixed-capacity
            // buffer that never grows, so the only ongoing "limit" is that
            // fixed capacity — the attribute round-trips (get/setAttributes)
            // and the immediate check is faithful.
            "PolyThreadMaxStackSize" => {
                let new_size = args.get(1).copied().unwrap_or(PolyWord::tagged(0));
                if let Some(t) = self.thread_object {
                    self.thread_obj_write(t, 4, new_size);
                }
                let new_words = crate::rts::ml_int_as_i64_pub(None, new_size).unwrap_or(0);
                let current_words = i64::try_from(self.stack.len() - self.sp).unwrap_or(i64::MAX);
                if new_words > 0 && current_words > new_words {
                    return self.raise_interrupt().map(Some);
                }
                Ok(Some(self.push_continue(PolyWord::tagged(0))?))
            }
            // KillSelf(threadId): the thread function finished (Thread.exit).
            // End this thread's run loop by returning to its driver, which
            // releases ML memory + marks the handle exited.
            "PolyThreadKillSelf" => Ok(Some(StepResult::Returned(PolyWord::tagged(0)))),
            // WaitForSignal(threadId): the basis SIGNAL THREAD (its sole
            // caller) blocks here until a signal / weak-marker arrives. We do
            // NOT route SML signals (SIGINT raises `Interrupt` via
            // `crate::interrupt`, not this queue), so the signal thread has
            // nothing to deliver — it must PARK, not spin. The old
            // immediate-return stub turned `sigThread`'s
            // `waitForSig(); …; sigThread()` into a BUSY-LOOP that, once real
            // `fork` actually spawned the signal thread, pinned the giant lock
            // and hung the REPL at startup (the documented "fork inverts the
            // no-op stub architecture" hazard). Mark this handle a DAEMON (so
            // `wait_for_children` does not block on it at exit — upstream
            // abandons the signal thread when the root returns) and park
            // forever; a spurious wake (some unrelated `block_wake` bump)
            // simply re-parks. Reusing `block_on_event` means the parked
            // signal thread keeps its place in the GC handshake (it publishes
            // roots before releasing ML memory), so collection stays sound.
            "PolyWaitForSignal" => {
                self.handle
                    .is_daemon
                    .store(true, std::sync::atomic::Ordering::SeqCst);
                // P0: the daemon must be KILLABLE. An unconditional
                // `loop { block_on_event() }` never checks `requests`, so
                // any shutdown design that broadcasts KILL (PolyFinish,
                // Session teardown, root-halt) would deadlock on the
                // signal thread forever. Check for a pending KILL after
                // every wake; a KILL ends this thread's run loop exactly
                // like PolyThreadKillSelf. INTERRUPT is intentionally NOT
                // delivered here (upstream's signal thread is not an
                // interrupt target; broadcastInterrupt skips it via the
                // EnableBroadcastInterrupt flag).
                loop {
                    self.block_on_event();
                    let req = self
                        .handle
                        .requests
                        .load(std::sync::atomic::Ordering::SeqCst);
                    if req == crate::sched::request::KILL {
                        return Ok(Some(StepResult::Returned(PolyWord::tagged(0))));
                    }
                }
            }
            _ => Ok(None),
        }
    }

    /// Timed sibling of [`Self::block_on_event`]: wait for an event OR the
    /// millisecond deadline, whichever first, with the giant lock released
    /// (roots published) across the wait. The caller (ConditionVar's
    /// `waitUntil`) does not need to distinguish wake from timeout — the
    /// SML side re-checks its own wait list either way.
    fn block_on_event_timeout(&mut self, millis: u64) {
        let since = self.runtime.block_gen();
        self.block_on_event_timeout_since(since, millis);
    }

    /// [`Self::block_on_event_timeout`] with a caller-sampled generation
    /// (the lost-wakeup fence — see [`Self::block_on_event_since`]).
    fn block_on_event_timeout_since(&mut self, since: u64, millis: u64) {
        let runtime = Arc::clone(&self.runtime);
        let handle = Arc::clone(&self.handle);
        let (raw, send) = self.make_send_roots();
        // SAFETY: exactly as in `block_on_event` — `send` aliases live
        // `self`; the box outlives the wait; roots are published under the
        // giant lock BEFORE `running` clears.
        unsafe {
            runtime.release_ml_memory_publishing(&handle, send);
        }
        runtime.block_until_event_timeout(since, millis);
        runtime.reacquire_ml_memory(&handle);
        // SAFETY: reacquire set parked_roots = None; no live alias remains.
        unsafe {
            drop(Box::from_raw(raw));
        }
    }

    /// Block this thread until a mutex-unlock / condvar-wake event, with
    /// the giant lock RELEASED (and roots published) across the wait —
    /// the structural enforcement of "a blocking path publishes roots
    /// before releasing ML memory". Re-acquires the lock on wake.
    fn block_on_event(&mut self) {
        // Sample the event generation BEFORE releasing the lock, so a wake
        // racing in the release→wait window is not lost.
        let since = self.runtime.block_gen();
        self.block_on_event_since(since);
    }

    /// [`Self::block_on_event`] with a CALLER-sampled generation. Under
    /// `POLY_PARALLEL` a peer runs CONCURRENTLY with the RTS preamble that
    /// precedes the block (e.g. CondVarWait's atomic mutex release), so
    /// the generation must be sampled BEFORE the point at which a peer's
    /// wake can become destined for us — sampling inside `block_on_event`
    /// leaves a lost-wakeup window (found by the threaded differential
    /// oracle: upstream's strict-alternation condvar ping-pong hangs).
    fn block_on_event_since(&mut self, since: u64) {
        let runtime = Arc::clone(&self.runtime);
        let handle = Arc::clone(&self.handle);
        let (raw, send) = self.make_send_roots();
        // SAFETY: `send` aliases live `self`; the box outlives the wait and
        // `self` is not mutated while blocked. `release_ml_memory_publishing`
        // publishes the roots under the giant lock BEFORE clearing
        // `running`, so a collector that runs while we wait can scan our
        // stack and never aliases a running stack.
        unsafe {
            runtime.release_ml_memory_publishing(&handle, send);
        }
        // Wait for an event (giant lock released — only the block condvar).
        runtime.block_until_event(since);
        // Re-acquire the giant lock (retracts our published roots).
        runtime.reacquire_ml_memory(&handle);
        // SAFETY: reacquire set parked_roots = None, so no live alias to
        // the box remains; reclaim it.
        unsafe {
            drop(Box::from_raw(raw));
        }
    }

    /// Fork a real OS thread running `function` (a `unit -> unit` closure)
    /// over a fresh `ThreadContext` sharing this `Arc<Runtime>` (3d).
    /// Mirrors `Processes::ForkThread` + `IntTaskData::InitStackFrame`
    /// (processes.cpp:1501, interpreter.cpp:115): allocate the child's
    /// ThreadObject, push ONLY the closure onto the child stack, set PC to
    /// the closure's code body, and run. The SML `threadFunction` calls
    /// `Thread.exit` (→ PolyThreadKillSelf) at the end, ending the run.
    ///
    /// Returns the child's ThreadObject (the SML `thread` value).
    fn fork_thread(
        &mut self,
        function: PolyWord,
        attrs: PolyWord,
        stack: PolyWord,
    ) -> Result<PolyWord, InterpError> {
        if crate::env::env_flag("POLY_THREAD_TRACE") {
            eprintln!("[parent] fork_thread function={function:?}");
        }
        // Allocate the child's ThreadObject in the shared heap (we hold ML
        // memory). 9-word mutable object per processes.h:83-95, with the
        // ML-passed attribute flags + max-stack words stored exactly as
        // upstream ForkThread (processes.cpp:1515-1517).
        let thread_obj = self.alloc_thread_object_value(attrs, stack)?;

        // The child shares the Runtime; build its handle.
        let runtime = Arc::clone(&self.runtime);
        let child_handle = crate::sched::ThreadHandle::new();

        // Thread IDENTITY, both directions (see the ThreadHandle field
        // docs): word 0 of the thread object (upstream's threadRef
        // C-identity slot, "Not used by ML") gets the tagged handle id —
        // GC-immune, so `PolyThreadInterruptThread`/`KillThread`/`IsActive`
        // can map the object back to the handle across collections; and
        // the handle's `thread_obj_addr` mirror gets the object's current
        // address (refreshed by every GC via ForkRoots/ThreadRoots) so
        // `PolyThreadBroadcastInterrupt` can reach the object from the
        // handle.
        #[allow(clippy::cast_possible_wrap)]
        self.thread_obj_write(
            thread_obj,
            0,
            PolyWord::tagged(child_handle.thread_id as isize),
        );
        child_handle
            .thread_obj_addr
            .store(thread_obj.0, std::sync::atomic::Ordering::SeqCst);

        // ---- Close the fork TOCTOU (B1): publish the child's INITIAL
        // roots BEFORE registering, so the invariant "registered AND
        // not-running ⟹ parked_roots is Some" holds from the instant the
        // child becomes visible to the collector. The child's only live
        // heap pointers before it acquires the lock are its starting
        // closure (`function`) and its ThreadObject (`thread_obj`); we box
        // them as a `ForkRoots` and publish that.
        //
        // We are the running mutator (we hold the giant lock), so no GC can
        // fire between this publish and the spawn; and once the child is
        // registered-with-Some, a GC fired by US (the parent) before the
        // child runs WILL forward the child's closure via the ForkRoots
        // (exercised by the TOCTOU stress test).
        let fork_roots = Box::new(ForkRoots {
            function,
            thread_obj,
            handle: Arc::clone(&child_handle),
        });
        let fork_raw = Box::into_raw(fork_roots);
        let fork_send = crate::sched::SendRoots {
            ptr: fork_raw.cast::<()>(),
            forward: ForkRoots::forward_thunk,
            fixup: ForkRoots::fixup_thunk,
            audit: ForkRoots::audit_thunk,
        };
        *child_handle.parked_roots.lock().unwrap() = Some(fork_send);
        // SAFETY: parked_roots is Some (just published) and the child is not
        // yet in_ml; the published ForkRoots aliases `function`/`thread_obj`
        // which are GC-stable (forwarded in place) until the child retracts
        // them on its first acquire.
        unsafe { runtime.register_thread_published(&child_handle) };

        // The raw ForkRoots box pointer crosses to the child; it reads back
        // the (possibly forwarded) closure + thread object after it acquires
        // the lock, then reclaims the box. Wrap as a usize so it is Send.
        let fork_raw_bits = fork_raw as usize;
        let child_handle_for_thread = Arc::clone(&child_handle);
        // P0: the child inherits the parent's trust posture (see
        // for_child_thread) — an --untrusted session's forks stay untrusted.
        let child_untrusted = self.untrusted;
        let child_safe_spaces = self.safe_spaces.clone();

        // Spawn the OS thread. We are the running mutator (hold the giant
        // lock); `runtime` was moved into the closure, so keep a clone for
        // the failure path's cleanup.
        let runtime_for_cleanup = Arc::clone(&self.runtime);
        let spawn_result = std::thread::Builder::new()
            .name("poly-sml-thread".into())
            .stack_size(8 * 1024 * 1024)
            .spawn(move || {
                Self::child_thread_main(
                    runtime,
                    child_handle_for_thread,
                    fork_raw_bits as *mut ForkRoots,
                    child_untrusted,
                    child_safe_spaces,
                );
            });

        if let Err(e) = spawn_result {
            // LOW (spawn-failure deadlock): the child handle is ALREADY
            // registered with published ForkRoots, but no OS thread will ever
            // run/exit it. Left as-is it is a registered, not-running,
            // parked-with-Some handle that never drains — so the next
            // `request_gc` stop-the-world barrier (which waits for every
            // registered peer to be parked) is *satisfied* by it, but
            // `wait_for_children` would block forever (it never sets
            // `exited`). Deregister it + drop its published ForkRoots + free
            // the leaked box ourselves. We hold the giant lock (running), but
            // the CHILD does not, so use the PARKED exit (it must not clear
            // OUR `running`). Then reclaim the ForkRoots box (no published
            // slot references it after exit_parked clears it).
            runtime_for_cleanup.exit_parked(&child_handle);
            child_handle
                .exited
                .store(true, std::sync::atomic::Ordering::SeqCst);
            runtime_for_cleanup.notify_block_event();
            // SAFETY: exit_parked set this handle's parked_roots = None, so no
            // reader references the ForkRoots box; reclaim it.
            unsafe { drop(Box::from_raw(fork_raw_bits as *mut ForkRoots)) };
            if crate::env::env_flag("POLY_THREAD_TRACE") {
                eprintln!("[parent] fork_thread spawn FAILED: {e}; child deregistered");
            }
            return Err(InterpError::ThreadSpawnFailed(e.to_string()));
        }

        let _ = child_handle; // the parent drops its extra ref; registry + spawn hold it
        Ok(thread_obj)
    }

    /// Entry point of a forked OS thread. Builds a fresh `ThreadContext`
    /// over the shared `Runtime`, seeds the function closure, runs it to
    /// completion (Thread.exit ends the loop), then releases ML memory and
    /// marks the handle exited + wakes joiners.
    fn child_thread_main(
        runtime: Arc<crate::sched::Runtime>,
        handle: Arc<crate::sched::ThreadHandle>,
        fork_raw: *mut ForkRoots,
        untrusted: bool,
        safe_spaces: SafeSpaces,
    ) {
        let trace = crate::env::env_flag("POLY_THREAD_TRACE");
        if trace {
            eprintln!("[child] spawned, fork_raw={fork_raw:p}");
        }
        // Build a fresh ThreadContext. We do NOT seed its stack or set its
        // thread_object yet — the closure + thread object are still under
        // the parent-published `ForkRoots`, which a GC may forward in place
        // before we acquire. We read the (possibly-forwarded) values back
        // only AFTER acquiring the lock (see below), so the child never
        // holds a stale copy (the B1 root-handoff).
        let mut child = Interpreter::for_child_thread(
            runtime.clone(),
            handle.clone(),
            PolyWord::ZERO,
            untrusted,
            safe_spaces,
        );
        child.thread_object = None;
        // The parent already registered our handle (with published roots).
        child.registered = true;

        // P2b: the child gets its OWN nursery — per-thread bump allocation
        // with a per-thread trigger (the correctness mechanism for parallel
        // allocation, ahead of P4). Installed via the pool lock (safe here,
        // pre-acquire); the collector evacuates the whole pool, promoting
        // this nursery's live data into the primary and resetting it. Skip
        // when no heap is configured (heapless test contexts).
        if runtime.nursery_count() > 0 {
            let default_bytes = 32 * 1024 * 1024usize;
            let child_bytes = std::env::var("POLYML_CHILD_NURSERY_BYTES")
                .ok()
                .and_then(|s| s.parse::<usize>().ok())
                .filter(|&b| b >= 1024 * 1024)
                .unwrap_or(default_bytes);
            let cap_words = child_bytes / std::mem::size_of::<PolyWord>();
            child.nursery = runtime.install_nursery(crate::space::MemorySpace::new(
                cap_words,
                crate::space::SpaceKind::Mutable,
            ));
            let thresh = usize::from(crate::rts::gc_threshold_percent().unwrap_or(80));
            child.gc_trigger_words = cap_words.checked_mul(thresh).map_or(0, |x| x / 100);
        }

        // ---- Acquire the giant lock FIRST, KEEPING the parent-published
        // `ForkRoots` published while we wait (do NOT overwrite it with a
        // fresh empty capture — the child has no seeded stack yet, so an
        // empty capture would let a GC during the wait skip our closure →
        // B1 UAF). The ForkRoots stays published until we win the lock, so
        // a GC forwards our closure + thread object in place; the slot is
        // retracted to None the instant we win.
        runtime.acquire_ml_memory_keep_published(&handle);

        // ---- Read the forwarded closure + thread object back out of the
        // ForkRoots box (it was forwarded in place by any GC that fired
        // while we queued), then reclaim the box. From here the closure is
        // rooted by our own stack and the thread object by our own field,
        // both covered by our `ThreadRoots`.
        // SAFETY: we hold the giant lock; the slot is retracted; we are the
        // sole owner of the box now.
        let (function, thread_obj) = unsafe {
            let fr = &*fork_raw;
            (fr.function, fr.thread_obj)
        };
        // SAFETY: the box was leaked by the parent and is no longer
        // referenced by any published slot (retracted on acquire).
        unsafe { drop(Box::from_raw(fork_raw)) };

        child.thread_object = Some(thread_obj);
        // Seed the stack: push ONLY the (forwarded) closure (InitStackFrame).
        // The function reads its environment from the closure (LOCAL_0); it
        // calls Thread.exit at the end so it never RETURNs past this frame.
        let _ = child.push(function);
        // Set PC + code bounds to the closure's code body.
        if child.jit_set_code_segment_to_closure(function).is_err() {
            // Malformed function: we ARE the running mutator here (we just
            // acquired the lock above and have NOT released it), so exit via
            // the RUNNING path — it clears `running` (which we hold) while
            // deregistering. Using the parked path here (the H2 hazard)
            // would leave `running == true` forever → permanent deadlock for
            // every peer waiting on the giant lock.
            runtime.exit_running(&handle);
            // We deregistered explicitly; clear the flag so `child`'s Drop
            // does not re-enter the exit path (exit_* is idempotent, so the
            // double call is benign, but leaving it invites a future reader to
            // assume Drop is the sole deregister site).
            child.registered = false;
            handle
                .exited
                .store(true, std::sync::atomic::Ordering::SeqCst);
            runtime.notify_block_event();
            return;
        }
        // Run the thread body. We ALREADY hold the giant lock (acquired
        // above), so run_until must not re-acquire — flag it. A large step
        // cap; Thread.exit ends it sooner.
        child.holds_lock_on_entry = true;
        if trace {
            eprintln!(
                "[child] entering run_until, registry_len={}",
                runtime.registry_len()
            );
        }
        let (steps, _outcome) = child.run_until(u64::MAX);
        if trace {
            eprintln!("[child] run_until returned after {steps} steps: {_outcome:?}");
        }
        // run_until's exit published our (now-quiescent) roots via
        // `release_ml_memory` and stashed the box in `child.published_box`.
        // We are about to die: at this point run_until ALREADY RELEASED the
        // giant lock, so we are NOT the running mutator — exit via the
        // PARKED path, which deregisters + drops our published roots WITHOUT
        // touching `running` (a peer may now hold it; the H2 fix). It also
        // waits out any in-flight collection before deregistering. Then free
        // the stashed box.
        runtime.exit_parked(&handle);
        // Deregistered explicitly; clear the flag so `child`'s Drop is a no-op
        // on the registry (see the malformed-function path above).
        child.registered = false;
        child.free_published_box();
        handle
            .exited
            .store(true, std::sync::atomic::Ordering::SeqCst);
        runtime.notify_block_event();
    }

    /// Allocate a ThreadObject value (9-word mutable object) in the shared
    /// heap, seeding the ML-passed attribute flags + max-stack size.
    /// Layout per processes.h:83-95 / upstream ForkThread
    /// (processes.cpp:1512-1519); word 0 (threadRef, the identity slot) is
    /// written by the caller.
    fn alloc_thread_object_value(
        &mut self,
        attrs: PolyWord,
        stack: PolyWord,
    ) -> Result<PolyWord, InterpError> {
        use crate::length_word::F_MUTABLE_BIT;
        let length = 9;
        let p = self.allocate(length, F_MUTABLE_BIT)?;
        // SAFETY: just allocated 9 words. (ATOMIC init — see do_tuple)
        unsafe {
            Self::heap_write(p.add(0), PolyWord::tagged(0)); // threadRef (id written by caller)
            Self::heap_write(p.add(1), attrs); // flags — the ML attrs word, as passed
            Self::heap_write(p.add(2), PolyWord::tagged(0)); // threadLocal
            Self::heap_write(p.add(3), PolyWord::tagged(0)); // requestCopy
            Self::heap_write(p.add(4), stack); // mlStackSize — the ML stack word, as passed
            for i in 5..length {
                Self::heap_write(p.add(i), PolyWord::tagged(0)); // debuggerSlots
            }
        }
        Ok(PolyWord::from_ptr(p.cast_const()))
    }

    /// Reset a mutex object's word 0 to TAGGED(0) (unlocked). Mirrors
    /// `InterpreterReleaseMutex` (bytecode.cpp:2465). Defensive against a
    /// non-pointer "mutex".
    fn reset_mutex_word(&self, mutex: PolyWord) -> Result<(), InterpError> {
        if mutex.is_data_ptr() && mutex.0 & (std::mem::size_of::<usize>() - 1) == 0 {
            self.reset_mutex_word_atomic(mutex)?;
        }
        Ok(())
    }

    /// View a validated, word-aligned heap word as an `AtomicUsize`
    /// (parallelism P3). `PolyWord` is `repr(transparent)` over `usize`, so
    /// this is a plain reinterpret of the same location. The atomic RMW /
    /// store ops on the SML `Thread.Mutex` protocol word mirror upstream's
    /// interlocked ops (native x86 `XCHG` / arm64 `LDXR/STXR`; the
    /// interpreter serialises with a global `mutexLock`), so two parallel
    /// mutators inside one critical section can't both "acquire" (the TOCTOU
    /// the plain read-modify-write had). Single-threaded the atomic op
    /// yields the identical numerical result — byte-identical.
    ///
    /// # Safety
    /// `p` must be a valid, word-aligned, writable `PolyWord` slot (callers
    /// gate on `word0_deref_ok` / `is_data_ptr` + alignment, and in
    /// untrusted mode on `validate_obj`).
    #[inline]
    unsafe fn atomic_word<'p>(p: *mut PolyWord) -> &'p std::sync::atomic::AtomicUsize {
        // SAFETY: caller guarantees `p` is a valid aligned usize-sized slot.
        unsafe { &*std::sync::atomic::AtomicUsize::from_ptr(p.cast::<usize>()) }
    }

    /// Position-2 memory model (parallelism P4 prerequisite): relaxed
    /// atomic heap-word load/store. On x86-64/aarch64 these compile to the
    /// same mov/ldr/str as a plain access — and MEASURED ~9.5% FASTER on the
    /// heap-heavy benchmarks (sort/deriv/nbody/mmult; drift-cancelled A/B),
    /// because the atomic gives LLVM cleaner aliasing info than a raw `*p`
    /// deref. This makes concurrent shared-`ref` access well-defined (no
    /// data-race UB) instead of the plain-raw-pointer race upstream lives
    /// with — the "memory-safe port" keeps its promise. Byte accesses stay
    /// plain (they carry no pointers; a sub-word atomic would need RMW).
    #[inline]
    unsafe fn heap_read(p: *const PolyWord) -> PolyWord {
        // SAFETY: caller guarantees `p` is a valid aligned readable slot.
        let bits = unsafe {
            std::sync::atomic::AtomicUsize::from_ptr(p.cast::<usize>().cast_mut())
                .load(std::sync::atomic::Ordering::Relaxed)
        };
        PolyWord::from_bits(bits)
    }
    #[inline]
    unsafe fn heap_write(p: *mut PolyWord, w: PolyWord) {
        // SAFETY: caller guarantees `p` is a valid aligned writable slot.
        unsafe {
            Self::atomic_word(p).store(w.0, std::sync::atomic::Ordering::Relaxed);
        }
    }

    /// The word-aligned, (untrusted-)validated ATOMIC store of `TAGGED(0)`
    /// into the mutex word — split out so [`Self::reset_mutex_word`] keeps
    /// its guard shape. Upstream releases the mutex with an interlocked op;
    /// a plain store could erase a peer's just-taken lock (two threads
    /// inside one critical section).
    fn reset_mutex_word_atomic(&self, mutex: PolyWord) -> Result<(), InterpError> {
        if self.untrusted {
            // The mutex pointer is image-controlled (reachable only via
            // PolyThreadMutexUnlock under POLY_REAL_THREADS=1 + --untrusted
            // — the experimental real-threads + untrusted combo). Validate
            // in-space + >= 1 word before the OOB-prone write. (#96
            // secondary finding from the adversarial re-verify: this static
            // fn could not consult self.untrusted; now a &self method.)
            let vo = self.validate_obj(mutex, "MUTEX_UNLOCK")?;
            vo.check_word_index(0)
                .map_err(|why| InterpError::BadImage {
                    op: "MUTEX_UNLOCK",
                    why,
                })?;
        }
        let p = mutex.as_ptr::<PolyWord>().cast_mut();
        // ATOMIC store (P3): a plain store could erase a peer's just-taken
        // lock. SAFETY: trusted (compiler-emitted mutex) OR untrusted-
        // validated in-space object >= 1 word; word-aligned (caller checks).
        unsafe {
            Self::atomic_word(p).store(PolyWord::tagged(0).0, std::sync::atomic::Ordering::Release);
        }
        Ok(())
    }

    /// Run a copying GC over the alloc space, forwarding all roots
    /// (interpreter stack, exception packet, code segment, frames,
    /// recent-call ring buffer, the per-thread bootstrap tail-call slot,
    /// every parked thread's published roots, and any configured
    /// image-mutable-root regions). Returns the new `used_words` count of
    /// the alloc space.
    ///
    /// Precondition (3c): the caller is the collector — it holds the
    /// giant lock and every OTHER thread is parked with roots published.
    /// Reached via `Self::request_gc_collect`.
    pub fn gc(&mut self) -> Option<usize> {
        // ---- Build the per-thread root-set REGISTRY.
        //
        // Today the interpreter is single-threaded, so the registry has
        // exactly ONE entry — the root-set captured from `self`. The
        // collector below drives this registry as an iterable ("for each
        // thread-root-set in registry { forward / fixup }") so that a 2nd
        // thread is a push to this Vec, not a rewrite of the root walk.
        //
        // `capture` returns a self-contained struct of raw pointers into
        // `self`'s fields, so the `&mut self` borrow ends here; that is
        // what lets the registry coexist with the `&mut alloc_space`
        // borrow `collect` takes, and (eventually) many threads' captures.
        // (`capture` and the shared-root reads below have no side effects,
        // so doing them before the `?` early-return on a missing alloc
        // space is behaviour-identical to the original "bail first".)
        let mut registry: Vec<ThreadRoots> = vec![ThreadRoots::capture(self)];

        // ---- PARKED-THREAD roots (multi-threaded only).
        //
        // Every OTHER live thread is, by the time we run as the collector,
        // parked at its safepoint or in a blocking RTS wait, having
        // PUBLISHED its root-set into its `ThreadHandle::parked_roots`
        // slot. That `Mutex<Option<SendRoots>>` is the ONLY route we have
        // to another thread's stack — a `None` slot is unreachable, so we
        // structurally only touch a thread we have confirmed parked.
        //
        // We forward those published roots via the type-erased
        // `forward`/`fixup` thunks the parking thread stored, holding each
        // handle's `parked_roots` lock for the duration (the parked thread
        // is blocked and cannot retract it until the collection finishes).
        //
        // Single-threaded: the registry has just our own handle, whose
        // slot is `None` (we are `in_ml`, not parked) — so this loop is
        // empty and the GC is byte-identical to the legacy one.
        let parked_handles = self.runtime.registry_snapshot();
        let my_handle = Arc::as_ptr(&self.handle);
        // Guards kept alive until after fixup (so a parked thread cannot
        // wake and mutate its stack mid-collection).
        let mut parked_guards: Vec<std::sync::MutexGuard<'_, Option<crate::sched::SendRoots>>> =
            Vec::new();
        // Parked threads' EXTRA RTS root cells (see ThreadHandle::
        // rts_park_root): each is an RTS-local PolyWord in a blocked RTS
        // fn's live frame (e.g. a parked readArray's destination byte
        // array), forwarded alongside the thread's published root-set. The
        // raw cell pointers are collected here UNDER the corresponding
        // parked_roots guard (held for the whole collection), so the owner
        // can neither retract its publication nor clear the cell while we
        // hold them.
        let mut parked_rts_cells: Vec<*mut PolyWord> = Vec::new();
        for h in &parked_handles {
            if Arc::as_ptr(h) == my_handle {
                continue;
            }
            let guard = h.parked_roots.lock().unwrap();
            if guard.is_some() {
                if let Some(cell) = *h.rts_park_root.lock().unwrap() {
                    parked_rts_cells.push(cell.0);
                }
                parked_guards.push(guard);
            }
        }

        // ---- SHARED roots (process-level, NOT per-thread): forwarded
        //      once regardless of how many threads are in the registry.
        // (The bootstrap tail-call slot is now PER-THREAD — captured +
        // forwarded + fixed-up inside each `ThreadRoots`, not here.)
        // Image mutable spaces (the global namespace + runtime refs).
        let image_roots = self.image_mutable_roots.clone();

        // Reach the nursery via the pool (P1: exactly one, index 0). We
        // hold the STW barrier (every other thread parked), so we are the
        // sole live heap accessor; the Box-pinned handles are stable.
        // P2b: gather EVERY pool nursery — the collection evacuates the
        // UNION (cross-nursery pointers are unrestricted, so partial
        // collection is unsound; docs/parallel-design.md).
        // SAFETY: sole accessor under the barrier; each handle addresses a
        // pinned nursery; handles are distinct pool entries (no aliasing).
        let n_nurseries = self.runtime.nursery_count();
        if n_nurseries == 0 {
            return None;
        }
        let mut nursery_refs: Vec<&mut crate::space::MemorySpace> = (0..n_nurseries)
            .map(|i| unsafe { &mut *self.runtime.nursery_handle(i) })
            .collect();
        // Capture every from-space range so we can audit for residual
        // pointers after the swap. Anything in interpreter state (or the
        // new to-space) that still points into any of these post-GC is a
        // missed root.
        let from_ranges: Vec<(usize, usize)> = nursery_refs
            .iter()
            .map(|s| {
                let r = s.as_ptr_range();
                (r.start as usize, r.end as usize)
            })
            .collect();
        // The single-range audit variables cover the PRIMARY (kept for the
        // existing audit plumbing; the union audit loops the full list).
        let (from_lo, from_hi) = from_ranges[0];

        let new_used = crate::gc::collect_pool(&mut nursery_refs, |c| {
            // ---- Per-thread roots: drive the registry as an iterable.
            for roots in registry.iter_mut() {
                // SAFETY: each capture aliases live interpreter state for
                // the duration of this collect, and no other path mutates
                // it meanwhile.
                unsafe { roots.forward(c) };
            }

            // ---- Parked OTHER threads' published roots. Each guard holds
            // a `Some(SendRoots)`; we call its type-erased `forward` thunk
            // with the collector. The parked thread is blocked and cannot
            // retract its publication until we clear gc_requested.
            for guard in &mut parked_guards {
                if let Some(sr) = guard.as_mut() {
                    // SAFETY: the parked thread published a root-set
                    // aliasing its live (frozen) ThreadContext; it is
                    // blocked, so we are the sole accessor. `forward` is
                    // the `ThreadRoots::forward` thunk; `c` is the
                    // collector.
                    unsafe {
                        (sr.forward)(sr.ptr, std::ptr::from_mut(c).cast::<()>());
                    }
                }
            }
            // ---- Parked threads' EXTRA RTS root cells (blocking-syscall
            // parks that must touch a heap object after re-acquiring).
            for &cell in &parked_rts_cells {
                // SAFETY: each cell is a live Rust stack local in a blocked
                // RTS fn's frame (stable across the park); its owner cannot
                // touch it until it re-acquires the lock we hold. Forwarding
                // it here is what makes the owner's post-park re-derive see
                // the MOVED object instead of dangling into from-space.
                unsafe { c.forward(cell) };
            }

            // ---- Shared roots, forwarded ONCE.
            // (The bootstrap tail-call slot moved to per-thread roots above.)
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
                            // WEAK image-mutable object: slots are weak
                            // links — register for the post-trace fixup
                            // instead of strongly forwarding (upstream
                            // scans permanent-mutable weak areas in
                            // gc_check_weak_ref.cpp::ScanAreas).
                            if (crate::length_word::flags_of(lw) & crate::length_word::F_WEAK_BIT)
                                != 0
                            {
                                c.register_weak(body as usize);
                            } else {
                                // Ordinary word object.
                                for k in 0..n {
                                    unsafe { c.forward(body.add(k)) };
                                }
                            }
                        }
                    }
                    i += 1 + n;
                    img_objects_scanned += 1;
                }
            }
            if !crate::env::env_flag("POLYML_GC_QUIET") {
                eprintln!(
                    "  GC roots: image-mut objects scanned = {img_objects_scanned}, total image-mut words = {}",
                    image_roots.iter().map(|(_, l)| l).sum::<usize>()
                );
            }
        });

        // ---- Per-thread post-GC fixup: drive the registry as an iterable.
        //
        // For each thread-root-set we (a) scrub its below-sp free region
        // and (b) write its forwarded slots back into the owning
        // interpreter. With one thread this is exactly the legacy inline
        // block; a 2nd thread is just another iteration.
        //
        // ---- Scrub the below-sp (free/garbage) region (per thread).
        //
        // The collector forwards only the LIVE set [sp, len). Slots in
        // [0, sp) are the free/garbage zone (drop_n/RESET bump sp past
        // them, leaving stale values BY DESIGN — see "Below sp is free"
        // above). Those stale values can be pointers into the from-space
        // Box that `collect` just RETIRED via replace_storage (freed, or
        // stashed as the ping-pong spare — either way dead), so they now
        // DANGLE. A later sp-lowering op that re-exposes one before
        // writing it would let the dispatch loop dereference dead
        // memory → use-after-free SIGSEGV (or, with the spare reused,
        // silently read recycled to-space).
        //
        // Overwrite every below-sp slot with a safe tagged sentinel
        // (Tagged(0)). This is sound because below-sp is dead-for-
        // correctness: every legitimate stack READ is at index >= sp,
        // and every sp-lowering op writes the newly-exposed slot before
        // it is read. So if a scrubbed slot were ever re-exposed and
        // read it would be a benign tagged int 0, not a wild deref.
        // O(sp) once per collect — cheap vs the Cheney copy; deliberately
        // NOT on the hot drop_n/RESET path. This runs AFTER from-space is
        // retired (replace_storage inside collect) and BEFORE any op or
        // the audit, closing the dangling-pointer window. History: the
        // GC-soak findings + fix, commits 77b6141 + 8756419 (task #109).
        for roots in registry.iter_mut() {
            // SAFETY: captures still alias live interpreter state; the
            // collect above has freed from-space, so scrub then fixup.
            unsafe {
                roots.scrub_below_sp();
                roots.apply_fixups();
            }
        }
        drop(registry);

        // ---- Parked OTHER threads' post-GC fixup. Same scrub + write-back
        // as our own thread, via the type-erased `fixup` thunk. Still
        // under each handle's `parked_roots` lock (the parked thread is
        // blocked), so no race. Dropping the guards afterwards lets the
        // threads wake once we clear gc_requested.
        for guard in &mut parked_guards {
            if let Some(sr) = guard.as_mut() {
                // SAFETY: collect freed from-space; the parked thread is
                // still blocked, so we are the sole accessor of its roots.
                unsafe {
                    (sr.fixup)(sr.ptr);
                }
            }
        }
        drop(parked_guards);

        // (The per-thread bootstrap tail-call slot and recent-call ring
        // buffer are written back / cleared inside each root-set's
        // `apply_fixups`. No shared root write-back remains.)

        // ---- Audit: any pointer still in old from-space is a missed root.
        // Opt-in via POLYML_GC_AUDIT=1 — full audit is O(used+stack)
        // and meaningful overhead on the hot loop. P2b: audited per
        // from-space RANGE over the whole union. Caveat: the PRIMARY's
        // range check is against its OLD storage range, whose Box was
        // dropped by the swap — the addresses can never recur in live data
        // (the allocator can't hand them out again until the OS reuses the
        // mapping), so a hit is still a genuine missed root. Non-primary
        // nurseries keep their storage (reset_empty), so their hits are
        // exact.
        if crate::env::env_flag("POLYML_GC_AUDIT") {
            for &(lo, hi) in &from_ranges {
                self.audit_no_residual_from_space_ptrs(lo, hi);
            }
        }
        let _ = from_lo;
        let _ = from_hi;
        Some(new_used)
    }

    fn audit_no_residual_from_space_ptrs(&self, from_lo: usize, from_hi: usize) {
        let in_old = |addr: usize| addr >= from_lo && addr < from_hi;
        let mut residual = 0usize;
        let mut samples: Vec<(&'static str, usize, usize)> = Vec::new();
        // 1. Interpreter stack — scan the FULL stack [0, len), not just
        //    the live set [sp, len). Below-sp slots are scrubbed to
        //    Tagged(0) on each collect (see Interpreter::gc), so on a
        //    correct run they hold no from-space pointers; scanning the
        //    whole stack makes the detector honest for the below-sp
        //    use-after-free class (task #109) without firing on clean
        //    runs.
        for i in 0..self.stack.len() {
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
        // 5b. bootstrap tail-call slot (per-thread root). A residual here
        //     means the per-thread forward/fixup missed it.
        if in_old(self.bootstrap_tail_call.0) {
            residual += 1;
            samples.push(("bootstrap_tail", 0, self.bootstrap_tail_call.0));
        }
        // 6. Walk the NEW alloc-space body words and look for stale
        //    inbound pointers. This is the big one — missed children
        //    of forwarded objects.
        if let Some(space) = self.alloc_space_ref() {
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
        // 8. CROSS-STACK audit (B3): scan EVERY OTHER registered thread's
        //    PUBLISHED roots (+ flag any registered-but-unpublished peer).
        //    Extracted into a helper to keep this function readable.
        residual += self.audit_cross_stack_residual(from_lo, from_hi, &mut samples);
        if residual > 0 {
            eprintln!("  GC AUDIT: {residual} residual from-space pointers remain after collect:");
            for (where_, idx, addr) in samples {
                eprintln!("    {where_}[{idx}] = 0x{addr:016x}");
            }
        }
        // Record the residual into the Runtime so a test can ASSERT on it —
        // the audit's teeth (a NEGATIVE control that reintroduces H1/H2 must
        // see this go positive; a sound run keeps it 0).
        self.runtime
            .gc_audit_residual
            .fetch_add(residual as u64, std::sync::atomic::Ordering::Relaxed);
    }

    /// CROSS-STACK audit (B3): scan EVERY OTHER registered thread's PUBLISHED
    /// roots for residual from-space pointers, and flag any registered-but-
    /// unpublished peer (the B1/B2 invariant violation — its live stack would
    /// have been skipped). Returns the residual count to add. We re-snapshot +
    /// re-lock each handle's slot; the parked threads are still blocked
    /// (`gc_requested` is cleared only after `gc()` returns), so the slots are
    /// frozen.
    fn audit_cross_stack_residual(
        &self,
        from_lo: usize,
        from_hi: usize,
        samples: &mut Vec<(&'static str, usize, usize)>,
    ) -> usize {
        let me = Arc::as_ptr(&self.handle);
        let mut residual = 0usize;
        let mut unpublished_others = 0usize;
        for h in &self.runtime.registry_snapshot() {
            if Arc::as_ptr(h) == me {
                continue;
            }
            let guard = h.parked_roots.lock().unwrap();
            match guard.as_ref() {
                Some(sr) => {
                    // SAFETY: the parked thread is blocked; we are the sole
                    // accessor of its published roots under this lock.
                    let n = unsafe { (sr.audit)(sr.ptr, from_lo, from_hi) };
                    if n > 0 {
                        residual += n;
                        if samples.len() < 5 {
                            samples.push(("parked_thread_roots", 0, 0));
                        }
                    }
                }
                None => {
                    // A registered, non-running peer with UNPUBLISHED roots is
                    // itself a soundness violation (the B1/B2 invariant): the
                    // collector would have skipped its live stack. Flag it
                    // loudly even though we cannot scan what was skipped.
                    unpublished_others += 1;
                }
            }
        }
        if unpublished_others > 0 {
            eprintln!(
                "  GC AUDIT: {unpublished_others} registered NON-running thread(s) had \
                 parked_roots == None at collect time (B1/B2 invariant violated — \
                 their live stacks were SKIPPED)"
            );
            residual += unpublished_others;
        }
        residual
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

    /// Push one word onto the ML stack while hand-building the entry
    /// call frame ("seeding"). Every run entry point uses it to
    /// simulate the post-CALL state the root function expects: args
    /// (deepest first), then [`Self::seed_return_sentinel`], then the
    /// closure word on top.
    pub fn seed_push(&mut self, w: PolyWord) {
        let _ = self.push(w);
    }

    /// Renamed: use [`Self::seed_push`].
    #[doc(hidden)]
    #[deprecated(note = "renamed to `seed_push`")]
    pub fn test_seed_top(&mut self, w: PolyWord) {
        self.seed_push(w);
    }

    /// Reset the stack to empty (sp = stack.len()). Used by the
    /// differential tester to run multiple distinct calls on the
    /// same interpreter without re-loading the image.
    pub fn reset_stack(&mut self) {
        self.sp = self.stack.len();
        self.frames.clear();
        self.handler_sp = 0;
    }

    /// Test-only: acquire the giant mutator lock (become the running
    /// thread), publishing roots while waiting. Pairs with
    /// [`Self::test_release_running`]. Used by the fork-TOCTOU stress test
    /// to drive the real `fork_thread` path from Rust.
    #[doc(hidden)]
    pub fn test_acquire_running(&mut self) {
        // `acquire_running` registers-and-acquires atomically on its first
        // call (H1), so there is no separate bare-register step.
        self.acquire_running();
    }

    /// Test-only: release the giant mutator lock after a
    /// [`Self::test_acquire_running`], publishing our (quiesced) roots so
    /// the invariant holds. Quiesces first (terminal-style) so a child's GC
    /// after we release cannot race a write-back into our `self`.
    #[doc(hidden)]
    pub fn test_release_running(&mut self) {
        self.quiesce_roots();
        let runtime = Arc::clone(&self.runtime);
        let handle = Arc::clone(&self.handle);
        let (raw, send) = self.make_send_roots();
        // SAFETY: quiesced ⇒ root-free capture; box stashed to outlive the
        // published-slot window, freed on the next acquire / Drop.
        unsafe { runtime.release_ml_memory(&handle, send) };
        self.stash_published_box(raw);
    }

    /// Test-only: build a minimal *runnable* closure in the SHARED heap that
    /// the child-fork path can execute — a code object whose body is
    /// `RETURN_B 0` (return immediately) plus a closure word pointing at it.
    /// Because it lives in the collected heap, a GC fired before the child
    /// runs WILL move it — exercising the B1 root-handoff (the child must
    /// read the FORWARDED closure back out of its `ForkRoots`). Caller must
    /// hold the giant lock. Returns the closure `PolyWord`.
    ///
    /// # Panics
    /// If the runtime has no alloc space.
    #[doc(hidden)]
    pub fn test_build_runnable_closure(&mut self) -> PolyWord {
        use crate::length_word::{F_CLOSURE_OBJ, F_CODE_OBJ};
        // Code body: RETURN_B 0 (opcode 0x1f, imm 0). Plus a 2-word const
        // tail (n_consts=0 + the const-base offset word) matching
        // make_code_object's layout so const_segment_for_code is valid.
        let code_bytes: [u8; 2] = [0x1f, 0x00];
        let word = std::mem::size_of::<usize>();
        let code_words = code_bytes.len().div_ceil(word);
        let total_words = code_words + 2; // + n_consts word + const-base word
        let code_obj = self
            .allocate(total_words, F_CODE_OBJ)
            .expect("alloc code obj");
        // SAFETY: just allocated total_words; layout per make_code_object.
        unsafe {
            let dst = code_obj.cast::<u8>();
            std::ptr::copy_nonoverlapping(code_bytes.as_ptr(), dst, code_bytes.len());
            let pad = code_bytes.len().next_multiple_of(word) - code_bytes.len();
            if pad > 0 {
                std::ptr::write_bytes(dst.add(code_bytes.len()), 0, pad);
            }
            code_obj.add(code_words).write(PolyWord::from_bits(0)); // n_consts = 0
            let const_addr_index = (code_words + 1) as isize;
            let total_isize = total_words as isize;
            let offset_bytes = (const_addr_index - total_isize) * (word as isize);
            code_obj
                .add(total_words - 1)
                .write(PolyWord::from_bits(offset_bytes as usize));
        }
        // Closure: 1 word = the code-object pointer.
        let closure = self.allocate(1, F_CLOSURE_OBJ).expect("alloc closure");
        // SAFETY: 1-word closure; word[0] = code object pointer.
        unsafe {
            closure
                .add(0)
                .write(PolyWord::from_ptr(code_obj.cast_const()));
        }
        PolyWord::from_ptr(closure.cast_const())
    }

    /// Test-only: fork a real child OS thread running `function` via the
    /// genuine [`Self::fork_thread`] path (publishes the child's ForkRoots,
    /// registers it, spawns it). Caller must hold the giant lock. Returns
    /// the child's ThreadObject.
    ///
    /// # Panics
    /// If `fork_thread` fails (e.g. no alloc space).
    #[doc(hidden)]
    pub fn test_fork_child(&mut self, function: PolyWord) -> PolyWord {
        // Default attributes = the SML fork wrapper's defaults
        // (Thread.sml:471-472): no broadcast + InterruptSynch, unlimited
        // stack.
        #[allow(clippy::cast_possible_wrap)]
        self.fork_thread(
            function,
            PolyWord::tagged(pflag::SYNCH as isize),
            PolyWord::tagged(0),
        )
        .expect("fork_thread")
    }

    /// Test-only: force a stop-the-world collection right now (the caller is
    /// the running thread). With a freshly-forked child still registered but
    /// not yet acquired, this exercises the B1 TOCTOU window: the collector's
    /// stop-the-world barrier waits for the child to be confirmed parked
    /// (its ForkRoots published), then forwards the child's closure.
    #[doc(hidden)]
    pub fn test_force_gc(&mut self) {
        let _ = self.request_gc_collect();
    }

    /// NEGATIVE-CONTROL ONLY (proves the audit has teeth): collect DIRECTLY
    /// via `gc()`, bypassing `request_gc`'s stop-the-world barrier. The
    /// barrier is exactly what BLOCKS on a registered-but-unpublished peer
    /// (the H1 hazard), so a faithful H1 reintroduction would DEADLOCK in
    /// `request_gc` — not a useful negative control. By collecting directly
    /// we let the collector run with an H1-violating registry present and
    /// observe that the POLYML_GC_AUDIT cross-stack pass DETECTS it
    /// (`gc_audit_residual` goes positive). Caller must be the running thread
    /// (hold the giant lock). Returns the new used-words (or None).
    #[doc(hidden)]
    pub fn test_force_gc_no_barrier(&mut self) -> Option<usize> {
        self.gc()
    }

    /// NEGATIVE-CONTROL ONLY: reintroduce the H1 unsound state by pushing a
    /// dummy peer handle into the scheduler registry with `parked_roots ==
    /// None` (a "registered, not-running, unpublished" thread — exactly what
    /// the structural H1 fix forbids, since the production API no longer has
    /// a bare `register_thread`). A subsequent direct collect
    /// (`test_force_gc_no_barrier`) under POLYML_GC_AUDIT=1 must flag this as
    /// an unpublished-peer residual. Returns the dummy handle so the test can
    /// clean it up (deregister) afterwards. Caller holds the giant lock.
    #[doc(hidden)]
    #[must_use]
    pub fn test_register_unpublished_peer_unsound(&self) -> Arc<crate::sched::ThreadHandle> {
        let dummy = crate::sched::ThreadHandle::new();
        // Bare-register: push into the registry while parked_roots stays
        // None. This is the H1 invariant violation, reproduced on purpose.
        let mut inner = self.runtime.sched.inner.lock().unwrap();
        inner.registry.push(Arc::clone(&dummy));
        dummy
    }

    /// NEGATIVE-CONTROL cleanup: remove a dummy peer handle previously
    /// pushed by [`Self::test_register_unpublished_peer_unsound`].
    #[doc(hidden)]
    pub fn test_deregister_peer(&self, handle: &Arc<crate::sched::ThreadHandle>) {
        let mut inner = self.runtime.sched.inner.lock().unwrap();
        inner.registry.retain(|h| !Arc::ptr_eq(h, handle));
    }

    /// Test-only getter: cumulative GC-audit residual count (see
    /// [`crate::sched::Runtime::gc_audit_residual`]).
    #[doc(hidden)]
    #[must_use]
    pub fn test_gc_audit_residual(&self) -> u64 {
        self.runtime
            .gc_audit_residual
            .load(std::sync::atomic::Ordering::Relaxed)
    }

    /// Test-only getter: number of completed GC cycles (see
    /// [`crate::sched::Runtime::gc_count`]). Used by the forced-GC-mid-
    /// region test to assert the collection actually FIRED.
    #[doc(hidden)]
    #[must_use]
    pub fn test_gc_count(&self) -> u64 {
        self.runtime
            .gc_count
            .load(std::sync::atomic::Ordering::Relaxed)
    }

    /// Test-only setter: force the GC trigger word count to `words` (both
    /// the per-interpreter mirror and the shared Runtime). Lets a test arm
    /// the top-of-step / region-safepoint collection at a tiny watermark so
    /// it fires deterministically mid-run. `words == 0` disables GC.
    #[doc(hidden)]
    pub fn test_set_gc_trigger_words(&mut self, words: usize) {
        self.gc_trigger_words = words;
        if let Some(rt) = Arc::get_mut(&mut self.runtime) {
            rt.gc_trigger_words = words;
        }
    }

    /// Test-only getter: whether the giant lock is held (`running`). Used by
    /// the H2 negative control.
    #[doc(hidden)]
    #[must_use]
    pub fn test_running(&self) -> bool {
        self.runtime.running_for_test()
    }

    /// H2 NEGATIVE-CONTROL ONLY: stage a parked peer (registered + published,
    /// root-free) and call `exit_parked` on it. The CALLER (host) must be the
    /// running mutator (hold the giant lock). After this:
    ///   * with the H2 FIX, `exit_parked` does NOT touch `running`, so the
    ///     host still holds the lock (`test_running() == true`);
    ///   * with the H2 BUG (clearing `running` unconditionally), the host's
    ///     ownership is clobbered (`test_running() == false`) → a second
    ///     mutator could run.
    /// The test asserts `test_running()` stays true, proving the fix and that
    /// reintroducing H2 would FAIL this assertion (teeth).
    #[doc(hidden)]
    pub fn test_exit_parked_peer_while_running(&mut self) {
        // Stage a parked peer with a root-free dummy capture.
        let peer = crate::sched::ThreadHandle::new();
        let dummy: Box<ThreadRoots> = Box::new(ThreadRoots::capture(self));
        let raw = Box::into_raw(dummy);
        let send = crate::sched::SendRoots {
            ptr: raw.cast::<()>(),
            forward: ThreadRoots::forward_thunk,
            fixup: ThreadRoots::fixup_thunk,
            audit: ThreadRoots::audit_thunk,
        };
        // SAFETY: no GC runs against this dummy; thunks are never invoked.
        unsafe { self.runtime.test_register_parked_dummy(&peer, send) };
        // Now exit the parked peer (it is NOT the running thread — WE are).
        self.runtime.exit_parked(&peer);
        // The dummy box is now unreferenced (exit_parked cleared the slot).
        // SAFETY: reclaim it.
        unsafe { drop(Box::from_raw(raw)) };
    }

    /// Push the synthetic return-to-top sentinel onto the stack so the
    /// interpreter can be used inside a hand-built call frame.
    ///
    /// Use this after [`Self::seed_push`]es for the args and before the
    /// closure, so the stack layout becomes `[closure, retPC=null,
    /// args...]`. When the callee's RETURN fires, it'll find
    /// retPC=null and yield `Returned`.
    pub fn seed_return_sentinel(&mut self) {
        // retPC = null pointer encoded as a PolyWord bit pattern.
        let _ = self.push(PolyWord::from_bits(0));
    }

    /// Renamed: use [`Self::seed_return_sentinel`].
    #[doc(hidden)]
    #[deprecated(note = "renamed to `seed_return_sentinel`")]
    pub fn test_seed_return_sentinel(&mut self) {
        self.seed_return_sentinel();
    }

    /// Test/debug API: invoke `do_call` from outside the crate. Used
    /// to validate the JIT-dispatch fast path without needing a full
    /// bytecode-emitting caller.
    #[doc(hidden)]
    pub fn test_invoke_do_call(&mut self, closure: PolyWord) -> Result<(), InterpError> {
        self.do_call(closure)
    }

    /// WHOLE-REGION DYNAMIC-CALL TRAMPOLINE re-entry (S4e).
    ///
    /// A native region, at a `CALL_LOCAL_B` / `CALL_CLOSURE` (a dynamic
    /// target), has already pushed the callee's N args onto the SHARED
    /// stack (the same `self.stack`). It calls back here (via
    /// `boundary::region_interp_call`, through the `interp_ptr` stored in
    /// the region's `ExnCtx`) to run that callee in the interpreter and
    /// hand the result back on the shared stack — then resume natively.
    ///
    /// `sp_at_top_arg` is the downward stack index of the top (last
    /// pushed) callee arg; `closure_bits` is the closure word the region
    /// would have called. On success the single result sits at
    /// `stack[new_sp]` (the args + the synthetic closure/retPC slots
    /// collapsed exactly as the interpreter's `do_call` + `do_return`
    /// would), `raised == 0`. On an interpreter error the call returns
    /// `raised == 1` with the region exn sentinel in `*exn_packet_out`.
    ///
    /// SOUNDNESS: this re-enters `do_call` / the interpreter run loop on
    /// `self`. The ONLY live `&mut self` up the call stack belongs to the
    /// outer `do_call` hook that invoked the region; that borrow is
    /// DORMANT for the whole duration of the native region call (the hook
    /// touches `self` again only after `dispatch(...)` returns). So the
    /// `&mut self` the trampoline holds here never aliases a *used* outer
    /// `&mut`. This is the exact discipline the per-function JIT fast
    /// path already relies on via the `JIT_INTERP` thread-local raw
    /// pointer (`jit_dispatch_*`). The re-entry SAVES and RESTORES the
    /// interpreter's PC + code-segment + handler state around the run, so
    /// the native region resumes with the interpreter exactly as it was.
    ///
    /// # Errors
    /// Returns `raised == 1` (with a sentinel in `*exn_packet_out`) if the
    /// callee run errors or fails to return cleanly.
    #[doc(hidden)]
    pub fn region_interp_call(
        &mut self,
        sp_at_top_arg: i64,
        closure_bits: i64,
        exn_packet_out: &mut i64,
    ) -> RegionRetC {
        // Save the interpreter execution state the run will clobber.
        let saved_pc = self.pc;
        let saved_start = self.code_start;
        let saved_end = self.code_end;
        let saved_frames_depth = self.frames.len();
        let saved_handler = self.handler_sp;
        let saved_handler_frames_depth = self.handler_frames_depth.len();

        // RAISE FIDELITY (S4-proper): ISOLATE the interpreter's handler for
        // the callee run. The native region (the caller) installs handlers
        // via the ExnCtx checked-return model — `self.handler_sp` does NOT
        // describe the region's handler, and an OUTER interpreted caller's
        // handler must NOT be unwound to from INSIDE this nested run (its
        // handler frame lives above sp_at_top_arg, and do_raise_ex's collapse
        // arithmetic assumes a continuous interp frame chain this re-entry
        // breaks). So we set handler_sp to the "no handler" sentinel
        // (`stack.len()`) for the callee. If the callee handles its OWN raise
        // internally (its own SET_HANDLER), it returns `Returned` normally.
        // If the callee raises and does NOT handle it, do_raise_ex / RAISE_EX
        // finds no handler and returns `Err(UnhandledException)` with
        // `self.exception_packet` set to the REAL packet — which we carry
        // back across the boundary (raised=1, the REAL packet bits) so the
        // do_call hook re-raises the REAL exception through the interpreter's
        // own (restored) handler machinery, byte-identical to a fully
        // interpreted callee.
        self.handler_sp = self.stack.len();

        // Point sp at the top callee arg (the region pushed the args onto
        // the shared stack already). Then build the callee entry frame the
        // SAME way do_call does: push retPC = 0 (the top-level sentinel,
        // so the callee's RETURN_N yields `Returned`) then the closure.
        self.sp = sp_at_top_arg as usize;
        let closure = PolyWord::from_bits(closure_bits as usize);

        // Push retPC sentinel (0) then closure, then jump to the callee's
        // code object — exactly do_call's non-JIT frame setup, but with a
        // 0 retPC so the run terminates at this callee's RETURN.
        if self.push(PolyWord::from_bits(0)).is_err() || self.push(closure).is_err() {
            *exn_packet_out = REGION_EXN_STACKOVERFLOW;
            return RegionRetC {
                new_sp: self.sp as i64,
                raised: 1,
            };
        }
        if !closure.is_data_ptr() {
            *exn_packet_out = REGION_EXN_OVERFLOW; // misroute → treat as raise
            return RegionRetC {
                new_sp: self.sp as i64,
                raised: 1,
            };
        }
        let closure_ptr = closure.as_ptr::<PolyWord>();
        // SAFETY: closure verified a data pointer just above.
        let code_word = unsafe { *closure_ptr };
        let new_code_obj = code_word.as_ptr::<PolyWord>();
        self.frames.push((self.code_start, self.code_end));
        // SAFETY: closure invariant guarantees a real code object.
        let (consts_start, _) = unsafe { crate::length_word::const_segment_for_code(new_code_obj) };
        self.code_start = new_code_obj.cast::<u8>();
        self.code_end = consts_start.cast::<u8>();
        self.pc = self.code_start;

        // Run the callee to its top-level Returned (retPC == 0 sentinel).
        // This RE-ENTERS the interpreter (and, for a registered region
        // callee, the region dispatch again — native recursion through the
        // interp). The recursion is bounded by the bytecode's own depth.
        let run_result = self.run();

        // Restore the saved interpreter state regardless of outcome. The
        // handler register + the handler-frames side stack are restored to
        // exactly what they were before the isolated callee run (the callee
        // is REQUIRED to balance its own SET_HANDLER / DELETE_HANDLER, but a
        // raise that escapes the callee leaves a residual handler frame; the
        // truncate cleans it).
        self.pc = saved_pc;
        self.code_start = saved_start;
        self.code_end = saved_end;
        self.frames.truncate(saved_frames_depth);
        self.handler_sp = saved_handler;
        self.handler_frames_depth
            .truncate(saved_handler_frames_depth);

        match run_result {
            Ok(StepResult::Returned(result)) => {
                // The callee's do_return popped the result off (retPC == 0),
                // leaving sp ABOVE the collapse point. Re-push the result so
                // it sits on top at stack[new_sp] — the layout the native
                // CALL site expects (result on top, args collapsed).
                if self.push(result).is_err() {
                    *exn_packet_out = REGION_EXN_STACKOVERFLOW;
                    return RegionRetC {
                        new_sp: self.sp as i64,
                        raised: 1,
                    };
                }
                RegionRetC {
                    new_sp: self.sp as i64,
                    raised: 0,
                }
            }
            Err(InterpError::UnhandledException) => {
                // RAISE FIDELITY (the gap this method closes): the callee
                // RAISED a real SML exception it did not handle. Because we
                // isolated the interp handler (handler_sp = stack.len()),
                // do_raise_ex / RAISE_EX returned UnhandledException with the
                // REAL packet recorded in `self.exception_packet`. Carry the
                // REAL packet bits back so the do_call hook re-raises it as
                // ITSELF through the interpreter's own (now-restored) handler
                // machinery — byte-identical to a fully interpreted callee
                // whose exception unwinds to the caller's handler. The
                // pervasive Overflow exception ALSO arrives here (raise_overflow
                // → do_raise_ex → no handler), so a real Overflow from a
                // trampolined callee propagates as its OWN packet too, NOT the
                // EXN_OVERFLOW sentinel — still byte-exact, since the hook's
                // do_raise_ex path drives the same machinery raise_overflow
                // would. `self.sp` was reset to the handler register by
                // do_raise_ex (== stack.len(), no handler), but the do_call
                // hook resets sp to its pre-call frame top before re-raising,
                // so new_sp here is informational only.
                let pkt = self
                    .exception_packet
                    .map_or(REGION_EXN_OVERFLOW, |w| w.0 as i64);
                *exn_packet_out = pkt;
                RegionRetC {
                    new_sp: self.sp as i64,
                    raised: 1,
                }
            }
            Err(InterpError::DivByZero) => {
                // FixedInt quot/rem by zero is a HARD interpreter error
                // (InterpError::DivByZero), NOT a catchable SML packet — it
                // never reaches do_raise_ex. Keep the hard sentinel so the
                // do_call hook re-surfaces Err(DivByZero), exactly as a
                // fully interpreted callee would.
                *exn_packet_out = REGION_EXN_DIVZERO;
                RegionRetC {
                    new_sp: self.sp as i64,
                    raised: 1,
                }
            }
            Err(InterpError::StackOverflow) => {
                // A genuine stack-overflow in the callee — HARD error, keep
                // the sentinel (the hook re-surfaces Err(StackOverflow)).
                *exn_packet_out = REGION_EXN_STACKOVERFLOW;
                RegionRetC {
                    new_sp: self.sp as i64,
                    raised: 1,
                }
            }
            Ok(_) | Err(_) => {
                // The callee did not return cleanly and did not raise a
                // recognised exception (an unsupported opcode / NotAClosure /
                // NoAllocator — unreachable for a verified registered region's
                // callee). Surface defensively via the Overflow sentinel so
                // the hook drives a catchable raise rather than reading
                // garbage.
                *exn_packet_out = REGION_EXN_OVERFLOW;
                RegionRetC {
                    new_sp: self.sp as i64,
                    raised: 1,
                }
            }
        }
    }

    /// THE GC-SAFEPOINT SLOW PATH (S4c). Called by a native region's
    /// back-edge poll ONLY when the inline check found the alloc threshold
    /// crossed (`*gc_used_ptr >= gc_trigger`). `live_sp` is the region's
    /// current downward SSA `sp`, which the region published into its
    /// `ExnCtx.live_sp` BEFORE calling here.
    ///
    /// It (1) publishes `self.sp = live_sp` so the GC's `[sp, len)` root
    /// walk covers every value the native region has live on the SHARED
    /// stack, then (2) runs the EXACT top-of-step collection logic
    /// (mod.rs:3541 — `gc_trigger_words > 0 && used >= trigger` →
    /// `request_gc_collect`). After it returns, objects may have MOVED;
    /// the region resumes reading the (now-forwarded) shared stack.
    ///
    /// SOUNDNESS (the block-boundary argument): the region's translator
    /// carries exactly ONE cross-block-live SSA value — the integer `sp`.
    /// Every heap value is on the shared SML stack (the fixed `Box`, a GC
    /// root scanned `[sp, len)`). The back-edge safepoint is at a BLOCK
    /// BOUNDARY (the JUMP_BACK terminator), so no register holds a heap
    /// pointer that could go stale: publishing `sp` and collecting
    /// forwards every root, and the region resumes correctly. The
    /// cache-ptr-across-alloc hazard is a within-block / S4d concern, not
    /// this back-edge case.
    ///
    /// Returns the (unchanged) `live_sp` — the GC does not move the stack
    /// Box, only the heap objects the stack slots POINT at (forwarded in
    /// place), so `sp` is identical after the collection.
    #[doc(hidden)]
    pub fn region_safepoint(&mut self, live_sp: i64) -> i64 {
        // Publish the region's live sp so the root walk covers [sp, len).
        self.sp = live_sp as usize;
        // EXACT top-of-step GC condition (mirror mod.rs:3541-3558).
        if self.gc_trigger_words > 0
            && let Some(used) = self.alloc_space_ref().map(MemorySpace::used_words)
            && used >= self.gc_trigger_words
        {
            let before = used;
            let stack_depth = self.stack_height();
            let new_used = self.request_gc_collect().unwrap_or(before);
            if !crate::env::env_flag("POLYML_GC_QUIET") {
                eprintln!(
                    "  GC[region-safepoint]: {before} -> {new_used} words ({}% retained), stack={stack_depth}",
                    if before > 0 {
                        (new_used * 100) / before
                    } else {
                        0
                    }
                );
            }
        }
        // The stack Box is fixed; sp is unchanged by the collection.
        self.sp as i64
    }

    /// THE GC-SAFE ALLOC TRAMPOLINE (S4d). Called by a native region at an
    /// allocation opcode (TUPLE / CLOSURE / ALLOC_* / etc.) BEFORE it
    /// bump-allocates, because the interpreter's `allocate` (mod.rs:5470)
    /// NEVER triggers a GC — it bump-allocates and fails clean (a terminal
    /// `HeapExhausted`) on exhaustion.
    /// The ONLY GC in the interpreter is the top-of-step threshold check
    /// (mod.rs:3662). So a region alloc must go through THIS trampoline,
    /// which:
    ///   (1) publishes `self.sp = live_sp` so a collection's `[sp, len)`
    ///       root walk covers everything the region has live on the SHARED
    ///       stack (the args/operands of the alloc + every loop var);
    ///   (2) runs the EXACT top-of-step GC condition (collect iff
    ///       `gc_trigger_words > 0 && used >= trigger`) — the SAME check the
    ///       interpreter does before each step;
    ///   (3) bump-allocates `n_words` with `flags` and returns the new
    ///       object's BODY pointer (bits).
    ///
    /// After this returns, every heap object MAY have MOVED. The new-object
    /// pointer it returns is a TO-SPACE pointer valid until the NEXT
    /// allocation. THE CALLER'S DISCIPLINE (the make-or-break, enforced in
    /// the memtrans lowering, NOT here): the region must re-read every
    /// operand (field values, init value, base pointers) from the
    /// (forwarded) SHARED STACK *after* this returns — it must NEVER hold a
    /// stack-loaded heap pointer in a register across this call.
    ///
    /// SOUNDNESS / NO ALIASING UB: identical discipline to
    /// `region_safepoint` / `region_interp_call` — the only live
    /// `&mut Interpreter` up the call stack is the outer `do_call` hook's
    /// `&mut self`, dormant for the whole region call, so the transient
    /// `&mut` the C-ABI shim reconstructs here never aliases a *used* one.
    ///
    /// Returns the body pointer (bits) on success, or 0 on a NoAllocator /
    /// post-GC exhaustion error (the region treats 0 as a hard failure: the
    /// shim raises StackOverflow rather than let the region deref null —
    /// matching the interpreter's fail-clean HeapExhausted as a trapped error).
    #[doc(hidden)]
    #[must_use]
    pub fn region_alloc(&mut self, live_sp: i64, n_words: i64, flags: i64) -> i64 {
        // (1) Publish the region's live sp so a collection forwards [sp,len).
        self.sp = live_sp as usize;
        // (2) EXACT top-of-step GC condition (mirror mod.rs:3662-3679). The
        //     region may have allocated since the last poll, so re-check.
        if self.gc_trigger_words > 0
            && let Some(used) = self.alloc_space_ref().map(MemorySpace::used_words)
            && used >= self.gc_trigger_words
        {
            let before = used;
            let stack_depth = self.stack_height();
            let new_used = self.request_gc_collect().unwrap_or(before);
            if !crate::env::env_flag("POLYML_GC_QUIET") {
                eprintln!(
                    "  GC[region-alloc]: {before} -> {new_used} words ({}% retained), stack={stack_depth}",
                    if before > 0 {
                        (new_used * 100) / before
                    } else {
                        0
                    }
                );
            }
        }
        // (3) Bump-allocate post-GC. On exhaustion / no allocator return 0.
        if n_words < 0 {
            return 0;
        }
        match self.allocate(n_words as usize, flags as u8) {
            Ok(p) => p as i64,
            Err(_) => 0,
        }
    }

    /// Raw bits of a `*const usize` pointing at the LIVE heap
    /// words-allocated counter (`MemorySpace.used`), or 0 if no heap is
    /// attached. The do_call hook copies this into the region's
    /// `ExnCtx.gc_used_ptr` so the inline back-edge poll reads the SAME
    /// counter the top-of-step GC check reads (mod.rs:3542). The address
    /// is stable while the heap lives (the heap is a fixed `Box` inside
    /// the Runtime, and the poll runs only under the giant lock, on the
    /// mutator thread, between this hook and the region's return).
    #[doc(hidden)]
    #[must_use]
    pub fn region_gc_used_ptr(&self) -> i64 {
        self.alloc_space_ref()
            .map_or(0, |s| std::ptr::addr_of!(s.used) as i64)
    }

    /// The GC trigger word count for the region's poll, as an `i64`:
    /// `gc_trigger_words` when GC is enabled, else `i64::MAX` (so the poll
    /// — `used >= trigger` — never trips, matching the interpreter's
    /// `gc_trigger_words > 0` guard).
    #[doc(hidden)]
    #[must_use]
    pub fn region_gc_trigger(&self) -> i64 {
        if self.gc_trigger_words > 0 {
            self.gc_trigger_words as i64
        } else {
            i64::MAX
        }
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

    /// Execute a single instruction. Back-compat wrapper over the fully
    /// instrumented code path; external loops (tests, the old `run`) keep
    /// their exact behaviour.
    #[inline]
    pub fn step(&mut self) -> Result<StepResult, InterpError> {
        self.step_impl::<true>()
    }

    /// Run up to `max_steps` instructions in a tight in-crate loop and return
    /// `(steps_executed, terminating_result)`. The step count is reported on
    /// BOTH the success and the error path: the error variant of the inner
    /// `Result` does not carry a count, so returning it alongside `steps`
    /// keeps the executed-step total honest even when the run halts on a
    /// fault (e.g. stack overflow). Previously a `?`-propagated error
    /// discarded the local counter, so callers reported "Executed 0 steps"
    /// for a run that had executed billions before faulting.
    ///
    /// Picks the instrumented vs fast code path ONCE: in production (no
    /// `--profile`, no RTS trace) the fast path is monomorphised with the
    /// per-step trace/diag branches compiled out entirely. GC and finish
    /// cadence are byte-identical to `step()` — only the always-off debug
    /// checks differ — so timing/GC behaviour is unchanged. (Perf lever,
    /// task #88: hoists the per-step global checks the CLI loop used to pay
    /// across the crate boundary on every opcode.)
    pub fn run_until(&mut self, max_steps: u64) -> (u64, Result<StepResult, InterpError>) {
        // ---- Concurrency (3c): become THE running mutator for the
        // duration of this run. Register this thread's handle (if not
        // already), then acquire the giant lock — publishing our roots
        // while we wait (so a GC firing on the running peer can scan us),
        // retracting them the instant we win the lock. On the
        // single-threaded floor there is no peer and no GC in flight, so
        // acquire returns immediately and the step count is byte-identical.
        let runtime = Arc::clone(&self.runtime);
        let handle = Arc::clone(&self.handle);
        // The forked-child entry acquires the lock itself (to retract its
        // pre-published ForkRoots and read back the forwarded closure)
        // before seeding its stack, so it enters here already holding the
        // lock — acquiring again would deadlock. Consume the one-shot flag.
        let entered_holding = self.holds_lock_on_entry;
        self.holds_lock_on_entry = false;
        if entered_holding {
            // The child was registered (with published ForkRoots) by its
            // PARENT before the spawn, so it is already in the registry with
            // the invariant satisfied; nothing to register here. (Defensive:
            // a child must arrive already registered.)
            debug_assert!(
                self.registered,
                "a lock-holding (forked child) entry must already be registered"
            );
        } else {
            // H1 (structural): the FIRST acquire registers-and-acquires
            // atomically (no bare register, no None-while-registered window);
            // subsequent acquires just publish + wait. `acquire_running`
            // sets `self.registered` on its first call.
            self.acquire_running();
        }

        let instrumented = self.diag.is_some() || arbint_trace_on() || crate::rts::is_traced();
        let result = if instrumented {
            self.run_until_impl::<true>(max_steps)
        } else {
            self.run_until_impl::<false>(max_steps)
        };

        // ---- Release the giant lock on leaving the interpreter loop, but
        // STAY REGISTERED with PUBLISHED roots (B2): there must be no
        // release-while-registered that leaves parked_roots == None, or a
        // peer's GC would skip our live stack. We must distinguish two
        // exits, because between calls the OWNING thread may run lock-free
        // driver code that mutates `self` (the REPL re-seeding, the test's
        // chunk loop) — and the collector forwards a published capture by
        // WRITING BACK into `self`, which would race that driver code:
        //
        //  * TERMINAL (Returned / Err): the bytecode frame is fully unwound;
        //    nothing on this thread's stack is needed any more (the result
        //    is returned BY VALUE). We QUIESCE — empty the live stack +
        //    null the code/frame/handler/exn roots — so the published
        //    capture is root-free. The collector then forwards/writes-back
        //    nothing live, so a concurrent driver mutating `self` cannot
        //    race a write-back, AND a peer GC has no live root to miss.
        //
        //  * RESUMABLE (Continue / hit max_steps): the caller will re-enter
        //    `run_until` to CONTINUE this exact execution WITHOUT mutating
        //    `self`. Here the live stack DOES root live heap, so we publish
        //    the real capture; it is race-free because the caller does not
        //    touch `self` before the next acquire retracts the slot.
        let terminal = matches!(result, (_, Ok(StepResult::Returned(_)) | Err(_)));
        if terminal {
            self.quiesce_roots();
        }
        let (raw, send) = self.make_send_roots();
        // SAFETY: `send` aliases live `self`; for a TERMINAL exit the
        // capture is root-free (quiesced); for a RESUMABLE exit `self` is
        // not mutated by the caller before the next acquire retracts the
        // slot. The leaked box must stay valid for the WHOLE quiescent
        // window (the published `SendRoots` references it), so we stash it
        // and free it on the next acquire / on thread exit — NOT here.
        unsafe {
            runtime.release_ml_memory(&handle, send);
        }
        self.stash_published_box(raw);
        result
    }

    /// Empty this thread's live GC root state so a published capture taken
    /// immediately afterwards is root-free (B2, the TERMINAL-exit path).
    /// Called only when `run_until` is leaving with a TERMINAL result
    /// (Returned / Err) — the bytecode frame is fully unwound and the result
    /// is returned by value, so nothing here is needed for resumption. After
    /// this, a concurrent peer GC forwarding our published capture writes
    /// back nothing live, eliminating the data race with lock-free driver
    /// code that re-seeds `self` between calls.
    fn quiesce_roots(&mut self) {
        self.sp = self.stack.len(); // live set [sp, len) is now empty
        self.frames.clear();
        self.handler_frames_depth.clear();
        self.handler_sp = self.stack.len();
        self.exception_packet = None;
        self.pc = std::ptr::null();
        self.code_start = std::ptr::null();
        self.code_end = std::ptr::null();
        self.recent_call_targets = [0; 16];
        // NB: thread_object + bootstrap_tail_call are intentionally KEPT —
        // they are per-thread identity/state, not transient frame roots, and
        // are still forwarded (they are not mutated by lock-free driver
        // code; the driver re-seeds the STACK + code, not these).
    }

    /// Wait until every OTHER registered thread has exited, so the process
    /// does not terminate (killing detached child threads) while a forked
    /// SML thread is still running (3f). With real threads OFF there are
    /// never any children, so this returns immediately. The main thread
    /// must NOT hold the giant lock while waiting (it isn't — `run_until`
    /// released it), so children can run + drain.
    pub fn wait_for_children(&self) {
        if !real_threads_enabled() {
            return;
        }
        // P0 exit semantics: after PolyFinish/OS.Process.exit the process
        // EXITS — upstream never joins threads on exit() at all. Peers got
        // a KILL broadcast (the finish check in step_impl) and most drain
        // promptly, but a thread blocked in a parked KERNEL syscall (a
        // stdin read, an accept) cannot be woken by a flag; joining it
        // would hang the exit forever. Like upstream, don't wait: the
        // process teardown reclaims the OS threads.
        if crate::rts::finish_requested().is_some() {
            return;
        }
        loop {
            // Count registered threads that are not us and not exited.
            let snapshot = self.runtime.registry_snapshot();
            let me = Arc::as_ptr(&self.handle);
            let live_others = snapshot
                .iter()
                .filter(|h| {
                    Arc::as_ptr(h) != me
                        && !h.exited.load(std::sync::atomic::Ordering::SeqCst)
                        // Daemon threads (the signal thread parked forever in
                        // PolyWaitForSignal) never return; like upstream, the
                        // process exits without waiting for them.
                        && !h.is_daemon.load(std::sync::atomic::Ordering::SeqCst)
                })
                .count();
            if live_others == 0 {
                return;
            }
            // Wait for a child to exit (block_wake is bumped on exit) — or a
            // bounded sleep as a backstop against missed wakeups.
            let since = self.runtime.block_gen();
            // Re-check after sampling to avoid a lost-wakeup race.
            let snapshot = self.runtime.registry_snapshot();
            let live_others = snapshot
                .iter()
                .filter(|h| {
                    Arc::as_ptr(h) != me
                        && !h.exited.load(std::sync::atomic::Ordering::SeqCst)
                        // Daemon threads (the signal thread parked forever in
                        // PolyWaitForSignal) never return; like upstream, the
                        // process exits without waiting for them.
                        && !h.is_daemon.load(std::sync::atomic::Ordering::SeqCst)
                })
                .count();
            if live_others == 0 {
                return;
            }
            self.runtime.block_until_event_timeout(since, 50);
        }
    }

    /// Build a `SendRoots` for THIS thread (a boxed `ThreadRoots` capture
    /// + its type-erased thunks). Returns the raw box pointer so the
    /// caller can reclaim it after the publish window closes.
    ///
    /// # Safety
    /// The returned `SendRoots` aliases live `self` state; it is valid
    /// only while `self` is not mutated (i.e. while this thread is parked
    /// / waiting for the giant lock). The caller MUST reclaim the box with
    /// `Box::from_raw` once the slot is retracted.
    fn make_send_roots(&mut self) -> (*mut ThreadRoots, crate::sched::SendRoots) {
        let roots: Box<ThreadRoots> = Box::new(ThreadRoots::capture(self));
        let raw = Box::into_raw(roots);
        let send = crate::sched::SendRoots {
            ptr: raw.cast::<()>(),
            forward: ThreadRoots::forward_thunk,
            fixup: ThreadRoots::fixup_thunk,
            audit: ThreadRoots::audit_thunk,
        };
        (raw, send)
    }

    /// Stash the leaked `ThreadRoots` box published on a quiescent
    /// `run_until` release (B2). Frees any previously-stashed box first
    /// (only reachable after its slot was retracted by an intervening
    /// acquire), then records the new one so it outlives the whole
    /// quiescent window during which the published `SendRoots` references
    /// it. The box is finally freed by the next [`Self::acquire_running`]
    /// (after it retracts the slot) or by this method's free-prior step.
    fn stash_published_box(&mut self, raw: *mut ThreadRoots) {
        // INVARIANT: the preceding `acquire_running` (every `run_until`
        // acquires before it releases) already retracted + freed the prior
        // box AND applied its deferred identity write-back, so there must be
        // no outstanding stash here. If one somehow remained, freeing it here
        // (we do NOT hold the giant lock at this point — release just cleared
        // `running`) would also SKIP its deferred identity write-back,
        // leaving `self.thread_object` stale (from-space) for the fresh
        // capture below. That must not happen — assert it.
        debug_assert!(
            self.published_box.is_none(),
            "a stashed quiesced box outlived its acquire (deferred writeback skipped)"
        );
        if let Some(prev) = self.published_box.take() {
            // Leak-guard only (unreachable per the invariant above).
            unsafe { drop(Box::from_raw(prev)) };
        }
        self.published_box = Some(raw);
    }

    /// Whether the stashed published box (if any) was a QUIESCED capture.
    /// Used by `acquire_running` to decide between the keep-published
    /// re-acquire (quiesced: forwarded identity roots live only in the box)
    /// and the fresh-capture acquire (no stash, or a resumable stash on the
    /// single-threaded CLI loop).
    fn stashed_box_is_quiesced(&self) -> bool {
        // SAFETY: we own the stashed box; reading its `quiesced` flag is a
        // plain field read.
        self.published_box.is_some_and(|b| unsafe { (*b).quiesced })
    }

    /// Free the box stashed by the last quiescent release, if any. Called
    /// right after an acquire retracts the published slot (so no reader
    /// references it).
    ///
    /// (LOW, round 2) BEFORE freeing, apply the DEFERRED quiesced identity
    /// write-back: a quiesced capture's `apply_fixups` deliberately does NOT
    /// reach into the (lock-free, between-`run_until`) owning thread's `self`
    /// — so the collector forwarded this thread's identity roots (thread
    /// object + bootstrap tail) IN PLACE in this box but never wrote them
    /// back. Now that WE hold the giant lock (the acquire that called us just
    /// retracted the slot and the collector is done), copy the forwarded
    /// identity values out of the box into `self` — race-free by construction
    /// (we own `self` and the lock; no collector can be mid-forward). A
    /// resumable box already wrote these back from the collector, but it is
    /// harmless/idempotent to re-copy the same (forwarded) values.
    fn free_published_box(&mut self) {
        if let Some(prev) = self.published_box.take() {
            // SAFETY: acquire set parked_roots = None before returning, so
            // the collector can no longer reach this box; we are the sole
            // owner now. Read the (forwarded) identity slots, then reclaim.
            unsafe {
                let b = &*prev;
                if b.quiesced {
                    if b.thread_obj_present {
                        self.thread_object = Some(b.thread_obj_slot);
                    }
                    self.bootstrap_tail_call = b.bootstrap_tail_slot;
                }
                drop(Box::from_raw(prev));
            }
        }
    }

    /// Acquire the giant mutator lock, publishing our roots while we wait.
    ///
    /// H1 (structural): the FIRST acquire of a not-yet-registered thread
    /// REGISTERS + publishes + acquires atomically under a single scheduler
    /// lock acquisition ([`Runtime::register_and_acquire_ml_memory`]), so the
    /// handle never appears in the registry as "registered, not-running,
    /// `parked_roots == None`" — closing the generic register-path TOCTOU
    /// (the analogue of the fork B1 window). Subsequent acquires (the REPL
    /// driver re-entering `run_until`) take the plain publishing acquire.
    fn acquire_running(&mut self) {
        let runtime = Arc::clone(&self.runtime);
        let handle = Arc::clone(&self.handle);
        let trace = crate::env::env_flag("POLY_THREAD_TRACE");
        if trace {
            eprintln!("[thread] acquire_running: waiting for giant lock");
        }

        // Re-acquire after a QUIESCED release keeps the already-published box
        // as the slot (it holds the forwarded identity roots) — see
        // `reacquire_kept_published`.
        if self.registered && self.stashed_box_is_quiesced() {
            self.reacquire_kept_published(&runtime, &handle);
            if trace {
                eprintln!("[thread] acquire_running: GOT giant lock (kept-published)");
            }
            return;
        }

        let (raw, send) = self.make_send_roots();
        // SAFETY: `send` aliases live `self`; we are about to block in
        // acquire (so `self` is frozen), and acquire retracts the slot
        // (sets it None) before returning. We then reclaim the box.
        unsafe {
            if self.registered {
                runtime.acquire_ml_memory(&handle, send);
            } else {
                // Register-and-acquire atomically: publish roots, push into
                // the registry, then wait — all without releasing `inner`,
                // so the invariant holds from the instant we are visible.
                runtime.register_and_acquire_ml_memory(&handle, send);
                self.registered = true;
            }
            drop(Box::from_raw(raw));
        }
        // The acquire just retracted the slot (set it None), so any box
        // published on the PREVIOUS quiescent release is now unreferenced —
        // free it (B2 lifetime management).
        self.free_published_box();
        if trace {
            eprintln!("[thread] acquire_running: GOT giant lock");
        }
    }

    /// Re-acquire after a QUIESCED `run_until` release (LOW, round 2).
    ///
    /// A terminal `run_until` exit published a QUIESCED capture box and
    /// stashed it (`published_box`). Its `apply_fixups` deliberately does NOT
    /// write the forwarded identity roots back into `self` (the lock-free
    /// between-`run_until` driver owns `&mut self`, so a collector write into
    /// `self` would be a data race / aliasing violation). So the forwarded
    /// identity roots live ONLY in that box.
    ///
    /// Therefore we MUST NOT take a FRESH capture and publish it:
    /// `self.thread_object` may be a STALE from-space pointer (a peer GC
    /// forwarded the box but not `self`), so a fresh capture would publish a
    /// dangling root and a GC during the acquire-wait would chase it → UAF.
    /// Instead KEEP the already-published quiesced box as the slot (it holds
    /// the current forwarded identity roots), wait, retract on win, and only
    /// THEN — holding the giant lock, collector done — copy the forwarded
    /// identity values out of the box into `self` (`free_published_box`). This
    /// is the keep-published discipline, reused (the child fork path uses the
    /// same primitive).
    ///
    /// (A RESUMABLE stash — `run_until` returned Continue / max_steps — is
    /// NON-quiesced and is handled by the fresh-capture path in
    /// `acquire_running`; it only occurs on the single-threaded CLI step-cap
    /// loop, where no peer can fire a GC during the park, so `self` is never
    /// stale and the fresh-capture path is sound + byte-identical.)
    fn reacquire_kept_published(
        &mut self,
        runtime: &Arc<crate::sched::Runtime>,
        handle: &Arc<crate::sched::ThreadHandle>,
    ) {
        debug_assert!(
            handle.parked_roots.lock().unwrap().is_some(),
            "a stashed published box must still be the published slot on re-acquire"
        );
        runtime.acquire_ml_memory_keep_published(handle);
        // Retracted; now apply the box's forwarded identity write-back + free
        // it (race-free: we hold the lock).
        self.free_published_box();
    }

    #[inline]
    fn run_until_impl<const INSTR: bool>(
        &mut self,
        max_steps: u64,
    ) -> (u64, Result<StepResult, InterpError>) {
        let mut steps = 0u64;
        loop {
            if steps >= max_steps {
                return (steps, Ok(StepResult::Continue));
            }
            // Coarse safepoint poll, one check per 65536 steps (so the hot
            // loop is unaffected, ~ms-scale latency).
            if steps & 0xFFFF == 0 {
                // Safepoint (3c): if a peer thread requested a GC, park here
                // — publishing this thread's roots so the collector can
                // forward our stack — until the collection finishes.
                // Single-threaded: `gc_requested` is never set by a peer (we
                // ARE the only thread), so this never fires and the step
                // count is unchanged.
                if self.runtime.gc_requested_poll() {
                    self.safepoint_park();
                }
                // Per-thread interrupt/kill request (3f) routed via the
                // handle (Thread.interrupt / Thread.kill).
                match self.check_thread_requests() {
                    Ok(StepResult::Continue) => {}
                    Ok(other) => return (steps, Ok(other)),
                    Err(e) => return (steps, Err(e)),
                }
                // Async SIGINT (Ctrl-C): raise the SML `Interrupt`
                // exception, which unwinds to the nearest handler (e.g. the
                // REPL top level) or halts the run if none.
                if crate::interrupt::take_interrupt() {
                    match self.raise_interrupt() {
                        Ok(StepResult::Continue) => {}
                        Ok(other) => return (steps, Ok(other)),
                        Err(e) => return (steps, Err(e)),
                    }
                }
                // Cooperative yield (3f): hand the giant lock to a waiting
                // peer so threads interleave. No-op when single-threaded
                // (registry_len <= 1), so the floor is unaffected.
                self.cooperative_yield();
            }
            // BURST: run instructions inside ONE function frame up to the
            // next safepoint boundary (or max_steps). The per-call
            // architecture reloaded ALL hot interpreter state (pc, sp,
            // code bounds, stack base) from `self` memory at EVERY
            // instruction — `step_burst` inlines the step body once into
            // its loop, so LLVM keeps that state in registers ACROSS
            // instructions. The quota stops exactly at the 65536 boundary,
            // so the safepoint cadence (and every observable step count)
            // is byte-identical to the per-call loop.
            #[allow(clippy::cast_possible_truncation)]
            let quota = (0x10000 - (steps & 0xFFFF)).min(max_steps - steps) as u32;
            let (did, r) = self.step_burst::<INSTR>(quota);
            steps += u64::from(did);
            match r {
                Ok(StepResult::Continue) => {}
                Ok(other) => return (steps, Ok(other)),
                Err(e) => return (steps, Err(e)),
            }
        }
    }

    /// Would the auto-GC trigger fire right now? (The fast tier gates on
    /// this ONCE per run: its opcodes never allocate, so the condition
    /// cannot newly arise inside the tier.)
    #[inline]
    fn gc_trigger_met(&self) -> bool {
        self.gc_trigger_words > 0
            && self
                .alloc_space_ref()
                .is_some_and(|s| s.used_words() >= self.gc_trigger_words)
    }

    /// Execute up to `quota` instructions inside one frame (see the burst
    /// note in `run_until_impl`). Returns how many instructions were
    /// executed and the first non-`Continue` outcome (if any).
    ///
    /// ## The FAST TIER
    ///
    /// The hottest opcodes (~half of all dynamic steps: local pushes,
    /// small constants, stack resets, byte jumps) are pure register
    /// machine work — no allocation, no calls, no raising. The per-call
    /// architecture made every one of them pay a `step_one` call plus a
    /// reload of pc/sp/bounds from `self` memory, PLUS the per-step
    /// finish-flag and GC-trigger checks. The tier runs them from LOCAL
    /// variables (pc, sp, stack base, code bounds), committing back to
    /// `self` when it exits.
    ///
    /// Soundness containment:
    /// - Entry gates: skipped entirely under `INSTR` (per-step
    ///   diagnostics semantics), when PolyFinish is pending, or when the
    ///   GC trigger is already met — and fast ops cannot make any of
    ///   those newly true.
    /// - REPLAY discipline: every arm validates against the locals and
    ///   commits only on full success; on any fault (bounds, underflow,
    ///   unknown opcode) it breaks with pc/sp still at the instruction
    ///   START, and the general `step_one` re-executes that instruction,
    ///   raising the canonical error — byte-identical error behavior.
    /// - The stack is a fixed `Box<[PolyWord]>` (never reallocates), so
    ///   the cached base pointer is stable; sp moves only via the same
    ///   checked arithmetic the primitives use.
    #[allow(clippy::inline_always)]
    #[allow(clippy::too_many_lines)]
    fn step_burst<const INSTR: bool>(
        &mut self,
        quota: u32,
    ) -> (u32, Result<StepResult, InterpError>) {
        use opcodes::{
            INSTR_CALL_CONST_ADDR8_0, INSTR_CONST_0, INSTR_CONST_1, INSTR_CONST_2,
            INSTR_CONST_INT_B, INSTR_EQUAL_WORD, INSTR_FIXED_ADD, INSTR_FIXED_SUB,
            INSTR_INDIRECT_LOCAL_B0, INSTR_INDIRECT_LOCAL_B1, INSTR_JUMP_BACK8,
            INSTR_JUMP_NEQ_LOCAL, INSTR_JUMP8, INSTR_JUMP8_FALSE, INSTR_LESS_EQ_UNSIGNED,
            INSTR_LESS_SIGNED, INSTR_LOCAL_0, INSTR_LOCAL_7, INSTR_LOCAL_B, INSTR_RESET_1,
            INSTR_RESET_R_2, INSTR_RETURN_1, INSTR_SET_STACK_VAL_B, INSTR_WORD_ADD,
        };
        let mut done = 0u32;
        while done < quota {
            if !INSTR
                && !self.untrusted
                && crate::rts::finish_requested().is_none()
                && !self.gc_trigger_met()
                && !self.code_start.is_null()
            {
                // ---- FAST TIER (locals) ----
                let mut pc = self.pc;
                let mut sp = self.sp;
                let mut code_start = self.code_start;
                let mut code_end = self.code_end;
                let base: *mut PolyWord = self.stack.as_mut_ptr();
                let stack_len = self.stack.len();
                while done < quota {
                    if pc >= code_end {
                        break; // fault → replay on the general path
                    }
                    // SAFETY: pc < code_end (live code bytes).
                    let op = unsafe { *pc };
                    match op {
                        INSTR_CONST_0 | INSTR_CONST_1 | INSTR_CONST_2 => {
                            if sp == 0 {
                                break;
                            }
                            sp -= 1;
                            // SAFETY: sp < stack_len (checked non-zero, decremented).
                            unsafe {
                                *base.add(sp) = PolyWord::tagged((op - INSTR_CONST_0) as isize);
                            }
                            // SAFETY: pc+1 <= code_end.
                            pc = unsafe { pc.add(1) };
                        }
                        INSTR_CONST_INT_B => {
                            // SAFETY GATE: operand byte must be in bounds.
                            if unsafe { pc.add(1) } >= code_end || sp == 0 {
                                break;
                            }
                            // SAFETY: pc+1 < code_end checked.
                            let b = unsafe { *pc.add(1) };
                            sp -= 1;
                            // SAFETY: sp < stack_len.
                            unsafe {
                                *base.add(sp) = PolyWord::tagged(isize::from(b));
                            }
                            // SAFETY: pc+2 <= code_end.
                            pc = unsafe { pc.add(2) };
                        }
                        INSTR_LOCAL_0..=INSTR_LOCAL_7 => {
                            let depth = (op - INSTR_LOCAL_0) as usize;
                            let idx = sp + depth;
                            if idx >= stack_len || sp == 0 {
                                break;
                            }
                            // SAFETY: idx < stack_len; sp-1 < stack_len.
                            unsafe {
                                let v = *base.add(idx);
                                sp -= 1;
                                *base.add(sp) = v;
                            }
                            // SAFETY: pc+1 <= code_end.
                            pc = unsafe { pc.add(1) };
                        }
                        INSTR_RESET_1 => {
                            if sp + 1 > stack_len {
                                break;
                            }
                            sp += 1;
                            // SAFETY: pc+1 <= code_end.
                            pc = unsafe { pc.add(1) };
                        }
                        INSTR_JUMP8 => {
                            if unsafe { pc.add(1) } >= code_end {
                                break;
                            }
                            // SAFETY: pc+1 < code_end.
                            let off = unsafe { *pc.add(1) } as usize;
                            // fetch advanced past the operand, then offset.
                            // SAFETY: pointer arithmetic within/one-past the
                            // code object, validated below.
                            let new_pc = unsafe { pc.add(2 + off) };
                            if new_pc < code_start || new_pc >= code_end {
                                break; // replay → canonical PcOutOfBounds
                            }
                            pc = new_pc;
                        }
                        INSTR_JUMP8_FALSE => {
                            if unsafe { pc.add(1) } >= code_end || sp >= stack_len {
                                break;
                            }
                            // SAFETY: pc+1 < code_end; sp < stack_len.
                            let off = unsafe { *pc.add(1) } as usize;
                            let v = unsafe { *base.add(sp) };
                            let taken_pc = unsafe { pc.add(2 + off) };
                            let fall_pc = unsafe { pc.add(2) };
                            if v == PolyWord::tagged(0) {
                                if taken_pc < code_start || taken_pc >= code_end {
                                    break;
                                }
                                sp += 1;
                                pc = taken_pc;
                            } else {
                                sp += 1;
                                pc = fall_pc;
                            }
                        }
                        INSTR_SET_STACK_VAL_B => {
                            if unsafe { pc.add(1) } >= code_end || sp >= stack_len {
                                break;
                            }
                            // SAFETY: pc+1 < code_end.
                            let idx = unsafe { *pc.add(1) } as usize;
                            if idx == 0 {
                                break; // replay → canonical StackUnderflow
                            }
                            // pop, then write sp[idx-1] with the popped sp.
                            let target = sp + 1 + (idx - 1);
                            if target >= stack_len {
                                break;
                            }
                            // SAFETY: sp < stack_len; target < stack_len.
                            unsafe {
                                let u = *base.add(sp);
                                *base.add(target) = u;
                            }
                            sp += 1;
                            // SAFETY: pc+2 <= code_end.
                            pc = unsafe { pc.add(2) };
                        }
                        INSTR_JUMP_BACK8 => {
                            if unsafe { pc.add(1) } >= code_end {
                                break;
                            }
                            // SAFETY: pc+1 < code_end. new_pc = (pc+2) −
                            // (off+2) = pc − off (see the general arm's
                            // derivation).
                            let off = unsafe { *pc.add(1) } as usize;
                            let new_pc = (pc as usize).wrapping_sub(off) as *const u8;
                            if new_pc < code_start || new_pc >= code_end {
                                break; // replay → canonical PcOutOfBounds
                            }
                            pc = new_pc;
                        }
                        INSTR_JUMP_NEQ_LOCAL => {
                            // Operands: depth, want, off at pc+1..=pc+3.
                            if unsafe { pc.add(3) } >= code_end {
                                break;
                            }
                            // SAFETY: pc+1..pc+3 < code_end.
                            let (depth, want, off) =
                                unsafe { (*pc.add(1) as usize, *pc.add(2), *pc.add(3) as usize) };
                            let idx = sp + depth;
                            if idx >= stack_len {
                                break;
                            }
                            // SAFETY: idx < stack_len.
                            let u = unsafe { *base.add(idx) };
                            if u.is_tagged() && u.untag() == isize::from(want) {
                                // equal → fall through
                                // SAFETY: pc+4 <= code_end.
                                pc = unsafe { pc.add(4) };
                            } else {
                                // SAFETY: arithmetic validated below.
                                let new_pc = unsafe { pc.add(4 + off) };
                                if new_pc < code_start || new_pc >= code_end {
                                    break;
                                }
                                pc = new_pc;
                            }
                        }
                        INSTR_FIXED_SUB | INSTR_FIXED_ADD => {
                            // pop x, pop y, push tagged(y∓x); overflow →
                            // replay (the general arm raises SML Overflow).
                            if sp + 1 >= stack_len {
                                break;
                            }
                            // SAFETY: sp, sp+1 < stack_len.
                            let (x, y) = unsafe { (*base.add(sp), *base.add(sp + 1)) };
                            let t = if op == INSTR_FIXED_SUB {
                                (y.untag() as i128) - (x.untag() as i128)
                            } else {
                                (x.untag() as i128) + (y.untag() as i128)
                            };
                            if t < crate::poly_word::MIN_TAGGED as i128
                                || t > crate::poly_word::MAX_TAGGED as i128
                            {
                                break; // overflow → replay raises
                            }
                            sp += 1;
                            // SAFETY: sp < stack_len.
                            #[allow(clippy::cast_possible_truncation)]
                            unsafe {
                                *base.add(sp) = PolyWord::tagged(t as isize);
                            }
                            // SAFETY: pc+1 <= code_end.
                            pc = unsafe { pc.add(1) };
                        }
                        INSTR_LESS_SIGNED => {
                            // pop x, pop y, push tagged(y < x) — raw-word
                            // signed compare, exactly `bin_op_cmp`.
                            if sp + 1 >= stack_len {
                                break;
                            }
                            // SAFETY: sp, sp+1 < stack_len.
                            let (x, y) = unsafe { (*base.add(sp), *base.add(sp + 1)) };
                            sp += 1;
                            // SAFETY: sp < stack_len.
                            unsafe {
                                *base.add(sp) =
                                    PolyWord::tagged(isize::from((y.0 as isize) < (x.0 as isize)));
                            }
                            // SAFETY: pc+1 <= code_end.
                            pc = unsafe { pc.add(1) };
                        }
                        INSTR_RESET_R_2 => {
                            // pop top, drop 2, push top back (`reset(2)`).
                            let new_sp = sp + 2;
                            if new_sp >= stack_len {
                                break;
                            }
                            // SAFETY: sp < new_sp < stack_len.
                            unsafe {
                                let top = *base.add(sp);
                                *base.add(new_sp) = top;
                            }
                            sp = new_sp;
                            // SAFETY: pc+1 <= code_end.
                            pc = unsafe { pc.add(1) };
                        }
                        INSTR_CALL_CONST_ADDR8_0 => {
                            // Frontier op: SYNC → the proven general-path
                            // helpers → RELOAD (the call switches code
                            // objects, so code bounds change; it touches
                            // only the ML stack + frames — no allocation,
                            // no GC/finish state change — so no re-gating
                            // is needed).
                            if unsafe { pc.add(1) } >= code_end {
                                break;
                            }
                            // SAFETY: pc+1 < code_end.
                            let imm = unsafe { *pc.add(1) } as usize;
                            self.pc = unsafe { pc.add(2) };
                            self.sp = sp;
                            done += 1;
                            // SAFETY: same contract as the general arm
                            // (read_pc_const validates in untrusted mode).
                            let call = unsafe { self.read_pc_const(imm, 3) }
                                .and_then(|closure| self.do_call(closure));
                            if let Err(e) = call {
                                return (done, Err(e));
                            }
                            pc = self.pc;
                            sp = self.sp;
                            code_start = self.code_start;
                            code_end = self.code_end;
                            if code_start.is_null() {
                                break;
                            }
                            continue;
                        }
                        INSTR_RETURN_1 => {
                            // Frontier op: sync → do_return(1) → reload
                            // (returns restore the caller's code bounds).
                            self.pc = unsafe { pc.add(1) };
                            self.sp = sp;
                            done += 1;
                            match self.do_return(1) {
                                Ok(StepResult::Continue) => {}
                                other => return (done, other),
                            }
                            pc = self.pc;
                            sp = self.sp;
                            code_start = self.code_start;
                            code_end = self.code_end;
                            if code_start.is_null() {
                                break;
                            }
                            continue;
                        }
                        INSTR_LOCAL_B => {
                            // Operand-depth local push (`dup_local(b)`).
                            if unsafe { pc.add(1) } >= code_end || sp == 0 {
                                break;
                            }
                            // SAFETY: pc+1 < code_end.
                            let depth = unsafe { *pc.add(1) } as usize;
                            let idx = sp + depth;
                            if idx >= stack_len {
                                break;
                            }
                            // SAFETY: idx < stack_len; sp-1 < stack_len.
                            unsafe {
                                let v = *base.add(idx);
                                sp -= 1;
                                *base.add(sp) = v;
                            }
                            // SAFETY: pc+2 <= code_end.
                            pc = unsafe { pc.add(2) };
                        }
                        INSTR_INDIRECT_LOCAL_B0 | INSTR_INDIRECT_LOCAL_B1 => {
                            // push local[depth]'s heap word 0/1 (TRUSTED
                            // path only — the tier gate excludes untrusted
                            // mode, whose validation must not be bypassed).
                            if unsafe { pc.add(1) } >= code_end || sp == 0 {
                                break;
                            }
                            // SAFETY: pc+1 < code_end.
                            let depth = unsafe { *pc.add(1) } as usize;
                            let idx = sp + depth;
                            if idx >= stack_len {
                                break;
                            }
                            // SAFETY: idx < stack_len.
                            let u = unsafe { *base.add(idx) };
                            if u.is_tagged() {
                                break; // not a pointer → replay (canonical fault)
                            }
                            let field = usize::from(op == INSTR_INDIRECT_LOCAL_B1);
                            let p = u.as_ptr::<PolyWord>();
                            // SAFETY: trusted mode; caller emitted a valid
                            // object reference (same contract as the
                            // general arm); atomic heap read.
                            let val = unsafe { Self::heap_read(p.add(field)) };
                            sp -= 1;
                            // SAFETY: sp < stack_len.
                            unsafe {
                                *base.add(sp) = val;
                            }
                            // SAFETY: pc+2 <= code_end.
                            pc = unsafe { pc.add(2) };
                        }
                        INSTR_EQUAL_WORD | INSTR_LESS_EQ_UNSIGNED => {
                            if sp + 1 >= stack_len {
                                break;
                            }
                            // SAFETY: sp, sp+1 < stack_len.
                            let (x, y) = unsafe { (*base.add(sp), *base.add(sp + 1)) };
                            let b = if op == INSTR_EQUAL_WORD {
                                x.0 == y.0
                            } else {
                                y.0 <= x.0
                            };
                            sp += 1;
                            // SAFETY: sp < stack_len.
                            unsafe {
                                *base.add(sp) = PolyWord::tagged(isize::from(b));
                            }
                            // SAFETY: pc+1 <= code_end.
                            pc = unsafe { pc.add(1) };
                        }
                        INSTR_WORD_ADD => {
                            // Tagged word add: y + x − TAG (`bin_op_word`).
                            if sp + 1 >= stack_len {
                                break;
                            }
                            // SAFETY: sp, sp+1 < stack_len.
                            let (x, y) = unsafe { (*base.add(sp), *base.add(sp + 1)) };
                            let r = y.0.wrapping_add(x.0).wrapping_sub(PolyWord::tagged(0).0);
                            sp += 1;
                            // SAFETY: sp < stack_len.
                            unsafe {
                                *base.add(sp) = PolyWord::from_bits(r);
                            }
                            // SAFETY: pc+1 <= code_end.
                            pc = unsafe { pc.add(1) };
                        }
                        _ => break, // non-fast opcode → general path
                    }
                    done += 1;
                }
                self.pc = pc;
                self.sp = sp;
                if done >= quota {
                    break;
                }
            }
            // One general step (the instruction the tier declined, or the
            // INSTR/finish/GC-gated mode).
            done += 1;
            match self.step_one::<INSTR>() {
                Ok(StepResult::Continue) => {}
                other => return (done, other),
            }
        }
        (done, Ok(StepResult::Continue))
    }

    /// Execute a single instruction (the out-of-line entry used by the
    /// CLI `step()` drivers, the JIT bridge, and the diff harness; the
    /// hot loop goes through [`Self::step_burst`], which inlines
    /// [`Self::step_one`]'s body directly into its loop).
    fn step_impl<const INSTR: bool>(&mut self) -> Result<StepResult, InterpError> {
        self.step_one::<INSTR>()
    }

    /// Execute a single instruction. `INSTR` selects the instrumented path
    /// (per-step RTS-trace ring, diagnostics counters, RTS step trace); when
    /// `false` those branches vanish at monomorphisation.
    #[allow(clippy::too_many_lines)]
    #[allow(clippy::wildcard_imports)]
    #[inline(always)]
    fn step_one<const INSTR: bool>(&mut self) -> Result<StepResult, InterpError> {
        use opcodes::*;

        // If PolyFinish was just called, halt cleanly with the
        // requested exit code rather than executing junk bytecode
        // past the "exit" point. (Upstream's PolyFinish calls
        // `exit()` and never returns; we don't have that luxury.)
        if let Some(code) = crate::rts::finish_requested() {
            // SINGLE-THREADED (the default): consume-and-clear, exactly as
            // ever — byte-identical.
            //
            // MULTI-THREADED (P0 exit-semantics fix): PolyFinish/
            // OS.Process.exit means the PROCESS exits. The flag used to be
            // consumed by whichever thread stepped next — a CHILD could
            // swallow the exit (its run loop just ends as a normal thread
            // exit) while the exiting program kept running: an inversion.
            // Now: leave the flag SET so every thread (including main,
            // whose Returned(code) is what the CLI turns into the process
            // exit) sees it; broadcast KILL so blocked peers (mutex/
            // condvar/park waiters, the signal daemon) wake and terminate
            // instead of blocking wait_for_children forever.
            if self.runtime.registry_len() > 1 {
                for h in self.runtime.registry_snapshot() {
                    if !std::ptr::eq(Arc::as_ptr(&h), Arc::as_ptr(&self.handle)) {
                        h.requests.store(
                            crate::sched::request::KILL,
                            std::sync::atomic::Ordering::SeqCst,
                        );
                    }
                }
                self.runtime.notify_block_event();
            } else {
                crate::rts::clear_finish_requested();
            }
            return Ok(StepResult::Returned(PolyWord::tagged(code)));
        }

        // Auto-GC: trigger when heap.used reaches the pre-computed
        // threshold. Trigger is 0 when no heap or when POLYML_GC_THRESHOLD
        // selects "disable GC" — either way `used >= 0` would always be
        // true if used == 0, so we also guard on `gc_trigger_words > 0`.
        //
        // Concurrency (3c): we become the COLLECTOR via
        // `request_gc_collect`, which (single-threaded) sees
        // threads_in_heap == 1 immediately and runs the collection inline
        // — byte-identical to the old direct `self.gc()`. With multiple
        // threads it sets gc_requested, waits for every peer to park at
        // its safepoint, then collects every thread's roots.
        if self.gc_trigger_words > 0
            && let Some(used) = self.alloc_space_ref().map(MemorySpace::used_words)
            && used >= self.gc_trigger_words
        {
            let before = used;
            let stack_depth = self.stack_height();
            let new_used = self.request_gc_collect().unwrap_or(before);
            if !crate::env::env_flag("POLYML_GC_QUIET") {
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
        if INSTR && arbint_trace_on() {
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
        if INSTR && let Some(d) = self.diag.as_mut() {
            #[allow(clippy::cast_possible_truncation)]
            let off = unsafe { opcode_pc.offset_from(self.code_start) as u32 };
            let code = self.code_start as usize;
            d.total_steps += 1;
            *d.pc_visits.entry((code, off)).or_insert(0) += 1;
            d.opcode_counts[op as usize] += 1;
        }
        if INSTR && crate::rts::is_traced() {
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
                // SAFETY: just allocated `length` words (ATOMIC init
                // — see do_tuple)
                unsafe {
                    for i in 0..length {
                        Self::heap_write(p.add(i), init);
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
                if self.untrusted {
                    let p =
                        self.untrusted_container_ptr(container_ref, n, "MOVE_TO_CONTAINER_B")?;
                    // SAFETY: validated stack-internal pointer + in-bounds slot.
                    unsafe { p.cast_mut().add(n).write(u) };
                    return Ok(StepResult::Continue);
                }
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
                if self.untrusted {
                    let p =
                        self.untrusted_container_ptr(container_ref, n, "INDIRECT_CONTAINER_B")?;
                    // SAFETY: validated stack-internal pointer + in-bounds slot.
                    let val = unsafe { *p.add(n) };
                    self.pop()?;
                    return self.push_continue(val);
                }
                let ref_ptr = container_ref.0 as *const PolyWord;
                // SAFETY: same as MOVE_TO_CONTAINER_B
                let val = unsafe { *ref_ptr.add(n) };
                self.pop()?;
                self.push_continue(val)
            }

            // ----- Cell introspection (length / flag-byte of a heap obj)
            INSTR_CELL_LENGTH => {
                let v = self.peek(0)?;
                if self.untrusted {
                    let vo = self.validate_obj(v, "CELL_LENGTH")?;
                    let len = crate::length_word::length_of(vo.length_word);
                    self.pop()?;
                    return self.push_continue(PolyWord::tagged(len as isize));
                }
                let p = v.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid object reference
                let lw = unsafe { MemorySpace::length_word_of(p) };
                let len = crate::length_word::length_of(lw);
                self.pop()?;
                self.push_continue(PolyWord::tagged(len as isize))
            }
            INSTR_CELL_FLAGS => {
                let v = self.peek(0)?;
                if self.untrusted {
                    let vo = self.validate_obj(v, "CELL_FLAGS")?;
                    let f = crate::length_word::flags_of(vo.length_word);
                    self.pop()?;
                    return self.push_continue(PolyWord::tagged(isize::from(f)));
                }
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
                if self.untrusted {
                    let v = self.untrusted_field(base, index, "LOAD_ML_WORD")?;
                    self.pop()?;
                    return self.push_continue(v);
                }
                let p = base.as_ptr::<PolyWord>();
                // SAFETY: caller emits valid offsets
                let v = unsafe { Self::heap_read(p.add(index)) };
                self.pop()?;
                self.push_continue(v)
            }
            INSTR_LOAD_ML_BYTE => {
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                if self.untrusted {
                    let vobj = self.validate_obj(base, "LOAD_ML_BYTE")?;
                    vobj.check_byte_range(index, 1)
                        .map_err(|why| InterpError::BadImage {
                            op: "LOAD_ML_BYTE",
                            why,
                        })?;
                    // SAFETY: validated object + in-bounds byte index.
                    let b = unsafe { *vobj.ptr.cast::<u8>().add(index) };
                    self.pop()?;
                    return self.push_continue(PolyWord::tagged(isize::from(b)));
                }
                let p = base.as_ptr::<u8>();
                // SAFETY: caller emits valid offsets
                let b = unsafe { *p.add(index) };
                self.pop()?;
                self.push_continue(PolyWord::tagged(isize::from(b)))
            }
            INSTR_LOAD_UNTAGGED => {
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                if self.untrusted {
                    let v = self.untrusted_field(base, index, "LOAD_UNTAGGED")?;
                    self.pop()?;
                    return self.push_continue(PolyWord::tagged(v.0 as isize));
                }
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
                // SAFETY: caller emits valid offsets (ATOMIC — shared
                // heap word; see heap_read)
                let raw = unsafe { Self::heap_read(p.add(index)) };
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
                if self.untrusted {
                    let v = self.validate_obj(base, "STORE_ML_WORD")?;
                    let bad = v
                        .require_mutable()
                        .and_then(|()| v.require_word_typed())
                        .and_then(|()| v.check_word_index(index));
                    bad.map_err(|why| InterpError::BadImage {
                        op: "STORE_ML_WORD",
                        why,
                    })?;
                    // SAFETY: validated mutable word-typed object + in-bounds index.
                    unsafe { v.ptr.cast_mut().add(index).write(to_store) };
                    self.pop()?;
                    return self.push_continue(PolyWord::tagged(0));
                }
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
                unsafe { Self::heap_write(p.add(index), to_store) };
                self.pop()?;
                self.push_continue(PolyWord::tagged(0))
            }
            INSTR_STORE_ML_BYTE => {
                let to_store = self.pop()?.untag() as u8;
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                if self.untrusted {
                    let v = self.validate_obj(base, "STORE_ML_BYTE")?;
                    let bad = v
                        .require_mutable()
                        .and_then(|()| v.check_byte_range(index, 1));
                    bad.map_err(|why| InterpError::BadImage {
                        op: "STORE_ML_BYTE",
                        why,
                    })?;
                    // SAFETY: validated mutable object + in-bounds byte index.
                    unsafe { v.ptr.cast_mut().cast::<u8>().add(index).write(to_store) };
                    self.pop()?;
                    return self.push_continue(PolyWord::tagged(0));
                }
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
                if self.untrusted {
                    // STORE_UNTAGGED writes raw bits into a word slot of a
                    // mutable byte/word object (e.g. a Word8Array.update or a
                    // mutable boxed-word cell). It must NOT be allowed to
                    // plant a forged pointer into a code object, so require
                    // mutable + an in-bounds word slot.
                    let v = self.validate_obj(base, "STORE_UNTAGGED")?;
                    let bad = v.require_mutable().and_then(|()| v.check_word_index(index));
                    bad.map_err(|why| InterpError::BadImage {
                        op: "STORE_UNTAGGED",
                        why,
                    })?;
                    // SAFETY: validated mutable object + in-bounds word index.
                    // (ATOMIC — shared heap word.)
                    unsafe {
                        Self::heap_write(v.ptr.cast_mut().add(index), PolyWord::from_bits(raw));
                    }
                    self.pop()?;
                    return self.push_continue(PolyWord::tagged(0));
                }
                let p = base.as_ptr::<PolyWord>().cast_mut();
                // SAFETY: caller emits valid offset on mutable base
                // (ATOMIC — shared heap word.)
                unsafe { Self::heap_write(p.add(index), PolyWord::from_bits(raw)) };
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
                let dest_word = self.pop()?;
                let src_off = self.pop()?.untag() as usize;
                let src_word = self.peek(0)?;
                if self.untrusted {
                    let dv = self.validate_obj(dest_word, "BLOCK_MOVE_BYTE")?;
                    let sv = self.validate_obj(src_word, "BLOCK_MOVE_BYTE")?;
                    dv.require_mutable()
                        .and_then(|()| dv.check_byte_range(dest_off, length))
                        .and_then(|()| sv.check_byte_range(src_off, length))
                        .map_err(|why| InterpError::BadImage {
                            op: "BLOCK_MOVE_BYTE",
                            why,
                        })?;
                    // SAFETY: both ranges validated in-bounds; dest mutable.
                    unsafe {
                        std::ptr::copy(
                            sv.ptr.cast::<u8>().add(src_off),
                            dv.ptr.cast_mut().cast::<u8>().add(dest_off),
                            length,
                        );
                    }
                    self.pop()?;
                    return self.push_continue(PolyWord::tagged(0));
                }
                let dest = dest_word.as_ptr::<u8>().cast_mut();
                let src = src_word.as_ptr::<u8>();
                // SAFETY: caller emits valid offsets + lengths
                unsafe { std::ptr::copy(src.add(src_off), dest.add(dest_off), length) };
                self.pop()?;
                self.push_continue(PolyWord::tagged(0))
            }
            // blockMoveWord: same but moves length WORDS (PolyWord-sized).
            INSTR_BLOCK_MOVE_WORD => {
                let length = self.pop()?.untag() as usize;
                let dest_off = self.pop()?.untag() as usize;
                let dest_word = self.pop()?;
                let src_off = self.pop()?.untag() as usize;
                let src_word = self.peek(0)?;
                if self.untrusted {
                    let dv = self.validate_obj(dest_word, "BLOCK_MOVE_WORD")?;
                    let sv = self.validate_obj(src_word, "BLOCK_MOVE_WORD")?;
                    let dest_end = dest_off.checked_add(length);
                    let src_end = src_off.checked_add(length);
                    let ok = dv.require_mutable().is_ok()
                        && dest_end.is_some_and(|e| e <= dv.n_words)
                        && src_end.is_some_and(|e| e <= sv.n_words);
                    if !ok {
                        let why = if dv.require_mutable().is_err() {
                            DerefError::WrongType
                        } else {
                            DerefError::IndexOutOfBounds
                        };
                        return Err(InterpError::BadImage {
                            op: "BLOCK_MOVE_WORD",
                            why,
                        });
                    }
                    // SAFETY: both word ranges validated in-bounds; dest mutable.
                    unsafe {
                        std::ptr::copy(
                            sv.ptr.add(src_off),
                            dv.ptr.cast_mut().add(dest_off),
                            length,
                        );
                    }
                    self.pop()?;
                    return self.push_continue(PolyWord::tagged(0));
                }
                let dest = dest_word.as_ptr::<PolyWord>().cast_mut();
                let src = src_word.as_ptr::<PolyWord>();
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
                let w2 = self.pop()?;
                let off1 = self.pop()?.untag() as usize;
                let w1 = self.peek(0)?;
                let equal = if self.untrusted {
                    let v1 = self.validate_obj(w1, "BLOCK_EQUAL_BYTE")?;
                    let v2 = self.validate_obj(w2, "BLOCK_EQUAL_BYTE")?;
                    v1.check_byte_range(off1, length)
                        .and_then(|()| v2.check_byte_range(off2, length))
                        .map_err(|why| InterpError::BadImage {
                            op: "BLOCK_EQUAL_BYTE",
                            why,
                        })?;
                    // SAFETY: both byte ranges validated in-bounds.
                    unsafe {
                        let s1 = std::slice::from_raw_parts(v1.ptr.cast::<u8>().add(off1), length);
                        let s2 = std::slice::from_raw_parts(v2.ptr.cast::<u8>().add(off2), length);
                        s1 == s2
                    }
                } else {
                    let p2 = w2.as_ptr::<u8>();
                    let p1 = w1.as_ptr::<u8>();
                    // SAFETY: caller emits valid offsets + lengths
                    unsafe {
                        let s1 = std::slice::from_raw_parts(p1.add(off1), length);
                        let s2 = std::slice::from_raw_parts(p2.add(off2), length);
                        s1 == s2
                    }
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
                let w2 = self.pop()?;
                let off1 = self.pop()?.untag() as usize;
                let w1 = self.peek(0)?;
                let ordering = if self.untrusted {
                    let v1 = self.validate_obj(w1, "BLOCK_COMPARE_BYTE")?;
                    let v2 = self.validate_obj(w2, "BLOCK_COMPARE_BYTE")?;
                    v1.check_byte_range(off1, length)
                        .and_then(|()| v2.check_byte_range(off2, length))
                        .map_err(|why| InterpError::BadImage {
                            op: "BLOCK_COMPARE_BYTE",
                            why,
                        })?;
                    // SAFETY: both byte ranges validated in-bounds.
                    unsafe {
                        let s1 = std::slice::from_raw_parts(v1.ptr.cast::<u8>().add(off1), length);
                        let s2 = std::slice::from_raw_parts(v2.ptr.cast::<u8>().add(off2), length);
                        s1.cmp(s2)
                    }
                } else {
                    let p2 = w2.as_ptr::<u8>();
                    let p1 = w1.as_ptr::<u8>();
                    // SAFETY: caller emits valid offsets + lengths
                    unsafe {
                        let s1 = std::slice::from_raw_parts(p1.add(off1), length);
                        let s2 = std::slice::from_raw_parts(p2.add(off2), length);
                        s1.cmp(s2)
                    }
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
                if self.untrusted {
                    let val = self.untrusted_field(u, 0, "INDIRECT_LOCAL_B0")?;
                    return self.push_continue(val);
                }
                let p = u.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid object reference
                let val = unsafe { Self::heap_read(p) };
                self.push_continue(val)
            }
            INSTR_INDIRECT_LOCAL_B1 => {
                let depth = self.fetch_u8()? as usize;
                let u = self.peek(depth)?;
                if self.untrusted {
                    let val = self.untrusted_field(u, 1, "INDIRECT_LOCAL_B1")?;
                    return self.push_continue(val);
                }
                let p = u.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid object reference
                let val = unsafe { Self::heap_read(p.add(1)) };
                self.push_continue(val)
            }
            INSTR_INDIRECT_0_LOCAL_0 => {
                let u = self.peek(0)?;
                if self.untrusted {
                    let val = self.untrusted_field(u, 0, "INDIRECT_0_LOCAL_0")?;
                    return self.push_continue(val);
                }
                let p = u.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid object reference
                let val = unsafe { Self::heap_read(p) };
                self.push_continue(val)
            }
            INSTR_INDIRECT_LOCAL_BB => {
                let depth = self.fetch_u8()? as usize;
                let slot = self.fetch_u8()? as usize;
                let u = self.peek(depth)?;
                if self.untrusted {
                    let val = self.untrusted_field(u, slot, "INDIRECT_LOCAL_BB")?;
                    return self.push_continue(val);
                }
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
                let u = if self.untrusted {
                    self.untrusted_field(local, 0, "JUMP_NEQ_LOCAL_IND")?
                } else {
                    let p = local.as_ptr::<PolyWord>();
                    // SAFETY: caller emitted a valid tuple reference
                    unsafe { *p }
                };
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
                if self.untrusted {
                    let val =
                        self.untrusted_field(closure_word, 1 + slot, "INDIRECT_CLOSURE_BB")?;
                    return self.push_continue(val);
                }
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
                let w = unsafe { self.read_pc_const(imm, 3) }?;
                self.push_continue(w)
            }
            INSTR_CONST_ADDR8_1 => {
                let imm = self.fetch_u8()? as usize;
                let w = unsafe { self.read_pc_const(imm, 4) }?;
                self.push_continue(w)
            }
            INSTR_CONST_ADDR8_8 => {
                let imm1 = self.fetch_u8()? as usize;
                let imm2 = self.fetch_u8()? as usize;
                let w = unsafe { self.read_pc_const(imm1, imm2 + 3) }?;
                self.push_continue(w)
            }
            INSTR_CONST_ADDR16_8 => {
                let imm1 = self.fetch_u16_le()? as usize;
                let imm2 = self.fetch_u8()? as usize;
                let w = unsafe { self.read_pc_const(imm1, imm2 + 3) }?;
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
                let closure = unsafe { self.read_pc_const(imm, 3) }?;
                self.do_call(closure)?;
                Ok(StepResult::Continue)
            }
            INSTR_CALL_CONST_ADDR8_1 => {
                let imm = self.fetch_u8()? as usize;
                let closure = unsafe { self.read_pc_const(imm, 4) }?;
                self.do_call(closure)?;
                Ok(StepResult::Continue)
            }
            INSTR_CALL_CONST_ADDR8_8 => {
                let imm1 = self.fetch_u8()? as usize;
                let imm2 = self.fetch_u8()? as usize;
                let closure = unsafe { self.read_pc_const(imm1, imm2 + 3) }?;
                self.do_call(closure)?;
                Ok(StepResult::Continue)
            }
            INSTR_CALL_CONST_ADDR16_8 => {
                let imm1 = self.fetch_u16_le()? as usize;
                let imm2 = self.fetch_u8()? as usize;
                let closure = unsafe { self.read_pc_const(imm1, imm2 + 3) }?;
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
                    // UNTRUSTED MODE (task #96, HOLE 4): the inline jump table
                    // `[table_after, table_after + arg1*2)` lives in the code
                    // object's bytecode; `u` (the selector) and `arg1` (the
                    // table size) are both image-controlled. A forged arg1 /
                    // selector can drive `entry` past the code object into the
                    // adjacent arena. Bound the 2-byte read window
                    // `[entry, entry+2)` against the current code object body
                    // before the read; trusted path is byte-identical.
                    if self.untrusted {
                        self.check_case16_table_read(table_after, u as usize)?;
                    }
                    // SAFETY: u in [0, arg1) (trusted), or bounds-checked above.
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
                // SAFETY: just allocated 1 word (ATOMIC init — see do_tuple)
                unsafe { Self::heap_write(p.add(0), PolyWord::tagged(0)) };
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
                let acquired = if self.word0_deref_ok(mutex) {
                    let p = mutex.as_ptr::<PolyWord>().cast_mut();
                    // ATOMIC fetch-add-2 (P3): the counter bump is one
                    // interlocked op, so two threads can't both read
                    // TAGGED(0) and both believe they acquired.
                    // SAFETY: pointer-aligned & is_data_ptr ⇒ valid mutex slot
                    let old = unsafe {
                        Self::atomic_word(p).fetch_add(2, std::sync::atomic::Ordering::AcqRel)
                    };
                    old == PolyWord::tagged(0).0
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
                let acquired = if self.word0_deref_ok(mutex) {
                    let p = mutex.as_ptr::<PolyWord>().cast_mut();
                    // ATOMIC compare-exchange (P3): claim the lock only if
                    // it was TAGGED(0), atomically — no read-then-write race.
                    // SAFETY: pointer-aligned & is_data_ptr ⇒ valid mutex slot
                    unsafe {
                        Self::atomic_word(p)
                            .compare_exchange(
                                PolyWord::tagged(0).0,
                                PolyWord::tagged(1).0,
                                std::sync::atomic::Ordering::AcqRel,
                                std::sync::atomic::Ordering::Acquire,
                            )
                            .is_ok()
                    }
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
                let was_sole_locker = if self.word0_deref_ok(mutex) {
                    let p = mutex.as_ptr::<PolyWord>().cast_mut();
                    // ATOMIC swap (P3): read-old-and-store-TAGGED(0) in one
                    // interlocked op — upstream's AtomicallyReleaseMutex
                    // (native XCHG). The "was I sole locker" answer must be
                    // atomic with the reset or it can lie under contention.
                    // SAFETY: pointer-aligned & is_data_ptr
                    let old = unsafe {
                        Self::atomic_word(p)
                            .swap(PolyWord::tagged(0).0, std::sync::atomic::Ordering::AcqRel)
                    };
                    old == PolyWord::tagged(1).0
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
                let old = if self.word0_deref_ok(obj) {
                    let p = obj.as_ptr::<PolyWord>().cast_mut();
                    // ATOMIC fetch-add (P3): new = old + addend - 1 (raw-tag
                    // arithmetic collapses the doubled tag bit), done in one
                    // interlocked op. Returns the OLD word0.
                    // SAFETY: pointer-aligned & is_data_ptr
                    let delta = addend.0.wrapping_sub(1);
                    let old_bits = unsafe {
                        Self::atomic_word(p).fetch_add(delta, std::sync::atomic::Ordering::AcqRel)
                    };
                    PolyWord::from_bits(old_bits)
                } else {
                    PolyWord::tagged(0)
                };
                // Replace top (the object) with the OLD word0.
                self.pop()?;
                self.push_continue(old)
            }
            // log2(word at top), replace top. (bytecode.cpp:2359-2367.)
            // ----- C-memory load/store (Foreign.Memory get*/set*).
            // Stack (top→down) for loads: offset, index, base; the base
            // is a boxed large-word whose word 0 holds a raw C pointer.
            // `p = *(byte**)base + offset` (offset SIGNED bytes), then
            // `((T*)p)[index]` (index SIGNED elements). bytecode.cpp:2061+.
            // Trusted-only: the base is an unmanaged C pointer no space
            // predicate can validate, so untrusted mode HALTS cleanly
            // (no wild deref) rather than dereferencing it.
            EXTINSTR_LOAD_C8
            | EXTINSTR_LOAD_C16
            | EXTINSTR_LOAD_C32
            | EXTINSTR_LOAD_C64
            | EXTINSTR_LOAD_C_FLOAT
            | EXTINSTR_LOAD_C_DOUBLE => {
                if self.untrusted {
                    return Ok(StepResult::Unimplemented {
                        op: ext,
                        extended: true,
                    });
                }
                let offset = self.pop()?.untag();
                let index = self.pop()?.untag();
                let base = self.peek(0)?;
                // SAFETY: trusted path; base is a boxed large-word (word 0
                // = C pointer). The element address is that pointer plus
                // the signed byte offset plus index*elem_size — an
                // FFI-controlled unmanaged address by contract.
                let cptr = unsafe { (*base.as_ptr::<PolyWord>()).0 };
                let byte_base = (cptr as isize).wrapping_add(offset);
                match ext {
                    EXTINSTR_LOAD_C8 => {
                        // SAFETY: FFI address by contract.
                        let v = unsafe { ((byte_base + index) as *const u8).read_unaligned() };
                        self.pop()?;
                        self.push_continue(PolyWord::tagged(isize::from(v)))
                    }
                    EXTINSTR_LOAD_C16 => {
                        let v = unsafe { ((byte_base + index * 2) as *const u16).read_unaligned() };
                        self.pop()?;
                        self.push_continue(PolyWord::tagged(v as isize))
                    }
                    EXTINSTR_LOAD_C32 => {
                        let v = unsafe { ((byte_base + index * 4) as *const u32).read_unaligned() };
                        // 64-bit host: tagged (bytecode.cpp #ifdef IS64BITS).
                        self.pop()?;
                        self.push_continue(PolyWord::tagged(v as isize))
                    }
                    EXTINSTR_LOAD_C64 => {
                        let v = unsafe { ((byte_base + index * 8) as *const u64).read_unaligned() };
                        self.pop()?;
                        self.alloc_large_word(v as usize)
                    }
                    EXTINSTR_LOAD_C_FLOAT => {
                        // Read a 32-bit float, box as a Real (double).
                        let v = unsafe { ((byte_base + index * 4) as *const f32).read_unaligned() };
                        self.pop()?;
                        let boxed = self.alloc_real(f64::from(v))?;
                        self.push_continue(boxed)
                    }
                    // EXTINSTR_LOAD_C_DOUBLE
                    _ => {
                        let v = unsafe { ((byte_base + index * 8) as *const f64).read_unaligned() };
                        self.pop()?;
                        let boxed = self.alloc_real(v)?;
                        self.push_continue(boxed)
                    }
                }
            }
            // Stores. Stack (top→down): toStore, offset, index, base;
            // result is Zero (unit). bytecode.cpp:2148+.
            EXTINSTR_STORE_C8
            | EXTINSTR_STORE_C16
            | EXTINSTR_STORE_C32
            | EXTINSTR_STORE_C64
            | EXTINSTR_STORE_C_FLOAT
            | EXTINSTR_STORE_C_DOUBLE => {
                if self.untrusted {
                    return Ok(StepResult::Unimplemented {
                        op: ext,
                        extended: true,
                    });
                }
                let value = self.pop()?;
                // For float/double the value is a boxed Real — read it
                // before popping offset/index (read_real borrows self).
                let real = matches!(ext, EXTINSTR_STORE_C_FLOAT | EXTINSTR_STORE_C_DOUBLE)
                    .then(|| self.read_real(value))
                    .transpose()?;
                let offset = self.pop()?.untag();
                let index = self.pop()?.untag();
                let base = self.peek(0)?;
                // SAFETY: trusted path; unmanaged FFI address by contract.
                let cptr = unsafe { (*base.as_ptr::<PolyWord>()).0 };
                let byte_base = (cptr as isize).wrapping_add(offset);
                // SAFETY: FFI address by contract; width per opcode.
                unsafe {
                    match ext {
                        EXTINSTR_STORE_C8 => {
                            ((byte_base + index) as *mut u8).write_unaligned(value.untag() as u8);
                        }
                        EXTINSTR_STORE_C16 => {
                            ((byte_base + index * 2) as *mut u16)
                                .write_unaligned(value.untag() as u16);
                        }
                        EXTINSTR_STORE_C32 => {
                            ((byte_base + index * 4) as *mut u32)
                                .write_unaligned(value.untag() as u32);
                        }
                        EXTINSTR_STORE_C64 => {
                            // value is a boxed large-word (word 0 = raw bits).
                            let raw = (*value.as_ptr::<PolyWord>()).0;
                            ((byte_base + index * 8) as *mut u64).write_unaligned(raw as u64);
                        }
                        EXTINSTR_STORE_C_FLOAT => {
                            #[allow(clippy::cast_possible_truncation)]
                            ((byte_base + index * 4) as *mut f32)
                                .write_unaligned(real.unwrap() as f32);
                        }
                        // EXTINSTR_STORE_C_DOUBLE
                        _ => {
                            ((byte_base + index * 8) as *mut f64).write_unaligned(real.unwrap());
                        }
                    }
                }
                self.stack[self.sp] = PolyWord::tagged(0);
                Ok(StepResult::Continue)
            }
            // ----- C heap alloc/free (Foreign.Memory C-stack path).
            // allocCSpace: top = byte length (tagged); replace with a
            // boxed voidStar of malloc(length). bytecode.cpp:2369.
            EXTINSTR_ALLOC_C_SPACE => {
                if self.untrusted {
                    return Ok(StepResult::Unimplemented {
                        op: ext,
                        extended: true,
                    });
                }
                #[allow(clippy::cast_sign_loss)]
                let len = self.pop()?.untag() as usize;
                // SAFETY: libc malloc with a byte count (null on failure).
                let ptr = unsafe { libc::malloc(len) } as usize;
                self.alloc_large_word(ptr)
            }
            // freeCSpace: stack (top→down) size, addr; pop size, free the
            // pointer in addr's word 0, replace addr with Zero.
            // bytecode.cpp:2378.
            EXTINSTR_FREE_C_SPACE => {
                if self.untrusted {
                    return Ok(StepResult::Unimplemented {
                        op: ext,
                        extended: true,
                    });
                }
                let _size = self.pop()?;
                let addr = self.peek(0)?;
                if addr.is_data_ptr() {
                    // SAFETY: addr is a boxed voidStar (word 0 = the malloc'd
                    // pointer from allocCSpace / PolyFFIMalloc).
                    let ptr = unsafe { (*addr.as_ptr::<PolyWord>()).0 };
                    if ptr != 0 {
                        unsafe { libc::free(ptr as *mut libc::c_void) };
                    }
                }
                self.stack[self.sp] = PolyWord::tagged(0);
                Ok(StepResult::Continue)
            }
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
                if self.untrusted {
                    let field = self.untrusted_field(v, idx, "INDIRECT_W")?;
                    self.pop()?;
                    return self.push_continue(field);
                }
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
                if self.untrusted {
                    let val = self.untrusted_field(closure_word, 1 + item, "INDIRECT_CLOSURE_W")?;
                    self.pop()?;
                    return self.push_continue(val);
                }
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
                if self.untrusted {
                    if p.is_data_ptr() {
                        let v = self.untrusted_field(p, 0, "LONG_W_TO_TAGGED")?;
                        #[allow(clippy::cast_possible_wrap)]
                        let val = v.0 as isize;
                        self.stack[self.sp] = PolyWord::tagged(val);
                    }
                    return Ok(StepResult::Continue);
                }
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
                let space = self.alloc_space_mut().ok_or(InterpError::NoAllocator)?;
                let p = space
                    .try_alloc(1)
                    .ok_or_else(|| InterpError::heap_exhausted(1, space))?;
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
                let space = self.alloc_space_mut().ok_or(InterpError::NoAllocator)?;
                let p = space
                    .try_alloc(1)
                    .ok_or_else(|| InterpError::heap_exhausted(1, space))?;
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
                if self.untrusted {
                    // Raw word-array read: a `usize` is PolyWord-sized, so the
                    // word index must be in-bounds for the object's words.
                    let v = self.validate_obj(base, "LOAD_POLY_WORD")?;
                    v.check_word_index(index)
                        .map_err(|why| InterpError::BadImage {
                            op: "LOAD_POLY_WORD",
                            why,
                        })?;
                    // SAFETY: validated object + in-bounds word index.
                    let r = unsafe { *v.ptr.cast::<usize>().add(index) };
                    let boxed = self.alloc_lg_word(r)?;
                    self.stack[self.sp] = boxed;
                    return Ok(StepResult::Continue);
                }
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
                let lgw = self.pop()?;
                let to_store = self.read_lg_word(lgw)?;
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                if self.untrusted {
                    let v = self.validate_obj(base, "STORE_POLY_WORD")?;
                    v.require_mutable()
                        .and_then(|()| v.check_word_index(index))
                        .map_err(|why| InterpError::BadImage {
                            op: "STORE_POLY_WORD",
                            why,
                        })?;
                    // SAFETY: validated mutable object + in-bounds word index.
                    unsafe { *v.ptr.cast::<usize>().cast_mut().add(index) = to_store };
                    self.stack[self.sp] = PolyWord::tagged(0);
                    return Ok(StepResult::Continue);
                }
                let p = base.as_ptr::<usize>().cast_mut();
                // SAFETY: compiler emits a valid mutable base + in-bounds index.
                unsafe { *p.add(index) = to_store };
                self.stack[self.sp] = PolyWord::tagged(0);
                Ok(StepResult::Continue)
            }
            // storeNativeWord: same but does NOT replace top — base stays. Net -2.
            EXTINSTR_STORE_NATIVE_WORD => {
                let lgw = self.pop()?;
                let to_store = self.read_lg_word(lgw)?;
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                if self.untrusted {
                    let v = self.validate_obj(base, "STORE_NATIVE_WORD")?;
                    v.require_mutable()
                        .and_then(|()| v.check_word_index(index))
                        .map_err(|why| InterpError::BadImage {
                            op: "STORE_NATIVE_WORD",
                            why,
                        })?;
                    // SAFETY: validated mutable object + in-bounds word index.
                    unsafe { *v.ptr.cast::<usize>().cast_mut().add(index) = to_store };
                    return Ok(StepResult::Continue);
                }
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
                let d = self.read_real(r)?;
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
                let f = self.read_real(r)?;
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
                // SAFETY: trusted compiler-emitted offsets (or, in untrusted
                // mode, read_pc_const bounds the 32-bit offset vs the current
                // code object before the read — HOLE 4's killer).
                let w = unsafe { self.read_pc_const(byte_off, c_num + 3) }?;
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
        if self.untrusted {
            // word0 read+write: require an in-space mutable cell with a word.
            let v = self.validate_obj(cell, "ATOMIC_INCR_DECR")?;
            v.require_mutable()
                .and_then(|()| v.check_word_index(0))
                .map_err(|why| InterpError::BadImage {
                    op: "ATOMIC_INCR_DECR",
                    why,
                })?;
        }
        let p = cell.as_ptr::<PolyWord>().cast_mut();
        // ATOMIC fetch_add/sub-2 (P3): Thread.Atomic incr/decr must be a
        // single interlocked op so concurrent bumps don't lose an update.
        // Returns the NEW value (fetch_* returns old; add the delta back).
        // SAFETY: cell is a heap-allocated mutable ref cell (validated in
        // untrusted mode above; word-aligned by allocation).
        let new_word = unsafe {
            let a = Self::atomic_word(p);
            let old = if incr {
                a.fetch_add(2, std::sync::atomic::Ordering::AcqRel)
            } else {
                a.fetch_sub(2, std::sync::atomic::Ordering::AcqRel)
            };
            let new = if incr {
                old.wrapping_add(2)
            } else {
                old.wrapping_sub(2)
            };
            PolyWord::from_bits(new)
        };
        // Replace top with the new value.
        self.pop()?;
        self.push_continue(new_word)
    }

    fn indirect(&mut self, n: usize) -> Result<StepResult, InterpError> {
        let obj_word = self.pop()?;
        if self.untrusted {
            let v = self.validate_obj(obj_word, "INDIRECT")?;
            v.check_word_index(n).map_err(|why| InterpError::BadImage {
                op: "INDIRECT",
                why,
            })?;
            // SAFETY: validated pointer + in-bounds index.
            let field = unsafe { *v.ptr.add(n) };
            return self.push_continue(field);
        }
        let p = obj_word.as_ptr::<PolyWord>();
        // SAFETY: caller (compiled code) is trusted to emit valid offsets.
        let field = unsafe { Self::heap_read(p.add(n)) };
        self.push_continue(field)
    }

    // ---- Allocation ---------------------------------------------------

    /// Bump-allocate `n_words` words plus a length word, setting the
    /// length word's flag byte to `flags`. Returns a `*mut` pointer
    /// to the body's first slot. Exhaustion is a clean terminal
    /// [`InterpError::HeapExhausted`] — never a GC-retry (see
    /// `MemorySpace::try_alloc` for the corruption-hazard rationale)
    /// and never a Rust panic.
    fn allocate(&mut self, n_words: usize, flags: u8) -> Result<*mut PolyWord, InterpError> {
        use crate::space;
        let space = self.alloc_space_mut().ok_or(InterpError::NoAllocator)?;
        let p = space
            .try_alloc(n_words)
            .ok_or_else(|| InterpError::heap_exhausted(n_words, space))?;
        // SAFETY: try_alloc just returned the matching length-word slot
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
        // ATOMIC init writes (Relaxed): under POLY_PARALLEL a peer can
        // reach this object through a racy SML publish, and TSan proved
        // the plain-write/atomic-read pair is a formal data race (the
        // publish-by-racy-ref probe). Relaxed is free on x86/aarch64.
        for i in (0..n).rev() {
            let v = self.pop()?;
            // SAFETY: i < n_words by construction.
            unsafe { Self::heap_write(p.add(i), v) };
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
            // SAFETY: i < length (ATOMIC init — see do_tuple)
            unsafe { Self::heap_write(p.add(i), v) };
        }
        // Now the source closure is on top. Copy its first word
        // (code address) to slot 0 of the new closure.
        let src_word = self.peek(0)?;
        let code_addr = if self.untrusted {
            self.untrusted_field(src_word, 0, "CLOSURE")?
        } else {
            let src_ptr = src_word.as_ptr::<PolyWord>();
            // SAFETY: src is a valid closure
            unsafe { *src_ptr }
        };
        // SAFETY: slot 0 is in bounds (ATOMIC init — see do_tuple)
        unsafe { Self::heap_write(p.add(0), code_addr) };
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
        let code_addr = if self.untrusted {
            self.untrusted_field(src_word, 0, "ALLOC_MUT_CLOSURE")?
        } else {
            let src_ptr = src_word.as_ptr::<PolyWord>();
            // SAFETY: src closure invariant
            unsafe { *src_ptr }
        };
        // SAFETY: indices < length (ATOMIC init — see do_tuple)
        unsafe {
            Self::heap_write(p.add(0), code_addr);
            for i in 1..length {
                Self::heap_write(p.add(i), PolyWord::tagged(0));
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
        if self.untrusted {
            let v = self.validate_obj(target, "MOVE_TO_MUT_CLOSURE")?;
            v.require_mutable()
                .and_then(|()| v.check_word_index(slot + 1))
                .map_err(|why| InterpError::BadImage {
                    op: "MOVE_TO_MUT_CLOSURE",
                    why,
                })?;
            // SAFETY: validated mutable object + in-bounds slot.
            // (ATOMIC — mutable closure slots are shared heap words.)
            unsafe { Self::heap_write(v.ptr.cast_mut().add(slot + 1), u) };
            return Ok(StepResult::Continue);
        }
        let p = target.as_ptr::<PolyWord>();
        // We need mutable access despite holding a *const. Cast is
        // safe because the closure was allocated mutable.
        let p_mut = p.cast_mut();
        // SAFETY: caller emitted a valid slot index for a closure
        // with at least slot+2 words. (ATOMIC — shared heap word.)
        unsafe { Self::heap_write(p_mut.add(slot + 1), u) };
        Ok(StepResult::Continue)
    }

    /// `alloc_ref`: allocate a 1-word mutable cell initialised to the
    /// value currently on top. REPLACES top with cell pointer (the
    /// initialiser doesn't get popped, just replaced).
    fn do_alloc_ref(&mut self) -> Result<StepResult, InterpError> {
        use crate::length_word::F_MUTABLE_BIT;

        let init = self.peek(0)?;
        let p = self.allocate(1, F_MUTABLE_BIT)?;
        // SAFETY: 1 word allocated (ATOMIC init — see do_tuple)
        unsafe { Self::heap_write(p.add(0), init) };
        self.pop()?;
        self.push_continue(PolyWord::from_ptr(p.cast_const()))
    }

    /// Clear the mutable bit on the length word of the object at top
    /// of stack. INSTR_LOCK leaves the object on top; INSTR_CLEAR_MUTABLE
    /// replaces it with TAGGED(0).
    fn clear_mutable_bit(&mut self, replace_with_zero: bool) -> Result<StepResult, InterpError> {
        use crate::length_word::{self, F_MUTABLE_BIT};

        let v = self.peek(0)?;
        if self.untrusted {
            // validate_obj proves there is room for the length word at
            // ptr.sub(1) (it read it). Rewriting that one length word in
            // place is bounded; no body access.
            let vo = self.validate_obj(v, "CLEAR_MUTABLE")?;
            let new_bits =
                vo.length_word.0 & !((F_MUTABLE_BIT as usize) << length_word::FLAGS_SHIFT);
            // SAFETY: vo.ptr.sub(1) is the validated length-word slot.
            // (ATOMIC — header words are shared; pairs with the atomic
            // length_word_of.)
            unsafe { Self::heap_write(vo.ptr.cast_mut().sub(1), PolyWord::from_bits(new_bits)) };
            return if replace_with_zero {
                self.pop()?;
                self.push_continue(PolyWord::tagged(0))
            } else {
                Ok(StepResult::Continue)
            };
        }
        let p = v.as_ptr::<PolyWord>().cast_mut();
        // SAFETY: caller upholds top is a mutable heap object. (ATOMIC —
        // header words are shared; pairs with the atomic length_word_of.)
        unsafe {
            let lw_ptr = p.sub(1);
            let lw = Self::heap_read(lw_ptr);
            let new_bits = lw.0 & !((F_MUTABLE_BIT as usize) << length_word::FLAGS_SHIFT);
            Self::heap_write(lw_ptr, PolyWord::from_bits(new_bits));
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
        if self.untrusted {
            let v = self.validate_obj(closure_word, "INDIRECT_CLOSURE")?;
            v.check_word_index(1 + slot_offset)
                .map_err(|why| InterpError::BadImage {
                    op: "INDIRECT_CLOSURE",
                    why,
                })?;
            // SAFETY: validated pointer + in-bounds slot.
            let val = unsafe { *v.ptr.add(1 + slot_offset) };
            return self.push_continue(val);
        }
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
        #[cfg(target_pointer_width = "64")]
        {
            #[allow(clippy::cast_possible_truncation)]
            let i = ((w.0 as isize) >> 32) as i32;
            return f32::from_bits(i as u32);
        }
        // A 32-bit word cannot hold an f32 + tag bit, so upstream PolyML *boxes*
        // Real32 on 32-bit hosts instead of tagging it (FLT_SHIFT=32 is 64-bit
        // only). The boxed-Real32 path isn't ported yet — cross-word-size
        // stretch (task #120).
        #[cfg(not(target_pointer_width = "64"))]
        {
            let _ = w;
            unimplemented!("boxed Real32 on 32-bit hosts not yet ported (task #120)")
        }
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
        let result = self.dispatch_typed_fast_call(stub, &[arg])?;
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
        let result = self.dispatch_typed_fast_call(stub, &[arg1, arg2])?;
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
        let result = self.dispatch_typed_fast_call(stub, &[arg])?;
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
        let result = self.dispatch_typed_fast_call(stub, &[arg1, arg2])?;
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
    fn dispatch_typed_fast_call(
        &mut self,
        stub: PolyWord,
        args: &[PolyWord],
    ) -> Result<f64, InterpError> {
        if !stub.is_data_ptr() {
            return Ok(0.0);
        }
        if self.untrusted {
            // The stub is an IMAGE-CONTROLLED operand off the stack: validate
            // it is an in-space object with >= 1 word before reading word0 as
            // the token. This is the #96 third sibling (found by the
            // independent adversarial re-verify): the generic CALL_FAST_RTS
            // path (rts_call) validates its stub, but this typed-FP twin
            // (reached by CALL_FAST_*_TO_*) open-coded the same `(*p).0` read
            // after only is_data_ptr -> 8-byte OOB read -> SEGV under
            // --untrusted. Same fix shape as read_real/read_lg_word.
            let vo = self.validate_obj(stub, "FAST_CALL")?;
            vo.check_word_index(0)
                .map_err(|why| InterpError::BadImage {
                    op: "FAST_CALL",
                    why,
                })?;
        }
        let p = stub.as_ptr::<PolyWord>();
        // SAFETY: trusted stub OR untrusted-validated in-space object >= 1 word.
        let token = unsafe { (*p).0 };
        let Some(entry) = self.rts.entry(token) else {
            return Ok(0.0);
        };
        let entry_func = entry.func;
        let rts_ref = self.rts.clone();
        let rts_spaces = self.rts_safe_spaces();
        let mut ctx = crate::rts::RtsContext {
            alloc_space: self.alloc_space_mut(),
            raised_exception: None,
            gc_requested_by_rts: false,
            rts: Some(&rts_ref),
            // The typed-FP fast-call path never dispatches
            // `PolyEndBootstrapMode`, so the slot stays ZERO (unused).
            bootstrap_tail_call: PolyWord::ZERO,
            safe_spaces: rts_spaces,
        };
        let result_word = match (args.len(), entry_func) {
            (1, crate::rts::RtsFn::Arity1(f)) => f(&mut ctx, args[0]),
            (2, crate::rts::RtsFn::Arity2(f)) => f(&mut ctx, args[0], args[1]),
            _ => PolyWord::tagged(0),
        };
        drop(ctx);
        // The result is RTS-computed (a freshly-allocated boxed real), so it is
        // safe to deref; route it through the validated reader for defense in
        // depth (untrusted also bounds-checks it; trusted = direct deref).
        self.read_real(result_word)
    }

    /// Real binop helper: pop x (boxed Real), peek y (boxed Real),
    /// compute `op(y, x)`, replace top with a freshly-allocated
    /// boxed Real holding the result.
    fn real_binop<F: FnOnce(f64, f64) -> f64>(&mut self, op: F) -> Result<StepResult, InterpError> {
        let x = self.pop()?;
        let y = self.peek(0)?;
        // SAFETY: caller (compiler) emits valid boxed reals.
        let fx = self.read_real(x)?;
        let fy = self.read_real(y)?;
        let result = op(fy, fx);
        let p = self.alloc_real(result)?;
        self.stack[self.sp] = p;
        Ok(StepResult::Continue)
    }

    fn real_unop<F: FnOnce(f64) -> f64>(&mut self, op: F) -> Result<StepResult, InterpError> {
        let r = self.peek(0)?;
        let f = self.read_real(r)?;
        let p = self.alloc_real(op(f))?;
        self.stack[self.sp] = p;
        Ok(StepResult::Continue)
    }

    fn real_cmp<F: FnOnce(f64, f64) -> bool>(&mut self, op: F) -> Result<StepResult, InterpError> {
        let x = self.pop()?;
        let y = self.peek(0)?;
        let fx = self.read_real(x)?;
        let fy = self.read_real(y)?;
        self.stack[self.sp] = PolyWord::tagged(isize::from(op(fy, fx)));
        Ok(StepResult::Continue)
    }

    /// Read an f64 from a boxed Real (1-word byte object).
    ///
    /// # Safety
    /// `w` must be a valid boxed-Real pointer.
    fn read_real(&self, w: PolyWord) -> Result<f64, InterpError> {
        if !w.is_data_ptr() {
            return Ok(0.0);
        }
        if self.untrusted {
            // The operand is image-controlled: validate it is an in-space
            // object with >= 8 bytes (1 word = sizeof(f64)) BEFORE the deref.
            // A wild-but-aligned pointer here is an 8-byte OOB read -> SEGV
            // (the task #96 hole found in adversarial verify: read_real was
            // an associated fn that derefed after only is_data_ptr, before any
            // untrusted branch, reached by every Real op).
            let vo = self.validate_obj(w, "REAL")?;
            vo.check_byte_range(0, std::mem::size_of::<f64>())
                .map_err(|why| InterpError::BadImage { op: "REAL", why })?;
        }
        // SAFETY: trusted (compiler-emitted boxed real) OR untrusted-validated
        // in-space object of >= 8 bytes; 1 word = sizeof(f64), word-aligned.
        Ok(unsafe { *w.as_ptr::<f64>() })
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
        let space = self.alloc_space_mut().ok_or(InterpError::NoAllocator)?;
        let p = space
            .try_alloc(1)
            .ok_or_else(|| InterpError::heap_exhausted(1, space))?;
        // SAFETY: just allocated 1 word (= 8 bytes), enough for f64.
        unsafe {
            crate::space::set_length_word(p, 1, crate::length_word::F_BYTE_OBJ);
            p.cast::<f64>().write(v);
        }
        Ok(PolyWord::from_ptr(p.cast_const()))
    }

    /// Box a raw native word as a 1-word LargeWord byte object (the
    /// `loadC64` result / `voidStar` shape). Mirrors `SIGNED_TO_LONG_W`.
    fn alloc_large_word(&mut self, v: usize) -> Result<StepResult, InterpError> {
        let space = self.alloc_space_mut().ok_or(InterpError::NoAllocator)?;
        let p = space
            .try_alloc(1)
            .ok_or_else(|| InterpError::heap_exhausted(1, space))?;
        // SAFETY: just allocated 1 word.
        unsafe {
            crate::space::set_length_word(p, 1, crate::length_word::F_BYTE_OBJ);
            p.write(PolyWord::from_bits(v));
        }
        self.push_continue(PolyWord::from_ptr(p.cast_const()))
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
        let wx = self.read_lg_word(x)?;
        let wy = self.read_lg_word(y)?;
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
        let wy = self.read_lg_word(y)?;
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
        let wx = self.read_lg_word(x)?;
        let wy = self.read_lg_word(y)?;
        self.stack[self.sp] = PolyWord::tagged(isize::from(op(wy, wx)));
        Ok(StepResult::Continue)
    }

    /// Read the first word of a boxed LargeWord object.
    ///
    /// # Safety
    /// `w` must be a valid boxed-LargeWord pointer (1+ word byte object).
    fn read_lg_word(&self, w: PolyWord) -> Result<usize, InterpError> {
        if !w.is_data_ptr() {
            if arbint_trace_on() {
                eprintln!(
                    "  read_lg_word on NON-PTR operand: 0x{:016x} (tagged={})",
                    w.0,
                    w.is_tagged()
                );
                std::process::abort();
            }
            return Ok(0);
        }
        if self.untrusted {
            // Image-controlled operand: validate >= 1 word in-space BEFORE the
            // word0 deref (the task #96 sibling hole — read_lg_word derefed
            // after only is_data_ptr, reached by the LargeWord/PackWord ops +
            // STORE_POLY/NATIVE_WORD's to_store operand).
            let vo = self.validate_obj(w, "LGWORD")?;
            vo.check_word_index(0)
                .map_err(|why| InterpError::BadImage { op: "LGWORD", why })?;
        }
        // SAFETY: trusted (compiler-emitted boxed long-word) OR untrusted-
        // validated in-space object of >= 1 word.
        Ok(unsafe { (*w.as_ptr::<PolyWord>()).0 })
    }

    fn alloc_lg_word(&mut self, word: usize) -> Result<PolyWord, InterpError> {
        let space = self.alloc_space_mut().ok_or(InterpError::NoAllocator)?;
        let p = space
            .try_alloc(1)
            .ok_or_else(|| InterpError::heap_exhausted(1, space))?;
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
        // UNTRUSTED MODE (task #96, HOLE 5): the inline ARB opcode path reaches
        // poly_word_to_bigint on stack operands that may be forged boxed
        // bignum pointers; thread the live safe-space snapshot so the bignum
        // reader gates its deref. None in trusted mode -> byte-identical.
        let spaces = self.rts_safe_spaces();
        let result = crate::rts::arb_add_via_bigint(spaces.as_ref(), self.alloc_space_mut(), x, y);
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
        let spaces = self.rts_safe_spaces();
        let result = crate::rts::arb_sub_via_bigint(spaces.as_ref(), self.alloc_space_mut(), x, y);
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
        let spaces = self.rts_safe_spaces();
        let result = crate::rts::arb_mult_via_bigint(spaces.as_ref(), self.alloc_space_mut(), x, y);
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
        // SAFETY: just allocated `length` words (ATOMIC init — see do_tuple)
        unsafe {
            for i in 0..length {
                Self::heap_write(p.add(i), PolyWord::tagged(0));
            }
        }
        let t = PolyWord::from_ptr(p.cast_const());
        // REAL-THREADS ONLY (default stays all-zero = byte-identical):
        // this lazily-materialized object belongs to a thread that was NOT
        // forked — i.e. the ROOT thread (children get theirs eagerly in
        // `fork_thread`). Give it upstream's root-thread identity + flags:
        // word 0 = the tagged handle id (threadRef identity slot, so
        // `Thread.interrupt`/`kill`/`isActive` can target the root), word 1
        // = PFLAG_BROADCAST|PFLAG_ASYNCH ("the initial thread is set to
        // accept broadcast interrupt requests", processes.cpp:1311-1313),
        // and refresh the handle's address mirror.
        if real_threads_enabled() {
            // SAFETY: same fresh allocation as above.
            unsafe {
                #[allow(clippy::cast_possible_wrap)]
                p.add(0)
                    .write(PolyWord::tagged(self.handle.thread_id as isize));
                #[allow(clippy::cast_possible_wrap)]
                p.add(1).write(PolyWord::tagged(
                    (pflag::BROADCAST | pflag::ASYNCH) as isize,
                ));
            }
            self.handle
                .thread_obj_addr
                .store(t.0, std::sync::atomic::Ordering::SeqCst);
        }
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
        if self.untrusted {
            // The stub must be a valid in-space object with a word0 token.
            // A forged stub would otherwise OOB-read word0 here.
            let v = self.validate_obj(stub, "CALL_FAST_RTS")?;
            v.check_word_index(0).map_err(|why| InterpError::BadImage {
                op: "CALL_FAST_RTS",
                why,
            })?;
        }
        let p = stub.as_ptr::<PolyWord>();
        // SAFETY: caller (bytecode) guarantees `stub` is a valid
        // EntryPoint object with word 0 holding the dispatch token. In
        // untrusted mode `stub` was validated above.
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
                    alloc_space: self.alloc_space_mut(),
                    raised_exception: None,
                    gc_requested_by_rts: false,
                    rts: None,
                    bootstrap_tail_call: PolyWord::ZERO,
                    safe_spaces: None,
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
        // ---- Concurrency (3d/3e/3f): a handful of threading RTS calls
        // need the full ThreadContext (the `Arc<Runtime>`, the giant
        // lock), not just the `RtsContext` the generic dispatch hands a
        // plain RTS fn. Special-case them here where we still hold
        // `&mut self`. `Some(r)` = handled; `None` = fall through to the
        // generic path (the existing single-thread stub).
        if let Some(r) = self.try_thread_rts(entry_name, &args[..n_args])? {
            return Ok(r);
        }
        let rts_ref = self.rts.clone(); // Arc clone, cheap
        // MULTI-THREADED sessions only: arm the blocking-syscall park so an
        // RTS function that blocks in the kernel (socket accept/recv/send,
        // a stdin read, OS.Process.system's wait) can release the giant
        // lock — publishing this thread's roots — instead of freezing every
        // peer. The single-threaded default (all existing workloads) never
        // takes this branch: zero cost, byte-identical. NB the park's
        // published roots make this thread's stack GC-scannable while it
        // waits; the `ctx` below stays dormant across the window (the
        // parked closure is native-data-only by contract).
        let armed_park = real_threads_enabled() && self.runtime.registry_len() > 1;
        if armed_park {
            let (raw, send) = self.make_send_roots();
            crate::rts::install_park(crate::rts::RtsPark::new(
                Arc::clone(&self.runtime),
                Arc::clone(&self.handle),
                raw.cast::<()>(),
                send,
                free_thread_roots_erased,
            ));
        }
        // Read the per-thread tail-call slot into a local BEFORE the
        // `alloc_space_mut()` borrow (which now borrows all of `self`,
        // since the heap moved behind `runtime.heap_mut()`).
        let seed_tail = self.bootstrap_tail_call;
        // Untrusted-mode: snapshot the live spaces for the code-constant
        // family's R1 guard BEFORE the `alloc_space_mut()` borrow.
        let rts_spaces = self.rts_safe_spaces();
        let mut ctx = RtsContext {
            alloc_space: self.alloc_space_mut(),
            raised_exception: None,
            gc_requested_by_rts: false,
            rts: Some(&rts_ref),
            // Seed the per-thread bootstrap tail-call slot from this
            // interpreter's field. `PolyEndBootstrapMode` writes it back
            // via the context; we read it back below. (Replaces the old
            // process-global static.)
            bootstrap_tail_call: seed_tail,
            safe_spaces: rts_spaces,
        };
        let result = match entry_func {
            RtsFn::Arity0(f) => f(&mut ctx),
            RtsFn::Arity1(f) => f(&mut ctx, args[0]),
            RtsFn::Arity2(f) => f(&mut ctx, args[0], args[1]),
            RtsFn::Arity3(f) => f(&mut ctx, args[0], args[1], args[2]),
            RtsFn::Arity4(f) => f(&mut ctx, args[0], args[1], args[2], args[3]),
            RtsFn::Arity5(f) => f(&mut ctx, args[0], args[1], args[2], args[3], args[4]),
        };
        // Read the per-thread bootstrap tail-call slot back into the
        // interpreter field before we drop `ctx` (it borrows `self`).
        let raised = ctx.raised_exception;
        let gc_requested = ctx.gc_requested_by_rts;
        self.bootstrap_tail_call = ctx.bootstrap_tail_call;
        // Disarm the blocking-syscall park (frees the roots box if the call
        // never parked; no-op if it parked, or single-threaded).
        if armed_park {
            crate::rts::clear_park();
        }
        // Deliver pending interrupt/kill requests at EVERY RTS return
        // (upstream's InterruptCode-poisoned stack-limit trap fires on
        // exactly this boundary, interpreter.cpp:141-156). The 65536-step
        // safepoint alone is NOT enough: a thread looping through blocking
        // RTS calls (the basis slices OS.Process.sleep into 1 s polls)
        // executes only ~tens of bytecode steps per second, so a
        // `Thread.kill` against a sleeper went undelivered for many
        // minutes — found by the threaded differential oracle (upstream
        // kills a sleeper promptly).
        //
        // This runs BEFORE the raised-exception handling: an ABORTED
        // blocking call (the slice-loops return an EINTR SysErr) must
        // surface as the KILL / Interrupt that aborted it, not as the
        // SysErr artifact — upstream's aborted waits raise Interrupt.
        // (A pending SYNCH interrupt leaves process_asynch_requests as a
        // no-op and falls through to the normal raise, exactly upstream's
        // deferred semantics.)
        if real_threads_enabled()
            && self
                .handle
                .requests
                .load(std::sync::atomic::Ordering::SeqCst)
                != crate::sched::request::NONE
        {
            if raised.is_none() {
                self.push_continue(result)?;
            }
            if let Some(sr) = self.process_asynch_requests()? {
                return Ok(sr);
            }
            if raised.is_none() {
                return Ok(StepResult::Continue);
            }
            // fall through: Synch-deferred request + a real raise
        }
        // SINGLE-THREADED twin: a pending Ctrl-C (SIGINT) is delivered at
        // the RTS boundary too — the REPL's blocked stdin read aborts via
        // the slice loop and must surface as the SML Interrupt exception
        // promptly, not wait for the 65536-step poll (nor surface as the
        // slice loop's EINTR SysErr).
        if !real_threads_enabled() && crate::interrupt::take_interrupt() {
            if raised.is_none() {
                self.push_continue(result)?;
            }
            return self.raise_interrupt();
        }
        // If the RTS function asked to raise an exception, push the
        // packet onto the stack and unwind to the registered handler.
        // Matches upstream's CALL_FAST_RTS<N> dispatch:
        //   if (GetExceptionPacket().IsDataPtr()) goto RAISE_EXCEPTION;
        if let Some(packet) = raised {
            self.push(packet)?;
            self.do_raise_ex()?;
            return Ok(StepResult::Continue);
        }
        if let Some(fn_closure) = self.take_bootstrap_tail_call() {
            self.push(PolyWord::tagged(0))?;
            self.do_call(fn_closure)?;
            return Ok(StepResult::Continue);
        }
        let r = self.push_continue(result);
        if gc_requested {
            // PolyFullGC: collect NOW, synchronously — after the (unit)
            // result is pushed and rooted, at an instruction boundary.
            // Waiting for the 65536-step safepoint would let the caller
            // read a weak ref BEFORE the collection it just requested.
            let _ = self.request_gc_collect();
        }
        r
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
                alloc_space: self.alloc_space_mut(),
                raised_exception: None,
                gc_requested_by_rts: false,
                rts: None,
                bootstrap_tail_call: PolyWord::ZERO,
                safe_spaces: None,
            };
            crate::rts::make_overflow_exception(&mut ctx)
        };
        self.push(packet)?;
        self.do_raise_ex()?;
        Ok(StepResult::Continue)
    }

    /// Raise the SML `Interrupt` exception (`EXC_interrupt = 1`) — the response
    /// to an async SIGINT delivered via [`crate::interrupt`]. Same shape as
    /// [`Self::raise_overflow`]: build the pervasive packet, push it, unwind.
    /// `do_raise_ex` returns `Err(UnhandledException)` if no handler is
    /// installed, which halts the run cleanly (vs. the OS hard-killing us).
    fn raise_interrupt(&mut self) -> Result<StepResult, InterpError> {
        let packet = {
            let mut ctx = crate::rts::RtsContext {
                alloc_space: self.alloc_space_mut(),
                raised_exception: None,
                gc_requested_by_rts: false,
                rts: None,
                bootstrap_tail_call: PolyWord::ZERO,
                safe_spaces: None,
            };
            crate::rts::make_interrupt_exception(&mut ctx)
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
    /// UNTRUSTED-MODE validation of the call primitive (Tier 0 — the
    /// wild-jump). Validates, in order:
    ///   1. `closure` is a valid in-space object (tag + membership +
    ///      header) — so reading its word0 is in-bounds.
    ///   2. word0 (the code address) resolves to a valid in-space object
    ///      that IS a code object.
    ///   3. The code object's trailing const-segment (read by
    ///      `const_segment_for_code` to set the PC bounds) lands WITHIN the
    ///      code object's space — i.e. the derived `code_end` is not wild.
    /// Any failure → a clean [`InterpError::BadImage`], never the wild jump.
    fn untrusted_validate_call(&self, closure: PolyWord) -> Result<(), InterpError> {
        let op = "CALL";
        // (1) The closure object itself. Word0 must exist (n_words >= 1).
        let cl = self.validate_obj(closure, op)?;
        cl.check_word_index(0)
            .map_err(|why| InterpError::BadImage { op, why })?;
        // SAFETY: cl validated; index 0 in bounds.
        let code_word = unsafe { *cl.ptr };

        // (2) word0 resolves to an in-space CODE object.
        let code = self.validate_obj(code_word, op)?;
        code.require_code()
            .map_err(|why| InterpError::BadImage { op, why })?;

        // (3) The const-segment derivation must stay within the code
        // object's containing space. Re-derive `cp` exactly as
        // const_segment_for_code does, but with bounds checks instead of
        // blind deref. We need: n_words >= 2 (a code object has at least
        // the trailing offset word + count word), and the computed cp (and
        // cp-1) lie within the same space as the code object body.
        let n_words = code.n_words;
        if n_words < 2 {
            return Err(InterpError::BadImage {
                op,
                why: DerefError::BadHeader,
            });
        }
        // The space containing the code object (re-find it; cheap).
        let space = match self.space_of_ptr(code.ptr) {
            Some(s) => s,
            None => {
                return Err(InterpError::BadImage {
                    op,
                    why: DerefError::NotInSpace,
                });
            }
        };
        // last_word = code.ptr + (n_words - 1) — in bounds (header checked).
        // SAFETY: code object fits the space (validate_obj), so
        // code.ptr + (n_words-1) is the last body word.
        let last_word_ptr = unsafe { code.ptr.add(n_words - 1) };
        // SAFETY: last_word_ptr is within the validated object body.
        let offset_bytes = unsafe { (*last_word_ptr).0 } as isize;
        let word_bytes = std::mem::size_of::<usize>() as isize;
        // cp = last_word_ptr + 1 + offset_bytes/word_bytes (mirrors
        // const_segment_for_code). CRUCIAL: a forged `offset_bytes` can be a
        // wild value, so we must NOT form `cp` with pointer `.offset()` (that
        // is itself UB if it leaves the allocation). Compute the candidate
        // address by INTEGER arithmetic (wrapping) and only ever COMPARE it
        // against the space bounds — never deref it here.
        let cp_addr = (last_word_ptr as usize)
            .wrapping_add(word_bytes as usize) // + 1 word
            .wrapping_add((offset_bytes / word_bytes).wrapping_mul(word_bytes) as usize);
        let start_addr = space.start as usize;
        let end_addr = space.end as usize;
        let code_addr = code.ptr as usize;
        // cp[-1] (the const-count word) must be a readable slot inside the
        // space: cp must be strictly above the space start (room for cp-1)
        // and at most one-past-the-end.
        if cp_addr <= start_addr || cp_addr > end_addr {
            return Err(InterpError::BadImage {
                op,
                why: DerefError::BadHeader,
            });
        }
        // cp must be at/after the code object body start so the PC range
        // [code_start, cp) lies within the code object.
        if cp_addr < code_addr {
            return Err(InterpError::BadImage {
                op,
                why: DerefError::BadHeader,
            });
        }
        Ok(())
    }

    /// Find the live space (image or alloc) containing `p`, returning its
    /// range. Untrusted-mode only.
    fn space_of_ptr(&self, p: *const PolyWord) -> Option<SpaceRange> {
        self.safe_spaces.space_containing(p).or_else(|| {
            self.alloc_space_range()
                .filter(|a| p >= a.start && p < a.end)
        })
    }

    fn do_call(&mut self, closure: PolyWord) -> Result<(), InterpError> {
        use crate::length_word;

        // === UNTRUSTED MODE: validate the wild-jump primitive (Tier 0). ===
        // This is the most dangerous deref in the whole interpreter: word0
        // of the "closure" becomes the code-object address whose trailing
        // const-segment offset sets the PC bounds for the NEXT function. A
        // wrong-type / wild closure here lets an untrusted image jump into
        // attacker-shaped memory. Validate the closure AND the resolved code
        // object (space-member + header + is_code_object + const-segment
        // fits the space) BEFORE the jump. The trusted path is untouched
        // below.
        if self.untrusted {
            self.untrusted_validate_call(closure)?;
        }

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

        // === WHOLE-REGION JIT BOUNDARY (S3b) ===
        // If this closure's code object has a COMPILED native region
        // root, route the call through the global region-dispatch
        // boundary (boundary::dispatch_region) on the interpreter's REAL
        // shared stack + a real ExnCtx mirroring the interp handler.
        //
        // INERT WHEN OFF: `self.region_registry` is empty (the JIT
        // registers nothing unless WHOLE_REGION_JIT is on), so this is
        // one never-taken branch — the default + --jit paths are
        // byte-identical.
        if !self.region_registry.is_empty() {
            // Resolve the closure's code object exactly as the frame-
            // setup path below does, then probe the registry.
            let region_code_ptr = {
                let closure_ptr = closure.as_ptr::<PolyWord>();
                // SAFETY: closure is a verified data pointer (checked above).
                let code_word = unsafe { *closure_ptr };
                code_word.0
            };
            if let Some(entry) = self.region_registry.get(&region_code_ptr).copied() {
                let dispatch_bits = REGION_DISPATCH.load(std::sync::atomic::Ordering::Acquire);
                // The dispatch callback MUST be installed if a region is
                // registered (the JIT installs both together); guard
                // anyway so a missing callback falls through to the
                // interpreter rather than calling a null pointer.
                if dispatch_bits != 0 {
                    // SAFETY: install_region_dispatch stored a valid
                    // RegionDispatchFn pointer.
                    let dispatch: RegionDispatchFn =
                        unsafe { std::mem::transmute::<usize, RegionDispatchFn>(dispatch_bits) };
                    // Mirror the interpreter's real handler state into the
                    // region's ExnCtx. `handler_sp == stack.len()` (no
                    // handler) maps to the JIT's NO_HANDLER sentinel so
                    // the region's downward range tests are unambiguous.
                    let handler_sp_i64 = if self.handler_sp >= self.stack.len() {
                        REGION_NO_HANDLER
                    } else {
                        self.handler_sp as i64
                    };
                    // SOUNDNESS (the dynamic-call trampoline): stash a raw
                    // `*mut Interpreter` in the ctx BEFORE invoking the
                    // region, so a region's CALL_LOCAL_B / CALL_CLOSURE
                    // trampoline can re-enter `do_call` via this raw pointer
                    // WITHOUT materializing a second aliasing `&mut self`.
                    // The `&mut self` held by THIS `do_call` is dormant for
                    // the entire `dispatch(...)` call (we touch `self` again
                    // only AFTER it returns), so the transient `&mut` the
                    // trampoline reconstructs from `interp_ptr` never aliases
                    // a live one. This mirrors the established `JIT_INTERP`
                    // thread-local raw-pointer re-entry the per-function JIT
                    // fast path uses below.
                    let interp_ptr = (self as *mut Interpreter) as i64;
                    // GC-safepoint poll wiring (S4c): hand the region the
                    // address of the live words-allocated counter + the GC
                    // trigger so its back-edge poll reads the SAME values
                    // the top-of-step check uses. `live_sp` starts at the
                    // call sp; the region overwrites it before any
                    // safepoint slow-path call.
                    let gc_used_ptr = self.region_gc_used_ptr();
                    let gc_trigger = self.region_gc_trigger();
                    let mut ctx = ExnCtxC {
                        handler_sp: handler_sp_i64,
                        exn_packet: 0,
                        interp_ptr,
                        live_sp: self.sp as i64,
                        gc_used_ptr,
                        gc_trigger,
                    };
                    let stack_base = self.stack.as_mut_ptr().cast::<i64>();
                    let sp_at_top_arg = self.sp as i64;
                    let closure_bits = closure.0 as i64;
                    // SAFETY: stack_base covers all sp indices the region
                    // touches (the region's frame grows DOWN from sp,
                    // within the same Box); region_fn is a finalized root
                    // with the region ABI; ctx is a valid *mut ExnCtxC.
                    let ret = unsafe {
                        dispatch(
                            entry.region_fn,
                            stack_base,
                            sp_at_top_arg,
                            closure_bits,
                            &mut ctx,
                        )
                    };
                    if ret.raised == 0 {
                        // Normal return: the single result is on top at
                        // stack[new_sp]; the frame collapsed exactly like
                        // do_return (result + closure + retPC + N args).
                        self.sp = ret.new_sp as usize;
                        return Ok(());
                    }
                    // raised == 1: an exception escaped the region to the
                    // interpreter. Map the region's exn sentinel onto the
                    // interpreter's REAL raise machinery so the packet +
                    // unwind + handler dispatch (or hard halt) are
                    // byte-identical to a fully-interpreted run. Reset sp
                    // to the pre-call frame top (the region left it mid-
                    // flight) before re-entering the interp raise.
                    self.sp = sp_at_top_arg as usize;
                    match ctx.exn_packet {
                        REGION_EXN_DIVZERO => {
                            // FixedInt quot/rem by zero is a HARD error in
                            // the interpreter (InterpError::DivByZero, not
                            // a catchable SML Div) — mirror exactly.
                            return Err(InterpError::DivByZero);
                        }
                        REGION_EXN_OVERFLOW => {
                            // FixedInt overflow raises the catchable
                            // pervasive Overflow, exactly as fixed_add/
                            // sub/mult do via raise_overflow().
                            self.raise_overflow()?;
                            return Ok(());
                        }
                        REGION_EXN_STACKOVERFLOW => {
                            // A region's faithful STACK_SIZE16 check tripped
                            // (sp < needed). The interpreter treats this as
                            // a HARD error (InterpError::StackOverflow,
                            // mod.rs:3457) — mirror exactly.
                            return Err(InterpError::StackOverflow);
                        }
                        other => {
                            // A REAL exception packet crossing the boundary.
                            // This is now LIVE: a dynamic-call region whose
                            // trampolined callee RAISEs a real (non-sentinel)
                            // SML exception arrives here with `other` = the
                            // REAL packet bits (carried faithfully by
                            // region_interp_call). Route it through the
                            // interpreter's OWN raise machinery: push the
                            // packet on top and do_raise_ex, so the packet +
                            // unwind + handler dispatch (or the hard
                            // UnhandledException halt) are byte-identical to a
                            // fully-interpreted callee whose exception
                            // propagates to the caller's handler. (A real
                            // pervasive Overflow ALSO arrives here as its own
                            // packet, which do_raise_ex drives identically to
                            // raise_overflow's path.)
                            let pkt = PolyWord::from_bits(other as usize);
                            self.push(pkt)?;
                            self.do_raise_ex()?;
                            return Ok(());
                        }
                    }
                }
            }
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
                if crate::env::env_flag("JIT_TRACE_CALLS_BC") {
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
            // Args marshalling buffer. The old code `vec![0; arity_init]`
            // heap-allocated on EVERY JIT call (measured 6.1 ns/call — a
            // material fraction of the 35.6 ns boundary). Use a stack
            // array for the common small arity (covers arity_init up to
            // JIT_ARGS_INLINE = 16, i.e. sml_arity up to 14, which is
            // every real bootstrap function) and fall back to a heap Vec
            // only for the rare larger arity. `args_buf` is a `&mut [i64]`
            // view over whichever backing store, so the rest of the
            // marshalling code is byte-identical regardless of path.
            let mut inline_buf = [0i64; JIT_ARGS_INLINE];
            let mut spill_buf: Vec<i64>;
            let args_buf: &mut [i64] = if arity_init <= JIT_ARGS_INLINE {
                &mut inline_buf[..arity_init]
            } else {
                spill_buf = vec![0; arity_init];
                &mut spill_buf[..]
            };
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
    ///
    /// UNTRUSTED MODE (task #96, HOLE 4): `byte_off` is an IMAGE-CONTROLLED
    /// immediate baked into the bytecode (up to 4 GiB via
    /// `CONST_ADDR32_16`'s 32-bit offset), so in trusted mode the raw
    /// `read_unaligned` at `pc + byte_off` can escape the process map and
    /// SEGV / OOB. When `self.untrusted` we bound the computed read window
    /// `[addr, addr + 8)` against the CURRENT code object's body
    /// `[code_start, code_obj_end)` BEFORE the read and reject an
    /// out-of-bounds access as a clean [`InterpError::BadImage`]. The trusted
    /// path is byte-identical (the exact original `read_unaligned`).
    unsafe fn read_pc_const(&self, byte_off: usize, idx: usize) -> Result<PolyWord, InterpError> {
        if self.untrusted {
            self.check_pc_const_bounds(byte_off, idx)?;
        }
        // SAFETY: precondition (trusted) OR bounds-checked above (untrusted).
        Ok(unsafe {
            let base = self.pc.add(byte_off);
            base.cast::<PolyWord>().add(idx).read_unaligned()
        })
    }

    /// UNTRUSTED MODE: bound the PC-relative constant read computed by
    /// [`Self::read_pc_const`] against the current code object's full word
    /// extent `[code_start, code_start + n_words*8)`. The constant pool lives
    /// inside the code object body, so any legitimate constant read lands in
    /// `[code_start, code_obj_end)`; an image-controlled `byte_off` that
    /// escapes that window is a forged read and is rejected. Computes the
    /// candidate address by INTEGER arithmetic (never `.add` past the
    /// allocation) and only COMPARES — no deref here.
    #[cold]
    fn check_pc_const_bounds(&self, byte_off: usize, idx: usize) -> Result<(), InterpError> {
        let op = "CONST_ADDR";
        // The current code object body pointer (code_start is its byte addr).
        let code_obj = self.code_start.cast::<PolyWord>();
        // Validate the code object itself is an in-space code object, then use
        // its header length to bound the read. (code_start always points at
        // the active code object's body, set by do_call/enter from a closure
        // whose word0 was already validated by untrusted_validate_call.)
        let code = self.validate_obj(PolyWord::from_ptr(code_obj), op)?;
        code.require_code()
            .map_err(|why| InterpError::BadImage { op, why })?;
        // The read window is [addr, addr + 8): addr = pc + byte_off + idx*8.
        let word_bytes = std::mem::size_of::<PolyWord>();
        let addr = (self.pc as usize)
            .wrapping_add(byte_off)
            .wrapping_add(idx.wrapping_mul(word_bytes));
        let read_end = addr.wrapping_add(word_bytes);
        let lo = self.code_start as usize;
        // code_obj_end = code_start + n_words * word_bytes (header-validated
        // by validate_obj, so n_words fits the space).
        let hi = lo.wrapping_add(code.n_words.wrapping_mul(word_bytes));
        // Require the whole 8-byte window inside the code object body, and no
        // address wrap.
        if addr < lo || read_end > hi || read_end < addr {
            return Err(InterpError::BadImage {
                op,
                why: DerefError::IndexOutOfBounds,
            });
        }
        Ok(())
    }

    /// UNTRUSTED MODE: bound a CASE16 inline jump-table entry read against the
    /// current code object body. `table_after` is the byte address of the
    /// table start (derived from `self.pc`); `u` is the (image-controlled)
    /// selector; the entry occupies `[table_after + u*2, table_after + u*2 +
    /// 2)`. Rejects any window that escapes `[code_start, code_obj_end)`.
    /// Integer arithmetic + compares only; no deref.
    #[cold]
    fn check_case16_table_read(&self, table_after: *const u8, u: usize) -> Result<(), InterpError> {
        let op = "CASE16";
        let code_obj = self.code_start.cast::<PolyWord>();
        let code = self.validate_obj(PolyWord::from_ptr(code_obj), op)?;
        code.require_code()
            .map_err(|why| InterpError::BadImage { op, why })?;
        let entry = (table_after as usize).wrapping_add(u.wrapping_mul(2));
        // The two table bytes occupy [entry, entry + 2).
        let entry_end = entry.wrapping_add(2);
        let lo = self.code_start as usize;
        let hi = lo.wrapping_add(code.n_words.wrapping_mul(std::mem::size_of::<PolyWord>()));
        if entry < lo || entry_end > hi || entry_end < entry {
            return Err(InterpError::BadImage {
                op,
                why: DerefError::IndexOutOfBounds,
            });
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::opcodes::*;
    use super::*;
    use crate::length_word::{F_CLOSURE_OBJ, F_CODE_OBJ};
    use crate::space::{MemorySpace, SpaceKind};

    /// ABI LOCK (S4c): the runtime's ExnCtxC (the struct the do_call hook
    /// builds) MUST have byte offsets identical to the JIT's ExnCtx (which
    /// the region reinterprets the SAME memory as). A field drift here is
    /// silent heap corruption under mid-region GC.
    #[test]
    fn exn_ctx_c_field_offsets_match_jit_side() {
        assert_eq!(std::mem::offset_of!(ExnCtxC, handler_sp), 0);
        assert_eq!(std::mem::offset_of!(ExnCtxC, exn_packet), 8);
        assert_eq!(std::mem::offset_of!(ExnCtxC, interp_ptr), 16);
        assert_eq!(std::mem::offset_of!(ExnCtxC, live_sp), 24);
        assert_eq!(std::mem::offset_of!(ExnCtxC, gc_used_ptr), 32);
        assert_eq!(std::mem::offset_of!(ExnCtxC, gc_trigger), 40);
        assert_eq!(std::mem::size_of::<ExnCtxC>(), 48);
    }

    // ---- ALU + control flow tests (carried over, adjusted for new API)

    fn run_to_int(code: Vec<u8>) -> isize {
        let mut interp = Interpreter::from_bytes(64, code);
        // For from_bytes tests we don't have a real call frame, so we
        // seed retPC=null + a dummy closure beneath any args, mimicking
        // the entry-from-top-level shape.
        interp.seed_return_sentinel();
        interp.seed_push(PolyWord::ZERO); // dummy "closure" placeholder
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
            i.seed_push(PolyWord::from_ptr(p.cast_const()));
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
        i.seed_push(PolyWord::from_ptr(p.cast_const())); // object (deeper)
        i.seed_push(PolyWord::tagged(5)); // addend (top)
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
        interp.seed_return_sentinel();
        interp.seed_push(PolyWord::ZERO); // caller's "self" closure
        interp.seed_push(PolyWord::from_ptr(callee_closure)); // top: callee closure to call

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
        interp.seed_return_sentinel();
        interp.seed_push(PolyWord::ZERO);

        match interp.run() {
            Ok(StepResult::Returned(v)) => assert_eq!(v.untag(), 42),
            other => panic!("expected Returned(42), got {other:?}"),
        }
    }

    #[test]
    fn unimplemented_surface() {
        // ESCAPE + an extension byte we don't handle. 0xe3/0xe4 are gaps
        // in the ext table between loadCDouble (0xe2) and storeC8 (0xe5),
        // unmapped in both our dispatch and upstream int_opcodes.h. (The
        // former probe used 0xe2 — now a real loadCDouble FFI opcode.)
        let code = vec![INSTR_ESCAPE, 0xe3]; // some unimplemented ext
        let mut interp = Interpreter::from_bytes(64, code);
        match interp.run().unwrap() {
            StepResult::Unimplemented { op, extended } => {
                assert_eq!(op, 0xe3);
                assert!(extended);
            }
            other => panic!("expected Unimplemented (extended), got {other:?}"),
        }
    }
}
