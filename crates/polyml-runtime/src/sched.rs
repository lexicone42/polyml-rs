//! Cooperative scheduler + shared runtime for the giant-lock concurrency
//! model.
//!
//! Faithful port of upstream's `processes.cpp` model (one shared ML heap,
//! a single global "mutator lock" meaning *"I am the thread currently
//! allowed to run bytecode"*, released at each safepoint so threads
//! interleave cooperatively). This is **concurrency, not parallelism** —
//! under the giant lock only one SML thread executes at a time, exactly
//! like upstream Poly/ML's interpreter mode.
//!
//! ## The pieces
//!
//! - [`Runtime`] is `Arc`-shared between every thread's `ThreadContext`.
//!   It owns the heap [`MemorySpace`] (accessed ONLY by the lock-holder),
//!   the pre-computed GC trigger, the RTS table, the image-mutable root
//!   regions, and the [`SchedState`].
//! - [`SchedState`] is the giant lock: a `Mutex<SchedInner>` plus two
//!   `Condvar`s (one to wake parked mutators, one to wake the collector).
//! - [`ThreadHandle`] is one per live SML thread; the registry of them
//!   (`SchedInner::registry`) is what the collector iterates to forward
//!   every thread's roots.
//!
//! ## The ownership handshake (the load-bearing safety invariant)
//!
//! The collector must forward EVERY parked thread's stack. The ONLY route
//! it has to another thread's roots is [`ThreadHandle::parked_roots`], a
//! `Mutex<Option<SendRoots>>`. A `None` slot is literally unreachable —
//! so the type system enforces *"the collector touches a thread's roots
//! IFF that thread confirmed it parked AND published its roots."*
//!
//! A blocking path MUST publish its roots BEFORE releasing ML memory
//! (`threads_in_heap -= 1`). Otherwise the collector either deadlocks
//! (`threads_in_heap` never reaches 0) or — worse — collects while an
//! `in_ml` thread mutates its stack (a use-after-free). The publish is
//! done inside the publishing release/park helpers, which store the roots
//! under the handle's lock *before* they decrement `threads_in_heap`,
//! making the invariant structural.

// The giant-lock helpers deliberately hold their `MutexGuard`s for the
// full critical section (the publish-before-decrement ordering is the
// whole point), so the "drop the guard earlier" lint is wrong here.
#![allow(clippy::significant_drop_tightening)]
#![allow(clippy::significant_drop_in_scrutinee)]

use std::sync::atomic::{AtomicBool, AtomicU8, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};

use crate::poly_word::PolyWord;
use crate::rts::RtsTable;
use crate::space::MemorySpace;

/// `Send` wrapper for a raw `*const PolyWord` image-root pointer. The
/// pointed-at image-mutable spaces are process-global and outlive all
/// threads; only the GC (lock-holder) dereferences them.
#[derive(Clone, Copy)]
pub struct SendPtr(pub *const PolyWord);
// SAFETY: dereferenced only by the lock-holding collector.
unsafe impl Send for SendPtr {}
unsafe impl Sync for SendPtr {}

/// The image-mutable root regions to scan during GC.
#[derive(Clone, Default)]
pub struct ImageRoots(pub Vec<(SendPtr, usize)>);

/// The published GC root-set of a parked thread.
///
/// Captured by the parking thread and consumed by the collector. Carrying
/// it as an opaque, `Send`-able box keeps the `interpreter` module the
/// sole owner of the root-capture layout while letting the collector
/// reach it across the thread boundary.
///
/// # Safety
/// Every pointer inside aliases the publishing thread's live
/// `ThreadContext` state. It is valid only while that thread is parked
/// (it released the mutator lock and is blocked in a safepoint / a
/// blocking RTS wait). The collector mutates it in place and the parking
/// thread re-reads it on wake — both under the giant lock, so there is no
/// concurrent access.
pub struct SendRoots {
    /// Opaque payload — a `*mut ThreadRoots` the `interpreter` crate
    /// stored. We keep it as a raw `*mut ()` so `sched` has zero
    /// knowledge of the root layout (no cyclic type dependency).
    pub ptr: *mut (),
    /// Type-erased "forward all roots via this collector" thunk. Second
    /// arg is the `*mut Collector`.
    pub forward: unsafe fn(*mut (), *mut ()),
    /// Type-erased "scrub below sp + write forwarded slots back" thunk.
    pub fixup: unsafe fn(*mut ()),
    /// Type-erased "audit my root slots for residual from-space pointers"
    /// thunk. Args: `(*mut payload, from_lo, from_hi)`; returns the count of
    /// residual pointers found. Lets `POLYML_GC_AUDIT=1` validate EVERY
    /// parked thread's published roots, not just the collector's own stack
    /// (B3) — so a reintroduced B1/B2 (a skipped parked stack) is detected.
    pub audit: unsafe fn(*mut (), usize, usize) -> usize,
}
// SAFETY: the wrapped pointer is only ever dereferenced under the giant
// lock (by exactly one of: the publishing thread before/after the park,
// or the collector while the publisher is confirmed parked).
unsafe impl Send for SendRoots {}

/// Per-thread request flags, checked at the safepoint. Bit semantics
/// mirror upstream `processes.h` `requests` enum (interrupt / kill).
pub mod request {
    /// No pending request.
    pub const NONE: u8 = 0;
    /// Raise the SML `Interrupt` exception at the next safepoint.
    pub const INTERRUPT: u8 = 1;
    /// Terminate the thread at the next safepoint.
    pub const KILL: u8 = 2;
}

/// One live SML thread's scheduler handle. Shared (`Arc`) between the
/// owning `ThreadContext` and the `SchedInner::registry`.
pub struct ThreadHandle {
    /// True while this thread holds ML memory (is executing bytecode and
    /// may touch the heap). The collector waits until `threads_in_heap`
    /// reaches 1 (just itself), at which point every OTHER handle has
    /// `in_ml == false` and has published its roots.
    pub in_ml: AtomicBool,
    /// Set once the thread has returned / been killed. A joiner polls
    /// this (under `mutator_wake`).
    pub exited: AtomicBool,
    /// The thread's exit result word (valid once `exited`). Tagged(0) by
    /// default.
    pub result: Mutex<PolyWord>,
    /// Pending interrupt/kill request, checked at the safepoint.
    pub requests: AtomicU8,
    /// The ONLY route the collector has to this thread's roots. `Some`
    /// IFF the thread is confirmed parked (released ML memory) and has
    /// published a consistent root-set. `None` IFF the thread is either
    /// `in_ml` (touching its own stack — collector must NOT alias it) or
    /// fully exited.
    pub parked_roots: Mutex<Option<SendRoots>>,
    /// True for a BACKGROUND/daemon thread that never returns on its own
    /// (the basis signal thread, parked forever in `PolyWaitForSignal`).
    /// `wait_for_children` does NOT wait for daemons at process exit — like
    /// upstream, the signal thread is abandoned when the root returns. A
    /// daemon still participates fully in the GC handshake (it parks with
    /// published roots), so this flag only governs join/shutdown, never
    /// collection safety.
    pub is_daemon: AtomicBool,
    /// Process-unique thread identity (never 0). The interpreter stores
    /// `Tagged(thread_id)` in the ML thread object's word 0 — upstream's
    /// `threadRef` slot ("the address of the thread data. Not used by ML",
    /// processes.h:84) — so the targeted thread RTS calls
    /// (`PolyThreadInterruptThread`/`KillThread`/`IsActive`/`CondVarWake`)
    /// can map an ML thread OBJECT back to its handle. A tagged int is
    /// GC-immune (it moves WITH the object, and its value never changes),
    /// unlike the raw C pointer upstream stores.
    pub thread_id: u64,
    /// MIRROR of the current address of this thread's ML thread object
    /// (0 = not yet materialized). This is the handle→object direction
    /// (upstream `TaskData::threadObject`), needed by
    /// `PolyThreadBroadcastInterrupt` to read each peer's flags word and
    /// by `MakeRequest` to set its `requestCopy`. The GC MOVES the object,
    /// so the mirror is refreshed by the collector on every collection
    /// (in `ThreadRoots::forward` / `ForkRoots::forward_thunk`, right
    /// after the thread-object slot is forwarded) and (re)set by the owner
    /// at object creation. It is only ever DEREFERENCED by the running
    /// mutator under the giant lock (peers parked, no GC in flight), so it
    /// can never be read while stale.
    pub thread_obj_addr: AtomicUsize,
}

/// Monotonic source for [`ThreadHandle::thread_id`] (0 is reserved for
/// "no thread" — a thread object whose word 0 is `Tagged(0)` maps to no
/// handle, like upstream's zeroed `threadRef` after thread exit).
static NEXT_THREAD_ID: AtomicU64 = AtomicU64::new(1);

impl ThreadHandle {
    #[must_use]
    pub fn new() -> Arc<Self> {
        Arc::new(Self {
            in_ml: AtomicBool::new(false),
            exited: AtomicBool::new(false),
            result: Mutex::new(PolyWord::tagged(0)),
            requests: AtomicU8::new(request::NONE),
            parked_roots: Mutex::new(None),
            is_daemon: AtomicBool::new(false),
            thread_id: NEXT_THREAD_ID.fetch_add(1, Ordering::Relaxed),
            thread_obj_addr: AtomicUsize::new(0),
        })
    }
}

/// State guarded by the giant lock.
pub struct SchedInner {
    /// A collection has been requested; the running mutator parks at its
    /// next safepoint to let the requester become the collector, OR (the
    /// common case) the requester IS the running mutator and collects
    /// immediately.
    pub gc_requested: bool,
    /// The giant mutator lock: `true` while exactly one thread is running
    /// bytecode (and may touch the heap). Only one thread can run at a
    /// time — this is concurrency, not parallelism (upstream's
    /// interpreter-mode model). A thread waiting to run blocks on
    /// `mutator_wake` until `running` is `false` and `!gc_requested`.
    pub running: bool,
    /// Number of threads currently blocked in `acquire`/`reacquire`/`park`
    /// waiting for the giant lock. A cooperative `yield` checks this: if a
    /// peer is waiting it forces a hand-off (waits until someone else has
    /// taken the lock); if not, it keeps running (no pointless self-yield).
    pub waiters: usize,
    /// Every live thread's handle. The collector iterates this to forward
    /// each NON-running thread's published roots.
    ///
    /// INVARIANT: every registered thread that is not the running thread
    /// has `parked_roots == Some(..)` (it published before yielding /
    /// blocking / waiting to run). So the collector — which runs only as
    /// the single running thread — can forward its own roots directly and
    /// every other registered thread's roots via its published slot.
    pub registry: Vec<Arc<ThreadHandle>>,
}

/// The giant lock + its condition variables.
pub struct SchedState {
    pub inner: Mutex<SchedInner>,
    /// Notified when the giant lock frees up (a runner released / yielded
    /// / a collection finished) and when a thread exits (wakes joiners).
    pub mutator_wake: Condvar,
    /// Notified by each parking mutator so a waiting collector re-checks
    /// its preconditions.
    pub collector_wake: Condvar,
    /// Monotonic "blocking event" generation, bumped on every mutex-unlock
    /// / condvar-wake / thread-exit / interrupt. A thread blocked in
    /// `block_until_event` waits for this to change, so wakeups are not
    /// lost (it samples the generation BEFORE releasing the giant lock).
    pub block_gen: Mutex<u64>,
    /// Notified whenever `block_gen` is bumped (a blocked mutex/condvar
    /// waiter or joiner should re-check its condition).
    pub block_wake: Condvar,
}

impl Default for SchedState {
    fn default() -> Self {
        Self::new()
    }
}

impl SchedState {
    #[must_use]
    pub fn new() -> Self {
        Self {
            inner: Mutex::new(SchedInner {
                gc_requested: false,
                running: false,
                waiters: 0,
                registry: Vec::new(),
            }),
            mutator_wake: Condvar::new(),
            collector_wake: Condvar::new(),
            block_gen: Mutex::new(0),
            block_wake: Condvar::new(),
        }
    }
}

/// A `Send`/`Sync` cell holding the shared heap.
///
/// Only the lock-holder (a thread with `in_ml == true`, or the collector
/// while all mutators are parked) dereferences it, so no inner per-access
/// mutex is needed — the giant lock IS the heap's mutual exclusion.
pub struct HeapCell(std::cell::UnsafeCell<Option<MemorySpace>>);
// SAFETY: synchronised by the giant lock, not by Rust's borrow checker.
unsafe impl Send for HeapCell {}
unsafe impl Sync for HeapCell {}

/// The `Arc`-shared runtime: everything common to all threads.
pub struct Runtime {
    /// The shared ML heap. Accessed only by the current lock-holder.
    heap: HeapCell,
    /// Count of completed collections (diagnostic; lets a test assert that
    /// a GC actually fired mid-run).
    pub gc_count: std::sync::atomic::AtomicU64,
    /// Cumulative count of residual from-space pointers the `POLYML_GC_AUDIT`
    /// pass found across ALL collections (own stack + every parked thread's
    /// published roots + a registered-but-unpublished peer). Stays 0 on a
    /// sound run; a NEGATIVE-CONTROL test that reintroduces H1/H2 asserts
    /// this goes positive — proving the audit has teeth (it is not a
    /// stderr-only print that a passing test ignores).
    pub gc_audit_residual: std::sync::atomic::AtomicU64,
    /// Pre-computed GC trigger in words (0 = never auto-GC).
    pub gc_trigger_words: usize,
    /// The RTS function table (immutable after construction).
    pub rts: Arc<RtsTable>,
    /// Image-mutable root regions to scan during GC.
    pub image_roots: Mutex<ImageRoots>,
    /// The giant lock + scheduler state.
    pub sched: SchedState,
}

impl Runtime {
    #[must_use]
    pub fn new(
        heap: Option<MemorySpace>,
        gc_trigger_words: usize,
        rts: Arc<RtsTable>,
    ) -> Arc<Self> {
        Arc::new(Self {
            heap: HeapCell(std::cell::UnsafeCell::new(heap)),
            gc_count: std::sync::atomic::AtomicU64::new(0),
            gc_audit_residual: std::sync::atomic::AtomicU64::new(0),
            gc_trigger_words,
            rts,
            image_roots: Mutex::new(ImageRoots::default()),
            sched: SchedState::new(),
        })
    }

    /// Mutable access to the shared heap.
    ///
    /// # Safety
    /// The caller must currently hold ML memory (`in_ml == true`) or be
    /// the collector with all mutators parked. The giant-lock discipline
    /// guarantees no aliasing.
    #[allow(clippy::mut_from_ref)]
    pub unsafe fn heap_mut(&self) -> &mut Option<MemorySpace> {
        // SAFETY: caller upholds the giant-lock discipline.
        unsafe { &mut *self.heap.0.get() }
    }

    /// Append an image-mutable root region.
    pub fn add_image_root(&self, ptr: *const PolyWord, len_words: usize) {
        self.image_roots
            .lock()
            .unwrap()
            .0
            .push((SendPtr(ptr), len_words));
    }

    // NOTE (H1, structural): there is DELIBERATELY no bare `register_thread`
    // method. A bare register of a not-yet-running thread leaves the handle
    // in the registry with `parked_roots == None`, which violates the
    // registry invariant ("registered AND not-running ⟹ parked_roots is
    // Some") for a TOCTOU window and makes the collector's forward loop skip
    // the new thread's live stack. EVERY registration path must publish
    // roots before (or atomically as) the handle becomes registry-visible:
    //   * fork:    [`Self::register_thread_published`] (parent pre-publishes
    //              the child's ForkRoots, then registers).
    //   * generic: [`Self::register_and_acquire_ml_memory`] (publish + push
    //              + acquire under one lock acquisition).
    // Enforcing the invariant by REMOVING the unsound API (rather than a
    // doc warning) is what makes H1 structural.

    /// Register a thread handle that ALREADY holds published roots
    /// (`parked_roots == Some`). The publish must have happened BEFORE this
    /// call, so that the instant the handle becomes visible in the registry
    /// the invariant "registered AND not-running ⟹ parked_roots is Some"
    /// already holds — closing the fork TOCTOU window (B1). This is the
    /// fork path's registration: the parent publishes the child's INITIAL
    /// roots (its starting closure + thread object) under the handle's lock,
    /// then registers via this method.
    ///
    /// # Safety
    /// `handle.parked_roots` must be `Some(..)` and the published roots must
    /// alias live, GC-stable state until the child retracts them on its
    /// first [`Self::acquire_ml_memory`].
    pub unsafe fn register_thread_published(&self, handle: &Arc<ThreadHandle>) {
        debug_assert!(
            handle.parked_roots.lock().unwrap().is_some(),
            "register_thread_published requires pre-published roots"
        );
        debug_assert!(
            !handle.in_ml.load(Ordering::SeqCst),
            "a freshly-forked child must not be in_ml before it acquires"
        );
        self.sched
            .inner
            .lock()
            .unwrap()
            .registry
            .push(Arc::clone(handle));
    }

    // NOTE: deregistration is folded into the exit paths ([`Self::exit_parked`]
    // / [`Self::exit_running`]) so that removal-from-registry and
    // clearing-`parked_roots` always happen under the SAME lock — there is no
    // standalone `deregister_thread` that could leave a half-torn-down handle.

    /// Acquire the giant mutator lock: become THE single running thread.
    /// Port of `ThreadUseMLMemoryWithSchedLock` (processes.cpp:878).
    ///
    /// While waiting for the lock (another thread is running or a GC is in
    /// progress) this thread's roots are PUBLISHED so the collector can
    /// forward its stack. The instant the lock is acquired the roots are
    /// retracted (we are about to mutate the stack, so the collector must
    /// not alias it). The publish-while-waiting upholds the registry
    /// invariant: every non-running registered thread has published roots.
    ///
    /// # Safety
    /// `roots` must alias the calling thread's live `ThreadContext`. It
    /// stays published only while the thread is parked (blocked here);
    /// once acquired and retracted, the alias is no longer exposed.
    pub unsafe fn acquire_ml_memory(&self, handle: &ThreadHandle, roots: SendRoots) {
        let mut inner = self.sched.inner.lock().unwrap();
        // Publish before any wait so a collection that fires while we are
        // queued can still scan our stack.
        *handle.parked_roots.lock().unwrap() = Some(roots);
        handle.in_ml.store(false, Ordering::SeqCst);
        // Nudge a possibly-waiting collector (we just published / are not
        // running, so it may now proceed).
        self.sched.collector_wake.notify_all();
        inner.waiters += 1;
        while inner.running || inner.gc_requested {
            inner = self.sched.mutator_wake.wait(inner).unwrap();
        }
        inner.waiters -= 1;
        // We won the lock. Retract our roots (we will mutate the stack)
        // and become the running thread.
        *handle.parked_roots.lock().unwrap() = None;
        inner.running = true;
        handle.in_ml.store(true, Ordering::SeqCst);
        // Announce the take: a yielder blocked in its forced-hand-off loop
        // (yield_ml_memory) waits for `running` to become true, and without
        // this notify a PURE-COMPUTE taker (which never blocks or notifies
        // again) would leave it asleep until some unrelated event — the
        // yielder is not yet counted in `waiters` there, so the taker's own
        // later yields early-return and the yielder starves (found by the
        // preemption-fairness test).
        self.sched.mutator_wake.notify_all();
    }

    /// Atomically REGISTER a previously-unregistered thread handle AND
    /// acquire the giant mutator lock — publishing its roots BEFORE the
    /// handle is pushed into the registry, all under ONE acquisition of the
    /// scheduler lock. This is the H1 structural fix for the GENERIC
    /// register path: a bare `register_thread` followed by a separate
    /// `acquire_ml_memory` left a TOCTOU window in which the handle was
    /// registered, not running, AND `parked_roots == None` — a state the
    /// stop-the-world barrier must treat as "not-yet-parked" and the
    /// collector's forward loop SKIPS. By publishing then pushing then
    /// waiting without ever releasing `inner`, the instant the handle
    /// becomes reachable to a collector it ALREADY satisfies the registry
    /// invariant "registered AND not-running ⟹ parked_roots is Some".
    ///
    /// The handle must NOT already be in the registry (this PUSHES it).
    ///
    /// # Safety
    /// `roots` must alias the calling thread's live `ThreadContext`; it
    /// stays published only while the thread is parked here, and is
    /// retracted (set `None`) before this returns.
    pub unsafe fn register_and_acquire_ml_memory(
        &self,
        handle: &Arc<ThreadHandle>,
        roots: SendRoots,
    ) {
        let mut inner = self.sched.inner.lock().unwrap();
        // Do NOT join a collection already in progress: the collector
        // snapshotted the registry before we existed, so pushing now would
        // leave our (possibly from-space) roots unforwarded by THIS cycle and
        // stale when we wake. We are not yet registered, so the stop-the-world
        // barrier (which iterates `registry`) does not await us — waiting here
        // cannot deadlock. Once `gc_requested` clears we STILL hold `inner`, so
        // the push below is atomic w.r.t. any next collection: it would then
        // see us registered + parked + published and forward us correctly.
        while inner.gc_requested {
            inner = self.sched.mutator_wake.wait(inner).unwrap();
        }
        // Publish BEFORE the handle becomes reachable via the registry, so
        // there is no observable registered-but-None window.
        *handle.parked_roots.lock().unwrap() = Some(roots);
        handle.in_ml.store(false, Ordering::SeqCst);
        inner.registry.push(Arc::clone(handle));
        // Nudge a possibly-waiting collector (a new registered thread just
        // appeared, already with published roots, so the barrier can re-check).
        self.sched.collector_wake.notify_all();
        inner.waiters += 1;
        while inner.running || inner.gc_requested {
            inner = self.sched.mutator_wake.wait(inner).unwrap();
        }
        inner.waiters -= 1;
        // We won the lock. Retract our roots and become the running thread.
        *handle.parked_roots.lock().unwrap() = None;
        inner.running = true;
        handle.in_ml.store(true, Ordering::SeqCst);
        // Announce the take (see `acquire_ml_memory`): wake any yielder
        // blocked in its forced-hand-off loop.
        self.sched.mutator_wake.notify_all();
    }

    /// Acquire the giant mutator lock for a thread whose roots are ALREADY
    /// published (the freshly-forked child: its `ForkRoots` were published
    /// by the parent before registration). Unlike [`Self::acquire_ml_memory`]
    /// this does NOT overwrite `parked_roots` with a fresh capture — doing so
    /// would replace the `ForkRoots` (which root the child's starting closure
    /// and thread object) with an EMPTY capture (the child has not seeded its
    /// stack yet), so a GC during the acquire-wait would skip the child's
    /// closure → use-after-free (the exact B1 hazard). The existing
    /// `Some(ForkRoots)` stays published until we win the lock, then we
    /// retract it to `None`.
    ///
    /// # Safety
    /// `handle.parked_roots` must already be `Some(..)` with roots that
    /// alias live, GC-stable state (the parent-published `ForkRoots`).
    pub fn acquire_ml_memory_keep_published(&self, handle: &ThreadHandle) {
        let mut inner = self.sched.inner.lock().unwrap();
        debug_assert!(
            handle.parked_roots.lock().unwrap().is_some(),
            "acquire_ml_memory_keep_published requires pre-published roots"
        );
        handle.in_ml.store(false, Ordering::SeqCst);
        // Nudge a possibly-waiting collector (we are not running and our
        // roots are published, so it may proceed).
        self.sched.collector_wake.notify_all();
        inner.waiters += 1;
        while inner.running || inner.gc_requested {
            inner = self.sched.mutator_wake.wait(inner).unwrap();
        }
        inner.waiters -= 1;
        // We won the lock. Retract the (forwarded) ForkRoots and become the
        // running thread.
        *handle.parked_roots.lock().unwrap() = None;
        inner.running = true;
        handle.in_ml.store(true, Ordering::SeqCst);
        // Announce the take (see `acquire_ml_memory`): the forking parent
        // may be blocked in its yield's forced-hand-off loop waiting for
        // this exact take — and a pure-compute child never notifies again.
        self.sched.mutator_wake.notify_all();
    }

    /// Release the giant mutator lock when LEAVING the interpreter loop
    /// (e.g. `run_until` returned to the REPL driver, hit `max_steps`, or
    /// errored) while STAYING REGISTERED. The stack is quiescent but may
    /// still root live heap objects (the REPL's working state between
    /// declarations), so this PUBLISHES the thread's roots — there must be
    /// NO release-while-registered that leaves `parked_roots == None`
    /// (the B2 invariant). A peer that fires a GC while we sit between
    /// `run_until` calls can then still forward our stack.
    ///
    /// Port of `ThreadReleaseMLMemoryWithSchedLock` (processes.cpp:897).
    /// Hands the lock to a waiting peer and nudges any waiting collector.
    ///
    /// # Safety
    /// `roots` aliases the calling thread's live `ThreadContext` and stays
    /// valid until the next [`Self::acquire_ml_memory`] (the next
    /// `run_until`) retracts it, or until [`Self::exit_parked`]
    /// deregisters this thread.
    pub unsafe fn release_ml_memory(&self, handle: &ThreadHandle, roots: SendRoots) {
        let mut inner = self.sched.inner.lock().unwrap();
        // Publish BEFORE clearing `running`: a collector can only proceed
        // once `running == false`, and by then our roots are already Some.
        *handle.parked_roots.lock().unwrap() = Some(roots);
        handle.in_ml.store(false, Ordering::SeqCst);
        inner.running = false;
        self.sched.mutator_wake.notify_all();
        self.sched.collector_wake.notify_all();
    }

    /// DEREGISTER on true thread EXIT for a thread that IS the running
    /// mutator (it currently holds the giant lock). The malformed-function
    /// early-exit in `child_thread_main` is the canonical caller: the child
    /// has just `acquire`d and is `running == true` / `in_ml == true`.
    ///
    /// Clears `running` (this thread DOES hold it), deregisters, and clears
    /// `parked_roots`, all under the same lock — so there is never a window
    /// in which a dead thread is registered with `parked_roots == None`.
    /// `parked_roots = None` is set only AFTER removing the handle from the
    /// registry, so a collector — which snapshots the registry under the
    /// lock — can never observe this handle as a registered-but-None thread.
    ///
    /// # Panics
    /// In debug builds, asserts the caller actually holds the lock
    /// (`running == true`) — clearing `running` here when the thread does
    /// NOT hold it would corrupt the flag (the H2 hazard) and let a second
    /// mutator run concurrently.
    pub fn exit_running(&self, handle: &Arc<ThreadHandle>) {
        let mut inner = self.sched.inner.lock().unwrap();
        debug_assert!(
            inner.running,
            "exit_running called but the giant lock is not held (running == false)"
        );
        inner.registry.retain(|h| !Arc::ptr_eq(h, handle));
        handle.in_ml.store(false, Ordering::SeqCst);
        // This thread holds the lock, so clearing it is correct: we are
        // releasing it on the way out.
        inner.running = false;
        // Now unreachable by the collector (off the registry); drop the
        // dead stack's published roots if any.
        *handle.parked_roots.lock().unwrap() = None;
        self.sched.mutator_wake.notify_all();
        self.sched.collector_wake.notify_all();
    }

    /// DEREGISTER on true thread EXIT for a thread that is NOT the running
    /// mutator (it has already released the giant lock — e.g. via
    /// `release_ml_memory` at the end of `run_until` — and is parked with
    /// published roots). The normal child / host exit path is the caller.
    ///
    /// Crucially this does NOT touch `running`: the exiting thread does not
    /// hold the lock, so SOME OTHER thread may currently be the running
    /// mutator. Unconditionally clearing `running` here (the H2 bug) would
    /// clobber that peer's ownership and admit a second concurrent mutator.
    ///
    /// It also COOPERATES WITH THE COLLECTOR: if a stop-the-world GC is in
    /// flight (`gc_requested`), it WAITS until the collection finishes
    /// before deregistering, so it never races the collector's registry
    /// snapshot / published-roots forward. (The collector also holds this
    /// handle's `parked_roots` guard while forwarding, so even without this
    /// wait the `parked_roots = None` below would serialize behind it — the
    /// explicit wait makes the non-racing discipline structural.)
    ///
    /// Deregister-then-clear-`parked_roots` happen under the same lock, so
    /// the only `None`-while-registered states stay eliminated.
    pub fn exit_parked(&self, handle: &Arc<ThreadHandle>) {
        let mut inner = self.sched.inner.lock().unwrap();
        // Cooperate with an in-flight collection: do not deregister / drop
        // published roots while the collector may be mid-forward over us.
        while inner.gc_requested {
            // Nudge the collector (it re-checks the barrier on this wake) —
            // though we publish nothing new, this keeps liveness if it is
            // waiting on us, and parks us until the collection clears.
            self.sched.collector_wake.notify_all();
            inner = self.sched.mutator_wake.wait(inner).unwrap();
        }
        inner.registry.retain(|h| !Arc::ptr_eq(h, handle));
        handle.in_ml.store(false, Ordering::SeqCst);
        // Do NOT touch `inner.running`: this thread does not hold the lock.
        // Now unreachable by the collector (off the registry); drop the
        // dead stack's published roots if any.
        *handle.parked_roots.lock().unwrap() = None;
        self.sched.mutator_wake.notify_all();
        self.sched.collector_wake.notify_all();
    }

    /// Release the giant mutator lock for a BLOCKING path (mutex-block /
    /// condvar-wait), publishing the thread's roots so the collector can
    /// forward its stack while blocked. Mirrors upstream's
    /// `ThreadReleaseMLMemory` around `WaitInfinite` (processes.cpp:533).
    /// The publish happens BEFORE `running` is cleared, so the collector
    /// (which can only proceed once `running == false`) always finds the
    /// roots.
    ///
    /// # Safety
    /// `roots` aliases the calling thread's live `ThreadContext` and stays
    /// valid until the matching [`Self::reacquire_ml_memory`].
    pub unsafe fn release_ml_memory_publishing(&self, handle: &ThreadHandle, roots: SendRoots) {
        let mut inner = self.sched.inner.lock().unwrap();
        *handle.parked_roots.lock().unwrap() = Some(roots);
        handle.in_ml.store(false, Ordering::SeqCst);
        inner.running = false;
        self.sched.mutator_wake.notify_all();
        self.sched.collector_wake.notify_all();
    }

    /// Re-acquire the giant mutator lock after a blocking wait, retracting
    /// the published roots. Symmetric to
    /// [`Self::release_ml_memory_publishing`]. Waits until the lock is free
    /// and no GC is in progress, then retracts roots and becomes running.
    pub fn reacquire_ml_memory(&self, handle: &ThreadHandle) {
        let mut inner = self.sched.inner.lock().unwrap();
        inner.waiters += 1;
        while inner.running || inner.gc_requested {
            self.sched.collector_wake.notify_all();
            inner = self.sched.mutator_wake.wait(inner).unwrap();
        }
        inner.waiters -= 1;
        *handle.parked_roots.lock().unwrap() = None;
        inner.running = true;
        handle.in_ml.store(true, Ordering::SeqCst);
        // Announce the take (see `acquire_ml_memory`): wake any yielder
        // blocked in its forced-hand-off loop.
        self.sched.mutator_wake.notify_all();
    }

    /// Park at a safepoint because a GC was requested by a peer. Publishes
    /// roots, releases the lock, waits for the collection to finish, then
    /// re-acquires (retracting roots).
    ///
    /// # Safety
    /// `roots` aliases the live `ThreadContext` and stays valid across the
    /// park.
    pub unsafe fn safepoint_park(&self, handle: &ThreadHandle, roots: SendRoots) {
        let mut inner = self.sched.inner.lock().unwrap();
        *handle.parked_roots.lock().unwrap() = Some(roots);
        handle.in_ml.store(false, Ordering::SeqCst);
        inner.running = false;
        self.sched.mutator_wake.notify_all();
        self.sched.collector_wake.notify_all();
        // Re-acquire the lock once the GC finished AND it is free.
        inner.waiters += 1;
        while inner.running || inner.gc_requested {
            inner = self.sched.mutator_wake.wait(inner).unwrap();
        }
        inner.waiters -= 1;
        *handle.parked_roots.lock().unwrap() = None;
        inner.running = true;
        handle.in_ml.store(true, Ordering::SeqCst);
        // Announce the take (see `acquire_ml_memory`): wake any yielder
        // blocked in its forced-hand-off loop.
        self.sched.mutator_wake.notify_all();
    }

    /// Cooperatively yield the giant lock so a waiting peer can run, then
    /// re-acquire it. This is what makes interleaving observable: a thread
    /// running a long loop drops the lock at its safepoint, lets a peer
    /// take a turn, and resumes. Publishes roots across the yield (so a
    /// GC during the gap can scan us).
    ///
    /// # Safety
    /// `roots` aliases the live `ThreadContext` and stays valid across the
    /// yield.
    pub unsafe fn yield_ml_memory(&self, handle: &ThreadHandle, roots: SendRoots) {
        let mut inner = self.sched.inner.lock().unwrap();
        // No peer is waiting for the lock — keep running (a self-yield
        // would be pointless and would just churn condvars).
        if inner.waiters == 0 {
            return;
        }
        // Publish + release the lock so a waiting peer can take it.
        *handle.parked_roots.lock().unwrap() = Some(roots);
        handle.in_ml.store(false, Ordering::SeqCst);
        inner.running = false;
        self.sched.mutator_wake.notify_all();
        self.sched.collector_wake.notify_all();
        // FORCE a hand-off: wait until a peer has actually TAKEN the lock
        // (running becomes true) — otherwise our own re-acquire below would
        // win the race against the just-notified peer and nothing would
        // interleave. (If meanwhile a GC is requested, the collector takes
        // priority; we wait it out in the re-acquire loop.) We only insist
        // on a hand-off while a peer is still queued.
        while inner.waiters > 0 && !inner.running && !inner.gc_requested {
            inner = self.sched.mutator_wake.wait(inner).unwrap();
        }
        // Now re-acquire normally (wait our turn behind the peer that ran).
        inner.waiters += 1;
        while inner.running || inner.gc_requested {
            inner = self.sched.mutator_wake.wait(inner).unwrap();
        }
        inner.waiters -= 1;
        *handle.parked_roots.lock().unwrap() = None;
        inner.running = true;
        handle.in_ml.store(true, Ordering::SeqCst);
        // Announce the take (see `acquire_ml_memory`): wake any OTHER
        // yielder blocked in its forced-hand-off loop.
        self.sched.mutator_wake.notify_all();
    }

    /// Request a stop-the-world GC and run it as the collector. Port of
    /// `MakeRootRequest` (processes.cpp:912) + the `allStopped` spin
    /// (processes.cpp:1369-1399). The caller is THE running thread (only
    /// the running thread allocates, so only it can hit the trigger).
    ///
    /// Steps:
    /// 1. Set `gc_requested` so no peer can newly acquire the lock and so
    ///    any peer reaching its safepoint parks (publishing its roots).
    /// 2. **Stop-the-world barrier (B4):** WAIT until every OTHER registered
    ///    thread is confirmed parked — `in_ml == false` AND its
    ///    `parked_roots == Some(..)`. Only then is it sound to move objects:
    ///    a peer still `in_ml` could be mutating its stack concurrently, and
    ///    a peer that is `in_ml == false` but has not yet published roots
    ///    (a fork TOCTOU survivor, or a thread mid-handshake) would be
    ///    skipped by the collector — both are use-after-free hazards. We
    ///    wait on `collector_wake`, which every park/release/publish nudges.
    /// 3. Run `collect` (the collector forwards our own roots + every parked
    ///    thread's published roots).
    /// 4. Clear `gc_requested` and wake the parked mutators.
    ///
    /// Single-threaded: the registry holds only us, so the barrier loop's
    /// "every other thread parked" predicate is vacuously true and returns
    /// immediately — byte-identical to a direct `self.gc()`.
    pub fn request_gc<R>(&self, handle: &Arc<ThreadHandle>, collect: impl FnOnce() -> R) -> R {
        {
            let mut inner = self.sched.inner.lock().unwrap();
            // We are the running thread; mark a GC so no peer can acquire
            // the lock mid-collection and so peers at their safepoint park.
            inner.gc_requested = true;
            // ---- Stop-the-world barrier: wait for every OTHER registered
            // thread to be parked (not in_ml) AND to have published its
            // roots. `running` stays true (we hold it), so no peer can
            // become the running mutator while we spin here.
            let me = Arc::as_ptr(handle);
            loop {
                let all_parked = inner.registry.iter().all(|h| {
                    if Arc::as_ptr(h) == me {
                        // Ourself: we are the running collector — roots
                        // forwarded directly, not via parked_roots.
                        return true;
                    }
                    // A peer is safe to forward IFF it is not touching its
                    // own stack AND has published a root-set the collector
                    // can reach. `in_ml == false` alone is NOT enough — the
                    // fork TOCTOU leaves a child not-in_ml but unpublished
                    // for a window; require Some as well.
                    !h.in_ml.load(Ordering::SeqCst) && h.parked_roots.lock().unwrap().is_some()
                });
                if all_parked {
                    break;
                }
                // Wait for a peer to park / publish, then re-check. (Each
                // park/publish/exit nudges `collector_wake`.)
                inner = self.sched.collector_wake.wait(inner).unwrap();
            }
        }
        // Run the collection WITHOUT holding the scheduler lock (the
        // collect closure re-locks `inner` and each handle's `parked_roots`
        // to read published roots — std Mutex is not reentrant, so we must
        // not hold `inner` here). `gc_requested == true` + `running == true`
        // + the barrier above guarantee exclusivity: no peer can acquire the
        // lock, and every peer is non-running with published, frozen roots.
        let r = collect();
        self.gc_count
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        {
            let mut inner = self.sched.inner.lock().unwrap();
            inner.gc_requested = false;
            self.sched.mutator_wake.notify_all();
        }
        r
    }

    /// Snapshot the registry handles (for the collector to iterate the
    /// parked threads' published roots).
    #[must_use]
    pub fn registry_snapshot(&self) -> Vec<Arc<ThreadHandle>> {
        self.sched.inner.lock().unwrap().registry.clone()
    }

    /// Number of live threads in the registry.
    #[must_use]
    pub fn registry_len(&self) -> usize {
        self.sched.inner.lock().unwrap().registry.len()
    }

    /// Whether the giant mutator lock is currently held (`running`). Test
    /// probe for the H2 negative control: an `exit_parked` from a NON-holder
    /// must NOT flip this off while a peer holds it.
    #[must_use]
    pub fn running_for_test(&self) -> bool {
        self.sched.inner.lock().unwrap().running
    }

    /// Test-only: publish a (dummy, root-free) `SendRoots` into a handle's
    /// slot + register it, marking it parked — without an `Interpreter`. Used
    /// by the H2 negative control to stage a "parked peer" deterministically.
    ///
    /// # Safety
    /// The published `SendRoots` thunks are never invoked by this path (no GC
    /// is run against this dummy); it exists only to satisfy the
    /// registered+published invariant so the peer looks parked.
    pub unsafe fn test_register_parked_dummy(&self, handle: &Arc<ThreadHandle>, roots: SendRoots) {
        let mut inner = self.sched.inner.lock().unwrap();
        *handle.parked_roots.lock().unwrap() = Some(roots);
        handle.in_ml.store(false, Ordering::SeqCst);
        inner.registry.push(Arc::clone(handle));
    }

    /// Relaxed check of whether a GC has been requested (the safepoint
    /// poll). Correctness only needs eventual visibility; the lock
    /// acquire is amortised over the 65536-step poll cadence.
    #[must_use]
    pub fn gc_requested_relaxed(&self) -> bool {
        self.sched.inner.lock().unwrap().gc_requested
    }

    /// Sample the current blocking-event generation. A blocking RTS path
    /// reads this BEFORE releasing the giant lock, then passes it to
    /// [`Self::block_until_event`] — so a wake that fires in the window
    /// between release and wait is not lost.
    #[must_use]
    pub fn block_gen(&self) -> u64 {
        *self.sched.block_gen.lock().unwrap()
    }

    /// Bump the blocking-event generation and wake all blocked waiters
    /// (mutex-unlock / condvar-wake / thread-exit / interrupt). Idempotent
    /// and cheap; spurious wakeups are fine (callers re-check their
    /// condition).
    pub fn notify_block_event(&self) {
        *self.sched.block_gen.lock().unwrap() += 1;
        self.sched.block_wake.notify_all();
    }

    /// Block until the blocking-event generation advances past `since`
    /// (i.e. some mutex-unlock / condvar-wake / exit happened after the
    /// caller sampled it). The caller must already have RELEASED the giant
    /// lock (published its roots) before calling this — this only waits on
    /// the `block_wake` condvar, not the giant lock.
    pub fn block_until_event(&self, since: u64) {
        let mut g = self.sched.block_gen.lock().unwrap();
        while *g == since {
            g = self.sched.block_wake.wait(g).unwrap();
        }
    }

    /// Like [`Self::block_until_event`] but with a millisecond timeout
    /// backstop (returns when the event fires OR the timeout elapses).
    /// Used by the join wait so a missed wakeup cannot hang forever.
    pub fn block_until_event_timeout(&self, since: u64, millis: u64) {
        let g = self.sched.block_gen.lock().unwrap();
        if *g != since {
            return;
        }
        let _ = self
            .sched
            .block_wake
            .wait_timeout(g, std::time::Duration::from_millis(millis))
            .unwrap();
    }
}
