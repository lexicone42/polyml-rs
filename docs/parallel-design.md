# Breaking the giant lock: true parallelism design

Status: **authoritative design** (recon-informed). Sources: a five-surface
recon fleet + completeness critic over the actual code (2026-07-02), the
upstream reference (`vendor/polyml/libpolyml/processes.cpp`, `gc.cpp`,
`quick_gc.cpp`), and this codebase's own concurrency history. The raw maps
(79 assumption sites with file:line cites, 48 change items, 43 hazards +
the critic's corrections) are preserved in the campaign notes; this document
is the distilled architecture + staging.

## Goal, non-goals, kill-switch

**Goal.** Multiple SML threads executing bytecode *simultaneously*:
per-thread allocation nurseries (lock-free bump allocation), one-collector
stop-the-world GC over all nurseries, the giant lock decomposed. Capstone:
a multi-connection SML web server; stretch: Isabelle `Par_List` on cores.

**Non-goals.** Parallel *collection* (single collector; upstream's GC task
farm is a later optimization); concurrent/incremental GC; minor
per-nursery GC (**unsound here by construction** — there are no write
barriers/remembered sets, and tenured/peer-nursery → nursery pointers are
unrestricted, so every collection is global STW over the union).

**Kill-switch.** Everything behind `POLY_PARALLEL=1` (default OFF). The
default path stays **byte-identical** at every stage (stage-0 1,110,805
steps; the 27.7B-step chain, same polyexport md5). `POLY_REAL_THREADS=1`
alone keeps today's giant-lock model — correct concurrency is the floor we
never give back. If a stage's soundness argument cannot be closed, STOP,
bank the landed stages, document the boundary. Performance is not a kill
criterion, but the honest headline requires the parallel path to beat the
giant lock on an embarrassingly-parallel workload — measured, either way.

## The five load-bearing decisions (recon-convergent)

1. **Allocation NEVER collects — nursery-full fetches a fresh chunk.**
   This codebase's biggest deliberate divergence from upstream (which pays
   for alloc-time GC with SaveVec handle discipline on every RTS
   allocation): ~40 RTS/opcode sites hold raw `*mut PolyWord` and popped
   PolyWords in Rust locals across sequential allocations
   (`make_syserr_exception`'s pair→packet chain, `ALLOC_WORD_MEMORY`'s
   popped init, `do_tuple`, select's vectors→triple, …). Rust locals are
   not GC roots; GC-at-allocation would convert every such site into a
   silent use-after-free. So: upstream's `FindAllocationSpace` shape —
   fixed-size nursery chunks handed to threads from a global pool (Mutex
   on the pool, amortized); a full nursery is retired (immortal until the
   next STW) and a fresh chunk installed. Objects never move outside STW.
2. **Per-thread nurseries, Box-pinned.** Each `ThreadHandle` owns its
   nursery; the three existing funnels (`Interpreter::alloc_space_mut`,
   `RtsContext.alloc_space`, `jit_bridge`) make the fast path a
   fix-in-one-place change. Nurseries must be individually heap-pinned
   (never `Vec<MemorySpace>` — Vec growth moves the structs, dangling the
   whole-region JIT's baked `addr_of!(space.used)` pointers and any live
   `RtsContext` borrow). The per-step GC-trigger check becomes a read of
   the thread's OWN counter — faster than today's shared read, and free of
   shared-cacheline traffic (the perf cliff the recon flagged).
3. **One collector, elected; everyone else parks.** Two mutators crossing
   their triggers simultaneously is the recon's #1 deadlock (both set
   `gc_requested`, both wait for the other to park — livelock; structurally
   impossible today, immediate under parallelism). Election: CAS an owner
   token; losers park as peers. A thread blocked on the *pool lock* during
   a pending STW must count as parked for the barrier. The existing
   publish-before-release root discipline (H1/H2, `parked_roots`,
   `rts_park_root`) **generalizes as-is** — it was built for N parked
   threads and is the strongest asset in the codebase. `running`/`waiters`/
   the yield hand-off get **deleted on the parallel path**, not adapted;
   `in_ml` (a count) + the safepoint poll become the only stop mechanism,
   later upgraded to a per-thread trap flag so the collector can hasten
   stragglers (upstream's `InterruptCode`).
4. **Cheney generalizes by membership, not by space.** `gc.rs` forwarding
   is already membership-driven (`contains` + `find_object`); from-space
   becomes a sorted range-set over all nurseries; every nursery is
   evacuated every cycle into a shared destination (promotion). The
   to-space sizing assert must be Σ-aware (a naive port either panics
   mid-collection — unrecoverable, half-tombstoned heap — or silently
   doubles peak RSS × N). Three shared-read footguns fixed first:
   `gc_requested` becomes a real atomic with release-on-publish /
   acquire-on-collect ordering (it currently inherits ordering from the
   sched mutex); the collector reads **Runtime's** image roots, not its
   per-Interpreter clone; per-nursery trigger accounting.
5. **A Runtime-owned live-space table with a GC epoch.** Every edge
   consumer — `safe_deref`, `RtsSafeSpaces`, export's `ptr_ok`, the GC
   audit — reads or snapshots one authoritative table (image spaces +
   tenured + nurseries), epoch-stamped so stale snapshots self-invalidate.
   The recon's sharpest edge finding (the **validator-UAF inversion**):
   a stale untrusted-mode range doesn't just mis-answer — `validate_obj_fit`
   derefs `p.sub(1)` after the range check passes, so a range covering a
   freed from-space turns the safety mechanism itself into the UAF.
   Export and untrusted-mode validation run as STW operations in v1 (cold
   paths; the barrier already exists). Cross-nursery *untrusted* validation
   is only sound against bounds frozen at a safepoint (a peer's `used` is
   mid-bump; header writes are non-atomic) — use published used-marks.

## The memory model (written position — fifth recon map folded in)

With N mutators, SML programs sharing `ref`s without `Thread.Mutex` race.
Upstream: plain loads/stores for user data; interlocked ops only for the
mutex/condvar protocol (`processes.cpp` AtomicIncrement/Decrement/Exchange,
taken under a global `mutexLock` in interpreter builds — `bytecode.cpp`).

**The atomics site inventory (recon-complete).** The words that MUST become
atomic: the Thread.Mutex protocol word — `EXTINSTR_LOCK_MUTEX` (mod.rs
~6114, read-then-write TOCTOU today), `TRY_LOCK_MUTEX` (~6138),
`EXTINSTR_ATOMIC_RESET` (~6170, must be an atomic *exchange* or the
"was-I-sole-locker" answer lies), `ATOMIC_EXCH_ADD` (~6202),
`atomic_incr_decr` (~6764), `reset_mutex_word` (~2833, called from
MutexUnlock/CondVarWait/WaitUntil); and thread-object words 1 (`flags`,
SML-written via STORE_ML_WORD, cross-read by BroadcastInterrupt/CondVarWake)
and 3 (`requestCopy`, cross-written by make_thread_request). `ThreadHandle.
requests` (AtomicU8, fetch_max + CAS-consume) is ALREADY the correct
template. **Correction the map verified against upstream:** the
`PolyThreadMutexUnlock` arm's plain word reset is NOT upstream-faithful
(`Processes::MutexUnlock` doesn't write the word) and can erase a peer's
just-taken lock; the CondVarWait/WaitUntil preamble resets ARE faithful
(`AtomicallyReleaseMutex`).

**Already-safe (map-confirmed, no change):** every process-global is already
`Mutex`/`Atomic`/`OnceLock` EXCEPT the two P0 semantic ones (`FINISH_REQUESTED`,
SIGINT's `INTERRUPT_PENDING` — both handled in P0). `CURRENT_PARK`/`JIT_INTERP`
are `thread_local!` (correct *provided* one OS thread drives one Interpreter —
an invariant to keep). Interpreter per-thread fields (stack/sp/pc/frames/
thread_object/bootstrap_tail_call — the last two explicitly hoisted from
globals for exactly this) are correct; `rts: Arc<RtsTable>` is immutable
post-register (fingerprint-protected). The `bootstrap_tail_call`
global→per-thread hoist is the proven prior-art pattern for the remaining
migrations.

Our position, staged:

- **Protocol words become genuinely atomic** (the SML `Thread.Mutex` lock
  word, condvar words, thread-object `requests`/`requestCopy`/flags):
  relaxed/acq-rel `AtomicUsize` views over the heap word, faithful to
  upstream's interlocked semantics. v1 mirrors upstream interpreter-mode
  exactly: one global mutex around the interlocked opcodes, then optimize
  to per-word atomics (keeps the differential oracle meaningful).
  Correction from the critic: the `PolyThreadMutexUnlock` arm's extra
  plain word-reset is NOT upstream-faithful (upstream never writes the
  word there) and can erase a peer's just-taken lock — it must go atomic
  or go away; the CondVarWait preamble resets ARE upstream-faithful
  (`AtomicallyReleaseMutex`) and just need the atomic port.
- **User data — LEANING Position 2 (abstract-machine clean).** The recon's
  decisive argument is identity, not physics: this project's whole
  differentiator is "faithful port with **stronger** memory safety," and
  Position 1 (plain raw-pointer racy accesses, upstream's C model) embeds a
  class of textbook data-race UB that Miri/TSan flag on day one — betraying
  the brand for a few percent the 4×-slower-than-upstream dispatch loop
  renders immaterial. Position 2: route every heap-word load/store (the
  INDIRECT family — INDIRECT_LOCAL_B0/B1 are the profiled-hottest opcodes —
  LOAD/STORE_ML_WORD/BYTE/UNTAGGED, blockMove, `thread_obj_read/write`, the
  header rewrite in `clear_mutable_bit`, and GC's `forward` reads) through
  `AtomicUsize::from_ptr(p).load/store(Relaxed)`. On x86-64/aarch64 a
  Relaxed load/store is the SAME instruction as a plain one — cost is only
  inhibited compiler reordering of adjacent heap ops. What does NOT change:
  the per-thread ML stack (private), immutable code-byte fetches, and
  fresh-object init (the STW handshake's Mutex/SeqCst boundaries already
  provide the publication fences). **The measurement gate stays**: wrap the
  accessor in one inline helper, build both, run `tools/bench.sh`; if
  Position 2 is ≤ a few % (expected), take it and the UB boundary
  disappears entirely. The full plain-store site list (now inventoried
  above) gates the start of P4 — scheduler surgery does not begin without
  it.

## P0 — the semantic layer (the critic's find: build this FIRST)

Cheap, flag-invisible, and every multi-mutator test depends on
deterministic shutdown — without these the negative-control suite itself
hangs:

- **PolyFinish is an inversion today**: the flag is consumed by whichever
  thread steps next — `OS.Process.exit` in one thread can kill a random
  worker while the exiting thread continues. Becomes: broadcast KILL +
  bounded join + the requester carries the exit code.
- **The un-killable signal daemon**: `PolyWaitForSignal`'s
  `loop { block_on_event() }` never checks `requests` — every shutdown
  design deadlocks on it. The loop honors KILL. (Also a hidden N-mutator
  cost: it does a full root-capture/publish on every global block event.)
- **SIGINT routes through `BroadcastInterrupt`** (per-thread delivery honoring
  InterruptState), not the first-poller process flag.
- **Process-globals audit**: `FINISH_REQUESTED`, `COMMAND_ARGS`, the
  synthetic-stdin queue move behind `Runtime` (the existing test-only
  `FINISH_FLAG_LOCK` is the smoking gun that these already bite under
  parallel *tests*). Two `Session`s per process get documented/enforced.
- **Thread-id export scrub**: dense per-process ids persisted in exported
  thread objects resurrect against live handles on reload
  (`handle_for_thread_object` would mis-target) — exports scrub word 0.
- **Bare `step()`/`run()` loops** (CLI checkpoint loop, `poly diff`
  drivers, embedder API) either take the acquire bracket + safepoint poll
  or are documented single-threaded-only; a stepping loop that never polls
  deadlocks the STW barrier.
- Pre-existing hole (fix regardless): `for_child_thread` hard-codes
  trusted mode — the first fork in an `--untrusted` session currently
  de-fangs the safe mode for that child.

## Stages (each flag-gated, each fully fenced before the next)

- **P0 — semantic layer** (above). Flag-invisible; all existing fences.
- **P1 — nursery plumbing, single-threaded. ✅ LANDED.** The heap moved
  from `Runtime.heap` (one `Option<MemorySpace>` behind an UnsafeCell) into
  a `NurseryPool` (`Vec<Pin<Box<MemorySpace>>>` behind a Mutex, in
  `sched.rs`). Each `Interpreter` caches a raw `*mut MemorySpace` handle to
  its nursery — resolved once from the pool, stable for life (Box-pinned),
  so the hot allocation path (`alloc_space_mut`/`nursery_ptr`) never takes
  the pool lock. The pool lock is taken only to install a nursery (build
  time) or by the collector (`gc()` reaches nursery 0 via
  `runtime.nursery_handle(0)`). P1 has exactly ONE nursery, so the
  single-space `collect` is byte-identical; the collector still evacuates
  one space (multi-range membership is P2). Forked children share nursery 0
  through the pool. Fences all green: stage-0 + 7-stage chain byte-identical,
  the tiny-heap GC-UAF fence (GC actually fires + collects through the pool),
  all six concurrency demos, 102/0 units, 13/13 runtime integration.
- **P2a — multi-space-capable collector. ✅ LANDED.** `collect` →
  `collect_pool(&mut [&mut MemorySpace], visit_roots)`: from-space is the
  UNION of all nurseries (sorted range-set, binary-search membership); the
  object pre-pass walks every nursery's used region; the to-space is Σ
  CAPACITY (can never overflow — live ≤ Σ used ≤ Σ capacity); after the
  Cheney scan the primary takes the to-space and every other nursery is
  reset empty (its live objects PROMOTED into the primary, every pointer
  forwarded). Cross-nursery pointers need no special case. For N=1 this is
  byte-identical to the old single-space collect (Σ capacity = primary
  capacity). Proven by a hand-built two-nursery unit test
  (`collect_pool_forwards_cross_nursery_pointer`): a parent in nursery A
  pointing at a leaf in nursery B — both promote into A, B resets empty,
  the cross-link is rewritten. Byte-identity fences all green.
- **P2b — per-thread nurseries + collector election.** Give each forked
  thread its OWN nursery (today they share nursery 0); `gc()` collects the
  whole pool; CAS collector election so two trigger-crossers don't
  livelock; pool-lock-blocked threads count as parked for the barrier. Still
  giant-locked, so no new heap-word races. Fences: all six concurrency demos
  + fork-heavy allocation storm under `POLYML_GC_THRESHOLD=1` + `GC_AUDIT`
  over the union + negative controls for the new invariants (election
  livelock, Σ-sizing, pool-lock parking) built BEFORE the code — this
  project's history says the test is the discovery instrument.
- **P3 — atomics + statics.** Protocol words atomic (upstream-faithful,
  global-mutexLock shape first); RTS statics behind per-subsystem locks;
  `gc_requested` a real atomic with explicit ordering. Still giant-locked.
- **P4 — drop the lock (`POLY_PARALLEL=1`).** Gated on the fifth map's
  plain-store inventory + the measured atomics decision. Mutators run
  free; safepoint poll = STW check; `running`/yield deleted on this path.
  Fences: everything + N-thread compute-scaling (must beat the giant lock
  wall-clock) + racy-ref probe (must not crash; values unspecified) +
  Mutex-hammer exactness + the sockets/stdin demos under `POLY_PARALLEL`.
- **P5 — capstone + docs.** Multi-connection web server under load;
  README/CLAUDE/SECURITY/correctness-doc updates; the honest performance
  table.

## Fence plan

Every stage: stage-0 byte-identity; the 27.7B-step chain byte-identity
(default path); registration fingerprint; the five concurrency demos; the
GC-handshake suite (re-examined under the new orderings when `gc_requested`
goes atomic). New: N-thread allocation-storm soak (threshold=1, audit on);
collector-election negative controls; Σ-overflow to-space test; the
racy-ref and Mutex-exactness probes; web-server load test. The
`forward_stack_slot` no-tag-filter alias risk (any integer aliasing any
nursery range gets rewritten) scales with total nursery VA — the soak
must run long enough to be a statistical instrument, and nursery VA should
be kept compact.
