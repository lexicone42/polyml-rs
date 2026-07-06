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
- **User data — Position 2 ADOPTED (measured free-to-faster).** The
  measurement gate ran (drift-cancelled A/B, the heap-heavy bench corpus on
  the self-bootstrapped REPL): converting the hot heap-word accessors
  (LOAD/STORE_ML_WORD, the INDIRECT family) to relaxed `AtomicUsize` was
  **~9.5% FASTER**, not slower (sort 6590→5928ms, and deriv/nbody/mmult all
  6–10% faster) — reproducible across interleaved iterations, so real, not
  noise. Mechanism: the atomic gives LLVM cleaner aliasing information than
  a raw `*p` deref (which may alias anything), so it keeps values in
  registers better across adjacent heap ops. So the abstract-machine-clean
  memory model that removes the data-race UB is ALSO a modest speedup — the
  decision is unambiguous. Landed for the hot word accessors (byte accesses
  stay plain: they carry no pointers, and a sub-word atomic would need RMW);
  byte-identical (the chain is unchanged). Historical context below.

- **User data — Position 2 (abstract-machine clean), the reasoning:** The recon's
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
- **P2b — per-thread nurseries. ✅ LANDED.** Every forked thread installs
  its OWN nursery (default 32 MB, `POLYML_CHILD_NURSERY_BYTES` override,
  1 MB floor) with a per-thread trigger; `gc()` gathers ALL pool nurseries
  and drives `collect_pool` (union from-space; promote-into-primary; reset
  children); the `POLYML_GC_AUDIT` residual scan runs per from-space range
  over the union; the untrusted RTS-arg ranges (`rts_safe_spaces`) cover
  every pool nursery. Collector ELECTION was verified structurally
  unnecessary under the giant lock (exactly one thread runs ⟹ only the
  runner can cross its trigger) — it lands with P4, where mutators run
  free. Known conservative limitation: the OPCODE-level untrusted predicate
  still validates against this thread's nursery only, so a cross-nursery
  pointer under the (out-of-envelope) untrusted+threads combo gets a clean
  `BadImage` halt, never unsoundness; widen with P4. Fences: the
  alloc-storm demo (3 workers, exact-total discriminator — written BEFORE
  the change and passing on both sides of it), a 2 MB-child-nursery variant
  (264 s of continuous child-triggered pool collections, total intact),
  all six concurrency demos, stage-0 + chain byte-identity.
- **P3 — protocol-word atomics. ✅ (mutex + thread-object words LANDED).**
  The SML `Thread.Mutex` protocol word is now manipulated with GENUINE
  atomics via `Interpreter::atomic_word` (an `AtomicUsize` view of the
  `repr(transparent)` PolyWord): lockMutex → `fetch_add(2, AcqRel)`,
  tryLockMutex → `compare_exchange`, atomicReset → `swap` (upstream's
  `AtomicallyReleaseMutex`/XCHG), atomicExchAdd → `fetch_add`, the legacy
  `atomic_incr_decr` → `fetch_add/sub`, and `reset_mutex_word` → atomic
  `store` (the plain store that could erase a peer's lock is GONE — the
  recon's verified not-upstream-faithful bug). Thread-object protocol words
  (flags word 1, requestCopy word 3, cross-read by BroadcastInterrupt/
  CondVarWake/testInterrupt) → Relaxed atomic load/store in
  `thread_obj_read`/`write` (request-delivery happens-before is carried by
  the handle's AtomicU8 + block_gen, not this ML mirror). All byte-identical
  single-threaded (an atomic op yields the identical value; not the hot
  path). PROOF: `concurrency_mutex_hammer` — two threads hammer ONE mutex
  400,000 lock/incr/unlock cycles, EXACT count (a lost update = wrong
  total). Remaining P3 (with P4): `gc_requested` → real atomic with explicit
  release-on-publish/acquire-on-collect ordering; per-subsystem RTS-static
  locks (audited already thread-safe by the shared-state recon — mostly
  Mutex/Atomic/OnceLock today).
- **P4 — drop the lock (`POLY_PARALLEL=1`). ✅ LANDED — TRUE PARALLELISM,
  measured: two compute-bound workers run at ratio 0.51 of the giant-lock
  wall-clock (23.66s → 12.04s; 0.50 is the 2-thread ideal), with
  byte-identical computed results. Implementation notes (refinements on
  the contract below, which is otherwise implemented as written):**

  * `SchedInner::running` became a **count** (`usize`); giant mode uses it
    as 0/1 (provably the old bool), parallel mode keeps it as a sanity
    invariant only. Every acquire/re-acquire wait loop is now
    `while (!parallel && running > 0) || gc_requested` — under
    `POLY_PARALLEL` only the collection component excludes.
  * The **sched mutex stays for state transitions** (brief, amortized —
    entry/exit/park/safepoint only, like upstream's schedLock) but no
    longer excludes runners. The per-step poll reads the lock-free
    `gc_requested_atomic` mirror (`gc_requested_poll`, Acquire), stored
    (Release) under the mutex at both request/clear sites.
  * Collector **election is the sched mutex itself**, not a separate CAS
    token: `request_gc_parallel`'s first-to-set-`gc_requested` wins;
    losers park as safepoint peers (publish + not-in_ml, counted by the
    winner's barrier) and return `None` — the caller just retries its
    allocation against the evacuated pool.
  * The pool-lock-parked clause proved unnecessary: `install_nursery` is
    brief and never blocks on scheduler state, and the collector takes
    the pool lock only AFTER the barrier confirms every peer parked — no
    lock-order cycle exists.
  * The cooperative yield is deleted under `POLY_PARALLEL` (early-return
    before the registry probe); the safepoint poll's only jobs are the
    STW check + request delivery.

  Fences (all green): `concurrency_parallel.rs` — alloc-storm exact
  total + `POLYML_GC_AUDIT=1` under 3 truly-parallel workers,
  mutex-hammer exact 400k (P3 protocol atomics now load-bearing),
  racy-ref bounded-value/no-crash, compute-scaling ratio gate (<0.85,
  measured 0.51), `POLY_PARALLEL`-without-real-threads no-op; every
  pre-existing demo (mutex/sockets/preempt/interrupt/stdin/exit/storm/
  hammer) passes BOTH flag-off and flag-on; the GC-handshake suite
  passes; stage-0 byte-identical flag-off AND with `POLY_PARALLEL=1`
  alone; `POLY_REAL_THREADS=1` step count unchanged by `POLY_PARALLEL`.

  **The original invariant contract (implemented):**

  *States.* Each thread is in exactly one of: RUNNING (`in_ml == true`,
  executing bytecode, may touch the heap), PARKED (`in_ml == false` AND
  `parked_roots == Some` — blocked wait / safepoint park / quiesced), or
  EXITED. The old giant-lock state (`running: bool`, `waiters`, the yield
  hand-off, `mutator_wake`-on-acquire) is BYPASSED under `POLY_PARALLEL`
  — mutators transition themselves without mutual exclusion.

  *H1′ (root reachability).* At every instant, a thread that is not
  RUNNING and not EXITED has published roots. Structural: every path that
  clears `in_ml` publishes FIRST (the existing publish-before-release
  helpers already enforce this order; the parallel path reuses them
  verbatim, minus the lock wake).

  *STW handshake.* `gc_requested` becomes a real `AtomicBool`
  (release-store by the requester, acquire-load at safepoints — the
  happens-before that makes published roots visible to the collector).
  Collector ELECTION: CAS on an `AtomicBool` owner token; the winner
  becomes collector, losers PARK at their safepoint like any peer (their
  own nursery-full condition re-checks after the collection — likely
  satisfied by the reset). The collector waits until every registered,
  non-exited peer is PARKED (in_ml false + roots published — the
  conjunctive check, per the fork-TOCTOU lesson), collects, clears
  `gc_requested`, then wakes parked peers. A thread blocked on the POOL
  LOCK during a pending STW must count as parked (it publishes before
  taking the pool mutex on the refill path — refill is a park-shaped
  operation).

  *Safepoint poll.* The 65536-step poll (+ every blocking park) checks
  `gc_requested` (acquire). Under `POLY_PARALLEL` the cooperative yield
  disappears (threads just run); the poll's only job is the STW check +
  request delivery. Bare `step()` loops (CLI checkpoint, diff drivers,
  embedder API) remain single-threaded-only — documented, unchanged.

  *What still serializes.* The sched registry mutex (registration /
  snapshots — cold); the nursery-pool mutex (install/refill — cold); the
  RTS statics' own locks (already in place); the protocol-word atomics
  (P3); `block_gen`/condvar machinery for blocking waits (unchanged).

  Fences: everything so far + N-thread compute-SCALING (two compute-bound
  threads under `POLY_PARALLEL` must approach 2× the giant-lock
  wall-clock — the honest headline number) + racy-ref probe (two threads
  hammering an unprotected ref: must not crash, values unspecified) +
  mutex-hammer exactness under `POLY_PARALLEL` + the alloc-storm +
  sockets/stdin demos under `POLY_PARALLEL` + the GC-audit soak with N
  threads. `POLY_PARALLEL` without `POLY_REAL_THREADS` is a no-op;
  default OFF keeps the giant-lock model byte-identical.
- **P5 — capstone + docs.** Multi-connection web server under load;
  README/CLAUDE/SECURITY/correctness-doc updates; the honest performance
  table. ✅ LANDED (4-connection compute server at 0.24×, 4-way ideal
  0.25, exact-oracle-verified responses; `concurrency_server.rs`).
- **P6 — PARALLEL COLLECTION (`POLYML_PARALLEL_GC=1`, default OFF) —
  BUILT + MEASURED. VERDICT: the parallel drain is SOUND but LOSES to a
  well-tuned serial sweep at every scale tested; the campaign's real
  yield was making the SERIAL collector ~3.7× faster (default-on).**

  What landed default-on (measured on a 512 MB heap, ~115 MB live tree,
  `POLYML_GC_PHASES=1` per-phase timing — also new):
  * **Pre-pass: 148 → 46 ms.** The per-object `(body, len)` table
    (~16 B/object, ~300 MB on a churny heap, built EVERY pause) became
    an object-start BITMAP (Σwords/8 bytes, cache-resident).
  * **Scratch: 175 → 0 ms.** `vec![PolyWord::ZERO; n]` missed Rust's
    `IsZero`→calloc specialization (custom struct) and explicitly
    memset the whole capacity; allocating as `Vec<usize>` + a
    repr(transparent) box transmute gets LAZY kernel zero pages — only
    live pages ever fault.
  * **Scan: 307 → 98 ms.** Slot forwarding no longer binary-searches
    the object table per slot (memory-bound, the dominant cost); the
    bitmap's exact-bit test resolves body-start pointers O(1), with the
    backward bitmap scan only for genuine mid-body values.
    **The chain fence caught a wrong first cut here**: ML slots are NOT
    always body starts — closure word-0 can hold an entry offset INSIDE
    a code object (a mid-body code pointer). The bitmap-exact-hit
    design handles both without heuristics. Total pause 680 → 185 ms;
    the Isabelle parallel-kernel benchmark dropped 4.6 → 1.4 s with
    DEFAULT nurseries (ratio vs giant-lock 0.78 → 0.31 — the
    big-nursery tuning knob is now much less needed).

  The FIRST parallel drain (queue-driven: claim-then-copy CAS + atomic
  bump + batched work-stealing queues) was proven sound but measured
  SLOWER than the optimized serial scan at every live size (115 MB: 168
  vs 98 ms; 900 MB: ~1.4 s vs ~0.7 s): the linear Cheney sweep's
  sequential prefetch beats 6 workers doing random-order queue visits
  with atomic claim traffic. It was REPLACED by **CHUNKED Cheney (the
  current implementation)** — see the P6b section below. Historical
  design notes for the shared pieces (claim protocol, gating) follow:

  *Claim protocol.* From-space header states: NORMAL → BUSY →
  TOMBSTONE(to-ptr). A copier CASes NORMAL→BUSY (BUSY = the tombstone
  bit with a NULL pointer — an otherwise-impossible encoding, since
  `bump_to` never returns null); the winner copies the body, then
  publishes the real tombstone with a Release store. A racing reader
  finding BUSY spins (`hint::spin_loop`) until the Acquire-loaded
  header becomes a real tombstone — the Release/Acquire pair makes the
  copied body visible. Exactly ONE copy per object, so the Σ-capacity
  to-space bound is preserved (no duplicate-copy waste).

  *Allocation.* One shared to-space, `to_used` becomes an atomic bump
  cursor (`fetch_add`, Relaxed — reservation is the only claim).

  *Scan.* The linear Cheney scan is REPLACED in parallel mode by a
  queue-driven scan: the claiming copier pushes each newly-copied
  object exactly once onto its worker-local deque; workers pop locally
  and steal from peers when dry. This sidesteps the
  scan-past-incomplete-copy hazard by construction (an object is only
  reachable via a queue AFTER its copy completed). Termination: a
  shared `pending` counter — incremented on push, decremented only
  AFTER an object's scan (including its child pushes) completes;
  workers exit when `pending == 0`.

  *What stays serial.* Root forwarding (seeds the queues; runs before
  workers spawn), the from-objects pre-pass, the untracked-address
  check, the promote/reset swap, per-thread fixup thunks, and the
  POLYML_GC_AUDIT pass.

  *Gating + identity.* Flag OFF (default) takes the exact pre-P6 serial
  path — stage-0 and the 27.7B-step chain stay byte-identical. Flag ON
  changes to-space LAYOUT nondeterministically (copy order races) —
  semantically invisible to SML (addresses are unobservable; pointerEq
  sharing is preserved by any copy order; upstream's parallel GC has
  the same property), but the byte-identity fences are therefore
  flag-off only. Worker count: `POLYML_GC_THREADS` override, default
  `available_parallelism`.

  Fences: all existing GC unit tests + the cross-nursery pool test run
  under the flag; alloc-storm + audit + the Isabelle kernel benchmark
  flag-on; the honest measurement is the Isabelle parallel-kernel ratio
  (0.37 serial-GC baseline) plus a single-mutator GC-heavy workload
  (the STW pause shrinks in EVERY mode, not just POLY_PARALLEL). Kill
  switch: if the measured win is noise (the whole-region-JIT
  precedent), flag stays off and the code is documented as a testbed.

- **P6b — CHUNKED CHENEY (`POLYML_PARALLEL_GC=1`, default OFF) — BUILT
  + MEASURED. VERDICT: an honest, bounded WIN on the shape it targets —
  scan 2.35× faster / total pause 1.7× shorter on a 410 MB wide live
  graph at 4 workers (plateaus there: memory-bandwidth-bound, 6 adds
  nothing); NEUTRAL on small-live and chain-shaped heaps; byte-identical
  SML results everywhere; the default serial path untouched
  (chain-fence-proven).**

  Design (all in `gc.rs::par`): one contiguous to-space arena; workers
  claim CHUNKS from an atomic frontier (one `fetch_add` per chunk, not
  per object — object allocation is a plain local bump) and sweep each
  chunk LINEARLY — the per-worker sequential prefetch the queue-drain
  lacked. The pieces that made it work:
  * **Filler seals.** A sealed chunk's dead tail is plugged with a
    byte-object header, so the promoted heap stays ONE contiguous valid
    object sequence — no multi-segment space accounting anywhere (the
    design problem that deferred P6b originally just dissolves).
    Workers also seal their final open chunk at quiescence.
  * **Root-prefix pseudo-chunk.** The serial roots phase copies into
    `[0, root_used)`; that prefix seeds the steal queue as the first
    chunk — zero changes to root forwarding.
  * **Two-slot worker + whole-chunk stealing.** Each worker allocates
    into `cur` and keeps one sealed-but-unscanned predecessor
    (`scanning`); further sealed chunks and OVERSIZE objects (exact
    arena slices, published only AFTER their copy completes) go to a
    mutex steal queue. Thieves sweep stolen chunks linearly — locality
    preserved.
  * **Adaptive chunk growth.** Chunks start at 4 K words and double per
    seal to 512 K: a collection that copies little claims little
    (constant-size chunks inflated `to_used` with fillers and fired the
    80% GC trigger EARLY on small heaps — measured as extra collections
    before the fix).
  * **Wide-object scan splitting.** `forward_slot` copies children
    inline during the parent's scan, so ONE wide pointer array put
    99.7% of a 410 MB probe on one worker (per-worker stats,
    `POLYML_GC_PAR_STATS=1`). Scans of word objects wider than 4 K
    words binary-split their slot ranges into the steal queue
    (`Task::Slots`) — breadth becomes stealable work.
  * **Termination.** A `busy` counter: workers decrement entering the
    idle probe, re-increment on acquiring work; `busy == 0` + empty
    queue = quiescence (copies only happen while scanning, so the
    condition cannot un-quiesce).

  Honest measurements (410 MB live, 900 MB heap, 9 collections,
  `POLYML_GC_PHASES=1`): WIDE graph (80×80 vector tree of 8 K-word
  arrays): scan 287 → 122 ms (4w), pause 398 → 234 ms; identical
  stdout. CHAIN of arrays (a linked list — inherent graph depth, no GC
  can parallelize it): copying stays on one worker, split-scan still
  trims scan 270 → 237 ms. Small-live workloads (the Isabelle 6-worker
  kernel bench, ~35 MB live): no measurable change — there the pause is
  dominated by the pre-pass + promote phases, which stay serial.
  Limits: the win needs live data big enough that scan dominates AND
  graph breadth; plateaued at 4 workers by memory bandwidth.

- **P6c — PING-PONG SEMISPACE REUSE (default ON) — the promote phase
  drops to ~0 and the serial scan nearly halves.** The phase profile on
  REAL workloads (the Euler LCF driver: promote 189 ms of a 429 ms
  pause) exposed where the pause actually went: every collection
  calloc'd a fresh to-space and DROPPED the old from-space — a ~190 ms
  munmap of the faulted pages inside the pause, plus an invisible
  mutator tax re-faulting the fresh lazy-zero arena after every
  collection, plus first-touch faults during the scan's own copying.
  Now the primary STASHES its retired from-space (`MemorySpace::spare`)
  and the next collection reuses it as scratch when big enough: no
  munmap, no re-fault; stale contents are harmless because the
  collector never reads to-space words it did not write. Measured
  (410 MB-live storm): serial pause 398 → 180 ms (scan 287 → 144 — the
  scan had been paying the fault cost; promote → 0.0), wall −9%;
  stacked with the P6b parallel drain: **pause 398 → 85 ms (4.7×)**.
  Euler driver: pause 429 → 239 ms. Gates: `POLYML_GC_REUSE_MAX_BYTES`
  (default 4 GB; 0 disables) bounds the sustained 2× residency on huge
  heaps, and `POLYML_GC_AUDIT=1` forces the calloc path — the audit
  scans `[0, len)` (stale tails would false-positive) and fresh
  mappings keep missed-root dangling pointers SEGV-detectable rather
  than silently reading recycled memory. Fences: ping-pong round-trip
  unit test (same buffer across cycles, correct results on the stale
  arena); the 27.7B-step chain byte-identical WITH reuse on (this
  change touches the default path — the chain is the read-before-write
  detector: any code depending on fresh-zero heap would diverge);
  370/372 diff-oracle (the 2 = the known upstream andb/orb stage-0
  bug); storm+audit suites green; regression fast green.

  Fences: 4 parallel unit tests incl. a chunk-churn stress (64-word
  chunks force hundreds of seal/steal/oversize transitions; filler-aware
  EXACT live accounting + full-heap walk validation) hammered 60×
  clean; `concurrency_parallel` storm+audit suite green flag-on
  (parallel mutators + parallel GC + heap audit); GC storm with
  `POLYML_GC_AUDIT=1` flag-on/off stdout-identical; the Euler
  theorem driver (3.3B steps of real LCF proving) flag-on/off
  stdout-identical; stage-0 + the 27.7B-step chain byte-identical
  (default path); `tools/regression.sh fast` green.

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
