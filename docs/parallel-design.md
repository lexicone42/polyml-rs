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

## The memory model (written position)

With N mutators, SML programs sharing `ref`s without `Thread.Mutex` race.
Upstream: plain loads/stores for user data; interlocked ops only for the
mutex/condvar protocol (`processes.cpp` AtomicIncrement/Decrement/Exchange,
taken under a global `mutexLock` in interpreter builds — `bytecode.cpp`).
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
- **User data stays plain-but-racy-by-contract**: raw-pointer word-aligned
  loads/stores (never `&mut` over shared words); no tearing on aligned
  64-bit words on x86-64/aarch64; racy programs get unspecified *values*,
  never memory-unsafety. This is de-facto (hardware + raw pointer)
  soundness rather than Rust-abstract-machine purity — the same boundary
  upstream lives with — documented in the correctness docs as such.
  Before committing: **measure** the clean alternative (relaxed
  `AtomicUsize` for every bytecode heap load/store) on the single-threaded
  benchmark suite; if it is ≤1–2% we take it and the boundary disappears.
  (The fifth recon map — the full plain-store site inventory — gates the
  start of P4; scheduler surgery does not begin without it.)

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
- **P1 — nursery plumbing, single-threaded.** Chunk pool + per-thread
  nursery owned by the handle (Box-pinned); the CLI path uses exactly one
  nursery; GC learns range-set membership but still collects one nursery.
  Byte-identity proves the plumbing invisible.
- **P2 — multi-nursery GC, still giant-locked.** Forked threads get their
  own nurseries; the elected collector evacuates all of them; the giant
  lock still serializes execution (no new races yet). Fences: all five
  concurrency demos + fork-heavy allocation storm under
  `POLYML_GC_THRESHOLD=1` + `POLYML_GC_AUDIT` widened to the union +
  negative controls for the new invariants (collector election, pool-lock
  parking, Σ-sizing) built BEFORE the code — this project's history says
  the test is the discovery instrument.
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
