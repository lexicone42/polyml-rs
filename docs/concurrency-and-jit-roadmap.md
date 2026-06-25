# Concurrency & whole-region JIT — next-swing roadmap

> **STATUS (2026-06-25): Track A increments 1–3 LANDED.** Real OS threads ship
> behind `POLY_REAL_THREADS=1` (default OFF, single-threaded path byte-identical):
> giant lock + safepoint stop-the-world GC (`crates/polyml-runtime/src/sched.rs`),
> real `Thread.fork`/`Mutex`/`ConditionVar`, the 2-thread mutex demo passing
> end-to-end on the `polyexport` REPL (`concurrency_mutex_demo.rs` → counter=200000),
> and the runtime-level GC-handshake/H1/H2/TOCTOU controls
> (`concurrency_gc_handshake.rs`, ASAN-clean). The startup-hang keystone: the basis
> signal thread loops on `PolyWaitForSignal` and must PARK (daemon flag) once `fork`
> is real, or it busy-spins the giant lock. STILL OPEN: a preemptive scheduler
> (only cooperative safepoint yielding today), `Thread` attribute fidelity, and
> Track B (whole-region JIT). The roadmap below is the original planning artifact.

> Output of the `arch-design` design+feasibility fleet (2 designs -> adversarial
> feasibility critics -> synthesis). Both first-increments-as-scoped came back
> NO-GO; the value is the re-sequencing both critics converged on: land the
> generalized safepoint/multi-root GC substrate (single-threaded, oracle-verified,
> zero behavior change) FIRST, since it gates BOTH tracks. Grounded in source
> (file:line cites). A planning artifact, not a commitment.
>
> **Correction (2026-06-24, post-synthesis):** the critics treated the below-`sp`
> GC use-after-free as still-latent and the `POLYML_GC_AUDIT` detector as blind to
> it. That is OUT OF DATE — it was fixed + tested in commit 8756419 (task #109):
> every collect scrubs `[0,sp)` to `Tagged(0)` (`interpreter/mod.rs:823`) and the
> audit now scans the full stack `[0,len)` (`mod.rs:878`); reproducer
> `gc_tiny_heap_uaf.rs` passes and the tiny-heap soak is clean. So the "fix the
> below-`sp` invariant first" gating prerequisite is ALREADY DONE; the remaining
> shared substrate is only the multi-root root-walk extraction.

---

# polyml-rs: Next-Swing Roadmap — Concurrency vs. Whole-Region JIT

*Decision-ready synthesis. Written after the quadratic-reciprocity work, for choosing the next build target. Every architectural claim below is grounded in source; citations are `file:line`.*

> **Input caveat (read first):** The critique payload I received was truncated mid-sentence inside the concurrency design (it cuts off at "captures only `Arc<Runtime>` + the (heap) PolyWord for `function` (not…"), and **only the concurrency track's critique was included** — the whole-region JIT design + its adversarial critique were not delivered to me. I verified the concurrency design's structural claims directly against source and upstream, and they hold. For the JIT track I reconstruct the position from the codebase's own extensive documentation (`CLAUDE.md` §Performance & JIT, `PLAN.md`, and `crates/polyml-jit/src/lib.rs`), and I mark inferred critic-positions as such. If a written JIT critique exists, reconcile this section against it before committing.

---

## Track A — Real Concurrency (giant-lock interpreter + safepoint stop-the-world GC)

### 1. Plain summary of the landable slice
Port upstream's exact model (`processes.cpp`): one shared ML heap, a single global "mutator lock" that means *"I am the thread currently allowed to run bytecode,"* released at each safepoint so threads interleave cooperatively (concurrency, **not** parallelism). The GC becomes stop-the-world: any thread crossing the allocation threshold requests a collection, every other thread parks itself at its next safepoint having saved a consistent root set, and the collector forwards *every* thread's roots before waking them to re-fix their pointers. The landable first slice delivers correct `Thread.fork` / `Mutex` / `ConditionVar` semantics — real blocking, real wakeups, real interleaving — which today are single-thread fakes (`EXTINSTR_LOCK_MUTEX` just writes word0, `mod.rs:2610`; `PolyThreadForkThread` allocates a *dormant* descriptor and never runs the function, `rts.rs:1825`; `CondVarWait` is `noop2`, `rts.rs:848`). It does **not** deliver multicore speedup — under the giant lock only one SML thread executes at a time.

### 2. Go / No-Go after critique
**GO, but staged and bounded.** The design is faithful (it copies upstream's `inMLHeap`/`schedLock`/`MakeRootRequest` machinery, confirmed at `processes.cpp:212-223, 774, 878, 912`), and the existing GC already does the hard pointer-fixup math the design reuses — capturing byte-offsets for `pc`, `code_end`, every `frames` start, and every `handler_frames_depth` entry, then restoring them post-swap (`mod.rs:660-692, 836-850`). Generalizing that from "the one `self`" to "iterate a registry" is mechanical.

**The critic's most important caveat** (this is the load-bearing one, and it is *not* in the part of the design I can read because the JSON truncated exactly there): **the GC root set is currently `self`, and making it a registry means the collector must own/borrow every parked thread's `ThreadContext` while that thread is blocked — which collides head-on with Rust's aliasing rules and with the existing latent below-`sp` use-after-free.** Two concrete, source-confirmed hazards the critique would flag:

- **The collector scans only `[sp, len)` and panics on any untracked from-space pointer** (`mod.rs:709`, `gc.rs:381`). The MEMORY.md "GC use-after-free" entry already records that `drop_n`/`RESET` leave dangling from-space pointers *below* `sp` that the forward loop and `POLYML_GC_AUDIT` are both blind to. Today that's latent (the fixed 1.6 GB `Box` never shrinks under it). The moment you have **N parked stacks**, each parked at an arbitrary safepoint, the probability of a below-`sp` dangling pointer in *some* thread being re-exposed across a collection rises sharply — and the collector has no detector for it. **The safepoint-GC build must fix the below-`sp` scrub-or-scan invariant first** (the existing scrub-to-`Tagged(0)` at `mod.rs:823` is the seed of the fix; it must become an invariant enforced at every safepoint, per-thread).

- **Ownership.** The collector mutates each thread's saved root slots in place (it rewrites `frames`, `handler_frames_depth`, `thread_object`). With one interpreter that's `&mut self`. With a registry, the collecting thread needs `&mut` to *other* threads' contexts while those threads are parked. The design's "registry of `Arc<ThreadHandle>`" must therefore expose each context's roots behind a lock the parked thread is provably *not* holding (it released the mutator lock to park) — and the parking handshake (`threads_in_heap` drops to 1) is what makes that provable. This is correct in principle but is the single most error-prone seam; it must be encoded so the type system, not a comment, enforces "the collector only touches a context whose thread is confirmed parked."

### 3. Staged plan (ordered, with effort tags)
1. **[S, ~1 wk] Hoist per-thread state out of process-global statics, single-threaded still.** Move `FINISH_REQUESTED` is process-level (keep), but `BOOTSTRAP_TAIL_CALL` (`rts.rs:1274`) and `thread_object` (`mod.rs:362`) become per-`ThreadContext`. Make `thread_object` a *real* per-thread `ThreadObject` (layout already documented at `rts.rs:1816-1823`) registered by identity. Ship as a no-op refactor verified by the existing differential oracle (~1,300 cases) + bootstrap → `Tagged(0)`. **This increment is shippable on its own and de-risks everything after.**
2. **[M, ~1.5 wk] Introduce `Runtime` (Arc-shared): shared heap + `SchedState (Mutex+Condvar)` + thread registry.** Heap moves from per-`Interpreter` `alloc_space` (`mod.rs:317`) to one `Runtime` `MemorySpace`; allocation bumps a shared pointer *held only by the active mutator*. Still exactly one thread — proves the giant-lock plumbing without touching GC scanning. Re-run oracle + bootstrap.
3. **[L, ~2 wk] Generalize the GC root walk to iterate the registry**, and **fix the below-`sp` invariant** as a precondition. Per-thread root forwarding reusing the existing offset-capture/restore (`mod.rs:660-692, 836-850`). Add a per-thread post-fixup `POLYML_GC_AUDIT` that also scans `[0, sp)` for residual from-space pointers (close the detector blind spot). **Test with two threads where thread B is a pure spinner that forces GCs while A allocates** — the minimal stop-the-world exerciser.
4. **[M, ~1.5 wk] Real safepoint + cooperative yield.** Augment the existing poll site (`mod.rs:1386`, `steps & 0xFFFF == 0`) with `runtime.safepoint(self)`: check `gc_requested`, park if set; check this thread's request queue (interrupt/kill); opportunistically drop+reacquire the mutator lock so a peer runs. This is where interleaving becomes observable.
5. **[M, ~1.5 wk] Real `fork` / `Mutex` / `CondVar`.** `PolyThreadForkThread` (`rts.rs:1825`) spawns an OS thread with a fresh `ThreadContext` sharing `Arc<Runtime>`. Wrap blocking RTS calls (IO, `CondVarWait`, `MutexBlock`, sleep) in `release_ml_memory()`/`acquire_ml_memory()` so a blocked thread counts as "stopped" for GC — this mirrors upstream's `WaitInfinite` **exactly** (release ML memory around the wait, `processes.cpp:533`, which I verified). First real concurrent SML program runs.
6. **[S, ~0.5 wk] Interrupt/kill delivery** (`InterruptThread`/`BroadcastInterrupt`, currently no-ops at `rts.rs:1060-1061`) routed through the per-thread request queue + the safepoint.

### 4. Single biggest risk
**The below-`sp` dangling-from-space UAF (already documented as latent) becomes reachable and intermittent the moment multiple stacks are parked across a collection.** It is a memory-safety bug in the exact subsystem whose *whole point* is memory safety, and the current GC audit cannot see it. If step 3 doesn't make "no below-`sp` from-space pointer survives a safepoint" a *type/invariant-enforced* property, the project ships a faithful concurrency model with a worse safety story than the single-threaded one it replaces.

---

## Track B — Whole-Region JIT (native-code speedup)

*(Reconstructed from the codebase; the design doc + critique were not in my input.)*

### 1. Plain summary of the landable slice
Today's JIT compiles **one code object at a time** to Cranelift IR and trampolines back to the interpreter at every call boundary (`crates/polyml-jit/src/lib.rs:100-113`). It is correct end-to-end (bootstrap, 7-stage chain, all HOL4 tests) but only **~2% faster** than the interpreter (`CLAUDE.md` §Performance). Whole-region JIT means compiling a **connected region of functions** (a hot call tree) into one native unit so that intra-region calls become native `call`s that don't pay the trampoline + don't desynchronize the stack. The landable slice would be: pick the hottest connected region from the profiler, compile it as a unit honoring Poly/ML's non-popping call convention natively, and demonstrate a real (>1.3×) speedup on one workload. It does **not**, in its first slice, make the whole system fast — it makes one measured region fast.

### 2. Go / No-Go after critique
**NO-GO as the *next* swing; keep as future-work.** (Inferred critic position, strongly supported by source.) The wall is precisely documented and structural: the hottest functions are blocked by `CALL_CONST_ADDR` / `CALL_LOCAL_B`, which model a **non-popping call convention** — args physically persist on the stack across the call, and the callee's `RETURN_N` collapses them (`lib.rs:251-263`, citing `bytecode.cpp:411-414, 454-460`). The current per-call trampoline can only install such functions when *every* CCA sits in tail-equivalent position (`cca_all_tail_equivalent`, `lib.rs:283`); a mid-function CCA over-pops, leaving a later `INDIRECT_CONTAINER_B` to deref a stale `tagged-0` as a heap pointer → SIGSEGV (proven on install index 0, `lib.rs:260-263`).

**The critic's most important caveat:** whole-region compilation isn't an *extension* of the current JIT — it requires **re-architecting how compiled code models the SML stack**, because the entire speedup hinges on representing the persistent-args/`RETURN_N`-collapse convention in native IR *correctly mid-function*, which is the exact thing the current translator gets wrong. That is a from-scratch codegen design (stack maps across the region, a faithful frame model, GC-safepoint integration *inside* native code), competing for the same safepoint/GC-stack-scanning work that Track A needs anyway. And per MEMORY.md the JIT's current honest value is as a **correctness testbed** (`poly diff`), not speed — so the opportunity cost of *not* doing it is low.

### 3. Staged plan (ordered, with effort tags) — *if pursued later*
1. **[M] Region selection from the profiler.** `poly run --profile` already dumps hot opcodes/functions; add hot-call-tree extraction.
2. **[XL] Faithful native frame model.** Represent the non-popping convention + `RETURN_N` collapse in Cranelift so mid-region CCA/`CALL_LOCAL_B` are correct (the root unsolved problem, `lib.rs:240-269`).
3. **[L] In-native-code GC safepoints + stack maps** for the region (shares machinery with Track A's safepoint work — note the dependency).
4. **[M] Region install/trampoline boundary** (only at region edges, not per call).
5. **[M] Differential-validate** via the existing interp-vs-JIT `poly diff` harness before trusting any region.

### 4. Single biggest risk
**It may be a large multi-month codegen rewrite that lands a speedup on synthetic hot loops but never moves the needle on the real workloads (Isabelle/HOL4 proving), because those are dominated by allocation + GC + megamorphic dispatch, not by interpreter loop overhead.** The 2% ceiling today is a warning sign that the interpreter loop isn't the bottleneck. High effort, uncertain payoff, and the payoff is invisible to the project's actual users (the proving towers), who care about *what can be proved*, not raw speed.

---

## RECOMMENDATION

**Build Track A (concurrency), staged. It is the better next swing on every axis that matters for this project — but ship it one increment at a time, and treat the below-`sp` GC invariant as a gating prerequisite, not a follow-up.**

Reasoning across the four lenses:

- **Shippability of the first increment.** Track A step 1 (hoist per-thread state, still single-threaded) is a self-contained, oracle-verifiable refactor that lands value (correctness clarity) with near-zero risk. Track B has *no* small correct first increment — its first honest milestone is "solve the mid-function non-popping convention," which is the hard part, not a warm-up.

- **Observable user value.** Concurrency turns three *currently-fake* primitives into real ones: `Thread.fork` actually runs (today it's dormant, `rts.rs:1825`), `Mutex` actually blocks (today it pokes word0, `mod.rs:2610`), `CondVar` actually waits/wakes (today `noop2`). That is a visible capability jump — concurrent SML programs run for the first time. Track B's win (2%→maybe 130% on one region) is invisible to the HOL4/Isabelle users who define this project's character.

- **Correctness risk.** Both touch the GC, but Track A *reuses* the existing, battle-tested offset-capture/fixup logic (`mod.rs:660-850`) and follows upstream's exact, proven model (`processes.cpp`) — it's a *port*, the project's core competency and its stated faithfulness goal. Track B requires *inventing* correct native codegen for a convention the current JIT demonstrably gets wrong (SIGSEGV at `lib.rs:260`). Porting a proven design is lower-variance than inventing one.

- **Advances the project's character (faithful + safe Poly/ML).** This is decisive. polyml-rs's thesis is *"a faithful port with stronger memory safety."* Concurrency is the largest remaining faithfulness gap — `PLAN.md:86` and `CLAUDE.md` both name "full concurrency" as the headline open item, and upstream's whole `processes.cpp` model is currently faked. Closing it directly advances *faithfulness*. And done with the below-`sp` invariant fix, it advances *safety* too (it forces the project to finally close a documented latent UAF). Track B advances neither faithfulness (upstream's compiler also uses native codegen, but ours diverges in approach) nor safety (more `unsafe` native codegen is a safety *liability*, not an asset).

**One honest qualifier:** Track A delivers *concurrency*, not *parallelism* — under the giant lock only one SML thread runs at a time. That is exactly upstream Poly/ML's interpreter-mode model, so it is faithful; but set the expectation explicitly so "we have threads now" isn't misread as "we got faster." True parallelism (per-thread heaps / parallel GC) is a separate, much later phase that `PLAN.md:238,250` already correctly defers.

**Track B should stay future-work** until either (a) a concrete proving workload is shown to be interpreter-loop-bound (it currently isn't — the 2% ceiling argues otherwise), or (b) the safepoint/stack-map machinery built for Track A makes the in-native-code GC integration cheap enough to change the calculus. Its standing value as a `poly diff` correctness testbed is real and is preserved by doing nothing.

---

## Observations (beyond scope)

- **Stale CLAUDE.md follow-up.** CLAUDE.md's closing note (and one MEMORY.md entry) says the four-square FULL driver still needs promoting to a fenced `#[ignore]` test with artifacts in "gitignored resume scratch." That appears **already done**: `four_square_full_theorem` is a real `#[ignore]` test at `crates/polyml-bin/tests/isabelle_four_square.rs:98` (on `/tmp/l4_foursq_star`), and the resume artifacts under `tests/isabelle_support/four_square_resume/` are **tracked, not gitignored** (`git check-ignore` returns nothing; `base.sml`, `assembly_delta.sml`, the eight divide-leaf deltas, etc. are all present). Worth deleting the follow-up note so it stops reading as open work.

- **The two tracks share their hardest dependency.** Both need GC safepoints that scan native/parked stacks correctly. If concurrency is built first (recommended), it pays down a chunk of the JIT's eventual cost — another reason to sequence A before B rather than treating them as independent. Worth noting in PLAN.md so the JIT phase later inherits, rather than re-derives, the safepoint machinery.

- **The below-`sp` UAF deserves its own pre-emptive ticket regardless of which track is chosen.** It is documented as latent-but-unreachable today, but it is the seam that *both* tracks reactivate (multiple parked stacks for A; native frames for B). Fixing the invariant standalone — make every safepoint guarantee no below-`sp` from-space pointer survives, and extend `POLYML_GC_AUDIT` to scan `[0, sp)` — would be valuable cleanup even if neither big track ships soon.

Relevant files for an implementer: `crates/polyml-runtime/src/interpreter/mod.rs` (GC root walk `gc()` 651-932; safepoint poll site 1386; per-thread state fields 300-362; mutex fakes ~2610), `crates/polyml-runtime/src/rts.rs` (thread/mutex/condvar stubs 848-1061, fork 1825, process-global statics 1154/1274), `crates/polyml-jit/src/lib.rs` (call-convention wall + `cca_all_tail_equivalent` 240-283), `vendor/polyml/libpolyml/processes.cpp` (the port target: giant-lock 878, `MakeRootRequest` 912, `WaitInfinite` release-around-block 511-540), and `PLAN.md` Phase 2.3/2.4 (225-251).
