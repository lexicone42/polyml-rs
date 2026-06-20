# "Native-stack-overflow cluster" (#96) — root-caused + RECHARACTERIZED (2026-06-19)

ultracode wf_20383fd0-a94 (recon → fix → verify), re-confirmed by hand. The
foundation audit's framing of this cluster was **factually wrong**; this is the
correction.

## TL;DR — it is NOT a native overflow, and it is largely a FAITHFULNESS WIN

The upstream `Tests/Succeed/Test{132,205,206,207,210}.ML` "fail" on our runtime, but:

1. **It is the interpreter's own fixed-size MANAGED PolyWord stack overflowing**, not
   the native (Rust/OS) stack. The dispatch is a flat loop (`run_until_impl`), GC is
   iterative Cheney, export is worklist-iterative — there is **no** native recursion
   ∝ ML depth (the only native-stack-∝-depth path is the JIT trampoline, capped by
   `MAX_JIT_DEPTH`). `push()`/`STACK_SIZE16` return `Err(InterpError::StackOverflow)`
   from the fixed `Box<[PolyWord]>` of 1024*1024 words.
2. **Observed reality** (refutes the audit's "native Rust stack overflow, ~0 bytecode
   steps, exit 134/139"): a clean `Halted with error: stack overflow`, **exit 4**,
   after **2,555,553 steps** — and **byte-identical across runs**. That determinism is
   itself the proof it is the *managed* stack: a native overflow would SIGSEGV (139)
   and vary with frame layout.
3. **Gated by COMPILER VINTAGE, not interpreter capability** (the decisive check):
   - `poly run /tmp/basis_loaded < Test205.ML` (stage-0 Poly/ML 5.9 bootstrap compiler)
     → overflow @ 2,555,553 steps, exit 4.
   - `poly run vendor/polyml/polyexport < Test205.ML` (the stage-7 compiler we
     self-bootstrapped through OUR runtime) → **`val f = fn: int -> int`, `Tagged(0)`,
     exit 0, 547,758 steps. PASSES.**
   The 5 `Succeed/` tests document COMPILER bugs upstream later FIXED; the stage-0
   compiler recurses unboundedly (its own bug) and we reproduce it FAITHFULLY, while
   our self-compiled stage-7 compiler passes. **Same lineage/faithfulness pattern as
   the andb/orb stage-0 finding** (docs/differential-oracle-2026-06-09.md).

So this cluster is not a polyml-rs capability gap — it is faithful reproduction of a
fixed-in-later-versions stage-0 compiler bug. The worker-thread big-native-stack
stopgap does **not** apply (wrong layer) and was correctly not committed.

## The HONEST residual (separate, real): the fixed managed stack

Independent of the vintage cluster, our managed PolyWord stack is a **fixed** 1M-word
`Box` (`interpreter/mod.rs:295`, allocated at `:411/:456`). A legitimately
deep-but-BOUNDED program (e.g. a depth-60000 nested expression that upstream compiles
fine) overflows it. Mitigation that EXISTS today: `POLY_ML_STACK_WORDS=<n>` (16M words
made a depth-60000 case complete `Tagged(0)`) — but a fixed ceiling cannot save the
genuinely-unbounded stage-0 cluster (correctly — that recursion is unbounded).

## Banked for hands-on: a GROWABLE managed stack

Mirror upstream `HandleStackOverflow → CheckAndGrowStack`
(vendor/polyml/libpolyml/bytecode.cpp:480/546/557, interpreter.cpp:129):
1. Replace the fixed `stack: Box<[PolyWord]>` with a reallocatable buffer; grow in a
   `#[cold]` branch off the `STACK_SIZE16` (`mod.rs:~1480`) and `push` (`mod.rs:1226`)
   checks.
2. On grow: allocate larger, copy live `[sp..len)` to the HIGH end, and **fix up every
   absolute stack index** by the grow delta — `sp`, `handler_sp` (`mod.rs:419/464`),
   and the in-stack handler-frame links.
3. Honor a `MaximumMLStack` ceiling so genuinely-unbounded recursion raises a
   **catchable** SML stack-overflow/Interrupt packet instead of an `Err` halt.
Invasive + hot-path-adjacent (the grow branch must be `#[cold]`) → hands-on only, not
auto-applied. This closes the deep-but-bounded residual AND makes the overflow a
catchable SML exception (more faithful), without changing the stage-0 cluster outcome.

## Doc corrections this finding triggers

- `docs/upstream-testsuite-findings-2026-06-17.md` (#96 row): re-triage — NOT a native
  stack bug; mechanism = fixed managed PolyWord stack + stage-0 compiler vintage;
  PASSES on stage-7 polyexport.
- The "native Rust stack overflow, ~0 bytecode steps, exit 134/139" framing in the
  foundation audit + the auto-memory is factually wrong (observed: clean Err halt,
  millions of steps, exit 4) — corrected here.
