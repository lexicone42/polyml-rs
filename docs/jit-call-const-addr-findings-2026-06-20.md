# CALL_CONST_ADDR JIT SEGV — root-caused + the deep-dive's "interaction" framing REFUTED (2026-06-20)

JIT Phase 1 (task #115, ultracode wf_ebde3819-88c: recon×3 → root-cause → fix →
measure), re-verified by hand. The 2026-06-18 deep-dive
(docs/jit-feasibility-2026-06-18.md) called the CALL_CONST_ADDR (CCA, 0x57/0x58/0x17/
0x18) install SEGV a "multi-fn INTERACTION bug (curated installs are correct)". That is
**factually wrong**; this is the correction + the definitive root cause.

## TL;DR

- **NOT an interaction bug.** Install index 0 **alone** SEGVs (`JIT_INSTALL_LIMIT=1`);
  indices 1–5 alone are clean; `JIT_INSTALL_SKIP=0` (install all *other* 2060) still
  SEGVs. It is a **CLASS of individually-broken per-function** CCA translations —
  trust-all just installs many at once. (Confirmed live: `JIT_TRUST_CALL_CONST_ADDR=1`
  → 2061 installs, exit 139 on the simple bootstrap.)
- **Root cause = a MID-FUNCTION OVER-POP**, structurally identical to the already-
  documented CALL_LOCAL_B blocker. The CCA translation pops `n_args` SSA values off the
  compile-time stack and pushes one result (translate.rs:774–813). But upstream
  CALL_CLOSURE (vendor/polyml/libpolyml/bytecode.cpp:411–414) pops **only the closure**
  — the args physically PERSIST on the stack across the call, and the callee's
  `RETURN_N` (bytecode.cpp:454–460, `sp += returnCount`) collapses them. The SML
  compiler then addresses the **surviving** slots (a `STACK_CONTAINER_B` ref, fillers)
  by absolute LOCAL/CONTAINER offset *after* the call. The over-pop eats those slots, so
  a later `INDIRECT_CONTAINER_B` / `LOCAL_K` dereferences a stale `iconst(tag 0)` (=0x1)
  as a heap pointer → SIGSEGV at `si_addr=0x1`.
- **Proven on install index 0** (head `78 81 2b 0e 02 3b 2a 57 6f 50 29 74 00 …`,
  `JIT_INSTALL_DUMP_IDX=0`): `0e 02` STACK_CONTAINER_B count=2 pushes [filler, filler,
  container_ref]; `57 6f` CALL_CONST_ADDR8_0 pops n_args=4 → eats the LOCAL_1 dup, the
  CONST_0 tag0, the container_ref, and a filler; `74 00` INDIRECT_CONTAINER_B two ops
  later pops the now-stale tag0 (`iconst 1`) and `load(1)` → SEGV. `JIT_TRAMP_DUMP_ARGS`
  confirms the 4 raw args = `[stack_addr 0x7fff…d60, 0x1, stack_addr 0x7fff…d60, 0x1]` —
  the container ref + tagged-0 fillers consumed as call args.

## Refuted hypotheses (so the next engineer doesn't chase them)

- **"multi-fn interaction"** (deep-dive): refuted — single install SEGVs.
- **"stale baked address after GC"** (commit 598f312 / CLAUDE.md): refuted —
  **zero GC cycles** fire before the single-install crash, and the bad value is a
  *compile-time constant* (`iconst 1`), not a moved heap pointer. (The runtime-load
  change in translate.rs:786 fixed a *separate, real* GC-stale-VALUE issue and is
  ORTHOGONAL to this over-pop; the comment claiming it "unblocks CCA" was corrected.)
- **"wrong guessed arity"** (a recon proximate guess): refuted —
  `JIT_TRAMP_VERIFY_ARITY` reports ZERO mismatch (n_args matches the closure header).
  The arity is right; the compile-time `Vec<Value>` is still desynced because the SML
  stack KEEPS the args while the JIT removes them.
- **"no-container CCAs are safe"** (a tempting narrower gate): refuted live —
  `JIT_CCA_NO_CONTAINER=1` installs 1661 and still SEGVs (exit 139, ~500K–1M steps into
  the basis load): a no-container CCA still desyncs via a post-call absolute-offset
  LOCAL read. Left in as a default-off diagnostic so the refutation is re-runnable.

## The fix that landed: a correctness-fenced install gate (outcome: root-caused-no-fix)

`cca_all_tail_equivalent` (crates/polyml-jit/src/lib.rs) — a boundary-aware disasm walk
that admits a CCA function ONLY when **every** CCA in it is in **tail-equivalent**
position (next op is `RETURN_1/2/3/B/W`, or the `LOCAL_0;RESET_R_1;RETURN_1` cleanup
idiom — exactly the gate CALL_CLOSURE already uses, translate.rs:606–625). In tail
position the over-pop is harmless: nothing reads the corrupted slots below the result;
the very next op returns it. `None` on ESCAPE/unknown/truncation → treated as not-safe
(conservative). Fenced by `tests/call_const_addr_differential.rs` (5 tests: tail-
position CCA installs + JIT==interp returns 107; the container-over-push index-0 shape
+ a mid-function-result-consumed shape are REJECTED; no-CCA vacuously safe).

**The catch: the tail-equivalent safe subset is EMPTY on the bootstrap image.** Of 1302
functions containing a CCA, `JIT_CCA_STATS=1` reports **0** tail-equivalent (1301
`Some(false)`, 1 `None`). Functions are HOT precisely *because* they consume the call
result mid-function — the exact shape the over-pop poisons. So the gate adds **0**
installs here. It is correct + **forward-compatible** (auto-admits any future tail-
position CCA on a different image) + replaces an unjustified blanket skip + corrects the
docs — but it is honestly a "correct gate, empty safe subset" result, **not** a coverage
win.

## Measurement vs the bicimage >1.5× gate

3 interleaved rounds, basis load, wall-clock (all Tagged(0), deterministic step counts):

| config              | median wall | vs interp | installs | cache-hit | basis steps    |
|---------------------|-------------|-----------|----------|-----------|----------------|
| interp (no --jit)   | 17.127 s    | 1.000×    | —        | —         | 1,783,981,044  |
| --jit legacy (767)  | 17.043 s    | 1.005×    | 767      | 14.7%     | 1,654,720,773  |
| --jit (823, CCA gate)| 16.862 s   | **1.016×**| 823      | 15.4%     | 1,609,040,163  |

(Step counts are NOT comparable interp-vs-JIT — JIT-executed work isn't tallied as
interp steps; wall-clock is the only honest cross-config metric.) `--jit` is **+1.6%**
over the interpreter — but **all of that is Phase 0** (the boundary-aware filter that
installed the #1 hot function); the CCA gate contributed **exactly 0** (823 byte-
identical to the pre-gate baseline, reproduced across 2 determinism runs + 1 forced-GC
run at `POLYML_GC_THRESHOLD=5`).

**Verdict: CCA-as-install-gate is a dead end for coverage on this image, and the
bicimage >1.5× gate is no closer.** The ~22% of hot steps locked behind CCA cannot be
unlocked by *any* install gate — the hot functions are mid-function-consume by
construction. The trampoline JIT has plateaued at single-digit-% over a ~95–104M-steps/
sec interpreter.

## The ONE real next lever: Tier 2 / whole-region compilation

Model upstream's **non-popping** convention for mid-function CCA (and the structurally
identical CALL_LOCAL_B, which the same fix unblocks): keep the call args PERSISTENT
across the call, have the trampoline return the callee's runtime RETURN count, and
reconcile the JIT compile-time stack to `depth = depth − returnCount + 1` against the
persisted-args layout — with post-call LOCAL/CONTAINER reads reloading from a spilled
physical stack at interpreter-consistent offsets. This is route 1 in
docs/jit-feasibility-2026-06-18.md (keep nested calls in native code), a substantial
re-architecture out of scope for a correctness-gated incremental change. Gate any of it
behind a **forced-GC differential** + a full basis-load Tagged(0). If a whole-region
rewrite is not on the table, the trampoline JIT's honest value is a **correctness
testbed** (an excellent differential harness + a real but modest +1.6% speedup), not a
throughput win — and bicimage stays gated, while `pexport` already ships portable.
