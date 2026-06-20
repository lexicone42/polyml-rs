# Upstream PolyML test-suite run — findings (2026-06-17)

Ran upstream PolyML's own validation corpus (`vendor/polyml/Tests/`: 212
`Succeed` + 83 `Fail`) through **our** interpreter (on `/tmp/basis_loaded`) and
diffed against upstream (`/tmp/polybuild/poly` native + `/tmp/polybuild-interp/poly`
interp). Ultracode workflow wf_fb708f67-8a4 (recon → 8 run batches → triage).

**Result: ~265/291 pass** (≈188/212 Succeed, ≈81/83 Fail; ~4 Succeed not reached).
Of 26 non-passes: **10 unsupported features**, **2 stage-0 / older-compiler
artifacts**, and **16 genuine faithfulness bugs across 8 root causes**. The
interpreter is *highly faithful* on PolyML's own suite — but the suite found real
bugs the number-theory proofs and the Basis diff-corpus never could (they exercise
valid code on the bytecode path; this suite hits error cases, the RTS emulation
path, GC semantics, OS, and the compiler under load).

## Genuine bugs

| # | Test | Sev | Status | Bug |
|---|------|-----|--------|-----|
| 1 | Test101 | HIGH | **FIXED (dcdbbd4)** | `PolySubtractArbitrary` RTS path returned `arg2−arg1` (the negation). `arb_binop` computes `op(arg2,arg1)` — fine for commutative add/mult, wrong for subtraction. Fixed by swapping args. The inline opcode `arb_sub_pair` was already correct, so the diff-corpus (opcode path) missed it. Regression fence: `tools/diff-corpus/intinf_rts_arith.sml`. |
| 2 | Test120 | MED | open | Weak refs (`Weak.weak`) are **not cleared** after `PolyML.fullGC()` — our Cheney copying GC keeps weak-referenced objects alive / never nulls the weak cell. `!w = SOME _` where upstream gives `NONE`. |
| 3 | Test121 | MED | open | `IEEEReal.setRoundingMode` is a **silent no-op**: `getRoundingMode()` doesn't return the set mode and FP arithmetic doesn't honour it. Worst of both — neither raises `Fail` nor implements. |
| 4 | Test174 | MED | open | `Real32.fromLarge` **ignores its rounding-mode argument** and always rounds to nearest (directed-rounding cases wrong). Likely same root as #3. |
| 5 | Test190 | MED | open | `OS.Process.terminate` **does not terminate** — the RTS call returns instead of exiting, so the unreachable `raise Fail "never"` in `basis/OS.sml` fires. |
| 6 | Test196 | LOW | open | `OS.FileSys.fullPath ""` returns `""` instead of the cwd (empty path not treated as `.`). |
| 7 | Test132 / 205 / 206 / 207 / 210 | LOW (faithfulness win) | RECHARACTERIZED 2026-06-19 | **Compiler-vintage cluster (was mis-framed as a "native-stack" bug).** ROOT-CAUSED (docs/native-stack-findings-2026-06-19.md, wf_20383fd0-a94): this is NOT a native-stack overflow. It is the interpreter's **fixed-size MANAGED PolyWord stack** (1M-word `Box`) returning a clean `Err(StackOverflow)` — observed `Halted with error: stack overflow`, **exit 4, after ~2.5M steps, byte-identical across runs** (the determinism proves it is the managed stack, not native; the dispatch is a flat loop, GC iterative, export worklist-iterative — no native recursion ∝ ML depth). Decisive: Test205 OVERFLOWS on stage-0 `basis_loaded` but **PASSES (`Tagged(0)`) on the stage-7 `polyexport`** we self-bootstrapped → gated by **compiler vintage, not interpreter capability** — the same lineage/faithfulness pattern as andb/orb. The 5 `Succeed/` tests document compiler bugs upstream later fixed; we reproduce the stage-0 compiler's unbounded recursion FAITHFULLY. The honest residual (separate): the fixed managed stack overflows legit deep-but-bounded programs — mitigable today via `POLY_ML_STACK_WORDS=<n>`; proper fix = a GROWABLE managed stack (banked, hands-on, see the findings doc). The earlier "native Rust stack / 0 steps / exit 134/139 / RUST_MIN_STACK" framing is factually wrong. |

## Unsupported features (upstream depends on them; not faithfulness bugs)
BSD sockets (×6), Foreign/FFI (×2), real multithreading, `Thread.Thread`
`MaximumMLStack`, and `PolyML.Compiler.languageExtensions` (checkpoint vintage).
These are genuine gaps but out of scope for "interpreter faithfulness."

## Stage-0 / version artifacts (not our bug)
2 `Fail` tests behave per an older compiler version baked into the stage-0
bootstrap image (the same lineage class as the resolved `andb`/`orb` finding,
task #72).

## Verdict
The interpreter is faithful on the bulk of PolyML's own suite; the one HIGH bug
(arbitrary-precision subtraction) is fixed. The remaining open bugs are MEDIUM/LOW
and cluster into: **weak-ref GC semantics**, **FP rounding modes**, **a couple of
OS shims**, and **the compiler-under-load native-stack cluster** (the most
interesting / highest-value remaining). Full triage: the workflow result for
wf_fb708f67-8a4.

Worth banking as a permanent harness: a `tools/run-upstream-tests.sh` that runs
the Succeed/Fail suite and reports the pass count, fenced (allowing the known
unsupported/artifact set) — so faithfulness regressions surface automatically.
