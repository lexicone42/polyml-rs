# Benchmarks — faithfulness + honest wall-clock vs upstream Poly/ML

This is a **non-proof** performance and faithfulness corpus built from the
classic SML/NJ benchmark set (fib, tak, queens, sieve, sort, mmult, mandelbrot,
life, deriv, cpstak, nbody, ray). It answers two questions:

1. **Faithfulness at scale** — does `polyml-rs` compute *byte-identical* results
   to real upstream Poly/ML on non-trivial programs, at both small and large
   inputs? (Yes, on all 12.)
2. **How fast are we, honestly** — the first apples-to-apples wall-clock/CPU
   comparison against upstream Poly/ML's own **interpreter** (the fair fight)
   and its **native code generator** (the "how far from native" reference).

The headline is deliberately un-flattering: on dispatch-bound loops we are
**~4–7× slower than upstream's C++ bytecode interpreter** and **~25–70× slower
than upstream native codegen**; the gap narrows to **~1.5–2.3×** (interp) on
allocation/GC-bound workloads. Our raw interpreter throughput is fine in
absolute terms (~145 M bytecode steps/s here) — the residual is upstream's more
mature interpreter and, above it, real native compilation.

## The corpus

| benchmark | flavour | kernel | checksum |
| --- | --- | --- | --- |
| `fib` | non-tail integer recursion | naive Fibonacci | value |
| `tak` | recursion / call overhead | Takeuchi function | value |
| `cpstak` | closures / CPS | Takeuchi in continuation-passing style | value |
| `queens` | backtracking search | count N-queens solutions | value |
| `sieve` | array mutation, tight int loop | Sieve of Eratosthenes | (#primes, Σprimes mod p) |
| `sort` | list allocation + GC | bottom-up merge sort of an LCG list | len : sorted? : hash : permutation? |
| `mmult` | nested loop + array indexing | dense integer matrix multiply (flat `Array`) | Σ C mod p |
| `mandelbrot` | floating-point inner loop | escape-time render (integer escape-count sum) | Σ iterations |
| `life` | list/GC + comparison sort | Conway's Life from an r-pentomino | population : coord-hash |
| `deriv` | small-object allocation | symbolic differentiation (Gabriel `deriv`) | result node count |
| `nbody` | float + `sqrt`, O(n²) | direct-sum gravitational N-body, leapfrog | Σ quantized positions |
| `ray` | float + `sqrt` + branching | 4-sphere Lambertian ray tracer | Σ pixel intensity |

**Dropped from the classic set, and why:**

- **barnes-hut** — the canonical benchmark is the O(n log n) *octree* N-body. A
  faithful octree port is large and easy to get subtly wrong; the octree is a
  spatial *approximation*, not the physics. We substitute the direct O(n²) sum
  (`nbody`), which exercises the identical profile that matters here — a
  floating-point `sqrt`/mul/div inner loop — with an obviously-correct kernel,
  and name it honestly.
- **boyer** / **knuth-bendix** — the real Gabriel `boyer` (tautology checker)
  and `knuth-bendix` (completion) carry large SML/NJ-specific rule/lemma tables;
  reproducing them faithfully from the original is error-prone, and a
  subtly-wrong port would *still* agree engine-vs-engine (the differential test
  compares the two engines, not a reference answer) — buying nothing while
  risking a silent bug. Their flavour — symbolic term rewriting + heavy small-
  object allocation — is already represented by `deriv` and `life`.
- **nucleic / simple** — large real-heavy floating-point programs; `nbody`,
  `ray`, and `mandelbrot` already cover the FP profile without the porting risk.

### One source, two uses

Each `tools/diff-corpus/bench_<name>.sml` is **self-contained** and drives itself
from environment variables, so the *same file* serves both the faithfulness
sweep and the timing harness (single source of truth):

- **No env vars → faithfulness mode.** Runs a SMALL default size and prints
  `@@<bench_name>=<checksum>`. `tools/diff-oracle.sh --dir tools/diff-corpus`
  globs these automatically, so `tools/regression.sh full` compares each against
  upstream byte-for-byte.
- **`BENCH_TIME=1` → timing mode.** Runs `BENCH_REPS` reps at size `BENCH_N`
  under an in-SML CPU `Timer`, printing `@@time_ms` / `@@reps` / `@@n` /
  `@@checksum`.

The algorithm "heads" live in `tools/bench-src/<name>.sml`; the shared driver
footer is `tools/bench-footer.sml`; `tools/gen-bench-corpus.sh` concatenates them
into the committed self-contained corpus files (regenerate after any edit).

### Determinism (so the checksum is comparable)

- Fixed input sizes; any randomness is a constant-seeded LCG (values kept
  < 2³¹ and products < 2⁶², so integer arithmetic stays on the tagged-fixnum
  fast path on both engines — no accidental big-int divergence).
- No wall-clock, PID, or environment enters a *computed* result.
- Floating-point benchmarks use **only** `+ - * / sqrt` and rounding — all IEEE
  **correctly-rounded**, hence **bit-identical** across engines (verified: a hash
  over 200 000 `sqrt` results and a 100 000-term div/mul chain match upstream
  exactly) — and reduce to **integer** checksums, so real-to-string formatting
  can never cause a spurious diff.

## Deliverable 1 — faithfulness result

All 12 benchmarks **AGREE byte-for-byte** with upstream Poly/ML, at both the
small (sweep) size and the large (timing) size:

- Small sizes, via `tools/diff-oracle.sh` (upstream native oracle): **12/12 agree.**
- The full corpus sweep `tools/diff-oracle.sh --dir tools/diff-corpus`
  (372 cases incl. the 12 new ones): **370/372 agree**; the only 2 divergences
  are the pre-existing, documented `intinf.sml` / `intinf_bitwise_order.sml`
  `andb`/`orb` case — a *latent upstream stage-0 compiler bug* we reproduce
  byte-for-byte (see `docs/correctness-and-safety.md`), unrelated to these
  benchmarks.
- Large sizes: `tools/bench.sh` cross-checks `@@checksum` across all three
  engines every run — **all `ok`** (see the table's `cksum` column). No
  divergence surfaced at scale.

**No faithfulness bug found.** (This corpus was built partly to hunt for one; it
came up clean.)

## Deliverable 2 — the performance table

Metric = **in-SML CPU time** (`Timer.startCPUTimer`), which starts *after* the
benchmark function is defined, so it excludes process start-up, image load, and
driver compilation on **all three** engines. Each cell is the **minimum of 3**
process runs. Sizes are calibrated so "ours" runs ~1–3 s/rep.

Machine: this dev box (x86-64 Linux); single core. Reproduce with
`tools/bench.sh` (see commands below). Absolute ms vary with hardware; the
**ratios** are the portable signal.

```
benchmark           N    ours_ms    interp_ms    native_ms  vs_interp   vs_native    cksum
-------------------------------------------------------------------------------------------------
fib                35       2538          507           48       5.01       52.88       ok
tak                 9       1641          301           23       5.45       71.35       ok
cpstak              9       2595          587           88       4.42       29.49       ok
queens             11       1154          212           20       5.44       57.70       ok
sieve         5000000       2491          475           73       5.24       34.12       ok
sort           300000       2029         1413          638       1.44        3.18       ok
mmult             150       1255          669           18       1.88       69.72       ok
mandelbrot        400       2582          531           69       4.86       37.42       ok
life              250       1048          464           60       2.26       17.47       ok
deriv            2600       1318          195           30       6.76       43.93       ok
nbody             350       1708          298           46       5.73       37.13       ok
ray               450       1336          216           53       6.19       25.21       ok
```

- `ours` = `./target/release/poly run /tmp/basis_loaded` (our Rust interpreter).
- `interp` = `/tmp/polybuild-interp/poly` — upstream Poly/ML built with the
  **bytecode interpreter** backend. This shares our bytecode backend class and is
  the **fair, apples-to-apples comparison**: same SML source, same Poly/ML
  compiler front-end, interpreter vs interpreter (C++ vs Rust).
- `native` = `/tmp/polybuild/poly` — upstream Poly/ML with its **native code
  generator**. The "how far from native" reference.
- `vs_interp` = `ours / interp`, `vs_native` = `ours / native` (>1 ⇒ we are slower).

**Summary (geometric mean over the 12):** `vs_interp = 4.13×`, `vs_native = 32.3×`.

### Wall clock + peak RSS (isolated per process)

CPU-ms above excludes start-up; end-to-end **wall** (incl. image load + driver
compile) and **peak RSS** for a compute-bound (`fib`) and a GC-bound (`sort`)
case:

```
== fib N=35 ==
  ours               wall= 3.43s  peakRSS= 1689 MB
  upstream-interp    wall= 0.54s  peakRSS=   23 MB
  upstream-native    wall= 0.08s  peakRSS=   27 MB
== sort N=300000 ==
  ours               wall= 2.91s  peakRSS= 1689 MB
  upstream-interp    wall= 0.99s  peakRSS=  120 MB
  upstream-native    wall= 0.44s  peakRSS=   94 MB
```

Two honest notes on those numbers:

- **RSS**: our default is a **fixed 1.6 GB heap reserved up front** (200 M words ×
  8 B; see `POLYML_HEAP_BYTES` in `CLAUDE.md`), so peak RSS is ~1.69 GB
  regardless of workload, whereas upstream grows on demand (23–120 MB). This is a
  **tunable reservation, not intrinsic per-workload memory**: with
  `POLYML_HEAP_BYTES=256M`, `fib` peak RSS drops to ~345 MB (wall unchanged).
- **Wall vs CPU**: our wall is a bit above CPU-ms because of the checkpoint image
  load + driver compile on each launch; upstream's start-up is smaller.

## Interpretation — what's fast, what's slow, and why

**We are consistently ~4–7× slower than upstream's *interpreter* on dispatch-
bound code** (fib, tak, cpstak, queens, sieve, mandelbrot, deriv, nbody, ray:
4.4–6.8×). These kernels are dominated by the bytecode dispatch loop — tight
integer/float ops and calls with little heap traffic. Our raw throughput here is
~145 M bytecode steps/s (fib 35 = 362 M steps in 2.50 s CPU), *above* the ~92 M
steps/s figure quoted elsewhere in the tree — so the interpreter is fast in
absolute terms. The gap to upstream is that upstream's C++ interpreter is a very
mature threaded-dispatch loop; end-to-end it does the same work ~5× faster.
(This is an *end-to-end* number — same SML source through each engine's own
compiler + interpreter. We did not fully decompose "fewer bytecode instructions"
vs "faster per-instruction dispatch"; both plausibly contribute.)

**The gap collapses to ~1.5–2.3× on allocation/GC-bound code** (`sort` 1.44×,
`mmult` 1.88×, `life` 2.26×). When the bottleneck is the memory system rather
than the dispatch loop, our copying (Cheney) GC and allocator are within a small
factor of upstream's — the interpreter-dispatch penalty is amortized away. `sort`
is the closest we come, and notably it is also only **3.2× off native** (vs
25–70× on the arithmetic loops), because a merge sort's cost is list allocation +
GC, which native codegen can't accelerate much either.

**Native codegen is 25–70× faster than us on the arithmetic loops** and this is
expected and unremarkable: it is compiled machine code vs a bytecode
interpreter. The interpreter's value proposition was never raw speed — it is
faithfulness, memory safety, and portability (see the README). The relevant fair
comparison is `vs_interp`, and there the honest number is **~4×**.

**Design context (why the interpreter, and where the ~4× lives).** `polyml-rs`
is a threaded bytecode interpreter with a copying GC. The `--jit` and
`--whole-region` Cranelift paths were built and measured; both are correctness
testbeds, not speedups on real workloads (the tight threaded loop wins — see
`CLAUDE.md` "Performance & JIT"). The remaining interpreter headroom vs upstream
is in the dispatch loop itself (opcode fusion, fewer bounds/tag checks on the hot
INDIRECT/JUMP families); the profile hooks to chase it are `poly run --profile`.

## Reproduce

```sh
# build our interpreter
cargo build --release -p polyml-bin

# (optional) build the two upstream oracles the table compares against
tools/build-oracle.sh          # -> /tmp/polybuild/poly        (native codegen)
tools/build-oracle.sh interp   # -> /tmp/polybuild-interp/poly (bytecode interp)

# regenerate the self-contained corpus from tools/bench-src/*.sml + footer
tools/gen-bench-corpus.sh

# faithfulness sweep (small sizes; part of `tools/regression.sh full`)
tools/diff-oracle.sh --dir tools/diff-corpus     # bench_* included automatically

# the performance table (min of 3 runs; all engines auto-detected)
tools/bench.sh                                   # all 12, default large sizes
tools/bench.sh fib sort mmult                    # a subset
REPEAT=5 BENCH_SIZE_fib=37 tools/bench.sh fib     # tune reps / a single size
```

Missing oracles are handled gracefully: `bench.sh` prints `NA` for an absent
engine's column and still reports `ours`; `diff-oracle.sh` needs at least the
native oracle + the `/tmp/basis_loaded` checkpoint.
