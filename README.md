# polyml-rs

A Rust reimplementation of [Poly/ML](https://github.com/polyml/polyml)'s
bytecode interpreter, runtime, image loader, and garbage collector — with an
experimental Cranelift JIT and a longer-term goal of **architecture-portable
heap images** (save an image on one machine, load and run it on a different
architecture, no recompilation).

> Lineage & credit: the "RuPaulyML" idea — fork Poly/ML, rewrite the C++ runtime
> in Rust, swap in Cranelift codegen, and chase portable heap images — comes from
> [a tweet by @ember_arlynx](https://x.com/ember_arlynx/status/2055420264536498545).
> This project is that idea, built out for real.

**Status:** runs on **x86-64 Linux**, **arm64 macOS**, **riscv64**, and two
**big-endian** arches (**s390x**, **ppc64**) — the non-x86 ones under qemu. The runtime faithfully
executes real Poly/ML: it boots the upstream bootstrap image, self-compiles the
entire 7-stage compiler chain, and hosts a working SML REPL. Faithfulness is
continuously checked against upstream Poly/ML (a differential oracle, byte-identical
on ~1,300+ cases) and stress-tested by running HOL4's full prover stack and a
from-scratch Isabelle/Pure number-theory development that machine-checks dozens
of landmark theorems by genuine LCF kernel inference.

The headline *novelty* goal — architecture-portable heap images — is **partly
demonstrated**: an image our runtime builds on x86-64 Linux executes on Apple
Silicon (arm64 macOS) with a **byte-identical step count** — cross-architecture
**and** cross-OS, on real hardware, no recompilation (runbook:
[`docs/apple-silicon-cross-arch-demo.md`](docs/apple-silicon-cross-arch-demo.md)).
The same x86-64-built image also runs **byte-identically on riscv64 and on two
big-endian arches (s390x, ppc64)** under qemu — `1,110,805` steps → `Tagged(0)` on
**all five**, across both endiannesses. So image portability holds across
architecture *and* byte order (for same-word-size 64-bit targets — the
cross-*word-size* case is characterized separately below). There's also a compact *binary* image format (`bicimage`, ~½ the size,
loads + runs identically, endian-neutral on the wire). Crossing *word size*
(64↔32) carries data but not word-size-specific compiled code (see [Roadmap](#roadmap)).

---

## Try it in one command

No build, no toolchain — download a prebuilt `poly` + the portable REPL image
and start an SML session (from a [release](https://github.com/lexicone42/polyml-rs/releases)):

```sh
tools/try-polyml-rs.sh          # → an SML REPL
tools/try-polyml-rs.sh --demo   # → the cross-arch portability probe (same step count everywhere)
```

Or by hand: grab `poly-<your-triple>` and `polyexport.bic` from the release, then
`echo "1+1;" | ./poly run polyexport.bic`. Building from source is below.

---

## What works today

Everything below runs through the Rust runtime — no upstream `poly` involved.
The examples assume you've obtained `vendor/polyml/` (it's git-ignored) — see
[`docs/REPRODUCING.md`](docs/REPRODUCING.md).

### 1. Boot the real Poly/ML bootstrap image and run SML

```sh
cargo build --release -p polyml-bin
echo "fun fact 0 = 1 | fact n = n * fact (n-1); fact 10;" \
  | ./target/release/poly run vendor/polyml/polyexport
# Poly/ML 5.9.2 Release (Git version polyml-rs)
# > val fact = fn: int -> int
# > val it = 3628800: int
```

That's a real SML REPL — Hindley–Milner type inference, recursive and
higher-order functions, the lot — running an image **our runtime
self-bootstrapped** (see #2). NB `vendor/polyml/polyexport` is *produced by*
example #2 — run that first (~5 min), or point `run` at
`vendor/polyml/bootstrap/bootstrap64.txt` for the bare stage-0 compiler (no
basis loaded, so no REPL niceties).

### 2. Self-compile Poly/ML end to end

Piping the bootstrap driver through our interpreter runs all seven stages of
Poly/ML's self-compilation (`Stage1.sml` → builds `MLCompiler` → re-loads the
basis on the freshly compiled compiler → … → `Writing object code`) and writes a
real `polyexport` heap image — which then loads back as the working REPL above.
The whole Poly/ML compiler bootstraps *on our runtime*, from the same source the
upstream build uses, in ~5 minutes.

```sh
cd vendor/polyml
../../target/release/poly run --max-steps 200000000000 \
    bootstrap/bootstrap64.txt < bootstrap/Stage1.sml
# ... ~28 billion bytecode steps, 7 stages ...
# ******Writing object code******
# Result: Tagged(0) — clean return
```

### 3. Run an SML script one-shot

`--use FILE` targets the **stage-0** image (it provides `Bootstrap.use`), with
the script's directory auto-added as an include path:

```sh
./target/release/poly run vendor/polyml/bootstrap/bootstrap64.txt --use script.sml
```

To run a script against the full-basis REPL instead, pipe it on stdin:
`./target/release/poly run vendor/polyml/polyexport < script.sml`.

### 4. Inspect / disassemble / diff images

`poly inspect`, `poly disasm`, and `poly diff` for heap-image forensics and
differential debugging.

### 5. (Experimental) Cranelift JIT

`poly run --jit <image>` translates trusted bytecode to Cranelift IR and
dispatches via a JIT cache. It runs the full pipeline correctly (bootstrap, the
7-stage chain, all HOL4 tests). After the Phase-0 install/trampoline work it is
**~2% faster than the tuned interpreter on the basis load** — a modest win; the
JIT's primary value today is as a correctness testbed (a differential harness
that runs each function in both JIT and interpreter and compares). See
`CLAUDE.md` for the honest performance analysis.

The JIT (and its Cranelift dependency) is an **optional cargo feature** (default
on). `cargo build -p polyml-bin --no-default-features` produces an
**interpreter-only** `poly` — **74% smaller** (≈8.9 MB vs ≈34.6 MB), Cranelift-free,
~8× faster to compile, byte-identical execution — which also **cross-compiles
natively to big-endian s390x** (no Cranelift build-script workaround needed).

### 6. Run an untrusted image safely

`poly run --untrusted <image>` is a memory-safe mode for *foreign* images: every
dangerous pointer-follow validates (space-membership + object-header sanity +
per-op shape) before the unsafe use, so a deliberately-malicious image gets a clean
halt instead of undefined behaviour. The default (trusted) path is byte-identical
and exactly as fast — every check sits behind the untrusted flag. A committed
malicious-image corpus (`tools/malicious-corpus/`) + a deref-surface lint
(`tools/lint-image-deref.py`) fence it.

Scope note: `--untrusted` is *memory* safety, **not a sandbox** — the image still
runs with your user's ambient authority (filesystem, environment, stdout). See
[`SECURITY.md`](SECURITY.md) for the threat model.

---

## Faithfulness, not just "it boots"

The interesting claim about a reimplementation is that it's *correct*. The
evidence here is unusually strong — and it was earned by finding real bugs.

- **Differential oracle vs real upstream Poly/ML.** `tools/diff-oracle.sh` runs
  the same SML through real upstream Poly/ML (built two ways: native codegen and
  the bytecode interpreter) and through `poly run`, then diffs the results —
  ~1,300+ deterministic cases across the Basis, compiler-stress programs, and
  seeded LCG fuzz drivers (~16K random arithmetic cases). The interpreter is
  faithful on all of them, and even reproduces a latent *upstream* stage-0
  compiler bug byte-for-byte (the strongest faithfulness statement available).
- **Poly/ML's own test corpus.** We run upstream's `Tests/` suite (212 Succeed +
  83 Fail programs) through both engines — this is how the `PolySubtractArbitrary`
  negation bug was caught and fixed (it lived in the RTS path the diff-corpus
  missed).
- **Hunted for soundness from every angle.** Arithmetic/structure/program fuzz,
  loader fuzz (found + fixed 2 memory-safety bugs on untrusted images), a GC
  soak, the interp-vs-JIT differential (1,201 fn×args cases, zero real JIT bugs),
  and a full static audit of all 449 `unsafe` blocks. The methods and findings
  (including the honest open issues) are written up in
  [`docs/correctness-and-safety.md`](docs/correctness-and-safety.md).

These also double as the most demanding regression tests imaginable for the
runtime.

### How fast is it? (honest numbers)

A 12-program classic-SML benchmark corpus (`tools/diff-corpus/bench_*.sml`,
timed by `tools/bench.sh`) gives the first wall-clock comparison against upstream
Poly/ML. All 12 compute **byte-identical results** to upstream at both small and
large inputs (so they double as a real-program faithfulness net). On CPU time,
our interpreter is a geometric-mean **~4× slower than upstream's own bytecode
interpreter** (range 1.4–6.8×) and **~32× slower than upstream native codegen** —
but the interpreter gap narrows to **1.4–2.3× on allocation/GC-bound workloads**
(merge sort, matrix multiply, Life), where the copying GC, not dispatch,
dominates. Raw throughput is ~145M bytecode steps/s; the residual is upstream's
more mature C++ dispatch loop and, above it, real native compilation. Full
methodology + the measured table: [`docs/benchmarks.md`](docs/benchmarks.md).

---

## It runs real theorem provers

The runtime is faithful enough that two large, real-world SML theorem provers run
on it — and prove real mathematics by genuine kernel inference.

### HOL4 — the full prover stack

The HOL4 theorem prover's kernel, term/type parser, `bool` theory, tactic layer,
simplifier, the `MESON` and `METIS` automated provers, and the `Datatype` package
all run on the Rust interpreter. Highlights (each an `#[ignore]` regression test,
all fenced by `tools/regression.sh full`):

- **Pelletier benchmark suite — 46/47 by `MESON_TAC`** (P47, Schubert's
  Steamroller, is the expected `MESON` failure, matching upstream HOL4's own
  selftest — i.e. parity with upstream).
- **`METIS_TAC`** resolution + paramodulation (AC chains, equality congruence).
- **Verified programs** built and *run* on the interpreter: insertion sort, merge
  sort, quicksort (each proven to permute + sort), Euclid's GCD, a binary search
  tree with its ordering invariant, and a **verified compiler** (the Bahr–Hutton
  expression compiler, `compile_correct` proven 0-hyp).

### Isabelle/Pure — a self-derived number-theory tower

Isabelle's logical core (`Pure`) loads — 261/285 files; the remaining 24 are the
Scala/PIDE frontend, which genuinely needs Scala/sockets, not logic — and
*proves*. On top of it, we built up elementary number theory **from first
principles** and machine-checked the landmark theorems by the **real LCF kernel**.
The proofs are original ML-on-`Pure` (constructed via `Thm.*`/`Drule.*`/tactics),
**not lifted** from Isabelle's `HOL-Number_Theory` or the AFP (only `Pure` itself is
vendored, so there is nothing upstream to copy).

Every theorem test machine-enforces a soundness audit
([`tests/isabelle_support/sound_audit.sml`](crates/polyml-bin/tests/isabelle_support/sound_audit.sml)):
the proved theorem is **0-hypothesis** (`hyps_of = []`, `extra_shyps = []`),
**oracle-free** (`Thm_Deps.all_oracles = []` — no `Skip_Proof`/oracle escape, even
under `Proofterm.proofs := 0`), and **every axiom of its theory is a member of a
known-conservative allowlist** (the object-logic ND rules, Peano, and the
fresh-constant defining/recursion equations) with **exactly one classical axiom,
excluded middle** — plus α-equivalence + negative probes that confirm the kernel
*rejects* false variants. A committed negative test smuggles axioms under innocuous
names + a `Skip_Proof` oracle and confirms the audit **fails**, so the gate has
teeth (it's a membership *allowlist*, not a name blacklist).

*The one honest boundary:* the audit certifies every axiom is a recognized
*conservative* name and that EM is the sole classical assumption, but the
**conservativity of each axiom and the consistency of the whole foundation is a
mathematical (human) argument, not machine-checked** — `Pure`, like any foundational
kernel, does not prove its own consistency. (This is the same footing as any
Isabelle/HOL development: you trust the kernel + the axioms; here the axioms are the
enumerated conservative base + excluded middle, and nothing else.) These claims have
been put through an independent read-only adversarial audit (cheat-scan + live axiom/
oracle enumeration + provenance + cold reproduction).

What is proved (each a fenced regression test under `crates/polyml-bin/tests/isabelle_*.rs`):

| Theorem | File |
|---|---|
| **The Quadratic Reciprocity Law** `(p/q)(q/p) = (−1)^(((p−1)/2)((q−1)/2))` — Gauss's *theorema aureum*, via Gauss's lemma → the Eisenstein bridge → the lattice-point count | `isabelle_quadratic_reciprocity.rs` |
| **Bertrand's postulate** `∀n. 0<n ⟹ ∃ prime p. n < p ≤ 2n` — unconditional, the full Erdős proof (central-binomial bounds → the analytic threshold) | `isabelle_bertrand.rs` |
| **Wilson's theorem** `(p−1)! ≡ −1 (mod p)`, its **converse**, and the full **iff** primality criterion | `isabelle_wilson{,_converse,_iff}.rs` |
| **Fermat's little theorem** `a^p ≡ a (mod p)` | `isabelle_flt.rs` |
| **Euler's theorem** `a^φ(n) ≡ 1 (mod n)` + **Euler's criterion** (±1 dichotomy) | `isabelle_euler{,_criterion}.rs` |
| **Chinese Remainder Theorem** (existence + uniqueness) | `isabelle_crt.rs` |
| **Euclid's theorem** (infinitude of primes) + **infinitely many primes ≡ 1 and ≡ 3 (mod 4)** | `isabelle_euclid.rs`, `isabelle_primes_{1,3}mod4.rs` |
| **Fundamental Theorem of Arithmetic** (existence + uniqueness) | `isabelle_fta{,_unique}.rs` |
| **√2 is irrational** (infinite descent) | `isabelle_sqrt2.rs` |
| **Fermat's two-square theorem** — the FULL characterization (n is a sum of two squares ⟺ every prime ≡ 3 mod 4 divides it to an even power) | `isabelle_twosquare{,_full}.rs` |
| **The Euclid–Euler theorem** — the FULL characterization of even perfect numbers (n is even perfect ⟺ n = 2^(p−1)(2^p−1) with 2^p−1 prime) | `isabelle_euclid_euler.rs` |
| **Zeckendorf's theorem** (unique non-consecutive Fibonacci representation) | `isabelle_zeckendorf.rs` |
| **Pythagorean triples** parametrization | `isabelle_pyth.rs` |
| **Fibonacci identities** (sum, addition law, Cassini) | `isabelle_fibonacci.rs` |
| **The binomial theorem**, Vandermonde, the central binomial identity, Nicomachus / Faulhaber closed forms, Gauss summation | `isabelle_binom_thm.rs`, `isabelle_combinatorics.rs`, `isabelle_central_binomial.rs`, `isabelle_summation_forms.rs` |
| gcd/Bézout, modular inverse, Euclid's lemma, the division theorem, the multiplicative group mod p, ℕ as a commutative semiring + linear order, divisibility | `isabelle_gcd.rs`, `isabelle_euclid_lemma.rs`, `isabelle_division.rs`, `isabelle_mult_group.rs`, … |

…and more (59 Isabelle proof tests in all).

### Three capstones: Quadratic Reciprocity, Bertrand's Postulate, Lagrange's four squares

The tower has no open partials, and it is crowned by three of the hardest results
in elementary number theory — each a 0-hypothesis theorem by genuine LCF kernel
inference, axiom-audited (only excluded middle), on the self-bootstrapped Rust
runtime:

- **The Quadratic Reciprocity Law** — Gauss's *theorema aureum*, proved via Gauss's
  lemma → the Eisenstein lattice bridge → the lattice-point count.
- **Bertrand's Postulate** — `∀n>0. ∃ prime p. n < p ≤ 2n`, unconditional, the full
  Erdős proof (central-binomial bounds → the `4^(2n/3)` refinement → the analytic
  threshold contradiction, closed by a fixed-exponent poly-vs-exp induction; ~224
  billion bytecode steps to re-verify).
- **Lagrange's four-square theorem** — `∀n. ∃a b c d. n = a²+b²+c²+d²`, via the
  classical Euler descent (the four-square identity + the signed divide-by-`m²`
  leaves → strict descent → strong induction to every prime). Details:
  [`docs/four-square-progress-2026-06-17.md`](docs/four-square-progress-2026-06-17.md).

So **every landmark theorem listed above is machine-checked on a Rust
reimplementation of Poly/ML, by the real Isabelle/Pure kernel — no open partials,
no fabricated axioms.**

---

## What's not done yet

- **Cross-*word-size* images (64↔32)** — investigated and characterized (the
  same-word-size cross-arch above is the achievable headline; this is the harder
  case). The codebase now *builds and runs on 32-bit* (`i686`), and the loader
  *reconstructs a 64-bit image's data graph* on a 32-bit heap (boxing tagged ints
  that overflow the smaller tag). But **64-bit-compiled *code* can't run faithfully
  on 32-bit** — the compiler's own bytecode bakes in 64-bit word-size constants
  (the `2⁵⁶−1` header mask, the `−2⁶²` tag bound), so a 64-bit image diverges on a
  32-bit host. This is upstream PolyML's documented limitation ("no correctness
  guarantee across word sizes without recompilation"); cross-word-size carries
  *data*, not compiled code. Details + proof in
  [`docs/tier-b-portable-images-design.md`](docs/tier-b-portable-images-design.md).
- **OS / Basis-library breadth** — the RTS implements what the compiler, REPL,
  HOL4, and Isabelle workloads exercise (files, arithmetic, strings, time,
  argv/env, ...), plus a growing set of *real* OS surface: **`OS.Process.system`**
  (real `sh -c`), **`Date`** local-time (real `localtime`/`strftime`), IO errors
  as real `SysErr`, and **TCP/UDP sockets** over `std::net`/libc — an SML echo
  server round-trips bytes through the kernel (`tests/sockets.rs`). All
  differential-verified byte-for-byte against upstream. Still stubbed (they raise
  a catchable `SysErr`, never fake success — fenced by `tests/rts_defang.rs`): the
  C FFI, `Signal.signal` *delivery* (Ctrl-C itself works), SaveState, the `Posix`
  structure, and IPv6 / DNS on the socket side.
- **Windows** — not yet validated (the RTS/filesystem layer is Unix-oriented). The
  endianness gap is **closed**: s390x (big-endian) runs byte-identically (above).
- **Full concurrency** — real OS threads (`Thread.fork` / `Thread.Mutex` /
  `ConditionVar` over a shared heap) work behind **`POLY_REAL_THREADS=1`** (default
  OFF): a giant-lock + safepoint stop-the-world GC model — *concurrency, not
  parallelism* (one mutator runs bytecode at a time, matching upstream's
  interpreter-mode semantics). A 2-thread mutex demo runs end-to-end (counter →
  200000), and — since blocking socket syscalls (`accept`/`connect`/`select`)
  now **release the giant lock** across their wait — an **in-process concurrent
  socket server + client** round-trips a payload between two SML threads
  (`concurrency_sockets`), which would deadlock if a blocked thread held the
  lock. `ConditionVar` timed wait and `Thread.numProcessors` are real too.
  Default OFF keeps the bootstrap/REPL/HOL4/Isabelle paths byte-identical
  single-threaded. Still open: a *preemptive* scheduler (beyond the cooperative
  safepoint yield), releasing the lock across `recv`/`send`/stdin blocking too
  (needs GC forwarding of RTS-local heap refs), and breaking the giant lock for
  true parallelism. **Interrupts are done**: Ctrl-C (SIGINT) raises the SML
  `Interrupt` exception, so a runaway loop is interruptible instead of hard-killed.
- **JIT as a big speedup** — it's correct and a *modest* (~2%) win. Whole-region
  native compilation was built end-to-end and measured: **byte-identical across the
  full 27.7-billion-step self-bootstrap (a deep soundness result) but a net
  *slowdown* (~0.87×)** — the compiler's real hot path falls outside the compilable
  subset, so the tight threaded interpreter wins. The JIT's honest value is a
  correctness testbed, not speed.

---

## Layout

| Crate | Role |
|---|---|
| [`polyml-runtime`](crates/polyml-runtime) | the bytecode interpreter, runtime system (RTS) calls, exceptions, and the copying GC — the Rust port of `vendor/polyml/libpolyml/` |
| [`polyml-image`](crates/polyml-image)   | heap-image formats: the `pexport` text reader/writer and the compact binary `bicimage` format (endian-neutral, ~½ the size) |
| [`polyml-jit`](crates/polyml-jit)       | the Cranelift-backed JIT (bytecode → Cranelift IR) — an **optional** (default-on) feature; drop it for interpreter-only builds |
| [`polyml-bin`](crates/polyml-bin)       | the `poly` binary (`run` / `load` / `inspect` / `disasm` / `diff` / `bic`) + the HOL4 / Isabelle proof tests |

Upstream Poly/ML is obtained read-only under `vendor/polyml/` (git-ignored; see
[`docs/REPRODUCING.md`](docs/REPRODUCING.md)); the interpreter cross-references
the C++ it ports (`libpolyml/bytecode.cpp`) by line.

---

## Build & test

Requires the pinned toolchain (Rust 1.96, via `rust-toolchain.toml`).

```sh
cargo build --release -p polyml-bin                       # the `poly` binary (with JIT)
cargo build --release -p polyml-bin --no-default-features # interpreter-only (no Cranelift, 74% smaller)
tools/regression.sh fast                # build + always-on tests (~2 min, no checkpoints)
tools/regression.sh full                # + the headline HOL4/Isabelle workloads (~50 min)
```

`regression.sh fast` is the always-on gate (runtime + JIT unit tests, the
interp-vs-JIT differentials, a tiny-heap GC fence, the simple bootstrap). The
headline prover demos are `#[ignore]` tests that need warm checkpoints; see
[`docs/REPRODUCING.md`](docs/REPRODUCING.md) for how to build them and run the
HOL4 / Isabelle / oracle demos.

---

## Roadmap

The original staged plan is in [`PLAN.md`](PLAN.md). In short:

- **Done:** the bytecode interpreter, the RTS, the copying GC, pexport load/save,
  the **compact binary `bicimage` format** (endian-neutral, ~½ the text size,
  loads + runs identically), the experimental Cranelift JIT, an extensive
  faithfulness harness, the HOL4 / Isabelle prover demos, and **cross-arch +
  cross-endian image portability across five 64-bit architectures** — x86-64 Linux,
  arm64 macOS (real hardware), riscv64, s390x (big-endian) and ppc64 (big-endian),
  the non-x86 ones under qemu, all running the same image byte-identically.
- **Characterized:** cross-*word-size* (64↔32) — the data/object-graph
  reconstructs (the loader boxes oversized ints), but 64-bit-compiled *code* can't
  run faithfully on 32-bit (its bytecode bakes in 64-bit word-size constants);
  this matches upstream's documented limitation. So cross-word-size carries data,
  not compiled code; a true 64↔32 execution story needs recompilation.
- **Settled this cycle:** real OS threads behind `POLY_REAL_THREADS=1` (giant-lock +
  safepoint-GC concurrency); interrupts (SIGINT → SML `Interrupt`); the
  memory-safety residual (the `--untrusted` safe mode); the JIT made an optional
  feature (interpreter-only / big-endian-native builds); and the
  **whole-region-JIT-as-speedup question — answered "no"**: it was built end-to-end,
  proven byte-identical across the 27.7-billion-step self-bootstrap, but measured a
  net slowdown (the tight threaded interpreter wins). The number-theory tower is
  complete.
- **Next:** the remaining larger subsystems — a *preemptive* thread scheduler (beyond
  the cooperative safepoint yield), Windows, and the cross-*word-size* recompilation
  story.

---

## License

Dual-licensed under **MIT** ([LICENSE-MIT](LICENSE-MIT)) **OR**
**Apache-2.0** ([LICENSE-APACHE](LICENSE-APACHE)), at your option.

`vendor/polyml/` (including the bootstrap heap image) is upstream Poly/ML under
**LGPL-2.1** and is not covered by the above; the Rust runtime in `crates/`
contains no LGPL-derived code. HOL4 and Isabelle sources used by the demo tests
are obtained separately (not vendored) and carry their own licenses.
