# polyml-rs

A Rust reimplementation of [Poly/ML](https://github.com/polyml/polyml)'s
bytecode interpreter, runtime, image loader, and garbage collector — with an
experimental Cranelift JIT and a longer-term goal of **architecture-portable
heap images** (save an image on one machine, load and run it on a different
architecture, no recompilation).

> Lineage: this is the "RuPaulyML" idea — fork Poly/ML, rewrite the C++ runtime
> in Rust, swap in Cranelift codegen, and chase portable heap images — built out
> for real.

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
self-bootstrapped** (see #2).

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

```sh
./target/release/poly run vendor/polyml/bootstrap/bootstrap64.txt --use script.sml
```

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
[`docs/jit-feasibility-2026-06-18.md`](docs/jit-feasibility-2026-06-18.md) and
`CLAUDE.md` for the honest performance analysis.

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
  See [`docs/differential-oracle-2026-06-09.md`](docs/differential-oracle-2026-06-09.md).
- **Poly/ML's own test corpus.** We run upstream's `Tests/` suite (212 Succeed +
  83 Fail programs) through both engines — this is how the `PolySubtractArbitrary`
  negation bug was caught and fixed (it lived in the RTS path the diff-corpus
  missed). See [`docs/upstream-testsuite-findings-2026-06-17.md`](docs/upstream-testsuite-findings-2026-06-17.md).
- **Hunted for soundness from every angle.** Arithmetic/structure/program fuzz,
  loader fuzz (found + fixed 2 memory-safety bugs on untrusted images), a GC
  soak, the interp-vs-JIT differential (1,201 fn×args cases, zero real JIT bugs),
  and a full static audit of all 449 `unsafe` blocks. The findings (including the
  honest open issues) are in `docs/`.

These also double as the most demanding regression tests imaginable for the
runtime.

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
*proves*. On top of it, we built up elementary number theory from first
principles and machine-checked the landmark theorems by the **real LCF kernel**
(0-hypothesis, axiom-audited, with soundness probes that confirm the kernel
rejects false variants; the only classical assumption is excluded middle).

What is proved (each a fenced regression test under `crates/polyml-bin/tests/isabelle_*.rs`):

| Theorem | File |
|---|---|
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

…and more (56 Isabelle proof tests in all).

### One open theorem (stated honestly)

**Lagrange's four-square theorem** (`∀n. ∃a b c d. n = a²+b²+c²+d²`) is **NOT yet
proved** — it is the only open partial in the tower, and it is genuinely
research-grade. A lot is banked and the wall is now broken, not just mapped:
Euler's four-square identity (multiplicativity), the multiplicative-closure
reduction, the descent setup, and — the prior fleets' declared wall — the
**Euler divide-by-m² is proven end-to-end for one of 8 sign-leaves**, with the
clever-ℕ "signed conjugate star" path confirmed viable (no new abstraction
needed). The remaining work (the other 7 sign-leaves + the descent iteration) is
precisely scoped as ~2 focused proof runs. See
[`docs/four-square-progress-2026-06-17.md`](docs/four-square-progress-2026-06-17.md)
and `isabelle_four_square.rs`.

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
- **Windows** — not yet validated (the RTS/filesystem layer is Unix-oriented). The
  endianness gap is **closed**: s390x (big-endian) runs byte-identically (above).
- **Concurrency & interrupts** — the interpreter is single-threaded; Poly/ML's
  thread/`Future` machinery loads lazily but isn't scheduled concurrently.
- **JIT as a big speedup** — it's correct and a *modest* (~2%) win; whole-region
  native compilation (the real road to native speed) is future work.
- **Lagrange's four-square theorem** — the one open partial in the Isabelle tower
  (above).

---

## Layout

| Crate | Role |
|---|---|
| [`polyml-runtime`](crates/polyml-runtime) | the bytecode interpreter, runtime system (RTS) calls, exceptions, and the copying GC — the Rust port of `vendor/polyml/libpolyml/` |
| [`polyml-image`](crates/polyml-image)   | heap-image formats: the `pexport` text reader/writer and the compact binary `bicimage` format (endian-neutral, ~½ the size) |
| [`polyml-jit`](crates/polyml-jit)       | the Cranelift-backed JIT (bytecode → Cranelift IR) |
| [`polyml-bin`](crates/polyml-bin)       | the `poly` binary (`run` / `inspect` / `disasm` / `diff` / `bic`) + the HOL4 / Isabelle proof tests |

Upstream Poly/ML is obtained read-only under `vendor/polyml/` (git-ignored; see
[`docs/REPRODUCING.md`](docs/REPRODUCING.md)); the interpreter cross-references
the C++ it ports (`libpolyml/bytecode.cpp`) by line.

---

## Build & test

Requires the pinned toolchain (Rust 1.96, via `rust-toolchain.toml`).

```sh
cargo build --release -p polyml-bin     # build the `poly` binary
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
- **Next:** the larger subsystems — concurrency/interrupts, Windows, maturing the
  JIT into a genuine speedup — and closing Lagrange's four-square theorem.

---

## License

Dual-licensed under **MIT** ([LICENSE-MIT](LICENSE-MIT)) **OR**
**Apache-2.0** ([LICENSE-APACHE](LICENSE-APACHE)), at your option.

`vendor/polyml/` (including the bootstrap heap image) is upstream Poly/ML under
**LGPL-2.1** and is not covered by the above; the Rust runtime in `crates/`
contains no LGPL-derived code. HOL4 and Isabelle sources used by the demo tests
are obtained separately (not vendored) and carry their own licenses.
