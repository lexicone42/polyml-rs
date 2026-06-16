# polyml-rs

A Rust reimplementation of [Poly/ML](https://github.com/polyml/polyml)'s
bytecode interpreter, runtime, image loader, and garbage collector — with an
experimental Cranelift JIT and a longer-term goal of **architecture-portable
heap images** (save an image on one machine, load and run it on a different
architecture, no recompilation).

> Lineage: this is the "RuPaulyML" idea — fork Poly/ML, rewrite the C++ runtime
> in Rust, swap in Cranelift codegen, and chase portable heap images — built out
> for real.

**Status:** runs on **x86-64 Linux**. The runtime faithfully executes real
Poly/ML: it boots the upstream bootstrap image, self-compiles the entire 7-stage
compiler chain, and hosts a working SML REPL. Faithfulness is continuously
checked against upstream Poly/ML (a differential oracle, byte-identical on
~1,300 cases) and stress-tested by running HOL4's full prover stack and a
from-scratch Isabelle/Pure number-theory development. The headline goal —
architecture-portable images — is **not done yet**; see [Roadmap](#roadmap).

## What works today

Everything below runs through the Rust runtime, no upstream `poly` involved.
The examples assume you've obtained `vendor/polyml/` (it's git-ignored) — see
[`docs/REPRODUCING.md`](docs/REPRODUCING.md).

**1. Boot the real Poly/ML bootstrap image and run SML.**
```sh
cargo build --release -p polyml-bin
echo "fun fact 0 = 1 | fact n = n * fact (n-1); fact 10;" \
  | ./target/release/poly run vendor/polyml/polyexport
# > val it = 3628800: int
```

**2. Self-compile Poly/ML end to end.** Piping the bootstrap driver through our
interpreter runs all seven stages of Poly/ML's self-compilation
(`Stage1.sml` → `MLCompiler` → … → `Writing object code`) and writes a real
`polyexport` image — which then loads back as a working REPL. The whole compiler
bootstraps *on our runtime*.

**3. Run an SML script one-shot.**
```sh
./target/release/poly run vendor/polyml/bootstrap/bootstrap64.txt --use script.sml
```

**4. Inspect / disassemble / diff images.** `poly inspect`, `poly disasm`,
`poly diff` for image forensics.

**5. (Experimental) JIT.** `poly run --jit <image>` translates trusted bytecode
to Cranelift IR and dispatches via a JIT cache. It runs the full pipeline
correctly (bootstrap, the 7-stage chain, HOL4) — but is currently a
*correctness testbed*, roughly perf-neutral with the tuned interpreter, not yet
a speed win. See `CLAUDE.md` for the honest performance analysis.

## Faithfulness, not just "it boots"

The interesting claim about a reimplementation is that it's *correct*. The
evidence here is unusually strong:

- **Differential oracle.** `tools/diff-oracle.sh` runs the same SML through real
  upstream Poly/ML and through `poly run` and diffs the results — ~1,300
  deterministic cases across the Basis and compiler-stress programs. The
  interpreter is faithful on all of them (and even reproduces a latent *upstream*
  stage-0 compiler bug byte-for-byte — the strongest faithfulness statement
  available). See [`docs/differential-oracle-2026-06-09.md`](docs/differential-oracle-2026-06-09.md).
- **HOL4 runs on it.** The HOL4 theorem prover's kernel, term/type parser,
  tactic layer, simplifier, `MESON`/`METIS`, the Pelletier benchmark suite
  (46/47, at parity with upstream HOL4's MESON), the `Datatype` package, and
  verified programs (insertion/merge/quicksort, Euclid's GCD, a verified
  compiler, BSTs) all run on the Rust interpreter.
- **Isabelle/Pure runs on it.** Isabelle's logical core loads and *proves*. On
  top of it we machine-checked a self-derived elementary number-theory tower —
  Euclid's theorem, √2 irrational, the Fundamental Theorem of Arithmetic,
  Fermat's little theorem, gcd/Bézout, the Chinese Remainder Theorem, and
  **Wilson's theorem** — every step verified by the real LCF kernel.

These double as the most demanding regression tests imaginable for the runtime.

## What's not done yet

- **Architecture-portable images** (the headline goal). The foundation is in
  place — execution is via arch-independent bytecode — but the portable
  `bicimage` format isn't implemented and we have only ever run on x86-64. The
  cross-arch demo (save on x86-64, load on aarch64) is the next milestone.
- **A second architecture** (aarch64 / riscv64) — not yet targeted.
- **macOS / Windows** — Linux only.
- **Concurrency & interrupts** — the interpreter is single-threaded; Poly/ML's
  thread/`Future` machinery loads lazily but isn't scheduled concurrently.
- **JIT as a speedup** — it's correct but not yet faster than the interpreter.

## Layout

| Crate | Role |
|---|---|
| [`polyml-runtime`](crates/polyml-runtime) | the bytecode interpreter, runtime system (RTS) calls, exceptions, and the copying GC — the Rust port of `vendor/polyml/libpolyml/` |
| [`polyml-image`](crates/polyml-image)   | heap-image formats: the `pexport` reader/writer today, the portable `bicimage` format to come |
| [`polyml-jit`](crates/polyml-jit)       | the Cranelift-backed JIT (bytecode → Cranelift IR) |
| [`polyml-bin`](crates/polyml-bin)       | the `poly` binary (`run` / `inspect` / `disasm` / `diff`) |

Upstream Poly/ML is obtained read-only under `vendor/polyml/` (git-ignored; see
[`docs/REPRODUCING.md`](docs/REPRODUCING.md)); the interpreter cross-references
the C++ it ports (`libpolyml/bytecode.cpp`) by line.

## Build & test

Requires the pinned toolchain (Rust 1.95, via `rust-toolchain.toml`).

```sh
cargo build --release -p polyml-bin     # build the `poly` binary
tools/regression.sh fast                # build + always-on tests (~2 min, no checkpoints)
tools/regression.sh full                # + the headline HOL4/Isabelle workloads (~50 min)
```

`regression.sh fast` is the always-on gate (runtime + JIT unit tests, the
interp-vs-JIT differentials, the simple bootstrap). The headline prover demos
are `#[ignore]` tests that need warm checkpoints; see
[`docs/REPRODUCING.md`](docs/REPRODUCING.md) for how to build them and run the
HOL4 / Isabelle / oracle demos.

## Roadmap

The original Stage-2 plan is in [`PLAN.md`](PLAN.md). In short:

- **Done:** the bytecode interpreter, the RTS, the copying GC, pexport load/save,
  the experimental Cranelift JIT, and an extensive faithfulness harness.
- **Next (the dream): portable `bicimage` + a second architecture.** Implement
  an image format that ships bytecode + a portable object graph (no native code,
  explicit word-size/endianness/tagging), cross-compile `poly` to aarch64, and
  demonstrate a cross-arch image load. This is what makes the project novel.
- **Later:** concurrency/interrupts, macOS, riscv64, and maturing the JIT into a
  genuine speedup.

## License

Dual-licensed under **MIT** ([LICENSE-MIT](LICENSE-MIT)) **OR**
**Apache-2.0** ([LICENSE-APACHE](LICENSE-APACHE)), at your option.

`vendor/polyml/` (including the bootstrap heap image) is upstream Poly/ML under
**LGPL-2.1** and is not covered by the above; the Rust runtime in `crates/`
contains no LGPL-derived code. HOL4 and Isabelle sources used by the demo tests
are obtained separately (not vendored) and carry their own licenses.
