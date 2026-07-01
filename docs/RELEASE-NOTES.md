# polyml-rs v0.1.0

A Rust reimplementation of [Poly/ML](https://github.com/polyml/polyml)'s
bytecode interpreter, runtime, image loader, and copying GC. It boots the real
Poly/ML bootstrap image, self-compiles the entire 7-stage SML compiler chain,
hosts HOL4 and Isabelle/Pure, and runs the same heap image byte-identically
across five 64-bit architectures and both endiannesses.

## Try it in one command (no build, no toolchain)

```sh
# from a clone:
tools/try-polyml-rs.sh           # downloads the binary + image, drops into an SML REPL
tools/try-polyml-rs.sh --demo    # runs the cross-arch portability probe
```

Or by hand:

```sh
# grab poly-<your-triple> and polyexport.bic from this release, then:
echo "fun fact 0 = 1 | fact n = n * fact (n-1); fact 10;" | ./poly run polyexport.bic
# > val it = 3628800: int
```

## Assets

| Asset | What |
|---|---|
| `poly-x86_64-unknown-linux-gnu` | the `poly` runtime, x86-64 Linux |
| `poly-aarch64-apple-darwin` | the `poly` runtime, arm64 macOS (from the nightly macOS job) |
| `polyexport.bic` | the self-bootstrapped SML REPL image, portable binary `bicimage` format (~½ the pexport size, endian-neutral) |
| `SHA256SUMS` | checksums |

The same `polyexport.bic` runs on every listed target and reports the **same
step count** — that is the portability claim, made runnable.

## Highlights

- **Faithful:** byte-identical to upstream Poly/ML on a ~1,300-case differential
  oracle (it even reproduces a latent upstream stage-0 bug byte-for-byte).
- **Real theorem provers:** HOL4's full prover stack and a from-scratch
  Isabelle/Pure number-theory tower (Quadratic Reciprocity, Bertrand's
  Postulate, Lagrange's four-square theorem, …) — all machine-checked by the
  real LCF kernel, with a machine-enforced soundness audit.
- **Memory-safe untrusted mode:** `poly run --untrusted <image>` validates every
  image-controlled pointer follow (see `SECURITY.md`).
- **Portable images:** one image byte, five arches, both endiannesses.

## Attribution

`polyexport.bic` embeds compiled code derived from the upstream Poly/ML basis
library, which is **LGPL-2.1** (https://github.com/polyml/polyml). The Rust
runtime in `crates/` is dual MIT/Apache-2.0 and contains no LGPL-derived code.
See [`docs/REPRODUCING.md`](REPRODUCING.md) to rebuild the image yourself.
