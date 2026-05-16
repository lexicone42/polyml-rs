# polyml-rs

A Rust rewrite of PolyML's runtime, with a Cranelift-based codegen
backend replacing the existing native code generators, and a
longer-term goal of architecture-portable heap images.

**Status**: Stage 2 just begun. See [`PLAN.md`](PLAN.md) for the
phased roadmap and [`notes/`](notes/) for the Stage-1 architecture
research that backs it.

## What this is

- A Rust implementation of [PolyML's](https://github.com/polyml/polyml)
  C++ runtime (`libpolyml/`).
- A Cranelift backend that replaces PolyML's hand-written X86 and
  ARM64 codegen, plugging into the existing
  `mlsource/MLCompiler/CodeTree/GENCODE.sig` seam (single function:
  `gencodeLambda`).
- A new architecture-portable heap-image format (`bicimage`) that
  ships compiler IR rather than native machine code, allowing one
  image to load on x86_64, aarch64, or riscv64.

## What this is not

- A new SML compiler frontend. PolyML's compiler is itself in SML; we
  use it as-is via the existing codegen seam.
- A drop-in replacement (yet). Stage 2 deliverables build incrementally
  toward feature parity with upstream PolyML on Linux x86_64.

## License

Dual licensed under **MIT** OR **Apache-2.0** at your option. See
[LICENSE-MIT](LICENSE-MIT) and [LICENSE-APACHE](LICENSE-APACHE).

The bootstrap heap image (`bootstrap64.txt`) is a separate sibling
crate (`polyml-bootstrap`) and remains under PolyML's **LGPL-2.1**.
The runtime in this repo does not contain LGPL-derived code.

## Build

Requires Rust 1.95 (pinned via `rust-toolchain.toml`).

```sh
cargo check     # workspace check
cargo build     # build the `poly` binary
cargo test      # run tests (none yet)
```

## Layout

| Crate | Status | Role |
|---|---|---|
| `polyml-runtime` | scaffold | GC, heap, scheduler, FFI, exceptions |
| `polyml-image`   | scaffold | pexport reader/writer; later `bicimage` |
| `polyml-bin`     | scaffold | the `poly` binary entry point |
| *future*: `polyml-interpreter` | not yet | bytecode interpreter (Phase 2.1) |
| *future*: `polyml-codegen-cl`  | not yet | Cranelift backend (Phase 2.2) |
| *future*: `polyml-bootstrap` (sibling repo) | not yet | LGPL-2.1 sidecar |

## Plan

See [`PLAN.md`](PLAN.md). Stage-2 is roughly one engineer-year for
single-arch x86_64 production-quality, growing to two arches plus
macOS by phase 2.6.
