# Reproducing the demos

The always-on tests (`tools/regression.sh fast`) need nothing but the Rust
toolchain. The *headline* demos — booting the real Poly/ML, the differential
oracle, and the HOL4 / Isabelle proof workloads — need data that is **not
committed** (`/vendor` is git-ignored) plus warm checkpoints built under `/tmp`.
This page is how to obtain them.

## 0. Toolchain

```sh
rustup show            # installs the pinned toolchain from rust-toolchain.toml (Rust 1.96)
cargo build --release -p polyml-bin
```

## 1. Vendor Poly/ML (required for everything below)

The runtime loads the upstream bootstrap image and the interpreter
cross-references upstream's C++. Place a checkout of
[Poly/ML](https://github.com/polyml/polyml) at `vendor/polyml/`:

```sh
git clone https://github.com/polyml/polyml vendor/polyml
git -C vendor/polyml checkout c27c2953ef   # last-validated upstream commit; newer may work
```

You need the bootstrap heap image `vendor/polyml/bootstrap/bootstrap64.txt`
(shipped in the upstream tree). A self-bootstrapped `vendor/polyml/polyexport`
(a full basis image) is what the REPL examples in the README load; produce it by
running the 7-stage chain:

```sh
cd vendor/polyml && ../../target/release/poly run --max-steps 200000000000 \
    bootstrap/bootstrap64.txt < bootstrap/Stage1.sml     # ~5 min, writes ./polyexport
```

`vendor/polyml` stays read-only; it is upstream **LGPL-2.1** and is deliberately
not part of this repo's MIT/Apache source. (One caveat: the Isabelle demos apply
tracked patches from `patches/` to the vendored source — applied idempotently by
the build scripts; see [`patches/README.md`](../patches/README.md).)

## 2. The differential oracle (faithfulness vs upstream)

```sh
tools/build-oracle.sh             # builds upstream poly at /tmp/polybuild/poly (native codegen)
tools/build-oracle.sh interp      # and /tmp/polybuild-interp/poly (bytecode backend)
tools/diff-oracle.sh --dir tools/diff-corpus    # ~1300 cases, both engines, diffed
```

Any divergence is a faithfulness bug in our port. See
[`correctness-and-safety.md`](correctness-and-safety.md) for the methodology, the
verdict, and the one (latent *upstream*) divergence we reproduce byte-for-byte.

## 3. HOL4 demos

Obtain [HOL4](https://github.com/HOL-Theorem-Prover/HOL) at `vendor/hol4/`
(git-ignored), then build the warm checkpoints and run the tests:

```sh
git clone https://github.com/HOL-Theorem-Prover/HOL vendor/hol4
git -C vendor/hol4 checkout 286dbfccc4     # last-validated upstream commit
tools/build-hol4-checkpoints.sh datatype   # full ladder: basis -> kernel -> ... -> datatype
                                           # (chains its own prerequisites; bare `all` stops
                                           #  at the core prover stack, before arithmetic)
cargo test --release -p polyml-bin --test hol4_metis    -- --ignored --nocapture
cargo test --release -p polyml-bin --test hol4_pelletier -- --ignored --nocapture
# ...and the other hol4_*.rs tests
```

The checkpoints persist via `tools/persist-ckpts.sh` (symlinks into
`/var/tmp/polyml-rs`), so they survive reboots without rebuilding.

## 4. Isabelle/Pure demos (the number-theory tower)

Obtain a blobless sparse checkout of Isabelle's `src/Pure`:

```sh
git clone --filter=blob:none --no-checkout \
  https://github.com/isabelle-prover/mirror-isabelle vendor/isabelle/mirror-isabelle
( cd vendor/isabelle/mirror-isabelle && git sparse-checkout set src/Pure \
  && git checkout 454217c3cd )              # last-validated upstream commit
tools/intflip-bootstrap.sh                 # one-time prerequisite: the arbitrary-precision-int
                                           # bootstrap image (/tmp/arbint_image); applies the
                                           # tracked patches/polyml-*.patch to vendor/polyml
tools/build-isabelle-pure.sh               # loads logical Pure, exports /tmp/isabelle_pure (~2s reload)
```

Then run any of the proof tests, e.g. the landmark theorems:

```sh
cargo test --release -p polyml-bin --test isabelle_wilson  -- --ignored --nocapture   # Wilson's theorem
cargo test --release -p polyml-bin --test isabelle_fta     -- --ignored --nocapture   # FTA
cargo test --release -p polyml-bin --test isabelle_flt     -- --ignored --nocapture   # Fermat's little theorem
# ...the full set is wired into `tools/regression.sh full`
```

## 5. Everything at once

Once `vendor/*` and the checkpoints exist, the full fence runs the whole lot:

```sh
tools/regression.sh full      # build + always-on tests + every headline #[ignore] workload (~50 min)
```

It builds any missing checkpoints first, then runs the bootstrap chain, all HOL4
and Isabelle workloads, the int-flip basis, and (if the oracle is built) the
differential corpus.
