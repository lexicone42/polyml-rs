# Lagrange's four-square theorem — proof artifacts

This directory holds the genuine, machine-checked proof of **Lagrange's
four-square theorem**

> ∀ n. ∃ a b c d. n = a² + b² + c² + d²

in Isabelle/Pure, run on the polyml-rs interpreter (the SML compiler our own
Rust runtime self-bootstraps). The final theorem is a 0-hypothesis theorem by
genuine LCF kernel inference; the only classical assumption is excluded middle
(`ex_middle`), and it adds **no new axioms** over the conservative
number-theory base shared by the rest of the tower.

It is the last theorem the Isabelle number-theory tower had open; with it the
tower is complete. The historical campaign (three earlier fleets that mapped the
wall, then two that closed it) is recorded in
`docs/four-square-progress-2026-06-17.md`.

## How to reproduce

The proof's working set is large, so it runs in the same two stages the
campaign used — a base **checkpoint**, then the heavy proof **on** that
checkpoint (the same pattern as the HOL4 `/tmp/hol4_*` checkpoints):

```sh
# 0. one-time: warm Isabelle/Pure checkpoint
tools/build-isabelle-pure.sh                 # -> /tmp/isabelle_pure

# 1. build the four-square base checkpoint (NT ladder + four_sq_mult +
#    lagrange_assembly + the signed-residue keystone + star_v), a few minutes
tools/build-l4-checkpoint.sh                  # -> /tmp/l4_foursq_star

# 2. run the full theorem (the 9 divide leaves -> descent step -> iterate)
cargo test --release -p polyml-bin --test isabelle_four_square \
      four_square_full_theorem -- --ignored --nocapture
```

The test asserts the kernel markers `MEGA_ALL_LEAVES_DONE`, `DSTEP_ALL_OK`,
`L4_ITER_ALL_OK`, and `MEGA_LAGRANGE_FOUR_SQUARE_PROVED`, and that the final
theorem is 0-hypothesis and α-equivalent to the statement above.

Both runs set `Proofterm.proofs := 0`, which drops auxiliary proof-*term*
recording to bound RAM. The kernel still validates every inference, so the
theorem remains genuine — this is standard Isabelle practice for large proofs.

## What each file is

The proof is structured as a self-contained **base** plus independently-checked
**deltas** (the leaves and assembly steps), then one driver that runs them all:

| file | role |
| --- | --- |
| `_assembled_base.sml` | the live-context base the checkpoint is exported from: the classical-FOL number-theory ladder + `four_sq_mult` (Euler's identity) + `lagrange_assembly` (the multiplicative reduction) + `sym_residue_signed` (the signed-residue keystone). `tools/build-l4-checkpoint.sh` adds `star_v` and exports it. |
| `base.sml` | the number-theory foundation that `_assembled_base.sml` begins with (also the base the `four_square_identity_and_reduction` test runs directly). |
| `partA_identity_delta.sml` | Euler's four-square identity `four_sq_mult` + the `proveStarFor` star machinery. |
| `partB_*_delta.sml`, `partC_*_delta.sml` | the residue-pigeonhole front end and the signed-residue keystone. |
| `divide_leaf_<signs>_delta.sml` | the 8 signed Euler divide-by-m² leaves (`pppp` … `pnnn`) + the 9th all-negative `nnnn` leaf — each independently 0-hyp checked. |
| `descent_step_assembly_delta.sml` | the 16→9 `disjE` tree assembling the leaves into one descent step. |
| `strict_rltm_FINAL_delta.sml` | the strict bound `0 < r < m` (the `r = m` exclusion) that lets the descent start a strong induction. |
| `iterate_discharge_delta.sml` | iterate the descent down to `m = 1` (strong induction) and discharge `lagrange_assembly`. |
| `lagrange_four_square_FULL_driver.sml` | the one-process driver that, on `/tmp/l4_foursq_star`, runs every leaf + the descent step + the iteration and concludes the theorem. |

The individual `*_delta.sml` files are the human-readable record of how each
piece was proved; the FULL driver is the single artifact the test runs.
