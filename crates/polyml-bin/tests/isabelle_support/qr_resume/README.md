# Quadratic reciprocity — campaign artifacts

This directory holds the proof of **Gauss's lemma** — the cornerstone of quadratic
reciprocity — in Isabelle/Pure, run on the polyml-rs interpreter, plus the resume
scratch from the multi-fleet campaign that built it.

> gauss_lemma : ⊢ prime2 p ⟹ ¬(p∣a) ⟹ (p−1 = m+m) ⟹
>                  ∃S. cong p (pow a m) S ∧ (cong p S 1 ∨ cong p S (p−1))

i.e. `a^((p−1)/2) ≡ (−1)^μ (mod p)`, where the sign `S = (−1)^μ` is the running
product of the per-residue flip signs and the `±1` is derived from the `{1,p−1}`
closure (`(p−1)²≡1`), *not* from the Euler dichotomy — so it genuinely ties `a^m`
to the residue flips. A 0-hypothesis theorem by genuine LCF kernel inference; no
new axioms over the conservative base; only classical assumption is `ex_middle`.

## The committed artifact

- **`gauss_final.sml`** — the **self-contained** driver (15.7k lines) that proves
  Gauss's lemma end-to-end on `/tmp/isabelle_pure`. It embeds the whole chain: the
  Euler-criterion summit + `prodf` + a natlist library + `lmap` + `rmod`/`lar`,
  then `abs_inj` → the residue lemmas → the permutation-product (`lprod_perm_of_inj`,
  `lar_perm`) → `prod_axk_eq_pow` → `prod_split_sign` → `gauss_lemma`. Driven by the
  `#[ignore]` test `gauss_lemma` in `crates/polyml-bin/tests/isabelle_gauss.rs`.

Reproduce:

```sh
tools/build-isabelle-pure.sh          # -> /tmp/isabelle_pure (one-time)
cargo test --release -p polyml-bin --test isabelle_gauss -- --ignored --nocapture
```

The test asserts the kernel markers `PROD_AXK_OK`, `PROD_SPLIT_OK`, `GAUSS_LEMMA_OK`,
`GAUSS_FINAL_ALL_OK`, and that no unexpected axiom was introduced.

## Campaign history (the cruxes)

The lemma was built across several ultracode fleets; the two genuine cruxes were:
1. **`abs_inj`** — injectivity of the least-absolute-residue map (the `+/-` collision
   `0 < k+k2 < p` is vacuous), proved on the Euler base.
2. **`lprod_perm_of_inj`** — the Wilson pairing product-invariant generalized from an
   involution to an injection, giving `∏ lar(a·k) = m!`.

The intermediate per-stage drivers from the campaign (the foundation base, the
`abs_inj` standalone, the Stage-R and Stage-P drivers, the recon plan) are
**superseded by `gauss_final.sml`** (which embeds all of them) and are kept only as
local resume scratch — they are gitignored, not tracked.

## Open: the full reciprocity *law*

Gauss's *lemma* is the cornerstone; the reciprocity *law*
`(p/q)(q/p) = (−1)^(((p−1)/2)((q−1)/2))` additionally needs **Eisenstein's
lattice-point count** (`Σ_{k} ⌊q·k/p⌋ + Σ_{j} ⌊p·j/q⌋ = ((p−1)/2)((q−1)/2)`)
combined with this lemma in the `(−1)^(Σ⌊⌋)` form. That is tracked as further work.
