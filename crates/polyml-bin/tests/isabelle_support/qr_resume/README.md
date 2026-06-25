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

## F2 — the Eisenstein bridge (PARTIAL; per-k crux + half the parity bookkeeping)

The next step from Gauss's *lemma* toward the *law* is **Eisenstein's bridge**: recast
`a^((p−1)/2) ≡ (−1)^μ` into the floor-sum form `legendre(q,p) = (−1)^(Σ_{k=1..m} ⌊q·k/p⌋)`.
Fleet F2 built the toolbox + the analytic crux on top of the F1 toolbox
(`qr_f1_toolbox.sml`, which banks `gauss_lemma` + `parity`/`cnt`/`sumf`/`lar`/`rdiv`).

Committed delta: **`qr_f2_appendix.sml`** (the F2 delta) — concatenate after
`qr_f1_toolbox.sml` to get the self-contained driver `qr_f2.sml` (both gitignored as
1MB scratch; rebuild with `cat qr_f1_toolbox.sml qr_f2_appendix.sml > qr_f2.sml`). Runs
to `Tagged(0)` (~4.05e9 steps, 4 GB heap); 0 new axioms over F1.

**Proved (all 0-hyp + aconv; markers in `qr_f2_progress.json`):**
- `split_lemma` — the EXACT floor/remainder split `q·k = p·⌊q·k/p⌋ + (q·k mod p)`,
  `(q·k mod p) < p` (`EIS_SPLIT_OK`).
- `parity_mult_l` / `parity_odd_mult` / `parity_double` — parity of products
  (`parity(ab) = parity((parity a)·b)`; odd·b parity = parity b; `parity(z+z)=0`).
- **`floor_parity_link`** — THE per-k analytic crux: for odd `a`,`p`,
  `parity(⌊a·k/p⌋) = parity(k + (a·k mod p))`, i.e. `⌊a·k/p⌋ ≡ k + (a·k mod p) (mod 2)`
  (`FLOOR_PARITY_LINK_OK`).
- `parity_sumf_cong` — pointwise parity agreement lifts through `sumf`.
- **`floor_sum_kr_parity`** — HALF the Eisenstein parity bookkeeping:
  `Σ_k ⌊q·k/p⌋ ≡ (Σ_k k) + (Σ_k q·k mod p) (mod 2)` (`FLOOR_SUM_KR_PARITY_OK`).

**Blocker (the remaining half):** `μ ≡ Σ_k ⌊q·k/p⌋ (mod 2)` needs the OTHER equation
`Σ_k (q·k mod p) ≡ (Σ_k k) + μ (mod 2)`, which follows from
`Σ (q·k mod p) = Σ lar(q·k) + μ·p − 2·(Σ of flipped lar)` ONLY via the **sum-permutation
invariance of `lar`** (`Σ_{k=1..m} lar(q·k) = Σ_{k=1..m} k`). The tower banks `lar_perm`
only as a **product** invariant (`lprod` over the natlist) — there is **no list-sum
(`lsumf`)** and **no sum-reindex/sum-permutation** lemma. Re-deriving `lar`'s permutation
as a *sum* is fresh infrastructure (a parallel `lsumf` + `lsumf_perm_of_inj`) — a separate
fleet. Once that parity equality lands, the Eisenstein *lemma* follows immediately from the
already-proved `gauss_lemma` (`S = (−1)^μ`).

## Open: the full reciprocity *law*

Gauss's *lemma* is the cornerstone; the reciprocity *law*
`(p/q)(q/p) = (−1)^(((p−1)/2)((q−1)/2))` additionally needs **Eisenstein's
lattice-point count** (`Σ_{k} ⌊q·k/p⌋ + Σ_{j} ⌊p·j/q⌋ = ((p−1)/2)((q−1)/2)`)
combined with the Eisenstein bridge above. That is tracked as further work.
