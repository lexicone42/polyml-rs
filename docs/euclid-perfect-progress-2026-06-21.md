# Euclid's perfect-number theorem — progress (2026-06-21)

Ultracode campaign wf_a1ac4dbf-1b1 toward Euclid's theorem (Elements IX.36): if 2ᵖ−1 is
prime then n = 2^(p−1)·(2ᵖ−1) is PERFECT (σ(n) = 2n), on the Isabelle/Pure interpreter.
The full theorem is **NOT yet proved** (confirmed multi-fleet); banked the σ subsystem +
`sigma_prime` + the geometric-sum lemmas, all fenced (`isabelle_sigma.rs`, 2/2 pass ~204s).
Introduces the sum-of-divisors function σ — a new area for the tower.

## Proved + banked (0-hyp, aconv-intended; on `common::with_binom_thm`)
- **σ subsystem** (`isabelle_sigma.sml`): a new HO const `sigma : nat⇒nat` + a summand-weight
  const `swt`, via EXACTLY 3 conservative axioms (none mentions `perfect`/the conclusion):
  `swt_dvd : d∣n ⟹ swt n d = d`, `swt_ndvd : ¬(d∣n) ⟹ swt n d = 0`,
  `sigma_def : sigma n = sumf (swt n) n` (sum over d=0..n; d=0 contributes 0 since 0∤n for
  n>0). The conditional summand mirrors the proven `count`/`remove1` conditional-axiom pattern.
- **`sigma_prime`** : `⊢ prime2 q ⟹ sigma q = q + 1` (the only divisors of a structural prime
  are 1 and q). The graceful-floor headline.
- **`geo_sum`** : `⊢ ∑_{i=0}^k 2^i = 2^(k+1) − 1`  and  **`geo_add`** : `⊢ 1 + ∑_{i=0}^k 2^i =
  2^(k+1)` (the geometric value of σ(2ᵏ), by induction).
- **FAITHFULNESS by genuine computation** (`isabelle_sigma_probe.sml`): the kernel unfolds
  sigma_def → sumf → swt and decides divisibility at every index, proving the 0-hyp numeral
  theorems `sigma 6 = 12`, `sigma 28 = 56` (6, 28 PERFECT) and `sigma 8 = 15 ≠ 16` (8 NOT
  perfect, neg(oeq 15 16) kernel-proved). This is the strongest faithfulness check — a wrong
  σ definition computes wrong values.
- Axiom audit: 52 total (Pure meta-logic + the binom_thm foundation + the 3 conservative σ
  axioms); ZERO mention `perfect`/the conclusion; only classical assumption = ex_middle.

## The wall (why the full theorem is multi-fleet) — a representation footgun
`sigma_pow2` (σ(2ᵏ)=2^(k+1)−1 over σ itself), the divisor characterization `sigma_char`, and
hence `euclid_perfect` are blocked on the **SUM-SUPPORT REINDEX**: `sigma N = sumf (swt N) N`
sums over the FULL range d=0..N, which for N=2^a·q is **exponential**, while the summand is
nonzero at only the 2(a+1) divisor points {2ⁱ, 2ⁱ·q}. Collapsing this *sparse sum over an
exponential range* to the dense geometric sum is the genuine wall (two independent seats
blocked at exactly this point). The single-interior-point collapse that makes `sigma_prime`
tractable does NOT scale to the multi-point step-function of 2^a·q.

LESSON: the σ-via-`sumf`-over-`[0..N]` representation is clean to DEFINE but a footgun for the
divisor-sum proofs. The right representation is a **divisor LIST** (sum over the actual list of
divisors), where σ(2^a·q) is a list-sum over 2(a+1) elements — no sparse/exponential reindex.

## Resume path (next fleet — Route A)
1. Consolidate this banked prelude (σ subsystem + geo + sigma_prime + the FOL/dvd helper
   layer on the final context) into a `common::with_sigma` splice.
2. Build a `natlist` divisor list + list-sum; prove `lsum(divisor_list(2^a·q)) =
   (2^(a+1)−1)(q+1)` via `geo_sum` (easy), then the **support bijection**
   `sumf (swt N) N = lsum(divisor_list N)` (the hard piece, ~ Wilson-list-product scale).
   Sub-lemmas needed (none banked): `prime2_two` (prime2 2), `pow2_dvd_char`
   (d∣2ᵏ ⟹ ∃i≤k. d=2ⁱ, by repeated euclid_lemma), the interior-collapse.
3. With `sigma_char` banked, the S4 assembly (σ(2^(p-1)·q)=(2^p−1)·2^p=2n ⟹ perfect) is
   mechanical and `euclid_perfect` closes. The in-driver S4 note (`isabelle_sigma.sml`)
   carries the exact statement + assembly outline. Then Euler's converse → the full
   Euclid–Euler characterization of even perfect numbers is the next branch.
