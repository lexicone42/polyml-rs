# Euclid–Euler theorem (even perfect numbers) — PROVED, COMPLETE (2026-06-22)

## 2026-06-22 UPDATE (SCG close fleet wf_3f6516e5-ac4) — euclid_euler CLOSED UNCONDITIONALLY

The residual lemma SCG was proved and discharged. `euclid_euler` is now a complete 0-hyp
theorem, hand-verified (`isabelle_euclid_euler.rs`, 1/1 pass ~44s):
  `⊢ 0<n ⟹ even n ⟹ (perfect n ⟺ ∃p. prime2(2^p−1) ∧ n = 2^(p−1)·(2^p−1))`
the FULL Euclid–Euler characterization of even perfect numbers. The conditional partial is
GONE — the SCG meta-hypothesis is discharged (EUCLID_EULER_UNCONDITIONAL_OK).
- **SCG proved** (0-hyp): `⊢ ⋀a m. ¬(2∣m) ⟹ σ(2^a·m) = (∑_{i≤a}2^i)·σ(m)` (σ-multiplicativity
  for any odd m), via: a general **divisor_list(m)** = filter [1..m] by ∣ (completeness
  `lmem d (divisor_list m) ⟺ 0<d ∧ d≤m ∧ d∣m` + lnodup, the support of σ(m)); the **product
  divisor list** `dl2 a D` with `lnodup` (cross-level 2-adic distinctness) + **completeness**
  (the 2-adic split: every divisor of 2^a·m is 2^i·d with i≤a via pow2_dvd_char, d∣m the odd
  cofactor peeled by euclid_lemma at prime 2); fed through the banked `sigma_mult_reduction` +
  the support bijection. New files: `isabelle_euler_converse_dl2.sml` (dl2) +
  `isabelle_euler_converse_close.sml` (divisor_list + SCG + the discharge).
- 0-hyp, aconv the intended biconditional; runtime axiom audit = 80, the only σ-mentioning
  axiom is the conservative `sigma_def`, ZERO mention perfect/euclid; only classical
  assumption = ex_middle. Instantiated BOTH ways at n=6 and n=28 by genuine inference.
- Self-contained: 5 drivers (base + converse + sigma_mult + dl2 + close), run directly.

The 2026-06-22 "reduced to one lemma" record below is kept for the SCG diagnosis + the
supporting-lemma detail.

---

# Euclid–Euler theorem — Euler's converse, REDUCED to one lemma (superseded above)

Ultracode campaign wf_1fc90eed-991 toward Euler's converse + the full Euclid–Euler iff:
**every even perfect number is 2^(p−1)(2ᵖ−1) with 2ᵖ−1 prime**. Euclid's direction is the
banked `euclid_perfect` (Elements IX.36). This campaign proved the converse + the iff
**CONDITIONAL on one residual lemma (SCG)** + two supporting lemmas outright. The full
theorem is NOT unconditionally closed — it is *reduced to one clean open lemma*. Fenced
(`isabelle_euclid_euler.rs`, 1/1 pass ~35s warm; verified by hand).

## Proved UNCONDITIONALLY (0-hyp, aconv-intended, soundness-probed; on the euclid_perfect base)
- **`sigma_bound`** : `⊢ 1<m ⟹ d∣m ⟹ d<m ⟹ σ(m)=m+d ⟹ (d=1 ∧ prime2 m)` — the
  "σ(m) equals m plus a proper divisor forces m prime" argument (if d>1 then {1,d,m} are 3
  distinct divisors so σ(m) ≥ 1+d+m > m+d; so d=1, σ(m)=m+1, equality iff m prime). Via the
  divisor-list: σ(m) = lsumf id (divisor_list m) ≥ lsumf over a distinct-divisor sublist.
- **`factor_2s`** : `⊢ 0<n ⟹ even n ⟹ ∃a m. n=2^a·m ∧ odd m ∧ 0<a` (extract the 2-part).
- **`consec_coprime`** (of 2^b and 2^b−1: a common divisor divides their difference 1) + the
  EC assembly helpers (m_le_sigma, the parity bridge, the context transfer).

## Proved CONDITIONAL on SCG (the residual wall)
SCG := `⋀a m. odd m ⟹ σ(2^a·m) = σ(2^a)·σ(m)` — σ-multiplicativity for an ARBITRARY odd m.
- **`euclid_euler_cond`** : `⊢ SCG ⟹ 0<n ⟹ even n ⟹ (perfect n ⟺ ∃p. prime2(2^p−1) ∧
  n=2^(p−1)(2^p−1))`. 0-hyp (HYPS=0, SHYPS=0) modulo the SCG meta-hypothesis, aconv the
  intended biconditional. The kernel confirms it genuinely NEEDS SCG (a probe: dropping SCG
  is not aconv the proved thm). The FORWARD half is Euler's converse; the BACKWARD half is the
  banked `euclid_perfect`. So the FULL Euclid–Euler theorem holds **modulo σ-multiplicativity
  for general odd m**.
- Axiom audit: 70 axioms; the only one mentioning σ is the conservative `sigma_def`; ZERO
  mention perfect/euclid/converse/scg. Only classical assumption = ex_middle.

## THE RESIDUAL WALL (SCG) — the resume point
The banked σ machinery (divlist / sigma_char / div2aq_complete) is SPECIALIZED TO PRIME q:
`divlist a q` has exactly 2 elements per 2-power level ({2ⁱ, 2ⁱ·q}) because a prime q has
exactly 2 divisors. SCG needs the GENERAL odd m, whose divisor list has a VARIABLE number of
elements per level. Closing SCG requires (a) a general `divlist2 a (divisor_list m)` = the
product list {2ⁱ·d : i≤a, d ∈ divisor_list m}; (b) `lnodup` of it (cross-level 2ⁱ·d
distinctness); (c) COMPLETENESS — every divisor e≤2^a·m equals 2ⁱ·d with i≤a, d∣m (the 2-adic
split: pow2_dvd_char on the 2-part + euclid_lemma at prime 2 to peel the odd cofactor); then
σ(2^a·m) = lsumf id (product list) = (Σ 2ⁱ)·(lsumf id (divisor_list m)) = σ(2^a)·σ(m) via a
list-distribution lemma. This is a div2aq_complete-scale fresh wall (a dedicated fleet).
Partial work: `isabelle_euler_converse_sigma_mult.sml`. NB SCG is exactly the (specialized,
a=2-power) case of general σ-multiplicativity for coprimes — a famous reusable lemma; once
banked, `euclid_euler_cond` discharges it and the full theorem closes mechanically. With it,
the FULL Euclid–Euler characterization of even perfect numbers is complete.

Drivers (run directly): `isabelle_euclid_perfect.sml` (base) + `isabelle_euler_converse.sml`
(the converse + iff delta) + `isabelle_euler_converse_sigma_mult.sml` (the SCG partial).
