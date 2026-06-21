# Fermat's two-square theorem (FULL characterization) — progress (2026-06-20)

Ultracode campaign wf_9cb6cd8a-cdc toward
`⊢ 0<n ⟹ (n is a sum of two squares ⟺ every prime p≡3 (mod 4) divides n to an even
power)` on the Isabelle/Pure interpreter — the full form completing the banked
two-square crown jewel (`isabelle_twosquare.sml`, which proved only the prime case
p≡1mod4 ⟹ p=a²+b²). The full iff is **NOT yet proved**; the graceful floor banked two
genuine 0-hyp lemmas, fenced by `isabelle_twosquare_full.rs` (2/2 pass, ~29s warm).

## Proved + banked (both re-verified independently, 0-hyp, aconv-intended, soundness-probed)

`crates/polyml-bin/tests/isabelle_support/twosquare_full_resume/`:

- **`brahmagupta`** — the Brahmagupta–Fibonacci sum-of-two-squares MULTIPLICATIVITY
  identity (the `four_sq_mult` analogue for two squares):
  `⊢ ∃P Q. (a²+b²)·(c²+d²) = P²+Q²`. Stated in the faithful sum-PRESERVATION form
  (the literal `sub` form is false in truncated ℕ; `P=|ac−bd|` via an `le_total`
  case-split). Driver: `ts_brahmagupta.sml` (the lean ~536-line delta, spliced via
  `common::with_nt_helpers`). Marker `BRAHMAGUPTA_DONE`; ~3.15B steps; runtime axiom
  audit = 38 (Pure + conservative NT foundation + ND rules), 0 mentioning the
  conclusion shape.
- **`key_onlyif`** — the only-if KEY lemma ("−1 is not a QR mod p≡3mod4"):
  `⊢ prime2 p ⟹ (∃k. p = 4k+3) ⟹ p ∣ a²+b² ⟹ (p∣a ∧ p∣b)`. Via the inverse + FLT-order
  argument (x=b·a⁻¹ has x²≡−1; FLT x^(p−1)≡1; (−1)^((p−1)/2)=−1 since (p−1)/2 odd ⟹ p∣2
  ⟹ contradiction). Driver: `ts_key_lemma.sml` (self-contained on a custom
  `primes_1mod4` spine = the euler_criterion/FLT base + parity machinery `apm1`,
  `lagrange_roots`). Marker `KEY_ONLYIF_OK`; ~2.63B steps; 49 axioms, 0 suspicious;
  4 soundness probes (needs mod4, needs dvd, conjunctive conclusion, NOT the false
  p≡1mod4 companion). Concrete kernel probes on the brahmagupta base: ACCEPT 2/5/9/13
  as sums of two squares (explicit witnesses), REJECT 3/7/21 (every candidate witness
  refuted to oFalse by genuine inference).

## What is left (the open iff — both halves)

**ONLY-IF** (n=a²+b² ⟹ every p≡3mod4 to even power) — ~90% built, blocked on ONE
proof-engineering bug (NOT a math gap):
- Statement (relational valuation, no `vp` const): `0<n ⟹ (∃a b. n=a²+b²) ⟹ (prime2 p
  ∧ p=4k+3) ⟹ ∃v m. n = pʵ·m ∧ ¬(p∣m) ∧ ∃j. v=2j`. Method: strong-induction descent —
  p∣n ⟹[key_onlyif] p∣a,p∣b ⟹ n=p²·n', n'<n ⟹ IH ⟹ even v.
- ALL 11 arithmetic/algebra sub-lemmas verify in isolation (`oi_arith.sml`:
  lt0_suc/lt_add_pos/lt_self_mult/sq_factor/factor_n/pow_step/even_step/pp_suc2 +
  key_onlyif_at/prime2_gt1/dvd-extract). caseB (¬p∣n base case) builds aconv-true.
- BLOCKER: caseA (the p∣n descent branch, `oi_casea.sml`) raises
  `THM("implies_elim: major premise")` in the big nested let-assembly — the SAME class
  already fixed in caseB: a meta-vs-object implication / witness-shape mismatch in the
  disjE-combine + impI_S2 wrapping + the applyIH→conclNp(mp_S2) chain. NEXT: add
  per-step `out`/`handle` markers inside caseA to localize the failing `implies_elim`
  (candidates: the disjE combine of caseZ/caseSq, the mp_S2 conclNp, the cbInner
  conjunct projections), then align the meta/object boundary as in caseB. ~27s dev loop
  on the warm spine. GOTCHA logged: `le`/`lt`/`dvd` are ABBREVIATIONS with an inner
  Ex/Abs, so a rewrite predicate `Abs("z", le m (Bound 0))` CAPTURES Bound 0 — always
  build such predicates with `Term.lambda` over a FRESH Free (bit lt_add_pos_at /
  lt_self_mult_at, now fixed).

**IF** (every p≡3mod4 to even power ⟹ sum of two squares) — NOT started. The heavier
half: factor n (FTA existence), each prime power is a sum of two squares (2=1²+1²,
p≡1mod4 banked, p^(2k)=(pᵏ)²+0², p≡3mod4-to-even=(pʲ)²+0²), multiply via `brahmagupta`.
Needs the 3-monolith merge (twosquare ⊕ FLT ⊕ FTA) + a `vp` const or the relational
exponent. `brahmagupta` (the multiplicativity wrapper) is banked on the light
with_nt_helpers base.

## Resume recipe (next fleet)
1. FIRST close the only-if: prepend the primes_1mod4 spine (`ts_key_lemma.sml`) then
   `oi_arith.sml oi_descent.sml oi_casea.sml`; localize + fix the caseA `implies_elim`.
2. Then the if-direction on the merged base (twosquare spine + FTA splice + brahmagupta),
   define the relational exponent, assemble the iff (mkConj of both Imps, cf.
   `isabelle_wilson_iff.sml`). See `twosquare_full_resume/RESUME.txt` for the exact
   commands. Like four-square, this is a multi-fleet crown jewel — the two banked lemmas
   + the near-complete only-if are the standing increment.
