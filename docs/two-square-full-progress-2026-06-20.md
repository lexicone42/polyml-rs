# Fermat's two-square theorem (FULL characterization) — PROVED, COMPLETE (2026-06-22)

## 2026-06-22 UPDATE (merge fleet wf_8cdcec09-4f4 + bridge fleet wf_355aeea1-2fc) — FULL IFF CLOSED, UNCONDITIONAL

The full unconditional two-square characterization is PROVED, hand-verified
(isabelle_twosquare_full.rs::full_iff_unconditional, 1/1 pass ~203s):
  `twosquare_full : ⊢ 0<n ⟹ (∃a b. n=a²+b²  ⟺  ∀p. prime2 p ⟹ p≡3mod4 ⟹ v_p(n) even)`
i.e. **n is a sum of two squares IFF every prime ≡3 (mod 4) divides n to an even power** —
the complete Fermat two-square characterization, 0-hyp by genuine LCF kernel inference.
- MERGE (wf_8cdcec09-4f4): spliced the FLT/binom/key_onlyif sub-tree onto thyGR
  (seat1_flt_region_rerooted.sml) so the banked only_if and the unconditional if_direction
  COEXIST on compatible contexts; assembled the conditional iff (seat1_iff_assembly.sml).
- BRIDGE (wf_355aeea1-2fc, both seats closed it): proved mult_left_cancel (le-witness +
  left_distrib + add_left_cancel + mult_eq_zero, no induction) → valuation_unique
  (vpred p n e is unique in e, via mult_left_cancel + pow_add + p∣p^≥1) → bridged only_if's
  per-prime EXISTENTIAL even-valuation to hpBody's UNIVERSAL inner → discharged the only-if
  object hypothesis (oiH) → mkConj with if_direction → the UNCONDITIONAL twosquare_full.
  Files: bridge_seat2.sml + tsf_verify.sml.
- VERIFIED: TWOSQUARE_FULL hyps=0 aconv=true; the oiH/SCG hypothesis is GONE (PROBE_OK
  twosquare_full is UNCONDITIONAL); 0 new axioms/consts over the monolith baseline, only
  classical = ex_middle; kernel accepts 5/9/2/13 as sums of two squares + rejects 3/7/21,
  both directions, by genuine inference. Self-contained ~27.7K-line driver, run directly.

The 2026-06-21/06-22 records below (only-if close, if-direction close, the context-merge) are
kept for the campaign history.

---

# Fermat's two-square theorem (FULL characterization) — progress (2026-06-20, updated 2026-06-21, 2026-06-22)

## 2026-06-22 UPDATE (if-direction fleet wf_dfaa09fe-380) — IF-DIRECTION PROVED UNCONDITIONAL; both directions now done

The if-direction CLOSED unconditionally — the harder direction of the full characterization.
**Both directions are now proved**; the full iff awaits only a context-merge (no new math).
Hand-verified (isabelle_twosquare_full.rs, 7/7 pass ~191s).
- **`if_direction`** : `⊢ 0<n ⟹ hpBody n ⟹ sumsq n` (UNCONDITIONAL, 0-hyp, aconv, 0 new axioms
  = 78 monolith baseline; only classical = ex_middle), where `hpBody n` = every prime p≡3mod4
  divides n to an EVEN power (relational valuation) and `sumsq n` = ∃a b. n=a²+b². This is the
  "even-power ⟹ sum of two squares" direction. Markers IF_DIRECTION_CLOSED + VAL_TRANSFER_CLOSED.
- Closed via: **`mod4_trichotomy`** (prime ⟹ 2 ∨ ≡1mod4 ∨ ≡3mod4, via div_mod at 4); the
  **per-prime-power** sum-of-2-sq leaves (`pow2_sumsq`, `p1mod4_pow_sumsq` via Brahmagupta on
  the banked `twosquare`, `p3mod4_even_sumsq` = (p^(e/2))²+0²); and — the piece the Setup feared
  was multi-fleet but which CLOSED — the **valuation transfer** `val_transfer` (+ `val_mult_coprime`,
  `val_coprime_self`, `padic_split`, `prime_div_eq`, `prime_not_dvd_pow`): the per-prime relational
  valuation matches the FTA exponent, via euclid_lemma + strong induction (the same divisor/valuation
  approach as the Euclid-Euler SCG close). Folded via the banked `prod_all_sumsq`.
- **`twosquare_full_modulo_onlyif`** : the conditional full iff (if_direction + only_if as a
  hypothesis) — proved. New files: if_full_direction/if_trichotomy/if_perprime/if_valuation/if_iff.sml.

REMAINING for the UNCONDITIONAL FULL IFF (no new math — a CONTEXT-MERGE, multi-fleet by volume):
`if_direction` lives on the monolith context `ctxtGR`; the banked `only_if` lives on the spine
context `ctxtSub` (= thyP→binom→sumf, carrying FLT/apm1/key_onlyif). Both extend the SHARED `ctxtP`
byte-identically. To `mkConj` the two directions into the full iff they must share ONE context:
re-establish `only_if` on `ctxtGR` by splicing the FLT/binom/key_onlyif sub-tree (~6K lines,
ts_key_lemma 5954-12220) onto thyGR + re-running the only_if descent (oi_arith/oi_descent/oi_casea).
A dedicated context-merge fleet. Both directions are DONE; this is bookkeeping-heavy plumbing.

---

# Fermat's two-square theorem (FULL characterization) — progress (2026-06-20, updated 2026-06-21)

## 2026-06-21 UPDATE (finish fleet wf_c883d0a5-498) — ONLY-IF DIRECTION CLOSED; if-direction substantial

The "finish" fleet closed the only-if direction in full and made substantial if-direction
progress. The full iff is still open (the if-direction's valuation-transfer + the final
merge remain). All re-verified independently; fenced (isabelle_twosquare_full.rs, 5/5 pass
~111s warm).

- **ONLY-IF DIRECTION — PROVED + FENCED** (both seats independently closed it, same fix;
  verifier re-ran from scratch): `⊢ prime2 p ⟹ (∃k. p=4k+3) ⟹ (0<n ∧ ∃a b. n=a²+b²) ⟹
  ∃v m. n = pʵ·m ∧ ¬(p∣m) ∧ ∃j. v=2j` (p divides n to an even power, relational valuation,
  no vp const). 0-hyp, aconv-intended, axiom-audit clean (49 axioms, 0 conclusion-mentioning,
  only ex_middle classical). Concrete kernel decision probes pass: REJECT 3/7/21, ACCEPT
  5/9/2/13 (`oi_concrete_probe.sml`). ~2.8B steps, Tagged(0), deterministic.
  - THE caseA FIX (root cause, both seats converged): the descent's num-cases arms
    (caseZ = n'=0 contra, caseSq = n'=Suc q descent) were wrapped in `impI_S2`, converting
    the META-implication into an OBJECT `jT(Imp A C)` — but `disjE_elimSub` consumes its
    arms as RAW META-implications (`jT A ⟹ jT C`) via `Thm.implies_elim`. The double-wrap
    handed an object impl where a meta one was required → `THM("implies_elim: major premise")`.
    FIX: drop the two `impI_S2` wrappers, pass caseZ/caseSq directly (the exact pattern apm1
    + the dvd-EM split already use). NOT a math gap; all 11 arith sub-lemmas were already fine.
    Banked: `oi_casea_seat2.sml` (caseA rebuilt mirroring the working caseB) + `oi_verify.sml`.
- **IF DIRECTION — substantial progress (not closed)**, on the merged twosquare base
  (`if_toolkit.sml`/`if_brahma.sml`/`if_blocks.sml`/`if_direction.sml`): PROVED the leaf +
  fold machinery — brahma4 (brahmagupta on the twosquare base), two_is_sumsq (2=1²+1²),
  sq_is_sumsq (k²=k²+0²), sumsq_times_sq, sumsq_mult, and **prod_all_sumsq** (the product
  fold over an FTA-style list, 0-hyp+aconv+probe). NOT yet built: (a) the mod-4 trichotomy
  (prime2 p ⟹ p=2 ∨ p=4k+1 ∨ p=4k+3 — concrete, via div_mod_exists at 4), (b) the
  strong-induction VALUATION TRANSFER (v_q(n)=v_q(n/p) for q≠p — an FTA-uniqueness-grade
  coprime-valuation argument; the crux). Fenced (if_direction_machinery test).
- **FULL IFF — not assembled.** Needs: close the if-direction (trichotomy + valuation
  transfer), then re-establish the only-if on the twosquare base (the monolith has
  lagrange_roots/mod_cancel/cong but NOT FLT(apm1) nor key_onlyif — splice them), then mkConj
  the two Imps (cf. isabelle_wilson_iff.sml). The 3-way merge (twosquare ⊕ FLT ⊕ FTA) + the
  valuation transfer is the remaining work — a follow-up fleet.

---

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
