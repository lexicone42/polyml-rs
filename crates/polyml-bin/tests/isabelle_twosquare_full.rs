//! TOWARD FERMAT'S TWO-SQUARE FULL IFF — the two banked graceful-floor lemmas.
//!
//! GOAL (multi-fleet, NOT closed): n is a sum of two squares IFF every prime
//! p ≡ 3 (mod 4) divides n to an EVEN power. This file banks the two genuinely
//! valuable + independently-citable lemmas the campaign produced; the full iff
//! (and the only-if descent / if-direction FTA volume) remain a follow-up.
//!
//! (1) brahmagupta — the Brahmagupta-Fibonacci sum-of-two-squares MULTIPLICATIVITY
//!     identity (the four_sq_mult analogue for two squares):
//!         |- Ex P Q. (a^2+b^2)*(c^2+d^2) = P^2 + Q^2
//!     (the faithful sum-PRESERVATION form: the literal `sub` form is FALSE in
//!     truncated ℕ; P = |a*c - b*d| is produced by an le_total case-split.)
//!     Built on `common::with_nt_helpers` (the classical NT foundation). 0-hyp,
//!     aconv-intended, soundness-probed (NOT the false single-square form).
//!     ~3.15B steps. Marker: BRAHMAGUPTA_DONE.
//!
//! (2) key_onlyif — the only-if KEY lemma ("-1 is not a QR mod p≡3mod4"):
//!         |- prime2 p ==> (Ex k. p = (k+k+k+k)+3) ==> p | a^2+b^2
//!              ==> (p|a /\ p|b)
//!     Built on the (self-contained) isabelle_primes_1mod4 spine (the
//!     euler_criterion/FLT base + parity machinery: apm1, lagrange_roots).
//!     0-hyp, aconv-intended, 4 soundness probes (needs mod4, needs dvd,
//!     conjunctive conclusion, NOT the false p≡1mod4 companion). ~2.63B steps.
//!     Marker: KEY_ONLYIF_OK.
//!
//! Both re-verified independently FROM SCRATCH (verifier seat), Tagged(0),
//! 0-hyp, aconv true; runtime `Theory.all_axioms_of` audit clean (brahmagupta
//! 38 axioms, key_onlyif 49 — all Pure meta-logic + conservative recursion +
//! object-logic ND rules + the single classical ex_middle; ZERO axiom mentions
//! the conclusion). Concrete kernel soundness probes (on the brahmagupta base):
//! ACCEPT 2/5/9/13 as sums of two squares (explicit witnesses), REJECT 3/7/21
//! (every candidate witness refuted to oFalse by genuine inference).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_twosquare_full -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use common::with_nt_helpers;
use std::path::PathBuf;

fn checkpoint() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/isabelle_pure");
    p.exists().then_some(p)
}

fn support(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/twosquare_full_resume")
        .join(name)
}

const ENV: &[(&str, &str)] = &[
    ("ML_SYSTEM", "polyml"),
    ("ML_PLATFORM", "x86_64-linux"),
    ("ISABELLE_HOME", "/tmp/isa"),
];

/// Brahmagupta-Fibonacci multiplicativity — spliced via `with_nt_helpers`.
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn brahmagupta_multiplicativity() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    // The committed delta is the splice-ready form (no restore_pure_context;
    // with_nt_helpers prepends the foundation). The resume dir currently holds
    // the self-contained `ts_brahmagupta_full.sml`; for banking, the delta
    // `ts_brahmagupta.sml` (the proof only) is the file to splice.
    let driver =
        std::fs::read_to_string(support("ts_brahmagupta.sml")).expect("read ts_brahmagupta.sml");

    let Some((out, _)) = run_image_env(&image, &with_nt_helpers(&driver), 990_000_000_000, ENV)
    else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(
        out.contains("BRAHMAGUPTA_DONE"),
        "brahmagupta did not prove:\n{out}"
    );
    assert!(
        out.contains("brahmagupta aconv intended = true"),
        "brahmagupta conclusion not aconv the intended statement:\n{out}"
    );
    assert!(
        out.contains("PROBE_OK brahmagupta"),
        "soundness probe (not the false single-square form) missing:\n{out}"
    );
    assert!(
        !out.contains("PROBE_UNSOUND") && !out.contains("BRAHMAGUPTA_FAILED"),
        "a soundness probe fired / lemma FAILED:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("Static Errors") && !out.contains(": error:"),
        "compile error during proof:\n{out}"
    );
}

/// The only-if KEY lemma — self-contained driver (the primes_1mod4 spine).
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn key_only_if_lemma() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    // Self-contained (embeds the primes_1mod4 / euler / FLT spine) — run directly.
    let driver =
        std::fs::read_to_string(support("ts_key_lemma.sml")).expect("read ts_key_lemma.sml");

    let Some((out, _)) = run_image_env(&image, &driver, 990_000_000_000, ENV) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(
        out.contains("KEY_ONLYIF_OK"),
        "key only-if lemma did not prove:\n{out}"
    );
    assert!(
        out.contains("KEY hyps=0 aconv=true"),
        "0-hyp / aconv check failed:\n{out}"
    );
    assert!(
        out.contains("PROBE_OK key_onlyif"),
        "soundness probes (mod4 / dvd / conjunction / not-1mod4) missing:\n{out}"
    );
    assert!(
        !out.contains("PROBE_UNSOUND") && !out.contains("KEY_ONLYIF_FAILED"),
        "a soundness probe fired / lemma FAILED:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("Static Errors") && !out.contains(": error:"),
        "compile error during proof:\n{out}"
    );
}

/// The IF-DIRECTION machinery on the MERGED twosquare base.
///
/// Appends `if_direction.sml` after the full `isabelle_twosquare.sml` monolith
/// (final context ctxtGR), banking the if-direction infrastructure for the full
/// two-square iff — all 0-hyp / 0-extra-hyp + aconv-checked on the SAME merged
/// base that carries the `twosquare` theorem (prime2 p ⟹ p≡1mod4 ⟹ p=a²+b²):
///   * BRAHMAGUPTA on the twosquare base (sum-of-two-squares multiplicativity),
///     `brahma4 (a,b,c,d)`  →  marker IF_BRAHMA_OK.
///   * two_is_sumsq (2=1²+1²), sq_is_sumsq (k²=k²+0²)  →  IF_TWO_OK / IF_SQ_OK.
///   * sumsq_times_sq (sumsq n ⟹ sumsq ((k*k)*n))  →  IF_STSQ_OK.
///   * sumsq_mult (sumsq m ⟹ sumsq n ⟹ sumsq (m*n)), THE brahmagupta fold step
///     →  IF_SMULT_OK.
///   * prod_all_sumsq : ⊢ ∀ps. (∀x. lmem x ps ⟹ sumsq x) ⟹ sumsq (lprod ps),
///     THE structural backbone — a list of sums-of-two-squares multiplies to a
///     sum of two squares (the fold over an FTA-style prime-power list).
///     0-hyp, aconv-intended, soundness-probed  →  IF_PROD_OK.
///
/// This is the GRACEFUL FLOOR of the if-direction: it reduces the if-direction
/// to (a) an FTA factorization of n into prime-powers, (b) classifying each
/// prime mod 4 to show every prime-power factor is a sum of two squares (2,
/// p≡1mod4 via the banked `twosquare`, p^(2k)=(p^k)²+0², p≡3mod4-to-even=
/// (p^j)²+0²), and (c) `prod_all_sumsq`. The remaining open piece is the
/// strong-induction VALUATION TRANSFER (an FTA-uniqueness-grade
/// coprime-valuation argument) + the mod-4 trichotomy + only-if re-splice for
/// the final iff — documented in the resume tree.
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn if_direction_machinery() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    // Merged base: the full twosquare monolith (it calls restore_pure_context),
    // then the if-direction delta appended on its final context ctxtGR.
    let monolith = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/isabelle_support/isabelle_twosquare.sml"),
    )
    .expect("read isabelle_twosquare.sml");
    let delta =
        std::fs::read_to_string(support("if_direction.sml")).expect("read if_direction.sml");
    let driver = format!("{monolith}\n{delta}\n");

    let Some((out, _)) = run_image_env(&image, &driver, 990_000_000_000, ENV) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // The merged base loaded and the twosquare theorem is present.
    assert!(
        out.contains("TWOSQ_ALL_OK"),
        "merged base / twosquare not OK:\n{out}"
    );
    // brahmagupta on the merged base.
    assert!(
        out.contains("IF_BRAHMA_OK"),
        "brahmagupta did not prove on merged base:\n{out}"
    );
    // leaf lemmas.
    assert!(
        out.contains("IF_TWO_OK aconv=true"),
        "two_is_sumsq failed:\n{out}"
    );
    assert!(
        out.contains("IF_SQ_OK hyps=0 aconv=true"),
        "sq_is_sumsq failed:\n{out}"
    );
    assert!(
        out.contains("IF_STSQ_OK hyps=0"),
        "sumsq_times_sq failed:\n{out}"
    );
    // the brahmagupta fold step.
    assert!(
        out.contains("IF_SMULT_OK hyps=0"),
        "sumsq_mult fold failed:\n{out}"
    );
    // THE structural backbone.
    assert!(
        out.contains("prod_all_sumsq aconv intended = true"),
        "prod_all_sumsq not aconv the intended statement:\n{out}"
    );
    assert!(
        out.contains("PROBE_OK prod_all_sumsq"),
        "prod_all_sumsq soundness probe missing:\n{out}"
    );
    assert!(
        out.contains("IF_PROD_OK hyps=0 aconv=true"),
        "prod_all_sumsq failed:\n{out}"
    );
    assert!(
        out.contains("IF_BLOCKS_DONE"),
        "if-direction blocks did not finish:\n{out}"
    );
    // not degenerate / exceptional.
    assert!(
        !out.contains("PROBE_UNSOUND")
            && !out.contains("IF_PROD_FAILED")
            && !out.contains("IF_BRAHMA_FAILED"),
        "a soundness probe fired / a lemma FAILED:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("Static Errors") && !out.contains(": error:"),
        "compile error during proof:\n{out}"
    );
}

/// THE ONLY-IF DIRECTION — CLOSED (0-hyp, aconv-intended, axiom-audited).
///
/// Runs the only-if spine + descent + the caseA fix + an independent verifier
/// add-on (runtime `Theory.all_axioms_of` audit + aconv recheck) as ONE fresh
/// process. Proves (schematic on the Frees `p`,`n`; 0-hyp; aconv the intended):
///
///   prime2 p ⟹ (∃k. p = 4k+3)
///     ⟹ (0<n ∧ ∃a b. n = a²+b²)
///     ⟹ ∃v m. (n = pᵛ·m) ∧ ¬(p∣m) ∧ (∃j. v = j+j)
///
/// i.e. for the GENUINE structural prime p ≡ 3 (mod 4): if 0<n and n is a sum
/// of two squares, then p divides n to an EVEN power (relational valuation, no
/// `vp` constant). The caseA fix (the historic blocker) was dropping the
/// `impI_S2` over-wrap on the `disjE_elimSub` case-arms (oi_casea_seat2.sml) —
/// they were already correct meta-implications.
///
/// Chain: ts_key_lemma.sml (primes_1mod4/euler spine, warm-loads ~27s) +
/// oi_arith.sml (11 arith sub-lemmas) + oi_descent.sml (strong_induct setup +
/// caseB) + oi_casea_seat2.sml (caseA + assembly) + oi_verify.sml (axiom audit
/// + aconv recheck). ~2.8B steps, Tagged(0). Markers: ONLY_IF_CLOSED,
/// OIV_AUDIT_CLEAN (49 axioms, 0 conclusion-mentioning), OIRECHK aconv=true.
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn only_if_direction() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let mut driver = String::new();
    for f in [
        "ts_key_lemma.sml",
        "oi_arith.sml",
        "oi_descent.sml",
        "oi_casea_seat2.sml",
        "oi_verify.sml",
    ] {
        driver
            .push_str(&std::fs::read_to_string(support(f)).unwrap_or_else(|_| panic!("read {f}")));
        driver.push('\n');
    }

    let Some((out, _)) = run_image_env(&image, &driver, 990_000_000_000, ENV) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // The spine warm-loaded and the key only-if lemma is present.
    assert!(
        out.contains("KEY_ONLYIF_OK"),
        "spine / key only-if lemma not OK:\n{out}"
    );
    // caseA (the fix) and caseB both build as the intended meta-implications.
    assert!(
        out.contains("OI_CASEA_OK aconv-impl=true"),
        "caseA did not close:\n{out}"
    );
    assert!(
        out.contains("OI_CASEB_OK aconv-impl=true"),
        "caseB did not close:\n{out}"
    );
    // the strong-induction assembly closes to the intended only_if, 0-hyp + aconv.
    assert!(
        out.contains("ONLY_IF hyps=0 aconv=true"),
        "only_if not 0-hyp / aconv:\n{out}"
    );
    assert!(
        out.contains("ONLY_IF_CLOSED"),
        "only_if direction did not close:\n{out}"
    );
    // soundness: the prime hyp is load-bearing, the conclusion is not collapsed.
    assert!(
        !out.contains("ONLY_IF_FAILED"),
        "an only_if soundness check fired:\n{out}"
    );
    // independent runtime axiom audit: zero conclusion-mentioning axioms.
    assert!(
        out.contains("OIV_AUDIT_CLEAN"),
        "axiom audit not clean:\n{out}"
    );
    assert!(
        out.contains("OIV suspicious_axioms=0"),
        "a suspicious axiom was found:\n{out}"
    );
    // independent aconv recheck.
    assert!(
        out.contains("OIRECHK hyps=0"),
        "aconv recheck: hyps not empty:\n{out}"
    );
    assert!(
        out.contains("OIRECHK aconv_intended=true"),
        "aconv recheck failed:\n{out}"
    );
    // not exceptional.
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("Static Errors") && !out.contains(": error:"),
        "compile error during proof:\n{out}"
    );
}

/// CONCRETE KERNEL SOUNDNESS PROBE — sum-of-two-squares DECISIONS by inference.
///
/// On `with_nt_helpers` (the classical NT foundation: add/mult/Suc/Zero/oeq/
/// oeq_subst/exI/oFalse/Suc_inj/Suc_neq_Zero), NO axiom about sums of two
/// squares. The kernel must:
///   * ACCEPT 2,5,9,13 — prove a witnessed `∃P Q. P²+Q²=n` (hyps=0).
///   * REJECT 3,7,21   — for EVERY candidate (a,b) with a²,b²≤n (a provably
///     COMPLETE finite set, since a²≤a²+b²=n ⟹ a≤⌊√n⌋), derive
///     `oeq (a²+b²) n ⟹ oFalse` by genuine Suc_inj/Suc_neq_Zero peeling, so
///     NO witness exists. `all_refuted=true`, no `REJECT_FAIL`.
/// ~1.6B steps, Tagged(0).
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn concrete_soundness_probe() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let probe = std::fs::read_to_string(support("oi_concrete_probe.sml"))
        .expect("read oi_concrete_probe.sml");

    let Some((out, _)) = run_image_env(&image, &with_nt_helpers(&probe), 990_000_000_000, ENV)
    else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(
        out.contains("PROBE2_HELPERS_OK"),
        "probe helpers failed:\n{out}"
    );
    // ACCEPT — explicit witnesses, 0-hyp.
    for n in [2u32, 5, 9, 13] {
        assert!(
            out.contains(&format!("ACCEPT n={n} ")) && out.contains("hyps=0"),
            "ACCEPT {n} as a sum of two squares failed:\n{out}"
        );
    }
    // REJECT — every candidate refuted.
    for n in [3u32, 7, 21] {
        assert!(
            out.contains(&format!("REJECT n={n} ")) && out.contains("all_refuted=true"),
            "REJECT {n} (not a sum of two squares) failed:\n{out}"
        );
    }
    assert!(
        !out.contains("REJECT_FAIL"),
        "a REJECT candidate was NOT refuted:\n{out}"
    );
    assert!(out.contains("PROBE2_END"), "probe did not finish:\n{out}");
    assert!(
        !out.contains("Exception-"),
        "exception during probe:\n{out}"
    );
    assert!(
        !out.contains("Static Errors") && !out.contains(": error:"),
        "compile error during probe:\n{out}"
    );
}

/// Build the FULL merged if-direction driver: the twosquare monolith (final
/// context `ctxtGR`, which calls `restore_pure_context`), then the banked
/// if-direction machinery (`if_direction.sml`), the mod-4 TRICHOTOMY
/// (`if_trichotomy.sml`), the per-prime-power leaves (`if_perprime.sml`), the
/// VALUATION TRANSFER (`if_valuation.sml`), and finally the strong-induction
/// assembly (`if_full_direction.sml`) [+ the conditional iff `if_iff.sml`].
fn merged_if_driver(extra: &[&str]) -> String {
    let monolith = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/isabelle_support/isabelle_twosquare.sml"),
    )
    .expect("read isabelle_twosquare.sml");
    let mut s = monolith;
    for f in [
        "if_direction.sml",
        "if_trichotomy.sml",
        "if_perprime.sml",
        "if_valuation.sml",
        "if_full_direction.sml",
    ]
    .iter()
    .chain(extra.iter())
    {
        s.push('\n');
        s.push_str(&std::fs::read_to_string(support(f)).unwrap_or_else(|_| panic!("read {f}")));
    }
    s.push('\n');
    s
}

/// THE IF-DIRECTION — CLOSED (0-hyp, aconv-intended, soundness-probed).
///
/// Proves, by strong induction on n on the merged twosquare base `ctxtGR`
/// (schematic n, 0-hyp, only classical = ex_middle):
///
///   if_direction : 0 < n  ==>  H_pred n  ==>  sumsq n
///
/// where  sumsq n  ==  ∃a b. n = a²+b²  and  H_pred n  ==  hpBody n  ==
///   ∀p. prime2 p ⟹ (∃k. p = (((k+k)+k)+k)+3) ⟹ ∀e. (∃m. n=pᵉ·m ∧ ¬p|m)
///                                                          ⟹ ∃j. e = j+j
/// i.e. if every prime p≡3(mod 4) divides n to an EVEN power, n is a sum of two
/// squares (the harder direction of the full Fermat two-square characterization).
///
/// Composition: prime_divisor_exists peels a prime p|n; padic_split gives
/// n = pᵛ·m, ¬p|m (so v≥1, 0<m, m<n); the IH at m (via the banked
/// val_transfer : H survives on the cofactor) gives sumsq m; mod4_trichotomy
/// classifies p (2 / 4k+1 / 4k+3), the three per-prime-power leaves give
/// sumsq pᵛ (the 4k+3 case uses v even from H), and sumsq_mult folds
/// sumsq pᵛ · sumsq m = sumsq n.  0 new axioms over the monolith.
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn if_direction_closed() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver = merged_if_driver(&[]);
    let Some((out, _)) = run_image_env(&image, &driver, 990_000_000_000, ENV) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // merged base + the three banked pieces are present.
    assert!(out.contains("TWOSQ_ALL_OK"), "merged base not OK:\n{out}");
    assert!(
        out.contains("IF_PROD_OK"),
        "if-direction machinery not OK:\n{out}"
    );
    assert!(
        out.contains("TSF_TRICHOTOMY_DONE"),
        "trichotomy not OK:\n{out}"
    );
    assert!(
        out.contains("TSF_PERPRIME_ALL_OK"),
        "per-prime leaves not OK:\n{out}"
    );
    assert!(
        out.contains("VAL_TRANSFER_CLOSED"),
        "valuation transfer not OK:\n{out}"
    );
    // the strong-induction assembly closes to the intended if-direction.
    assert!(
        out.contains("IF_DIRECTION hyps=0 aconv=true"),
        "if_direction not 0-hyp / aconv:\n{out}"
    );
    assert!(
        out.contains("PROBE_OK if_direction keeps 0<n"),
        "soundness probe (keeps 0<n) missing:\n{out}"
    );
    assert!(
        out.contains("PROBE_OK if_direction keeps the even-valuation hypothesis H"),
        "soundness probe (keeps H) missing:\n{out}"
    );
    assert!(
        out.contains("IF_DIRECTION_CLOSED"),
        "if-direction did not close:\n{out}"
    );
    assert!(
        !out.contains("IF_DIRECTION_FAILED") && !out.contains("PROBE_FAIL if_direction"),
        "a soundness probe fired / the if-direction FAILED:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("Static Errors") && !out.contains(": error:"),
        "compile error during proof:\n{out}"
    );
}

/// THE FULL IFF — assembled MODULO the only-if half (the documented merge).
///
/// On the merged base (which carries the PROVED if_direction), with the only-if
/// half taken as an OBJECT-implication hypothesis  Imp (sumsq n) (hpBody n):
///
///   twosquare_full_modulo_onlyif :
///     0 < n  ==>  Imp (sumsq n) (hpBody n)
///            ==>  Conj (Imp (sumsq n) (hpBody n)) (Imp (hpBody n) (sumsq n))
///
/// i.e. GIVEN the only-if half, the full biconditional sumsq n ⟺ hpBody n holds
/// (under 0<n).  The SECOND conjunct is the unconditionally-PROVED if_direction;
/// the first is the assumed only-if.  This is the honest "full iff modulo one
/// named, scoped lemma" — the remaining piece is re-establishing the BANKED
/// `only_if` (currently on the spine context ctxtSub, needing the FLT/key_onlyif
/// sub-tree spliced onto ctxtGR) + valuation UNIQUENESS to upgrade its per-prime
/// EXISTENTIAL even-valuation to the UNIVERSAL `hpBody n`.  0-hyp, aconv-intended,
/// soundness-probed (the second conjunct is genuinely the if-direction, not a
/// copy of the assumed only-if).
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn full_iff_modulo_only_if() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver = merged_if_driver(&["if_iff.sml"]);
    let Some((out, _)) = run_image_env(&image, &driver, 990_000_000_000, ENV) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(
        out.contains("IF_DIRECTION_CLOSED"),
        "if-direction (the second conjunct) not closed:\n{out}"
    );
    assert!(
        out.contains("TSF_IFF hyps=0 aconv=true"),
        "conditional iff not 0-hyp / aconv:\n{out}"
    );
    assert!(
        out.contains("PROBE_OK iff second conjunct is the if-direction"),
        "soundness probe (second conjunct = if-direction) missing:\n{out}"
    );
    assert!(
        out.contains("PROBE_OK iff keeps 0<n"),
        "soundness probe (keeps 0<n) missing:\n{out}"
    );
    assert!(
        out.contains("TSF_IFF_MODULO_ONLYIF_CLOSED"),
        "conditional iff did not close:\n{out}"
    );
    assert!(
        !out.contains("TSF_IFF_FAILED") && !out.contains("PROBE_FAIL iff"),
        "a soundness probe fired / the iff FAILED:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("Static Errors") && !out.contains(": error:"),
        "compile error during proof:\n{out}"
    );
}

/// Build the MERGED full-iff driver (the seat-1 merge): the twosquare monolith
/// (final context `ctxtGR`), the if-direction deltas, the RE-ROOTED spine
/// FLT/binom/key_onlyif sub-tree (`seat1_flt_region_rerooted.sml`, extending
/// `thyGR`), the only-if descent (`oi_arith` / `oi_descent` / `oi_casea_seat2`),
/// the assembly (`seat1_iff_assembly.sml`), and the verifier axiom audit
/// (`seat1_audit.sml`). This is byte-identical to the /tmp/tsf_iff_seat1.sml
/// driver the verifier re-ran (22,620,992,236 steps, Tagged(0)), assembled
/// entirely from the banked resume tree (no /tmp dependency).
fn merged_full_iff_driver() -> String {
    let monolith = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/isabelle_support/isabelle_twosquare.sml"),
    )
    .expect("read isabelle_twosquare.sml");
    let mut s = monolith;
    for f in [
        "if_direction.sml",
        "if_trichotomy.sml",
        "if_perprime.sml",
        "if_valuation.sml",
        "if_full_direction.sml",
        "seat1_flt_region_rerooted.sml",
        "oi_arith.sml",
        "oi_descent.sml",
        "oi_casea_seat2.sml",
        "seat1_iff_assembly.sml",
        "seat1_audit.sml",
    ] {
        s.push('\n');
        s.push_str(&std::fs::read_to_string(support(f)).unwrap_or_else(|_| panic!("read {f}")));
    }
    s.push('\n');
    s
}

/// Build the UNCONDITIONAL full-iff driver: the `merged_full_iff_driver` chain
/// (which closes the only-if half on the merged context `ctxtSub` and the
/// CONDITIONAL modulo-bridge iff), then the BRIDGE SEAT (`bridge_seat2.sml`)
/// that builds `mult_left_cancel` + `valuation_unique` and uses them to discharge
/// the only-if object hypothesis (oiH), assembling the UNCONDITIONAL
/// `twosquare_full`, then the independent VERIFIER add-on (`tsf_verify.sml`,
/// runtime axiom audit of `twosquare_full` + 0-hyp/aconv recheck).
fn merged_full_iff_unconditional_driver() -> String {
    let mut s = merged_full_iff_driver();
    for f in ["bridge_seat2.sml", "tsf_verify.sml"] {
        s.push('\n');
        s.push_str(&std::fs::read_to_string(support(f)).unwrap_or_else(|_| panic!("read {f}")));
    }
    s.push('\n');
    s
}

/// THE FULL IFF — the MERGE SEAT (only-if PROVED on the merged context `ctxtGR`,
/// the iff assembled MODULO the existential→universal valuation bridge).
///
/// This is the strongest banked artifact of the full-iff campaign and the SOLE
/// FULL-IFF DRIVER for human review. It runs the documented hard splice in ONE
/// process on the merged twosquare base:
///
///   * `twosquare` (the monolith) and the unconditional `if_direction`
///     (0<n ⟹ hpBody n ⟹ sumsq n) on `ctxtGR`;
///   * the spine FLT / binom / `key_onlyif` sub-tree RE-ROOTED onto `thyGR`
///     (`ctxtSub` extends `thyGR`), giving `key_onlyif` and then `only_if` on the
///     MERGED context:
///       prime2 p ⟹ (∃k. p=4k+3) ⟹ (0<n ∧ sumsq n)
///         ⟹ ∃v m. n=pᵛ·m ∧ ¬(p|m) ∧ ∃j. v=j+j     (per-prime EXISTENTIAL valuation)
///   * the iff `twosquare_full_seat1_modulo_bridge`, assembled on `ctxtGR`:
///       0<n ⟹ Imp(sumsq n)(hpBody n)
///            ⟹ Conj(Imp(sumsq n)(hpBody n))(Imp(hpBody n)(sumsq n))
///     0-hyp, aconv the (conditional) biconditional, second conjunct = the
///     PROVED unconditional if_direction.
///   * a runtime `Theory.all_axioms_of` axiom audit (`seat1_audit.sml`): ZERO
///     conclusion-mentioning axioms in either the only_if or the iff theory;
///     the only classical axiom is `ex_middle`.
///
/// HONEST SCOPE — NOT the unconditional biconditional. The proved iff takes the
/// only-if half (`Imp (sumsq n) (hpBody n)`) as a SCOPED OBJECT HYPOTHESIS,
/// because the genuinely-proved `only_if` is in the per-prime EXISTENTIAL
/// even-valuation form, while `hpBody`'s inner clause is the UNIVERSAL
/// `∀e. vpred p n e ⟹ even e`. Bridging existential→universal needs valuation
/// UNIQUENESS (`vpred p n e₁ ⟹ vpred p n e₂ ⟹ e₁=e₂`), which in turn needs
/// `mult_left_cancel` (cancel a positive p-power) — NOT in the monolith (only
/// `add_left_cancel` is). That is the SINGLE remaining contained sub-development;
/// the splice (only_if on `ctxtGR`) and the mkConj shape are DONE.
///
/// ~22.6B steps, Tagged(0). Markers: ONLY_IF_CLOSED, SEAT1_SUBTHY_OK,
/// TSF_SEAT1_IFF_MODULO_BRIDGE_CLOSED, SEAT1_AUDIT_CLEAN.
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh); ~22.6B steps / ~12 min"]
fn full_iff_merge_seat() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver = merged_full_iff_driver();
    let Some((out, _)) = run_image_env(&image, &driver, 990_000_000_000, ENV) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // merged base + if-direction (the second iff conjunct, unconditional).
    assert!(out.contains("TWOSQ_ALL_OK"), "merged base not OK:\n{out}");
    assert!(
        out.contains("IF_DIRECTION hyps=0 aconv=true") && out.contains("IF_DIRECTION_CLOSED"),
        "if-direction (second conjunct) not closed 0-hyp/aconv:\n{out}"
    );
    // the FLT/key_onlyif sub-tree spliced onto thyGR + the only-if descent.
    assert!(
        out.contains("KEY_ONLYIF_OK") && out.contains("KEY hyps=0 aconv=true"),
        "key_onlyif not proved on the merged context:\n{out}"
    );
    assert!(
        out.contains("ONLY_IF hyps=0 aconv=true") && out.contains("ONLY_IF_CLOSED"),
        "only_if not closed 0-hyp/aconv on the merged context:\n{out}"
    );
    // the merge backbone: only_if lives ABOVE thyGR (the splice succeeded).
    assert!(
        out.contains("SEAT1_SUBTHY_OK"),
        "only_if is NOT above thyGR — the FLT splice did not compose:\n{out}"
    );
    assert!(
        out.contains("SEAT1_CTXT_COMPAT_OK") && out.contains("SEAT1_ONLYIF_ON_SUB_OK"),
        "merged-context compatibility checks failed:\n{out}"
    );
    // the conditional (modulo-bridge) biconditional, 0-hyp + aconv + probed.
    assert!(
        out.contains("TSF_SEAT1_IFF hyps=0 aconv=true"),
        "modulo-bridge iff not 0-hyp/aconv:\n{out}"
    );
    assert!(
        out.contains("PROBE_OK seat1 iff second conjunct is the if-direction (R==>L)"),
        "soundness probe (second conjunct = if-direction) missing:\n{out}"
    );
    assert!(
        out.contains("PROBE_OK seat1 iff keeps 0<n"),
        "soundness probe (keeps 0<n) missing:\n{out}"
    );
    assert!(
        out.contains("TSF_SEAT1_IFF_MODULO_BRIDGE_CLOSED"),
        "modulo-bridge iff did not close:\n{out}"
    );
    // runtime axiom audit: ZERO conclusion-mentioning axioms in either theory.
    assert!(
        out.contains("SEAT1_AUDIT_CLEAN"),
        "axiom audit not clean (a conclusion-mentioning axiom found):\n{out}"
    );
    assert!(
        out.contains("SEAT1_AUDIT[only_if] suspicious_axioms=0")
            && out.contains("SEAT1_AUDIT[modulo_bridge_iff] suspicious_axioms=0"),
        "a suspicious axiom was found:\n{out}"
    );
    // not degenerate / exceptional.
    assert!(
        !out.contains("TSF_SEAT1_IFF_FAILED")
            && !out.contains("ONLY_IF_FAILED")
            && !out.contains("PROBE_FAIL")
            && !out.contains("SEAT1_AUDIT_DIRTY"),
        "a soundness probe fired / a lemma FAILED:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("Static Errors") && !out.contains(": error:"),
        "compile error during proof:\n{out}"
    );
}

/// THE FULL IFF — UNCONDITIONAL (Fermat's two-square characterization, both
/// directions, no scoped hypothesis).
///
/// Runs the `merged_full_iff_driver` chain (which proves the only-if half
/// `only_if` on the merged context and the CONDITIONAL modulo-bridge iff), then
/// the BRIDGE SEAT (`bridge_seat2.sml`), which closes the documented final gap:
///
///   * `mult_left_cancel` : 0<p ⟹ p·a = p·b ⟹ a = b  (from scratch on
///     `ctxtGR`, via le_total + left_distrib + add_left_cancel + a from-scratch
///     `mult_eq_zero`; NO hard induction);
///   * `valuation_unique` : prime2 p ⟹ 0<n ⟹ vpred p n e₁ ⟹ vpred p n e₂
///     ⟹ e₁ = e₂  (uniqueness of the p-adic valuation, by `mult_left_cancel` +
///     `pow_add`, ruling out a surplus p-factor against ¬p|m);
///   * the BRIDGE `oiH_thm` : 0<n ⟹ Imp (sumsq n) (hpBody n) — a THEOREM:
///     instantiate `only_if` (per-prime EXISTENTIAL even valuation ∃v) under
///     hpBody's premises, then transfer `even v` to the UNIVERSAL inner `e` by
///     `valuation_unique`; allI over e and p gives `hpBody n`;
///   * the DISCHARGE: feed `oiH_thm` (now PROVED) + the unconditional
///     `if_direction` to the same mkConj, giving the UNCONDITIONAL
///       twosquare_full : 0<n ⟹ Conj (Imp (sumsq n) (hpBody n))
///                                    (Imp (hpBody n) (sumsq n))
///     where sumsq n == ∃a b. n = a²+b² and hpBody n == every prime p≡3(mod 4)
///     divides n to an EVEN power. The only-if hypothesis is GONE.
///
/// Then the independent VERIFIER add-on (`tsf_verify.sml`) re-checks 0-hyp /
/// aconv the full biconditional / unconditional, and runs a runtime
/// `Theory.all_axioms_of` audit on `twosquare_full`'s theory (ZERO
/// conclusion-mentioning axioms; only classical = ex_middle). 0 new
/// axioms/consts/types over the merged base. ~22.7B steps, Tagged(0).
///
/// Markers: TWOSQUARE_FULL_OK, the three twosquare_full PROBE_OK lines,
/// TSFV_RECHECK_OK, TSFV_AUDIT_CLEAN.
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh); ~22.7B steps / ~12 min"]
fn full_iff_unconditional() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver = merged_full_iff_unconditional_driver();
    let Some((out, _)) = run_image_env(&image, &driver, 990_000_000_000, ENV) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // merged base + both halves coexist (only-if proved, if-direction proved).
    assert!(out.contains("TWOSQ_ALL_OK"), "merged base not OK:\n{out}");
    assert!(
        out.contains("ONLY_IF hyps=0 aconv=true") && out.contains("ONLY_IF_CLOSED"),
        "only_if not closed on the merged context:\n{out}"
    );
    assert!(
        out.contains("IF_DIRECTION hyps=0 aconv=true") && out.contains("IF_DIRECTION_CLOSED"),
        "if-direction not closed:\n{out}"
    );
    // the bridge sub-development.
    assert!(
        out.contains("MULT_LEFT_CANCEL hyps=0"),
        "mult_left_cancel not 0-hyp:\n{out}"
    );
    assert!(
        out.contains("VALUATION_UNIQUE hyps=0") && out.contains("VALUATION_UNIQUE aconv=true"),
        "valuation_unique not 0-hyp / aconv:\n{out}"
    );
    assert!(
        out.contains("PROBE_OK valuation_unique keeps prime2 p")
            && out.contains("PROBE_OK valuation_unique concludes oeq e1 e2 (not e1 e1)"),
        "valuation_unique soundness probes missing:\n{out}"
    );
    assert!(
        out.contains("OIH_THM hyps=0") && out.contains("OIH_THM aconv=true"),
        "the bridge oiH_thm not 0-hyp / aconv:\n{out}"
    );
    // THE DELIVERABLE: the UNCONDITIONAL full biconditional, 0-hyp + aconv.
    assert!(
        out.contains("TWOSQUARE_FULL hyps=0 aconv=true"),
        "twosquare_full not 0-hyp / aconv the full biconditional:\n{out}"
    );
    // the only-if hypothesis (oiH) is GONE — the iff is unconditional.
    assert!(
        out.contains("PROBE_OK twosquare_full is UNCONDITIONAL (no Imp L R hypothesis)"),
        "soundness probe (unconditional, oiH gone) missing:\n{out}"
    );
    assert!(
        out.contains("PROBE_OK twosquare_full second conjunct is R==>L (genuine iff)"),
        "soundness probe (second conjunct = if-direction) missing:\n{out}"
    );
    assert!(
        out.contains("PROBE_OK twosquare_full keeps 0<n"),
        "soundness probe (keeps 0<n) missing:\n{out}"
    );
    assert!(
        out.contains("TWOSQUARE_FULL_OK"),
        "the unconditional twosquare_full did not close:\n{out}"
    );
    // independent verifier recheck + runtime axiom audit on twosquare_full.
    assert!(
        out.contains("TSFV recheck hyps=0 aconv_intended=true"),
        "verifier recheck (0-hyp / aconv) failed:\n{out}"
    );
    assert!(
        out.contains("TSFV recheck UNCONDITIONAL (no Imp L R hypothesis)")
            && out.contains("TSFV_RECHECK_OK"),
        "verifier unconditional recheck failed:\n{out}"
    );
    assert!(
        out.contains("TSFV_AUDIT suspicious_axioms=0") && out.contains("TSFV_AUDIT_CLEAN"),
        "runtime axiom audit on twosquare_full not clean:\n{out}"
    );
    // not degenerate / exceptional.
    assert!(
        !out.contains("TWOSQUARE_FULL_FAILED")
            && !out.contains("TSFV_RECHECK_FAIL")
            && !out.contains("TSFV_AUDIT_DIRTY")
            && !out.contains("PROBE_FAIL"),
        "a soundness probe fired / a lemma FAILED:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("Static Errors") && !out.contains(": error:"),
        "compile error during proof:\n{out}"
    );
}
