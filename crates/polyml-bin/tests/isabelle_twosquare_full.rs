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
