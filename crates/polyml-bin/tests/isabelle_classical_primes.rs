//! CLASSICAL FOL + the GENUINE "every n ≥ 2 has a prime divisor" in Isabelle/Pure
//! on the polyml-rs interpreter — the honest completion of the primes capstone.
//!
//! This SUPERSEDES the caveated capstone in `isabelle_primes.rs` (which assumed an
//! abstract-prime `prime_cases` axiom). Here the case-split is DERIVED, so the
//! theorem is genuine, over the STRUCTURAL prime definition. On the full
//! self-derived number-theory ladder, this driver:
//!
//!  1. Makes the object logic CLASSICAL — adds object `Imp`/`Conj`/`Forall` +
//!     ONE classical axiom, excluded middle `⊢ A ∨ ¬A`, then DERIVES the standard
//!     classical lemmas (each 0-extra-hyp, aconv-checked):
//!       dbl_neg `¬¬A ⟹ A`, deMorgan_or `¬(A∨B) ⟹ ¬A∧¬B`,
//!       not_imp `¬(A⟶B) ⟹ A∧¬B`, not_forall `¬(∀x.P x) ⟹ ∃x.¬P x`.
//!  2. Adds the strict order + num facts + strong (course-of-values) induction +
//!     the STRUCTURAL `prime p ≝ 1<p ∧ (∀d. d∣p ⟹ d=1 ∨ d=p)`.
//!  3. DERIVES the primality case-split (NOT an axiom this time):
//!       prime_cases `⊢ 1<n ⟹ prime n ∨ (∃d. 1<d ∧ d<n ∧ d∣n)`
//!     from excluded middle + the structural prime + `dvd_le` + the classical lemmas.
//!  4. Proves the GENUINE capstone BY STRONG INDUCTION:
//!       prime_divisor_exists `⊢ 2≤n ⟹ ∃p. prime p ∧ p∣n`   (structural prime).
//!     The only classical assumption is excluded middle (which real Isabelle/HOL
//!     object logics have). Soundness probes confirm the kernel rejects false
//!     variants. This is a real, named number-theory theorem proved from a single
//!     classical axiom on our Rust runtime.
//!
//! Engineered by a 4-phase ultracode pipeline (wf_26188260-4af): classical FOL →
//! NT connectors + strong induction → prime_cases (3 seats, ALL derived it) →
//! capstone (2 seats, BOTH proved it). Each phase validated on the checkpoint.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_classical_primes -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use std::path::PathBuf;

fn checkpoint() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/isabelle_pure");
    p.exists().then_some(p)
}

#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn classical_fol_and_genuine_prime_divisor_theorem() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_classical_primes.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_classical_primes.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        240_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // classical FOL derived from the single excluded-middle axiom
    for lemma in ["dbl_neg", "deMorgan_or", "not_imp", "not_forall"] {
        assert!(out.contains(&format!("OK {lemma}")), "classical lemma `{lemma}` did not check:\n{out}");
    }
    // strong (course-of-values) induction
    assert!(out.contains("OK strong_induct"), "strong induction did not check:\n{out}");
    // the DERIVED primality case-split (the keystone that was an axiom before)
    assert!(out.contains("OK prime_cases"), "prime_cases was not DERIVED:\n{out}");
    // the GENUINE capstone, structural prime, no abstract-prime axiom
    assert!(
        out.contains("OK prime_divisor_exists"),
        "genuine prime-divisor theorem did not check:\n{out}"
    );
    assert!(out.contains("CAPSTONE_DONE"), "capstone development did not complete:\n{out}");
    assert!(!out.contains("Exception-"), "exception during proof:\n{out}");
    assert!(!out.contains("UNSOUND"), "a soundness probe fired UNSOUND:\n{out}");
}
