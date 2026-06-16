//! EUCLID'S THEOREM — the infinitude of primes — proved in Isabelle/Pure on the
//! polyml-rs interpreter. The grand capstone of the self-derived number-theory
//! ladder.
//!
//!     euclid : ⊢ ∀n. ∃p. prime p ∧ n < p
//!
//! For every natural number n there is a prime p strictly greater than n — there
//! are infinitely many primes. A 0-hypothesis theorem over the STRUCTURAL prime
//! (`prime p ≝ 1<p ∧ ∀d. d∣p ⟹ d=1 ∨ d=p`), proved by genuine LCF kernel
//! inference; the only classical assumption in the whole development is excluded
//! middle (which real Isabelle/HOL object logics have).
//!
//! Proof (classical Euclid): given n, let N = n!+1 (≥2 by `fact_pos`). By the
//! genuine `prime_divisor_exists`, N has a prime divisor p. If p ≤ n then `dvd_fact`
//! gives p∣n! and also p∣N=n!+1; but a prime cannot divide two consecutive numbers
//! (`consec_coprime`), contradiction — so p > n. Generalise over n.
//!
//! Top of the ladder: object logic → Peano → semiring → summation → order →
//! divisibility → strong induction → classical FOL → genuine prime-divisor →
//! EUCLID. Built on `isabelle_classical_primes.sml` by a 3-phase ultracode pipeline
//! (wf_a72a4b68-c26): helpers → consec_coprime (3 seats all derived it) → Euclid
//! (2 seats both proved it).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_euclid -- --ignored --nocapture
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
fn euclid_infinitude_of_primes() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_euclid.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_euclid.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_nt_helpers(&driver),
        300_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // the supporting lemmas (factorial positivity, p|n!, consecutive-coprimality)
    for lemma in ["fact_pos", "dvd_fact", "consec_coprime"] {
        assert!(
            out.contains(&format!("OK {lemma}")),
            "supporting lemma `{lemma}` did not check:\n{out}"
        );
    }
    // EUCLID: forall n, exists a prime p with n < p (structural prime, 0-hyp)
    assert!(
        out.contains("OK euclid"),
        "Euclid's theorem (infinitude of primes) did not check:\n{out}"
    );
    assert!(
        out.contains("EUCLID_DONE"),
        "Euclid development did not complete:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("UNSOUND"),
        "a soundness probe fired UNSOUND:\n{out}"
    );
}
