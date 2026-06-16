//! STRONG (course-of-values) INDUCTION + the STRICT LINEAR ORDER + PRIMALITY in
//! Isabelle/Pure on the polyml-rs interpreter — the top of the self-built
//! number-theory ladder (object logic → Peano → semiring → summation → order →
//! divisibility → HERE).
//!
//! FULLY GENUINE results (0-hypothesis theorems, pure LCF kernel inference, no
//! extra axioms beyond the Peano/discrimination set already in the ladder):
//!   strong_induct   course-of-values induction, DERIVED from `nat_induct` + the
//!                   strict order: `(⋀n. (⋀m. m<n ⟹ P m) ⟹ P n) ⟹ ⋀n. P n`.
//!                   This is the headline — a new induction principle built from
//!                   scratch, the tool that unlocks everything harder.
//!   lt_trans, lt_trichotomy   the STRICT LINEAR order (`m<n ∨ m=n ∨ n<m`),
//!                   `m<n ≝ Suc m ≤ n`.
//!   prime_two       `⊢ prime 2`  — 2 is prime, for the STRUCTURAL definition
//!                   `prime p ≝ 1<p ∧ (∀d. d∣p ⟹ d=1 ∨ d=p)`.
//!   prime_gt_1      `⊢ prime p ⟹ 1 < p`.
//!
//! CAPSTONE WITH A DISCLOSED ASSUMPTION:
//!   prime_divisor_exists  `⊢ 2 ≤ n ⟹ ∃p. prime p ∧ p∣n` — "every n ≥ 2 has a
//!   prime divisor", proved BY strong induction + `dvd_trans` chaining. The
//!   *structure* of the proof (the strong induction, the witnessing, `dvd_trans`)
//!   is genuine kernel inference, but it rests on a CLASSICAL AXIOM `prime_cases`
//!   (`1<n ⟹ prime n ∨ ∃d. 1<d<n ∧ d∣n`) over an ABSTRACT `prime` predicate —
//!   NOT the structural `prime` above. Pure's object logic here is intuitionistic
//!   (no excluded middle), so this case-split cannot be derived; in real
//!   Isabelle/HOL it is a lemma from EM + the structural definition + `dvd_le`.
//!   So treat the capstone as "every n≥2 has a prime divisor, MODULO the classical
//!   primality case-split" — a demonstration that the strong-induction machinery
//!   reaches it, not a from-first-principles proof. Principled follow-up: add a
//!   single excluded-middle axiom and DERIVE `prime_cases` from the structural
//!   `prime` + `dvd_le`, unifying the two `prime`s.
//!
//! Engineered by a foundation→fan-out→merge ultracode workflow (wf_968ad1d0-b77):
//! foundation (strict order + its basics) + four seats (strong induction, the
//! strict linear order, primality, the capstone) + a merge agent. Each seat
//! verified on the checkpoint; the capstone's axiom dependency is disclosed above.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_primes -- --ignored --nocapture
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
fn strong_induction_strict_order_and_primality() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_primes.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_primes.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        220_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // The fully-genuine results (no axioms beyond the ladder's Peano/discrimination
    // set). strong_induct is the headline: course-of-values induction derived from
    // nat_induct + the strict order.
    for thm in [
        "strong_induct",
        "lt_trans",
        "lt_trichotomy",
        "prime_two",
        "prime_gt_1",
    ] {
        assert!(
            out.contains(&format!("OK {thm}")),
            "genuine theorem `{thm}` did not check:\n{out}"
        );
    }
    // The capstone — proved by strong induction MODULO the classical `prime_cases`
    // axiom (see the module doc). The driver derives it; we assert it checks, but
    // its status is "modulo a disclosed classical axiom", not from first principles.
    assert!(
        out.contains("OK prime_divisor_exists"),
        "capstone `prime_divisor_exists` (modulo prime_cases) did not check:\n{out}"
    );
    assert!(
        out.contains("PRIME_DONE"),
        "prime development did not complete:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
}
