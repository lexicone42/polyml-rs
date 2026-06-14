//! EUCLID'S LEMMA FOR LISTS in Isabelle/Pure on the polyml-rs interpreter — Stage 3
//! of the FTA-uniqueness arc, and the key lemma for the uniqueness argument.
//!
//!   prime_in_prime_list : ⊢ prime p ⟹ all_prime ps ⟹ p ∣ product ps ⟹ in_list p ps
//!
//! A prime dividing the product of a list of primes IS one of them. 0-hypothesis;
//! only classical assumption = excluded middle. Re-derives the list machinery
//! (natlist + product + all_prime + a membership predicate `in_list`) on the Stage-2
//! Euclid-lemma base, proves `prime_div_eq` (two primes, p∣q ⟹ p=q), then the headline
//! by list induction on `euclid_lemma` (product (Cons h t) = h·∏t; split p∣h·∏t into
//! p∣h ⟹ p=h ⟹ in_list, or p∣∏t ⟹ IH).
//!
//! Built on `isabelle_euclid_lemma.sml` by a 2-phase ultracode pipeline
//! (wf_1b8fb713-66f): list foundation + prime_div_eq → prime_in_prime_list (3 seats,
//! all proved it). Stage 3 of 4 (task #75); Stage 4 = the uniqueness count argument.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_euclid_list -- --ignored --nocapture
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
fn prime_dividing_product_of_primes_is_one_of_them() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_euclid_list.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_euclid_list.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        280_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(out.contains("OK prime_div_eq"), "prime_div_eq (two primes p|q => p=q) did not check:\n{out}");
    assert!(
        out.contains("OK prime_in_prime_list"),
        "Euclid's lemma for lists did not check:\n{out}"
    );
    assert!(out.contains("PRIME_IN_LIST_DONE"), "Stage-3 development did not complete:\n{out}");
    assert!(!out.contains("Exception-"), "exception during proof:\n{out}");
}
