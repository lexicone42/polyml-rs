//! FUNDAMENTAL THEOREM OF ARITHMETIC — UNIQUENESS, in Isabelle/Pure on the polyml-rs
//! interpreter. Stage 4 (finale) of the FTA-uniqueness arc.
//!
//!   fta_unique : ⊢ all_prime ps ⟹ all_prime qs ⟹ product ps = product qs
//!                     ⟹ ∀r. count r ps = count r qs
//!
//! Two prime factorisations of the same number are the SAME multiset (every value
//! occurs equally often). Together with FTA *existence* (`isabelle_fta.rs`), this is
//! the full Fundamental Theorem of Arithmetic, proved from first principles (only
//! classical assumption = excluded middle) on a Rust reimplementation of PolyML.
//!
//! The 4-stage arc: division theorem → Euclid's lemma (Gauss descent, no gcd) →
//! Euclid's lemma for lists → UNIQUENESS. This stage adds `count`/`remove1` (via
//! conditional defining axioms + `ex_middle` case-splits) and the bridging lemmas
//! (`product_remove1`, `count_remove1_self/other`, `all_prime_remove1`,
//! `mult_left_cancel`, `product_one_nil`), then proves `fta_unique` by list induction
//! on `prime_in_prime_list`: a prime of `ps` is in `qs`, remove one copy, cancel it
//! from the product, recurse.
//!
//! Built on `isabelle_euclid_list.sml` by a 2-phase ultracode pipeline
//! (wf_20445576-234): count/remove1 layer → fta_unique (3 seats, all proved it).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_fta_unique -- --ignored --nocapture
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
fn fta_uniqueness_prime_factorisations_have_same_multiset() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_fta_unique.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_fta_unique.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_sound_audit(&driver, "fta_unique", &["fta_unique"]),
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

    assert!(
        out.contains("OK fta_unique"),
        "FTA uniqueness did not check:\n{out}"
    );
    assert!(
        out.contains("FTA_UNIQUE_DONE"),
        "FTA-uniqueness development did not complete:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("UNSOUND"),
        "a soundness probe fired UNSOUND:\n{out}"
    );
    assert!(
        out.contains("SOUND_AUDIT_OK fta_unique"),
        "soundness audit did not certify fta_unique:\n{out}"
    );
}
