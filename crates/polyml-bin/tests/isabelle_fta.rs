//! FUNDAMENTAL THEOREM OF ARITHMETIC (existence) in Isabelle/Pure on the polyml-rs
//! interpreter — the finale that fuses the list theory with the primes machinery.
//!
//!     fta_existence : ⊢ ∀n. 2 ≤ n ⟹ ∃ps. all_prime ps ∧ product ps = n
//!
//! Every natural number n ≥ 2 is a product of primes. A 0-hypothesis theorem by
//! strong (course-of-values) induction; only classical assumption = excluded middle.
//! Combines the LIST theory (inductive `natlist` + `product` + `all_prime`) with the
//! classical PRIME theory (derived `prime_cases`).
//!
//! Proof: strong induction on n; `prime_cases` splits 1<n into prime (singleton list)
//! or composite — a proper divisor d (via `cofactor`) yields n = d·e with d,e<n, so the
//! strong IH gives prime-lists for d and e; append them (`product_append`,
//! `all_prime_append`) → a prime-list with product n.
//!
//! Built on `isabelle_classical_primes.sml` by a 2-phase ultracode pipeline
//! (wf_15cdc379-e01): list/product helpers → FTA (2 seats, both proved it). With
//! `isabelle_euclid` (infinitely many primes) and `isabelle_sqrt2` (√2 irrational),
//! this completes a genuine elementary number theory from first principles on the
//! Rust PolyML interpreter.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_fta -- --ignored --nocapture
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
fn fundamental_theorem_of_arithmetic_existence() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/isabelle_support/isabelle_fta.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_fta.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_sound_audit(&common::with_nt_helpers(&driver), "fta", &["fta_existence"]),
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

    // the list/product helpers (the engine of the composite case)
    for lemma in ["product_append", "all_prime_append", "cofactor"] {
        assert!(
            out.contains(&format!("OK {lemma}")),
            "FTA helper `{lemma}` did not check:\n{out}"
        );
    }
    // FTA existence: every n >= 2 is a product of primes (0-hyp, by strong induction)
    assert!(
        out.contains("OK fta_existence"),
        "FTA (existence) did not check:\n{out}"
    );
    assert!(
        out.contains("FTA_DONE"),
        "FTA development did not complete:\n{out}"
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
        out.contains("SOUND_AUDIT_OK fta"),
        "soundness audit did not certify fta:\n{out}"
    );
}
