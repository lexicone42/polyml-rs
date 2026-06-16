//! THE MULTIPLICATIVE GROUP MOD p — the Wilson keystones — in Isabelle/Pure on
//! the polyml-rs interpreter.
//!
//!   inverse_unique : ⊢ cong p (a·b) 1 ⟹ cong p (a·c) 1 ⟹ cong p b c
//!   mod_cancel     : ⊢ prime p ⟹ ¬(p∣a) ⟹ cong p (a·b) (a·c) ⟹ cong p b c
//!   lagrange_roots : ⊢ prime p ⟹ cong p (a·a) 1 ⟹ (cong p a 1 ∨ cong p (Suc a) 0)
//!
//! The algebraic core of (ℤ/pℤ)*: uniqueness of the modular inverse (a pure
//! congruence chain), cancellation by a unit (via Euclid's lemma), and Lagrange's
//! theorem on square roots of unity — the only square roots of 1 mod a prime are
//! ±1 (−1 expressed as Suc a ≡ 0, so no truncated subtraction). Each a 0-hyp
//! theorem by genuine kernel inference, with a soundness probe.
//!
//! These are the algebraic heart of Wilson's theorem. Built on the full gcd /
//! Bézout / Euclid-lemma development (`isabelle_gcd.sml` + ntbase) over the
//! classical foundation, spliced in by `common::with_gcd`. Proved by a multi-seat
//! ultracode fleet (wf_3eef19b5-87f); re-verified end-to-end by hand.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_mult_group -- --ignored --nocapture
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
fn multiplicative_group_mod_p() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_mult_group.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_mult_group.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_gcd(&driver),
        700_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // the gcd / Euclid-lemma base must load first
    assert!(
        out.contains("MOD_INVERSE_OK"),
        "gcd/Euclid base did not load:\n{out}"
    );
    for (lemma, marker) in [
        ("inverse_unique", "INVERSE_UNIQUE_OK"),
        ("mod_cancel", "MOD_CANCEL_OK"),
        ("lagrange_roots", "LAGRANGE_ROOTS_OK"),
    ] {
        assert!(
            out.contains(&format!("OK {lemma}")),
            "lemma `{lemma}` did not check:\n{out}"
        );
        assert!(out.contains(marker), "marker `{marker}` missing:\n{out}");
    }
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("PROBE_UNSOUND"),
        "a soundness probe fired UNSOUND:\n{out}"
    );
    assert!(!out.contains("UNSOUND"), "an UNSOUND marker fired:\n{out}");
}
