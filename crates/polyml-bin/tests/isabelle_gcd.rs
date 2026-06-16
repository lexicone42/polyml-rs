//! THE EUCLIDEAN ALGORITHM — gcd universal property, BEZOUT'S IDENTITY, and the
//! MODULAR INVERSE, in Isabelle/Pure on the polyml-rs interpreter.
//!
//!   gcd_props      : ⊢ ∀a b. ∃g. g∣a ∧ g∣b ∧ (∀d. d∣a ⟹ d∣b ⟹ d∣g)
//!   bezout         : ⊢ ∀a b. ∃g. (g the gcd) ∧ (∃x y. a·x = b·y + g ∨ b·y = a·x + g)
//!   coprime_bezout : ⊢ (∀d. d∣a ⟹ d∣b ⟹ d=1) ⟹ ∃x y. a·x = b·y + 1 ∨ b·y = a·x + 1
//!   mod_inverse    : ⊢ prime p ⟹ ¬(p∣a) ⟹ ∃b. cong p (a·b) 1
//!
//! Closes the gap the rest of the tower deliberately sidestepped ("gcd/Bezout
//! needs integers over ℕ"): all four are proved as PURE EXISTENTIALS over the
//! existing theory (no new constant, no new axiom), by genuine LCF kernel
//! inference, driven by the already-proved division theorem (`div_mod_exists`)
//! through a strong induction. Two-sided ℕ form throughout (no subtraction).
//!
//! Built on the unified number-theory base (`isabelle_ntbase.sml`, spliced in by
//! `common::with_ntbase`). Proved by a 3-phase ultracode fleet (wf_a420c57e-d18):
//! gcd-props → bezout → coprime/inverse, each phase a multi-seat race feeding the
//! next; re-verified end-to-end by hand before landing.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_gcd -- --ignored --nocapture
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
fn gcd_bezout_modular_inverse() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/isabelle_support/isabelle_gcd.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_gcd.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_ntbase(&driver),
        600_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // the unified base must load first
    assert!(
        out.contains("NT_BASE_OK"),
        "unified ntbase did not load:\n{out}"
    );
    // each rung of the ladder, by its named lemma + its phase-completion marker
    for (lemma, marker) in [
        ("gcd_props", "GCD_PROPS_OK"),
        ("bezout", "BEZOUT_OK"),
        ("coprime_bezout", "COPRIME_BEZOUT_OK"),
        ("mod_inverse", "MOD_INVERSE_OK"),
    ] {
        assert!(
            out.contains(&format!("OK {lemma}")),
            "lemma `{lemma}` did not check:\n{out}"
        );
        assert!(out.contains(marker), "marker `{marker}` missing:\n{out}");
    }
    // no kernel failure and no soundness probe firing
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
