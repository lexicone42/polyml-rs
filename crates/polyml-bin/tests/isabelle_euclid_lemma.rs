//! EUCLID'S LEMMA over the naturals, in Isabelle/Pure on the polyml-rs interpreter
//! — Stage 2 of the FTA-uniqueness arc.
//!
//!   euclid_lemma : ⊢ prime p ⟹ p ∣ a·b ⟹ p∣a ∨ p∣b
//!
//! A prime dividing a product divides one of the factors. 0-hypothesis, over the
//! STRUCTURAL prime; only classical assumption = excluded middle. Proved by the
//! GAUSS DESCENT — no gcd, no Bézout, no integers: `bounded_euclid` (a<p) by strong
//! induction (divide p by a, `dvd_diff` to get p∣r·b, recurse at r<a), then the
//! general lemma by reducing a mod p. Rests on the Stage-1 division theorem plus
//! `dvd_diff` / `prime_not_dvd_pos_lt` / `mult_le_mono` / `dvd_mult_assoc_l`.
//!
//! Built by a 2-phase ultracode pipeline (wf_904dd5f8-976): helpers → euclid_lemma
//! (3 seats, all proved it). The crux of FTA uniqueness; Stages 3-4 (list form →
//! uniqueness) remain (task #75).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_euclid_lemma -- --ignored --nocapture
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
fn euclids_lemma_prime_divides_product() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_euclid_lemma.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_euclid_lemma.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_sound_audit(
            &common::with_nt_helpers(&driver),
            "euclid_lemma",
            &["euclid_lemma"],
        ),
        250_000_000_000,
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
        out.contains("OK bounded_euclid"),
        "bounded Euclid (a<p) did not check:\n{out}"
    );
    assert!(
        out.contains("OK euclid_lemma"),
        "Euclid's lemma did not check:\n{out}"
    );
    assert!(
        out.contains("EUCLID_LEMMA_DONE"),
        "Euclid-lemma development did not complete:\n{out}"
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
        out.contains("SOUND_AUDIT_OK euclid_lemma"),
        "soundness audit did not certify euclid_lemma:\n{out}"
    );
}
