//! EULER'S CRITERION (the ±1 dichotomy + QR-forward) in Isabelle/Pure on the
//! polyml-rs interpreter.
//!
//!   dichotomy  : ⊢ prime2 p ⟹ ¬(p∣a) ⟹ (p−1 = m+m) ⟹
//!                    cong p (pow a m) 1  ∨  cong p (Suc (pow a m)) 0
//!   qr_forward : ⊢ prime2 p ⟹ ¬(p∣a) ⟹ (p−1 = m+m) ⟹ (∃x. cong p (x·x) a) ⟹
//!                    cong p (pow a m) 1
//!
//! i.e. for an ODD prime p (p−1 = 2m) coprime to a: a^((p−1)/2) ≡ ±1 (mod p)
//! (−1 written as Suc(a^m)≡0 to avoid truncated ℕ subtraction), and a quadratic
//! residue forces the +1 case. Both 0-hypothesis theorems by genuine LCF kernel
//! inference; only classical assumption = `ex_middle`. `prime2` is the genuine
//! structural prime (never the buggy legacy `prime`).
//!
//! Proof: y = a^m, y·y = a^(m+m) = a^(p−1) ≡ 1 (Fermat-for-units `apm1`, from
//! `flt` + `mod_cancel`), so by `lagrange_roots` (the only square roots of 1 mod
//! a prime are ±1) y ≡ 1 ∨ y ≡ −1. QR-forward: a ≡ x² ⟹ a^m ≡ x^(p−1) ≡ 1.
//!
//! Base composition (the hard part): Fermat and `lagrange_roots` live in
//! different tower branches; the foundation re-derives `mod_cancel`/
//! `lagrange_roots` on the `isabelle_flt.sml` base (both euclid_lemma-based) so
//! all three (Fermat-power algebra + lagrange + pow/cong) coexist in one
//! context. Built by a foundation→3-seat→verify ultracode fleet
//! (wf_0415115b-1a5); re-verified end-to-end by hand (2,184,717,059 steps,
//! Tagged(0), 38-axiom audit clean, soundness probes pass).
//!
//! NOT proved: the REVERSE direction (a^m ≡ 1 ⟹ a is a QR), the harder half of
//! the full iff — it needs a primitive-root / roots-counting argument. Tracked
//! as follow-up. Driver is self-contained (run directly, no `with_*` splice).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_euler_criterion -- --ignored --nocapture
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
fn eulers_criterion() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_euler_criterion.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_euler_criterion.sml");

    // Self-contained driver (embeds its flt-based foundation) — run directly.
    let Some((out, _)) = run_image_env(
        &image,
        &common::with_sound_audit(&driver, "euler_criterion", &["dichotomy", "qr_forward"]),
        990_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // Fermat-for-units base must build first.
    assert!(
        out.contains("OK apm1"),
        "Fermat-for-units (apm1) did not prove:\n{out}"
    );
    // The ±1 dichotomy — Euler's criterion core.
    assert!(
        out.contains("EC_DICHOTOMY_OK"),
        "dichotomy did not prove:\n{out}"
    );
    // The quadratic-residue ⟹ +1 forward direction.
    assert!(
        out.contains("EC_QRFWD_OK"),
        "qr_forward did not prove:\n{out}"
    );
    // Both halves together.
    assert!(
        out.contains("EC_ALL_OK"),
        "EC_ALL_OK marker missing:\n{out}"
    );
    // Soundness probes (conditional on prime / ¬(p∣a) / square; two-sided).
    assert!(out.contains("PROBE_OK"), "no soundness probe fired:\n{out}");
    // Not a degenerate / failed / exceptional run.
    assert!(
        !out.contains("PROBE_UNSOUND"),
        "a soundness probe fired UNSOUND:\n{out}"
    );
    assert!(!out.contains("UNSOUND"), "an UNSOUND marker fired:\n{out}");
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        out.contains("SOUND_AUDIT_OK euler_criterion"),
        "soundness audit did not certify euler_criterion:\n{out}"
    );
}
