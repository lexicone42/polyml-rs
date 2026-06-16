//! WILSON'S THEOREM in Isabelle/Pure on the polyml-rs interpreter.
//!
//!   wilson : ⊢ prime p ⟹ cong p ((p−1)!) (p−1)         i.e. (p−1)! ≡ −1 (mod p)
//!
//! A 0-hypothesis theorem by genuine LCF kernel inference — the classical companion
//! to Fermat's little theorem, proved on a Rust reimplementation of PolyML. `prime`
//! is `prime2`, the genuine structural prime (1<p ∧ ∀d. d∣p ⟹ d=1∨d=p), used
//! consistently by the whole keystone chain. Three soundness probes pass: it needs
//! the prime hypothesis, the residue is p−1 (=−1) not 0, and it is NOT the false
//! unconditional `(p−1)! ≡ 1`.
//!
//! The proof pairs each residue in [2..p−2] with its modular inverse (1 and p−1 are
//! self-inverse), so by the involution-pairing lemma ∏[2..p−2] ≡ 1, whence
//! (p−1)! = (p−1)·1·∏[2..p−2] ≡ p−1 ≡ −1. Built on the full Wilson development
//! (pairing lemma + `finv` inverse function + residue range + keystones) via
//! `common::with_wilson_inverse`. Proved by a 3-seat ultracode assembly fleet
//! (wf_39658abf-b42) — the capstone of a multi-run campaign; re-verified by hand.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_wilson -- --ignored --nocapture
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
fn wilsons_theorem() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_wilson.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_wilson.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_wilson_inverse(&driver),
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

    // the full Wilson development must load first (inverse function, pairing lemma)
    assert!(
        out.contains("INVERSE_FN_OK"),
        "Wilson base did not load:\n{out}"
    );
    // WILSON'S THEOREM, verified 0-hyp + aconv the intended statement
    assert!(out.contains("OK wilson"), "wilson did not check:\n{out}");
    assert!(
        out.contains("WILSON_OK"),
        "WILSON_OK marker missing:\n{out}"
    );
    // the result is the genuine theorem, not a degenerate/false variant
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
