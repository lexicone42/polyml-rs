//! THE MODULAR-INVERSE FUNCTION + RESIDUE RANGE toward Wilson's theorem, in
//! Isabelle/Pure on the polyml-rs interpreter.
//!
//!   cong_iff_rmod : ⊢ 0<p ⟹ (cong p a b ⟺ a mod p = b mod p)   (congruence made decidable)
//!   finv_inv      : ⊢ cong p (x · finv p x) 1                    (finv is a correct inverse)
//!   finv_mem      : ⊢ lmem (finv p x) (upto (p−1))               (lands back in range)
//!   finv_invol    : ⊢ finv p (finv p x) = x                      (LITERAL involution)
//!   finv_neq      : ⊢ on [2..p−2], finv p x ≠ x                  (fixed-point free)
//!
//! The `pairing_lemma` needs the modular inverse as a literal involution FUNCTION,
//! but the object logic has no choice operator and `cong` isn't directly decidable.
//! The unlock: a `mod` function makes congruence decidable (`cong_iff_rmod`), so the
//! inverse is built by a list search over the residue range. The four `finv` lemmas
//! are exactly `pairing_lemma`'s hypotheses. Each 0-hyp, aconv intended, with
//! soundness probes.
//!
//! Built on the Wilson-pairing base via `common::with_wilson_pairing`. Proved by a
//! 2-phase ultracode fleet (wf_a22d8bd7-115); re-verified end-to-end by hand.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_wilson_inverse -- --ignored --nocapture
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
fn modular_inverse_function() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_wilson_inverse.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_wilson_inverse.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_wilson_pairing(&driver),
        950_000_000_000,
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
        out.contains("PAIRING_OK"),
        "Wilson-pairing base did not load:\n{out}"
    );
    assert!(
        out.contains("RANGE_MOD_OK"),
        "range/mod phase did not complete:\n{out}"
    );
    for lemma in ["finv_inv", "finv_mem", "finv_invol", "finv_neq"] {
        assert!(
            out.contains(&format!("OK {lemma}")),
            "lemma `{lemma}` did not check:\n{out}"
        );
    }
    assert!(
        out.contains("INVERSE_FN_OK"),
        "INVERSE_FN_OK marker missing:\n{out}"
    );
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
