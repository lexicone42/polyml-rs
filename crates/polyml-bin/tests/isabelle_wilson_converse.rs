//! WILSON'S CONVERSE in Isabelle/Pure on the polyml-rs interpreter.
//!
//!   wc_converse : ⊢ composite n ⟹ 4 < n ⟹ dvd n (factorial n)
//!
//! i.e. every composite n > 4 divides (n−1)!  (so (n−1)! ≡ 0, not −1, mod n).
//! With Wilson's theorem (prime p ⟹ (p−1)! ≡ −1 mod p, isabelle_wilson.rs) this
//! is the non-trivial half of the primality characterization
//! `n prime ⟺ (n−1)! ≡ −1 (mod n)` — the n=4 exception (3! = 6 ≡ 2 ≢ −1 mod 4)
//! is correctly excluded by the 4 < n bound.
//!
//! A 0-hypothesis theorem by genuine LCF kernel inference; it adds NO new axioms
//! (the delta is purely derived over the with_wilson_inverse base) — the only
//! classical assumption is the base's single `ex_middle`. `composite n ≝ ∃a.
//! 1<a ∧ a<n ∧ dvd a n`; `factorial n ≝ lprod (upto (sub n 1))`.
//!
//! Elementary proof (no Wilson's theorem needed): a composite n has a proper
//! divisor a with cofactor b (n = a·b), both in [1..n−1]; the key lemma — two
//! DISTINCT list members x≠y ⟹ x·y ∣ lprod L (via `extract` twice) — gives
//! n = a·b ∣ (n−1)!. Perfect-square case n = a²: use a and 2a (distinct, both
//! < n exactly when n > 4), so 2a² = 2n ∣ (n−1)! and n ∣ 2n ∣ (n−1)!.
//!
//! Built on `common::with_wilson_inverse` (lprod/upto/extract/lremove/dvd) by a
//! foundation→3-seat→verify ultracode fleet (wf_cf5755d5-b5f, all 3 seats proved
//! it incl. the square case); re-verified end-to-end by hand.
//!
//! NOT included: the small cases (n=2,3,4) and a single combined-iff wrapper
//! theorem — this driver proves the dvd-the-factorial heart of the converse.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_wilson_converse -- --ignored --nocapture
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
fn wilsons_converse() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_wilson_converse.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_wilson_converse.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_sound_audit(
            &common::with_wilson_inverse(&driver),
            "wilson_converse",
            &["wc_converse"],
        ),
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

    // The converse: composite n > 4 ⟹ n ∣ (n−1)!  (incl. the perfect-square case).
    assert!(
        out.contains("WC_CONVERSE_OK"),
        "Wilson's converse did not prove:\n{out}"
    );
    assert!(
        out.contains("WC_ALL_OK"),
        "WC_ALL_OK marker missing:\n{out}"
    );
    // Soundness probes (statement aconv intended; needs composite + needs 4<n).
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
        !out.contains("Static Errors") && !out.contains(": error:"),
        "compile error during proof:\n{out}"
    );
    assert!(
        out.contains("SOUND_AUDIT_OK wilson_converse"),
        "soundness audit did not certify wilson_converse:\n{out}"
    );
}
