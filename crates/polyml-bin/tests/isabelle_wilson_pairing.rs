//! THE INVOLUTION-PAIRING LEMMA — the historic wall toward Wilson's theorem —
//! with its list-product library, in Isabelle/Pure on the polyml-rs interpreter.
//!
//!   extract       : ⊢ lmem x L ⟹ lprod L = x · lprod (lremove x L)
//!   pairing_lemma : ⊢ lnodup L ⟹ (∀x∈L. inv x ∈ L) ⟹ (∀x∈L. cong p (x·inv x) 1)
//!                     ⟹ (∀x∈L. inv x ≠ x) ⟹ (∀x∈L. inv(inv x) = x)
//!                     ⟹ cong p (lprod L) 1
//!
//! The classical Wilson proof pairs each residue with its inverse; formalizing
//! that pairing — a PRODUCT INVARIANT UNDER A FIXED-POINT-FREE INVOLUTION, with no
//! finite-set library — is the wall. Here it's proved by genuine kernel inference:
//! a `natlist` datatype + list-product library (`lprod`/`lmem`/`lremove`/`llen`/
//! `lnodup` + the key `extract` lemma), then `pairing_lemma` by strong induction on
//! length (extract head `a` and its partner `inv a`, remove both, recurse; `inv`
//! injective on the list from the involution). The pure combinatorial core of
//! Wilson's theorem, abstracted from the residue range. Soundness probes confirm it
//! genuinely uses the inverse hypothesis and is conditional.
//!
//! Built on the modular/keystone base (`isabelle_mult_group.sml` + gcd + Euclid's
//! lemma) via `common::with_mult_group`. Proved by a 2-phase ultracode fleet
//! (wf_1ef6ffe6-859); re-verified end-to-end by hand.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_wilson_pairing -- --ignored --nocapture
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
fn involution_pairing_lemma() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_wilson_pairing.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_wilson_pairing.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_mult_group(&driver),
        900_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // the modular/keystone base must load first
    assert!(out.contains("LAGRANGE_ROOTS_OK"), "modular/keystone base did not load:\n{out}");
    // the list-product library (incl. the key extract lemma) and the pairing lemma
    assert!(out.contains("OK extract"), "the extract lemma did not check:\n{out}");
    assert!(out.contains("LIST_LIB_OK"), "list-product library did not complete:\n{out}");
    assert!(out.contains("OK pairing_lemma"), "the pairing lemma did not check:\n{out}");
    assert!(out.contains("PAIRING_OK"), "PAIRING_OK marker missing:\n{out}");
    assert!(!out.contains("Exception-"), "exception during proof:\n{out}");
    assert!(!out.contains("PROBE_UNSOUND"), "a soundness probe fired UNSOUND:\n{out}");
    assert!(!out.contains("UNSOUND"), "an UNSOUND marker fired:\n{out}");
}
