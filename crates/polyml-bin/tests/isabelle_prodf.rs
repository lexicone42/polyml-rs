//! THE FINITE-PRODUCT COMBINATOR `prodf` in Isabelle/Pure on the polyml-rs interpreter.
//!
//!   prodf f 0 = f 0 ;  prodf f (Suc n) = (prodf f n) * (f (Suc n))    (a new const)
//!   prod_cong         : ⊢ (∀k≤n. f k = g k) ⟹ prodf f n = prodf g n
//!   prod_const_pow    : ⊢ prodf (λk. c) n = pow c (Suc n)
//!   prod_mult_combine : ⊢ (prodf f n)·(prodf g n) = prodf (λk. f k · g k) n
//!
//! The multiplicative mirror of the higher-order finite sum `sumf` — a new
//! higher-order constant defined conservatively by two recursion axioms (as
//! sumf/fact/pow are), with its core algebra proved by genuine LCF kernel
//! induction (each 0-hyp). This is the structural piece the tower lacked toward
//! Wilson's & Euler's theorems (both reduce to a finite product over a residue
//! range). Adding the const extends the theory, so the development uses one final
//! context and re-varifies reused lemmas (the new-const discipline);
//! `prod_const_pow` has a soundness probe.
//!
//! Built on `isabelle_binom_thm.sml` (the sumf template) over the classical
//! foundation, spliced in by `common::with_binom_thm`. Proved by a 3-seat
//! ultracode fleet (wf_66aae28d-292); re-verified end-to-end by hand.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_prodf -- --ignored --nocapture
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
fn finite_product_combinator() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_prodf.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_prodf.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_binom_thm(&driver),
        800_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(out.contains("BINOM_THM_DONE"), "finite-sum base did not load:\n{out}");
    for lemma in ["prodf_def", "prod_cong", "prod_const_pow", "prod_mult_combine"] {
        assert!(out.contains(&format!("OK {lemma}")), "`{lemma}` did not check:\n{out}");
    }
    assert!(out.contains("PRODF_OK"), "PRODF_OK marker missing:\n{out}");
    assert!(!out.contains("Exception-"), "exception during proof:\n{out}");
    assert!(!out.contains("PROBE_UNSOUND"), "a soundness probe fired UNSOUND:\n{out}");
    assert!(!out.contains("UNSOUND"), "an UNSOUND marker fired:\n{out}");
}
