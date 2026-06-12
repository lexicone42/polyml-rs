//! A minimal FIRST-ORDER OBJECT LOGIC, built on Isabelle/Pure and proved in, on
//! the polyml-rs interpreter — the step from meta-logic to mathematics.
//!
//! Isabelle/Pure is the meta-logic (⟹, ≡, ⋀). Real mathematics happens in an
//! OBJECT logic (FOL/HOL), which Isabelle ships as `.thy` files loaded through
//! Thy_Info — and Thy_Info needs PIDE, which isn't loaded here. So instead we
//! build the logic the way `IFOL.thy` does: a formula type `o`, a judgment
//! `Trueprop :: o ⇒ prop`, connective/quantifier constants, and the
//! natural-deduction rules as AXIOMS (`Thm.add_axiom_global`) — purely in ML, on
//! the warm `/tmp/isabelle_pure` checkpoint — then prove with the kernel,
//! tactics, and resolution. Five connectives, each a genuine checked theorem:
//!   conj `⊢ A ∧ B ⟹ B ∧ A`,  oimp `⊢ A ⟶ B ⟶ A` (K),
//!   disj `⊢ A ∨ B ⟹ B ∨ A` (via disjE),
//!   All  `⊢ (∀x. P x ∧ Q x) ⟹ ∀x. P x`,  oeq `⊢ a = b ⟹ b = a` (subst).
//! Engineered by a 5-seat ultracode workflow (wf_570c4e06-017); all verified.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_object_logic -- --ignored --nocapture
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
fn first_order_object_logic_proofs() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_object_logic.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_object_logic.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        30_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(out.contains("ISA_OBJLOGIC_START"), "driver did not start:\n{out}");
    // each connective's natural-deduction theorem must be checked
    for rung in ["conj", "oimp", "disj", "forall", "oeq"] {
        assert!(
            out.contains(&format!("RUNG {rung} OK")),
            "object-logic rung `{rung}` did not produce a checked theorem:\n{out}"
        );
    }
    assert!(out.contains("ISA_OBJLOGIC_DONE"), "object-logic demo did not finish:\n{out}");
}
