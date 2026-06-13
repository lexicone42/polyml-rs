//! A LIST THEORY in Isabelle/Pure on the polyml-rs interpreter — structural
//! induction over a SECOND inductive datatype (beyond `nat`).
//!
//! On the Peano semiring foundation (nat + add, for `length`), this builds an
//! inductive list datatype over nat — `natlist = Nil | Cons nat natlist` with its
//! own list-equality `leq` (refl + subst) and a `list_induct` axiom — and proves
//! the classic list laws by structural induction, each a 0-hypothesis theorem:
//!   append_nil    `leq (append l Nil) l`
//!   append_assoc  `leq (append (append a b) c) (append a (append b c))`
//!   rev_append    `leq (reverse (append a b)) (append (reverse b) (reverse a))`
//!   rev_rev       `leq (reverse (reverse l)) l`           (the headline)
//!   length_append `oeq (length (append a b)) (add (length a) (length b))`
//!
//! The Isabelle analogue of the HOL4 `list_laws_verified.sml` — demonstrating the
//! hand-built object logic handles a second inductive datatype with its own
//! induction principle, not just `nat`. A soundness probe confirms the kernel
//! rejects a garbled `rev_rev`.
//!
//! Built on `isabelle_number_theory.sml` by a 3-seat ultracode fleet
//! (wf_666cb3a1-e29); all three verified independently.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_list_theory -- --ignored --nocapture
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
fn list_laws_by_structural_induction() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_list_theory.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_list_theory.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        120_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    for law in ["append_nil", "append_assoc", "rev_append", "rev_rev", "length_append"] {
        assert!(out.contains(&format!("OK {law}")), "list law `{law}` did not check:\n{out}");
    }
    assert!(out.contains("LIST_THEORY_DONE"), "list theory did not complete:\n{out}");
    assert!(!out.contains("Exception-"), "exception during proof:\n{out}");
    assert!(!out.contains("UNSOUND"), "a soundness probe fired UNSOUND:\n{out}");
}
