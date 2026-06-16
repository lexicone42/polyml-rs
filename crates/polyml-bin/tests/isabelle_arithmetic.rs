//! PEANO ARITHMETIC BY INDUCTION in our Isabelle object logic — real math on the
//! polyml-rs interpreter.
//!
//! Building on the first-order object logic (isabelle_object_logic.rs), this is
//! the Isabelle analogue of the HOL4 INDUCT_TAC trophies (n+0=n, ADD_COMM): a
//! Peano logic — type `nat` with Zero/Suc/add, an object equality with refl+subst,
//! and a `nat` induction axiom — built programmatically in ML on the warm
//! /tmp/isabelle_pure checkpoint, then real arithmetic proved BY INDUCTION:
//!   add_0_right    `⊢ n + 0 = n`              (induction on n — the keystone)
//!   add_comm       `⊢ m + n = n + m`
//!   add_assoc      `⊢ (m + n) + k = m + (n + k)`
//!   mult_0_right   `⊢ n * 0 = 0`              (multiplication defined + induction)
//! all checked 0-hypothesis theorems. A soundness probe in the driver confirms the
//! kernel REJECTS the false `n + 0 = Suc n`, so the logic is non-degenerate.
//! Engineered by a two-phase ultracode workflow (wf_76f81af9-9ac, foundation 5/5 +
//! headlines 4/4).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_arithmetic -- --ignored --nocapture
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
fn peano_arithmetic_by_induction() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_arithmetic.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_arithmetic.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        60_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // n + 0 = n by induction (the keystone), then the laws + multiplication
    assert!(
        out.contains("OK add_0_right"),
        "n+0=n (by induction) failed:\n{out}"
    );
    assert!(
        out.contains("OK add_comm"),
        "add commutativity failed:\n{out}"
    );
    assert!(
        out.contains("OK add_assoc"),
        "add associativity failed:\n{out}"
    );
    assert!(
        out.contains("OK mult"),
        "mult_0_right (multiplication by induction) failed:\n{out}"
    );
    assert!(
        out.contains("ISA_ARITH_DONE"),
        "arithmetic demo did not finish:\n{out}"
    );
    assert!(!out.contains("Exception-"), "exception:\n{out}");
}
