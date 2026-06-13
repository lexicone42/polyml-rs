//! GAUSS SUMMATION + SUM OF ODDS, proved BY INDUCTION in Isabelle/Pure on the
//! polyml-rs interpreter — closed-form summation identities, one rung up from the
//! commutative-semiring development (`isabelle_number_theory.rs`) and the Isabelle
//! mirror of the HOL4 `hol4_summation.rs` trophy.
//!
//! Copies the full semiring foundation (object logic + Peano add/mult + the
//! semiring laws), then defines two summation functions by recursion and proves
//! the two classics, each a 0-hypothesis theorem, by genuine structural induction:
//!   sum  0 = 0,  sum  (Suc n) = (Suc n) + sum n      (triangular numbers)
//!   osum 0 = 0,  osum (Suc n) = osum n + (2n+1)       (running sum of odds)
//!   GAUSS        `⊢ sum n + sum n = n · (Suc n)`      (2·(0+···+n) = n·(n+1))
//!   SUM_OF_ODDS  `⊢ osum n = n · n`                   (1+3+···+(2n−1) = n²)
//! Pure LCF kernel inference (nat_induct + the semiring lemmas, no automation).
//! Each proof asserts `hyps = 0` AND `prop aconv goal`; a soundness probe confirms
//! the kernel rejects the false "drop the +1" Gauss variant (non-degenerate).
//!
//! Engineered by a 3-seat ultracode workflow (wf_4ca14273-6ab): all three seats
//! proved BOTH identities independently — agreement on the same theorems is the
//! correctness signal.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_summation -- --ignored --nocapture
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
fn gauss_summation_and_sum_of_odds_by_induction() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_summation.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_summation.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        90_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // Gauss (2*(0+..+n) = n(n+1), doubling form) and sum-of-odds (n^2), each a
    // checked theorem (driver prints `OK <name>` only when hyps=0 AND aconv goal)
    assert!(out.contains("OK gauss"), "Gauss summation not proved:\n{out}");
    assert!(out.contains("OK sum_of_odds"), "sum-of-odds (n^2) not proved:\n{out}");
    // the driver prints this only when both OK gates + the soundness probe fired
    assert!(out.contains("GAUSS_DONE"), "summation development did not complete:\n{out}");
    assert!(!out.contains("Exception-"), "exception during proof:\n{out}");
}
