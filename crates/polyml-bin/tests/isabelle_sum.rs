//! SUMMATION OPERATOR + TRUNCATED SUBTRACTION, in Isabelle/Pure on the polyml-rs
//! interpreter — Stage C1 of the Fermat-little-theorem arc (the machinery the
//! binomial theorem mod p needs).
//!
//! Pure is HIGHER-ORDER, so `sumf : (nat⇒nat)⇒nat⇒nat` is a legit const (pass
//! concrete summands as object lambdas, `beta_norm` after applying). Each a
//! 0-hypothesis theorem; only classical assumption = excluded middle:
//!   `sumf f 0 = f 0`, `sumf f (Suc n) = sumf f n + f (Suc n)`
//!   `sub` (truncated subtraction) + `sub_self` (`n−n=0`), `sub_Suc_le`
//!     (`k≤n ⟹ (Suc n)−k = Suc(n−k)`)
//!   `sum_cong` : `(⋀k. k≤n ⟹ f k = g k) ⟹ sumf f n = sumf g n`  (the workhorse,
//!     a higher-order induction over the meta `⋀k` hyp on `f k`/`g k`)
//!
//! Built on `isabelle_binom.sml` by a 2-seat ultracode fleet (wf_0d8f0cb2-45c).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_sum -- --ignored --nocapture
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
fn summation_operator_and_truncated_subtraction() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_sum.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_sum.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        280_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(out.contains("OK sub_self"), "sub_self did not check:\n{out}");
    assert!(out.contains("OK sub_Suc_le"), "sub_Suc_le did not check:\n{out}");
    assert!(out.contains("OK sum_cong"), "sum_cong did not check:\n{out}");
    assert!(out.contains("SUMSUB_DONE"), "Stage-C1 development did not complete:\n{out}");
    assert!(!out.contains("Exception-"), "exception during proof:\n{out}");
}
