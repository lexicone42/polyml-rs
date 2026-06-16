//! THE BINOMIAL THEOREM, in Isabelle/Pure on the polyml-rs interpreter — Stage C2 of
//! the Fermat-little-theorem arc (the hardest proof in the tower).
//!
//!   binom_theorem : ⊢ (a+b)^n = Σ_{k=0}^n C(n,k)·a^k·b^(n−k)
//!
//! A 0-hypothesis theorem; only classical assumption = excluded middle. Foundation
//! sum-algebra also proved: `sum_mult_l`, `sum_add`, `sum_peel_first` (reindex),
//! `binom_n_n` (`C(n,n)=1`, via `binom_diag_zero`: `C(n,n+1+j)=0` by single induction
//! with the IH at j AND j+1 — sidesteps lt machinery), `pow_b_sub_Suc`.
//!
//! The induction on n: `(a+b)^(Suc n) = (a+b)·(a+b)^n = a·S + b·S` [IH + right_distrib];
//! distribute into the sum (`sum_mult_l`), shift exponents (`pow_Suc`/`pow_b_sub_Suc`);
//! the RHS at Suc n is peeled (`sum_peel_first`), each term Pascal-split (`binom_Suc_Suc`)
//! into two sums via `sum_add`; the pieces recombine. The classic painful index-shift,
//! by genuine LCF kernel inference.
//!
//! Built on `isabelle_sum.sml` by a 2-phase ultracode pipeline (wf_a511fcbc-470):
//! sum-algebra → binom_theorem (3 seats, ALL proved it).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_binom_thm -- --ignored --nocapture
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
fn the_binomial_theorem() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_binom_thm.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_binom_thm.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_nt_helpers(&driver),
        300_000_000_000,
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
        out.contains("OK sum_peel_first"),
        "sum_peel_first (reindex) did not check:\n{out}"
    );
    assert!(
        out.contains("OK binom_n_n"),
        "binom_n_n (C(n,n)=1) did not check:\n{out}"
    );
    assert!(
        out.contains("OK binom_theorem"),
        "the binomial theorem did not check:\n{out}"
    );
    assert!(
        out.contains("BINOM_THM_DONE"),
        "Stage-C2 development did not complete:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
}
