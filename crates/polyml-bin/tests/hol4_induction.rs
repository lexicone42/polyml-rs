//! HOL4 induction trophy — the FIRST genuine induction proofs over the natural
//! numbers running on the polyml-rs Rust interpreter.
//!
//! Chain: kernel -> Theory -> parser -> bool -> combin -> **numTheory** (built
//! by `build_num_checkpoint.sml`, which bootstraps the naturals + `INDUCTION`
//! from `boolTheory.INFINITY_AX`). On top of `/tmp/hol4_num` we load HOL4's
//! generic structural-induction support (`src/1/Prim_rec`; `INDUCT_THEN` takes
//! the induction theorem as an argument, so no prim_recTheory is needed),
//! define
//! ```text
//! INDUCT_TAC = Prim_rec.INDUCT_THEN numTheory.INDUCTION Tactic.ASSUME_TAC
//! ```
//! and prove two theorems that GENUINELY require induction (verified: neither
//! is provable by `GEN_TAC THEN REWRITE_TAC []`):
//!   * `|- !n. (n = 0) \/ (?m. n = SUC m)`  (every nat is zero or a successor)
//!   * `|- !n. ~(SUC n = n)`                (SUC_ID; step uses the IH via ASM)
//!
//! Every theorem object is built by HOL4's LCF-style kernel running on our
//! interpreter — not a simulation.
//!
//! `#[ignore]` because it needs `/tmp/hol4_num`, built once with:
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh num   # basis->…->combin->num
//! cargo test --release -p polyml-bin --test hol4_induction -- --ignored --nocapture
//! ```

mod common;
use common::*;

#[test]
#[ignore = "slow: needs /tmp/hol4_num (tools/build-hol4-checkpoints.sh num)"]
fn induction_proofs_over_num() {
    let Some(num) = num_checkpoint_path() else {
        eprintln!("SKIP: /tmp/hol4_num missing — run tools/build-hol4-checkpoints.sh num");
        return;
    };

    let Some((out, _code)) =
        run_support_driver_on(&num, "prove_induction.sml", 150_000_000_000)
    else {
        eprintln!("SKIP: vendor/hol4 or driver missing");
        return;
    };

    assert!(
        out.contains("PROVE_INDUCTION_DONE"),
        "prove_induction.sml did not run to completion.\n{}",
        tail(&out, 40)
    );

    // numTheory.INDUCTION survived the checkpoint and is the real thing.
    assert!(
        out.contains("∀P. P 0 ∧ (∀n. P n ⇒ P (SUC n)) ⇒ ∀n. P n")
            || out.contains("!P. P 0"),
        "numTheory.INDUCTION not present / wrong shape.\n{}",
        tail(&out, 40)
    );

    // Trophy 1: cases theorem, proved with zero hypotheses.
    assert!(
        out.contains("TROPHY_CASES_PASS"),
        "cases induction proof did not pass.\n{}",
        tail(&out, 40)
    );
    assert!(
        out.contains("∀n. n = 0 ∨ ∃m. n = SUC m"),
        "cases theorem statement not the expected |- !n. (n=0) \\/ (?m. n = SUC m).\n{}",
        tail(&out, 40)
    );

    // Trophy 2: SUC_ID, the canonical arithmetic induction.
    assert!(
        out.contains("TROPHY_SUC_ID_PASS"),
        "SUC_ID induction proof did not pass.\n{}",
        tail(&out, 40)
    );
    assert!(
        out.contains("∀n. SUC n ≠ n") || out.contains("∀n. ¬(SUC n = n)"),
        "SUC_ID theorem statement not the expected |- !n. ~(SUC n = n).\n{}",
        tail(&out, 40)
    );

    assert!(
        out.contains("INDUCTION_PROOF_PASS"),
        "not all induction trophies passed.\n{}",
        tail(&out, 40)
    );
    eprintln!("HOL4 induction trophy: both proofs PASS on the Rust interpreter");
}
