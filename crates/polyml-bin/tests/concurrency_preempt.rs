//! Preemption-fairness proof: two REAL OS threads whose hot loops are PURE
//! computation (no mutex, no blocking call — nothing that voluntarily
//! releases the giant lock) provably INTERLEAVE, because the safepoint
//! cooperative yield (every 65536 steps) hands the giant lock to the
//! waiting peer. This is the interpreter-level "preemption" the
//! concurrency roadmap asks for: a compute-bound SML thread cannot starve
//! its peers.
//!
//! The driver (`concurrency_support/preempt_demo.sml`) forks two workers
//! that each bump a shared progress ref once per 50k-iteration compute
//! round; the main thread samples both counters and asserts that at the
//! first sample past a quarter of the total work BOTH are strictly
//! between 0 and done — a run-to-completion (non-interleaving) scheduler
//! would show one at the threshold and the other at 0.
//!
//! `#[ignore]` — needs the self-bootstrapped `vendor/polyml/polyexport`:
//! ```sh
//! cd vendor/polyml && ../../target/release/poly run --max-steps 200000000000 \
//!       bootstrap/bootstrap64.txt < bootstrap/Stage1.sml      # -> polyexport (~5 min)
//! cargo test --release -p polyml-bin --test concurrency_preempt -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use std::path::PathBuf;

fn polyexport() -> Option<PathBuf> {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../vendor/polyml/polyexport");
    p.canonicalize().ok().filter(|p| p.exists())
}

#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn compute_bound_threads_interleave_fairly() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/concurrency_support/preempt_demo.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read preempt_demo.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        4_000_000_000,
        &[("POLY_REAL_THREADS", "1")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // Fairness: at the first midway sample BOTH compute-bound workers had
    // made progress and NEITHER had finished — the safepoint yield really
    // interleaves threads that never block.
    assert!(
        out.contains("PREEMPT_OK"),
        "compute-bound threads did not provably interleave \
         (run-to-completion scheduling or a starved worker):\n{out}"
    );
    // Completeness: both workers ran to their exact totals.
    assert!(
        out.contains("FINAL_OK"),
        "workers did not both complete their full round count:\n{out}"
    );
    assert!(
        !out.contains("FAIL"),
        "the preemption demo reported a FAIL marker:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "an exception was raised during the demo:\n{out}"
    );
}
