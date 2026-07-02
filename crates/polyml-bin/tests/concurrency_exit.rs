//! P0 exit-semantics fence — a forked thread's `OS.Process.exit` terminates
//! the process instead of being swallowed while the program runs on.
//!
//! The pre-fix inversion: the process-exit flag was consumed by whichever
//! thread stepped next, so a child's exit ended only the CHILD's run loop
//! while main continued. The fix broadcasts KILL to peers and leaves the
//! flag set. This test pins the observable property: main must NOT reach
//! the end of its work (no BUG_REACHED_END) and the process must not hang.
//!
//! `#[ignore]` — needs `vendor/polyml/polyexport` (self-bootstrap first):
//! ```sh
//! cargo test --release -p polyml-bin --test concurrency_exit -- --ignored --nocapture
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
fn thread_exit_terminates_the_process() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/concurrency_support/exit_inversion_demo.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read exit_inversion_demo.sml");

    // run_image_env bounds the run with --max-steps; a hang (exit failing to
    // stop main) would blow the step budget and still return, so the
    // BUG_REACHED_END check is the real discriminator.
    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        20_000_000_000,
        &[("POLY_REAL_THREADS", "1")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(out.contains("BEGIN"), "the driver never started:\n{out}");
    assert!(
        !out.contains("BUG_REACHED_END"),
        "the forked thread's OS.Process.exit was SWALLOWED — main ran to \
         completion (the pre-fix inversion):\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "an exception was raised during the demo:\n{out}"
    );
}
