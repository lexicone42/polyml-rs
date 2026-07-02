//! Thread-attribute interrupt fidelity, end-to-end through the real basis
//! `Thread` structure on the `polyexport` REPL (POLY_REAL_THREADS=1):
//!
//! 1. `Thread.interrupt` on a compute-bound worker forked with
//!    `InterruptState InterruptAsynch` raises SML `Interrupt` in that
//!    worker at a safepoint (the `ProcessAsynchRequests` port).
//! 2. `Thread.interrupt` on a worker blocked in `ConditionVar.wait` wakes
//!    it and the interrupt is delivered via the basis' `testInterrupt`
//!    (the `WaitInfinite` + `TestSynchronousRequests` ports) — i.e. an
//!    interrupt cancels a wait, upstream's defining condvar semantics.
//! 3. `InterruptState InterruptDefer` really DEFERS: the pending interrupt
//!    is not delivered at safepoints nor by an explicit `testInterrupt`
//!    until the worker flips its state to `InterruptSynch`.
//!
//! `#[ignore]` — needs the self-bootstrapped `vendor/polyml/polyexport`:
//! ```sh
//! cd vendor/polyml && ../../target/release/poly run --max-steps 200000000000 \
//!       bootstrap/bootstrap64.txt < bootstrap/Stage1.sml      # -> polyexport (~5 min)
//! cargo test --release -p polyml-bin --test concurrency_interrupt -- --ignored --nocapture
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
fn thread_interrupt_attribute_fidelity() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/concurrency_support/interrupt_demo.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read interrupt_demo.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        4_000_000_000,
        &[("POLY_REAL_THREADS", "1")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // 1. Asynch: delivered at a safepoint into a pure compute loop.
    assert!(
        out.contains("INTERRUPT_ASYNC_OK"),
        "asynchronous interrupt was not delivered to a compute-bound \
         InterruptAsynch worker:\n{out}"
    );
    // 2. A blocked ConditionVar.wait is cancelled by Thread.interrupt.
    assert!(
        out.contains("INTERRUPT_CONDVAR_OK"),
        "interrupt did not cancel a blocked ConditionVar.wait:\n{out}"
    );
    // 3. Defer defers (through safepoints AND an explicit testInterrupt),
    //    then delivers once the state is flipped to Synch.
    assert!(
        out.contains("DEFER_OK"),
        "InterruptDefer did not defer (or the deferred interrupt was \
         lost after flipping to Synch):\n{out}"
    );
    // The driver ran to completion (no hang cut short by the step cap).
    assert!(
        out.contains("INTERRUPT_DEMO_DONE"),
        "the interrupt demo did not run to completion:\n{out}"
    );
    assert!(
        !out.contains("_FAIL"),
        "the interrupt demo reported a FAIL marker:\n{out}"
    );
}
