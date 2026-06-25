//! End-to-end SML concurrency demo: two REAL OS threads, one `Thread.Mutex`,
//! a shared `ref`, 100_000 mutex-protected increments each → counter = 200_000.
//!
//! This is the SML-LEVEL companion to the runtime-level
//! `polyml-runtime/tests/concurrency_gc_handshake.rs`: it drives the actual
//! `Thread.Thread` / `Thread.Mutex` BASIS through the self-bootstrapped
//! `polyexport` REPL with `POLY_REAL_THREADS=1`, proving real `fork` + real
//! mutual exclusion + real interleaving under the giant lock + safepoint GC.
//!
//! Why it needs the signal-thread fix: the basis forks an internal SIGNAL
//! thread at startup (`Signal.sml` → `Thread.fork(sigThread, [])`), which loops
//! on `PolyWaitForSignal`. Once `fork` genuinely spawns OS threads, that thread
//! must PARK (it is marked a daemon and blocks in `try_thread_rts`) instead of
//! busy-spinning the giant lock — otherwise the REPL hangs at startup. See the
//! `PolyWaitForSignal` arm in `interpreter/mod.rs`.
//!
//! `#[ignore]` — needs the self-bootstrapped `vendor/polyml/polyexport`:
//! ```sh
//! cd vendor/polyml && ../../target/release/poly run --max-steps 200000000000 \
//!       bootstrap/bootstrap64.txt < bootstrap/Stage1.sml      # -> polyexport (~5 min)
//! cargo test --release -p polyml-bin --test concurrency_mutex_demo -- --ignored --nocapture
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
fn two_thread_mutex_demo_real_threads() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let driver_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/concurrency_support/mutex_demo.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read mutex_demo.sml");

    // POLY_REAL_THREADS=1 enables genuine Thread.fork/Mutex (default OFF, so the
    // bootstrap/REPL/HOL4/Isabelle paths stay byte-identical single-threaded).
    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        2_000_000_000,
        &[("POLY_REAL_THREADS", "1")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // The demo forks two workers, each doing 100_000 { lock; r:=!r+1; unlock };
    // the parent mutex-joins on a `done` counter, then asserts !r = 2*100_000.
    assert!(
        out.contains("counter = 200000 expected = 200000  PASS"),
        "two-thread mutex demo did not reach counter=200000 PASS \
         (a hang, a lost update, or no real interleaving):\n{out}"
    );
    assert!(
        !out.contains("FAIL"),
        "the demo reported FAIL (lost update → no mutual exclusion):\n{out}"
    );
    // "exception Interrupt" appears legitimately in `structure T`'s echoed
    // signature (Thread has an `exception Interrupt`); a RAISED exception shows
    // as "Exception-". Guard on the latter only.
    assert!(
        !out.contains("Exception-"),
        "an exception was raised during the demo:\n{out}"
    );
}
