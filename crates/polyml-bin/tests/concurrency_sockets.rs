//! In-process concurrent-socket demo — the definitive giant-lock-release
//! (blocking-syscall park) test.
//!
//! Drives `concurrency_support/socket_threads_demo.sml` through the
//! self-bootstrapped `polyexport` REPL with `POLY_REAL_THREADS=1`: a forked
//! SERVER thread binds/listens/accepts on loopback while the MAIN thread
//! connects as a client and echoes a payload — ALL IN ONE PROCESS.
//!
//! Under the giant lock exactly one mutator runs bytecode at a time, so if
//! the server's blocking `accept` (or the recv/send readiness `select`)
//! held the lock, the client thread could never run to connect/send — a
//! deadlock. It completes ONLY because `accept`/`connect`/`select` release
//! the lock across their wait (`park_while_blocking`, publishing GC roots),
//! letting the two threads hand off. A regression that stopped parking any
//! of them turns this into a HANG (caught by the test harness timeout).
//!
//! `#[ignore]` — needs `vendor/polyml/polyexport` (self-bootstrap first):
//! ```sh
//! cargo test --release -p polyml-bin --test concurrency_sockets -- --ignored --nocapture
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
fn concurrent_socket_echo_real_threads() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/concurrency_support/socket_threads_demo.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read socket_threads_demo.sml");

    // POLY_REAL_THREADS=1 enables genuine Thread.fork + the blocking-syscall
    // park. Default OFF, so every other workload stays byte-identical.
    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        20_000_000_000,
        &[("POLY_REAL_THREADS", "1")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(
        out.contains("SOCKET_THREADS_PASS"),
        "the concurrent socket echo did not PASS (a deadlock/hang would mean a \
         blocking syscall failed to release the giant lock, or a lost echo):\n{out}"
    );
    assert!(
        out.contains("ECHO=[PING-through-the-giant-lock]"),
        "the payload did not round-trip through the kernel between two SML threads:\n{out}"
    );
    assert!(
        !out.contains("SOCKET_THREADS_FAIL") && !out.contains("Exception-"),
        "the demo reported FAIL or raised an exception:\n{out}"
    );
}
