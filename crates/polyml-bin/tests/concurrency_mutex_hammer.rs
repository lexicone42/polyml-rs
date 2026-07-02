//! P3 fence — two threads hammer the SAME `Thread.Mutex` on a tight
//! lock/incr/unlock loop; the exact final count (2*N) proves the atomic
//! mutex-word ops (lockMutex/tryLockMutex/atomicReset) lose no updates.
//!
//! A pre-P3 plain read-modify-write on the mutex word had a TOCTOU: two
//! threads could both read it unlocked and both enter the critical
//! section, dropping increments. The atomic ops (fetch_add/compare_exchange/
//! swap) close that — the count stays exact as the giant lock is broken.
//!
//! `#[ignore]` — needs `vendor/polyml/polyexport` (self-bootstrap first):
//! ```sh
//! cargo test --release -p polyml-bin --test concurrency_mutex_hammer -- --ignored --nocapture
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
fn two_threads_hammering_one_mutex_lose_no_updates() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/concurrency_support/mutex_hammer_demo.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read mutex_hammer_demo.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        40_000_000_000,
        &[("POLY_REAL_THREADS", "1")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(
        out.contains("MUTEX_HAMMER_PASS"),
        "the shared counter lost updates under mutex contention \
         (atomic mutex-word ops failed):\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "an exception was raised during the hammer:\n{out}"
    );
}
