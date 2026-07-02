//! P2b fence — fork-heavy allocation storm across many GC cycles.
//!
//! Three SML workers allocate hard (build/fold lists) while depositing
//! into a shared accumulator; a LOW `POLYML_GC_THRESHOLD` forces frequent
//! collections whose roots span every thread's stack + the shared state.
//! With per-thread nurseries (P2b), every collection must promote each
//! worker's live data into the primary and reset the worker nurseries —
//! a dropped or double-promoted object shows up as a WRONG EXACT TOTAL
//! (or a crash), not flaky timing.
//!
//! This fence is written to pass both BEFORE P2b (children share nursery
//! 0) and AFTER (children own nurseries) — it pins the allocation+GC
//! semantics across the transition.
//!
//! `#[ignore]` — needs `vendor/polyml/polyexport` (self-bootstrap first):
//! ```sh
//! cargo test --release -p polyml-bin --test concurrency_alloc_storm -- --ignored --nocapture
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
fn alloc_storm_exact_total_across_gc_cycles() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/concurrency_support/alloc_storm_demo.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read alloc_storm_demo.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        60_000_000_000,
        &[
            ("POLY_REAL_THREADS", "1"),
            // Frequent collections: the storm must survive many promote/
            // reset cycles, not just one.
            ("POLYML_GC_THRESHOLD", "2"),
            ("POLYML_GC_QUIET", "1"),
            ("POLYML_HEAP_BYTES", &(512 * 1024 * 1024).to_string()),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(
        out.contains("ALLOC_STORM_PASS"),
        "the allocation storm lost or corrupted data across GC cycles \
         (wrong exact total):\n{out}"
    );
    assert!(
        !out.contains("Exception-") && !out.contains("GC invariant violated"),
        "an exception / GC invariant violation fired during the storm:\n{out}"
    );
}
