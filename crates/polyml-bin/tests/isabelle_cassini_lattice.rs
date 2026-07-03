//! THE CASSINI LATTICE — parallel-verified Fibonacci where the
//! consistency of the parallel work is itself kernel-checked.
//!
//! Phase 1 (parallel): workers prove the cells `⊢ fib n ≡ F_n` for
//! n = 0..15 by a verified evaluator over the fib defining axioms.
//! Phase 2 (parallel): for each of 14 overlapping windows, a worker
//! instantiates the GENERAL Cassini identity (proved by induction in
//! `isabelle_fibonacci.sml`) and transports three cell theorems into
//! it — deriving concrete identities like `⊢ 34·89 = 55² + 1` whose
//! proofs run through the general theorem, not through evaluation.
//! Windows consume cells proved by DIFFERENT phase-1 workers: parallel
//! work stitched across thread boundaries by inference.
//!
//! Every cell sits in up to three windows; a single wrong value would
//! make two windows underivable. The audit closes the loop the other
//! way: each window's literals are re-checked by independent SML
//! integer arithmetic, and a negative probe confirms a +2 variant of a
//! window statement does NOT match. `LATTICE_CLOSED` = all of it held.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! cargo test --release -p polyml-bin --test isabelle_cassini_lattice -- --ignored --nocapture
//! ```

mod common;
use common::{run_image_env, with_nt_helpers};
use std::path::PathBuf;

fn checkpoint() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/isabelle_pure");
    p.exists().then_some(p)
}

fn driver() -> String {
    let base = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/isabelle_support");
    let fib = std::fs::read_to_string(base.join("isabelle_fibonacci.sml"))
        .expect("read isabelle_fibonacci.sml");
    let lattice = std::fs::read_to_string(base.join("isabelle_cassini_lattice.sml"))
        .expect("read isabelle_cassini_lattice.sml");
    with_nt_helpers(&format!("{fib}\n{lattice}"))
}

#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn cassini_lattice_closes_in_parallel() {
    if checkpoint().is_none() {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    }
    let image = checkpoint().unwrap();
    let sml = driver();
    let Some((out, code)) = run_image_env(
        &image,
        &sml,
        200_000_000_000,
        &[
            ("POLY_REAL_THREADS", "1"),
            ("POLY_PARALLEL", "1"),
            // Allocation-heavy proving: roomy per-worker nurseries (the
            // documented parallel-prover tuning knob).
            ("POLYML_CHILD_NURSERY_BYTES", "268435456"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // The foundation's own gate must hold first (the general Cassini
    // identity proved by induction).
    assert!(
        out.contains("FIB_CASSINI_OK"),
        "the general Cassini development failed (exit={code}):\n{}",
        out.lines().rev().take(25).collect::<Vec<_>>().join("\n")
    );
    assert!(
        out.contains("SOUND_CELLS 16/16"),
        "not every Fibonacci cell was proved sound:\n{out}"
    );
    assert!(
        out.contains("SOUND_WINDOWS 14/14"),
        "not every Cassini window theorem was derived + cross-checked:\n{out}"
    );
    assert!(
        out.contains("PROBE_OK lattice audit rejects +2 variant"),
        "the lattice's negative probe did not fire — the audit is toothless"
    );
    assert!(
        out.contains("LATTICE_CLOSED"),
        "the lattice did not close:\n{out}"
    );
}
