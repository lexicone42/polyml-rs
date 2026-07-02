//! P4 fences — the giant lock is DROPPED under `POLY_PARALLEL=1`.
//!
//! Five fences, each pinning a different clause of the P4 invariant
//! contract (docs/parallel-design.md):
//!
//! 1. `parallel_alloc_storm…` — the STW handshake is SOUND under true
//!    parallelism: three allocating workers + frequent collections +
//!    `POLYML_GC_AUDIT=1`, judged by an exact total (wrong integer, not
//!    flaky timing).
//! 2. `parallel_mutex_hammer…` — SML mutex atomicity now rests on the
//!    protocol-word atomics (P3), not on the giant lock: two threads ×
//!    200k lock/incr/unlock must total EXACTLY 400k.
//! 3. `parallel_racy_ref…` — deliberately-racy SML gets unspecified
//!    VALUES, never runtime-level failure (the Position-2 memory-model
//!    guarantee).
//! 4. `parallel_compute_scaling` — the headline: two pure-compute
//!    workers must run measurably FASTER with the lock dropped than
//!    under the giant lock, with byte-identical computed results.
//! 5. `parallel_flag_without_real_threads…` — `POLY_PARALLEL=1` alone
//!    (no `POLY_REAL_THREADS`) is a documented no-op.
//!
//! `#[ignore]` — needs `vendor/polyml/polyexport` (self-bootstrap first):
//! ```sh
//! cargo test --release -p polyml-bin --test concurrency_parallel -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use std::path::PathBuf;
use std::time::Instant;

fn polyexport() -> Option<PathBuf> {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../vendor/polyml/polyexport");
    p.canonicalize().ok().filter(|p| p.exists())
}

fn driver(name: &str) -> String {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/concurrency_support")
        .join(name);
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
}

#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn parallel_alloc_storm_exact_total_with_audit() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let sml = driver("alloc_storm_demo.sml");
    let Some((out, _)) = run_image_env(
        &image,
        &sml,
        60_000_000_000,
        &[
            ("POLY_REAL_THREADS", "1"),
            ("POLY_PARALLEL", "1"),
            // Frequent collections: the STW handshake (election + barrier
            // + cross-nursery evacuation) must hold across many cycles
            // with genuinely-parallel mutators.
            ("POLYML_GC_THRESHOLD", "2"),
            ("POLYML_GC_QUIET", "1"),
            // The audit re-walks every root set for residual from-space
            // pointers after each collection — a missed parked stack or a
            // torn barrier shows up here even if the total survives.
            ("POLYML_GC_AUDIT", "1"),
            ("POLYML_HEAP_BYTES", &(512 * 1024 * 1024).to_string()),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("ALLOC_STORM_PASS"),
        "parallel allocation storm lost or corrupted data across GC cycles:\n{out}"
    );
    assert!(
        !out.contains("GC AUDIT") && !out.contains("Exception-"),
        "GC audit residual / exception under parallel storm:\n{out}"
    );
}

#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn parallel_mutex_hammer_exact_count() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let sml = driver("mutex_hammer_demo.sml");
    let Some((out, _)) = run_image_env(
        &image,
        &sml,
        60_000_000_000,
        &[("POLY_REAL_THREADS", "1"), ("POLY_PARALLEL", "1")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("MUTEX_HAMMER_PASS"),
        "mutex atomicity broke without the giant lock (P3 protocol-word \
         atomics are now load-bearing):\n{out}"
    );
}

#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn parallel_racy_ref_unspecified_value_no_crash() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let sml = driver("racy_ref_demo.sml");
    let Some((out, code)) = run_image_env(
        &image,
        &sml,
        60_000_000_000,
        &[("POLY_REAL_THREADS", "1"), ("POLY_PARALLEL", "1")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("RACY_REF_OK"),
        "racy-ref final value out of bounds (or the run died) — racy SML \
         must yield unspecified values, never runtime failure \
         (exit={code}):\n{out}"
    );
}

/// The headline fence: dropping the giant lock makes two compute-bound
/// workers measurably faster. Runs the SAME deterministic driver under
/// the giant lock and under `POLY_PARALLEL=1`, asserts (a) the computed
/// result lines are byte-identical, (b) the parallel run's wall-clock
/// is at most `SCALING_GATE` of the giant run's. The gate is deliberately
/// generous (a shared CI box is noisy; image-load time dilutes the
/// ratio); the PRINTED numbers are the honest measurement.
#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn parallel_compute_scaling() {
    const SCALING_GATE: f64 = 0.85;

    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let sml = driver("parallel_scaling_demo.sml");

    let run = |parallel: bool| -> Option<(String, f64)> {
        let mut envs = vec![("POLY_REAL_THREADS", "1")];
        if parallel {
            envs.push(("POLY_PARALLEL", "1"));
        }
        let t0 = Instant::now();
        let (out, _) = run_image_env(&image, &sml, 60_000_000_000, &envs)?;
        let secs = t0.elapsed().as_secs_f64();
        Some((out, secs))
    };

    let Some((out_giant, t_giant)) = run(false) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    let Some((out_par, t_par)) = run(true) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(
        out_giant.contains("SCALING_DONE") && out_par.contains("SCALING_DONE"),
        "scaling driver did not complete:\n--- giant ---\n{out_giant}\n--- parallel ---\n{out_par}"
    );

    // Byte-identical computation, different schedule: the deterministic
    // spin results must match exactly across the two modes.
    // The REPL may prefix echoed lines, so match by containment and slice
    // from the marker.
    let result_line = |s: &str| -> String {
        s.lines()
            .find_map(|l| l.find("spin results:").map(|i| l[i..].to_string()))
            .unwrap_or_default()
    };
    let (rg, rp) = (result_line(&out_giant), result_line(&out_par));
    assert!(
        !rg.is_empty() && rg == rp,
        "computed results diverged between giant-lock and parallel runs:\n\
         giant:    {rg}\n parallel: {rp}"
    );

    let ratio = t_par / t_giant;
    eprintln!(
        "[scaling] giant-lock {t_giant:.2}s, POLY_PARALLEL {t_par:.2}s, ratio {ratio:.2} \
         (gate {SCALING_GATE})"
    );
    assert!(
        ratio < SCALING_GATE,
        "dropping the giant lock did not speed up 2 compute-bound workers: \
         giant {t_giant:.2}s vs parallel {t_par:.2}s (ratio {ratio:.2}, gate {SCALING_GATE})"
    );
}

/// `POLY_PARALLEL=1` WITHOUT `POLY_REAL_THREADS` is a documented no-op:
/// fork remains the dormant stub and everything runs exactly as the
/// single-threaded default. A plain computation must still produce the
/// exact expected answer.
#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn parallel_flag_without_real_threads_is_noop() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let sml = "fun fact 0 = 1 | fact n = n * fact (n - 1);\n\
               val () = print (\"fact 10 = \" ^ Int.toString (fact 10) ^ \"\\n\");\n";
    let Some((out, _)) = run_image_env(&image, sml, 1_000_000_000, &[("POLY_PARALLEL", "1")])
    else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("fact 10 = 3628800"),
        "POLY_PARALLEL without POLY_REAL_THREADS must be a no-op:\n{out}"
    );
}
