//! ISABELLE'S OWN PARALLELISM runs on the polyml-rs runtime — the futures
//! scheduler (`Pure/Concurrent/future.ML`, `Par_List`) forks REAL worker
//! threads, and under `POLY_PARALLEL=1` they execute on real cores.
//!
//! This is the crown-jewel stress for the P4 lock drop: not a synthetic
//! demo but the genuine Isabelle concurrency stack — `Synchronized.var`
//! (mutex+condvar), `Thread_Data` (per-thread `Thread.self()` identity),
//! `Thread_Attributes` (interrupt states), the scheduler thread's timed
//! condvar waits, task-queue bookkeeping — driving LCF kernel inference
//! in parallel workers.
//!
//! Three fences:
//! 1. `futures_scheduler_parallel_speedup` — Par_List over pure compute:
//!    identical deterministic results in both modes, parallel beats the
//!    giant lock by the gate (measured 0.15 on a 6-core box — the giant
//!    baseline also pays cooperative hand-off churn).
//! 2. `kernel_inference_parallel_sound_and_faster` — 6 workers × 100k
//!    certified kernel inferences (`Thm.symmetric`/`Thm.transitive`
//!    chains), every result checked 0-hyp with the exact proposition
//!    (measured 0.31 — allocation-heavy work is partially GC-bound; the
//!    collector is serial. Needs big per-thread nurseries, which is also
//!    the documented tuning guidance).
//! 3. `kernel_inference_parallel_gc_audit_clean` — the same kernel load
//!    under a low GC threshold + `POLYML_GC_AUDIT=1`: theorems stay sound
//!    while collections constantly move kernel objects under 6 parallel
//!    mutators, and the audit finds no residual from-space pointers.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! cargo test --release -p polyml-bin --test isabelle_parallel -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use std::path::PathBuf;

fn checkpoint() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/isabelle_pure");
    p.exists().then_some(p)
}

fn driver(name: &str) -> String {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support")
        .join(name);
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
}

fn elapsed_ms(out: &str) -> Option<u64> {
    out.lines()
        .find_map(|l| l.split("ELAPSED_MS = ").nth(1))
        .and_then(|s| s.trim().parse().ok())
}

fn line_containing(out: &str, marker: &str) -> String {
    out.lines()
        .find_map(|l| l.find(marker).map(|i| l[i..].trim().to_string()))
        .unwrap_or_default()
}

/// Run a driver on the Pure checkpoint under the given threading mode.
fn run_mode(sml: &str, parallel: bool, extra: &[(&str, &str)]) -> Option<String> {
    let image = checkpoint()?;
    let mut envs: Vec<(&str, &str)> = vec![("POLY_REAL_THREADS", "1")];
    if parallel {
        envs.push(("POLY_PARALLEL", "1"));
    }
    envs.extend_from_slice(extra);
    let (out, _) = run_image_env(&image, sml, 200_000_000_000, &envs)?;
    Some(out)
}

#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn futures_scheduler_parallel_speedup() {
    const GATE: f64 = 0.6;
    if checkpoint().is_none() {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    }
    let sml = driver("isabelle_parallel_compute.sml");

    let Some(giant) = run_mode(&sml, false, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    let Some(par) = run_mode(&sml, true, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    for (mode, out) in [("giant", &giant), ("parallel", &par)] {
        assert!(
            out.contains("SCALE_PROBE_DONE"),
            "{mode}: Par_List probe did not complete:\n{out}"
        );
    }
    // Deterministic computation: identical results across modes.
    let (rg, rp) = (
        line_containing(&giant, "PAR_RESULTS ="),
        line_containing(&par, "PAR_RESULTS ="),
    );
    assert!(
        !rg.is_empty() && rg == rp,
        "Par_List results diverged:\n giant:    {rg}\n parallel: {rp}"
    );

    let (tg, tp) = (
        elapsed_ms(&giant).expect("giant ELAPSED_MS") as f64,
        elapsed_ms(&par).expect("parallel ELAPSED_MS") as f64,
    );
    let ratio = tp / tg;
    eprintln!(
        "[isabelle-par] Par_List compute: giant {:.1}s, POLY_PARALLEL {:.1}s, ratio {ratio:.2} (gate {GATE})",
        tg / 1000.0,
        tp / 1000.0
    );
    assert!(
        ratio < GATE,
        "Isabelle's futures did not speed up under POLY_PARALLEL: \
         giant {tg}ms vs parallel {tp}ms (ratio {ratio:.2}, gate {GATE})"
    );
}

#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn kernel_inference_parallel_sound_and_faster() {
    const GATE: f64 = 0.7;
    // Allocation-heavy kernel work needs room per worker or the run is
    // GC-frequency-bound (measured: 32 MB default → ratio 0.78; 256 MB →
    // 0.31). This is the documented tuning knob for parallel provers.
    const NURSERY: &str = "268435456";

    if checkpoint().is_none() {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    }
    let sml = driver("isabelle_parallel_kernel.sml");
    let extra = [("POLYML_CHILD_NURSERY_BYTES", NURSERY)];

    let Some(giant) = run_mode(&sml, false, &extra) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    let Some(par) = run_mode(&sml, true, &extra) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    for (mode, out) in [("giant", &giant), ("parallel", &par)] {
        assert!(
            out.contains("SOUND_TASKS = 6/6"),
            "{mode}: a kernel task produced an unsound/wrong theorem \
             (hyps nonempty or wrong proposition):\n{out}"
        );
        assert!(
            out.contains("KERNEL_PAR_DONE"),
            "{mode}: kernel probe did not complete:\n{out}"
        );
    }

    let (tg, tp) = (
        elapsed_ms(&giant).expect("giant ELAPSED_MS") as f64,
        elapsed_ms(&par).expect("parallel ELAPSED_MS") as f64,
    );
    let ratio = tp / tg;
    eprintln!(
        "[isabelle-par] LCF kernel inference (600k certified inferences, 6 workers): \
         giant {:.1}s, POLY_PARALLEL {:.1}s, ratio {ratio:.2} (gate {GATE})",
        tg / 1000.0,
        tp / 1000.0
    );
    assert!(
        ratio < GATE,
        "parallel kernel inference did not beat the giant lock: \
         giant {tg}ms vs parallel {tp}ms (ratio {ratio:.2}, gate {GATE})"
    );
}

#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn kernel_inference_parallel_gc_audit_clean() {
    if checkpoint().is_none() {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    }
    let sml = driver("isabelle_parallel_kernel.sml");
    // Low threshold: collections fire constantly while 6 workers churn
    // theorems; the audit re-walks every root set after each collection.
    let extra = [("POLYML_GC_THRESHOLD", "30"), ("POLYML_GC_AUDIT", "1")];

    let Some(out) = run_mode(&sml, true, &extra) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("SOUND_TASKS = 6/6"),
        "kernel theorems corrupted under audited parallel collections:\n{out}"
    );
    assert!(
        out.contains("KERNEL_PAR_DONE"),
        "audited kernel probe did not complete:\n{out}"
    );
    // "GC AUDIT:" is printed unconditionally (not GC_QUIET-gated) whenever
    // the post-collect walk finds residual from-space pointers or an
    // unpublished registered peer — its absence is a real verdict.
    assert!(
        !out.contains("GC AUDIT"),
        "GC audit flagged residual from-space pointers / unpublished peers \
         under parallel kernel load:\n{out}"
    );
}
