//! PARALLEL THEOREM PROVING — the multiplication table derived from the
//! Peano axioms by genuine LCF kernel inference, one Par_List future per
//! cell, on the polyml-rs parallel runtime.
//!
//! This is the showpiece the whole 2026-07 concurrency arc builds to:
//! Isabelle's OWN futures scheduler distributing REAL proof search
//! (a verified evaluator — every step a kernel-checked axiom
//! instantiation chained through congruences; no oracle, no reflection)
//! across worker threads that, under `POLY_PARALLEL=1`, execute on real
//! cores. Every resulting theorem is audited: 0 hypotheses and
//! proposition aconv an INDEPENDENTLY built statement; a negative probe
//! confirms the audit rejects a wrong table entry (`3*4=13`).
//!
//! Two tests:
//! 1. `parallel_proving_sound_and_faster` — both modes prove all 144
//!    cells soundly; the parallel run beats the giant lock by the gate.
//! 2. (the driver's own probes run in both modes as part of 1.)
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! cargo test --release -p polyml-bin --test isabelle_parallel_proving -- --ignored --nocapture
//! ```

mod common;
use common::{run_image_env, with_ntbase};
use std::path::PathBuf;

fn checkpoint() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/isabelle_pure");
    p.exists().then_some(p)
}

fn driver() -> String {
    let delta = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/isabelle_support/isabelle_parallel_proving.sml"),
    )
    .expect("read isabelle_parallel_proving.sml");
    with_ntbase(&delta)
}

fn elapsed_ms(out: &str) -> Option<u64> {
    out.lines()
        .find_map(|l| l.split("TABLE_ELAPSED_MS ").nth(1))
        .and_then(|s| s.trim().parse().ok())
}

fn assert_sound(mode: &str, out: &str) {
    assert!(
        out.contains("SOUND_CELLS 144/144"),
        "{mode}: not every table cell was proved sound (0-hyp + aconv):\n{}",
        out.lines().rev().take(30).collect::<Vec<_>>().join("\n")
    );
    assert!(
        out.contains("PROBE_OK audit rejects 3*4=13"),
        "{mode}: the negative probe did not fire — the audit is toothless"
    );
    assert!(
        out.contains("PAR_PROVING_DONE"),
        "{mode}: driver did not complete"
    );
}

#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn parallel_proving_sound_and_faster() {
    const GATE: f64 = 0.7;
    if checkpoint().is_none() {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    }
    let image = checkpoint().unwrap();
    let sml = driver();

    let run = |parallel: bool| -> Option<String> {
        let mut envs = vec![("POLY_REAL_THREADS", "1")];
        if parallel {
            envs.push(("POLY_PARALLEL", "1"));
        }
        let (out, _) = run_image_env(&image, &sml, 200_000_000_000, &envs)?;
        Some(out)
    };

    let Some(giant) = run(false) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    let Some(par) = run(true) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert_sound("giant", &giant);
    assert_sound("parallel", &par);

    let (tg, tp) = (
        elapsed_ms(&giant).expect("giant TABLE_ELAPSED_MS") as f64,
        elapsed_ms(&par).expect("parallel TABLE_ELAPSED_MS") as f64,
    );
    let ratio = tp / tg;
    eprintln!(
        "[par-proving] 144 kernel-certified cells: giant {:.1}s, POLY_PARALLEL {:.1}s, \
         ratio {ratio:.2} (gate {GATE})",
        tg / 1000.0,
        tp / 1000.0
    );
    assert!(
        ratio < GATE,
        "parallel theorem proving did not beat the giant lock: \
         giant {tg}ms vs parallel {tp}ms (ratio {ratio:.2}, gate {GATE})"
    );
}
