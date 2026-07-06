//! Weak-reference fences — real `Weak.weak` / `Weak.weakArray` semantics
//! plus a REAL `PolyML.fullGC` (upstream Test120's exact shape).
//!
//! History: weak refs were the weak-as-strong gap (entries never demoted;
//! upstream-suite Test120 failed) and `PolyFullGC` was a success-shaped
//! stub (returned unit without collecting). Now the collector skips weak
//! slots during the trace and a post-trace fixup (`gc.rs::weak_fixup`,
//! the copying-GC port of upstream `gc_check_weak_ref.cpp`) forwards
//! surviving SOME cells and demotes dead entries to NONE; `PolyFullGC`
//! requests a synchronous stop-the-world collection at the RTS boundary.
//!
//! Three fences in one driver:
//! - a dead weak ref reads NONE after `PolyML.fullGC()` (Test120);
//! - a weak ref whose referent is strongly held elsewhere SURVIVES with
//!   the payload intact (the demotion must not over-fire);
//! - `Weak.weakArray` entries demote too.
//!
//! `#[ignore]` — needs `vendor/polyml/polyexport` (self-bootstrap first):
//! ```sh
//! cargo test --release -p polyml-bin --test weak_refs -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use std::path::PathBuf;

fn polyexport() -> Option<PathBuf> {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../vendor/polyml/polyexport");
    p.canonicalize().ok().filter(|p| p.exists())
}

const DRIVER: &str = r#"
val w = let val x = SOME (ref 3) in Weak.weak x end;
val keepref = ref 42;
val kept = Weak.weak (SOME keepref);
PolyML.fullGC ();
val () = case !w of NONE => print "DEAD-OK\n" | SOME _ => print "DEAD-FAIL\n";
val () =
    case !kept of
        SOME r => print ("KEPT-OK " ^ Int.toString (!r) ^ "\n")
      | NONE => print "KEPT-FAIL\n";
val arr = Weak.weakArray (3, SOME (ref 7));
PolyML.fullGC ();
val () = case Array.sub (arr, 1) of NONE => print "ARR-OK\n" | SOME _ => print "ARR-FAIL\n";
"#;

fn run_weak(envs: &[(&str, &str)]) {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let Some((out, _rc)) = run_image_env(&image, DRIVER, 20_000_000_000, envs) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("DEAD-OK"),
        "dead weak ref not demoted to NONE after fullGC (Test120 semantics):\n{out}"
    );
    assert!(
        out.contains("KEPT-OK 42"),
        "strongly-held referent wrongly demoted (or payload corrupted):\n{out}"
    );
    assert!(
        out.contains("ARR-OK"),
        "weakArray entry not demoted after fullGC:\n{out}"
    );
}

#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn weak_refs_demote_and_survive() {
    run_weak(&[]);
}

/// Same semantics must hold under the chunked parallel collector.
#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn weak_refs_demote_and_survive_parallel_gc() {
    run_weak(&[("POLYML_PARALLEL_GC", "1")]);
}
