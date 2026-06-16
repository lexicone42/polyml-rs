//! Isabelle/Pure Phase 0 = 27/27 on the ARBITRARY-PRECISION-INT image.
//!
//! The sibling `isabelle_pure.rs` loads Phase 0 on a FixedInt(63) basis checkpoint
//! and gets 23/27 — the 4 holdouts (`ml_statistics`, `time`, `isabelle_thread`,
//! `ml_compiler0`) fail on the int-precision divergence (Isabelle assumes upstream
//! PolyML's arbitrary-precision default int, e.g. `Real.fromInt(Time.toNanoseconds
//! t)` in `time.ML`).
//!
//! With the int flip done (our interpreter self-bootstraps an arbitrary-int image;
//! see `tools/intflip-bootstrap.sh` + commit 7fa5090), ALL 27 load — no stubs, the
//! real divergence is gone. This pins that payoff.
//!
//! `#[ignore]` (needs /tmp/arbint_image from `tools/intflip-bootstrap.sh` ~5min +
//! vendored Isabelle/Pure):
//! ```sh
//! tools/intflip-bootstrap.sh
//! cargo test --release -p polyml-bin --test isabelle_pure_arbint -- --ignored --nocapture
//! ```

mod common;
use common::*;

use std::path::PathBuf;

fn arbint_image() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/arbint_image");
    p.exists().then_some(p)
}

#[test]
#[ignore = "needs /tmp/arbint_image (tools/intflip-bootstrap.sh) + vendor/isabelle"]
fn pure_phase0_all_27_under_arbitrary_int() {
    let (Some(pure), Some(image)) = (isabelle_pure_dir(), arbint_image()) else {
        eprintln!("SKIP: /tmp/arbint_image or vendor/isabelle/src/Pure missing");
        return;
    };
    let p = pure.to_str().unwrap();
    let driver = format!(
        r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val PURE = "{p}";
val nok = ref 0;
fun useF f = (PolyML.use (PURE ^ "/" ^ f); pr ("ISA_OK " ^ f ^ "\n"); nok := !nok+1)
             handle e => pr ("ISA_FAIL " ^ f ^ " :: " ^ exnMessage e ^ "\n");
val files = [
  "ML/ml_statistics.ML","PIDE/xml0.ML","General/exn.ML","General/output_primitives.ML",
  "Concurrent/thread_attributes.ML","Concurrent/thread_data.ML","Concurrent/thread_position.ML",
  "ML/ml_recursive.ML","ML/ml_name_space.ML","ML/ml_init.ML","ML/ml_system.ML",
  "General/basics.ML","General/string.ML","General/vector.ML","General/array.ML",
  "General/symbol_explode.ML","General/time.ML",
  "Concurrent/multithreading.ML","Concurrent/unsynchronized.ML","Concurrent/synchronized.ML",
  "Concurrent/counter.ML","Concurrent/single_assignment.ML","Concurrent/isabelle_thread.ML",
  "ML/ml_heap.ML","ML/ml_print_depth0.ML","ML/ml_pretty.ML","ML/ml_compiler0.ML"];
val () = List.app useF files;
val () = pr ("ARB_INT = " ^ (case Int.precision of NONE => "yes" | SOME _ => "NO") ^ "\n");
val () = pr ("ISA_LOADED " ^ Int.toString (!nok) ^ "/27\n");
pr "ISA_ARB_DONE\n";
"#
    );
    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        60_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("ISA_ARB_DONE"),
        "probe did not finish.\n{}",
        tail(&out, 40)
    );
    // Confirm we really are on an arbitrary-precision-int image.
    assert!(
        out.contains("ARB_INT = yes"),
        "image is not arbitrary-precision int.\n{}",
        tail(&out, 10)
    );
    // The 4 that fail under FixedInt must now load.
    for f in [
        "ML/ml_statistics.ML",
        "General/time.ML",
        "Concurrent/isabelle_thread.ML",
        "ML/ml_compiler0.ML",
    ] {
        assert!(
            out.contains(&format!("ISA_OK {f}")),
            "{f} did not load under arbitrary int.\n{}",
            tail(&out, 40)
        );
    }
    // Full Phase 0 (the int flip's payoff).
    assert!(
        out.contains("ISA_LOADED 27/27"),
        "Phase-0 count is not 27/27.\n{}",
        tail(&out, 40)
    );
}
