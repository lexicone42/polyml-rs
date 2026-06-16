//! First steps of the Isabelle/Pure ML bootstrap on the polyml-rs interpreter.
//!
//! After completing HOL4's full prover stack, this probes the north star: can our
//! Rust PolyML run Isabelle? Isabelle/Pure has a Scala-free ML entry
//! (`poly --eval "val SML_file = PolyML.use" --use ROOT.ML`); its hard PolyML
//! coupling (`PolyML.NameSpace`, structural `PolyML.pretty`, the `CPCompilerResultFun`
//! parse-tree path) is vendored SML already compiled into our image — the same
//! surface HOL4 drives via `PolyML.use`, just exercised more deeply.
//!
//! `#[ignore]` (needs vendored Isabelle/Pure + /tmp/basis_loaded):
//! ```sh
//! tools/build-hol4-checkpoints.sh basis
//! # vendor src/Pure: see common::isabelle_pure_dir()
//! cargo test --release -p polyml-bin --test isabelle_pure -- --ignored --nocapture
//! ```
//!
//! STATUS (2026-06-06, go/no-go probe): GREEN — the NameSpace/system/pretty/
//! concurrency coupling loads on our reloaded image; **23 of 27 Phase-0 files load**.
//! The first real WALL is a systemic basis divergence: our default `int` is
//! FixedInt(63-bit) (`Int.precision = SOME 63`) but upstream PolyML defaults to
//! arbitrary-precision `int`, so `Real.fromInt (Time.toNanoseconds t)` (which
//! Isabelle's `time.ML` relies on) type-errors — cascading to `isabelle_thread.ML`
//! and `ml_compiler0.ML`. (`ml_statistics.ML` separately needs a real
//! `PolyML.Statistics` record shape.) Full Pure is months away (127 ML_file
//! directives + the parse-tree compiler path at #226); this pins the first rung.

mod common;
use common::*;

#[test]
#[ignore = "needs vendor/isabelle (src/Pure) + /tmp/basis_loaded"]
fn pure_phase0_namespace_and_coupling_load() {
    let (Some(pure), Some(basis)) = (isabelle_pure_dir(), basis_checkpoint_path()) else {
        eprintln!("SKIP: vendor/isabelle/src/Pure or /tmp/basis_loaded missing");
        return;
    };
    let p = pure.to_str().unwrap();
    // Load the load-bearing Phase-0 files (the coupling that gates the whole
    // project) and exercise PolyML.NameSpace via Isabelle's ML_Name_Space.
    // ROOT0.ML prerequisites + ROOT.ML Phase 0, in bootstrap order. 23 of these 27
    // load on our runtime; the 4 that don't (ml_statistics, time, isabelle_thread,
    // ml_compiler0) wall on the FixedInt(63) vs arbitrary-`int` divergence and the
    // Statistics record shape (see the module header).
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
  "ML/ml_recursive.ML",
  "ML/ml_name_space.ML","ML/ml_init.ML","ML/ml_system.ML",
  "General/basics.ML","General/string.ML","General/vector.ML","General/array.ML",
  "General/symbol_explode.ML","General/time.ML",
  "Concurrent/multithreading.ML","Concurrent/unsynchronized.ML","Concurrent/synchronized.ML",
  "Concurrent/counter.ML","Concurrent/single_assignment.ML","Concurrent/isabelle_thread.ML",
  "ML/ml_heap.ML","ML/ml_print_depth0.ML","ML/ml_pretty.ML","ML/ml_compiler0.ML"];
val () = List.app useF files;
(* the keystone: Isabelle's ML name space round-trips over PolyML.NameSpace *)
val () = (case (#lookupStruct ML_Name_Space.global) "List" of
            SOME _ => pr "NS_ROUNDTRIP_OK\n" | NONE => pr "NS_ROUNDTRIP_NONE\n")
         handle e => pr ("NS_ROUNDTRIP_FAIL " ^ exnMessage e ^ "\n");
val () = pr ("ISA_LOADED " ^ Int.toString (!nok) ^ "/27\n");
pr "ISA_PROBE_DONE\n";
"#
    );
    // ml_system.ML reads ML_SYSTEM/ML_PLATFORM via getEnv (now real).
    let Some((out, _)) = run_image_env(
        &basis,
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
        out.contains("ISA_PROBE_DONE"),
        "probe did not finish.\n{}",
        tail(&out, 30)
    );
    // The keystone: Isabelle's ML_Name_Space loads and PolyML.NameSpace round-trips.
    assert!(
        out.contains("ISA_OK ML/ml_name_space.ML"),
        "ml_name_space.ML did not load.\n{}",
        tail(&out, 40)
    );
    assert!(
        out.contains("NS_ROUNDTRIP_OK"),
        "PolyML.NameSpace lookup did not round-trip.\n{}",
        tail(&out, 40)
    );
    // The load-bearing system + pretty + concurrency + namespace-recursion coupling.
    for f in [
        "ML/ml_system.ML",
        "ML/ml_pretty.ML",
        "ML/ml_recursive.ML",
        "Concurrent/multithreading.ML",
        "Concurrent/synchronized.ML",
        "Concurrent/thread_attributes.ML",
        "ML/ml_heap.ML",
    ] {
        assert!(
            out.contains(&format!("ISA_OK {f}")),
            "{f} did not load.\n{}",
            tail(&out, 40)
        );
    }
    // 23 of 27 load (the go-signal); the 4 known walls are documented in the header.
    assert!(
        out.contains("ISA_LOADED 23/27"),
        "Phase-0 load count changed from 23/27.\n{}",
        tail(&out, 40)
    );
}
