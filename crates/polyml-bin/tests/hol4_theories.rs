//! HOL4 theory-building integration tests (markerTheory, combinTheory).
//!
//! These verify that HOL4 `*Script.sml` theories — built on a NON-empty base via
//! the generalized Script→Theory recipe + the `new_theory` export keystone fix —
//! are present and usable on the warm checkpoints. `#[ignore]` (need the chain):
//!
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh        # …-> marker -> combin
//! cargo test --release -p polyml-bin --test hol4_theories -- --ignored --nocapture
//! ```
//!
//! markerTheory (src/marker/markerScript.sml) and combinTheory
//! (src/combin/combinScript.sml) are the two theories HOL4's simplifier needs
//! above bool. Building them proved the keystone: `Theory.new_theory` on a
//! non-empty base no longer trips the export VM halt (it now honors
//! `Globals.interactive`), and ancestor axioms are registered so synthesized-
//! theory theorems pass `uptodate_axioms`.

mod common;
use common::*;

/// markerTheory is built and usable: the `marker` segment is current, `stmarker`
/// is a real constant, and a saved theorem (Abbrev_CONG) is reachable.
#[test]
#[ignore = "slow: needs /tmp/hol4_marker (tools/build-hol4-checkpoints.sh marker)"]
fn marker_theory_built() {
    let Some(image) = marker_checkpoint_path() else {
        eprintln!("SKIP: /tmp/hol4_marker missing — run tools/build-hol4-checkpoints.sh marker");
        return;
    };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val () = pr ("THY " ^ Theory.current_theory() ^ "\n");
val () = (ignore (Term.prim_mk_const{Name="stmarker",Thy="marker"}); pr "STMARKER_CONST_OK\n")
         handle e => pr ("FAIL const :: " ^ exnMessage e ^ "\n");
val () = (ignore markerTheory.Abbrev_CONG; pr "ABBREV_CONG_OK\n")
         handle e => pr ("FAIL thm :: " ^ exnMessage e ^ "\n");
pr "MARKER_TEST_DONE\n";
"#;
    let Some((out, _)) = run_image_env(&image, driver, 10_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    for s in ["THY marker", "STMARKER_CONST_OK", "ABBREV_CONG_OK", "MARKER_TEST_DONE"] {
        assert!(out.contains(s), "missing {s}.\n{}", tail(&out, 30));
    }
}

/// combinTheory is built and usable: `I` is a real `combin` constant and
/// `combinTheory.I_THM` (`⊢ ∀x. I x = x`) is reachable; bool/marker ancestors
/// survive. This exercised the recipe's harder case (Q + a stubbed computeLib).
#[test]
#[ignore = "slow: needs /tmp/hol4_combin (tools/build-hol4-checkpoints.sh combin)"]
fn combin_theory_built() {
    let Some(image) = combin_checkpoint_path() else {
        eprintln!("SKIP: /tmp/hol4_combin missing — run tools/build-hol4-checkpoints.sh combin");
        return;
    };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val () = pr ("THY " ^ Theory.current_theory() ^ "\n");
val () = (ignore (Term.prim_mk_const{Name="I",Thy="combin"}); pr "I_CONST_OK\n")
         handle e => pr ("FAIL const :: " ^ exnMessage e ^ "\n");
val () = (ignore combinTheory.I_THM; ignore combinTheory.K_THM; ignore combinTheory.S_THM;
          pr "COMBIN_THMS_OK\n") handle e => pr ("FAIL thm :: " ^ exnMessage e ^ "\n");
val () = (ignore boolTheory.AND_CLAUSES; ignore markerTheory.stmarker_def; pr "ANCESTORS_OK\n")
         handle e => pr ("FAIL anc :: " ^ exnMessage e ^ "\n");
pr "COMBIN_TEST_DONE\n";
"#;
    let Some((out, _)) = run_image_env(&image, driver, 10_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    for s in ["THY combin", "I_CONST_OK", "COMBIN_THMS_OK", "ANCESTORS_OK", "COMBIN_TEST_DONE"] {
        assert!(out.contains(s), "missing {s}.\n{}", tail(&out, 30));
    }
    assert!(!out.contains("FAIL "), "a combin check failed.\n{}", tail(&out, 30));
}
