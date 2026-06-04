//! HOL4 simplifier (simpLib / SIMP_CONV / SIMP_TAC) integration test.
//!
//! Drives HOL4's real simplifier on the warm `/tmp/hol4_simp` checkpoint.
//! `#[ignore]` (needs the chain):
//!
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh        # …-> combin -> simp
//! cargo test --release -p polyml-bin --test hol4_simp -- --ignored --nocapture
//! ```
//!
//! simpLib is the conditional-rewriting simplification engine (one tier above
//! REWRITE_TAC). The checkpoint assembles it on the combin base with the simp
//! leaves + 5-module core + typed markerLib/TypeBase stubs (the real markerLib
//! needs the absent proofManagerLib, and the full bool_ss/UNWIND path needs the
//! absent SAT subsystem — neither is required for SIMP_CONV/SIMP_TAC with a
//! hand-rolled simpset). See build_simp_checkpoint.sml.

mod common;
use common::*;

/// SIMP_CONV rewrites a term and SIMP_TAC proves a goal, using a hand-rolled
/// simpset (empty_ss ++ rewrites [...]).
#[test]
#[ignore = "slow: needs /tmp/hol4_simp (tools/build-hol4-checkpoints.sh simp)"]
fn simp_conv_and_simp_tac_run() {
    let Some(image) = simp_checkpoint_path() else {
        eprintln!("SKIP: /tmp/hol4_simp missing — run tools/build-hol4-checkpoints.sh simp");
        return;
    };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val ss = simpLib.++ (simpLib.empty_ss,
           simpLib.rewrites [combinTheory.I_THM, boolTheory.AND_CLAUSES,
                             boolTheory.REFL_CLAUSE]);
(* SIMP_CONV: (I x = x) simplifies to T *)
val () =
  (let val th = simpLib.SIMP_CONV ss [] (Parse.Term [QUOTE "(I:'a->'a) x = x"])
   in if Term.aconv (boolSyntax.rhs (Thm.concl th)) boolSyntax.T then pr "SIMP_CONV_OK\n"
      else pr ("SIMP_CONV_BAD " ^ Parse.thm_to_string th ^ "\n")
   end) handle e => pr ("SIMP_CONV_FAIL :: " ^ exnMessage e ^ "\n");
(* SIMP_TAC: prove (I x = x) *)
val () =
  (let val th = Tactical.prove (Parse.Term [QUOTE "(I:'a->'a) x = x"], simpLib.SIMP_TAC ss [])
   in if null (Thm.hyp th) then pr "SIMP_TAC_OK\n" else pr "SIMP_TAC_BAD\n"
   end) handle e => pr ("SIMP_TAC_FAIL :: " ^ exnMessage e ^ "\n");
pr "SIMP_TEST_DONE\n";
"#;
    let Some((out, _)) = run_image_env(&image, driver, 20_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    for s in ["SIMP_CONV_OK", "SIMP_TAC_OK", "SIMP_TEST_DONE"] {
        assert!(
            out.contains(s),
            "missing {s}; simpLib SIMP_CONV/SIMP_TAC did not behave.\n{}",
            tail(&out, 40)
        );
    }
    assert!(
        !out.contains("_FAIL") && !out.contains("_BAD"),
        "a simp proof failed.\n{}",
        tail(&out, 40)
    );
}
