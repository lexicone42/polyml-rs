//! Stage 6b of the Datatype roadmap: HOL4's `Define` (TotalDefn) — the full
//! TFL well-founded-recursion definition package — RUNS on the interpreter.
//!
//! `/tmp/hol4_defn` carries the whole stack: the real TypeBase infrastructure
//! (Pmatch/TypeBasePure/TypeBase), the pairLib SML stack, the coretypes
//! theories (pair/sum/one/option) + basicSize, the proofman subsystem, the
//! TFL core (wfrecUtils/Rules/Induction/Extract/Defn) and TotalDefn, with num
//! registered in TypeBase so `0`/`SUC n` patterns compile.
//!
//! Build: tools/build-hol4-checkpoints.sh defn

mod common;

use common::run_image_env;
use std::path::PathBuf;

fn ckpt() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_defn");
    p.exists().then_some(p)
}

#[test]
#[ignore = "needs /tmp/hol4_defn (tools/build-hol4-checkpoints.sh defn)"]
fn define_nonrecursive() {
    let Some(image) = ckpt() else { return };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val th = TotalDefn.Define [QUOTE "dbl x = x + x"];
val () = pr ("DEF " ^ Parse.thm_to_string th ^ "\n");
val () = pr "DEFINE_OK\n";
"#;
    let (out, _) = run_image_env(&image, driver, 100_000_000_000, &[]).expect("run");
    assert!(
        out.contains("DEFINE_OK"),
        "non-recursive Define failed:\n{out}"
    );
    assert!(!out.contains("Exception-"), "exception:\n{out}");
}

#[test]
#[ignore = "needs /tmp/hol4_defn (tools/build-hol4-checkpoints.sh defn)"]
fn define_recursive_with_termination() {
    // The full path: pattern-matching on 0/SUC (needs num in TypeBase) plus
    // automatic well-founded-termination proof for the recursion.
    let Some(image) = ckpt() else { return };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val th = TotalDefn.Define
           [QUOTE "(sumto 0 = 0) /\\ (sumto (SUC n) = SUC n + sumto n)"];
val () = pr ("DEF " ^ Parse.thm_to_string th ^ "\n");
val () = if List.null (Thm.hyp th) then pr "REC_DEFINE_OK\n" else pr "HAS_HYPS\n";
"#;
    let (out, _) = run_image_env(&image, driver, 200_000_000_000, &[]).expect("run");
    assert!(
        out.contains("REC_DEFINE_OK"),
        "recursive Define (with termination) failed:\n{out}"
    );
}
