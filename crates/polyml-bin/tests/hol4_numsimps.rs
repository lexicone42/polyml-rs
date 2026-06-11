//! Stage 5 of the Datatype roadmap: the HOL4 arithmetic decision procedure
//! (Arith.ARITH_CONV — Presburger via Sup-Inf), the ARITH_ss simpset
//! fragment, computeLib (first build ever), and reduceLib's REDUCE_CONV all
//! run on the interpreter.
//!
//! Needs the warm checkpoint: tools/build-hol4-checkpoints.sh numsimps
//! (chain: … → arithmetic → numeral → numsimps → /tmp/hol4_numsimps).

mod common;

use common::run_image_env;
use std::path::PathBuf;

fn ckpt() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_numsimps");
    p.exists().then_some(p)
}

#[test]
#[ignore = "needs /tmp/hol4_numsimps (tools/build-hol4-checkpoints.sh numsimps)"]
fn arith_conv_decides_presburger() {
    let Some(image) = ckpt() else { return };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val th1 = Arith.ARITH_CONV (Parse.Term [QUOTE "2 + 3 * x <= 3 + 3 * x"]);
val () = pr ("T1 " ^ Parse.term_to_string (Thm.concl th1) ^ "\n");
val th2 = Arith.ARITH_CONV (Parse.Term [QUOTE "!m n. m + n - m = n"]);
val () = pr ("T2 " ^ Parse.term_to_string (Thm.concl th2) ^ "\n");
val th3 = Arith.ARITH_CONV
    (Parse.Term [QUOTE "x < y /\\ y < z ==> x + 1 < z"]);
val () = pr ("T3 " ^ Parse.term_to_string (Thm.concl th3) ^ "\n");
val () = pr "ARITH_CONV_OK\n";
"#;
    let (out, _) = run_image_env(&image, driver, 100_000_000_000, &[]).expect("run");
    assert!(out.contains("ARITH_CONV_OK"), "ARITH_CONV failed:\n{out}");
    assert!(!out.contains("Exception-"), "exception in output:\n{out}");
}

#[test]
#[ignore = "needs /tmp/hol4_numsimps (tools/build-hol4-checkpoints.sh numsimps)"]
fn arith_ss_proves_via_simp() {
    let Some(image) = ckpt() else { return };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val th = Tactical.prove (
    Parse.Term [QUOTE "x + 1 <= y ==> x < y + 2"],
    simpLib.SIMP_TAC (simpLib.++ (boolSimps.bool_ss, numSimps.ARITH_ss)) []);
val () = if List.null (Thm.hyp th) then pr "ARITH_SS_OK\n" else pr "HYPS\n";
"#;
    let (out, _) = run_image_env(&image, driver, 100_000_000_000, &[]).expect("run");
    assert!(out.contains("ARITH_SS_OK"), "ARITH_ss proof failed:\n{out}");
}

#[test]
#[ignore = "needs /tmp/hol4_numsimps (tools/build-hol4-checkpoints.sh numsimps)"]
fn reduce_conv_computes_addition() {
    // NOTE: numeral *multiplication* reduction is currently degraded
    // (enumeral_mult/numeral_MIN/MAX unproved — see build_numsimps notes);
    // addition/comparison reduce fully.
    let Some(image) = ckpt() else { return };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val th = reduceLib.REDUCE_CONV (Parse.Term [QUOTE "2 + 3 + 4 < 10"]);
val () = pr ("R " ^ Parse.term_to_string (Thm.concl th) ^ "\n");
val () = pr "REDUCE_OK\n";
"#;
    let (out, _) = run_image_env(&image, driver, 100_000_000_000, &[]).expect("run");
    assert!(out.contains("REDUCE_OK"), "REDUCE_CONV failed:\n{out}");
    assert!(
        out.contains("<=> T") || out.contains("⇔ T"),
        "expected 2+3+4<10 to reduce to T:\n{out}"
    );
}
