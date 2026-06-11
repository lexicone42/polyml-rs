//! Stage 6a of the Datatype roadmap: pairTheory — the product type `'a # 'b`
//! built by `new_type_definition`, with all the TFL/Define prerequisites
//! (pair_CASES, FORALL_PROD, EXISTS_PROD, pair_induction, FST/SND, UNCURRY).
//!
//! Needs the warm checkpoint: tools/build-hol4-checkpoints.sh pair
//! (chain: … → numsimps → pair → /tmp/hol4_pair).

mod common;

use common::run_image_env;
use std::path::PathBuf;

fn ckpt() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_pair");
    p.exists().then_some(p)
}

#[test]
#[ignore = "needs /tmp/hol4_pair (tools/build-hol4-checkpoints.sh pair)"]
fn tfl_prerequisites_present() {
    // The structural theorems the TFL/Define stack consumes. All must be
    // saved in the `pair` segment for Stage 6b to even type-check.
    let Some(image) = ckpt() else { return };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
fun chk n = (ignore (DB.fetch "pair" n); pr ("HAVE " ^ n ^ "\n"))
            handle _ =>
              (ignore (PolyML.use (let val f = "/tmp/p1.sml"
                                       val os = TextIO.openOut f
                                   in TextIO.output (os, "val _ = pairTheory." ^ n ^ ";\n");
                                      TextIO.closeOut os; f end));
               pr ("HAVE " ^ n ^ "\n"))
            handle _ => pr ("MISS " ^ n ^ "\n");
val () = List.app chk
  ["pair_CASES", "PAIR_EQ", "FST", "SND", "FORALL_PROD", "EXISTS_PROD",
   "pair_induction", "ABS_PAIR_THM", "UNCURRY", "CURRY_DEF", "pair_case_def"];
val () = pr "PROBE_DONE\n";
"#;
    let (out, _) = run_image_env(&image, driver, 30_000_000_000, &[]).expect("run");
    assert!(out.contains("PROBE_DONE"), "probe didn't finish:\n{out}");
    assert!(!out.contains("MISS "), "a TFL prerequisite is missing:\n{out}");
}

#[test]
#[ignore = "needs /tmp/hol4_pair (tools/build-hol4-checkpoints.sh pair)"]
fn fst_snd_compute() {
    // FST (x,y) = x and SND (x,y) = y must reduce — the projection identities
    // TFL's termination extraction relies on.
    let Some(image) = ckpt() else { return };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val th = Tactical.prove (
    Parse.Term [QUOTE "(FST ((a:'a),(b:'b)) = a) /\\ (SND (a,b) = b)"],
    boolLib.REWRITE_TAC [pairTheory.FST, pairTheory.SND]);
val () = if List.null (Thm.hyp th) then pr "FST_SND_OK\n" else pr "HYPS\n";
"#;
    let (out, _) = run_image_env(&image, driver, 30_000_000_000, &[]).expect("run");
    assert!(out.contains("FST_SND_OK"), "FST/SND projection failed:\n{out}");
}
