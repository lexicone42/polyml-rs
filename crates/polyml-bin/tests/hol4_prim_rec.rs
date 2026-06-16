//! The REAL HOL4 prim_recTheory on the polyml-rs interpreter — Datatype
//! roadmap Stage 1 (`/tmp/hol4_prim_rec`, built by build_prim_rec_checkpoint.sml
//! from the actual prim_recScript.sml with three trophy-proof splices; see the
//! build script header for the surgery).
//!
//! `#[ignore]` (needs the chain → num → prim):
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh prim
//! cargo test --release -p polyml-bin --test hol4_prim_rec -- --ignored --nocapture
//! ```

mod common;
use common::*;

/// prim_recTheory reloads with the genuine primitive-recursion theorem and
/// LESS theory, all hypothesis-free — and num_Axiom actually FUNCTIONS as a
/// recursion principle: define a recursive function via new_specification.
#[test]
#[ignore = "slow: needs /tmp/hol4_prim_rec (tools/build-hol4-checkpoints.sh prim)"]
fn prim_rec_theory_present_and_functional() {
    let Some(image) = prim_rec_checkpoint_path() else {
        eprintln!("SKIP: /tmp/hol4_prim_rec missing — run tools/build-hol4-checkpoints.sh prim");
        return;
    };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
fun show tag th = pr (tag ^ ": " ^ Parse.thm_to_string th ^ "\n");
val () = pr ("CURRENT=" ^ Theory.current_theory() ^ "\n");
val () = show "num_Axiom"    prim_recTheory.num_Axiom;
val () = show "SIMP_REC_THM" prim_recTheory.SIMP_REC_THM;
val () = show "PRIM_REC_THM" prim_recTheory.PRIM_REC_THM;
val () = show "LESS_THM"     prim_recTheory.LESS_THM;
val () = show "PRE"          prim_recTheory.PRE;
val clean = List.all (fn th => null (Thm.hyp th))
  [prim_recTheory.num_Axiom, prim_recTheory.SIMP_REC_THM,
   prim_recTheory.PRIM_REC_THM, prim_recTheory.LESS_THM, prim_recTheory.PRE];
val () = pr ("ALL_CLEAN=" ^ Bool.toString clean ^ "\n");
(* num_Axiom as a working recursion principle: define dbl by recursion. *)
val dblAx = Drule.ISPECL
  [Parse.Term [QUOTE "0"], Parse.Term [QUOTE "\\(k:num) (r:num). SUC (SUC r)"]]
  prim_recTheory.num_Axiom;
val dblAx2 = Conv.CONV_RULE (Conv.DEPTH_CONV Thm.BETA_CONV) dblAx;
val dbl_spec = Theory.Definition.new_specification("dbl_def", ["dbl"], dblAx2);
val () = show "dbl_spec" dbl_spec;
pr "PRIM_REC_TEST_DONE\n";
"#;
    let Some((out, _)) = run_image_env(&image, driver, 50_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("PRIM_REC_TEST_DONE"),
        "driver did not finish.\n{}",
        tail(&out, 40)
    );
    assert!(
        out.contains("CURRENT=prim_rec"),
        "wrong current theory.\n{}",
        tail(&out, 40)
    );
    assert!(
        out.contains("ALL_CLEAN=true"),
        "a prim_rec theorem has hypotheses.\n{}",
        tail(&out, 40)
    );
    // exact statements of the keystones
    assert!(
        out.contains("∀e f. ∃fn. fn 0 = e ∧ ∀n. fn (SUC n) = f n (fn n)"),
        "num_Axiom not the primitive recursion theorem.\n{}",
        tail(&out, 40)
    );
    assert!(
        out.contains("∀m n. m < SUC n ⇔ m = n ∨ m < n"),
        "LESS_THM wrong.\n{}",
        tail(&out, 40)
    );
    // and the recursion principle WORKS:
    assert!(
        out.contains("dbl 0 = 0 ∧ ∀n. dbl (SUC n) = SUC (SUC (dbl n))"),
        "num_Axiom failed to define a recursive function.\n{}",
        tail(&out, 40)
    );
}
