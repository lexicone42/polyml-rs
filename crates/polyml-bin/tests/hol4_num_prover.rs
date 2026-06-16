//! The unified foundation toward the HOL4 Datatype package: the REAL `numTheory`
//! (HOL4's `numScript.sml`, not a hand-roll) coexisting with the FULL prover stack
//! (`bool_ss` with real EXISTS_UNIQUE machinery, `MESON_TAC`) on one checkpoint.
//!
//! `#[ignore]` (needs /tmp/hol4_num on the prover base):
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh num     # now built on /tmp/hol4_metis
//! cargo test --release -p polyml-bin --test hol4_num_prover -- --ignored --nocapture
//! ```
//!
//! WHY THIS MATTERS: HOL4's `Datatype` package needs `ind_typeTheory`, whose
//! ancestors are `num prim_rec arithmetic numpair` and which simplifies with
//! `bool_ss ++ numSimps`. Our `num` branch and prover branch had diverged at
//! `combin`; this checkpoint re-bases `num` on the prover stack, so the real
//! `numTheory` and `bool_ss`/`MESON` are live together — the first stage of the
//! arithmetic foundation under Datatype. The discriminating check that the *real*
//! `bool_ss` (not the old hand-rolled simpset) is present is that it simplifies a
//! genuine `∃!` (EXISTS_UNIQUE) goal.

mod common;
use common::*;

#[test]
#[ignore = "slow: needs /tmp/hol4_num on the prover base (build-hol4-checkpoints.sh num)"]
fn real_num_theory_and_full_bool_ss_coexist() {
    let Some(image) = num_checkpoint_path() else {
        eprintln!("SKIP: /tmp/hol4_num missing — run tools/build-hol4-checkpoints.sh num");
        return;
    };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val () = pr ("IND: " ^ Parse.thm_to_string numTheory.INDUCTION ^ "\n");
(* the REAL bool_ss: simplify a genuine EXISTS_UNIQUE goal (the old hand-rolled
   simpset could not — this is the discriminating check). *)
val () = (let val th = simpLib.SIMP_CONV boolSimps.bool_ss [] (Parse.Term [QUOTE "?!x. x = a"])
          in pr ("BOOLSS: " ^ Parse.thm_to_string th ^ "\n") end)
         handle e => pr ("BOOLSS_FAIL " ^ exnMessage e ^ "\n");
(* the prover stack is live alongside num *)
val () = (let val th = Tactical.prove(Parse.Term [QUOTE "(!x. P x ==> Q x) /\\ P a ==> Q a"], mesonLib.MESON_TAC [])
          in pr ("MESON: " ^ Parse.thm_to_string th ^ "\n") end)
         handle e => pr ("MESON_FAIL " ^ exnMessage e ^ "\n");
pr "NUMPROVER_DONE\n";
"#;
    let Some((out, _)) = run_image_env(&image, driver, 20_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("NUMPROVER_DONE"),
        "driver did not finish.\n{}",
        tail(&out, 30)
    );
    // real numScript INDUCTION
    assert!(
        out.contains("IND: ⊢ ∀P. P 0 ∧ (∀n. P n ⇒ P (SUC n)) ⇒ ∀n. P n"),
        "numTheory.INDUCTION is not the real numScript statement.\n{}",
        tail(&out, 30)
    );
    // real bool_ss simplifies ∃! to T
    assert!(
        out.contains("BOOLSS: ⊢ (∃!x. x = a) ⇔ T"),
        "bool_ss did not simplify the EXISTS_UNIQUE goal (real bool_ss absent?).\n{}",
        tail(&out, 30)
    );
    assert!(
        !out.contains("BOOLSS_FAIL"),
        "bool_ss raised.\n{}",
        tail(&out, 30)
    );
    // MESON live alongside num
    assert!(
        out.contains("MESON: ⊢ (∀x. P x ⇒ Q x) ∧ P a ⇒ Q a"),
        "MESON_TAC not working on the num checkpoint.\n{}",
        tail(&out, 30)
    );
}
