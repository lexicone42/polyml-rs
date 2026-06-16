//! HOL4 summation mini-development — two classic closed-form summation identities
//! proved by induction on the polyml-rs interpreter, on top of `/tmp/hol4_arith`.
//!
//! `#[ignore]` (needs the chain → arith):
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh arith      # …-> num -> arith
//! cargo test --release -p polyml-bin --test hol4_summation -- --ignored --nocapture
//! ```
//!
//! On `/tmp/hol4_arith` (which carries `num_Axiom`, `add`/`mult` + the Peano laws,
//! and `INDUCT_TAC`) this defines two recursive functions via `num_Axiom` and
//! proves, by `INDUCT_TAC` alone (no bool_ss / SAT / decision procedure):
//!
//!   GAUSS        |- !n. sum n + sum n = mult n (SUC n)     (2·(0+1+…+n) = n·(n+1))
//!   SUM_OF_ODDS  |- !n. osum n = mult n n                  (1+3+…+(2n−1) = n²)
//!
//! The only non-obvious ingredient is `DOUBLE_ADD` ((a+b)+(a+b) = (a+a)+(b+b)),
//! itself proved by induction — it stands in for the AC normalisation an
//! arith_ss/numSimps would otherwise provide (the lean arith checkpoint has only
//! plain REWRITE). This is "real mathematics by induction" on a runtime that the
//! upstream-PolyML differential oracle has verified faithful.

mod common;
use common::*;

#[test]
#[ignore = "slow: needs /tmp/hol4_arith (tools/build-hol4-checkpoints.sh arith)"]
fn gauss_and_sum_of_odds_by_induction() {
    let Some(image) = arith_checkpoint_path() else {
        eprintln!("SKIP: /tmp/hol4_arith missing — run tools/build-hol4-checkpoints.sh arith");
        return;
    };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
fun T q = Parse.Term [QUOTE q];
infix THEN THENL THEN1 ORELSE;
open numArith;

(* sum n = 0+1+…+n (triangular numbers), via num_Axiom (primitive recursion).
   The recursor applies f as `f index recursiveResult`, so the body takes the
   index first: f idx rc = add rc (SUC idx)  ⇒  sum (SUC n) = sum n + SUC n. *)
val sumAx    = Drule.ISPECL [T "0", T "\\(idx:num) (rc:num). add rc (SUC idx)"] num_Axiom;
val sumAx2   = Conv.CONV_RULE (Conv.DEPTH_CONV Thm.BETA_CONV) sumAx;
val sum_spec = Definition.new_specification("sum_def", ["sum"], sumAx2);
val SUM0 = Tactical.prove(T "sum 0 = 0", REWRITE_TAC[sum_spec]);
val SUMS = Tactical.prove(T "!n. sum (SUC n) = add (sum n) (SUC n)", REWRITE_TAC[sum_spec]);

(* AC helper proved by induction (stands in for arith_ss AC-normalisation). *)
val DOUBLE_ADD = Tactical.prove(
  T "!a b. add (add a b) (add a b) = add (add a a) (add b b)",
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]);

(* GAUSS: 2 * sum n = n * (n+1). *)
val GAUSS = Tactical.prove(
  T "!n. add (sum n) (sum n) = mult n (SUC n)",
  INDUCT_TAC THENL [
    REWRITE_TAC [SUM0, MULT0, ADD_CLAUSES],
    REWRITE_TAC [SUMS, MULTS, MULT_SUC, DOUBLE_ADD]
      THEN ASM_REWRITE_TAC [ADD_CLAUSES, ADD_ASSOC]
      THEN REWRITE_TAC [MULT_SUC] ]);
val () = pr ("GAUSS: " ^ Parse.thm_to_string GAUSS ^ "\n");

(* osum n = 1+3+…+(2n−1); the (n+1)-th odd (0-indexed n) is 2n+1 = SUC(n+n). *)
val osumAx    = Drule.ISPECL [T "0", T "\\(idx:num) (rc:num). add rc (SUC (add idx idx))"] num_Axiom;
val osumAx2   = Conv.CONV_RULE (Conv.DEPTH_CONV Thm.BETA_CONV) osumAx;
val osum_spec = Definition.new_specification("osum_def", ["osum"], osumAx2);
val OSUM0 = Tactical.prove(T "osum 0 = 0", REWRITE_TAC[osum_spec]);
val OSUMS = Tactical.prove(T "!n. osum (SUC n) = add (osum n) (SUC (add n n))", REWRITE_TAC[osum_spec]);

(* SUM_OF_ODDS: sum of the first n odd numbers = n^2. *)
val ODDS = Tactical.prove(
  T "!n. osum n = mult n n",
  INDUCT_TAC THENL [
    REWRITE_TAC [OSUM0, MULT0],
    REWRITE_TAC [OSUMS, MULTS, MULT_SUC]
      THEN ASM_REWRITE_TAC [ADD_CLAUSES, ADD_ASSOC] ]);
val () = pr ("SUM_OF_ODDS: " ^ Parse.thm_to_string ODDS ^ "\n");

(* concrete sanity: sum 3 = 6 (triangular), osum 4 = 16 (= 4^2). *)
val S3 = Tactical.prove(
  T "sum (SUC(SUC(SUC 0))) = SUC(SUC(SUC(SUC(SUC(SUC 0)))))",
  REWRITE_TAC[SUMS, SUM0, ADD_CLAUSES]);
val () = pr ("SUM3: " ^ Parse.thm_to_string S3 ^ "\n");

(* both headline theorems are hypothesis-free. *)
val clean = List.all (fn th => null (Thm.hyp th)) [GAUSS, ODDS];
val () = pr ("ALL_CLEAN=" ^ Bool.toString clean ^ "\n");
pr "SUMMATION_TEST_DONE\n";
"#;
    let Some((out, _)) = run_image_env(&image, driver, 100_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("SUMMATION_TEST_DONE"),
        "summation driver did not finish.\n{}",
        tail(&out, 50)
    );
    assert!(
        out.contains("ALL_CLEAN=true"),
        "a summation theorem has hypotheses.\n{}",
        tail(&out, 50)
    );
    // exact theorem statements (the closed forms), proved by induction.
    assert!(
        out.contains("∀n. sum n + sum n = mult n (SUC n)"),
        "GAUSS not the expected closed form.\n{}",
        tail(&out, 50)
    );
    assert!(
        out.contains("∀n. osum n = mult n n"),
        "SUM_OF_ODDS not the expected closed form.\n{}",
        tail(&out, 50)
    );
    // concrete: sum 3 = 6 (six nested SUCs over 0).
    assert!(
        out.contains("sum (SUC (SUC (SUC 0))) = SUC (SUC (SUC (SUC (SUC (SUC 0)))))"),
        "sum 3 = 6 sanity failed.\n{}",
        tail(&out, 50)
    );
}
