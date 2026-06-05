//! HOL4 arithmetic library — Peano laws proved by induction on the polyml-rs
//! interpreter, persisted in `structure numArith` on `/tmp/hol4_arith`.
//!
//! `#[ignore]` (needs the chain → arith):
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh arith     # …-> num -> arith
//! cargo test --release -p polyml-bin --test hol4_arith -- --ignored --nocapture
//! ```
//!
//! `add`/`mult`/`EVEN`/`ODD` are defined from `num_Axiom` (primitive recursion),
//! and the laws are proved by `INDUCT_TAC` — no bool_ss / SAT subsystem (the
//! `HO_REWR_CONV` technique replaces it). Headline: `ADD_COMM`, `MULT_COMM`, and
//! the parity theorem `|- !m n. EVEN (m + n) <=> (EVEN m <=> EVEN n)`.

mod common;
use common::*;

/// The arithmetic library reloads and its theorems are the genuine Peano laws,
/// reachable via `structure numArith` (so no re-derivation on reload).
#[test]
#[ignore = "slow: needs /tmp/hol4_arith (tools/build-hol4-checkpoints.sh arith)"]
fn arithmetic_library_present() {
    let Some(image) = arith_checkpoint_path() else {
        eprintln!("SKIP: /tmp/hol4_arith missing — run tools/build-hol4-checkpoints.sh arith");
        return;
    };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
fun show tag th = pr (tag ^ ": " ^ Parse.thm_to_string th ^ "\n");
val () = show "ADD_COMM"          numArith.ADD_COMM;
val () = show "ADD_ASSOC"         numArith.ADD_ASSOC;
val () = show "MULT_COMM"         numArith.MULT_COMM;
val () = show "RIGHT_ADD_DISTRIB" numArith.RIGHT_ADD_DISTRIB;
val () = show "ADD_RCANCEL"       numArith.ADD_RCANCEL;
val () = show "EVEN_ADD"          numArith.EVEN_ADD;
(* all hypothesis-free *)
val clean = List.all (fn th => null (Thm.hyp th))
  [numArith.ADD_COMM, numArith.ADD_ASSOC, numArith.MULT_COMM,
   numArith.RIGHT_ADD_DISTRIB, numArith.ADD_RCANCEL, numArith.EVEN_ADD];
val () = pr ("ALL_CLEAN=" ^ Bool.toString clean ^ "\n");
pr "ARITH_TEST_DONE\n";
"#;
    let Some((out, _)) = run_image_env(&image, driver, 20_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(out.contains("ARITH_TEST_DONE"), "arith driver did not finish.\n{}", tail(&out, 40));
    assert!(out.contains("ALL_CLEAN=true"), "an arithmetic law has hypotheses.\n{}", tail(&out, 40));
    // exact theorem statements (commutativity of + and *, and the parity law)
    for (tag, stmt) in [
        ("ADD_COMM", "∀m n. m + n = n + m"),
        ("MULT_COMM", "∀m n. mult m n = mult n m"),
        ("EVEN_ADD", "∀m n. EVEN (m + n) ⇔ (EVEN m ⇔ EVEN n)"),
    ] {
        assert!(
            out.contains(stmt),
            "{tag} not the expected statement `{stmt}`.\n{}",
            tail(&out, 40)
        );
    }
    assert!(!out.contains("_FAIL") && !out.contains("not been declared"),
        "an arithmetic theorem was unreachable.\n{}", tail(&out, 40));
}
