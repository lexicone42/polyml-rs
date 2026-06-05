//! HOL4 propositional tautology proving (tautLib / HolSatLib) on the polyml-rs
//! interpreter, via HOL4's *pure-SML* DPLL solver — no external minisat.
//!
//! `#[ignore]` (needs the chain → taut):
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh taut      # …combin -> taut
//! cargo test --release -p polyml-bin --test hol4_taut -- --ignored --nocapture
//! ```
//!
//! WHY THIS MATTERS: HOL4's SAT subsystem was previously believed to block the
//! whole Datatype / bool_ss / METIS layer because `HolSatLib` "shells out to an
//! external minisat binary". It does not, on our runtime: `minisatProve`
//! gates the external solver on `access(solverExe,[A_EXEC])`, the binary is
//! absent, our `fs_access` returns false, and the call falls through to the
//! pure-SML `DPLL_TAUT` prover — genuine kernel inference. The only real gap
//! was `OS.FileSys.tmpName` (IO subcode 67), which dimacsTools writes before the
//! DPLL fallback fires; that (and `OS.FileSys.remove`) are now implemented in
//! rts.rs. So `tautLib.TAUT_PROVE` proves real propositional tautologies here.

mod common;
use common::*;

#[test]
#[ignore = "slow: needs /tmp/hol4_taut (tools/build-hol4-checkpoints.sh taut)"]
fn tautlib_proves_tautologies_via_dpll() {
    let Some(image) = taut_checkpoint_path() else {
        eprintln!("SKIP: /tmp/hol4_taut missing — run tools/build-hol4-checkpoints.sh taut");
        return;
    };
    // Each TAUT_PROVE drives the full HolSat pipeline (CNF -> dimacs tmpfile ->
    // access-gate false -> DPLL_TAUT) and returns a real kernel theorem.
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
fun chk tag q =
  let val th = tautLib.TAUT_PROVE (Parse.Term [QUOTE q])
  in pr ("TH " ^ tag ^ ": " ^ Parse.thm_to_string th ^ "\n");
     pr ("HYPS " ^ tag ^ "=" ^ Int.toString (length (Thm.hyp th)) ^ "\n")
  end handle e => pr ("ERR " ^ tag ^ " :: " ^ exnMessage e ^ "\n");
val () = chk "EM"     "p \\/ ~p";
val () = chk "DM"     "~(p /\\ q) <=> ~p \\/ ~q";
val () = chk "SYLL"   "(p ==> q) /\\ (q ==> r) ==> (p ==> r)";
val () = chk "PEIRCE" "((p ==> q) ==> p) ==> p";
pr "TAUT_TEST_DONE\n";
"#;
    let Some((out, _)) = run_image_env(&image, driver, 20_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(out.contains("TAUT_TEST_DONE"), "taut driver did not finish.\n{}", tail(&out, 40));
    // Each must be a proved theorem (turnstile) with zero hypotheses.
    for (tag, stmt) in [
        ("EM", "⊢ p ∨ ¬p"),
        ("DM", "⊢ ¬(p ∧ q) ⇔ ¬p ∨ ¬q"),
        ("SYLL", "⊢ (p ⇒ q) ∧ (q ⇒ r) ⇒ p ⇒ r"),
        ("PEIRCE", "⊢ ((p ⇒ q) ⇒ p) ⇒ p"),
    ] {
        assert!(
            out.contains(&format!("TH {tag}: {stmt}")),
            "{tag} not proved as `{stmt}`.\n{}",
            tail(&out, 40)
        );
        assert!(
            out.contains(&format!("HYPS {tag}=0")),
            "{tag} should be proved with no hypotheses.\n{}",
            tail(&out, 40)
        );
    }
    assert!(!out.contains("ERR "), "a tautology failed to prove.\n{}", tail(&out, 40));
}
