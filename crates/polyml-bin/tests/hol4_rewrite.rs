//! HOL4 REWRITE_TAC (rewriting engine) integration tests.
//!
//! These drive HOL4's real rewriting tactic (src/1/Rewrite, REWRITE_TAC and
//! friends) on the warm `/tmp/hol4_rewrite` checkpoint and assert that
//! rewrite-based proofs run. `#[ignore]` because they need the checkpoint
//! chain, built once with:
//!
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh        # …-> tactic -> rewrite
//! cargo test --release -p polyml-bin --test hol4_rewrite -- --ignored --nocapture
//! ```
//!
//! REWRITE_TAC is the first *automated* tactic: it normalizes a goal with a set
//! of equational rewrite rules. The engine is just BoundedRewrites + Rewrite on
//! top of the tactic checkpoint (Net + Conv's REWR_CONV are already present);
//! the default rewrite set carries 11 boolTheory clauses, so `REWRITE_TAC []`
//! simplifies boolean goals with no explicit lemmas.

mod common;
use common::*;

fn run_rewrite(sml: &str) -> Option<(String, i32)> {
    let image = rewrite_checkpoint_path()?;
    run_image_env(&image, sml, 30_000_000_000, &[])
}

const SKIP: &str =
    "SKIP: /tmp/hol4_rewrite missing — run tools/build-hol4-checkpoints.sh rewrite";

/// `REWRITE_TAC []` proves boolean goals via the default rewrite set, explicit
/// `REWRITE_TAC [thm]` and `ASM_REWRITE_TAC`/`ONCE_REWRITE_TAC` also work, and
/// the default rewrite set is populated (11 boolTheory clauses).
#[test]
#[ignore = "slow: needs /tmp/hol4_rewrite (tools/build-hol4-checkpoints.sh rewrite)"]
fn rewrite_tac_simplifies_boolean_goals() {
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val () = pr ("IMPLICIT_SIZE "
  ^ Int.toString (length (Rewrite.dest_rewrites (Rewrite.implicit_rewrites()))) ^ "\n");
fun proved tag tac q =
  (let val th = Tactical.prove (Parse.Term [QUOTE q], tac)
   in if null (Thm.hyp th) then pr ("PROVED " ^ tag ^ "\n")
      else pr ("BAD " ^ tag ^ " (hyps)\n")
   end) handle e => pr ("FAIL " ^ tag ^ " :: " ^ exnMessage e ^ "\n");
val () = proved "rw-and-T"  (Rewrite.REWRITE_TAC [])                       "(T /\\ p) <=> p";
val () = proved "rw-or-T"   (Rewrite.REWRITE_TAC [])                       "p \\/ T";
val () = proved "rw-dneg"   (Rewrite.REWRITE_TAC [])                       "~~p <=> p";
val () = proved "rw-thm"    (Rewrite.REWRITE_TAC [boolTheory.AND_CLAUSES]) "(T /\\ p) <=> p";
val () = proved "asm-rw"
  (Tactical.THEN (Tactic.STRIP_TAC, Rewrite.ASM_REWRITE_TAC [])) "p ==> (p /\\ T)";
(* ONCE_REWRITE_TAC does a single pass (T /\ p -> p), leaving p <=> p for REFL_TAC. *)
val () = proved "once-rw"
  (Tactical.THEN (Rewrite.ONCE_REWRITE_TAC [], Tactic.REFL_TAC)) "(T /\\ p) <=> p";
val () = pr "REWRITE_TEST_DONE\n";
"#;
    let Some((out, _code)) = run_rewrite(driver) else {
        eprintln!("{SKIP}");
        return;
    };
    assert!(
        out.contains("IMPLICIT_SIZE 11"),
        "default rewrite set not populated (expected 11 boolTheory clauses).\n{}",
        tail(&out, 40)
    );
    for tag in ["rw-and-T", "rw-or-T", "rw-dneg", "rw-thm", "asm-rw", "once-rw"] {
        assert!(
            out.contains(&format!("PROVED {tag}")),
            "REWRITE_TAC proof '{tag}' did not succeed.\n{}",
            tail(&out, 40)
        );
    }
    assert!(
        out.contains("REWRITE_TEST_DONE")
            && !out.contains("FAIL ")
            && !out.contains("BAD "),
        "a REWRITE_TAC proof failed or produced the wrong theorem.\n{}",
        tail(&out, 40)
    );
}
