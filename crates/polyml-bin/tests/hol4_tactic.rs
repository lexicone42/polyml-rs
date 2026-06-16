//! HOL4 tactic-layer integration tests.
//!
//! These drive HOL4's real tactic engine (src/1: Tactical/Tactic/Conv/Drule/
//! Thm_cont over the synthesized `structure boolTheory`) on the warm
//! `/tmp/hol4_tactic` checkpoint and assert that goal-directed proofs run.
//! `#[ignore]` because they need the checkpoint chain, built once with:
//!
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh        # basis -> kernel -> theory -> parse -> bool -> tactic
//! cargo test --release -p polyml-bin --test hol4_tactic -- --ignored --nocapture
//! ```
//!
//! Provenance of the checkpoint chain (each a real HOL4 layer on our Rust
//! interpreter): kernel (LCF primitives) -> Theory subsystem -> term/type
//! parser (src/parse, 79/79) -> bool theory (src/bool/boolScript.sml run
//! through HOL4's own quote-filter; `structure boolTheory` synthesized from the
//! live segment) -> tactic layer (src/1, 27 files). The goals below are proved
//! by HOL4's actual Tactical.prove + DISCH_TAC/STRIP_TAC/CONJ_TAC/ACCEPT_TAC —
//! goal-directed proof, not raw kernel inference.

mod common;
use common::*;

fn run_tactic(sml: &str) -> Option<(String, i32)> {
    let image = tactic_checkpoint_path()?;
    run_image_env(&image, sml, 30_000_000_000, &[])
}

const SKIP: &str = "SKIP: /tmp/hol4_tactic missing — run tools/build-hol4-checkpoints.sh tactic";

/// HOL4's tactic engine proves goals on our interpreter: implication
/// reflexivity (`p ==> p`), conjunction commutativity (`p /\ q ==> q /\ p`),
/// and a K-combinator goal (`q ==> p ==> q`) — each via real tactics.
#[test]
#[ignore = "slow: needs /tmp/hol4_tactic (tools/build-hol4-checkpoints.sh tactic)"]
fn tactics_prove_propositional_goals() {
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
fun proved tag tac q =
  (let val th = Tactical.prove (Parse.Term [QUOTE q], tac)
   in if boolSyntax.is_imp (Thm.concl th) andalso null (Thm.hyp th)
      then pr ("PROVED " ^ tag ^ "\n") else pr ("BAD " ^ tag ^ "\n")
   end) handle e => pr ("FAIL " ^ tag ^ " :: " ^ exnMessage e ^ "\n");
val () = proved "imp-refl"
  (Tactical.THEN (Tactic.DISCH_TAC, Tactical.POP_ASSUM Tactic.ACCEPT_TAC))
  "p ==> p";
val () = proved "conj-comm"
  (Tactical.THEN (Tactic.STRIP_TAC,
     Tactical.THEN (Tactic.CONJ_TAC, Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC)))
  "p /\\ q ==> q /\\ p";
val () = proved "k-comb"
  (Tactical.THEN (Tactic.STRIP_TAC,
     Tactical.THEN (Tactic.STRIP_TAC, Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC)))
  "q ==> p ==> q";
val () = pr "TACTIC_TEST_DONE\n";
"#;
    let Some((out, _code)) = run_tactic(driver) else {
        eprintln!("{SKIP}");
        return;
    };
    for tag in ["imp-refl", "conj-comm", "k-comb"] {
        assert!(
            out.contains(&format!("PROVED {tag}")),
            "tactic proof '{tag}' did not succeed.\n{}",
            tail(&out, 40)
        );
    }
    assert!(
        out.contains("TACTIC_TEST_DONE") && !out.contains("FAIL ") && !out.contains("BAD "),
        "a tactic proof failed or produced the wrong theorem.\n{}",
        tail(&out, 40)
    );
}
