//! HOL4 first-order automated proving (mesonLib / MESON_TAC) on the polyml-rs
//! interpreter. MESON is a model-elimination prover: it Skolemizes, instantiates
//! quantifiers by first-order unification, and chains inferences — things plain
//! rewriting / tautLib cannot do.
//!
//! `#[ignore]` (needs the chain → meson):
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh meson     # …simp -> meson (replays taut layer)
//! cargo test --release -p polyml-bin --test hol4_meson -- --ignored --nocapture
//! ```
//!
//! This cascades directly from the SAT-wall fix: mesonLib `open`s tautLib at
//! load, and tautLib now runs via HOL4's pure-SML DPLL solver (see hol4_taut.rs).

mod common;
use common::*;

#[test]
#[ignore = "slow: needs /tmp/hol4_meson (tools/build-hol4-checkpoints.sh meson)"]
fn meson_tac_proves_first_order_goals() {
    let Some(image) = meson_checkpoint_path() else {
        eprintln!("SKIP: /tmp/hol4_meson missing — run tools/build-hol4-checkpoints.sh meson");
        return;
    };
    // Each goal genuinely needs first-order reasoning (quantifier instantiation /
    // Skolemization), which MESON_TAC provides and rewriting does not.
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val () = mesonLib.chatting := 0;
fun chk tag q =
  let val g = Parse.Term [QUOTE q]
      val th = Tactical.prove(g, mesonLib.MESON_TAC [])
  in pr ("TH " ^ tag ^ ": " ^ Parse.thm_to_string th ^ "\n");
     pr ("HYPS " ^ tag ^ "=" ^ Int.toString (length (Thm.hyp th)) ^ "\n")
  end handle e => pr ("ERR " ^ tag ^ " :: " ^ exnMessage e ^ "\n");
(* universal instantiation + modus ponens *)
val () = chk "SYLL"  "(!x. P x ==> Q x) /\\ P a ==> Q a";
(* the drinker paradox — needs Skolemization + classical reasoning *)
val () = chk "DRINK" "?x. D x ==> !y. D y";
(* symmetric + transitive relation, instantiated and chained *)
val () = chk "REL"   "(!x y. R x y ==> R y x) /\\ (!x y z. R x y /\\ R y z ==> R x z) /\\ R a b ==> R a a";
pr "MESON_TEST_DONE\n";
"#;
    let Some((out, _)) = run_image_env(&image, driver, 50_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("MESON_TEST_DONE"),
        "meson driver did not finish.\n{}",
        tail(&out, 40)
    );
    for (tag, stmt) in [
        ("SYLL", "⊢ (∀x. P x ⇒ Q x) ∧ P a ⇒ Q a"),
        ("DRINK", "⊢ ∃x. D x ⇒ ∀y. D y"),
        (
            "REL",
            "⊢ (∀x y. R x y ⇒ R y x) ∧ (∀x y z. R x y ∧ R y z ⇒ R x z) ∧ R a b ⇒ R a a",
        ),
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
    assert!(
        !out.contains("ERR "),
        "a MESON goal failed to prove.\n{}",
        tail(&out, 40)
    );
}
