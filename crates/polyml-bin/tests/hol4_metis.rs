//! HOL4 METIS (metisLib / METIS_TAC) on the polyml-rs interpreter — Joe Hurd's
//! resolution + paramodulation prover, the strongest of HOL4's first-order
//! automation, where MESON is weak (equality reasoning).
//!
//! `#[ignore]` (needs the chain → metis):
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh metis     # …simp(real markerLib) -> meson -> metis
//! cargo test --release -p polyml-bin --test hol4_metis -- --ignored --nocapture
//! ```
//!
//! Building this required: a real `markerLib` (the rewriting functions) in the
//! simp layer so the FULL `bool_ss` loads; the 33-module `mlib*` prover core;
//! `normalForms`/`folTools` (with a COND_COND proof patched to a case-split, since
//! our simp does not rewrite CONDs through atomic-bool assumptions); and the
//! realToInt interpreter fix.
//!
//! KNOWN LIMITATION (honest): mlib's time-slice scheduler interacts with our
//! runtime's timing such that cumulative heavy proving in ONE process eventually
//! raises a spurious `Time` exception (mlibOmega's `Time.fromSeconds`). It resets
//! on a fresh image load, and is NOT a soundness issue (every returned theorem is
//! real). So this test runs each goal group in its own fresh `poly` process.

mod common;
use common::*;

fn prove_on_metis(driver: &str) -> Option<String> {
    let image = metis_checkpoint_path()?;
    run_image_env(&image, driver, 50_000_000_000, &[]).map(|(out, _)| out)
}

#[test]
#[ignore = "slow: needs /tmp/hol4_metis (tools/build-hol4-checkpoints.sh metis)"]
fn metis_proves_paramodulation_goal() {
    if metis_checkpoint_path().is_none() {
        eprintln!("SKIP: /tmp/hol4_metis missing — run tools/build-hol4-checkpoints.sh metis");
        return;
    }
    // AC_CHAIN: reverse a 4-deep product using only commutativity + associativity.
    // This is the HOL4 README's own METIS showcase — genuine ordered paramodulation
    // that plain MESON cannot do. (Heavy; run alone in this fresh process.)
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val () = (Feedback.set_trace "metis" 0) handle _ => ();
val g = Parse.Term [QUOTE "(!x y. mul x y = mul y x) /\\ (!x y z. mul (mul x y) z = mul x (mul y z)) ==> mul (mul (mul a b) c) d = mul d (mul c (mul b a))"];
val () = (let val th = Tactical.prove(g, metisLib.METIS_TAC [])
          in pr ("METIS_AC: " ^ Parse.thm_to_string th ^ " HYPS=" ^ Int.toString (length (Thm.hyp th)) ^ "\n") end)
         handle e => pr ("METIS_AC_FAIL " ^ exnMessage e ^ "\n");
pr "METIS_TEST_DONE\n";
"#;
    let out = prove_on_metis(driver).expect("poly spawn");
    assert!(out.contains("METIS_TEST_DONE"), "driver did not finish.\n{}", tail(&out, 30));
    assert!(
        out.contains("METIS_AC: ⊢ (∀x y. mul x y = mul y x) ∧")
            && out.contains("HYPS=0"),
        "AC_CHAIN not proved by METIS_TAC (0 hyps).\n{}",
        tail(&out, 30)
    );
}

#[test]
#[ignore = "slow: needs /tmp/hol4_metis (tools/build-hol4-checkpoints.sh metis)"]
fn metis_proves_equality_and_first_order() {
    if metis_checkpoint_path().is_none() {
        eprintln!("SKIP: /tmp/hol4_metis missing — run tools/build-hol4-checkpoints.sh metis");
        return;
    }
    // One METIS proof per fresh process (the robust regime — see the known
    // limitation above): an equality-congruence chain, then a first-order
    // syllogism, each in its own `poly` invocation. Both 0-hypothesis theorems.
    fn one(tag: &str, q: &str) -> String {
        let driver = format!(
            "fun pr s = (print s; TextIO.flushOut TextIO.stdOut);\n\
             val () = (Feedback.set_trace \"metis\" 0) handle _ => ();\n\
             val () = (let val th = Tactical.prove(Parse.Term [QUOTE \"{q}\"], metisLib.METIS_TAC [])\n\
                       in pr (\"M {tag}: \" ^ Parse.thm_to_string th ^ \" HYPS=\" ^ Int.toString (length (Thm.hyp th)) ^ \"\\n\") end)\n\
                      handle e => pr (\"M_FAIL {tag} \" ^ exnMessage e ^ \"\\n\");\n\
             pr \"METIS_TEST_DONE\\n\";\n"
        );
        prove_on_metis(&driver).expect("poly spawn")
    }
    let cong = one("CONG", r"(a = b) /\\ (b = c) /\\ (c = d) ==> (f a = f d)");
    assert!(cong.contains("METIS_TEST_DONE"), "CONG driver did not finish.\n{}", tail(&cong, 30));
    assert!(cong.contains("M CONG: ⊢ a = b ∧ b = c ∧ c = d ⇒ f a = f d HYPS=0"),
        "equality-congruence not proved.\n{}", tail(&cong, 30));

    let syll = one("SYLL", r"(!x. P x ==> Q x) /\\ P a ==> Q a");
    assert!(syll.contains("METIS_TEST_DONE"), "SYLL driver did not finish.\n{}", tail(&syll, 30));
    assert!(syll.contains("M SYLL: ⊢ (∀x. P x ⇒ Q x) ∧ P a ⇒ Q a HYPS=0"),
        "syllogism not proved.\n{}", tail(&syll, 30));
}
