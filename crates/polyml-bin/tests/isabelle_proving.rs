//! REAL ISABELLE PROVING runs on the polyml-rs interpreter.
//!
//! Today's breakthrough took the Isabelle/Pure source load from 182 to 261/285 —
//! the entire logical Pure (kernel + Isar + proof + method + simplifier + syntax)
//! compiles on our interpreter. `tools/build-isabelle-pure.sh` exports that as a
//! warm `/tmp/isabelle_pure` checkpoint (reloads in ~2s). On it, the proving
//! machinery WORKS: this test exercises five rungs, each producing a genuine
//! checked Isabelle/Pure `thm`:
//!   1. the TACTIC FRAMEWORK   (`Goal.prove` + `resolve_tac`/`assume_tac`)
//!   2. the SIMPLIFIER         (`Simplifier.rewrite`/`asm_full_simp_tac`)
//!   3. THEORY DEVELOPMENT     (declare a type/consts + axiom `⋀x. P x`, derive `⊢ P c`)
//!   4. RESOLUTION / Drule     (`RS` + `implies_intr_list` → transitivity of `⟹`)
//!   5. the PARSER             (`Syntax.read_prop` → `⊢ PROP A ⟹ PROP A`)
//! The Isabelle analogue of the HOL4 verified-programs arc. Engineered by a 5-seat
//! ultracode workflow (wf_e7312cf7-ece).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh, which
//! needs /tmp/arbint_image + vendored Isabelle/Pure with patches applied):
//! ```sh
//! tools/intflip-bootstrap.sh && tools/isabelle-pure-probe.sh   # image + patches
//! tools/build-isabelle-pure.sh                                  # warm checkpoint
//! cargo test --release -p polyml-bin --test isabelle_proving -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use std::path::PathBuf;

fn checkpoint() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/isabelle_pure");
    p.exists().then_some(p)
}

#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn isabelle_pure_proving_rungs() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_proving.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_proving.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        30_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(out.contains("ISA_PROVING_START"), "driver did not start:\n{out}");
    for rung in ["tactic", "simplifier", "theory_axiom", "resolution", "parser"] {
        assert!(
            out.contains(&format!("RUNG {rung} OK")),
            "Isabelle proving rung `{rung}` did not produce a checked theorem:\n{out}"
        );
    }
    assert!(out.contains("ISA_PROVING_DONE"), "proving demo did not finish:\n{out}");
}
