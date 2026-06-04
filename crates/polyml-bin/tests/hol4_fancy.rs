//! HOL4 "fancy proof" showcase — non-trivial theorems by real tactics.
//!
//! Runs `hol4_support/fancy_proofs.sml` on the warm `/tmp/hol4_simp` checkpoint
//! and asserts the headline theorems prove. `#[ignore]` (needs the chain):
//!
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh        # …-> simp
//! cargo test --release -p polyml-bin --test hol4_fancy -- --ignored --nocapture
//! ```
//!
//! These are genuine theorems, not the p ==> p baseline: the **Drinker Paradox**
//! `⊢ ∃x. D x ⇒ ∀y. D y` (Smullyan's classical theorem, unprovable
//! intuitionistically), classical quantifier duality `⊢ ∀P. (∃x. P x) ⇔ ¬∀x. ¬P x`,
//! and the combinator identity `⊢ S K K = I` — all built by HOL4's real LCF
//! kernel + tactic engine running on the Rust interpreter.

mod common;
use common::*;

/// The full fancy-proofs showcase runs and the headline classical/combinatory
/// theorems all prove (no `=FAIL=`).
#[test]
#[ignore = "slow: needs /tmp/hol4_simp (tools/build-hol4-checkpoints.sh simp)"]
fn fancy_theorems_prove() {
    let Some(image) = simp_checkpoint_path() else {
        eprintln!("SKIP: /tmp/hol4_simp missing — run tools/build-hol4-checkpoints.sh simp");
        return;
    };
    let sml = match std::fs::read_to_string(support_file("fancy_proofs.sml")) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("SKIP: cannot read fancy_proofs.sml: {e}");
            return;
        }
    };
    let Some((out, _)) = run_image_env(&image, &sml, 40_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("FANCY_PROOFS_DONE"),
        "fancy_proofs.sml did not run to completion.\n{}",
        tail(&out, 40)
    );
    // The headline theorems must prove (exact printed forms).
    for sentinel in [
        "=PROVED= [drinker_paradox] \u{22a2} \u{2203}x. D x", // ⊢ ∃x. D x ⇒ ∀y. D y
        "=PROVED= [exists_dual]",
        "=PROVED= [skk_eq_i] \u{22a2} S K K = I",
        "=PROVED= [ex_or_allnot]",
        "=PROVED= [simp_compound]",
    ] {
        assert!(
            out.contains(sentinel),
            "missing fancy proof: {sentinel}\n{}",
            tail(&out, 50)
        );
    }
    assert!(
        !out.contains("=FAIL="),
        "a fancy proof failed.\n{}",
        tail(&out, 50)
    );
}
