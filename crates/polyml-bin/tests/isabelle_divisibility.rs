//! DIVISIBILITY on ℕ — a preorder compatible with + and ·, refining the order —
//! proved in Isabelle/Pure on the polyml-rs interpreter. The number-theory rung
//! above the linear order (`isabelle_ordering.rs`), and the gateway toward GCD /
//! primes.
//!
//! Defines `a ∣ b ≝ ∃k. b = a·k` (an ML abbreviation over the existing existential
//! quantifier) on the full ladder (semiring + existential + order), and proves the
//! divisibility structure, each a 0-hypothesis theorem by pure LCF kernel inference:
//!   dvd_refl `⊢ a∣a`   one_dvd `⊢ 1∣n`   dvd_zero `⊢ a∣0`
//!   dvd_trans      `⊢ a∣b ⟹ b∣c ⟹ a∣c`           (transitivity ⇒ PREORDER)
//!   dvd_add        `⊢ d∣m ⟹ d∣n ⟹ d∣(m+n)`
//!   dvd_mult_right `⊢ a∣b ⟹ a∣(b·c)`,  dvd_mult_cong `⊢ a∣b ⟹ (a·c)∣(b·c)`  (· compat)
//!   dvd_le         `⊢ d∣n ⟹ n≠0 ⟹ d ≤ n`          (CAPSTONE: ties ∣ to the order)
//! `dvd_le` (the capstone) uses a num-cases lemma + `mult_Suc_right` + the Peano
//! discrimination axiom (the n≠0 premise is a meta-implication `oeq n 0 ⟹ oFalse`).
//! Soundness probes (in the source proofs) confirm the kernel rejects false variants.
//!
//! Engineered by a foundation→fan-out→merge ultracode workflow (wf_2eb4085c-828):
//! one agent defined `dvd` + the easy lemmas, four seats each proved a divisibility
//! law independently (incl. the `dvd_le` capstone), a fifth merged them —
//! independent agreement is the correctness signal.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_divisibility -- --ignored --nocapture
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
fn divisibility_is_a_preorder_compatible_with_plus_and_times() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_divisibility.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_divisibility.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        160_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // each divisibility law is a checked theorem (driver prints `OK <name>` only
    // when hyps = 0 AND prop aconv the intended goal)
    for law in [
        "dvd_refl",
        "one_dvd",
        "dvd_zero",
        "dvd_trans",
        "dvd_add",
        "dvd_mult_right",
        "dvd_mult_cong",
        "dvd_le",
    ] {
        assert!(
            out.contains(&format!("OK {law}")),
            "divisibility law `{law}` did not produce a checked theorem:\n{out}"
        );
    }
    // printed only when all eight OK gates fired
    assert!(
        out.contains("DVD_DONE"),
        "divisibility development did not complete:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
}
