//! ℕ IS A COMMUTATIVE SEMIRING, proved BY INDUCTION in Isabelle/Pure on the
//! polyml-rs interpreter — the Isabelle analogue of the HOL4 arith trophies, one
//! rung up from `isabelle_arithmetic.rs`.
//!
//! Building on the Peano object logic (type `nat` with Zero/Suc, object equality
//! with refl+subst, the `nat` induction axiom), this development defines
//! multiplication (recursion on the 1st arg, matching `add`) and proves the FULL
//! commutative-semiring law set — every one a 0-hypothesis theorem, by genuine
//! induction (no automation, pure LCF kernel inference):
//!   add_0_right   `⊢ n + 0 = n`              add_comm  `⊢ m + n = n + m`
//!   add_assoc     `⊢ (m+n)+k = m+(n+k)`
//!   mult_0_right  `⊢ n * 0 = 0`              mult_1_right `⊢ n * 1 = n`
//!   mult_comm     `⊢ m * n = n * m`          mult_assoc   `⊢ (m*n)*k = m*(n*k)`
//!   left_distrib  `⊢ k*(m+n) = k*m + k*n`    right_distrib `⊢ (m+n)*k = m*k + n*k`
//! Together: (ℕ, +, ·, 0, 1) is a commutative semiring — real algebra, kernel-
//! checked by Isabelle/Pure running on our Rust PolyML. Each proof asserts
//! `hyps = 0` AND `prop aconv goal`, and a soundness probe confirms the kernel
//! rejects false variants, so the theorems are non-degenerate.
//!
//! Engineered by a foundation→fan-out ultracode workflow (wf_c761c4e8-236): one
//! agent built+validated the multiplication scaffolding, four seats each proved a
//! semiring law independently, then a fifth merged them into one driver — every
//! seat verifying on the checkpoint is the correctness signal.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_number_theory -- --ignored --nocapture
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
fn naturals_form_a_commutative_semiring() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_number_theory.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_number_theory.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        80_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // every semiring law must be a checked theorem (the driver prints `OK <name>`
    // only when hyps = 0 AND prop aconv the intended goal)
    for law in [
        "add_0_right",
        "add_comm",
        "add_assoc",
        "mult_0_right",
        "mult_1_right",
        "mult_comm",
        "mult_assoc",
        "left_distrib",
        "right_distrib",
    ] {
        assert!(
            out.contains(&format!("OK {law}")),
            "semiring law `{law}` did not produce a checked theorem:\n{out}"
        );
    }
    // the driver only prints this when all nine OK gates fired
    assert!(
        out.contains("SEMIRING_OK"),
        "semiring development did not complete:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
}
