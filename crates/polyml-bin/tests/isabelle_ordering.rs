//! (ℕ, ≤) IS A LINEAR ORDER COMPATIBLE WITH +, proved in Isabelle/Pure on the
//! polyml-rs interpreter — the order-theory rung of the Isabelle number-theory
//! ladder (object logic → Peano → semiring → summation → ORDER), and the mirror
//! of HOL4 `hol4_order.rs`.
//!
//! This development first EXTENDS the object logic with two genuine logical
//! primitives — the EXISTENTIAL QUANTIFIER (`Ex`/`exI`/`exE`) and PEANO
//! DISCRIMINATION (`oFalse`/`oFalse_elim`/`Suc_neq_Zero`/`Suc_inj`, legitimate
//! Peano axioms) — plus a DISJUNCTION connective (`Disj`/`disjI`/`disjE`), then
//! defines `m ≤ n ≝ ∃p. n = m + p` and proves the full order structure, each a
//! 0-hypothesis theorem by pure LCF kernel inference:
//!   le_refl    `⊢ n ≤ n`              zero_le   `⊢ 0 ≤ n`        le_add `⊢ m ≤ m+p`
//!   le_trans   `⊢ m≤n ⟹ n≤k ⟹ m≤k`   (transitivity)
//!   le_antisym `⊢ m≤n ⟹ n≤m ⟹ m=n`   (antisymmetry  ⇒ PARTIAL order)
//!   le_suc_mono `⊢ m≤n ⟹ Suc m ≤ Suc n`,  le_add_mono `⊢ a≤b ⟹ a+c ≤ b+c`  (+ compat)
//!   le_total   `⊢ m≤n ∨ n≤m`          (linearity  ⇒ LINEAR order)
//! Antisymmetry rests on `add_left_cancel` + `add_eq_zero_left` (proved by
//! induction via a meta-implication→object-predicate reflection, since
//! `nat_induct`'s predicate is object-level). Soundness probes confirm the kernel
//! rejects false variants (reversed le_trans, one-premise le_antisym).
//!
//! Engineered by a foundation→fan-out→merge ultracode workflow (wf_74f3a1e0-a99):
//! one agent built the existential/discrimination/le scaffolding, four seats each
//! proved an order law independently (including the `le_total` stretch, which added
//! disjunction), a fifth merged them — independent agreement is the correctness
//! signal.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_ordering -- --ignored --nocapture
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
fn naturals_with_le_form_a_linear_order() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_ordering.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_ordering.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        130_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // each order law is a checked theorem (driver prints `OK <name>` only when
    // hyps = 0 AND prop aconv the intended goal)
    for law in [
        "le_refl",
        "zero_le",
        "le_add",
        "le_trans",
        "le_antisym",
        "le_suc_mono",
        "le_add_mono",
        "le_total",
    ] {
        assert!(
            out.contains(&format!("OK {law}")),
            "order law `{law}` did not produce a checked theorem:\n{out}"
        );
    }
    // the driver prints this only when all eight OK gates + the soundness probes fired
    assert!(
        out.contains("ORDER_DONE"),
        "order development did not complete:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
}
