//! MODULAR ARITHMETIC in Isabelle/Pure on the polyml-rs interpreter — congruence
//! mod m is a congruence relation (equivalence + compatible with + and ×), the
//! foundation of ℤ/mℤ.
//!
//! `cong m a b ≝ (∃k. b = a + m·k) ∨ (∃k. a = b + m·k)` (two-sided, since ℕ has no
//! subtraction). Each law a 0-hypothesis theorem on the classical number-theory base;
//! only classical assumption = excluded middle:
//!   cong_refl, cong_sym, cong_trans     (equivalence relation)
//!   cong_add, cong_mult                 (compatible with + and · ⇒ ℤ/mℤ is a comm. ring)
//!
//! Note: `cong_add`'s mixed cases genuinely need `le_total` — the linear order enters
//! even though the statement is purely additive (ℕ can't decide which side the
//! m-multiple lands on without it). A soundness probe confirms the kernel rejects a
//! false variant. The gateway to Fermat's little theorem.
//!
//! Built on `isabelle_classical_primes.sml` by a 2-phase ultracode pipeline
//! (wf_0bbaeabe-bc6: cong foundation refl/sym/add → trans + mult) then merged into one
//! driver.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_modular -- --ignored --nocapture
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
fn congruence_mod_m_is_a_congruence_relation() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_modular.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_modular.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        280_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // equivalence relation
    for law in ["cong_refl", "cong_sym", "cong_trans"] {
        assert!(out.contains(&format!("OK {law}")), "equivalence law `{law}` did not check:\n{out}");
    }
    // compatible with + and *  =>  Z/mZ is a commutative ring
    for law in ["cong_add", "cong_mult"] {
        assert!(out.contains(&format!("OK {law}")), "ring-compat law `{law}` did not check:\n{out}");
    }
    assert!(out.contains("MODULAR_DONE"), "modular-arithmetic development did not complete:\n{out}");
    assert!(!out.contains("Exception-"), "exception during proof:\n{out}");
    assert!(!out.contains("UNSOUND"), "a soundness probe fired UNSOUND:\n{out}");
}
