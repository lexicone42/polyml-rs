//! POWERS + MODULAR POWERS in Isabelle/Pure on the polyml-rs interpreter — Stage A
//! of the Fermat-little-theorem arc.
//!
//! `pow a 0 = 1`, `pow a (Suc n) = a · pow a n`. Each a 0-hypothesis theorem on the
//! modular-arithmetic base; only classical assumption = excluded middle:
//!   pow_one       `a^1 = a`
//!   pow_add       `a^(m+n) = a^m · a^n`
//!   pow_mult_base `(a·b)^n = a^n · b^n`
//!   cong_pow      `a ≡ b (mod m) ⟹ a^n ≡ b^n (mod m)`   (the modular star)
//!
//! `cong_pow` is induction on n using `cong_mult` + `cong_refl` + a `cong_cong` helper
//! (rewrite both sides of a congruence by an `oeq` via capture-avoiding `oeq_subst`).
//! The foundation for Fermat's little theorem (`a^p ≡ a mod p`).
//!
//! Built on `isabelle_modular.sml` by a 3-seat ultracode fleet (wf_f0e818c6-9ed).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_power -- --ignored --nocapture
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
fn powers_and_modular_powers() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/isabelle_support/isabelle_power.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_power.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        250_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    for law in ["pow_one", "pow_add", "pow_mult_base", "cong_pow"] {
        assert!(
            out.contains(&format!("OK {law}")),
            "power law `{law}` did not check:\n{out}"
        );
    }
    assert!(
        out.contains("POW_DONE"),
        "powers development did not complete:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
}
