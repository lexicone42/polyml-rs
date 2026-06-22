//! THE EUCLID–EULER THEOREM (even perfect numbers) — Euler's converse direction,
//! REDUCED to one open lemma. (task #118, ultracode wf_1fc90eed-991)
//!
//! Euclid's direction (2^p−1 prime ⟹ 2^(p−1)(2^p−1) perfect) is the BANKED
//! `euclid_perfect` (isabelle_euclid_perfect.rs). This file is Euler's CONVERSE
//! (every even perfect number has that form) + the full iff assembly. It is
//! **CONDITIONAL** on one residual lemma, honestly labelled:
//!
//! PROVED UNCONDITIONALLY (each 0-hyp, aconv-intended, soundness-probed):
//!   sigma_bound  : ⊢ 1<m ⟹ d∣m ⟹ d<m ⟹ σ(m)=m+d ⟹ (d=1 ∧ prime2 m)
//!   factor_2s    : ⊢ 0<n ⟹ even n ⟹ ∃a m. n=2^a·m ∧ odd m ∧ 0<a
//!   consec_coprime (of 2^b and 2^b−1) + the EC assembly helpers.
//!
//! PROVED CONDITIONAL on SCG (general-m σ-multiplicativity, the residual wall):
//!   SCG := ⋀a m. odd m ⟹ σ(2^a·m) = σ(2^a)·σ(m)
//!   euclid_euler_cond : ⊢ SCG ⟹ 0<n ⟹ even n
//!                          ⟹ (perfect n ⟺ ∃p. prime2(2^p−1) ∧ n=2^(p−1)(2^p−1))
//! i.e. the FULL Euclid–Euler theorem holds MODULO σ-multiplicativity for an
//! arbitrary odd m (the banked machinery only has the PRIME-q divisor list;
//! general odd m needs a divisor-completeness argument for variable-element
//! divisor lists — a div2aq_complete-scale wall). The conditional iff is 0-hyp
//! (HYPS=0, SHYPS=0) modulo SCG, aconv the intended biconditional, and the
//! kernel confirms it genuinely NEEDS SCG (PROBE_OK ... needs the sigma-mult
//! bridge SCG). The backward half is the banked euclid_perfect. Resume:
//! docs/euclid-euler-converse-progress-2026-06-22.md.
//!
//! Self-contained: base (isabelle_euclid_perfect.sml) + the converse delta
//! (isabelle_euler_converse.sml), run directly. `#[ignore]` (needs
//! /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! cargo test --release -p polyml-bin --test isabelle_euclid_euler -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use std::path::PathBuf;

fn checkpoint() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/isabelle_pure");
    p.exists().then_some(p)
}

fn support(name: &str) -> String {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support")
        .join(name);
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("read {name}: {e}"))
}

/// Euler's converse + the full Euclid–Euler iff, conditional on SCG; plus the
/// two unconditionally-proved supporting lemmas.
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn euclid_euler_conditional() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    // base (euclid_perfect driver) + the converse delta, run directly.
    let driver = format!(
        "{}\n{}",
        support("isabelle_euclid_perfect.sml"),
        support("isabelle_euler_converse.sml")
    );
    let env = &[
        ("ML_SYSTEM", "polyml"),
        ("ML_PLATFORM", "x86_64-linux"),
        ("ISABELLE_HOME", "/tmp/isa"),
    ];
    let Some((out, _)) = run_image_env(&image, &driver, 300_000_000_000, env) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    for marker in [
        // base intact
        "EUCLID_PERFECT_ALL_OK",
        // unconditional supporting lemmas
        "SIGMA_BOUND_ALL_OK",
        "FACTOR_2S_OK",
        "CONSEC_COPRIME_OK",
        "EC_M_LE_SIGMA_OK",
        "EC_PARITY_BRIDGE_OK",
        // the conditional converse + iff (0-hyp modulo SCG, aconv)
        "EULER_CONVERSE_COND_ACONV_OK",
        "EUCLID_EULER_COND_HYPS = 0",
        "EUCLID_EULER_COND_SHYPS = 0",
        "EUCLID_EULER_COND_ACONV_OK",
        // it genuinely needs the sigma-mult bridge (not vacuous)
        "PROBE_OK euler_converse needs the sigma-mult bridge SCG",
        "EUCLID_EULER_ALL_OK",
    ] {
        assert!(out.contains(marker), "marker `{marker}` missing:\n{out}");
    }
    assert!(
        !out.contains("PROBE_FAIL"),
        "a soundness probe FAILED:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
}
