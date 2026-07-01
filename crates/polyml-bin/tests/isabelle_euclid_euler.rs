//! THE EUCLID–EULER THEOREM (even perfect numbers) — COMPLETE, UNCONDITIONAL.
//! (task #118, ultracode wf_1fc90eed-991 → wf_3f6516e5-ac4)
//!
//!   euclid_euler : ⊢ 0<n ⟹ even n
//!                     ⟹ (perfect n ⟺ ∃p. prime2(2^p−1) ∧ n = 2^(p−1)·(2^p−1))
//!
//! i.e. AN EVEN NUMBER IS PERFECT IFF IT IS 2^(p−1)·(2^p−1) WITH 2^p−1 PRIME —
//! the full Euclid–Euler characterization of even perfect numbers, a 0-hyp
//! theorem by genuine LCF kernel inference on the self-bootstrapped Rust PolyML
//! interpreter. Euclid's direction (Elements IX.36) is `euclid_perfect`; Euler's
//! converse is the hard direction.
//!
//! The residual lemma SCG (σ-multiplicativity for any odd m) is now PROVED 0-hyp:
//!   SCG : ⊢ ⋀a m. ¬(2∣m) ⟹ σ(2^a·m) = (∑_{i≤a} 2^i)·σ(m)
//! via a general divisor_list(m) (filter [1..m] by ∣, completeness + lnodup) and
//! the 2-adic-split completeness of the product divisor list dl2 a D (every
//! divisor of 2^a·m is 2^i·d with i≤a, d∣m — pow2_dvd_char + euclid_lemma at 2),
//! fed into the support bijection. SCG discharges the banked euclid_euler_cond →
//! the UNCONDITIONAL theorem (the SCG meta-hypothesis is gone).
//!
//! Verified: 0-hyp, aconv the intended biconditional, the SCG hypothesis is GONE
//! (EUCLID_EULER_UNCONDITIONAL_OK); runtime axiom audit = 80, the only σ-mentioning
//! axiom is the conservative `sigma_def`, ZERO mention perfect/euclid; only
//! classical assumption = ex_middle. The iff was instantiated BOTH ways at n=6 and
//! n=28 (the even perfect numbers <30) by genuine inference during the campaign.
//!
//! Self-contained: 5 drivers concatenated, run directly (base euclid_perfect +
//! the converse + the σ-mult partial + the dl2 completeness + the close delta;
//! consolidation onto a `common::with_sigma` splice is a tracked follow-up).
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
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

/// The full UNCONDITIONAL Euclid–Euler theorem (SCG proved + discharged).
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn euclid_euler_unconditional() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    // 5-file driver, concatenated + run directly.
    let driver = [
        "isabelle_euclid_perfect.sml", // base (σ + divisor-list + support bijection)
        "isabelle_euler_converse.sml", // sigma_bound + factor_2s + euclid_euler_cond
        "isabelle_euler_converse_sigma_mult.sml", // sigma_mult_reduction + lsumf distribution
        "isabelle_euler_converse_dl2.sml", // dl2 completeness + lnodup (2-adic split)
        "isabelle_euler_converse_close.sml", // general divisor_list(m) + SCG + the discharge
    ]
    .iter()
    .map(|f| support(f))
    .collect::<Vec<_>>()
    .join("\n");
    let env = &[
        ("ML_SYSTEM", "polyml"),
        ("ML_PLATFORM", "x86_64-linux"),
        ("ISABELLE_HOME", "/tmp/isa"),
    ];
    let Some((out, _)) = run_image_env(
        &image,
        &common::with_sound_audit(&driver, "euclid_euler", &["euclid_euler"]),
        300_000_000_000,
        env,
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    for marker in [
        // base + supporting lemmas intact
        "EUCLID_PERFECT_ALL_OK",
        "SIGMA_BOUND_ALL_OK",
        "FACTOR_2S_OK",
        // the conditional iff (still proved en route)
        "EUCLID_EULER_COND_ACONV_OK",
        // SCG now a real 0-hyp theorem (the residual lemma, proved)
        "SCG_ACONV_OK",
        "SCG_PROVED_0HYP_OK",
        // the UNCONDITIONAL theorem: SCG discharged, meta-hyp gone, aconv the iff
        "EUCLID_EULER_ACONV_OK",
        "EUCLID_EULER_UNCONDITIONAL_OK",
    ] {
        assert!(out.contains(marker), "marker `{marker}` missing:\n{out}");
    }
    assert!(
        !out.contains("PROBE_FAIL"),
        "a soundness probe FAILED:\n{out}"
    );
    assert!(
        !out.contains("UNSOUND"),
        "an unsoundness marker fired:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        out.contains("SOUND_AUDIT_OK euclid_euler"),
        "soundness audit did not certify euclid_euler:\n{out}"
    );
}
