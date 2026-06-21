//! THE SUM-OF-DIVISORS FUNCTION sigma — the foundation rung toward Euclid's
//! perfect-number theorem (Elements IX.36), in Isabelle/Pure on the polyml-rs
//! interpreter. (task #117, ultracode wf_a1ac4dbf-1b1)
//!
//! PROVED (each a 0-hypothesis theorem by genuine LCF kernel inference,
//! aconv the intended statement):
//!   sigma_prime : ⊢ prime2 q ⟹ sigma q = q + 1   (sum of divisors of a prime)
//!   geo_sum     : ⊢ ∑_{i=0}^k 2^i = 2^(k+1) − 1   (the geometric value half)
//!   geo_add     : ⊢ 1 + ∑_{i=0}^k 2^i = 2^(k+1)
//!
//! Phase 0 introduces the sigma subsystem with EXACTLY three conservative
//! defining axioms (none mentions `perfect`/the conclusion):
//!   swt_dvd  : dvd d n ⟹ swt n d = d
//!   swt_ndvd : ¬(dvd d n) ⟹ swt n d = 0
//!   sigma_def: sigma n = ∑_{d=0}^n swt n d
//!
//! FAITHFULNESS of the sigma definition is demonstrated by GENUINE COMPUTATION
//! (`sigma_computational_probe`): the kernel unfolds sigma_def → sumf → swt and
//! decides divisibility at every index, proving 0-hyp numeral theorems
//!   sigma 6 = 12  (6 PERFECT),  sigma 28 = 56  (28 PERFECT),
//!   sigma 8 = 15  (8 NOT perfect; 2*8 = 16 ≠ 15, neg(oeq 15 16) kernel-proved).
//! A wrong sigma definition would compute wrong values.
//!
//! NOT proved: the target `euclid_perfect` (2^p-1 prime ⟹ 2^(p-1)(2^p-1)
//! perfect). It is blocked on the divisor-set reindex `sigma_char` — collapsing
//! the SPARSE sum `sumf (swt N) N` over the EXPONENTIAL range 0..N to the dense
//! geometric sum over the 2(a+1) actual divisors. That needs a divisor-LIST
//! representation + a support bijection (Route A); a confirmed multi-fleet
//! follow-up (docs/euclid-perfect-progress-2026-06-21.md). Do NOT advertise the
//! perfect-number theorem as proved.
//!
//! Built on the binomial-theorem development (`isabelle_binom_thm.sml`, which
//! carries sumf + the sum-algebra + pow + sub + prime2 + dvd + Euclid's lemma)
//! spliced in by `common::with_binom_thm`.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_sigma -- --ignored --nocapture
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

const ENV: &[(&str, &str)] = &[
    ("ML_SYSTEM", "polyml"),
    ("ML_PLATFORM", "x86_64-linux"),
    ("ISABELLE_HOME", "/tmp/isa"),
];

/// The sigma subsystem + the two floor lemmas (sigma_prime, geo_sum/geo_add).
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn sigma_floor() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver = support("isabelle_sigma.sml");
    let Some((out, _)) = run_image_env(
        &image,
        &common::with_binom_thm(&driver),
        300_000_000_000,
        ENV,
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    for marker in [
        "SIGMA_CONSTS_OK",
        "OK sigma_prime",
        "SIGMA_PRIME_ALL_OK",
        "OK geo_sum",
        "GEO_OK",
        "EUCLID_PERFECT_FLOOR_BANKED",
    ] {
        assert!(out.contains(marker), "marker `{marker}` missing:\n{out}");
    }
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("PROBE_FAIL"),
        "a soundness probe FAILED:\n{out}"
    );
}

/// Faithfulness of the sigma DEFINITION by genuine kernel computation:
/// sigma 6 = 12, sigma 28 = 56 (perfect), sigma 8 = 15 ≠ 16 (not perfect).
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn sigma_computational_probe() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    // The probe builds on the floor's sigma subsystem; concat floor + probe.
    let driver = format!(
        "{}\n{}",
        support("isabelle_sigma.sml"),
        support("isabelle_sigma_probe.sml")
    );
    let Some((out, _)) = run_image_env(
        &image,
        &common::with_binom_thm(&driver),
        300_000_000_000,
        ENV,
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    for marker in [
        "PROBE_OK sigma 6 = 12",
        "PROBE_OK sigma 28 = 56",
        "PROBE_OK sigma 8 = 15",
        "VERDICT 6 PERFECT",
        "VERDICT 28 PERFECT",
        "VERDICT 8 NOT-PERFECT",
        "VF_PROBES_DONE",
    ] {
        assert!(
            out.contains(marker),
            "probe marker `{marker}` missing:\n{out}"
        );
    }
    assert!(
        !out.contains("PROBE_FAIL"),
        "a computational probe FAILED:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during probe:\n{out}"
    );
}
