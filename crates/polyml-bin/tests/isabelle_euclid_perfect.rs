//! EUCLID'S PERFECT-NUMBER THEOREM (Elements IX.36), in Isabelle/Pure on the
//! polyml-rs interpreter. (task #117 finale)
//!
//! PROVED (a 0-hypothesis theorem by genuine LCF kernel inference, aconv the
//! intended statement):
//!
//!   euclid_perfect :
//!     ⊢ prime2 q ⟹ q + 1 = 2^p ⟹ 1 < p
//!         ⟹ sigma (2^(p-1) · q) = 2 · (2^(p-1) · q)
//!
//! i.e. for a (structural) prime q with q + 1 = 2^p and 1 < p, the number
//! n = 2^(p-1)·q is PERFECT: sigma(n) = 2n (the divisors sum to twice n).
//! `perfect n := sigma n = 2·n`; the conclusion is exactly `perfect (2^(p-1)·q)`.
//!
//! Proved en route, the crux (the documented multi-fleet wall — the sum-support
//! reindex collapsing the EXPONENTIAL-range sparse sum to the dense geometric
//! sum over the 2(a+1) actual divisors):
//!
//!   sigma_char : ⊢ prime2 q ⟹ ¬(2 ∣ q)
//!                  ⟹ sigma (2^a · q) = (∑_{i=0}^a 2^i) · (q + 1)
//!
//! via the reusable SUPPORT BIJECTION sum_supp_collapse (a duplicate-free list of
//! support points all in [0..N] ⟹ full-range sum = sparse list-sum), the
//! divisor characterization div2aq_complete (every divisor of 2^a·q is 2^i or
//! 2^i·q, by euclid_lemma on prime q), pow2_dvd_char + prime2_two (the 2-adic
//! lemmas), and the geometric value geo_add.
//!
//! AXIOM AUDIT (Theory.all_axioms_of, 70 axioms): the only sigma/list additions
//! are the CONSERVATIVE defining axioms — swt_dvd (d∣n ⟹ swt n d = d), swt_ndvd
//! (¬(d∣n) ⟹ swt n d = 0), sigma_def (sigma n = ∑_{d=0}^n swt n d), and the two
//! divlist recursion equations (divlist 0 q = [1,q]; divlist (Suc a) q =
//! [2^(Suc a), 2^(Suc a)·q] ++ divlist a q) — plus the established natlist
//! list-lib. ZERO axioms mention `perfect`/the conclusion. The only classical
//! input is the foundation's single `ex_middle`.
//!
//! FAITHFULNESS: the same swt/sigma_def axioms compute (genuine kernel inference)
//! sigma 6 = 12 (6 PERFECT), sigma 28 = 56 (28 PERFECT), sigma 8 = 15 ≠ 16 (not
//! perfect) — see isabelle_sigma.rs. And the proved euclid_perfect, instantiated
//! at p=2,q=3 and p=3,q=7 by genuine inference, specializes (0-hyp, aconv) to
//! exactly the perfect statements for n=6 and n=28.
//!
//! The driver is SELF-CONTAINED (embeds nt_helpers + binom_thm + the sigma floor
//! + the support bijection + pow2_dvd_char + the divisor characterization + the
//! final assembly), run DIRECTLY (no `common::with_*` splice), like
//! isabelle_euler / isabelle_twosquare. Consolidation onto a `common::with_sigma`
//! splice is a tracked follow-up.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_euclid_perfect -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use std::path::PathBuf;

fn checkpoint() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/isabelle_pure");
    p.exists().then_some(p)
}

const ENV: &[(&str, &str)] = &[
    ("ML_SYSTEM", "polyml"),
    ("ML_PLATFORM", "x86_64-linux"),
    ("ISABELLE_HOME", "/tmp/isa"),
];

/// Euclid's perfect-number theorem (IX.36): sigma(2^(p-1)·q) = 2·(2^(p-1)·q)
/// for a prime q with q+1 = 2^p and 1<p. Self-contained driver, run directly.
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh); ~3.0B steps"]
fn euclid_perfect() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/isabelle_support/isabelle_euclid_perfect.sml"),
    )
    .expect("read isabelle_euclid_perfect.sml");
    let Some((out, _)) = run_image_env(&image, &driver, 300_000_000_000, ENV) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    for marker in [
        "SIGMA_CHAR_OK",
        "OK sigma_char",
        "EUCLID_PERFECT_HYPS = 0",
        "OK euclid_perfect",
        "EUCLID_PERFECT_OK",
        "PROBE_OK euclid_perfect needs prime2 q",
        "PROBE_OK euclid_perfect needs q+1=2^p",
        "PROBE_OK euclid_perfect needs 1<p",
        "PROBE_OK euclid_perfect conclusion is 2*n (perfect)",
        "EUCLID_PERFECT_EXTRA_SHYPS = 0",
        "EUCLID_PERFECT_ALL_OK",
    ] {
        assert!(out.contains(marker), "marker `{marker}` missing:\n{out}");
    }
    assert!(
        !out.contains("PROBE_FAIL"),
        "a soundness probe FAILED:\n{out}"
    );
    assert!(
        !out.contains("FAIL euclid_perfect"),
        "euclid_perfect chk FAILED:\n{out}"
    );
    assert!(
        !out.contains("SIGMA_CHAR_FAIL"),
        "sigma_char FAILED:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("EUCLID_PERFECT_INCOMPLETE"),
        "euclid_perfect incomplete:\n{out}"
    );
}
