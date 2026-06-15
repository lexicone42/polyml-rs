//! CLOSED-FORM SUMMATION THEOREMS in Isabelle/Pure on the polyml-rs interpreter.
//!
//!   nicomachus   : ⊢ ∑_{k=0}^n k³ = (∑_{k=0}^n k)²        (Nicomachus's theorem)
//!   faulhaber_sq : ⊢ 6·∑_{k=0}^n k² = n·(n+1)·(2n+1)      (Faulhaber, sum of squares)
//!   pronic_sum   : ⊢ 3·∑_{k=0}^n k·(k+1) = n·(n+1)·(n+2)
//!
//! Three named closed-form sums, each a 0-hypothesis theorem by genuine LCF
//! kernel inference over the higher-order finite sum `sumf` (pure identities, no
//! new constant; sums cleared of denominators to stay in ℕ). Nicomachus goes via
//! the Gauss-doubling helper (2·∑k = n(n+1)); the others by nat induction +
//! semiring algebra. Each carries a soundness probe.
//!
//! Built on the finite-sum development (`isabelle_binom_thm.sml`) over the
//! classical foundation, spliced in by `common::with_binom_thm`. Proved by a
//! multi-seat ultracode fleet racing all three concurrently (wf_62507100-db8);
//! re-verified end-to-end by hand before landing.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_summation_forms -- --ignored --nocapture
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
fn closed_form_summations() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_summation_forms.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_summation_forms.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_binom_thm(&driver),
        800_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(out.contains("BINOM_THM_DONE"), "finite-sum base did not load:\n{out}");
    for (lemma, marker) in [
        ("nicomachus", "NICOMACHUS_OK"),
        ("faulhaber_sq", "FAULHABER_SQ_OK"),
        ("pronic_sum", "PRONIC_OK"),
    ] {
        assert!(out.contains(&format!("OK {lemma}")), "identity `{lemma}` did not check:\n{out}");
        assert!(out.contains(marker), "marker `{marker}` missing:\n{out}");
    }
    assert!(!out.contains("Exception-"), "exception during proof:\n{out}");
    assert!(!out.contains("PROBE_UNSOUND"), "a soundness probe fired UNSOUND:\n{out}");
    assert!(!out.contains("UNSOUND"), "an UNSOUND marker fired:\n{out}");
}
