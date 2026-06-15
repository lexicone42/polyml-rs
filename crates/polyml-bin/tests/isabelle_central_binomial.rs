//! THE CENTRAL BINOMIAL COEFFICIENT IDENTITY in Isabelle/Pure on the polyml-rs interpreter.
//!
//!   binom_symmetry   : ⊢ ∀n k. k ≤ n ⟹ C(n,k) = C(n, n−k)
//!   central_binomial : ⊢ ∑_{k=0}^n C(n,k)² = C(2n, n)
//!
//! The central binomial identity is a corollary of VANDERMONDE (instantiated at
//! m=n, k=n: ∑_j C(n,j)·C(n,n−j) = C(2n,n)) with the summand rewritten by binomial
//! symmetry under `sum_cong`. Both 0-hyp by genuine kernel inference, each with a
//! soundness probe.
//!
//! Built on the combinatorial-identities development (`isabelle_combinatorics.sml`,
//! which carries Vandermonde) via `common::with_combinatorics`. Proved by a 2-phase
//! ultracode fleet (wf_f6d7e8db-f16); re-verified end-to-end by hand.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_central_binomial -- --ignored --nocapture
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
fn central_binomial_identity() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_central_binomial.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_central_binomial.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_combinatorics(&driver),
        800_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(out.contains("VANDERMONDE_OK"), "combinatorics base did not load:\n{out}");
    for (lemma, marker) in [
        ("binom_symmetry", "BINOM_SYMMETRY_OK"),
        ("central_binomial", "CENTRAL_BINOMIAL_OK"),
    ] {
        assert!(out.contains(&format!("OK {lemma}")), "lemma `{lemma}` did not check:\n{out}");
        assert!(out.contains(marker), "marker `{marker}` missing:\n{out}");
    }
    assert!(!out.contains("Exception-"), "exception during proof:\n{out}");
    assert!(!out.contains("PROBE_UNSOUND"), "a soundness probe fired UNSOUND:\n{out}");
    assert!(!out.contains("UNSOUND"), "an UNSOUND marker fired:\n{out}");
}
