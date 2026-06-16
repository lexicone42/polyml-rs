//! CLASSIC COMBINATORIAL IDENTITIES in Isabelle/Pure on the polyml-rs interpreter.
//!
//!   pascal_row_sum : ⊢ ∑_{k=0}^n C(n,k) = 2^n          (Pascal's triangle row sum)
//!   hockey_stick   : ⊢ ∑_{i=0}^n C(i,r) = C(n+1, r+1)  (the hockey-stick identity)
//!   vandermonde    : ⊢ ∑_{j=0}^k C(m,j)·C(n,k−j) = C(m+n, k)   (Vandermonde)
//!
//! Three famous binomial-coefficient identities, each a 0-hypothesis theorem by
//! genuine LCF kernel inference. The row sum is a corollary of the binomial
//! theorem at a=b=1; the hockey stick is induction on n + Pascal; Vandermonde
//! (the capstone) is the classic Pascal-split + reindex + recombine induction.
//! Each carries a soundness probe.
//!
//! Built on the binomial-theorem development (`isabelle_binom_thm.sml`) over the
//! classical foundation, spliced in by `common::with_binom_thm`. Proved by a
//! multi-seat ultracode fleet racing all three concurrently (wf_bd77c82b-594);
//! re-verified end-to-end by hand before landing.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_combinatorics -- --ignored --nocapture
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
fn combinatorial_identities() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_combinatorics.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_combinatorics.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_binom_thm(&driver),
        800_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // the binomial-theorem base must load first
    assert!(
        out.contains("BINOM_THM_DONE"),
        "binomial-theorem base did not load:\n{out}"
    );
    // each identity, by named lemma + phase marker
    for (lemma, marker) in [
        ("pascal_row_sum", "PASCAL_ROW_SUM_OK"),
        ("hockey_stick", "HOCKEY_STICK_OK"),
        ("vandermonde", "VANDERMONDE_OK"),
    ] {
        assert!(
            out.contains(&format!("OK {lemma}")),
            "identity `{lemma}` did not check:\n{out}"
        );
        assert!(out.contains(marker), "marker `{marker}` missing:\n{out}");
    }
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("PROBE_UNSOUND"),
        "a soundness probe fired UNSOUND:\n{out}"
    );
    assert!(!out.contains("UNSOUND"), "an UNSOUND marker fired:\n{out}");
}
