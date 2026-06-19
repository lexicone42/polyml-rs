//! WILSON'S IFF — the full primality criterion, in Isabelle/Pure on the
//! polyml-rs interpreter.
//!
//!   wilson_iff : ⊢ 1 < n ⟹ (prime2 n ⟺ cong n ((n−1)!) (n−1))
//!
//! For n > 1, n is (structurally) prime IFF (n−1)! ≡ −1 (mod n) — the way
//! Wilson's theorem is usually *stated* (as a primality test, both directions).
//! `prime2` is the genuine structural prime; (n−1)! = lprod(upto(n−1));
//! −1 ≡ n−1 (mod n); ⟺ is the object Conj of the two implications.
//!
//! Assembles the two banked halves on the modular-inverse base (no new axioms;
//! `wilson` and `wc_converse` are PROVEN theorems, not re-axiomatized; only
//! classical assumption = excluded middle):
//!   - FORWARD: instantiate the proven Wilson theorem (`isabelle_wilson`) at n.
//!   - BACKWARD (contrapositive): 1<n ∧ ¬prime2 n ⟹ composite; the 4<n case
//!     applies Wilson's converse (`isabelle_wilson_converse`: ≡0≢−1 since
//!     0<n−1<n); the n=4 case is computed from scratch (3!=6≡2≢3).
//! 0-hyp (modulo the single 1<n side-condition), aconv-intended, soundness-probed
//! (the iff genuinely keeps 1<n, is a real biconditional, and the residue is
//! n−1=−1 not 0). Re-verified end-to-end: Tagged(0), ~2.99B steps.
//!
//! Spliced via `common::with_wilson` (carries the proven Wilson theorem); the
//! support .sml prepends the Wilson-converse delta then the iff-assembly delta.
//! ultracode wf_1c71659d-8ce.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_wilson_iff -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use common::with_wilson;
use std::path::PathBuf;

fn checkpoint() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/isabelle_pure");
    p.exists().then_some(p)
}

#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn wilson_iff_primality_criterion() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_wilson_iff.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_wilson_iff.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &with_wilson(&driver),
        990_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // the Wilson converse re-proved (prereq for the backward direction)
    assert!(
        out.contains("WC_CONVERSE_OK"),
        "Wilson converse did not re-prove:\n{out}"
    );
    // the iff: prime2 n ⟺ (n−1)! ≡ −1 (mod n), 0-hyp, aconv-intended
    assert!(
        out.contains("WILSON_IFF_OK"),
        "wilson_iff did not check:\n{out}"
    );
    assert!(
        out.contains("WIFF_DELTA_DONE"),
        "iff assembly did not complete:\n{out}"
    );
    // soundness probes: keeps 1<n, is a real biconditional, residue is n−1 not 0
    assert!(
        out.contains("PROBE_OK iff keeps the 1<n hypothesis")
            && out.contains("PROBE_OK conclusion is a biconditional")
            && out.contains("PROBE_OK residue is"),
        "a wilson_iff soundness probe is missing:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains(": error:") && !out.contains("Static Errors"),
        "a compile error slipped through:\n{out}"
    );
    assert!(
        !out.contains("PROBE_FAIL") && !out.contains("WILSON_IFF_FAILED"),
        "a probe or the iff fired FAILED:\n{out}"
    );
}
