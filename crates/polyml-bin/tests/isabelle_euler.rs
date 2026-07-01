//! EULER'S THEOREM in Isabelle/Pure on the polyml-rs interpreter.
//!
//!   euler : ⊢ 1 < n ⟹ unit_test n a ⟹ cong n (pow a (phiU n)) 1
//!           i.e.  a^φ(n) ≡ 1 (mod n)  for a a unit mod n
//!
//! A 0-hypothesis theorem by genuine LCF kernel inference — the generalisation of
//! Fermat's little theorem to a composite modulus, proved on a Rust reimplementation
//! of PolyML. Coprimality is defined AS invertibility (`unit_test n r` = the search
//! for an inverse succeeds), so "is a unit" and "has an inverse" coincide by
//! construction. Four soundness probes pass: the statement is aconv the intended
//! one, it needs the `unit_test` hypothesis, the exponent is φ(n) (not n), and the
//! residue is 1 (not 0).
//!
//! Proof (Lagrange in the unit group): multiply-by-a permutes the reduced residues
//! (the multiply-by-a bijection, Phase 1, `bij_prod` via the permutation-invariance
//! lemma `lprod_perm`), so ∏(a·units) = ∏(units); factoring out a^φ(n) and cancelling
//! the (unit) product with `gen_cancel` gives a^φ(n) ≡ 1. Built by a multi-phase
//! ultracode fleet (wf_72da364c-704: unit group + bijection → final assembly);
//! re-verified end-to-end by hand (3,269,745,139 steps, Result: Tagged(0), 145
//! sub-lemmas, zero exceptions; axiom audit clean — only the established
//! conservative foundation + the single classical `ex_middle`).
//!
//! NOTE: this driver is INTENTIONALLY SELF-CONTAINED — it embeds its own
//! foundation rather than splicing via a `common::with_*` helper. Consolidating
//! it onto the splice chain was considered (task #87) and DECLINED: the proof is
//! a working, fenced, byte-for-byte reproducible 3.27-billion-step artifact, and
//! re-deriving it through the shared context only to dedup ~14k lines of embedded
//! foundation is marginal-value, high-risk surgery (the cterm/context threading
//! is the documented silent-no-op footgun). A standalone driver is also the more
//! *shareable* form — it reads end-to-end without the splice helpers. Kept as-is
//! by design; #87 closed resolved-not-consolidated.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_euler -- --ignored --nocapture
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
fn eulers_theorem() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/isabelle_support/isabelle_euler.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_euler.sml");

    // The driver is self-contained (embeds its own foundation), so it is run
    // directly — no `with_*` splice.
    let Some((out, _)) = run_image_env(
        &image,
        &common::with_sound_audit(&driver, "euler", &["euler"]),
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

    // Phase 1 (unit group + multiply-by-a bijection) must build first.
    assert!(
        out.contains("EULER_BIJ_OK"),
        "Euler Phase-1 (unit group + bijection) did not complete:\n{out}"
    );
    // EULER'S THEOREM: the 0-hyp theorem checked, aconv the intended statement.
    assert!(
        out.contains("OK euler"),
        "euler did not check 0-hyp:\n{out}"
    );
    assert!(out.contains("EULER_OK"), "EULER_OK marker missing:\n{out}");
    // All four soundness probes passed (aconv / needs unit_test / exponent φ(n) / residue 1).
    assert!(
        out.contains("EULER_PROBES_OK"),
        "soundness probes did not all pass:\n{out}"
    );
    assert!(
        out.contains("EULER_THEOREM_COMPLETE"),
        "EULER_THEOREM_COMPLETE marker missing:\n{out}"
    );
    // Not a degenerate / failed / exceptional run.
    assert!(
        !out.contains("EULER_PROBES_FAILED"),
        "a soundness probe FAILED:\n{out}"
    );
    assert!(!out.contains("PROBE_FAIL"), "a PROBE_FAIL fired:\n{out}");
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(!out.contains("UNSOUND"), "an UNSOUND marker fired:\n{out}");
    assert!(
        out.contains("SOUND_AUDIT_OK euler"),
        "soundness audit did not certify euler:\n{out}"
    );
}
