//! QUADRATIC RECIPROCITY — Gauss's golden theorem — by genuine LCF kernel
//! inference in Isabelle/Pure on the polyml-rs interpreter.
//!
//! For distinct odd primes p, q (m = (p−1)/2, m2 = (q−1)/2), the proved
//! `qr_law` is the conjunction:
//!   (1) cong p (pow q m) (pow (sub p 1) (Σ_{k=1..m}  ⌊q·k/p⌋))   [(q/p) = (−1)^Σ, Eisenstein]
//!   (2) cong q (pow p m2)(pow (sub q 1) (Σ_{j=1..m2} ⌊p·j/q⌋))   [(p/q) = (−1)^Σ, Eisenstein]
//!   (3) parity(Σ⌊q·k/p⌋ + Σ⌊p·j/q⌋) = parity(m·m2)               [reciprocity exponent law]
//! Together (1)+(2)+(3) give (q/p)(p/q) = (−1)^(((p−1)/2)((q−1)/2)).
//!
//! The proof is assembled from five committed self-contained pieces (each a
//! tracked resume delta; concatenated they form one driver that runs on
//! /tmp/isabelle_pure to Tagged(0)):
//!   qr_f1_toolbox.sml   — Gauss's lemma + floor-div API + lar + sum algebra
//!   qr_f2_appendix.sml  — per-k parity crux + half the parity bookkeeping
//!   qr_f2b_appendix.sml — lsumf permutation infra → eisenstein_parity (μ ≡ Σ⌊⌋ mod 2)
//!   qr_f2c_appendix.sml — gauss_sign_count → THE EISENSTEIN LEMMA
//!   qr_f3_appendix.sml  — lattice symmetry (Fubini double-count) → the LAW + master gate
//!
//! 0-hypothesis, aconv to the intended term; the only classical assumption is
//! ex_middle; 0 fabricated axioms (the full proof adds no axiom over the
//! conservative Pure base, audited by name at the end of the driver).
//!
//! `#[ignore]` (needs the warm Pure checkpoint):
//! ```sh
//! tools/build-isabelle-pure.sh     # -> /tmp/isabelle_pure (one-time)
//! cargo test --release -p polyml-bin --test isabelle_quadratic_reciprocity -- --ignored --nocapture
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
fn quadratic_reciprocity_full_law() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/isabelle_support/qr_resume");
    // The five committed pieces, concatenated in order, ARE the self-contained
    // driver (no scratch input) — the four-square reproducibility discipline.
    let pieces = [
        "qr_f1_toolbox.sml",
        "qr_f2_appendix.sml",
        "qr_f2b_appendix.sml",
        "qr_f2c_appendix.sml",
        "qr_f3_appendix.sml",
    ];
    let mut driver = String::new();
    for p in pieces {
        driver.push_str(
            &std::fs::read_to_string(dir.join(p)).unwrap_or_else(|e| panic!("read {p}: {e}")),
        );
        driver.push('\n');
    }

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_sound_audit(&driver, "quadratic_reciprocity", &["qr_law"]),
        990_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
            ("POLYML_HEAP_BYTES", "4000000000"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // The six route stages (each gated on a 0-hyp + aconv kernel check)
    for marker in [
        "FLOOR_AS_COUNT_OK",
        "NO_DIAGONAL_OK",
        "COMPL_COUNT_OK",
        "FUBINI_OK",
        "LATTICE_OK",
        "QR_LAW_OK",
    ] {
        assert!(
            out.contains(marker),
            "stage marker {marker} missing:\n{out}"
        );
    }
    // The headline: the full reciprocity law closed (0-hyp aconv master gate)
    assert!(
        out.contains("QUADRATIC_RECIPROCITY_PROVED"),
        "the reciprocity law did not close (master gate):\n{out}"
    );
    assert!(
        !out.contains("QR_NOT_CLOSED") && !out.contains("F3_PARTIAL"),
        "a master-gate probe reported the law not closed:\n{out}"
    );
    // Soundness: ex_middle is the only classical axiom; nothing fabricated.
    assert!(
        out.contains("f3_ex_middle_present=true"),
        "ex_middle audit line missing:\n{out}"
    );
    assert!(
        out.contains("f3_fabricated_axioms=[]"),
        "a reciprocity/lattice/legendre-shaped axiom was smuggled in:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains(": error:") && !out.contains("Static Errors"),
        "a compile error slipped through:\n{out}"
    );
    // The shared soundness audit (stronger allowlist + oracle-free check).
    assert!(
        out.contains("SOUND_AUDIT_OK quadratic_reciprocity"),
        "soundness audit did not certify quadratic_reciprocity:\n{out}"
    );
}
