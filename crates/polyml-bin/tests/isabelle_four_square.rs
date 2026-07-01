//! LAGRANGE'S FOUR-SQUARE THEOREM — ∀n. ∃a b c d. n = a²+b²+c²+d², by genuine
//! LCF kernel inference in Isabelle/Pure on the polyml-rs interpreter.
//!
//! Two tests, two checkpoints:
//!
//!   `four_square_identity_and_reduction` (on /tmp/isabelle_pure) — the two
//!   lightweight base results, fast to re-check:
//!     PART A   four_sq_mult       : ⊢ four_sq m ⟹ four_sq n ⟹ four_sq (m·n)
//!              (Euler's four-square identity / multiplicativity; `four_sq k :=
//!               ∃a b c d. k = a²+b²+c²+d²`, an object existential, not an axiom;
//!               proved via a ring-over-ℕ decision procedure with absdiff for the
//!               signed cross terms).
//!     ASSEMBLY lagrange_assembly  : ⊢ (⋀p. prime2 p ⟹ four_sq p) ⟹ (⋀n. four_sq n)
//!              (multiplicative-closure reduction; prime2 = structural prime).
//!
//!   `four_square_full_theorem` (on /tmp/l4_foursq_star) — the WHOLE theorem:
//!              ⊢ ∀n. ∃a b c d. n = a²+b²+c²+d²
//!     0-hypothesis; no new axioms over the conservative base; only classical
//!     assumption = excluded middle. Closed by the Euler descent: 9 signed
//!     divide-by-m² leaves → a 16→9 disjE descent step → strict 0<r<m → strong
//!     induction down to m=1 → discharge lagrange_assembly. Reproduction +
//!     per-file roles: tests/isabelle_support/four_square_resume/README.md; the
//!     campaign history: docs/four-square-progress-2026-06-17.md.
//!
//! Both proofs add 0 new axioms and are re-verified by hand. The full proof sets
//! `Proofterm.proofs := 0` to bound RAM — the kernel still validates every
//! inference, so the theorem is genuine (standard Isabelle practice).
//!
//! `#[ignore]` (need warm checkpoints):
//! ```sh
//! tools/build-isabelle-pure.sh     # -> /tmp/isabelle_pure  (both tests)
//! tools/build-l4-checkpoint.sh     # -> /tmp/l4_foursq_star (full theorem)
//! cargo test --release -p polyml-bin --test isabelle_four_square -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use std::path::PathBuf;

fn checkpoint() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/isabelle_pure");
    p.exists().then_some(p)
}

fn l4_checkpoint() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/l4_foursq_star");
    p.exists().then_some(p)
}

#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn four_square_identity_and_reduction() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_four_square.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_four_square.sml");

    // Self-contained driver (embeds the two-square base) — run directly.
    let Some((out, _)) = run_image_env(
        &image,
        &driver,
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

    // PART A: Euler's four-square identity / multiplicativity (0-hyp, probed)
    assert!(
        out.contains("L4_IDENTITY_ALL_OK"),
        "four_sq_mult (Euler four-square identity) did not check:\n{out}"
    );
    // ASSEMBLY: the conditional multiplicative-closure reduction (0-hyp, probed)
    assert!(
        out.contains("L4_ASM_ALL_OK"),
        "lagrange_assembly (multiplicative reduction) did not check:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains(": error:") && !out.contains("Static Errors"),
        "a compile error slipped through:\n{out}"
    );
}

#[test]
#[ignore = "needs /tmp/l4_foursq_star (tools/build-l4-checkpoint.sh)"]
fn four_square_full_theorem() {
    let Some(image) = l4_checkpoint() else {
        eprintln!("SKIP: /tmp/l4_foursq_star missing (tools/build-l4-checkpoint.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/four_square_resume/lagrange_four_square_FULL_driver.sml");
    let driver =
        std::fs::read_to_string(&driver_path).expect("read lagrange_four_square_FULL_driver.sml");

    // Runs ON the four-square base checkpoint: the 9 Euler divide-by-m² leaves →
    // the 16→9 disjE descent step → strict 0<r<m → strong-induction iteration →
    // discharge lagrange_assembly. proofs:=0 is set by the driver to bound RAM.
    let Some((out, _)) = run_image_env(
        &image,
        &common::with_sound_audit(&driver, "four_square", &["lagrange_four_square"]),
        990_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
            ("POLYML_HEAP_BYTES", "3000000000"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // the 9 divide leaves, the assembled descent step, and the iteration
    assert!(
        out.contains("MEGA_ALL_LEAVES_DONE"),
        "the 9 Euler divide-by-m² leaves did not all check:\n{out}"
    );
    assert!(
        out.contains("DSTEP_ALL_OK"),
        "the descent step (16→9 disjE assembly) did not validate:\n{out}"
    );
    assert!(
        out.contains("L4_ITER_ALL_OK"),
        "the strong-induction iteration / discharge did not validate:\n{out}"
    );
    // the theorem itself: 0-hyp, aconv ∀n.∃a b c d. n=a²+b²+c²+d²
    assert!(
        out.contains("MEGA_LAGRANGE_FOUR_SQUARE_PROVED"),
        "Lagrange's four-square theorem did not close (0-hyp aconv check):\n{out}"
    );
    assert!(
        !out.contains("MEGA_FAILED") && !out.contains("MEGA_LAGRANGE_FAILED"),
        "a validation probe reported failure:\n{out}"
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
        out.contains("SOUND_AUDIT_OK four_square"),
        "soundness audit did not certify four_square:\n{out}"
    );
}
