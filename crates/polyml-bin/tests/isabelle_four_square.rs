//! TOWARD LAGRANGE'S FOUR-SQUARE THEOREM — the proved core, by kernel inference
//! in Isabelle/Pure on the polyml-rs interpreter.
//!
//! The full theorem (∀n. ∃a b c d. n = a²+b²+c²+d²) is NOT yet proved. This test
//! fences the two genuine 0-hyp results the campaign DID land (the graceful-floor
//! sub-results of a staged multi-phase attempt):
//!
//!   PART A — Euler's four-square IDENTITY (multiplicativity):
//!     four_sq_mult : ⊢ four_sq m ⟹ four_sq n ⟹ four_sq (m·n)
//!     (the product of two sums of four squares is a sum of four squares;
//!      `four_sq k := ∃a b c d. k = a²+b²+c²+d²`, an object existential, not an
//!      axiom). Proved via a ring-over-ℕ decision procedure with absdiff handling
//!      the signed cross terms w,x,y,z.
//!
//!   ASSEMBLY — the multiplicative-closure REDUCTION:
//!     lagrange_assembly : ⊢ (⋀p. prime2 p ⟹ four_sq p) ⟹ (⋀n. four_sq n)
//!     (IF every prime is a sum of four squares THEN every natural is — via
//!      prime_cases + strong_induct + four_sq_mult; prime2 = structural prime).
//!
//! Self-contained driver (embeds the two-square base: Thue pigeonhole + Wilson/QR
//! + cong + the absdiff/ring machinery) — run DIRECTLY, no `with_*` helper. 0 new
//! axioms over the 67-axiom conservative base; the only classical assumption is
//! excluded middle. Soundness probes confirm the identity is genuinely conditional
//! and concludes four_sq(m·n) (not m+n), and the assembly genuinely needs the prime
//! hypothesis.
//!
//! The two OPEN cruxes for the full theorem (resume material in
//! tests/isabelle_support/four_square_resume/, plan in
//! docs/four-square-progress-2026-06-17.md): PART B front-end (residue-set
//! pigeonhole) + PART C descent step (Euler-identity divide-by-m²).
//!
//! Built by ultracode wf_abb7c4f3-0ba; re-verified by hand.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_four_square -- --ignored --nocapture
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
