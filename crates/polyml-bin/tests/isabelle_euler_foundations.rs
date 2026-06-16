//! EULER FOUNDATIONS toward Euler's theorem, in Isabelle/Pure on the polyml-rs interpreter.
//!
//!   lprod_perm : ⊢ lnodup L1 ⟹ lnodup L2 ⟹ (∀x. lmem x L1 ⟺ lmem x L2) ⟹ lprod L1 = lprod L2
//!   gcdf / rrl / phi : a gcd function (Euclid via rmod), the reduced-residue list, and φ
//!   lmem_rrl   : ⊢ lmem r (rrl n) ⟺ (lmem r (upto (n−1)) ∧ coprime r n)
//!
//! The two new ingredients Euler needs beyond the Wilson machinery: **permutation
//! invariance** of the list product (Euler's `x↦a·x` is a bijection on the reduced
//! residues, not an involution) — proved by structural list induction with the second
//! list generalized via a fresh object natlist-universal quantifier — and the
//! **reduced-residue list with φ** (a decidable coprimality test via a `gcd` function
//! from `rmod`). Both 0-hyp, with soundness probes.
//!
//! Built on the Wilson-inverse base via `common::with_wilson_inverse`. Proved by a
//! 2-goal ultracode fleet (wf_5604358b-d48); re-verified end-to-end by hand.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_euler_foundations -- --ignored --nocapture
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
fn euler_foundations() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_euler_foundations.sml");
    let driver =
        std::fs::read_to_string(&driver_path).expect("read isabelle_euler_foundations.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_wilson_inverse(&driver),
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

    assert!(
        out.contains("INVERSE_FN_OK"),
        "Wilson-inverse base did not load:\n{out}"
    );
    assert!(
        out.contains("OK lprod_perm"),
        "lprod_perm did not check:\n{out}"
    );
    assert!(
        out.contains("PERM_INV_OK"),
        "PERM_INV_OK marker missing:\n{out}"
    );
    assert!(
        out.contains("OK lmem_rrl"),
        "lmem_rrl did not check:\n{out}"
    );
    assert!(
        out.contains("REDUCED_RES_OK"),
        "REDUCED_RES_OK marker missing:\n{out}"
    );
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
