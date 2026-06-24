//! GAUSS'S LEMMA — the cornerstone of quadratic reciprocity — by genuine LCF
//! kernel inference in Isabelle/Pure on the polyml-rs interpreter.
//!
//!   gauss_lemma : ⊢ prime2 p ⟹ ¬(p∣a) ⟹ (p−1 = m+m) ⟹
//!                    ∃S. cong p (pow a m) S ∧ (cong p S 1 ∨ cong p S (p−1))
//!
//! i.e. for an odd prime p (p−1 = 2m) coprime to a, a^((p−1)/2) ≡ S (mod p) where
//! S = (−1)^μ is the running product of the per-residue flip signs s_k ∈ {1, p−1}
//! (s_k = 1 when the least residue of a·k is in the lower half, p−1 when it flips
//! to the upper half), and S is ≡ ±1. Crucially the ±1 is derived from the
//! {1,p−1} multiplicative closure ((p−1)²≡1), NOT from the banked Euler dichotomy
//! — so the result genuinely ties a^m to the residue flips (it is strictly more
//! than `a^m ≡ ±1`). `−1` is encoded as `p−1` (= `sub p 1`); `prime2` is the
//! structural prime.
//!
//! Proof chain (all 0-hyp, aconv, no new axioms over the conservative base; the
//! only classical assumption is excluded middle):
//!   abs_inj (injectivity of the least-absolute-residue map; the +/- collision
//!     0<k+k2<p is vacuous) → lar_in_range / lar_cong (the signed residue facts)
//!   → lprod_perm_of_inj (the Wilson pairing generalized from an involution to an
//!     injection) → lar_perm (∏ lar(a·k) = m!) → S1 prod_axk_eq_pow (∏(a·k) =
//!     a^m·m!) → S2 prod_split_sign (fold lar_cong per element with a running sign
//!     product) → cancel m! (coprime to p) → gauss_lemma.
//!
//! Built on the Euler-criterion base extended (new-const discipline) with prodf, a
//! natlist library + lmap, and rmod/lar. Self-contained driver (run directly on
//! /tmp/isabelle_pure, no `with_*` splice). Campaign + the intermediate lemmas:
//! tests/isabelle_support/qr_resume/README.md. Multi-fleet ultracode; re-verified
//! by hand (3,688,737,825 steps → Tagged(0), 77 axioms, only ex_middle classical).
//!
//! The full reciprocity LAW ((p/q)(q/p) = (−1)^(((p−1)/2)((q−1)/2))) additionally
//! needs Eisenstein's lattice-point count on top of this lemma — tracked separately.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_gauss -- --ignored --nocapture
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
fn gauss_lemma() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/qr_resume/gauss_final.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read gauss_final.sml");

    // Self-contained driver (Euler base + prodf + natlist + rmod/lar, then the full
    // Gauss chain) — run directly. ~3.69e9 steps; 3 GB heap like the heavy drivers.
    let Some((out, _)) = run_image_env(
        &image,
        &driver,
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

    // the product identity (S1) and the running-sign split (S2, the hard piece)
    assert!(
        out.contains("PROD_AXK_OK"),
        "prod_axk_eq_pow (∏(a·k) = a^m·m!) did not check:\n{out}"
    );
    assert!(
        out.contains("PROD_SPLIT_OK"),
        "prod_split_sign (running flip-sign product) did not check:\n{out}"
    );
    // Gauss's lemma itself: 0-hyp, aconv ∃S. a^m≡S ∧ S≡±1, S the flip-product
    assert!(
        out.contains("GAUSS_LEMMA_OK"),
        "gauss_lemma did not close (0-hyp aconv + soundness probes):\n{out}"
    );
    assert!(
        out.contains("GAUSS_FINAL_ALL_OK"),
        "the final all-stages gate did not pass:\n{out}"
    );
    // no new axioms smuggled (only ex_middle classical)
    assert!(
        out.contains("gauss_axiom_names_present=[]"),
        "an unexpected axiom was introduced:\n{out}"
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
