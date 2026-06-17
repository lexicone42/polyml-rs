//! FERMAT'S TWO-SQUARE THEOREM in Isabelle/Pure on the polyml-rs interpreter —
//! a landmark of elementary number theory, machine-checked on a Rust
//! reimplementation of PolyML.
//!
//!   twosquare : ⊢ prime2 p ⟹ (p−1 = 4k) ⟹ ∃a b. p = a² + b²
//!
//! Every prime p ≡ 1 (mod 4) is a sum of two squares (e.g. 13=2²+3², 29=2²+5²).
//! A 0-hypothesis theorem by genuine LCF kernel inference over the GENUINE
//! structural prime (1<p ∧ ∀d. d∣p ⟹ d=1∨d=p); the only classical assumption is
//! `ex_middle`. p≡1 mod4 is encoded `p−1 = 4k`.
//!
//! The classical proof, assembled from the banked cores:
//!  • Wilson's theorem ⟹ `((p−1)/2)!² ≡ −1 (mod p)`, so −1 is a quadratic
//!    residue (`isabelle_neg1_qr`);
//!  • Thue's lemma (`isabelle_thue`: floor_sqrt + grid + the image-collision
//!    pigeonhole) ⟹ a nontrivial collision `x₁ + c·y₂ ≡ x₂ + c·y₁ (mod p)`;
//!  • the descent: U=|x₁−x₂|, V=|y₁−y₂| give `U² ≡ c²V² ≡ −V²`, so `p ∣ U²+V²`;
//!    with `0 < U²+V² < 2p` (using "a prime is not a perfect square") the only
//!    multiple of p in range forces `U²+V² = p`.
//!
//! Proved by a foundation→2-seat→verify ultracode fleet (wf_737ad703-71d; both
//! seats — direct + robust — proved it independently, agreeing on an identical
//! conservative 67-axiom base). Re-verified end-to-end by hand (Tagged(0),
//! aconv + 0-hyp + soundness probes: needs the prime hyp, needs p≡1 mod4, the
//! conclusion is genuinely a SUM of two squares; Thue/QR/Wilson are USED as the
//! proven lemmas, not re-axiomatized; residue function stays concrete).
//!
//! The driver is SELF-CONTAINED (it embeds the full chain incl. Wilson + the QR +
//! Thue developments with one clashing axiom renamed during the splice), so it is
//! run DIRECTLY, no `with_*` helper.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_twosquare -- --ignored --nocapture
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
fn fermat_two_square() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_twosquare.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_twosquare.sml");

    // Self-contained driver (embeds Wilson + QR + Thue) — run directly.
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

    // p = a² + b² for every prime p ≡ 1 mod 4.
    assert!(
        out.contains("TWOSQ_OK"),
        "two-square theorem did not prove:\n{out}"
    );
    assert!(
        out.contains("TWOSQ_ALL_OK"),
        "TWOSQ_ALL_OK marker missing:\n{out}"
    );
    // Not a degenerate / failed / exceptional run.
    assert!(
        !out.contains("PROBE_UNSOUND"),
        "a soundness probe fired UNSOUND:\n{out}"
    );
    assert!(!out.contains("UNSOUND"), "an UNSOUND marker fired:\n{out}");
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("Static Errors") && !out.contains(": error:"),
        "compile error during proof:\n{out}"
    );
}
