//! −1 IS A QUADRATIC RESIDUE mod p for p ≡ 1 (mod 4) — the Lagrange / First
//! Supplement to Quadratic Reciprocity (easy direction), in Isabelle/Pure on the
//! polyml-rs interpreter. The gateway to Fermat's two-square theorem.
//!
//!   wsq : ⊢ prime2 p ⟹ (p−1 = 4k) ⟹ cong p (w·w) (p−1)      where w = ((p−1)/2)!
//!   qr  : ⊢ prime2 p ⟹ (p−1 = 4k) ⟹ ∃x. cong p (x·x) (p−1)
//!
//! i.e. for a prime p ≡ 1 (mod 4), `((p−1)/2)!` is an explicit square root of −1
//! (≡ p−1) mod p, so −1 is a quadratic residue. Both 0-hyp theorems by genuine
//! LCF kernel inference; only classical assumption = `ex_middle`. `prime2` is the
//! genuine structural prime; `cong` is two-sided ℕ congruence; p ≡ 1 mod 4 is
//! encoded as `p−1 = (k+k)+(k+k)`.
//!
//! Proof (the classical argument): m = (p−1)/2 is even; by **Wilson's theorem**
//! (the proven `wilson`, not re-axiomatized) `(p−1)! ≡ −1`; pairing j with p−j in
//! [1..p−1] gives `(p−1)! ≡ (−1)^m·(m!)²`, and with m even the sign vanishes, so
//! `(m!)² ≡ −1`. The fleet used the **pair-up** route — each pair `(p−a)(p−b) ≡
//! a·b` cancels its own signs (`parity_crux`), avoiding `(−1)^m` entirely.
//!
//! Built on `common::with_wilson` (Wilson's theorem on the modular-inverse base)
//! by a foundation→3-seat→verify ultracode fleet (wf_a1850dba-804); all 3 seats
//! proved it, two independent routes (pair-up + signed) converged with a p=5
//! numeric cross-check. Re-verified end-to-end by hand (axiom audit: only
//! conservative foundation + `ex_middle` + the conservative `uprod` recursion;
//! Wilson is the proven theorem; soundness probes confirm it needs the prime +
//! p≡1mod4 hypotheses and the residue is p−1 = −1, not 0).
//!
//! NOT here: the converse (p ≡ 3 mod 4 ⟹ −1 is NOT a QR), and piece B of
//! Fermat's two-square — Thue's pigeonhole descent turning `x²≡−1` into
//! `p = a²+b²` (needs finite-counting machinery the tower lacks).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_neg1_qr -- --ignored --nocapture
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
fn neg_one_is_qr_mod_p() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_neg1_qr.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_neg1_qr.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_wilson(&driver),
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

    // ((p−1)/2)!² ≡ −1, and ∃x. x² ≡ −1 mod p.
    assert!(
        out.contains("NEG1QR_WSQ_OK"),
        "((p-1)/2)!^2 ≡ -1 did not prove:\n{out}"
    );
    assert!(
        out.contains("NEG1QR_OK"),
        "-1-is-a-QR did not prove:\n{out}"
    );
    assert!(
        out.contains("NEG1QR_ALL_OK"),
        "NEG1QR_ALL_OK marker missing:\n{out}"
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
