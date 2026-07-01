//! INFINITELY MANY PRIMES ≡ 1 (mod 4), in Isabelle/Pure on the polyml-rs
//! interpreter — the companion to the banked ≡ 3 (mod 4) result.
//!
//!   p1m4_inf : ⊢ ∀n. ∃q. prime2 q ∧ n < q ∧ (∃t. q = 4·t + 1)
//!
//! For every n there is a (genuine structural) prime q > n with q ≡ 1 (mod 4) —
//! so there are infinitely many. Proved 0-hyp by genuine LCF kernel inference;
//! only classical assumption = excluded middle.
//!
//!   KEY LEMMA (p1m4_key — the First Supplement's hard direction, the converse
//!   of the banked neg1_qr): ⊢ prime2 q ⟹ 2<q ⟹ ¬(q∣x) ⟹ x²≡−1 (mod q)
//!     ⟹ ∃t. q = 4·t + 1.   (Odd prime q∤x with −1 a QR ⟹ q ≡ 1 mod 4, via
//!   FLT (q∤x ⟹ x^(q−1)≡1) + parity: q≡3 mod4 makes (q−1)/2 odd, so
//!   x^(q−1) = (x²)^((q−1)/2) ≡ (−1)^odd = −1 ≢ 1, contradicting FLT.)
//!
//!   INFINITUDE: Euclid construction N = (2·n!)² + 1; a prime divisor q has
//!   (2n!)² ≡ −1 (mod q), so q ≡ 1 mod 4 by the key lemma, and q > n via
//!   dvd_fact + consec-coprimality.
//!
//! Self-contained driver (run DIRECTLY, like isabelle_twosquare/euler) — it
//! MERGES the FLT/euler-criterion branch (lagrange_roots/apm1) with the
//! euclid/classical-primes branch (prime_divisor_exists/dvd_fact/consec_coprime),
//! re-deriving the factorial machinery onto the merged theory. 0 axioms mention
//! prime2/cong/dvd/the-mod-4-conjunct (all DEFINED via FOL connectives); both
//! results 0-hyp + aconv-intended + soundness-probed. Re-verified by hand:
//! Tagged(0), ~2.6B steps. ultracode wf_76164d04-62a.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_primes_1mod4 -- --ignored --nocapture
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
fn infinitely_many_primes_1_mod_4() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_primes_1mod4.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_primes_1mod4.sml");

    // Self-contained driver (embeds the merged FLT + euclid/factorial base) — run directly.
    let Some((out, _)) = run_image_env(
        &image,
        &common::with_sound_audit(&driver, "primes_1mod4", &["p1m4_inf"]),
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

    // KEY LEMMA: x²≡−1 mod odd-prime-q ⟹ q≡1 mod4 (0-hyp, aconv, probed)
    assert!(
        out.contains("P1M4_KEY_OK"),
        "key lemma did not check:\n{out}"
    );
    // INFINITUDE: ∀n. ∃q>n prime, q≡1 mod4 (0-hyp, aconv, probed)
    assert!(
        out.contains("P1M4_INF_OK"),
        "infinitude did not check:\n{out}"
    );
    // both 0-hyp + aconv the intended statements
    assert!(
        out.contains("KEY hyps=0 aconv=true") && out.contains("INF hyps=0 aconv=true"),
        "a result is not 0-hyp / aconv-intended:\n{out}"
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
        !out.contains("PROBE_UNSOUND") && !out.contains("FAIL"),
        "a soundness probe fired / a check FAILed:\n{out}"
    );
    assert!(
        out.contains("SOUND_AUDIT_OK primes_1mod4"),
        "soundness audit did not certify primes_1mod4:\n{out}"
    );
}
