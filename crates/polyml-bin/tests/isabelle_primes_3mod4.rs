//! INFINITELY MANY PRIMES ≡ 3 (mod 4) in Isabelle/Pure on the polyml-rs
//! interpreter — the classical baby case of Dirichlet's theorem.
//!
//!   p3mod4_all : ⊢ ∀n. ∃q. prime2 q ∧ n < q ∧ q ≡ 3 (mod 4)
//!
//! (prime2 = structural prime; n<q = le (Suc n) q, genuine strict order;
//!  q ≡ 3 mod 4 encoded additively as ∃t. q = 4·t + 3.) A 0-hypothesis theorem
//! by genuine LCF kernel inference; only classical assumption = `ex_middle`.
//!
//! Euclid-style proof: given n, N = 4·n! − 1 = 4·(n!−1) + 3 ≡ 3 mod 4 and N>1;
//! the key lemma (by strong induction) — a number ≡ 3 mod 4 with m>1 has a prime
//! factor ≡ 3 mod 4 (since a product of `≡1`-factors stays `≡1`: `mul_r3_split`) —
//! gives a prime q ≡ 3 mod 4 dividing N; and q > n, since a prime ≤ n divides n!
//! and would then divide both N and N+1 = 4·n!, hence 1 (consec_coprime).
//!
//! Built on `common::with_euclid` (the factorial / `dvd_fact` / `consec_coprime`
//! machinery on the classical-primes foundation) by a foundation→3-seat→verify
//! ultracode fleet (wf_e8b99c4e-d3e, all 3 seats proved it); re-verified
//! end-to-end by hand (1.18B steps, Tagged(0), axiom audit clean, soundness
//! probes confirm the n<q orientation + the mod-4 + primality conjuncts).
//!
//! Scope (honest): the elementary 3-mod-4 case only; the ≡1-mod-4 companion needs
//! −1 being a QR (beyond Euclid), and the general Dirichlet theorem needs
//! L-functions. This sits one rung above the plain infinitude of primes.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_primes_3mod4 -- --ignored --nocapture
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
fn primes_three_mod_four() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_primes_3mod4.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_primes_3mod4.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_euclid(&driver),
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

    // ∀n. ∃q. prime2 q ∧ n<q ∧ q≡3 mod4.
    assert!(out.contains("P3MOD4_OK"), "theorem did not prove:\n{out}");
    assert!(
        out.contains("P3MOD4_ALL_OK"),
        "P3MOD4_ALL_OK marker missing:\n{out}"
    );
    // 0-hyp + soundness probes (n<q orientation, mod-4 + primality conjuncts present).
    assert!(
        out.contains("P3MOD4_NOHYPS_OK"),
        "0-hyp check did not fire:\n{out}"
    );
    assert!(
        out.contains("P3MOD4_PROBES_OK"),
        "soundness probes did not all pass:\n{out}"
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
