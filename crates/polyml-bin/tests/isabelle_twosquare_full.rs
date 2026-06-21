//! TOWARD FERMAT'S TWO-SQUARE FULL IFF — the two banked graceful-floor lemmas.
//!
//! GOAL (multi-fleet, NOT closed): n is a sum of two squares IFF every prime
//! p ≡ 3 (mod 4) divides n to an EVEN power. This file banks the two genuinely
//! valuable + independently-citable lemmas the campaign produced; the full iff
//! (and the only-if descent / if-direction FTA volume) remain a follow-up.
//!
//! (1) brahmagupta — the Brahmagupta-Fibonacci sum-of-two-squares MULTIPLICATIVITY
//!     identity (the four_sq_mult analogue for two squares):
//!         |- Ex P Q. (a^2+b^2)*(c^2+d^2) = P^2 + Q^2
//!     (the faithful sum-PRESERVATION form: the literal `sub` form is FALSE in
//!     truncated ℕ; P = |a*c - b*d| is produced by an le_total case-split.)
//!     Built on `common::with_nt_helpers` (the classical NT foundation). 0-hyp,
//!     aconv-intended, soundness-probed (NOT the false single-square form).
//!     ~3.15B steps. Marker: BRAHMAGUPTA_DONE.
//!
//! (2) key_onlyif — the only-if KEY lemma ("-1 is not a QR mod p≡3mod4"):
//!         |- prime2 p ==> (Ex k. p = (k+k+k+k)+3) ==> p | a^2+b^2
//!              ==> (p|a /\ p|b)
//!     Built on the (self-contained) isabelle_primes_1mod4 spine (the
//!     euler_criterion/FLT base + parity machinery: apm1, lagrange_roots).
//!     0-hyp, aconv-intended, 4 soundness probes (needs mod4, needs dvd,
//!     conjunctive conclusion, NOT the false p≡1mod4 companion). ~2.63B steps.
//!     Marker: KEY_ONLYIF_OK.
//!
//! Both re-verified independently FROM SCRATCH (verifier seat), Tagged(0),
//! 0-hyp, aconv true; runtime `Theory.all_axioms_of` audit clean (brahmagupta
//! 38 axioms, key_onlyif 49 — all Pure meta-logic + conservative recursion +
//! object-logic ND rules + the single classical ex_middle; ZERO axiom mentions
//! the conclusion). Concrete kernel soundness probes (on the brahmagupta base):
//! ACCEPT 2/5/9/13 as sums of two squares (explicit witnesses), REJECT 3/7/21
//! (every candidate witness refuted to oFalse by genuine inference).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_twosquare_full -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use common::with_nt_helpers;
use std::path::PathBuf;

fn checkpoint() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/isabelle_pure");
    p.exists().then_some(p)
}

fn support(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/twosquare_full_resume")
        .join(name)
}

const ENV: &[(&str, &str)] = &[
    ("ML_SYSTEM", "polyml"),
    ("ML_PLATFORM", "x86_64-linux"),
    ("ISABELLE_HOME", "/tmp/isa"),
];

/// Brahmagupta-Fibonacci multiplicativity — spliced via `with_nt_helpers`.
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn brahmagupta_multiplicativity() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    // The committed delta is the splice-ready form (no restore_pure_context;
    // with_nt_helpers prepends the foundation). The resume dir currently holds
    // the self-contained `ts_brahmagupta_full.sml`; for banking, the delta
    // `ts_brahmagupta.sml` (the proof only) is the file to splice.
    let driver = std::fs::read_to_string(support("ts_brahmagupta.sml"))
        .expect("read ts_brahmagupta.sml");

    let Some((out, _)) = run_image_env(&image, &with_nt_helpers(&driver), 990_000_000_000, ENV)
    else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(out.contains("BRAHMAGUPTA_DONE"), "brahmagupta did not prove:\n{out}");
    assert!(
        out.contains("brahmagupta aconv intended = true"),
        "brahmagupta conclusion not aconv the intended statement:\n{out}"
    );
    assert!(
        out.contains("PROBE_OK brahmagupta"),
        "soundness probe (not the false single-square form) missing:\n{out}"
    );
    assert!(!out.contains("PROBE_UNSOUND") && !out.contains("BRAHMAGUPTA_FAILED"),
        "a soundness probe fired / lemma FAILED:\n{out}");
    assert!(!out.contains("Exception-"), "exception during proof:\n{out}");
    assert!(
        !out.contains("Static Errors") && !out.contains(": error:"),
        "compile error during proof:\n{out}"
    );
}

/// The only-if KEY lemma — self-contained driver (the primes_1mod4 spine).
#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn key_only_if_lemma() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    // Self-contained (embeds the primes_1mod4 / euler / FLT spine) — run directly.
    let driver = std::fs::read_to_string(support("ts_key_lemma.sml"))
        .expect("read ts_key_lemma.sml");

    let Some((out, _)) = run_image_env(&image, &driver, 990_000_000_000, ENV) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(out.contains("KEY_ONLYIF_OK"), "key only-if lemma did not prove:\n{out}");
    assert!(out.contains("KEY hyps=0 aconv=true"), "0-hyp / aconv check failed:\n{out}");
    assert!(
        out.contains("PROBE_OK key_onlyif"),
        "soundness probes (mod4 / dvd / conjunction / not-1mod4) missing:\n{out}"
    );
    assert!(!out.contains("PROBE_UNSOUND") && !out.contains("KEY_ONLYIF_FAILED"),
        "a soundness probe fired / lemma FAILED:\n{out}");
    assert!(!out.contains("Exception-"), "exception during proof:\n{out}");
    assert!(
        !out.contains("Static Errors") && !out.contains(": error:"),
        "compile error during proof:\n{out}"
    );
}
