//! THE CHINESE REMAINDER THEOREM in Isabelle/Pure on the polyml-rs interpreter.
//!
//!   gen_inverse      : ⊢ coprime a m ⟹ 0<m ⟹ ∃b. cong m (a·b) 1
//!   crt_exists       : ⊢ coprime m n ⟹ 0<m ⟹ 0<n ⟹ ∀a b. ∃x. cong m x a ∧ cong n x b
//!   gauss            : ⊢ coprime n m ⟹ n∣(m·c) ⟹ n∣c
//!   coprime_mult_dvd : ⊢ coprime m n ⟹ m∣k ⟹ n∣k ⟹ (m·n)∣k
//!   crt_unique       : ⊢ coprime m n ⟹ cong m x y ⟹ cong n x y ⟹ cong (m·n) x y
//!
//! For coprime moduli m,n and any residues a,b there is an x ≡ a (mod m) and
//! ≡ b (mod n) (EXISTENCE, by x = a·n·s + b·m·t with n·s≡1 mod m, m·t≡1 mod n),
//! and it is unique mod m·n (UNIQUENESS, via Gauss's lemma). Genuine LCF kernel
//! inference over ℕ (two-sided cong, no subtraction); only classical assumption
//! is excluded middle. Each lemma carries a soundness probe.
//!
//! Built on the full gcd/Bézout development (`isabelle_gcd.sml`: coprime_bezout,
//! mod_inverse, dvd_diff) over the unified base, spliced in by `common::with_gcd`.
//! Proved by a 3-phase ultracode fleet (wf_f77ae210-0f5: gen-inverse →
//! crt-existence → crt-uniqueness); re-verified end-to-end by hand before landing.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_crt -- --ignored --nocapture
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
fn chinese_remainder_theorem() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/isabelle_support/isabelle_crt.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_crt.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_sound_audit(
            &common::with_gcd(&driver),
            "crt",
            &["crt_exists", "crt_unique"],
        ),
        700_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // the gcd/Bézout base must load first
    assert!(
        out.contains("MOD_INVERSE_OK"),
        "gcd/Bézout base did not load:\n{out}"
    );
    // each rung of the CRT ladder, by named lemma + phase marker
    for lemma in [
        "gen_inverse",
        "crt_exists",
        "gauss",
        "coprime_mult_dvd",
        "crt_unique",
    ] {
        assert!(
            out.contains(&format!("OK {lemma}")),
            "lemma `{lemma}` did not check:\n{out}"
        );
    }
    for marker in ["GEN_INVERSE_OK", "CRT_EXISTS_OK", "CRT_UNIQUE_OK"] {
        assert!(out.contains(marker), "marker `{marker}` missing:\n{out}");
    }
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("PROBE_UNSOUND"),
        "a soundness probe fired UNSOUND:\n{out}"
    );
    assert!(!out.contains("UNSOUND"), "an UNSOUND marker fired:\n{out}");
    assert!(
        out.contains("SOUND_AUDIT_OK crt"),
        "soundness audit did not certify crt:\n{out}"
    );
}
