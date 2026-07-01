//! NEGATIVE TEST for the shared soundness audit (`isabelle_support/sound_audit.sml`).
//!
//! Proves the audit has TEETH: on the classical NT foundation it runs
//! `sound_audit` on three theorems and confirms the two synthetic violations
//! are rejected while the genuine one is certified —
//!
//!   neg_clean    (prime_divisor_exists)          -> SOUND_AUDIT_OK
//!   neg_smuggled (fabricated non-allowlist axiom) -> SOUND_AUDIT_FAIL
//!   neg_oracle   (Skip_Proof oracle taint)        -> SOUND_AUDIT_FAIL
//!
//! Without this, the positive `SOUND_AUDIT_OK` asserts in the ~31 theorem tests
//! could be vacuously true. Here we show the check distinguishes sound from
//! unsound input, so a real violation WOULD flip the assert to a panic.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_sound_audit_negative -- --ignored --nocapture
//! ```

mod common;
use common::{run_image_env, sound_audit_prelude, with_nt_helpers};
use std::path::PathBuf;

fn checkpoint() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/isabelle_pure");
    p.exists().then_some(p)
}

#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn sound_audit_rejects_smuggled_axiom_and_oracle() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let delta_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/sound_audit_negative.sml");
    let delta = std::fs::read_to_string(&delta_path).expect("read sound_audit_negative.sml");

    // Build: NT foundation (adds ex_middle) + the negative setup + the audit
    // routine, then explicitly audit all three thms with distinct labels.
    let driver = format!(
        "{}\n{}\n\
         val () = sound_audit \"neg_clean\" [neg_clean_thm];\n\
         val () = sound_audit \"neg_smuggled\" [neg_smuggled_thm];\n\
         val () = sound_audit \"neg_oracle\" [neg_oracle_thm];\n\
         val () = TextIO.output (TextIO.stdOut, \"NEG_AUDIT_DONE\\n\");\n",
        with_nt_helpers(&delta),
        sound_audit_prelude(),
    );

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        300_000_000_000,
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
        out.contains("NEG_AUDIT_DONE"),
        "negative driver did not run to completion:\n{out}"
    );

    // The genuine theorem is certified.
    assert!(
        out.contains("SOUND_AUDIT_OK neg_clean"),
        "the audit failed to certify a genuine conservative theorem:\n{out}"
    );

    // The fabricated (non-allowlisted) axiom is REJECTED — and the reason names
    // the smuggled axiom.
    assert!(
        out.contains("SOUND_AUDIT_FAIL neg_smuggled"),
        "the audit did NOT reject a fabricated non-allowlist axiom (no teeth):\n{out}"
    );
    assert!(
        !out.contains("SOUND_AUDIT_OK neg_smuggled"),
        "the audit wrongly CERTIFIED a fabricated axiom:\n{out}"
    );
    assert!(
        out.contains("NONALLOWLISTED_AXIOM smuggled_false_lemma"),
        "the smuggled axiom was not named in the failure report:\n{out}"
    );

    // The oracle-tainted theorem is REJECTED — even under Proofterm.proofs := 0.
    assert!(
        out.contains("SOUND_AUDIT_FAIL neg_oracle"),
        "the audit did NOT reject an oracle-tainted (Skip_Proof) theorem:\n{out}"
    );
    assert!(
        !out.contains("SOUND_AUDIT_OK neg_oracle"),
        "the audit wrongly CERTIFIED an oracle-tainted theorem:\n{out}"
    );
    assert!(
        out.contains("ORACLE Pure.skip_proof"),
        "the skip_proof oracle was not named in the failure report:\n{out}"
    );
}
