//! UNIFIED NUMBER-THEORY BASE for Isabelle/Pure on the polyml-rs interpreter — one
//! driver consolidating the previously-separate branches so downstream work (Fermat's
//! little theorem etc.) builds on a single rich context instead of re-deriving
//! foundations. Everything 0-hypothesis; only classical assumption = excluded middle.
//!
//! Provides + validates (`NT_BASE_OK`):
//!   - classical number theory + Peano add/mult + semiring + classical FOL + le/lt/dvd
//!     + order laws + strong_induct + prime2/prime_cases;
//!   - the DIVISION THEOREM (`div_mod_exists`) and EUCLID'S LEMMA (`euclid_lemma`);
//!   - MODULAR ARITHMETIC: `cong` + `cong_refl`/`sym`/`trans`/`add`/`mult`;
//!   - POWERS: `pow` + `pow_one`/`pow_add`/`pow_mult_base` + `cong_pow`.
//!
//! Built by a 2-seat ultracode workflow (wf_0e7a6ed2-f88) lifting the `cong`
//! (isabelle_modular) and `pow` (isabelle_power) layers onto the Euclid-lemma driver
//! (isabelle_euclid_lemma). The springboard for the Fermat arc (Stage B `p∣C(p,k)` etc.).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_ntbase -- --ignored --nocapture
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
fn unified_number_theory_base() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_ntbase.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_ntbase.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_nt_helpers(&driver),
        280_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // the four layers all present on the one final context
    for thm in [
        "cong_refl", "cong_sym", "cong_trans", "cong_add", "cong_mult", // modular
        "pow_one", "pow_add", "pow_mult_base", "cong_pow",              // powers
        "euclid_lemma",                                                  // division branch
    ] {
        assert!(out.contains(&format!("OK {thm}")), "unified base lemma `{thm}` did not check:\n{out}");
    }
    assert!(out.contains("NT_BASE_OK"), "unified base did not validate:\n{out}");
    assert!(!out.contains("Exception-"), "exception during proof:\n{out}");
}
