//! FERMAT'S LITTLE THEOREM, in Isabelle/Pure on the polyml-rs interpreter — the
//! summit of the self-derived number-theory tower.
//!
//!   flt : ⊢ prime p ⟹ a^p ≡ a (mod p)
//!
//! For a prime p and any natural a, a^p ≡ a mod p. A 0-hypothesis theorem; the only
//! classical assumption in the whole tower is excluded middle. A soundness probe
//! confirms the kernel keeps the prime premise (it does NOT collapse to the false
//! unconditional `a^p ≡ a`).
//!
//! Proved via the FRESHMAN'S DREAM (also checked here):
//!   freshman_dream : ⊢ prime p ⟹ (a+b)^p ≡ a^p + b^p (mod p)
//! from the binomial theorem at exponent p — peel the k=0 (b^p) and k=p (a^p)
//! endpoints; every interior `C(p,k)·a^k·b^(p−k)` (0<k<p) is divisible by p
//! (`p_dvd_binom`), so the interior sum is ≡ 0 mod p (`sum_all_dvd` +
//! `dvd_imp_cong_zero`). FLT then follows by induction on a (`0^p=0`; step
//! `(a+1)^p ≡ a^p+1 ≡ a+1` via the freshman's dream + IH + `cong_add`/`cong_trans`).
//!
//! Built on `isabelle_binom_thm.sml` by a 2-phase ultracode pipeline (wf_263aa14e-2ad):
//! helpers → freshman_dream + flt (3 seats, ALL proved it). With Euclid's theorem,
//! √2 irrational, and the FTA, this completes a tour of the landmark theorems of
//! elementary number theory — all proved from first principles by an LCF kernel
//! running on a Rust reimplementation of PolyML.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_flt -- --ignored --nocapture
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
fn fermats_little_theorem() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_flt.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_flt.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        320_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // the freshman's dream (a+b)^p == a^p + b^p mod p
    assert!(out.contains("OK freshman_dream"), "freshman's dream did not check:\n{out}");
    // FERMAT'S LITTLE THEOREM: a^p == a mod p
    assert!(out.contains("OK flt"), "Fermat's little theorem did not check:\n{out}");
    assert!(out.contains("FLT_DONE"), "FLT development did not complete:\n{out}");
    assert!(!out.contains("Exception-"), "exception during proof:\n{out}");
    assert!(!out.contains("UNSOUND"), "a soundness probe fired UNSOUND:\n{out}");
}
