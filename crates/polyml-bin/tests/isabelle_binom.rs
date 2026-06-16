//! BINOMIAL COEFFICIENTS + `p ∣ C(p,k)`, in Isabelle/Pure on the polyml-rs
//! interpreter — Stage B of the Fermat-little-theorem arc.
//!
//! On the unified number-theory base (Euclid's lemma + modular powers), defines
//! binomial coefficients via Pascal's rule and proves the celebrated divisibility,
//! each a 0-hypothesis theorem (only classical assumption = excluded middle):
//!   `binom n 0 = 1`, `binom 0 (Suc k) = 0`,
//!   `binom (Suc n)(Suc k) = binom n k + binom n (Suc k)`  (Pascal)
//!   `absorption  : (k+1)·C(n+1,k+1) = (n+1)·C(n,k)`
//!   `p_dvd_binom : prime p ⟹ 0<k ⟹ k<p ⟹ p ∣ C(p,k)`
//!
//! `p_dvd_binom` (a prime divides its inner binomial coefficients) is the keystone
//! of FLT / the freshman's dream mod p: absorption gives `k·C(p,k) = p·C(p−1,k−1)`,
//! so `p ∣ k·C(p,k)`; `p∤k` (0<k<p) + Euclid's lemma ⟹ `p ∣ C(p,k)`. The absorption
//! identity is by induction on n with k universal (object `Forall`), using the IH at
//! two points + both Pascal directions.
//!
//! Built on `isabelle_ntbase.sml` by a 2-phase ultracode pipeline (wf_2f2eeca9-c88):
//! binom + absorption → p_dvd_binom (3 seats, all proved it).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_binom -- --ignored --nocapture
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
fn prime_divides_inner_binomial_coefficients() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/isabelle_support/isabelle_binom.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_binom.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_nt_helpers(&driver),
        280_000_000_000,
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
        out.contains("OK absorption"),
        "absorption identity did not check:\n{out}"
    );
    assert!(
        out.contains("OK p_dvd_binom"),
        "p | C(p,k) did not check:\n{out}"
    );
    assert!(
        out.contains("P_DVD_BINOM_DONE"),
        "Stage-B development did not complete:\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("UNSOUND"),
        "a soundness probe fired UNSOUND:\n{out}"
    );
}
