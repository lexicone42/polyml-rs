//! THE DIVISION THEOREM over the naturals, in Isabelle/Pure on the polyml-rs
//! interpreter — Stage 1 of the FTA-uniqueness arc.
//!
//!   div_mod_exists : ⊢ 0 < b ⟹ ∃q r. a = b·q + r ∧ r < b
//!   div_mod_unique : ⊢ 0 < b ⟹ (a = b·q1+r1 ∧ r1<b) ⟹ (a = b·q2+r2 ∧ r2<b)
//!                          ⟹ q1 = q2 ∧ r1 = r2
//!
//! For a divisor b>0 the quotient and remainder EXIST and are UNIQUE. Both
//! 0-hypothesis theorems, pure LCF kernel inference; only classical assumption =
//! excluded middle. Existence is by strong induction on a with NO subtraction
//! (a<b → (0,a); else a=b+a2 via the le-witness, a2<a, recurse, recompose via
//! mult_Suc_right). The foundation for gcd / Bézout / Euclid's lemma / FTA
//! uniqueness (Stages 2-4).
//!
//! Built on `isabelle_classical_primes.sml` by a 3-seat ultracode fleet
//! (wf_17792bed-545); all three proved existence, one also proved uniqueness.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_division -- --ignored --nocapture
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
fn division_theorem_existence_and_uniqueness() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_division.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_division.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        200_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    assert!(out.contains("OK div_mod_exists"), "division-theorem existence did not check:\n{out}");
    assert!(out.contains("OK div_mod_unique"), "division-theorem uniqueness did not check:\n{out}");
    assert!(out.contains("DIVISION_DONE"), "division development did not complete:\n{out}");
    assert!(!out.contains("Exception-"), "exception during proof:\n{out}");
}
