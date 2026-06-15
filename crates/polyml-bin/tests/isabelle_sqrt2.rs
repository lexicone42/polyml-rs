//! √2 IS IRRATIONAL — proved by infinite descent in Isabelle/Pure on the polyml-rs
//! interpreter. The companion capstone to Euclid's theorem.
//!
//!     sqrt2_irrational : ⊢ ¬ (∃a. 0 < a ∧ (∃b. a·a = 2·(b·b)))
//!
//! There are no positive naturals a, b with a² = 2·b² — i.e. √2 is irrational. A
//! 0-hypothesis theorem proved by INFINITE DESCENT via strong (course-of-values)
//! induction on the classical Isabelle/Pure number-theory development; the only
//! classical assumption is excluded middle.
//!
//! Proof: `Sol x ≝ 0<x ∧ ∃b. x²=2b²`; show `∀x. ¬Sol x` by strong induction. A
//! solution x forces x even (`sq_even_even`, via the odd²-is-odd parity argument —
//! no Euclid's lemma), x=2c; cancelling 2 (`mult_left_cancel`) gives `b²=2c²` = Sol b
//! with b<x (`sq_lt_cancel`) and 0<b — a smaller solution, contradicting minimality.
//! A soundness probe confirms the kernel REJECTS the false positivity-dropped variant
//! (a=b=0 is a solution).
//!
//! Built on `isabelle_classical_primes.sml` by a 2-phase ultracode pipeline
//! (wf_d7246a73-e08): parity helpers → descent (2 seats, both proved it).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_sqrt2 -- --ignored --nocapture
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
fn sqrt2_is_irrational_by_infinite_descent() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_sqrt2.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_sqrt2.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_nt_helpers(&driver),
        300_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // the parity development (the descent engine)
    assert!(out.contains("PARITY_OK"), "parity helpers did not check:\n{out}");
    // √2 irrational: no positive a,b with a^2 = 2 b^2, by infinite descent (0-hyp)
    assert!(
        out.contains("OK sqrt2_irrational"),
        "sqrt 2 irrationality did not check:\n{out}"
    );
    assert!(out.contains("SQRT2_DONE"), "sqrt2 development did not complete:\n{out}");
    assert!(!out.contains("Exception-"), "exception during proof:\n{out}");
    assert!(!out.contains("UNSOUND"), "a soundness probe fired UNSOUND:\n{out}");
}
