//! CLASSICAL FIBONACCI IDENTITIES in Isabelle/Pure on the polyml-rs interpreter —
//! a fresh flavor (standard Fibonacci, distinct from Zeckendorf's `zfib`).
//!
//! Standard fib (conservative recursion): fib 0 = 0, fib 1 = 1, fib(n+2) = fib(n+1)+fib(n).
//! Each result 0-hyp, aconv-intended, soundness-probed; only classical assumption = ex_middle
//! (a runtime `all_axioms_of` dump confirmed only Pure meta-logic + the conservative NT
//! foundation + 7 conservative recursion axioms for fib/fibsum/dbl; every algebraic lemma derived).
//!
//!   SUM (FIB_SUM_OK):     ⊢ fibsum n + 1 = fib(n+2)   (∑_{i=0}^n fib i = fib(n+2)−1, sub-free)
//!   ADDITION (FIB_ADD_OK): ⊢ fib(m+n+1) = fib(m+1)·fib(n+1) + fib(m)·fib(n)  (sign-free)
//!   CASSINI (FIB_CASSINI_OK), the ℕ parity form (the +1 on opposite sides = (−1)ⁿ sign-free):
//!       fib(2k)·fib(2k+2) + 1 = fib(2k+1)²   and   fib(2k+1)·fib(2k+3) = fib(2k+2)² + 1
//!
//! Self-contained `with_nt_helpers` delta (fib_base + addition + cassini). ultracode
//! wf_c7994e02-6d9; re-verified by hand.
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_fibonacci -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use common::with_nt_helpers;
use std::path::PathBuf;

fn checkpoint() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/isabelle_pure");
    p.exists().then_some(p)
}

#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh)"]
fn fibonacci_sum_addition_cassini() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_fibonacci.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_fibonacci.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &common::with_sound_audit(
            &with_nt_helpers(&driver),
            "fibonacci",
            &["fib_sum", "fib_add2", "cassini_a", "cassini_b"],
        ),
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

    assert!(
        out.contains("FIB_SUM_OK"),
        "sum identity did not check:\n{out}"
    );
    assert!(
        out.contains("FIB_ADD_OK"),
        "addition law did not check:\n{out}"
    );
    assert!(
        out.contains("FIB_CASSINI_OK"),
        "Cassini did not check:\n{out}"
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
        !out.contains("PROBE_UNSOUND") && !out.contains("_FAILED"),
        "a soundness probe fired / an identity FAILED:\n{out}"
    );
    assert!(
        out.contains("SOUND_AUDIT_OK fibonacci"),
        "soundness audit did not certify fibonacci:\n{out}"
    );
}
