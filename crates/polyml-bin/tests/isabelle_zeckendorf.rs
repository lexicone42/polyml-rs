//! ZECKENDORF'S THEOREM — every positive integer has a UNIQUE representation as a
//! sum of NON-CONSECUTIVE Fibonacci numbers (e.g. 100 = 89 + 8 + 3), proved by
//! kernel inference in Isabelle/Pure on the polyml-rs interpreter.
//!
//!   EXISTENCE   ⊢ ∀n. 0 < n ⟹ ∃r. valid_rep r ∧ rep_sum r = n
//!   UNIQUENESS  ⊢ ∀n r1 r2. valid_rep r1 ⟹ valid_rep r2
//!                          ⟹ rep_sum r1 = n ⟹ rep_sum r2 = n ⟹ r1 = r2
//!
//! Both 0-hypothesis theorems on the classical NT foundation. `zfib` is the
//! distinct-Fibonacci sequence (1,2,3,5,8,…); a representation is an `ixlist` of
//! indices with `valid_rep` forcing strictly-decreasing indices and gaps ≥ 2
//! (the genuine non-consecutive condition). Existence is the greedy algorithm
//! (largest `zfib k ≤ n`, recurse on `n − zfib k`) by strong induction;
//! uniqueness rests on the CRUX sum-bound `zfib k ≤ rep_sum r < zfib(k+1)` for a
//! rep topping at `k`, which pins the largest index from `n` alone. The only
//! non-Peano assumption is excluded middle.
//!
//! Introduces Fibonacci to the Isabelle number-theory tower. Built by ultracode
//! wf_20b7a36f-ce3 (3 seats, all proved BOTH halves independently); this driver
//! is the "robust" seat with explicit kernel soundness probes (the rep is
//! genuinely non-consecutive; `req` genuinely discriminates lists; uniqueness
//! genuinely concludes r1 = r2, not the trivial r1 = r1).
//!
//! `#[ignore]` (needs /tmp/isabelle_pure from tools/build-isabelle-pure.sh):
//! ```sh
//! tools/build-isabelle-pure.sh
//! cargo test --release -p polyml-bin --test isabelle_zeckendorf -- --ignored --nocapture
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
fn zeckendorf_existence_and_uniqueness() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/isabelle_support/isabelle_zeckendorf.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read isabelle_zeckendorf.sml");

    let Some((out, _)) = run_image_env(
        &image,
        &with_nt_helpers(&driver),
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

    // base machinery (zfib + ixlist + rep_sum + valid_rep + the crux sum-bound)
    assert!(
        out.contains("BASE_OK"),
        "Zeckendorf base did not check:\n{out}"
    );
    // EXISTENCE: every n>0 has a valid non-consecutive Fibonacci representation
    assert!(
        out.contains("ZK_EXIST_OK"),
        "existence did not check:\n{out}"
    );
    // UNIQUENESS: the representation is unique
    assert!(
        out.contains("ZK_UNIQUE_OK"),
        "uniqueness did not check:\n{out}"
    );
    // soundness probes: existence rep genuinely valid; uniqueness genuinely r1=r2
    assert!(
        out.contains("ZK_EXIST_PROBE_OK"),
        "existence soundness probe did not pass:\n{out}"
    );
    assert!(
        out.contains("ZK_UNIQUE_PROBE_OK"),
        "uniqueness soundness probe did not pass:\n{out}"
    );
    // both halves together
    assert!(out.contains("ZK_ALL_OK"), "ZK_ALL_OK not reached:\n{out}");

    assert!(
        !out.contains("Exception-"),
        "exception during proof:\n{out}"
    );
    assert!(
        !out.contains("PROBE_UNSOUND"),
        "a soundness probe fired UNSOUND:\n{out}"
    );
    assert!(
        !out.contains(": error:") && !out.contains("Static Errors"),
        "a compile error slipped through:\n{out}"
    );
}
