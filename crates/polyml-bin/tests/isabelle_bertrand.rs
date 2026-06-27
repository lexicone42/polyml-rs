//! BERTRAND'S POSTULATE — ∀n. 0<n ⟹ ∃ prime p. n < p ≤ 2n — by genuine LCF
//! kernel inference in Isabelle/Pure on the polyml-rs interpreter (Erdős's proof).
//!
//!   bertrand : ⊢ ∀n. lt 0 n ⟹ ∃p. prime2 p ∧ lt n p ∧ le p (add n n)
//!
//! 0-hypothesis (hyps_of = [] AND extra_shyps = []); the conclusion asserts a
//! STRUCTURAL prime strictly greater than n and at most 2n (range-probed — not
//! weakened); the only classical assumption is ex_middle. The proof adds NO
//! prime-existence / Bertrand / SEB / inequality axiom (audited by name at the
//! end of the driver); the lone non-Peano constants are `bitlen` (2 conservative
//! recursion eqns) and the number-theory ladder from the f7 base.
//!
//! The full proof is assembled from seven committed pieces (concatenated in order;
//! the five intermediate appendices have their trailing `OS.Process.exit` stripped
//! so the driver runs to EOF). It is HEAVY: ~224 billion bytecode steps, dominated
//! by `prime2 631` (unary trial-division) and the f7 base load — needs a 12 GB
//! heap and runs ~25–35 min.
//!
//! Proof architecture (Erdős):
//!   bertrand_f7_full.sml       — central-binomial machinery: cb_lower, cb_refined
//!                                (4^(2n/3) refinement), threshold_assembled, the
//!                                primorial bound, p-adic valuation, FTA factorization
//!   bertrand_w1_appendix.sml   — bertrand_large_given_seb (the threshold ⟹ a prime
//!                                exists for n≥513, by contradiction) + seb_reduce
//!   w1_crude_appendix.sml      — seb_tail_reduce + the bitlen tower
//!   w1_pow_poly_appendix.sml   — crude_tail: SEB for ALL s≥36 via a fixed exponent
//!                                b=⌊(s+9)/4⌋ + a poly-vs-exp induction (no log layer)
//!   bertrand_ch_appendix.sml   — bertrand_chain: a prime in (n,2n] for all n<631
//!                                (prime2 of 2,3,5,7,13,23,43,83,163,317,631 proved)
//!   bertrand_jewel_appendix.sml— the fat-margin s=35 case + seb_full_tail (SEB for
//!                                all n≥631) + bertrand_large(n≥631) + bertrand_given_chain
//!   bertrand_full_discharge_appendix.sml — discharge the real proved chain ⟹ bertrand
//!
//! `#[ignore]` (needs the warm Pure checkpoint; heavy):
//! ```sh
//! tools/build-isabelle-pure.sh   # -> /tmp/isabelle_pure (one-time)
//! cargo test --release -p polyml-bin --test isabelle_bertrand -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use std::path::PathBuf;

fn checkpoint() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/isabelle_pure");
    p.exists().then_some(p)
}

#[test]
#[ignore = "needs /tmp/isabelle_pure (tools/build-isabelle-pure.sh); ~25-35 min, 12 GB heap"]
fn bertrands_postulate() {
    let Some(image) = checkpoint() else {
        eprintln!("SKIP: /tmp/isabelle_pure missing (tools/build-isabelle-pure.sh)");
        return;
    };
    let dir =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/isabelle_support/bertrand_resume");
    let read = |name: &str| -> String {
        std::fs::read_to_string(dir.join(name)).unwrap_or_else(|e| panic!("read {name}: {e}"))
    };
    // The f7 base + full-discharge are concatenated verbatim; the five intermediate
    // appendices have their trailing `OS.Process.exit` removed so the driver does not
    // halt before the next piece (matches the reproduced committed concat).
    let strip = |name: &str| -> String {
        read(name)
            .lines()
            .filter(|l| !l.contains("OS.Process.exit"))
            .collect::<Vec<_>>()
            .join("\n")
    };
    let mut driver = String::new();
    driver.push_str(&read("bertrand_f7_full.sml"));
    driver.push('\n');
    for p in [
        "bertrand_w1_appendix.sml",
        "w1_crude_appendix.sml",
        "w1_pow_poly_appendix.sml",
        "bertrand_ch_appendix.sml",
        "bertrand_jewel_appendix.sml",
    ] {
        driver.push_str(&strip(p));
        driver.push('\n');
    }
    driver.push_str(&read("bertrand_full_discharge_appendix.sml"));
    driver.push('\n');

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        990_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
            ("POLYML_HEAP_BYTES", "12000000000"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };

    // The chain's large primes genuinely proved (not asserted)
    assert!(
        out.contains("CH prime2 631 0hyp=true"),
        "prime2 631 (the top chain prime) did not prove 0-hyp:\n{out}"
    );
    // The s=35 fat-margin case + SEB for all n≥631
    assert!(
        out.contains("SEB_FULL_TAIL_OK"),
        "seb_full_tail missing:\n{out}"
    );
    assert!(
        out.contains("BERTRAND_LARGE631_OK"),
        "bertrand_large(n≥631) missing:\n{out}"
    );
    // The headline: unconditional Bertrand, 0-hyp, aconv, strict range
    assert!(
        out.contains("bertrand 0hyp=true aconv=true"),
        "the unconditional bertrand is not 0-hyp + aconv:\n{out}"
    );
    assert!(
        out.contains("BERTRAND_FULL_RANGE_PROBE_OK"),
        "the conclusion was weakened (range probe failed — must be a prime strictly >n and ≤2n):\n{out}"
    );
    assert!(
        out.contains("BERTRAND_PROVED"),
        "BERTRAND_PROVED master gate missing:\n{out}"
    );
    // Soundness: only ex_middle classical; nothing smuggled.
    assert!(
        out.contains("BERTRAND_FINAL_AXIOM_AUDIT total=68 classical=1")
            && out.contains("suspicious=0"),
        "axiom audit not clean (expected only ex_middle classical, nothing smuggled):\n{out}"
    );
    assert!(
        !out.contains("Exception-"),
        "exception during the proof:\n{out}"
    );
}
