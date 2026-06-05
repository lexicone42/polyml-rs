//! The classic Pelletier FOL benchmark suite, proved by HOL4's `MESON_TAC` on the
//! polyml-rs interpreter. Pelletier (1986), "Seventy-Five Problems for Testing
//! Automatic Theorem Provers", is THE standard first-order theorem-proving
//! benchmark set.
//!
//! `#[ignore]` (slow — runs 47 MESON proofs in one process; needs /tmp/hol4_meson):
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh meson
//! cargo test --release -p polyml-bin --test hol4_pelletier -- --ignored --nocapture
//! ```
//!
//! RESULT: 46 of 47 proved (P1–P46), including P34 (Andrews's Challenge), P38, and
//! P39 (Russell's paradox). The lone failure, P47 (Schubert's Steamroller), is the
//! EXPECTED failure for plain `MESON_TAC` — HOL4's own `src/meson/test/selftest.sml`
//! marks the identical P47 as expected-to-fail. So we are at parity with upstream
//! HOL4's MESON on the benchmark suite. MESON_TAC is sound, so each PROVED line is a
//! genuine `|- goal` theorem (verified with 0 hypotheses). Problems + driver:
//! `hol4_support/pelletier_problems.sml` (predicates F,S renamed Fp,Sp since F=false,
//! S=combinator in HOL4 — a pure alpha-rename of uninterpreted predicate symbols).

mod common;
use common::*;

#[test]
#[ignore = "slow: 47 MESON proofs; needs /tmp/hol4_meson (build-hol4-checkpoints.sh meson)"]
fn meson_proves_pelletier_suite() {
    let Some(image) = meson_checkpoint_path() else {
        eprintln!("SKIP: /tmp/hol4_meson missing — run tools/build-hol4-checkpoints.sh meson");
        return;
    };
    let Some((out, _)) =
        run_support_driver_on(&image, "pelletier_problems.sml", 200_000_000_000)
    else {
        eprintln!("SKIP: vendor/hol4 or driver missing");
        return;
    };
    assert!(out.contains("PELLETIER_DONE"), "driver did not finish.\n{}", tail(&out, 30));

    // All 46 of P1..P46 prove, each as a 0-hypothesis theorem.
    let proved = out.matches("PROVED HYPS=0").count();
    assert_eq!(proved, 46, "expected 46 zero-hyp MESON proofs, got {proved}.\n{}", tail(&out, 60));

    // No problem in the proved set failed or smuggled a hypothesis.
    assert!(!out.contains(" FAILED"), "a Pelletier problem failed.\n{}", tail(&out, 60));
    for n in 1..=46 {
        assert!(
            out.contains(&format!("PELL P{n} PROVED HYPS=0")),
            "P{n} not proved (0 hyps).\n{}",
            tail(&out, 60)
        );
    }

    // P47 (Schubert's Steamroller) is the expected MESON failure — parity with HOL4.
    assert!(
        out.contains("PELL P47 EXPECTED_FAIL"),
        "P47 should be the expected MESON failure (not a pass, not a crash).\n{}",
        tail(&out, 30)
    );
    assert!(!out.contains("UNEXPECTED_PASS"), "P47 unexpectedly passed?\n{}", tail(&out, 30));
}
