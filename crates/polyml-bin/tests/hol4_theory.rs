//! HOL4 Theory-subsystem integration tests.
//!
//! These load the captured reconstruction
//! (`tests/hol4_support/theory_subsystem.sml`) on the warm basis+kernel
//! checkpoint and assert on the result. They are `#[ignore]` because they
//! need `/tmp/hol4_kernel`, built once with:
//!
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh        # builds /tmp/basis_loaded + /tmp/hol4_kernel
//! cargo test --release -p polyml-bin --test hol4_theory -- --ignored --nocapture
//! ```
//!
//! Quick ad-hoc runs without cargo:
//! ```sh
//! HOL4_DIR=$PWD/vendor/hol4 tools/sml-exp.sh /tmp/hol4_kernel \
//!   crates/polyml-bin/tests/hol4_support/theory_subsystem.sml
//! ```

mod common;
use common::*;

/// The Theory subsystem (src/postkernel + portableML/prekernel deps) compiles
/// and loads on our interpreter. As of 2026-05-30 this is 50/54 modules; the
/// 4 stuck are the theorem-DB *search* layer (DB / DBSearchParser /
/// TheoryReader), which Theory itself does not need. Guard at >= 50 so the
/// test is a regression fence without being brittle about the search layer.
#[test]
#[ignore = "slow: needs /tmp/hol4_kernel (tools/build-hol4-checkpoints.sh)"]
fn theory_subsystem_loads() {
    let Some((out, _code)) =
        run_theory_subsystem("val () = print \"THEORY_TEST_SENTINEL\\n\";", 200_000_000_000)
    else {
        eprintln!("SKIP: /tmp/hol4_kernel or vendor/hol4 missing — run tools/build-hol4-checkpoints.sh");
        return;
    };

    assert!(
        out.contains("THEORY_SUBSYSTEM_DONE"),
        "theory_subsystem.sml did not run to completion.\n{}",
        tail(&out, 40)
    );

    let (loaded, total) = parse_loaded(&out).unwrap_or_else(|| {
        panic!("no LOADED_OK marker.\n{}", tail(&out, 40));
    });
    eprintln!("Theory subsystem: {loaded}/{total} modules loaded");
    assert!(
        loaded >= 50,
        "expected >= 50 modules to load, got {loaded}/{total}.\n{}",
        classify_errors(&out)
    );
}

/// `Theory.new_theory` is reachable at runtime: the smoke block compiles
/// against the (opaquely re-ascribed) FinalType/FinalTerm/FinalThm kernel and
/// executes. This documents the current frontier — it asserts new_theory was
/// *reached* (printed OK or RAISED), not that it succeeds; seeding the base
/// theory so it returns cleanly is the next milestone. The captured message is
/// printed for diagnosis.
#[test]
#[ignore = "slow: needs /tmp/hol4_kernel (tools/build-hol4-checkpoints.sh)"]
fn theory_new_theory_runs() {
    let smoke = r#"
val () =
  (let val _  = Theory.new_theory "scratch"
       val bt = Type.mk_type("bool", [])
       val v  = Term.mk_var("p", bt)
       val th = Thm.REFL v
   in print ("NEW_THEORY_OK refl_hyps=" ^ Int.toString (length (Thm.hyp th))
             ^ " curThy=" ^ Theory.current_theory() ^ "\n")
   end)
  handle e => print ("NEW_THEORY_RAISED " ^ General.exnMessage e ^ "\n");
"#;
    let Some((out, _code)) = run_theory_subsystem(smoke, 200_000_000_000) else {
        eprintln!("SKIP: /tmp/hol4_kernel or vendor/hol4 missing — run tools/build-hol4-checkpoints.sh");
        return;
    };

    let ok = out.contains("NEW_THEORY_OK");
    let raised = out.contains("NEW_THEORY_RAISED");
    if ok {
        eprintln!("new_theory succeeded: {}", grep_line(&out, "NEW_THEORY_OK"));
    } else if raised {
        eprintln!("new_theory ran and raised: {}", grep_line(&out, "NEW_THEORY_RAISED"));
    }
    assert!(
        ok || raised,
        "new_theory neither ran nor raised — likely a compile error in the smoke block.\n{}",
        classify_errors(&out)
    );
}

fn grep_line(out: &str, needle: &str) -> String {
    out.lines()
        .find(|l| l.contains(needle))
        .unwrap_or("")
        .trim_start_matches(['>', '#', ' '])
        .to_string()
}
