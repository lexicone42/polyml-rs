//! HOL4 term/type parser integration tests.
//!
//! These drive HOL4's real `Parse.Term` / `Parse.Type` (src/parse, 79 modules)
//! on the warm `/tmp/hol4_parse` checkpoint and assert the parser produces the
//! right HOL4 term/type structure. They are `#[ignore]` because they need the
//! checkpoint chain, built once with:
//!
//! ```sh
//! cargo build --release -p polyml-bin
//! tools/build-hol4-checkpoints.sh        # basis -> kernel -> theory -> parse
//! cargo test --release -p polyml-bin --test hol4_parse -- --ignored --nocapture
//! ```
//!
//! Why this checkpoint exists at all: the parser core was blocked for several
//! sessions by a *missing pervasive `Interrupt`*. Real PolyML installs
//! Interrupt/Bind/Match into the initial top-level namespace
//! (mlsource/MLCompiler/INITIALISE_.ML:524); basis/General.sml re-binds
//! Bind/Match/Overflow/etc. at top level but NOT Interrupt, and our checkpoint
//! export/reload drops the compiler-pervasive one — so a bare `Interrupt` was
//! UNBOUND. HOL4's src/portableML/Portable.sml uses `... handle Interrupt =>
//! raise Interrupt | _ => NONE` for Lib.total / Lib.can / with_exn; with
//! Interrupt unbound those parse as a catch-all *variable* that re-raises
//! EVERYTHING, so total/can never returned NONE — silently breaking
//! term_grammar's min_grammar build (Overload.add_overloading -> strip_comb ->
//! total dest_comb re-raised "not a comb"). The fix is one line in
//! build_kernel_checkpoint.sml (`exception Interrupt = RunCall.Interrupt;`).

mod common;
use common::*;

/// Run `sml` on the warm parser checkpoint. Returns None (caller skips) if
/// `/tmp/hol4_parse` or `vendor/polyml` are absent.
fn run_parse(sml: &str) -> Option<(String, i32)> {
    let image = parse_checkpoint_path()?;
    run_image_env(&image, sml, 50_000_000_000, &[])
}

const SKIP: &str =
    "SKIP: /tmp/hol4_parse missing — run tools/build-hol4-checkpoints.sh parse";

/// `Parse.Type` turns a quotation into the right HOL4 type, and `Parse.Term`
/// turns quotations into variables, applications, and lambda abstractions —
/// i.e. HOL4's full term/type parser runs on our interpreter.
#[test]
#[ignore = "slow: needs /tmp/hol4_parse (tools/build-hol4-checkpoints.sh parse)"]
fn parser_parses_types_terms_and_lambdas() {
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val () =
  let val ty = Parse.Type [QUOTE ":('a -> 'b) -> 'a -> 'b"]
  in if Lib.can Type.dom_rng ty then pr "PARSE_TYPE_OK\n"
     else pr "PARSE_TYPE_BAD\n" end;
val () =
  let val tm = Parse.Term [QUOTE "x:'a"]
  in if Term.is_var tm andalso #1 (Term.dest_var tm) = "x" then pr "PARSE_VAR_OK\n"
     else pr "PARSE_VAR_BAD\n" end;
val () =
  let val tm = Parse.Term [QUOTE "(f:'a->'b) x"]
  in if Term.is_comb tm then pr "PARSE_COMB_OK\n" else pr "PARSE_COMB_BAD\n" end;
val () =
  let val tm = Parse.Term [QUOTE "\\(x:'a). x"]
      val (v, body) = Term.dest_abs tm
  in if Term.is_var v andalso Term.aconv v body then pr "PARSE_LAMBDA_OK\n"
     else pr "PARSE_LAMBDA_BAD\n" end;
pr "PARSE_TEST_DONE\n";
"#;
    let Some((out, _code)) = run_parse(driver) else {
        eprintln!("{SKIP}");
        return;
    };
    for sentinel in [
        "PARSE_TYPE_OK",
        "PARSE_VAR_OK",
        "PARSE_COMB_OK",
        "PARSE_LAMBDA_OK",
        "PARSE_TEST_DONE",
    ] {
        assert!(
            out.contains(sentinel),
            "missing {sentinel}; Parse.Term/Parse.Type did not behave.\n{}",
            tail(&out, 40)
        );
    }
    assert!(
        !out.contains("PARSE_TYPE_BAD")
            && !out.contains("PARSE_VAR_BAD")
            && !out.contains("PARSE_COMB_BAD")
            && !out.contains("PARSE_LAMBDA_BAD"),
        "a parse produced the wrong structure.\n{}",
        tail(&out, 40)
    );
}

/// Regression fence for the keystone: HOL4's `Lib.total` must return `NONE`
/// when its function argument raises (it relies on a pervasive `Interrupt`).
/// If `Interrupt` is unbound again, `total` re-raises and this fails.
#[test]
#[ignore = "slow: needs /tmp/hol4_parse (tools/build-hol4-checkpoints.sh parse)"]
fn lib_total_swallows_non_interrupt_exceptions() {
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val () =
  case Lib.total (fn _ => raise Fail "boom") 0 of
      NONE   => pr "TOTAL_NONE_OK\n"
    | SOME _ => pr "TOTAL_SOME_BAD\n";
pr "TOTAL_TEST_DONE\n";
"#;
    let Some((out, _code)) = run_parse(driver) else {
        eprintln!("{SKIP}");
        return;
    };
    assert!(
        out.contains("TOTAL_NONE_OK") && !out.contains("TOTAL_SOME_BAD"),
        "Lib.total did not return NONE on a raising arg — pervasive Interrupt \
         likely unbound again (see build_kernel_checkpoint.sml).\n{}",
        tail(&out, 40)
    );
}
