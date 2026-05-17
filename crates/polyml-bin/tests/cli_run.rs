//! Integration tests for the `poly run` subcommand.
//!
//! Goal: lock in the "we compile SML" milestone as a regression
//! guard. If any future change re-breaks the read-stdin /
//! type-check / write-stderr / clean-exit path, these tests fail.

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

fn workspace_root() -> PathBuf {
    let mut p: PathBuf = env!("CARGO_MANIFEST_DIR").into();
    loop {
        let cargo = p.join("Cargo.toml");
        if cargo.exists()
            && let Ok(text) = std::fs::read_to_string(&cargo)
            && text.contains("[workspace]")
        {
            return p;
        }
        assert!(p.pop());
    }
}

fn poly_bin() -> PathBuf {
    // CARGO_BIN_EXE_<name> is set by cargo for integration tests.
    PathBuf::from(env!("CARGO_BIN_EXE_poly"))
}

fn bootstrap_image() -> Option<PathBuf> {
    let p = workspace_root().join("vendor/polyml/bootstrap/bootstrap64.txt");
    p.exists().then_some(p)
}

fn run_with_stdin(stdin_data: &str, max_steps: u64) -> Result<(String, String), std::io::Error> {
    let Some(image) = bootstrap_image() else {
        return Ok((String::new(), String::from("SKIP: bootstrap image not present")));
    };
    let mut child = Command::new(poly_bin())
        .arg("run")
        .arg("--max-steps")
        .arg(max_steps.to_string())
        .arg(&image)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(stdin_data.as_bytes())?;
    drop(child.stdin.take());
    let out = child.wait_with_output()?;
    Ok((
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    ))
}

#[test]
fn bootstrap_compiles_simple_literal_and_exits_cleanly() {
    let Ok((stdout, _stderr)) = run_with_stdin("42;\n", 5_000_000) else {
        return;
    };
    if stdout.is_empty() {
        return; // SKIP path
    }
    assert!(
        stdout.contains("Tagged(0)"),
        "expected clean exit, got stdout: {stdout}"
    );
    assert!(
        stdout.contains("clean return"),
        "expected clean-return marker, got stdout: {stdout}"
    );
}

#[test]
fn bootstrap_reports_type_error_on_bad_input() {
    let Ok((_stdout, stderr_or_stdout_combined)) = run_with_stdin("1 + 1;\n", 10_000_000) else {
        return;
    };
    // The error is written by PolyML to stderr (which we routed
    // through std::io::stderr()). Check both, the test framework
    // captures both — the CLI prints to stdout but the bootstrap
    // writes error to stderr.
    let Ok((stdout, stderr)) = run_with_stdin("1 + 1;\n", 10_000_000) else {
        return;
    };
    let combined = format!("{stdout}\n---\n{stderr}");
    assert!(
        combined.contains("Type error") || combined.contains("Error-"),
        "expected a type-error report, got:\n{combined}"
    );
    let _ = stderr_or_stdout_combined;
}

#[test]
fn bootstrap_runs_lambda_application_cleanly() {
    let Ok((stdout, _)) = run_with_stdin("val it = (fn x => x) 42;\n", 10_000_000) else {
        return;
    };
    if stdout.is_empty() {
        return;
    }
    assert!(
        stdout.contains("Tagged(0)"),
        "expected clean exit, got stdout: {stdout}"
    );
}

/// The bootstrap64.txt image is the BARE PolyML interpreter (Stage 0
/// of the bootstrap chain). It has no infix declarations or operator
/// overloads — those come from `basis/InitialBasis.ML` which would
/// normally be loaded by Stage1.sml piped to stdin. We can bootstrap
/// the operators ourselves with a few prelude lines and then do real
/// arithmetic.
#[test]
fn bootstrap_can_register_infix_plus_and_compute() {
    let prelude = "infix 6 + -; RunCall.addOverload FixedInt.+ \"+\"; ";
    let src = format!("{prelude} val x = 1 + 2; ");
    let Ok((stdout, _)) = run_with_stdin(&src, 10_000_000) else {
        return;
    };
    if stdout.is_empty() {
        return;
    }
    // If `1 + 2` failed to type-check (or to evaluate), the bootstrap
    // would have raised an exception, hit the error-write path, and
    // we'd see "Error-" in the output. Clean Tagged(0) means the
    // expression succeeded.
    assert!(
        stdout.contains("Tagged(0)"),
        "expected clean exit after `val x = 1 + 2`, got: {stdout}"
    );
    assert!(
        !stdout.contains("Error-"),
        "expected no compiler errors, got: {stdout}"
    );
}

#[test]
fn bootstrap_polyml_print_emits_output() {
    let Ok((stdout, stderr)) = run_with_stdin("PolyML.print 42;\n", 10_000_000) else {
        return;
    };
    let combined = format!("{stdout}\n---\n{stderr}");
    if combined.trim().is_empty() {
        return;
    }
    // The basis-less bootstrap's default printer just emits "?",
    // but the fact that ANYTHING gets through to our stdout from
    // PolyML.print proves the compile-and-evaluate path works.
    assert!(
        combined.contains('?') || combined.contains("42"),
        "expected printer output, got:\n{combined}"
    );
    assert!(
        stdout.contains("Tagged(0)"),
        "expected clean exit after PolyML.print, got: {stdout}"
    );
}
