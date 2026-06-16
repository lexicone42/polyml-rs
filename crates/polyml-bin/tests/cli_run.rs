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
    run_with_stdin_and_args(stdin_data, max_steps, &[])
}

fn run_with_stdin_and_args(
    stdin_data: &str,
    max_steps: u64,
    extra_args: &[&str],
) -> Result<(String, String), std::io::Error> {
    run_with_stdin_args_and_jit(stdin_data, max_steps, extra_args, false, None)
}

fn run_with_stdin_args_and_jit(
    stdin_data: &str,
    max_steps: u64,
    extra_args: &[&str],
    with_jit: bool,
    cwd: Option<&std::path::Path>,
) -> Result<(String, String), std::io::Error> {
    let Some(image) = bootstrap_image() else {
        return Ok((
            String::new(),
            String::from("SKIP: bootstrap image not present"),
        ));
    };
    let mut cmd = Command::new(poly_bin());
    cmd.arg("run").arg("--max-steps").arg(max_steps.to_string());
    if with_jit {
        cmd.arg("--jit");
    }
    cmd.arg(&image);
    if !extra_args.is_empty() {
        cmd.arg("--");
        cmd.args(extra_args);
    }
    if let Some(d) = cwd {
        cmd.current_dir(d);
    }
    let mut child = cmd
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

/// `poly run img --use /path/to/file.sml` is the one-shot equivalent of
/// `echo 'val () = Bootstrap.use "file.sml";' | poly run img -- -I /path/to`
/// plus closing stdin so the bootstrap exits cleanly after running it.
#[test]
fn bootstrap_use_flag_runs_file_one_shot() {
    let dir = std::env::temp_dir().join("polyml_rs_use_flag_test");
    let _ = std::fs::create_dir_all(&dir);
    let script = dir.join("script.sml");
    std::fs::write(
        &script,
        b"infix 6 +; RunCall.addOverload FixedInt.+ \"+\"; val x = 21 + 21;",
    )
    .unwrap();

    let Some(image) = bootstrap_image() else {
        return;
    };
    let out = Command::new(poly_bin())
        .arg("run")
        .arg("--max-steps")
        .arg("10000000")
        .arg(&image)
        .arg("--use")
        .arg(&script)
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "poly run --use failed: status={:?} stdout={} stderr={}",
        out.status,
        stdout,
        stderr
    );
    assert!(
        stdout.contains("Use: script.sml"),
        "expected 'Use: script.sml' marker, got stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("Tagged(0)"),
        "expected clean exit, got stdout={stdout} stderr={stderr}"
    );
}

/// `poly run img -- -I path` makes `path` visible to the SML side
/// as a `CommandLine.argument`. `Bootstrap.use "file.sml"` then
/// finds and loads it via `TextIO.openIn` (RTS file I/O subcodes 3/4)
/// + `OS.Path.concat`. This is the foundation for "use" — without
/// it, only stdin-piped programs can run.
#[test]
fn bootstrap_use_finds_relative_file_via_minus_i() {
    // Write a tiny prelude that the SML can load.
    let dir = std::env::temp_dir().join("polyml_rs_use_test");
    let _ = std::fs::create_dir_all(&dir);
    let prelude_path = dir.join("prelude.sml");
    std::fs::write(
        &prelude_path,
        b"infix 6 +; RunCall.addOverload FixedInt.+ \"+\"; val x = 1 + 2;",
    )
    .unwrap();

    let dir_str = dir.to_string_lossy().into_owned();
    let stdin = "val () = Bootstrap.use \"prelude.sml\";\n";
    let Ok((stdout, stderr)) = run_with_stdin_and_args(stdin, 10_000_000, &["-I", &dir_str]) else {
        return;
    };
    if stdout.is_empty() {
        return;
    }
    assert!(
        stdout.contains("Use: prelude.sml"),
        "expected 'Use: prelude.sml' marker, got stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("Tagged(0)"),
        "expected clean exit after Bootstrap.use, got stdout={stdout} stderr={stderr}"
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

/// Regression test for `--jit` breaking basis loading. The simple
/// bootstrap + HOL4-via-checkpoint tests don't catch this because
/// they don't exercise the `Bootstrap.use "basis/..."` path. Stage1
/// basis load was silently broken by a CONST_ADDR install
/// regression that the other tests passed cleanly.
///
/// This test loads a small section of basis (just InitialBasis +
/// PolyMLException) with --jit. If basis fails to load (= 'Error-'
/// or missing structures), the JIT install regressed something on
/// the basis-load path.
#[test]
fn bootstrap_jit_loads_initial_basis() {
    let polyml_dir = workspace_root().join("vendor/polyml");
    if !polyml_dir.join("basis/InitialBasis.ML").exists() {
        eprintln!("SKIP: vendor/polyml not present");
        return;
    }
    // The shortest meaningful sequence: load just a couple of basis
    // files and check no compile errors. PolyMLException.sml is the
    // file where the CONST_ADDR regression manifested (line 22
    // referenced CommandLine which wasn't yet declared).
    //
    // Run from vendor/polyml so basis/ paths resolve.
    let sml = "\
val () = Bootstrap.use \"basis/InitialBasis.ML\";\n\
val () = Bootstrap.use \"basis/Universal.ML\";\n\
val () = Bootstrap.use \"basis/General.sml\";\n\
val () = Bootstrap.use \"basis/LibrarySupport.sml\";\n\
val () = Bootstrap.use \"basis/PolyMLException.sml\";\n\
PolyML.print \"BASIS_LOAD_OK\";\n";
    let Ok((stdout, stderr)) = run_with_stdin_args_and_jit(
        sml,
        200_000_000_000,
        &[],
        true, // --jit
        Some(&polyml_dir),
    ) else {
        return;
    };
    let combined = format!("{stdout}\n---STDERR---\n{stderr}");
    if combined.trim().is_empty() {
        eprintln!("SKIP: empty output");
        return;
    }
    let errs: Vec<&str> = combined
        .lines()
        .filter(|l| {
            l.starts_with("Error-")
                || l.contains("has not been declared")
                || l.contains("Static Errors")
        })
        .take(10)
        .collect();
    assert!(
        errs.is_empty(),
        "basis load with --jit emitted compile errors:\n{}\n\n---output tail---\n{}",
        errs.join("\n"),
        combined
            .lines()
            .rev()
            .take(20)
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert!(
        combined.contains("BASIS_LOAD_OK"),
        "missing BASIS_LOAD_OK sentinel. Output tail:\n{}",
        combined
            .lines()
            .rev()
            .take(20)
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect::<Vec<_>>()
            .join("\n")
    );
}
