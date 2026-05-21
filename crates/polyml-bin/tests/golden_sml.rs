//! Golden tests: pair each `tests/golden/*.sml` with a
//! `<same>.expected` file describing the expected substrings (one
//! per line) that must appear in the combined stdout+stderr output.
//!
//! Lines starting with `#` in the expected file are comments.
//! Empty lines are ignored. Each remaining line is a substring that
//! must appear somewhere in the output.
//!
//! To add a new test: drop `foo.sml` and `foo.expected` into
//! `tests/golden/`. Re-run `cargo test -p polyml-bin --test golden_sml`.
//!
//! Goal: as we extend the runtime, every "this kind of SML now works"
//! milestone gets locked in as a tiny SML program here. When a future
//! change regresses it, the test fails with a clear pointer to which
//! feature broke.

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
    PathBuf::from(env!("CARGO_BIN_EXE_poly"))
}

fn bootstrap_image() -> Option<PathBuf> {
    let p = workspace_root().join("vendor/polyml/bootstrap/bootstrap64.txt");
    p.exists().then_some(p)
}

fn run_sml(src: &str, max_steps: u64) -> Option<(String, String, i32)> {
    let image = bootstrap_image()?;
    let mut child = Command::new(poly_bin())
        .arg("run")
        .arg("--max-steps")
        .arg(max_steps.to_string())
        .arg(&image)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .env("POLYML_GC_QUIET", "1")
        .spawn()
        .ok()?;
    child.stdin.as_mut()?.write_all(src.as_bytes()).ok()?;
    drop(child.stdin.take());
    let out = child.wait_with_output().ok()?;
    Some((
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
        out.status.code().unwrap_or(-1),
    ))
}

fn parse_expected(path: &std::path::Path) -> Vec<String> {
    let text = match std::fs::read_to_string(path) {
        Ok(t) => t,
        Err(_) => return Vec::new(),
    };
    text.lines()
        .map(str::trim_end)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(str::to_owned)
        .collect()
}

#[test]
fn run_golden_corpus() {
    let dir = workspace_root().join("crates/polyml-bin/tests/golden");
    if bootstrap_image().is_none() {
        eprintln!("SKIP: bootstrap image not present");
        return;
    }
    let Ok(entries) = std::fs::read_dir(&dir) else {
        panic!("missing golden dir: {}", dir.display());
    };
    let mut sml_files: Vec<PathBuf> = entries
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("sml"))
        .collect();
    sml_files.sort();
    assert!(
        !sml_files.is_empty(),
        "no .sml golden cases found under {}",
        dir.display()
    );

    let mut failures = Vec::new();
    for sml in &sml_files {
        let name = sml.file_name().unwrap().to_string_lossy().to_string();
        let expected_path = sml.with_extension("expected");
        let src = match std::fs::read_to_string(sml) {
            Ok(s) => s,
            Err(e) => {
                failures.push(format!("{name}: cannot read source: {e}"));
                continue;
            }
        };
        let expected = parse_expected(&expected_path);
        if expected.is_empty() {
            failures.push(format!(
                "{name}: missing or empty .expected (need at least one substring)"
            ));
            continue;
        }
        let Some((stdout, stderr, _code)) = run_sml(&src, 100_000_000) else {
            failures.push(format!("{name}: subprocess failure"));
            continue;
        };
        let combined = format!("{stdout}\n---STDERR---\n{stderr}");
        for needle in &expected {
            if !combined.contains(needle) {
                failures.push(format!(
                    "{name}: expected substring not found:\n  needle:   {needle:?}\n  combined:\n{combined}"
                ));
                break;
            }
        }
    }

    if !failures.is_empty() {
        let msg = format!("{} golden test failure(s):\n\n{}", failures.len(), failures.join("\n\n"));
        panic!("{msg}");
    }
}
