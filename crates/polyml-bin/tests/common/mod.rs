//! Shared helpers for the SML / HOL4 reconstruction integration tests.
//!
//! `hol4_recon.rs` predates this module and keeps its own inline copies of
//! the path/run helpers; new test files should `mod common;` and use these.
//! Included via `mod common;` (a subdir module, so Cargo does not compile it
//! as its own test binary).
#![allow(dead_code)]

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

/// Walk up from this crate's manifest dir to the workspace root.
pub fn workspace_root() -> PathBuf {
    let mut p: PathBuf = env!("CARGO_MANIFEST_DIR").into();
    loop {
        let cargo = p.join("Cargo.toml");
        if cargo.exists()
            && std::fs::read_to_string(&cargo)
                .map(|t| t.contains("[workspace]"))
                .unwrap_or(false)
        {
            return p;
        }
        assert!(p.pop(), "could not find workspace root");
    }
}

pub fn poly_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_poly"))
}

pub fn vendor_polyml_dir() -> Option<PathBuf> {
    let p = workspace_root().join("vendor/polyml");
    p.exists().then_some(p)
}

pub fn hol4_dir() -> Option<PathBuf> {
    let p = workspace_root().join("vendor/hol4");
    p.exists().then_some(p)
}

/// Warm basis+kernel checkpoint built by `tools/build-hol4-checkpoints.sh kernel`.
pub fn kernel_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_kernel");
    p.exists().then_some(p)
}

/// Warm basis+kernel+Theory+parser checkpoint built by
/// `tools/build-hol4-checkpoints.sh parse`.
pub fn parse_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_parse");
    p.exists().then_some(p)
}

/// Warm parser+bool-theory checkpoint built by
/// `tools/build-hol4-checkpoints.sh bool`.
pub fn bool_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_bool");
    p.exists().then_some(p)
}

/// Warm bool+tactic-layer checkpoint built by
/// `tools/build-hol4-checkpoints.sh tactic`.
pub fn tactic_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_tactic");
    p.exists().then_some(p)
}

/// Warm tactic+REWRITE_TAC checkpoint built by
/// `tools/build-hol4-checkpoints.sh rewrite`.
pub fn rewrite_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_rewrite");
    p.exists().then_some(p)
}

/// Warm checkpoint with markerTheory (`tools/build-hol4-checkpoints.sh marker`).
pub fn marker_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_marker");
    p.exists().then_some(p)
}

/// Warm checkpoint with combinTheory (`tools/build-hol4-checkpoints.sh combin`).
pub fn combin_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_combin");
    p.exists().then_some(p)
}

/// Warm checkpoint with simpLib / SIMP_TAC (`tools/build-hol4-checkpoints.sh simp`).
pub fn simp_checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_simp");
    p.exists().then_some(p)
}

/// A file under `crates/polyml-bin/tests/hol4_support/`.
pub fn support_file(name: &str) -> PathBuf {
    workspace_root()
        .join("crates/polyml-bin/tests/hol4_support")
        .join(name)
}

/// Pipe `sml` into `poly run <image>` (cwd = vendor/polyml), with extra env.
/// Returns (combined stdout+stderr, exit code), or None if poly can't spawn.
pub fn run_image_env(
    image: &std::path::Path,
    sml: &str,
    max_steps: u64,
    envs: &[(&str, &str)],
) -> Option<(String, i32)> {
    let vendor = vendor_polyml_dir()?;
    let mut cmd = Command::new(poly_bin());
    cmd.current_dir(&vendor)
        .arg("run")
        .arg("--max-steps")
        .arg(max_steps.to_string())
        .arg(image)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .env("POLYML_GC_THRESHOLD", "99")
        .env("POLYML_GC_QUIET", "1");
    for (k, v) in envs {
        cmd.env(k, v);
    }
    let mut child = cmd.spawn().ok()?;
    child.stdin.as_mut().unwrap().write_all(sml.as_bytes()).ok()?;
    drop(child.stdin.take());
    let out = child.wait_with_output().ok()?;
    let combined = format!(
        "{}\n---STDERR---\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    Some((combined, out.status.code().unwrap_or(-1)))
}

/// Load the captured Theory-subsystem reconstruction
/// (`hol4_support/theory_subsystem.sml`) on the warm kernel checkpoint, then
/// run `extra_sml`. Returns None if `/tmp/hol4_kernel` or `vendor/hol4` are
/// absent (caller should skip).
pub fn run_theory_subsystem(extra_sml: &str, max_steps: u64) -> Option<(String, i32)> {
    let kernel = kernel_checkpoint_path()?;
    let hol = hol4_dir()?;
    // Pipe the loader's source into the REPL rather than `PolyML.use`-ing it:
    // when the whole file is one `PolyML.use` unit, an uncaught exception
    // (e.g. a "Cannot open") propagates through the use machinery and trips an
    // interpreter exception-unwinding halt; piped, each top-level declaration
    // is handled independently (matches hol4_recon.rs's working tests).
    let loader_src = std::fs::read_to_string(support_file("theory_subsystem.sml")).ok()?;
    let driver = format!("{loader_src}\n{extra_sml}");
    run_image_env(
        &kernel,
        &driver,
        max_steps,
        &[("HOL4_DIR", hol.to_str().unwrap())],
    )
}

// ----------------------------------------------------------------------------
// Compile-output analysis (mirrors tools/sml-exp.sh's grouping on the Rust side)
// ----------------------------------------------------------------------------

/// Parse a `LOADED_OK n/m` marker emitted by the fixpoint loader.
pub fn parse_loaded(out: &str) -> Option<(usize, usize)> {
    for line in out.lines() {
        if let Some(idx) = line.find("LOADED_OK") {
            let rest = &line[idx + "LOADED_OK".len()..];
            let tok = rest.split_whitespace().next()?; // "50/54"
            let (a, b) = tok.split_once('/')?;
            return Some((a.trim().parse().ok()?, b.trim().parse().ok()?));
        }
    }
    None
}

/// Extract `(X)` from a line like `... (Foo) has not been declared`.
fn paren_ident(line: &str) -> Option<&str> {
    let start = line.find('(')? + 1;
    let end = line[start..].find(')')? + start;
    Some(&line[start..end])
}

fn count_distinct<'a>(items: impl Iterator<Item = &'a str>) -> Vec<(String, usize)> {
    let mut map: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    for it in items {
        *map.entry(it.to_string()).or_insert(0) += 1;
    }
    let mut v: Vec<_> = map.into_iter().collect();
    v.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    v
}

/// A grouped, human-readable summary of compile diagnostics in `out`, suitable
/// for an assertion-failure message. Empty-ish when there are no errors.
pub fn classify_errors(out: &str) -> String {
    let mut s = String::new();

    if let Some((a, b)) = parse_loaded(out) {
        s.push_str(&format!("modules: {a}/{b} loaded\n"));
        for line in out.lines() {
            if let Some(i) = line.find("STUCKERR ") {
                let f = line[i + "STUCKERR ".len()..].trim();
                let base = f.rsplit('/').next().unwrap_or(f);
                s.push_str(&format!("  stuck: {base}\n"));
            }
        }
    }

    let undeclared_structs = count_distinct(
        out.lines()
            .filter(|l| l.contains("Structure (") && l.contains("has not been declared"))
            .filter_map(paren_ident),
    );
    if !undeclared_structs.is_empty() {
        s.push_str("undeclared structures:\n");
        for (name, n) in undeclared_structs.iter().take(20) {
            s.push_str(&format!("  {n:>3} {name}\n"));
        }
    }

    let undeclared_vals = count_distinct(
        out.lines()
            .filter(|l| {
                (l.contains("Value or constructor (") || l.contains("Constructor ("))
                    && l.contains("has not been declared")
            })
            .filter_map(paren_ident),
    );
    if !undeclared_vals.is_empty() {
        s.push_str("undeclared values/constructors:\n");
        for (name, n) in undeclared_vals.iter().take(20) {
            s.push_str(&format!("  {n:>3} {name}\n"));
        }
    }

    let type_errs = out.lines().filter(|l| l.contains("error: Type error")).count();
    if type_errs > 0 {
        s.push_str(&format!("type errors: {type_errs}\n"));
    }
    let sig_mismatch = out
        .lines()
        .filter(|l| l.contains("Structure does not match signature"))
        .count();
    if sig_mismatch > 0 {
        s.push_str(&format!("signature mismatches: {sig_mismatch}\n"));
    }
    let static_errs = out.lines().filter(|l| l.contains("Static Errors")).count();
    if static_errs > 0 {
        s.push_str(&format!("Static Errors lines: {static_errs}\n"));
    }

    if s.is_empty() {
        s.push_str("(no recognized compile diagnostics)\n");
    }
    s
}

/// Last `n` lines of `out`, for compact assertion messages.
pub fn tail(out: &str, n: usize) -> String {
    let lines: Vec<&str> = out.lines().collect();
    let start = lines.len().saturating_sub(n);
    lines[start..].join("\n")
}
