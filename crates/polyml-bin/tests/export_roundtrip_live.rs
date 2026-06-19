//! End-to-end "bootstrap loop closing" test:
//!
//! 1. Run our `poly` binary on bootstrap64.txt, piping a tiny SML
//!    driver that loads the basis and calls `PolyML.export`.
//! 2. Confirm a pexport file lands on disk.
//! 3. Re-load that pexport file through our loader (`poly load`).
//! 4. Re-execute it (`poly run`) and confirm the root closure
//!    starts dispatching bytecode.
//!
//! Together this verifies that the writer we just landed in
//! `polyml_runtime::export` produces files our reader+loader+
//! interpreter all accept. If any of those four pieces regresses,
//! this test fails.

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

fn vendor_polyml_dir() -> Option<PathBuf> {
    let p = workspace_root().join("vendor/polyml");
    p.exists().then_some(p)
}

/// Run `poly run <image>` with `stdin_data` on stdin, in working
/// directory `cwd`. Returns combined output and exit code.
fn run_poly(
    image: &std::path::Path,
    stdin_data: &str,
    cwd: &std::path::Path,
    max_steps: u64,
) -> std::io::Result<(String, i32)> {
    let mut child = Command::new(poly_bin())
        .current_dir(cwd)
        .arg("run")
        .arg("--max-steps")
        .arg(max_steps.to_string())
        .arg(image)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .env("POLYML_GC_THRESHOLD", "99") // minimise GC overhead
        .env("POLYML_GC_QUIET", "1")
        .spawn()?;
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(stdin_data.as_bytes())?;
    drop(child.stdin.take());
    let out = child.wait_with_output()?;
    let combined = format!(
        "{}\n---STDERR---\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    Ok((combined, out.status.code().unwrap_or(-1)))
}

#[test]
#[ignore = "slow: loads full basis library (~few minutes); run with `cargo test -- --ignored`"]
fn live_export_roundtrip_through_basis() {
    let Some(image) = bootstrap_image() else {
        eprintln!("SKIP: bootstrap image not present");
        return;
    };
    let Some(vendor) = vendor_polyml_dir() else {
        eprintln!("SKIP: vendor/polyml directory not present");
        return;
    };

    // Use a per-test output path under /tmp so concurrent runs don't collide.
    let pexport_path =
        std::env::temp_dir().join(format!("polyml-rs-live-export-{}", std::process::id()));
    // Don't carry over a stale file from a prior run.
    let _ = std::fs::remove_file(&pexport_path);
    let pexport_str = pexport_path.to_string_lossy().to_string();

    // SML driver: load the basis, then export a trivial root.
    let sml = format!(
        "val () = Bootstrap.use \"basis/build.sml\";\n\
         val () = PolyML.export(\"{}\", fn () => ());\n",
        pexport_str.replace('"', "\\\""),
    );

    let (out, code) =
        run_poly(&image, &sml, &vendor, 5_000_000_000).expect("first run (basis+export)");
    assert_eq!(code, 0, "first run did not exit clean. output:\n{out}");
    assert!(
        out.contains("Tagged(0)"),
        "first run did not finish with Tagged(0) result. output:\n{out}"
    );

    let meta = std::fs::metadata(&pexport_path).unwrap_or_else(|e| {
        panic!(
            "PolyML.export did not produce {}: {e}",
            pexport_path.display()
        )
    });
    assert!(
        meta.len() > 1000,
        "exported file is suspiciously tiny ({} bytes)",
        meta.len()
    );

    // Re-run through `poly run` on the exported file. We expect at
    // least one bytecode step before halting (the trivial root
    // function returns immediately, so a few steps is fine).
    let (out2, _code2) =
        run_poly(&pexport_path, "", &vendor, 1_000_000).expect("second run (re-loaded export)");
    assert!(
        out2.contains("Loaded ") && out2.contains(" bytecode step(s)"),
        "re-loaded image didn't enter the interpreter. output:\n{out2}"
    );

    let _ = std::fs::remove_file(&pexport_path);
}

/// Run `poly run <image>` with `stdin_data`, a low GC threshold (so the
/// Cheney collector actually fires), and `POLYML_GC_AUDIT=1`. Returns the
/// combined output and exit code. The audit prints a `GC AUDIT:` line on
/// stderr if it finds residual from-space pointers after a collect, so the
/// caller can assert that line is absent.
fn run_poly_gc_audited(
    image: &std::path::Path,
    stdin_data: &str,
    cwd: &std::path::Path,
    extra_args: &[&str],
    max_steps: u64,
) -> std::io::Result<(String, i32)> {
    let mut cmd = Command::new(poly_bin());
    cmd.current_dir(cwd)
        .arg("run")
        .arg("--max-steps")
        .arg(max_steps.to_string())
        .arg(image);
    for a in extra_args {
        cmd.arg(a);
    }
    let mut child = cmd
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        // Force the GC to fire repeatedly so the audit actually has collects
        // to inspect (the default 80% threshold + 1.6 GB heap means the basis
        // load triggers very few cycles; 8% triggers ~8).
        .env("POLYML_GC_THRESHOLD", "8")
        .env("POLYML_GC_AUDIT", "1")
        .spawn()?;
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(stdin_data.as_bytes())?;
    drop(child.stdin.take());
    let out = child.wait_with_output()?;
    let combined = format!(
        "{}\n---STDERR---\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    Ok((combined, out.status.code().unwrap_or(-1)))
}

/// GC-audit smoke fence on a real workload.
///
/// Loads the full basis (`Bootstrap.use "basis/build.sml"`) — ~1.8 B steps,
/// which fires ~8 Cheney collects under `POLYML_GC_THRESHOLD=8` — with
/// `POLYML_GC_AUDIT=1`. The audit checks, after EACH collect, that no
/// from-space pointer survives across the interpreter's tracked state, and
/// emits a `GC AUDIT:` line on stderr if it finds one. This test asserts:
///
///   1. the run exits clean with `Tagged(0)`, and
///   2. NO `GC AUDIT:` residual line was printed.
///
/// This pins the GC-correctness invariant on the heaviest GC-firing workload
/// that is cheap enough for an `#[ignore]` integration test, so a future GC
/// or interpreter change that re-introduces a residual-from-space-pointer bug
/// (the heap-corruption class) is caught here.
///
/// NOTE on scope: the audit scans only the LIVE stack region `[sp, len)` (the
/// same root set the collector forwards), so it cannot catch a stale
/// *below-sp* dangling pointer — that distinct latent class is documented in
/// `examples/gc_tiny_heap_stress.rs` and is not reachable through any `poly
/// run` invocation (the CLI never builds a small enough alloc-space Box). This
/// fence covers the tracked-state residual class, which is the one the audit
/// was built to detect.
#[test]
#[ignore = "slow: loads full basis library (~few minutes) under GC audit; run with `cargo test -- --ignored`"]
fn gc_audit_smoke_basis_load() {
    let Some(image) = bootstrap_image() else {
        eprintln!("SKIP: bootstrap image not present");
        return;
    };
    let Some(vendor) = vendor_polyml_dir() else {
        eprintln!("SKIP: vendor/polyml directory not present");
        return;
    };

    let sml = "val () = Bootstrap.use \"basis/build.sml\";\n";
    let (out, code) = run_poly_gc_audited(&image, sml, &vendor, &["--", "-I", "."], 5_000_000_000)
        .expect("basis load under GC audit");

    assert_eq!(
        code, 0,
        "basis load under GC audit did not exit clean. output:\n{out}"
    );
    assert!(
        out.contains("Tagged(0)"),
        "basis load did not finish with Tagged(0). output:\n{out}"
    );
    assert!(
        !out.contains("GC AUDIT:"),
        "GC audit reported residual from-space pointers after a collect — \
         heap-corruption regression. output:\n{out}"
    );
    // Sanity: confirm the collector actually fired (otherwise the audit had
    // nothing to inspect and the test is vacuous).
    assert!(
        out.contains("GC: "),
        "expected at least one GC cycle at POLYML_GC_THRESHOLD=8 — the audit \
         smoke is vacuous without a collect. output:\n{out}"
    );
}
