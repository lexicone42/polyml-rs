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
    child.stdin.as_mut().unwrap().write_all(stdin_data.as_bytes())?;
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
    let pexport_path = std::env::temp_dir()
        .join(format!("polyml-rs-live-export-{}", std::process::id()));
    // Don't carry over a stale file from a prior run.
    let _ = std::fs::remove_file(&pexport_path);
    let pexport_str = pexport_path.to_string_lossy().to_string();

    // SML driver: load the basis, then export a trivial root.
    let sml = format!(
        "val () = Bootstrap.use \"basis/build.sml\";\n\
         val () = PolyML.export(\"{}\", fn () => ());\n",
        pexport_str.replace('"', "\\\""),
    );

    let (out, code) = run_poly(&image, &sml, &vendor, 5_000_000_000)
        .expect("first run (basis+export)");
    assert_eq!(
        code, 0,
        "first run did not exit clean. output:\n{out}"
    );
    assert!(
        out.contains("Tagged(0)"),
        "first run did not finish with Tagged(0) result. output:\n{out}"
    );

    let meta = std::fs::metadata(&pexport_path)
        .unwrap_or_else(|e| panic!("PolyML.export did not produce {}: {e}", pexport_path.display()));
    assert!(meta.len() > 1000, "exported file is suspiciously tiny ({} bytes)", meta.len());

    // Re-run through `poly run` on the exported file. We expect at
    // least one bytecode step before halting (the trivial root
    // function returns immediately, so a few steps is fine).
    let (out2, _code2) = run_poly(&pexport_path, "", &vendor, 1_000_000)
        .expect("second run (re-loaded export)");
    assert!(
        out2.contains("Loaded ") && out2.contains(" bytecode step(s)"),
        "re-loaded image didn't enter the interpreter. output:\n{out2}"
    );

    let _ = std::fs::remove_file(&pexport_path);
}
