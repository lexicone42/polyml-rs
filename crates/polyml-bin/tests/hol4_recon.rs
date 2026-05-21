//! HOL4 reconnaissance: try to compile pieces of the HOL4 source
//! tree through our runtime, growing the list as more compile.
//!
//! Each test case is a single HOL4 module (or a small group). The
//! test loads the basis, then `PolyML.use`s the file(s), then
//! prints a sentinel. We assert the sentinel appears in output.
//!
//! All tests are `#[ignore]` because they each take ~3 minutes
//! (most of that is basis load). Run with:
//!
//! ```sh
//! cargo test -p polyml-bin --test hol4_recon -- --ignored --nocapture
//! ```

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

fn hol4_dir() -> Option<PathBuf> {
    let p = workspace_root().join("vendor/hol4");
    p.exists().then_some(p)
}

/// Run our `poly run` on bootstrap64.txt, piping `sml_driver` on
/// stdin from `vendor/polyml/` as cwd. Returns (combined output,
/// exit code).
fn run_with_driver(
    sml_driver: &str,
    max_steps: u64,
) -> std::io::Result<(String, i32)> {
    let image = bootstrap_image().expect("bootstrap image");
    let vendor = vendor_polyml_dir().expect("vendor polyml");
    let mut child = Command::new(poly_bin())
        .current_dir(&vendor)
        .arg("run")
        .arg("--max-steps")
        .arg(max_steps.to_string())
        .arg(&image)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .env("POLYML_GC_THRESHOLD", "99") // minimise GC overhead
        .env("POLYML_GC_QUIET", "1")
        .spawn()?;
    child.stdin.as_mut().unwrap().write_all(sml_driver.as_bytes())?;
    drop(child.stdin.take());
    let out = child.wait_with_output()?;
    let combined = format!(
        "{}\n---STDERR---\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    Ok((combined, out.status.code().unwrap_or(-1)))
}

fn skip_if_missing() -> Option<()> {
    bootstrap_image()?;
    hol4_dir()?;
    Some(())
}

#[test]
#[ignore = "slow: loads HOL4 source through full basis (~3-5 min)"]
fn recon_compiles_simple_buffer() {
    if skip_if_missing().is_none() {
        eprintln!("SKIP: vendor/polyml or vendor/hol4 not present");
        return;
    }
    let hol = hol4_dir().unwrap();
    let driver = format!(
        "val () = Bootstrap.use \"basis/build.sml\";\n\
         val () = PolyML.use \"{path}/tools/util/SimpleBuffer.sig\";\n\
         val () = PolyML.use \"{path}/tools/util/SimpleBuffer.sml\";\n\
         print \"HOL_OK\\n\";\n",
        path = hol.display(),
    );
    let (out, code) = run_with_driver(&driver, 10_000_000_000)
        .expect("run");
    assert_eq!(code, 0, "exit non-zero. Output:\n{out}");
    assert!(
        out.contains("HOL_OK"),
        "did not print HOL_OK. Output:\n{out}"
    );
    assert!(
        !out.contains("Error-"),
        "compiler error during HOL4 compile. Output:\n{out}"
    );
}

#[test]
#[ignore = "slow: loads HOL4 source through full basis (~5-7 min)"]
fn recon_compiles_portable() {
    if skip_if_missing().is_none() {
        eprintln!("SKIP: missing vendor dirs");
        return;
    }
    let hol = hol4_dir().unwrap();
    let driver = format!(
        "val () = Bootstrap.use \"basis/build.sml\";\n\
         val () = PolyML.use \"{path}/src/portableML/Portable.sig\";\n\
         val () = PolyML.use \"{path}/src/portableML/Portable.sml\";\n\
         print \"HOL_OK\\n\";\n",
        path = hol.display(),
    );
    let (out, code) = run_with_driver(&driver, 20_000_000_000)
        .expect("run");
    // Note: this may fail today — that's the point of recon.
    // We capture the output for diagnosis even on failure.
    if code != 0 || !out.contains("HOL_OK") {
        panic!(
            "Portable.sml didn't compile (code={code}).\n\
             First few errors:\n{}",
            out.lines()
                .filter(|l| l.contains("Error-") || l.contains("not been declared")
                    || l.contains("Halted") || l.contains("Result:"))
                .take(10)
                .collect::<Vec<_>>()
                .join("\n")
        );
    }
}
