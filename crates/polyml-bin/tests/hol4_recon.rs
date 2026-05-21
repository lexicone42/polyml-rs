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

/// Path to the basis-loaded checkpoint built by:
///
/// ```sh
/// cd vendor/polyml
/// echo 'val () = Bootstrap.use "basis/build.sml";
///       val () = PolyML.export("/tmp/basis_loaded", PolyML.rootFunction);' \
///   | ../../target/release/poly run --max-steps 10000000000 \
///       bootstrap/bootstrap64.txt
/// ```
///
/// Re-using this skips the 3-5 min basis-load on every test. The
/// helper functions below check for it and skip the test cleanly
/// if it's absent.
fn checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/basis_loaded");
    p.exists().then_some(p)
}

fn run_through_checkpoint(sml: &str, max_steps: u64) -> Option<(String, i32)> {
    let ckpt = checkpoint_path()?;
    let mut child = Command::new(poly_bin())
        .arg("run")
        .arg("--max-steps")
        .arg(max_steps.to_string())
        .arg(&ckpt)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .env("POLYML_GC_QUIET", "1")
        .spawn()
        .ok()?;
    child.stdin.as_mut()?.write_all(sml.as_bytes()).ok()?;
    drop(child.stdin.take());
    let out = child.wait_with_output().ok()?;
    let combined = format!(
        "{}\n---STDERR---\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    Some((combined, out.status.code().unwrap_or(-1)))
}

#[test]
fn recon_via_checkpoint_compiles_simple_buffer() {
    let Some(_) = checkpoint_path() else {
        eprintln!("SKIP: /tmp/basis_loaded not present (build via README)");
        return;
    };
    if hol4_dir().is_none() {
        eprintln!("SKIP: vendor/hol4 not present");
        return;
    }
    let hol = hol4_dir().unwrap();
    let driver = format!(
        "PolyML.use \"{path}/tools/util/SimpleBuffer.sig\";\n\
         PolyML.use \"{path}/tools/util/SimpleBuffer.sml\";\n\
         print \"HOL_OK\\n\";\n",
        path = hol.display(),
    );
    let Some((out, code)) = run_through_checkpoint(&driver, 1_000_000_000) else {
        panic!("subprocess failure");
    };
    assert!(out.contains("HOL_OK"), "no HOL_OK. Output:\n{out}");
    assert_eq!(code, 0, "non-zero exit. Output:\n{out}");
}

#[test]
fn recon_via_checkpoint_compiles_portable() {
    let Some(_) = checkpoint_path() else {
        eprintln!("SKIP: /tmp/basis_loaded not present");
        return;
    };
    if hol4_dir().is_none() {
        eprintln!("SKIP: vendor/hol4 not present");
        return;
    }
    let hol = hol4_dir().unwrap();
    let pm = format!("{}/src/portableML", hol.display());
    let driver = format!(
        "fun U f = PolyML.use (\"{pm}/\" ^ f);\n\
         U \"quotation_dtype.sml\";\n\
         U \"poly/PrettyImpl.sml\";\n\
         U \"Uref.sig\"; U \"Uref.sml\";\n\
         U \"HOLPP.sig\"; U \"HOLPP.sml\";\n\
         U \"OldPP.sig\"; U \"OldPP.sml\";\n\
         U \"poly/Arbnumcore.sig\"; U \"poly/Arbnumcore.sml\";\n\
         U \"Arbnum.sig\"; U \"Arbnum.sml\";\n\
         U \"Portable.sig\"; U \"Portable.sml\";\n\
         print \"HOL_PORTABLE_OK\\n\";\n",
    );
    let Some((out, _)) = run_through_checkpoint(&driver, 5_000_000_000) else {
        panic!("subprocess failure");
    };
    assert!(out.contains("HOL_PORTABLE_OK"), "Output:\n{out}");
}

#[test]
fn recon_via_checkpoint_compiles_prekernel_lib() {
    let Some(_) = checkpoint_path() else {
        eprintln!("SKIP: /tmp/basis_loaded not present");
        return;
    };
    if hol4_dir().is_none() {
        eprintln!("SKIP: vendor/hol4 not present");
        return;
    }
    let hol = hol4_dir().unwrap();
    let pm = format!("{}/src/portableML", hol.display());
    let pk = format!("{}/src/prekernel", hol.display());
    let driver = format!(
        "fun PMu f = PolyML.use (\"{pm}/\" ^ f);\n\
         fun PKu f = PolyML.use (\"{pk}/\" ^ f);\n\
         PMu \"quotation_dtype.sml\";\n\
         PMu \"poly/PrettyImpl.sml\";\n\
         PMu \"Uref.sig\"; PMu \"Uref.sml\";\n\
         PMu \"HOLPP.sig\"; PMu \"HOLPP.sml\";\n\
         PMu \"OldPP.sig\"; PMu \"OldPP.sml\";\n\
         PMu \"poly/Arbnumcore.sig\"; PMu \"poly/Arbnumcore.sml\";\n\
         PMu \"Arbnum.sig\"; PMu \"Arbnum.sml\";\n\
         PMu \"Portable.sig\"; PMu \"Portable.sml\";\n\
         PMu \"Redblackmap.sig\"; PMu \"Redblackmap.sml\";\n\
         PKu \"Feedback_dtype.sml\";\n\
         PKu \"Feedback.sig\"; PKu \"Feedback.sml\";\n\
         PKu \"Lib.sig\"; PKu \"Lib.sml\";\n\
         print \"HOL_LIB_OK\\n\";\n",
    );
    let Some((out, _)) = run_through_checkpoint(&driver, 10_000_000_000) else {
        panic!("subprocess failure");
    };
    assert!(out.contains("HOL_LIB_OK"), "Output (tail):\n{}",
        out.lines().rev().take(20).collect::<Vec<_>>().into_iter().rev()
            .collect::<Vec<_>>().join("\n"));
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
