//! The PolyML basis loads + runs under ARBITRARY-PRECISION int on our interpreter.
//!
//! `--intIsIntInf` flips `Bootstrap.intIsArbitraryPrecision`, so `basis/build.sml`
//! loads `IntAsLargeInt.sml` and the whole basis compiles with default `int` =
//! arbitrary precision (matching upstream PolyML's default). This is the keystone
//! the Isabelle port (#69) needs — Isabelle requires arbitrary-precision int
//! (`time.ML`, etc.).
//!
//! Getting here cleared a chain of arbitrary-int-only bugs that our FixedInt-only
//! history never exercised: stubbed Real-math RTS (`toArbitrary o realFloor` SEGV),
//! `PolyFloatArbitraryPrecision`/`fromLargeInt`, negative arithmetic shifts,
//! `PolyGetLowOrderAsLargeWord` sign, and finally the keystone — `EXTINSTR_REAL_TO_FLOAT`
//! not consuming its rounding-mode operand byte (a 1-byte PC desync, since the
//! operand value 5 == `INSTR_STORE_ML_WORD`, that only surfaced because
//! `Real32.fromLargeInt = Real32.fromReal o Real.fromLargeInt` puts `realToFloat`
//! right after a `G_TO_R` fast-call on the arbitrary-precision branch).
//!
//! `#[ignore]` (slow ~90s; needs vendor/polyml):
//! ```sh
//! cargo test --release -p polyml-bin --test intflip_basis -- --ignored --nocapture
//! ```

mod common;
use common::*;

use std::io::Write;
use std::process::{Command, Stdio};

#[test]
#[ignore = "slow ~90s: full basis compile under --intIsIntInf; needs vendor/polyml"]
fn basis_loads_under_arbitrary_precision_int() {
    let Some(vendor) = vendor_polyml_dir() else {
        eprintln!("SKIP: vendor/polyml missing");
        return;
    };
    let image = vendor.join("bootstrap/bootstrap64.txt");
    if !image.exists() {
        eprintln!("SKIP: bootstrap64.txt missing");
        return;
    }
    // Drive the bare Stage-0 compiler: load the whole basis, print a marker.
    // `-- -I . --intIsIntInf` populates CommandLine.arguments(): -I . lets the
    // bootstrap find basis sources, and --intIsIntInf flips the default int to
    // arbitrary precision before basis/build.sml runs.
    let mut child = Command::new(poly_bin())
        .current_dir(&vendor)
        .arg("run")
        .arg("--max-steps")
        .arg("50000000000")
        .arg(&image)
        .arg("--")
        .arg("-I")
        .arg(".")
        .arg("--intIsIntInf")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .env("POLYML_GC_THRESHOLD", "99")
        .env("POLYML_GC_QUIET", "1")
        .spawn()
        .expect("spawn poly");
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(b"val () = Bootstrap.use \"basis/build.sml\";\nprint \"ARBINT_BASIS_OK\\n\";\n")
        .unwrap();
    drop(child.stdin.take());
    let out = child.wait_with_output().expect("wait");
    let combined = format!(
        "{}\n---STDERR---\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );

    // The whole basis compiled under arbitrary int and our marker ran.
    assert!(
        combined.contains("ARBINT_BASIS_OK"),
        "basis did not finish loading under --intIsIntInf (wall regressed?).\n{}",
        tail(&combined, 40)
    );
    // Clean VM return, no SEGV / compile error / exn-unwind halt.
    assert_eq!(out.status.code(), Some(0), "non-zero exit under --intIsIntInf");
    assert!(
        combined.contains("Result: Tagged(0)"),
        "no clean Tagged(0) return.\n{}",
        tail(&combined, 20)
    );
    // The last basis file must have been reached (not stuck mid-way at Real.sml).
    assert!(
        combined.contains("Use: basis/TopLevelPolyML.sml"),
        "basis load did not reach the final file.\n{}",
        tail(&combined, 20)
    );
}
