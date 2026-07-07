//! Interpreted-mode C FFI CALL fences — the full `Foreign.call` path over
//! the system libffi (`PolyInterpretedGetAbiList` / `CreateCIF` /
//! `CallFunction`, port of bytecode.cpp:2478+). Requires the `ffi` cargo
//! feature (default-on) and a linkable system libffi.
//!
//! Calls real libc/libm functions through the ML `Foreign` structure and
//! checks the results against the known C answers (differential-verified
//! against upstream Poly/ML at development time). Covers: int arg/result
//! (`abs`), pointer arg (`strlen`), double arg/result (`sqrt`), two
//! double args (`pow`), and a STRUCT return (`div` → `div_t`). Also
//! checks that `--untrusted` refuses the call path.
//!
//! `#[ignore]` — needs `vendor/polyml/polyexport` (self-bootstrap first):
//! ```sh
//! cargo test --release -p polyml-bin --test ffi_calls -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use std::path::PathBuf;

fn polyexport() -> Option<PathBuf> {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../vendor/polyml/polyexport");
    p.canonicalize().ok().filter(|p| p.exists())
}

const DRIVER: &str = r#"
open Foreign;
val exe = loadExecutable ();
val cabs = buildCall1 (getSymbol exe "abs", cInt, cInt);
val () = print ("ABS=" ^ Int.toString (cabs ~5) ^ "\n");
val cstrlen = buildCall1 (getSymbol exe "strlen", cString, cInt);
val () = print ("STRLEN=" ^ Int.toString (cstrlen "hello") ^ "\n");
val csqrt = buildCall1 (getSymbol exe "sqrt", cDouble, cDouble);
val () = print ("SQRT=" ^ Real.toString (csqrt 2.0) ^ "\n");
val cpow = buildCall2 (getSymbol exe "pow", (cDouble, cDouble), cDouble);
val () = print ("POW=" ^ Real.toString (cpow (2.0, 10.0)) ^ "\n");
val cdiv = buildCall2 (getSymbol exe "div", (cInt, cInt), cStruct2(cInt, cInt));
val (q, r) = cdiv (17, 5);
val () = print ("DIV=" ^ Int.toString q ^ "/" ^ Int.toString r ^ "\n");
"#;

/// Real C functions called through the whole Foreign stack return the
/// correct C answers.
#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn foreign_calls_real_libc() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let Some((out, _rc)) = run_image_env(&image, DRIVER, 20_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    for expect in [
        "ABS=5",
        "STRLEN=5",
        "SQRT=1.41421356237",
        "POW=1024.0",
        "DIV=3/2",
    ] {
        assert!(
            out.contains(expect),
            "FFI call fence missing {expect}:\n{out}"
        );
    }
}

/// `--untrusted` must refuse the FFI call path (raw unmanaged pointers no
/// space predicate can validate); the call raises rather than executing.
#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn untrusted_refuses_foreign_call() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let sml = "open Foreign;\n\
               val cabs = buildCall1 (getSymbol (loadExecutable ()) \"abs\", cInt, cInt);\n\
               val () = print (\"UT-ABS=\" ^ Int.toString (cabs ~5) ^ \"\\n\");\n";
    let vendor = image.parent().unwrap();
    let poly = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../target/release/poly");
    let out = std::process::Command::new(poly)
        .current_dir(vendor)
        .args(["run", "--untrusted", "polyexport"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .and_then(|mut c| {
            use std::io::Write;
            c.stdin.take().unwrap().write_all(sml.as_bytes())?;
            c.wait_with_output()
        })
        .expect("spawn poly");
    let all = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        !all.contains("UT-ABS=5"),
        "untrusted mode executed a foreign call:\n{all}"
    );
}
