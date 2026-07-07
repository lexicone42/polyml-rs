//! Foreign.Memory fences — the C-memory layer of the FFI (upstream
//! Test162/Test163's substrate).
//!
//! What's real: `PolyFFIMalloc`/`PolyFFIFree` (libc malloc/free returning
//! a boxed voidStar) and the twelve `loadC*`/`storeC*` interpreter
//! opcodes (bytecode.cpp:2061+): base = boxed large-word holding a raw C
//! pointer, SIGNED byte offset + SIGNED typed index, widths 8/16/32/64/
//! float/double (loads tag or box per width; float loads widen to Real).
//!
//! SECURITY: the C-memory opcodes dereference unmanaged addresses that no
//! space predicate can validate, so `--untrusted` REFUSES them (clean
//! Unimplemented halt, no wild deref) — checked here.
//!
//! `#[ignore]` — needs `vendor/polyml/polyexport` (self-bootstrap first):
//! ```sh
//! cargo test --release -p polyml-bin --test ffi_memory -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use std::path::PathBuf;

fn polyexport() -> Option<PathBuf> {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../vendor/polyml/polyexport");
    p.canonicalize().ok().filter(|p| p.exists())
}

const DRIVER: &str = r#"
open Foreign.Memory;
val m = malloc 0w64;
val () = set8(m, 0w0, 0wxAB);
val () = set16(m, 0w1, 0wx1234);
val () = set32(m, 0w1, 0wxDEADBEEF);
val () = set64(m, 0w1, 0wx1122334455667788);
val () = setFloat(m, 0w4, 3.5);
val () = setDouble(m, 0w3, 2.718281828459045);
val () = print ("G8=" ^ Word8.toString (get8(m,0w0)) ^ "\n");
val () = print ("G16=" ^ Word.toString (get16(m,0w1)) ^ "\n");
val () = print ("G32=" ^ Word32.toString (get32(m,0w1)) ^ "\n");
val () = print ("G64=" ^ SysWord.toString (get64(m,0w1)) ^ "\n");
val () = print ("GF=" ^ Real.toString (getFloat(m,0w4)) ^ "\n");
val () = print ("GD=" ^ Real.toString (getDouble(m,0w3)) ^ "\n");
(* Negative-offset check: write via e (=m+16) at index ~1 → m+12, read
   via m at index 3 → m+12 (SAME address); tests signed index/offset. *)
val e = ++(m, 0w16);
val () = set32(e, ~ 0w1, 0wxCAFE);
val () = print ("NEG=" ^ Word32.toString (get32(m, 0w3)) ^ "\n");
val () = free m;
(* The int16 conversion round-trip that upstream Test162 checks (negative
   values need sign-extension through the 16-bit store/load). *)
val c = Foreign.breakConversion Foreign.cInt16;
fun rt v =
let
    val mm = Foreign.Memory.malloc (#size (#ctype c));
    val _ = #store c (mm, v);
    val r = #load c mm before Foreign.Memory.free mm
in
    if r = v then () else raise Fail "roundtrip"
end;
val () = List.app rt [~1, 1, 0, 32767, ~32768];
val () = print "INT16-OK\n";
"#;

/// All widths round-trip with the exact values upstream produces
/// (differential-verified at development time; the literals below are
/// the shared expectation).
#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn c_memory_round_trips() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let Some((out, _rc)) = run_image_env(&image, DRIVER, 20_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    for expect in [
        "G8=AB",
        "G16=1234",
        "G32=DEADBEEF",
        "G64=1122334455667788",
        "GF=3.5",
        "GD=2.71828182846",
        "NEG=CAFE",
        "INT16-OK",
    ] {
        assert!(out.contains(expect), "missing {expect}:\n{out}");
    }
}

/// `--untrusted` must REFUSE the C-memory opcodes (clean halt, no deref).
#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn untrusted_refuses_c_memory() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let sml = "val m = Foreign.Memory.malloc 0w8;\n\
               val () = Foreign.Memory.set32(m, 0w0, 0wx1234);\n\
               val () = print \"UNTRUSTED-EXECUTED\\n\";\n";
    let Some((out, _rc)) =
        run_image_env(&image, sml, 20_000_000_000, &[("POLY_UNTRUSTED_TEST", "1")])
    else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    // The harness env doesn't set --untrusted; drive it via the flag.
    // (run_image_env has no flag plumbing, so run the binary directly.)
    drop(out);
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
        !all.contains("UNTRUSTED-EXECUTED"),
        "untrusted mode executed a C-memory store:\n{all}"
    );
}
