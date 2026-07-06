//! Fences for the 2026-07-06 capability batch: REAL IEEE rounding modes,
//! REAL DNS (getaddrinfo/getnameinfo), and the OS.syserror name->errno
//! lookup.
//!
//! - Rounding: `IEEEReal.setRoundingMode` is fesetround (per-arch FE_*
//!   tables in `rts.rs::fenv`); our Real ops are Rust f64 arithmetic
//!   lowered to SSE/FPCR-honoring instructions, so directed rounding
//!   flows through ordinary SML arithmetic AND `Real32.fromLarge`'s
//!   set-convert-restore dance (upstream Test121/Test174/Test171).
//! - DNS: `NetHostDB.getByName`/`getByAddr` are real getaddrinfo /
//!   getnameinfo under `park_while_blocking` (upstream Test078 gate).
//! - `OS.syserror`: PolyProcessEnvErrorFromString inverts the errno_name
//!   table (upstream Test082's ECONNREFUSED comparison).
//!
//! `#[ignore]` — needs `vendor/polyml/polyexport` (self-bootstrap first):
//! ```sh
//! cargo test --release -p polyml-bin --test rounding_dns -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use std::path::PathBuf;

fn polyexport() -> Option<PathBuf> {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../vendor/polyml/polyexport");
    p.canonicalize().ok().filter(|p| p.exists())
}

fn run(driver: &str) -> Option<String> {
    let image = polyexport()?;
    let (out, _rc) = run_image_env(&image, driver, 20_000_000_000, &[])?;
    Some(out)
}

/// Directed rounding is honored by subsequent interpreter FP arithmetic
/// (Test121's core assertion) and reads back via getRoundingMode.
#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn rounding_modes_honored_by_arithmetic() {
    let driver = r#"
open IEEEReal;
val () = setRoundingMode TO_POSINF;
val () = if getRoundingMode () = TO_POSINF then print "MODE-OK\n" else print "MODE-FAIL\n";
val pos = 1.0 / 3.0;
val () = if pos * 3.0 > 1.0 then print "POSINF-OK\n" else print "POSINF-FAIL\n";
val () = setRoundingMode TO_NEGINF;
val neg = 1.0 / 3.0;
val () = if neg * 3.0 < 1.0 then print "NEGINF-OK\n" else print "NEGINF-FAIL\n";
val () = setRoundingMode TO_NEAREST;
"#;
    let Some(out) = run(driver) else {
        eprintln!("SKIP: image or poly missing");
        return;
    };
    for m in ["MODE-OK", "POSINF-OK", "NEGINF-OK"] {
        assert!(out.contains(m), "rounding fence missing {m}:\n{out}");
    }
}

/// Real32.fromLarge with an explicit mode argument rounds directionally
/// (Test174's core assertion — cvtsd2ss honors the FP environment).
#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn real32_from_large_directed() {
    let driver = r#"
val p = Real32.toLarge Real32.Math.pi;
val pp = Real.nextAfter (p, Real.posInf);
infix 4 ==; val op == = Real32.==;
val () = if Real32.fromLarge IEEEReal.TO_ZERO pp == Real32.Math.pi
         then print "R32-ZERO-OK\n" else print "R32-ZERO-FAIL\n";
val () = if Real32.fromLarge IEEEReal.TO_POSINF pp == Real32.Math.pi
         then print "R32-POSINF-FAIL\n" else print "R32-POSINF-OK\n";
"#;
    let Some(out) = run(driver) else {
        eprintln!("SKIP: image or poly missing");
        return;
    };
    for m in ["R32-ZERO-OK", "R32-POSINF-OK"] {
        assert!(
            out.contains(m),
            "Real32 directed-rounding fence missing {m}:\n{out}"
        );
    }
}

/// getByName/getByAddr resolve localhost both ways (needs a working
/// loopback resolver — /etc/hosts covers this without network).
#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn dns_localhost_round_trip() {
    let driver = r#"
val () = case NetHostDB.getByName "localhost" of
    SOME e => print ("DNS-OK " ^ NetHostDB.toString (NetHostDB.addr e) ^ "\n")
  | NONE => print "DNS-NONE\n";
val () = case NetHostDB.getByAddr (valOf (NetHostDB.fromString "127.0.0.1")) of
    SOME e => print ("REV-OK " ^ NetHostDB.name e ^ "\n")
  | NONE => print "REV-NONE\n";
"#;
    let Some(out) = run(driver) else {
        eprintln!("SKIP: image or poly missing");
        return;
    };
    assert!(
        out.contains("DNS-OK 127.0.0.1"),
        "getByName localhost must resolve to 127.0.0.1:\n{out}"
    );
    assert!(
        out.contains("REV-OK"),
        "getByAddr reverse lookup failed:\n{out}"
    );
}

/// OS.syserror inverts OS.errorName (Test082's equality check depends on
/// exactly this round trip).
#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn syserror_name_round_trip() {
    let driver = r#"
val () = case OS.syserror "ECONNREFUSED" of
    SOME e => print ("SYS-OK " ^ OS.errorName e ^ "\n")
  | NONE => print "SYS-NONE\n";
val () = case OS.syserror "ENOSUCHNAME" of
    SOME _ => print "BOGUS-FAIL\n"
  | NONE => print "BOGUS-OK\n";
"#;
    let Some(out) = run(driver) else {
        eprintln!("SKIP: image or poly missing");
        return;
    };
    assert!(
        out.contains("SYS-OK ECONNREFUSED"),
        "OS.syserror must round-trip errorName:\n{out}"
    );
    assert!(
        out.contains("BOGUS-OK"),
        "unknown names must map to NONE:\n{out}"
    );
}
