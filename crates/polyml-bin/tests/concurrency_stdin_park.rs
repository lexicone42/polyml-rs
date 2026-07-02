//! Parked-stdin proof — a thread blocked reading STDIN releases the giant
//! lock, and a GC while it is parked is SOUND (the read's heap destination
//! is bounced through native memory and re-derived from a collector-
//! forwarded root cell).
//!
//! Drives `concurrency_support/stdin_park_demo.sml` with POLY_REAL_THREADS=1
//! and a LOW GC threshold: main forks an allocation-heavy worker (GCs fire
//! constantly), prints READY, and blocks in TextIO.inputLine. The harness
//! waits ~2s after READY — the worker can only make progress in that window
//! if the blocked read released the lock — then writes a line. The demo
//! asserts the worker progressed AND the line arrived INTACT through the
//! bounce+forwarded-cell path (many collections moved the destination
//! buffer while the reader was parked).
//!
//! Unlike the other concurrency demos this cannot use `run_image_env` (it
//! pipes all stdin upfront, so the read would never block): it spawns poly
//! directly and writes stdin in two timed phases.
//!
//! `#[ignore]` — needs `vendor/polyml/polyexport` (self-bootstrap first):
//! ```sh
//! cargo test --release -p polyml-bin --test concurrency_stdin_park -- --ignored --nocapture
//! ```

use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};

fn polyexport() -> Option<PathBuf> {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../vendor/polyml/polyexport");
    p.canonicalize().ok().filter(|p| p.exists())
}

#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn stdin_read_parks_the_giant_lock() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/concurrency_support/stdin_park_demo.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read stdin_park_demo.sml");

    let mut child = Command::new(env!("CARGO_BIN_EXE_poly"))
        .args(["run", "--max-steps", "50000000000"])
        .arg(&image)
        .env("POLY_REAL_THREADS", "1")
        // Aggressive threshold: collections fire constantly under the
        // worker's allocation, so the parked reader's destination buffer
        // provably MOVES while it waits.
        .env("POLYML_GC_THRESHOLD", "1")
        .env("POLYML_GC_QUIET", "1")
        .env("POLYML_HEAP_BYTES", (256 * 1024 * 1024).to_string())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn poly");

    // The driver source; the REPL compiles it, forks the worker, prints
    // READY, then consumes buffered leftovers until our "mark" line (the
    // REPL and the program SHARE the buffered stdin, so leftovers from the
    // driver text itself would make a single naive read return instantly).
    let mut stdin = child.stdin.take().expect("stdin");
    stdin.write_all(driver.as_bytes()).expect("write driver");
    // "mark" sent immediately — phase-1 reads must not block.
    stdin.write_all(b"mark\n").expect("write mark");
    stdin.flush().expect("flush driver+mark");

    // Bounded stdout scanning (a helper so READY/MARKED share the logic).
    let stdout = child.stdout.take().expect("stdout");
    let mut reader = BufReader::new(stdout);
    let mut seen = String::new();
    let mut await_line = |seen: &mut String, want: &str| {
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(120);
        loop {
            assert!(
                std::time::Instant::now() < deadline,
                "timed out waiting for {want}; output so far:\n{seen}"
            );
            let mut line = String::new();
            let n = reader.read_line(&mut line).expect("read stdout");
            assert!(n > 0, "poly exited before {want}; output so far:\n{seen}");
            seen.push_str(&line);
            if line.contains(want) {
                break;
            }
        }
    };
    await_line(&mut seen, "READY");
    await_line(&mut seen, "MARKED");

    // Main is now PARKED in the blocking stdin read (p0 snapshotted); the
    // worker allocates — GCs fire constantly — for this whole window. If
    // the blocked read held the giant lock, main would hit no safepoint
    // and the worker would make EXACTLY ZERO progress (delta = 0).
    std::thread::sleep(std::time::Duration::from_secs(2));
    let go = "the-parked-line-arrives-intact-through-the-bounce-and-forwarded-cell";
    stdin
        .write_all(format!("{go}\n").as_bytes())
        .expect("write go line");
    stdin.flush().expect("flush go line");
    drop(stdin); // EOF ends the REPL session cleanly.

    // Drain the REST of stdout from OUR reader — we took child.stdout, so
    // wait_with_output would collect nothing (the verdict lines would be
    // silently discarded from the BufReader).
    {
        use std::io::Read;
        let mut rest = String::new();
        reader.read_to_string(&mut rest).expect("drain stdout");
        seen.push_str(&rest);
    }
    let out = child.wait_with_output().expect("wait");
    let all = format!("{seen}{}", String::from_utf8_lossy(&out.stderr));

    assert!(
        all.contains(&format!("GOT=[{go}]")),
        "the go-line did not round-trip intact through the parked read \
         (bounce/forwarded-cell corruption?):\n{all}"
    );
    assert!(
        all.contains("STDIN_PARK_PASS"),
        "the worker made ~no progress while main was blocked in the stdin \
         read — the read did not release the giant lock:\n{all}"
    );
    assert!(
        !all.contains("Exception-"),
        "an exception was raised during the demo:\n{all}"
    );
}
