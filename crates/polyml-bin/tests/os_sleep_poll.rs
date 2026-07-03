//! `OS.IO.poll` / `OS.Process.sleep` fences — the real `poll(2)` behind
//! `PolyPollIODescriptors`.
//!
//! That entry was a legacy success-shaped stub (returned tagged 0 where
//! the basis expects a `word Vector.vector`); `OS.Process.sleep` — which
//! is `OS.IO.poll([], SOME t)` — then ran `Vector.exists` over the 0 and
//! dereferenced a near-null header. Upstream's own Test166 found the
//! resulting SEGV under `POLY_REAL_THREADS=1` after 450 clean fuzz seeds
//! (the fuzzer never called sleep — coverage of code paths is not
//! coverage of entry points).
//!
//! Two fences:
//! 1. `sleep_really_sleeps` — sleep must take wall-clock time (the stub
//!    returned instantly) and return cleanly, single-threaded.
//! 2. `upstream_test166_condvars_with_real_threads` — the full upstream
//!    condvar test (3 workers on one condvar, a 10,000-round signal
//!    ping-pong, a 2 s sleep, a signal/wait shutdown protocol) runs to
//!    completion under `POLY_REAL_THREADS=1`.
//!
//! `#[ignore]` — needs `vendor/polyml/polyexport` (self-bootstrap first):
//! ```sh
//! cargo test --release -p polyml-bin --test os_sleep_poll -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use std::path::PathBuf;
use std::time::Instant;

fn polyexport() -> Option<PathBuf> {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../vendor/polyml/polyexport");
    p.canonicalize().ok().filter(|p| p.exists())
}

#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn sleep_really_sleeps() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let sml = "val () = OS.Process.sleep (Time.fromSeconds 2);\n\
               val () = print \"SLEEP_OK\\n\";\n";
    let t0 = Instant::now();
    let Some((out, _)) = run_image_env(&image, sml, 10_000_000_000, &[]) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    let secs = t0.elapsed().as_secs_f64();
    assert!(
        out.contains("SLEEP_OK"),
        "sleep did not return cleanly (the tagged-0-as-vector stub \
         crashed here):\n{out}"
    );
    assert!(
        secs >= 1.5,
        "OS.Process.sleep(2s) returned in {secs:.2}s — the deceptive \
         instant-return stub is back"
    );
}

/// Ctrl-C (SIGINT) during a BLOCKED stdin read must raise the SML
/// `Interrupt` exception promptly — caught by the program's own handler —
/// not wait for input to arrive (the pre-fix behavior: the EINTR retry
/// loop swallowed the signal and the 65536-step poll never came while
/// blocked) and not surface as a `SysErr` artifact of the aborted read.
#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn sigint_aborts_blocked_stdin_read_with_sml_interrupt() {
    use std::io::{BufRead, BufReader, Write};
    use std::process::{Command, Stdio};
    use std::time::{Duration, Instant};

    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let mut child = Command::new(env!("CARGO_BIN_EXE_poly"))
        .args(["run", "--max-steps", "10000000000"])
        .arg(&image)
        .env("POLYML_GC_QUIET", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn poly");

    // One declaration, two reads: the first consumes the declaration's own
    // leftover newline (the REPL and program share buffered stdin); the
    // second genuinely blocks. Stdin stays OPEN (no data) so only SIGINT
    // can end the read.
    let mut stdin = child.stdin.take().expect("stdin");
    stdin
        .write_all(
            b"val x = (TextIO.inputLine TextIO.stdIn; TextIO.inputLine TextIO.stdIn) \
              handle e => (print (\"@@CAUGHT \" ^ exnName e ^ \"\\n\"); NONE);\n",
        )
        .expect("write driver");
    stdin.flush().expect("flush");

    // Give the REPL time to compile and block in the second read.
    std::thread::sleep(Duration::from_secs(3));
    let pid = child.id().to_string();
    let t0 = Instant::now();
    let _ = Command::new("kill").args(["-INT", &pid]).status();

    // The handler's print must arrive promptly.
    let stdout = child.stdout.take().expect("stdout");
    let mut reader = BufReader::new(stdout);
    let mut seen = String::new();
    let caught = loop {
        if t0.elapsed() > Duration::from_secs(5) {
            break false;
        }
        let mut line = String::new();
        match reader.read_line(&mut line) {
            Ok(0) => break false,
            Ok(_) => {
                seen.push_str(&line);
                if line.contains("@@CAUGHT Interrupt") {
                    break true;
                }
            }
            Err(_) => break false,
        }
    };
    let latency = t0.elapsed();
    let _ = child.kill();
    let _ = child.wait();
    assert!(
        caught,
        "SIGINT did not raise SML Interrupt into the blocked read's handler \
         within 5s:\n{seen}"
    );
    assert!(
        latency < Duration::from_secs(3),
        "Interrupt took {latency:?} — the blocked read is not aborting promptly"
    );
}

#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn upstream_test166_condvars_with_real_threads() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let test = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../vendor/polyml/Tests/Succeed/Test166.ML");
    if !test.exists() {
        eprintln!("SKIP: vendor Tests/Succeed/Test166.ML missing");
        return;
    }
    let sml = "exception NotApplicable;\n\
               val () = (PolyML.use \"Tests/Succeed/Test166.ML\"; print \"\\nT166_PASS\\n\")\n\
               \x20 handle NotApplicable => print \"\\nT166_PASS\\n\"\n\
               \x20      | e => print (\"\\nT166_FAIL \" ^ exnMessage e ^ \"\\n\");\n";
    let Some((out, code)) =
        run_image_env(&image, sml, 50_000_000_000, &[("POLY_REAL_THREADS", "1")])
    else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("T166_PASS"),
        "upstream Test166 (condvars + sleep under real threads) failed \
         (exit={code}) — the poll/condvar surface regressed:\n{out}"
    );
}
