//! P5 capstone — a multi-connection SML compute server under load, driven
//! by REAL external TCP clients from this Rust harness.
//!
//! `concurrency_support/parallel_server_demo.sml` runs an accept loop that
//! forks a handler thread per connection; each handler computes a
//! deterministic pure function of the client's seed and sends it back.
//! The harness connects 4 concurrent clients, verifies every response
//! against a Rust reimplementation of the compute (EXACT values — a wrong
//! integer, not flaky timing), and measures wall-clock from first connect
//! to last response.
//!
//! Two tests:
//! - `server_giant_lock` — the demo is correct under the default
//!   giant-lock threading model (handlers interleave cooperatively).
//! - `server_parallel_speedup` — with `POLY_PARALLEL=1` the four handler
//!   computations run on four cores: wall-clock must beat the giant-lock
//!   run by the gate ratio, with identical responses.
//!
//! This is the P4 integration surface in one program: accept/recv/send
//! parking, 6 live threads (main + accept loop + 4 handlers), parallel
//! compute, handler-side allocation across GCs, external TCP.
//!
//! `#[ignore]` — needs `vendor/polyml/polyexport` (self-bootstrap first):
//! ```sh
//! cargo test --release -p polyml-bin --test concurrency_server -- --ignored --nocapture
//! ```

use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpStream;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const N_CONN: usize = 4;
const ITERS: u64 = 20_000_000;

fn polyexport() -> Option<PathBuf> {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../vendor/polyml/polyexport");
    p.canonicalize().ok().filter(|p| p.exists())
}

/// Rust mirror of the driver's `spin` — the exact-value oracle.
fn spin(seed: u64, iters: u64) -> u64 {
    let mut acc = seed;
    for _ in 0..iters {
        acc = (acc * 31 + 7) % 1_000_003;
    }
    acc
}

/// Spawn the server, drive N_CONN concurrent clients, verify exact
/// responses, return the load wall-clock (first connect → last response).
/// Returns None if poly can't spawn (missing image handled by callers).
fn drive_server(parallel: bool) -> Option<Duration> {
    let image = polyexport()?;
    let driver_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/concurrency_support/parallel_server_demo.sml");
    let driver = std::fs::read_to_string(&driver_path).expect("read parallel_server_demo.sml");

    let mut cmd = Command::new(env!("CARGO_BIN_EXE_poly"));
    cmd.args(["run", "--max-steps", "60000000000"])
        .arg(&image)
        .env("POLY_REAL_THREADS", "1")
        .env("POLYML_GC_QUIET", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if parallel {
        cmd.env("POLY_PARALLEL", "1");
    }
    let mut child = cmd.spawn().ok()?;

    let mut stdin = child.stdin.take().expect("stdin");
    stdin.write_all(driver.as_bytes()).expect("write driver");
    stdin.flush().expect("flush driver");
    drop(stdin); // EOF: the REPL exits once the join declaration finishes.

    // Scan stdout for the kernel-assigned port.
    let stdout = child.stdout.take().expect("stdout");
    let mut reader = BufReader::new(stdout);
    let mut seen = String::new();
    let port: u16 = {
        let deadline = Instant::now() + Duration::from_secs(120);
        loop {
            assert!(
                Instant::now() < deadline,
                "timed out waiting for PORT=; output so far:\n{seen}"
            );
            let mut line = String::new();
            let n = reader.read_line(&mut line).expect("read stdout");
            assert!(n > 0, "poly exited before PORT=; output so far:\n{seen}");
            seen.push_str(&line);
            if let Some(i) = line.find("PORT=") {
                break line[i + 5..].trim().parse().expect("parse port");
            }
        }
    };

    // The load: N_CONN concurrent clients, one OS thread each. Wall-clock
    // spans first connect → last verified response.
    let t0 = Instant::now();
    let handles: Vec<_> = (0..N_CONN)
        .map(|i| {
            std::thread::spawn(move || {
                let seed = (i + 1) as u64;
                let mut c = TcpStream::connect(("127.0.0.1", port)).expect("connect");
                c.write_all(seed.to_string().as_bytes()).expect("send seed");
                // Half-close is unnecessary: the handler does ONE recv.
                let mut resp = String::new();
                c.read_to_string(&mut resp).expect("read response");
                assert_eq!(
                    resp,
                    format!("{seed}:{}", spin(seed, ITERS)),
                    "handler for seed {seed} returned a wrong value"
                );
            })
        })
        .collect();
    for h in handles {
        h.join().expect("client thread");
    }
    let load = t0.elapsed();

    // Drain the rest of stdout from OUR reader (we took child.stdout).
    let mut rest = String::new();
    reader.read_to_string(&mut rest).expect("drain stdout");
    seen.push_str(&rest);
    let out = child.wait_with_output().expect("wait");
    let all = format!("{seen}{}", String::from_utf8_lossy(&out.stderr));

    assert!(
        all.contains("SERVER_DONE"),
        "server did not report completion:\n{all}"
    );
    assert!(
        !all.contains("Exception-"),
        "an exception was raised during the server run:\n{all}"
    );
    Some(load)
}

#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn server_giant_lock() {
    if polyexport().is_none() {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    }
    let Some(load) = drive_server(false) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    eprintln!(
        "[server] giant-lock load handled in {:.2}s",
        load.as_secs_f64()
    );
}

#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn server_parallel_speedup() {
    // Generous gate: the giant-lock run serializes ~4 handler computations;
    // POLY_PARALLEL runs them on 4 cores. Ideal is ~0.25 + constant costs;
    // the gate only has to exclude "no parallelism".
    const GATE: f64 = 0.8;

    if polyexport().is_none() {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    }
    let Some(giant) = drive_server(false) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    let Some(par) = drive_server(true) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    let (tg, tp) = (giant.as_secs_f64(), par.as_secs_f64());
    let ratio = tp / tg;
    eprintln!(
        "[server] giant-lock {tg:.2}s, POLY_PARALLEL {tp:.2}s, ratio {ratio:.2} (gate {GATE})"
    );
    assert!(
        ratio < GATE,
        "4 concurrent connections did not get faster with the giant lock \
         dropped: giant {tg:.2}s vs parallel {tp:.2}s (ratio {ratio:.2}, gate {GATE})"
    );
}
