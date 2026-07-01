//! Wave 1b — REAL SOCKETS end-to-end proof.
//!
//! Drives an SML TCP echo server (`socket_support/echo_demo.sml`) through the
//! self-bootstrapped `polyexport` REPL, which now calls the genuine
//! `PolyNetwork*` RTS entry points (blocking libc sockets — see the
//! `mod socket_rts` block in `crates/polyml-runtime/src/rts.rs`). The server
//! binds 127.0.0.1:0, prints its kernel-assigned port, and echoes one message.
//! THIS TEST is the CLIENT: it reads the port, connects a `std::net::TcpStream`,
//! sends a payload, and asserts the identical bytes come back — proving bytes
//! actually round-trip through real kernel sockets (not a faked success).
//!
//! Single-threaded by design: the SML side blocks on `accept`/`recv` (there is
//! no scheduler in the default runtime), so the client must be a SEPARATE OS
//! process — here, this Rust test itself.
//!
//! Skips cleanly when `vendor/polyml/polyexport` is absent (build it by
//! self-bootstrapping the 7-stage chain; see the crate README / CLAUDE.md).

use std::io::{BufRead, BufReader, Read, Write};
use std::net::{Ipv4Addr, SocketAddrV4, TcpStream};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::mpsc;
use std::time::Duration;

fn workspace_root() -> PathBuf {
    let mut p: PathBuf = env!("CARGO_MANIFEST_DIR").into();
    loop {
        let is_root = std::fs::read_to_string(p.join("Cargo.toml"))
            .is_ok_and(|t| t.contains("[workspace]"));
        if is_root {
            return p;
        }
        assert!(p.pop(), "could not find workspace root");
    }
}

fn polyexport() -> Option<PathBuf> {
    let p = workspace_root().join("vendor/polyml/polyexport");
    p.exists().then_some(p)
}

/// Best-effort kill so a wedged child never lingers past the test.
fn reap(mut child: Child) {
    let _ = child.kill();
    let _ = child.wait();
}

#[test]
fn echo_server_roundtrips_real_kernel_sockets() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap the 7-stage chain)");
        return;
    };
    let driver = include_str!("socket_support/echo_demo.sml");

    let mut child = Command::new(env!("CARGO_BIN_EXE_poly"))
        .args(["run", "--max-steps", "2000000000"])
        .arg(&image)
        .env("POLYML_GC_QUIET", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn poly");

    // Feed the server driver, then close stdin so the REPL exits on EOF once
    // the echo declaration completes.
    child
        .stdin
        .take()
        .unwrap()
        .write_all(driver.as_bytes())
        .expect("write driver to poly stdin");

    // Drain stderr on a background thread (keeps the pipe from filling and
    // preserves diagnostics on failure).
    let stderr = child.stderr.take().unwrap();
    let err_handle = std::thread::spawn(move || {
        let mut s = String::new();
        let _ = BufReader::new(stderr).read_to_string(&mut s);
        s
    });

    // Read stdout on a background thread: scan for "PORT=<n>", hand the port
    // to the main thread, and keep draining (so the server never blocks on a
    // full stdout pipe). Returns the full stdout text when the child exits.
    let stdout = child.stdout.take().unwrap();
    let (port_tx, port_rx) = mpsc::channel::<u16>();
    let out_handle = std::thread::spawn(move || {
        let mut acc = String::new();
        let mut sent = false;
        let reader = BufReader::new(stdout);
        for line in reader.lines() {
            let Ok(line) = line else { break };
            if !sent && let Some(port) = parse_port(&line) {
                let _ = port_tx.send(port);
                sent = true;
            }
            acc.push_str(&line);
            acc.push('\n');
        }
        acc
    });

    // Wait (bounded) for the server to announce its port.
    let Ok(port) = port_rx.recv_timeout(Duration::from_secs(45)) else {
        reap(child);
        let out = out_handle.join().unwrap_or_default();
        let err = err_handle.join().unwrap_or_default();
        panic!(
            "server never printed PORT= within 45s\n--- stdout ---\n{out}\n--- stderr ---\n{err}"
        );
    };
    assert!(port != 0, "server reported an ephemeral port of 0");

    // ---- The actual round-trip through real kernel sockets. ----
    let payload = b"HELLO, polyml-rs sockets! 0123456789";
    let addr = SocketAddrV4::new(Ipv4Addr::LOCALHOST, port);
    let echoed: Vec<u8> = (|| {
        let mut stream = TcpStream::connect_timeout(&addr.into(), Duration::from_secs(10))?;
        stream.set_read_timeout(Some(Duration::from_secs(10)))?;
        stream.set_write_timeout(Some(Duration::from_secs(10)))?;
        stream.write_all(payload)?;
        stream.flush()?;
        // The server echoes then closes the connection, so read to EOF.
        let mut buf = Vec::new();
        stream.read_to_end(&mut buf)?;
        Ok::<Vec<u8>, std::io::Error>(buf)
    })()
    .unwrap_or_else(|e| {
        // Grab whatever the child printed to aid debugging before we bail.
        let _ = child.kill();
        panic!("client socket exchange failed: {e}");
    });

    // Let the child finish and collect its output.
    let _ = child.wait();
    let out = out_handle.join().unwrap_or_default();
    let err = err_handle.join().unwrap_or_default();

    assert_eq!(
        echoed,
        payload.to_vec(),
        "bytes did NOT round-trip through the kernel sockets\n\
         sent={:?}\nback={:?}\n--- server stdout ---\n{out}\n--- server stderr ---\n{err}",
        String::from_utf8_lossy(payload),
        String::from_utf8_lossy(&echoed),
    );
    assert!(
        out.contains(&format!("ECHOED={}", payload.len())),
        "server did not report echoing all {} bytes\n--- stdout ---\n{out}",
        payload.len()
    );
    assert!(
        !out.contains("Exception-") && !err.contains("Exception-"),
        "an SML exception was raised during the socket demo\n--- stdout ---\n{out}\n--- stderr ---\n{err}"
    );
}

/// Extract the port from a REPL line that contains `PORT=<digits>` (the line
/// may carry a leading `> ` prompt or other REPL noise).
fn parse_port(line: &str) -> Option<u16> {
    let idx = line.find("PORT=")?;
    let digits: String = line[idx + 5..]
        .chars()
        .take_while(char::is_ascii_digit)
        .collect();
    digits.parse().ok()
}
