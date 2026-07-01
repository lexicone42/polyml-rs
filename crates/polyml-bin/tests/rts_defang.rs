//! Regression fence for the RTS stub DE-FANG (task #135): unimplemented
//! OS-level entry points must raise a catchable exception, never return a
//! success-shaped default.
//!
//! History: `OS.Process.system "cmd"` returned tagged(0) — which is also
//! the registered success value — so it reported success without running
//! anything. Same class: chDir, sockets, Posix operations, FFI, SaveState,
//! stream seek. Each now raises (`SysErr` for the errno-shaped OS surface,
//! a generic catchable exception otherwise). These tests drive the real
//! self-bootstrapped REPL and pin both halves of the contract:
//!   1. the call raises (no silent fake success), and
//!   2. the exception is CATCHABLE with the upstream handler shape
//!      (`handle OS.SysErr _`), so defensive SML code keeps working.
//!
//! Needs `vendor/polyml/polyexport` (the basis-bearing image example #2 of
//! the README builds); skips cleanly when absent. The load-bearing stubs
//! that must NOT raise (signal-handler registration at REPL startup,
//! `Posix.FileSys.stdin/stdout/stderr` construction, `getConst` errno
//! tables at basis load) are pinned implicitly: the REPL starting up AND
//! the probes running at all proves them.

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

fn polyexport() -> Option<PathBuf> {
    let p = workspace_root().join("vendor/polyml/polyexport");
    p.exists().then_some(p)
}

/// Pipe `sml` into the polyexport REPL, return stdout+stderr.
fn repl(sml: &str) -> Option<String> {
    let image = polyexport()?;
    let mut child = Command::new(env!("CARGO_BIN_EXE_poly"))
        .args(["run", "--max-steps", "50000000"])
        .arg(&image)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .ok()?;
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(sml.as_bytes())
        .ok()?;
    let out = child.wait_with_output().ok()?;
    Some(format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    ))
}

#[test]
fn process_system_raises_catchable_syserr() {
    let Some(out) = repl(
        r#"(OS.Process.system "echo LEAKED_EXECUTION") handle OS.SysErr (m, _) => (print ("CAUGHT: " ^ m ^ "\n"); OS.Process.failure);"#,
    ) else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (build it: README example #2)");
        return;
    };
    assert!(
        out.contains("CAUGHT: OS.Process.system: not implemented"),
        "OS.Process.system did not raise a catchable SysErr:\n{out}"
    );
    // The command must NOT have actually run (it never did; the old stub
    // only pretended) — and must NOT report silent success.
    assert!(
        !out.contains("LEAKED_EXECUTION"),
        "OS.Process.system executed a real command:\n{out}"
    );
}

#[test]
fn chdir_raises_catchable_syserr() {
    let Some(out) = repl(
        r#"(OS.FileSys.chDir "/tmp") handle OS.SysErr (m, _) => print ("CAUGHT: " ^ m ^ "\n");"#,
    ) else {
        eprintln!("SKIP: vendor/polyml/polyexport missing");
        return;
    };
    assert!(
        out.contains("CAUGHT: OS.FileSys.chDir: not implemented"),
        "chDir did not raise a catchable SysErr:\n{out}"
    );
}

#[test]
fn repl_still_healthy_after_defanged_raises() {
    // A raise-then-continue session: the de-fanged raises must not poison
    // the REPL (exception unwinding, GC state, IO).
    let Some(out) = repl(concat!(
        r#"(OS.Process.system "x") handle OS.SysErr _ => OS.Process.failure;"#,
        "\n",
        "fun fact 0 = 1 | fact n = n * fact (n - 1); fact 10;\n",
        "OS.FileSys.getDir ();\n",
    )) else {
        eprintln!("SKIP: vendor/polyml/polyexport missing");
        return;
    };
    assert!(
        out.contains("3628800"),
        "REPL unhealthy after raise:\n{out}"
    );
    assert!(
        out.contains("Result: Tagged(0)"),
        "session did not end cleanly:\n{out}"
    );
}
