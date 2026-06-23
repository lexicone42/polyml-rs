//! Asynchronous interrupt (SIGINT / Ctrl-C) delivery to the running
//! interpreter.
//!
//! The host process installs a signal handler that calls [`request_interrupt`]
//! (async-signal-safe — a single relaxed atomic store). The interpreter's
//! `run_until` loop polls [`take_interrupt`] at a coarse cadence and, when an
//! interrupt is pending, raises the SML `Interrupt` exception
//! (`EXC_interrupt = 1`, `vendor/polyml/libpolyml/sys.h:26`). That unwinds to
//! the nearest handler — e.g. the REPL's top level returns to the prompt —
//! instead of the OS hard-killing the process on Ctrl-C.
//!
//! This is the "interrupts" half of PolyML's "threads & interrupts"; it works
//! in the single-threaded interpreter and needs no scheduler.

use std::sync::atomic::{AtomicBool, Ordering};

static INTERRUPT_PENDING: AtomicBool = AtomicBool::new(false);

/// Request an asynchronous interrupt. **Async-signal-safe** (one relaxed atomic
/// store), so it is safe to call directly from a signal handler. Returns the
/// *previous* pending state: a `true` return means a prior interrupt has not yet
/// been consumed (e.g. a second Ctrl-C while the interpreter hasn't reached a
/// poll point), which the caller may treat as a force-quit request.
pub fn request_interrupt() -> bool {
    INTERRUPT_PENDING.swap(true, Ordering::Relaxed)
}

/// Consume a pending interrupt. Returns `true` exactly once per
/// [`request_interrupt`]. Used by the interpreter's poll point.
#[must_use]
pub fn take_interrupt() -> bool {
    INTERRUPT_PENDING.swap(false, Ordering::Relaxed)
}

/// Whether an interrupt is pending, without consuming it (for the SML-level
/// `Thread.Thread.testInterrupt` RTS call).
#[must_use]
pub fn interrupt_pending() -> bool {
    INTERRUPT_PENDING.load(Ordering::Relaxed)
}

/// Clear any pending interrupt (e.g. when a REPL returns to its prompt).
pub fn clear_interrupt() {
    INTERRUPT_PENDING.store(false, Ordering::Relaxed);
}
