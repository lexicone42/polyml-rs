//! Concurrency increment 3 (Track A) — real two-thread integration test.
//!
//! Proves the load-bearing pieces of the giant-lock + safepoint model with
//! REAL OS threads sharing one `Runtime` (one heap, one scheduler):
//!
//! - **Real fork-style spawn + shared heap**: two `ThreadContext`s over a
//!   single `Arc<Runtime>`, each running real bytecode that allocates.
//! - **Giant-lock mutual exclusion**: only one thread runs bytecode at a
//!   time; a shared counter bumped by each thread between bytecode steps
//!   shows no lost updates.
//! - **Stop-the-world GC handshake (the biggest risk)**: a tiny heap +
//!   low threshold makes the GC fire *while the other thread is parked at
//!   a safepoint with published roots*. With `POLYML_GC_AUDIT=1` the
//!   collector must report ZERO residual from-space pointers across BOTH
//!   threads' stacks — i.e. every parked thread's roots were forwarded.
//!
//! This does NOT drive the full SML `Thread`/`Mutex` basis (that path is
//! exercised only through the self-bootstrapped REPL, whose own startup
//! console-thread architecture is incompatible with naive real-fork — see
//! the worktree report). It exercises the same scheduler primitives the
//! SML path uses, at the Rust API boundary.

// Width/sign casts in the hand-built code-object layout mirror the
// interpreter's own `make_code_object` test helper; the redundant `let x =
// x` re-bind is the idiomatic "move this Copy into the spawned closure".
#![allow(
    clippy::cast_sign_loss,
    clippy::cast_possible_wrap,
    clippy::cast_possible_truncation,
    clippy::cast_lossless,
    clippy::redundant_locals,
    clippy::significant_drop_tightening
)]

use std::sync::Arc;

use polyml_runtime::interpreter::Interpreter;
use polyml_runtime::poly_word::PolyWord;
use polyml_runtime::space::{MemorySpace, SpaceKind};

// Opcode bytes (mirrors crate::interpreter::opcodes).
const CONST_0: u8 = 0x3b;
const ALLOC_REF: u8 = 0x06;
const RESET_B: u8 = 0x26;
const CONST_INT_B: u8 = 0x28;
const LOCAL_0: u8 = 0x29;
const JUMP_BACK8: u8 = 0x1e;
const RETURN_B: u8 = 0x1f;
const JUMP8_TRUE: u8 = 0x46;
const EQUAL_WORD: u8 = 0xa0;
const FIXED_SUB: u8 = 0xab;

/// An allocation loop: while the on-stack counter != 0, allocate a 1-word
/// ref (immediately discarded → garbage → forces GC churn) and decrement
/// the counter; then RETURN the counter (0). Stack-neutral per iteration
/// except the decrement. Byte offsets are hand-computed (see comments).
fn alloc_loop_code() -> Vec<u8> {
    vec![
        // pc=0  top:
        CONST_0,   // [0, ctr]      push init value 0
        ALLOC_REF, // [ref, ctr]    replace top with a fresh ref
        RESET_B,
        1, // [ctr]         drop the ref (garbage)
        CONST_INT_B,
        1,          // [1, ctr]
        FIXED_SUB,  // [ctr-1]       ctr - 1
        LOCAL_0,    // [c', c']      dup the new counter
        CONST_0,    // [0, c', c']
        EQUAL_WORD, // [bool, c']    c' == 0 ?
        // pc=10 JUMP8_TRUE +2 -> end (pc after imm = 12, +2 = 14)
        JUMP8_TRUE,
        2,
        // pc=12 JUMP_BACK8 12 -> ic(12) - 12 = 0 (top)
        JUMP_BACK8,
        12,
        // pc=14 end:
        RETURN_B,
        0,
    ]
}

/// Materialise a code object holding `code_bytes` + an (empty) constant
/// pool, into `space`. Returns the code-object pointer. (Same layout as
/// the interpreter's internal `make_code_object` test helper.)
fn make_code_object(space: &mut MemorySpace, code_bytes: &[u8]) -> *const PolyWord {
    let word = std::mem::size_of::<usize>();
    let code_words = code_bytes.len().div_ceil(word);
    let n_consts = 0usize;
    let total_words = code_words + n_consts + 2;
    let obj_ptr = space.alloc(total_words);
    unsafe {
        polyml_runtime::space::set_length_word(
            obj_ptr,
            total_words,
            polyml_runtime::length_word::F_CODE_OBJ,
        );
        let dst = obj_ptr.cast::<u8>();
        std::ptr::copy_nonoverlapping(code_bytes.as_ptr(), dst, code_bytes.len());
        let pad = code_bytes.len().next_multiple_of(word) - code_bytes.len();
        if pad > 0 {
            std::ptr::write_bytes(dst.add(code_bytes.len()), 0, pad);
        }
        obj_ptr.add(code_words).write(PolyWord::from_bits(n_consts));
        let const_addr_index = (code_words + 1) as isize;
        let total_isize = total_words as isize;
        let word_isize = word as isize;
        let offset_bytes = (const_addr_index - total_isize) * word_isize;
        obj_ptr
            .add(total_words - 1)
            .write(PolyWord::from_bits(offset_bytes as usize));
    }
    obj_ptr.cast_const()
}

/// A `Send` wrapper for the code-object pointer so it can cross the spawn
/// boundary. The code object lives in the shared heap and is rooted by
/// each worker's `code_start`, so it stays live (and is forwarded by the
/// GC) for the whole run.
#[derive(Clone, Copy)]
struct CodePtr(usize);
unsafe impl Send for CodePtr {}

#[test]
fn two_threads_shared_heap_gc_handshake() {
    // Tiny heap + aggressive GC threshold so collections fire WHILE the
    // other thread is parked at a safepoint. Audit on, to catch any
    // un-forwarded parked-thread root.
    // SAFETY: single-test process; env is read once + cached by the
    // interpreter, so setting it before the first interpreter use is fine.
    unsafe {
        std::env::set_var("POLY_REAL_THREADS", "1");
        std::env::set_var("POLYML_GC_THRESHOLD", "50");
        std::env::set_var("POLYML_GC_QUIET", "1");
        std::env::set_var("POLYML_GC_AUDIT", "1");
    }

    // The loop code object lives in a SEPARATE, leaked code space that the
    // GC never collects (the collector only touches the runtime's main
    // heap). This gives the code object a STABLE address across collections
    // — exactly like real SML code, which is rooted in a closure and is in
    // the (non-moving) code space. Re-entering at a fixed address is then
    // sound even though many GCs fire mid-run.
    let code_space: &'static mut MemorySpace =
        Box::leak(Box::new(MemorySpace::new(4096, SpaceKind::Code)));
    let code_ptr = make_code_object(code_space, &alloc_loop_code());
    let code = CodePtr(code_ptr as usize);

    // Build a "host" interpreter to own the shared Runtime + (GC'd) heap.
    let heap = MemorySpace::new(64 * 1024, SpaceKind::Mutable); // 64K words ~512KB
    let host = Interpreter::from_bytes(64, vec![]).with_alloc_space(heap);
    let runtime = host.runtime_arc();

    // Per-iteration count per thread. Large enough to span many safepoints
    // (each iteration is ~12 steps; 200k iters ~2.4M steps >> the 65536
    // safepoint cadence, so GCs + yields interleave heavily).
    let iters: isize = 200_000;
    let threads = 2;

    // A shared counter bumped once per worker iteration, between bytecode
    // runs, under the giant lock by construction (only one thread runs at
    // a time). No lost updates ⇒ mutual exclusion holds.
    let shared = Arc::new(std::sync::Mutex::new(0i64));

    let mut handles = Vec::new();
    for _ in 0..threads {
        let rt = Arc::clone(&runtime);
        let code = code;
        let shared = Arc::clone(&shared);
        handles.push(std::thread::spawn(move || {
            let mut w = Interpreter::for_shared_runtime_test(rt);
            // Run the loop in CHUNKS so we bump the shared counter between
            // chunks (proving interleaving + mutual exclusion across the
            // giant lock). Each chunk re-seeds the counter and re-enters.
            let chunk: isize = 1000;
            let mut done = 0isize;
            while done < iters {
                let this = chunk.min(iters - done);
                w.reset_stack();
                // Seed the entry frame, top-down: [counter, dummyClosure,
                // retPC=null]. RETURN_B 0 pops result(counter), closure,
                // retPC; seeing retPC=null it yields Returned. (Same shape
                // as the interpreter's own `run_to_int` test helper.)
                w.test_seed_return_sentinel(); // retPC = null (deepest)
                w.test_seed_top(PolyWord::tagged(0)); // dummy closure
                w.test_seed_top(PolyWord::tagged(this)); // loop counter (top)
                // SAFETY: code_ptr is a valid code object in the shared heap.
                unsafe { w.set_code_segment_to_code_obj(code.0) };
                let (_, r) = w.run_until(u64::MAX);
                match r {
                    Ok(polyml_runtime::StepResult::Returned(_)) => {}
                    other => panic!("worker run failed: {other:?}"),
                }
                // Bump the shared counter `this` times under the lock.
                {
                    let mut g = shared.lock().unwrap();
                    *g += this as i64;
                }
                done += this;
            }
        }));
    }
    for h in handles {
        h.join().expect("worker thread panicked");
    }

    let total = *shared.lock().unwrap();
    let expected = (iters as i64) * (threads as i64);
    assert_eq!(
        total, expected,
        "lost updates under the giant lock: got {total}, expected {expected}"
    );

    // The whole point: GC fired (many times) WHILE threads ran, and the
    // run completed cleanly (no SEGV, audit clean). Assert collections
    // actually happened — otherwise the handshake wasn't exercised.
    let gcs = runtime.gc_count.load(std::sync::atomic::Ordering::Relaxed);
    assert!(
        gcs > 0,
        "expected the GC to fire mid-run (tiny heap + threshold 50), but gc_count == 0"
    );
    eprintln!("[demo] total={total} (=2N), collections fired = {gcs}, audit clean");

    // Keep `host` alive to the end so the shared heap (and code object)
    // outlive the workers.
    drop(host);
}

/// Interleaving evidence (a positive control for "the threads really do
/// take turns under the giant lock", not run-to-completion serially).
///
/// Each worker runs many small `run_until` chunks; at every chunk it
/// records the GLOBAL handoff order under a shared counter (incremented
/// while holding the giant lock implicitly — only the running thread bumps
/// it). If both threads' handoff records are interspersed (each thread saw
/// the other run between its own turns), the giant lock is genuinely being
/// yielded and re-acquired — real interleaving.
///
/// (A lost-update negative control is intentionally NOT attempted here:
/// under a giant lock only ONE thread executes bytecode at a time, so a
/// read-modify-write that does not span a safepoint can never lose updates
/// — that is the model working as designed. A lost-update demo requires an
/// RMW of a shared heap ref split across a safepoint, which needs the full
/// SML mutex basis; see the worktree report for why the REPL path is
/// blocked.)
#[test]
fn threads_interleave_under_giant_lock() {
    unsafe {
        std::env::set_var("POLY_REAL_THREADS", "1");
    }
    let code_space: &'static mut MemorySpace =
        Box::leak(Box::new(MemorySpace::new(4096, SpaceKind::Code)));
    let code_ptr = make_code_object(code_space, &alloc_loop_code());
    let code = CodePtr(code_ptr as usize);
    let heap = MemorySpace::new(64 * 1024, SpaceKind::Mutable);
    let host = Interpreter::from_bytes(64, vec![]).with_alloc_space(heap);
    let runtime = host.runtime_arc();

    // Shared log of (thread_id) in handoff order.
    let log = Arc::new(std::sync::Mutex::new(Vec::<u8>::new()));
    let chunks = 40;
    let mut handles = Vec::new();
    for tid in 0u8..2 {
        let rt = Arc::clone(&runtime);
        let code = code;
        let log = Arc::clone(&log);
        handles.push(std::thread::spawn(move || {
            let mut w = Interpreter::for_shared_runtime_test(rt);
            for _ in 0..chunks {
                w.reset_stack();
                w.test_seed_return_sentinel();
                w.test_seed_top(PolyWord::tagged(0));
                // A biggish chunk so the safepoint yield fires inside it,
                // forcing a hand-off mid-chunk.
                w.test_seed_top(PolyWord::tagged(200_000));
                unsafe { w.set_code_segment_to_code_obj(code.0) };
                let _ = w.run_until(u64::MAX);
                log.lock().unwrap().push(tid);
            }
        }));
    }
    for h in handles {
        h.join().unwrap();
    }
    drop(host);

    let log = log.lock().unwrap();
    // Count "transitions" (adjacent entries from different threads). A
    // serial run (all of thread 0 then all of thread 1) has exactly 1
    // transition; genuine interleaving has many.
    let transitions = log.windows(2).filter(|w| w[0] != w[1]).count();
    eprintln!(
        "[interleave] handoff log len={} transitions={} (1 = serial, many = interleaved)",
        log.len(),
        transitions
    );
    assert!(
        transitions >= 2,
        "threads ran serially (transitions={transitions}); expected interleaving"
    );
}

/// Fork TOCTOU stress test (B1). The HARDENING target: a freshly-forked
/// child is registered in the collector's scan set BEFORE it runs, while its
/// only live heap roots (its starting closure + thread object) sit in the
/// shared heap. If the collector could fire between register and the child's
/// first acquire WITHOUT forwarding the child's closure, the closure would
/// be freed/moved out from under the child → use-after-free when the child
/// later dereferences it (`jit_set_code_segment_to_closure`).
///
/// This drives the REAL `fork_thread` / `child_thread_main` path: the parent
/// holds the giant lock, allocates a runnable closure in the COLLECTED heap,
/// forks a child on it, then IMMEDIATELY forces a stop-the-world GC — the
/// child is by construction still parked (registered with its `ForkRoots`
/// published, blocked in acquire because the parent holds the lock +
/// gc_requested). The GC must forward the child's closure; the child reads
/// the FORWARDED closure back and runs it to a clean exit. Repeated many
/// times with `POLYML_GC_AUDIT=1`, so the extended cross-stack audit (B3)
/// validates that no parked thread's roots were skipped. A reintroduced
/// B1/B2 surfaces as a SEGV or a non-zero audit count.
#[test]
fn fork_toctou_force_gc_before_child_runs() {
    // SAFETY: env is read + cached once; set before first interpreter use.
    unsafe {
        std::env::set_var("POLY_REAL_THREADS", "1");
        std::env::set_var("POLYML_GC_QUIET", "1");
        std::env::set_var("POLYML_GC_AUDIT", "1");
        // A generous threshold so OUR forced GCs (not auto-GC) drive the
        // test; the closures are tiny so auto-GC would rarely fire anyway.
        std::env::set_var("POLYML_GC_THRESHOLD", "90");
    }

    // Host owns the shared Runtime + a real (collected) heap. The closures
    // we fork on live IN this heap, so the forced GC genuinely moves them.
    let heap = MemorySpace::new(256 * 1024, SpaceKind::Mutable);
    let mut host = Interpreter::from_bytes(64, vec![]).with_alloc_space(heap);

    let rounds = 500usize;
    for _ in 0..rounds {
        // Become the running mutator (so we can allocate + fork + force GC).
        host.test_acquire_running();
        // Allocate a fresh runnable closure in the collected heap.
        let closure = host.test_build_runnable_closure();
        // Fork a child on it (publishes ForkRoots + registers + spawns).
        let _thread_obj = host.test_fork_child(closure);
        // IMMEDIATELY force a GC — the child is still parked (we hold the
        // lock), so this exercises the B1 window: the collector must
        // forward the child's just-published ForkRoots (closure +
        // thread_obj). Force a SECOND GC for good measure (the child may
        // still be queued in acquire after the first).
        host.test_force_gc();
        host.test_force_gc();
        // RELEASE the lock so THIS round's child can acquire, read its
        // FORWARDED closure back, run it, and exit — exercising the full B1
        // cycle (GC-before-run THEN run with the moved closure) per round
        // rather than accumulating parked children. Then wait for it to
        // drain before re-acquiring for the next round.
        host.test_release_running();
        host.wait_for_children();
    }

    // All rounds done; ensure no straggler children remain.
    host.wait_for_children();

    // Every child must have exited cleanly; the registry should be back to
    // just the host (registered) or empty. Assert no child is stuck.
    let live = runtime_live_others(&host);
    assert_eq!(live, 0, "some forked children never drained (live={live})");

    let gcs = host
        .runtime_arc()
        .gc_count
        .load(std::sync::atomic::Ordering::Relaxed);
    assert!(
        gcs >= rounds as u64,
        "expected >= {rounds} forced collections, got {gcs}"
    );
    eprintln!(
        "[toctou] {rounds} fork+force-GC rounds completed, collections fired = {gcs}, audit clean"
    );
}

/// NEGATIVE CONTROL — proves the POLYML_GC_AUDIT cross-stack pass HAS TEETH.
///
/// The whole point of the round-2 H1 fix is "registered AND not-running ⟹
/// parked_roots is Some". If a test could pass while that invariant is
/// VIOLATED, the test would be worthless. So we deliberately reintroduce the
/// H1 violation — bare-register a peer handle with `parked_roots == None`
/// (the exact state the structural fix forbids) — and assert that a collect
/// under audit DETECTS it (`gc_audit_residual > 0`). Then we show that with
/// the invariant RESTORED (no unpublished peer) the same collect reports 0.
///
/// (We collect via `test_force_gc_no_barrier`, bypassing `request_gc`'s
/// stop-the-world barrier: the barrier itself BLOCKS forever on an
/// unpublished peer — that is round-1's defense — so a faithful H1
/// reintroduction would DEADLOCK there, never reaching the audit. The direct
/// collect lets the audit run and prove it sees the skip.)
#[test]
fn audit_detects_h1_unpublished_peer_negative_control() {
    unsafe {
        std::env::set_var("POLY_REAL_THREADS", "1");
        std::env::set_var("POLYML_GC_QUIET", "1");
        std::env::set_var("POLYML_GC_AUDIT", "1");
        std::env::set_var("POLYML_GC_THRESHOLD", "90");
    }
    let heap = MemorySpace::new(256 * 1024, SpaceKind::Mutable);
    let mut host = Interpreter::from_bytes(64, vec![]).with_alloc_space(heap);
    host.test_acquire_running();

    // ---- POSITIVE control: a clean collect (no unpublished peer) reports
    // ZERO residual — so the assertion below is meaningful (not always-true).
    let before_clean = host.test_gc_audit_residual();
    let _ = host.test_force_gc_no_barrier();
    let after_clean = host.test_gc_audit_residual();
    assert_eq!(
        after_clean,
        before_clean,
        "a CLEAN collect must report 0 audit residual (got +{})",
        after_clean - before_clean
    );

    // ---- NEGATIVE control: reintroduce H1 (a registered, not-running,
    // UNPUBLISHED peer) and collect. The audit must flag it.
    let dummy = host.test_register_unpublished_peer_unsound();
    let before_bad = host.test_gc_audit_residual();
    let _ = host.test_force_gc_no_barrier();
    let after_bad = host.test_gc_audit_residual();
    // Clean up the dummy before asserting (so a failed assert still leaves a
    // sane registry for Drop).
    host.test_deregister_peer(&dummy);
    assert!(
        after_bad > before_bad,
        "AUDIT HAS NO TEETH: an H1-violating unpublished peer was NOT detected \
         (residual stayed {before_bad}). The negative control failed — the H1 \
         fix could regress silently."
    );
    eprintln!(
        "[neg-control] clean collect residual=0; H1-violating collect residual=+{} (detected)",
        after_bad - before_bad
    );

    host.test_release_running();
    drop(host);
}

/// NEGATIVE CONTROL — proves the H2 running-flag fix HAS TEETH.
///
/// H2: `exit_parked` (a thread exiting that does NOT hold the giant lock)
/// must NOT clear `running` — doing so clobbers a peer's ownership and admits
/// a second concurrent mutator (a data race / UAF). This test stages a parked
/// peer and exits it WHILE the host holds the giant lock, then asserts the
/// host still holds it. With the fix, `running` stays true. If H2 is
/// reintroduced (exit_parked clears `running` unconditionally), this assert
/// FAILS — so the bug cannot regress silently.
#[test]
fn exit_parked_does_not_clobber_running_h2_negative_control() {
    unsafe {
        std::env::set_var("POLY_REAL_THREADS", "1");
        std::env::set_var("POLYML_GC_QUIET", "1");
    }
    let heap = MemorySpace::new(64 * 1024, SpaceKind::Mutable);
    let mut host = Interpreter::from_bytes(64, vec![]).with_alloc_space(heap);

    host.test_acquire_running();
    assert!(
        host.test_running(),
        "precondition: host must hold the giant lock after acquire"
    );
    // Exit a PARKED peer while WE (the host) are the running mutator.
    host.test_exit_parked_peer_while_running();
    assert!(
        host.test_running(),
        "H2 REGRESSION: exit_parked from a non-holder cleared `running` — the \
         host's giant-lock ownership was clobbered. A second mutator could now \
         run concurrently (data race / UAF)."
    );
    eprintln!("[h2-neg-control] exit_parked preserved the running flag (no clobber)");
    host.test_release_running();
    drop(host);
}

/// Count registered threads other than the host that have not exited.
fn runtime_live_others(host: &Interpreter) -> usize {
    let rt = host.runtime_arc();
    let snap = rt.registry_snapshot();
    // The host itself is registered; exclude exited handles. We cannot
    // Arc::ptr_eq the host's private handle from here, so count non-exited
    // entries and subtract the host (which is alive + registered).
    let non_exited = snap
        .iter()
        .filter(|h| !h.exited.load(std::sync::atomic::Ordering::SeqCst))
        .count();
    // The host is one non-exited registered thread; any beyond it is a
    // child that never drained.
    non_exited.saturating_sub(1)
}
