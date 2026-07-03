//! Seeded concurrency FUZZER — randomized fork/compute/alloc/mutex/
//! condvar/kill/interrupt storms against the real-threads runtime,
//! reproducible by seed.
//!
//! Every generated driver is built so that CLEAN COMPLETION IS DECIDABLE
//! (the oracle stays sharp — every failure is a real finding):
//!
//! - Threads are PARTITIONED by role. "Chaos victims" do pure compute +
//!   allocation and may be killed/interrupted at any moment. "Lock users"
//!   exercise mutexes + condition variables but are NEVER kill targets —
//!   an asynchronous kill landing inside a critical section strands the
//!   mutex forever (upstream semantics too), which would make the
//!   expected outcome undefined.
//! - The MAIN thread never blocks on anything a dead thread was supposed
//!   to signal: it polls `Thread.isActive` over every forked thread with
//!   a bounded spin, then prints its verdict. Kills cannot hang the join.
//! - Lock users' critical sections always release (no kill exposure), so
//!   their shared counter has an EXACT expected value — a lost update is
//!   a mutex-atomicity bug, not noise.
//!
//! Each seed runs with a LOW GC threshold + `POLYML_GC_AUDIT=1`, so
//! collections fire constantly under the storm and every root set is
//! re-walked after each one. PASS = `FUZZ_DONE` + the exact lock-counter
//! line + no panic / no `GC AUDIT` residual / no `GC invariant` line /
//! clean exit, within the timeout. A failing seed prints its driver path
//! for immediate reproduction.
//!
//! Seeds rotate: `FUZZ_BASE` (default 1) and `FUZZ_COUNT` (default 12
//! per mode) env vars — nightly CI can sweep a different window each run
//! (`FUZZ_BASE=$(date +%j)` style).
//!
//! `#[ignore]` — needs `vendor/polyml/polyexport` (self-bootstrap first):
//! ```sh
//! cargo test --release -p polyml-bin --test concurrency_fuzz -- --ignored --nocapture
//! ```

mod common;
use common::run_image_env;
use std::fmt::Write as _;
use std::path::PathBuf;

fn polyexport() -> Option<PathBuf> {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../vendor/polyml/polyexport");
    p.canonicalize().ok().filter(|p| p.exists())
}

/// Deterministic LCG (same constants as the diff-corpus fuzz drivers).
struct Lcg(u64);
impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1))
    }
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 11
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// Generate one storm driver from a seed. Returns (sml, expected_lock_total).
fn generate(seed: u64) -> (String, u64) {
    let mut r = Lcg::new(seed);

    let n_victims = 1 + r.below(3); // 1..=3 killable compute/alloc threads
    let n_lockers = 1 + r.below(3); // 1..=3 mutex/condvar users (never killed)
    let n_chaos = 1 + r.below(2); // 1..=2 kill/interrupt storm threads
    let locker_rounds = 200 + r.below(800); // exact-count work per locker
    let victim_iters = 20_000 + r.below(80_000);
    let chaos_shots = 10 + r.below(40);
    let expected_total = n_lockers * locker_rounds;

    let mut s = String::new();
    let _ = write!(
        s,
        "(* concurrency fuzz driver, seed {seed}: {n_victims} victims, \
         {n_lockers} lockers x {locker_rounds}, {n_chaos} chaos x {chaos_shots} *)\n\
         structure T = Thread.Thread;\n\
         structure M = Thread.Mutex;\n\
         structure C = Thread.ConditionVar;\n\
         val m = M.mutex ();\n\
         val cv = C.conditionVar ();\n\
         val total = ref 0;\n\
         fun spin (acc, 0) = acc | spin (acc, k) = spin ((acc * 31 + 7) mod 1000003, k - 1);\n\
         fun mk (0, acc) = acc | mk (k, acc) = mk (k - 1, k :: acc);\n"
    );

    // Victims: pure compute + allocation, immortal-loop-free (bounded),
    // fair game for kill/interrupt. Their result is NOT part of the
    // oracle (they may die at any point) — they exist to be storm targets
    // while allocating across constant GCs.
    let _ = write!(
        s,
        "fun victim () =\n\
         \x20 let fun go 0 = () | go n = (ignore (spin (n, 50)); ignore (length (mk (40, []))); go (n - 1))\n\
         \x20 in go {victim_iters} end;\n"
    );

    // Lockers: exact-count mutex work + occasional bounded condvar waits.
    // Never killed, so the critical sections always release and the final
    // total is EXACT.
    let cv_every = 50 + r.below(150);
    let _ = write!(
        s,
        "fun locker () =\n\
         \x20 let fun go 0 = () | go n =\n\
         \x20   (M.lock m; total := !total + 1;\n\
         \x20    if n mod {cv_every} = 0 then ignore (C.waitUntil (cv, m, Time.+ (Time.now (), Time.fromMilliseconds 2))) else ();\n\
         \x20    C.signal cv; M.unlock m;\n\
         \x20    ignore (length (mk (20, [])));\n\
         \x20    go (n - 1))\n\
         \x20 in go {locker_rounds} end;\n"
    );

    // Fork victims FIRST (they are the storm targets), keep their thread
    // objects for the chaos threads to aim at. Victims run ASYNCH so
    // interrupts genuinely land mid-compute (the default Synch state
    // would defer them forever on a thread that never blocks — the
    // interrupt axis of the storm would be a no-op).
    let _ = write!(
        s,
        "val victims = List.tabulate ({n_victims}, fn _ => T.fork (victim, [T.InterruptState T.InterruptAsynch]));\n\
         val lockers = List.tabulate ({n_lockers}, fn _ => T.fork (locker, []));\n"
    );

    // Chaos threads: interrupt + kill the victims (only) at random-ish
    // cadence. Dead-target exceptions are expected and swallowed.
    let kill_mode = r.below(3); // 0: interrupts only, 1: kills only, 2: both
    let _ = write!(
        s,
        "fun chaos () =\n\
         \x20 let fun shot (t, k) =\n\
         \x20       (ignore (spin (k, 2000));\n\
         \x20        {};\n\
         \x20        {})\n\
         \x20     fun go 0 = () | go n =\n\
         \x20       (List.app (fn t => shot (t, n)) victims; go (n - 1))\n\
         \x20 in go {chaos_shots} end;\n\
         val chaosT = List.tabulate ({n_chaos}, fn _ => T.fork (chaos, []));\n",
        if kill_mode != 1 {
            "((T.interrupt t) handle _ => ())"
        } else {
            "()"
        },
        if kill_mode != 0 {
            "((T.kill t) handle _ => ())"
        } else {
            "()"
        },
    );

    // Main: poll isActive over EVERYTHING with a bounded spin — no wait
    // depends on a possibly-dead thread. Then the exact-count verdict.
    let _ = write!(
        s,
        "fun anyActive [] = false | anyActive (t :: ts) = ((T.isActive t) handle _ => false) orelse anyActive ts;\n\
         fun drain 0 = () | drain n =\n\
         \x20 (if anyActive (victims @ lockers @ chaosT) then (ignore (spin (n, 20000)); drain (n - 1)) else ());\n\
         val () = drain 200000;\n\
         val () = print (\"lock total = \" ^ Int.toString (!total) ^ \" (expect {expected_total})\\n\");\n\
         val () = print (if !total = {expected_total} then \"LOCK_EXACT\\n\" else \"LOCK_WRONG\\n\");\n\
         val () = print \"FUZZ_DONE\\n\";\n"
    );

    (s, expected_total)
}

/// Run one seed in one mode; return an error description on any failure.
fn run_seed(image: &std::path::Path, seed: u64, parallel: bool) -> Result<(), String> {
    let (sml, _expected) = generate(seed);
    // FUZZ_DUMP=1: save every generated driver (not just failures) so it
    // can be replayed under other binaries — e.g. the TSan-instrumented
    // interpreter-only poly.
    if std::env::var("FUZZ_DUMP").is_ok_and(|v| v == "1") {
        let _ = std::fs::write(format!("/tmp/fuzz_dump_seed_{seed}.sml"), &sml);
    }
    let mut envs: Vec<(&str, &str)> = vec![
        ("POLY_REAL_THREADS", "1"),
        // Storm under constant, audited collections.
        ("POLYML_GC_THRESHOLD", "5"),
        ("POLYML_GC_AUDIT", "1"),
        ("POLYML_GC_QUIET", "1"),
    ];
    if parallel {
        envs.push(("POLY_PARALLEL", "1"));
    }
    let mode = if parallel { "parallel" } else { "giant" };

    let Some((out, code)) = run_image_env(image, &sml, 120_000_000_000, &envs) else {
        return Err(format!("seed {seed} [{mode}]: poly could not spawn"));
    };

    let fail = |why: &str, out: &str| -> Result<(), String> {
        // Bank the reproducer.
        let path = format!("/tmp/fuzz_seed_{seed}_{mode}.sml");
        let _ = std::fs::write(&path, &sml);
        Err(format!(
            "seed {seed} [{mode}]: {why} (driver saved to {path}, exit={code})\n\
             --- output ---\n{out}"
        ))
    };

    if !out.contains("FUZZ_DONE") {
        return fail("did not complete (hang/crash before FUZZ_DONE)", &out);
    }
    if !out.contains("LOCK_EXACT") {
        return fail("mutex exact-count VIOLATED (lost update under storm)", &out);
    }
    if out.contains("GC AUDIT") {
        return fail("GC audit residual under storm", &out);
    }
    if out.contains("GC invariant violated") || out.contains("panicked") {
        return fail("GC invariant violation / Rust panic", &out);
    }
    Ok(())
}

fn fuzz_env(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|s| s.trim().parse().ok())
        .unwrap_or(default)
}

#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn fuzz_storms_giant_lock() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let base = fuzz_env("FUZZ_BASE", 1);
    let count = fuzz_env("FUZZ_COUNT", 12);
    let mut failures = Vec::new();
    for seed in base..base + count {
        match run_seed(&image, seed, false) {
            Ok(()) => eprintln!("[fuzz giant] seed {seed} OK"),
            Err(e) => {
                eprintln!("[fuzz giant] {e}");
                failures.push(e);
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {count} giant-lock storm seeds FAILED:\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}

#[test]
#[ignore = "needs vendor/polyml/polyexport (self-bootstrap the 7-stage chain first)"]
fn fuzz_storms_parallel() {
    let Some(image) = polyexport() else {
        eprintln!("SKIP: vendor/polyml/polyexport missing (self-bootstrap first)");
        return;
    };
    let base = fuzz_env("FUZZ_BASE", 1);
    let count = fuzz_env("FUZZ_COUNT", 12);
    let mut failures = Vec::new();
    for seed in base..base + count {
        match run_seed(&image, seed, true) {
            Ok(()) => eprintln!("[fuzz parallel] seed {seed} OK"),
            Err(e) => {
                eprintln!("[fuzz parallel] {e}");
                failures.push(e);
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {count} parallel storm seeds FAILED:\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}
