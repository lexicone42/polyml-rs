//! Coarse comparison: interpreter vs JIT for self-contained
//! arithmetic functions. Not a real benchmark crate — just a
//! demonstrator that the JIT'd code is faster (it should be, by
//! a large factor) and produces the same result.
//!
//! Run with: `cargo test --release -p polyml-jit --test jit_speedup_bench -- --nocapture`

use polyml_jit::{translate, Jit};
use polyml_runtime::{Interpreter, StepResult, PolyWord};
use std::time::Instant;

const INSTR_LOCAL_2: u8 = 0x2b;
const INSTR_CONST_1: u8 = 0x3c;
const INSTR_CONST_INT_B: u8 = 0x28;
const INSTR_FIXED_ADD: u8 = 0xaa;
const INSTR_FIXED_MULT: u8 = 0xac;
const INSTR_RETURN_1: u8 = 0x42;

fn tag(n: i64) -> i64 {
    2 * n + 1
}
fn untag(t: i64) -> i64 {
    assert_eq!(t & 1, 1, "expected tagged, got {t}");
    (t - 1) >> 1
}

/// Run bytecode via the interpreter for an arity-1 function.
/// Returns (result, elapsed_nanos).
fn run_interp(bytecode: &[u8], arg0: i64) -> (i64, u128) {
    let start = Instant::now();
    let mut interp = Interpreter::from_bytes(64, bytecode.to_vec());
    interp.test_seed_return_sentinel();
    interp.test_seed_top(PolyWord::from_bits(arg0 as usize));
    interp.test_seed_top(PolyWord::from_bits(0)); // retPC
    interp.test_seed_top(PolyWord::from_bits(0)); // closure
    let result = loop {
        match interp.step() {
            Ok(StepResult::Continue) => continue,
            Ok(StepResult::Returned(v)) => break v.0 as i64,
            other => panic!("interp: {other:?}"),
        }
    };
    (result, start.elapsed().as_nanos())
}

/// Run bytecode via the JIT — measures compile + execute together
/// when called fresh; pass `pre_compiled` for execute-only measurement.
fn run_jit(jit_fn: translate::JitFn, arg0: i64) -> (i64, u128) {
    let start = Instant::now();
    let args = [arg0, 0i64, 0i64];
    let result = unsafe { jit_fn(args.as_ptr()) };
    (result, start.elapsed().as_nanos())
}

#[test]
fn arithmetic_function_jit_matches_interp_and_is_faster() {
    // f(x) = (x + 1) * 2 + 5
    let bc = vec![
        INSTR_LOCAL_2,
        INSTR_CONST_1,
        INSTR_FIXED_ADD,
        INSTR_CONST_INT_B,
        2,
        INSTR_FIXED_MULT,
        INSTR_CONST_INT_B,
        5,
        INSTR_FIXED_ADD,
        INSTR_RETURN_1,
    ];
    let mut jit = Jit::new().unwrap();
    let jit_fn = translate::compile(&mut jit, &bc).expect("compile");

    // Sanity: same result.
    for x in [0i64, 1, 5, 10, -3, 100] {
        let (interp_result, _) = run_interp(&bc, tag(x));
        let (jit_result, _) = run_jit(jit_fn, tag(x));
        let expected = (x + 1) * 2 + 5;
        assert_eq!(untag(interp_result), expected, "interp f({x})");
        assert_eq!(untag(jit_result), expected, "jit f({x})");
    }

    // Time many runs.
    const ITERS: usize = 100_000;
    let interp_start = Instant::now();
    for _ in 0..ITERS {
        let _ = run_interp(&bc, tag(42));
    }
    let interp_total_ns = interp_start.elapsed().as_nanos();

    let jit_start = Instant::now();
    for _ in 0..ITERS {
        let _ = run_jit(jit_fn, tag(42));
    }
    let jit_total_ns = jit_start.elapsed().as_nanos();

    let interp_per = interp_total_ns / ITERS as u128;
    let jit_per = jit_total_ns / ITERS as u128;
    eprintln!("Interp: {interp_total_ns} ns total, {interp_per} ns/call");
    eprintln!("JIT:    {jit_total_ns} ns total, {jit_per} ns/call");
    if jit_per > 0 {
        eprintln!("Speedup: {:.2}x", interp_per as f64 / jit_per as f64);
    }

    // The JIT should be substantially faster — the interpreter has
    // to fetch+decode+dispatch each opcode, while the JIT runs
    // straight-line native code.
    assert!(
        jit_per < interp_per,
        "JIT ({jit_per} ns) should be faster than interp ({interp_per} ns)"
    );
}
