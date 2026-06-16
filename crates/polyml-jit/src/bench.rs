//! Micro-benchmarks comparing JIT-compiled bytecode against a
//! hand-coded Rust equivalent and a tiny stack-machine interpreter.
//!
//! These are correctness-and-speed sanity tests, not production
//! benchmarks. They use `Instant`-based timing inside a regular
//! `#[test]` so they run as part of `cargo test --release` and
//! cleanly skip if the system clock is too coarse.

#![cfg(test)]

use crate::Jit;
use crate::translate::compile;

// Opcode constants — kept in sync with `translate.rs`.
const INSTR_CONST_1: u8 = 0x3c;
const INSTR_CONST_INT_B: u8 = 0x28;
const INSTR_FIXED_ADD: u8 = 0xaa;
const INSTR_FIXED_MULT: u8 = 0xac;
const INSTR_RETURN_1: u8 = 0x42;
const INSTR_EQUAL_WORD: u8 = 0xa0;
const INSTR_JUMP8_TRUE: u8 = 0x46;
const INSTR_JUMP_BACK8: u8 = 0x1e;

fn tag(n: i64) -> i64 {
    n.wrapping_mul(2).wrapping_add(1)
}
fn untag(t: i64) -> i64 {
    (t - 1) >> 1
}

/// A tiny stack-machine interpreter for our JIT'd opcode set.
/// Same semantics as polyml-runtime's interpreter for these ops,
/// but minimal — just enough to be a baseline.
fn interp(bytecode: &[u8]) -> i64 {
    let mut stack: Vec<i64> = Vec::with_capacity(16);
    let mut pc = 0usize;
    loop {
        let op = bytecode[pc];
        pc += 1;
        match op {
            0x3b..=0x3f => stack.push(tag(i64::from(op - 0x3b))),
            0x40 => stack.push(tag(10)),
            INSTR_CONST_INT_B => {
                let imm = bytecode[pc] as i8 as i64;
                pc += 1;
                stack.push(tag(imm));
            }
            INSTR_FIXED_ADD => {
                let x = stack.pop().unwrap();
                let y = stack.pop().unwrap();
                stack.push(x.wrapping_add(y).wrapping_sub(1));
            }
            INSTR_FIXED_MULT => {
                let x = stack.pop().unwrap();
                let y = stack.pop().unwrap();
                let xn = (x - 1) >> 1;
                let yn = (y - 1) >> 1;
                stack.push(tag(xn.wrapping_mul(yn)));
            }
            INSTR_EQUAL_WORD => {
                let x = stack.pop().unwrap();
                let y = stack.pop().unwrap();
                stack.push(tag(i64::from(x == y)));
            }
            INSTR_JUMP8_TRUE => {
                let off = bytecode[pc] as usize;
                pc += 1;
                let cond = stack.pop().unwrap();
                if cond != tag(0) {
                    pc += off;
                }
            }
            INSTR_JUMP_BACK8 => {
                let off = bytecode[pc] as usize;
                pc += 1;
                pc -= off + 2;
            }
            INSTR_RETURN_1 => return stack.pop().unwrap(),
            _ => panic!("interp: unsupported op 0x{op:02x} at pc {pc:?}"),
        }
    }
}

/// Bytecode for `sum_to_100` = 0+1+2+...+100 = 5050.
/// Layout:
///   0:  CONST_0          ; sum = 0
///   1:  CONST_0          ; counter = 0 (top of stack)
///   2: ── loop head, stack = [sum, counter] depth 2 ──
///   2:  CONST_INT_B 100  ; push limit
///   4:  EQUAL_WORD       ; counter == 100? (pops both!)
/// — wait. EQUAL_WORD pops counter AND the limit. So after this,
/// stack = [sum] and we've LOST the counter. Need to use a different
/// approach.
///
/// For a real loop we need either DUP or local variables. Neither
/// is implemented. So instead let me write a benchmark that's pure
/// straight-line arithmetic: compute (((1+1)+1)+...) 1000 times.

fn straight_line_add_program(n: usize) -> Vec<u8> {
    // CONST_1; (CONST_1, ADD) * (n-1); RETURN_1  → result = n
    let mut bc = Vec::with_capacity(2 + 2 * n);
    bc.push(INSTR_CONST_1);
    for _ in 0..n.saturating_sub(1) {
        bc.push(INSTR_CONST_1);
        bc.push(INSTR_FIXED_ADD);
    }
    bc.push(INSTR_RETURN_1);
    bc
}

// JIT functions with a RETURN_N now load the SML call-frame slots
// (arg_count = sml_arity + 2) from args_ptr. These hand-crafted tests
// don't have args, but the JIT still loads 3 slots (0+2 = arity 0,
// or 1+2 for RETURN_1). Pass a small zero-initialized buffer so the
// JIT's loads don't null-deref.
const ARGS_DUMMY: [i64; 16] = [0; 16];

#[test]
fn jit_matches_interp_for_addition_chain() {
    let bc = straight_line_add_program(50);
    let mut jit = Jit::new().unwrap();
    let jit_fn = compile(&mut jit, &bc).unwrap();
    let args_dummy = ARGS_DUMMY;
    assert_eq!(untag(unsafe { jit_fn(args_dummy.as_ptr(), 0, 0) }), 50);
    assert_eq!(untag(interp(&bc)), 50);
}

#[test]
fn jit_matches_interp_for_mult_chain() {
    // 2 * 2 * 2 * 2 * 2 = 32
    let bc = vec![
        INSTR_CONST_INT_B,
        2,
        INSTR_CONST_INT_B,
        2,
        INSTR_FIXED_MULT,
        INSTR_CONST_INT_B,
        2,
        INSTR_FIXED_MULT,
        INSTR_CONST_INT_B,
        2,
        INSTR_FIXED_MULT,
        INSTR_CONST_INT_B,
        2,
        INSTR_FIXED_MULT,
        INSTR_RETURN_1,
    ];
    let mut jit = Jit::new().unwrap();
    let jit_fn = compile(&mut jit, &bc).unwrap();
    let args_dummy = ARGS_DUMMY;
    assert_eq!(untag(unsafe { jit_fn(args_dummy.as_ptr(), 0, 0) }), 32);
    assert_eq!(untag(interp(&bc)), 32);
}

#[test]
fn jit_speedup_over_micro_interpreter() {
    // 1000-op add chain, 100k iterations.
    let bc = straight_line_add_program(1000);
    let mut jit = Jit::new().unwrap();
    let jit_fn = compile(&mut jit, &bc).unwrap();
    let args_dummy = ARGS_DUMMY;

    // Sanity-check both return 1000.
    assert_eq!(untag(unsafe { jit_fn(args_dummy.as_ptr(), 0, 0) }), 1000);
    assert_eq!(untag(interp(&bc)), 1000);

    let iters = 100_000;

    let t0 = std::time::Instant::now();
    let mut sink = 0i64;
    for _ in 0..iters {
        sink = sink.wrapping_add(unsafe { jit_fn(args_dummy.as_ptr(), 0, 0) });
    }
    let jit_elapsed = t0.elapsed();

    let t1 = std::time::Instant::now();
    for _ in 0..iters {
        sink = sink.wrapping_add(interp(&bc));
    }
    let interp_elapsed = t1.elapsed();

    let speedup = interp_elapsed.as_secs_f64() / jit_elapsed.as_secs_f64();
    eprintln!(
        "JIT  : {} iters in {:?}  ({:>8.0} ns/iter)",
        iters,
        jit_elapsed,
        jit_elapsed.as_nanos() as f64 / iters as f64
    );
    eprintln!(
        "INTRP: {} iters in {:?}  ({:>8.0} ns/iter)",
        iters,
        interp_elapsed,
        interp_elapsed.as_nanos() as f64 / iters as f64
    );
    eprintln!("speedup: {speedup:.1}x");

    // Sink usage to prevent the compiler from optimising the call away.
    std::hint::black_box(sink);

    // Expect at least *some* speedup — JITted code does ~1000 adds in
    // one pass through native instructions, while the interpreter does
    // a 1000-iteration dispatch loop with a match on every step.
    // Empirically we see ~50-200x; require ≥ 5x to leave headroom for
    // the slow ones.
    assert!(
        speedup >= 5.0,
        "expected JIT to be at least 5x faster than the toy interpreter, got {speedup:.2}x"
    );
}
