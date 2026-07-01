//! Differential CASE16 test: a hand-built jump-table function must
//! produce the SAME result under the JIT and the interpreter for every
//! selector value (each in-range case AND the out-of-range default).
//!
//! This is the correctness gate for the CASE16 CFG depth-propagation
//! fix: the JIT now translates CASE16-containing functions, so we must
//! prove the translation is semantically faithful, not just that it
//! compiles.

use polyml_jit::{Jit, differential, translate};
use polyml_runtime::{Interpreter, PolyWord, StepResult};

const INSTR_LOCAL_2: u8 = 0x2b;
const INSTR_CASE16: u8 = 0x0a;
const INSTR_CONST_INT_B: u8 = 0x28;
const INSTR_RETURN_1: u8 = 0x42;

/// `\sel -> case sel of 0 => 11 | 1 => 22 | _ => 99`
///
/// Layout (byte offsets):
///   0: LOCAL_2                    ; push selector (arg_0)
///   1: CASE16 arg1=2              ; pops selector
///   2-3: 02 00                    ; arg1 = 2
///   4-5: off0 (u16 LE) = 7        ; case0 -> table_start(4)+7 = 11
///   6-7: off1 (u16 LE) = 10       ; case1 -> table_start(4)+10 = 14
///   8: CONST_INT_B 99 ; RETURN_1  ; default body (= table_start+arg1*2 = 8)
///  11: CONST_INT_B 11 ; RETURN_1  ; case0 body
///  14: CONST_INT_B 22 ; RETURN_1  ; case1 body
fn case16_bytecode() -> Vec<u8> {
    vec![
        INSTR_LOCAL_2,
        INSTR_CASE16,
        0x02,
        0x00, // arg1 = 2
        0x07,
        0x00, // off0 = 7  -> case0 @ 11
        0x0a,
        0x00, // off1 = 10 -> case1 @ 14
        // default body @ 8
        INSTR_CONST_INT_B,
        99,
        INSTR_RETURN_1,
        // case0 body @ 11
        INSTR_CONST_INT_B,
        11,
        INSTR_RETURN_1,
        // case1 body @ 14
        INSTR_CONST_INT_B,
        22,
        INSTR_RETURN_1,
    ]
}

fn run_interp(bc: &[u8], selector: i64) -> i64 {
    let mut interp = Interpreter::from_bytes(64, bc.to_vec());
    interp.seed_return_sentinel();
    interp.seed_push(PolyWord::from_bits(selector as usize)); // arg_0 = selector
    interp.seed_push(PolyWord::from_bits(0)); // retPC
    interp.seed_push(PolyWord::from_bits(0)); // closure
    loop {
        match interp.step() {
            Ok(StepResult::Continue) => continue,
            Ok(StepResult::Returned(v)) => break v.0 as i64,
            other => panic!("interp: {other:?}"),
        }
    }
}

#[test]
fn case16_jit_matches_interp_all_selectors() {
    let bc = case16_bytecode();

    // It must actually translate now.
    let mut jit = Jit::new().unwrap();
    let f = translate::compile(&mut jit, &bc).expect("CASE16 must translate");

    // Expected: 0->11, 1->22, anything else (incl. out-of-range and
    // negative)->99.
    let cases: &[(i64, i64)] = &[
        (0, 11),
        (1, 22),
        (2, 99), // out of range high
        (5, 99),
        (-1, 99), // out of range negative
        (100, 99),
    ];

    for &(sel, want) in cases {
        let arg = differential::tag(sel);
        let interp_result = run_interp(&bc, arg);
        let args_buf = [arg, 0, 0];
        let jit_result = unsafe { f(args_buf.as_ptr(), 0, 0) };
        assert_eq!(
            interp_result, jit_result,
            "JIT/interp diverged for selector {sel}: interp={interp_result:#x} jit={jit_result:#x}",
        );
        assert_eq!(
            differential::untag(jit_result),
            want,
            "selector {sel}: expected {want}",
        );
    }
}
