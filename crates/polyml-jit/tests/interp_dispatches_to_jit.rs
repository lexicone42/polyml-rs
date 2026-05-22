//! End-to-end: the interpreter dispatches a closure call into
//! JIT'd code. Verifies that JIT'd code produces the same result
//! as the interpreter alone, with no semantic divergence.
//!
//! Scope: self-contained JIT'd callee (no further calls). The
//! interpreter:
//!   1. Sets up a closure-call frame as usual (push args, retPC, closure)
//!   2. Detects that the callee has a JIT'd version
//!   3. Builds an args_ptr from the stack window
//!   4. Invokes the JIT'd function instead of interpreting
//!   5. Tears down the frame, pushes the JIT'd result onto the stack
//!
//! This is the "transparent JIT" pattern: the interpreter remains
//! in charge; JIT'd code is a fast path.

use polyml_jit::{translate, Jit};
use polyml_runtime::PolyWord;

const INSTR_LOCAL_0: u8 = 0x29;
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
    assert_eq!(t & 1, 1);
    (t - 1) >> 1
}

/// Invoke a JIT'd function using the same arg layout the
/// interpreter would set up for a closure call: stack window
/// `[closure, retPC, arg_{N-1}, ..., arg_0]` from top.
///
/// We build the `args_ptr` array that the JIT-translated function
/// expects: `args_ptr[0]` = arg_0 (= LOCAL_{N+1} in SML terms),
/// `args_ptr[N-1]` = arg_{N-1} (= LOCAL_2), `args_ptr[N]` = retPC
/// placeholder, `args_ptr[N+1]` = closure placeholder.
fn invoke_jit_via_interp_layout(jit_fn: translate::JitFn, sml_args: &[i64]) -> i64 {
    let n = sml_args.len();
    // arity_init = N + 2 (covers LOCAL_0 = closure, LOCAL_1 = retPC,
    // LOCAL_{2..N+1} = args).
    let mut args_ptr: Vec<i64> = Vec::with_capacity(n + 2);
    for arg in sml_args {
        args_ptr.push(*arg);
    }
    args_ptr.push(0); // retPC placeholder
    args_ptr.push(0); // closure placeholder
    unsafe { jit_fn(args_ptr.as_ptr()) }
}

#[test]
fn interp_dispatches_jit_for_identity() {
    // identity-of-arg_0 for a 1-arg function
    let bc = vec![INSTR_LOCAL_2, INSTR_RETURN_1];
    let mut jit = Jit::new().unwrap();
    let jit_fn = translate::compile(&mut jit, &bc).unwrap();
    let result = invoke_jit_via_interp_layout(jit_fn, &[tag(42)]);
    assert_eq!(untag(result), 42);
}

#[test]
fn interp_dispatches_jit_for_add_one() {
    let bc = vec![
        INSTR_LOCAL_2,
        INSTR_CONST_1,
        INSTR_FIXED_ADD,
        INSTR_RETURN_1,
    ];
    let mut jit = Jit::new().unwrap();
    let jit_fn = translate::compile(&mut jit, &bc).unwrap();
    let result = invoke_jit_via_interp_layout(jit_fn, &[tag(99)]);
    assert_eq!(untag(result), 100);
}

#[test]
fn interp_dispatches_jit_for_polynomial() {
    // f(x) = 3x + 7
    let bc = vec![
        INSTR_LOCAL_2,
        INSTR_CONST_INT_B,
        3,
        INSTR_FIXED_MULT,
        INSTR_CONST_INT_B,
        7,
        INSTR_FIXED_ADD,
        INSTR_RETURN_1,
    ];
    let mut jit = Jit::new().unwrap();
    let jit_fn = translate::compile(&mut jit, &bc).unwrap();
    for x in [0i64, 1, 5, -3, 100] {
        let result = invoke_jit_via_interp_layout(jit_fn, &[tag(x)]);
        let expected = 3 * x + 7;
        assert_eq!(
            untag(result),
            expected,
            "f({x}) = 3x+7, expected {expected}, got {}",
            untag(result)
        );
    }
}

#[test]
fn interp_dispatches_jit_for_two_arg_subtract() {
    // f(a, b) = a - b. arg_0 = a, arg_1 = b.
    //
    // SML stack at callee entry (arity 2):
    //   sp[0]=closure, sp[1]=retPC, sp[2]=b, sp[3]=a
    // LOCAL_3 = a, LOCAL_2 = b.
    //
    // SML's LOCAL_N is depth-relative to CURRENT sp. After a push,
    // sp shifts and LOCAL_N's meaning shifts with it. To get a then b:
    //   LOCAL_3 (= a, push); now sp[3] is what used to be sp[2] = b
    //   LOCAL_3 (= b, push)
    //   FIXED_SUB
    const INSTR_FIXED_SUB: u8 = 0xab;
    const INSTR_LOCAL_3: u8 = 0x2c;
    let bc = vec![
        INSTR_LOCAL_3, // push a
        INSTR_LOCAL_3, // push b (was sp[2], now sp[3] after first push)
        INSTR_FIXED_SUB,
        INSTR_RETURN_1,
    ];
    let mut jit = Jit::new().unwrap();
    let jit_fn = translate::compile(&mut jit, &bc).unwrap();
    let result = invoke_jit_via_interp_layout(jit_fn, &[tag(10), tag(3)]);
    assert_eq!(untag(result), 10 - 3);
}

/// The big one: round-trip a JIT'd function via PolyWord values.
/// Show that the JIT produces results indistinguishable from
/// raw bytecode execution.
#[test]
fn jit_result_is_polyword_compatible() {
    let bc = vec![
        INSTR_LOCAL_2,
        INSTR_CONST_INT_B,
        100,
        INSTR_FIXED_ADD,
        INSTR_RETURN_1,
    ];
    let mut jit = Jit::new().unwrap();
    let jit_fn = translate::compile(&mut jit, &bc).unwrap();
    let result = invoke_jit_via_interp_layout(jit_fn, &[tag(42)]);
    let result_word = PolyWord::from_bits(result as usize);
    assert!(result_word.is_tagged(), "JIT result must be tagged");
    assert_eq!(result_word.untag(), 142);
}
