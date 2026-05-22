//! End-to-end test: JIT-compile a hand-built SML-style bytecode
//! function, then run it BOTH via the interpreter AND via the JIT,
//! verifying both produce the same result.
//!
//! This pins down the "JIT actually executes correctly" claim for
//! self-contained functions (no closure calls, no allocations).
//! Closure-call dispatch lives in a follow-up test once the real
//! trampoline is wired up.

use polyml_jit::{translate, Jit};
use polyml_runtime::{Interpreter, PolyWord};

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
    assert_eq!(t & 1, 1, "expected tagged int, got raw {t}");
    (t - 1) >> 1
}

/// Run bytecode via the JIT for an SML-arity-1 function.
///
/// JIT calling convention: args_ptr[0] becomes stack[0] (bottom);
/// args_ptr[arg_count-1] becomes stack[top]. LOCAL_N reads
/// `stack[stack.len() - 1 - N]`, so LOCAL_2 reads args_ptr[0]
/// (i.e. arg_0 sits at args_ptr[0]).
///
/// For an arity-1 SML function where LOCAL_2 = arg_0:
///   args_ptr[0] = arg_0
///   args_ptr[1] = retPC placeholder
///   args_ptr[2] = closure placeholder
fn run_jit_arity1(bytecode: &[u8], arg0: i64) -> i64 {
    let mut jit = Jit::new().unwrap();
    let f = translate::compile(&mut jit, bytecode).expect("translate");
    let args = [arg0, 0i64, 0i64];
    unsafe { f(args.as_ptr()) }
}

/// Run the same bytecode via the interpreter. Stack is seeded with
/// [closure, retPC, arg_0] as the JIT-callable shape; we use raw
/// from_bytes which doesn't push frames — for self-contained code
/// without RETURN-unwinding-into-frame logic, RETURN_1 just halts
/// with the result on top.
fn run_interp_arity1(bytecode: &[u8], arg0: i64) -> i64 {
    let mut interp = Interpreter::from_bytes(64, bytecode.to_vec());
    // Use raw test seeders so the stack matches the JIT shape.
    // Build the stack from below: arg_0 first, then retPC, then closure.
    interp.test_seed_return_sentinel();
    interp.test_seed_top(PolyWord::from_bits(arg0 as usize));
    // For the interpreter, LOCAL_0 reads sp[0], so the interp expects
    // sp[0] = arg_0 if we want LOCAL_2 to read past retPC + closure.
    // We need to also push placeholders for retPC and closure ABOVE the arg.
    // Actually `test_seed_top` puts arg at sp[0]; we want it at sp[2].
    // Push two placeholders above it (= more recent pushes).
    interp.test_seed_top(PolyWord::from_bits(0)); // retPC slot at sp[1]
    interp.test_seed_top(PolyWord::from_bits(0)); // closure slot at sp[0]
    // Now run until RETURN_1 fires. The interp's RETURN_1 expects to
    // pop closure + retPC + 1 arg, leaving the result on top.
    loop {
        match interp.step() {
            Ok(polyml_runtime::StepResult::Continue) => continue,
            Ok(polyml_runtime::StepResult::Returned(v)) => return v.0 as i64,
            Ok(other) => panic!("unexpected step result: {other:?}"),
            Err(e) => panic!("interp error: {e:?}"),
        }
    }
}

#[test]
fn jit_and_interp_agree_on_identity_arg() {
    // Bytecode: LOCAL_2 (= arg_0); RETURN_1
    let bc = vec![INSTR_LOCAL_2, INSTR_RETURN_1];
    let arg = tag(42);
    let interp_result = run_interp_arity1(&bc, arg);
    let jit_result = run_jit_arity1(&bc, arg);
    assert_eq!(jit_result, interp_result, "JIT ≠ interp");
    assert_eq!(untag(jit_result), 42, "expected arg back");
}

#[test]
fn jit_and_interp_agree_on_arg_plus_one() {
    // arg_0 + 1
    // Bytecode: LOCAL_2; CONST_1; FIXED_ADD; RETURN_1
    let bc = vec![
        INSTR_LOCAL_2,
        INSTR_CONST_1,
        INSTR_FIXED_ADD,
        INSTR_RETURN_1,
    ];
    let arg = tag(99);
    let interp_result = run_interp_arity1(&bc, arg);
    let jit_result = run_jit_arity1(&bc, arg);
    assert_eq!(jit_result, interp_result);
    assert_eq!(untag(jit_result), 100);
}

#[test]
fn jit_and_interp_agree_on_arg_times_3_plus_7() {
    // 3 * arg_0 + 7
    let bc = vec![
        INSTR_LOCAL_2,            // arg_0
        INSTR_CONST_INT_B, 3,     // const 3
        INSTR_FIXED_MULT,         // arg_0 * 3
        INSTR_CONST_INT_B, 7,     // const 7
        INSTR_FIXED_ADD,          // + 7
        INSTR_RETURN_1,
    ];
    let arg = tag(5);
    let interp_result = run_interp_arity1(&bc, arg);
    let jit_result = run_jit_arity1(&bc, arg);
    assert_eq!(jit_result, interp_result);
    assert_eq!(untag(jit_result), 5 * 3 + 7);
}

#[test]
fn jit_zero_arg_function_returns_constant() {
    // No-arg function: CONST_1; RETURN_1. Inferred arity 0.
    let bc = vec![INSTR_CONST_1, INSTR_RETURN_1];
    let mut jit = Jit::new().unwrap();
    let f = translate::compile(&mut jit, &bc).expect("translate");
    let result = unsafe { f(std::ptr::null()) };
    assert_eq!(untag(result), 1);
}

/// Sanity: confirm that for a tail of LOCAL_0 (peek-of-top), arity
/// inference picks 1 — and a single arg passed via the args array
/// is returned.
#[test]
fn jit_local_0_is_arg_for_arity_1_inference() {
    let bc = vec![INSTR_LOCAL_0, INSTR_RETURN_1];
    let mut jit = Jit::new().unwrap();
    let f = translate::compile(&mut jit, &bc).expect("translate");
    let args = [tag(77)];
    let result = unsafe { f(args.as_ptr()) };
    assert_eq!(untag(result), 77, "LOCAL_0 should read args[0]");
}
