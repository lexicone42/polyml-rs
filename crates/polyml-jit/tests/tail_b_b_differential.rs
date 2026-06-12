//! Differential TAIL_B_B test: a hand-built tail-calling function must
//! produce the SAME result under the JIT and the interpreter.
//!
//! This is the correctness gate for the TAIL_B_B install fix
//! (2026-06-12). The old JIT translation consumed only `tail_count-1`
//! stack slots (closure + args), forgetting the retPC placeholder the
//! SML compiler pushes on TOP of the call group. Upstream
//! (bytecode.cpp:387-406) consumes `tail_count` items: retPC + closure
//! + (tail_count-2) args. The off-by-one made the value treated as the
//! "closure" actually be the bottom-most arg (often a tagged int),
//! producing "call to non-closure value" / SEGV on tail-recursive code
//! (List.map / List.tabF).
//!
//! Here we build a CALLER that tail-calls a real callee closure (the
//! callee adds 100 to its single arg) via `CONST_ADDR8_0` + `TAIL_B_B`,
//! and assert JIT result == interp result == the expected value, for
//! several inputs. This exercises the trampoline → dispatch → callee
//! chain through the FIXED translation.

use polyml_jit::{translate, Jit};
use polyml_runtime::{Interpreter, JitEntry, PolyWord, StepResult};

const INSTR_CONST_INT_B: u8 = 0x28;
const INSTR_LOCAL_2: u8 = 0x2b;
const INSTR_LOCAL_3: u8 = 0x2c;
const INSTR_FIXED_ADD: u8 = 0xaa;
const INSTR_RETURN_1: u8 = 0x42;
const INSTR_CONST_ADDR8_0: u8 = 0x55;
const INSTR_TAIL_B_B: u8 = 0x7b;

fn tag(n: i64) -> i64 {
    2 * n + 1
}
fn untag(t: i64) -> i64 {
    assert_eq!(t & 1, 1, "expected tagged int, got raw 0x{t:016x}");
    (t - 1) >> 1
}

/// Construct a heap-style code object whose body is `bytecode`
/// followed by a count-word of 0 and a trailing-offset word of -8.
/// Returns the address of the body (= what `closure[0]` would point at).
/// Leaks the storage (lives forever — fine for a test).
fn make_code_object(bytecode: &[u8]) -> usize {
    let n_body_words = bytecode.len().div_ceil(8) + 2;
    let lw: usize = n_body_words | (0x04_usize << 56); // F_CODE_OBJ
    let mut storage: Vec<usize> = vec![0; 1 + n_body_words];
    storage[0] = lw;
    storage[n_body_words] = (-8_i64) as u64 as usize; // trailing offset
    let body_ptr = (&mut storage[1] as *mut usize) as *mut u8;
    unsafe {
        std::ptr::copy_nonoverlapping(bytecode.as_ptr(), body_ptr, bytecode.len());
    }
    let body_addr = (&storage[1] as *const usize) as usize;
    Box::leak(storage.into_boxed_slice());
    body_addr
}

/// Construct a closure object whose first word is `code_obj_ptr`.
fn make_closure(code_obj_ptr: usize) -> usize {
    let lw: usize = 1 | (0x03_usize << 56); // F_CLOSURE_OBJ
    let storage = vec![lw, code_obj_ptr];
    let body_addr = (&storage[1] as *const usize) as usize;
    Box::leak(storage.into_boxed_slice());
    body_addr
}

/// Callee: `\x -> x + 100`. SML arity 1; LOCAL_2 = arg_0.
fn callee_bc() -> Vec<u8> {
    vec![
        INSTR_LOCAL_2,
        INSTR_CONST_INT_B,
        100,
        INSTR_FIXED_ADD,
        INSTR_RETURN_1,
    ]
}

/// Caller: arity 1. Forwards its OWN arg_0 to the callee via TAIL_B_B.
///
/// The caller's entry frame (SML convention, top → bottom):
///   sp[0] = closure (caller's own)
///   sp[1] = retPC
///   sp[2] = arg_0
///
/// Bytecode (offsets):
///   0: LOCAL_2                ; push caller arg_0 (sp[2] at entry)
///   1: CONST_ADDR8_0 imm      ; push the callee closure (the call target)
///   3: LOCAL_3                ; push caller's OWN retPC slot as the
///                            ; tail-call retPC placeholder. After the
///                            ; two pushes above, the caller's retPC has
///                            ; shifted from sp[1] to sp[3]. Forwarding
///                            ; it means the callee returns to the
///                            ; caller's CALLER (= tail-call semantics);
///                            ; here that retPC is the null sentinel, so
///                            ; the callee's RETURN yields Returned.
///   4: TAIL_B_B tc=3 skip=0   ; tail-call: [retPC, closure, 1 arg]
///
/// Const pool holds the callee closure pointer; CONST_ADDR8_0's
/// read address = pc(after imm) + imm + (count word). We lay the
/// const at offset 24 and choose imm so the math lands there.
fn caller_full_body(callee_closure_ptr: usize) -> (Vec<u8>, usize) {
    // Bytecode area: 6 bytes (0..6). Const segment begins at byte 8
    // (word boundary) with the count word; the closure pointer goes at
    // byte 24 (= count word @ 8, two alignment words @ 16/24 — we put
    // the pointer at 24).
    //
    // CONST_ADDR8_0 read address (matches translate.rs / interp):
    //   read_at = pc_after_opcode_byte + imm + 8(count) + 8 + 8
    // We solve for imm so read_at = 24.
    //   CONST_ADDR8_0 is at offset 1; its imm byte at offset 2; pc
    //   advances to 3 after the imm. read_at = 3 + imm + 24 must = 24?
    // Rather than hand-solve, mirror the proven offset from the
    // CALL_CONST_ADDR8 test: place the pointer 3 words past the count
    // word and pick imm so it resolves. Empirically (see
    // jit_call_const_addr8_end_to_end.rs) the const lands at
    // read_at = pc + imm + 24 with the pointer 3 words above the count
    // word. We replicate: pointer at byte 32, imm chosen to hit it.
    let mut body: Vec<u8> = vec![0; 40];
    body[0] = INSTR_LOCAL_2; // push caller arg_0 (sp[2] at entry)
    body[1] = INSTR_CONST_ADDR8_0;
    // imm at body[2]; pc after imm = 3. read_at = 3 + imm + 24 = 32 -> imm = 5.
    body[2] = 5;
    body[3] = INSTR_LOCAL_3; // retPC placeholder = caller's retPC
                             // (now at sp[3] after the two pushes above)
    body[4] = INSTR_TAIL_B_B;
    body[5] = 3; // tail_count: retPC + closure + 1 arg
    body[6] = 0; // skip = 0 (no caller-frame slots to drop in this
                 // hand-built frame; the JIT ignores skip regardless,
                 // and the interp's shift is then a no-op)
    body[32..40].copy_from_slice(&(callee_closure_ptr as u64).to_le_bytes());
    let bytecode_end = 7;
    (body, bytecode_end)
}

/// Run the caller under the interpreter with arg_0 = `arg`.
fn run_interp(caller_code_obj: usize, arg: i64) -> i64 {
    let mut interp = Interpreter::from_bytes(64, vec![INSTR_RETURN_1]);
    // Seed the caller's top-level frame: sentinel retPC, arg_0, retPC=0,
    // closure. RETURN at the END (after the tail-callee returns) pops
    // down to the sentinel and yields Returned.
    interp.test_seed_return_sentinel();
    interp.test_seed_top(PolyWord::from_bits(arg as usize)); // arg_0
    interp.test_seed_top(PolyWord::from_bits(0)); // retPC = 0
    interp.test_seed_top(PolyWord::from_bits(0)); // caller closure (unused)
    // SAFETY: caller_code_obj is a valid heap-style code object.
    unsafe {
        interp.set_code_segment_to_code_obj(caller_code_obj);
    }
    const STEP_BUDGET: u64 = 1_000_000;
    let mut steps = 0u64;
    loop {
        steps += 1;
        assert!(steps < STEP_BUDGET, "interp step budget exceeded");
        if std::env::var("TAIL_TEST_TRACE").is_ok() {
            let off = interp.pc_offset();
            let sp = interp.peek_sp_for_debug();
            eprintln!("  [interp] step={steps} pc_off={off} sp={sp}");
        }
        match interp.step() {
            Ok(StepResult::Continue) => continue,
            Ok(StepResult::Returned(v)) => return v.0 as i64,
            other => panic!("interp: {other:?} at step {steps}"),
        }
    }
}

#[test]
fn tail_b_b_jit_matches_interp() {
    let callee = callee_bc();
    let callee_code_obj = make_code_object(&callee);
    let callee_closure = make_closure(callee_code_obj);

    let (caller_body, caller_bc_end) = caller_full_body(callee_closure);
    let caller_code_obj = make_code_object(&caller_body[..]);

    // Build the JIT: compile callee (so it can install) + caller.
    let mut jit = Jit::new().unwrap();
    let callee_jit = translate::compile(&mut jit, &callee).expect("callee translate");
    let caller_jit = translate::compile_with_consts(&mut jit, &caller_body, caller_bc_end)
        .expect("caller (TAIL_B_B) must translate");

    // Install the callee in the interp's JIT cache so the trampoline
    // can dispatch to it. (Also exercises JIT→JIT through the tail
    // call, but the JIT→interp fallback path runs the bytecode if the
    // callee weren't installed — both must agree.)
    let mut interp = Interpreter::from_bytes(64, vec![INSTR_RETURN_1]);
    interp.install_jit(
        callee_code_obj,
        JitEntry {
            func: callee_jit,
            arity_init: 3,
            sml_arity: 1,
        },
    );

    for &x in &[0i64, 1, 5, 42, -7, 1000] {
        let arg = tag(x);
        let want = x + 100;

        // Interp result (no JIT cache involvement on the bytecode path —
        // the interp runs the caller's TAIL_B_B + the callee bytecode).
        let interp_result = run_interp(caller_code_obj, arg);
        assert_eq!(
            untag(interp_result),
            want,
            "interp wrong for x={x}: got {}",
            untag(interp_result)
        );

        // JIT result: run the caller's JIT code; its TAIL_B_B dispatches
        // through closure_call_trampoline into the callee (cache hit ->
        // JIT-callee, or fallback -> interp callee). args_buf shape:
        // [arg_0, retPC, closure] (arity_init=3 for an arity-1 caller).
        let args_buf = [arg, 0i64, 0i64];
        let jit_result = polyml_runtime::with_jit_interp(&mut interp, || unsafe {
            caller_jit(args_buf.as_ptr(), 0, 0)
        });

        assert_eq!(
            jit_result, interp_result,
            "JIT/interp diverged for x={x}: interp=0x{interp_result:016x} jit=0x{jit_result:016x}",
        );
        assert_eq!(
            untag(jit_result),
            want,
            "JIT wrong for x={x}: got {}",
            untag(jit_result)
        );
    }
}
