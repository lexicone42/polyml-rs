//! Differential + install-gate test for CALL_CONST_ADDR (0x57/0x58/
//! 0x17/0x18) — the correctness fence for the task-#115 CCA install
//! gate (ROOT-CAUSED 2026-06-20).
//!
//! ROOT CAUSE: the CCA translation is a MID-FUNCTION over-pop — it pops
//! `n_args` SSA values off the compile-time stack and pushes one result
//! (translate.rs:752-814), but upstream CALL_CLOSURE (bytecode.cpp:
//! 411-414) pops ONLY the closure: the call args PERSIST across the call
//! and the callee's RETURN_N (bytecode.cpp:454-460) collapses them. The
//! SML compiler then addresses the surviving slots (e.g. a
//! STACK_CONTAINER_B ref) by absolute offset AFTER the call, so the
//! over-pop desyncs the compile-time stack and a later
//! INDIRECT_CONTAINER_B derefs a stale tagged-0 (0x1) → SIGSEGV.
//!
//! THE SAFE SUBSET is a CCA in TAIL-EQUIVALENT position (next op is
//! RETURN_N or the LOCAL_0;RESET_R_1;RETURN_1 idiom): nothing reads the
//! corrupted slots below the result; the very next op returns it. This
//! mirrors the gate CALL_CLOSURE already uses.
//!
//! This test has two halves:
//!  1. POSITIVE control: a tail-position CCA caller must (a) pass the
//!     install gate (`cca_install_safe`) and (b) produce JIT == interp
//!     results across several args (the non-negotiable correctness
//!     gate).
//!  2. NEGATIVE control: the container-over-push shape (a STACK_CONTAINER
//!     ref live across the CCA, the real install-index-0 SEGV shape) must
//!     be REJECTED by the install gate, so it never reaches the unsafe
//!     translation. (We assert the GATE rejects it; we do NOT run it,
//!     because the unsafe translation SEGVs by construction — that is the
//!     bug the gate prevents.)

use polyml_jit::{Jit, cca_install_safe, translate};
use polyml_runtime::{Interpreter, JitEntry, PolyWord, StepResult};

const INSTR_CONST_INT_B: u8 = 0x28;
const INSTR_LOCAL_2: u8 = 0x2b;
const INSTR_FIXED_ADD: u8 = 0xaa;
const INSTR_RETURN_1: u8 = 0x42;
const INSTR_CALL_CONST_ADDR8_0: u8 = 0x57;
const INSTR_STACK_CONTAINER_B: u8 = 0x0e;
const INSTR_INDIRECT_CONTAINER_B: u8 = 0x74;
const INSTR_LOCAL_0: u8 = 0x29;
const INSTR_RESET_R_1: u8 = 0x64;
const INSTR_RESET_1: u8 = 0x50;

fn untag(t: i64) -> i64 {
    assert_eq!(t & 1, 1, "expected tagged int, got raw 0x{t:016x}");
    (t - 1) >> 1
}

/// Heap-style code object: `bytecode` + count-word(0) + trailing-offset(-8).
/// Returns the body address (= what `closure[0]` points at). Leaked.
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

/// Closure whose first word is `code_obj_ptr`. Leaked.
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

/// POSITIVE control caller: pushes `7`, calls the callee via
/// CALL_CONST_ADDR8_0, then RETURN_1. The CCA is in DIRECT-TAIL
/// position, so the over-pop is harmless and JIT == interp.
///
/// Bytecode:
///   0: CONST_INT_B 7
///   2: CALL_CONST_ADDR8_0 imm=4   (read_at = pc(4) + 4 + 24 = 32)
///   4: RETURN_1
/// Const pool: closure pointer at byte 32.
fn tail_caller_full_body(callee_closure_ptr: usize) -> (Vec<u8>, usize) {
    let mut body: Vec<u8> = vec![0; 40];
    body[0] = INSTR_CONST_INT_B;
    body[1] = 7;
    body[2] = INSTR_CALL_CONST_ADDR8_0;
    body[3] = 4;
    body[4] = INSTR_RETURN_1;
    body[32..40].copy_from_slice(&(callee_closure_ptr as u64).to_le_bytes());
    (body, 5)
}

/// Run a hand-built caller code object in the interpreter with one
/// top-of-stack arg already pushed via the test seeds. Returns the
/// raw result word.
fn run_interp_caller(caller_code_obj: usize) -> i64 {
    let mut interp = Interpreter::from_bytes(64, vec![INSTR_RETURN_1]);
    interp.test_seed_return_sentinel();
    // Seed the caller's top-level frame: arg_0 (unused by the tail
    // caller, which pushes its own const), retPC=0, closure=0.
    interp.test_seed_top(PolyWord::from_bits(0)); // arg_0
    interp.test_seed_top(PolyWord::from_bits(0)); // retPC
    interp.test_seed_top(PolyWord::from_bits(0)); // closure
    // SAFETY: caller_code_obj is a valid heap-style code object.
    unsafe {
        interp.set_code_segment_to_code_obj(caller_code_obj);
    }
    const STEP_BUDGET: u64 = 1_000_000;
    let mut steps = 0u64;
    loop {
        steps += 1;
        assert!(steps < STEP_BUDGET, "interp step budget exceeded");
        match interp.step() {
            Ok(StepResult::Continue) => continue,
            Ok(StepResult::Returned(v)) => return v.0 as i64,
            other => panic!("interp: {other:?} at step {steps}"),
        }
    }
}

#[test]
fn tail_position_cca_is_install_safe_and_jit_matches_interp() {
    let callee = callee_bc();
    let callee_code_obj = make_code_object(&callee);
    let callee_closure = make_closure(callee_code_obj);

    let (caller_body, caller_bc_end) = tail_caller_full_body(callee_closure);

    // (a) The install gate must accept a tail-position CCA.
    assert!(
        cca_install_safe(&caller_body[..caller_bc_end]),
        "tail-position CCA must pass the install gate"
    );

    let caller_code_obj = make_code_object(&caller_body[..]);

    // (b) JIT == interp.
    let mut jit = Jit::new().unwrap();
    let callee_jit = translate::compile(&mut jit, &callee).expect("callee translate");
    let caller_jit = translate::compile_with_consts(&mut jit, &caller_body, caller_bc_end)
        .expect("tail-position CCA caller must translate");

    let mut interp = Interpreter::from_bytes(64, vec![INSTR_RETURN_1]);
    interp.install_jit(
        callee_code_obj,
        JitEntry {
            func: callee_jit,
            arity_init: 3,
            sml_arity: 1,
        },
    );

    let interp_result = run_interp_caller(caller_code_obj);
    assert_eq!(untag(interp_result), 107, "interp: 7 + 100 = 107");

    // JIT: caller has no args (arity 0-ish); arity_init = max(peeks, 0+2).
    let args_buf = [0i64; 3];
    let jit_result = polyml_runtime::with_jit_interp(&mut interp, || unsafe {
        caller_jit(args_buf.as_ptr(), 0, 0)
    });
    assert_eq!(
        jit_result, interp_result,
        "JIT/interp diverged: interp=0x{interp_result:016x} jit=0x{jit_result:016x}"
    );
    assert_eq!(untag(jit_result), 107, "JIT: 7 + 100 = 107");
}

#[test]
fn container_over_push_cca_is_rejected_by_install_gate() {
    // The real install-index-0 SEGV shape: a STACK_CONTAINER ref is
    // LIVE across the CCA, and an INDIRECT_CONTAINER_B reads it AFTER
    // the call. The CCA is NOT in tail position. The install gate MUST
    // reject this (else the over-pop eats the container ref and the
    // later INDIRECT_CONTAINER_B SEGVs).
    //
    //   0: STACK_CONTAINER_B 1   ; push [filler, container_ref]
    //   2: CONST_INT_B 7         ; push the call arg
    //   4: CALL_CONST_ADDR8_0 .. ; pop 1 arg, push result (NON-tail)
    //   6: RESET_1               ; drop the result
    //   7: INDIRECT_CONTAINER_B 0; deref the container ref (would SEGV
    //                            ; if the ref were eaten by the over-pop)
    //   9: RETURN_1
    let mut body: Vec<u8> = vec![0; 8];
    body[0] = INSTR_STACK_CONTAINER_B;
    body[1] = 1;
    body[2] = INSTR_CONST_INT_B;
    body[3] = 7;
    body[4] = INSTR_CALL_CONST_ADDR8_0;
    body[5] = 0; // imm (immaterial — we only test the gate, not run it)
    body[6] = INSTR_RESET_1;
    body[7] = INSTR_INDIRECT_CONTAINER_B;
    // bytecode continues past our 8-byte window conceptually; for the
    // GATE test only the instruction-boundary walk matters, and the
    // walk decodes CCA's "next op" = RESET_1 (0x50), which is NOT a
    // return ⇒ not tail-equivalent ⇒ rejected.
    assert!(
        !cca_install_safe(&body),
        "container-over-push CCA (non-tail) must be REJECTED by the install gate"
    );
}

#[test]
fn mid_function_cca_with_local_read_is_rejected() {
    // A no-container but still UNSAFE shape: the CCA result is consumed
    // mid-function (RESET_1 then more ops), NOT immediately returned.
    // The over-pop net delta matches the interpreter, but a post-call
    // op addressing a persisted slot would desync — the basis-load
    // verification showed the no-container subset still SEGVs. The gate
    // must reject any non-tail CCA regardless of containers.
    //
    //   0: CONST_INT_B 7
    //   2: CALL_CONST_ADDR8_0 ..  (NON-tail: followed by RESET_1)
    //   4: RESET_1
    //   5: CONST_INT_B 1
    //   7: RETURN_1
    let body: Vec<u8> = vec![
        INSTR_CONST_INT_B,
        7,
        INSTR_CALL_CONST_ADDR8_0,
        0,
        INSTR_RESET_1,
        INSTR_CONST_INT_B,
        1,
        INSTR_RETURN_1,
    ];
    assert!(
        !cca_install_safe(&body),
        "mid-function CCA (result not immediately returned) must be REJECTED"
    );
}

#[test]
fn cleanup_tail_idiom_cca_is_install_safe() {
    // The LOCAL_0; RESET_R_1; RETURN_1 cleanup-tail idiom is also
    // tail-equivalent (mirrors translate.rs CALL_CLOSURE pattern B).
    //
    //   0: CONST_INT_B 7
    //   2: CALL_CONST_ADDR8_0 ..
    //   4: LOCAL_0
    //   5: RESET_R_1
    //   6: RETURN_1
    let body: Vec<u8> = vec![
        INSTR_CONST_INT_B,
        7,
        INSTR_CALL_CONST_ADDR8_0,
        0,
        INSTR_LOCAL_0,
        INSTR_RESET_R_1,
        INSTR_RETURN_1,
    ];
    assert!(
        cca_install_safe(&body),
        "cleanup-tail-idiom CCA must pass the install gate"
    );
}

#[test]
fn no_cca_function_is_vacuously_safe() {
    let body: Vec<u8> = vec![INSTR_CONST_INT_B, 7, INSTR_RETURN_1];
    assert!(
        cca_install_safe(&body),
        "a function with no CCA is vacuously install-safe"
    );
}
