//! End-to-end demonstrator: the interpreter's `do_call` dispatches
//! a closure call into a JIT'd function via the install_jit cache.
//!
//! This is the "transparent JIT" pattern in action — the interp
//! handles all of bytecode execution, but recognises pre-JIT'd
//! code objects and calls the native function instead of stepping.

use polyml_jit::{Jit, translate};
use polyml_runtime::{Interpreter, JitEntry, PolyWord};

const INSTR_LOCAL_2: u8 = 0x2b;
const INSTR_CONST_INT_B: u8 = 0x28;
const INSTR_FIXED_ADD: u8 = 0xaa;
const INSTR_RETURN_1: u8 = 0x42;

fn tag(n: i64) -> i64 {
    2 * n + 1
}
fn untag(t: i64) -> i64 {
    assert_eq!(t & 1, 1, "expected tagged int, got raw {t}");
    (t - 1) >> 1
}

#[test]
fn interp_do_call_dispatches_to_jit_cache() {
    // 1. JIT-compile a 1-arg "add 100" function.
    let bc = vec![
        INSTR_LOCAL_2,
        INSTR_CONST_INT_B,
        100,
        INSTR_FIXED_ADD,
        INSTR_RETURN_1,
    ];
    let mut jit = Jit::new().unwrap();
    let jit_fn = translate::compile(&mut jit, &bc).expect("jit compile");

    // 2. Synthesize a "closure" pointing at a fake code-object
    //    address. The interpreter looks up the JIT cache by that
    //    address; the dispatch fast-path doesn't actually deref
    //    the code object (it skips the bytecode setup entirely).
    let fake_code_obj_marker = vec![0u8; 16];
    let code_obj_ptr = fake_code_obj_marker.as_ptr() as usize;
    // The closure object: first word = code_obj_ptr (the JIT cache key).
    // Must be 8-byte aligned (do_call checks).
    let closure_storage = Box::new([PolyWord::from_bits(code_obj_ptr), PolyWord::ZERO]);
    let closure_storage = Box::leak(closure_storage); // simplest: leak for test
    let closure_word = PolyWord::from_ptr(closure_storage.as_ptr());

    // 3. Build a no-op interpreter (we only need it for the dispatch).
    let mut interp = Interpreter::from_bytes(64, vec![INSTR_RETURN_1]);

    // 4. Install the JIT entry.
    interp.install_jit(
        code_obj_ptr,
        JitEntry {
            func: jit_fn,
            arity_init: 3, // SML arity 1 + retPC + closure slots
            sml_arity: 1,
        },
    );

    // 5. Set up the stack for a 1-arg call. The caller pushed arg_0 = 7.
    //    After do_call (the call-instruction equivalent), sp = [closure,
    //    retPC, arg_0]. The interpreter usually pushes retPC+closure
    //    inside do_call; we just seed the arg here and let do_call do
    //    its thing.
    interp.seed_push(PolyWord::from_bits(tag(7) as usize));
    // Save SP so we can verify post-call state.
    let sp_before_call = interp.test_sp();

    // 6. Invoke do_call. The JIT-cache hit should dispatch to jit_fn.
    interp.test_invoke_do_call(closure_word).expect("dispatch");

    // 7. Inspect result. After the JIT-fast-path returns, the stack
    //    should have the result on top (replacing the arg).
    let top = interp.test_peek_top();
    assert_eq!(top.0 as i64 & 1, 1, "result must be tagged");
    assert_eq!(untag(top.0 as i64), 107, "expected 7 + 100 = 107");

    // 8. Stack depth should be sp_before_call - 1 + 1 = sp_before_call
    //    (we popped arg, pushed result). Net: same SP.
    assert_eq!(interp.test_sp(), sp_before_call, "stack depth changed");
}
