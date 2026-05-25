//! JIT-to-JIT calls: function A (JIT'd) calls function B (also JIT'd
//! via the trampoline path). Verifies the closure_call_trampoline
//! actually dispatches through `jit_bridge::jit_dispatch_closure_call`
//! and returns the right result.
//!
//! This is the FULL JIT pipeline:
//!   interp.do_call → JIT-A (native)
//!     A's CALL_CONST_ADDR8 → closure_call_trampoline
//!       trampoline → jit_dispatch_closure_call
//!         dispatch → interp.do_call → JIT-B (native)
//!           B returns
//!         dispatch returns B's result
//!       trampoline returns
//!     A continues with B's result
//!   A returns

use polyml_jit::{translate, Jit};
use polyml_runtime::{Interpreter, JitEntry, PolyWord};

const INSTR_LOCAL_2: u8 = 0x2b;
const INSTR_CONST_INT_B: u8 = 0x28;
const INSTR_FIXED_ADD: u8 = 0xaa;
const INSTR_RETURN_1: u8 = 0x42;

fn tag(n: i64) -> i64 {
    2 * n + 1
}
fn untag(t: i64) -> i64 {
    assert_eq!(t & 1, 1, "expected tagged, got {t}");
    (t - 1) >> 1
}

/// Helper: invoke a JIT'd 1-arg function with a raw argument value.
/// Sets up the args_ptr per JIT convention (arg_0 first, then retPC
/// + closure placeholders).
fn call_jit_arity1(jit_fn: translate::JitFn, arg0: i64) -> i64 {
    let args = [arg0, 0i64, 0i64];
    unsafe { jit_fn(args.as_ptr()) }
}

#[test]
fn interp_dispatches_to_first_jit_function() {
    // 1-arg "add 100" via direct interp dispatch (no nesting).
    let bc = vec![
        INSTR_LOCAL_2,
        INSTR_CONST_INT_B,
        100,
        INSTR_FIXED_ADD,
        INSTR_RETURN_1,
    ];
    let mut jit = Jit::new().unwrap();
    let jit_fn = translate::compile(&mut jit, &bc).unwrap();

    let result = call_jit_arity1(jit_fn, tag(42));
    assert_eq!(untag(result), 142);
}

/// Verify the trampoline-driven dispatch path: install a JIT'd
/// "add 100" in the interpreter's cache, then invoke it via
/// `jit_dispatch_closure_call` (the function our trampoline calls).
///
/// NOTE: this test exercised the JIT-to-JIT fast path. After
/// commit (this) we disabled that path by default (MAX_JIT_DEPTH=0)
/// to avoid OS thread stack overflow on deeply recursive bootstrap
/// code AND a separate SEGV bug. The test now goes through the
/// interpreter loop, which doesn't have the right setup for a
/// hand-built fake closure (no real code object). Ignored until
/// MAX_JIT_DEPTH is bumped back > 0.
#[test]
#[ignore = "JIT-to-JIT fast path disabled (MAX_JIT_DEPTH=0); see jit_bridge.rs"]
fn jit_bridge_dispatches_into_cached_jit() {
    // Build the inner function: 1-arg add-100.
    let bc = vec![
        INSTR_LOCAL_2,
        INSTR_CONST_INT_B,
        100,
        INSTR_FIXED_ADD,
        INSTR_RETURN_1,
    ];
    let mut jit = Jit::new().unwrap();
    let jit_fn = translate::compile(&mut jit, &bc).unwrap();

    // Synthesize a closure pointing at a fake code-obj address.
    let fake_code_obj = vec![0u8; 16];
    let code_obj_ptr = fake_code_obj.as_ptr() as usize;
    let closure_storage = Box::new([PolyWord::from_bits(code_obj_ptr), PolyWord::ZERO]);
    let closure_storage = Box::leak(closure_storage);
    let closure = PolyWord::from_ptr(closure_storage.as_ptr());

    // Install in the interpreter's cache.
    let mut interp = Interpreter::from_bytes(64, vec![INSTR_RETURN_1]);
    interp.install_jit(
        code_obj_ptr,
        JitEntry {
            func: jit_fn,
            arity_init: 3,
            sml_arity: 1,
        },
    );

    // Use jit_bridge::with_jit_interp + jit_dispatch_closure_call.
    let result = polyml_runtime::with_jit_interp(&mut interp, || {
        polyml_runtime::jit_dispatch_closure_call(closure, &[PolyWord::from_bits(tag(7) as usize)])
            .expect("dispatch")
    });
    assert_eq!(untag(result.0 as i64), 107);
}
