//! The full pipeline end-to-end with real JIT-emitted bytecode:
//!
//!   JIT-compile A which contains a CALL_CONST_ADDR8_0 reading
//!   a closure pointer from the const segment. The closure points
//!   at a code object whose JIT'd version is installed in the
//!   cache. Run A; verify the trampoline → cache → JIT-B chain
//!   executes correctly.
//!
//! This is the architectural validation: every piece between
//! "JIT translator emits a CALL" and "JIT'd target runs" is
//! exercised together.

use polyml_jit::{translate, Jit};
use polyml_runtime::{Interpreter, JitEntry, PolyWord};

const INSTR_CONST_INT_B: u8 = 0x28;
const INSTR_CALL_CONST_ADDR8_0: u8 = 0x57;
const INSTR_LOCAL_2: u8 = 0x2b;
const INSTR_FIXED_ADD: u8 = 0xaa;
const INSTR_RETURN_1: u8 = 0x42;

fn tag(n: i64) -> i64 {
    2 * n + 1
}
fn untag(t: i64) -> i64 {
    assert_eq!(t & 1, 1, "expected tagged, got {t}");
    (t - 1) >> 1
}

/// Construct a heap-style code object whose body is `bytecode`
/// followed by a count-word of 0 and a trailing-offset word of -8.
/// Returns the address of the body (= what `closure[0]` would point at).
///
/// The Box is intentionally leaked — caller owns nothing; the heap
/// data lives forever (fine for a test).
fn make_code_object(bytecode: &[u8]) -> usize {
    // Body layout (in word slots):
    //   slot 0..N-1: bytecode (1 byte per byte, padded to word boundary)
    //   slot N:     count = 0
    //   slot N+1:   trailing-offset = -8
    let n_body_words = bytecode.len().div_ceil(8) + 2;
    // Total storage = length-word + body words.
    let lw: usize = n_body_words | (0x04_usize << 56); // F_CODE_OBJ
    let mut storage: Vec<usize> = vec![0; 1 + n_body_words];
    storage[0] = lw;
    // Trailing offset at the last word: -8.
    storage[n_body_words] = (-8_i64) as u64 as usize;
    // Copy bytecode into the bytes view of word[1..N].
    let body_ptr = (&mut storage[1] as *mut usize) as *mut u8;
    unsafe {
        std::ptr::copy_nonoverlapping(bytecode.as_ptr(), body_ptr, bytecode.len());
    }
    let body_addr = (&storage[1] as *const usize) as usize;
    Box::leak(storage.into_boxed_slice());
    body_addr
}

/// Construct a closure object whose first word is `code_obj_ptr`.
/// Returns the body address.
fn make_closure(code_obj_ptr: usize) -> usize {
    let lw: usize = 1 | (0x03_usize << 56); // F_CLOSURE_OBJ
    let storage = vec![lw, code_obj_ptr];
    let body_addr = (&storage[1] as *const usize) as usize;
    Box::leak(storage.into_boxed_slice());
    body_addr
}

#[test]
fn jit_emitted_call_const_addr8_chains_through_trampoline() {
    // 1. Build a 1-arg "add 100" callee bytecode.
    let callee_bc = vec![
        INSTR_LOCAL_2,
        INSTR_CONST_INT_B,
        100,
        INSTR_FIXED_ADD,
        INSTR_RETURN_1,
    ];

    // 2. Construct a heap-style code object so closure_arity_from_addr
    //    can deref and find RETURN_1.
    let callee_code_obj_ptr = make_code_object(&callee_bc);
    let callee_closure_ptr = make_closure(callee_code_obj_ptr);

    // 3. JIT-compile the callee. Install in the cache.
    let mut jit = Jit::new().unwrap();
    let callee_jit = translate::compile(&mut jit, &callee_bc).unwrap();

    // 4. Build the CALLER's full_body:
    //    Bytecode:
    //       0: CONST_INT_B 7              (push tag(7) as the arg)
    //       2: CALL_CONST_ADDR8_0 imm=4   (pop 1 arg, call callee)
    //       4: RETURN_1
    //    Constants area (starts at byte 8 with count word):
    //       [8..16]: count word
    //       [16..24]: alignment
    //       [24..32]: alignment
    //       [32..40]: closure pointer  ← read_at = pc(4) + imm(4) + 3*8 = 32 ✓
    let mut caller_full_body: Vec<u8> = vec![0; 40];
    caller_full_body[0] = INSTR_CONST_INT_B;
    caller_full_body[1] = 7;
    caller_full_body[2] = INSTR_CALL_CONST_ADDR8_0;
    caller_full_body[3] = 4; // imm: pc(4) + 4 + 24 = 32
    caller_full_body[4] = INSTR_RETURN_1;
    caller_full_body[32..40]
        .copy_from_slice(&(callee_closure_ptr as u64).to_le_bytes());

    let caller_bytecode_end = 5;
    let caller_jit =
        translate::compile_with_consts(&mut jit, &caller_full_body, caller_bytecode_end)
            .expect("caller compile");

    // 5. Install the callee in the cache.
    let mut interp = Interpreter::from_bytes(64, vec![INSTR_RETURN_1]);
    interp.install_jit(
        callee_code_obj_ptr,
        JitEntry {
            func: callee_jit,
            arity_init: 3,
            sml_arity: 1,
        },
    );

    // 6. Invoke the CALLER under with_jit_interp so the trampoline
    //    can find the live interpreter.
    //    The caller's arity_init is at least 3 (max of peeks=0 and
    //    RETURN_N+2 = 1+2 = 3). Provide 3 dummy slots.
    let dummy_args = [0i64; 3];
    let result = polyml_runtime::with_jit_interp(&mut interp, || unsafe {
        caller_jit(dummy_args.as_ptr(), 0, 0)
    });

    // Expected chain: caller pushes 7 → calls callee → callee's
    // LOCAL_2 reads 7 → adds 100 → returns 107 → caller returns
    // 107.
    assert_eq!(
        untag(result),
        107,
        "expected 7 + 100 = 107, got raw {result:#x}"
    );
}

/// Sanity demo: directly call the JIT'd callee with a known arg
/// and verify the answer. This isolates the callee's correctness
/// from the trampoline chain.
#[test]
fn callee_jit_directly_returns_arg_plus_100() {
    let callee_bc = vec![
        INSTR_LOCAL_2,
        INSTR_CONST_INT_B,
        100,
        INSTR_FIXED_ADD,
        INSTR_RETURN_1,
    ];
    let mut jit = Jit::new().unwrap();
    let callee_jit = translate::compile(&mut jit, &callee_bc).unwrap();
    let args = [tag(7), 0, 0];
    let result = unsafe { callee_jit(args.as_ptr(), 0, 0) };
    assert_eq!(untag(result), 107);
}
