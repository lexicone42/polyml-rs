//! JIT'd code allocates real heap tuples via the real
//! alloc_tuple_trampoline (routed through the interpreter's
//! alloc_space).
//!
//! Bytecode: take 1 arg, build a TUPLE_2 containing (arg, arg + 1),
//! return the tuple pointer. Verify the tuple lives in the interp's
//! heap and its fields read back correctly.

use polyml_jit::{translate, Jit};
use polyml_runtime::{Interpreter, MemorySpace, PolyWord, SpaceKind};

const INSTR_LOCAL_2: u8 = 0x2b;
const INSTR_LOCAL_3: u8 = 0x2c;
const INSTR_CONST_1: u8 = 0x3c;
const INSTR_FIXED_ADD: u8 = 0xaa;
const INSTR_TUPLE_2: u8 = 0x69;
const INSTR_RETURN_1: u8 = 0x42;

fn tag(n: i64) -> i64 {
    2 * n + 1
}
fn untag(t: i64) -> i64 {
    assert_eq!(t & 1, 1, "expected tagged, got {t}");
    (t - 1) >> 1
}

#[test]
fn jit_allocates_tuple_via_real_trampoline() {
    // Bytecode for f(x) = (x, x + 1):
    //   LOCAL_2        ; push x (the SML arg at sp[2])
    //   LOCAL_3        ; push x again (after the first push, LOCAL_3 = original sp[2])
    //   CONST_1        ; push 1
    //   FIXED_ADD      ; (x + 1)
    //   TUPLE_2        ; build tuple
    //   RETURN_1
    let bc = vec![
        INSTR_LOCAL_2,
        INSTR_LOCAL_3,
        INSTR_CONST_1,
        INSTR_FIXED_ADD,
        INSTR_TUPLE_2,
        INSTR_RETURN_1,
    ];
    let mut jit = Jit::new().unwrap();
    let jit_fn = translate::compile(&mut jit, &bc).expect("translate");

    // Set up an interpreter with an alloc space so the trampoline
    // has somewhere to allocate.
    let mut interp = Interpreter::from_bytes(64, vec![INSTR_RETURN_1])
        .with_alloc_space(MemorySpace::new(4096, SpaceKind::Mutable));

    // Invoke the JIT'd function inside with_jit_interp so the
    // alloc_tuple_trampoline can reach the live interpreter.
    let args = [tag(42), 0i64, 0i64];
    let result = polyml_runtime::with_jit_interp(&mut interp, || unsafe {
        jit_fn(args.as_ptr(), 0, 0)
    });

    // The result should be a heap pointer (not tagged).
    let result_word = PolyWord::from_bits(result as usize);
    assert!(
        result_word.is_data_ptr(),
        "result should be a heap pointer, got raw {result:#x}"
    );

    // Dereference the tuple and verify its two fields.
    let tuple_ptr = result as *const PolyWord;
    let field0 = unsafe { (*tuple_ptr).0 as i64 };
    let field1 = unsafe { (*tuple_ptr.add(1)).0 as i64 };
    assert_eq!(untag(field0), 42, "field 0 should be x");
    assert_eq!(untag(field1), 43, "field 1 should be x + 1");
}
