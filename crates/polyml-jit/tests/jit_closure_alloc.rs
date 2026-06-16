//! JIT'd CLOSURE_B builds a real closure object on the heap, with
//! slot 0 = source closure's code-addr and slots 1..N = captures.
//!
//! Test bytecode: take 2 args (capture0, src_closure), build a
//! closure capturing arg_0. Verify the result is a heap pointer
//! whose first word matches the source's code-addr and whose
//! second word matches arg_0.

use polyml_jit::{Jit, translate};
use polyml_runtime::{Interpreter, MemorySpace, PolyWord, SpaceKind};

const INSTR_LOCAL_2: u8 = 0x2b;
const INSTR_CLOSURE_B: u8 = 0xd0;
const INSTR_RETURN_1: u8 = 0x42;

fn tag(n: i64) -> i64 {
    2 * n + 1
}

#[test]
fn jit_closure_b_builds_real_closure() {
    // Bytecode:
    //   LOCAL_3   ; push arg_1 (= the source closure)
    //   LOCAL_3   ; push arg_0 (capture) — after first push, sp[3] = arg_0
    //   CLOSURE_B 1 ; 1 capture; top = src_closure (we want it BELOW capture)
    //   RETURN_1
    //
    // Wait: CLOSURE_B's stack expectation is `[src_closure, caps...]`
    // from bottom — TOP is src_closure. Let me re-check our impl.
    //
    // Looking at our impl: `let src_closure = stack.pop().unwrap();
    // for _ in 0..n_captures { caps.push(stack.pop().unwrap()); }`
    // So top = src_closure, below = captures (with captures[0] = first popped,
    // CLOSURE_B semantics (per upstream libpolyml/bytecode.cpp
    // CREATE_CLOSURE): pop N captures from top in order (first pop →
    // slot N, last pop → slot 1), then PEEK src (now top) and copy
    // its slot 0 (code addr) as the new closure's slot 0.
    //
    // So stack BEFORE CLOSURE_B (top → bottom):
    //   cap_N  (top — will go to slot N)
    //   cap_{N-1}
    //   ...
    //   cap_1
    //   src   (bottom of group — provides code addr)
    //
    // Bytecode pattern: push src first, then push captures cap_1..cap_N.
    //
    // For our 2-arg test (sml_arity=2):
    //   At entry: sp[0]=closure, sp[1]=retPC, sp[2]=arg_1, sp[3]=arg_0
    //   We want src=arg_1, capture=arg_0.
    //   - LOCAL_2 → push arg_1 (now sp top, stack shifted)
    //   - LOCAL_4 → push arg_0 (reads original sp[3] after the shift)
    //   - CLOSURE_B 1 → pops arg_0 as cap_1, peeks arg_1 as src.
    const INSTR_LOCAL_4: u8 = 0x2d;

    let bc = vec![
        INSTR_LOCAL_2, // push arg_1 (= src closure)
        INSTR_LOCAL_4, // push arg_0 (= capture); reads original sp[3]
        INSTR_CLOSURE_B,
        1,
        INSTR_RETURN_1,
    ];
    let mut jit = Jit::new().unwrap();
    let jit_fn = translate::compile(&mut jit, &bc).expect("translate");

    // Build a source closure: 2-word object [code_addr, anything].
    // The code_addr is just a marker for the test.
    let fake_code_addr: u64 = 0xdeadbeefcafebabe;
    let src_storage: Box<[usize]> = Box::new([
        // length-word: 1 word, F_CLOSURE_OBJ
        1 | (0x03_usize << 56),
        fake_code_addr as usize,
    ]);
    let src_closure_ptr = (&src_storage[1] as *const usize) as usize;
    let src_storage = Box::leak(src_storage);
    let _ = src_storage; // keep alive

    let mut interp = Interpreter::from_bytes(64, vec![INSTR_RETURN_1])
        .with_alloc_space(MemorySpace::new(4096, SpaceKind::Mutable));

    // arg_0 = capture (tag(42)), arg_1 = src_closure pointer.
    // JIT args_ptr convention for 2-arg function:
    //   args_ptr[0] = arg_0
    //   args_ptr[1] = arg_1
    //   args_ptr[2] = retPC placeholder
    //   args_ptr[3] = closure placeholder
    let args = [tag(42), src_closure_ptr as i64, 0, 0];
    let result =
        polyml_runtime::with_jit_interp(&mut interp, || unsafe { jit_fn(args.as_ptr(), 0, 0) });

    let result_word = PolyWord::from_bits(result as usize);
    assert!(
        result_word.is_data_ptr(),
        "closure should be heap-allocated, got {result:#x}"
    );

    // Read the closure body.
    let ptr = result as *const u64;
    let slot0 = unsafe { *ptr };
    let slot1 = unsafe { *ptr.add(1) };
    assert_eq!(
        slot0, fake_code_addr,
        "slot 0 should be source closure's code addr"
    );
    // slot 1 = capture = tag(42)
    assert_eq!(slot1 as i64, tag(42), "slot 1 should be the capture");
}
