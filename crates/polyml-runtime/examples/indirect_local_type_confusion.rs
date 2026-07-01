//! Standing repro for the INDIRECT_LOCAL_* / INDIRECT field-load opcode
//! type-confusion deref (interpreter-opcode-deref cluster, audit finding 2).
//!
//! THREAT MODEL: an untrusted/corrupted image. The fused stack/heap
//! opcodes `INDIRECT_LOCAL_B0/B1/BB`, `INDIRECT_0_LOCAL_0`,
//! `JUMP_NEQ_LOCAL_IND`, the `INDIRECT_CLOSURE_*` family, and `indirect()`
//! all read a stack-local word and dereference it via
//! `PolyWord::as_ptr().add(slot)` with NO object-type or object-length
//! check. `peek`/`pop` bound the STACK access (so `depth` is stack-safe),
//! and the GC only fires between opcodes (so the slot is never dangling).
//! The sole remaining violation is TYPE/SIZE confusion: a corrupted image
//! that puts a tagged int (or a too-small / wrong-type object) where the
//! bytecode expects a sufficiently-large object pointer.
//!
//! This is the same class as the documented loader residual `lf_ref_52`
//! (task #96): the loader cannot catch a "valid Ref to a wrong-TYPE object"
//! without whole-image type inference, and the field-load opcodes trust
//! the pointer at deref time.
//!
//! POST-SCRUB NUANCE (GC-soak fix, commit 8756419): the
//! GC now scrubs `[0, sp)` to `Tagged(0)`. `Tagged(0)`'s bits are 1, so
//! `as_ptr()` is address 1 and the deref is a DETERMINISTIC near-null
//! SIGSEGV (a loud crash) rather than a silent use-after-free. This repro
//! shows the type-confusion deref directly: a tagged int in the slot ->
//! `as_ptr()` is a low/garbage address -> `*p` faults.
//!
//! Run (expect SIGSEGV / exit 139):
//!   cargo build --release -p polyml-runtime --example indirect_local_type_confusion
//!   ./target/release/examples/indirect_local_type_confusion
//!
//! This demonstrates the invariant violation through the REAL opcode
//! dispatch (`step()`), not by directly poking `as_ptr`. It is a library/
//! example reproducer; the equivalent via `poly run` needs a hand-crafted
//! image carrying a code object whose bytecode contains INDIRECT_LOCAL_B0
//! over a type-confused local (the lf_ref_52 pattern), which the loader
//! accepts because the ref is in-range and well-formed.

use polyml_runtime::interpreter::Interpreter;
use polyml_runtime::poly_word::PolyWord;

const INSTR_INDIRECT_LOCAL_B0: u8 = 0xc7; // opcodes.rs:158

fn main() {
    // One-instruction "code object": INDIRECT_LOCAL_B0 depth=0.
    // (from_bytes builds a raw byte buffer; this opcode does no
    // PC-relative addressing, so no real const pool is needed.)
    let code = vec![INSTR_INDIRECT_LOCAL_B0, 0x00];
    let mut interp = Interpreter::from_bytes(64, code);

    // Seed the stack with a TAGGED INT in the slot the opcode will treat
    // as an object pointer. A type-safe SML compiler never emits an
    // INDIRECT_LOCAL_B0 over a slot it didn't prove holds a >=1-word
    // object; a corrupted image can. Tagged(0x1234) -> bits 0x2469 ->
    // as_ptr() == 0x2469 -> *p SIGSEGVs at that low address.
    interp.seed_push(PolyWord::tagged(0x1234));

    eprintln!(
        "about to step INDIRECT_LOCAL_B0 over a tagged-int local; \
         expect SIGSEGV (type-confusion deref of as_ptr() = a non-pointer)"
    );

    // Real dispatch. This calls the unsafe `*p` at mod.rs:2078.
    let r = interp.step();

    // If we get here, no fault occurred (it should not on a tagged-int
    // slot). Report what came back so a non-faulting build is visible.
    eprintln!("step returned without faulting: {r:?} -- UNEXPECTED");
    std::process::exit(0);
}
