//! Repro for AUDIT finding index 1 / 2: `do_call` validates the CLOSURE
//! word (is_data_ptr + alignment) but NEVER validates the closure's
//! word0 (`code_word`) before treating it as a code-object pointer and
//! feeding it to `const_segment_for_code`.
//!
//! Two violation modes, selectable by argv[1]:
//!   - "tagged" : closure word0 is a TAGGED INT. `code_word.as_ptr()`
//!                yields an ODD address; `const_segment_for_code` derefs
//!                `obj_ptr.sub(1)` at an unaligned/garbage address -> UB.
//!   - "noncode": closure word0 points at a NON-CODE heap object (an
//!                ordinary tuple). `const_segment_for_code` reads the
//!                tuple's body words as a trailing-offset + count and
//!                computes a WILD `code_end` (the PC bound for the whole
//!                next function). In RELEASE the is_code_object/n>=2
//!                debug_asserts are compiled out, so this is SILENT.
//!
//! Build + run in RELEASE so the debug_asserts in const_segment_for_code
//! are compiled out (the production / `poly run` configuration):
//!   cargo run --release -p polyml-runtime --example do_call_bad_code_word -- tagged
//!   cargo run --release -p polyml-runtime --example do_call_bad_code_word -- noncode

use polyml_runtime::length_word::{F_CLOSURE_OBJ, flags_of, is_code_object, length_of};
use polyml_runtime::space::set_length_word;
use polyml_runtime::{Interpreter, MemorySpace, PolyWord, SpaceKind};

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "tagged".into());
    println!("=== do_call bad-code_word repro: mode={mode} ===");

    // A space to hold the bad closure (and, in noncode mode, the
    // non-code object its word0 points at). We must keep it alive for
    // the whole run so the pointers stay valid.
    let mut space = MemorySpace::new(4096, SpaceKind::Mutable);

    // Build the bad closure as a 2-word CLOSURE object.
    let closure_body = space.alloc(2);
    unsafe { set_length_word(closure_body, 2, F_CLOSURE_OBJ) };

    let bad_code_word: PolyWord = match mode.as_str() {
        "tagged" => {
            // word0 = a tagged int (LSB set). The compiler NEVER emits
            // this in word0 of a closure, but a corrupted image can.
            PolyWord::tagged(123)
        }
        "noncode" => {
            // word0 = a pointer to a NON-CODE object (an ordinary 3-word
            // tuple full of attacker-chosen words). const_segment_for_code
            // will read tuple_body[n-1] as a signed byte offset and
            // tuple_body[cp-1] as a count -> wild code_end.
            let tuple = space.alloc(3);
            // Type bits 0 == F_WORD/ordinary (NOT F_CODE_OBJ).
            unsafe { set_length_word(tuple, 3, 0x00) };
            // Fill the body with large values so the derived offset is
            // far out of bounds (the attacker controls these via the
            // pexport `O3|...` line).
            unsafe {
                tuple.add(0).write(PolyWord::from_bits(0xdead_beef_0000));
                tuple.add(1).write(PolyWord::from_bits(0xfeed_face_0000));
                // tuple_body[n-1] is the "trailing offset" word.
                tuple.add(2).write(PolyWord::from_bits(0x7fff_ffff_0000));
            }
            // Show what const_segment_for_code WOULD compute (this is the
            // unsafe deref the audit flags; do it explicitly so we can
            // print before the interpreter blindly trusts it).
            let lw = unsafe { MemorySpace::length_word_of(tuple) };
            println!(
                "  non-code object header: n_words={} flags=0x{:02x} is_code_object={}",
                length_of(lw),
                flags_of(lw),
                is_code_object(lw),
            );
            PolyWord::from_ptr(tuple)
        }
        other => {
            eprintln!("unknown mode {other:?}; use tagged|noncode");
            std::process::exit(2);
        }
    };

    // Write the bad code word into the closure's word0; word1 = a tagged
    // capture so it is NOT mistaken for the self-pointer guard.
    unsafe {
        closure_body.add(0).write(bad_code_word);
        closure_body.add(1).write(PolyWord::tagged(0));
    }

    let closure = PolyWord::from_ptr(closure_body);
    println!(
        "  bad closure = {closure:?}; word0 (code_word) = {bad_code_word:?} \
         (is_data_ptr={})",
        bad_code_word.is_data_ptr()
    );

    // Build an interpreter with a trivial owned code segment (RETURN-ish
    // bytes; never executed — we go straight into do_call). Seed a
    // return sentinel + the closure on the stack the way a CALL site
    // would.
    let mut interp = Interpreter::from_bytes(1024, vec![0u8; 16]);
    interp.seed_return_sentinel();

    println!(
        "  -> calling do_call(bad_closure); in RELEASE this is the wild deref the audit flags..."
    );
    let r = interp.test_invoke_do_call(closure);
    // If we reach here, do_call returned without crashing. Report what
    // code_end it derived (the PC bound for the next function) — a wild
    // value here is the silent corruption.
    let (cs, ce) = interp.peek_code_seg_for_debug();
    println!("  do_call returned: {r:?}");
    println!(
        "  derived code segment: start=0x{:016x} end=0x{:016x} (len={} bytes)",
        cs as usize,
        ce as usize,
        (ce as usize).wrapping_sub(cs as usize),
    );
    println!("  (no crash this run — but the code_end above is WILD; the very next");
    println!("   fetch_u8 against it reads out of the code object's allocation.)");

    // Keep space alive to the end.
    drop(space);
}
