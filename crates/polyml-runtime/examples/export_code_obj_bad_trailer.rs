//! AUDIT REPRO (unsafe-audit finding #13 + the export/snapshot cluster) —
//! `export::snapshot` -> `build_code` F_CODE_OBJ const-segment OOB.
//!
//! `snapshot(root)` (export.rs:50) walks every object reachable from `root`,
//! reading each object's length word at `*(addr-1)` and dispatching on the
//! type bits. For an F_CODE_OBJ it calls `build_code` (export.rs:180-211),
//! which derives the constants segment via the SHARED helper
//! `length_word::const_segment_for_code` (the SAME primitive the GC routes
//! through), then loops `for i in 0..count { *cp_start.add(i) }`
//! (export.rs:201-204) with NO release-time bounds check on either `cp` or
//! `count` (the helper's is_code_object / n_words>=2 guards are debug_assert
//! ONLY). The note in the audit ("RISKIEST BLOCK") is the `let _ = n;` at
//! export.rs:205 — the object's true length word is read but DISCARDED, so
//! nothing bounds the loop against the object's actual allocation.
//!
//! If the code object's trailing-offset word and/or count word are corrupt
//! (an adversarial pexport image, or a SetCodeConstant that wrote a bad
//! trailer), `build_code` reads (and INTERNS, recursing) arbitrary memory
//! far past the object body.
//!
//! Production reach: `snapshot` is called from `poly_export` (rts.rs:1239),
//! which gates only `root.is_data_ptr()` — it never validates that the root
//! (or any object reached from it) is in a managed space nor that its
//! trailer words are well-formed. A loaded image whose live heap contains a
//! type-confused / corrupted code object reachable from the `PolyML.export`
//! root therefore wild-walks here. This is the export-side sibling of the
//! KNOWN GC-side finding (examples/gc_code_obj_bad_trailer.rs) and of the
//! loader untyped-ref type-confusion residual (lf_ref_52 / task #96).
//!
//! Run:
//!   cargo run --release -p polyml-runtime --example export_code_obj_bad_trailer
//! Expect: SIGSEGV (exit 139) from the OOB read in build_code's 0..count loop.

use polyml_runtime::PolyWord;
use polyml_runtime::export;
use polyml_runtime::length_word::F_CODE_OBJ;
use polyml_runtime::space::{MemorySpace, SpaceKind, set_length_word};

fn main() {
    // A small space. Code object layout (n_words = 4 body):
    //   body[0]      code byte word (arbitrary)
    //   body[1]      a "constant" slot
    //   body[2]      unused
    //   body[3]      TRAILING OFFSET word (last word) — we corrupt THIS.
    let mut space = MemorySpace::new(64, SpaceKind::Mutable);

    let n_words = 4usize;
    let obj = space.alloc(n_words);
    unsafe {
        set_length_word(obj, n_words, F_CODE_OBJ);
        obj.add(0).write(PolyWord::from_bits(0xdead_beef));
        obj.add(1).write(PolyWord::from_bits(0));
        obj.add(2).write(PolyWord::from_bits(0));

        // body[3] (= last word) holds the SIGNED byte offset.
        // const_segment_for_code computes cp = last_word + 1 + offset/8.
        // offset = 1 GiB => cp jumps 2^27 words forward into unmapped
        // memory. build_code then reads count = *(cp-1) (already wild) and
        // loops 0..count reading *cp.add(i). The count read faults first.
        let wild_offset_bytes: usize = 1usize << 30; // 1 GiB forward
        obj.add(n_words - 1)
            .write(PolyWord::from_bits(wild_offset_bytes));
    }

    let obj_addr = obj as usize;
    let last_word_addr = obj_addr + (n_words - 1) * std::mem::size_of::<usize>();
    let computed_cp = last_word_addr + std::mem::size_of::<usize>() + (1usize << 30);
    eprintln!(
        "code obj body @ 0x{obj_addr:016x} (n_words={n_words}); \
         corrupt trailer makes cp -> 0x{computed_cp:016x}"
    );
    eprintln!("calling export::snapshot; build_code will deref the wild cp ...");

    // The root is the corrupt code object itself. snapshot interns it,
    // drain() reads its length word (F_CODE_OBJ), dispatches to build_code,
    // which calls const_segment_for_code -> wild cp -> OOB read.
    let root = PolyWord::from_ptr(obj.cast_const());
    let img = unsafe { export::snapshot(root) };

    // If we get here, no OOB fault occurred (bound check landed cp inside).
    eprintln!(
        "export::snapshot returned WITHOUT fault ({} objects)",
        img.objects.len()
    );
}
