//! AUDIT REPRO (unsafe-audit finding #4) — GC F_CODE_OBJ const-segment OOB.
//!
//! The Cheney collector's `scan_object` F_CODE_OBJ branch (gc.rs:245-255)
//! and the image-root code scan (interpreter/mod.rs:762-768) BOTH derive
//! the constants segment of a code object via
//! `length_word::const_segment_for_code`, then loop `for i in 0..count {
//! forward(cp.add(i)) }`. `const_segment_for_code` reads the object's
//! TRAILING word as a signed byte offset and `cp[-1]` as the count, with
//! NO release-time bounds check (only debug_assert!). If those trailer
//! words are corrupt (an adversarial image, or a byte_vec turned into a
//! code object whose trailer lies), the loop reads (and conditionally
//! WRITES — `forward` writes the slot when the read word looks like a
//! from-space pointer) far out of bounds.
//!
//! This harness reproduces it WITHOUT the full interpreter: build a tiny
//! alloc-space, lay down a code object with a deliberately corrupt
//! trailing-offset word so `cp` lands far past the object body, make it
//! a live root, then run `gc::collect`. The to-space scan then walks the
//! wild `cp` range -> OOB read -> SIGSEGV.
//!
//! Run:
//!   cargo run --release -p polyml-runtime --example gc_code_obj_bad_trailer
//! Expect: SIGSEGV (exit 139) from the OOB read in the F_CODE_OBJ scan.

use polyml_runtime::PolyWord;
use polyml_runtime::gc;
use polyml_runtime::length_word::{F_CODE_OBJ, make_length_word};
use polyml_runtime::space::{MemorySpace, SpaceKind, set_length_word};

fn main() {
    // A small alloc-space. Code object layout we build (n_words = 4 body):
    //   body[0]      code byte word (arbitrary)
    //   body[1]      count slot (cp[-1]) — what const_segment reads as count
    //   body[2]      a "constant" slot
    //   body[3]      TRAILING OFFSET word (last word) — we corrupt THIS.
    let mut alloc = MemorySpace::new(64, SpaceKind::Mutable);

    let n_words = 4usize;
    let obj = alloc.alloc(n_words);
    unsafe {
        set_length_word(obj, n_words, F_CODE_OBJ);
        // body[0]: an innocuous code word.
        obj.add(0).write(PolyWord::from_bits(0xdead_beef));
        // body[1]: doesn't matter directly; we will arrange cp[-1] (count)
        //          to be read from a wild address along with cp.
        obj.add(1).write(PolyWord::from_bits(0));
        obj.add(2).write(PolyWord::from_bits(0));

        // body[3] (= last word, obj.add(n_words-1)) holds the SIGNED byte
        // offset. const_segment_for_code computes:
        //     cp = last_word_ptr + 1 + offset_bytes / 8
        // We want cp to land ~1 GiB past the object — a guaranteed wild,
        // unmapped address. offset_bytes = 1<<30 bytes => cp jumps 2^27
        // words forward. count is then read from *(cp-1): also wild, but
        // the very first deref of cp[-1] (the count read) faults.
        let wild_offset_bytes: usize = 1usize << 30; // 1 GiB forward
        obj.add(n_words - 1)
            .write(PolyWord::from_bits(wild_offset_bytes));
    }

    // Sanity: confirm the (cp, count) the collector WILL use is wild,
    // BUT do not dereference cp here (that would fault in this preamble
    // and muddy which site faults). Just print the computed cp address.
    let obj_addr = obj as usize;
    let last_word_addr = obj_addr + (n_words - 1) * std::mem::size_of::<usize>();
    let computed_cp = last_word_addr + std::mem::size_of::<usize>() + (1usize << 30);
    eprintln!(
        "code obj body @ 0x{obj_addr:016x} (n_words={n_words}); \
         corrupt trailer makes cp -> 0x{computed_cp:016x} (count read from cp-8, then 0..count loop)"
    );
    eprintln!("running gc::collect; the F_CODE_OBJ scan will deref the wild cp ...");

    // Make the code object a LIVE root by forwarding a slot that points at
    // its body. `collect` forwards roots, copies the object to to-space,
    // then `cheney_scan` -> `scan_object` hits the F_CODE_OBJ branch on
    // the to-space copy and walks the corrupt const segment.
    let mut root = PolyWord::from_ptr(obj.cast_const());
    let _ = make_length_word; // silence unused import on some builds

    let _new_used = gc::collect(&mut alloc, |c| unsafe {
        c.forward(&mut root as *mut PolyWord);
    });

    // If we got here, no OOB fault occurred (would mean the bound check
    // landed cp inside the object). Print so a "safe" outcome is visible.
    eprintln!(
        "gc::collect returned WITHOUT fault (root now = 0x{:016x})",
        root.0
    );
}
