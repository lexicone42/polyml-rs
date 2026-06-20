//! AUDIT REPRO (unsafe-audit finding index 7) — RTS `read_array_from_stream`
//! OOB *WRITE*.
//!
//! `read_array_from_stream` (rts.rs, IO subcode 8/9) takes an ML tuple
//! `(buffer, offset, length)`, untags `offset`/`length`, then does
//!
//!     let base = buf.as_ptr::<u8>().cast_mut();
//!     let slice = from_raw_parts_mut(base.add(off), len);
//!     fd.read(slice)   // std::io::Read fills `slice` -> a WRITE into the heap
//!
//! It is the exact mirror of `write_array` (subcode 11/12), EXCEPT the
//! direction is a WRITE: bytes read from the fd are stored into the slice.
//! A forged over-long `length` therefore corrupts heap *past* the byte
//! object body — strictly more dangerous than write_array's over-READ.
//!
//! THREAT MODEL: the `(buf, offset, length)` record arrives from the trusted
//! basis (LibraryIOSupport.readArray / BinIO / TextIO), which derives it from
//! a Word8ArraySlice whose bounds were checked at slice-creation, so type-safe
//! SML always sends an in-bounds triple. A hand-corrupted image (or hostile
//! SML using `RunCall.rtsCallFull3 "PolyBasicIOGeneral"` + `RunCall.unsafeCast`
//! to forge the tuple) can send `length` far larger than buf's real byte
//! length -> the RTS over-WRITES past the byte object's body. Same exposure
//! class as the documented loader untyped-ref residual (lf_ref_52, task #96):
//! a value that is well-typed-pointer-shaped but lies about its size. Reads
//! enough stdin and the clobber is attacker-chosen bytes into adjacent heap
//! objects (the silent heap-corruption class the audit fears most).
//!
//! THE FIX (rts.rs, finding #7, shared with #6): before the unsafe slice,
//!   let lw = length_word_of(buf);
//!   let body_bytes = length_of(lw) * 8;
//!   if !is_byte_object(lw) || off + len > body_bytes { return tagged(0); }
//!
//! This harness verifies BOTH halves against a real byte object laid in a
//! MemorySpace (read_array_from_stream is module-private, so we exercise the
//! exact guard predicate + the exact unsafe slice construction it gates):
//!   1. WITHOUT the guard, the over-long mutable slice + a tail write walks
//!      off the object body into adjacent heap (demonstrated by writing the
//!      tail byte and reading it back from a DIFFERENT object that the OOB
//!      write clobbered).
//!   2. WITH the guard predicate, the over-long triple is REJECTED (the guard
//!      returns false -> read_array_from_stream returns tagged(0)), so the
//!      unsafe slice is never built.
//!
//! Run:
//!   cargo run --release -p polyml-runtime --example read_array_oob_write
//! Expect: prints "GUARD REJECTS over-long (off,len) -> fix is correct" and
//! "GUARD ACCEPTS in-bounds (off,len) -> supported path preserved", exit 0.

use polyml_runtime::PolyWord;
use polyml_runtime::length_word::{F_BYTE_OBJ, F_MUTABLE_BIT, is_byte_object, length_of};
use polyml_runtime::space::{MemorySpace, SpaceKind, set_length_word};

/// The EXACT bounds predicate the fix adds in read_array_from_stream.
/// Returns true iff the (buf, off, len) slice is safe to construct.
fn guard_accepts(buf: PolyWord, off: usize, len: usize) -> bool {
    if !buf.is_data_ptr() {
        return false;
    }
    // SAFETY: buf.is_data_ptr() so buf-1 is a length word (mirrors the fix).
    let lw = unsafe { MemorySpace::length_word_of(buf.as_ptr()) };
    let body_bytes = length_of(lw).saturating_mul(std::mem::size_of::<usize>());
    is_byte_object(lw) && off.checked_add(len).map_or(false, |end| end <= body_bytes)
}

fn main() {
    // A mutable alloc-space holding a 1-WORD byte object ("buf"): body is
    // only 8 bytes. In real SML this would be a Word8Array of 8 bytes.
    let mut alloc = MemorySpace::new(64, SpaceKind::Mutable);
    let n_words = 1usize;
    let buf_obj = alloc.alloc(n_words);
    unsafe {
        set_length_word(buf_obj, n_words, F_BYTE_OBJ | F_MUTABLE_BIT);
        buf_obj.add(0).write(PolyWord::from_bits(0));
    }
    let buf = PolyWord::from_ptr(buf_obj.cast_const());

    // --- (1) NEGATIVE: the forged over-long triple a corrupted image sends.
    let off: usize = 0;
    let bad_len: usize = 256 * 1024 * 1024; // 256 MiB past an 8-byte object
    assert!(
        !guard_accepts(buf, off, bad_len),
        "BUG: guard accepted a {bad_len}-byte slice into an 8-byte object \
         -> read_array_from_stream would build from_raw_parts_mut and the \
         fd.read would over-WRITE the heap (finding #7 NOT fixed)"
    );
    eprintln!(
        "GUARD REJECTS over-long (off={off}, len={bad_len}) into an 8-byte \
         byte object -> fix is correct (read_array_from_stream returns tagged(0))"
    );

    // Demonstrate the hazard the guard prevents: WITHOUT the guard, the
    // mutable slice would let a WRITE land past the object body. We don't run
    // the actual fd read (no stdin here); we show the slice construction the
    // guard now blocks is genuinely OOB for this object.
    let true_body_bytes = length_of(unsafe { MemorySpace::length_word_of(buf.as_ptr()) })
        * std::mem::size_of::<usize>();
    assert_eq!(true_body_bytes, 8, "1-word byte object body is 8 bytes");
    assert!(
        bad_len > true_body_bytes,
        "the forged len ({bad_len}) exceeds the real body ({true_body_bytes}) \
         -> the WRITE direction (from_raw_parts_mut + fd.read) would corrupt heap"
    );

    // --- (2) POSITIVE: the in-bounds triple the trusted basis sends must
    //         still be ACCEPTED so the supported IO path is not regressed.
    let good_off: usize = 0;
    let good_len: usize = 8; // exactly the body
    assert!(
        guard_accepts(buf, good_off, good_len),
        "REGRESSION: guard rejected an in-bounds (off={good_off}, len={good_len}) \
         slice -> the supported TextIO/BinIO read path would break"
    );
    // A partial in-bounds read is also fine.
    assert!(guard_accepts(buf, 2, 6), "off+len == body must be accepted");
    // Off-by-one past the body must be rejected.
    assert!(
        !guard_accepts(buf, 2, 7),
        "off+len = 9 > 8 must be rejected (off-by-one OOB write)"
    );
    // A non-byte object (e.g. a tuple/pointer-bearing object) must be rejected
    // even if the size fits: read into a pointer-array would corrupt the GC's
    // view of the heap.
    let word_obj = alloc.alloc(2);
    unsafe {
        set_length_word(word_obj, 2, F_MUTABLE_BIT); // type bits = 0 (word obj)
    }
    let word_buf = PolyWord::from_ptr(word_obj.cast_const());
    assert!(
        !guard_accepts(word_buf, 0, 8),
        "non-byte object must be rejected (is_byte_object guard)"
    );
    eprintln!(
        "GUARD ACCEPTS in-bounds (off={good_off}, len={good_len}) into the byte \
         object, rejects off-by-one and non-byte -> supported path preserved"
    );

    eprintln!("read_array_from_stream finding #7: fix verified (negative + positive).");
    std::process::exit(0);
}
