//! AUDIT REPRO (unsafe-audit finding #6) — RTS write_array / read_array OOB.
//!
//! `write_array` (rts.rs:3009, IO subcode 11/12) and
//! `read_array_from_stream` (rts.rs:3539, subcode 8/9) take an ML tuple
//! `(vec, offset, length)`, untag `offset`/`length`, then do
//!
//!     let base = vec.as_ptr::<u8>();
//!     let slice = from_raw_parts(base.add(off), len);   // write: read of slice
//!     // (read_array uses from_raw_parts_mut + Read::read -> a WRITE)
//!
//! with NO check that `off + len <= byte_length(vec)`. The only validation
//! is `is_data_ptr(vec)` + `is_tagged(offset/length)` — type, not bounds.
//!
//! THREAT MODEL: the (vec, offset, length) record arrives from the trusted
//! basis (LibraryIOSupport.writeArray), which derives it from a slice that
//! was bounds-checked at slice-creation time, so type-safe SML always sends
//! an in-bounds triple. A hand-corrupted image (or hostile SML using
//! `RunCall.rtsCallFull3 "PolyBasicIOGeneral"` + `RunCall.unsafeCast` to
//! forge the tuple) can send `length` far larger than vec's real byte
//! length -> the RTS over-reads (write_array) / over-WRITES
//! (read_array_from_stream) past the byte object's body. Same exposure
//! class as the documented loader untyped-ref residual (lf_ref_52,
//! task #96): a value that is well-typed-pointer-shaped but lies about its
//! size.
//!
//! This harness reproduces the exact unsafe operation WITHOUT the full RTS
//! dispatch (write_array is module-private): build a tiny mutable space,
//! lay down a 1-word byte object near the END of the space, then mirror
//! write_array's `from_raw_parts(base.add(off), len)` with a `len` that
//! runs ~256 MiB past the object body, and touch the tail of the slice.
//! That deref walks off the mapped allocation -> SIGSEGV.
//!
//! STATUS: the real `write_array` / `read_array_from_stream` are NOW guarded
//! (rts.rs: `off + len <= byte_length(vec)` + `is_byte_object` check, returns
//! the "did nothing" stub on violation; unit test `write_read_array_bounds_guard`).
//! This example shows the RAW unsafe operation the guard protects — it still
//! faults because it deliberately bypasses the guard to demonstrate the
//! invariant. It is a standing repro of the underlying hazard, like the
//! sibling `do_call_bad_code_word` / `gc_code_obj_bad_trailer` examples.
//!
//! Run:
//!   cargo run --release -p polyml-runtime --example write_array_oob
//! Expect: SIGSEGV (exit 139) from the OOB read of the over-long slice.

use polyml_runtime::PolyWord;
use polyml_runtime::length_word::{F_BYTE_OBJ, F_MUTABLE_BIT};
use polyml_runtime::space::{MemorySpace, SpaceKind, set_length_word};

fn main() {
    // A small alloc-space. We deliberately place a 1-WORD byte object so
    // the body is only 8 bytes; the over-long slice reaches far past it.
    let mut alloc = MemorySpace::new(64, SpaceKind::Mutable);

    // A 1-word byte object: this is `vec`. In real SML this would be a
    // Word8Vector/CharArray of 8 bytes.
    let n_words = 1usize;
    let vec_obj = alloc.alloc(n_words);
    unsafe {
        set_length_word(vec_obj, n_words, F_BYTE_OBJ | F_MUTABLE_BIT);
        vec_obj.add(0).write(PolyWord::from_bits(0)); // 8 zero bytes
    }
    let vec = PolyWord::from_ptr(vec_obj.cast_const());

    // The forged tuple fields. In write_array:
    //   off = offset.untag() as usize
    //   len = length.untag() as usize
    // The basis would send off=0, len<=8. A corrupted image sends a huge
    // len. (offset/length are tagged ints; we mirror the post-untag values.)
    let off: usize = 0;
    let len: usize = 256 * 1024 * 1024; // 256 MiB past an 8-byte object

    // EXACT mirror of write_array's unsafe slice construction (rts.rs:3036).
    // is_data_ptr(vec) is true (it IS a pointer); offset/length would be
    // tagged ints -> all of write_array's guards pass. The missing guard is
    // `off + len <= length_of(length_word_of(vec)) * 8`.
    let base = vec.as_ptr::<u8>();
    eprintln!(
        "vec body = 8 bytes; constructing a {len}-byte slice at base+{off} \
         (mirrors write_array rts.rs:3036-3037 with NO off+len bounds check)"
    );
    let slice = unsafe { std::slice::from_raw_parts(base.add(off), len) };

    // write_array then hands `slice` to Write::write, which reads every
    // byte. Touch the tail to force the OOB read to fault. (Use a volatile
    // read so the optimiser can't elide it.)
    let tail = unsafe { std::ptr::read_volatile(slice.as_ptr().add(len - 1)) };
    eprintln!("read OOB tail byte = {tail} -- UNEXPECTED (no fault occurred)");
    std::process::exit(0);
}
