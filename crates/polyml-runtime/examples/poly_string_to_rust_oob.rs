//! AUDIT REPRO (unsafe-audit finding #8) — RTS poly_string_to_rust OOB read.
//!
//! `poly_string_to_rust` (rts.rs:3314) decodes a PolyString filename/arg for
//! the file-IO + entry-point + process-env RTS paths
//! (`open_file_input`/`open_file_output`/`open_directory`/
//! `PolyCreateEntryPointObject`/`PolySpecificGeneral`). It does:
//!
//!     let p = s.as_ptr::<PolyWord>();
//!     let len = (*p).0;                       // word 0 = byte length
//!     if len > 1_000_000 { return None; }     // the ONLY old guard
//!     let chars_ptr = p.add(1).cast::<u8>();
//!     let slice = from_raw_parts(chars_ptr, len);
//!     String::from_utf8(slice.to_vec()).ok()
//!
//! BEFORE the fix: the only validation was `is_data_ptr(s)` (LSB clear,
//! non-zero) + `len > 1_000_000 -> None`. There was NO `is_byte_object` check
//! (so a non-string pointer's word 0 is mis-read as a length) and NO
//! cross-check of `len` against the object's real byte body — so a byte object
//! whose stored word-0 length LIES (e.g. 900_000 in a 1-word object) makes
//! `from_raw_parts(chars_ptr, len)` over-read up to ~1 MB past the 8-byte body.
//! `String::from_utf8` then copies the whole over-long slice (the OOB read has
//! already happened before any UTF-8 validation can reject it).
//!
//! THREAT MODEL: the filename arg arrives from the trusted compiler/basis as a
//! real PolyStringObject, so type-safe SML always passes a well-formed string.
//! A hand-corrupted image (or hostile SML via `RunCall.rtsCallFull1
//! "PolyBasicIOGeneral"` + `RunCall.unsafeCast` to forge the arg) can pass a
//! byte object whose word-0 length over-runs its body. Same exposure class as
//! the documented loader untyped-ref residual (lf_ref_52, task #96): a value
//! that is pointer-shaped but lies about its size.
//!
//! This harness reproduces the exact unsafe operation WITHOUT the full RTS
//! dispatch (poly_string_to_rust is module-private): build a tiny mutable
//! space, lay down a 1-WORD byte object whose word-0 "length" is 256 MiB, then
//! mirror the unguarded slice construction and touch the slice tail. That
//! deref walks off the mapped allocation -> SIGSEGV.
//!
//! STATUS: the real `poly_string_to_rust` is NOW guarded (rts.rs:
//! `is_byte_object` + `size_of::<usize>() + len <= byte_body(s)`, returns None
//! on violation; unit test `poly_string_to_rust_rejects_oversized_length`).
//! This example shows the RAW unsafe operation the guard protects — it still
//! faults because it deliberately bypasses the guard to demonstrate the
//! invariant. It is a standing repro of the underlying hazard, like the
//! sibling `write_array_oob` / `do_call_bad_code_word` examples.
//!
//! Run:
//!   cargo run --release -p polyml-runtime --example poly_string_to_rust_oob
//! Expect: SIGSEGV (exit 139) from the OOB read of the over-long slice.

use polyml_runtime::PolyWord;
use polyml_runtime::length_word::{F_BYTE_OBJ, F_MUTABLE_BIT};
use polyml_runtime::space::{MemorySpace, SpaceKind, set_length_word};

fn main() {
    let mut alloc = MemorySpace::new(64, SpaceKind::Mutable);

    // A 1-word byte object: this is the would-be PolyString `s`. Its body is
    // only 8 bytes (word 0). We set word 0 to a forged, oversized "byte
    // length" (256 MiB) — exactly the lie a corrupted filename arg carries.
    let n_words = 1usize;
    let s_obj = alloc.alloc(n_words);
    let forged_len: usize = 256 * 1024 * 1024; // 256 MiB past an 8-byte body
    unsafe {
        set_length_word(s_obj, n_words, F_BYTE_OBJ | F_MUTABLE_BIT);
        // word 0 = the stored byte length (the lie).
        s_obj.add(0).write(PolyWord::from_bits(forged_len));
    }
    let s = PolyWord::from_ptr(s_obj.cast_const());

    // EXACT mirror of poly_string_to_rust's pre-fix body (rts.rs:3320-3327).
    // is_data_ptr(s) is true; the only old guard `len > 1_000_000` — note our
    // forged_len is WAY over that, so even the old cap would reject THIS value.
    // The real hazard the cap missed is a len in (8, 1_000_000]: still an OOB
    // read of up to ~1 MB. We use 256 MiB here only to force a deterministic
    // page fault for the demo; the guard added by the fix
    // (size_of::<usize>() + len <= byte_body) rejects BOTH ranges.
    let p = s.as_ptr::<PolyWord>();
    let len = unsafe { (*p).0 };
    eprintln!(
        "byte body = 8 bytes; word-0 'length' = {len}; constructing a {len}-byte \
         slice at body+8 (mirrors poly_string_to_rust rts.rs:3325-3326 with NO \
         is_byte_object / len-vs-body bounds check)"
    );
    let chars_ptr = unsafe { p.add(1).cast::<u8>() };
    let slice = unsafe { std::slice::from_raw_parts(chars_ptr, len) };

    // poly_string_to_rust then does slice.to_vec() (reads every byte). Touch
    // the tail to force the OOB read to fault. (Volatile so it can't be elided.)
    let tail = unsafe { std::ptr::read_volatile(slice.as_ptr().add(len - 1)) };
    eprintln!("read OOB tail byte = {tail} -- UNEXPECTED (no fault occurred)");
    std::process::exit(0);
}
