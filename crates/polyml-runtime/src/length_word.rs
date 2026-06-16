//! The length word that precedes every PolyML heap object.
//!
//! Layout: the top byte is flags, the remaining bytes are the object
//! length in words. Values match `vendor/polyml/libpolyml/globals.h`:
//!
//! - `F_BYTE_OBJ        = 0x01` — payload is bytes (no pointers)
//! - `F_CODE_OBJ        = 0x02` — payload is machine code + constants
//! - `F_CLOSURE_OBJ     = 0x03` — 32-in-64 closure (first word = code addr)
//! - `F_GC_MARK         = 0x04` — set during the mark phase
//! - `F_NO_OVERWRITE    = 0x08` — V flag in pexport
//! - `F_NEGATIVE_BIT    = 0x10` — sign for arbitrary precision (byte segs)
//! - `F_PROFILE_BIT     = 0x10` — overlaps NEGATIVE; word segs only
//! - `F_WEAK_BIT        = 0x20` — W flag
//! - `F_MUTABLE_BIT     = 0x40` — M flag
//! - `F_TOMBSTONE_BIT   = 0x80` — forwarding pointer (GC)
//!
//! The bottom two bits of the flag byte form the *type code*:
//! `0` = ordinary word object, `1` = byte, `2` = code, `3` = closure.
//! The shift is `8 * (sizeof(PolyWord) - 1)` which puts the flag byte
//! in the high byte of the word regardless of word size.

#![allow(clippy::cast_possible_truncation)]

use crate::poly_word::PolyWord;

// ----- Type bits (low two bits of the flag byte) -----------------------

pub const F_BYTE_OBJ: u8 = 0x01;
pub const F_CODE_OBJ: u8 = 0x02;
pub const F_CLOSURE_OBJ: u8 = 0x03;

// ----- Other flags -----------------------------------------------------

pub const F_GC_MARK: u8 = 0x04;
pub const F_NO_OVERWRITE: u8 = 0x08;
pub const F_NEGATIVE_BIT: u8 = 0x10;
pub const F_PROFILE_BIT: u8 = 0x10; // alias
pub const F_WEAK_BIT: u8 = 0x20;
pub const F_MUTABLE_BIT: u8 = 0x40;
pub const F_TOMBSTONE_BIT: u8 = 0x80;

// ----- Shift for placing flags in the top byte -------------------------

/// `8 * (sizeof(PolyWord) - 1)` — number of bits the flag byte must be
/// shifted left to land in the high byte of a `usize`.
pub const FLAGS_SHIFT: u32 = 8 * (std::mem::size_of::<usize>() as u32 - 1);

/// Mask covering the high-byte flag bits.
pub const FLAGS_MASK: usize = (0xff_usize) << FLAGS_SHIFT;

/// Mask covering the length-bits portion of a length word.
pub const LENGTH_MASK: usize = !FLAGS_MASK;

// ----- Constructor -----------------------------------------------------

/// Pack a length (in words) and a flag byte into a length word.
#[must_use]
pub const fn make_length_word(length: usize, flags: u8) -> PolyWord {
    debug_assert!(
        length & FLAGS_MASK == 0,
        "length overflows length-word field"
    );
    PolyWord::from_bits(length | ((flags as usize) << FLAGS_SHIFT))
}

#[must_use]
pub const fn length_of(word: PolyWord) -> usize {
    word.0 & LENGTH_MASK
}

#[must_use]
pub const fn flags_of(word: PolyWord) -> u8 {
    (word.0 >> FLAGS_SHIFT) as u8
}

/// Low two bits of the flag byte: the type code.
#[must_use]
pub const fn type_of(word: PolyWord) -> u8 {
    flags_of(word) & 0x03
}

#[must_use]
pub const fn is_byte_object(word: PolyWord) -> bool {
    type_of(word) == F_BYTE_OBJ
}

#[must_use]
pub const fn is_code_object(word: PolyWord) -> bool {
    type_of(word) == F_CODE_OBJ
}

#[must_use]
pub const fn is_closure_object(word: PolyWord) -> bool {
    type_of(word) == F_CLOSURE_OBJ
}

#[must_use]
pub const fn is_word_object(word: PolyWord) -> bool {
    type_of(word) == 0
}

#[must_use]
pub const fn is_mutable(word: PolyWord) -> bool {
    (flags_of(word) & F_MUTABLE_BIT) != 0
}

#[must_use]
pub const fn is_weak(word: PolyWord) -> bool {
    (flags_of(word) & F_WEAK_BIT) != 0
}

#[must_use]
pub const fn is_no_overwrite(word: PolyWord) -> bool {
    (flags_of(word) & F_NO_OVERWRITE) != 0
}

/// Recover the address and count of the constants segment of a code
/// object, mirroring the default `GetConstSegmentForCode` in
/// `vendor/polyml/libpolyml/machine_dep.h:61-67`:
///
/// ```c++
/// PolyWord* last_word = obj->Offset(obj_length - 1);
/// POLYSIGNED offset = last_word->AsSigned();
/// cp = last_word + 1 + offset / sizeof(PolyWord);
/// count = cp[-1].AsUnsigned();
/// ```
///
/// Returns `(constants_ptr, constants_count)`.
///
/// # Safety
/// `obj_ptr` must point at a fully-initialised code object as laid out
/// by [`crate::loader`]. The caller is responsible for not following
/// past the constants region.
#[must_use]
pub unsafe fn const_segment_for_code(obj_ptr: *const PolyWord) -> (*const PolyWord, usize) {
    // SAFETY: caller upholds that obj_ptr is a code object.
    unsafe {
        let lw = crate::space::MemorySpace::length_word_of(obj_ptr);
        let n_words = length_of(lw);
        // Debug-only guards: a malformed/zero-length object (e.g. after a
        // GC corruption or a stale pointer) would make `n_words - 1` wrap
        // to usize::MAX below and produce a wild pointer. Fail fast and
        // precisely here in debug/test builds; zero release overhead.
        debug_assert!(
            is_code_object(lw),
            "const_segment_for_code on non-code object: flags=0x{:02x}",
            flags_of(lw)
        );
        debug_assert!(n_words >= 2, "code object too small: n_words={n_words}");
        let last_word_ptr = obj_ptr.add(n_words - 1);
        // The trailing offset is a signed byte distance written by the
        // loader; the high bit acts as the sign. Casting from usize is
        // intentional reinterpretation.
        #[allow(clippy::cast_possible_wrap)]
        let offset_bytes = (*last_word_ptr).0 as isize;
        #[allow(clippy::cast_possible_wrap)]
        let word_bytes = std::mem::size_of::<usize>() as isize;
        let cp = last_word_ptr.add(1).offset(offset_bytes / word_bytes);
        let count = (*cp.sub(1)).0;
        (cp, count)
    }
}

/// Best-effort extract of the function-name string from a code object.
///
/// PolyML's compiler stores the function's source name (if known)
/// as the FIRST entry of the constant area. The string is a
/// `PolyStringObject` (length-prefix word + chars).
///
/// Returns `Some("name")` when the first constant looks like a
/// non-empty string, `None` otherwise (anonymous functions or
/// objects without that convention).
///
/// # Safety
/// `obj_ptr` must point at a fully-initialised code object.
#[must_use]
pub unsafe fn function_name_for_code(obj_ptr: *const PolyWord) -> Option<String> {
    // SAFETY: caller upholds.
    unsafe {
        let (cp, count) = const_segment_for_code(obj_ptr);
        if count == 0 {
            return None;
        }
        let name_word = *cp;
        if name_word.0 == 0 || (name_word.0 & 1) != 0 {
            // Anonymous code (name = 0) or a tagged value (not a string).
            return None;
        }
        let name_ptr = name_word.as_ptr::<PolyWord>();
        let lw = crate::space::MemorySpace::length_word_of(name_ptr);
        if !is_byte_object(lw) {
            return None;
        }
        // PolyStringObject: word 0 is the byte length, then chars.
        let len = (*name_ptr).0;
        if len == 0 || len > 4096 {
            return None;
        }
        let chars_ptr = name_ptr.add(1).cast::<u8>();
        let slice = std::slice::from_raw_parts(chars_ptr, len);
        std::str::from_utf8(slice).ok().map(str::to_owned)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pack_unpack_length_word() {
        let w = make_length_word(42, F_BYTE_OBJ | F_MUTABLE_BIT);
        assert_eq!(length_of(w), 42);
        assert_eq!(flags_of(w), F_BYTE_OBJ | F_MUTABLE_BIT);
        assert!(is_byte_object(w));
        assert!(is_mutable(w));
        assert!(!is_code_object(w));
    }

    #[test]
    fn type_bits_dispatch() {
        for (flag, name) in [
            (F_BYTE_OBJ, "byte"),
            (F_CODE_OBJ, "code"),
            (F_CLOSURE_OBJ, "closure"),
        ] {
            let w = make_length_word(1, flag);
            assert_eq!(type_of(w), flag, "type bits for {name}");
        }
        // Type code 0 = ordinary word object.
        let w = make_length_word(1, 0);
        assert!(is_word_object(w));
        assert!(!is_byte_object(w));
    }

    #[test]
    fn flags_shift_for_64bit_target() {
        // On 64-bit Linux (the only supported Stage-2 target), FLAGS_SHIFT
        // is 56 and FLAGS_MASK is 0xff00000000000000.
        if std::mem::size_of::<usize>() == 8 {
            assert_eq!(FLAGS_SHIFT, 56);
            assert_eq!(FLAGS_MASK, 0xff00_0000_0000_0000_usize);
        }
    }
}
