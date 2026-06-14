//! `PolyWord`: a single machine-word slot in the PolyML heap.
//!
//! Tagging scheme (see `vendor/polyml/libpolyml/globals.h:25-44`):
//!
//! - Bottom bit `= 1` → tagged integer; payload is the bits shifted
//!   right by 1 (sign-extended).
//! - Bottom bit `= 0` → object pointer; word-aligned, points one word
//!   *past* the object's length word.
//!
//! Equality and ordering on `PolyWord` are bitwise — we don't interpret
//! the payload. The runtime knows which is which from context (object
//! type flags on the containing cell, or the bit pattern itself).
//!
//! This Stage-2 implementation does **not** model 32-in-64 mode
//! (`POLYML32IN64`). Per `PLAN.md` §6 row 4, compressed pointers are
//! deferred to Stage 3.

use std::fmt;

/// The single-word PolyML value. Stored as a raw `usize` for direct
/// memory aliasing — the GC must see raw bits, not Rust enum tags.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct PolyWord(pub usize);

impl PolyWord {
    /// All zero bits. Used as a placeholder during heap construction;
    /// not a valid PolyWord in a finished heap (it would look like an
    /// untagged object pointer to address 0).
    pub const ZERO: Self = Self(0);

    /// Tag a signed integer. Caller is responsible for ensuring the
    /// value fits in `WORD_BITS - 1` bits (otherwise it should be
    /// boxed as arbitrary precision).
    #[must_use]
    #[inline(always)]
    pub const fn tagged(n: isize) -> Self {
        // ((n << 1) | 1) — relies on signed left-shift behavior
        // matching the C++ writer at globals.h:145.
        #[allow(clippy::cast_sign_loss)]
        Self(((n as usize) << 1) | 1)
    }

    /// Construct a PolyWord that contains the raw bit pattern of a
    /// pointer. Caller must ensure the pointer is word-aligned (bottom
    /// bit will be checked as 0 by `is_tagged`).
    ///
    /// Not `const fn` because `ptr as usize` is forbidden in const
    /// context (pointers don't have an integer value until runtime).
    #[must_use]
    #[inline(always)]
    pub fn from_ptr<T>(p: *const T) -> Self {
        Self(p as usize)
    }

    /// Raw constructor from a bit pattern. Avoid; prefer `tagged` or
    /// `from_ptr`.
    #[must_use]
    #[inline(always)]
    pub const fn from_bits(bits: usize) -> Self {
        Self(bits)
    }

    /// True iff the bottom bit is set (i.e. this slot holds a tagged
    /// integer rather than an object pointer).
    #[must_use]
    #[inline(always)]
    pub const fn is_tagged(self) -> bool {
        (self.0 & 1) != 0
    }

    /// True iff the bottom bit is clear AND the rest is a plausible
    /// address (not zero — zero is reserved). The runtime uses other
    /// signals (the containing object's type bits) to know whether to
    /// follow this; this is a quick filter only.
    #[must_use]
    #[inline(always)]
    pub const fn is_data_ptr(self) -> bool {
        self.0 != 0 && (self.0 & 1) == 0
    }

    /// Read the integer payload of a tagged word. Undefined behavior
    /// (in the C-spec sense) if `!is_tagged()`.
    #[must_use]
    #[inline(always)]
    pub const fn untag(self) -> isize {
        // Debug-only guard: `untag` on a pointer-shaped word is a
        // semantic bug (treating an object pointer as a tagged int).
        // Release builds keep the raw shift (the hot dispatch path).
        debug_assert!(
            self.is_tagged(),
            "untag() on a non-tagged PolyWord (likely a pointer)"
        );
        #[allow(clippy::cast_possible_wrap)]
        let s = self.0 as isize;
        s >> 1
    }

    /// Reinterpret as a raw pointer. Result is meaningless unless
    /// `is_data_ptr()` is true at the call site.
    ///
    /// Not `const fn` for the same reason as `from_ptr`.
    ///
    /// NOTE: deliberately NOT guarded with a `debug_assert` — PC values
    /// and `from_bits` raw addresses legitimately have the low bit set,
    /// and the GC treats any bit pattern as a candidate pointer.
    #[must_use]
    #[inline(always)]
    pub fn as_ptr<T>(self) -> *const T {
        self.0 as *const T
    }
}

impl fmt::Debug for PolyWord {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_tagged() {
            write!(f, "Tagged({})", self.untag())
        } else if self.0 == 0 {
            f.write_str("ZERO")
        } else {
            write!(f, "Ptr(0x{:x})", self.0)
        }
    }
}

/// Maximum value representable as a tagged `isize` on the current
/// target. See `MAXTAGGED` in `globals.h:218`.
pub const MAX_TAGGED: isize = isize::MAX >> 1;
/// Minimum value representable as a tagged `isize`.
pub const MIN_TAGGED: isize = isize::MIN >> 1;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tag_round_trip() {
        for n in [0, 1, -1, 42, -42, MAX_TAGGED, MIN_TAGGED] {
            let w = PolyWord::tagged(n);
            assert!(w.is_tagged(), "tagged for {n}");
            assert_eq!(w.untag(), n, "untag round-trip for {n}");
        }
    }

    #[test]
    fn ptr_round_trip() {
        let x: u64 = 0xdead_beef;
        let p: *const u64 = &raw const x;
        let w = PolyWord::from_ptr(p);
        assert!(!w.is_tagged());
        assert!(w.is_data_ptr());
        assert_eq!(w.as_ptr::<u64>(), p);
    }

    #[test]
    fn zero_is_neither() {
        let z = PolyWord::ZERO;
        assert!(!z.is_tagged());
        assert!(!z.is_data_ptr()); // explicitly excluded by definition
    }

    #[test]
    fn max_tagged_matches_polyml() {
        // MAXTAGGED on 64-bit is 2^62 - 1.
        assert_eq!(MAX_TAGGED, (1_isize << 62) - 1);
    }
}
