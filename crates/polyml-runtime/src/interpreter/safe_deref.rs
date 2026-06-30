//! The typed-deref predicate used **only** in untrusted mode.
//!
//! ## Why this exists (the one honest memory-safety caveat)
//!
//! The pexport image format carries **untyped** references: a well-formed,
//! in-range word can point at a *wrong-type* object (the loader-fuzz repro
//! `lf_ref_52` re-pointed a tuple field at a valid-but-wrong-type object —
//! e.g. a code object). The loader cannot reject this without whole-image
//! type inference (a limit shared with upstream Poly/ML). So when the
//! interpreter later **follows** that pointer (a field load, a call, a
//! heap read/write) it can cause real UB: an OOB read/write, a wild jump
//! (following word0 of a non-closure as a code address), or dereferencing
//! a non-pointer.
//!
//! This module is the **typed-deref predicate**: given a [`PolyWord`] and
//! the operation's expected shape, it validates the pointer-follow BEFORE
//! the unsafe use, so an untrusted image produces a **clean, deterministic
//! outcome** (a controlled "bad image" halt) instead of UB.
//!
//! ## The trusted/untrusted split (performance is sacred)
//!
//! The interpreter is the proven-fastest execution path; byte-identical
//! performance on the normal paths (`poly run bootstrap64.txt`, the REPL,
//! HOL4, Isabelle, the 7-stage self-bootstrap) is non-negotiable. So:
//!
//! - **DEFAULT = trusted** — this module is *never consulted*. Every
//!   hardened site reads `if self.untrusted { … } else { the EXACT current
//!   fast path }`, and [`SafeSpaces`] is empty / unread. Zero extra cost.
//! - **`--untrusted` = an opt-in safe mode** — every dangerous
//!   pointer-follow validates first. Slower, but only for explicitly
//!   foreign images where safety > speed.
//!
//! ## The predicate (the four checks)
//!
//! Given a `PolyWord` w and the operation's expected shape, validate:
//!
//! - **(a) tag**  — `w` is a pointer, not a tagged int (and non-zero,
//!   word-aligned).
//! - **(b) space-membership** — `w` lies within a *live* heap space (the
//!   loaded image's immutable / mutable / code spaces **plus** the live
//!   alloc space), AND there is room for its length word at `w.sub(1)`.
//!   This generalizes [`crate::gc::Collector::contains_polyword`] (one
//!   `from_start..from_end` range) to a membership test over the vector of
//!   live spaces.
//! - **(c) header sanity** — the object's length word at `w.sub(1)` gives a
//!   length such that the **whole object fits** within its containing
//!   space.
//! - **(d) per-op shape** — e.g. a field index `< object length`
//!   (`INDIRECT`), the target is a code/closure object (`CALL`), the object
//!   is byte-typed (string ops), etc. These are the per-call helpers.
//!
//! On any failure: a clean [`DerefError`], which the call site turns into
//! [`InterpError::BadImage`] — a controlled halt, never UB.

// The `unsafe impl Send/Sync for SafeSpaces` is deliberate: the raw
// pointers it holds are read-only space bounds (compared, never followed
// for mutation through the struct), aliasing the loaded image which
// outlives the interpreter — the same Send/Sync rationale as `LoadedImage`.
#![allow(clippy::non_send_fields_in_send_ty)]
// Several doc comments lead with a deliberately full sentence > the nursery
// "first paragraph too long" threshold; matching the crate's house style.
#![allow(clippy::too_long_first_doc_paragraph)]

use crate::length_word;
use crate::poly_word::PolyWord;

/// A half-open address range `[start, end)` over `PolyWord` slots,
/// identifying one live memory space.
#[derive(Clone, Copy, Debug)]
pub struct SpaceRange {
    pub start: *const PolyWord,
    pub end: *const PolyWord,
}

impl SpaceRange {
    #[inline]
    fn contains(&self, p: *const PolyWord) -> bool {
        p >= self.start && p < self.end
    }
}

/// The set of live spaces consulted by the predicate in untrusted mode.
///
/// Holds the three **image** spaces (immutable / mutable / code), which are
/// tenured (their bounds are fixed for the run). The **alloc** space is NOT
/// stored here — it is swapped wholesale by every Cheney GC, so its bounds
/// are read *live* from the interpreter on each check (see
/// [`crate::interpreter::Interpreter`]'s `alloc_space_range`).
///
/// In trusted mode this is `Default` (all-empty) and never read.
#[derive(Clone, Default)]
pub struct SafeSpaces {
    /// The fixed image spaces. A small `Vec` (≤ 3 entries) scanned
    /// linearly — cheap, and only on the explicitly-slow untrusted path.
    image: Vec<SpaceRange>,
}

// The raw pointers here alias the loaded image spaces, which outlive the
// interpreter. They are only ever read (range compares), never followed
// for mutation through this struct. Same Send/Sync rationale as
// `LoadedImage`.
unsafe impl Send for SafeSpaces {}
unsafe impl Sync for SafeSpaces {}

impl SafeSpaces {
    /// Register one image space `[base, base + used_words)`. A zero-length
    /// or null space is skipped (nothing to point into).
    ///
    /// The end bound is computed by *integer* address arithmetic (not
    /// pointer `.add`), so this stays a safe `pub fn`: the predicate only
    /// ever does range *comparisons* against these bounds — it never
    /// dereferences `base` here. (The single guarded deref of a validated
    /// pointer happens in [`Self::validate_obj`].)
    pub fn push_image_space(&mut self, base: *const PolyWord, used_words: usize) {
        if base.is_null() || used_words == 0 {
            return;
        }
        let end_addr = (base as usize).wrapping_add(used_words * std::mem::size_of::<PolyWord>());
        let end = end_addr as *const PolyWord;
        self.image.push(SpaceRange { start: base, end });
    }

    /// Whether any image space is registered. When false the predicate has
    /// nothing to validate against and treats every pointer as out-of-space
    /// (the safe default: reject rather than follow).
    #[must_use]
    pub fn is_configured(&self) -> bool {
        !self.image.is_empty()
    }

    /// Find the image space containing `p`, if any. The alloc space is
    /// handled by the caller (it is dynamic).
    #[inline]
    fn image_space_of(&self, p: *const PolyWord) -> Option<SpaceRange> {
        self.image.iter().copied().find(|s| s.contains(p))
    }

    /// Public membership over the IMAGE spaces only (the alloc space is
    /// dynamic and handled by the interpreter). Returns the containing
    /// space's range, if any.
    #[must_use]
    pub fn space_containing(&self, p: *const PolyWord) -> Option<SpaceRange> {
        self.image_space_of(p)
    }

    /// The image-space ranges as `(start, end)` integer pairs — for handing
    /// to an RTS-side validator that doesn't depend on the raw-pointer type.
    #[must_use]
    pub fn image_ranges_usize(&self) -> Vec<(usize, usize)> {
        self.image
            .iter()
            .map(|s| (s.start as usize, s.end as usize))
            .collect()
    }
}

/// Why a pointer-follow was rejected in untrusted mode. Each maps to a
/// clean halt; none is UB.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DerefError {
    /// The word was a tagged int / zero / misaligned where a pointer was
    /// required.
    NotAPointer,
    /// The pointer did not lie within any live heap space (a wild pointer,
    /// or a dangling/out-of-image address).
    NotInSpace,
    /// The object's length word claims a length that would run past the end
    /// of its containing space (a forged / corrupt header).
    BadHeader,
    /// A field/element index was `>=` the object's length (OOB access).
    IndexOutOfBounds,
    /// The object's type was wrong for the operation (e.g. CALL on a
    /// non-closure/non-code object, a byte op on a word object).
    WrongType,
    /// A byte offset/length window ran past the object's byte payload.
    ByteRangeOob,
}

impl std::fmt::Display for DerefError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::NotAPointer => "expected a heap pointer (got a tagged int / null / misaligned)",
            Self::NotInSpace => "pointer is not within any live heap space (wild/dangling)",
            Self::BadHeader => "object length word runs past the end of its space (forged header)",
            Self::IndexOutOfBounds => "field/element index out of bounds for the object",
            Self::WrongType => "object type is wrong for the operation",
            Self::ByteRangeOob => "byte range runs past the object's payload",
        };
        f.write_str(s)
    }
}

/// A validated object handle: a pointer that has passed the tag,
/// space-membership and header-sanity checks (predicate steps a–c). It
/// carries the verified length word so per-op shape checks (step d) are
/// pure arithmetic with no further deref.
#[derive(Clone, Copy)]
pub struct ValidObj {
    /// The (validated) object body pointer.
    pub ptr: *const PolyWord,
    /// The object's length word (already read safely from `ptr.sub(1)`).
    pub length_word: PolyWord,
    /// Number of body words available from `ptr` (from the length word).
    pub n_words: usize,
}

impl ValidObj {
    /// Field index `idx` is in-bounds for an ordinary/word/closure read.
    #[inline]
    pub fn check_word_index(&self, idx: usize) -> Result<(), DerefError> {
        if idx < self.n_words {
            Ok(())
        } else {
            Err(DerefError::IndexOutOfBounds)
        }
    }

    /// The object is a byte object and `[off, off+len)` fits its byte
    /// payload (used for string / byte-block ops). `n_words` words = at
    /// most `n_words * size_of::<usize>()` bytes; the *exact* payload of a
    /// string is shorter but never longer, so this is a sound upper bound
    /// against OOB into other objects.
    #[inline]
    pub fn check_byte_range(&self, off: usize, len: usize) -> Result<(), DerefError> {
        let max_bytes = self.n_words.saturating_mul(std::mem::size_of::<usize>());
        match off.checked_add(len) {
            Some(end) if end <= max_bytes => Ok(()),
            _ => Err(DerefError::ByteRangeOob),
        }
    }

    /// The object is a code object.
    #[inline]
    pub fn require_code(&self) -> Result<(), DerefError> {
        if length_word::is_code_object(self.length_word) {
            Ok(())
        } else {
            Err(DerefError::WrongType)
        }
    }

    /// The object is mutable (required for an assignment / store). A store
    /// into an immutable object is both a soundness bug (it could mutate an
    /// object the GC treats as read-only / shared) and exactly the
    /// wrong-type primitive an untrusted image would use to corrupt the
    /// heap; reject it.
    #[inline]
    pub fn require_mutable(&self) -> Result<(), DerefError> {
        if length_word::is_mutable(self.length_word) {
            Ok(())
        } else {
            Err(DerefError::WrongType)
        }
    }

    /// The object is NOT a byte/code object (i.e. an ordinary word or
    /// closure object whose body slots are PolyWords) — required before
    /// writing a PolyWord into a word slot.
    #[inline]
    pub fn require_word_typed(&self) -> Result<(), DerefError> {
        if length_word::is_byte_object(self.length_word)
            || length_word::is_code_object(self.length_word)
        {
            Err(DerefError::WrongType)
        } else {
            Ok(())
        }
    }
}

impl SafeSpaces {
    /// Run predicate steps (a)–(c): the word is a pointer, lies inside a
    /// live space (image space here, or the alloc range passed by the
    /// caller), and its header length keeps the whole object inside that
    /// space. Returns a [`ValidObj`] carrying the verified header.
    ///
    /// `alloc` is the live alloc-space range (read fresh by the caller each
    /// call, since the GC swaps it); `None` if there is no alloc space.
    ///
    /// # Safety
    /// This function performs exactly ONE read — the length word at
    /// `p.sub(1)` — and only AFTER confirming `p` is inside a space with
    /// room for that word. That read is therefore in-bounds for the
    /// space's allocation. No other deref happens here.
    pub fn validate_obj(
        &self,
        w: PolyWord,
        alloc: Option<SpaceRange>,
    ) -> Result<ValidObj, DerefError> {
        // (a) tag + alignment + non-null.
        if !w.is_data_ptr() {
            return Err(DerefError::NotAPointer);
        }
        if w.0 & (std::mem::size_of::<usize>() - 1) != 0 {
            return Err(DerefError::NotAPointer);
        }
        let p = w.as_ptr::<PolyWord>();

        // (b) space-membership: find the containing space (image or alloc).
        let space = match self.image_space_of(p) {
            Some(s) => s,
            None => match alloc {
                Some(a) if a.contains(p) => a,
                _ => return Err(DerefError::NotInSpace),
            },
        };

        // There must be room for the length word at p.sub(1): p must be
        // strictly above the space start (the length-word slot lies within
        // the same space).
        if p <= space.start {
            return Err(DerefError::BadHeader);
        }

        // (c) header sanity: read the length word (now provably in-bounds)
        // and confirm the whole object fits within the space.
        // SAFETY: p > space.start and p < space.end, both within the same
        // live allocation, so p.sub(1) is a valid readable slot.
        let length_word = unsafe { *p.sub(1) };
        let n_words = length_word::length_of(length_word);
        // The object body occupies [p, p + n_words); it must fit the space.
        // Use a pointer-distance check that cannot overflow: available
        // words from p to end.
        // SAFETY: p and space.end are both within / one-past the same
        // allocation, so offset_from is defined.
        let avail = unsafe { space.end.offset_from(p) };
        if avail < 0 || (n_words as isize) > avail {
            return Err(DerefError::BadHeader);
        }

        Ok(ValidObj {
            ptr: p,
            length_word,
            n_words,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::space::{MemorySpace, SpaceKind, set_length_word};

    fn space_range(space: &MemorySpace) -> SpaceRange {
        let base = space
            .iter()
            .next()
            .map_or(std::ptr::null(), std::ptr::from_ref::<PolyWord>);
        // Fall back: if empty, use storage start.
        let base = if base.is_null() {
            space.storage_bytes().as_ptr().cast::<PolyWord>()
        } else {
            base
        };
        SpaceRange {
            start: base,
            // SAFETY: used_words within the storage.
            end: unsafe { base.add(space.used_words()) },
        }
    }

    #[test]
    fn rejects_tagged_int() {
        let spaces = SafeSpaces::default();
        let r = spaces.validate_obj(PolyWord::tagged(5), None);
        assert_eq!(r.err(), Some(DerefError::NotAPointer));
    }

    #[test]
    fn rejects_wild_pointer() {
        let mut spaces = SafeSpaces::default();
        let mut space = MemorySpace::new(64, SpaceKind::Immutable);
        let _ = space.alloc(2);
        let r = space_range(&space);
        spaces.push_image_space(r.start, space.used_words());
        // A pointer far outside the space.
        let wild = PolyWord::from_bits(0x4000_0000_0000_usize & !1);
        assert_eq!(
            spaces.validate_obj(wild, None).err(),
            Some(DerefError::NotInSpace)
        );
    }

    #[test]
    fn accepts_valid_object_and_checks_index() {
        let mut space = MemorySpace::new(64, SpaceKind::Immutable);
        let obj = space.alloc(3);
        unsafe { set_length_word(obj, 3, 0) };
        let r = space_range(&space);
        let mut spaces = SafeSpaces::default();
        spaces.push_image_space(r.start, space.used_words());
        let w = PolyWord::from_ptr(obj.cast_const());
        let v = spaces.validate_obj(w, None).expect("valid obj");
        assert_eq!(v.n_words, 3);
        assert!(v.check_word_index(2).is_ok());
        assert_eq!(
            v.check_word_index(3).err(),
            Some(DerefError::IndexOutOfBounds)
        );
    }

    #[test]
    fn rejects_forged_oversized_header() {
        let mut space = MemorySpace::new(64, SpaceKind::Immutable);
        let obj = space.alloc(2);
        // Forge a length word claiming a huge object that runs past the
        // space end.
        unsafe { set_length_word(obj, 1_000_000, 0) };
        let r = space_range(&space);
        let mut spaces = SafeSpaces::default();
        spaces.push_image_space(r.start, space.used_words());
        let w = PolyWord::from_ptr(obj.cast_const());
        assert_eq!(
            spaces.validate_obj(w, None).err(),
            Some(DerefError::BadHeader)
        );
    }

    #[test]
    fn per_op_shape_checks() {
        use crate::length_word::{F_CODE_OBJ, F_MUTABLE_BIT};
        let mut space = MemorySpace::new(64, SpaceKind::Immutable);

        // A mutable word object.
        let m = space.alloc(2);
        unsafe { set_length_word(m, 2, F_MUTABLE_BIT) };
        // An immutable code object.
        let c = space.alloc(3);
        unsafe { set_length_word(c, 3, F_CODE_OBJ) };
        // An immutable byte object (4 bytes).
        let b = space.alloc(1);
        unsafe { set_length_word(b, 1, crate::length_word::F_BYTE_OBJ) };

        let r = space_range(&space);
        let mut spaces = SafeSpaces::default();
        spaces.push_image_space(r.start, space.used_words());

        let vm = spaces
            .validate_obj(PolyWord::from_ptr(m.cast_const()), None)
            .unwrap();
        assert!(vm.require_mutable().is_ok());
        assert_eq!(vm.require_code().err(), Some(DerefError::WrongType));
        assert!(vm.require_word_typed().is_ok());

        let vc = spaces
            .validate_obj(PolyWord::from_ptr(c.cast_const()), None)
            .unwrap();
        assert!(vc.require_code().is_ok());
        assert_eq!(vc.require_mutable().err(), Some(DerefError::WrongType));
        // A code object is not "word-typed" for a PolyWord STORE.
        assert_eq!(vc.require_word_typed().err(), Some(DerefError::WrongType));

        let vb = spaces
            .validate_obj(PolyWord::from_ptr(b.cast_const()), None)
            .unwrap();
        // 1 word = 8 bytes upper bound; [0,8) ok, [0,9) and [4,8)+1 not.
        assert!(vb.check_byte_range(0, 8).is_ok());
        assert_eq!(
            vb.check_byte_range(0, 9).err(),
            Some(DerefError::ByteRangeOob)
        );
        assert_eq!(
            vb.check_byte_range(usize::MAX, 1).err(),
            Some(DerefError::ByteRangeOob)
        );
        // A byte object is not word-typed.
        assert_eq!(vb.require_word_typed().err(), Some(DerefError::WrongType));
    }
}
