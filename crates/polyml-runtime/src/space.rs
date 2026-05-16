//! `MemorySpace`: a contiguous, fixed-size block of `PolyWord` storage
//! that PolyML objects are laid out within.
//!
//! Each space matches one of the GC-relevant memory classes from
//! `vendor/polyml/libpolyml/memmgr.h`:
//!
//! - **immutable** — permanent immutable objects (the bulk of a heap)
//! - **mutable**   — permanent mutable objects (refs, arrays, RTS state)
//! - **code**      — code objects; logically separate because once a
//!   GC settles, these would be page-protected read-only + executable.
//!
//! Stage-2 simplification: storage is plain heap memory (`Box<[PolyWord]>`)
//! with stable addresses. We do NOT yet `mmap` executable pages for
//! the code space — that comes in Phase 2.2 when we actually run code.
//!
//! Bump-allocation only; no per-object frees within a space (PolyML
//! does compaction via the major GC, not free-lists).

use crate::length_word;
use crate::poly_word::PolyWord;

/// What kind of objects live in a space, plus the GC-relevant flags.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpaceKind {
    Immutable,
    Mutable,
    Code,
}

/// A fixed-capacity, bump-allocated space of `PolyWord` slots.
///
/// Storage is in a `Box<[PolyWord]>` so the address of any slot is
/// stable for the lifetime of this `MemorySpace`. Allocation is
/// bottom-up (lower addresses first); PolyML's runtime conventionally
/// uses top-down within local heaps, but for permanent spaces
/// populated at load the direction doesn't matter.
pub struct MemorySpace {
    storage: Box<[PolyWord]>,
    used: usize,
    kind: SpaceKind,
}

impl MemorySpace {
    /// Create a space holding up to `capacity_words` `PolyWord` slots.
    #[must_use]
    pub fn new(capacity_words: usize, kind: SpaceKind) -> Self {
        let storage = vec![PolyWord::ZERO; capacity_words].into_boxed_slice();
        Self {
            storage,
            used: 0,
            kind,
        }
    }

    #[must_use]
    pub const fn kind(&self) -> SpaceKind {
        self.kind
    }

    #[must_use]
    pub const fn used_words(&self) -> usize {
        self.used
    }

    #[must_use]
    pub fn capacity_words(&self) -> usize {
        self.storage.len()
    }

    /// Iterate every slot in the space, in laid-out order. Useful for
    /// debug dumps and post-load validation.
    pub fn iter(&self) -> std::slice::Iter<'_, PolyWord> {
        self.storage[..self.used].iter()
    }
}

impl<'a> IntoIterator for &'a MemorySpace {
    type Item = &'a PolyWord;
    type IntoIter = std::slice::Iter<'a, PolyWord>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl MemorySpace {

    /// Bump-allocate space for an object of `n_words` words, plus its
    /// preceding length word. Returns the **object pointer** — the
    /// address of the *first body word*, with the length word at offset
    /// `-1`. The length word is initialised to zero; the caller is
    /// expected to overwrite it via [`set_length_word`].
    ///
    /// # Panics
    /// Panics if the space is exhausted. In Monday-milestone code the
    /// loader pre-sizes spaces; an exhaustion here is a sizing bug, not
    /// a runtime condition.
    pub fn alloc(&mut self, n_words: usize) -> *mut PolyWord {
        let length_idx = self.used;
        let body_idx = length_idx + 1;
        let new_used = body_idx + n_words;
        assert!(
            new_used <= self.storage.len(),
            "MemorySpace {:?} exhausted: requested {n_words}, used {}/{}",
            self.kind,
            self.used,
            self.storage.len()
        );
        self.used = new_used;
        // SAFETY: body_idx is in-bounds because we asserted above.
        unsafe { self.storage.as_mut_ptr().add(body_idx) }
    }

    /// Read the length word that precedes the given object pointer.
    ///
    /// # Safety
    /// `obj_ptr` must have been returned by an `alloc` on **this**
    /// `MemorySpace`. Crossing-space lookups are undefined.
    #[must_use]
    pub unsafe fn length_word_of(obj_ptr: *const PolyWord) -> PolyWord {
        // SAFETY: precondition.
        unsafe { *obj_ptr.sub(1) }
    }

    /// Bytes covered by the space's storage. Useful for the future
    /// mmap-and-protect path.
    #[must_use]
    pub fn storage_bytes(&self) -> &[u8] {
        // SAFETY: PolyWord is repr(transparent) over usize; bit-cast
        // for a read-only byte view is well-defined.
        unsafe {
            std::slice::from_raw_parts(
                self.storage.as_ptr().cast::<u8>(),
                std::mem::size_of_val::<[PolyWord]>(&self.storage),
            )
        }
    }
}

/// Write the length word at offset `-1` from an object pointer.
///
/// # Safety
/// `obj_ptr` must have come from a `MemorySpace::alloc` call.
pub unsafe fn set_length_word(obj_ptr: *mut PolyWord, n_words: usize, flags: u8) {
    // SAFETY: precondition.
    unsafe {
        obj_ptr
            .sub(1)
            .write(length_word::make_length_word(n_words, flags));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alloc_and_set_length_word() {
        let mut space = MemorySpace::new(16, SpaceKind::Immutable);
        let obj = space.alloc(3); // requests 3 words; total used: 4 (1 len + 3 body)
        unsafe {
            set_length_word(obj, 3, length_word::F_BYTE_OBJ | length_word::F_MUTABLE_BIT);
        }
        assert_eq!(space.used_words(), 4);

        // Length word is at obj-1.
        let lw = unsafe { MemorySpace::length_word_of(obj) };
        assert_eq!(length_word::length_of(lw), 3);
        assert!(length_word::is_byte_object(lw));
        assert!(length_word::is_mutable(lw));
    }

    #[test]
    fn multiple_objects_have_stable_addresses() {
        let mut space = MemorySpace::new(16, SpaceKind::Immutable);
        let a = space.alloc(2);
        let b = space.alloc(2);
        let c = space.alloc(1);

        // b is exactly (length word + a's body size) words after a.
        let a_off = unsafe { b.offset_from(a) };
        assert_eq!(a_off, 3); // 2 body words + 1 length-word slot for b
        let b_off = unsafe { c.offset_from(b) };
        assert_eq!(b_off, 3);
    }

    #[test]
    #[should_panic(expected = "exhausted")]
    fn alloc_panics_on_overflow() {
        let mut space = MemorySpace::new(4, SpaceKind::Immutable);
        let _ = space.alloc(10);
    }
}
