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
    pub(crate) storage: Box<[PolyWord]>,
    pub(crate) used: usize,
    kind: SpaceKind,
    /// Retired from-space kept for PING-PONG reuse as the next
    /// collection's to-space scratch (primary space only; see
    /// `gc::collect_pool_with_workers`). Never part of the space's
    /// address range. Contents are STALE — the collector only reads
    /// to-space words it wrote.
    pub(crate) spare: Option<Box<[PolyWord]>>,
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
            spare: None,
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
    /// Panics if the space is exhausted. Reserved for the PRE-SIZED
    /// paths (loader/export/GC/tests size the space to fit up front),
    /// where an exhaustion is a sizing bug, not a runtime condition.
    /// Runtime-heap allocation — where exhaustion is a *user* condition
    /// (the workload outgrew `POLYML_HEAP_BYTES`) — must go through
    /// [`Self::try_alloc`] (the interpreter, → `InterpError::HeapExhausted`)
    /// or [`Self::alloc_or_exit`] (the RTS helpers) instead.
    pub fn alloc(&mut self, n_words: usize) -> *mut PolyWord {
        self.try_alloc(n_words).unwrap_or_else(|| {
            panic!(
                "MemorySpace {:?} exhausted: requested {n_words}, used {}/{}",
                self.kind,
                self.used,
                self.storage.len()
            )
        })
    }

    /// Bump-allocate like [`Self::alloc`], but on exhaustion fail CLEAN:
    /// print one diagnostic naming `POLYML_HEAP_BYTES` to stderr and exit
    /// non-zero — no Rust panic/backtrace. This is the RTS-helper path
    /// (`rts.rs`): an RTS function returns a bare `PolyWord` with no error
    /// channel, and it cannot even raise an SML exception here because the
    /// exception packet itself would need heap. The interpreter's own
    /// alloc path surfaces [`crate::InterpError::HeapExhausted`] through
    /// `run_until` instead — same message, cleaner unwind.
    pub fn alloc_or_exit(&mut self, n_words: usize) -> *mut PolyWord {
        self.try_alloc(n_words).unwrap_or_else(|| {
            eprintln!(
                "poly: heap exhausted (RTS allocation): requested {n_words} word(s), \
                 used {}/{} words — raise POLYML_HEAP_BYTES (a byte count) and rerun",
                self.used,
                self.storage.len()
            );
            std::process::exit(4);
        })
    }

    /// Non-panicking allocation. Returns `None` if `n_words` (plus its
    /// length word) wouldn't fit. A failed attempt consumes nothing.
    ///
    /// Exhaustion is TERMINAL BY DESIGN — callers must NOT try
    /// GC-then-retry here: RTS helpers like `do_alloc_ref` and the
    /// `ALLOC_WORD_MEMORY` opcode cache the allocation pointer across the
    /// call, so a GC in the middle of an allocation would leave them
    /// holding stale from-space pointers (a known heap-corruption hazard;
    /// see the foundation-audit notes in `docs/`). The normal GC already
    /// fires *between* interpreter steps at the threshold, so reaching
    /// exhaustion means the live set genuinely outgrew the heap — the
    /// designed response is failing clean with a `POLYML_HEAP_BYTES` hint.
    pub fn try_alloc(&mut self, n_words: usize) -> Option<*mut PolyWord> {
        let length_idx = self.used;
        let body_idx = length_idx + 1;
        let new_used = body_idx + n_words;
        if new_used > self.storage.len() {
            return None;
        }
        self.used = new_used;
        // SAFETY: body_idx is in-bounds because we checked above.
        Some(unsafe { self.storage.as_mut_ptr().add(body_idx) })
    }

    /// Read the length word that precedes the given object pointer.
    ///
    /// ATOMIC (Relaxed): under `POLY_PARALLEL` a peer can allocate at a
    /// RECYCLED address (nursery reset + reallocation) while this thread
    /// still reaches the old object through a racy SML publish — TSan
    /// proved the plain read races with `set_length_word`'s header write.
    /// Relaxed is free on x86/aarch64.
    ///
    /// # Safety
    /// `obj_ptr` must have been returned by an `alloc` on **this**
    /// `MemorySpace`. Crossing-space lookups are undefined.
    #[must_use]
    pub unsafe fn length_word_of(obj_ptr: *const PolyWord) -> PolyWord {
        // SAFETY: precondition.
        let bits = unsafe {
            std::sync::atomic::AtomicUsize::from_ptr(obj_ptr.sub(1).cast::<usize>().cast_mut())
                .load(std::sync::atomic::Ordering::Relaxed)
        };
        PolyWord::from_bits(bits)
    }

    /// Bytes covered by the space's storage. Useful for the future
    /// mmap-and-protect path.
    #[must_use]
    pub fn storage_bytes(&self) -> &[u8] {
        // Length = words * size_of::<PolyWord>(). Spelled out explicitly
        // rather than via `size_of_val::<[PolyWord]>(&self.storage)`,
        // whose correctness depended on a turbofish-driven auto-deref;
        // dropping that turbofish (or changing the container) would
        // silently yield a fat-pointer's 16 bytes over a multi-MB heap.
        let n_bytes = self.storage.len() * std::mem::size_of::<PolyWord>();
        // SAFETY: PolyWord is repr(transparent) over usize; bit-cast
        // for a read-only byte view is well-defined.
        let out =
            unsafe { std::slice::from_raw_parts(self.storage.as_ptr().cast::<u8>(), n_bytes) };
        debug_assert_eq!(
            out.len(),
            self.capacity_words() * std::mem::size_of::<PolyWord>(),
            "storage_bytes() length out of sync with capacity_words()"
        );
        out
    }
}

/// Write the length word at offset `-1` from an object pointer.
///
/// # Safety
/// `obj_ptr` must have come from a `MemorySpace::alloc` call.
pub unsafe fn set_length_word(obj_ptr: *mut PolyWord, n_words: usize, flags: u8) {
    // ATOMIC (Relaxed) — pairs with `length_word_of`; see its note on the
    // recycled-address race under POLY_PARALLEL.
    // SAFETY: precondition.
    unsafe {
        std::sync::atomic::AtomicUsize::from_ptr(obj_ptr.sub(1).cast::<usize>()).store(
            length_word::make_length_word(n_words, flags).0,
            std::sync::atomic::Ordering::Relaxed,
        );
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

    #[test]
    fn try_alloc_exhaustion_is_clean() {
        let mut space = MemorySpace::new(4, SpaceKind::Immutable);
        // Too big: fails without panicking and consumes nothing.
        assert!(space.try_alloc(10).is_none());
        assert_eq!(space.used_words(), 0);
        // A fitting request still succeeds after a failed one.
        assert!(space.try_alloc(2).is_some()); // 1 len + 2 body = 3
        assert_eq!(space.used_words(), 3);
        // 1 word left can't hold 1 len + 1 body.
        assert!(space.try_alloc(1).is_none());
        assert_eq!(space.used_words(), 3);
    }
}
