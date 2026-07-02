//! Cheney-style copying GC for the runtime alloc space.
//!
//! ## What we collect
//!
//! Only `Interpreter::alloc_space` (the bump-allocator the runtime
//! uses for new objects) is collected. The image spaces (immutable
//! / mutable / code) are tenured — their pointers stay stable, but
//! their *contents* are still scanned because the mutable image
//! space holds the global namespace (hash table installed during
//! `enterStruct` / `enterVal`) which references alloc-space objects.
//!
//! ## Algorithm sketch
//!
//! 1. Allocate a fresh "to-space" buffer the same size as the
//!    active alloc-space.
//! 2. Walk every root (interpreter stack, exception packet, current
//!    code-segment pointer, image mutable space) and *forward* any
//!    PolyWord that points into from-space:
//!    - If the object is not yet forwarded: copy its body to
//!      to-space and write a tombstone in the original length word
//!      (high bit set) pointing to the new location.
//!    - Otherwise: read the tombstone, update the slot.
//! 3. Scan to-space sequentially with `scan_ptr`. For each object,
//!    walk its child pointer slots and forward them; advance
//!    `scan_ptr`. Continue until `scan_ptr == alloc_ptr`.
//! 4. Swap the alloc-space storage with the to-space buffer.
//! 5. The caller (interpreter) translates any remaining byte
//!    pointers it holds (e.g. `code_start` / `code_end` / saved
//!    frames) via the table of `(old_code_obj, new_code_obj)`
//!    accumulated during the copy.
//!
//! ## Object-shape rules
//!
//! - **`F_BYTE_OBJ`** (incl. bignums): no internal PolyWords. Skip
//!   the body when scanning. Copy bytes verbatim when forwarding.
//! - **`F_CODE_OBJ`**: the body holds bytecode bytes; the trailing
//!   region holds PolyWord constants (located via the last-word
//!   offset trick — see `length_word::const_segment_for_code`).
//!   Only the constants are scanned for pointers.
//! - **`F_CLOSURE_OBJ`**: word\[0\] is a *raw* code-object byte
//!   pointer (NOT a tagged PolyWord). Forward by treating it as a
//!   pointer-to-code-object and updating to the new code-obj
//!   location. Words[1..] are ordinary PolyWords.
//! - **Default (word object)**: every body word is a PolyWord.
//!
//! ## Forwarding
//!
//! We reuse PolyML's `F_TOMBSTONE_BIT` (0x80) in the length word.
//! When set, the rest of the word is a pointer to the new
//! location (with bit 0 = pointer, so we encode as
//! `PolyWord::from_ptr` and rely on it being aligned).

#![allow(dead_code)]

use crate::length_word::{
    self, F_BYTE_OBJ, F_CLOSURE_OBJ, F_CODE_OBJ, F_TOMBSTONE_BIT, FLAGS_SHIFT, flags_of, length_of,
    type_of,
};
use crate::poly_word::PolyWord;
use crate::space::MemorySpace;

/// A handle to the alloc-space(s) being GC'd. Lives only for the duration
/// of `collect`/`collect_pool`. Callers reach into here to ask whether a
/// PolyWord points into from-space and to install forwarding pointers.
///
/// Parallelism P2: from-space is a UNION of ranges — every nursery in the
/// pool is evacuated in one stop-the-world cycle (cross-nursery pointers
/// are unrestricted, so partial collection is unsound; see
/// docs/parallel-design.md). Membership is a binary search over the
/// sorted, disjoint range list; with one nursery this degenerates to the
/// old two-comparison check.
pub struct Collector<'a> {
    /// Sorted, disjoint (start, end) address ranges of every from-space.
    from_ranges: Vec<(usize, usize)>,
    /// Scratch buffer; copies go here.
    to_storage: &'a mut [PolyWord],
    /// Bump pointer into `to_storage`.
    to_used: usize,
    /// Pre-built map of from-space object body ranges, sorted by
    /// start address. Used by `forward` to detect mid-object PC
    /// pointers (handler PCs, retPC values pushed on stack) and
    /// translate them to the corresponding mid-object address in
    /// to-space.
    from_objects: Vec<(usize, usize)>, // (body_start_addr, n_words)
    /// Addresses that fell in from-space but didn't match any tracked
    /// object — usually a pre-pass bug. Logged at end of collect.
    untracked_addrs: Vec<usize>,
}

impl<'a> Collector<'a> {
    /// Union membership: is `addr` inside any from-space range? Binary
    /// search over the sorted, disjoint range list.
    #[inline]
    fn in_from_space(&self, addr: usize) -> bool {
        let idx = self
            .from_ranges
            .partition_point(|&(start, _)| start <= addr);
        idx > 0 && addr < self.from_ranges[idx - 1].1
    }

    fn contains_polyword(&self, w: PolyWord) -> bool {
        if w.is_tagged() {
            return false;
        }
        self.in_from_space(w.0)
    }

    fn contains_raw_ptr(&self, p: *const u8) -> bool {
        self.in_from_space(p as usize)
    }

    /// Forward (or read forwarding pointer of) the object pointed to
    /// by `slot`. The slot is updated in place to point at the
    /// to-space copy.
    ///
    /// # Safety
    /// `slot` must be a valid, writable pointer to a PolyWord.
    pub unsafe fn forward(&mut self, slot: *mut PolyWord) {
        // Tagged-PolyWord variant: respects LSB. Body words of
        // word-objects, closures, and code-object constants are
        // always tagged-or-pointer here, so we filter by LSB to
        // skip immediates.
        unsafe {
            self.forward_impl(slot, /*tagged_filter=*/ true)
        };
    }

    /// Variant for stack slots: PC values (retPC, handler PCs)
    /// pushed on the stack are raw byte addresses and may have
    /// LSB=1 just by chance. Don't filter by LSB — instead rely on
    /// the from-space range check plus the object-map lookup.
    ///
    /// # Safety
    /// Same as [`Self::forward`].
    pub unsafe fn forward_stack_slot(&mut self, slot: *mut PolyWord) {
        unsafe {
            self.forward_impl(slot, /*tagged_filter=*/ false)
        };
    }

    unsafe fn forward_impl(&mut self, slot: *mut PolyWord, tagged_filter: bool) {
        let w = unsafe { *slot };
        if tagged_filter && w.is_tagged() {
            return;
        }
        let addr = w.0;
        // Range check on the raw address (union membership).
        if !self.in_from_space(addr) {
            return;
        }
        // Look up which from-space object contains this address.
        // Body-start matches → ordinary forward. Otherwise it's a
        // mid-body pointer (PC value) and we keep the offset.
        let Some((body_start, _n_words)) = self.find_object(addr) else {
            self.untracked_addrs.push(addr);
            return;
        };
        let body_ptr = body_start as *const PolyWord;
        let new_body = unsafe { self.forward_object(body_ptr) };
        let offset_bytes = addr.wrapping_sub(body_start);
        let new_addr = (new_body as usize).wrapping_add(offset_bytes);
        unsafe { slot.write(PolyWord::from_bits(new_addr)) };
    }

    /// Binary-search the from-objects table for the object body
    /// whose range covers `addr` (in bytes). Returns
    /// `Some((body_start_addr, n_words))` if found, else `None`.
    /// A zero-length object's body is a single-point range — the
    /// body address itself, useful as an identity.
    fn find_object(&self, addr: usize) -> Option<(usize, usize)> {
        let idx = self
            .from_objects
            .partition_point(|(start, _)| *start <= addr);
        if idx == 0 {
            return None;
        }
        let (start, n) = self.from_objects[idx - 1];
        // Saturating arithmetic: a corrupt length word (flag bits leaking
        // into the length field) could make `n` huge and wrap `start +
        // n*8`, which would silently mis-forward or drop a live pointer —
        // the worst class of GC bug. For all valid (non-overflowing) `n`
        // the result is identical to the plain computation.
        let end = start.saturating_add(n.saturating_mul(std::mem::size_of::<usize>()));
        if addr < end || (n == 0 && addr == start) {
            Some((start, n))
        } else {
            None
        }
    }

    /// Forward an object that's known to be in from-space. Returns
    /// the to-space pointer (the object's new body address).
    ///
    /// # Safety
    /// `obj_ptr` must be a valid pointer into from-space, pointing
    /// at the body of a properly-headered object.
    unsafe fn forward_object(&mut self, obj_ptr: *const PolyWord) -> *const PolyWord {
        let lw = unsafe { *obj_ptr.sub(1) };
        if (flags_of(lw) & F_TOMBSTONE_BIT) != 0 {
            // Already forwarded; pointer is in the low bits.
            // We stored the bits as a raw pointer (mask off the flag).
            let bits = lw.0 & !((F_TOMBSTONE_BIT as usize) << FLAGS_SHIFT);
            return bits as *const PolyWord;
        }
        // First time we see this object: copy body to to-space and
        // install a forwarding pointer.
        let n_words = length_of(lw);
        let flags = flags_of(lw);
        let to_ptr = self.bump_to(n_words);
        // Write header
        let new_lw = length_word::make_length_word(n_words, flags);
        unsafe { to_ptr.sub(1).write(new_lw) };
        // Copy body
        unsafe {
            std::ptr::copy_nonoverlapping(obj_ptr, to_ptr, n_words);
        }
        // Install tombstone in old header so subsequent forwards short-circuit.
        let fwd_word =
            PolyWord::from_bits((to_ptr as usize) | ((F_TOMBSTONE_BIT as usize) << FLAGS_SHIFT));
        unsafe { obj_ptr.cast::<PolyWord>().cast_mut().sub(1).write(fwd_word) };
        to_ptr
    }

    fn bump_to(&mut self, n_words: usize) -> *mut PolyWord {
        let len_idx = self.to_used;
        let body_idx = len_idx + 1;
        let new_used = body_idx + n_words;
        // INVARIANT: to_storage is allocated with the same capacity as
        // from-space (see collect()); a Cheney copy never produces more
        // live words than from-space held, so this assert can only fire
        // on collector corruption — it is a real release-time guard, not
        // a debug-only check.
        assert!(
            new_used <= self.to_storage.len(),
            "GC to-space overflow: requested {n_words}, used {}/{}",
            self.to_used,
            self.to_storage.len()
        );
        self.to_used = new_used;
        // SAFETY: body_idx < new_used <= to_storage.len() per the assert above.
        unsafe { self.to_storage.as_mut_ptr().add(body_idx) }
    }

    /// Scan an object's body for child pointer slots, forwarding
    /// each. Layout depends on the object's type code.
    ///
    /// # Safety
    /// `obj_ptr` must point at a valid object's body, with a
    /// well-formed length word at `-1`. The object is assumed to
    /// be in *to-space* (we are scanning newly-copied data).
    unsafe fn scan_object(&mut self, obj_ptr: *mut PolyWord) {
        let lw = unsafe { *obj_ptr.sub(1) };
        let n_words = length_of(lw);
        let ty = type_of(lw);
        match ty {
            F_BYTE_OBJ => {
                // No internal pointers.
            }
            F_CODE_OBJ => {
                // Constants live at the END of the body, located via
                // the trailing-offset trick. Reuse the upstream-style
                // accessor: const_segment_for_code returns
                // (const_start, count).
                let (cp, count) = unsafe { length_word::const_segment_for_code(obj_ptr) };
                let cp_mut = cp.cast_mut();
                for i in 0..count {
                    unsafe { self.forward(cp_mut.add(i)) };
                }
            }
            F_CLOSURE_OBJ => {
                // Word 0 is a raw code-object body-start pointer
                // (treated by upstream as `POLYCODEPTR*`). With the
                // unified `forward` that handles mid-body pointers
                // via the object-map lookup, all word slots can be
                // forwarded uniformly.
                for i in 0..n_words {
                    unsafe { self.forward(obj_ptr.add(i)) };
                }
            }
            _ => {
                // Ordinary word object: every body word is a PolyWord.
                for i in 0..n_words {
                    unsafe { self.forward(obj_ptr.add(i)) };
                }
            }
        }
    }

    /// Cheney scan loop: walk to-space objects sequentially, forwarding
    /// their child pointers, until we catch up to the alloc pointer.
    unsafe fn cheney_scan(&mut self) {
        let mut scan = 0usize;
        while scan < self.to_used {
            // Object at index `scan` is the *length word* slot;
            // body starts at scan+1.
            // SAFETY: scan < to_used and to_used is in-range.
            let lw = unsafe { *self.to_storage.as_ptr().add(scan) };
            let n_words = length_of(lw);
            let body_ptr = unsafe { self.to_storage.as_mut_ptr().add(scan + 1) };
            unsafe { self.scan_object(body_ptr) };
            scan += 1 + n_words;
        }
    }
}

/// Run a Cheney-style collection on `alloc`. The `visit_roots` closure
/// is called once with a `&mut Collector` it can use to forward each
/// root pointer slot. After it returns, the collector performs the
/// Cheney scan over to-space, and finally we swap the storage of
/// `alloc` to the to-space buffer.
///
/// Returns the number of live words copied (= new `used` in `alloc`
/// post-collection).
pub fn collect<F>(alloc: &mut MemorySpace, visit_roots: F) -> usize
where
    F: FnOnce(&mut Collector<'_>),
{
    collect_pool(std::slice::from_mut(&mut &mut *alloc), visit_roots)
}

/// Multi-nursery stop-the-world collection (parallelism P2).
///
/// Evacuates the UNION of all `spaces` (every pool nursery) into ONE fresh
/// to-space, then swaps `spaces[0]`'s storage for it and resets every other
/// nursery empty (their live objects were promoted into the primary).
/// Cross-nursery pointers need no special case — forwarding is
/// membership-driven over the union of from-space ranges.
///
/// To-space is sized to Σ CAPACITY over all nurseries, so it can NEVER
/// overflow (live ≤ Σ used ≤ Σ capacity); with a single nursery this is
/// exactly the primary's capacity — byte-identical to the pre-pool
/// single-space collect.
pub fn collect_pool<F>(spaces: &mut [&mut MemorySpace], visit_roots: F) -> usize
where
    F: FnOnce(&mut Collector<'_>),
{
    assert!(
        !spaces.is_empty(),
        "collect_pool needs at least one nursery"
    );

    // from-space ranges (full storage capacity per space, as the old
    // single-space code used `as_ptr_range`) + the union object pre-pass
    // over each space's USED region. Ranges are sorted for binary-search
    // membership; from_objects sorted by body start for `find_object`.
    let mut from_ranges: Vec<(usize, usize)> = Vec::with_capacity(spaces.len());
    let mut from_objects: Vec<(usize, usize)> = Vec::new();
    let mut total_capacity = 0usize;
    for space in spaces.iter() {
        let range = space.as_ptr_range();
        from_ranges.push((range.start as usize, range.end as usize));
        total_capacity += space.capacity_words();
        // Pre-pass: object body ranges in this space's live region.
        let storage_start = range.start;
        let used_words = space.used_words();
        let mut i = 0usize;
        while i < used_words {
            // SAFETY: i is in-bounds of this space's storage slice.
            let lw = unsafe { *storage_start.add(i) };
            let n = length_of(lw);
            if i + 1 + n > used_words {
                i += 1;
                continue;
            }
            let body_addr = unsafe { storage_start.add(i + 1) } as usize;
            from_objects.push((body_addr, n));
            i += 1 + n;
        }
    }
    from_ranges.sort_unstable();
    from_objects.sort_unstable_by_key(|&(start, _)| start);

    // Σ-capacity to-space (never overflows).
    let mut scratch = vec![PolyWord::ZERO; total_capacity].into_boxed_slice();

    let mut col = Collector {
        from_ranges,
        to_storage: &mut scratch,
        to_used: 0,
        from_objects,
        untracked_addrs: Vec::new(),
    };

    visit_roots(&mut col);
    // SAFETY: collector invariants upheld.
    unsafe { col.cheney_scan() };

    let new_used = col.to_used;
    if !col.untracked_addrs.is_empty() {
        let mut sample: Vec<usize> = col.untracked_addrs.iter().copied().collect();
        sample.sort_unstable();
        sample.dedup();
        eprintln!(
            "  GC untracked: {} pointer occurrences in from-space did not match any tracked object ({} unique addresses):",
            col.untracked_addrs.len(),
            sample.len(),
        );
        for addr in sample.iter().take(5) {
            // Read the would-be length word at addr-8.
            // SAFETY: addr was a real pointer into from-space; addr-8
            // may or may not be a valid header but the page is still
            // mapped because no from_storage Box has dropped yet.
            let lw_ptr = (*addr - std::mem::size_of::<usize>()) as *const PolyWord;
            let lw_val = unsafe { (*lw_ptr).0 };
            let raw_len = length_of(PolyWord::from_bits(lw_val));
            let raw_flags = flags_of(PolyWord::from_bits(lw_val));
            eprintln!(
                "    0x{addr:016x}  would-be LW @ -8: raw=0x{lw_val:016x}  length_of={raw_len}  flags=0x{raw_flags:02x}",
            );
        }
        // A from-space pointer matching no tracked object means a missed GC root;
        // the swap below drops from-space, which would leave that slot dangling —
        // a silent use-after-free. Fail fast instead of corrupting the heap. (In
        // correct operation this set is always empty; this only fires on a genuine
        // collector bug, exactly when crashing beats continuing.)
        panic!(
            "GC invariant violated: {} untracked from-space pointer occurrence(s) \
             (e.g. 0x{:016x}); a root was missed",
            col.untracked_addrs.len(),
            sample.first().copied().unwrap_or(0)
        );
    }

    // Promote: the primary takes the to-space; every other nursery is now
    // empty (its live objects were copied into the primary's new storage
    // and every pointer to them forwarded).
    let n_spaces = spaces.len();
    spaces[0].replace_storage(scratch, new_used);
    for space in spaces.iter_mut().take(n_spaces).skip(1) {
        space.reset_empty();
    }
    new_used
}

/// Extension on `MemorySpace` that the GC needs in addition to the
/// public alloc API.
impl MemorySpace {
    /// Address range of the active storage. Used by the GC to test
    /// "is this PolyWord a pointer into us?".
    #[must_use]
    pub fn as_ptr_range(&self) -> std::ops::Range<*const PolyWord> {
        let start = self.storage_ptr();
        // SAFETY: capacity_words is the length of storage; end is one-past-end.
        let end = unsafe { start.add(self.capacity_words()) };
        start..end
    }

    /// Hand back the raw storage pointer (start of the box).
    pub(crate) fn storage_ptr(&self) -> *const PolyWord {
        let bytes = self.storage_bytes();
        bytes.as_ptr().cast()
    }

    /// Swap in a fresh storage buffer with `new_used` bytes occupied.
    /// Old storage is dropped. Used by the GC after copy completes.
    pub fn replace_storage(&mut self, new_storage: Box<[PolyWord]>, new_used: usize) {
        assert!(new_used <= new_storage.len());
        self.storage = new_storage;
        self.used = new_used;
    }

    /// Reset a nursery to empty after a multi-nursery collection promoted
    /// its live objects into the primary (parallelism P2). Storage (and
    /// hence capacity) is kept; only the bump pointer is rewound. The old
    /// contents are dead (every pointer to them was forwarded), so they
    /// are simply overwritten by future allocations.
    pub fn reset_empty(&mut self) {
        self.used = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::length_word::{F_BYTE_OBJ, F_MUTABLE_BIT};
    use crate::space::{SpaceKind, set_length_word};

    #[test]
    fn collect_empty_heap_is_empty() {
        let mut space = MemorySpace::new(64, SpaceKind::Mutable);
        let new_used = collect(&mut space, |_c| {});
        assert_eq!(new_used, 0);
    }

    #[test]
    fn collect_unreferenced_object_is_dropped() {
        let mut space = MemorySpace::new(64, SpaceKind::Mutable);
        let p = space.alloc(3);
        unsafe { set_length_word(p, 3, F_BYTE_OBJ | F_MUTABLE_BIT) };
        assert!(space.used_words() > 0);
        let new_used = collect(&mut space, |_c| {});
        assert_eq!(new_used, 0, "unrooted object should be reclaimed");
    }

    #[test]
    fn collect_keeps_rooted_byte_object() {
        let mut space = MemorySpace::new(64, SpaceKind::Mutable);
        let p = space.alloc(2);
        unsafe { set_length_word(p, 2, F_BYTE_OBJ | F_MUTABLE_BIT) };
        // SAFETY: just allocated.
        unsafe {
            p.write(PolyWord::from_bits(0x1234_5678));
            p.add(1).write(PolyWord::from_bits(0x9abc_def0));
        }

        // Root slot: a PolyWord pointing at the object.
        let mut root = PolyWord::from_ptr(p.cast_const());
        let new_used = collect(&mut space, |c| {
            // SAFETY: root is a valid, writable PolyWord.
            unsafe { c.forward(&mut root as *mut _) };
        });

        // After GC the object is in the new storage, root updated.
        assert!(new_used >= 3, "should have at least header + 2 words");
        // Read back through the updated root.
        let new_p = root.as_ptr::<PolyWord>();
        unsafe {
            assert_eq!((*new_p).0, 0x1234_5678);
            assert_eq!((*new_p.add(1)).0, 0x9abc_def0);
        }
    }

    #[test]
    fn collect_traces_through_word_object() {
        let mut space = MemorySpace::new(64, SpaceKind::Mutable);
        // Allocate a leaf byte object
        let leaf = space.alloc(1);
        unsafe {
            set_length_word(leaf, 1, F_BYTE_OBJ);
            leaf.write(PolyWord::from_bits(0xdead_beef));
        }
        // Allocate a parent word object pointing at it
        let parent = space.alloc(2);
        unsafe {
            set_length_word(parent, 2, 0);
            parent.write(PolyWord::from_ptr(leaf.cast_const()));
            parent.add(1).write(PolyWord::tagged(42));
        }

        let mut root = PolyWord::from_ptr(parent.cast_const());
        collect(&mut space, |c| {
            unsafe { c.forward(&mut root as *mut _) };
        });
        // Walk through the new parent to find the leaf.
        let new_parent = root.as_ptr::<PolyWord>();
        let leaf_word = unsafe { *new_parent };
        let new_leaf = leaf_word.as_ptr::<PolyWord>();
        assert_eq!(unsafe { (*new_leaf).0 }, 0xdead_beef);
        assert_eq!(unsafe { (*new_parent.add(1)).0 }, PolyWord::tagged(42).0);
    }

    /// P2 multi-nursery collection with a CROSS-NURSERY pointer: a parent
    /// object in nursery A points at a leaf in nursery B. `collect_pool`
    /// must forward through the union (membership over both ranges),
    /// promote both objects into the primary (A), and reset B empty — with
    /// the cross-nursery link rewritten to the promoted leaf.
    #[test]
    fn collect_pool_forwards_cross_nursery_pointer() {
        let mut a = MemorySpace::new(64, SpaceKind::Mutable);
        let mut b = MemorySpace::new(64, SpaceKind::Mutable);
        // Leaf lives in nursery B.
        let leaf = b.alloc(1);
        unsafe {
            set_length_word(leaf, 1, F_BYTE_OBJ);
            leaf.write(PolyWord::from_bits(0xcafe_f00d));
        }
        // Parent lives in nursery A, pointing across into B.
        let parent = a.alloc(2);
        unsafe {
            set_length_word(parent, 2, 0);
            parent.write(PolyWord::from_ptr(leaf.cast_const()));
            parent.add(1).write(PolyWord::tagged(7));
        }
        let leaf_addr_before = leaf as usize;

        let mut root = PolyWord::from_ptr(parent.cast_const());
        let new_used = collect_pool(&mut [&mut a, &mut b], |c| {
            unsafe { c.forward(&mut root as *mut _) };
        });

        // The whole live graph (parent + leaf) is now in the primary (A);
        // B was promoted-and-reset.
        assert_eq!(b.used_words(), 0, "nursery B should be reset empty");
        assert!(new_used >= 4, "parent(1+2) + leaf(1+1) live words expected");

        let new_parent = root.as_ptr::<PolyWord>();
        let new_leaf = unsafe { *new_parent }.as_ptr::<PolyWord>();
        // The cross-nursery link was rewritten (leaf MOVED out of B).
        assert_ne!(
            new_leaf as usize, leaf_addr_before,
            "the cross-nursery leaf pointer must be forwarded, not stale"
        );
        assert_eq!(
            unsafe { (*new_leaf).0 },
            0xcafe_f00d,
            "leaf value must survive promotion"
        );
        assert_eq!(unsafe { (*new_parent.add(1)).0 }, PolyWord::tagged(7).0);
        // Both promoted objects live in the primary's new storage.
        let a_range = a.as_ptr_range();
        let a_lo = a_range.start as usize;
        let a_hi = a_range.end as usize;
        assert!(
            (new_parent as usize) >= a_lo && (new_parent as usize) < a_hi,
            "promoted parent must be in the primary"
        );
        assert!(
            (new_leaf as usize) >= a_lo && (new_leaf as usize) < a_hi,
            "promoted leaf must be in the primary"
        );
    }
}
