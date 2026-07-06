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
    self, F_BYTE_OBJ, F_CLOSURE_OBJ, F_CODE_OBJ, F_TOMBSTONE_BIT, F_WEAK_BIT, FLAGS_SHIFT,
    flags_of, length_of, type_of,
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
    /// Object-start BITMAP over the union of from-space ranges: bit i of
    /// the space starting at `from_ranges[k]` (bit base `range_bit_base[k]`)
    /// is set iff word i is an object BODY START. Consumed only by
    /// `forward_stack_slot` (mid-body PC translation + the
    /// integer-aliasing canary) — ML slots forward via the header
    /// directly. Replaces the old `(body, len)` Vec: the walk writes a
    /// cache-resident ~Σwords/8-byte bitmap instead of a 16-bytes-per-
    /// object table (measured: the table build dominated the pause).
    start_bits: Vec<u64>,
    /// Per-range starting bit index into `start_bits` (parallel to
    /// `from_ranges`).
    range_bit_base: Vec<usize>,
    /// Weak objects (F_WEAK_BIT word objects) registered during the scan:
    /// their slots are NOT traced (that is what makes them weak); the
    /// post-trace `weak_fixup` forwards surviving SOME cells and demotes
    /// dead entries to NONE. Entries are BODY addresses — to-space bodies
    /// for copied weak objects, permanent bodies for image-mutable ones.
    pub weak_objects: Vec<usize>,
    /// Addresses that fell in from-space but didn't match any tracked
    /// object — usually a pre-pass bug. Logged at end of collect.
    untracked_addrs: Vec<usize>,
    /// PARALLEL COLLECTION (P6): when `Some(n)`, the linear Cheney scan
    /// is replaced by an n-worker queue-driven scan, and the serial
    /// root-forwarding phase records every object it copies here (the
    /// workers' seed queue — to-space body addresses). `None` (default)
    /// = the exact pre-P6 serial path, byte-identical.
    par_workers: Option<usize>,
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

    /// Register a WEAK object (body address) for the post-trace fixup
    /// instead of tracing its slots. Used by the image-mutable root scan
    /// for permanent weak objects; copied weak objects self-register in
    /// `scan_object`.
    pub fn register_weak(&mut self, body: usize) {
        self.weak_objects.push(body);
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
        // Resolve the containing object via the start bitmap. The exact-bit
        // hit is O(1) and covers ~every ML slot; the backward scan handles
        // MID-BODY pointers — stack PC values, AND closure word-0 code
        // pointers, which can point at an entry offset INSIDE the code
        // object, not its body start (the chain fence caught a
        // body-start-assumption version of this reading garbage headers).
        let Some(body_start) = self.find_body_start(addr) else {
            self.untracked_addrs.push(addr);
            return;
        };
        let body_ptr = body_start as *const PolyWord;
        let new_body = unsafe { self.forward_object(body_ptr) };
        let offset_bytes = addr.wrapping_sub(body_start);
        let new_addr = (new_body as usize).wrapping_add(offset_bytes);
        unsafe { slot.write(PolyWord::from_bits(new_addr)) };
    }

    /// Length of the object whose BODY starts at `body` — reading through
    /// a tombstone if the object was already forwarded (the from-space
    /// header then holds the to-pointer; the real length word lives on
    /// the to-space copy).
    fn object_len_via_header(&self, body: usize) -> usize {
        let lw = unsafe { *(body as *const PolyWord).sub(1) };
        if (flags_of(lw) & F_TOMBSTONE_BIT) != 0 {
            let to = lw.0 & !((F_TOMBSTONE_BIT as usize) << FLAGS_SHIFT);
            let to_lw = unsafe { *(to as *const PolyWord).sub(1) };
            length_of(to_lw)
        } else {
            length_of(lw)
        }
    }

    /// Find the BODY START of the from-space object containing `addr` via
    /// the object-start bitmap. Exact-bit hit (the overwhelmingly common
    /// case — every ML body-start pointer) is O(1); otherwise scan the
    /// bitmap backwards for the containing object (mid-body pointers:
    /// stack PC values, closure word-0 entry offsets) and validate the
    /// offset against the object's length (read via the header,
    /// tombstone-indirected). A zero-length object matches only its exact
    /// body address.
    fn find_body_start(&self, addr: usize) -> Option<usize> {
        // Which range?
        let idx = self
            .from_ranges
            .partition_point(|&(start, _)| start <= addr);
        if idx == 0 || addr >= self.from_ranges[idx - 1].1 {
            return None;
        }
        let (range_start, _) = self.from_ranges[idx - 1];
        let bit_base = self.range_bit_base[idx - 1];
        let word_idx = bit_base + (addr - range_start) / std::mem::size_of::<usize>();
        let is_start = |i: usize| self.start_bits[i / 64] & (1u64 << (i % 64)) != 0;
        if is_start(word_idx) {
            // Return the ALIGNED word address, not `addr`: an unaligned PC
            // pointing into an object's FIRST word must keep its byte
            // offset (the caller computes offset = addr − body_start).
            let start = range_start + (word_idx - bit_base) * std::mem::size_of::<usize>();
            return Some(start);
        }
        // Mid-body: scan back to a start bit; validate; on a miss (e.g. a
        // zero-length object between us and the true container) keep
        // scanning.
        let mut i = word_idx;
        while i > bit_base {
            i -= 1;
            if !is_start(i) {
                continue;
            }
            let start = range_start + (i - bit_base) * std::mem::size_of::<usize>();
            let n = self.object_len_via_header(start);
            // Saturating arithmetic: a corrupt length word could make `n`
            // huge and wrap the end bound, silently mis-forwarding — the
            // worst class of GC bug.
            let end = start.saturating_add(n.saturating_mul(std::mem::size_of::<usize>()));
            if addr < end {
                return Some(start);
            }
            // A start bit whose object ends before `addr` means `addr` is
            // in header/no-man's land (an aliasing integer) — but keep
            // scanning past zero-length objects, whose body point IS the
            // next header.
            if n > 0 {
                return None;
            }
        }
        None
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
                // WEAK word object (Weak.weak / weakArray, alloc flags
                // 0wx60): its slots are exactly the weak links — do NOT
                // trace them (tracing is what keeps referents alive).
                // Register for the post-trace `weak_fixup`, which forwards
                // surviving SOME cells and demotes dead entries to NONE.
                // Weak BYTE cells fall into the byte arm above (ignored),
                // matching upstream gc_check_weak_ref.cpp.
                if (flags_of(lw) & F_WEAK_BIT) != 0 {
                    self.weak_objects.push(obj_ptr as usize);
                    return;
                }
                // Ordinary word object: every body word is a PolyWord.
                for i in 0..n_words {
                    unsafe { self.forward(obj_ptr.add(i)) };
                }
            }
        }
    }

    /// Post-trace weak-reference fixup — the copying-GC port of upstream
    /// `gc_check_weak_ref.cpp` (runs between mark and update phases there;
    /// after the strong trace reaches its fixpoint here). For every slot
    /// of every registered weak object:
    /// - tagged (NONE) or non-from-space SOME with permanent ref: keep;
    /// - SOME strongly forwarded elsewhere: point at that copy (its ref
    ///   was strongly traced through it — same result as upstream, where
    ///   a marked SOME implies a marked ref);
    /// - weak-only SOME whose inner ref survived (tombstoned or
    ///   permanent): copy the 1-word SOME cell now (never scanned — its
    ///   single slot is final) and tombstone the original, so a SOME cell
    ///   shared by several weak slots gets ONE copy;
    /// - inner ref dead: slot := TAGGED(0) (NONE) and the from-space SOME
    ///   content := TAGGED(0) — upstream's "for safety" overwrite, which
    ///   is exactly what makes the shared-SOME case converge (a later
    ///   visitor sees the tagged content and demotes too).
    /// A slot pointing at anything that is not a 1-word word object is
    /// demoted to NONE: upstream asserts there (UB in release); we define
    /// the total behavior, and never leave a from-space pointer behind.
    ///
    /// # Safety
    /// Must run after the strong trace completed (serial cheney_scan or
    /// the parallel drain), before promote. Single-threaded.
    unsafe fn weak_fixup(&mut self) {
        const TOMB: usize = (F_TOMBSTONE_BIT as usize) << FLAGS_SHIFT;
        let weak_objs = std::mem::take(&mut self.weak_objects);
        for body in weak_objs {
            let n = length_of(unsafe { *(body as *const PolyWord).sub(1) });
            for i in 0..n {
                let slot = (body as *mut PolyWord).wrapping_add(i);
                let w = unsafe { *slot };
                if w.is_tagged() {
                    continue;
                }
                let some_addr = w.0;
                if !self.in_from_space(some_addr) {
                    // Permanent SOME cell: its CONTENT may still be a
                    // dying local ref (upstream scans permanent-mutable
                    // weak areas for exactly this).
                    let ref_w = unsafe { *(some_addr as *const PolyWord) };
                    if ref_w.is_tagged() {
                        // Safety-overwritten earlier this pass (shared).
                        unsafe { slot.write(PolyWord::tagged(0)) };
                    } else if self.in_from_space(ref_w.0) {
                        let ref_hdr = unsafe { *(ref_w.0 as *const PolyWord).sub(1) };
                        if (flags_of(ref_hdr) & F_TOMBSTONE_BIT) != 0 {
                            let fwd = ref_hdr.0 & !TOMB;
                            unsafe {
                                (some_addr as *mut PolyWord).write(PolyWord::from_bits(fwd));
                            }
                        } else {
                            unsafe {
                                (some_addr as *mut PolyWord).write(PolyWord::tagged(0));
                                slot.write(PolyWord::tagged(0));
                            }
                        }
                    }
                    continue;
                }
                let some_hdr = unsafe { *(some_addr as *const PolyWord).sub(1) };
                if (flags_of(some_hdr) & F_TOMBSTONE_BIT) != 0 {
                    // Strongly copied (and strongly scanned) elsewhere.
                    unsafe { slot.write(PolyWord::from_bits(some_hdr.0 & !TOMB)) };
                    continue;
                }
                if length_of(some_hdr) != 1 || type_of(some_hdr) != 0 {
                    unsafe { slot.write(PolyWord::tagged(0)) };
                    continue;
                }
                let ref_w = unsafe { *(some_addr as *const PolyWord) };
                if ref_w.is_tagged() {
                    unsafe { slot.write(PolyWord::tagged(0)) };
                    continue;
                }
                let new_ref = if self.in_from_space(ref_w.0) {
                    let ref_hdr = unsafe { *(ref_w.0 as *const PolyWord).sub(1) };
                    if (flags_of(ref_hdr) & F_TOMBSTONE_BIT) != 0 {
                        PolyWord::from_bits(ref_hdr.0 & !TOMB)
                    } else {
                        // Dead ref: NONE + the safety overwrite.
                        unsafe {
                            (some_addr as *mut PolyWord).write(PolyWord::tagged(0));
                            slot.write(PolyWord::tagged(0));
                        }
                        continue;
                    }
                } else {
                    ref_w // permanent ref — always reachable
                };
                // Survivor: copy the SOME cell, tombstone the original.
                let to_ptr = self.bump_to(1);
                unsafe {
                    to_ptr
                        .sub(1)
                        .write(length_word::make_length_word(1, flags_of(some_hdr)));
                    to_ptr.write(new_ref);
                    (some_addr as *mut PolyWord)
                        .sub(1)
                        .write(PolyWord::from_bits((to_ptr as usize) | TOMB));
                    slot.write(PolyWord::from_bits(to_ptr as usize));
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

// ---------------------------------------------------------------------------
// P6: parallel queue-driven scan (docs/parallel-design.md § P6).
//
// The linear Cheney scan is inherently sequential (the scan pointer chases
// the alloc pointer). The parallel replacement is a work-stealing drain:
// the claiming copier of each object pushes it (exactly once) onto a
// worker-local deque; workers pop locally, steal when dry, and exit when
// the shared pending counter hits zero. The from-space header is the
// synchronization point: NORMAL -> BUSY (claim CAS) -> TOMBSTONE(to-ptr)
// (Release publish after the body copy), so exactly one worker copies each
// object and every reader observes a fully-copied body (Acquire).
mod par {
    use super::{
        F_BYTE_OBJ, F_CLOSURE_OBJ, F_CODE_OBJ, F_TOMBSTONE_BIT, FLAGS_SHIFT, PolyWord, flags_of,
        length_of, length_word, type_of,
    };
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicUsize, Ordering};

    /// BUSY claim sentinel: the tombstone bit with a NULL forward pointer —
    /// an otherwise-impossible header (`bump_to` never returns null).
    const BUSY: usize = (F_TOMBSTONE_BIT as usize) << FLAGS_SHIFT;

    /// `Send`+`Sync` wrapper for the raw to-space base pointer. Workers
    /// write disjoint reserved regions (the atomic bump cursor is the
    /// arbiter) and scan each object exactly once (deque transfer).
    struct SendBase(*mut PolyWord);
    unsafe impl Send for SendBase {}
    unsafe impl Sync for SendBase {}

    /// MAXIMUM chunk size in words (4 MB): the granularity of work
    /// OWNERSHIP. Each chunk is allocated into by exactly one worker and
    /// scanned LINEARLY by exactly one worker — the property the
    /// queue-drain design lacked (its random-order visits lost to the
    /// serial sweep's sequential prefetch at every scale; see
    /// docs/parallel-design.md). Workers START small
    /// (`INITIAL_CHUNK_WORDS`) and DOUBLE per seal up to this max, so a
    /// collection that copies little claims little (fillers inflate
    /// `to_used`, and an inflated `used` fires the 80% GC trigger early
    /// on small heaps — measured as extra collections on a 64 MB storm).
    const CHUNK_WORDS: usize = 512 * 1024;
    /// First chunk claim per worker (32 KB).
    const INITIAL_CHUNK_WORDS: usize = 4 * 1024;

    /// One contiguous slice of the arena: `[start, alloc)` holds copied
    /// objects; `[scan, alloc)` is not yet scanned. All word indices.
    pub(super) struct Chunk {
        start: usize,
        end: usize,
        alloc: usize,
        scan: usize,
    }

    /// A unit of stealable scan work.
    pub(super) enum Task {
        /// A whole chunk: swept linearly by its thief.
        Chunk(Chunk),
        /// A slot range [lo, hi) of ONE wide to-space object (body byte
        /// address): wide pointer arrays are the breadth of the object
        /// graph, but `forward_slot` copies children inline during the
        /// parent's scan — without splitting, one worker copies every
        /// child of a wide parent (measured: 99.7% of a 410 MB probe on
        /// one worker). Ranges are disjoint, so each slot is forwarded
        /// exactly once.
        Slots { body: usize, lo: usize, hi: usize },
    }

    /// Scan grain for wide-object splitting (words). A 51200-slot array
    /// becomes ~12 stealable ranges via binary splitting.
    const SPLIT_WORDS: usize = 4096;

    /// Shared state of one CHUNKED parallel collection.
    pub(super) struct Shared<'a> {
        pub from_ranges: &'a [(usize, usize)],
        /// Object-start bitmap + per-range bit bases (see
        /// `Collector::find_body_start`) — read-only during the drain.
        start_bits: &'a [u64],
        range_bit_base: &'a [usize],
        base: SendBase,
        to_len: usize,
        /// Arena frontier: CHUNK claims only (one fetch_add per ~4 MB,
        /// not per object — object allocation is a plain local bump
        /// inside the owning worker's chunk).
        pub arena_used: AtomicUsize,
        /// Per-collection chunk size (== arena size when workers == 1, so
        /// the single-worker path never seals a chunk and produces the
        /// EXACT serial layout — no fillers, same addresses). Overridable
        /// per collection (`POLYML_GC_CHUNK_WORDS` / test stress).
        chunk_words: usize,
        /// Objects of `1 + n` words strictly above this get their own
        /// exact-size arena slice (bounds filler waste per seal).
        oversize_words: usize,
        /// Workers currently holding scannable work. A worker decrements
        /// on entering its idle probe and re-increments when it acquires
        /// work; `busy == 0` with an empty steal queue is quiescence
        /// (copies only happen while scanning, i.e. while busy).
        busy: AtomicUsize,
        /// Stealable work: full-but-unscanned chunks (swept linearly by
        /// the thief — locality preserved) and split wide-object slot
        /// ranges.
        steal: Mutex<Vec<Task>>,
        /// From-space pointers matching no tracked object (collector-bug
        /// canary, merged into `Collector::untracked_addrs` after the drain).
        pub untracked: Mutex<Vec<usize>>,
        /// POLYML_GC_PAR_STATS=1: per-worker breakdown on stderr.
        stats: bool,
        /// Weak objects registered during the parallel scan (to-space
        /// bodies); merged into `Collector::weak_objects` after the
        /// drain — the fixup itself is single-threaded.
        pub weak: Mutex<Vec<usize>>,
    }

    /// A worker's private two-slot state: the chunk it is SCANNING and
    /// the chunk it is ALLOCATING into (often the same — the serial-
    /// Cheney case, where scan chases alloc within one chunk).
    struct Worker {
        cur: Chunk,
        /// Sealed-but-still-scanning predecessor (when the alloc chunk
        /// filled mid-scan, scanning continues here until exhausted).
        scanning: Option<Chunk>,
        /// Next chunk claim size — doubles per seal up to
        /// `Shared::chunk_words` (adaptive: small collections claim
        /// small, big copiers reach the max in a few seals).
        next_chunk: usize,
        /// POLYML_GC_PAR_STATS instrumentation (words scanned / copied,
        /// chunks stolen, CAS claim losses) — zero-cost adds on the
        /// already-taken paths.
        words_scanned: usize,
        words_copied: usize,
        steals: usize,
        claim_losses: usize,
    }

    impl<'a> Shared<'a> {
        pub fn new(
            from_ranges: &'a [(usize, usize)],
            start_bits: &'a [u64],
            range_bit_base: &'a [usize],
            to_storage: &mut [PolyWord],
            root_used: usize,
            workers: usize,
            chunk_override: Option<usize>,
        ) -> Self {
            let to_len = to_storage.len();
            let chunk_words = if workers <= 1 {
                to_len
            } else {
                chunk_override.unwrap_or(CHUNK_WORDS).max(16)
            };
            let oversize_words = if workers <= 1 {
                usize::MAX
            } else {
                (chunk_words / 8).max(2)
            };
            // The serial roots phase copied into the contiguous prefix
            // [0, root_used) — seed it as the first stealable chunk.
            let mut steal = Vec::new();
            if root_used > 0 {
                steal.push(Task::Chunk(Chunk {
                    start: 0,
                    end: root_used,
                    alloc: root_used,
                    scan: 0,
                }));
            }
            Self {
                from_ranges,
                start_bits,
                range_bit_base,
                base: SendBase(to_storage.as_mut_ptr()),
                to_len,
                arena_used: AtomicUsize::new(root_used),
                chunk_words,
                oversize_words,
                busy: AtomicUsize::new(workers),
                steal: Mutex::new(steal),
                untracked: Mutex::new(Vec::new()),
                stats: crate::env::env_flag("POLYML_GC_PAR_STATS"),
                weak: Mutex::new(Vec::new()),
            }
        }

        /// Claim `n` words from the arena frontier. Panics on overflow —
        /// the caller sizes the arena with worker slack, and the serial
        /// path's Σ-used bound plus that slack covers every real case
        /// (same failure class as the serial `bump_to` assert).
        fn claim_arena(&self, n: usize) -> usize {
            let start = self.arena_used.fetch_add(n, Ordering::Relaxed);
            assert!(
                start + n <= self.to_len,
                "GC to-space overflow (chunked): requested {n}, at {start}/{}",
                self.to_len
            );
            start
        }

        /// Allocate `1 + n_words` for a copied object in the worker's
        /// current chunk (plain local bump); seal + replace the chunk
        /// when full. Returns the BODY pointer, plus — for OVERSIZED
        /// objects — a private chunk descriptor the caller must publish
        /// only AFTER the copy completes (publishing the chunk first
        /// would let a thief scan uninitialized words).
        fn alloc_obj(&self, w: &mut Worker, n_words: usize) -> (*mut PolyWord, Option<Chunk>) {
            let need = 1 + n_words;
            if need > self.oversize_words {
                // Oversized: its own exact arena slice.
                let start = self.claim_arena(need);
                let chunk = Chunk {
                    start,
                    end: start + need,
                    alloc: start + need,
                    scan: start,
                };
                // SAFETY: exclusive fresh claim.
                return (unsafe { self.base.0.add(start + 1) }, Some(chunk));
            }
            if w.cur.alloc + need > w.cur.end {
                self.seal_and_replace(w, need);
            }
            let body = w.cur.alloc + 1;
            w.cur.alloc += need;
            // SAFETY: within the worker's exclusively-owned chunk.
            (unsafe { self.base.0.add(body) }, None)
        }

        /// Seal the worker's current alloc chunk (plug the dead tail with
        /// a FILLER byte-object header so the heap stays one contiguous
        /// valid object sequence — walkers skip it; the next collection
        /// reclaims it) and open a fresh one big enough for `need`.
        fn seal_and_replace(&self, w: &mut Worker, need: usize) {
            let gap = w.cur.end - w.cur.alloc;
            if gap > 0 {
                // SAFETY: [alloc, end) is our exclusive dead tail.
                unsafe {
                    self.base
                        .0
                        .add(w.cur.alloc)
                        .write(length_word::make_length_word(gap - 1, F_BYTE_OBJ));
                }
                w.cur.alloc = w.cur.end;
            }
            let size = w.next_chunk.max(need);
            w.next_chunk = (w.next_chunk * 2).min(self.chunk_words);
            let start = self.claim_arena(size);
            let fresh = Chunk {
                start,
                end: start + size,
                alloc: start,
                scan: start,
            };
            let old = std::mem::replace(&mut w.cur, fresh);
            if old.scan < old.alloc {
                // Unscanned content survives the seal: keep it as our
                // scanning slot if free (we may be mid-sweep of exactly
                // this chunk — the sweep re-reads worker state each
                // iteration and picks it back up from `scanning`),
                // otherwise share it whole.
                if w.scanning.is_none() {
                    w.scanning = Some(old);
                } else {
                    self.steal.lock().unwrap().push(Task::Chunk(old));
                }
            }
        }

        #[inline]
        fn in_from_space(&self, addr: usize) -> bool {
            let idx = self
                .from_ranges
                .partition_point(|&(start, _)| start <= addr);
            idx > 0 && addr < self.from_ranges[idx - 1].1
        }

        /// Length of the object whose body starts at `body`, read
        /// ATOMICALLY (a peer may CAS the header concurrently): a NORMAL
        /// header gives the length directly (lengths never change, so a
        /// concurrent claim can't invalidate it); BUSY spins for the
        /// publish; a tombstone reads the (stable) to-space header.
        fn object_len_via_header_atomic(&self, body: usize) -> usize {
            let header_ptr = (body as *const PolyWord).cast_mut().wrapping_sub(1);
            let header = unsafe { AtomicUsize::from_ptr(header_ptr.cast::<usize>()) };
            let mut bits = header.load(Ordering::Acquire);
            loop {
                if (flags_of(PolyWord::from_bits(bits)) & F_TOMBSTONE_BIT) == 0 {
                    return length_of(PolyWord::from_bits(bits));
                }
                if bits != BUSY {
                    let to = bits & !BUSY;
                    let to_lw = unsafe { *(to as *const PolyWord).sub(1) };
                    return length_of(to_lw);
                }
                std::hint::spin_loop();
                bits = header.load(Ordering::Acquire);
            }
        }

        /// Parallel mirror of `Collector::find_body_start` (keep in sync):
        /// exact-bit O(1) hit, else backward scan with BUSY-safe length
        /// validation.
        fn find_body_start(&self, addr: usize) -> Option<usize> {
            let idx = self
                .from_ranges
                .partition_point(|&(start, _)| start <= addr);
            if idx == 0 || addr >= self.from_ranges[idx - 1].1 {
                return None;
            }
            let (range_start, _) = self.from_ranges[idx - 1];
            let bit_base = self.range_bit_base[idx - 1];
            let word_size = std::mem::size_of::<usize>();
            let word_idx = bit_base + (addr - range_start) / word_size;
            let is_start = |i: usize| self.start_bits[i / 64] & (1u64 << (i % 64)) != 0;
            if is_start(word_idx) {
                return Some(range_start + (word_idx - bit_base) * word_size);
            }
            let mut i = word_idx;
            while i > bit_base {
                i -= 1;
                if !is_start(i) {
                    continue;
                }
                let start = range_start + (i - bit_base) * word_size;
                let n = self.object_len_via_header_atomic(start);
                let end = start.saturating_add(n.saturating_mul(word_size));
                if addr < end {
                    return Some(start);
                }
                if n > 0 {
                    return None;
                }
            }
            None
        }

        /// Parallel forward of one object known to start at `body_start`:
        /// claim via header CAS, copy into the worker's chunk, publish.
        /// Returns the to-space body.
        ///
        /// # Safety
        /// `body_start` must be the body address of a well-formed
        /// from-space object (came from `find_object`).
        unsafe fn forward_object(&self, body_start: usize, w: &mut Worker) -> usize {
            let header_ptr = (body_start as *const PolyWord).cast_mut().wrapping_sub(1);
            // SAFETY: PolyWord is repr(transparent) over usize; the header
            // word is shared mutable state, accessed atomically only.
            let header = unsafe { AtomicUsize::from_ptr(header_ptr.cast::<usize>()) };
            let mut lw_bits = header.load(Ordering::Acquire);
            loop {
                if (flags_of(PolyWord::from_bits(lw_bits)) & F_TOMBSTONE_BIT) != 0 {
                    if lw_bits == BUSY {
                        // Another worker is mid-copy: wait for the publish.
                        std::hint::spin_loop();
                        lw_bits = header.load(Ordering::Acquire);
                        continue;
                    }
                    // Real tombstone: to-space body pointer in the low bits.
                    return lw_bits & !BUSY;
                }
                // NORMAL: try to claim.
                match header.compare_exchange_weak(
                    lw_bits,
                    BUSY,
                    Ordering::AcqRel,
                    Ordering::Acquire,
                ) {
                    Ok(_) => break,
                    Err(cur) => {
                        w.claim_losses += 1;
                        lw_bits = cur;
                    }
                }
            }
            // We hold the claim; lw_bits is the original length word.
            let lw = PolyWord::from_bits(lw_bits);
            let n_words = length_of(lw);
            let flags = flags_of(lw);
            let (to_ptr, oversize) = self.alloc_obj(w, n_words);
            let new_lw = length_word::make_length_word(n_words, flags);
            // SAFETY: to_ptr-1..to_ptr+n_words is our exclusive reservation;
            // the source body is frozen (all mutators parked, we hold the claim).
            unsafe {
                to_ptr.sub(1).write(new_lw);
                std::ptr::copy_nonoverlapping(body_start as *const PolyWord, to_ptr, n_words);
            }
            w.words_copied += 1 + n_words;
            unsafe {}
            // Publish: Release makes the copied body visible to any reader
            // that Acquire-loads this tombstone. No work-queue push: the
            // object sits in the worker's own chunk, which is swept
            // linearly (or stolen whole).
            header.store((to_ptr as usize) | BUSY, Ordering::Release);
            if let Some(c) = oversize {
                // Publish the oversize slice only now that its body is
                // fully written (the steal-mutex handoff orders the writes
                // for the thief).
                if w.scanning.is_none() {
                    w.scanning = Some(c);
                } else {
                    self.steal.lock().unwrap().push(Task::Chunk(c));
                }
            }
            to_ptr as usize
        }

        /// Parallel mirror of `Collector::forward_impl` for one slot.
        ///
        /// # Safety
        /// `slot` must be a valid, writable pointer to a PolyWord in a
        /// to-space object owned (being scanned) by this worker.
        unsafe fn forward_slot(&self, slot: *mut PolyWord, w: &mut Worker) {
            let word = unsafe { *slot };
            if word.is_tagged() {
                return;
            }
            let addr = word.0;
            if !self.in_from_space(addr) {
                return;
            }
            // Resolve the containing object via the start bitmap — O(1)
            // exact hit for body-start pointers; the backward scan covers
            // mid-body values (closure word-0 entry offsets point INSIDE
            // code objects — the body-start-assumption version of this
            // read garbage headers, caught by the chain fence).
            let Some(body_start) = self.find_body_start(addr) else {
                self.untracked.lock().unwrap().push(addr);
                return;
            };
            let new_body = unsafe { self.forward_object(body_start, w) };
            let offset_bytes = addr.wrapping_sub(body_start);
            unsafe { slot.write(PolyWord::from_bits(new_body.wrapping_add(offset_bytes))) };
        }

        /// Scan one to-space object — the parallel mirror of
        /// `Collector::scan_object` (same shape rules; keep in sync).
        ///
        /// # Safety
        /// `body` must be a fully-copied to-space object body address that
        /// this worker popped from a queue (sole scanner).
        unsafe fn scan_object(&self, body: usize, w: &mut Worker) {
            let obj_ptr = body as *mut PolyWord;
            // SAFETY: header written before the queue push (program order
            // of the copier + the Mutex transfer / local ownership).
            let lw = unsafe { *obj_ptr.sub(1) };
            let n_words = length_of(lw);
            match type_of(lw) {
                F_BYTE_OBJ => {}
                F_CODE_OBJ => {
                    let (cp, count) = unsafe { length_word::const_segment_for_code(obj_ptr) };
                    let cp_mut = cp.cast_mut();
                    for i in 0..count {
                        unsafe { self.forward_slot(cp_mut.add(i), w) };
                    }
                }
                F_CLOSURE_OBJ => {
                    for i in 0..n_words {
                        unsafe { self.forward_slot(obj_ptr.add(i), w) };
                    }
                }
                _ => {
                    // WEAK word object: slots are the weak links — skip
                    // (mirror of the serial arm; the single-threaded
                    // post-drain `weak_fixup` resolves them).
                    if (super::flags_of(lw) & super::F_WEAK_BIT) != 0 {
                        self.weak.lock().unwrap().push(body);
                        return;
                    }
                    // SAFETY: sole scanner of this object; scan_slots
                    // splits wide ranges into disjoint stealable tasks.
                    unsafe { self.scan_slots(body, 0, n_words, w) };
                }
            }
        }

        /// Forward slots [lo, hi) of the word object at `body`, binary-
        /// splitting ranges wider than `SPLIT_WORDS` into the steal queue
        /// so peers copy a wide parent's children in parallel.
        ///
        /// # Safety
        /// The range [lo, hi) of `body` must be exclusively ours (sole
        /// scanner of the object, or a stolen disjoint range).
        unsafe fn scan_slots(&self, body: usize, mut lo: usize, mut hi: usize, w: &mut Worker) {
            while hi - lo > SPLIT_WORDS {
                let mid = lo + (hi - lo) / 2;
                self.steal
                    .lock()
                    .unwrap()
                    .push(Task::Slots { body, lo: mid, hi });
                hi = mid;
            }
            let obj_ptr = body as *mut PolyWord;
            for i in lo..hi {
                unsafe { self.forward_slot(obj_ptr.add(i), w) };
            }
            w.words_scanned += hi - lo;
        }

        /// Sweep the worker's OWN current chunk: the serial-Cheney
        /// scan-chases-alloc loop, re-reading `w.cur` FRESH each
        /// iteration — a copy can seal-and-replace the chunk under us
        /// (the sealed remainder moves to `w.scanning`/the steal queue
        /// atomically, so nothing is scanned twice or skipped).
        unsafe fn sweep_own(&self, w: &mut Worker) {
            loop {
                if w.cur.scan >= w.cur.alloc {
                    return;
                }
                // SAFETY: [scan, alloc) of our exclusively-owned chunk is
                // a valid object sequence (headers precede publication).
                let lw = unsafe { *self.base.0.add(w.cur.scan) };
                let n = length_of(lw);
                let body = unsafe { self.base.0.add(w.cur.scan + 1) } as usize;
                w.cur.scan += 1 + n;
                w.words_scanned += 1 + n;
                // SAFETY: fully-copied object in the arena.
                unsafe { self.scan_object(body, w) };
            }
        }

        /// Sweep a FOREIGN chunk (sealed predecessor or stolen): its
        /// alloc frontier is frozen, contents exclusively ours to scan;
        /// fresh copies land in `w.cur` (which may itself seal — handled
        /// by `seal_and_replace`).
        unsafe fn sweep_foreign(&self, mut chunk: Chunk, w: &mut Worker) {
            while chunk.scan < chunk.alloc {
                // SAFETY: as in sweep_own; frozen frontier.
                let lw = unsafe { *self.base.0.add(chunk.scan) };
                let n = length_of(lw);
                let body = unsafe { self.base.0.add(chunk.scan + 1) } as usize;
                chunk.scan += 1 + n;
                w.words_scanned += 1 + n;
                // SAFETY: fully-copied object in the arena.
                unsafe { self.scan_object(body, w) };
            }
        }

        /// One worker's run loop — the CHUNKED drain. Priority: the
        /// sealed predecessor, then our own alloc frontier (serial-Cheney
        /// locality), then stealing WHOLE chunks; quiesce when everyone
        /// is idle and nothing is stealable (copies only happen while
        /// scanning, so `busy == 0` + empty queue cannot un-quiesce).
        pub(super) fn drain(&self) {
            let mut w = Worker {
                cur: Chunk {
                    start: 0,
                    end: 0,
                    alloc: 0,
                    scan: 0,
                },
                scanning: None,
                next_chunk: INITIAL_CHUNK_WORDS.min(self.chunk_words),
                words_scanned: 0,
                words_copied: 0,
                steals: 0,
                claim_losses: 0,
            };
            let mut idle_spins = 0u32;
            loop {
                if let Some(sc) = w.scanning.take() {
                    idle_spins = 0;
                    // SAFETY: exclusively ours (the seal handoff).
                    unsafe { self.sweep_foreign(sc, &mut w) };
                    continue;
                }
                if w.cur.scan < w.cur.alloc {
                    idle_spins = 0;
                    // SAFETY: our own chunk.
                    unsafe { self.sweep_own(&mut w) };
                    continue;
                }
                let stolen = self.steal.lock().unwrap().pop();
                if let Some(task) = stolen {
                    idle_spins = 0;
                    w.steals += 1;
                    // SAFETY: exclusively transferred by the queue.
                    match task {
                        Task::Chunk(sc) => unsafe { self.sweep_foreign(sc, &mut w) },
                        Task::Slots { body, lo, hi } => unsafe {
                            self.scan_slots(body, lo, hi, &mut w)
                        },
                    }
                    continue;
                }
                // Idle probe: nothing local, nothing stealable.
                self.busy.fetch_sub(1, Ordering::AcqRel);
                loop {
                    if !self.steal.lock().unwrap().is_empty() {
                        self.busy.fetch_add(1, Ordering::AcqRel);
                        break; // re-enter the work loop
                    }
                    if self.busy.load(Ordering::Acquire) == 0 {
                        if self.stats {
                            eprintln!(
                                "  GC worker: scanned {}w copied {}w steals {} claim_losses {}",
                                w.words_scanned, w.words_copied, w.steals, w.claim_losses
                            );
                        }
                        // Global quiescence. Plug our final open chunk's
                        // tail with a filler so the whole promoted arena
                        // [0, arena_used) stays one contiguous valid
                        // object sequence — the next collection's bitmap
                        // pre-pass walks it by headers.
                        let gap = w.cur.end - w.cur.alloc;
                        if gap > 0 {
                            // SAFETY: [alloc, end) is our exclusive dead tail.
                            unsafe {
                                self.base
                                    .0
                                    .add(w.cur.alloc)
                                    .write(length_word::make_length_word(gap - 1, F_BYTE_OBJ));
                            }
                        }
                        return;
                    }
                    idle_spins += 1;
                    if idle_spins < 64 {
                        std::hint::spin_loop();
                    } else if idle_spins < 80 {
                        std::thread::yield_now();
                    } else {
                        std::thread::sleep(std::time::Duration::from_micros(50));
                    }
                }
            }
        }
    }
}

/// P6 gate: `Some(n)` iff `POLYML_PARALLEL_GC=1` and the effective worker
/// count (`POLYML_GC_THREADS` override, else `available_parallelism`) is
/// at least 2. `None` = the exact serial path (default; byte-identical).
fn parallel_gc_workers() -> Option<usize> {
    if !crate::env::env_flag("POLYML_PARALLEL_GC") {
        return None;
    }
    let n = std::env::var("POLYML_GC_THREADS")
        .ok()
        .and_then(|s| s.trim().parse::<usize>().ok())
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(std::num::NonZeroUsize::get)
                .unwrap_or(1)
        })
        .min(64);
    (n >= 2).then_some(n)
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
    // P6: parallel scan gate. Read fresh per collection (collections are
    // rare; no memoization hazard for tests).
    collect_pool_with_workers(spaces, parallel_gc_workers(), visit_roots)
}

/// [`collect_pool`] with an explicit parallel-worker override (`None` /
/// `Some(0|1)` = serial). Unit tests drive the parallel drain through this
/// without process-global env manipulation.
pub fn collect_pool_with_workers<F>(
    spaces: &mut [&mut MemorySpace],
    par_workers: Option<usize>,
    visit_roots: F,
) -> usize
where
    F: FnOnce(&mut Collector<'_>),
{
    // POLYML_GC_CHUNK_WORDS: per-worker chunk size tuning knob for the
    // chunked parallel drain (default 512K words = 4 MB).
    let chunk_override = std::env::var("POLYML_GC_CHUNK_WORDS")
        .ok()
        .and_then(|v| v.parse::<usize>().ok());
    collect_pool_with_workers_impl(spaces, par_workers, chunk_override, visit_roots)
}

fn collect_pool_with_workers_impl<F>(
    spaces: &mut [&mut MemorySpace],
    par_workers: Option<usize>,
    chunk_override: Option<usize>,
    visit_roots: F,
) -> usize
where
    F: FnOnce(&mut Collector<'_>),
{
    assert!(
        !spaces.is_empty(),
        "collect_pool needs at least one nursery"
    );

    // POLYML_GC_PHASES=1: per-phase pause timing on stderr (pre-pass /
    // scratch / roots / scan / promote) — the instrument that tells you
    // WHICH term dominates a pause before optimizing the wrong one.
    let phases = crate::env::env_flag("POLYML_GC_PHASES");
    let t0 = std::time::Instant::now();

    // from-space ranges (full storage capacity per space, as the old
    // single-space code used `as_ptr_range`), sorted for binary-search
    // membership, + the object-start BITMAP pre-pass over each space's
    // USED region (consumed only by stack-slot forwarding — see
    // `Collector::find_object`).
    let mut ranges_unsorted: Vec<(usize, usize, usize)> = Vec::with_capacity(spaces.len()); // (start, end, capacity)
    let mut total_used = 0usize;
    for space in spaces.iter() {
        let range = space.as_ptr_range();
        ranges_unsorted.push((
            range.start as usize,
            range.end as usize,
            space.capacity_words(),
        ));
        total_used += space.used_words();
    }
    // To-space sizing: live can never exceed Σ USED, and the primary
    // should keep (at least) its own capacity across the swap. Sizing by
    // Σ CAPACITY instead (the original pool formula) BALLOONED the
    // primary by the children's total capacity on EVERY pool collection
    // (replace_storage hands the whole scratch to the primary) —
    // unbounded RSS growth, ~+192 MB/cycle with six 32 MB nurseries.
    // Single-space: Σ used ≤ capacity, so this is exactly the old
    // "to-space = the space's capacity" — byte-identical.
    let total_capacity = spaces[0].capacity_words().max(total_used);
    ranges_unsorted.sort_unstable();
    let from_ranges: Vec<(usize, usize)> =
        ranges_unsorted.iter().map(|&(s, e, _)| (s, e)).collect();
    // Bit bases: each (sorted) range gets a contiguous bit run sized to
    // its capacity.
    let mut range_bit_base = Vec::with_capacity(ranges_unsorted.len());
    let mut bits_total = 0usize;
    for &(_, _, cap) in &ranges_unsorted {
        range_bit_base.push(bits_total);
        bits_total += cap;
    }
    if std::env::var("POLYML_GC_SIZES").is_ok() {
        let total_used: usize = spaces.iter().map(|s| s.used_words()).sum();
        eprintln!(
            "  GC sizes: spaces={} primary_cap={} total_used={} bits_total={} bitmap_bytes={}",
            spaces.len(),
            spaces[0].capacity_words(),
            total_used,
            bits_total,
            bits_total.div_ceil(64) * 8,
        );
    }
    let mut start_bits = vec![0u64; bits_total.div_ceil(64)];
    for (k, &(start, _, _)) in ranges_unsorted.iter().enumerate() {
        let space = spaces
            .iter()
            .find(|s| s.as_ptr_range().start as usize == start)
            .expect("sorted range must correspond to a space");
        let storage_start = space.as_ptr_range().start;
        let used_words = space.used_words();
        let bit_base = range_bit_base[k];
        let mut i = 0usize;
        while i < used_words {
            // SAFETY: i is in-bounds of this space's storage slice.
            let lw = unsafe { *storage_start.add(i) };
            let n = length_of(lw);
            if i + 1 + n > used_words {
                i += 1;
                continue;
            }
            let body_bit = bit_base + i + 1;
            start_bits[body_bit / 64] |= 1u64 << (body_bit % 64);
            i += 1 + n;
        }
    }

    let t_prepass = t0.elapsed();

    // Σ-capacity to-space (never overflows). Allocate as `Vec<usize>` —
    // that hits the `IsZero` → `alloc_zeroed` (calloc) specialization, so
    // the kernel hands us LAZY zero pages and only live pages ever fault
    // in. `vec![PolyWord::ZERO; n]` (a custom struct) misses the
    // specialization and explicitly memsets the whole capacity — measured
    // ~175 ms per collection on a 512 MB heap, the second-largest pause
    // term. PolyWord is repr(transparent) over usize, so the box transmute
    // is layout-identical.
    // Worker count None/0/1 = the exact serial path.
    let par_workers = par_workers.filter(|&n| n >= 2);
    // CHUNKED-path slack: sealed chunk tails (fillers) + open chunks per
    // worker can exceed Σ used. Bound: at max chunk size each seal wastes
    // < CHUNK/8 (oversize objects get exact slices) while consuming ≥
    // 7/8·CHUNK, so steady-state waste ≤ consumed/7; the adaptive growth
    // ramp (INITIAL → CHUNK doubling) adds < 2·CHUNK per worker of
    // sub-max claims plus the final open chunk. live/4 + 3·w·CHUNK sits
    // safely above waste ≤ live/6 + ~2.4·w·CHUNK. Over-reservation is
    // virtually free (lazy-zero pages — only live pages fault in).
    let total_capacity = if let Some(w) = par_workers {
        let live: usize = spaces.iter().map(|s| s.used_words()).sum();
        let chunk = chunk_override.unwrap_or(512 * 1024).max(16);
        total_capacity.max(live + live / 4 + w * 3 * chunk)
    } else {
        total_capacity
    };

    // PING-PONG scratch reuse: the primary's retired from-space (stashed
    // last cycle) becomes this cycle's to-space when big enough — killing
    // the per-cycle munmap of ~capacity faulted pages (measured ~190 ms of
    // the promote phase on a 1.3 GB heap) AND the invisible mutator-side
    // re-faulting of a fresh lazy-zero arena after every collection. The
    // collector never reads to-space words it did not write, so STALE
    // contents are harmless. Gates: POLYML_GC_REUSE_MAX_BYTES (default
    // 4 GB; 0 disables) bounds the sustained 2x residency on huge heaps,
    // and POLYML_GC_AUDIT forces the calloc path (the audit scans
    // [0, len) — stale tails would false-positive — and fresh mappings
    // keep missed-root dangling pointers SEGV-detectable rather than
    // silently reading recycled memory).
    let audit = crate::env::env_flag("POLYML_GC_AUDIT");
    let reuse_max_words = std::env::var("POLYML_GC_REUSE_MAX_BYTES")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(4_000_000_000)
        / std::mem::size_of::<usize>();
    let reuse_enabled = !audit && total_capacity <= reuse_max_words;
    let mut scratch: Box<[PolyWord]> = match spaces[0].spare.take() {
        Some(b) if reuse_enabled && b.len() >= total_capacity => b,
        _ => {
            // Fresh calloc arena (lazy zero pages; see the comment above).
            let scratch_raw: Box<[usize]> = vec![0usize; total_capacity].into_boxed_slice();
            // SAFETY: PolyWord is repr(transparent) over usize (same layout,
            // any bit pattern valid); Box<[usize]> and Box<[PolyWord]> are
            // interchangeable.
            unsafe { Box::from_raw(Box::into_raw(scratch_raw) as *mut [PolyWord]) }
        }
    };

    let t_scratch = t0.elapsed();

    let mut col = Collector {
        from_ranges,
        to_storage: &mut scratch,
        to_used: 0,
        start_bits,
        range_bit_base,
        weak_objects: Vec::new(),
        untracked_addrs: Vec::new(),
        par_workers,
    };

    visit_roots(&mut col);
    let t_roots = t0.elapsed();
    if let Some(workers) = col.par_workers {
        // P6 CHUNKED parallel collection (docs/parallel-design.md § P6):
        // the serial roots phase copied into the contiguous prefix
        // [0, to_used), which becomes the first stealable chunk; workers
        // then claim 4 MB chunks from the arena frontier, allocate into
        // them with PLAIN LOCAL bumps, and sweep each chunk LINEARLY —
        // the per-worker serial-Cheney locality the queue-drain design
        // lacked. Dead chunk tails are plugged with FILLER byte objects,
        // so the promoted heap stays one contiguous valid object
        // sequence and no space accounting changes anywhere.
        let shared = par::Shared::new(
            &col.from_ranges,
            &col.start_bits,
            &col.range_bit_base,
            col.to_storage,
            col.to_used,
            workers,
            chunk_override,
        );
        std::thread::scope(|s| {
            for _ in 1..workers {
                let sh = &shared;
                s.spawn(move || sh.drain());
            }
            shared.drain();
        });
        col.to_used = shared.arena_used.load(std::sync::atomic::Ordering::Acquire);
        col.untracked_addrs
            .extend(shared.untracked.lock().unwrap().iter().copied());
        col.weak_objects
            .extend(shared.weak.lock().unwrap().iter().copied());
    } else {
        // SAFETY: collector invariants upheld.
        unsafe { col.cheney_scan() };
    }
    // Weak-reference fixup (single-threaded, both paths): forward
    // surviving SOME cells, demote dead entries to NONE. Runs after the
    // strong trace's fixpoint, before promote — so no weak slot ever
    // survives into the promoted heap holding a from-space pointer.
    // SAFETY: trace complete; sole heap accessor.
    unsafe { col.weak_fixup() };
    let t_scan = t0.elapsed();

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
    spaces[0].replace_storage_pingpong(scratch, new_used, reuse_enabled);
    for space in spaces.iter_mut().take(n_spaces).skip(1) {
        space.reset_empty();
    }
    if phases {
        let total = t0.elapsed();
        eprintln!(
            "  GC phases: pre-pass {:.1}ms | scratch {:.1}ms | roots {:.1}ms | scan {:.1}ms | promote {:.1}ms | total {:.1}ms ({} live words, workers={:?})",
            t_prepass.as_secs_f64() * 1e3,
            (t_scratch - t_prepass).as_secs_f64() * 1e3,
            (t_roots - t_scratch).as_secs_f64() * 1e3,
            (t_scan - t_roots).as_secs_f64() * 1e3,
            (total - t_scan).as_secs_f64() * 1e3,
            total.as_secs_f64() * 1e3,
            new_used,
            par_workers,
        );
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
        self.replace_storage_pingpong(new_storage, new_used, false);
    }

    /// Swap in the new to-space; the retired from-space is STASHED as the
    /// ping-pong spare (`keep_spare`) for reuse as the next collection's
    /// scratch, or dropped (the pre-reuse behavior).
    pub fn replace_storage_pingpong(
        &mut self,
        new_storage: Box<[PolyWord]>,
        new_used: usize,
        keep_spare: bool,
    ) {
        assert!(new_used <= new_storage.len());
        let old = std::mem::replace(&mut self.storage, new_storage);
        self.used = new_used;
        self.spare = if keep_spare { Some(old) } else { None };
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

    /// P6: the PARALLEL drain preserves the same cross-nursery graph the
    /// serial collector does (4 workers, explicit override — no env).
    #[test]
    fn parallel_collect_pool_forwards_cross_nursery_pointer() {
        let mut a = MemorySpace::new(64, SpaceKind::Mutable);
        let mut b = MemorySpace::new(64, SpaceKind::Mutable);
        let leaf = b.alloc(1);
        unsafe {
            set_length_word(leaf, 1, F_BYTE_OBJ);
            leaf.write(PolyWord::from_bits(0xcafe_f00d));
        }
        let parent = a.alloc(2);
        unsafe {
            set_length_word(parent, 2, 0);
            parent.write(PolyWord::from_ptr(leaf.cast_const()));
            parent.add(1).write(PolyWord::tagged(7));
        }

        let mut root = PolyWord::from_ptr(parent.cast_const());
        let new_used = collect_pool_with_workers(&mut [&mut a, &mut b], Some(4), |c| {
            unsafe { c.forward(&mut root as *mut _) };
        });

        assert_eq!(b.used_words(), 0);
        assert!(new_used >= 4);
        let new_parent = root.as_ptr::<PolyWord>();
        let new_leaf = unsafe { *new_parent }.as_ptr::<PolyWord>();
        assert_eq!(unsafe { (*new_leaf).0 }, 0xcafe_f00d);
        assert_eq!(unsafe { (*new_parent.add(1)).0 }, PolyWord::tagged(7).0);
    }

    /// P6 stress: a wide shared DAG across two nurseries — 2,000 parents
    /// that ALL point at the same two leaves plus a long chain, drained by
    /// 4 workers. The shared leaves force claim-CAS races (many scanners
    /// reach them concurrently); the chain forces steal traffic (all depth
    /// initially on one worker). Verifies: exact live word count (no
    /// duplicate copies — the Σ-capacity bound's soundness), every parent's
    /// leaf pointers point at ONE shared copy each (sharing preserved), and
    /// chain integrity end-to-end.
    #[test]
    fn parallel_collect_shared_dag_stress() {
        const PARENTS: usize = 2000;
        const CHAIN: usize = 1000;
        let mut a = MemorySpace::new((PARENTS + CHAIN) * 8, SpaceKind::Mutable);
        let mut b = MemorySpace::new((PARENTS + CHAIN) * 8, SpaceKind::Mutable);

        // Two shared leaves in B.
        let leaf1 = b.alloc(1);
        let leaf2 = b.alloc(1);
        unsafe {
            set_length_word(leaf1, 1, F_BYTE_OBJ);
            leaf1.write(PolyWord::from_bits(0x1111_1111));
            set_length_word(leaf2, 1, F_BYTE_OBJ);
            leaf2.write(PolyWord::from_bits(0x2222_2222));
        }
        // A chain of CHAIN cons cells in B (tail-linked), ending at leaf2.
        let mut chain_head = PolyWord::from_ptr(leaf2.cast_const());
        for i in 0..CHAIN {
            let cell = b.alloc(2);
            unsafe {
                set_length_word(cell, 2, 0);
                cell.write(PolyWord::tagged(i as isize));
                cell.add(1).write(chain_head);
            }
            chain_head = PolyWord::from_ptr(cell.cast_const());
        }
        // PARENTS parents in A, each pointing at BOTH leaves + the chain.
        let mut parents = Vec::with_capacity(PARENTS);
        for i in 0..PARENTS {
            let p = a.alloc(4);
            unsafe {
                set_length_word(p, 4, 0);
                p.write(PolyWord::from_ptr(leaf1.cast_const()));
                p.add(1).write(PolyWord::from_ptr(leaf2.cast_const()));
                p.add(2).write(chain_head);
                p.add(3).write(PolyWord::tagged(i as isize));
            }
            parents.push(PolyWord::from_ptr(p.cast_const()));
        }

        // Live words: parents (1+4 each) + chain (1+2 each) + 2 leaves (1+1).
        let expected_live = PARENTS * 5 + CHAIN * 3 + 2 * 2;

        let new_used = collect_pool_with_workers(&mut [&mut a, &mut b], Some(4), |c| {
            for r in &mut parents {
                unsafe { c.forward(r as *mut _) };
            }
        });
        // Chunked promotion plugs dead chunk tails with FILLER byte
        // objects, so new_used ≥ live; the exact-count check moves to a
        // filler-aware heap walk below.
        assert!(
            new_used >= expected_live,
            "promoted arena smaller than live data — lost work"
        );

        // Sharing preserved: every parent sees the SAME forwarded leaves.
        let p0 = parents[0].as_ptr::<PolyWord>();
        let (l1, l2, ch) = unsafe { ((*p0).0, (*p0.add(1)).0, (*p0.add(2)).0) };

        // Walk the promoted heap [0, new_used): every header must parse
        // (contiguous valid object sequence — an unsealed tail or corrupt
        // filler shows here), and non-filler words must sum EXACTLY to
        // the live count — a duplicate copy (claim race) or a dropped
        // object (lost work) shows here. The only real byte objects are
        // the two leaves, so any other byte object is a filler.
        let heap_start = a.as_ptr_range().start;
        let mut i = 0usize;
        let mut live_words = 0usize;
        while i < new_used {
            let lw = unsafe { *heap_start.add(i) };
            let n = length_of(lw);
            assert!(
                i + 1 + n <= new_used,
                "object at word {i} (len {n}) overruns the promoted arena"
            );
            let body = unsafe { heap_start.add(i + 1) } as usize;
            let is_filler = type_of(lw) == F_BYTE_OBJ && body != l1 && body != l2;
            if !is_filler {
                live_words += 1 + n;
            }
            i += 1 + n;
        }
        assert_eq!(
            i, new_used,
            "promoted arena walk must land exactly on new_used"
        );
        assert_eq!(
            live_words, expected_live,
            "live word count must be EXACT — a duplicate copy (claim race) \
             or a dropped object (lost work) shows here"
        );
        for (i, r) in parents.iter().enumerate() {
            let p = r.as_ptr::<PolyWord>();
            unsafe {
                assert_eq!((*p).0, l1, "parent {i}: leaf1 sharing broken");
                assert_eq!((*p.add(1)).0, l2, "parent {i}: leaf2 sharing broken");
                assert_eq!((*p.add(2)).0, ch, "parent {i}: chain sharing broken");
                assert_eq!((*p.add(3)).0, PolyWord::tagged(i as isize).0);
            }
        }
        unsafe {
            assert_eq!((*(l1 as *const PolyWord)).0, 0x1111_1111);
            assert_eq!((*(l2 as *const PolyWord)).0, 0x2222_2222);
        }
        // Chain integrity: walk all CHAIN cells to the shared leaf2.
        let mut cur = ch;
        for step in 0..CHAIN {
            let cell = cur as *const PolyWord;
            unsafe {
                assert_eq!(
                    (*cell).0,
                    PolyWord::tagged((CHAIN - 1 - step) as isize).0,
                    "chain payload corrupted at depth {step}"
                );
                cur = (*cell.add(1)).0;
            }
        }
        assert_eq!(cur, l2, "chain must terminate at the shared leaf2");
    }

    /// Chunk-churn stress: TINY chunks (64 words, oversize threshold 8)
    /// force constant seal / steal / oversize-slice traffic — hundreds of
    /// chunk transitions where the default 4 MB chunks would produce one.
    /// 8 chains of mixed-size nodes (2..=12 words — the top sizes take the
    /// oversize path) alternating across two nurseries (cross-space edges),
    /// all sharing 3 hot leaves (claim-CAS races), repeated 10 rounds.
    #[test]
    fn parallel_collect_chunk_churn_stress() {
        const CHAINS: usize = 8;
        const NODES: usize = 400; // per chain
        for _round in 0..10 {
            let mut a = MemorySpace::new(CHAINS * NODES * 16, SpaceKind::Mutable);
            let mut b = MemorySpace::new(CHAINS * NODES * 16, SpaceKind::Mutable);
            let mut expected_live = 0usize;

            // Three hot shared leaves (word objects; every node points at one).
            let mut leaves = [PolyWord::tagged(0); 3];
            for (j, leaf) in leaves.iter_mut().enumerate() {
                let p = b.alloc(1);
                unsafe {
                    set_length_word(p, 1, 0);
                    p.write(PolyWord::tagged(0x5EED + j as isize));
                }
                *leaf = PolyWord::from_ptr(p.cast_const());
                expected_live += 2;
            }

            let mut heads = Vec::with_capacity(CHAINS);
            for c in 0..CHAINS {
                let mut head = PolyWord::tagged(0);
                for i in 0..NODES {
                    let n = 2 + ((c + i) % 11); // 2..=12 words
                    let space = if (c + i) % 2 == 0 { &mut a } else { &mut b };
                    let p = space.alloc(n);
                    unsafe {
                        set_length_word(p, n, 0);
                        p.write(head);
                        p.add(1).write(leaves[(c + i) % 3]);
                        for k in 2..n {
                            p.add(k)
                                .write(PolyWord::tagged((c * 100_000 + i * 31 + k) as isize));
                        }
                    }
                    head = PolyWord::from_ptr(p.cast_const());
                    expected_live += 1 + n;
                }
                heads.push(head);
            }

            let new_used =
                collect_pool_with_workers_impl(&mut [&mut a, &mut b], Some(4), Some(64), |col| {
                    for r in &mut heads {
                        unsafe { col.forward(r as *mut _) };
                    }
                    for r in &mut leaves {
                        unsafe { col.forward(r as *mut _) };
                    }
                });

            // Walk the promoted arena: contiguous validity + EXACT live
            // accounting (all live objects are WORD objects, so every byte
            // object is a filler).
            let heap_start = a.as_ptr_range().start;
            let (mut i, mut live_words) = (0usize, 0usize);
            while i < new_used {
                let lw = unsafe { *heap_start.add(i) };
                let n = length_of(lw);
                assert!(
                    i + 1 + n <= new_used,
                    "object at word {i} overruns the arena"
                );
                if type_of(lw) != F_BYTE_OBJ {
                    live_words += 1 + n;
                }
                i += 1 + n;
            }
            assert_eq!(i, new_used, "walk must land exactly on new_used");
            assert_eq!(
                live_words, expected_live,
                "live word count must be EXACT — duplicate copy or lost object"
            );

            // Leaf payloads survived + forwarded roots are canonical.
            for (j, leaf) in leaves.iter().enumerate() {
                unsafe {
                    assert_eq!(
                        (*leaf.as_ptr::<PolyWord>()).0,
                        PolyWord::tagged(0x5EED + j as isize).0,
                        "leaf {j}: payload corrupted"
                    );
                }
            }
            // Payload + chain integrity, and leaf-sharing per node: every
            // node's leaf slot must be the ONE forwarded copy of its leaf.
            for (c, head) in heads.iter().enumerate() {
                let mut cur = *head;
                for i in (0..NODES).rev() {
                    let n = 2 + ((c + i) % 11);
                    let p = cur.as_ptr::<PolyWord>();
                    unsafe {
                        assert_eq!(
                            (*p.add(1)).0,
                            leaves[(c + i) % 3].0,
                            "chain {c} node {i}: leaf sharing broken"
                        );
                        for k in 2..n {
                            assert_eq!(
                                (*p.add(k)).0,
                                PolyWord::tagged((c * 100_000 + i * 31 + k) as isize).0,
                                "chain {c} node {i} word {k}: payload corrupted"
                            );
                        }
                        cur = *p;
                    }
                }
                assert_eq!(cur.0, PolyWord::tagged(0).0, "chain {c} must end at nil");
            }
        }
    }

    /// Weak references (upstream gc_check_weak_ref.cpp semantics, ported
    /// to the copying collector): a weak object's slots hold NONE or
    /// SOME-cell pointers; after collection an entry whose inner ref was
    /// unreachable through strong paths reads NONE, a surviving entry
    /// points at the ONE forwarded SOME whose content is the forwarded
    /// ref. Covers: dead ref -> NONE; live-elsewhere ref -> survives;
    /// SOME cell shared by two weak slots (both outcomes); SOME cell
    /// ALSO strongly reachable; and the parallel drain.
    #[test]
    fn weak_refs_dead_demoted_live_forwarded() {
        for workers in [None, Some(4)] {
            let mut a = MemorySpace::new(4096, SpaceKind::Mutable);

            let mk_ref = |sp: &mut MemorySpace, val: usize| {
                let r = sp.alloc(1);
                unsafe {
                    set_length_word(r, 1, F_MUTABLE_BIT);
                    r.write(PolyWord::tagged(val as isize));
                }
                r
            };
            let mk_some = |sp: &mut MemorySpace, r: *mut PolyWord| {
                let s = sp.alloc(1);
                unsafe {
                    set_length_word(s, 1, 0);
                    s.write(PolyWord::from_ptr(r.cast_const()));
                }
                s
            };

            let dead_ref = mk_ref(&mut a, 111);
            let live_ref = mk_ref(&mut a, 222);
            let shared_dead_ref = mk_ref(&mut a, 333);
            let strong_ref = mk_ref(&mut a, 444);

            let some_dead = mk_some(&mut a, dead_ref);
            let some_live = mk_some(&mut a, live_ref);
            let some_shared = mk_some(&mut a, shared_dead_ref);
            let some_strong = mk_some(&mut a, strong_ref);

            // Weak object: 5 slots (weakArray shape), alloc flags 0wx60.
            let wk = a.alloc(5);
            unsafe {
                set_length_word(wk, 5, F_MUTABLE_BIT | F_WEAK_BIT);
                wk.write(PolyWord::from_ptr(some_dead.cast_const()));
                wk.add(1).write(PolyWord::from_ptr(some_live.cast_const()));
                wk.add(2)
                    .write(PolyWord::from_ptr(some_shared.cast_const()));
                wk.add(3)
                    .write(PolyWord::from_ptr(some_shared.cast_const())); // shared
                wk.add(4)
                    .write(PolyWord::from_ptr(some_strong.cast_const()));
            }
            // Second weak object holding the live SOME too (shared, alive).
            let wk2 = a.alloc(1);
            unsafe {
                set_length_word(wk2, 1, F_MUTABLE_BIT | F_WEAK_BIT);
                wk2.write(PolyWord::from_ptr(some_live.cast_const()));
            }

            // Strong roots: both weak objects, the LIVE ref (held
            // elsewhere), and the strongly-shared SOME cell.
            let mut root_wk = PolyWord::from_ptr(wk.cast_const());
            let mut root_wk2 = PolyWord::from_ptr(wk2.cast_const());
            let mut root_live = PolyWord::from_ptr(live_ref.cast_const());
            let mut root_some_strong = PolyWord::from_ptr(some_strong.cast_const());

            collect_pool_with_workers_impl(&mut [&mut a], workers, Some(64), |c| unsafe {
                c.forward(&mut root_wk as *mut _);
                c.forward(&mut root_wk2 as *mut _);
                c.forward(&mut root_live as *mut _);
                c.forward(&mut root_some_strong as *mut _);
            });

            let w = root_wk.as_ptr::<PolyWord>();
            let none = PolyWord::tagged(0).0;
            unsafe {
                // Slot 0: dead ref -> NONE.
                assert_eq!((*w).0, none, "workers={workers:?}: dead entry not demoted");
                // Slot 1: live ref -> SOME survives; content = forwarded live ref.
                let s1 = (*w.add(1)).0;
                assert_ne!(s1, none, "workers={workers:?}: live entry wrongly demoted");
                let inner = (*(s1 as *const PolyWord)).0;
                assert_eq!(
                    inner, root_live.0,
                    "workers={workers:?}: surviving SOME must hold the forwarded ref"
                );
                assert_eq!(
                    (*(inner as *const PolyWord)).0,
                    PolyWord::tagged(222).0,
                    "workers={workers:?}: ref payload corrupted"
                );
                // wk2 shares the SAME surviving SOME copy.
                let w2 = root_wk2.as_ptr::<PolyWord>();
                assert_eq!(
                    (*w2).0,
                    s1,
                    "workers={workers:?}: shared surviving SOME must be ONE copy"
                );
                // Slots 2+3: shared SOME with dead ref -> both NONE.
                assert_eq!((*w.add(2)).0, none, "workers={workers:?}: shared dead 1");
                assert_eq!((*w.add(3)).0, none, "workers={workers:?}: shared dead 2");
                // Slot 4: SOME also strongly rooted -> the strong copy,
                // with its ref kept alive through it.
                let s4 = (*w.add(4)).0;
                assert_eq!(
                    s4, root_some_strong.0,
                    "workers={workers:?}: strongly-shared SOME must be the strong copy"
                );
                let inner4 = (*(s4 as *const PolyWord)).0;
                assert_eq!((*(inner4 as *const PolyWord)).0, PolyWord::tagged(444).0);
            }
        }
    }

    /// PING-PONG reuse: across consecutive collections the primary's
    /// retired from-space must round-trip as the next to-space (same
    /// allocation, no per-cycle map/unmap), and results must be correct
    /// on the recycled (stale, non-zero) buffer.
    #[test]
    fn pool_collect_pingpong_reuses_from_space() {
        let mut a = MemorySpace::new(4096, SpaceKind::Mutable);
        let mut b = MemorySpace::new(1024, SpaceKind::Mutable);
        let mut root = PolyWord::tagged(0);
        let mut prev_storage: Option<usize> = None;
        for round in 0..6 {
            let leaf = b.alloc(2);
            unsafe {
                set_length_word(leaf, 2, 0);
                leaf.write(PolyWord::tagged(round as isize));
                leaf.add(1).write(PolyWord::tagged(1000 + round as isize));
            }
            root = PolyWord::from_ptr(leaf.cast_const());
            let before = a.storage_ptr() as usize;
            collect_pool_with_workers_impl(&mut [&mut a, &mut b], None, None, |c| unsafe {
                c.forward(&mut root as *mut _);
            });
            // From round 2 on, the new to-space must BE round N-1's
            // from-space (the ping-pong pair established after round 1).
            if let Some(expect) = prev_storage {
                assert_eq!(
                    a.storage_ptr() as usize,
                    expect,
                    "round {round}: to-space is not the retired from-space                      (ping-pong reuse regressed)"
                );
            }
            assert!(a.spare.is_some(), "round {round}: from-space not stashed");
            prev_storage = Some(before);
            // Payload correct on the recycled (stale-content) buffer.
            let p = root.as_ptr::<PolyWord>();
            unsafe {
                assert_eq!((*p).0, PolyWord::tagged(round as isize).0);
                assert_eq!((*p.add(1)).0, PolyWord::tagged(1000 + round as isize).0);
            }
        }
    }

    /// Pool collections must NOT balloon the primary: to-space is sized
    /// max(primary capacity, Σ used), not Σ capacity — the original pool
    /// formula grew the primary by the children's total capacity on
    /// EVERY collection (unbounded RSS growth; +192 MB/cycle with six
    /// 32 MB nurseries).
    #[test]
    fn pool_collect_does_not_balloon_primary() {
        let mut a = MemorySpace::new(1024, SpaceKind::Mutable);
        let mut b = MemorySpace::new(1024, SpaceKind::Mutable);
        let cap0 = a.capacity_words();
        let mut root = PolyWord::tagged(0);
        for round in 0..5 {
            // A little live data in the child each round.
            let leaf = b.alloc(1);
            unsafe {
                set_length_word(leaf, 1, F_BYTE_OBJ);
                leaf.write(PolyWord::from_bits(0xbeef));
            }
            root = PolyWord::from_ptr(leaf.cast_const());
            // Pin the SERIAL path (workers = None): this test asserts the
            // serial Σ-used to-space sizing; the parallel path adds
            // bounded per-worker chunk slack by design, so a force-set
            // POLYML_PARALLEL_GC env must not leak in.
            collect_pool_with_workers_impl(&mut [&mut a, &mut b], None, None, |c| unsafe {
                c.forward(&mut root as *mut _);
            });
            assert_eq!(
                a.capacity_words(),
                cap0,
                "primary ballooned on pool collection round {round} \
                 (Σ-capacity to-space sizing regressed)"
            );
        }
    }

    /// P6 determinism floor: 1 worker (or None) takes the EXACT serial
    /// path — identical layout, identical used count.
    #[test]
    fn parallel_one_worker_is_exactly_serial() {
        let build = |space: &mut MemorySpace| {
            let leaf = space.alloc(1);
            unsafe {
                set_length_word(leaf, 1, F_BYTE_OBJ);
                leaf.write(PolyWord::from_bits(0xfeed));
            }
            let parent = space.alloc(2);
            unsafe {
                set_length_word(parent, 2, 0);
                parent.write(PolyWord::from_ptr(leaf.cast_const()));
                parent.add(1).write(PolyWord::tagged(9));
            }
            PolyWord::from_ptr(parent.cast_const())
        };
        let mut s1 = MemorySpace::new(64, SpaceKind::Mutable);
        let mut r1 = build(&mut s1);
        let u1 = collect_pool_with_workers(&mut [&mut s1], None, |c| unsafe {
            c.forward(&mut r1 as *mut _);
        });
        let mut s2 = MemorySpace::new(64, SpaceKind::Mutable);
        let mut r2 = build(&mut s2);
        let u2 = collect_pool_with_workers(&mut [&mut s2], Some(1), |c| unsafe {
            c.forward(&mut r2 as *mut _);
        });
        assert_eq!(u1, u2);
        // Layout identity: same word-index of the root object in to-space.
        let off1 = r1.0 - s1.as_ptr_range().start as usize;
        let off2 = r2.0 - s2.as_ptr_range().start as usize;
        assert_eq!(
            off1, off2,
            "Some(1) must take the byte-identical serial path"
        );
    }
}
