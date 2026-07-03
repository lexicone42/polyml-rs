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
    /// Addresses that fell in from-space but didn't match any tracked
    /// object — usually a pre-pass bug. Logged at end of collect.
    untracked_addrs: Vec<usize>,
    /// PARALLEL COLLECTION (P6): when `Some(n)`, the linear Cheney scan
    /// is replaced by an n-worker queue-driven scan, and the serial
    /// root-forwarding phase records every object it copies here (the
    /// workers' seed queue — to-space body addresses). `None` (default)
    /// = the exact pre-P6 serial path, byte-identical.
    par_workers: Option<usize>,
    /// Seed queue for the parallel scan (to-space body addresses copied
    /// during the serial roots phase). Unused when `par_workers` is None.
    par_seeds: Vec<usize>,
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
        // P6: the parallel scan is queue-driven — every object copied
        // during the (serial) roots phase seeds the workers.
        if self.par_workers.is_some() {
            self.par_seeds.push(to_ptr as usize);
        }
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

    /// Work-batch size: locals spill to the shared injector (and thieves
    /// take) in batches, so shared-lock traffic is per-BATCH, not
    /// per-object. A worker spills only when its local queue exceeds
    /// 2×BATCH — a chain-shaped graph (local queue depth ~1) never touches
    /// the injector at all and degrades to ~serial cost.
    const BATCH: usize = 256;

    /// Shared state of one parallel scan.
    pub(super) struct Shared<'a> {
        pub from_ranges: &'a [(usize, usize)],
        /// Object-start bitmap + per-range bit bases (see
        /// `Collector::find_body_start`) — read-only during the drain.
        start_bits: &'a [u64],
        range_bit_base: &'a [usize],
        base: SendBase,
        to_len: usize,
        /// Atomic bump cursor (word index into to-space).
        pub to_used: AtomicUsize,
        /// Objects pushed-but-not-fully-scanned. A worker decrements only
        /// AFTER scanning an object (its children already pushed), so
        /// `pending == 0` really means "no work anywhere".
        pending: AtomicUsize,
        /// Shared injector of work BATCHES (to-space body addresses).
        /// Workers keep an owner-local lock-free Vec and only exchange
        /// batches here.
        injector: Mutex<Vec<Vec<usize>>>,
        /// From-space pointers matching no tracked object (collector-bug
        /// canary, merged into `Collector::untracked_addrs` after the drain).
        pub untracked: Mutex<Vec<usize>>,
    }

    impl<'a> Shared<'a> {
        pub fn new(
            from_ranges: &'a [(usize, usize)],
            start_bits: &'a [u64],
            range_bit_base: &'a [usize],
            to_storage: &mut [PolyWord],
            to_used: usize,
            seeds: &[usize],
            workers: usize,
        ) -> Self {
            // Split the seeds into ~worker-count batches so everyone can
            // start immediately.
            let chunk = seeds.len().div_ceil(workers).max(1);
            let batches: Vec<Vec<usize>> = seeds.chunks(chunk).map(<[usize]>::to_vec).collect();
            Self {
                from_ranges,
                start_bits,
                range_bit_base,
                base: SendBase(to_storage.as_mut_ptr()),
                to_len: to_storage.len(),
                to_used: AtomicUsize::new(to_used),
                pending: AtomicUsize::new(seeds.len()),
                injector: Mutex::new(batches),
                untracked: Mutex::new(Vec::new()),
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

        /// Atomically reserve `1 + n_words` in to-space; returns the body
        /// pointer. The assert mirrors `bump_to` (Σ-capacity can never
        /// overflow because the claim CAS guarantees one copy per object).
        fn bump(&self, n_words: usize) -> *mut PolyWord {
            let len_idx = self.to_used.fetch_add(1 + n_words, Ordering::Relaxed);
            let new_used = len_idx + 1 + n_words;
            assert!(
                new_used <= self.to_len,
                "GC to-space overflow (parallel): requested {n_words}, at {len_idx}/{}",
                self.to_len
            );
            // SAFETY: reserved region is exclusively ours per the fetch_add.
            unsafe { self.base.0.add(len_idx + 1) }
        }

        /// Push newly-copied work: owner-local (lock-free); spill a batch
        /// to the shared injector when the local queue grows past 2×BATCH.
        fn push_work(&self, local: &mut Vec<usize>, body: usize) {
            self.pending.fetch_add(1, Ordering::Relaxed);
            local.push(body);
            // Share half once we clearly have surplus. A chain-shaped graph
            // keeps the local depth ~1 and never pays the injector lock; a
            // wide graph spills early so idle peers get fed.
            if local.len() > BATCH {
                let spill = local.split_off(local.len() / 2);
                self.injector.lock().unwrap().push(spill);
            }
        }

        /// Parallel forward of one object known to start at `body_start`:
        /// claim via header CAS, copy, publish. Returns the to-space body.
        ///
        /// # Safety
        /// `body_start` must be the body address of a well-formed
        /// from-space object (came from `find_object`).
        unsafe fn forward_object(&self, body_start: usize, local: &mut Vec<usize>) -> usize {
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
                    Err(cur) => lw_bits = cur,
                }
            }
            // We hold the claim; lw_bits is the original length word.
            let lw = PolyWord::from_bits(lw_bits);
            let n_words = length_of(lw);
            let flags = flags_of(lw);
            let to_ptr = self.bump(n_words);
            let new_lw = length_word::make_length_word(n_words, flags);
            // SAFETY: to_ptr-1..to_ptr+n_words is our exclusive reservation;
            // the source body is frozen (all mutators parked, we hold the claim).
            unsafe {
                to_ptr.sub(1).write(new_lw);
                std::ptr::copy_nonoverlapping(body_start as *const PolyWord, to_ptr, n_words);
            }
            // Publish: Release makes the copied body visible to any reader
            // that Acquire-loads this tombstone.
            header.store((to_ptr as usize) | BUSY, Ordering::Release);
            // Exactly-once push: we won the claim, so we are the sole pusher.
            self.push_work(local, to_ptr as usize);
            to_ptr as usize
        }

        /// Parallel mirror of `Collector::forward_impl` for one slot.
        ///
        /// # Safety
        /// `slot` must be a valid, writable pointer to a PolyWord in a
        /// to-space object owned (being scanned) by this worker.
        unsafe fn forward_slot(&self, slot: *mut PolyWord, local: &mut Vec<usize>) {
            let w = unsafe { *slot };
            if w.is_tagged() {
                return;
            }
            let addr = w.0;
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
            let new_body = unsafe { self.forward_object(body_start, local) };
            let offset_bytes = addr.wrapping_sub(body_start);
            unsafe { slot.write(PolyWord::from_bits(new_body.wrapping_add(offset_bytes))) };
        }

        /// Scan one to-space object — the parallel mirror of
        /// `Collector::scan_object` (same shape rules; keep in sync).
        ///
        /// # Safety
        /// `body` must be a fully-copied to-space object body address that
        /// this worker popped from a queue (sole scanner).
        unsafe fn scan_object(&self, body: usize, local: &mut Vec<usize>) {
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
                        unsafe { self.forward_slot(cp_mut.add(i), local) };
                    }
                }
                F_CLOSURE_OBJ => {
                    for i in 0..n_words {
                        unsafe { self.forward_slot(obj_ptr.add(i), local) };
                    }
                }
                _ => {
                    for i in 0..n_words {
                        unsafe { self.forward_slot(obj_ptr.add(i), local) };
                    }
                }
            }
        }

        /// One worker's drain loop: pop the owner-local queue (lock-free),
        /// refill from the shared batch injector when dry, back off (spin
        /// then yield) when the injector is empty too, exit on quiescence.
        pub(super) fn drain(&self) {
            let mut local: Vec<usize> = Vec::with_capacity(4 * BATCH);
            let mut idle_spins = 0u32;
            loop {
                if let Some(body) = local.pop() {
                    idle_spins = 0;
                    // SAFETY: popped exactly once; copy completed before the
                    // push (copier program order / Mutex batch transfer).
                    unsafe { self.scan_object(body, &mut local) };
                    // Decrement AFTER the scan (children already pushed), so
                    // pending==0 is a true quiescence signal.
                    self.pending.fetch_sub(1, Ordering::Release);
                    continue;
                }
                // Local dry: grab a whole batch from the injector.
                if let Some(batch) = self.injector.lock().unwrap().pop() {
                    idle_spins = 0;
                    local = batch;
                    continue;
                }
                if self.pending.load(Ordering::Acquire) == 0 {
                    return;
                }
                // Idle backoff, three tiers: spin (latency) → yield → SLEEP.
                // An idle worker must not burn CPU while a peer chases a
                // long chain — the first cut measured 2.3× SLOWDOWN from
                // exactly this (spinners at full burn); yield-only still
                // cost ~14s of sys-time context-switch churn. The 100µs
                // sleep caps wake-latency at a negligible fraction of any
                // collection big enough to matter.
                idle_spins += 1;
                if idle_spins < 64 {
                    std::hint::spin_loop();
                } else if idle_spins < 80 {
                    std::thread::yield_now();
                } else {
                    std::thread::sleep(std::time::Duration::from_micros(100));
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
    let scratch_raw: Box<[usize]> = vec![0usize; total_capacity].into_boxed_slice();
    let mut scratch: Box<[PolyWord]> =
        // SAFETY: PolyWord is repr(transparent) over usize (same layout,
        // any bit pattern valid); Box<[usize]> and Box<[PolyWord]> are
        // interchangeable.
        unsafe { Box::from_raw(Box::into_raw(scratch_raw) as *mut [PolyWord]) };

    let t_scratch = t0.elapsed();

    // Worker count None/0/1 = the exact serial path.
    let par_workers = par_workers.filter(|&n| n >= 2);

    let mut col = Collector {
        from_ranges,
        to_storage: &mut scratch,
        to_used: 0,
        start_bits,
        range_bit_base,
        untracked_addrs: Vec::new(),
        par_workers,
        par_seeds: Vec::new(),
    };

    visit_roots(&mut col);
    let t_roots = t0.elapsed();
    if let Some(workers) = col.par_workers {
        // P6 parallel queue-driven drain (docs/parallel-design.md § P6).
        // The roots phase above ran serially and seeded `par_seeds`.
        let shared = par::Shared::new(
            &col.from_ranges,
            &col.start_bits,
            &col.range_bit_base,
            col.to_storage,
            col.to_used,
            &col.par_seeds,
            workers,
        );
        std::thread::scope(|s| {
            for _ in 1..workers {
                let sh = &shared;
                s.spawn(move || sh.drain());
            }
            shared.drain();
        });
        col.to_used = shared.to_used.load(std::sync::atomic::Ordering::Acquire);
        col.untracked_addrs
            .extend(shared.untracked.lock().unwrap().iter().copied());
    } else {
        // SAFETY: collector invariants upheld.
        unsafe { col.cheney_scan() };
    }
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
    spaces[0].replace_storage(scratch, new_used);
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
        assert_eq!(
            new_used, expected_live,
            "live word count must be EXACT — a duplicate copy (claim race) \
             or a dropped object (lost work) shows here"
        );

        // Sharing preserved: every parent sees the SAME forwarded leaves.
        let p0 = parents[0].as_ptr::<PolyWord>();
        let (l1, l2, ch) = unsafe { ((*p0).0, (*p0.add(1)).0, (*p0.add(2)).0) };
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
            collect_pool(&mut [&mut a, &mut b], |c| unsafe {
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
