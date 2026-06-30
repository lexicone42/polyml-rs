//! Heap → pexport `Image` snapshot.
//!
//! Walks every object reachable from a set of roots (typically just
//! the `PolyML.rootFunction` closure passed to `PolyML.export`) and
//! produces a [`polyml_image::pexport::Image`] that can then be
//! [written][polyml_image::pexport::Image::write] back to disk in the
//! same text format the loader reads.
//!
//! Object IDs are assigned in BFS order from the root, so the root's
//! ID is 0. This matches no specific upstream convention but
//! parses+roundtrips cleanly.
//!
//! ## Pointer interpretation
//!
//! Each `PolyWord` is either:
//! - **Tagged** (LSB = 1): an immediate integer, encoded as
//!   `Value::Tagged(untag)`.
//! - **A real heap pointer** (LSB = 0): treated as a pointer to
//!   another object's body. We follow it, assign that object an ID
//!   if new, and encode as `Value::Ref(id)`.
//!
//! ## Limitations
//!
//! - Mid-object byte pointers (PC values pushed on the stack) aren't
//!   relevant here because exported objects are tree-shaped data, not
//!   the interpreter's execution state.
//! - Code objects with native-architecture relocations would need a
//!   relocation walker; the interpreted-mode bootstrap image uses no
//!   in-code-byte relocs, so we emit an empty reloc list.
//! - Weak refs become `WeakRef` body markers; their pointed targets
//!   are deliberately *not* followed (matching upstream behaviour).

use crate::length_word::{
    self, F_BYTE_OBJ, F_CLOSURE_OBJ, F_CODE_OBJ, F_MUTABLE_BIT, F_NEGATIVE_BIT, F_NO_OVERWRITE,
    F_WEAK_BIT,
};
use crate::poly_word::PolyWord;
use polyml_image::pexport::{
    Image, ObjFlags, Object, ObjectBody, ObjectId, SourceArch, Value, WordSize,
};
use std::collections::HashMap;

/// Build an [`Image`] snapshot of everything reachable from `root`.
///
/// # Safety
/// `root` must be a valid heap pointer (PolyWord with LSB=0 pointing
/// at an object body whose preceding header word is well-formed). The
/// underlying memory must stay valid for the duration of the call.
#[must_use]
pub unsafe fn snapshot(root: PolyWord) -> Image {
    // Trusted call site: no space validation (byte-identical to before).
    unsafe { snapshot_gated(root, None) }
}

/// Build an [`Image`] snapshot, optionally gating EVERY pointer-follow on a
/// live-space membership test (task #96, HOLE 6 / SURFACE 6).
///
/// The export path (`PolyExport` / `PolyExportPortable`, reachable from
/// untrusted bytecode via `CALL_FULL_RTS3`) walks the object graph reachable
/// from `root`, dereferencing `*body_ptr.sub(1)` for the root AND every child
/// pointer it interns. A wild / type-confused `root` or field would SEGV
/// during that walk. When `spaces` is `Some`, a pointer that is not a live
/// space member is NOT interned/walked — it is emitted as a safe placeholder
/// (`Value::Tagged(0)`), so the walk only ever derefs space-validated
/// addresses. `None` (trusted) is byte-identical to the legacy walk.
///
/// # Safety
/// `root` must be a tagged value or a valid heap pointer; in untrusted mode
/// (`spaces == Some`) an out-of-space `root` yields an empty image instead of
/// a deref. The underlying memory must stay valid for the call.
#[must_use]
pub unsafe fn snapshot_gated(root: PolyWord, spaces: Option<crate::rts::RtsSafeSpaces>) -> Image {
    let mut builder = SnapshotBuilder {
        spaces,
        ..SnapshotBuilder::default()
    };
    // Validate the root before interning: an out-of-space root must not enter
    // the work queue (else drain would deref its length word).
    let root_id = if root.is_tagged() || builder.ptr_ok(root) {
        unsafe { builder.intern(root) }
    } else {
        // Out-of-space root: emit a single empty placeholder object as root.
        builder.objects.push(placeholder());
        0
    };
    unsafe { builder.drain() };
    Image {
        root: root_id,
        arch: SourceArch::Interpreted,
        word_size: WordSize::Bits64,
        objects: builder.objects,
    }
}

#[derive(Default)]
struct SnapshotBuilder {
    /// Maps an object's body address to its assigned ID. We use the
    /// raw address as the key — two heap pointers point to the "same"
    /// object iff their addresses match.
    by_addr: HashMap<usize, ObjectId>,
    /// Built objects, indexed by ID.
    objects: Vec<Object>,
    /// Queue of object addresses whose bodies still need walking.
    /// We pop until empty.
    pending: Vec<usize>,
    /// UNTRUSTED MODE (task #96, SURFACE 6): the live image+alloc spaces. When
    /// `Some`, every pointer is checked for space-membership before it is
    /// interned/walked, so the graph walk never derefs a wild/type-confused
    /// pointer. `None` (trusted) -> no check, byte-identical.
    spaces: Option<crate::rts::RtsSafeSpaces>,
}

impl SnapshotBuilder {
    /// Whether following `w` as a heap pointer is safe in the current mode:
    /// trusted (`spaces == None`) -> always (the legacy behaviour);
    /// untrusted (`spaces == Some`) -> only when `w` is a live-space member
    /// with header room. Caller has already excluded tagged values.
    #[inline]
    fn ptr_ok(&self, w: PolyWord) -> bool {
        self.spaces
            .as_ref()
            .is_none_or(|s| w.is_data_ptr() && s.contains_with_header(w.as_ptr::<PolyWord>()))
    }
}

impl SnapshotBuilder {
    /// Look up `w` in the interning table and return its ID. If new,
    /// assign an ID and enqueue for body walking.
    ///
    /// # Safety
    /// `w` must be a tagged value or a valid heap pointer.
    unsafe fn intern(&mut self, w: PolyWord) -> ObjectId {
        debug_assert!(!w.is_tagged(), "intern called on tagged value");
        let addr = w.0;
        if let Some(&id) = self.by_addr.get(&addr) {
            return id;
        }
        let id = self.objects.len() as ObjectId;
        self.by_addr.insert(addr, id);
        // Reserve a slot — we'll fill the body in drain().
        self.objects.push(placeholder());
        self.pending.push(addr);
        id
    }

    /// Drain the work queue, populating each pending object.
    unsafe fn drain(&mut self) {
        while let Some(addr) = self.pending.pop() {
            let id = *self.by_addr.get(&addr).expect("pending without id");
            let body_ptr = addr as *const PolyWord;
            let lw = unsafe { *body_ptr.sub(1) };
            self.objects[id as usize] = unsafe { self.build_object(body_ptr, lw) };
        }
    }

    unsafe fn build_object(&mut self, body_ptr: *const PolyWord, lw: PolyWord) -> Object {
        // HEADER SANITY (task #96, SURFACE 6): the length word is image
        // controlled. In untrusted mode clamp the object's word count to what
        // fits its containing space, so a forged oversized header cannot drive
        // build_code/build_ordinary to read past the space end (a SEGV).
        // Trusted mode (spaces None) uses `n` verbatim — byte-identical.
        let n = {
            let raw_n = length_word::length_of(lw);
            self.spaces
                .as_ref()
                .and_then(|s| s.space_end_of(body_ptr))
                .map_or(raw_n, |end| {
                    let avail =
                        end.saturating_sub(body_ptr as usize) / std::mem::size_of::<usize>();
                    raw_n.min(avail)
                })
        };
        let raw_flags = length_word::flags_of(lw);
        let ty = length_word::type_of(lw);
        let mut flags = ObjFlags::default();
        if raw_flags & F_MUTABLE_BIT != 0 {
            flags |= ObjFlags::MUTABLE;
        }
        if raw_flags & F_NEGATIVE_BIT != 0 {
            flags |= ObjFlags::NEGATIVE;
        }
        if raw_flags & F_NO_OVERWRITE != 0 {
            flags |= ObjFlags::NO_OVERWRITE;
        }
        if raw_flags & F_WEAK_BIT != 0 {
            flags |= ObjFlags::WEAK;
        }
        let body = match ty {
            F_BYTE_OBJ => {
                let n_bytes = n * std::mem::size_of::<usize>();
                let bytes: Vec<u8> = (0..n_bytes)
                    .map(|i| unsafe { *body_ptr.cast::<u8>().add(i) })
                    .collect();
                // Heuristic: a string object's first word is the byte
                // length (a tagged int); the remaining bytes are the
                // chars. Upstream distinguishes them by checking that
                // the declared length fits within the alloc-rounded
                // size. For now, emit as Bytes — the runtime treats
                // both `S` and `B` identically when re-loading byte
                // segments, and roundtripping doesn't depend on the
                // distinction.
                ObjectBody::Bytes(bytes)
            }
            F_CODE_OBJ => self.build_code(body_ptr, n),
            F_CLOSURE_OBJ => unsafe { self.build_closure(body_ptr, n) },
            _ => unsafe { self.build_ordinary(body_ptr, n) },
        };
        Object { flags, body }
    }

    unsafe fn build_ordinary(&mut self, body_ptr: *const PolyWord, n: usize) -> ObjectBody {
        let mut values = Vec::with_capacity(n);
        for i in 0..n {
            let w = unsafe { *body_ptr.add(i) };
            values.push(self.value_for(w));
        }
        ObjectBody::Ordinary(values)
    }

    unsafe fn build_closure(&mut self, body_ptr: *const PolyWord, n: usize) -> ObjectBody {
        // Word 0 is a raw code-object pointer; remaining words are
        // captured ML values.
        let code_word = unsafe { *body_ptr };
        let code_addr = if code_word.is_tagged() || !self.ptr_ok(code_word) {
            // Tagged (strange) OR — UNTRUSTED MODE (SURFACE 6) — an
            // out-of-space code pointer: produce a stable placeholder rather
            // than interning + later dereferencing a wild code-object pointer.
            self.tagged_as_dummy_obj(code_word)
        } else {
            // SAFETY: code_word space-validated by ptr_ok (untrusted) /
            // trusted caller upholds validity.
            unsafe { self.intern(code_word) }
        };
        let mut values = Vec::with_capacity(n.saturating_sub(1));
        for i in 1..n {
            let w = unsafe { *body_ptr.add(i) };
            values.push(self.value_for(w));
        }
        ObjectBody::Closure { code_addr, values }
    }

    fn tagged_as_dummy_obj(&mut self, _w: PolyWord) -> ObjectId {
        // Shouldn't normally happen — closures always have a code
        // pointer in slot 0. If it does, return ID 0 (the root); the
        // emitted image will be inspectable but execution would be
        // undefined.
        0
    }

    fn build_code(&mut self, body_ptr: *const PolyWord, n: usize) -> ObjectBody {
        // PolyML code-object layout:
        //   [0 .. endIC)     bytecode bytes
        //   [endIC]          count word (one PolyWord)
        //   [endIC + 8 ..]   constants
        //   [last word]      trailing signed-byte offset back to const segment
        //
        // `const_segment_for_code` returns the address of the first
        // constant (cp), so the count word lives at `cp - 8` and the
        // actual bytecode ends at `cp - 8`. We need to subtract that
        // single PolyWord so the snapshot doesn't include the count
        // word as if it were bytecode.
        let word_bytes = std::mem::size_of::<usize>();
        let body_start_addr = body_ptr as usize;
        let (cp_start, count) = if self.spaces.is_some() {
            // UNTRUSTED MODE (task #96, SURFACE 6): `const_segment_for_code`
            // derefs the trailing-offset word at body[n-1] AND the count word
            // at cp[-1] for an attacker-controlled `cp` — two unguarded reads
            // (the residual the cold export_corrupt_code_oob_repro probe
            // documents). Compute (cp, count) inline with bounds: `n` is the
            // SPACE-CLAMPED word count, so body[n-1] is in-space; `cp` is
            // derived from the (forged-allowed) trailing offset by INTEGER
            // arithmetic and only the count word is read AFTER confirming cp[-1]
            // lies inside the object body. A wild cp yields count 0.
            let obj_end = body_start_addr + n.saturating_mul(word_bytes);
            if n < 2 {
                (body_ptr, 0usize)
            } else {
                // SAFETY: n >= 2 and n is space-clamped, so body[n-1] is a
                // readable in-space word.
                let last_word_ptr = unsafe { body_ptr.add(n - 1) };
                #[allow(clippy::cast_possible_wrap)]
                let offset_bytes = unsafe { (*last_word_ptr).0 } as isize;
                #[allow(clippy::cast_possible_wrap)]
                let wb = word_bytes as isize;
                // cp = last_word_ptr + 1 + offset_bytes/word_bytes (integer
                // arithmetic, never a wild pointer `.offset`).
                #[allow(clippy::cast_sign_loss)]
                let off_term = (offset_bytes / wb).wrapping_mul(wb) as usize;
                let cp_addr = (last_word_ptr as usize)
                    .wrapping_add(word_bytes)
                    .wrapping_add(off_term);
                // The count word is at cp-1; it must lie inside the object body
                // (>= body_start + 1 word so cp-1 is a body slot, < obj_end).
                if cp_addr > body_start_addr && cp_addr <= obj_end {
                    // SAFETY: cp-1 is in [body_start, obj_end) ⊆ the in-space body.
                    let cnt = unsafe { *((cp_addr - word_bytes) as *const PolyWord) }.0;
                    (cp_addr as *const PolyWord, cnt)
                } else {
                    (body_ptr, 0usize)
                }
            }
        } else {
            // Trusted: byte-identical to the legacy walk.
            unsafe { length_word::const_segment_for_code(body_ptr) }
        };
        let cp_start_addr = cp_start as usize;
        // The whole object body spans [body_start_addr, obj_end_addr). The
        // const-segment pointer and count come from `const_segment_for_code`,
        // which reads the object's own (loader-written) trailing-offset and
        // count words and applies only DEBUG-time sanity guards (no release
        // bounds check, by design). On a self-built heap those words are
        // consistent and `cp_start..cp_start+count` lies inside the body. But
        // a corrupted / type-confused code object (the lf_ref_52 / task #96
        // untrusted-input class) can drive `cp_start` and `count` to arbitrary
        // values, turning the `0..count` loop below into an unbounded OOB read
        // (and, via `value_for`, a recursive wild-pointer walk). Export is a
        // cold, one-shot path, so we clamp both against the object's own length
        // word `n` here — keeping the read provably in-bounds regardless of the
        // trailer's contents. See tests/export_corrupt_code_oob_repro.rs.
        let obj_end_addr = body_start_addr + n.saturating_mul(word_bytes);
        let bytecode_len_bytes = cp_start_addr
            .min(obj_end_addr) // clamp a wild (too-high) cp into the body
            .saturating_sub(body_start_addr)
            .saturating_sub(word_bytes);
        let code_bytes: Vec<u8> = (0..bytecode_len_bytes)
            .map(|i| unsafe { *body_ptr.cast::<u8>().add(i) })
            .collect();
        // A valid const segment starts inside the body and ends at or before
        // the trailing-offset word (the LAST body word, `body[n-1]`); the const
        // region is `[cp, cp+count)` with `cp+count == &body[n-1]` (loader.rs:
        // 372-374, mirroring upstream machine_dep.h:61-67). If `cp_start` is out
        // of range (below body, or at/after the trailing word), no constant can
        // be safely read. Otherwise cap `count` to the whole words that fit
        // between `cp_start` and the trailing word — never reading the offset
        // word itself nor past the object body.
        let consts_end_addr = obj_end_addr.saturating_sub(word_bytes); // &body[n-1]
        let safe_count = if cp_start_addr >= body_start_addr && cp_start_addr < consts_end_addr {
            let avail_words = (consts_end_addr - cp_start_addr) / word_bytes;
            count.min(avail_words)
        } else {
            0
        };
        let mut constants = Vec::with_capacity(safe_count);
        for i in 0..safe_count {
            // SAFETY: i < safe_count <= (obj_end - cp_start)/word_bytes, so
            // cp_start.add(i) lies within [cp_start, obj_end) ⊆ the object body.
            let w = unsafe { *cp_start.add(i) };
            constants.push(self.value_for(w));
        }
        ObjectBody::Code {
            code_bytes,
            constants,
            relocs: Vec::new(),
        }
    }

    /// Convert a `PolyWord` body slot to a pexport `Value`. Tagged
    /// values become `Value::Tagged`; pointers become `Value::Ref` by
    /// interning the pointed object.
    fn value_for(&mut self, w: PolyWord) -> Value {
        if w.is_tagged() {
            return Value::Tagged(w.untag() as i64);
        }
        // It's a pointer. UNTRUSTED MODE (SURFACE 6): only intern (and thus
        // later deref via drain) a pointer that is a live-space member; a
        // wild/type-confused field becomes a safe placeholder so the graph
        // walk never follows it. Trusted mode (spaces None) interns everything
        // — byte-identical.
        if !self.ptr_ok(w) {
            return Value::Tagged(0);
        }
        // SAFETY: caller of snapshot upholds heap validity (trusted) OR `w`
        // was just space-validated by ptr_ok (untrusted).
        let id = unsafe { self.intern(w) };
        Value::Ref(id)
    }
}

fn placeholder() -> Object {
    Object {
        flags: ObjFlags::default(),
        body: ObjectBody::Ordinary(Vec::new()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::space::{MemorySpace, SpaceKind, set_length_word};

    #[test]
    fn snapshot_single_word_object() {
        let mut space = MemorySpace::new(16, SpaceKind::Mutable);
        // Allocate a 2-word object: [Tagged(7), Tagged(9)].
        let p = space.alloc(2);
        unsafe {
            set_length_word(p, 2, 0);
            p.write(PolyWord::tagged(7));
            p.add(1).write(PolyWord::tagged(9));
        }
        let root = PolyWord::from_ptr(p.cast_const());
        let img = unsafe { snapshot(root) };
        assert_eq!(img.objects.len(), 1);
        assert_eq!(img.root, 0);
        match &img.objects[0].body {
            ObjectBody::Ordinary(values) => {
                assert_eq!(values, &[Value::Tagged(7), Value::Tagged(9)]);
            }
            other => panic!("expected Ordinary, got {other:?}"),
        }
    }

    #[test]
    fn snapshot_shared_subtree_interned_once() {
        let mut space = MemorySpace::new(32, SpaceKind::Mutable);
        // Allocate a "leaf" first.
        let leaf = space.alloc(1);
        unsafe {
            set_length_word(leaf, 1, 0);
            leaf.write(PolyWord::tagged(42));
        }
        // Parent points twice to the same leaf.
        let parent = space.alloc(2);
        unsafe {
            set_length_word(parent, 2, 0);
            parent.write(PolyWord::from_ptr(leaf.cast_const()));
            parent.add(1).write(PolyWord::from_ptr(leaf.cast_const()));
        }
        let img = unsafe { snapshot(PolyWord::from_ptr(parent.cast_const())) };
        // Parent + leaf = 2 objects only (leaf interned once).
        assert_eq!(img.objects.len(), 2);
        // Parent should reference the same id twice.
        match &img.objects[0].body {
            ObjectBody::Ordinary(values) => {
                let ids: Vec<_> = values
                    .iter()
                    .filter_map(|v| {
                        if let Value::Ref(id) = v {
                            Some(*id)
                        } else {
                            None
                        }
                    })
                    .collect();
                assert_eq!(ids.len(), 2);
                assert_eq!(ids[0], ids[1]);
            }
            other => panic!("expected Ordinary, got {other:?}"),
        }
    }

    #[test]
    fn snapshot_round_trips_through_pexport_text() {
        let mut space = MemorySpace::new(64, SpaceKind::Mutable);
        let leaf = space.alloc(1);
        unsafe {
            set_length_word(leaf, 1, 0);
            leaf.write(PolyWord::tagged(100));
        }
        let parent = space.alloc(2);
        unsafe {
            set_length_word(parent, 2, F_MUTABLE_BIT);
            parent.write(PolyWord::from_ptr(leaf.cast_const()));
            parent.add(1).write(PolyWord::tagged(-1));
        }
        let img = unsafe { snapshot(PolyWord::from_ptr(parent.cast_const())) };
        let mut buf = Vec::new();
        img.write(&mut buf).unwrap();
        let img2 = polyml_image::pexport::Image::parse(&buf).unwrap();
        assert_eq!(img2.objects.len(), img.objects.len());
        assert_eq!(img2.root, img.root);
        // Parent is the root and is mutable.
        assert_eq!(img2.objects[img2.root as usize].flags, ObjFlags::MUTABLE);
    }
}
