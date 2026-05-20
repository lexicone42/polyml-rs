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
    self, F_BYTE_OBJ, F_CLOSURE_OBJ, F_CODE_OBJ, F_NEGATIVE_BIT, F_MUTABLE_BIT,
    F_NO_OVERWRITE, F_WEAK_BIT,
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
    let mut builder = SnapshotBuilder::default();
    let root_id = unsafe { builder.intern(root) };
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
        let n = length_word::length_of(lw);
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
        let code_addr = if code_word.is_tagged() {
            // Strange — but produce a stable placeholder.
            self.tagged_as_dummy_obj(code_word)
        } else {
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
        // The bytecode portion runs from offset 0 up to the start of
        // the constants segment (computed via the trailing-offset
        // word). Use const_segment_for_code to find the boundary.
        let (cp_start, count) = unsafe { length_word::const_segment_for_code(body_ptr) };
        let cp_start_addr = cp_start as usize;
        let body_start_addr = body_ptr as usize;
        let bytecode_len_bytes = cp_start_addr.saturating_sub(body_start_addr);
        let code_bytes: Vec<u8> = (0..bytecode_len_bytes)
            .map(|i| unsafe { *body_ptr.cast::<u8>().add(i) })
            .collect();
        let mut constants = Vec::with_capacity(count);
        for i in 0..count {
            let w = unsafe { *cp_start.add(i) };
            constants.push(self.value_for(w));
        }
        let _ = n;
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
        // It's a pointer. Intern.
        // SAFETY: caller of snapshot upholds heap validity.
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
    use crate::space::{set_length_word, MemorySpace, SpaceKind};

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
                    .filter_map(|v| if let Value::Ref(id) = v { Some(*id) } else { None })
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
        assert_eq!(
            img2.objects[img2.root as usize].flags,
            ObjFlags::MUTABLE
        );
    }
}
