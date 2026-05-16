//! Convert a parsed [`polyml_image::pexport::Image`] into in-memory
//! `MemorySpace`s with proper length words, packed bytes, and resolved
//! object references.
//!
//! Layout strategy:
//!
//! - Mutable objects → `mutable` space
//! - Code objects    → `code` space
//! - Everything else → `immutable` space
//!
//! This mirrors `vendor/polyml/libpolyml/pexport.cpp:PImport`'s choice
//! of which `SpaceAlloc` to draw from based on the assembled flag bits
//! (`pexport.cpp:640-651`).
//!
//! Algorithm: two passes.
//!
//! 1. **Pass 1** — for every object, compute its size in words and
//!    `MemorySpace::alloc` a slot of that size in the destination space.
//!    Record the resulting object pointer in `pointers[id]`.
//!
//! 2. **Pass 2** — write the length word and the object body. Body
//!    words that are `Value::Ref(id)` become `PolyWord::from_ptr(pointers[id])`;
//!    `Value::Tagged(n)` become `PolyWord::tagged(n)`.

use std::mem::size_of;

use polyml_image::pexport::{Image, Object, ObjectBody, Value};
use thiserror::Error;

use crate::length_word::{
    self, F_BYTE_OBJ, F_CLOSURE_OBJ, F_CODE_OBJ, F_MUTABLE_BIT, F_NEGATIVE_BIT, F_NO_OVERWRITE,
    F_WEAK_BIT,
};
use crate::poly_word::{PolyWord, MAX_TAGGED, MIN_TAGGED};
use crate::space::{MemorySpace, SpaceKind};

/// The output of [`load_image`]: three populated spaces plus a pointer
/// to the root object.
pub struct LoadedImage {
    pub immutable: MemorySpace,
    pub mutable: MemorySpace,
    pub code: MemorySpace,
    /// Pointer to the root object (typically a closure containing the
    /// top-level function to invoke).
    pub root: *const PolyWord,
}

// Pointers into the loaded heap are necessarily raw — both Send and
// Sync are safe for inspection purposes; the loader and downstream
// runtime synchronise around them explicitly.
unsafe impl Send for LoadedImage {}
unsafe impl Sync for LoadedImage {}

#[derive(Debug, Error)]
pub enum LoadError {
    #[error("root index {root} out of bounds (image has {count} objects)")]
    BadRoot { root: u32, count: usize },
    #[error(
        "tagged integer {value} out of range for native word size \
         (must be in [{MIN_TAGGED}, {MAX_TAGGED}])"
    )]
    TaggedOutOfRange { value: i64 },
    #[error("reference to object {id} which has no allocation")]
    UnresolvedRef { id: u32 },
}

/// Compute the number of body words an object of the given variant
/// will occupy in the heap.
///
/// Mirrors the C++ importer at `pexport.cpp:582-634` exactly. Sizes
/// differ from `Image` payload lengths because of byte-to-word rounding
/// and the fixed-size headers on strings, code objects, and entry
/// points.
fn body_word_count(body: &ObjectBody) -> usize {
    match body {
        ObjectBody::Ordinary(vs) => vs.len(),

        // Closure = 1 word for code address + N captured values.
        // We normalise the legacy form to the same shape.
        ObjectBody::Closure { values, .. } => 1 + values.len(),
        ObjectBody::LegacyClosure { values } => values.len(),

        // String: 1 length-prefix word + ceil(N/8) data words.
        ObjectBody::String(b) => 1 + b.len().div_ceil(size_of::<usize>()),

        // Bytes: ceil(N/8) data words. No prefix.
        ObjectBody::Bytes(b) => b.len().div_ceil(size_of::<usize>()),

        // Code: ceil(code_bytes/8) code words + N const words + 2
        // (constant-count + trailing offset). See pexport.cpp:601-609.
        ObjectBody::Code {
            code_bytes,
            constants,
            ..
        } => code_bytes.len().div_ceil(size_of::<usize>()) + constants.len() + 2,

        // Entry point: ceil((name + sizeof(uintptr_t) + sizeof(usize)) / 8).
        // The leading uintptr_t is reserved for the resolved address;
        // the name is NUL-terminated. See pexport.cpp:627-633.
        ObjectBody::EntryPoint(name) => {
            (name.len() + size_of::<usize>() + size_of::<usize>()) / size_of::<usize>()
        }

        // Weak ref: just one uintptr_t worth.
        ObjectBody::WeakRef => 1,
    }
}

/// Decide which space the object lands in, and compute its complete
/// length-word flag byte.
fn classify(obj: &Object) -> (SpaceKind, u8) {
    let mut flags: u8 = 0;
    // Modifier flags carry over directly.
    if obj.flags.contains(polyml_image::pexport::ObjFlags::MUTABLE) {
        flags |= F_MUTABLE_BIT;
    }
    if obj.flags.contains(polyml_image::pexport::ObjFlags::NEGATIVE) {
        flags |= F_NEGATIVE_BIT;
    }
    if obj.flags.contains(polyml_image::pexport::ObjFlags::WEAK) {
        flags |= F_WEAK_BIT;
    }
    if obj.flags.contains(polyml_image::pexport::ObjFlags::NO_OVERWRITE) {
        flags |= F_NO_OVERWRITE;
    }
    // Type bits.
    match &obj.body {
        ObjectBody::String(_)
        | ObjectBody::Bytes(_)
        | ObjectBody::EntryPoint(_)
        | ObjectBody::WeakRef => flags |= F_BYTE_OBJ,
        ObjectBody::Code { .. } => flags |= F_CODE_OBJ,
        ObjectBody::Closure { .. } | ObjectBody::LegacyClosure { .. } => flags |= F_CLOSURE_OBJ,
        ObjectBody::Ordinary(_) => {} // 0 = word object
    }
    let kind = if flags & F_MUTABLE_BIT != 0 {
        SpaceKind::Mutable
    } else if length_word::F_CODE_OBJ == flags & 0x03 {
        SpaceKind::Code
    } else {
        SpaceKind::Immutable
    };
    (kind, flags)
}

/// Estimate per-space capacities so we can pre-size each `MemorySpace`.
/// Adds one length-word slot per object plus the body.
fn estimate_capacities(image: &Image) -> (usize, usize, usize) {
    let (mut imm, mut mutc, mut code) = (0_usize, 0_usize, 0_usize);
    for obj in &image.objects {
        let (kind, _) = classify(obj);
        let words = body_word_count(&obj.body) + 1; // +1 for length-word slot
        match kind {
            SpaceKind::Immutable => imm += words,
            SpaceKind::Mutable => mutc += words,
            SpaceKind::Code => code += words,
        }
    }
    (imm, mutc, code)
}

/// Convert a parsed `Image` into laid-out heap memory.
pub fn load_image(image: &Image) -> Result<LoadedImage, LoadError> {
    let root_idx = image.root as usize;
    if root_idx >= image.objects.len() {
        return Err(LoadError::BadRoot {
            root: image.root,
            count: image.objects.len(),
        });
    }

    // ---- Pass 0: estimate capacities (so each space is sized once).
    let (imm_cap, mut_cap, code_cap) = estimate_capacities(image);
    // Give each space a tiny safety margin (some objects may pad).
    let mut immutable = MemorySpace::new(imm_cap.max(16) + 16, SpaceKind::Immutable);
    let mut mutable = MemorySpace::new(mut_cap.max(16) + 16, SpaceKind::Mutable);
    let mut code = MemorySpace::new(code_cap.max(16) + 16, SpaceKind::Code);

    // ---- Pass 1: allocate a slot for each object.
    let mut pointers: Vec<*mut PolyWord> = vec![std::ptr::null_mut(); image.objects.len()];
    let mut flags_for: Vec<u8> = vec![0; image.objects.len()];

    for (id, obj) in image.objects.iter().enumerate() {
        let (kind, flags) = classify(obj);
        let n_words = body_word_count(&obj.body);
        let space = match kind {
            SpaceKind::Immutable => &mut immutable,
            SpaceKind::Mutable => &mut mutable,
            SpaceKind::Code => &mut code,
        };
        pointers[id] = space.alloc(n_words);
        flags_for[id] = flags;
    }

    // ---- Pass 2: write length words and contents.
    for (id, obj) in image.objects.iter().enumerate() {
        let obj_ptr = pointers[id];
        let n_words = body_word_count(&obj.body);
        let flags = flags_for[id];
        // SAFETY: pointers[id] was returned by alloc in pass 1 above.
        unsafe {
            crate::space::set_length_word(obj_ptr, n_words, flags);
        }
        write_body(obj_ptr, &obj.body, &pointers)?;
    }

    let root_ptr: *const PolyWord = pointers[root_idx];

    Ok(LoadedImage {
        immutable,
        mutable,
        code,
        root: root_ptr,
    })
}

/// Convert a parsed `Value` to a `PolyWord`, looking up `Ref` ids in
/// the per-id pointer table.
fn resolve_value(v: Value, pointers: &[*mut PolyWord]) -> Result<PolyWord, LoadError> {
    match v {
        Value::Tagged(n) => {
            // Range check against the *current target* word size.
            let n_isize = isize::try_from(n)
                .map_err(|_| LoadError::TaggedOutOfRange { value: n })?;
            if !(MIN_TAGGED..=MAX_TAGGED).contains(&n_isize) {
                return Err(LoadError::TaggedOutOfRange { value: n });
            }
            Ok(PolyWord::tagged(n_isize))
        }
        Value::Ref(id) => {
            let p = *pointers.get(id as usize).ok_or(LoadError::UnresolvedRef { id })?;
            if p.is_null() {
                return Err(LoadError::UnresolvedRef { id });
            }
            Ok(PolyWord::from_ptr(p))
        }
    }
}

/// Write the body of an object into the memory at `obj_ptr` (the
/// length word at `obj_ptr-1` is assumed already set).
///
/// # Safety
/// `obj_ptr` must be the pointer returned from this loader for `body`'s
/// allocation; in particular, `body_word_count(body)` words at
/// `obj_ptr` must be valid mutable memory.
fn write_body(
    obj_ptr: *mut PolyWord,
    body: &ObjectBody,
    pointers: &[*mut PolyWord],
) -> Result<(), LoadError> {
    match body {
        // Ordinary tuples and legacy closures both just write their
        // value list into the body starting at offset 0. The
        // difference (closure type bit) lives in the length word, set
        // by the caller before we run.
        ObjectBody::Ordinary(values) | ObjectBody::LegacyClosure { values } => {
            for (i, v) in values.iter().copied().enumerate() {
                let w = resolve_value(v, pointers)?;
                // SAFETY: i < values.len() == body word count
                unsafe { obj_ptr.add(i).write(w) };
            }
        }
        ObjectBody::Closure { code_addr, values } => {
            // First word = code address (always a Ref).
            let code = *pointers
                .get(*code_addr as usize)
                .ok_or(LoadError::UnresolvedRef { id: *code_addr })?;
            if code.is_null() {
                return Err(LoadError::UnresolvedRef { id: *code_addr });
            }
            // SAFETY: closure has at least 1 word.
            unsafe { obj_ptr.add(0).write(PolyWord::from_ptr(code)) };
            for (i, v) in values.iter().copied().enumerate() {
                let w = resolve_value(v, pointers)?;
                // SAFETY: i+1 < 1 + values.len() == body word count
                unsafe { obj_ptr.add(i + 1).write(w) };
            }
        }
        ObjectBody::String(bytes) => {
            // First word is the string length (in bytes).
            // SAFETY: string has at least 1 word.
            unsafe { obj_ptr.add(0).write(PolyWord::from_bits(bytes.len())) };
            write_bytes_packed(obj_ptr, 1, bytes);
        }
        ObjectBody::Bytes(bytes) => {
            write_bytes_packed(obj_ptr, 0, bytes);
        }
        ObjectBody::Code {
            code_bytes,
            constants,
            relocs,
        } => {
            // Layout (matches PolyML pexport.cpp:780-796 + machine_dep.h
            // SetAddressOfConstants default impl):
            //
            //   [0 .. code_words)              code bytes
            //   [code_words]                   const count (= n_consts)
            //   [code_words+1 .. total-1)      constants
            //   [total-1]                      trailing byte offset
            //
            // The trailing offset is the *signed byte distance* from the
            // start of the object to the constants area, **minus** the
            // total length-word count. The runtime recovers the const
            // pointer with:
            //     cp = last_word + 1 + offset / sizeof(PolyWord)
            // (see machine_dep.h:61-67).
            write_bytes_packed(obj_ptr, 0, code_bytes);
            let code_words = code_bytes.len().div_ceil(size_of::<usize>());
            let n_consts = constants.len();
            let total_words = code_words + n_consts + 2;

            // const count at [code_words]
            // SAFETY: code_words < total_words
            unsafe {
                obj_ptr
                    .add(code_words)
                    .write(PolyWord::from_bits(n_consts));
            }

            // constants at [code_words + 1 .. code_words + 1 + n_consts]
            for (i, v) in constants.iter().copied().enumerate() {
                let w = resolve_value(v, pointers)?;
                // SAFETY: code_words + 1 + i < total_words - 1
                unsafe { obj_ptr.add(code_words + 1 + i).write(w) };
            }

            // Trailing offset at [total_words - 1]. PolyML's default
            // SetAddressOfConstants in machine_dep.h:99-103 computes
            //     offset = (constAddr - objAddr - length) * sizeof(PolyWord)
            // with constAddr = obj_ptr + (code_words + 1). So:
            //     offset = (code_words + 1 - total_words) * sizeof(PolyWord)
            //            = -(n_consts + 1) * sizeof(PolyWord)
            //
            // The casts here are bounded by PolyML's per-object size
            // limit (the length-word LENGTH_MASK), well below isize::MAX
            // on any supported target.
            #[allow(clippy::cast_possible_wrap)]
            let const_addr_index = (code_words + 1) as isize;
            #[allow(clippy::cast_possible_wrap)]
            let total_isize = total_words as isize;
            #[allow(clippy::cast_possible_wrap)]
            let word_size_isize = size_of::<usize>() as isize;
            let offset_bytes: isize = (const_addr_index - total_isize) * word_size_isize;
            #[allow(clippy::cast_sign_loss)]
            // SAFETY: total_words - 1 < total_words
            unsafe {
                obj_ptr
                    .add(total_words - 1)
                    .write(PolyWord::from_bits(offset_bytes as usize));
            }

            // TODO Phase 2.2: relocations are not applied here. For the
            // Monday milestone we load images whose code we don't yet
            // execute; once we start running native code we'll need to
            // patch addresses inside the code bytes per the reloc
            // entries.
            let _ = relocs;
        }
        ObjectBody::EntryPoint(name) => {
            // First word is a placeholder for the resolved address.
            // SAFETY: at least size_of::<usize>() worth.
            unsafe { obj_ptr.add(0).write(PolyWord::ZERO) };
            // Then the C-string. Write it into bytes starting at
            // `obj_ptr + 1` (after the placeholder).
            let dst = unsafe { obj_ptr.add(1).cast::<u8>() };
            // SAFETY: by construction body_word_count reserved
            // enough words to fit name + NUL.
            unsafe {
                std::ptr::copy_nonoverlapping(name.as_ptr(), dst, name.len());
                // Trailing NUL.
                dst.add(name.len()).write(0);
            }
        }
        ObjectBody::WeakRef => {
            // SAFETY: 1 word body.
            unsafe { obj_ptr.add(0).write(PolyWord::ZERO) };
        }
    }
    Ok(())
}

/// Write `bytes` packed into native-endian words starting at
/// `obj_ptr + word_offset`. Pads the last word with zero bytes if
/// `bytes.len()` isn't a multiple of `size_of::<usize>()`.
fn write_bytes_packed(obj_ptr: *mut PolyWord, word_offset: usize, bytes: &[u8]) {
    let dst = unsafe { obj_ptr.add(word_offset).cast::<u8>() };
    // SAFETY: caller ensures sufficient capacity.
    unsafe {
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), dst, bytes.len());
        // Pad remainder of last word with zeros so it's deterministic.
        let pad = bytes.len().next_multiple_of(size_of::<usize>()) - bytes.len();
        if pad > 0 {
            std::ptr::write_bytes(dst.add(bytes.len()), 0, pad);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use polyml_image::pexport::Image;

    #[test]
    fn load_minimal_image() {
        // Two ordinary objects: O[Ref(1)], O[Tagged(7)].
        let src = b"Objects\t2\nRoot\t0 I 8\n\
                    0:O1|@1\n\
                    1:O1|7\n";
        let img = Image::parse(src).unwrap();
        let loaded = load_image(&img).unwrap();

        // Root points to obj 0. Its body word should be a pointer to obj 1.
        let root_word = unsafe { *loaded.root };
        assert!(root_word.is_data_ptr(), "root[0] = {root_word:?}");

        // Following the pointer to obj 1, that body word should be Tagged(7).
        let obj1 = root_word.as_ptr::<PolyWord>();
        let obj1_word = unsafe { *obj1 };
        assert_eq!(obj1_word.untag(), 7, "obj1[0] = {obj1_word:?}");
    }

    #[test]
    fn load_string_object() {
        // S2|4142 = "AB"
        let src = b"Objects\t1\nRoot\t0 I 8\n0:S2|4142\n";
        let img = Image::parse(src).unwrap();
        let loaded = load_image(&img).unwrap();
        let s = loaded.root;
        // Length word should mark this as a byte object.
        let lw = unsafe { MemorySpace::length_word_of(s) };
        assert!(length_word::is_byte_object(lw));
        // First word is the string length (in bytes).
        let len = unsafe { *s }.0;
        assert_eq!(len, 2);
        // Next bytes are 'A' 'B'.
        let chars = unsafe { s.add(1).cast::<u8>() };
        let a = unsafe { *chars };
        let b = unsafe { *chars.add(1) };
        assert_eq!((a, b), (b'A', b'B'));
    }

    #[test]
    fn load_bytes_object() {
        // 8 zero bytes.
        let src = b"Objects\t1\nRoot\t0 I 8\n0:B8|0000000000000000\n";
        let img = Image::parse(src).unwrap();
        let loaded = load_image(&img).unwrap();
        let p = loaded.root;
        let w = unsafe { *p };
        assert_eq!(w.0, 0);
    }

    #[test]
    fn load_closure() {
        // C with 2 items: code addr + 1 captured tagged int.
        let src = b"Objects\t2\nRoot\t0 I 8\n\
                    0:C2|@1,42\n\
                    1:O1|0\n";
        let img = Image::parse(src).unwrap();
        let loaded = load_image(&img).unwrap();
        let c = loaded.root;
        let lw = unsafe { MemorySpace::length_word_of(c) };
        assert!(length_word::is_closure_object(lw));
        // First word: code ptr
        let code_word = unsafe { *c };
        assert!(code_word.is_data_ptr());
        // Second word: tagged 42
        let cap = unsafe { *c.add(1) };
        assert_eq!(cap.untag(), 42);
    }

    #[test]
    fn rejects_bad_root() {
        // parse_header doesn't bounds-check the root; we expect the
        // loader to catch it.
        let src = b"Objects\t1\nRoot\t99 I 8\n0:O1|0\n";
        let img = Image::parse(src).expect("parser should accept this");
        let Err(err) = load_image(&img) else {
            panic!("expected BadRoot, got Ok")
        };
        assert!(matches!(err, LoadError::BadRoot { root: 99, count: 1 }));
    }
}
