//! Adversarial stress of the image export round-trip.
//!
//! The property under test:
//!
//!   reload(export(load(img)))  ==  load(img)   (semantically)
//!
//! and the stronger byte-level fixpoint:
//!
//!   export(reload(export(x)))  ==  export(x)    (byte-identical)
//!
//! Plus: export determinism (BFS order stable across two snapshots of
//! the same heap) and export-AFTER-GC (snapshot a collected/forwarded
//! heap — the corner the foundation audit flagged as untested, where a
//! GC forwarding bug and an export bug could compound silently).
//!
//! These tests are deliberately NOT wired into regression.sh (they take
//! a few seconds). Run with:
//!   cargo test --release -p polyml-runtime --test export_roundtrip_fuzz

use std::path::PathBuf;

use polyml_image::pexport::{Image, ObjFlags, Object, ObjectBody, SourceArch, Value, WordSize};
use polyml_runtime::{Interpreter, PolyWord, export, load_image};

fn workspace_root() -> PathBuf {
    let mut p: PathBuf = env!("CARGO_MANIFEST_DIR").into();
    loop {
        let cargo = p.join("Cargo.toml");
        if cargo.exists()
            && let Ok(text) = std::fs::read_to_string(&cargo)
            && text.contains("[workspace]")
        {
            return p;
        }
        assert!(p.pop());
    }
}

fn image_file(rel: &str) -> Option<PathBuf> {
    let p = workspace_root().join(rel);
    p.exists().then_some(p)
}

/// Snapshot the heap reachable from a loaded image's root, write to
/// pexport bytes, and return (image, bytes).
fn snapshot_to_bytes(loaded_root: *const PolyWord) -> (Image, Vec<u8>) {
    let snap = unsafe { export::snapshot(PolyWord::from_ptr(loaded_root)) };
    let mut buf = Vec::with_capacity(8 * 1024 * 1024);
    snap.write(&mut buf).expect("write pexport");
    (snap, buf)
}

/// Compare two object graphs field-for-field, returning the first
/// divergence as a human-readable string (or None if identical).
fn first_object_diff(a: &[Object], b: &[Object]) -> Option<String> {
    if a.len() != b.len() {
        return Some(format!("object count: {} vs {}", a.len(), b.len()));
    }
    for (i, (x, y)) in a.iter().zip(b.iter()).enumerate() {
        if x.flags != y.flags {
            return Some(format!(
                "obj {i} flags differ: {:?} vs {:?}",
                x.flags, y.flags
            ));
        }
        if x.body != y.body {
            return Some(format!(
                "obj {i} body differs:\n  A = {:?}\n  B = {:?}",
                short_body(&x.body),
                short_body(&y.body)
            ));
        }
    }
    None
}

fn short_body(b: &ObjectBody) -> String {
    match b {
        ObjectBody::Ordinary(v) => format!("Ordinary(len={}) {:?}", v.len(), head(v)),
        ObjectBody::Closure { code_addr, values } => {
            format!(
                "Closure(code=@{code_addr}, cap={}) {:?}",
                values.len(),
                head(values)
            )
        }
        ObjectBody::LegacyClosure { values } => format!("LegacyClosure(len={})", values.len()),
        ObjectBody::String(s) => format!("String(len={}) {:x?}", s.len(), &s[..s.len().min(8)]),
        ObjectBody::Bytes(s) => format!("Bytes(len={}) {:x?}", s.len(), &s[..s.len().min(8)]),
        ObjectBody::Code {
            code_bytes,
            constants,
            relocs,
        } => format!(
            "Code(bytes={}, consts={}, relocs={})",
            code_bytes.len(),
            constants.len(),
            relocs.len()
        ),
        ObjectBody::EntryPoint(n) => format!("EntryPoint({n})"),
        ObjectBody::WeakRef => "WeakRef".into(),
    }
}

fn head(v: &[Value]) -> Vec<Value> {
    v.iter().take(4).copied().collect()
}

// ---------------------------------------------------------------------------
// 1. DETERMINISM: two snapshots of the SAME unmodified heap are identical.
// ---------------------------------------------------------------------------

#[test]
fn snapshot_is_deterministic_across_two_walks() {
    let Some(path) = image_file("vendor/polyml/bootstrap/bootstrap64.txt") else {
        eprintln!("SKIP: bootstrap64.txt not present");
        return;
    };
    let bytes = std::fs::read(&path).unwrap();
    let image = Image::parse(&bytes).unwrap();
    let loaded = load_image(&image).unwrap();

    let (_s1, b1) = snapshot_to_bytes(loaded.root);
    let (_s2, b2) = snapshot_to_bytes(loaded.root);

    assert_eq!(
        b1.len(),
        b2.len(),
        "two snapshots of the same heap have different byte lengths"
    );
    assert!(
        b1 == b2,
        "two snapshots of the SAME heap differ — BFS order is non-deterministic"
    );
    eprintln!("determinism: two walks identical, {} bytes", b1.len());
}

// ---------------------------------------------------------------------------
// 2. FIXPOINT: export(reload(export(x))) == export(x), byte-for-byte.
//    This is the strong round-trip property: once a heap has been through
//    one export+reload, a second export must produce identical bytes.
//    Any writer/reader asymmetry shows up here as a byte diff.
// ---------------------------------------------------------------------------

fn fixpoint_for(rel: &str) {
    let Some(path) = image_file(rel) else {
        eprintln!("SKIP: {rel} not present");
        return;
    };
    let bytes = std::fs::read(&path).unwrap();
    let image = Image::parse(&bytes).unwrap();
    let loaded1 = load_image(&image).unwrap();

    // First export.
    let (snap1, buf1) = snapshot_to_bytes(loaded1.root);

    // Reload the exported image and export again.
    let reparsed1 = Image::parse(&buf1).expect("re-parse export #1");
    let loaded2 = load_image(&reparsed1).expect("re-load export #1");
    let (snap2, buf2) = snapshot_to_bytes(loaded2.root);

    eprintln!(
        "[{rel}] export#1 = {} objs / {} bytes ; export#2 = {} objs / {} bytes",
        snap1.objects.len(),
        buf1.len(),
        snap2.objects.len(),
        buf2.len()
    );

    // Structural fixpoint first (gives a readable diff if it fails).
    if let Some(d) = first_object_diff(&snap1.objects, &snap2.objects) {
        panic!("[{rel}] FIXPOINT BROKEN (structural): {d}");
    }
    assert_eq!(
        snap1.root, snap2.root,
        "[{rel}] root id changed across fixpoint"
    );

    // Byte-level fixpoint: the writer must be a true fixpoint after one pass.
    if buf1 != buf2 {
        // Locate first differing byte for the report.
        let n = buf1.len().min(buf2.len());
        let mut at = n;
        for i in 0..n {
            if buf1[i] != buf2[i] {
                at = i;
                break;
            }
        }
        let ctx_a =
            String::from_utf8_lossy(&buf1[at.saturating_sub(40)..(at + 40).min(buf1.len())]);
        let ctx_b =
            String::from_utf8_lossy(&buf2[at.saturating_sub(40)..(at + 40).min(buf2.len())]);
        panic!(
            "[{rel}] FIXPOINT BROKEN (bytes): first diff at byte {at} \
             (len {} vs {})\n  A: …{ctx_a}…\n  B: …{ctx_b}…",
            buf1.len(),
            buf2.len()
        );
    }
    eprintln!("[{rel}] fixpoint holds: byte-identical after reload+re-export");
}

#[test]
fn fixpoint_bootstrap64() {
    fixpoint_for("vendor/polyml/bootstrap/bootstrap64.txt");
}

#[test]
fn fixpoint_polyexport() {
    // The self-bootstrapped 13 MB image, if present (453K objects). The
    // heavy case — exercises every object variant at scale.
    fixpoint_for("vendor/polyml/polyexport");
}

// ---------------------------------------------------------------------------
// 3. EXPORT-AFTER-GC: snapshot a heap that has been collected/forwarded.
//    The foundation audit flagged this as the one corner with no coverage:
//    a GC forwarding bug + an export bug could compound silently.
//
//    We load bootstrap, run a meaningful chunk of execution (so the alloc
//    space fills and we can force a GC), force a GC via the public
//    Interpreter::gc(), then snapshot the IMAGE root (which lives in the
//    immutable space — unmoved) and confirm it still round-trips and is
//    structurally identical to a pre-GC snapshot of the same root.
// ---------------------------------------------------------------------------

#[test]
fn export_after_gc_immutable_root_stable() {
    let Some(path) = image_file("vendor/polyml/bootstrap/bootstrap64.txt") else {
        eprintln!("SKIP: bootstrap64.txt not present");
        return;
    };
    let bytes = std::fs::read(&path).unwrap();
    let image = Image::parse(&bytes).unwrap();
    let loaded = load_image(&image).unwrap();

    // The image root is in the immutable space; the copying GC only moves
    // the alloc space. So a pre-GC and post-GC snapshot of the immutable
    // root must be identical. (This guards against the GC clobbering or
    // forwarding immutable-space objects it shouldn't touch.)
    let root_ptr = loaded.root;
    let (pre_snap, pre_bytes) = snapshot_to_bytes(root_ptr);

    // Build an interpreter on this root, give it an alloc space.
    let code_obj_ptr = unsafe { *root_ptr }.as_ptr::<PolyWord>();
    let mut interp = unsafe { Interpreter::from_code_object(1024 * 1024, code_obj_ptr) }
        .with_default_alloc_space_words(8 * 1024 * 1024);

    // Force a GC immediately, with NO execution — nothing has mutated the
    // immutable root, so a pre/post snapshot of it must be identical and
    // safe. (If this SEGVs, GC-then-export is unsafe on its own; if only
    // the run-then-GC variant SEGVs, the cause is the run, not GC+export.)
    let used = interp.gc();
    eprintln!("forced GC (no run); alloc used_words now = {used:?}");

    // Snapshot the immutable root again — must be unchanged.
    let (post_snap, post_bytes) = snapshot_to_bytes(root_ptr);

    if let Some(d) = first_object_diff(&pre_snap.objects, &post_snap.objects) {
        panic!("EXPORT-AFTER-GC: immutable root snapshot changed after GC: {d}");
    }
    assert!(
        pre_bytes == post_bytes,
        "EXPORT-AFTER-GC: immutable root export bytes changed after GC \
         (pre {} bytes, post {} bytes)",
        pre_bytes.len(),
        post_bytes.len()
    );
    eprintln!(
        "export-after-gc: immutable root stable across GC ({} objs, {} bytes)",
        post_snap.objects.len(),
        post_bytes.len()
    );
}

// ---------------------------------------------------------------------------
// 3b. EXPORT-AFTER-A-GC-THAT-MOVED-OBJECTS: snapshot a heap whose objects
//     were ACTUALLY copied/forwarded by a real Cheney collection, and
//     structurally diff the pre-GC vs post-GC snapshot of the SAME root.
//
//     The test above (export_after_gc_immutable_root_stable) only checks
//     the IMMUTABLE image root — which the copying GC never moves — so it
//     cannot detect a forwarding bug that mis-copies a body, drops a child
//     pointer, mangles a flag/length word, or interns a stale address.
//     This test closes that gap: it builds an object graph IN the alloc
//     space (the from-space the GC frees), runs the real `gc::collect`
//     forwarding the root (so every object MOVES and the from-space Box is
//     dropped/freed), then snapshots the FORWARDED root and asserts it is
//     structurally identical to the pre-GC snapshot.
//
//     A copying-GC bug (wrong child slot forwarded, body truncated, flag
//     dropped, tagged/byte value corrupted, ref topology changed, or a
//     dangling read of freed from-space) shows up here as either a panic
//     inside snapshot()/collect() or a structural diff. The graph is
//     deliberately varied: shared subtrees (interning), deep chains,
//     mutable cells, byte objects with non-trivial payloads, and a
//     zero-length object.
//
//     Safety: this exercises gc::collect + export::snapshot DIRECTLY on a
//     synthetic MemorySpace — no interpreter, no bytecode, no stack — so it
//     is independent of (and cannot trip) the interpreter-stack-driven GC
//     corner that needs the full `poly` run. It isolates the
//     forwarding-then-export pipeline.
// ---------------------------------------------------------------------------

#[test]
fn export_after_real_gc_structural_fixpoint() {
    use polyml_runtime::length_word::{F_BYTE_OBJ, F_MUTABLE_BIT};
    use polyml_runtime::space::{MemorySpace, set_length_word};
    use polyml_runtime::{SpaceKind, gc};

    // Build a non-trivial object graph in an alloc-space (= from-space).
    // Layout (allocated leaf-first so parents can reference children):
    //
    //   leaf_bytes : byte object, 8 data bytes
    //   chain[0..D]: deep chain of word objects, each pointing at the next
    //                and ALSO at the shared leaf_bytes (forces interning of
    //                a leaf reachable many times)
    //   mut_cell   : a MUTABLE 1-word cell holding a tagged int
    //   empty      : a zero-length word object (legal; e.g. ())
    //   root       : a word object holding refs to chain[0], mut_cell,
    //                empty, leaf_bytes, plus a couple of tagged ints
    //
    // After GC every body moves to to-space; the post-GC snapshot must be
    // byte-for-byte structurally identical to the pre-GC one.
    let mut space = MemorySpace::new(4096, SpaceKind::Mutable);

    // Shared leaf byte object.
    let leaf = space.alloc(1);
    unsafe {
        set_length_word(leaf, 1, F_BYTE_OBJ);
        leaf.write(PolyWord::from_bits(0x0102_0304_0506_0708));
    }
    let leaf_w = PolyWord::from_ptr(leaf.cast_const());

    // Deep chain, each node = [next_or_nil, leaf, tagged(depth)].
    const DEPTH: usize = 64;
    let mut prev: Option<PolyWord> = None;
    let mut chain_head = leaf_w;
    for d in 0..DEPTH {
        let node = space.alloc(3);
        unsafe {
            set_length_word(node, 3, 0);
            // word0: pointer to the previously-built (deeper) node, or
            // reuse leaf as a terminator so every slot is a real pointer.
            node.write(prev.unwrap_or(leaf_w));
            node.add(1).write(leaf_w);
            node.add(2).write(PolyWord::tagged(d as isize));
        }
        let nw = PolyWord::from_ptr(node.cast_const());
        prev = Some(nw);
        chain_head = nw;
    }

    // Mutable cell.
    let mut_cell = space.alloc(1);
    unsafe {
        set_length_word(mut_cell, 1, F_MUTABLE_BIT);
        mut_cell.write(PolyWord::tagged(0x7fff_ffff));
    }
    let mut_w = PolyWord::from_ptr(mut_cell.cast_const());

    // Zero-length object (legal — empty tuple/vector).
    let empty = space.alloc(0);
    unsafe {
        set_length_word(empty, 0, 0);
    }
    let empty_w = PolyWord::from_ptr(empty.cast_const());

    // Root word object.
    let root = space.alloc(6);
    unsafe {
        set_length_word(root, 6, 0);
        root.write(chain_head);
        root.add(1).write(mut_w);
        root.add(2).write(empty_w);
        root.add(3).write(leaf_w);
        root.add(4).write(PolyWord::tagged(-12345));
        root.add(5).write(PolyWord::tagged(67890));
    }
    let mut root_w = PolyWord::from_ptr(root.cast_const());

    // Snapshot BEFORE the GC (objects still in from-space).
    let pre = unsafe { export::snapshot(root_w) };
    let mut pre_bytes = Vec::new();
    pre.write(&mut pre_bytes).expect("write pre snapshot");
    eprintln!(
        "pre-GC snapshot: {} objects, {} bytes",
        pre.objects.len(),
        pre_bytes.len()
    );

    // Capture the from-space range so we can PROVE the GC actually moved
    // things (post-GC root must point OUTSIDE the old from-space).
    let from = space.as_ptr_range();
    let from_lo = from.start as usize;
    let from_hi = from.end as usize;
    assert!(
        (root_w.0) >= from_lo && (root_w.0) < from_hi,
        "pre-GC root should be in from-space"
    );
    let pre_used = space.used_words();
    let pre_root_addr = root_w.0;

    // Run a REAL Cheney collection, forwarding only the root. Every live
    // object is copied to a fresh to-space and the from-space Box is
    // dropped (freed) inside collect()/replace_storage().
    let new_used = gc::collect(&mut space, |c| {
        // SAFETY: root_w is a valid, writable PolyWord pointer slot.
        unsafe { c.forward(&mut root_w as *mut _) };
    });
    eprintln!(
        "real GC: {pre_used} -> {new_used} live words; root forwarded \
         0x{pre_root_addr:016x} -> 0x{:016x}",
        root_w.0
    );

    // The root MUST have moved out of the freed from-space.
    assert!(
        !((root_w.0) >= from_lo && (root_w.0) < from_hi),
        "post-GC root still points into the FREED from-space \
         (GC did not forward the root) — would be a use-after-free"
    );
    // Sanity: a non-trivial graph really was retained.
    assert!(
        new_used > DEPTH,
        "GC dropped live objects (retained too few)"
    );

    // Snapshot AFTER the GC, from the forwarded root.
    let post = unsafe { export::snapshot(root_w) };
    let mut post_bytes = Vec::new();
    post.write(&mut post_bytes).expect("write post snapshot");
    eprintln!(
        "post-GC snapshot: {} objects, {} bytes",
        post.objects.len(),
        post_bytes.len()
    );

    // STRUCTURAL fixpoint: the object graph is unchanged by collection;
    // only addresses moved, and snapshot() abstracts addresses to dense
    // BFS ids (assigned in deterministic slot-discovery order). So the
    // pre- and post-GC snapshots must be IDENTICAL — same object count,
    // flags, bodies, and ref topology.
    if let Some(d) = first_object_diff(&pre.objects, &post.objects) {
        panic!("EXPORT-AFTER-REAL-GC: snapshot changed after forwarding: {d}");
    }
    assert_eq!(
        pre.root, post.root,
        "EXPORT-AFTER-REAL-GC: root id changed across GC"
    );
    // And byte-identical (the writer is deterministic on an identical graph).
    assert!(
        pre_bytes == post_bytes,
        "EXPORT-AFTER-REAL-GC: export bytes changed after GC \
         (pre {} bytes, post {} bytes)",
        pre_bytes.len(),
        post_bytes.len()
    );

    // Cross-check: the post-GC snapshot must also be a true reload fixpoint
    // (export -> reload -> re-export byte-identical), i.e. a heap that has
    // been GC'd still produces a clean, reloadable image.
    let reparsed = Image::parse(&post_bytes).expect("re-parse post-GC export");
    let loaded = load_image(&reparsed).expect("re-load post-GC export");
    let (_re_snap, re_bytes) = snapshot_to_bytes(loaded.root);
    assert!(
        re_bytes == post_bytes,
        "EXPORT-AFTER-REAL-GC: post-GC image is not a reload fixpoint \
         ({} vs {} bytes)",
        post_bytes.len(),
        re_bytes.len()
    );

    eprintln!(
        "export-after-real-GC: {} objects forwarded + snapshotted, \
         structural + byte fixpoint holds, reloads clean",
        post.objects.len()
    );
}

// ---------------------------------------------------------------------------
// 4. ITERATED RELOAD: load → export → reload → export → reload … N times.
//    Hammers the writer/reader symmetry; any drift accumulates.
// ---------------------------------------------------------------------------

#[test]
fn iterated_reload_is_stable() {
    let Some(path) = image_file("vendor/polyml/bootstrap/bootstrap64.txt") else {
        eprintln!("SKIP: bootstrap64.txt not present");
        return;
    };
    let bytes = std::fs::read(&path).unwrap();
    let image = Image::parse(&bytes).unwrap();
    let loaded = load_image(&image).unwrap();
    let (mut prev_snap, mut prev_bytes) = snapshot_to_bytes(loaded.root);

    for round in 1..=5 {
        let reparsed = Image::parse(&prev_bytes).expect("re-parse");
        let loaded_n = load_image(&reparsed).expect("re-load");
        let (snap, buf) = snapshot_to_bytes(loaded_n.root);

        if let Some(d) = first_object_diff(&prev_snap.objects, &snap.objects) {
            panic!("ITERATED RELOAD: drift at round {round}: {d}");
        }
        assert!(
            prev_bytes == buf,
            "ITERATED RELOAD: byte drift at round {round} ({} vs {} bytes)",
            prev_bytes.len(),
            buf.len()
        );
        prev_snap = snap;
        prev_bytes = buf;
    }
    eprintln!(
        "iterated reload: stable across 5 rounds, {} bytes",
        prev_bytes.len()
    );
}

// ---------------------------------------------------------------------------
// 5. SYNTHETIC GRAPHS: build pathological images directly and verify the
//    load → snapshot → write → parse → load pipeline preserves them.
//    Real bootstrap images don't exercise every corner (extreme tagged
//    values, every flag combo, zero-length objects, deep sharing).
// ---------------------------------------------------------------------------

fn img(root: u32, objects: Vec<Object>) -> Image {
    Image {
        root,
        arch: SourceArch::Interpreted,
        word_size: WordSize::Bits64,
        objects,
    }
}

fn ord(vs: Vec<Value>) -> Object {
    Object {
        flags: ObjFlags::default(),
        body: ObjectBody::Ordinary(vs),
    }
}

/// Load an image, snapshot it from the root, write+reparse, and return
/// the re-snapshot. Panics with a readable diff on any divergence.
fn pipeline(image: &Image) -> Image {
    let loaded = load_image(image).expect("load synthetic image");
    let (snap, buf) = snapshot_to_bytes(loaded.root);
    let reparsed = Image::parse(&buf).expect("re-parse snapshot");
    // Fixpoint: re-load and re-snapshot must match.
    let loaded2 = load_image(&reparsed).expect("re-load snapshot");
    let (snap2, buf2) = snapshot_to_bytes(loaded2.root);
    if let Some(d) = first_object_diff(&snap.objects, &snap2.objects) {
        panic!("synthetic pipeline fixpoint broken: {d}");
    }
    assert!(buf == buf2, "synthetic pipeline byte-fixpoint broken");
    snap
}

#[test]
fn synthetic_extreme_tagged_values() {
    // Tagged ints span the full i63 range in PolyWord. The pexport text
    // format stores them as decimal; verify the extremes survive.
    // PolyWord tags drop the top bit, so the representable untagged range
    // is roughly i63. Use large-but-safe values.
    let big = (1i64 << 60) - 1;
    let neg = -((1i64 << 60) - 1);
    let snap = pipeline(&img(
        0,
        vec![ord(vec![
            Value::Tagged(0),
            Value::Tagged(1),
            Value::Tagged(-1),
            Value::Tagged(big),
            Value::Tagged(neg),
        ])],
    ));
    match &snap.objects[0].body {
        ObjectBody::Ordinary(v) => {
            assert_eq!(v[0], Value::Tagged(0));
            assert_eq!(v[3], Value::Tagged(big), "large positive tagged lost");
            assert_eq!(v[4], Value::Tagged(neg), "large negative tagged lost");
        }
        other => panic!("expected Ordinary, got {other:?}"),
    }
}

#[test]
fn synthetic_string_becomes_bytes_but_memory_identical() {
    // THE ASYMMETRY: export::snapshot emits every byte object as `B`
    // (Bytes), never `S` (String). bootstrap64.txt has 3750 `S` records;
    // our exports have zero. This test pins the consequence: a String
    // object, once loaded and snapshotted, becomes Bytes — and the
    // in-memory layout of the reloaded image must be IDENTICAL to the
    // original load (the length-prefix word becomes leading data bytes,
    // but the words are the same).
    //
    // S<N>: word[0]=N, then ceil(N/8) packed data words.
    // After snapshot -> B<(1+ceil(N/8))*8>: ceil(M/8) = 1+ceil(N/8) words.
    // 24 bytes, like a real S record ("PolyML.runFunction(1)(1)").
    let original = img(
        0,
        vec![Object {
            flags: ObjFlags::default(),
            body: ObjectBody::String(b"PolyML.runFunction(1)(1)".to_vec()),
        }],
    );

    // Load the ORIGINAL String image and capture its raw object words.
    let loaded_orig = load_image(&original).expect("load String image");
    let orig_words = read_object_words(loaded_orig.root);

    // Snapshot it -> should come back as Bytes.
    let (snap, buf) = snapshot_to_bytes(loaded_orig.root);
    assert_eq!(snap.objects.len(), 1);
    match &snap.objects[0].body {
        ObjectBody::Bytes(_) => {} // expected: S normalised to B
        ObjectBody::String(_) => {
            panic!("snapshot unexpectedly preserved String — format note in export.rs is stale")
        }
        other => panic!("expected Bytes after snapshot, got {other:?}"),
    }

    // Reload the snapshot (now a B record) and compare raw words.
    let reparsed = Image::parse(&buf).expect("reparse");
    let loaded_b = load_image(&reparsed).expect("load Bytes image");
    let b_words = read_object_words(loaded_b.root);

    assert_eq!(
        orig_words, b_words,
        "S->B conversion changed the in-memory object words: \
         orig(String)={orig_words:?} vs reloaded(Bytes)={b_words:?}"
    );
    eprintln!(
        "S->B faithful: {} words identical (String prefix word {} preserved as data)",
        orig_words.len(),
        orig_words[0]
    );
}

/// Read the raw body words (as usize bit patterns) of the object at `ptr`.
fn read_object_words(ptr: *const PolyWord) -> Vec<usize> {
    let lw = unsafe { polyml_runtime::space::MemorySpace::length_word_of(ptr) };
    let n = polyml_runtime::length_word::length_of(lw);
    (0..n).map(|i| unsafe { (*ptr.add(i)).0 }).collect()
}

#[test]
fn synthetic_all_flag_combinations_on_bytes() {
    // Every modifier-flag combination on a byte object must round-trip.
    // (Mutable byte objects land in the mutable space; weak/negative/
    // no-overwrite are pure metadata.)
    for bits in 0u8..16 {
        let mut flags = ObjFlags::default();
        if bits & 1 != 0 {
            flags |= ObjFlags::MUTABLE;
        }
        if bits & 2 != 0 {
            flags |= ObjFlags::NEGATIVE;
        }
        if bits & 4 != 0 {
            flags |= ObjFlags::NO_OVERWRITE;
        }
        if bits & 8 != 0 {
            flags |= ObjFlags::WEAK;
        }
        // Root must be reachable; wrap the flagged byte object in an
        // ordinary root so the root itself is a normal word object.
        let image = img(
            0,
            vec![
                ord(vec![Value::Ref(1)]),
                Object {
                    flags,
                    body: ObjectBody::Bytes(vec![0xde, 0xad, 0xbe, 0xef, 0x01, 0x02, 0x03, 0x04]),
                },
            ],
        );
        let snap = pipeline(&image);
        // The snapshot's object[1] (the byte object) must carry the same
        // metadata flags. WEAK changes the variant (WeakRef has no body),
        // so only assert the non-weak flags survive when the body is Bytes.
        let got = snap.objects[1].flags;
        // MUTABLE / NEGATIVE / NO_OVERWRITE must be preserved.
        for (f, name) in [
            (ObjFlags::MUTABLE, "MUTABLE"),
            (ObjFlags::NEGATIVE, "NEGATIVE"),
            (ObjFlags::NO_OVERWRITE, "NO_OVERWRITE"),
            (ObjFlags::WEAK, "WEAK"),
        ] {
            assert_eq!(
                flags.contains(f),
                got.contains(f),
                "flag {name} not preserved for bits={bits}: in={flags:?} out={got:?}"
            );
        }
    }
    eprintln!("all 16 flag combinations on byte objects round-trip");
}

#[test]
fn synthetic_zero_length_and_empty() {
    // Zero-length objects are legal (empty tuple/array, empty string).
    // The root must be non-empty (loader-fuzz: a non-closure/empty root
    // is fine here since we snapshot structurally, not run it).
    let image = img(
        0,
        vec![
            ord(vec![Value::Ref(1), Value::Ref(2), Value::Ref(3)]),
            ord(vec![]), // empty tuple
            Object {
                flags: ObjFlags::default(),
                body: ObjectBody::Bytes(vec![]), // empty bytes
            },
            Object {
                flags: ObjFlags::default(),
                body: ObjectBody::String(vec![]), // empty string
            },
        ],
    );
    let snap = pipeline(&image);
    assert_eq!(snap.objects.len(), 4);
    eprintln!(
        "zero-length objects round-trip ({} objs)",
        snap.objects.len()
    );
}

#[test]
fn synthetic_deep_sharing_dag() {
    // A wide DAG where many parents share one leaf — interning must
    // collapse to a single object, and the count must be stable across
    // the fixpoint. (A non-deterministic intern would change object
    // count or ref ids.)
    let leaf = 1u32;
    let mut objects = vec![
        // root: 50 refs all to the same leaf
        ord((0..50).map(|_| Value::Ref(leaf)).collect()),
    ];
    objects.push(Object {
        flags: ObjFlags::default(),
        body: ObjectBody::Bytes(b"shared-leaf".to_vec()),
    });
    let snap = pipeline(&img(0, objects));
    assert_eq!(
        snap.objects.len(),
        2,
        "shared leaf not interned to one object"
    );
    match &snap.objects[0].body {
        ObjectBody::Ordinary(v) => {
            assert_eq!(v.len(), 50);
            // All refs point to the same id.
            let ids: Vec<u32> = v
                .iter()
                .filter_map(|x| {
                    if let Value::Ref(id) = x {
                        Some(*id)
                    } else {
                        None
                    }
                })
                .collect();
            assert_eq!(ids.len(), 50);
            assert!(ids.iter().all(|&id| id == ids[0]), "shared refs diverged");
        }
        other => panic!("expected Ordinary root, got {other:?}"),
    }
    eprintln!("deep-sharing DAG: 50 refs collapse to 1 interned leaf");
}

#[test]
fn synthetic_entry_point_normalised_to_bytes_with_token_preserved() {
    // DOCUMENTED BEHAVIOR (asserted): an EntryPoint object, once loaded
    // and patched, is a byte object: word0 = the RTS dispatch TOKEN (a
    // small integer, NOT a host pointer), then the C-string name + NUL.
    // export::snapshot has no EntryPoint case, so it re-emits as Bytes —
    // losing the `E` type letter but PRESERVING word0 (the token) and the
    // name as data. The interpreter dispatches entry points by reading
    // word0 as a token, so a re-exported image works WITHOUT re-running
    // patch_entry_points. (Confirmed end-to-end: the real polyexport has
    // 0 `E` records — all baked to `B` with the token in word0 — and runs
    // as a REPL.) The faithfulness caveat is the KNOWN RTS-token-staleness
    // hazard (MEMORY.md): a baked token is valid only against an RTS table
    // with the same register() order. Re-export inherits that hazard but
    // introduces no NEW one — crucially, NO host pointer is ever baked.
    use polyml_runtime::{RtsTable, patch_entry_points};

    let name = "PolyThreadMutexBlock";
    let image = img(
        0,
        vec![
            ord(vec![Value::Ref(1)]),
            Object {
                flags: ObjFlags::MUTABLE | ObjFlags::WEAK | ObjFlags::NO_OVERWRITE,
                body: ObjectBody::EntryPoint(name.to_string()),
            },
        ],
    );
    let mut loaded = load_image(&image).expect("load entry-point image");

    // Patch entry points against the real RTS table — bakes the token.
    let table = RtsTable::new();
    let expect_token = table.token_for(name);
    let (patched, _missing) = patch_entry_points(&mut loaded, &table);
    assert_eq!(patched, 1, "entry point {name} was not patched");
    let token = expect_token.expect("known RTS symbol must resolve to a token");

    let (snap, _buf) = snapshot_to_bytes(loaded.root);
    let b = match &snap.objects[1].body {
        ObjectBody::Bytes(b) => b,
        other => panic!(
            "entry point should snapshot as Bytes (E->B normalisation), got {}",
            short_body(other)
        ),
    };

    // word0 must equal the small integer token — NOT a host address.
    let word0 = usize::try_from(u64::from_le_bytes(b[0..8].try_into().unwrap())).unwrap();
    assert_eq!(
        word0, token,
        "entry-point word0 should be the RTS token {token}, got {word0}"
    );
    assert!(
        token < (1 << 32),
        "token {token} suspiciously large — would indicate a baked host pointer, not a token"
    );

    // Name must survive in the byte payload (offset 8, NUL-terminated).
    let name_end = b[8..]
        .iter()
        .position(|&c| c == 0)
        .map_or(b.len(), |p| 8 + p);
    let recovered = String::from_utf8_lossy(&b[8..name_end]);
    assert_eq!(recovered, name, "entry-point symbol name lost in B payload");

    // Flags must survive (entry points are MWVB in real images).
    assert!(snap.objects[1].flags.contains(ObjFlags::MUTABLE));
    assert!(snap.objects[1].flags.contains(ObjFlags::WEAK));
    assert!(snap.objects[1].flags.contains(ObjFlags::NO_OVERWRITE));

    eprintln!(
        "entry-point E->B: token {token} (not a host ptr) + name {recovered:?} preserved in {} bytes",
        b.len()
    );
}
