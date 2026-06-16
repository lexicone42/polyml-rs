//! Load the vendored bootstrap heap image end-to-end (parse → lay out
//! in memory → resolve pointers) and verify basic post-load invariants.
//!
//! Automatically skipped when `vendor/polyml/bootstrap/` is not present.

use std::path::PathBuf;

use polyml_image::pexport::Image;
use polyml_runtime::{
    MemorySpace, PolyWord,
    length_word::{self, length_of},
    load_image,
};

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
        assert!(
            p.pop(),
            "could not find workspace root from {}",
            env!("CARGO_MANIFEST_DIR")
        );
    }
}

fn bootstrap_file(name: &str) -> Option<PathBuf> {
    let p = workspace_root().join("vendor/polyml/bootstrap").join(name);
    p.exists().then_some(p)
}

#[test]
fn load_bootstrap64_end_to_end() {
    let Some(path) = bootstrap_file("bootstrap64.txt") else {
        eprintln!("SKIP: vendor/polyml/bootstrap/bootstrap64.txt not present");
        return;
    };
    let bytes = std::fs::read(&path).expect("read bootstrap64.txt");
    let image = Image::parse(&bytes).expect("parse bootstrap64.txt");
    let loaded = load_image(&image).expect("load_image");

    eprintln!(
        "loaded: immutable {} / mutable {} / code {} words",
        loaded.immutable.used_words(),
        loaded.mutable.used_words(),
        loaded.code.used_words()
    );

    // Smoke check: every space has some non-empty content.
    assert!(loaded.immutable.used_words() > 0);
    assert!(loaded.mutable.used_words() > 0);
    assert!(loaded.code.used_words() > 0);

    // Root pointer is non-null and reads a sensible length word.
    assert!(!loaded.root.is_null(), "root pointer null");
    let root_lw = unsafe { MemorySpace::length_word_of(loaded.root) };
    eprintln!(
        "root: length_word len={} flags=0x{:02x} (closure? {})",
        length_of(root_lw),
        length_word::flags_of(root_lw),
        length_word::is_closure_object(root_lw),
    );
    assert!(length_of(root_lw) > 0);
    assert!(length_of(root_lw) < 1_000_000);

    // Traversal: visit reachable objects from the root via BFS. For
    // ordinary/closure objects we follow body word pointers; for code
    // objects we follow the constant-segment pointers via the trailing
    // offset (mirroring how the GC actually scans). Byte objects are
    // terminal — their bytes are not GC roots.
    //
    // This stresses that every Value::Ref resolved to an in-bounds
    // pointer, and that the code-object layout (const-count + offset)
    // matches what the runtime helper expects.
    let mut seen: std::collections::HashSet<*const PolyWord> = std::collections::HashSet::new();
    let mut queue: Vec<*const PolyWord> = vec![loaded.root];

    while let Some(p) = queue.pop() {
        if !seen.insert(p) {
            continue;
        }
        if seen.len() > 50_000 {
            break; // bounded traversal cap
        }
        let lw = unsafe { MemorySpace::length_word_of(p) };
        let n = length_of(lw);
        if length_word::is_byte_object(lw) {
            continue;
        }
        if length_word::is_code_object(lw) {
            // Walk just the constants slice via the trailing offset.
            let (cp, count) = unsafe { length_word::const_segment_for_code(p) };
            for i in 0..count {
                let w = unsafe { *cp.add(i) };
                if w.is_data_ptr() {
                    queue.push(w.as_ptr::<PolyWord>());
                }
            }
            continue;
        }
        // Ordinary/closure: every body word may be a pointer.
        for i in 0..n {
            let w = unsafe { *p.add(i) };
            if w.is_data_ptr() {
                queue.push(w.as_ptr::<PolyWord>());
            }
        }
    }

    eprintln!("BFS from root touched {} objects", seen.len());
    // Bootstrap heap has 22588 objects; a healthy reachability check
    // should touch a large fraction of them from the root.
    assert!(
        seen.len() > 10_000,
        "root should reach >10k objects, only got {}",
        seen.len()
    );
}
