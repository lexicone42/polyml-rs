//! Load the bootstrap image, snapshot the heap from its root, write a
//! pexport file, re-parse it, and check that the re-parsed image
//! preserves the structural information we just walked.
//!
//! This is the "self-export round-trip" — proves that
//! `polyml_runtime::export::snapshot` + `polyml_image::pexport::Image::write`
//! together produce a file the existing reader treats as a valid
//! heap image.

use std::path::PathBuf;

use polyml_image::pexport::{Image, ObjectBody};
use polyml_runtime::{export, load_image, PolyWord};

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

fn bootstrap_file(name: &str) -> Option<PathBuf> {
    let p = workspace_root().join("vendor/polyml/bootstrap").join(name);
    p.exists().then_some(p)
}

#[test]
fn snapshot_loaded_bootstrap_roundtrips() {
    let Some(path) = bootstrap_file("bootstrap64.txt") else {
        eprintln!("SKIP: vendor/polyml/bootstrap/bootstrap64.txt not present");
        return;
    };
    let bytes = std::fs::read(&path).expect("read bootstrap64.txt");
    let image = Image::parse(&bytes).expect("parse");
    let loaded = load_image(&image).expect("load_image");

    // Snapshot the live heap starting from the loaded root.
    let root_word = PolyWord::from_ptr(loaded.root);
    let snapshot = unsafe { export::snapshot(root_word) };

    eprintln!(
        "snapshot: {} objects reachable from root (vs {} in original image)",
        snapshot.objects.len(),
        image.objects.len()
    );

    // Should reach at least 10k objects (most of the bootstrap is
    // reachable from the root closure).
    assert!(
        snapshot.objects.len() > 10_000,
        "expected >10k reachable objects, got {}",
        snapshot.objects.len()
    );

    // Write to bytes and re-parse.
    let mut buf = Vec::with_capacity(8 * 1024 * 1024);
    snapshot.write(&mut buf).expect("write pexport");
    eprintln!("emitted {} bytes of pexport text", buf.len());

    let reparsed = Image::parse(&buf).expect("re-parse our pexport");
    assert_eq!(reparsed.root, snapshot.root);
    assert_eq!(reparsed.objects.len(), snapshot.objects.len());

    // Sanity: each variant tag matches across snapshot and reparse.
    for (i, (a, b)) in snapshot.objects.iter().zip(&reparsed.objects).enumerate() {
        let tag_a = body_tag(&a.body);
        let tag_b = body_tag(&b.body);
        assert_eq!(tag_a, tag_b, "obj {i} variant differs: {tag_a} vs {tag_b}");
        assert_eq!(a.flags, b.flags, "obj {i} flags differ");
    }
}

fn body_tag(b: &ObjectBody) -> &'static str {
    match b {
        ObjectBody::Ordinary(_) => "Ordinary",
        ObjectBody::Closure { .. } => "Closure",
        ObjectBody::LegacyClosure { .. } => "LegacyClosure",
        ObjectBody::String(_) => "String",
        ObjectBody::Bytes(_) => "Bytes",
        ObjectBody::Code { .. } => "Code",
        ObjectBody::EntryPoint(_) => "EntryPoint",
        ObjectBody::WeakRef => "WeakRef",
    }
}
