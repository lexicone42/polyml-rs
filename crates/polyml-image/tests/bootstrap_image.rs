//! Integration tests against the real vendored bootstrap heap images.
//!
//! Skipped automatically when the `vendor/polyml` clone is not present
//! (so a fresh checkout without `git clone` of upstream PolyML doesn't
//! fail). To run for real:
//!
//! ```sh
//! git clone --depth=1 https://github.com/polyml/polyml vendor/polyml
//! cargo test -p polyml-image --test bootstrap_image
//! ```

use std::path::{Path, PathBuf};

use polyml_image::pexport::{Image, ObjectBody, SourceArch, WordSize};

/// Locate the workspace root by walking up from `CARGO_MANIFEST_DIR`
/// until we find a `Cargo.toml` that declares `[workspace]`. The
/// integration test executable's manifest dir is the per-crate dir,
/// not the workspace root.
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

fn load_or_skip(path: &Path) -> Option<Vec<u8>> {
    match std::fs::read(path) {
        Ok(b) => Some(b),
        Err(e) => {
            eprintln!("SKIP: cannot read {} ({e})", path.display());
            None
        }
    }
}

#[test]
fn parse_bootstrap64() {
    let Some(path) = bootstrap_file("bootstrap64.txt") else {
        eprintln!("SKIP: vendor/polyml/bootstrap/bootstrap64.txt not present");
        return;
    };
    let Some(bytes) = load_or_skip(&path) else {
        return;
    };

    let img = match Image::parse(&bytes) {
        Ok(i) => i,
        Err(e) => panic!("parse failed: {e}"),
    };

    // From the header: bootstrap64.txt declares 22588 objects, root 8390, I 8.
    assert_eq!(img.objects.len(), 22588, "object count from header");
    assert_eq!(img.root, 8390, "root index");
    assert_eq!(img.arch, SourceArch::Interpreted);
    assert_eq!(img.word_size, WordSize::Bits64);

    // Sanity: the root should resolve to *some* object.
    let root = &img.objects[img.root as usize];
    eprintln!("root object body: {:?}", std::mem::discriminant(&root.body));

    // Type histogram. Verified against modifier-aware grep:
    //   grep -c '^[0-9]*:[MNVW]*B' bootstrap64.txt  →  4442
    let mut histogram = std::collections::BTreeMap::<&'static str, usize>::new();
    for obj in &img.objects {
        let tag = match &obj.body {
            ObjectBody::Ordinary(_) => "Ordinary",
            ObjectBody::Closure { .. } => "Closure",
            ObjectBody::LegacyClosure { .. } => "LegacyClosure",
            ObjectBody::String(_) => "String",
            ObjectBody::Bytes(_) => "Bytes",
            ObjectBody::Code { .. } => "Code",
            ObjectBody::EntryPoint(_) => "EntryPoint",
            ObjectBody::WeakRef => "WeakRef",
        };
        *histogram.entry(tag).or_default() += 1;
    }
    for (tag, n) in &histogram {
        eprintln!("  {tag:<14} {n}");
    }

    // Histogram totals should equal the declared object count.
    let total: usize = histogram.values().sum();
    assert_eq!(total, 22588, "every object should land in some variant");

    // Spot checks on individual bucket sizes (matched against grep
    // after fixing the modifier-skipping bug in my original count):
    assert_eq!(*histogram.get("Bytes").unwrap_or(&0), 4442, "byte objects");
    assert_eq!(*histogram.get("Closure").unwrap_or(&0), 4513, "closures");
    assert_eq!(*histogram.get("Code").unwrap_or(&0), 4436, "code objects");
    assert_eq!(*histogram.get("String").unwrap_or(&0), 3750, "strings");
}

#[test]
fn bootstrap64_roundtrips_through_writer() {
    let Some(path) = bootstrap_file("bootstrap64.txt") else {
        eprintln!("SKIP: vendor/polyml/bootstrap/bootstrap64.txt not present");
        return;
    };
    let Some(bytes) = load_or_skip(&path) else {
        return;
    };

    let img = Image::parse(&bytes).expect("parse");
    let mut emitted = Vec::with_capacity(bytes.len());
    img.write(&mut emitted).expect("write");
    let img2 = Image::parse(&emitted).expect("re-parse");

    assert_eq!(img.root, img2.root);
    assert_eq!(img.arch, img2.arch);
    assert_eq!(img.word_size, img2.word_size);
    assert_eq!(img.objects.len(), img2.objects.len());
    for (i, (a, b)) in img.objects.iter().zip(&img2.objects).enumerate() {
        assert_eq!(a, b, "object {i} differs after round-trip");
    }
}

#[test]
fn parse_bootstrap32() {
    let Some(path) = bootstrap_file("bootstrap32.txt") else {
        eprintln!("SKIP: vendor/polyml/bootstrap/bootstrap32.txt not present");
        return;
    };
    let Some(bytes) = load_or_skip(&path) else {
        return;
    };

    let img = match Image::parse(&bytes) {
        Ok(i) => i,
        Err(e) => panic!("parse failed: {e}"),
    };

    assert_eq!(img.arch, SourceArch::Interpreted);
    assert_eq!(img.word_size, WordSize::Bits32);
    assert!(
        img.objects.len() > 1000,
        "bootstrap image should have many objects"
    );
}
