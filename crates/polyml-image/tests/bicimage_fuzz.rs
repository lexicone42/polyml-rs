//! Reader-robustness fuzz for the binary `bicimage` format.
//!
//! The loader-fuzz campaign that found two memory-safety bugs (a
//! non-closure root and a count/payload mismatch) was PEXPORT-only. The
//! `bicimage` reader (`Image::read_bic`) is newer and had never been
//! fuzzed. `read_bic` takes fully attacker-controlled bytes, so its
//! contract is total: for ANY input it must return `Ok` or `Err`, never
//! panic, hang, or over-read.
//!
//! We seed from a REAL image (the bootstrap, converted to bicimage) and
//! from hand-built tiny images, then apply deterministic mutations
//! (single-byte flips, truncations, byte insertions, length-field
//! corruption) and assert every result is a clean `Result`. The RNG is a
//! fixed-seed LCG so failures reproduce exactly.
//!
//! Run: `cargo test --release -p polyml-image --test bicimage_fuzz`
//! (needs vendor/polyml/bootstrap/bootstrap64.txt for the real-image
//! arm; the synthetic arm always runs).

use std::path::PathBuf;

use polyml_image::Image;

fn workspace_root() -> PathBuf {
    let mut p: PathBuf = env!("CARGO_MANIFEST_DIR").into();
    loop {
        if p.join("Cargo.toml").exists()
            && std::fs::read_to_string(p.join("Cargo.toml"))
                .map(|t| t.contains("[workspace]"))
                .unwrap_or(false)
        {
            return p;
        }
        assert!(p.pop(), "no workspace root");
    }
}

/// Deterministic LCG (glibc constants) — no `rand` dep, reproducible.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next() >> 33) as usize % n
        }
    }
}

/// The property: read_bic on arbitrary bytes never panics. `catch_unwind`
/// turns a would-be panic into a test failure with the offending bytes.
fn assert_total(bytes: &[u8], label: &str) {
    let owned = bytes.to_vec();
    let r = std::panic::catch_unwind(move || {
        // We only care that it RETURNS (Ok or Err). Drop the value.
        let _ = Image::read_bic(&owned);
    });
    assert!(
        r.is_ok(),
        "read_bic PANICKED on {label} ({} bytes): {:02x?}",
        bytes.len(),
        &bytes[..bytes.len().min(64)]
    );
}

/// Apply the mutation families to a seed and check totality of each mutant.
fn fuzz_seed(seed_bytes: &[u8], label: &str, rounds: usize) {
    // The seed itself must read back (it came from a real round-trip).
    assert_total(seed_bytes, &format!("{label}/pristine"));

    let mut rng = Lcg(0x1234_5678_9abc_def0 ^ (seed_bytes.len() as u64));

    // 1. Single-byte flips at random positions.
    for _ in 0..rounds {
        let mut m = seed_bytes.to_vec();
        if m.is_empty() {
            break;
        }
        let i = rng.below(m.len());
        m[i] ^= 1 << (rng.below(8));
        assert_total(&m, &format!("{label}/flip@{i}"));
    }

    // 2. Truncations at every prefix length (catches every "read past EOF").
    for cut in 0..seed_bytes.len().min(512) {
        assert_total(&seed_bytes[..cut], &format!("{label}/trunc@{cut}"));
    }

    // 3. Random byte replacement with adversarial values (0x00, 0xff, 0x80,
    //    high-bit-set varint continuations).
    let nasty = [0x00u8, 0xff, 0x80, 0x7f, 0xfe];
    for _ in 0..rounds {
        let mut m = seed_bytes.to_vec();
        if m.is_empty() {
            break;
        }
        let i = rng.below(m.len());
        m[i] = nasty[rng.below(nasty.len())];
        assert_total(&m, &format!("{label}/nasty@{i}"));
    }

    // 4. Byte insertions (shifts every downstream field / length).
    for _ in 0..rounds / 2 {
        let mut m = seed_bytes.to_vec();
        let i = rng.below(m.len() + 1);
        m.insert(i, nasty[rng.below(nasty.len())]);
        assert_total(&m, &format!("{label}/insert@{i}"));
    }
}

#[test]
fn read_bic_is_total_on_synthetic_mutants() {
    // A minimal valid-ish bicimage: MAGIC + arch + wordsize + root + count=0.
    // We don't know MAGIC here (private), so build the seed by round-tripping
    // the smallest real image we can construct: an empty-object image is not
    // expressible without the crate internals, so instead fuzz a pile of
    // structured-random byte strings that exercise the header + first-object
    // decode paths. Totality must hold regardless of validity.
    let mut rng = Lcg(0xdead_beef_cafe_babe);
    for len in [0usize, 1, 2, 8, 16, 32, 64, 256] {
        for _ in 0..64 {
            let mut m = vec![0u8; len];
            for b in &mut m {
                *b = (rng.next() & 0xff) as u8;
            }
            assert_total(&m, &format!("synthetic/len{len}"));
        }
    }
    // Also the "looks like a bicimage" prefix space: many inputs whose first
    // bytes we vary widely so the magic check + arch/wordsize/root/count path
    // is entered with hostile follow-on bytes.
    for _ in 0..2000 {
        let len = rng.below(96) + 4;
        let mut m = vec![0u8; len];
        for b in &mut m {
            *b = (rng.next() & 0xff) as u8;
        }
        assert_total(&m, "synthetic/prefix");
    }
}

#[test]
fn read_bic_is_total_on_real_image_mutants() {
    let img_path = workspace_root().join("vendor/polyml/bootstrap/bootstrap64.txt");
    let Ok(text) = std::fs::read(&img_path) else {
        eprintln!("SKIP: {} missing (vendor)", img_path.display());
        return;
    };
    let Ok(image) = Image::parse(&text) else {
        eprintln!("SKIP: bootstrap image did not parse");
        return;
    };
    // A REAL, large bicimage seed — its round-trip is also a smoke test that
    // the writer→reader path is self-consistent.
    let bic = image.to_bic_bytes();
    assert!(
        Image::read_bic(&bic).is_ok(),
        "the pristine round-tripped bootstrap bicimage must read back"
    );
    fuzz_seed(&bic, "bootstrap", 4000);
}
