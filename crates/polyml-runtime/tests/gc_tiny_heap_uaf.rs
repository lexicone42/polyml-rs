//! Regression fence for the GC below-sp use-after-free class (task #109).
//!
//! This is the committed form of the `gc_tiny_heap_stress` example: it
//! drives the real bootstrap entry point through `run_until` with a
//! DELIBERATELY TINY alloc space (so the Cheney collector fires on nearly
//! every allocation burst), under `POLYML_GC_AUDIT=1`, and asserts a clean
//! `Tagged(0)` return.
//!
//! What it pins (two INDEPENDENT correctness properties — both must hold):
//!
//!  1. NO SIGSEGV. Before the fix this configuration SEGV'd deterministically
//!     (exit 139) because the image's MUTABLE space was an UNREGISTERED GC
//!     root: an image mutable object's word held a pointer into alloc
//!     from-space, the collector could not forward it, it dangled when
//!     `collect` freed from-space, and a later `INDIRECT_LOCAL_B0`
//!     dereferenced freed memory. The harness now registers the image-mutable
//!     root exactly as the CLI does (`with_image_mutable_root`). A regression
//!     that drops that root — or any GC change that fails to forward a live
//!     root under heavy collection — makes this test SIGSEGV, which cargo
//!     reports as a failure of this test binary (the run is IN-PROCESS).
//!
//!  2. NO RESIDUAL FROM-SPACE POINTERS. Even with all roots registered, a
//!     collect used to leave stale from-space pointers in the below-sp
//!     free/garbage region (drop_n/RESET bump sp past them by design). Those
//!     are latent dangling pointers. `Interpreter::gc` now SCRUBS [0, sp) to
//!     `Tagged(0)` on every collect, and the (widened) `POLYML_GC_AUDIT`
//!     scanner now covers the full stack [0, len). The below-sp-residual
//!     class is fenced under that widened audit by the
//!     `gc_audit_smoke_basis_load` integration test (polyml-bin); THIS test
//!     pins property 1 (no UAF SIGSEGV under heavy collection) on the tiny
//!     heap the soak report used as its deterministic crash oracle.
//!
//! Heaps below the live working set (e.g. 32768 words) livelock rather than
//! crash, so this test uses 131072 words (1 MB) — the smallest heap the soak
//! report exercised that runs to completion — and a couple of clean smaller
//! heaps that still fit the working set.

use std::path::PathBuf;
use std::sync::Arc;

use polyml_image::pexport::Image;
use polyml_runtime::{Interpreter, PolyWord, RtsTable, StepResult, load_image, patch_entry_points};

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

/// Run the tiny-heap bootstrap stress once, in-process, with the image
/// mutable space registered as a GC root. Returns the final step result.
///
/// A use-after-free regression makes this SIGSEGV, crashing the test
/// process (cargo reports the binary as failed). A clean run returns
/// `Returned(Tagged(0))`.
fn run_tiny_heap_stress(heap_words: usize, max_steps: u64) -> StepResult {
    let path = workspace_root().join("vendor/polyml/bootstrap/bootstrap64.txt");
    let bytes = std::fs::read(&path).expect("read bootstrap64.txt");
    let image = Image::parse(&bytes).expect("parse");
    let mut loaded = load_image(&image).expect("load_image");

    let rts = Arc::new(RtsTable::new());
    let _ = patch_entry_points(&mut loaded, &rts);

    let root_closure_word = PolyWord::from_ptr(loaded.root);
    let code_obj = unsafe { *loaded.root };
    let code_obj_ptr = code_obj.as_ptr::<PolyWord>();

    // Register the image's MUTABLE space as a GC root, exactly as the CLI
    // does (main.rs:340-353). Omitting this is the exact bug the SEGV
    // reproducer exercised.
    let image_mut_ptr = loaded
        .mutable
        .iter()
        .next()
        .map(std::ptr::from_ref::<PolyWord>);
    let image_mut_len = loaded.mutable.used_words();
    let mut interp = unsafe { Interpreter::from_code_object(1024 * 1024, code_obj_ptr) }
        .with_default_alloc_space_words(heap_words)
        .with_rts(rts);
    if let Some(p) = image_mut_ptr {
        interp = interp.with_image_mutable_root(p, image_mut_len);
    }
    interp.test_seed_return_sentinel();
    interp.test_seed_top(root_closure_word);

    let (_steps, outcome) = interp.run_until(max_steps);
    outcome.expect("tiny-heap stress run errored")
}

/// The canonical reproducer heap (131072 words = 1 MB) must run to a clean
/// `Tagged(0)` WITHOUT SIGSEGV. Before the task #109 fix this SEGV'd 5/5.
#[test]
fn gc_tiny_heap_no_uaf_131072() {
    let path = workspace_root().join("vendor/polyml/bootstrap/bootstrap64.txt");
    if !path.exists() {
        eprintln!("SKIP: {} not present", path.display());
        return;
    }
    // Force the GC to fire aggressively so the below-sp scrub + the
    // tracked-root forwarding are exercised on nearly every burst.
    unsafe {
        std::env::set_var("POLYML_GC_THRESHOLD", "50");
        std::env::set_var("POLYML_GC_QUIET", "1");
    }
    let res = run_tiny_heap_stress(131_072, 2_000_000);
    assert!(
        matches!(res, StepResult::Returned(w) if w == PolyWord::tagged(0)),
        "tiny-heap (131072) stress must return Tagged(0), got {res:?}"
    );
}

/// Smaller heaps that still fit the working set must also complete cleanly.
#[test]
fn gc_tiny_heap_no_uaf_smaller_heaps() {
    let path = workspace_root().join("vendor/polyml/bootstrap/bootstrap64.txt");
    if !path.exists() {
        eprintln!("SKIP: {} not present", path.display());
        return;
    }
    unsafe {
        std::env::set_var("POLYML_GC_THRESHOLD", "50");
        std::env::set_var("POLYML_GC_QUIET", "1");
    }
    for heap in [65536usize, 98304] {
        let res = run_tiny_heap_stress(heap, 2_000_000);
        assert!(
            matches!(res, StepResult::Returned(w) if w == PolyWord::tagged(0)),
            "tiny-heap ({heap}) stress must return Tagged(0), got {res:?}"
        );
    }
}
