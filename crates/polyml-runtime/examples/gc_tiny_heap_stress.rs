//! Adversarial GC stress harness — drives the real bootstrap entry point
//! through `run_until` with a DELIBERATELY TINY alloc space, so the
//! auto-GC fires on nearly every allocation burst (the maximally
//! adversarial Cheney-copy stress the CLI's 1.6 GB heap cannot reach).
//!
//! HISTORY (task #109). This harness originally SEGV'd deterministically
//! under `POLYML_GC_AUDIT=1 POLYML_GC_THRESHOLD=50 ... 131072 2000000`,
//! and the GC-soak report (commit 77b6141) hypothesised the cause was
//! stale below-sp stack pointers dangling after a collect. Forensics (gdb + a from-space tripwire) showed the
//! ACTUAL proximate cause was different: this harness FAILED to register
//! the image's MUTABLE space as a GC root. The bootstrap image's mutable
//! objects (the global namespace hashtable, refs, arrays) hold pointers
//! into the runtime alloc-space; with the mutable root unregistered the
//! GC could not forward those pointers, so an image object's word-0
//! dangled into freed from-space and an `INDIRECT_LOCAL_B0` later
//! dereferenced it. The CLI ALWAYS registers this root (main.rs:340-353);
//! omitting it here hid a genuine root and is the bug this harness was
//! actually exercising. It now registers the root, exactly as the CLI
//! does, and runs clean.
//!
//! Two real, INDEPENDENT facts the investigation confirmed:
//!  1. The SEGV cause = the unregistered image-mutable root (fixed below).
//!  2. Even with the root registered, a collect leaves stale from-space
//!     pointers BELOW sp (44 here; ~26831 on a real basis load) — the
//!     free/garbage region drop_n/RESET leave behind. Those are latent
//!     dangling pointers (overwritten before re-deref in practice). The
//!     GC now SCRUBS [0, sp) to Tagged(0) on every collect (see
//!     Interpreter::gc), eliminating that hazard and making the widened
//!     `POLYML_GC_AUDIT` ([0, len)) scan honest.
//!
//! Heap size in WORDS is the first CLI arg; max steps is the second.

use std::path::PathBuf;
use std::sync::Arc;

use polyml_image::Image;
use polyml_runtime::{Interpreter, PolyWord, RtsTable, load_image, patch_entry_points};

fn main() {
    let heap_words: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(256 * 1024); // 256K words = 2 MB default — tiny

    let max_steps: u64 = std::env::args()
        .nth(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or(2_000_000);

    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../vendor/polyml/bootstrap/bootstrap64.txt");
    let bytes = std::fs::read(&root).expect("read bootstrap64.txt");
    let image = Image::parse(&bytes).expect("parse");
    let mut loaded = load_image(&image).expect("load_image");

    let rts = Arc::new(RtsTable::new());
    let (patched, missing) = patch_entry_points(&mut loaded, &rts);
    eprintln!(
        "RTS patch: {patched} resolved, {} unresolved",
        missing.len()
    );

    let root_closure_word = PolyWord::from_ptr(loaded.root);
    let code_obj = unsafe { *loaded.root };
    let code_obj_ptr = code_obj.as_ptr::<PolyWord>();

    eprintln!(
        "TINY-HEAP STRESS: heap={heap_words} words ({} MB), max_steps={max_steps}",
        heap_words * 8 / (1024 * 1024)
    );

    // Match the CLI's 1M-word stack so a tiny *heap* is the only
    // adversarial variable (an undersized stack is a separate axis).
    // Register the image's MUTABLE space as a GC root, exactly as the
    // CLI does (main.rs:340-353). The image's mutable objects (the
    // global namespace hashtable, refs, arrays) hold pointers into the
    // runtime alloc-space; without registering them the GC cannot
    // forward those pointers and they dangle after a collect.
    let image_mut_ptr = loaded.mutable.iter().next().map(|w| w as *const PolyWord);
    let image_mut_len = loaded.mutable.used_words();
    let mut interp = unsafe { Interpreter::from_code_object(1024 * 1024, code_obj_ptr) }
        .with_default_alloc_space_words(heap_words)
        .with_rts(rts);
    if let Some(p) = image_mut_ptr {
        interp = interp.with_image_mutable_root(p, image_mut_len);
    }
    interp.test_seed_return_sentinel();
    interp.test_seed_top(root_closure_word);

    let (steps, outcome) = interp.run_until(max_steps);
    match outcome {
        Ok(res) => {
            eprintln!("Executed {steps} step(s). Result: {res:?}");
        }
        Err(e) => {
            eprintln!("HALT after error: {e:?} (executed {steps} step(s))");
        }
    }
}
