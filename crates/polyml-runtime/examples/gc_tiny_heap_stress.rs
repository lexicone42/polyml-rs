//! THROWAWAY adversarial GC stress harness (NOT for commit — diagnostic
//! reproducer for a GC use-after-free found 2026-06-18).
//!
//! Drives the real bootstrap entry point through `run_until` with a
//! DELIBERATELY TINY alloc space, so the auto-GC fires on nearly every
//! allocation burst — the maximally adversarial Cheney-copy stress that
//! the CLI (1.6 GB hardcoded heap Box) cannot reach.
//!
//! FINDING (deterministic SEGV / heap use-after-free):
//!
//!   POLYML_GC_AUDIT=1 POLYML_GC_THRESHOLD=50 \
//!     cargo run --release -p polyml-runtime --example gc_tiny_heap_stress -- 131072
//!
//!   -> "GC: 65538 -> 26276 words (40% retained)" then SIGSEGV. The
//!      POLYML_GC_AUDIT detector reports CLEAN (it scans only the LIVE
//!      stack region [sp, len)), yet the program faults dereferencing a
//!      pointer INSIDE the just-freed from-space range.
//!
//!   ROOT CAUSE: the GC forwards / audits only stack slots [sp, len).
//!   Slots BELOW sp (the "free"/garbage region that drop_n/RESET leave
//!   stale, see mod.rs drop_n) can still hold pointers into from-space.
//!   gc::collect's replace_storage() drops (frees) the from-space Box, so
//!   those below-sp pointers dangle. Under tiny-heap pressure a GC fires
//!   while such stale pointers exist below sp; a later sp-lowering op
//!   re-exposes one and the interpreter dereferences freed memory.
//!   Confirmed: scanning the FULL stack (0..len) in the audit finds 44
//!   residual from-space pointers below sp; the standard [sp, len) scan
//!   misses them. All REAL workloads (basis load, 7-stage chain @51
//!   cycles, isabelle_euler @11 cycles) keep the below-sp region clean at
//!   every collect, so the bug is LATENT there; and the CLI never builds
//!   a small enough alloc-space Box for the freed pages to be reused, so
//!   it is not reachable through any current `poly` invocation.
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
    let mut interp = unsafe { Interpreter::from_code_object(1024 * 1024, code_obj_ptr) }
        .with_default_alloc_space_words(heap_words)
        .with_rts(rts);
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
