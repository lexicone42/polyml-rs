//! REPRO for audit finding index 15:
//! crates/polyml-runtime/src/export.rs:192-204 (build_code: the
//! `for i in 0..count { *cp.add(i) }` loop over an attacker-controlled
//! `count` returned by `const_segment_for_code`).
//!
//! Thesis under test: a CODE object whose trailing offset word and
//! count word are corrupt makes `const_segment_for_code` return an
//! arbitrary `(cp, count)` with NO release-time bounds check, and
//! `build_code` then loops `0..count` reading `*cp.add(i)` — an
//! unbounded OOB read driven directly by a heap word. The same
//! `(cp, count)` feeds gc.rs::scan_object's F_CODE_OBJ branch.
//!
//! This test is NOT wired into regression.sh; it is an adversarial
//! probe. Run with:
//!   cargo test -p polyml-runtime --test export_corrupt_code_oob_repro -- --nocapture
//!   (release: add --release; under ASAN it flags the over-read)

use polyml_runtime::length_word::{self, F_CODE_OBJ};
use polyml_runtime::poly_word::PolyWord;
use polyml_runtime::space::{MemorySpace, set_length_word};
use polyml_runtime::{SpaceKind, export};

/// Build a CODE object with a controllable (offset, count) const-segment
/// trailer and return (space, body_ptr).
///
/// Layout we lay down in the body (n words):
///   body[0]            : bytecode word (filler)
///   body[1]            : the const-count word  (cp will point at body[2])
///   body[2 .. n-1]     : "constants" (filler)
///   body[n-1]          : trailing signed byte offset back to cp
///
/// const_segment_for_code computes:
///   last_word_ptr = body + (n-1)
///   offset_bytes  = body[n-1] (signed)
///   cp            = last_word_ptr + 1 + offset_bytes/8
///   count         = cp[-1]
fn build_corrupt_code(
    n: usize,
    cp_word_index: usize, // where we want cp to land (cp[-1] = count word)
    count: usize,
) -> (MemorySpace, *const PolyWord) {
    // Allocate generously so the object + a little slack are in one space.
    let mut space = MemorySpace::new(4096, SpaceKind::Mutable);
    let body = space.alloc(n);
    unsafe {
        set_length_word(body, n, F_CODE_OBJ);
        // Fill the body with TAGGED ints (LSB=1) so value_for treats each
        // in-body const word as an immediate, not a pointer — this isolates
        // THIS finding (the unbounded `0..count` OOB read past the body)
        // from the separate in-body type-confusion deref class. Any word
        // read PAST the body is whatever the heap holds there (likely
        // pointer-shaped zeros from the backing buffer), so an unclamped
        // loop wild-derefs; a clamped loop reads only these tagged words.
        for i in 0..n {
            body.add(i).write(PolyWord::tagged(0x1000 + i as isize));
        }
        // Put the count where cp[-1] will read it.
        body.add(cp_word_index - 1)
            .write(PolyWord::from_bits(count));
        // Compute the trailing offset so cp = body + cp_word_index.
        //   cp = last_word_ptr + 1 + offset/8
        //   body + cp_word_index = (body + n-1) + 1 + offset/8
        //   offset/8 = cp_word_index - n
        let offset_words = cp_word_index as isize - n as isize;
        let offset_bytes = (offset_words * std::mem::size_of::<usize>() as isize) as usize;
        body.add(n - 1).write(PolyWord::from_bits(offset_bytes));
    }
    (space, body.cast_const())
}

#[test]
fn const_segment_returns_attacker_controlled_count_unchecked() {
    // A valid-shaped n=8 code object whose count word is set to a huge
    // value. const_segment_for_code returns that count VERBATIM with no
    // bounds check in release; build_code's loop would scan that many
    // words off cp.
    let n = 8;
    let cp_idx = 2; // cp -> body[2], count word at body[1]
    let huge: usize = 1_000_000;
    let (space, body) = build_corrupt_code(n, cp_idx, huge);

    let (cp, count) = unsafe { length_word::const_segment_for_code(body) };

    let obj_lo = body as usize;
    let obj_hi = obj_lo + n * std::mem::size_of::<usize>();
    let cp_addr = cp as usize;
    let scan_end = cp_addr + count * std::mem::size_of::<usize>();

    eprintln!(
        "object body = [0x{obj_lo:016x}, 0x{obj_hi:016x}) ({} bytes)\n\
         const_segment_for_code returned cp=0x{cp_addr:016x} count={count}\n\
         build_code would read up to 0x{scan_end:016x} \
         (= {} bytes PAST the object body)",
        n * std::mem::size_of::<usize>(),
        scan_end.saturating_sub(obj_hi),
    );

    // The hazard: count is returned verbatim (no clamp to the object
    // body), and cp+count*8 runs far past the object's allocation.
    assert_eq!(
        count, huge,
        "const_segment_for_code returned an unclamped attacker-controlled count"
    );
    assert!(
        scan_end > obj_hi,
        "the const-scan window extends past the object body \
         (this is the OOB read build_code/scan_object would perform)"
    );

    drop(space);
}

#[test]
fn build_code_via_snapshot_is_now_bounded() {
    // Drive the ACTUAL path the finding flags: export::snapshot ->
    // build_object -> build_code -> the `for i in 0..count` loop.
    //
    // BEFORE the fix this SIGSEGV'd: with `count = 64` the loop read 64
    // const words off `cp`, far past the 8-word object body; one of those
    // out-of-body words was pointer-shaped, `value_for` interned it, and
    // `drain` then dereferenced `*(addr-1)` on the wild address -> signal
    // 11. (Demonstrated; this test file's git history / the audit notes
    // record the crash.)
    //
    // AFTER the fix build_code clamps `count` to the words that actually
    // fit inside the object body (`n` words), so the loop is provably
    // in-bounds and snapshot returns cleanly — no OOB read, no SEGV.
    //
    // We make the corrupt code object the ROOT so snapshot() walks it.
    let n = 8;
    let cp_idx = 2; // cp -> body[2]; so 6 const words fit (body[2..8])
    let oob_count = 64; // attacker asks for 64 -> would be 58 words OOB
    let (space, body) = build_corrupt_code(n, cp_idx, oob_count);

    let root = PolyWord::from_ptr(body);
    // SAFETY: body points at a (deliberately malformed) F_CODE_OBJ. The
    // fix guarantees build_code reads only in-body const words, so this is
    // sound even on the corrupt object.
    let snap = unsafe { export::snapshot(root) };

    let code_obj = &snap.objects[snap.root as usize];
    match &code_obj.body {
        polyml_image::pexport::ObjectBody::Code { constants, .. } => {
            // cp lands at body[2], so words body[2..8] = 6 words fit.
            let max_in_body = n - cp_idx;
            eprintln!(
                "snapshot built a Code object with {} constants (clamped from \
                 the attacker-supplied count={oob_count} to the {max_in_body} \
                 words that fit inside the {n}-word body) — no OOB read",
                constants.len(),
            );
            assert!(
                constants.len() <= max_in_body,
                "build_code read past the object body: {} constants > {max_in_body} in-body words",
                constants.len(),
            );
            assert!(
                constants.len() < oob_count,
                "build_code did NOT clamp the attacker-controlled count \
                 (read {} of {oob_count}) — the OOB-read bound is missing",
                constants.len(),
            );
        }
        other => panic!("expected Code body, got {other:?}"),
    }

    drop(space);
}

#[test]
fn build_code_via_snapshot_huge_count_does_not_oob() {
    // The wild case: a count of 1,000,000 (would scan ~8 MB past the
    // object). With the clamp, build_code reads only the in-body words and
    // returns cleanly instead of walking off the heap.
    let n = 8;
    let cp_idx = 2;
    let huge = 1_000_000;
    let (space, body) = build_corrupt_code(n, cp_idx, huge);

    let root = PolyWord::from_ptr(body);
    // SAFETY: see above — the clamp keeps reads in-bounds.
    let snap = unsafe { export::snapshot(root) };
    match &snap.objects[snap.root as usize].body {
        polyml_image::pexport::ObjectBody::Code { constants, .. } => {
            assert!(
                constants.len() <= n - cp_idx,
                "huge count not clamped: {} constants",
                constants.len()
            );
            eprintln!(
                "huge count={huge} clamped to {} in-body const words — no wild scan",
                constants.len()
            );
        }
        other => panic!("expected Code body, got {other:?}"),
    }
    drop(space);
}
