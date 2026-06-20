//! AUDIT REPRO (finding index 5): `do_call` (interpreter/mod.rs:4305-4352)
//! derefs a closure's word0 as a CODE pointer with NO type check.
//!
//! `do_call` validates that the CLOSURE itself is a data pointer + 8-aligned
//! (mod.rs:4068), and rejects a self-pointer (mod.rs:4312). But it then does:
//!
//!     let code_word = unsafe { *closure_ptr };          // word0
//!     let new_code_obj = code_word.as_ptr::<PolyWord>();
//!     // ... self-pointer guard only ...
//!     let (consts_start, _) =
//!         unsafe { length_word::const_segment_for_code(new_code_obj) };
//!
//! with NO check that
//!   (a) `code_word.is_data_ptr()` — a tagged int in word0 gives a garbage addr;
//!   (b) `new_code_obj` actually points at an F_CODE_OBJ — a closure whose
//!       word0 points at an Ordinary tuple (the lf_ref_52 type-confusion shape,
//!       but as a closure's code address) makes `const_segment_for_code` read
//!       the tuple's trailing word as a SIGNED code-offset and compute a WILD
//!       `code_end` (the bound for every subsequent bytecode fetch).
//!
//! `const_segment_for_code`'s `debug_assert!(is_code_object)` /
//! `debug_assert!(n_words >= 2)` (length_word.rs:144-149) are COMPILED OUT in
//! release, so the wild pointer is produced silently in production builds.
//!
//! The loader's `runnable` check (loader.rs:260-275, gated by
//! `main.rs::ensure_runnable`) validates ONLY the ROOT closure's code address.
//! A NON-root closure reached during execution is never type-checked — so an
//! untrusted image whose root passes `ensure_runnable` but whose nested closure
//! is type-confused reaches this unguarded deref. This is the documented open
//! residual (lf_ref_52 / task #96), here surfacing on the closure-call side as
//! a SIBLING of the GC use-after-free class (a type-confused pointer rather
//! than a dangling one).
//!
//! These tests are the "build a repro" deliverable. Case 2 is `#[ignore]` by
//! default because it intentionally SIGSEGVs a child process.
#![allow(
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation,
    clippy::undocumented_unsafe_blocks
)]

use polyml_runtime::length_word::{F_CLOSURE_OBJ, F_CODE_OBJ};
use polyml_runtime::space::{MemorySpace, SpaceKind, set_length_word};
use polyml_runtime::{Interpreter, PolyWord};

/// Build an Ordinary (word) tuple in immutable space whose body words are
/// `vals`. This is NOT a code object — its length word carries flags 0.
fn make_ordinary(space: &mut MemorySpace, vals: &[PolyWord]) -> *const PolyWord {
    let obj = space.alloc(vals.len());
    unsafe {
        set_length_word(obj, vals.len(), 0 /* word object */);
        for (i, v) in vals.iter().enumerate() {
            obj.add(i).write(*v);
        }
    }
    obj.cast_const()
}

/// Build a 1-word closure object whose word0 is `word0` verbatim — used to
/// plant a type-confused code address.
fn make_closure_word0(space: &mut MemorySpace, word0: PolyWord) -> *const PolyWord {
    let obj = space.alloc(1);
    unsafe {
        set_length_word(obj, 1, F_CLOSURE_OBJ);
        obj.add(0).write(word0);
    }
    obj.cast_const()
}

/// A real, valid code object: `RETURN_B 0` (opcode 0x52, then a 0 byte) plus an
/// empty const pool, laid out exactly as the loader does. Used only as the
/// caller's "current" code object so the interpreter has a valid PC to start.
fn make_trivial_code(space: &mut MemorySpace) -> *const PolyWord {
    let word = std::mem::size_of::<usize>();
    // RETURN_B 0  (do_call needs a valid current code segment to push retPC
    // against; we never actually RETURN here — we invoke do_call directly).
    let code_bytes: [u8; 2] = [0x52, 0x00];
    let code_words = code_bytes.len().div_ceil(word); // 1
    let total_words = code_words + 0 /*consts*/ + 2; // 3
    let obj = space.alloc(total_words);
    unsafe {
        set_length_word(obj, total_words, F_CODE_OBJ);
        std::ptr::copy_nonoverlapping(code_bytes.as_ptr(), obj.cast::<u8>(), code_bytes.len());
        let pad = code_bytes.len().next_multiple_of(word) - code_bytes.len();
        if pad > 0 {
            std::ptr::write_bytes(obj.cast::<u8>().add(code_bytes.len()), 0, pad);
        }
        // const count = 0
        obj.add(code_words).write(PolyWord::from_bits(0));
        // trailing offset so const pool == slot code_words+1
        let const_addr_index = (code_words + 1) as isize;
        let offset_bytes = (const_addr_index - total_words as isize) * word as isize;
        obj.add(total_words - 1)
            .write(PolyWord::from_bits(offset_bytes as usize));
    }
    obj.cast_const()
}

/// Case 1 (observable, no crash): `do_call` ACCEPTS a closure whose word0
/// points at a non-code Ordinary tuple, and computes a `code_end` derived from
/// the tuple's data (NOT bounded to the object) — proving the missing type
/// check. A correct implementation would reject it (NotAClosure) before the
/// unsafe code-pointer deref.
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "const_segment_for_code's debug_assert!(is_code_object) PANICS in \
              debug (a debug-only tripwire); the bug — silent acceptance + wild \
              code_end — is release-only. Run in release: cargo test --release"
)]
fn do_call_accepts_type_confused_closure_and_corrupts_code_end() {
    let word = std::mem::size_of::<usize>();
    let mut code_space = MemorySpace::new(64, SpaceKind::Code);
    let mut data_space = MemorySpace::new(64, SpaceKind::Immutable);

    let caller_code = make_trivial_code(&mut code_space);

    // The type-confused target: a 2-word Ordinary tuple. Its body words are
    // ATTACKER-CONTROLLED. const_segment_for_code will read the LAST word
    // (slot 1) as a signed byte-offset. We plant a small, benign-but-WRONG
    // value (a tagged int) to keep this case non-crashing while still proving
    // the type confusion: the resulting code_end is NOT this object's end.
    //
    // Slot 0 = arbitrary tagged data, slot 1 = "offset" word = tagged(0)
    // (i.e. raw bits 0 after... actually tagged(0) has bit0 set; we want a raw
    // bits value, so use from_bits to control the exact offset word).
    let tuple = make_ordinary(
        &mut data_space,
        &[
            PolyWord::tagged(0x1111),
            PolyWord::from_bits(0), /* offset = 0 */
        ],
    );

    // A closure whose word0 = pointer to the tuple. is_data_ptr() is TRUE for
    // this (it is a valid heap pointer), and it is NOT the self-pointer, so
    // do_call's two guards both pass — yet the target is the wrong TYPE.
    let bad_closure = make_closure_word0(&mut code_space, PolyWord::from_ptr(tuple));

    let mut interp = unsafe { Interpreter::from_code_object(64, caller_code) };
    interp.test_seed_return_sentinel();
    interp.test_seed_top(PolyWord::ZERO);

    // Record the tuple's true end for comparison.
    let tuple_start = tuple as usize;
    let tuple_end = tuple_start + 2 * word; // 2-word body

    let res = interp.test_invoke_do_call(PolyWord::from_ptr(bad_closure));

    // (a) do_call did NOT reject the type-confused closure: NO type check fired.
    assert!(
        res.is_ok(),
        "do_call rejected the type-confused closure (a fix may have landed): {res:?}"
    );

    // (b) The computed code_end is derived from the tuple's CONTENTS, not from
    // its real allocation bounds. With offset word = 0, const_segment_for_code
    // returns cp = &tuple[2] (one past the body) and code_end = cp. The point:
    // code_end is whatever the (attacker-controlled) trailing word dictates —
    // it is NOT validated against the object's length word. We show code_end is
    // sourced from inside/after the tuple, treating a NON-code object as code.
    let (code_start, code_end) = interp.peek_code_seg_for_debug();
    let cs = code_start as usize;
    let ce = code_end as usize;
    assert_eq!(
        cs, tuple_start,
        "code_start should be the tuple address (the type-confused 'code object')"
    );
    eprintln!(
        "TYPE CONFUSION CONFIRMED: do_call treated a NON-code Ordinary tuple \
         (addr {tuple_start:#x}, true end {tuple_end:#x}) as a code object; \
         code_start={cs:#x} code_end={ce:#x} — the PC bound for the next \
         function is now derived from attacker-controlled tuple bytes, NOT a \
         validated code-object trailer."
    );
}

/// Case 1b: the SAME bug with a TAGGED INT in word0 (not even a pointer).
/// `do_call` checks the closure is a pointer, but NOT that word0 is. A tagged
/// int in word0 makes `new_code_obj` an odd/garbage address and
/// `const_segment_for_code` derefs `garbage - 1`. We keep this observable by
/// not running far enough to fault on a mapped-garbage address; the assertion
/// is simply that do_call accepts it (release) — in DEBUG the debug_assert in
/// const_segment_for_code may catch it, so this case is release-only-meaningful.
#[test]
#[ignore = "tagged-int word0 -> const_segment_for_code derefs a garbage addr; \
            crash-vs-mapped-read is heap-layout-dependent (nondeterministic), \
            and a debug_assert catches it in debug — run explicitly in release"]
fn do_call_accepts_tagged_int_in_word0() {
    let mut code_space = MemorySpace::new(64, SpaceKind::Code);
    let caller_code = make_trivial_code(&mut code_space);

    // Closure whose word0 is a TAGGED INT (bit0 set) — not a pointer at all.
    // We pick a value whose (as_ptr & !1) lands at a small but *mapped* address
    // is impossible to guarantee; instead choose a value that points back into
    // our own code_space so the subsequent deref reads mapped (garbage) memory
    // rather than faulting. word0 = from_bits(caller_code_addr | 1).
    let aliased = (caller_code as usize) | 1; // looks tagged, masks to code addr
    let bad_closure = make_closure_word0(&mut code_space, PolyWord::from_bits(aliased));

    let mut interp = unsafe { Interpreter::from_code_object(64, caller_code) };
    interp.test_seed_return_sentinel();
    interp.test_seed_top(PolyWord::ZERO);

    let res = interp.test_invoke_do_call(PolyWord::from_ptr(bad_closure));
    assert!(
        res.is_ok(),
        "do_call rejected a tagged-int word0 (a fix may have landed): {res:?}"
    );
    eprintln!(
        "NO is_data_ptr() CHECK ON word0 CONFIRMED: do_call accepted a closure \
         whose word0 = {aliased:#x} (bit0 set, i.e. a tagged int), treating its \
         masked address as a code object."
    );
}

/// Case 2 (true memory-unsafety, runs in a child process): make the
/// type-confused tuple's trailing word a LARGE offset so `const_segment_for_code`
/// computes a `cp` inside a `PROT_NONE` guard page; the `count = *(cp-1)` read
/// faults. The fault proves the unbounded deref is genuine UB, not a benign
/// "garbage but mapped" read. We re-exec the test binary so the SIGSEGV is
/// contained.
#[test]
#[ignore = "intentionally SIGSEGVs; run explicitly to demonstrate the UB"]
fn do_call_type_confusion_guard_page_segv_child() {
    if std::env::var("DOCALL_TC_CHILD").is_ok() {
        unsafe { crash_via_type_confused_closure() };
        eprintln!("NO FAULT: the type-confused deref landed in mapped memory");
        std::process::exit(0);
    }

    let exe = std::env::current_exe().expect("current_exe");
    let status = std::process::Command::new(exe)
        .args([
            "--ignored",
            "--exact",
            "do_call_type_confusion_guard_page_segv_child",
        ])
        .env("DOCALL_TC_CHILD", "1")
        .status()
        .expect("spawn child");

    use std::os::unix::process::ExitStatusExt;
    let sig = status.signal();
    eprintln!("child exit: code={:?} signal={:?}", status.code(), sig);
    assert_eq!(
        sig,
        Some(libc::SIGSEGV),
        "expected child to die on SIGSEGV from the type-confused code-pointer \
         deref; got {status:?}"
    );
}

/// SAFETY: maps two pages ([data | guard], guard = PROT_NONE) and plants a
/// type-confused closure whose word0 points at a fake "code object" laid AT the
/// guard-page boundary: the object's length word sits in the readable data page
/// (so `length_word_of` succeeds), but its BODY (where `const_segment_for_code`
/// reads the n_words-th word as a signed code-offset, and where the interpreter
/// would fetch bytecode) is in the PROT_NONE guard page. `do_call` derefs it as
/// a code object and faults — the proof the type-confused code-pointer deref is
/// genuine UB, not a benign mapped read.
unsafe fn crash_via_type_confused_closure() {
    let page = 4096usize;
    let word = std::mem::size_of::<usize>();

    // Two pages: RW data + PROT_NONE guard.
    let base = unsafe {
        libc::mmap(
            std::ptr::null_mut(),
            2 * page,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
            -1,
            0,
        )
    };
    assert!(base != libc::MAP_FAILED, "mmap failed");
    let base = base.cast::<u8>();
    let guard = unsafe { base.add(page) };
    let r = unsafe { libc::mprotect(guard.cast(), page, libc::PROT_NONE) };
    assert_eq!(r, 0, "mprotect failed");

    // The fake "code object" body starts AT the guard page. Its length word
    // lives one word BELOW, in the readable data page. do_call will:
    //   1. const_segment_for_code(fake): length_word_of(fake) = *(guard - word)
    //      OK (data page). Then it reads n_words and (*last_word_ptr) where
    //      last_word_ptr = fake + (n_words - 1) — INSIDE the guard page -> FAULT.
    //   (If the optimizer somehow elides that read, the subsequent pc = fake
    //   and any bytecode fetch (*pc) also faults — both are the same UB.)
    let fake_code = guard.cast::<PolyWord>(); // body starts at the guard boundary
    eprintln!(
        "fake_code(body)={:#x} guard={:#x} length_word_at={:#x} (data page)",
        fake_code as usize,
        guard as usize,
        fake_code as usize - word
    );

    // Length word at fake_code[-1] = guard - word (data page, readable). Claim a
    // plausible code object so const_segment_for_code proceeds to read the body.
    unsafe {
        set_length_word(fake_code, 4 /* n_words */, F_CODE_OBJ);
    }

    // Closure object in the data page, word0 = pointer to the fake code body.
    let closure = unsafe { base.add(64).cast::<PolyWord>() };
    unsafe {
        set_length_word(closure, 1, F_CLOSURE_OBJ);
        closure
            .add(0)
            .write(PolyWord::from_ptr(fake_code.cast_const()));
    }

    // A trivial valid current code object so from_code_object has a PC.
    let mut code_space = MemorySpace::new(64, SpaceKind::Code);
    let caller_code = make_trivial_code(&mut code_space);

    let mut interp = unsafe { Interpreter::from_code_object(64, caller_code) };
    interp.test_seed_return_sentinel();
    interp.test_seed_top(PolyWord::ZERO);

    // do_call -> reads closure.word0 (= fake_code, in the guard page) -> treats
    // it as a code object -> const_segment_for_code reads the body word in the
    // guard page -> FAULT.
    let _ = interp.test_invoke_do_call(PolyWord::from_ptr(closure.cast_const()));
}
