//! AUDIT REPRO (finding index 3): `read_pc_const` (interpreter/mod.rs:4489)
//! performs an UNBOUNDED PC-relative read into the constant pool of the
//! current code object. Unlike `fetch_u8` (which bounds-checks against
//! `code_end`), `read_pc_const` trusts the CONST_ADDR / CALL_CONST_ADDR
//! immediate offset to land within the object's allocation.
//!
//! `code_end` is set to `consts_start` (mod.rs:4354), so the const pool
//! lives in `[code_end, object_end)` — i.e. the read DELIBERATELY targets
//! memory past `code_end`. The only correct bound is the object's true end
//! (`code_start + n_words*8`), and nothing checks it. A corrupted/adversarial
//! immediate (or a wild `code_end` from finding 2) makes the read run OOB
//! past the object's allocation.
//!
//! These tests are the "build a repro" deliverable. They are `#[ignore]` by
//! default because the SIGSEGV case intentionally crashes a child process.
#![allow(
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation,
    clippy::unusual_byte_groupings,
    clippy::cast_ptr_alignment,
    clippy::items_after_statements,
    clippy::undocumented_unsafe_blocks
)]

use polyml_runtime::interpreter::opcodes::*;
use polyml_runtime::space::{MemorySpace, SpaceKind};
use polyml_runtime::{Interpreter, PolyWord, StepResult};

/// Mirror of the in-crate test helper `make_code_object`: bytecode bytes
/// followed by `constants`, then the const-count word and the trailing
/// signed offset word.
fn make_code_object(
    space: &mut MemorySpace,
    code_bytes: &[u8],
    constants: &[PolyWord],
) -> *const PolyWord {
    let word = std::mem::size_of::<usize>();
    let code_words = code_bytes.len().div_ceil(word);
    let n_consts = constants.len();
    let total_words = code_words + n_consts + 2;
    let obj_ptr = space.alloc(total_words);
    unsafe {
        polyml_runtime::space::set_length_word(
            obj_ptr,
            total_words,
            polyml_runtime::length_word::F_CODE_OBJ,
        );
        let dst = obj_ptr.cast::<u8>();
        std::ptr::copy_nonoverlapping(code_bytes.as_ptr(), dst, code_bytes.len());
        let pad = code_bytes.len().next_multiple_of(word) - code_bytes.len();
        if pad > 0 {
            std::ptr::write_bytes(dst.add(code_bytes.len()), 0, pad);
        }
        obj_ptr.add(code_words).write(PolyWord::from_bits(n_consts));
        for (i, c) in constants.iter().enumerate() {
            obj_ptr.add(code_words + 1 + i).write(*c);
        }
        #[allow(clippy::cast_possible_wrap)]
        let const_addr_index = (code_words + 1) as isize;
        let total_isize = total_words as isize;
        let word_isize = word as isize;
        let offset_bytes = (const_addr_index - total_isize) * word_isize;
        obj_ptr
            .add(total_words - 1)
            .write(PolyWord::from_bits(offset_bytes as usize));
    }
    obj_ptr.cast_const()
}

/// Case 1 (observable, no crash): show that with a corrupted immediate the
/// CONST_ADDR8_0 read returns a value that is NOT in the object's declared
/// const pool — proof the read is unbounded (it walked past `code_end` and
/// past the single declared constant, into whatever follows the object).
///
/// We plant a recognisable sentinel word in the MemorySpace AFTER the code
/// object and aim the immediate at it. A correct (bounds-checked) opcode
/// could never reach this slot — it is outside the code object entirely.
#[test]
fn read_pc_const_reads_past_object_end() {
    let word = std::mem::size_of::<usize>();
    let mut code_space = MemorySpace::new(64, SpaceKind::Code);

    // code object: [CONST_ADDR8_0, imm, NOP.., RETURN_B 0] + 1 const (tagged 42)
    // After fetching opcode+imm, self.pc = code_start + 2.
    // Read addr = code_start + 2 + imm + 3*word.
    let mut code_bytes = vec![INSTR_CONST_ADDR8_0, 0 /*imm patched below*/];
    code_bytes.resize(28, INSTR_NO_OP);
    code_bytes.push(INSTR_RETURN_B);
    code_bytes.push(0);
    let code_words = code_bytes.len().div_ceil(word); // 4
    let total_words = code_words + 1 /*const*/ + 2; // 7
    // The object spans code_start .. code_start + total_words*word.
    // Object end (exclusive) = code_start + total_words*word = +56 bytes.
    // We want to read a slot PAST the object end. Allocate a sentinel
    // word right after the object and aim at it.
    let code = make_code_object(&mut code_space, &code_bytes, &[PolyWord::tagged(42)]);

    // The next alloc lands immediately after the code object in this bump space.
    let sentinel_ptr = code_space.alloc(1);
    let sentinel_val = PolyWord::tagged(0x5EED); // recognisable, in-bounds-of-space but OUTSIDE the code object
    unsafe { sentinel_ptr.write(sentinel_val) };

    // Compute the immediate that targets the sentinel:
    //   sentinel_addr = code_start + 2 + imm + 3*word
    let code_start = code as usize;
    let sentinel_addr = sentinel_ptr as usize;
    let want = sentinel_addr as isize - (code_start as isize + 2 + 3 * word as isize);
    assert!(
        (0..=255).contains(&want),
        "sentinel offset {want} not encodable in a u8 immediate; bump-allocator layout changed"
    );
    // Patch the immediate (byte index 1 of the code).
    unsafe { (code as *mut u8).add(1).write(want as u8) };

    // Sanity: the sentinel really IS past the object's declared end.
    let object_end = code_start + total_words * word;
    assert!(
        sentinel_addr >= object_end,
        "sentinel ({sentinel_addr:#x}) must be at/after object end ({object_end:#x})"
    );

    let mut interp = unsafe { Interpreter::from_code_object(64, code) };
    interp.seed_return_sentinel();
    interp.seed_push(PolyWord::ZERO);

    match interp.run() {
        Ok(StepResult::Returned(v)) => {
            // A bounds-checked opcode would never return a value sourced
            // from outside the code object. The fact that we get the
            // sentinel back proves read_pc_const read past `code_end` AND
            // past the object end — the OOB read.
            assert_eq!(
                v.0, sentinel_val.0,
                "expected the OOB sentinel {:#x}, got {:#x} — \
                 if this differs the layout changed, but a non-42 value \
                 still proves the read left the const pool",
                sentinel_val.0, v.0
            );
            eprintln!(
                "OOB CONFIRMED: CONST_ADDR8_0 returned {:#x} sourced from \
                 {:#x}, which is {} bytes PAST the code object's end {:#x}",
                v.0,
                sentinel_addr,
                sentinel_addr - object_end,
                object_end
            );
        }
        other => panic!("unexpected: {other:?}"),
    }
}

/// Case 2 (true memory-unsafety, runs in a child process): place a code
/// object at the tail of a mapped page whose SUCCESSOR page is `PROT_NONE`,
/// then aim a CONST_ADDR read into the guard page. A bounds-checked opcode
/// would reject the immediate; `read_pc_const` follows it and faults.
///
/// The fault is the proof that the unbounded read is genuine UB (a wild
/// load), not merely a "garbage but mapped" read. We fork via a re-exec of
/// the test binary so the SIGSEGV is contained.
#[test]
#[ignore = "intentionally SIGSEGVs; run explicitly to demonstrate the UB"]
fn read_pc_const_guard_page_segv_child() {
    // When invoked with this env var set, BE the crashing child.
    if std::env::var("PCCONST_OOB_CHILD").is_ok() {
        unsafe { crash_in_guard_page() };
        // Unreachable if the read faulted; if we get here the bound held.
        eprintln!("NO FAULT: the OOB read landed in mapped memory (bound held?)");
        std::process::exit(0);
    }

    // Parent: re-exec ourselves as the child and assert it died on SIGSEGV.
    let exe = std::env::current_exe().expect("current_exe");
    let status = std::process::Command::new(exe)
        .args([
            "--ignored",
            "--exact",
            "read_pc_const_guard_page_segv_child",
        ])
        .env("PCCONST_OOB_CHILD", "1")
        .status()
        .expect("spawn child");

    use std::os::unix::process::ExitStatusExt;
    let sig = status.signal();
    eprintln!("child exit: code={:?} signal={:?}", status.code(), sig);
    assert_eq!(
        sig,
        Some(libc::SIGSEGV),
        "expected child to die on SIGSEGV from the OOB read; got {status:?}"
    );
}

/// SAFETY: maps two pages, makes the second `PROT_NONE`, lays a code object
/// in the first page so a CONST_ADDR read targets the guard page.
unsafe fn crash_in_guard_page() {
    let page = 4096usize;
    let word = std::mem::size_of::<usize>();
    // Two pages: [data | guard]. Map RW, then protect the guard page.
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

    // Lay the code object so its body ends well before the page boundary,
    // but a CONST_ADDR read with a large immediate reaches into the guard.
    // Object: length word at [base+page - obj_span - 8] is awkward; simplest
    // is to place the object near the page start and use a big immediate.
    //
    // We need an 8-aligned object pointer; base from mmap is page-aligned.
    let obj_ptr = base.cast::<PolyWord>();

    // Build: [CONST_ADDR16_8, off_lo, off_hi, idx, RETURN_B, 0] + 1 const.
    // CONST_ADDR16_8: after fetching opcode + u16 off + u8 idx, self.pc =
    // code_start + 4. Read addr = code_start + 4 + off + (idx+3)*word.
    // Aim into the guard page: target = guard + 16 (well inside PROT_NONE).
    let code_start = obj_ptr as usize;
    let target = guard as usize + 16;
    let idx: usize = 0;
    let off = target as isize - (code_start as isize + 4 + (idx as isize + 3) * word as isize);
    assert!(
        (0..=0xFFFF).contains(&off),
        "guard offset {off} not encodable in u16; layout assumption broke"
    );

    let code_bytes: Vec<u8> = vec![
        INSTR_CONST_ADDR16_8,
        (off as u16 & 0xFF) as u8,
        ((off as u16 >> 8) & 0xFF) as u8,
        idx as u8,
        INSTR_RETURN_B,
        0,
    ];
    let code_words = code_bytes.len().div_ceil(word);
    let n_consts = 1usize;
    let total_words = code_words + n_consts + 2;

    unsafe {
        polyml_runtime::space::set_length_word(
            obj_ptr,
            total_words,
            polyml_runtime::length_word::F_CODE_OBJ,
        );
        std::ptr::copy_nonoverlapping(code_bytes.as_ptr(), obj_ptr.cast::<u8>(), code_bytes.len());
        // const-count word + 1 dummy const + trailing offset (so the call
        // setup's const_segment_for_code yields a sane code_end).
        obj_ptr.add(code_words).write(PolyWord::from_bits(n_consts));
        obj_ptr.add(code_words + 1).write(PolyWord::tagged(42));
        #[allow(clippy::cast_possible_wrap)]
        let const_addr_index = (code_words + 1) as isize;
        let offset_bytes = (const_addr_index - total_words as isize) * word as isize;
        obj_ptr
            .add(total_words - 1)
            .write(PolyWord::from_bits(offset_bytes as usize));
    }

    let mut interp = unsafe { Interpreter::from_code_object(64, obj_ptr.cast_const()) };
    interp.seed_return_sentinel();
    interp.seed_push(PolyWord::ZERO);

    // This run drives CONST_ADDR16_8 -> read_pc_const into the guard page.
    let _ = interp.run();
}
