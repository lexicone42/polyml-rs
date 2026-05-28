//! Cranelift-backed JIT for PolyML bytecode.
//!
//! Status: proof-of-concept stub. We compile one toy function
//! (`compile_identity`) to native code and call it from Rust to
//! prove the Cranelift build + JIT plumbing works in this
//! workspace. Real bytecode-to-IR translation comes next.
//!
//! ## Long-term plan
//!
//! - Each PolyML `Closure { code_addr }` will get a JIT'd entry
//!   point computed from the underlying code object's bytecode.
//! - The interpreter dispatches CALL into a JIT'd function by
//!   looking the closure's code pointer up in a JIT cache.
//! - Inside JIT'd code, opcodes we haven't yet translated trampoline
//!   back to the interpreter (one entry per uncompiled opcode).
//! - JIT'd code shares the same `Interpreter::stack` array as the
//!   interpreter for now; later we can spill registers more
//!   aggressively.

#![allow(clippy::missing_safety_doc)]

pub mod translate;
pub mod differential;

#[cfg(test)]
mod bench;

/// Walk all code objects in a [`polyml_runtime::LoadedImage`],
/// JIT-translate each one that the translator accepts, and install
/// every successful translation in the given interpreter's JIT
/// cache. Returns `(total_code_objects, jit_translated, installed)`.
///
/// Uses the same logic as `jit_bootstrap_run.rs` (the bisection test)
/// but with no filters: every translatable function gets installed
/// at the recommended `arity_init`.
///
/// # Safety
/// Reads code-object bytes from the loaded image — caller must ensure
/// the image is loaded and code spaces are populated.
pub fn install_all_jit_entries(
    jit: &mut Jit,
    loaded: &polyml_runtime::LoadedImage,
    interp: &mut polyml_runtime::Interpreter,
) -> (usize, usize, usize) {
    use polyml_runtime::{length_word, JitEntry, MemorySpace, PolyWord};
    let mut total = 0usize;
    let mut jit_ok = 0usize;
    let mut installed = 0usize;

    // Bisection support: env vars to narrow the install set.
    //   JIT_INSTALL_LIMIT=N — install only first N functions
    //   JIT_INSTALL_SKIP=N,M,K — skip these install indices (comma list)
    //   JIT_INSTALL_VERBOSE=1 — print each install with its index
    let install_limit: Option<usize> = std::env::var("JIT_INSTALL_LIMIT")
        .ok()
        .and_then(|s| s.parse().ok());
    let skip_indices: std::collections::HashSet<usize> = std::env::var("JIT_INSTALL_SKIP")
        .ok()
        .map(|s| {
            s.split(',')
                .filter_map(|x| x.trim().parse().ok())
                .collect()
        })
        .unwrap_or_default();
    let verbose = std::env::var("JIT_INSTALL_VERBOSE").is_ok();
    let mut install_idx = 0usize;

    fn walk_code_objects<F: FnMut(*const PolyWord, PolyWord)>(
        space: &MemorySpace,
        mut f: F,
    ) {
        let mut i = 0usize;
        let used = space.used_words();
        let Some(base) = space.iter().next().map(|w| w as *const PolyWord) else {
            return;
        };
        while i < used {
            let lw = unsafe { *base.add(i) };
            let n = length_word::length_of(lw);
            if n == 0 || i + 1 + n > used {
                break;
            }
            let body = unsafe { base.add(i + 1) };
            if length_word::is_code_object(lw) {
                f(body, lw);
            }
            i += 1 + n;
        }
    }

    for space in [&loaded.immutable, &loaded.mutable, &loaded.code] {
        walk_code_objects(space, |code_obj_ptr, lw| {
            total += 1;
            let n_words = length_word::length_of(lw);
            let (cp, _count) = unsafe { length_word::const_segment_for_code(code_obj_ptr) };
            let body_start = code_obj_ptr as usize;
            let cp_start = cp as usize;
            let bytecode_len = cp_start
                .saturating_sub(body_start)
                .saturating_sub(std::mem::size_of::<usize>());
            let max_bytes = n_words * std::mem::size_of::<usize>();
            let bytecode_len = bytecode_len.min(max_bytes);
            let full_body: &[u8] =
                unsafe { std::slice::from_raw_parts(code_obj_ptr.cast::<u8>(), max_bytes) };
            let (jf, jit_arity_init) =
                match translate::compile_with_consts_meta(jit, full_body, bytecode_len) {
                    Ok(t) => t,
                    Err(e) => {
                        if std::env::var("JIT_LOG_TRANSLATE_ERRORS").is_ok() {
                            let dump_len: usize = std::env::var("JIT_LOG_BC_LEN")
                                .ok().and_then(|s| s.parse().ok()).unwrap_or(32);
                            let hex: Vec<String> = full_body[..bytecode_len.min(dump_len)]
                                .iter().map(|b| format!("{b:02x}")).collect();
                            eprintln!(
                                "  jit_translate err: code_obj=0x{body_start:016x} bytecode_len={bytecode_len} bc={} err={e}",
                                hex.join(" ")
                            );
                        }
                        return;
                    }
                };
            jit_ok += 1;
            let Some(sml_arity) = translate::arity_from_return_scan_pub(&full_body[..bytecode_len])
            else {
                return;
            };
            if sml_arity > 32 {
                return;
            }
            // Skip functions whose inferred JIT arity exceeds
            // sml_arity + 2 (= closure + retPC + args). These
            // functions read positions BELOW the entry frame — i.e.,
            // they peek into the caller's "older stack" via LOCAL_K.
            // Our do_call's args_buf layout doesn't fully model this:
            // older slots are zero-padded, which causes LOCAL_K to
            // read 0 where SML's interp has real values. Subsequent
            // deref of these zeros → SEGV. Skipping → these functions
            // run in the interp, behavior matches.
            if jit_arity_init > sml_arity + 2 {
                return;
            }
            // Filter opcodes whose translations our JIT doesn't
            // fully model.
            //
            // Currently blocked:
            // - CALL_LOCAL_B (0x16): the translation peeks the closure
            //   correctly (depth = -N + 1 when callee arity == N) but
            //   the actual bug is deeper: `CALL_LOCAL_B N` can be
            //   called with N > callee's true arity. The compiler
            //   over-pushes args and uses LOCAL_K on the leftover
            //   slots after the call. Without RUNTIME arity discovery
            //   (we only know N at translate time, not the closure
            //   target's actual arity), the JIT can't compute the
            //   correct post-call stack depth, and subsequent LOCAL_K
            //   reads land on the wrong slots. The translation
            //   semantics are right; the model is incomplete. To
            //   unblock: trampoline must return both result AND
            //   leftover-count so JIT can adjust its compile-time
            //   stack. Diagnosed at install_idx=17 in bootstrap64
            //   (function recursively calls itself via CALL_LOCAL_B 8
            //   while having sml_arity=3).
            // - TAIL_B_B (0x7b): similar issue (re-enabling breaks the
            //   basis-loaded HOL4 workload).
            // - CALL_CONST_ADDR (0x57/0x58/0x17/0x18): the runtime-load
            //   fix in translate.rs was needed for some entries, but
            //   when CALL_CONST_ADDR functions interact with each
            //   other (multiple installed), bootstrap SEGVs at a
            //   downstream STORE_ML_WORD. Bug unisolated.
            //
            // Verified SAFE (re-enabled without regressions):
            // - CLOSURE_B (0xd0), ALLOC_REF/BYTE_MEM/WORD_MEM
            //   (0x06/0xbd/0xda), RAISE_EX (0x10),
            //   SET_HANDLER8/16 (0x81/0xf9)
            // - CONST_ADDR (load) 0x55/0x56/0x15/0x14 — passes
            //   bootstrap + HOL4 cleanly. +239 functions installed.
            //
            // Going from 326 → 611 installed by removing the safe ones.
            const INSTR_CONST_ADDR8_0_OP: u8 = 0x55;
            const INSTR_CONST_ADDR8_1_OP: u8 = 0x56;
            const INSTR_CONST_ADDR8_8_OP: u8 = 0x15;
            const INSTR_CONST_ADDR16_8_OP: u8 = 0x14;
            const INSTR_CALL_CONST_ADDR8_0_OP: u8 = 0x57;
            const INSTR_CALL_CONST_ADDR8_1_OP: u8 = 0x58;
            const INSTR_CALL_CONST_ADDR8_8_OP: u8 = 0x17;
            const INSTR_CALL_CONST_ADDR16_8_OP: u8 = 0x18;
            const INSTR_CALL_LOCAL_B_OP: u8 = 0x16;
            const INSTR_TAIL_B_B_OP: u8 = 0x7b;
            // CALL_FAST_RTS variants: 0x83..=0x88.
            const INSTR_CALL_FAST_RTS_BASE: u8 = 0x83;
            const INSTR_CALL_FAST_RTS_LAST: u8 = 0x88;
            let bc = &full_body[..bytecode_len];
            let has_call_local_b = bc.contains(&INSTR_CALL_LOCAL_B_OP);
            let has_tail_b_b = bc.contains(&INSTR_TAIL_B_B_OP);
            let has_call_const_addr = bc.iter().any(|&b| {
                b == INSTR_CALL_CONST_ADDR8_0_OP
                    || b == INSTR_CALL_CONST_ADDR8_1_OP
                    || b == INSTR_CALL_CONST_ADDR8_8_OP
                    || b == INSTR_CALL_CONST_ADDR16_8_OP
            });
            // The CONST_ADDR (load) regression on Stage1 basis load was
            // a CONST_ADDR-loaded RTS stub passed to CALL_FAST_RTS. The
            // CONST_ADDR load itself isn't broken, but the RTS path
            // somehow misbehaves when JIT'd. Until that's diagnosed,
            // only skip CONST_ADDR functions whose bytecode ALSO
            // contains a CALL_FAST_RTS — leaving plain const-load
            // patterns (e.g., loading a constant for a comparison)
            // available to JIT.
            let has_const_addr = bc.iter().any(|&b| {
                b == INSTR_CONST_ADDR8_0_OP
                    || b == INSTR_CONST_ADDR8_1_OP
                    || b == INSTR_CONST_ADDR8_8_OP
                    || b == INSTR_CONST_ADDR16_8_OP
            });
            let has_call_fast_rts = bc
                .iter()
                .any(|&b| (INSTR_CALL_FAST_RTS_BASE..=INSTR_CALL_FAST_RTS_LAST).contains(&b));
            let const_addr_rts_wrapper = has_const_addr && has_call_fast_rts;
            if has_call_local_b
                || has_tail_b_b
                || has_call_const_addr
                || const_addr_rts_wrapper
            {
                return;
            }
            // Bisection: check limit + skip set BEFORE incrementing
            // the install index (so we count consistently).
            if let Some(lim) = install_limit
                && install_idx >= lim
            {
                install_idx += 1;
                return;
            }
            if skip_indices.contains(&install_idx) {
                install_idx += 1;
                return;
            }
            let arity_init = sml_arity + 2;
            if verbose {
                eprintln!(
                    "  install[{install_idx:4}]: code_obj=0x{body_start:016x} sml_arity={sml_arity} arity_init={arity_init}"
                );
            }
            // Dump bytecode for a specific install index.
            if let Ok(s) = std::env::var("JIT_INSTALL_DUMP_IDX")
                && let Ok(want_idx) = s.parse::<usize>()
                && install_idx == want_idx
            {
                let bc = &full_body[..bytecode_len];
                let hex: Vec<String> = bc.iter().map(|b| format!("{b:02x}")).collect();
                eprintln!(
                    "  install[{install_idx}] BYTECODE ({} bytes): {}",
                    bc.len(),
                    hex.join(" ")
                );
            }
            interp.install_jit(
                body_start,
                JitEntry {
                    func: jf,
                    arity_init,
                    sml_arity,
                },
            );
            installed += 1;
            install_idx += 1;
        });
    }
    (total, jit_ok, installed)
}

/// Trampoline that JIT'd code calls to dispatch `CALL_FAST_RTS<N>`.
/// Signature must match what `translate.rs` declares for the extern
/// symbol — `(stub: i64, n_args: i64, args: *const i64) -> i64`.
///
/// Looks up the RTS function via the thread-local interpreter handle
/// (set by `do_call` when invoking JIT'd code), invokes it, and
/// returns the result as raw PolyWord bits.
///
/// On any failure (thread-local unset, unresolved entry, alloc-space
/// missing) returns `1` = TAGGED(0) — safer than UB; the JIT'd code
/// downstream may misbehave, but at least we don't deref garbage.
///
/// # Arg layout
/// `args` is the JIT-emitted args buffer; `args[0]` = first popped
/// from stack top = LAST pushed = (per the interpreter convention)
/// LAST C-side arg. Reverse before calling the RTS function so
/// `rts_args[0]` matches the interpreter's `args[0]` (= threadId
/// for `rtsCallFullN`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rts_trampoline(
    stub_word: i64,
    n_args: i64,
    args: *const i64,
) -> i64 {
    use polyml_runtime::{
        rts::{RtsContext, RtsFn},
        PolyWord, JIT_INTERP,
    };

    let interp_ptr = JIT_INTERP.with(|c| c.get());
    if interp_ptr.is_null() {
        return 1; // TAGGED(0)
    }
    // SAFETY: JIT_INTERP non-null = caller of with_jit_interp holds
    // the borrow for this call.
    let interp = unsafe { &mut *interp_ptr };

    // stub_word is the raw PolyWord bits of an EntryPoint object.
    // Word 0 holds the RTS dispatch token (= entry index + 1).
    let stub = PolyWord::from_bits(stub_word as usize);
    if !stub.is_data_ptr() {
        return 1;
    }
    let token = unsafe { *stub.as_ptr::<PolyWord>() }.0;

    // Resolve the entry.
    let Some(entry) = interp.rts_table().entry(token).cloned() else {
        return 1;
    };
    let n = n_args as usize;
    if entry.func.arity() != n {
        return 1;
    }

    // Read N args from the JIT's buffer. JIT stored slot[0] = first
    // popped = top of stack = LAST C arg. Reverse on read.
    #[allow(clippy::cast_sign_loss)]
    let mut rts_args: [PolyWord; 5] = [PolyWord::ZERO; 5];
    for i in 0..n {
        // SAFETY: caller (JIT'd code) guarantees args[0..n] is valid.
        let v = unsafe { *args.add(i) };
        // JIT slot[i] = (n-1-i)-th C arg.
        rts_args[n - 1 - i] = PolyWord::from_bits(v as usize);
    }

    // Dispatch.
    let rts_ref = interp.rts_table_arc();
    let mut ctx = RtsContext {
        alloc_space: interp.jit_alloc_space_mut(),
        raised_exception: None,
        rts: Some(&rts_ref),
    };
    let result = match entry.func {
        RtsFn::Arity0(f) => f(&mut ctx),
        RtsFn::Arity1(f) => f(&mut ctx, rts_args[0]),
        RtsFn::Arity2(f) => f(&mut ctx, rts_args[0], rts_args[1]),
        RtsFn::Arity3(f) => f(&mut ctx, rts_args[0], rts_args[1], rts_args[2]),
        RtsFn::Arity4(f) => f(&mut ctx, rts_args[0], rts_args[1], rts_args[2], rts_args[3]),
        RtsFn::Arity5(f) => f(
            &mut ctx,
            rts_args[0],
            rts_args[1],
            rts_args[2],
            rts_args[3],
            rts_args[4],
        ),
    };
    result.0 as i64
}

/// Closure-call trampoline. Signature must match what `translate.rs`
/// declares: `(closure_word, n_args, args_ptr) -> i64`.
///
/// Real dispatch path: reads the thread-local interpreter handle
/// set by `polyml_runtime::with_jit_interp`, then invokes
/// `jit_dispatch_closure_call`. The dispatch may recurse into
/// another JIT'd function (cache hit in `Interpreter::do_call`) or
/// fall back to bytecode interpretation.
///
/// If the thread-local isn't set (e.g. JIT'd code being benchmarked
/// in isolation), returns TAGGED(0) as a safe-ish fallback.
#[unsafe(no_mangle)]
/// Probe a (possibly-closure) heap pointer for its arity. Returns
/// the arity as inferred from the ENTER_INT prologue or from
/// scanning the bytecode for RETURN_N. Returns None on any anomaly
/// so a caller can decide whether to log a warning vs panic.
unsafe fn check_closure_arity(addr: u64) -> Option<usize> {
    if addr == 0 || addr & 0x7 != 0 {
        return None;
    }
    let closure_ptr = addr as *const usize;
    let code_addr = unsafe { closure_ptr.read() };
    if code_addr == 0 || code_addr & 0x7 != 0 {
        return None;
    }
    // Read length word (1 word before code_addr).
    let lw = unsafe { (code_addr as *const usize).sub(1).read() };
    let n_words = lw & 0x00ff_ffff_ffff_ffff;
    if n_words == 0 || n_words > (1 << 24) {
        return None;
    }
    let body_len_bytes = n_words * 8;
    let b0 = unsafe { (code_addr as *const u8).read() };
    if b0 == 0xff || b0 == 0xe9 {
        // ENTER_INT prologue
        let b1 = unsafe { (code_addr as *const u8).add(1).read() };
        return Some((b1 & 0x7f) as usize);
    }
    // Fallback: scan bytecode for first RETURN_N. Use the same
    // arity_from_return_scan logic that the translator uses.
    let body =
        unsafe { std::slice::from_raw_parts(code_addr as *const u8, body_len_bytes) };
    // The const pool starts at body[body_len_bytes - 8] + body_len_bytes
    // (trailing-offset is signed, negative). Restrict scan to bytecode.
    let trailing_offset_word = body_len_bytes.checked_sub(8)?;
    let trailing_offset = i64::from_le_bytes(
        body[trailing_offset_word..trailing_offset_word + 8]
            .try_into()
            .ok()?,
    );
    let cp_byte_off = (body_len_bytes as i64 + trailing_offset) as usize;
    let bytecode_end = cp_byte_off.saturating_sub(8).min(body.len());
    let bytecode = &body[..bytecode_end];
    crate::translate::arity_from_return_scan_pub(bytecode)
}

pub unsafe extern "C" fn closure_call_trampoline(
    closure_word: i64,
    n_args: i64,
    args_ptr: *const i64,
) -> i64 {
    use polyml_runtime::PolyWord;
    let closure = PolyWord::from_bits(closure_word as usize);
    let n = n_args as usize;
    // Diagnostic: verify the runtime closure's arity matches the
    // n_args the JIT-translator computed at compile time. If they
    // differ, the JIT'd code will push too many or too few args
    // → stack drift → eventually SEGV in unrelated code.
    if std::env::var("JIT_TRAMP_VERIFY_ARITY").is_ok() {
        let runtime_arity = unsafe {
            check_closure_arity(closure_word as u64)
        };
        if let Some(rt_arity) = runtime_arity
            && rt_arity != n
        {
            eprintln!(
                "  closure_call_trampoline ARITY MISMATCH: closure=0x{closure_word:016x} jit_passed n_args={n} runtime_arity={rt_arity}"
            );
            std::process::abort();
        }
    }
    if std::env::var("JIT_TRAMP_DUMP_ARGS").is_ok() {
        use std::io::Write;
        let _ = writeln!(std::io::stderr(),
            "  closure_call_trampoline: closure=0x{closure_word:016x} n_args={n}",
        );
        for i in 0..n {
            let v = unsafe { args_ptr.add(i).read() };
            let _ = writeln!(std::io::stderr(),
                "    raw_slot[{i}] = 0x{v:016x}",
            );
        }
        let _ = std::io::stderr().flush();
    }
    let mut args: Vec<PolyWord> = Vec::with_capacity(n);
    // SAFETY: caller (JIT'd code) guarantees args_ptr[0..n] is valid.
    // Reverse on read to match jit_dispatch_closure_call's contract
    // (`args[0]` is SML's arg_0 = deepest in pushed block). JIT stored
    // slot[0] = first popped = top of SML = SML's arg_{N-1}, so we
    // reverse to put arg_0 at args[0].
    unsafe {
        for i in 0..n {
            let v = args_ptr.add(n - 1 - i).read();
            args.push(PolyWord::from_bits(v as usize));
        }
    }
    match polyml_runtime::jit_dispatch_closure_call(closure, &args) {
        Ok(v) => v.0 as i64,
        Err(e) => {
            if std::env::var("JIT_TRAMP_PANIC_ON_ERR").is_ok() {
                eprintln!(
                    "  closure_call_trampoline ERR: closure=0x{closure_word:016x} n_args={n} err={e:?}"
                );
                std::process::abort();
            }
            1 // TAGGED(0)
        }
    }
}

/// Word-block move trampoline. `(src, src_off, dest, dest_off, length) -> i64`.
/// Used by JIT'd `BLOCK_MOVE_WORD`. Mirrors the interpreter's
/// `INSTR_BLOCK_MOVE_WORD` semantics: copies `length` PolyWord-sized
/// elements from `src[src_off..src_off+length]` to
/// `dest[dest_off..dest_off+length]`. Returns TAGGED(0).
///
/// Uses `std::ptr::copy` (memmove semantics) for overlap-safety,
/// matching the interpreter.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn block_move_word_trampoline(
    src_word: i64,
    src_off: i64,
    dest_word: i64,
    dest_off: i64,
    length: i64,
) -> i64 {
    use polyml_runtime::PolyWord;
    let src = PolyWord::from_bits(src_word as usize).as_ptr::<PolyWord>();
    let dest_pw = PolyWord::from_bits(dest_word as usize).as_ptr::<PolyWord>();
    let dest = dest_pw.cast_mut();
    #[allow(clippy::cast_sign_loss)]
    let src_o = src_off.max(0) as usize;
    #[allow(clippy::cast_sign_loss)]
    let dest_o = dest_off.max(0) as usize;
    #[allow(clippy::cast_sign_loss)]
    let len = length.max(0) as usize;
    unsafe { std::ptr::copy(src.add(src_o), dest.add(dest_o), len) };
    1 // TAGGED(0)
}

/// Byte-block equality trampoline. `(p1, off1, p2, off2, length) -> tag(bool)`.
/// Returns tagged 1 if `p1[off1..off1+length] == p2[off2..off2+length]`,
/// tagged 0 otherwise. Used by JIT'd `BLOCK_EQUAL_BYTE`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn block_equal_byte_trampoline(
    p1_word: i64,
    off1: i64,
    p2_word: i64,
    off2: i64,
    length: i64,
) -> i64 {
    use polyml_runtime::PolyWord;
    let p1 = PolyWord::from_bits(p1_word as usize).as_ptr::<u8>();
    let p2 = PolyWord::from_bits(p2_word as usize).as_ptr::<u8>();
    #[allow(clippy::cast_sign_loss)]
    let o1 = off1.max(0) as usize;
    #[allow(clippy::cast_sign_loss)]
    let o2 = off2.max(0) as usize;
    #[allow(clippy::cast_sign_loss)]
    let len = length.max(0) as usize;
    let equal = unsafe {
        let s1 = std::slice::from_raw_parts(p1.add(o1), len);
        let s2 = std::slice::from_raw_parts(p2.add(o2), len);
        s1 == s2
    };
    if equal { 3 } else { 1 } // tagged 1 / tagged 0
}

/// Byte-block move trampoline. Same shape as block_move_word_trampoline
/// but operates on bytes. `length` is in bytes; pointer arithmetic
/// advances by 1 per index. Used by JIT'd `BLOCK_MOVE_BYTE`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn block_move_byte_trampoline(
    src_word: i64,
    src_off: i64,
    dest_word: i64,
    dest_off: i64,
    length: i64,
) -> i64 {
    use polyml_runtime::PolyWord;
    let src = PolyWord::from_bits(src_word as usize).as_ptr::<u8>();
    let dest_pw = PolyWord::from_bits(dest_word as usize).as_ptr::<u8>();
    let dest = dest_pw.cast_mut();
    #[allow(clippy::cast_sign_loss)]
    let src_o = src_off.max(0) as usize;
    #[allow(clippy::cast_sign_loss)]
    let dest_o = dest_off.max(0) as usize;
    #[allow(clippy::cast_sign_loss)]
    let len = length.max(0) as usize;
    unsafe { std::ptr::copy(src.add(src_o), dest.add(dest_o), len) };
    1 // TAGGED(0)
}

/// GET_THREAD_ID trampoline. Allocates an 8-word mutable cell with
/// all words = tagged(0). Used by JIT'd `INSTR_GET_THREAD_ID`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn get_thread_id_trampoline() -> i64 {
    match polyml_runtime::jit_dispatch_get_thread_id() {
        Some(ptr) => ptr as i64,
        None => 1, // tagged(0) on failure
    }
}

/// Byte-mem allocation trampoline. `(n_words, flags) -> i64`.
/// Used by JIT'd `ALLOC_BYTE_MEM`. Body is uninitialized.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn alloc_byte_mem_trampoline(
    n_words: i64,
    flags: i64,
) -> i64 {
    #[allow(clippy::cast_sign_loss)]
    let n = n_words.max(0) as usize;
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let f = (flags & 0xff) as u8;
    match polyml_runtime::jit_dispatch_alloc_bytes(n, f) {
        Some(ptr) => ptr as i64,
        None => 1,
    }
}

/// Closure-construction trampoline. `(n_captures, captures_ptr,
/// src_closure_word) -> i64` returning the new closure pointer.
///
/// Used by JIT-translated `CLOSURE_B`: builds a heap closure whose
/// slot 0 is the source closure's code address and slots 1..N are
/// the captures.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn closure_alloc_trampoline(
    n_captures: i64,
    captures_ptr: *const i64,
    src_closure_word: i64,
) -> i64 {
    #[allow(clippy::cast_sign_loss)]
    let n = n_captures.max(0) as usize;
    match polyml_runtime::jit_dispatch_closure_alloc(n, captures_ptr, src_closure_word as u64) {
        Some(ptr) => ptr as i64,
        None => 1,
    }
}

/// Tuple-alloc trampoline. `(n_words, values_ptr) -> i64` returning
/// the new heap-object pointer.
///
/// Routes through `polyml_runtime::jit_dispatch_alloc` which uses
/// the thread-local interpreter handle set by `with_jit_interp`.
/// If the handle isn't set (e.g. JIT'd code running in isolation
/// outside an interpreter dispatch), returns TAGGED(0) as a safe
/// fallback — the JIT'd code can still run, just produces a
/// useless tuple value.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn alloc_tuple_trampoline(
    n_words: i64,
    values_ptr: *const i64,
) -> i64 {
    #[allow(clippy::cast_sign_loss)]
    let n = n_words.max(0) as usize;
    match polyml_runtime::jit_dispatch_alloc(n, 0, values_ptr) {
        Some(ptr) => ptr as i64,
        None => 1, // TAGGED(0)
    }
}

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};
use thiserror::Error;

/// Errors from constructing or running a JIT compilation.
#[derive(Debug, Error)]
pub enum JitError {
    #[error("cranelift settings: {0}")]
    Settings(String),
    #[error("ISA construction failed: {0}")]
    Isa(String),
    #[error("module operation failed: {0}")]
    Module(String),
}

/// A live JIT environment. Owns the Cranelift module that holds
/// compiled functions — drop it and the JITted memory is freed.
pub struct Jit {
    pub(crate) module: JITModule,
    /// Monotonic counter so each compile gets a unique symbol name.
    next_id: u64,
}

impl Jit {
    /// Build a default native-target JIT environment.
    pub fn new() -> Result<Self, JitError> {
        let mut flags = settings::builder();
        flags
            .set("opt_level", "speed")
            .map_err(|e| JitError::Settings(e.to_string()))?;
        let isa_builder = cranelift_native::builder()
            .map_err(|e| JitError::Isa(e.to_string()))?;
        let isa = isa_builder
            .finish(settings::Flags::new(flags))
            .map_err(|e| JitError::Isa(e.to_string()))?;
        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        // Register the RTS-call trampoline so JIT'd code can call back
        // into Rust for any opcode that needs interpreter state.
        builder.symbol("polyml_jit_rts_trampoline", rts_trampoline as *const u8);
        builder.symbol(
            "polyml_jit_closure_call",
            closure_call_trampoline as *const u8,
        );
        builder.symbol(
            "polyml_jit_alloc_tuple",
            alloc_tuple_trampoline as *const u8,
        );
        builder.symbol(
            "polyml_jit_alloc_closure",
            closure_alloc_trampoline as *const u8,
        );
        builder.symbol(
            "polyml_jit_alloc_byte_mem",
            alloc_byte_mem_trampoline as *const u8,
        );
        builder.symbol(
            "polyml_jit_block_move_word",
            block_move_word_trampoline as *const u8,
        );
        builder.symbol(
            "polyml_jit_block_move_byte",
            block_move_byte_trampoline as *const u8,
        );
        builder.symbol(
            "polyml_jit_block_equal_byte",
            block_equal_byte_trampoline as *const u8,
        );
        builder.symbol(
            "polyml_jit_get_thread_id",
            get_thread_id_trampoline as *const u8,
        );
        Ok(Self {
            module: JITModule::new(builder),
            next_id: 0,
        })
    }

    pub(crate) fn fresh_name(&mut self, prefix: &str) -> String {
        let id = self.next_id;
        self.next_id += 1;
        format!("{prefix}_{id}")
    }

    /// Compile a toy "double the tagged int" function and return a
    /// pointer to its native entry point. Signature: `fn(i64) -> i64`.
    ///
    /// The function reads the high 63 bits of `x` (which is the
    /// PolyWord representation of a tagged int `n` as `2n+1`),
    /// extracts `n` via arithmetic shift right by 1, doubles it,
    /// then re-tags. This mirrors the operation `n -> 2n` on the
    /// SML-level int while preserving the tagged-bit invariant.
    pub fn compile_double(&mut self) -> Result<extern "C" fn(i64) -> i64, JitError> {
        let mut ctx = self.module.make_context();
        let mut func_builder_ctx = FunctionBuilderContext::new();
        let int = types::I64;
        // Signature: fn(i64) -> i64
        ctx.func.signature.params.push(AbiParam::new(int));
        ctx.func.signature.returns.push(AbiParam::new(int));

        {
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_builder_ctx);
            let block = builder.create_block();
            builder.append_block_params_for_function_params(block);
            builder.switch_to_block(block);
            builder.seal_block(block);

            let x = builder.block_params(block)[0];
            // n = (x - 1) >> 1   (tagged int is 2n+1)
            let one = builder.ins().iconst(int, 1);
            let x_minus_1 = builder.ins().isub(x, one);
            let n = builder.ins().sshr_imm(x_minus_1, 1);
            // doubled = n + n
            let doubled = builder.ins().iadd(n, n);
            // re-tag: 2*doubled + 1
            let two = builder.ins().iconst(int, 2);
            let shifted = builder.ins().imul(doubled, two);
            let tagged = builder.ins().iadd(shifted, one);
            builder.ins().return_(&[tagged]);

            builder.finalize();
        }

        let name = self.fresh_name("polyml_jit_double");
        let func_id = self
            .module
            .declare_function(&name, Linkage::Export, &ctx.func.signature)
            .map_err(|e| JitError::Module(e.to_string()))?;
        self.module
            .define_function(func_id, &mut ctx)
            .map_err(|e| JitError::Module(e.to_string()))?;
        self.module.clear_context(&mut ctx);
        self.module
            .finalize_definitions()
            .map_err(|e| JitError::Module(e.to_string()))?;

        let code_ptr = self.module.get_finalized_function(func_id);
        // SAFETY: We just compiled this function with the matching
        // signature `fn(i64) -> i64`. The JIT memory remains valid
        // as long as `self.module` does.
        let f: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(code_ptr) };
        Ok(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cranelift_compiles_and_runs_toy_function() {
        let mut jit = Jit::new().expect("jit init");
        let f = jit.compile_double().expect("compile");
        // PolyWord tagging: n is stored as 2n+1.
        //   tag(3)  = 7
        //   tag(6)  = 13
        let tagged_3: i64 = 2 * 3 + 1;
        let tagged_6: i64 = 2 * 6 + 1;
        assert_eq!(f(tagged_3), tagged_6, "double of tagged 3 should be tagged 6");

        let tagged_neg1: i64 = 2 * (-1) + 1; // = -1
        let tagged_neg2: i64 = 2 * (-2) + 1; // = -3
        assert_eq!(f(tagged_neg1), tagged_neg2);
    }

    #[test]
    fn jit_handle_can_compile_multiple_independent_functions() {
        // The same Jit can produce more than one function. (Real
        // bytecode→native translation will rely on this — each
        // PolyML code object becomes one Cranelift function.)
        let mut jit = Jit::new().expect("jit init");
        let f1 = jit.compile_double().expect("compile #1");
        let f2 = jit.compile_double().expect("compile #2");
        assert_eq!(f1(2 * 4 + 1), 2 * 8 + 1);
        assert_eq!(f2(2 * 5 + 1), 2 * 10 + 1);
    }
}
