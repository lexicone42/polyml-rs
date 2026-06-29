//! Cranelift-backed JIT for PolyML bytecode.
//!
//! Translates a code object's bytecode to Cranelift IR and installs the
//! compiled entry in the interpreter's JIT cache; `do_call` dispatches into a
//! JIT'd function by looking its code pointer up in that cache, and opcodes the
//! translator doesn't model trampoline back to the interpreter. It runs the
//! full pipeline correctly (the simple bootstrap, the 7-stage self-compilation
//! chain, and the HOL4 workloads), but is currently a correctness *testbed* —
//! roughly perf-neutral with the tuned interpreter rather than a speedup,
//! because the genuinely hot functions still contain un-translated opcodes (see
//! `CLAUDE.md`, "JIT status", for the coverage-bound performance analysis).
//! Enable with `poly run --jit <image>`.

#![allow(clippy::missing_safety_doc)]

pub mod boundary;
pub mod differential;
pub mod memtrans;
pub mod region;
pub mod translate;

#[cfg(test)]
mod bench;

/// The set of "blocker" opcodes whose JIT translations we don't yet
/// fully trust at install time. A function whose bytecode contains any
/// of these *at a real instruction boundary* is left in the
/// interpreter (see `install_all_jit_entries`).
mod blocker_opcodes {
    use polyml_runtime::interpreter::opcodes::*;
    pub const CALL_LOCAL_B: u8 = INSTR_CALL_LOCAL_B; // 0x16
    pub const CALL_CONST_ADDR8_0: u8 = INSTR_CALL_CONST_ADDR8_0; // 0x57
    pub const CALL_CONST_ADDR8_1: u8 = INSTR_CALL_CONST_ADDR8_1; // 0x58
    pub const CALL_CONST_ADDR8_8: u8 = INSTR_CALL_CONST_ADDR8_8; // 0x17
    pub const CALL_CONST_ADDR16_8: u8 = INSTR_CALL_CONST_ADDR16_8; // 0x18
    pub const CONST_ADDR8_0: u8 = INSTR_CONST_ADDR8_0; // 0x55
    pub const CONST_ADDR8_1: u8 = INSTR_CONST_ADDR8_1; // 0x56
    pub const CONST_ADDR8_8: u8 = INSTR_CONST_ADDR8_8; // 0x15
    pub const CONST_ADDR16_8: u8 = INSTR_CONST_ADDR16_8; // 0x14
    pub const CALL_FAST_RTS_BASE: u8 = INSTR_CALL_FAST_RTS0; // 0x83
    pub const CALL_FAST_RTS_LAST: u8 = INSTR_CALL_FAST_RTS5; // 0x88
    pub const ESCAPE: u8 = INSTR_ESCAPE; // 0xfe
    pub const CASE16: u8 = INSTR_CASE16; // 0x0a

    #[inline]
    pub fn is_call_const_addr(b: u8) -> bool {
        b == CALL_CONST_ADDR8_0
            || b == CALL_CONST_ADDR8_1
            || b == CALL_CONST_ADDR8_8
            || b == CALL_CONST_ADDR16_8
    }
    #[inline]
    pub fn is_const_addr(b: u8) -> bool {
        b == CONST_ADDR8_0 || b == CONST_ADDR8_1 || b == CONST_ADDR8_8 || b == CONST_ADDR16_8
    }
    #[inline]
    pub fn is_call_fast_rts(b: u8) -> bool {
        (CALL_FAST_RTS_BASE..=CALL_FAST_RTS_LAST).contains(&b)
    }
}

/// Which blocker opcodes a function's bytecode contains, computed by an
/// **instruction-boundary-aware** walk (so an opcode byte that is
/// actually an immediate of a preceding instruction — e.g. the `0x16`
/// immediate of `CONST_ADDR8_8`/`CONST_ADDR16_8` — is NOT
/// false-positively flagged as `CALL_LOCAL_B`).
#[derive(Clone, Copy, Default)]
struct BlockerScan {
    call_local_b: bool,
    call_const_addr: bool,
    const_addr: bool,
    call_fast_rts: bool,
}

impl BlockerScan {
    /// A `const_addr` followed (anywhere) by a `call_fast_rts` is a
    /// CONST_ADDR-RTS wrapper (still blocked — see the filter notes).
    fn const_addr_rts_wrapper(self) -> bool {
        self.const_addr && self.call_fast_rts
    }
}

/// The ORIGINAL raw-byte blocker scan: flags a blocker if its opcode
/// *byte* appears anywhere in the bytecode, with no instruction-boundary
/// awareness. Kept (a) as the conservative fallback when the
/// boundary-aware walk can't be trusted, and (b) behind
/// `JIT_LEGACY_BLOCKER_SCAN=1` for A/B measurement. This is intentionally
/// over-conservative — it false-positively rejects functions whose
/// blocker byte is merely an immediate of another instruction.
fn scan_blockers_raw(bc: &[u8]) -> BlockerScan {
    use blocker_opcodes as bo;
    BlockerScan {
        call_local_b: bc.contains(&bo::CALL_LOCAL_B),
        call_const_addr: bc.iter().any(|&b| bo::is_call_const_addr(b)),
        const_addr: bc.iter().any(|&b| bo::is_const_addr(b)),
        call_fast_rts: bc.iter().any(|&b| bo::is_call_fast_rts(b)),
    }
}

/// A static estimate of a function's outgoing-call density, used by
/// the per-function net-benefit install gate (Change 3). When a
/// function is JIT-installed, every *outgoing* call it makes pays the
/// interp→JIT trampoline boundary (a Cranelift `call` into
/// `closure_call_trampoline` / `dynamic_call_trampoline` / the RTS
/// trampoline, each of which does a dispatch + result marshalling).
/// A function dominated by outgoing calls is therefore a likely net
/// LOSS when JIT'd (the doc's "#4-class" regression: ~3.6% of steps,
/// many outgoing trampolined calls). A function with mostly
/// straight-line work amortizes the single inbound-boundary cost over
/// many native instructions and is a win.
///
/// `total_instrs` counts decoded instructions; `outgoing_calls`
/// counts the opcodes that an *installable* function can contain that
/// emit a trampoline boundary call: `CALL_CLOSURE`, `TAIL_B_B`, and
/// the `CALL_FAST_RTS<N>` family. (`CALL_LOCAL_B` /
/// `CALL_CONST_ADDR*` are already rejected by the blocker filter, so
/// an installed function never contains them.)
#[derive(Clone, Copy, Default)]
struct CallDensity {
    total_instrs: usize,
    outgoing_calls: usize,
}

impl CallDensity {
    /// `outgoing_calls / total_instrs`, the fraction of instructions
    /// that pay an outgoing trampoline boundary. 0.0 for a function
    /// with no decoded instructions (which the gate treats as a
    /// non-loser — it can't be call-dominated).
    #[allow(clippy::cast_precision_loss)] // counts are tiny (« 2^52)
    fn density(self) -> f64 {
        if self.total_instrs == 0 {
            0.0
        } else {
            self.outgoing_calls as f64 / self.total_instrs as f64
        }
    }
}

/// Walk `bc` instruction by instruction (boundary-aware, same
/// `disasm::decode` machinery as the blocker scan) and tally the
/// outgoing-call density. Returns `None` on any point the walk can't
/// trust (ESCAPE / unknown opcode / truncation) — the caller then
/// treats the function as "unknown density" and does NOT gate it out
/// (conservative: the gate only ever SKIPS functions it can prove are
/// call-dominated, so an untrusted walk must not cause a skip).
fn scan_call_density(bc: &[u8]) -> Option<CallDensity> {
    use polyml_runtime::interpreter::disasm::decode;
    use polyml_runtime::interpreter::opcodes as op;
    let mut cd = CallDensity::default();
    let mut pc = 0usize;
    while pc < bc.len() {
        let b = bc[pc];
        if b == op::INSTR_ESCAPE {
            return None;
        }
        let d = decode(bc, pc);
        if d.total_len == 0 {
            return None;
        }
        if d.op != op::INSTR_CASE16 && d.mnemonic == "?" {
            return None;
        }
        cd.total_instrs += 1;
        let is_outgoing_call = b == op::INSTR_CALL_CLOSURE
            || b == op::INSTR_TAIL_B_B
            || (op::INSTR_CALL_FAST_RTS0..=op::INSTR_CALL_FAST_RTS5).contains(&b);
        if is_outgoing_call {
            cd.outgoing_calls += 1;
        }
        let step = d.total_len;
        if pc + step > bc.len() {
            return None;
        }
        pc += step;
    }
    Some(cd)
}

/// Walk `bc` instruction by instruction (via the shared
/// `disasm::decode`, which respects immediate widths and the
/// variable-length `CASE16`) and record which blocker opcodes appear
/// at a real instruction boundary.
///
/// Returns `None` if the walk hits a point it cannot trust — an
/// `ESCAPE` (whose extended opcode has its own, here-undecoded
/// immediates), a truncated tail, or an opcode the decoder doesn't
/// recognise — so the caller falls back to the conservative raw-byte
/// scan for that function. This guarantees the boundary walk can only
/// ever *unblock* a function (when it completes cleanly and finds no
/// real blocker); it can never let a real blocker slip through.
fn scan_blockers_boundary_aware(bc: &[u8]) -> Option<BlockerScan> {
    use blocker_opcodes as bo;
    use polyml_runtime::interpreter::disasm::decode;
    let mut scan = BlockerScan::default();
    let mut pc = 0usize;
    while pc < bc.len() {
        let op = bc[pc];
        // ESCAPE: `decode` reports total_len=2 but the extended opcode
        // can carry further immediates we don't model here — walking
        // past it could misalign and MISS a downstream blocker. Bail
        // to the conservative raw scan. (Functions containing ESCAPE
        // don't translate, so this is belt-and-suspenders.)
        if op == bo::ESCAPE {
            return None;
        }
        let d = decode(bc, pc);
        // Unknown opcode (decoder doesn't recognise it) or truncation:
        // the decoder yields total_len <= 1 with an "?"/"<EOF>"
        // mnemonic. Don't trust the rest of the walk — bail.
        if d.total_len == 0 {
            return None;
        }
        if d.op != bo::CASE16 && d.mnemonic == "?" {
            return None;
        }
        // Record blockers seen at this real instruction boundary.
        if op == bo::CALL_LOCAL_B {
            scan.call_local_b = true;
        }
        if bo::is_call_const_addr(op) {
            scan.call_const_addr = true;
        }
        if bo::is_const_addr(op) {
            scan.const_addr = true;
        }
        if bo::is_call_fast_rts(op) {
            scan.call_fast_rts = true;
        }
        // A decoded instruction must consume at least its opcode byte;
        // `decode` guarantees total_len >= 1 here (the == 0 case bailed
        // above). Advancing by total_len keeps us on real boundaries.
        let step = d.total_len;
        // Sanity: a multi-byte instruction whose immediates run off the
        // end means a truncated body — bail conservatively.
        if pc + step > bc.len() {
            return None;
        }
        pc += step;
    }
    Some(scan)
}

/// Decide whether *every* `CALL_CONST_ADDR` (0x57/0x58/0x17/0x18) in
/// `bc` sits in a **tail-equivalent** position — i.e. one where the
/// JIT's current mid-function CCA translation (translate.rs:752-814,
/// which pops `n_args` SSA values and pushes a single result) produces
/// the CORRECT return value even though it desynchronizes the
/// compile-time stack from the persistent-stack layout the SML
/// compiler assumes.
///
/// WHY a tail-position CCA is safe under the over-pop model, but a
/// mid-function one is not (root cause, task #115):
///
/// Upstream CALL_CLOSURE (vendor/polyml/libpolyml/bytecode.cpp:411-414)
/// pops ONLY the closure; the call args physically PERSIST on the
/// stack across the call, and the callee's RETURN_N (bytecode.cpp:
/// 454-460, `sp += returnCount`) collapses them. The compiler then
/// addresses the surviving slots (a `STACK_CONTAINER_B` ref, fillers,
/// etc.) by absolute LOCAL/CONTAINER offset AFTER the call. The JIT's
/// CCA handler instead POPS those args and pushes one result, so a
/// later `INDIRECT_CONTAINER_B` / `LOCAL_K` dereferences a stale
/// compile-time value (a tagged-0 `iconst`, =0x1) as a heap pointer →
/// SIGSEGV. Proven on install index 0 (head `78 81 2b 0e 02 3b 2a 57
/// 6f 50 29 74 00 …`): the `0e 02` STACK_CONTAINER_B is live across the
/// `57 6f` CCA, and the `74 00` INDIRECT_CONTAINER_B two ops later
/// SEGVs.
///
/// In tail-equivalent position the over-pop is harmless: nothing reads
/// the (corrupted) slots below the result — the very next thing is a
/// RETURN that discards them. The trampoline still calls the closure
/// with the right `n_args` and returns the right result. This is
/// EXACTLY the gate `CALL_CLOSURE` already uses (translate.rs:606-625).
///
/// Tail-equivalent = the instruction immediately AFTER the CCA is one
/// of:
///   - `RETURN_1/2/3/B/W` (direct tail), OR
///   - the `LOCAL_0; RESET_R_1; RETURN_1` cleanup idiom
///     (0x29, 0x64, 0x42 — the compiler's "swap top into place before
///     return"; functionally a return of the call result).
///
/// Returns `None` when the boundary walk can't be trusted (ESCAPE,
/// unknown opcode, truncation) so the caller treats the function as
/// **not** CCA-safe (conservative: an untrusted walk must never let a
/// CCA function install). Returns `Some(true)` only when the walk
/// completes cleanly AND every CCA is tail-equivalent.
fn cca_all_tail_equivalent(bc: &[u8]) -> Option<bool> {
    use blocker_opcodes as bo;
    use polyml_runtime::interpreter::disasm::decode;
    // The cleanup-tail idiom (mirrors translate.rs:617-619).
    const LOCAL_0: u8 = 0x29;
    const RESET_R_1: u8 = 0x64;
    const RETURN_1: u8 = 0x42;
    const RETURN_2: u8 = 0x43;
    const RETURN_3: u8 = 0x44;
    const RETURN_B: u8 = 0x1f;
    const RETURN_W: u8 = 0x0d;

    let mut pc = 0usize;
    let mut all_tail = true;
    let mut saw_cca = false;
    while pc < bc.len() {
        let op = bc[pc];
        // ESCAPE / unknown / truncation: we cannot reliably find the
        // next instruction boundary, so we cannot prove tail-position.
        if op == bo::ESCAPE {
            return None;
        }
        let d = decode(bc, pc);
        if d.total_len == 0 {
            return None;
        }
        if d.op != bo::CASE16 && d.mnemonic == "?" {
            return None;
        }
        let step = d.total_len;
        if pc + step > bc.len() {
            return None;
        }
        if bo::is_call_const_addr(op) {
            saw_cca = true;
            let next_pc = pc + step;
            let next = bc.get(next_pc).copied();
            let direct_tail = matches!(
                next,
                Some(RETURN_1 | RETURN_2 | RETURN_3 | RETURN_B | RETURN_W)
            );
            let cleanup_tail = bc.get(next_pc).copied() == Some(LOCAL_0)
                && bc.get(next_pc + 1).copied() == Some(RESET_R_1)
                && bc.get(next_pc + 2).copied() == Some(RETURN_1);
            if !direct_tail && !cleanup_tail {
                all_tail = false;
            }
        }
        pc += step;
    }
    // `saw_cca` is implied true by the caller (it only calls this for
    // CCA functions), but guard anyway: a no-CCA function is vacuously
    // tail-safe.
    let _ = saw_cca;
    Some(all_tail)
}

/// Public, side-effect-free predicate mirroring the install filter's
/// CALL_CONST_ADDR (0x57/0x58/0x17/0x18) safety decision: returns
/// `true` iff a function whose bytecode is `bc` is SAFE to install
/// despite containing a CCA — i.e. it contains no CCA at all, or every
/// CCA it contains is in tail-equivalent position (so the JIT's
/// mid-function over-pop translation produces the correct return value;
/// see `cca_all_tail_equivalent` for the root cause). Used by the CCA
/// differential test (positive control must be `true`, the
/// container-over-push negative control must be `false`) so the gate is
/// fenced without relying on the bisection env toggles.
#[must_use]
pub fn cca_install_safe(bc: &[u8]) -> bool {
    use blocker_opcodes as bo;
    let has_cca = bc.iter().any(|&b| bo::is_call_const_addr(b));
    if !has_cca {
        return true;
    }
    cca_all_tail_equivalent(bc) == Some(true)
}

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
    use polyml_runtime::{JitEntry, MemorySpace, PolyWord, length_word};
    let mut total = 0usize;
    let mut jit_ok = 0usize;
    let mut installed = 0usize;

    // Bisection support: env vars to narrow the install set.
    //   JIT_INSTALL_LIMIT=N — install only first N functions
    //   JIT_INSTALL_SKIP=N,M,K — skip these install indices (comma list)
    //   JIT_INSTALL_VERBOSE=1 — print each install with its index
    // Bisection harness controls: warn loudly on a SET-but-malformed
    // value rather than silently defaulting (a typo'd value would
    // otherwise derail SEGV localization — see CLAUDE.md's harness docs).
    let install_limit: Option<usize> = match std::env::var("JIT_INSTALL_LIMIT") {
        Ok(s) => match s.parse() {
            Ok(n) => Some(n),
            Err(_) => {
                eprintln!("warning: JIT_INSTALL_LIMIT={s:?} is not a number; ignoring");
                None
            }
        },
        Err(_) => None,
    };
    let skip_indices: std::collections::HashSet<usize> = match std::env::var("JIT_INSTALL_SKIP") {
        Ok(s) => s
            .split(',')
            .filter(|x| !x.trim().is_empty())
            .filter_map(|x| match x.trim().parse() {
                Ok(n) => Some(n),
                Err(_) => {
                    eprintln!("warning: JIT_INSTALL_SKIP token {x:?} is not a number; ignoring it");
                    None
                }
            })
            .collect(),
        Err(_) => std::collections::HashSet::new(),
    };
    let verbose = std::env::var("JIT_INSTALL_VERBOSE").is_ok();
    let mut install_idx = 0usize;

    fn walk_code_objects<F: FnMut(*const PolyWord, PolyWord)>(space: &MemorySpace, mut f: F) {
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
            let (jf, jit_arity_init) = match translate::compile_with_consts_meta(
                jit,
                full_body,
                bytecode_len,
            ) {
                Ok(t) => t,
                Err(e) => {
                    if std::env::var("JIT_LOG_TRANSLATE_ERRORS").is_ok() {
                        let dump_len: usize = std::env::var("JIT_LOG_BC_LEN")
                            .ok()
                            .and_then(|s| s.parse().ok())
                            .unwrap_or(32);
                        let hex: Vec<String> = full_body[..bytecode_len.min(dump_len)]
                            .iter()
                            .map(|b| format!("{b:02x}"))
                            .collect();
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
            // - CALL_CONST_ADDR (0x57/0x58/0x17/0x18): ROOT-CAUSED
            //   (task #115, 2026-06-20). NOT a "multi-function
            //   interaction" — install index 0 ALONE SEGVs. It is a
            //   per-function MID-FUNCTION OVER-POP: the CCA translation
            //   pops `n_args` SSA values + pushes one result, but
            //   upstream CALL_CLOSURE (bytecode.cpp:411-414) pops ONLY
            //   the closure (args PERSIST across the call, the callee's
            //   RETURN_N collapses them), so a later container/LOCAL op
            //   addressing a surviving slot derefs a stale tagged-0 →
            //   SIGSEGV. See the `cca_all_tail_equivalent` gate below:
            //   a CCA function installs ONLY when every CCA in it is in
            //   tail-equivalent position. (On the bootstrap image that
            //   safe subset happens to be EMPTY — every hot CCA function
            //   uses its call result mid-function — so the count is
            //   unchanged; a correct mid-function CCA needs the
            //   non-popping / whole-region model.)
            //
            // Verified SAFE (re-enabled without regressions):
            // - CLOSURE_B (0xd0), ALLOC_REF/BYTE_MEM/WORD_MEM
            //   (0x06/0xbd/0xda), RAISE_EX (0x10),
            //   SET_HANDLER8/16 (0x81/0xf9)
            // - CONST_ADDR (load) 0x55/0x56/0x15/0x14 — passes
            //   bootstrap + HOL4 cleanly. +239 functions installed.
            //
            // Going from 326 → 611 installed by removing the safe ones.
            let bc = &full_body[..bytecode_len];
            // INSTRUCTION-BOUNDARY-AWARE blocker detection. The old
            // `bc.contains(&OPCODE)` raw-byte scans false-positively
            // rejected clean functions whose bytecode merely contained
            // a blocker *byte* as an IMMEDIATE of another instruction —
            // most notably the #1 hottest function (632 bytes, 7.4% of
            // all steps), whose `0x16` bytes are immediates of
            // CONST_ADDR16_8/CONST_ADDR8_8, NOT real CALL_LOCAL_B
            // opcodes. We now decode the body instruction by
            // instruction and flag a blocker ONLY when it sits at a real
            // instruction boundary.
            //
            // Correctness is conservative-by-design: if the boundary
            // walk hits anything it can't trust (ESCAPE, an
            // unrecognised opcode, or a truncated tail), it returns
            // `None` and we FALL BACK to the original raw-byte scan for
            // that function. So this change can only ever *unblock*
            // clean functions; it never relaxes which opcodes are
            // blocked, and never lets a real blocker slip past (which
            // would re-introduce the CALL_CONST_ADDR / CALL_LOCAL_B
            // SEGV class).
            // Bisection escape hatch: `JIT_LEGACY_BLOCKER_SCAN=1`
            // forces the old raw-byte `contains()` scan (with its
            // immediate-byte false positives), so the
            // boundary-aware-vs-legacy install sets can be A/B measured
            // without rebuilding. Default = the boundary-aware scan.
            let use_legacy = std::env::var("JIT_LEGACY_BLOCKER_SCAN").is_ok();
            let scan = if use_legacy {
                scan_blockers_raw(bc)
            } else {
                // Conservative fallback to the raw scan when the
                // boundary walk can't be trusted (ESCAPE / unknown /
                // truncated) — so this can only ever *unblock* clean
                // functions, never let a real blocker slip past.
                scan_blockers_boundary_aware(bc).unwrap_or_else(|| scan_blockers_raw(bc))
            };
            let has_call_local_b = scan.call_local_b;
            // CALL_CONST_ADDR (0x57/0x58/0x17/0x18) install gate
            // (task #115, ROOT-CAUSED 2026-06-20).
            //
            // ROOT CAUSE (definitive, not "interaction"): the CCA
            // translation is a MID-FUNCTION over-pop. It pops `n_args`
            // SSA values off the compile-time stack and pushes one
            // result (translate.rs:774-813), but upstream CALL_CLOSURE
            // (bytecode.cpp:411-414) pops ONLY the closure — the args
            // PERSIST across the call and the callee's RETURN_N
            // (bytecode.cpp:454-460) collapses them. The compiler
            // addresses the surviving slots (e.g. a STACK_CONTAINER_B
            // ref) by absolute offset AFTER the call, so the over-pop
            // desyncs the compile-time stack and a later
            // INDIRECT_CONTAINER_B derefs a stale tagged-0 (0x1) →
            // SIGSEGV. This is a per-function class (install index 0
            // ALONE SEGVs), NOT a multi-function interaction — see the
            // refuted hypotheses below.
            //
            // SAFE SUBSET: a CCA in TAIL-EQUIVALENT position (next op is
            // RETURN_N or the LOCAL_0;RESET_R_1;RETURN_1 cleanup idiom)
            // is correct under the over-pop model — nothing reads the
            // corrupted slots below the result; the very next op returns
            // it. This is exactly the gate CALL_CLOSURE already uses
            // (translate.rs:606-625). `cca_all_tail_equivalent` does a
            // boundary-aware walk and returns Some(true) only if EVERY
            // CCA in the body is tail-equivalent, None if the walk can't
            // be trusted (→ treated as not-safe, conservative).
            //
            // BISECTION ESCAPE HATCH (default-off, DO NOT SHIP ENABLED):
            // JIT_TRUST_CALL_CONST_ADDR=1 installs ALL CCA functions
            // (ignoring the tail gate), re-introducing the over-pop SEGV
            // so the class can be bisected (JIT_INSTALL_LIMIT /
            // JIT_INSTALL_SKIP). Trust-all SEGVs (823→2061 installs,
            // exit 139) on the simple bootstrap and ~3.77M steps into
            // the basis load.
            let trust_call_const_addr = std::env::var("JIT_TRUST_CALL_CONST_ADDR").is_ok();
            // EXPERIMENTAL (default-off): JIT_CCA_NO_CONTAINER=1 admits
            // CCA functions that contain NO container opcode
            // (STACK_CONTAINER_B / MOVE_TO_CONTAINER_B /
            // INDIRECT_CONTAINER_B and their W ESCAPE variants), even
            // mid-function. The over-pop net delta (-N+1) matches the
            // interpreter when n_args == callee arity (which
            // JIT_TRAMP_VERIFY_ARITY confirms holds for all CCA), so
            // the SEGV class is driven by the container-ref-live-across
            // -the-call hazard. This toggle was used to TEST whether the
            // no-container subset is safe; it is NOT (see the basis-load
            // verification — a no-container CCA still desyncs on a
            // post-call absolute-offset LOCAL read), so it ships
            // default-off and the tail-equivalent gate is authoritative.
            let cca_no_container_experiment = std::env::var("JIT_CCA_NO_CONTAINER").is_ok();
            // A function with a CCA is BLOCKED unless (trust toggle) OR
            // (every CCA in it is tail-equivalent) OR (the experimental
            // no-container toggle accepts it). A function with NO CCA
            // short-circuits past the (extra, install-time-only) tail
            // walk entirely.
            let cca_safe = !scan.call_const_addr
                || trust_call_const_addr
                || cca_all_tail_equivalent(bc) == Some(true)
                || (cca_no_container_experiment
                    && scan_blockers_boundary_aware(bc).is_some()
                    && !bc.iter().any(|&b| b == 0x0e || b == 0x24 || b == 0x74));
            let has_call_const_addr = scan.call_const_addr && !cca_safe;
            // Diagnostic: tally the CCA population vs how many pass the
            // tail-equivalent gate (JIT_CCA_STATS=1).
            if std::env::var("JIT_CCA_STATS").is_ok() && scan.call_const_addr {
                let tail = cca_all_tail_equivalent(bc);
                let has_container = bc.iter().any(|&b| {
                    b == 0x0e /* STACK_CONTAINER_B */
                        || b == 0x24 /* MOVE_TO_CONTAINER_B */
                        || b == 0x74 /* INDIRECT_CONTAINER_B */
                });
                eprintln!(
                    "  cca_stat: code_obj=0x{body_start:016x} bytecode_len={bytecode_len} all_tail={tail:?} has_container_byte={has_container}"
                );
            }
            let const_addr_rts_wrapper = scan.const_addr_rts_wrapper();
            // TAIL_B_B (0x7b) is now SAFE to install (2026-06-12).
            //
            // Root cause of the old break: the JIT translation of
            // TAIL_B_B consumed only `tail_count - 1` stack slots
            // (closure + n_args args), forgetting the retPC placeholder
            // that the SML compiler pushes on TOP of the call group.
            // Upstream (bytecode.cpp:387-406) consumes `tail_count`
            // items: it pops the retPC placeholder FIRST, then the
            // closure, then forwards the `tail_count-2` args. The
            // off-by-one made the value treated as "closure" actually
            // be the bottom-most arg (often a tagged int), producing
            // "call to non-closure value" / SEGV on tail-recursive code
            // (List.map / List.tabF). Fixed in translate.rs
            // (INSTR_TAIL_B_B): pop+discard the retPC placeholder before
            // popping the closure. Verified: simple bootstrap Tagged(0)
            // (+115 installed), the full basis load Tagged(0) with
            // JIT_TRAMP_VERIFY_ARITY=1 reporting ZERO arity mismatches
            // (tail_count-2 == callee arity holds for every dispatch —
            // a tail call forwards exactly its args, unlike CALL_LOCAL_B
            // which deliberately over-pushes), and a focused
            // JIT==interp differential (tail_b_b_differential.rs).
            //
            // We still exclude TAIL_B_B functions that ALSO contain a
            // currently-untrusted opcode (CALL_LOCAL_B / CALL_CONST_ADDR
            // / a CONST_ADDR-RTS wrapper) — those remain blocked by their
            // own filters below, independent of the tail-call fix.
            if has_call_local_b || has_call_const_addr || const_addr_rts_wrapper {
                return;
            }
            // CHANGE 3 — PER-FUNCTION NET-BENEFIT INSTALL GATE.
            //
            // A function that is dominated by *outgoing* calls is a
            // likely net LOSS when JIT-installed: every outgoing call
            // pays the interp→JIT trampoline boundary (a Cranelift
            // `call` into closure_call_trampoline /
            // dynamic_call_trampoline / the RTS trampoline + dispatch
            // + result marshalling), with little straight-line native
            // work in between to amortize the single inbound-boundary
            // cost. The feasibility doc's "#4-class" regression (a
            // call-heavy function, ~3.6% of steps, that made many
            // outgoing trampolined calls and cost +1.6 s when JIT'd)
            // is exactly this shape. We estimate net benefit from a
            // cheap static signal — outgoing-call density (fraction of
            // decoded instructions that are CALL_CLOSURE / TAIL_B_B /
            // CALL_FAST_RTS) — and SKIP installing functions above a
            // conservative threshold.
            //
            // The gate is conservative-by-design and MONOTONE:
            //  - It only ever SKIPS (never installs an extra function),
            //    so the gated set is a SUBSET of the ungated 823.
            //  - The default threshold (0.5) only fires on functions
            //    where MORE THAN HALF of all decoded instructions are
            //    outgoing trampoline calls — clear net-losers with
            //    almost no straight-line work to accelerate. Most
            //    installed functions have density well under 0.1, so
            //    the gate touches only the extreme call-dominated tail.
            //  - If the density walk can't be trusted (ESCAPE / unknown
            //    opcode / truncation) it returns None and we do NOT
            //    gate the function out (an untrusted walk must never
            //    cause a skip).
            //
            // Tunable for measurement / A/B:
            //   JIT_NET_GATE_DENSITY=<f>  — override the 0.5 threshold.
            //   JIT_NET_GATE_DENSITY=1.0  — effectively disables the
            //     gate (density can never exceed 1.0; > 1.0 = off).
            //   JIT_NET_GATE_DUMP=1       — log every candidate's
            //     (addr, total_instrs, outgoing_calls, density,
            //     gated?) so the density distribution can be correlated
            //     with the profiler's hot CALL targets.
            let gate_density_threshold: f64 = std::env::var("JIT_NET_GATE_DENSITY")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(0.5);
            let call_density = scan_call_density(bc);
            let gated_out = match call_density {
                Some(cd) => cd.density() > gate_density_threshold,
                None => false, // untrusted walk → never gate out
            };
            if std::env::var("JIT_NET_GATE_DUMP").is_ok() {
                let (ti, oc, dens) = match call_density {
                    Some(cd) => (cd.total_instrs, cd.outgoing_calls, cd.density()),
                    None => (0, 0, -1.0),
                };
                eprintln!(
                    "  net_gate: code_obj=0x{body_start:016x} total_instrs={ti} outgoing_calls={oc} density={dens:.3} gated_out={gated_out}"
                );
            }
            if gated_out {
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

/// A scanned region candidate: a real heap code object whose entire
/// static CALL_CONST_ADDR subgraph fits the whole-region core opcode
/// subset (so [`memtrans::build_region`] succeeds).
#[derive(Clone, Debug)]
pub struct RegionCandidate {
    /// Code-object body address of the region root.
    pub root_addr: u64,
    /// The root's SML arity.
    pub arity: usize,
    /// Number of code objects in the region (root + static callees).
    pub n_funcs: usize,
    /// The root's bytecode-only bytes (for provenance forensics).
    pub bytecode: Vec<u8>,
}

/// SCAN the loaded image's code objects for whole-region candidates: any
/// code object whose static call-subgraph fits the core opcode subset.
/// Returns every fitting root (build succeeds on a throwaway probe Jit),
/// sorted smallest-region-first. This is the GAP-1 real-heap-extraction
/// probe — it reports honestly which real regions exist.
///
/// # Safety
/// The image must be loaded and its code spaces populated; the heap is
/// frozen (no GC since load).
#[must_use]
pub unsafe fn scan_region_candidates(loaded: &polyml_runtime::LoadedImage) -> Vec<RegionCandidate> {
    use polyml_runtime::{MemorySpace, PolyWord, length_word};

    fn walk_code_objects<F: FnMut(*const PolyWord)>(space: &MemorySpace, mut f: F) {
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
                f(body);
            }
            i += 1 + n;
        }
    }

    let mut out: Vec<RegionCandidate> = Vec::new();
    for space in [&loaded.immutable, &loaded.mutable, &loaded.code] {
        walk_code_objects(space, |code_obj_ptr| {
            let root_addr = code_obj_ptr as u64;
            // Probe with a fresh throwaway Jit (NOT finalized — we only
            // care whether build_region succeeds).
            let Ok(mut probe) = Jit::new() else {
                return;
            };
            // SAFETY: root_addr is a live code object in the frozen heap.
            if let Ok(region) = unsafe { memtrans::build_region(&mut probe, root_addr) } {
                // Live-dispatch safety gate. S4b lowers STACK_SIZE16
                // faithfully, so a STACK_SIZE16-bearing region is now SAFE to
                // admit (over-push traps at the prologue). But two classes
                // stay REFUSED for live dispatch:
                //  - recursive: a static CALL_CONST_ADDR self/mutual cycle
                //    lowers to a native Cranelift self-`call` -> OS-thread
                //    stack growth (SIGSEGV at depth, NOT a controlled
                //    StackOverflow) + unchecked per-level pushes -> OOB write
                //    below the stack Box. The SML STACK_SIZE16 check does not
                //    bound the NATIVE recursion. (S4-proper: a native depth
                //    guard.)
                //  - has_dynamic_call: the CALL_LOCAL_B/CALL_CLOSURE
                //    trampoline is sound + measured (3.3x), but
                //    region_interp_call does not yet propagate a REAL
                //    exception from the callee faithfully (maps to Overflow).
                //    Live admission waits on that raise fidelity (S4-proper).
                // The trampoline mechanism + microbench exercise dynamic
                // calls directly (not via this live path), so the measurement
                // stands.
                if region.recursive || region.has_dynamic_call {
                    return;
                }
                // SAFETY: root_addr is live; resolve its bytecode for the
                // provenance report.
                let bytecode = unsafe { memtrans::resolve_code(root_addr) }
                    .map(|rc| rc.bytecode)
                    .unwrap_or_default();
                out.push(RegionCandidate {
                    root_addr,
                    arity: region.root_arity,
                    n_funcs: region.funcs.len(),
                    bytecode,
                });
            }
        });
    }
    out.sort_by_key(|c| (c.n_funcs, c.arity, c.root_addr));
    out
}

/// WHOLE-REGION JIT wiring (S3b): install the do_call dispatch callback
/// into the runtime, then compile + finalize + register the supplied
/// region roots so a live `poly run` dispatches them NATIVE through the
/// interpreter's do_call boundary.
///
/// `roots` are code-object body addresses (e.g. from
/// [`scan_region_candidates`], or a tailored in-subset code object
/// extracted from the heap). Each is compiled into ONE leaked `Jit`
/// module (so the finalized native code outlives this call), finalized,
/// and registered with `interp.install_region`. Returns the number of
/// roots successfully registered.
///
/// # Safety
/// Each root is a live code-object body pointer in the frozen heap.
pub unsafe fn install_whole_region(
    interp: &mut polyml_runtime::Interpreter,
    roots: &[u64],
) -> usize {
    // 1. Install the dispatch callback (idempotent). This is the ONLY
    //    place the runtime learns how to reach boundary::dispatch_region.
    polyml_runtime::install_region_dispatch(boundary::polyml_jit_region_dispatch);

    if roots.is_empty() {
        return 0;
    }

    // 2. Compile every root into ONE shared, leaked Jit module so all the
    //    finalized native code stays mapped for the whole process. (A
    //    region's inter-function native calls resolve within its own
    //    module; distinct roots can share one module since their FuncIds
    //    are unique.)
    let mut jit = match Jit::new() {
        Ok(j) => j,
        Err(_) => return 0,
    };
    let mut built: Vec<(u64, usize, cranelift_module::FuncId)> = Vec::new();
    for &root_addr in roots {
        // SAFETY: root_addr is a live code object in the frozen heap.
        if let Ok(region) = unsafe { memtrans::build_region(&mut jit, root_addr) } {
            // Defense in depth: STACK_SIZE16-bearing regions are now safe
            // (faithful trap), but recursive regions (native self-`call` ->
            // OS-stack SIGSEGV + unchecked over-push) and dynamic-call regions
            // (trampoline raise-fidelity gap) stay OUT of live dispatch until
            // S4-proper. Mirrors scan_region_candidates.
            if region.recursive || region.has_dynamic_call {
                continue;
            }
            built.push((root_addr, region.root_arity, region.root));
        }
    }
    if built.is_empty() {
        return 0;
    }
    // Finalize ONCE — after this no further definitions in this module.
    if jit.module.finalize_definitions().is_err() {
        return 0;
    }
    // 3. Resolve each root's finalized native pointer + register it.
    let mut registered = 0usize;
    for (root_addr, arity, func_id) in built {
        let ptr = jit.module.get_finalized_function(func_id);
        interp.install_region(
            root_addr as usize,
            polyml_runtime::RegionEntry {
                region_fn: ptr as usize,
                sml_arity: arity,
            },
        );
        registered += 1;
    }
    // Leak the Jit so its executable memory outlives this scope (the
    // interpreter holds raw native pointers into it).
    Box::leak(Box::new(jit));
    registered
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
pub unsafe extern "C" fn rts_trampoline(stub_word: i64, n_args: i64, args: *const i64) -> i64 {
    use polyml_runtime::{
        JIT_INTERP, PolyWord,
        rts::{RtsContext, RtsFn},
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
    // Seed the per-thread bootstrap tail-call slot from the interpreter so
    // a `PolyEndBootstrapMode` routed through JIT'd code records its pending
    // tail call where the interpreter will read it (replaces the old
    // process-global static the JIT path shared with the interpreter).
    let seed_bootstrap_tail = interp.bootstrap_tail_call();
    let mut ctx = RtsContext {
        alloc_space: interp.jit_alloc_space_mut(),
        raised_exception: None,
        rts: Some(&rts_ref),
        bootstrap_tail_call: seed_bootstrap_tail,
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
    // Write the (possibly updated) bootstrap tail-call slot back into the
    // interpreter. Reading the slot is `ctx`'s last use, so its borrow of
    // `interp` (via `jit_alloc_space_mut`) ends here and the write below is
    // allowed.
    let updated_bootstrap_tail = ctx.bootstrap_tail_call;
    interp.set_bootstrap_tail_call(updated_bootstrap_tail);
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
    // Object-header length = the word with its top flag byte cleared. On 64-bit
    // that's the low 56 bits (0x00ff_ffff_ffff_ffff); `usize::MAX >> 8` is the
    // same value there and the correct 32-bit layout (low 24 bits) too.
    let n_words = lw & (usize::MAX >> 8);
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
    let body = unsafe { std::slice::from_raw_parts(code_addr as *const u8, body_len_bytes) };
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
        let runtime_arity = unsafe { check_closure_arity(closure_word as u64) };
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
        let _ = writeln!(
            std::io::stderr(),
            "  closure_call_trampoline: closure=0x{closure_word:016x} n_args={n}",
        );
        for i in 0..n {
            let v = unsafe { args_ptr.add(i).read() };
            let _ = writeln!(std::io::stderr(), "    raw_slot[{i}] = 0x{v:016x}",);
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
    // A negative offset/length here means a JIT codegen bug (wrong arg
    // order / sign-extension). The .max(0) clamp keeps release builds
    // robust; the debug_assert turns the silent-truncation into a precise
    // failure under tests / JIT bisection.
    debug_assert!(
        src_off >= 0 && dest_off >= 0 && length >= 0,
        "block_move_word_trampoline negative arg: src_off={src_off} dest_off={dest_off} len={length}"
    );
    #[allow(clippy::cast_sign_loss)]
    let src_o = src_off.max(0) as usize;
    #[allow(clippy::cast_sign_loss)]
    let dest_o = dest_off.max(0) as usize;
    #[allow(clippy::cast_sign_loss)]
    let len = length.max(0) as usize;
    unsafe { std::ptr::copy(src.add(src_o), dest.add(dest_o), len) };
    1 // TAGGED(0)
}

/// Decode the `(p1_word, off1, p2_word, off2, length)` ABI shared by the
/// three byte-block trampolines into two raw `u8` pointers plus clamped
/// `usize` offsets/length. A negative offset/length means a JIT codegen
/// bug (wrong arg order / sign-extension); the `.max(0)` clamp keeps
/// release builds robust while the `debug_assert!` turns the silent
/// truncation into a precise failure under tests / JIT bisection.
/// (`block_move_word_trampoline` is NOT a caller — it decodes
/// `PolyWord`-typed pointers for word-sized elements.)
#[inline]
fn decode_byte_block(
    p1_word: i64,
    off1: i64,
    p2_word: i64,
    off2: i64,
    length: i64,
) -> (*const u8, *const u8, usize, usize, usize) {
    use polyml_runtime::PolyWord;
    let p1 = PolyWord::from_bits(p1_word as usize).as_ptr::<u8>();
    let p2 = PolyWord::from_bits(p2_word as usize).as_ptr::<u8>();
    debug_assert!(
        off1 >= 0 && off2 >= 0 && length >= 0,
        "byte-block trampoline negative arg: off1={off1} off2={off2} len={length}"
    );
    #[allow(clippy::cast_sign_loss)]
    (
        p1,
        p2,
        off1.max(0) as usize,
        off2.max(0) as usize,
        length.max(0) as usize,
    )
}

/// Byte-block compare trampoline. `(p1, off1, p2, off2, length) -> tag(-1|0|1)`.
/// Returns tagged -1 if `p1[off1..] < p2[off2..]`, 0 if equal, 1 if greater.
/// Used by JIT'd `BLOCK_COMPARE_BYTE`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn block_compare_byte_trampoline(
    p1_word: i64,
    off1: i64,
    p2_word: i64,
    off2: i64,
    length: i64,
) -> i64 {
    let (p1, p2, o1, o2, len) = decode_byte_block(p1_word, off1, p2_word, off2, length);
    let ordering = unsafe {
        let s1 = std::slice::from_raw_parts(p1.add(o1), len);
        let s2 = std::slice::from_raw_parts(p2.add(o2), len);
        s1.cmp(s2)
    };
    match ordering {
        std::cmp::Ordering::Less => -1,   // tag(-1)
        std::cmp::Ordering::Equal => 1,   // tag(0)
        std::cmp::Ordering::Greater => 3, // tag(1)
    }
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
    let (p1, p2, o1, o2, len) = decode_byte_block(p1_word, off1, p2_word, off2, length);
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
    let (src, dest_const, src_o, dest_o, len) =
        decode_byte_block(src_word, src_off, dest_word, dest_off, length);
    let dest = dest_const.cast_mut();
    unsafe { std::ptr::copy(src.add(src_o), dest.add(dest_o), len) };
    1 // TAGGED(0)
}

/// Dynamic CALL_CLOSURE trampoline. The JIT'd caller has popped the
/// closure (passed as `closure_word`) and spilled its remaining
/// compile-time stack into a Cranelift StackSlot at `args_ptr` of
/// length `args_depth`. The top of that spill — the N call args — is
/// at `args_ptr[args_depth - N..args_depth]`, where N is the callee
/// arity (read from the closure's code header at runtime).
///
/// Returns the callee's result. On failure, returns tagged(0) = 1.
///
/// Tail-call only: the JIT'd caller is expected to RETURN this
/// value.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn dynamic_call_trampoline(
    closure_word: i64,
    args_ptr: *const i64,
    args_depth: i64,
) -> i64 {
    // SAFETY: args_ptr is the JIT-spilled arg buffer of length args_depth, valid
    // for the duration of this trampoline call (the caller is JIT-generated code).
    match unsafe {
        polyml_runtime::jit_dispatch_dynamic_call(closure_word as u64, args_ptr, args_depth)
    } {
        Ok(v) => v.0 as i64,
        Err(e) => {
            if std::env::var("JIT_TRAMP_PANIC_ON_ERR").is_ok() {
                eprintln!(
                    "  dynamic_call_trampoline ERR: closure=0x{closure_word:016x} \
                     depth={args_depth} err={e:?}"
                );
                std::process::abort();
            }
            1 // tag(0)
        }
    }
}

/// ALLOC_MUT_CLOSURE_B trampoline. `(n_captures, src_closure) -> i64`.
/// Allocates an (n_captures+1)-word mutable closure; slot 0 = src
/// closure's code addr; slots 1..n_captures+1 = tagged(0). The
/// captures are filled in later by MOVE_TO_MUT_CLOSURE_B.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn alloc_mut_closure_trampoline(
    n_captures: i64,
    src_closure_word: i64,
) -> i64 {
    #[allow(clippy::cast_sign_loss)]
    let n = n_captures.max(0) as usize;
    match polyml_runtime::jit_dispatch_alloc_mut_closure(n, src_closure_word as u64) {
        Some(ptr) => ptr as i64,
        None => 1,
    }
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
pub unsafe extern "C" fn alloc_byte_mem_trampoline(n_words: i64, flags: i64) -> i64 {
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
    // SAFETY: captures_ptr points at n valid capture words spilled by the
    // JIT-generated caller; valid for the duration of this trampoline call.
    match unsafe {
        polyml_runtime::jit_dispatch_closure_alloc(n, captures_ptr, src_closure_word as u64)
    } {
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
pub unsafe extern "C" fn alloc_tuple_trampoline(n_words: i64, values_ptr: *const i64) -> i64 {
    #[allow(clippy::cast_sign_loss)]
    let n = n_words.max(0) as usize;
    // SAFETY: values_ptr points at n valid tuple-element words spilled by the
    // JIT-generated caller; valid for the duration of this trampoline call.
    match unsafe { polyml_runtime::jit_dispatch_alloc(n, 0, values_ptr) } {
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
        let isa_builder = cranelift_native::builder().map_err(|e| JitError::Isa(e.to_string()))?;
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
            "polyml_jit_block_compare_byte",
            block_compare_byte_trampoline as *const u8,
        );
        builder.symbol(
            "polyml_jit_get_thread_id",
            get_thread_id_trampoline as *const u8,
        );
        builder.symbol(
            "polyml_jit_alloc_mut_closure",
            alloc_mut_closure_trampoline as *const u8,
        );
        builder.symbol(
            "polyml_jit_dynamic_call",
            dynamic_call_trampoline as *const u8,
        );
        // Whole-region nativeness probe (region.rs). Lets a compiled
        // region prove NATIVE execution via a per-entry counter bump.
        builder.symbol(
            "polyml_jit_region_native_tick",
            region::region_native_tick as *const u8,
        );
        // Whole-region DYNAMIC-call trampoline (S4e). A region's
        // CALL_LOCAL_B / CALL_CLOSURE calls this to re-enter the
        // interpreter's do_call for a non-static target.
        builder.symbol(
            "polyml_jit_region_interp_call",
            boundary::polyml_jit_region_interp_call as *const u8,
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
        assert_eq!(
            f(tagged_3),
            tagged_6,
            "double of tagged 3 should be tagged 6"
        );

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
