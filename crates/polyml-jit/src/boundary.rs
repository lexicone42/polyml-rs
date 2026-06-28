//! S3 — the interpreter `do_call` BOUNDARY DISPATCH for whole-region JIT.
//!
//! When the interpreter is about to call a code object that has a
//! compiled region root, it hands the region its REAL `sp` + `stack_base`
//! + a real `ExnCtx` (handler_sp / exn_packet mirroring the interp's),
//! calls the native region, then consumes `RegionRet { new_sp, raised }`.
//!
//! - On `raised == 0`: sets `interp.sp = new_sp` and continues (the
//!   single result is on top at `stack[new_sp]`).
//! - On `raised == 1`: maps the region's exception sentinel onto the
//!   interpreter's real raise machinery, unwinding to `handler_sp`.
//!
//! The region shares the interpreter's ACTUAL `Box` stack (NOT a scratch
//! stack), so GC scanning `[sp, len)` covers region frames for free.
//!
//! =====================================================================
//! THE FRAME HANDSHAKE AT THE BOUNDARY (the make-or-break)
//! =====================================================================
//! The interpreter's `do_call` (mod.rs:5981) at the moment of the call
//! has the caller-pushed args on top (top arg at `stack[sp]`), then it
//! pushes `retPC` and `closure` and jumps. So at callee entry the
//! downward stack is:
//!
//!   stack[sp]     = closure        (LOCAL_0)
//!   stack[sp+1]   = retPC          (LOCAL_1)
//!   stack[sp+2]   = arg_{N-1}      (LOCAL_2, top arg)
//!   ...
//!   stack[sp+N+1] = arg_0          (LOCAL_{N+1}, deepest arg)
//!
//! The boundary replicates this EXACTLY: starting from the interp `sp`
//! (which points at the top arg the caller pushed), it pushes a retPC
//! placeholder then the closure, leaving `sp` pointing at the closure —
//! then invokes the region root with that `sp`. The region's RETURN_N
//! collapses result+closure+retPC+N args (collapse by N+2), so the
//! native `new_sp` points at the single result on top — byte-identical to
//! what the interpreter's `do_return` would have produced. The boundary
//! sets `interp.sp = new_sp` and the result sits at `stack[new_sp]`.
//!
//! This module also carries a SELF-CONTAINED demo that builds a REAL
//! region (genuine PolyML code objects in a real heap, root + a
//! statically-known CALL_CONST_ADDR callee), runs it BOTH ways (the pure
//! interpreter via `do_call`, and the native region via this boundary),
//! and proves the results are byte-identical + the region ran NATIVE.

#![allow(clippy::pedantic, clippy::nursery, clippy::doc_lazy_continuation)]
#![allow(
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap
)]

use crate::Jit;
use crate::memtrans::{self, CompiledMemRegion, EXN_DIVZERO, EXN_OVERFLOW};
use crate::region::{ExnCtx, RegionFn, native_tick_count, reset_native_tick};

/// Outcome of a region invocation through the boundary.
#[derive(Debug, Clone, Copy)]
pub enum BoundaryOutcome {
    /// Normal return: the single result is at `stack[new_sp]`.
    Returned { new_sp: i64 },
    /// An exception propagated past the region. `packet` is the region's
    /// sentinel (EXN_OVERFLOW / EXN_DIVZERO / a raised packet's bits) and
    /// `handler_sp` is where the interpreter should resume (or NO_HANDLER
    /// for an uncaught escape — the caller turns it into a halt).
    Raised { packet: i64, handler_sp: i64 },
}

/// Invoke a compiled region root through the boundary on the REAL shared
/// stack. `stack_base` is `interp.stack.as_mut_ptr()`; `sp_at_top_arg` is
/// the interpreter's `sp` AT THE CALL (pointing at the top caller-pushed
/// arg); `closure_bits` is the closure word the interpreter would push;
/// `ctx` carries handler_sp + exn_packet (mirroring the interp). Returns
/// the `RegionRet` interpretation.
///
/// THE FRAME HANDSHAKE: the boundary pushes retPC (placeholder 0) then
/// the closure on top of the args, so the region root sees the EXACT
/// interpreter callee-entry layout (closure = LOCAL_0). It then invokes
/// the native root with `sp` pointing at the closure.
///
/// # Safety
/// `stack_base` must point at a valid `[i64]` covering all the sp indices
/// the region touches; `region_fn` must be a finalized region root with
/// the [`RegionFn`] ABI; `ctx` must be a valid `*mut ExnCtx`.
pub unsafe fn dispatch_region(
    region_fn: RegionFn,
    stack_base: *mut i64,
    sp_at_top_arg: i64,
    closure_bits: i64,
    ctx: *mut ExnCtx,
) -> BoundaryOutcome {
    // SAFETY: caller-upheld stack/ctx validity.
    unsafe {
        // Push retPC placeholder then closure (mirror do_call). Downward:
        // sp -= 1 each push.
        let sp_ret = sp_at_top_arg - 1;
        *stack_base.add(sp_ret as usize) = 0; // retPC placeholder
        let sp_clo = sp_ret - 1;
        *stack_base.add(sp_clo as usize) = closure_bits; // closure (LOCAL_0)

        // Invoke the native region root.
        let ret = region_fn(stack_base, sp_clo, ctx);
        if ret.raised == 0 {
            BoundaryOutcome::Returned { new_sp: ret.new_sp }
        } else {
            let packet = (*ctx).exn_packet;
            BoundaryOutcome::Raised {
                packet,
                handler_sp: ret.new_sp,
            }
        }
    }
}

/// Human-readable name for a region exception sentinel (so the
/// boundary's raise mapping is auditable).
#[must_use]
pub fn exn_sentinel_name(packet: i64) -> &'static str {
    match packet {
        EXN_OVERFLOW => "Overflow",
        EXN_DIVZERO => "Div",
        _ => "(raised value)",
    }
}

// =====================================================================
// SELF-CONTAINED REAL-REGION DEMO — genuine PolyML code objects, run
// both ways (pure interp via do_call + native region via the boundary),
// proven byte-identical + native.
// =====================================================================

use polyml_runtime::interpreter::opcodes as op;
use polyml_runtime::length_word::{F_CLOSURE_OBJ, F_CODE_OBJ};
use polyml_runtime::space::{MemorySpace, SpaceKind, set_length_word};
use polyml_runtime::{Interpreter, PolyWord, StepResult};

/// A built code object + its closure, living in a `MemorySpace`.
struct BuiltCode {
    /// Closure PolyWord (word 0 = code object pointer).
    closure: PolyWord,
    /// Code object body address (= what the region builder roots on).
    code_addr: u64,
}

/// Lay out a real PolyML code object in `space`: `bytecode` (padded to a
/// word boundary), then `n_consts` constant words, then the
/// trailing-offset word — exactly matching `const_segment_for_code`'s
/// expected layout (see mod.rs `test_build_runnable_closure` +
/// length_word.rs). `consts` are the constant-pool words (e.g. callee
/// closures the bytecode's CALL_CONST_ADDR reads). Returns the closure.
fn build_code_object(space: &mut MemorySpace, bytecode: &[u8], consts: &[PolyWord]) -> BuiltCode {
    let word = std::mem::size_of::<usize>();
    let code_words = bytecode.len().div_ceil(word);
    let n_consts = consts.len();
    // Layout (words): [code_words bytecode] [n_consts const words]
    //                 [1 word: n_consts count] [1 word: const-base offset]
    // const_segment_for_code reads the LAST word as a signed byte offset
    // from (last_word+1); cp[-1] holds the count. So:
    //   - the const words sit at indices [code_words .. code_words+n_consts)
    //   - cp = first const word ⇒ cp[-1] = the count word must be the slot
    //     JUST before the first const word.
    // We arrange: [bytecode][count][consts...][trailer], with the trailer
    // pointing back to the first const. That makes cp[-1] = count.
    //
    // Index map:
    //   0 .. code_words            : bytecode
    //   code_words                 : count (= n_consts)
    //   code_words+1 .. +1+n_consts: const words (cp starts here)
    //   total-1                    : trailer (signed byte offset)
    let total_words = code_words + 1 + n_consts + 1;
    let code_obj = space.alloc(total_words);
    // SAFETY: just allocated total_words.
    unsafe {
        let dst = code_obj.cast::<u8>();
        std::ptr::copy_nonoverlapping(bytecode.as_ptr(), dst, bytecode.len());
        // Pad the bytecode region to a word boundary with NO_OP (0x52),
        // NOT 0x00 — the region pre-flight scan walks the whole bytecode
        // region, and 0x00 is an unknown opcode (would force a bail). The
        // pad is dead (after a RETURN) and never executed by the interp.
        let pad = bytecode.len().next_multiple_of(word) - bytecode.len();
        for i in 0..pad {
            dst.add(bytecode.len() + i).write(op::INSTR_NO_OP);
        }
        // count word
        code_obj
            .add(code_words)
            .write(PolyWord::from_bits(n_consts));
        // const words
        let cp_index = code_words + 1;
        for (i, c) in consts.iter().enumerate() {
            code_obj.add(cp_index + i).write(*c);
        }
        // trailer: byte offset s.t. (last_word+1) + offset/word == cp.
        // last_word index = total_words - 1. cp index = cp_index.
        // offset_words = cp_index - (last_word_index + 1) = cp_index - total_words.
        let last_word_index = (total_words - 1) as isize;
        let offset_words = cp_index as isize - (last_word_index + 1);
        let offset_bytes = offset_words * word as isize;
        code_obj
            .add(total_words - 1)
            .write(PolyWord::from_bits(offset_bytes as usize));
        set_length_word(code_obj, total_words, F_CODE_OBJ);
    }
    // Closure: 1 word = code object pointer.
    let closure = space.alloc(1);
    // SAFETY: 1-word closure.
    unsafe {
        closure
            .add(0)
            .write(PolyWord::from_ptr(code_obj.cast_const()));
        set_length_word(closure, 1, F_CLOSURE_OBJ);
    }
    BuiltCode {
        closure: PolyWord::from_ptr(closure.cast_const()),
        code_addr: code_obj as u64,
    }
}

/// Emit a CALL_CONST_ADDR8_8 that reads constant index `const_idx` (0 =
/// first const word) at a PC byte offset of 0. The interpreter formula
/// (read_pc_const) is `read at (pc_after_immediates) + byte_off +
/// idx*8`, where idx = imm2 + 3 for the _8_8 variant. The pc_after is
/// relative to the bytecode; but the const pool is contiguous AFTER the
/// bytecode in the same object, so for our hand-built object we must pick
/// byte_off so that `after + byte_off + idx*8` lands on the const word.
///
/// We instead pick `byte_off` explicitly in the demo builders below so
/// the read lands on the first const word.
///
/// Result of one real-region run, both ways.
#[derive(Debug, Clone, Copy)]
pub struct RealRegionResult {
    pub interp_result: i64,
    pub native_result: i64,
    pub native_ticks: u64,
    pub raised_interp: bool,
    pub raised_native: bool,
}

/// Build a REAL region whose root computes, with a statically-known
/// CALL_CONST_ADDR callee:
///
///   sum3(a, b, c) = add(a, b) + c          (root, arity 3)
///       add(x, y) = x + y                  (callee, arity 2)
///
/// Both functions are genuine PolyML bytecode (the interpreter executes
/// them via `do_call` / `do_return`); the root reaches `add` via a
/// constant-pool closure (CALL_CONST_ADDR) — exactly the non-popping
/// call the per-function JIT bails on. Returns (root_closure, root_addr,
/// add_closure) plus the interpreter that owns the heap.
///
/// The bytecode is constructed by hand from the real opcode constants so
/// it is byte-for-byte what the SML compiler emits for this shape: args
/// are at LOCAL_2.. (LOCAL_0=closure, LOCAL_1=retPC); a CALL_CONST_ADDR
/// pushes args then calls; RETURN_N collapses.
fn build_sum3_region(space: &mut MemorySpace) -> (BuiltCode, BuiltCode) {
    // ---- callee add(x, y) = x + y, arity 2 ----
    // At entry: LOCAL_0=closure, LOCAL_1=retPC, LOCAL_2=y(top), LOCAL_3=x.
    // Push x (LOCAL_3), push y (now at LOCAL_3 again after first push?).
    // Carefully: after pushing one value, depths shift by +1. We compute
    // x + y. The simplest faithful sequence:
    //   LOCAL_3   ; push x        (x now top, everything below +1)
    //   LOCAL_3   ; push y        (was LOCAL_2 before this push; after the
    //               first push y moved to depth 3)
    //   FIXED_ADD ; pop y, pop x, push (x+y)
    //   RETURN_B 2
    // Let's verify depths: entry sp at closure.
    //   stack: [clo, ret, y, x, ...]  (sp..)
    //   LOCAL_3 -> reads stack[sp+3] = x ; push -> stack[sp-1]=x; sp-=1.
    //   now stack: [x, clo, ret, y, x, ...]; sp at x.
    //   LOCAL_3 -> reads stack[sp+3] = y ; push -> y on top.
    //   now: [y, x, clo, ret, y, x]; FIXED_ADD pops y,x pushes y+x? interp
    //   FIXED_ADD = x_top + y_below = y + x. push (x+y). sp now at result.
    //   RETURN_B 2: result+clo+ret+2 args collapse.
    let add_bc = vec![
        op::INSTR_LOCAL_3,
        op::INSTR_LOCAL_3,
        op::INSTR_FIXED_ADD,
        op::INSTR_RETURN_B,
        2,
    ];
    let add = build_code_object(space, &add_bc, &[]);

    // ---- root sum3(a, b, c) = add(a, b) + c, arity 3 ----
    // At entry: LOCAL_0=clo, LOCAL_1=ret, LOCAL_2=c(top), LOCAL_3=b, LOCAL_4=a.
    // To call add(a, b): push a then b (b on top), then CALL_CONST_ADDR
    // (which reads the add closure from the const pool, pushes ret+clo,
    // jumps). add's RETURN_B 2 collapses to leave its result on top, with
    // the 2 args + ret + clo gone — net: the call replaced (a,b) on the
    // stack with one result. So after the call, sp points at add's result.
    //   LOCAL_4   ; push a   (a top)
    //   LOCAL_4   ; push b   (b was LOCAL_3; after first push it's LOCAL_4)
    //   CALL_CONST_ADDR8_8 <byte_off> <imm2>  ; call add(a,b)
    //   -- after the call: result of add on top (sp points at it) --
    //   LOCAL_3   ; push c   (c was LOCAL_2; the call left ONE result on
    //               top where the 2 args were ⇒ net stack height same as
    //               before the 2 arg pushes; so c is back at LOCAL_? )
    //   FIXED_ADD ; (add_result) + c
    //   RETURN_B 3
    //
    // Depth bookkeeping for `c` after the call: before the 2 arg pushes,
    // sp pointed at the root's working area; c was at LOCAL_2. We pushed 2
    // args (sp-=2), called add; add's RETURN collapsed result+clo+ret+2
    // args so sp = (sp_after_2_pushes) + 4 = original_sp + 2 ... wait:
    // do_return collapses N+2 from the callee's entry sp. The callee entry
    // sp = (root sp after pushing a,b) - 2 (the ret+clo). So:
    //   root_sp0 = entry working sp (points at c=LOCAL_2... actually
    //   LOCAL_2 is depth 2 from sp0). Let sp0 = root entry sp.
    //   push a: sp1 = sp0 - 1
    //   push b: sp2 = sp0 - 2
    //   do_call pushes ret,clo: callee entry sp = sp0 - 4.
    //   add RETURN_B 2 collapses N+2 = 4: new_sp = (sp0-4) + 4 = sp0.
    //   result lands at stack[sp0]. So after the call sp = sp0 and the
    //   add result is at stack[sp0] (replacing what was c=LOCAL_2!).
    // That OVERWRITES c. So we must read c BEFORE the call, or the
    // compiler would keep c deeper. The real compiler reads operands in
    // an order that doesn't clobber live values. Simplest correct shape:
    // push c FIRST (so it's deeper and survives), then compute add(a,b),
    // then add. But FIXED_ADD needs both operands on top. So:
    //   LOCAL_2   ; push c              (c saved on top; depths shift +1)
    //   LOCAL_5   ; push a   (a was LOCAL_4; +1 ⇒ LOCAL_5)
    //   LOCAL_5   ; push b   (b was LOCAL_3; +1 from c, +1 from a ⇒ LOCAL_5)
    //   CALL_CONST_ADDR8_8 ...   ; add(a,b) ⇒ result replaces the 2 args,
    //                              leaving [add_result, c, clo,ret,c,b,a]
    //                              with sp at add_result; c is at LOCAL_1?
    //   Let's recompute: after `push c`: spc = sp0-1, c at stack[spc].
    //     push a: spa = sp0-2. push b: spb = sp0-3.
    //     do_call ret,clo: callee entry = sp0-5. add RETURN collapses 4:
    //       new_sp = sp0-5+4 = sp0-1. result at stack[sp0-1].
    //     But stack[sp0-1] was c! So the add result OVERWRITES c again.
    // The issue: do_return collapses to the deepest of {result,clo,ret,args}
    //   = the deepest arg slot = stack[callee_entry + (N+2)] which is the
    //   slot of the DEEPEST collapsed item. The deepest arg is arg_0 = the
    //   first pushed of the call (here `a` at spa=sp0-2). So result lands
    //   at stack[sp0-2]?? Let me defer to do_return's exact arithmetic.
    //
    // do_return pops result, clo, ret, then N args (top-down), then pushes
    // result. In our downward stack that means: starting sp = callee entry
    // (points at result). pop result (sp+1), pop clo (sp+1), pop ret
    // (sp+1), pop N args (sp+N). Now sp = entry + 3 + N. push result
    // (sp-1). Final sp = entry + 2 + N, result at stack[entry+2+N].
    // entry = sp0 - 5 (after push c,a,b + ret,clo). N=2. final =
    // sp0-5+2+2 = sp0-1. So result at stack[sp0-1] — which is c. CLOBBERED.
    //
    // So pushing c first does NOT save it (the call collapses back over
    // it). The faithful pattern the compiler uses keeps c in a slot the
    // call's collapse doesn't reach: c must be DEEPER than the deepest
    // collapsed slot. The deepest collapsed slot is the deepest arg
    // (arg_0). If we push c, then a, then b, the call collapses [result..
    // through arg_0=a@sp0-2]; c@sp0-1 is SHALLOWER than a@sp0-2, so c is
    // NOT collapsed — it survives, and result lands at sp0-2 (a's slot),
    // which is DEEPER than c. After the call sp points at result@sp0-2,
    // and c is at stack[sp0-2 + 1] = stack[sp0-1] = LOCAL_1 from the new
    // sp. Good — c survives as LOCAL_1.
    //
    // Wait: final sp = entry+2+N = (sp0-5)+4 = sp0-1, NOT sp0-2. Let me
    // redo with entry=sp0-5, N=2: final = sp0-5+2+2 = sp0-1. Hmm that's
    // c's slot again. The discrepancy: "deepest collapsed slot" reasoning
    // vs the pop/push count. Trust the pop/push count: final sp = sp0-1,
    // result at sp0-1. That IS c's slot.
    //
    // The resolution: c is at sp0-1 only if we pushed c FIRST (spc=sp0-1).
    // Then pushed a (sp0-2), b (sp0-3). entry after ret,clo = sp0-5.
    // collapse leaves result at sp0-1. c WAS at sp0-1 ⇒ overwritten. So
    // pushing c first is wrong.
    //
    // Correct: DON'T pre-push c. Instead, do add(a,b), then read c from
    // its ORIGINAL deep slot (which the call did not disturb, because the
    // call only touched slots ABOVE sp0). Before the call, c is at
    // stack[sp0+2] (LOCAL_2). The call pushes onto slots < sp0 and
    // collapses back to sp0-... ; crucially it NEVER writes at indices
    // >= sp0+1 except... result lands at sp0-1 < sp0+2. So c at sp0+2 is
    // untouched. After the call sp = sp0-1, so c is at depth (sp0+2) -
    // (sp0-1) = 3 ⇒ LOCAL_3.
    //
    //   LOCAL_4   ; push a   (a=LOCAL_4 at sp0)  → sp0-1
    //   LOCAL_4   ; push b   (b=LOCAL_3 at sp0; +1 after a ⇒ LOCAL_4) → sp0-2
    //   CALL_CONST_ADDR8_8   ; → sp = sp0-1, add_result at stack[sp0-1]
    //   LOCAL_3   ; push c   (c at sp0+2; from sp0-1 that's depth 3)
    //   FIXED_ADD ; add_result + c → result, sp at sp0-2
    //   RETURN_B 3
    //
    // Now check: after FIXED_ADD, the two operands (add_result@sp0-1, c
    // pushed at sp0-2) are popped, result pushed → sp at sp0-2, result at
    // stack[sp0-2]. RETURN_B 3 from the ROOT: root entry sp = sp0 (points
    // at closure). do_return: pop result, clo, ret, 3 args, push result →
    // final sp = sp0 + 2 + 3 = sp0+5? Let me just let the interpreter and
    // the native region BOTH execute this and compare — that is the
    // differential. The arithmetic above is the design; the test is the
    // proof.
    //
    // We build the CALL_CONST_ADDR8_8 to read const index 0 (the add
    // closure). For our hand-built object, byte_off must make
    //   after + byte_off + idx*8  (idx = imm2+3)
    // land on the first const word. `after` = pc immediately past the
    // 3-byte CALL_CONST_ADDR8_8. We place the call such that the const
    // pool starts right after the bytecode; the read is an ABSOLUTE
    // address = code_start + after + byte_off + idx*8. The first const
    // word is at code_start + (code_words)*8 ... but the count word sits
    // at code_words and consts start at code_words+1. So the first const
    // (add closure) is at byte (code_words+1)*8.
    //
    // We pick imm2 = 0 ⇒ idx = 3, and byte_off so that:
    //   after + byte_off + 3*8 == (code_words+1)*8
    // We solve byte_off at build time once we know `after` and code_words.
    // To keep this deterministic we compute the full bytecode first with a
    // placeholder, then patch byte_off.
    //
    // Root bytecode with a placeholder for CALL_CONST_ADDR8_8's byte_off:
    let mut root_bc = vec![
        op::INSTR_LOCAL_4,            // push a
        op::INSTR_LOCAL_4,            // push b
        op::INSTR_CALL_CONST_ADDR8_8, // call add(a,b)
        0x00,                         // byte_off (patched below)
        0x00,                         // imm2 (idx = imm2 + 3 = 3)
        op::INSTR_LOCAL_3,            // push c
        op::INSTR_FIXED_ADD,          // add_result + c
        op::INSTR_RETURN_B,           // return
        3,
    ];
    // The CALL_CONST_ADDR8_8 reads the const at:
    //   read = pc_after_call + byte_off + idx*8   (idx = imm2 + 3)
    // where pc_after_call is byte 5 (the CALL is at index 2, 3 immediate
    // bytes). The first const word (the add closure) sits at object byte
    // (code_words + 1)*8 (after the bytecode + the count word). With idx
    // fixed at 3 (imm2 = 0), byte_off = (code_words+1)*8 - 5 - 24, which is
    // NEGATIVE for a short bytecode (the const pool is too close to the
    // call). Real bytecode is long enough that byte_off is small +
    // positive; our toy bytecode is short, so we PAD it with trailing
    // NO_OPs (dead code after RETURN, walked but harmless) until byte_off
    // lands in [0, 255]. NO_OP is in the core subset, so the region still
    // compiles fully.
    let word = std::mem::size_of::<usize>();
    let after = 5usize;
    let idx = 3usize; // imm2(0) + 3
    loop {
        let code_words = root_bc.len().div_ceil(word);
        let first_const_byte = (code_words + 1) * word;
        let byte_off = first_const_byte as i64 - after as i64 - (idx * 8) as i64;
        if (0..=255).contains(&byte_off) {
            root_bc[3] = byte_off as u8;
            break;
        }
        // Pad one NO_OP (after the RETURN — dead but valid) and retry.
        root_bc.push(op::INSTR_NO_OP);
        assert!(root_bc.len() < 4096, "root bytecode pad runaway");
    }

    let root = build_code_object(space, &root_bc, &[add.closure]);
    (root, add)
}

/// Build a SELF-RECURSIVE region (the harder handshake case):
///
///   sumto(n) = if n <= 0 then 0 else n + sumto(n - 1)     (arity 1)
///
/// This single function calls ITSELF via CALL_CONST_ADDR (the closure in
/// its own constant pool points at its own code object) and exercises the
/// JUMP family (JUMP8_FALSE), a comparison (LESS_EQ_SIGNED), FIXED_SUB +
/// FIXED_ADD, and a self-recursive non-popping native call whose result
/// is CONSUMED mid-function (`n + sumto(n-1)`). The recursion depth makes
/// the frame handshake load-bearing at every level. Returns the sumto
/// closure + its code address.
// The bytecode is built push-by-push so each opcode's offset is tracked
// for the jump/call patching; a Vec-literal would obscure the offset
// bookkeeping the comments depend on.
#[allow(clippy::vec_init_then_push)]
fn build_sumto_region(space: &mut MemorySpace) -> BuiltCode {
    // sumto(n), arity 1. Entry: LOCAL_0=closure, LOCAL_1=retPC, LOCAL_2=n.
    //
    //   LOCAL_2          ; push n
    //   CONST_0          ; push 0
    //   LESS_EQ_SIGNED   ; n <= 0 ?  (y<=x => n<=0)
    //   JUMP8_FALSE Lrec ; if NOT (n<=0) goto recursive
    //   CONST_0          ; base: 0
    //   RETURN_B 1
    // Lrec:
    //   LOCAL_2          ; push n          (for n-1)
    //   CONST_1          ; push 1
    //   FIXED_SUB        ; n - 1           (y - x)
    //   CALL_CONST_ADDR8_8 byte_off 0 ; sumto(n-1), result at new sp top
    //   LOCAL_2          ; push n (original, survives the call at LOCAL_2)
    //   FIXED_ADD        ; n + sumto(n-1)
    //   RETURN_B 1
    //
    // The branch geometry is verified by the differential: the native
    // region and the interpreter must agree across all n.
    //
    // We assemble with a placeholder CALL byte_off, locate the CALL's pc,
    // and patch byte_off so the CALL reads const index 0 (the self
    // closure). The base-case and recursive paths are laid out so the
    // JUMP8_FALSE target (Lrec) is a real instruction boundary.
    let mut bc: Vec<u8> = Vec::new();
    // [0] header / cond
    bc.push(op::INSTR_LOCAL_2); // 0
    bc.push(op::INSTR_CONST_0); // 1
    bc.push(op::INSTR_LESS_EQ_SIGNED); // 2
    bc.push(op::INSTR_JUMP8_FALSE); // 3
    let jump_off_idx = bc.len(); // 4 (offset byte, patched)
    bc.push(0x00); // 4: jump offset (patched)
    // base case
    bc.push(op::INSTR_CONST_0); // 5
    bc.push(op::INSTR_RETURN_B); // 6
    bc.push(1); // 7
    let lrec = bc.len(); // 8: recursive entry
    bc.push(op::INSTR_LOCAL_2); // 8: push n
    bc.push(op::INSTR_CONST_1); // 9: push 1
    bc.push(op::INSTR_FIXED_SUB); // 10: n-1
    let call_pc = bc.len(); // 11
    bc.push(op::INSTR_CALL_CONST_ADDR8_8); // 11
    let call_off_idx = bc.len(); // 12 (byte_off, patched)
    bc.push(0x00); // 12: byte_off
    bc.push(0x00); // 13: imm2 (idx = 3)
    // After the call, sp = entry_sp - 1 (the callee's result is on top,
    // one slot ABOVE the entry frame). The original arg n was at LOCAL_2
    // (= entry_sp + 2); from the post-call sp that is depth 3 => LOCAL_3.
    bc.push(op::INSTR_LOCAL_3); // 14: push n (original; LOCAL_3 post-call)
    bc.push(op::INSTR_FIXED_ADD); // 15: n + sumto(n-1)
    bc.push(op::INSTR_RETURN_B); // 16
    bc.push(1); // 17

    // JUMP8_FALSE: interp lands at (pc_after_immediates) + off. The opcode
    // is at index 3; pc_after = 5. Target = Lrec = 8. off = 8 - 5 = 3.
    let jump_after = 3 + 2; // opcode idx 3 + 2 immediate-consuming fetches
    let joff = lrec as i64 - jump_after as i64;
    assert!((0..=255).contains(&joff), "jump off {joff} out of range");
    bc[jump_off_idx] = joff as u8;

    // CALL_CONST_ADDR8_8 reads const idx 3 at: pc_after_call + byte_off +
    // 3*8, where pc_after_call = call_pc + 3. The first const (the self
    // closure) is at object byte (code_words+1)*8. Pad bc with NO_OP after
    // the final RETURN until byte_off lands in [0,255].
    let word = std::mem::size_of::<usize>();
    let call_after = call_pc + 3;
    let idx = 3usize;
    let byte_off;
    loop {
        let code_words = bc.len().div_ceil(word);
        let first_const_byte = (code_words + 1) * word;
        let bo = first_const_byte as i64 - call_after as i64 - (idx * 8) as i64;
        if (0..=255).contains(&bo) {
            byte_off = bo as u8;
            break;
        }
        bc.push(op::INSTR_NO_OP);
        assert!(bc.len() < 4096, "sumto pad runaway");
    }
    bc[call_off_idx] = byte_off;

    // Build with a placeholder const (ZERO), then patch it with the self
    // closure once the closure exists.
    let built = build_code_object(space, &bc, &[PolyWord::ZERO]);
    // Patch the const-pool slot (index 0) with the self closure. The const
    // word sits at object word (code_words + 1).
    let code_words = bc.len().div_ceil(word);
    let cp_index = code_words + 1;
    // SAFETY: code_addr is a live code object in `space`; cp_index is a
    // valid const-pool slot we laid out in build_code_object.
    unsafe {
        let code_obj = built.code_addr as *mut PolyWord;
        code_obj.add(cp_index).write(built.closure);
    }
    built
}

/// Run the sum3 region BOTH ways and report the differential. `a, b, c`
/// are the SML int args.
///
/// Pure interp path: seed a real `Interpreter` over the shared heap,
/// push the 3 args, invoke `do_call(root_closure)`, run to Returned.
///
/// Native path: compile the region from the root code-object address,
/// finalize, then run it through [`dispatch_region`] on a fresh shared
/// stack with the same 3 args. The result + the native-tick count prove
/// NATIVE execution.
pub fn run_sum3_both_ways(a: isize, b: isize, c: isize) -> RealRegionResult {
    // ---- shared heap with the region's code objects ----
    let mut space = MemorySpace::new(4096, SpaceKind::Code);
    let (root, _add) = build_sum3_region(&mut space);
    let root_addr = root.code_addr;
    let root_closure = root.closure;

    // ---- (1) PURE INTERP: enter the root as the top-level function ----
    // Build the EXACT callee-entry frame the interpreter's do_call would
    // produce: push args (a deepest), then retPC=0 (sentinel ⇒ Returned),
    // then the root closure (LOCAL_0). Then point the PC at the root code
    // object and run. The root's RETURN_B 3 collapses result+clo+ret+3
    // args; retPC=0 ⇒ Returned(result). This frame is byte-identical to
    // what the native boundary builds.
    let interp_result = {
        let mut interp = Interpreter::from_bytes(256, vec![]).with_alloc_space(space);
        interp.test_seed_top(PolyWord::tagged(a)); // deepest arg (LOCAL_4)
        interp.test_seed_top(PolyWord::tagged(b)); // LOCAL_3
        interp.test_seed_top(PolyWord::tagged(c)); // top arg (LOCAL_2)
        interp.test_seed_return_sentinel(); // retPC = 0 (LOCAL_1)
        interp.test_seed_top(root_closure); // closure (LOCAL_0)
        // SAFETY: root_addr is a live code object in `space`, now owned by
        // `interp`.
        unsafe { interp.set_code_segment_to_code_obj(root_addr as usize) };
        let r = match interp.run() {
            Ok(StepResult::Returned(w)) => (w.0 as i64, false),
            Ok(other) => panic!("interp did not return cleanly: {other:?}"),
            Err(e) => panic!("interp error: {e:?}"),
        };
        // Keep the heap alive (the interp owns it; the native path uses a
        // fresh, independent heap).
        std::mem::forget(interp);
        r
    };

    // ---- (2) NATIVE region via the boundary ----
    // Rebuild the region in a fresh heap so the addresses are independent
    // of the interp's (the native path reads the code objects from this
    // heap). We keep the heap alive for the duration of the native call.
    let mut native_space = MemorySpace::new(4096, SpaceKind::Code);
    let (native_root, _native_add) = build_sum3_region(&mut native_space);
    let native_root_addr = native_root.code_addr;
    let native_closure_bits = native_root.closure.0 as i64;

    let mut jit = Jit::new().expect("jit");
    // SAFETY: native_root_addr is a live code object in native_space,
    // which we keep alive below.
    let region: CompiledMemRegion =
        match unsafe { memtrans::build_region(&mut jit, native_root_addr) } {
            Ok(r) => r,
            Err(e) => panic!("region build bailed: {e}"),
        };
    jit.module.finalize_definitions().expect("finalize region");
    let ptr = jit.module.get_finalized_function(region.root);
    // SAFETY: region.root has the RegionFn ABI.
    let region_fn: RegionFn = unsafe { std::mem::transmute::<*const u8, RegionFn>(ptr) };

    // Fresh shared stack: push the 3 args (a deepest, c on top), sp at c.
    let cap = 256usize;
    let mut stack = vec![0i64; cap];
    stack[cap - 1] = PolyWord::tagged(a).0 as i64; // arg a (deepest, LOCAL_4)
    stack[cap - 2] = PolyWord::tagged(b).0 as i64; // arg b (LOCAL_3)
    stack[cap - 3] = PolyWord::tagged(c).0 as i64; // arg c (top, LOCAL_2)
    let sp_top_arg = (cap - 3) as i64;
    let mut ctx = ExnCtx::default();
    reset_native_tick();
    // SAFETY: stack covers all indices; region_fn is the finalized root;
    // ctx is valid.
    let outcome = unsafe {
        dispatch_region(
            region_fn,
            stack.as_mut_ptr(),
            sp_top_arg,
            native_closure_bits,
            &mut ctx,
        )
    };
    let ticks = native_tick_count();
    let (native_result, raised_native) = match outcome {
        BoundaryOutcome::Returned { new_sp } => (stack[new_sp as usize], false),
        BoundaryOutcome::Raised { .. } => (0, true),
    };
    // keep heaps alive across the native call
    let _ = native_root_addr;
    let _ = (native_root, _native_add, _add);
    let _ = root_addr; // (the interp-side addr; consumed for clarity)
    // native_space must outlive the native call (the region reads code
    // objects from it). It is dropped here, AFTER dispatch_region returned.
    drop(native_space);

    RealRegionResult {
        interp_result: interp_result.0,
        native_result,
        native_ticks: ticks,
        raised_interp: interp_result.1,
        raised_native,
    }
}

/// Run the SELF-RECURSIVE sumto region BOTH ways for `n`. The recursion
/// happens through native `call` instructions on the SHARED stack (no
/// per-call trampoline), at depth n. `native_ticks` counts every native
/// entry to sumto (= n+1 invocations), proving native recursion.
pub fn run_sumto_both_ways(n: isize) -> RealRegionResult {
    // ---- (1) PURE INTERP: enter sumto as the top-level function ----
    let interp_result = {
        let mut space = MemorySpace::new(8192, SpaceKind::Code);
        let f = build_sumto_region(&mut space);
        let f_addr = f.code_addr;
        let f_closure = f.closure;
        let mut interp = Interpreter::from_bytes(4096, vec![]).with_alloc_space(space);
        interp.test_seed_top(PolyWord::tagged(n)); // arg n (LOCAL_2)
        interp.test_seed_return_sentinel(); // retPC = 0 (LOCAL_1)
        interp.test_seed_top(f_closure); // closure (LOCAL_0)
        // SAFETY: f_addr is a live code object now owned by `interp`.
        unsafe { interp.set_code_segment_to_code_obj(f_addr as usize) };
        let r = match interp.run() {
            Ok(StepResult::Returned(w)) => (w.0 as i64, false),
            Ok(other) => panic!("interp did not return cleanly: {other:?}"),
            Err(e) => panic!("interp error: {e:?}"),
        };
        std::mem::forget(interp);
        r
    };

    // ---- (2) NATIVE region via the boundary ----
    let mut native_space = MemorySpace::new(8192, SpaceKind::Code);
    let f = build_sumto_region(&mut native_space);
    let f_addr = f.code_addr;
    let f_closure_bits = f.closure.0 as i64;

    let mut jit = Jit::new().expect("jit");
    // SAFETY: f_addr is a live code object in native_space.
    let region = match unsafe { memtrans::build_region(&mut jit, f_addr) } {
        Ok(r) => r,
        Err(e) => panic!("sumto region build bailed: {e}"),
    };
    jit.module.finalize_definitions().expect("finalize");
    let ptr = jit.module.get_finalized_function(region.root);
    // SAFETY: region root has the RegionFn ABI.
    let region_fn: RegionFn = unsafe { std::mem::transmute::<*const u8, RegionFn>(ptr) };

    // Fresh shared stack: large enough for the recursion depth n. Each
    // recursive frame uses ~5 slots (n, retPC, closure + working), so a
    // comfortable margin is 16 slots/level + headroom.
    let cap = 32 * (n.unsigned_abs() + 8) + 256;
    let mut stack = vec![0i64; cap];
    stack[cap - 1] = PolyWord::tagged(n).0 as i64; // arg n (top, LOCAL_2)
    let sp_top_arg = (cap - 1) as i64;
    let mut ctx = ExnCtx::default();
    reset_native_tick();
    // SAFETY: stack covers all indices; region_fn finalized; ctx valid.
    let outcome = unsafe {
        dispatch_region(
            region_fn,
            stack.as_mut_ptr(),
            sp_top_arg,
            f_closure_bits,
            &mut ctx,
        )
    };
    let ticks = native_tick_count();
    let (native_result, raised_native) = match outcome {
        BoundaryOutcome::Returned { new_sp } => (stack[new_sp as usize], false),
        BoundaryOutcome::Raised { .. } => (0, true),
    };
    drop(native_space);

    RealRegionResult {
        interp_result: interp_result.0,
        native_result,
        native_ticks: ticks,
        raised_interp: interp_result.1,
        raised_native,
    }
}

/// CLI entry: run the REAL whole-region demo (genuine PolyML bytecode
/// region through the do_call boundary), print a differential +
/// nativeness report, return `true` iff every case is differential-clean
/// AND ran native (tick == 1 per run).
#[must_use]
pub fn run_real_region_demo() -> bool {
    println!("== S3 real-bytecode whole-region demo (WHOLE_REGION_JIT) ==");
    println!("Region: sum3(a,b,c) = add(a,b) + c  [root + 1 CALL_CONST_ADDR callee]");
    println!("  genuine PolyML code objects; run BOTH ways (interp do_call vs native boundary)");

    let mut clean = true;
    let mut cases = 0usize;
    let mut diverged = 0usize;
    let mut non_native = 0usize;
    for a in -8..=8isize {
        for b in -8..=8isize {
            for c in -4..=4isize {
                let r = run_sum3_both_ways(a, b, c);
                cases += 1;
                if r.interp_result != r.native_result || r.raised_interp != r.raised_native {
                    diverged += 1;
                    clean = false;
                    if diverged <= 5 {
                        eprintln!(
                            "  DIVERGE a={a} b={b} c={c}: interp={} native={}",
                            r.interp_result, r.native_result
                        );
                    }
                }
                if r.native_ticks != 1 {
                    non_native += 1;
                    clean = false;
                }
            }
        }
    }
    println!("  {cases} cases, {diverged} diverged, {non_native} non-native");
    {
        let r = run_sum3_both_ways(3, 4, 5);
        println!(
            "  sum3(3,4,5) = {} (untagged), expected 12; native_ticks={} (1=native)",
            PolyWord::from_bits(r.native_result as usize).untag(),
            r.native_ticks
        );
    }
    if clean {
        println!("RESULT: S3 real-region demo DIFFERENTIAL-CLEAN + NATIVE (all cases).");
    } else {
        println!("RESULT: S3 real-region demo FAILED — see counts above.");
    }
    clean
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sum3_region_value_is_correct() {
        // sum3(3,4,5) = add(3,4) + 5 = 12.
        let r = run_sum3_both_ways(3, 4, 5);
        assert_eq!(
            PolyWord::from_bits(r.interp_result as usize).untag(),
            12,
            "pure interp sum3(3,4,5) must be 12"
        );
        assert_eq!(
            PolyWord::from_bits(r.native_result as usize).untag(),
            12,
            "native region sum3(3,4,5) must be 12"
        );
        // NATIVENESS: the native root must have run exactly once.
        assert_eq!(r.native_ticks, 1, "region root must execute NATIVE once");
    }

    #[test]
    fn sum3_region_differential_clean() {
        // The native region must be byte-identical to the pure
        // interpreter across a grid of inputs AND prove native execution.
        let mut diverged = 0usize;
        let mut non_native = 0usize;
        let mut cases = 0usize;
        for a in -6..=6isize {
            for b in -6..=6isize {
                for c in -3..=3isize {
                    let r = run_sum3_both_ways(a, b, c);
                    cases += 1;
                    if r.interp_result != r.native_result || r.raised_interp != r.raised_native {
                        diverged += 1;
                        eprintln!(
                            "DIVERGE a={a} b={b} c={c}: interp=0x{:016x} native=0x{:016x}",
                            r.interp_result as u64, r.native_result as u64
                        );
                    }
                    if r.native_ticks != 1 {
                        non_native += 1;
                    }
                }
            }
        }
        assert_eq!(diverged, 0, "{diverged}/{cases} cases diverged from interp");
        assert_eq!(non_native, 0, "{non_native}/{cases} cases were non-native");
    }

    #[test]
    fn real_region_demo_clean() {
        assert!(run_real_region_demo(), "S3 real-region demo not clean");
    }

    #[test]
    fn sumto_recursive_value_is_correct() {
        // sumto(10) = 0+1+..+10 = 55.
        let r = run_sumto_both_ways(10);
        assert_eq!(
            PolyWord::from_bits(r.interp_result as usize).untag(),
            55,
            "pure interp sumto(10) must be 55"
        );
        assert_eq!(
            PolyWord::from_bits(r.native_result as usize).untag(),
            55,
            "native sumto(10) must be 55"
        );
        // NATIVENESS: every recursive entry bumps the tick (n+1 = 11 here).
        assert_eq!(
            r.native_ticks, 11,
            "native sumto(10) must re-enter the region 11 times (n+1)"
        );
    }

    #[test]
    fn sumto_recursive_differential_clean() {
        // Self-recursive region: byte-identical to the interp across n,
        // including the base case (n<=0 → 0) and deep recursion.
        let mut diverged = 0usize;
        for n in -3..=30isize {
            let r = run_sumto_both_ways(n);
            if r.interp_result != r.native_result || r.raised_interp != r.raised_native {
                diverged += 1;
                eprintln!(
                    "DIVERGE sumto({n}): interp={} native={}",
                    PolyWord::from_bits(r.interp_result as usize).untag(),
                    PolyWord::from_bits(r.native_result as usize).untag(),
                );
            }
            let expected_ticks = if n <= 0 { 1 } else { (n as u64) + 1 };
            assert_eq!(
                r.native_ticks, expected_ticks,
                "sumto({n}) native ticks: got {} want {expected_ticks}",
                r.native_ticks
            );
        }
        assert_eq!(diverged, 0, "{diverged} sumto cases diverged");
    }
}
