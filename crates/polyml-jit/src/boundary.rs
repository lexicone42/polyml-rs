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

/// C-ABI dispatch shim the interpreter's `do_call` hook invokes (via the
/// process-global `REGION_DISPATCH` pointer installed by
/// [`crate::install_whole_region`]). It performs the boundary frame
/// handshake against a finalized native region root identified by its raw
/// address `region_fn_ptr`.
///
/// The interpreter passes `polyml_runtime::ExnCtxC` (layout-identical to
/// [`ExnCtx`]) and expects `polyml_runtime::RegionRetC` back. On a normal
/// return `raised == 0` and `new_sp` points at the single result on top;
/// on an escape `raised == 1`, `ctx.exn_packet` holds the region's exn
/// sentinel and the interpreter maps it onto its real raise machinery.
///
/// # Safety
/// `region_fn_ptr` must be a finalized region root with the [`RegionFn`]
/// ABI; `stack_base` must cover all sp indices the region touches; `ctx`
/// must be a valid `*mut polyml_runtime::ExnCtxC`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn polyml_jit_region_dispatch(
    region_fn_ptr: usize,
    stack_base: *mut i64,
    sp_at_top_arg: i64,
    closure_bits: i64,
    ctx: *mut polyml_runtime::ExnCtxC,
) -> polyml_runtime::RegionRetC {
    // SAFETY: caller-upheld region/stack/ctx validity.
    unsafe {
        let region_fn: RegionFn = std::mem::transmute::<usize, RegionFn>(region_fn_ptr);
        // The runtime ExnCtxC and the JIT ExnCtx are layout-identical
        // (#[repr(C)] { i64 handler_sp; i64 exn_packet; }); reinterpret
        // the pointer so the region reads/writes the SAME memory the
        // interpreter mirrors its handler state into.
        let ctx_jit = ctx.cast::<ExnCtx>();
        let outcome = dispatch_region(region_fn, stack_base, sp_at_top_arg, closure_bits, ctx_jit);
        match outcome {
            BoundaryOutcome::Returned { new_sp } => {
                polyml_runtime::RegionRetC { new_sp, raised: 0 }
            }
            BoundaryOutcome::Raised { handler_sp, .. } => polyml_runtime::RegionRetC {
                new_sp: handler_sp,
                raised: 1,
            },
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
use polyml_runtime::length_word::{F_BYTE_OBJ, F_CLOSURE_OBJ, F_CODE_OBJ};
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

// =====================================================================
// S4a — the #2-HASH-SHAPED region (a byte-string hash fold). Genuine
// PolyML bytecode exercising the NEW Tier-1 leaf opcodes: LOAD_ML_BYTE,
// WORD_MULT, WORD_ADD, SET_STACK_VAL_B (the loop vars), JUMP_NEQ_LOCAL
// (the loop-exit decision), and WORD_MOD (the final fold). Pure leaf: NO
// alloc, NO dynamic call, NO handler. The byte buffer is passed as an arg
// (allocated as an F_BYTE_OBJ in the same heap).
// =====================================================================

/// Allocate a byte object holding `bytes` (padded to a word boundary with
/// zeros). Returns its body pointer as a PolyWord. The object is a real
/// F_BYTE_OBJ so the interpreter / region read it via LOAD_ML_BYTE exactly
/// as compiled SML would.
fn build_byte_object(space: &mut MemorySpace, bytes: &[u8]) -> PolyWord {
    let word = std::mem::size_of::<usize>();
    let n_words = bytes.len().div_ceil(word).max(1);
    let obj = space.alloc(n_words);
    // SAFETY: just allocated n_words; we write within [0, n_words*word).
    unsafe {
        let dst = obj.cast::<u8>();
        std::ptr::write_bytes(dst, 0, n_words * word);
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), dst, bytes.len());
        set_length_word(obj, n_words, F_BYTE_OBJ);
    }
    PolyWord::from_ptr(obj.cast_const())
}

/// The Rust reference for the hand-built region: the EXACT fold the
/// bytecode computes, so the differential also pins the absolute value
/// (not just interp==native). `hash(buf, len)` folds i = len down to 1,
/// accumulating `h = h*31 + buf[i-1]` (wrapping into the tagged range as
/// WORD_* arithmetic does), then returns `h mod M`.
const HASHFOLD_MULT: i64 = 31;
const HASHFOLD_MOD: i64 = 97;

#[cfg(test)]
fn hashfold_reference(buf: &[u8], len: i64) -> i64 {
    // Model the EXACT tagged-word arithmetic the bytecode performs (the
    // interp's WORD_* closures: mod.rs:4418-4451 — operate on the raw
    // `usize` tagged-word bits with `>>1` / `<<1|1` and wrapping). A naive
    // i64 fold would diverge once `h` overflows (long buffers), because the
    // `>>1 ... <<1` payload model wraps differently from full-width i64. We
    // carry `h` as a tagged word and replay each op bit-for-bit.
    let tag = |n: usize| (n << 1) | 1; // PolyWord::tagged for non-neg payloads
    let mut h: usize = tag(0);
    let mut i = len;
    while i != 0 {
        let byte = tag(buf[(i - 1) as usize] as usize);
        // WORD_MULT: ((h>>1) * (31>>1... )) — x is the multiplier word.
        let mul = tag(HASHFOLD_MULT as usize);
        let prod = (((h >> 1).wrapping_mul(mul >> 1)) << 1) | 1; // h*31 (tagged)
        // WORD_ADD: y.wrapping_add(x).wrapping_sub(tagged(0)).
        h = prod.wrapping_add(byte).wrapping_sub(tag(0));
        i -= 1;
    }
    // WORD_MOD: (h>>1) % (97>>1...) re-tagged; return the untagged payload.
    let m = tag(HASHFOLD_MOD as usize);
    let modr = (((h >> 1) % (m >> 1)) << 1) | 1;
    (modr >> 1) as i64
}

/// Build the #2-hash-shaped region: `hash(buf, len)` (arity 2). Entry
/// frame: LOCAL_0=closure, LOCAL_1=retPC, LOCAL_2=len(top), LOCAL_3=buf.
///
/// Two persistent loop locals (h, i) are pushed onto the shared stack and
/// updated in place via SET_STACK_VAL_B; the loop counts i down from len
/// to 0 and exits via a JUMP_NEQ_LOCAL (want=0) decision; the body folds
/// `h = h*31 + buf[i-1]` with LOAD_ML_BYTE / WORD_MULT / WORD_ADD; the
/// tail computes `h mod 97` with WORD_MOD and RETURN_B 2.
///
/// The branch geometry + depth bookkeeping is DESIGN; the both-ways
/// differential (interp do_call oracle vs native boundary) + the Rust
/// reference are the PROOF.
#[allow(clippy::vec_init_then_push)]
fn build_hashfold_region(space: &mut MemorySpace) -> BuiltCode {
    // sp tracking (see the module comment for the downward stack model):
    // entry sp0 = closure. After pushing h0 then i0 the loop sp L = sp0-2,
    // where (from L): i=LOCAL_0, h=LOCAL_1, clo=LOCAL_2, ret=LOCAL_3,
    // len=LOCAL_4, buf=LOCAL_5.
    // This is a WHILE loop (test-at-top), NOT a do-while: the i!=0 test
    // guards the body so `buf[i-1]` is only read for i>=1 (the len==0 case
    // takes the exit immediately, never touching buf[-1]).
    let mut bc: Vec<u8> = Vec::new();
    // ---- prologue: push h=0, push i=len ----
    bc.push(op::INSTR_CONST_0); // h0 = 0  -> stack[sp0-1]
    bc.push(op::INSTR_LOCAL_3); // push len (LOCAL_3 from sp0-1) -> i0 stack[sp0-2]
    // ---- Ltest: if i != 0 jump fwd to Lbody; else fall through to tail ----
    let ltest = bc.len(); // L = sp0-2 here (from L: i=LOCAL_0, h=LOCAL_1, ...)
    bc.push(op::INSTR_JUMP_NEQ_LOCAL); // depth=0 (i=LOCAL_0), want=0
    bc.push(0); //   depth
    bc.push(0); //   want = 0
    let neq_off_idx = bc.len();
    bc.push(0x00); //   off (patched -> forward to Lbody)
    // ---- tail (fall-through, i==0): result = h mod 97; clean locals; ret.
    bc.push(op::INSTR_LOCAL_1); // push h (LOCAL_1 from sp L)      (sp L-1)
    bc.push(op::INSTR_CONST_INT_B); // push 97
    bc.push(HASHFOLD_MOD as u8); //   (=97)           (sp L-2)
    bc.push(op::INSTR_WORD_MOD); // h mod 97          (sp L-1)
    bc.push(op::INSTR_RESET_R_2); // drop i,h locals; keep result   (sp L+1)
    bc.push(op::INSTR_RETURN_B); // collapse result+clo+ret+2 args
    bc.push(2); //   arity 2
    // ---- Lbody: h = h*31 + buf[i-1]; i = i-1; JUMP_BACK to Ltest ----
    let lbody = bc.len();
    bc.push(op::INSTR_LOCAL_1); // push h            (sp L-1)
    bc.push(op::INSTR_CONST_INT_B); // push 31
    bc.push(HASHFOLD_MULT as u8); //   (=31)         (sp L-2)
    bc.push(op::INSTR_WORD_MULT); // h*31            (sp L-1)
    bc.push(op::INSTR_LOCAL_6); // push buf (LOCAL_6 from sp L-1)  (sp L-2)
    bc.push(op::INSTR_LOCAL_2); // push i  (LOCAL_2 from sp L-2)   (sp L-3)
    bc.push(op::INSTR_CONST_1); // push 1            (sp L-4)
    bc.push(op::INSTR_WORD_SUB); // i-1 (= idx)       (sp L-3)
    bc.push(op::INSTR_LOAD_ML_BYTE); // buf[idx]      (sp L-2)
    bc.push(op::INSTR_WORD_ADD); // h*31 + buf[idx]   (sp L-1)
    bc.push(op::INSTR_SET_STACK_VAL_B); // store h_new into h's slot (stack[L+1])
    bc.push(2); //   idx=2 (new_sp=L; L+2-1=L+1)      (sp L)
    // ---- i = i - 1 ----
    bc.push(op::INSTR_LOCAL_0); // push i (LOCAL_0 from sp L)      (sp L-1)
    bc.push(op::INSTR_CONST_1); // push 1            (sp L-2)
    bc.push(op::INSTR_WORD_SUB); // i-1               (sp L-1)
    bc.push(op::INSTR_SET_STACK_VAL_B); // store i-1 into i's slot (stack[L])
    bc.push(1); //   idx=1 (new_sp=L; L+1-1=L)        (sp L)
    // ---- JUMP_BACK to Ltest ----
    let jback_pc = bc.len();
    bc.push(op::INSTR_JUMP_BACK8);
    // JUMP_BACK8 (mod.rs / jump_target): the interp lands at pc - off where
    // pc is the JUMP_BACK opcode offset. So off = jback_pc - ltest.
    let back_off = jback_pc as i64 - ltest as i64;
    assert!(
        (0..=255).contains(&back_off),
        "hashfold back-off {back_off} out of range"
    );
    bc.push(back_off as u8);

    // JUMP_NEQ_LOCAL forward off: interp lands at after + off, after = the
    // pc past the 3 immediates = (neq opcode idx) + 4. The neq opcode is at
    // neq_off_idx - 3. Target = Lbody.
    let neq_opcode_idx = neq_off_idx - 3;
    let neq_after = neq_opcode_idx + 4;
    let fwd_off = lbody as i64 - neq_after as i64;
    assert!(
        (0..=255).contains(&fwd_off),
        "hashfold neq fwd-off {fwd_off} out of range"
    );
    bc[neq_off_idx] = fwd_off as u8;

    build_code_object(space, &bc, &[])
}

/// Run the hand-built #2-hash-shaped region BOTH ways for `(buf, len)`.
/// Pure interp via do_call vs native via the boundary, on a real byte
/// object in the heap. Returns the differential + the native tick count.
pub fn run_hashfold_both_ways(bytes: &[u8]) -> RealRegionResult {
    let len = bytes.len() as isize;

    // ---- (1) PURE INTERP ----
    let interp_result = {
        let mut space = MemorySpace::new(4096, SpaceKind::Code);
        let f = build_hashfold_region(&mut space);
        let buf = build_byte_object(&mut space, bytes);
        let f_addr = f.code_addr;
        let f_closure = f.closure;
        let mut interp = Interpreter::from_bytes(256, vec![]).with_alloc_space(space);
        interp.test_seed_top(buf); // arg buf (deepest, LOCAL_3)
        interp.test_seed_top(PolyWord::tagged(len)); // arg len (top, LOCAL_2)
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
    let mut native_space = MemorySpace::new(4096, SpaceKind::Code);
    let f = build_hashfold_region(&mut native_space);
    let buf = build_byte_object(&mut native_space, bytes);
    let f_addr = f.code_addr;
    let f_closure_bits = f.closure.0 as i64;

    let mut jit = Jit::new().expect("jit");
    // SAFETY: f_addr is a live code object in native_space.
    let region = match unsafe { memtrans::build_region(&mut jit, f_addr) } {
        Ok(r) => r,
        Err(e) => panic!("hashfold region build bailed: {e}"),
    };
    jit.module.finalize_definitions().expect("finalize");
    let ptr = jit.module.get_finalized_function(region.root);
    // SAFETY: region root has the RegionFn ABI.
    let region_fn: RegionFn = unsafe { std::mem::transmute::<*const u8, RegionFn>(ptr) };

    let cap = 256usize;
    let mut stack = vec![0i64; cap];
    stack[cap - 1] = buf.0 as i64; // arg buf (deepest, LOCAL_3)
    stack[cap - 2] = PolyWord::tagged(len).0 as i64; // arg len (top, LOCAL_2)
    let sp_top_arg = (cap - 2) as i64;
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

// =====================================================================
// GAP 3 — the Overflow / DivByZero / raised==1 boundary paths driven
// END-TO-END through the WIRED interpreter do_call, on REAL genuine-
// layout regions, flag-on (region registered → native) vs flag-off
// (pure interp), proven byte-identical INCLUDING the exception value +
// that the right handler catches it.
//
// Shape: an interpreted CALLER code object installs a handler, pushes
// two args, and CALL_CONST_ADDRs a CALLEE region that performs a single
// FixedInt op (which may Overflow / DivByZero). When the callee is
// REGISTERED, the interpreter's do_call routes it through
// polyml_jit_region_dispatch → the region runs NATIVE, raises across the
// native frame, and the do_call hook drives the interpreter's REAL raise
// machinery (raise_overflow / InterpError::DivByZero), unwinding to the
// caller's handler. When the callee is NOT registered it runs in the
// interpreter. Both must be byte-identical.
// =====================================================================

#[cfg(test)]
use polyml_runtime::{InterpError, RegionEntry, install_region_dispatch};

/// Which single FixedInt op the callee region performs on (a, b).
#[cfg(test)]
#[derive(Clone, Copy, Debug)]
enum CalleeOp {
    /// a * b — can Overflow.
    Mul,
    /// a div b — can DivByZero (b == 0).
    Quot,
}

/// Build a CALLEE region (arity 2) that computes one FixedInt op on its
/// two args and RETURNs. Genuine PolyML bytecode. At entry LOCAL_2=b(top),
/// LOCAL_3=a. We push a (LOCAL_3), then b (now LOCAL_3 after the first
/// push), apply the op, RETURN_B 2 — exactly the `add` shape in
/// build_sum3_region but with the chosen op.
#[cfg(test)]
fn build_arith_callee(space: &mut MemorySpace, opk: CalleeOp) -> BuiltCode {
    let opcode = match opk {
        CalleeOp::Mul => op::INSTR_FIXED_MULT,
        CalleeOp::Quot => op::INSTR_FIXED_QUOT,
    };
    let bc = vec![
        op::INSTR_LOCAL_3, // push a
        op::INSTR_LOCAL_3, // push b
        opcode,            // a OP b
        op::INSTR_RETURN_B,
        2,
    ];
    build_code_object(space, &bc, &[])
}

/// Build an interpreted CALLER (arity 0) that:
///   SET_HANDLER8 -> Lhandler
///   push a (CONST), push b (CONST)
///   CALL_CONST_ADDR8_8 callee     ; -> result (or raises)
///   DELETE_HANDLER                ; pop handler frame, keep result
///   RETURN_B 0
/// Lhandler:
///   LDEXC                         ; push the exception packet
///   RESET_R_1? -> instead: drop packet, push recovery, RETURN
///   CONST recovery; RETURN_B 0
///
/// `a`, `b` are baked as CONST_INT_W immediates (so the values are part
/// of the genuine bytecode). `recovery` is the value the handler returns.
/// The callee closure is in the caller's constant pool (index 0).
#[cfg(test)]
#[allow(clippy::vec_init_then_push)]
fn build_handler_caller(
    space: &mut MemorySpace,
    callee_closure: PolyWord,
    a: i64,
    b: i64,
    recovery: i64,
) -> BuiltCode {
    // We assemble the body, tracking offsets to patch the SET_HANDLER
    // target + the CALL_CONST_ADDR const read. The handler frame is the
    // upstream PUSH_HANDLER (save old hr) + SET_HANDLER8 (push handler pc,
    // hr = sp) two-word frame (bytecode.cpp:338-352).
    let mut bc: Vec<u8> = Vec::new();
    bc.push(op::INSTR_PUSH_HANDLER); // 0: push old handler register
    let set_pc = bc.len(); // 1
    bc.push(op::INSTR_SET_HANDLER8); // 1: set up handler
    let handler_off_idx = bc.len(); // 2 (patched)
    bc.push(0x00); // 2: handler offset (entry = pc_after + off)
    // push a (CONST_INT_W is a u16 immediate, sufficient for small test
    // values; for negative/large we still use it modulo the test range).
    bc.push(op::INSTR_CONST_INT_W); // 3
    bc.extend_from_slice(&(a as u16).to_le_bytes()); // 4,5
    bc.push(op::INSTR_CONST_INT_W); // 6
    bc.extend_from_slice(&(b as u16).to_le_bytes()); // 7,8
    let call_pc = bc.len(); // 9
    bc.push(op::INSTR_CALL_CONST_ADDR8_8); // 9
    let call_off_idx = bc.len(); // 10 (byte_off, patched)
    bc.push(0x00); // 10
    bc.push(0x00); // 11 (imm2 -> idx = 3)
    bc.push(op::INSTR_DELETE_HANDLER); // 12
    bc.push(op::INSTR_RETURN_B); // 13
    bc.push(0); // 14: arity 0
    let lhandler = bc.len(); // 15
    bc.push(op::INSTR_LDEXC); // 15: push exn packet
    bc.push(op::INSTR_RESET_1); // 16: drop the packet
    bc.push(op::INSTR_CONST_INT_W); // 17: push recovery
    bc.extend_from_slice(&(recovery as u16).to_le_bytes()); // 18,19
    bc.push(op::INSTR_RETURN_B); // 20
    bc.push(0); // 21: arity 0

    // SET_HANDLER8 target: interp does `entry = pc.add(off)` where pc is
    // AFTER the offset byte. SET_HANDLER8 is at set_pc; its offset byte is
    // at set_pc+1, so pc-after = set_pc+2. So off = Lhandler - (set_pc+2).
    let set_after = set_pc + 2;
    let hoff = lhandler as i64 - set_after as i64;
    assert!((0..=255).contains(&hoff), "handler off {hoff} out of range");
    bc[handler_off_idx] = hoff as u8;

    // CALL_CONST_ADDR8_8 reads const idx 3 at pc_after_call + byte_off +
    // 3*8, pc_after_call = call_pc + 3. First const word is at object byte
    // (code_words+1)*8. Pad with NO_OP after the final RETURN until
    // byte_off lands in [0,255].
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
        assert!(bc.len() < 4096, "caller pad runaway");
    }
    bc[call_off_idx] = byte_off;

    build_code_object(space, &bc, &[callee_closure])
}

/// Outcome of running a wired caller+callee: the returned value (untagged)
/// or an error string, plus whether the callee ran NATIVE.
#[cfg(test)]
#[derive(Debug, Clone)]
struct WiredOutcome {
    /// Untagged result, or None if the run errored.
    result: Option<i64>,
    /// Error (e.g. "DivByZero") if the run did not return cleanly.
    error: Option<String>,
    /// Native region-root entries during this run (0 = pure interp).
    native_ticks: u64,
}

/// Run a caller that calls an arith callee through the interpreter's REAL
/// do_call. If `register_region` is true, the callee is compiled to a
/// native region + registered → the call dispatches NATIVE through the
/// wired do_call boundary. Otherwise the callee runs in the interpreter.
#[cfg(test)]
fn run_wired_arith(
    opk: CalleeOp,
    a: i64,
    b: i64,
    recovery: i64,
    register_region: bool,
) -> WiredOutcome {
    let mut space = MemorySpace::new(8192, SpaceKind::Code);
    let callee = build_arith_callee(&mut space, opk);
    let caller = build_handler_caller(&mut space, callee.closure, a, b, recovery);
    let caller_addr = caller.code_addr;
    let callee_code_addr = callee.code_addr;

    let mut interp = Interpreter::from_bytes(256, vec![]).with_alloc_space(space);

    // Optionally compile + register the callee as a native region, wired
    // through the runtime's global dispatch callback. `_jit_keep` holds
    // the module alive for the whole run (the region's native code is
    // referenced by the registry); it drops after `interp.run()`.
    let mut _jit_keep: Option<Jit> = None;
    reset_native_tick();
    if register_region {
        install_region_dispatch(polyml_jit_region_dispatch);
        let mut jit = Jit::new().expect("jit");
        // SAFETY: callee_code_addr is a live code object now owned by
        // `interp` (its alloc space); the heap is frozen for this run.
        let region =
            unsafe { memtrans::build_region(&mut jit, callee_code_addr) }.expect("region build");
        jit.module.finalize_definitions().expect("finalize");
        let ptr = jit.module.get_finalized_function(region.root);
        interp.install_region(
            callee_code_addr as usize,
            RegionEntry {
                region_fn: ptr as usize,
                sml_arity: region.root_arity,
            },
        );
        _jit_keep = Some(jit);
    }

    // Top-level entry: arity-0 caller. Frame = [closure, retPC=0].
    interp.test_seed_return_sentinel(); // retPC = 0 (LOCAL_1)
    interp.test_seed_top(caller.closure); // closure (LOCAL_0)
    // SAFETY: caller_addr is a live code object now owned by `interp`.
    unsafe { interp.set_code_segment_to_code_obj(caller_addr as usize) };

    match interp.run() {
        Ok(StepResult::Returned(w)) => WiredOutcome {
            result: Some(PolyWord::from_bits(w.0).untag() as i64),
            error: None,
            native_ticks: native_tick_count(),
        },
        Ok(other) => WiredOutcome {
            result: None,
            error: Some(format!("{other:?}")),
            native_ticks: native_tick_count(),
        },
        Err(e) => WiredOutcome {
            result: None,
            error: Some(match e {
                InterpError::DivByZero => "DivByZero".to_string(),
                InterpError::UnhandledException => "UnhandledException".to_string(),
                other => format!("{other:?}"),
            }),
            native_ticks: native_tick_count(),
        },
    }
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

    /// S4a: the #2-hash-shaped region (LOAD_ML_BYTE / WORD_MULT / WORD_ADD
    /// loop with SET_STACK_VAL_B loop vars + a JUMP_NEQ_LOCAL exit ->
    /// WORD_MOD). It must (a) COMPILE (the new Tier-1 leaf opcodes), (b)
    /// run NATIVE (tick == 1: a single leaf entry, no recursion), and (c)
    /// be byte-identical to the pure interpreter AND to the Rust reference
    /// across a fuzz range of byte buffers.
    #[test]
    fn hashfold_region_differential_clean() {
        // A spread of buffers: empty (i==0 base case taken immediately),
        // single byte, ascending, descending, all-equal, zeros, and a
        // pseudo-random LCG sweep over lengths 0..=40.
        let mut buffers: Vec<Vec<u8>> = vec![
            vec![],
            vec![0],
            vec![255],
            vec![1, 2, 3, 4, 5],
            vec![5, 4, 3, 2, 1],
            vec![7; 16],
            vec![0; 12],
            b"Poly/ML hash fold!".to_vec(),
        ];
        // Seeded LCG fuzz: lengths 0..=40, bytes from a deterministic PRNG.
        let mut s: u64 = 0x9E37_79B9_7F4A_7C15;
        for len in 0..=40usize {
            let mut v = Vec::with_capacity(len);
            for _ in 0..len {
                s = s
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                v.push((s >> 33) as u8);
            }
            buffers.push(v);
        }

        let mut diverged = 0usize;
        let mut non_native = 0usize;
        let mut cases = 0usize;
        for buf in &buffers {
            let r = run_hashfold_both_ways(buf);
            cases += 1;
            let want = hashfold_reference(buf, buf.len() as i64);
            let interp = PolyWord::from_bits(r.interp_result as usize).untag() as i64;
            let native = PolyWord::from_bits(r.native_result as usize).untag() as i64;
            if interp != native || r.raised_interp != r.raised_native {
                diverged += 1;
                eprintln!(
                    "DIVERGE hashfold(len={}): interp={interp} native={native}",
                    buf.len()
                );
            }
            assert_eq!(
                interp,
                want,
                "interp hashfold(len={}) must match the Rust reference",
                buf.len()
            );
            assert_eq!(
                native,
                want,
                "native hashfold(len={}) must match the Rust reference",
                buf.len()
            );
            // A pure non-recursive leaf: exactly ONE native root entry.
            if r.native_ticks != 1 {
                non_native += 1;
            }
        }
        assert_eq!(diverged, 0, "{diverged}/{cases} hashfold cases diverged");
        assert_eq!(
            non_native, 0,
            "{non_native}/{cases} hashfold cases were non-native"
        );
    }

    /// The #2-hash region must NOT be flagged recursive or stack-size-using
    /// (it is a pure self-contained loop leaf with no CALL_CONST_ADDR and
    /// no STACK_SIZE16), so the live-dispatch scan WILL register it.
    #[test]
    fn hashfold_region_is_registerable_leaf() {
        let mut space = MemorySpace::new(4096, SpaceKind::Code);
        let f = build_hashfold_region(&mut space);
        let mut jit = Jit::new().expect("jit");
        // SAFETY: f.code_addr is a live code object in `space`.
        let r = unsafe { memtrans::build_region(&mut jit, f.code_addr) }
            .expect("hashfold region must build Ok (it was UnsupportedOpcode before S4a)");
        assert!(!r.recursive, "hashfold is a loop leaf, not recursive");
        assert!(!r.uses_stack_size, "hashfold declares no STACK_SIZE16");
        assert_eq!(r.funcs.len(), 1, "hashfold is a single leaf function");
    }

    /// EARLY S5 SPEED READ (the whole-region kill-switch). Microbenchmark the
    /// #2-shaped hashfold region NATIVE (via the do_call boundary) vs the REAL
    /// interpreter, isolating the per-loop-iteration execution cost with the
    /// two-point (len=N minus len=0) subtraction so setup/entry/exit cancel.
    /// Region #2 is the BEST CASE: no alloc, no dynamic-call trampoline tax. If
    /// native cannot clear ~1.2x here, region #1 (burdened with both) never
    /// will -> stop before building S4c/d/e. Run:
    ///   cargo test --release -p polyml-jit s5_hashfold -- --ignored --nocapture
    #[test]
    #[ignore]
    fn s5_hashfold_microbench() {
        use std::time::Instant;
        const N: usize = 50_000; // inner-loop iterations per call
        const ITERS: usize = 60; // timed repetitions

        let big: Vec<u8> = (0..N).map(|i| (i * 31 + 7) as u8).collect();
        let empty: Vec<u8> = Vec::new();

        // ---- NATIVE: compile + finalize ONCE; both byte objects in one space.
        let mut nspace = MemorySpace::new(1 << 16, SpaceKind::Code);
        let f = build_hashfold_region(&mut nspace);
        let f_closure_bits = f.closure.0 as i64;
        let buf_big = build_byte_object(&mut nspace, &big);
        let buf_empty = build_byte_object(&mut nspace, &empty);
        let mut jit = Jit::new().expect("jit");
        // SAFETY: f.code_addr is a live code object in nspace.
        let region = unsafe { memtrans::build_region(&mut jit, f.code_addr) }.expect("build");
        jit.module.finalize_definitions().expect("finalize");
        let ptr = jit.module.get_finalized_function(region.root);
        // SAFETY: region root has the RegionFn ABI.
        let region_fn: RegionFn = unsafe { std::mem::transmute::<*const u8, RegionFn>(ptr) };

        let native_once = |buf: PolyWord, len: i64| -> i64 {
            let cap = 256usize;
            let mut stack = vec![0i64; cap];
            stack[cap - 1] = buf.0 as i64;
            stack[cap - 2] = PolyWord::tagged(len as isize).0 as i64;
            let mut ctx = ExnCtx::default();
            // SAFETY: stack covers all indices; region_fn finalized; ctx valid.
            match unsafe {
                dispatch_region(
                    region_fn,
                    stack.as_mut_ptr(),
                    (cap - 2) as i64,
                    f_closure_bits,
                    &mut ctx,
                )
            } {
                BoundaryOutcome::Returned { new_sp } => stack[new_sp as usize],
                BoundaryOutcome::Raised { .. } => panic!("native raised"),
            }
        };
        let time_native = |buf: PolyWord, len: i64| -> f64 {
            native_once(buf, len); // warmup
            let t = Instant::now();
            for _ in 0..ITERS {
                std::hint::black_box(native_once(buf, len));
            }
            t.elapsed().as_secs_f64() / ITERS as f64
        };

        // ---- INTERP: fresh setup per call (subtraction cancels it).
        let interp_once = |bytes: &[u8]| -> i64 {
            let mut space = MemorySpace::new(1 << 16, SpaceKind::Code);
            let f = build_hashfold_region(&mut space);
            let buf = build_byte_object(&mut space, bytes);
            let f_closure = f.closure;
            let f_addr = f.code_addr;
            let mut interp = Interpreter::from_bytes(256, vec![]).with_alloc_space(space);
            interp.test_seed_top(buf);
            interp.test_seed_top(PolyWord::tagged(bytes.len() as isize));
            interp.test_seed_return_sentinel();
            interp.test_seed_top(f_closure);
            // SAFETY: f_addr is a live code object now owned by interp.
            unsafe { interp.set_code_segment_to_code_obj(f_addr as usize) };
            let r = match interp.run() {
                Ok(StepResult::Returned(w)) => w.0 as i64,
                other => panic!("interp: {other:?}"),
            };
            std::mem::forget(interp);
            r
        };
        let time_interp = |bytes: &[u8]| -> f64 {
            interp_once(bytes); // warmup
            let t = Instant::now();
            for _ in 0..ITERS {
                std::hint::black_box(interp_once(bytes));
            }
            t.elapsed().as_secs_f64() / ITERS as f64
        };

        // Correctness guard: native == interp (THE whole-region soundness
        // criterion — both paths execute the same bytecode over the same
        // buffer, so the speedup ratio times faithful work). The Rust
        // hashfold_reference is validated only on small fuzz buffers
        // (hashfold_region_differential_clean) and wraps differently at large
        // N, so it is not used here.
        let nr = native_once(buf_big, N as i64);
        let ir = interp_once(&big);
        assert_eq!(nr, ir, "native vs interp result mismatch");

        let nt_big = time_native(buf_big, N as i64);
        let nt_empty = time_native(buf_empty, 0);
        let it_big = time_interp(&big);
        let it_empty = time_interp(&empty);

        let nexec = nt_big - nt_empty; // per-call loop cost, native
        let iexec = it_big - it_empty; // per-call loop cost, interp
        let speedup = iexec / nexec;
        let ns_per_iter_native = nexec * 1e9 / N as f64;
        let ns_per_iter_interp = iexec * 1e9 / N as f64;

        eprintln!("==== S5 EARLY READ: region #2 (hashfold) native vs interp ====");
        eprintln!("  N={N} loop iters/call, {ITERS} timed reps");
        eprintln!(
            "  native: total {:.1}us, loop {:.1}us ({:.3} ns/iter)",
            nt_big * 1e6,
            nexec * 1e6,
            ns_per_iter_native
        );
        eprintln!(
            "  interp: total {:.1}us, loop {:.1}us ({:.3} ns/iter)",
            it_big * 1e6,
            iexec * 1e6,
            ns_per_iter_interp
        );
        eprintln!("  >>> SPEEDUP (interp/native, loop-isolated) = {speedup:.3}x");
        eprintln!(
            "  KILL-SWITCH: {} (>=1.2x continue S4c/d/e; <1.2x STOP)",
            if speedup >= 1.2 { "PASS" } else { "FAIL" }
        );
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

    /// The live-dispatch SAFETY GUARD: `build_region` must flag a recursive
    /// region as `recursive` (so `scan_region_candidates` /
    /// `install_whole_region` refuse to register it — unbounded shared-stack
    /// growth with the no-op'd STACK_SIZE16 would otherwise OOB-write the
    /// stack Box). The self-recursive `sumto` region must be flagged; an
    /// acyclic multi-function region (`sum3` root + its `add` callee) must
    /// NOT be.
    #[test]
    fn region_safety_flags_recursion() {
        let mut sumto_space = MemorySpace::new(8192, SpaceKind::Code);
        let f = build_sumto_region(&mut sumto_space);
        let mut jit = Jit::new().expect("jit");
        // SAFETY: f.code_addr is a live code object in sumto_space.
        let r = unsafe { memtrans::build_region(&mut jit, f.code_addr) }.expect("sumto builds");
        assert!(
            r.recursive,
            "self-recursive sumto must be flagged recursive (the registration guard)"
        );

        let mut sum3_space = MemorySpace::new(8192, SpaceKind::Code);
        let (root, _callee) = build_sum3_region(&mut sum3_space);
        let mut jit2 = Jit::new().expect("jit");
        // SAFETY: root.code_addr is a live code object in sum3_space.
        let r2 = unsafe { memtrans::build_region(&mut jit2, root.code_addr) }.expect("sum3 builds");
        assert!(
            !r2.recursive,
            "acyclic sum3 (root + add callee) must NOT be flagged recursive"
        );
        assert!(r2.funcs.len() >= 2, "sum3 region spans root + callee");
    }

    // ----- GAP 3: Overflow / DivByZero / raised==1 on REAL wired regions -----

    /// Normal (no-raise) wired path: a*b in range, caller returns it. The
    /// callee region runs NATIVE (tick==1) and the value is byte-identical
    /// to the pure-interp run.
    #[test]
    fn wired_mul_normal_differential_clean() {
        // NOTE: native_tick_count is a PROCESS-GLOBAL counter, so exact
        // tick assertions race with other parallel region tests. The
        // soundness proof is the result/error DIFFERENTIAL; nativeness is
        // asserted as >= 1 (the wired call did enter the native region).
        for (a, b) in [(3i64, 4i64), (7, 8), (0, 99), (12, 12), (1, 1)] {
            let interp = run_wired_arith(CalleeOp::Mul, a, b, 777, false);
            let native = run_wired_arith(CalleeOp::Mul, a, b, 777, true);
            assert_eq!(
                interp.result,
                Some(a * b),
                "pure interp {a}*{b} should be {}",
                a * b
            );
            assert_eq!(
                native.result, interp.result,
                "wired native {a}*{b} must match interp"
            );
            assert_eq!(interp.error, native.error, "error mismatch {a}*{b}");
            assert!(
                native.native_ticks >= 1,
                "wired path must run the region NATIVE"
            );
        }
    }

    /// OVERFLOW path: a*b overflows the tagged range → the region raises
    /// Overflow across the native frame → the do_call hook drives
    /// raise_overflow → the caller's handler catches it and returns the
    /// recovery value. Byte-identical to the pure-interp run, AND the
    /// region ran native.
    #[test]
    fn wired_mul_overflow_caught_by_handler() {
        // The operands (2^31 * 2^31 = 2^62) overflow the 62-bit tagged
        // range; the region raises Overflow across the native frame, the
        // do_call hook drives raise_overflow, and the caller's handler
        // catches it and returns the recovery value (12345). Operands are
        // seeded via a heap tuple (not u16 CONST immediates) so a genuine
        // FixedInt overflow is reachable.
        let r = run_wired_overflow_large(true);
        let i = run_wired_overflow_large(false);
        assert_eq!(
            i.result,
            Some(12345),
            "interp: handler must catch Overflow + return recovery 12345"
        );
        assert_eq!(
            r.result, i.result,
            "wired overflow recovery must match interp"
        );
        assert_eq!(r.error, i.error, "error mismatch");
        // native_tick_count is process-global; the wired path having
        // >= 1 entries proves the region ran NATIVE (the result/error
        // differential is the soundness proof).
        assert!(r.native_ticks >= 1, "wired overflow region must run NATIVE");
    }

    /// DIVBYZERO path: a div 0 → the region raises DivByZero → the do_call
    /// hook returns Err(InterpError::DivByZero), a HARD error exactly like
    /// the pure interpreter (NOT a catchable SML Div). Byte-identical.
    #[test]
    fn wired_div_by_zero_hard_error() {
        let interp = run_wired_arith(CalleeOp::Quot, 10, 0, 777, false);
        let native = run_wired_arith(CalleeOp::Quot, 10, 0, 777, true);
        assert_eq!(
            interp.error.as_deref(),
            Some("DivByZero"),
            "pure interp div-by-zero must be a hard DivByZero error"
        );
        assert_eq!(
            native.error, interp.error,
            "wired div-by-zero must be byte-identical hard error"
        );
        assert_eq!(interp.result, None);
        assert_eq!(native.result, None);
        // The region DID run native before raising (tick bumped at entry).
        assert!(native.native_ticks >= 1, "div-by-zero region ran NATIVE");
    }

    /// Normal quot (no zero divisor): byte-identical + native.
    #[test]
    fn wired_quot_normal_differential_clean() {
        for (a, b) in [(20i64, 4i64), (7, 2), (100, 9), (0, 5)] {
            let interp = run_wired_arith(CalleeOp::Quot, a, b, 777, false);
            let native = run_wired_arith(CalleeOp::Quot, a, b, 777, true);
            assert_eq!(interp.result, Some(a / b), "interp {a} div {b}");
            assert_eq!(native.result, interp.result, "wired {a} div {b}");
            // native_tick_count is process-global; assert >= 1 to avoid
            // racing parallel region tests (the differential is the proof).
            assert!(native.native_ticks >= 1, "quot region ran NATIVE");
        }
    }
}

// =====================================================================
// Large-operand OVERFLOW harness (operands seeded on the stack, not as
// u16 CONST immediates, so a genuine FixedInt overflow is reachable). A
// caller installs a handler, the callee region multiplies two large
// caller-pushed args, overflows, the raise unwinds across the native
// frame to the caller's handler. Driven flag-on vs flag-off.
// =====================================================================

/// Build a caller (arity 0) that pushes two LARGE args (as CONST_ADDR
/// would be needed for >u16; instead we seed them via a boxed constant in
/// the constant pool and read with INDIRECT). Simpler: read the two
/// operands from the constant pool tuple at const idx 1 (fields 0,1),
/// install a handler, CALL_CONST_ADDR the callee, return result; handler
/// returns 424242.
#[cfg(test)]
#[allow(clippy::vec_init_then_push)]
fn build_overflow_caller(space: &mut MemorySpace, callee_closure: PolyWord) -> BuiltCode {
    // Arity 2: the two LARGE operands are the caller's own args (seeded on
    // the stack), so a genuine FixedInt overflow is reachable (CONST_INT_W
    // only carries a u16). Entry: LOCAL_0=clo, LOCAL_1=ret, LOCAL_2=b,
    // LOCAL_3=a. The handler frame (PUSH_HANDLER + SET_HANDLER8) pushes 2
    // words, so after it a is LOCAL_5, b is LOCAL_4.
    let mut bc: Vec<u8> = Vec::new();
    bc.push(op::INSTR_PUSH_HANDLER); // 0: save old handler register
    let set_pc = bc.len(); // 1
    bc.push(op::INSTR_SET_HANDLER8); // 1
    let handler_off_idx = bc.len(); // 2
    bc.push(0x00); // 2: handler off (patched)
    bc.push(op::INSTR_LOCAL_5); // 3: push a (LOCAL_5 after +2 handler depth)
    bc.push(op::INSTR_LOCAL_5); // 4: push b (LOCAL_5 again after a pushed)
    let call_pc = bc.len(); // 5
    bc.push(op::INSTR_CALL_CONST_ADDR8_8); // 5
    let call_off_idx = bc.len(); // 6
    bc.push(0x00); // 6: byte_off (patched) -> const idx 0 (callee)
    bc.push(0x00); // 7: imm2 (idx = 3)
    bc.push(op::INSTR_DELETE_HANDLER); // 8
    bc.push(op::INSTR_RETURN_B); // 9
    bc.push(2); // 10: arity 2
    let lhandler = bc.len(); // 11
    bc.push(op::INSTR_LDEXC); // 11
    bc.push(op::INSTR_RESET_1); // 12: drop packet
    bc.push(op::INSTR_CONST_INT_W); // 13
    bc.extend_from_slice(&12345u16.to_le_bytes()); // 14,15: recovery value
    bc.push(op::INSTR_RETURN_B); // 16
    bc.push(2); // 17: arity 2

    // SET_HANDLER8 target: off = Lhandler - (set_pc + 2).
    let set_after = set_pc + 2;
    let hoff = lhandler as i64 - set_after as i64;
    assert!((0..=255).contains(&hoff), "handler off {hoff} out of range");
    bc[handler_off_idx] = hoff as u8;

    // CALL_CONST_ADDR8_8 reads const idx 3 (= callee closure at pool slot
    // 0) at pc_after_call + byte_off + 3*8. Pad with NO_OP until in range.
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
        assert!(bc.len() < 4096, "overflow caller pad runaway");
    }
    bc[call_off_idx] = byte_off;

    build_code_object(space, &bc, &[callee_closure])
}

/// Run the large-operand overflow harness flag-on (region native) or
/// flag-off (pure interp). The callee multiplies two large operands that
/// overflow the 62-bit tagged range; the caller catches Overflow and
/// returns 12345.
#[cfg(test)]
fn run_wired_overflow_large(register_region: bool) -> WiredOutcome {
    let mut space = MemorySpace::new(8192, SpaceKind::Code);
    // Operands a=b=2^31 ⇒ product 2^62 which is OUT of range
    // (MAX_TAGGED = 2^62-1) ⇒ FIXED_MULT raises Overflow.
    let a = 1i64 << 31;
    let b = 1i64 << 31;
    let callee = build_arith_callee(&mut space, CalleeOp::Mul);
    let caller = build_overflow_caller(&mut space, callee.closure);
    let caller_addr = caller.code_addr;
    let callee_code_addr = callee.code_addr;

    let mut interp = Interpreter::from_bytes(256, vec![]).with_alloc_space(space);
    let mut _jit_keep: Option<Jit> = None;
    reset_native_tick();
    if register_region {
        install_region_dispatch(polyml_jit_region_dispatch);
        let mut jit = Jit::new().expect("jit");
        // SAFETY: callee_code_addr is a live code object owned by interp.
        let region =
            unsafe { memtrans::build_region(&mut jit, callee_code_addr) }.expect("region build");
        jit.module.finalize_definitions().expect("finalize");
        let ptr = jit.module.get_finalized_function(region.root);
        interp.install_region(
            callee_code_addr as usize,
            RegionEntry {
                region_fn: ptr as usize,
                sml_arity: region.root_arity,
            },
        );
        _jit_keep = Some(jit);
    }
    // Arity-2 caller: frame = [closure, retPC=0, b, a] (a deepest).
    interp.test_seed_top(PolyWord::tagged(a as isize)); // arg a (LOCAL_3)
    interp.test_seed_top(PolyWord::tagged(b as isize)); // arg b (LOCAL_2)
    interp.test_seed_return_sentinel(); // retPC = 0 (LOCAL_1)
    interp.test_seed_top(caller.closure); // closure (LOCAL_0)
    // SAFETY: caller_addr is a live code object owned by interp.
    unsafe { interp.set_code_segment_to_code_obj(caller_addr as usize) };

    match interp.run() {
        Ok(StepResult::Returned(w)) => WiredOutcome {
            result: Some(PolyWord::from_bits(w.0).untag() as i64),
            error: None,
            native_ticks: native_tick_count(),
        },
        Ok(other) => WiredOutcome {
            result: None,
            error: Some(format!("{other:?}")),
            native_ticks: native_tick_count(),
        },
        Err(e) => WiredOutcome {
            result: None,
            error: Some(match e {
                InterpError::DivByZero => "DivByZero".to_string(),
                InterpError::UnhandledException => "UnhandledException".to_string(),
                other => format!("{other:?}"),
            }),
            native_ticks: native_tick_count(),
        },
    }
}
