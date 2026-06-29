//! Whole-region JIT — the non-popping shared-stack convention integrated
//! into a real Cranelift `JITModule`, behind the `WHOLE_REGION_JIT` flag.
//!
// Codegen module: pervasive intentional i64<->index casts + builder-pattern
// verbosity. The pedantic/nursery lints (cast_possible_truncation, use_self,
// uninlined_format_args, …) are noise here; deny-level lints still apply.
#![allow(clippy::pedantic, clippy::nursery)]
//!
//! ============================================================
//! WHY THIS EXISTS (the coverage wall, see CLAUDE.md "JIT status")
//! ============================================================
//! The per-function translator (`translate.rs`) tracks the SML value
//! stack as a *compile-time* `Vec<Value>` of SSA registers. That model
//! cannot express PolyML's NON-POPPING call convention: at a
//! `CALL_CLOSURE` / `CALL_CONST_ADDR` / `CALL_LOCAL_B`, the call args
//! PHYSICALLY PERSIST on the stack across the call and the callee's
//! `RETURN_N` collapses them (bytecode.cpp:411-414, 454-465). The
//! per-function JIT instead pops the args + pushes one result, which
//! desyncs the compile-time stack from the layout the SML compiler
//! addresses by absolute offset after the call → a later
//! `INDIRECT_CONTAINER_B` derefs a stale slot → SIGSEGV. So the install
//! gate (`cca_all_tail_equivalent`) only admits a CCA in tail position.
//! No install gate unlocks the hot, mid-function callers.
//!
//! ============================================================
//! THE WHOLE-REGION CONVENTION (proven in /tmp/wrjit_work PoCs)
//! ============================================================
//! A *region* is a root code object + its statically-known callees,
//! compiled TOGETHER into ONE `JITModule`. The region's functions share
//! the interpreter's real value stack (a fixed `Box<[PolyWord]>` →
//! stable base → GC-correct: GC scans `[sp, len)` exactly as it does for
//! interpreted frames). Region functions call each other with a native
//! `call`/`ret`; the callee's args persist in the shared stack across the
//! native call; `RETURN_N` collapses `sp` natively. NO per-call
//! trampoline, NO args_buf marshalling — the args live in the shared
//! stack the whole time.
//!
//! ABI (every region function):
//!   #[repr(C)] struct RegionRet { new_sp: i64, raised: i64 }
//!   extern "C" fn(stack_base: *mut i64, sp: i64, ctx: *mut ExnCtx)
//!                 -> RegionRet
//!
//! `RegionRet` is a `#[repr(C)]` struct, NOT a bare `(i64, i64)` tuple —
//! the latter is not FFI-safe (the exn PoC's go/no-go finding).
//!
//! ============================================================
//! THE INTERPRETER'S DOWNWARD STACK (the load-bearing adaptation)
//! ============================================================
//! The /tmp PoCs grew the stack UPWARD (push: sp+=1) for clarity. The
//! REAL interpreter (mod.rs `push`: `sp -= 1`; `pop`: read `stack[sp]`,
//! `sp += 1`) grows DOWNWARD: `sp` is an INDEX, smaller = deeper/more
//! recently pushed, `stack[sp]` is the top of stack, `stack.len()` is the
//! bottom. This module uses the interpreter's DOWNWARD direction so the
//! shared stack is byte-identical to what the interpreter sees, which is
//! the whole point (GC roots + boundary dispatch).
//!
//! Downward primitives (mirror mod.rs exactly):
//!   PUSH v        : sp -= 1; stack[sp] = v          (new sp = sp-1)
//!   LOCAL_K / peek: stack[sp + K]                   (K=0 is top)
//!   RETURN_N      : result is top (stack[sp]); drop result+N args =
//!                   collapse so result lands at stack[sp + N], new sp =
//!                   sp + N. (interp do_return pops result/closure/retPC
//!                   + N args + pushes result; the native call/ret
//!                   subsumes closure+retPC, leaving result + N args.)
//!
//! CALL site (non-popping, downward):
//!   1. PUSH each arg (top arg ends at stack[sp]).
//!   2. native call callee(base, sp, ctx) -> RegionRet.
//!   3. callee's RETURN_N collapsed its N args; new_sp points at the
//!      callee's single result on top (stack[new_sp]). The arg slots are
//!      gone. NO desync — sp is a runtime value, not a compile-time count.
//!
//! ============================================================
//! EXCEPTIONS (the verified checked-return-sentinel model)
//! ============================================================
//! A shared `*mut ExnCtx { handler_sp, exn_packet }` carries the
//! interpreter's `handler_sp` + `exception_packet` across the whole
//! region AND the boundary. A region fn returns `raised=1` when an
//! exception escapes its frame; per call site the caller emits
//! `brif raised`. On `raised`, the caller tests whether `handler_sp`
//! falls in ITS frame range (handler local?) → branch to the local
//! handler block; else propagate (return `raised=1`). Because
//! `handler_sp`+packet live in shared memory, the moment we reach the
//! frame whose range contains `handler_sp`, sp is already at handler_sp
//! and the packet is set. (Ported from region_exn_poc.rs, downward.)
//!
//! NOTE on frame-range test direction: downward, a handler installed in
//! THIS frame sits at a SMALLER sp index than the frame base captured at
//! entry (it was pushed after entry). "handler in this frame" =
//! `handler_sp <= frame_base_sp` (the handler frame is at or above the
//! current top toward the frame base) AND `handler_sp != NO_HANDLER`.
//! See `build_exn_region`'s `decide_blk` for the exact comparison used.

// Stack-index <-> i64 conversions are pervasive in this module (the
// region threads `sp` as an i64 to match the Cranelift ABI, but indexes
// the host Vec<i64> with usize). These casts are intentional and bounded
// (the demo stacks are 256 slots); allow the cast lints module-wide, as
// the interpreter (`mod.rs`) does at its hot sites.
#![allow(
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap
)]

use crate::Jit;
use cranelift::codegen::ir::{BlockArg, UserFuncName};
use cranelift::prelude::*;
use cranelift_module::{FuncId, Linkage, Module};
use std::sync::atomic::{AtomicU64, Ordering};

/// NATIVENESS PROOF: incremented exactly once per native region-root
/// invocation, by a Cranelift `call` the region root emits to
/// [`region_native_tick`] at entry. A non-zero value AFTER a region run
/// proves the NATIVE code actually executed (not an interpreter
/// fallback). Read via [`native_tick_count`]; reset via
/// [`reset_native_tick`].
static NATIVE_TICKS: AtomicU64 = AtomicU64::new(0);

/// The trampoline the region root calls at entry to bump [`NATIVE_TICKS`].
/// Registered in the JIT module under `polyml_jit_region_native_tick`.
/// `# Safety`: callable from JIT'd code; takes/returns nothing.
#[unsafe(no_mangle)]
pub extern "C" fn region_native_tick() {
    NATIVE_TICKS.fetch_add(1, Ordering::Relaxed);
}

/// Current native-tick count (number of native region-root entries since
/// the last reset).
#[must_use]
pub fn native_tick_count() -> u64 {
    NATIVE_TICKS.load(Ordering::Relaxed)
}

/// Reset the native-tick counter to 0 (call before a region run).
pub fn reset_native_tick() {
    NATIVE_TICKS.store(0, Ordering::Relaxed);
}

/// `true` iff the whole-region JIT path is enabled via the
/// `WHOLE_REGION_JIT` env var. Default OFF — the interpreter default path
/// and the per-function `--jit` path stay byte-identical. The CLI also
/// enables the path via the `--whole-region` flag, which is checked
/// alongside this env var in `Cmd::Run` dispatch (neither alters the
/// default run when absent).
#[must_use]
pub fn whole_region_enabled() -> bool {
    std::env::var("WHOLE_REGION_JIT").is_ok_and(|v| v != "0" && !v.is_empty())
}

/// Sentinel for "no handler in scope". The interpreter uses
/// `stack.len()` (past the deep end). We use a constant well below 0
/// (no real sp is negative) so the downward range tests are unambiguous.
/// `i64::MIN/2` is comfortably outside any real sp.
pub const NO_HANDLER: i64 = i64::MIN / 2;

/// The shared exception context threaded through every region function
/// via the `ctx` parameter. Mirrors the interpreter's `handler_sp: usize`
/// + `exception_packet: PolyWord`. `#[repr(C)]` so Cranelift can
/// load/store by fixed byte offset (handler_sp @ 0, exn_packet @ 8).
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct ExnCtx {
    /// Downward stack index of the current handler frame, or
    /// [`NO_HANDLER`].
    pub handler_sp: i64,
    /// The raised value (tagged PolyWord bits), read by LDEXC.
    pub exn_packet: i64,
    /// Raw `*mut Interpreter` (as `i64` bits), or 0. The do_call hook
    /// stores the live interpreter pointer here BEFORE invoking the
    /// region so the DYNAMIC-call trampoline (`region_interp_call`) can
    /// re-enter `do_call` without a second aliasing `&mut Interpreter`.
    /// Layout-identical to `polyml_runtime::ExnCtxC` (interp_ptr @ 16).
    pub interp_ptr: i64,
}

impl Default for ExnCtx {
    fn default() -> Self {
        Self {
            handler_sp: NO_HANDLER,
            exn_packet: 0,
            interp_ptr: 0,
        }
    }
}

/// `#[repr(C)]` return struct for the region ABI — NOT a bare tuple
/// (tuples are not FFI-safe; this was the exn PoC's central correctness
/// finding). `new_sp` is the post-collapse downward stack index;
/// `raised` is 0 (normal) or 1 (an exception is propagating: `ctx`
/// already holds the packet, and `new_sp` is `handler_sp` if a handler is
/// in scope, else the escape sp).
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct RegionRet {
    pub new_sp: i64,
    pub raised: i64,
}

/// The native region-function pointer type. (`stack_base`, `sp`, `ctx`)
/// → [`RegionRet`].
pub type RegionFn = unsafe extern "C" fn(*mut i64, i64, *mut ExnCtx) -> RegionRet;

// ---------------------------------------------------------------------
// IR helpers — DOWNWARD stack convention (mirror mod.rs push/pop/peek).
// Free functions so they don't borrow the module.
// ---------------------------------------------------------------------

/// Address of `stack[idx]` = `base + idx*8`.
fn addr_at(b: &mut FunctionBuilder, base: Value, idx: Value) -> Value {
    let eight = b.ins().iconst(types::I64, 8);
    let off = b.ins().imul(idx, eight);
    b.ins().iadd(base, off)
}

/// Load `stack[idx]`.
fn load_at(b: &mut FunctionBuilder, base: Value, idx: Value) -> Value {
    let a = addr_at(b, base, idx);
    b.ins().load(types::I64, MemFlags::trusted(), a, 0)
}

/// Store `v` into `stack[idx]`.
fn store_at(b: &mut FunctionBuilder, base: Value, idx: Value, v: Value) {
    let a = addr_at(b, base, idx);
    b.ins().store(MemFlags::trusted(), v, a, 0);
}

/// DOWNWARD PUSH: `sp -= 1; stack[sp] = v`. Returns the new sp.
fn emit_push(b: &mut FunctionBuilder, base: Value, sp: Value, v: Value) -> Value {
    let one = b.ins().iconst(types::I64, 1);
    let new_sp = b.ins().isub(sp, one);
    store_at(b, base, new_sp, v);
    new_sp
}

/// LOCAL_K / peek depth K (0 = top = `stack[sp]`): `stack[sp + K]`.
fn emit_local(b: &mut FunctionBuilder, base: Value, sp: Value, k: i64) -> Value {
    let kk = b.ins().iconst(types::I64, k);
    let idx = b.ins().iadd(sp, kk);
    load_at(b, base, idx)
}

/// untag tagged value: `(t - 1) >> 1` (arithmetic shift).
fn emit_untag(b: &mut FunctionBuilder, t: Value) -> Value {
    let one = b.ins().iconst(types::I64, 1);
    let m1 = b.ins().isub(t, one);
    b.ins().sshr_imm(m1, 1)
}

/// tag: `2n + 1`.
fn emit_tag(b: &mut FunctionBuilder, n: Value) -> Value {
    let two = b.ins().iconst(types::I64, 2);
    let m = b.ins().imul(n, two);
    let one = b.ins().iconst(types::I64, 1);
    b.ins().iadd(m, one)
}

/// DOWNWARD RETURN_N (normal exit). On entry the result is the top of
/// stack (`stack[sp]`) and the N args are at `stack[sp+1 .. sp+N]` (the
/// closure/retPC words are subsumed by the native call/ret). Collapse:
/// drop the result + N args, leave the result at `stack[sp+N]`, new sp =
/// `sp + N`. Returns `RegionRet { sp+N, 0 }`.
///
/// This is exactly the interpreter `do_return` value-collapse modulo the
/// closure+retPC bookkeeping the native frame handles: do_return pops
/// result, pops closure, pops retPC, drops N args, pushes result — i.e.
/// the surviving value (the result) ends up where the deepest collapsed
/// slot was. Here the deepest collapsed slot is `stack[sp+N]` (we don't
/// have closure/retPC slots on the shared stack — those are the native
/// frame), so new sp = sp+N and the result sits at stack[sp+N].
fn emit_return_n(b: &mut FunctionBuilder, base: Value, sp: Value, n: i64) {
    let result = load_at(b, base, sp); // top
    let n_v = b.ins().iconst(types::I64, n);
    let dst = b.ins().iadd(sp, n_v); // stack[sp+N]
    store_at(b, base, dst, result);
    let zero = b.ins().iconst(types::I64, 0);
    b.ins().return_(&[dst, zero]); // new_sp = sp+N, raised = 0
}

// ctx field accessors (handler_sp @ 0, exn_packet @ 8).
fn load_handler_sp(b: &mut FunctionBuilder, ctx: Value) -> Value {
    b.ins().load(types::I64, MemFlags::trusted(), ctx, 0)
}
fn store_handler_sp(b: &mut FunctionBuilder, ctx: Value, v: Value) {
    b.ins().store(MemFlags::trusted(), v, ctx, 0);
}
fn load_exn_packet(b: &mut FunctionBuilder, ctx: Value) -> Value {
    b.ins().load(types::I64, MemFlags::trusted(), ctx, 8)
}
fn store_exn_packet(b: &mut FunctionBuilder, ctx: Value, v: Value) {
    b.ins().store(MemFlags::trusted(), v, ctx, 8);
}
/// Load `ctx.interp_ptr` (offset 16) — the raw `*mut Interpreter` the
/// dynamic-call trampoline re-enters through.
#[allow(dead_code)]
fn load_interp_ptr(b: &mut FunctionBuilder, ctx: Value) -> Value {
    b.ins().load(types::I64, MemFlags::trusted(), ctx, 16)
}

// ---------------------------------------------------------------------
// Region — a small wrapper letting us declare + define several functions
// into the host `Jit`'s `JITModule`, so the region's native code shares
// the SAME module + lifetime as the per-function JIT (one finalize).
// ---------------------------------------------------------------------

/// The region-function signature: `(base, sp, ctx) -> (new_sp, raised)`.
fn region_sig(jit: &Jit) -> Signature {
    let mut sig = jit.module.make_signature();
    sig.params.push(AbiParam::new(types::I64)); // stack_base
    sig.params.push(AbiParam::new(types::I64)); // sp
    sig.params.push(AbiParam::new(types::I64)); // ctx ptr
    sig.returns.push(AbiParam::new(types::I64)); // new sp
    sig.returns.push(AbiParam::new(types::I64)); // raised (0/1)
    sig
}

/// Import the nativeness-tick trampoline into the function under
/// construction and emit a `call` to it (the root's first IR), so a
/// completed region run can prove NATIVE execution via the counter.
fn emit_native_tick(
    jit: &mut Jit,
    func: &mut cranelift::codegen::ir::Function,
) -> cranelift::codegen::ir::FuncRef {
    // No params, no returns.
    let sig = jit.module.make_signature();
    let id = jit
        .module
        .declare_function("polyml_jit_region_native_tick", Linkage::Import, &sig)
        .expect("declare native_tick");
    jit.module.declare_func_in_func(id, func)
}

/// A native multi-function region compiled into the host Jit module.
/// `root` is the entry the interpreter dispatches; the other ids are the
/// statically-known callees compiled in the SAME module (native
/// call/ret between them).
pub struct CompiledRegion {
    pub root: FuncId,
    pub callees: Vec<FuncId>,
}

// =====================================================================
// REGION SELECTION — the static call-subgraph step (S2 seam).
//
// A region is a root code object + its STATICALLY-KNOWN callees. The
// statically-known callees of a function are the closures it reaches via
// `CALL_CONST_ADDR*` (the closure pointer is baked in the code object's
// constant pool — known at compile time) — exactly the calls the
// per-function JIT cannot inline (the non-popping wall). `CALL_CLOSURE` /
// `CALL_LOCAL_B` targets are dynamic (a runtime stack value), so they
// stay at the region boundary and trampoline.
//
// `scan_static_callees` walks a code object's bytecode at instruction
// boundaries and returns the constant-pool byte offsets of every
// CALL_CONST_ADDR target. A full region builder would resolve each to a
// code object, recurse to a fixpoint, and compile the whole set into one
// JITModule. This function is the first hop of that fixpoint; it proves
// the selection seam is real (it reads true bootstrap bytecode), while
// the compilation of arbitrary real bytecode under the new convention is
// deferred to a later stage (it needs a full memory-backed translator).
// =====================================================================

/// A statically-known CALL_CONST_ADDR target inside a code object: the
/// bytecode offset of the call + the absolute address it reads the
/// closure pointer from (`full_body_ptr + read_at`).
#[derive(Debug, Clone, Copy)]
pub struct StaticCallee {
    /// Byte offset of the CALL_CONST_ADDR opcode in the bytecode.
    pub call_pc: usize,
    /// Absolute address of the constant-pool slot holding the callee
    /// closure pointer (read at runtime to survive GC).
    pub closure_slot_addr: u64,
}

/// Scan a code object for its statically-known callees (CALL_CONST_ADDR
/// targets). `bytecode` is the opcode-only portion; `full_body` is the
/// whole object (bytecode + constant pool), `full_body_addr` is its
/// absolute heap address. Returns one [`StaticCallee`] per CALL_CONST_ADDR
/// at a real instruction boundary. Stops (returns what it has) on the
/// first opcode whose length it can't decode — conservative.
#[must_use]
pub fn scan_static_callees(
    bytecode: &[u8],
    full_body: &[u8],
    full_body_addr: u64,
) -> Vec<StaticCallee> {
    use polyml_runtime::interpreter::disasm::decode;
    use polyml_runtime::interpreter::opcodes as op;

    let is_cca = |b: u8| {
        b == op::INSTR_CALL_CONST_ADDR8_0
            || b == op::INSTR_CALL_CONST_ADDR8_1
            || b == op::INSTR_CALL_CONST_ADDR8_8
            || b == op::INSTR_CALL_CONST_ADDR16_8
    };
    let mut out = Vec::new();
    let mut pc = 0usize;
    while pc < bytecode.len() {
        let b = bytecode[pc];
        let d = decode(bytecode, pc);
        if d.total_len == 0 {
            break; // can't find the next boundary; stop conservatively.
        }
        if is_cca(b) {
            // Re-derive the constant-pool read site exactly as the
            // interpreter / translator does (read_const_addr_operands).
            if let Some((byte_off, idx)) = cca_operands(bytecode, pc, b) {
                // pc after the opcode + immediates = pc + (d.total_len).
                let after = pc + d.total_len;
                let read_at = after + byte_off + idx * 8;
                if read_at + 8 <= full_body.len() {
                    out.push(StaticCallee {
                        call_pc: pc,
                        closure_slot_addr: full_body_addr + read_at as u64,
                    });
                }
            }
        }
        pc += d.total_len;
    }
    out
}

/// Decode CALL_CONST_ADDR immediate operands → (byte_off, const_idx),
/// mirroring `translate.rs::read_const_addr_operands`. `pc` points at the
/// opcode. Returns None on truncation.
fn cca_operands(bc: &[u8], pc: usize, op: u8) -> Option<(usize, usize)> {
    use polyml_runtime::interpreter::opcodes as o;
    let at = |i: usize| bc.get(i).copied();
    match op {
        o::INSTR_CALL_CONST_ADDR8_0 => Some((at(pc + 1)? as usize, 3)),
        o::INSTR_CALL_CONST_ADDR8_1 => Some((at(pc + 1)? as usize, 4)),
        o::INSTR_CALL_CONST_ADDR8_8 => Some((at(pc + 1)? as usize, at(pc + 2)? as usize + 3)),
        o::INSTR_CALL_CONST_ADDR16_8 => {
            let off = u16::from_le_bytes([at(pc + 1)?, at(pc + 2)?]) as usize;
            Some((off, at(pc + 3)? as usize + 3))
        }
        _ => None,
    }
}

/// One arithmetic leaf-callee spec for the demo region builder: arity +
/// a closed-form body over its untagged args. Body is `(args) -> result`
/// where args[k] is LOCAL_k (k=0 = top = last pushed = arg index
/// arity-1, matching the interpreter's arg layout in `region_top`).
pub struct LeafSpec {
    pub name: &'static str,
    pub arity: i64,
    /// `(builder, base, sp) -> tagged result value`. Implementors use
    /// `emit_local` to read args and must leave the tagged result in the
    /// returned SSA value (NOT yet pushed).
    pub body: fn(&mut FunctionBuilder, Value, Value) -> Value,
}

/// Compile a leaf (arithmetic-only, no calls) callee under the region
/// ABI: reads its args off the shared stack via LOCAL_k, computes a
/// result, pushes it, and emits RETURN_N(arity). Always `raised=0`.
fn build_leaf(jit: &mut Jit, spec: &LeafSpec) -> FuncId {
    let sig = region_sig(jit);
    let id = jit
        .module
        .declare_function(spec.name, Linkage::Local, &sig)
        .expect("declare leaf");
    let mut ctx = jit.module.make_context();
    ctx.func.signature = sig;
    ctx.func.name = UserFuncName::user(0, id.as_u32());
    let mut fbctx = FunctionBuilderContext::new();
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let base = b.block_params(entry)[0];
        let sp = b.block_params(entry)[1];
        // body computes the tagged result from the args on the stack.
        let result = (spec.body)(&mut b, base, sp);
        // PUSH result (downward), then RETURN_N(arity).
        let sp_pushed = emit_push(&mut b, base, sp, result);
        emit_return_n(&mut b, base, sp_pushed, spec.arity);
        b.finalize();
    }
    jit.module
        .define_function(id, &mut ctx)
        .expect("define leaf");
    jit.module.clear_context(&mut ctx);
    id
}

/// Build the demo whole-region root + callees. The region computes a
/// non-trivial expression that REQUIRES the non-popping convention:
///
///   region(a, b) = f(a, b) + g(a)
///       f(a,b) = a*b + a      (arity 2)
///       g(a)   = a + 100      (arity 1)
///
/// `region` calls `f`, then CONSUMES the result mid-function (adds g(a)) —
/// exactly the not-tail-equivalent case the per-function JIT bails on.
/// Both calls are NATIVE call/ret with args persisting on the shared
/// stack. This is a real multi-function region (3 functions, 2
/// inter-region native calls).
pub fn build_demo_region(jit: &mut Jit) -> CompiledRegion {
    // ---- leaf f(a,b) = a*b + a, arity 2 ----
    let f = build_leaf(
        jit,
        &LeafSpec {
            name: "wrjit_f",
            arity: 2,
            // args on stack: LOCAL_1 = a (deeper), LOCAL_0 = b (top).
            body: |b, base, sp| {
                let a_t = emit_local(b, base, sp, 1);
                let bb_t = emit_local(b, base, sp, 0);
                let a = emit_untag(b, a_t);
                let bb = emit_untag(b, bb_t);
                let ab = b.ins().imul(a, bb);
                let r = b.ins().iadd(ab, a);
                emit_tag(b, r)
            },
        },
    );
    // ---- leaf g(a) = a + 100, arity 1 ----
    let g = build_leaf(
        jit,
        &LeafSpec {
            name: "wrjit_g",
            arity: 1,
            body: |b, base, sp| {
                let a_t = emit_local(b, base, sp, 0);
                let a = emit_untag(b, a_t);
                let c = b.ins().iconst(types::I64, 100);
                let r = b.ins().iadd(a, c);
                emit_tag(b, r)
            },
        },
    );

    // ---- root region(a,b) = f(a,b) + g(a), arity 2, native calls ----
    let sig = region_sig(jit);
    let root = jit
        .module
        .declare_function("wrjit_region_top", Linkage::Local, &sig)
        .expect("declare root");
    let mut ctx = jit.module.make_context();
    ctx.func.signature = sig;
    ctx.func.name = UserFuncName::user(0, root.as_u32());
    let f_ref = jit.module.declare_func_in_func(f, &mut ctx.func);
    let g_ref = jit.module.declare_func_in_func(g, &mut ctx.func);
    let tick_ref = emit_native_tick(jit, &mut ctx.func);
    let mut fbctx = FunctionBuilderContext::new();
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let base = b.block_params(entry)[0];
        let sp0 = b.block_params(entry)[1];
        let cctx = b.block_params(entry)[2];
        // NATIVENESS PROOF: bump the native-tick counter on entry.
        b.ins().call(tick_ref, &[]);
        // root's own args (LOCAL_1 = a, LOCAL_0 = b).
        let a_t = emit_local(&mut b, base, sp0, 1);
        let b_t = emit_local(&mut b, base, sp0, 0);

        // === CALL f(a, b): push a then b (top arg = b at stack[sp]) ===
        let sp_a = emit_push(&mut b, base, sp0, a_t);
        let sp_b = emit_push(&mut b, base, sp_a, b_t);
        let call_f = b.ins().call(f_ref, &[base, sp_b, cctx]);
        let sp_after_f = b.inst_results(call_f)[0];
        // f's result is the top: stack[sp_after_f]. Read it; pop it
        // (sp += 1, downward) so the stack is back at sp0.
        let f_res_t = load_at(&mut b, base, sp_after_f);
        let one = b.ins().iconst(types::I64, 1);
        let sp_popped = b.ins().iadd(sp_after_f, one);

        // === CALL g(a): push a ===
        let sp_ga = emit_push(&mut b, base, sp_popped, a_t);
        let call_g = b.ins().call(g_ref, &[base, sp_ga, cctx]);
        let sp_after_g = b.inst_results(call_g)[0];
        let g_res_t = load_at(&mut b, base, sp_after_g);
        let sp_popped2 = b.ins().iadd(sp_after_g, one);

        // === region result = f_res + g_res (mid-function consume) ===
        let f_res = emit_untag(&mut b, f_res_t);
        let g_res = emit_untag(&mut b, g_res_t);
        let sum = b.ins().iadd(f_res, g_res);
        let sum_t = emit_tag(&mut b, sum);
        // PUSH the result; sp is back at sp0, so push → stack[sp0-1].
        // RETURN_N(2) collapses root's own 2 args.
        let sp_res = emit_push(&mut b, base, sp_popped2, sum_t);
        emit_return_n(&mut b, base, sp_res, 2);
        b.finalize();
    }
    jit.module
        .define_function(root, &mut ctx)
        .expect("define root");
    jit.module.clear_context(&mut ctx);

    CompiledRegion {
        root,
        callees: vec![f, g],
    }
}

/// Build a SECOND demo region exercising the native-frame EXCEPTION
/// convention: a root that installs a handler over a body that calls a
/// callee which RAISEs; the exception unwinds across the native frame
/// boundary back to the root's handler (the verified checked-return
/// model). The region computes:
///
///   safe(a) = (raiser(a)) handle _ => a + 7
///       raiser(a) RAISEs a Fail packet (tag 99) UNCONDITIONALLY.
///
/// So `safe(a)` always returns `a + 7` via the handler. This exercises:
///   - SET_HANDLER (handler_sp on the shared ctx),
///   - a native call to a callee that RAISEs (returns raised=1),
///   - the per-call-site `brif raised` + frame-range handler test,
///   - the local handler block + RETURN_N normal exit.
///
/// Block structure of the root:
///   entry      : SET_HANDLER; CALL raiser; brif raised -> decide / normal
///   decide_blk : handler in THIS frame? (handler_sp <= hidx, downward,
///                != NO_HANDLER) -> handler_blk(sp=handler_sp) else
///                propagate_blk
///   handler_blk: restore old handler_sp; LDEXC (read packet, ignore);
///                compute a+7; RETURN_N(1)
///   propagate  : return (sp, 1)  — handler is in an OUTER frame / interp
///   normal_blk : DELETE_HANDLER normal exit (callee returned normally —
///                unreachable here but valid IR + correct shape)
pub fn build_exn_region(jit: &mut Jit) -> CompiledRegion {
    // ---- callee raiser(a): RAISE Fail(99) unconditionally, arity 1 ----
    let sig = region_sig(jit);
    let raiser = jit
        .module
        .declare_function("wrjit_raiser", Linkage::Local, &sig)
        .expect("declare raiser");
    {
        let mut ctx = jit.module.make_context();
        ctx.func.signature = sig.clone();
        ctx.func.name = UserFuncName::user(0, raiser.as_u32());
        let mut fbctx = FunctionBuilderContext::new();
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let sp = b.block_params(entry)[1];
            let cctx = b.block_params(entry)[2];
            // RAISE Fail(99): set the packet, return (sp, raised=1).
            // handler_sp is NOT in this frame (the handler is in the
            // caller), so we PROPAGATE: leave sp as-is, return raised=1.
            // The frame that OWNS the handler sets sp=handler_sp, per the
            // checked-return model (it has the handler block to jump to).
            let fail = b.ins().iconst(types::I64, tag_i64(99));
            store_exn_packet(&mut b, cctx, fail);
            let raised = b.ins().iconst(types::I64, 1);
            b.ins().return_(&[sp, raised]);
            b.finalize();
        }
        jit.module
            .define_function(raiser, &mut ctx)
            .expect("define raiser");
        jit.module.clear_context(&mut ctx);
    }

    // ---- root safe(a) = raiser(a) handle _ => a+7, arity 1 ----
    let root = jit
        .module
        .declare_function("wrjit_safe", Linkage::Local, &sig)
        .expect("declare safe");
    let mut ctx = jit.module.make_context();
    ctx.func.signature = sig;
    ctx.func.name = UserFuncName::user(0, root.as_u32());
    let raiser_ref = jit.module.declare_func_in_func(raiser, &mut ctx.func);
    let tick_ref = emit_native_tick(jit, &mut ctx.func);
    let mut fbctx = FunctionBuilderContext::new();
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
        let entry = b.create_block();
        let decide_blk = b.create_block();
        let handler_blk = b.create_block();
        let propagate_blk = b.create_block();
        let normal_blk = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        let base = b.block_params(entry)[0];
        let sp0 = b.block_params(entry)[1];
        let cctx = b.block_params(entry)[2];
        // NATIVENESS PROOF: bump the native-tick counter on entry.
        b.ins().call(tick_ref, &[]);
        // a = LOCAL_0 (the single arg). Captured once for the handler.
        let a_t = emit_local(&mut b, base, sp0, 0);
        let a = emit_untag(&mut b, a_t);

        // === SET_HANDLER (downward two-word frame) ===
        // push marker (handler_pc placeholder) at stack[sp0-1], then push
        // old handler_sp at stack[sp0-2]; handler_sp = sp0-1 (marker idx).
        let marker = b.ins().iconst(types::I64, 0xBEEF);
        let sp_m = emit_push(&mut b, base, sp0, marker); // sp0-1
        let hidx = sp_m; // handler_sp = index of the marker slot
        let old_h = load_handler_sp(&mut b, cctx);
        let sp_old = emit_push(&mut b, base, sp_m, old_h); // sp0-2
        store_handler_sp(&mut b, cctx, hidx);

        // === body: CALL raiser(a) ===
        let sp_arg = emit_push(&mut b, base, sp_old, a_t); // sp0-3
        let call = b.ins().call(raiser_ref, &[base, sp_arg, cctx]);
        let sp_after = b.inst_results(call)[0];
        let raised = b.inst_results(call)[1];
        b.ins().brif(
            raised,
            decide_blk,
            &[BlockArg::from(sp_after)],
            normal_blk,
            &[BlockArg::from(sp_after)],
        );
        b.seal_block(entry);

        // ---- decide_blk: is the live handler in THIS frame? ----
        // Downward: a handler installed in this frame is at hidx (= sp0-1),
        // which is >= any sp the frame reaches (sp only decreases as we
        // push). The CURRENT handler_sp (from ctx) is in-frame iff it
        // equals our hidx AND is a real handler. (If an inner frame had
        // installed + not deleted its own handler the packet would target
        // that; but raiser installs none, so handler_sp is still hidx.)
        b.switch_to_block(decide_blk);
        let _sp_d = b.append_block_param(decide_blk, types::I64);
        let cur_hsp = load_handler_sp(&mut b, cctx);
        let no_h = b.ins().iconst(types::I64, NO_HANDLER);
        let is_real = b.ins().icmp(IntCC::NotEqual, cur_hsp, no_h);
        let is_ours = b.ins().icmp(IntCC::Equal, cur_hsp, hidx);
        let local = b.ins().band(is_real, is_ours);
        b.ins().brif(
            local,
            handler_blk,
            &[BlockArg::from(cur_hsp)],
            propagate_blk,
            &[],
        );
        b.seal_block(decide_blk);

        // ---- handler_blk: run the handler, normal-collapse + RETURN ----
        b.switch_to_block(handler_blk);
        let hsp = b.append_block_param(handler_blk, types::I64);
        // do_raise_ex restores handler_sp from the saved old value, which
        // we stored at stack[hidx-1] (= stack[sp0-2], i.e. hidx + 1 toward
        // the deep end? No: downward, old_h is at the SMALLER index sp_m-1
        // = hidx-1). Restore it.
        let one = b.ins().iconst(types::I64, 1);
        let old_slot = b.ins().isub(hsp, one); // hidx - 1
        let restored = load_at(&mut b, base, old_slot);
        store_handler_sp(&mut b, cctx, restored);
        // LDEXC: read the packet (a real handler would match on it; this
        // demo's `handle _ =>` ignores it).
        let _pkt = load_exn_packet(&mut b, cctx);
        // handler body: a + 7.
        let seven = b.ins().iconst(types::I64, 7);
        let res = b.ins().iadd(a, seven);
        let res_t = emit_tag(&mut b, res);
        // The handler produces the frame's single result. Root has arity
        // 1: its one arg is at stack[sp0] (LOCAL_0). Normal handle-exit
        // collapses to a RETURN_N(1): PUSH the result then RETURN_N(1) so
        // the result lands at stack[sp0] and new_sp = sp0 (result on top
        // at the collapse destination). We PUSH from `hsp` (= handler_sp =
        // hidx = sp0-1, the unwound sp), so push -> stack[sp0-2]; but
        // simpler + identical: derive from sp0 directly. PUSH at sp0
        // (sp_for_push = sp0) then RETURN_N(1) -> result at stack[sp0+1]?
        // No: we must leave it at stack[sp0]. Use emit_return_n with the
        // result already pushed at stack[sp0-1]:
        let _ = hsp; // unwound sp; not needed (we re-derive from sp0)
        let sp_push = emit_push(&mut b, base, sp0, res_t); // sp0-1
        emit_return_n(&mut b, base, sp_push, 1); // result -> stack[sp0], new_sp=sp0
        b.seal_block(handler_blk);

        // ---- propagate_blk: handler is in an OUTER frame / the interp ----
        b.switch_to_block(propagate_blk);
        let propagated = load_handler_sp(&mut b, cctx);
        let one2 = b.ins().iconst(types::I64, 1);
        b.ins().return_(&[propagated, one2]); // raised=1, sp=handler_sp
        b.seal_block(propagate_blk);

        // ---- normal_blk: callee returned normally (DELETE_HANDLER) ----
        // Unreachable at runtime in THIS demo (raiser always raises) but
        // valid + correct IR. Result is on top at stack[sp_n]. Restore
        // old handler_sp from stack[hidx-1], then RETURN_N(1).
        b.switch_to_block(normal_blk);
        let sp_n = b.append_block_param(normal_blk, types::I64);
        let one3 = b.ins().iconst(types::I64, 1);
        let old_slot_n = b.ins().isub(hidx, one3);
        let restored_n = load_at(&mut b, base, old_slot_n);
        store_handler_sp(&mut b, cctx, restored_n);
        emit_return_n(&mut b, base, sp_n, 1);
        b.seal_block(normal_blk);

        b.finalize();
    }
    jit.module
        .define_function(root, &mut ctx)
        .expect("define safe");
    jit.module.clear_context(&mut ctx);

    CompiledRegion {
        root,
        callees: vec![raiser],
    }
}

#[inline]
fn tag_i64(n: i64) -> i64 {
    n.wrapping_mul(2).wrapping_add(1)
}

// =====================================================================
// REFERENCE MODELS — faithful re-impls of the interpreter's downward
// stack discipline, the GROUND TRUTH for the differential. They mirror
// mod.rs push/pop + do_return + do_raise_ex / SET_HANDLER on an explicit
// fixed Vec, byte-identical collapse arithmetic.
// =====================================================================

#[inline]
fn untag_i64(t: i64) -> i64 {
    (t - 1) >> 1
}

/// Reference for [`build_demo_region`]: region(a,b)=f(a,b)+g(a) on a
/// DOWNWARD stack, step-for-step mirroring `build_demo_region`'s IR
/// (push: sp-=1; LOCAL_k: stack[sp+k]; RETURN_N(N): result on top
/// collapses to stack[sp+N], new sp = sp+N). The GROUND TRUTH for the
/// differential.
pub fn demo_region_reference(a: i64, b: i64) -> i64 {
    // Downward PUSH: sp -= 1; stack[sp] = v.
    fn push(stack: &mut [i64], sp: &mut usize, v: i64) {
        *sp -= 1;
        stack[*sp] = v;
    }
    // Downward RETURN_N(N): result is on top (stack[sp]); collapse so it
    // lands at stack[sp+N]; new sp = sp+N. Returns the new sp.
    fn return_n(stack: &mut [i64], sp: usize, n: usize) -> usize {
        let result = stack[sp];
        let dst = sp + n;
        stack[dst] = result;
        dst
    }

    let cap = 256usize;
    let mut stack = vec![0i64; cap];
    // Root's frame: caller pushed a then b so b is on top (LOCAL_0), a is
    // LOCAL_1 (matches build_demo's emit_local(sp,1)=a, (sp,0)=b).
    let mut sp = cap;
    push(&mut stack, &mut sp, tag_i64(a));
    push(&mut stack, &mut sp, tag_i64(b));
    let sp0 = sp;
    let a_t = stack[sp0 + 1]; // LOCAL_1
    let b_t = stack[sp0]; // LOCAL_0

    // CALL f(a,b): push a, b; f reads LOCAL_1=a, LOCAL_0=b; pushes
    // result; RETURN_N(2).
    push(&mut stack, &mut sp, a_t);
    push(&mut stack, &mut sp, b_t);
    let fa = untag_i64(stack[sp + 1]);
    let fb = untag_i64(stack[sp]);
    push(
        &mut stack,
        &mut sp,
        tag_i64(fa.wrapping_mul(fb).wrapping_add(fa)),
    );
    let sp_after_f = return_n(&mut stack, sp, 2);
    let f_res_t = stack[sp_after_f];
    let sp_popped = sp_after_f + 1; // pop f's result

    // CALL g(a): push a; g reads LOCAL_0=a; pushes result; RETURN_N(1).
    sp = sp_popped;
    push(&mut stack, &mut sp, a_t);
    let ga = untag_i64(stack[sp]);
    push(&mut stack, &mut sp, tag_i64(ga.wrapping_add(100)));
    let sp_after_g = return_n(&mut stack, sp, 1);
    let g_res_t = stack[sp_after_g];
    let sp_popped2 = sp_after_g + 1;

    // region result = f_res + g_res; push; RETURN_N(2) for root's args.
    sp = sp_popped2;
    let sum = tag_i64(untag_i64(f_res_t).wrapping_add(untag_i64(g_res_t)));
    push(&mut stack, &mut sp, sum);
    let final_sp = return_n(&mut stack, sp, 2);
    stack[final_sp]
}

/// Reference for [`build_exn_region`]: safe(a) = (raise Fail) handle _ =>
/// a + 7. Always returns a+7.
pub fn exn_region_reference(a: i64) -> i64 {
    tag_i64(a.wrapping_add(7))
}

// =====================================================================
// DRIVER — finalize the host module + run the region natively on a
// fresh shared stack, returning the native result. Used by the
// `whole-region` CLI demo + the differential test. A call counter in the
// region confirms NATIVENESS (the native code ran, not an interp
// fallback).
// =====================================================================

/// Result of running the demo region natively.
#[derive(Debug, Clone, Copy)]
pub struct RegionRunResult {
    pub native_result: i64,
    pub reference_result: i64,
    pub new_sp: i64,
    pub raised: i64,
    /// Number of native region-root entries observed during this run
    /// (proves NATIVE execution: must be exactly 1 for a single run).
    pub native_ticks: u64,
}

/// Compile + finalize the demo arithmetic region into `jit`, run it on a
/// fresh shared stack for `(a, b)`, and return both the native result and
/// the reference result. SAFETY: finalizes the module (no further
/// definitions after this in the same module unless re-prepared).
pub fn run_demo_region(jit: &mut Jit, a: i64, b: i64) -> RegionRunResult {
    let region = build_demo_region(jit);
    jit.module
        .finalize_definitions()
        .expect("finalize demo region");
    let ptr = jit.module.get_finalized_function(region.root);
    // SAFETY: region.root was compiled with the RegionFn ABI above.
    let f: RegionFn = unsafe { std::mem::transmute::<*const u8, RegionFn>(ptr) };

    let cap = 256usize;
    let mut stack = vec![0i64; cap];
    // Downward: place root args at the top region, sp pointing at them.
    // push a then b (b on top). sp = cap - 2.
    stack[cap - 1] = tag_i64(a); // arg a (deeper, LOCAL_1)
    stack[cap - 2] = tag_i64(b); // arg b (top,   LOCAL_0)
    let sp_in = (cap - 2) as i64;
    let mut ctx = ExnCtx::default();
    reset_native_tick();
    // SAFETY: stack is a valid [i64; cap]; ctx is a valid ExnCtx.
    let ret = unsafe { f(stack.as_mut_ptr(), sp_in, &mut ctx) };
    let ticks = native_tick_count();
    let native = stack[ret.new_sp as usize];
    RegionRunResult {
        native_result: native,
        reference_result: demo_region_reference(a, b),
        new_sp: ret.new_sp,
        raised: ret.raised,
        native_ticks: ticks,
    }
}

/// Compile + finalize the exception region, run it on a fresh shared
/// stack for `a`, and return native vs reference.
pub fn run_exn_region(jit: &mut Jit, a: i64) -> RegionRunResult {
    let region = build_exn_region(jit);
    jit.module
        .finalize_definitions()
        .expect("finalize exn region");
    let ptr = jit.module.get_finalized_function(region.root);
    // SAFETY: region.root compiled with the RegionFn ABI.
    let f: RegionFn = unsafe { std::mem::transmute::<*const u8, RegionFn>(ptr) };

    let cap = 256usize;
    let mut stack = vec![0i64; cap];
    stack[cap - 1] = tag_i64(a); // the single arg (LOCAL_0)
    let sp_in = (cap - 1) as i64;
    let mut ctx = ExnCtx::default();
    reset_native_tick();
    // SAFETY: valid stack + ctx.
    let ret = unsafe { f(stack.as_mut_ptr(), sp_in, &mut ctx) };
    let ticks = native_tick_count();
    let native = stack[ret.new_sp as usize];
    RegionRunResult {
        native_result: native,
        reference_result: exn_region_reference(a),
        new_sp: ret.new_sp,
        raised: ret.raised,
        native_ticks: ticks,
    }
}

/// CLI entry: compile + run the whole-region demo regions, print a
/// differential + nativeness report, and return `true` iff every case is
/// differential-clean AND ran native (tick == 1). Used by
/// `poly run --whole-region` (which only runs this demo when the env is
/// set — it does NOT alter the default interpreter run otherwise).
#[must_use]
pub fn run_whole_region_demo() -> bool {
    println!("== whole-region JIT demo (WHOLE_REGION_JIT) ==");
    println!("Region 1: non-popping shared-stack convention");
    println!("  region(a,b) = f(a,b)+g(a), f(a,b)=a*b+a, g(a)=a+100");
    println!("  (mid-function CALL result consumed — the case --jit bails on)");

    let mut clean = true;
    let mut cases = 0usize;
    let mut diverged = 0usize;
    let mut non_native = 0usize;
    for a in -30..=30i64 {
        for b in -30..=30i64 {
            let mut jit = match Jit::new() {
                Ok(j) => j,
                Err(e) => {
                    eprintln!("jit init failed: {e}");
                    return false;
                }
            };
            let r = run_demo_region(&mut jit, a, b);
            cases += 1;
            if r.raised != 0 || r.native_result != r.reference_result {
                diverged += 1;
                clean = false;
            }
            if r.native_ticks != 1 {
                non_native += 1;
                clean = false;
            }
        }
    }
    println!("  arithmetic region: {cases} cases, {diverged} diverged, {non_native} non-native");
    {
        let mut jit = Jit::new().expect("jit");
        let r = run_demo_region(&mut jit, 3, 4);
        println!(
            "  region(3,4) = {} (expected 118), native_ticks={} (1=native)",
            untag_i64(r.native_result),
            r.native_ticks
        );
    }

    println!("Region 2: native-frame EXCEPTION unwind");
    println!("  safe(a) = (raise Fail) handle _ => a+7  (raise crosses a native call)");
    let mut exn_cases = 0usize;
    let mut exn_bad = 0usize;
    for a in -30..=30i64 {
        let mut jit = Jit::new().expect("jit");
        let r = run_exn_region(&mut jit, a);
        exn_cases += 1;
        if r.raised != 0 || untag_i64(r.native_result) != a + 7 || r.native_ticks != 1 {
            exn_bad += 1;
            clean = false;
        }
    }
    println!("  exception region: {exn_cases} cases, {exn_bad} bad");
    {
        let mut jit = Jit::new().expect("jit");
        let r = run_exn_region(&mut jit, 10);
        println!(
            "  safe(10) = {} (expected 17), raised={} native_ticks={}",
            untag_i64(r.native_result),
            r.raised,
            r.native_ticks
        );
    }

    if clean {
        println!("RESULT: whole-region demo DIFFERENTIAL-CLEAN + NATIVE (all cases).");
    } else {
        println!("RESULT: whole-region demo FAILED — see counts above.");
    }
    clean
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn demo_region_differential_matches_reference() {
        // Each run finalizes its own module, so use a fresh Jit per case.
        let mut fails = 0usize;
        let mut ran = 0usize;
        for a in -20..=20i64 {
            for b in -20..=20i64 {
                let mut jit = Jit::new().expect("jit");
                let r = run_demo_region(&mut jit, a, b);
                ran += 1;
                assert_eq!(r.raised, 0, "demo region must not raise (a={a},b={b})");
                if r.native_result != r.reference_result {
                    fails += 1;
                    eprintln!(
                        "MISMATCH a={a} b={b}: native={} ref={}",
                        untag_i64(r.native_result),
                        untag_i64(r.reference_result)
                    );
                }
            }
        }
        assert_eq!(fails, 0, "{fails}/{ran} demo-region cases diverged");
    }

    #[test]
    fn demo_region_value_is_correct() {
        // region(3,4) = f(3,4)+g(3) = (3*4+3) + (3+100) = 15 + 103 = 118.
        let mut jit = Jit::new().expect("jit");
        let r = run_demo_region(&mut jit, 3, 4);
        assert_eq!(untag_i64(r.native_result), 118);
        assert_eq!(untag_i64(r.reference_result), 118);
        // NATIVENESS: the native root must have run exactly once (proves
        // native execution, not an interp fallback).
        assert_eq!(r.native_ticks, 1, "region root must execute NATIVE once");
    }

    #[test]
    fn scan_static_callees_finds_cca_at_boundary() {
        use polyml_runtime::interpreter::opcodes as op;
        // A tiny synthetic code body: CONST_INT_B 5; CALL_CONST_ADDR8_0 2;
        // RETURN_1.  CALL_CONST_ADDR8_0 (0x57) has one immediate (the
        // byte offset). With idx fixed = 3, the read site is
        // (pc_after_opcode_and_imm) + byte_off + 3*8.
        let bc = vec![
            op::INSTR_CONST_INT_B,
            5, // CONST_INT_B 5
            op::INSTR_CALL_CONST_ADDR8_0,
            0, // CALL_CONST_ADDR8_0, byte_off = 0
            op::INSTR_RETURN_1,
        ];
        // full_body = bytecode + an 8-word constant pool so read_at fits.
        let mut full = bc.clone();
        full.extend(std::iter::repeat_n(0u8, 8 * 8));
        let base_addr = 0x1000u64;
        let callees = scan_static_callees(&bc, &full, base_addr);
        assert_eq!(callees.len(), 1, "should find exactly one CCA target");
        assert_eq!(callees[0].call_pc, 2, "CCA opcode is at bytecode offset 2");
        // read_at = (after opcode+imm = 4) + byte_off(0) + 3*8 = 28.
        assert_eq!(callees[0].closure_slot_addr, base_addr + 28);
    }

    #[test]
    fn scan_static_callees_ignores_immediate_bytes() {
        use polyml_runtime::interpreter::opcodes as op;
        // CONST_INT_B 0x57 — the 0x57 is an IMMEDIATE, not a CCA opcode.
        // The boundary-aware scan must NOT flag it.
        let bc = vec![op::INSTR_CONST_INT_B, 0x57, op::INSTR_RETURN_1];
        let callees = scan_static_callees(&bc, &bc, 0x2000);
        assert!(
            callees.is_empty(),
            "0x57 as an immediate is not a CALL_CONST_ADDR"
        );
    }

    #[test]
    fn exn_region_unwinds_across_native_frame() {
        // safe(a) = (raise Fail) handle _ => a+7, for several a.
        for a in [-5i64, 0, 1, 10, 41, 100] {
            let mut jit = Jit::new().expect("jit");
            let r = run_exn_region(&mut jit, a);
            assert_eq!(
                r.raised, 0,
                "exn must be CAUGHT by the root handler (a={a}) — got raised={}",
                r.raised
            );
            assert_eq!(
                untag_i64(r.native_result),
                a + 7,
                "safe({a}) should be {} (handler caught the cross-frame raise)",
                a + 7
            );
            assert_eq!(untag_i64(r.reference_result), a + 7);
            assert_eq!(
                r.native_ticks, 1,
                "exn region root must execute NATIVE once"
            );
        }
    }
}
