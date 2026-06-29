//! S3 — the MEMORY-BACKED whole-region translator.
//!
//! Lowers REAL PolyML bytecode (bootstrap / compiled-SML code objects)
//! into Cranelift IR under the whole-region convention proven in
//! [`crate::region`] (S1-S2). Unlike [`crate::translate`] — which tracks
//! the SML value stack as a *compile-time* `Vec<Value>` and therefore
//! cannot express the non-popping call convention — this translator
//! lowers each opcode against the interpreter's REAL downward-growing
//! shared stack, threading the stack pointer `sp` as an SSA value through
//! every block. The shared stack IS `interp.stack` (a fixed
//! `Box<[PolyWord]>`), so GC scanning `[sp, len)` covers region frames
//! for free and the boundary hands the region the interpreter's real
//! `sp` / `stack_base` / `ExnCtx`.
//!
//! Behind the `WHOLE_REGION_JIT` flag. The default interpreter path and
//! the per-function `--jit` path are UNTOUCHED.
//!
//! =====================================================================
//! THE FRAME HANDSHAKE (the load-bearing correctness invariant)
//! =====================================================================
//! The interpreter's `do_call` (mod.rs:5981) pushes `retPC` then
//! `closure` before jumping to the callee, so at callee entry the
//! downward stack is (top -> bottom):
//!
//!   stack[sp]     = closure        (LOCAL_0)
//!   stack[sp+1]   = retPC          (LOCAL_1)
//!   stack[sp+2]   = arg_{N-1}      (LOCAL_2)   <- top arg (last pushed)
//!   ...
//!   stack[sp+N+1] = arg_0          (LOCAL_{N+1}, deepest arg)
//!
//! Real compiled bytecode addresses its args via exactly these LOCAL_K
//! indices, so the region MUST keep the closure + retPC slots physically
//! on the shared stack (they are NOT subsumed by the native call/ret as
//! the synthetic S1-S2 regions assumed). Two consequences:
//!
//!   - CALL_CONST_ADDR (a region->region native call): the SML compiler
//!     emits the arg pushes BEFORE the CALL opcode, and `do_call` pushes
//!     retPC + closure AFTER (on top of the args). So the native lowering,
//!     at a CALL_CONST_ADDR with the callee arity N already pushed as
//!     args, pushes a retPC placeholder then the closure word, THEN does
//!     the native `call`. The callee sees the exact interpreter layout.
//!
//!   - RETURN_N: `do_return` (mod.rs:6289) pops result, pops closure,
//!     pops retPC, drops N args, pushes result. Downward: at entry
//!     stack[sp]=result, stack[sp+1]=closure, stack[sp+2]=retPC,
//!     stack[sp+3 .. sp+2+N]=args; the result lands at stack[sp+2+N] and
//!     the new sp = sp+2+N. So a RETURN_N collapses by **N+2**, leaving
//!     the result where the deepest collapsed slot (the deepest arg) was.
//!     The native region's RETURN_N emits exactly this collapse, so after
//!     a region->region call the caller's sp points at the single result
//!     on top and the stack is byte-identical to the interpreter's.
//!
//! The boundary (the interp `do_call` hook) replicates the SAME push of
//! retPC + closure before invoking the region root, so the root's
//! LOCAL_K reads and its RETURN_N collapse are identical to the
//! interpreter. See [`crate::boundary`].
//!
//! =====================================================================
//! CORE OPCODE SUBSET (graceful floor)
//! =====================================================================
//! Covered (enough for a real arithmetic/recursive region):
//!   - CONST_0..4/10, CONST_INT_B/W                       (literal push)
//!   - LOCAL_0..15, LOCAL_B/W                             (peek + push)
//!   - INDIRECT_0..5, INDIRECT_B                          (heap field read)
//!   - INDIRECT_LOCAL_B0/B1, INDIRECT_0_LOCAL_0, INDIRECT_LOCAL_BB
//!   - RESET_1/2, RESET_B (drop N)                        (sp += N)
//!   - RESET_R_1/2/3, RESET_R_B (keep top, drop N below)
//!   - JUMP8/16, JUMP_BACK8/16, JUMP8/16_FALSE, JUMP8/16_TRUE
//!   - FIXED_ADD/SUB/MULT/QUOT/REM  (with Overflow / DivByZero raise)
//!   - WORD_ADD/SUB/MULT/AND/OR/XOR/SHL/SHR_LOG/DIV/MOD  (tag-aware)
//!   - EQUAL_WORD, LESS/GREATER (signed/unsigned, eq variants)
//!   - NOT_BOOLEAN, IS_TAGGED
//!   - RETURN_1/2/3, RETURN_B/W                            (collapse N+2)
//!   - CALL_CONST_ADDR8_0/8_1/8_8/16_8 (statically-resolved native call)
//!   - NO_OP, STACK_SIZE16 (prologue no-op)
//!
//! ANY other opcode bails the WHOLE region to the interpreter (clean
//! fallback, NOT a partial compile). FIXED_ADD/SUB/MULT raise Overflow
//! and FIXED_QUOT/REM + WORD_DIV/MOD raise DivByZero via the same
//! checked-return-sentinel exception model as the rest of the region
//! (raised=1, packet in ctx) -- see [`emit_raise`].

#![allow(clippy::pedantic, clippy::nursery)]
#![allow(
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap
)]

use crate::Jit;
use crate::region::NO_HANDLER;
use cranelift::codegen::ir::{Block, BlockArg, UserFuncName};
use cranelift::prelude::*;
use cranelift_module::{FuncId, Linkage, Module};
use polyml_runtime::interpreter::disasm::decode;
use polyml_runtime::interpreter::opcodes as op;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// Why a region failed to compile (bailed cleanly to the interpreter).
#[derive(Debug, Clone)]
pub enum BailReason {
    /// An opcode outside the core subset (whole region bails).
    UnsupportedOpcode {
        op: u8,
        name: &'static str,
        at: usize,
    },
    /// Truncated / undecodable bytecode at this offset.
    Truncated(usize),
    /// A CALL_CONST_ADDR whose target code object couldn't be resolved
    /// (e.g. arity inference failed) -- dynamic boundary, bail.
    UnresolvableCallee(usize),
    /// A jump landed off a real instruction boundary (mid-instruction)
    /// -- conservative bail (we never produce a partial compile).
    JumpMidInstruction(usize),
    /// Region call-graph exceeded the static-callee budget.
    RegionTooLarge,
    /// A Cranelift module-level error while declaring/defining.
    ModuleError(String),
}

impl std::fmt::Display for BailReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BailReason::UnsupportedOpcode { op, name, at } => {
                write!(f, "unsupported opcode 0x{op:02x} ({name}) at {at}")
            }
            BailReason::Truncated(at) => write!(f, "truncated bytecode at {at}"),
            BailReason::UnresolvableCallee(at) => write!(f, "unresolvable CCA callee at {at}"),
            BailReason::JumpMidInstruction(at) => write!(f, "jump to mid-instruction {at}"),
            BailReason::RegionTooLarge => write!(f, "region exceeds static-callee budget"),
            BailReason::ModuleError(s) => write!(f, "module error: {s}"),
        }
    }
}

/// A code object resolved for compilation: its bytecode-only slice, the
/// full body (bytecode + constant pool) so CONST/CALL reads land, the
/// object's absolute heap address, and its inferred SML arity.
#[derive(Clone)]
pub struct ResolvedCode {
    /// Absolute heap address of the code object's first body word.
    pub addr: u64,
    /// Bytecode-only bytes (opcodes, no constant pool).
    pub bytecode: Vec<u8>,
    /// Full body bytes (bytecode + const pool + trailer).
    pub full_body: Vec<u8>,
    /// SML arity (number of args), from a RETURN_N scan.
    pub arity: usize,
}

/// Resolve a code object at `code_obj_addr` (the body's first word) into
/// its bytecode + constant pool, mirroring `install_all_jit_entries`'s
/// code-object split exactly. Returns None if the object is malformed or
/// its arity cannot be inferred.
///
/// # Safety
/// `code_obj_addr` must be a live code object body pointer; only called
/// at compile time (heap frozen, no GC since image load).
#[must_use]
pub unsafe fn resolve_code(code_obj_addr: u64) -> Option<ResolvedCode> {
    if code_obj_addr == 0 || code_obj_addr & 0x7 != 0 {
        return None;
    }
    // SAFETY: caller-trusted compile-time invariant.
    unsafe {
        let code_obj = code_obj_addr as *const usize;
        let lw_ptr = code_obj.sub(1);
        let lw = lw_ptr.read();
        let n_words = lw & (usize::MAX >> 8);
        if !(2..=(1 << 24)).contains(&n_words) {
            return None;
        }
        let body_len_bytes = n_words * 8;
        let body = std::slice::from_raw_parts(code_obj.cast::<u8>(), body_len_bytes).to_vec();
        // Const-pool boundary = body_len + trailing-offset word.
        let trailing_offset_word = body_len_bytes - 8;
        let trailing_offset = i64::from_le_bytes(
            body[trailing_offset_word..trailing_offset_word + 8]
                .try_into()
                .ok()?,
        );
        let cp_byte_off = (body_len_bytes as i64 + trailing_offset) as usize;
        let bytecode_end = cp_byte_off.saturating_sub(8).min(body.len());
        let bytecode = body[..bytecode_end].to_vec();
        let arity = crate::translate::arity_from_return_scan_pub(&bytecode)?;
        Some(ResolvedCode {
            addr: code_obj_addr,
            bytecode,
            full_body: body,
            arity,
        })
    }
}

/// Read the closure pointer a CALL_CONST_ADDR* targets at COMPILE TIME
/// (the heap is frozen). Returns the code-object body address the
/// closure points at, or None. Mirrors the interpreter's
/// `read_pc_const` / `do_call` closure -> code resolution.
///
/// # Safety
/// Only called at compile time; the read address is inside the resolved
/// code object's constant pool, and the closure is a live data pointer.
unsafe fn cca_target_code_addr(rc: &ResolvedCode, pc: usize, opcode: u8) -> Option<u64> {
    let (byte_off, idx) = cca_operands(&rc.bytecode, pc, opcode)?;
    let d = decode(&rc.bytecode, pc);
    if d.total_len == 0 {
        return None;
    }
    let after = pc + d.total_len;
    let read_at = after + byte_off + idx * 8;
    if read_at + 8 > rc.full_body.len() {
        return None;
    }
    let closure = u64::from_le_bytes(rc.full_body[read_at..read_at + 8].try_into().ok()?);
    if closure == 0 || closure & 0x7 != 0 {
        return None;
    }
    // closure[0] = code object pointer (F_CLOSURE_OBJ layout).
    // SAFETY: compile-time; closure is a live data pointer.
    let code_obj = unsafe { (closure as *const usize).read() };
    if code_obj == 0 || code_obj & 0x7 != 0 {
        return None;
    }
    Some(code_obj as u64)
}

/// Read the closure word (bits) a CALL_CONST_ADDR* targets, at compile
/// time. This is the exact value the interpreter pushes as the closure.
fn cca_closure_bits(rc: &ResolvedCode, pc: usize, opcode: u8) -> Option<i64> {
    let (byte_off, idx) = cca_operands(&rc.bytecode, pc, opcode)?;
    let d = decode(&rc.bytecode, pc);
    if d.total_len == 0 {
        return None;
    }
    let after = pc + d.total_len;
    let read_at = after + byte_off + idx * 8;
    if read_at + 8 > rc.full_body.len() {
        return None;
    }
    Some(u64::from_le_bytes(rc.full_body[read_at..read_at + 8].try_into().ok()?) as i64)
}

/// Decode CALL_CONST_ADDR immediate operands -> (byte_off, const_idx).
/// Mirrors `translate::read_const_addr_operands`. `pc` points at the
/// opcode.
fn cca_operands(bc: &[u8], pc: usize, opcode: u8) -> Option<(usize, usize)> {
    let at = |i: usize| bc.get(i).copied();
    match opcode {
        op::INSTR_CALL_CONST_ADDR8_0 => Some((at(pc + 1)? as usize, 3)),
        op::INSTR_CALL_CONST_ADDR8_1 => Some((at(pc + 1)? as usize, 4)),
        op::INSTR_CALL_CONST_ADDR8_8 => Some((at(pc + 1)? as usize, at(pc + 2)? as usize + 3)),
        op::INSTR_CALL_CONST_ADDR16_8 => {
            let off = u16::from_le_bytes([at(pc + 1)?, at(pc + 2)?]) as usize;
            Some((off, at(pc + 3)? as usize + 3))
        }
        _ => None,
    }
}

fn is_cca(b: u8) -> bool {
    b == op::INSTR_CALL_CONST_ADDR8_0
        || b == op::INSTR_CALL_CONST_ADDR8_1
        || b == op::INSTR_CALL_CONST_ADDR8_8
        || b == op::INSTR_CALL_CONST_ADDR16_8
}

/// Decode CONST_ADDR* immediate operands -> (byte_off, const_idx). Mirrors
/// the interpreter's `read_pc_const(byte_off, idx)` argument selection
/// (mod.rs:4195-4216): CONST_ADDR8_0 -> idx 3, CONST_ADDR8_1 -> idx 4,
/// CONST_ADDR8_8 / CONST_ADDR16_8 -> idx = imm2 + 3. `pc` points at the
/// opcode. The const word's absolute body byte offset is then
/// `(pc + total_len) + byte_off + idx*8` (the same read_at formula
/// `cca_target_code_addr` uses, since the const pool follows the bytecode
/// in the same frozen object).
fn const_addr_operands(bc: &[u8], pc: usize, opcode: u8) -> Option<(usize, usize)> {
    let at = |i: usize| bc.get(i).copied();
    match opcode {
        op::INSTR_CONST_ADDR8_0 => Some((at(pc + 1)? as usize, 3)),
        op::INSTR_CONST_ADDR8_1 => Some((at(pc + 1)? as usize, 4)),
        op::INSTR_CONST_ADDR8_8 => Some((at(pc + 1)? as usize, at(pc + 2)? as usize + 3)),
        op::INSTR_CONST_ADDR16_8 => {
            let off = u16::from_le_bytes([at(pc + 1)?, at(pc + 2)?]) as usize;
            Some((off, at(pc + 3)? as usize + 3))
        }
        _ => None,
    }
}

/// Read the raw const-pool word a CONST_ADDR* pushes, at compile time
/// (the heap is frozen). Returns the exact bits the interpreter would
/// push via `read_pc_const`. The read lands in the resolved object's
/// constant pool (after the bytecode), so it is bounded by `full_body`.
fn const_addr_word_bits(rc: &ResolvedCode, pc: usize, opcode: u8) -> Option<i64> {
    let (byte_off, idx) = const_addr_operands(&rc.bytecode, pc, opcode)?;
    let d = decode(&rc.bytecode, pc);
    if d.total_len == 0 {
        return None;
    }
    let after = pc + d.total_len;
    let read_at = after + byte_off + idx * 8;
    if read_at + 8 > rc.full_body.len() {
        return None;
    }
    Some(u64::from_le_bytes(rc.full_body[read_at..read_at + 8].try_into().ok()?) as i64)
}

// ---------------------------------------------------------------------
// REGION FIXPOINT -- root + static CALL_CONST_ADDR callees, recursed to a
// fixpoint, all compiled into ONE JITModule.
// ---------------------------------------------------------------------

/// Maximum number of distinct code objects in a single region (the
/// static-callee closure budget). Keeps a pathological call graph from
/// blowing up compile time; over budget -> clean bail.
const MAX_REGION_FUNCS: usize = 256;

/// A whole region compiled into the host module: the root + every
/// statically-reachable CALL_CONST_ADDR callee, keyed by code-object
/// address.
pub struct CompiledMemRegion {
    /// Code-object address of the root.
    pub root_addr: u64,
    /// The root's FuncId in the module.
    pub root: FuncId,
    /// The root's SML arity.
    pub root_arity: usize,
    /// All compiled functions: code-obj address -> (FuncId, arity).
    pub funcs: HashMap<u64, (FuncId, usize)>,
    /// True if the static CALL_CONST_ADDR call graph contains a cycle
    /// (self- or mutual recursion). Such a region grows the shared
    /// downward stack per native-recursion level. The convention handles
    /// it (see the `sumto` test), but until `STACK_SIZE16` is lowered to a
    /// real stack-limit check (today it is a no-op — S4), a recursive
    /// region must NOT be registered for live dispatch: unbounded growth
    /// would write past the stack Box with no `StackOverflow` raise.
    pub recursive: bool,
    /// True if any function in the region carries an `INSTR_STACK_SIZE16`
    /// prologue. Now lowered FAITHFULLY (a real `sp < needed` check that
    /// raises `StackOverflow`, S4b), so such a region is safe to register —
    /// the flag is retained for diagnostics.
    pub uses_stack_size: bool,
    /// True if any function in the region contains a DYNAMIC call
    /// (`CALL_LOCAL_B` / `CALL_CLOSURE`). The trampoline that re-enters the
    /// interpreter for the callee is sound + measured (S4e de-risk: 3.3x) and
    /// `region_interp_call` now propagates a REAL callee exception faithfully
    /// (S4-proper, commit 27f8cd9 — fenced by
    /// `wired_dyncall_real_raise_propagates_byte_identical`), so dynamic-call
    /// regions ARE registered for live dispatch. The flag is retained for
    /// diagnostics (and `recursive` is still refused — see the guard).
    pub has_dynamic_call: bool,
}

/// Build the region fixpoint from a root code-object address. Scans the
/// root for CALL_CONST_ADDR targets, resolves each, recurses, and
/// compiles the whole reachable static subgraph into `jit`'s module.
/// Returns the compiled region (NOT yet finalized) or a bail reason.
///
/// # Safety
/// `root_addr` is a live code-object body pointer; the heap is frozen.
pub unsafe fn build_region(jit: &mut Jit, root_addr: u64) -> Result<CompiledMemRegion, BailReason> {
    // 1. Discover the full static call graph (root + transitive
    //    CALL_CONST_ADDR callees), resolving + pre-flighting each.
    let mut resolved: BTreeMap<u64, ResolvedCode> = BTreeMap::new();
    let mut worklist = vec![root_addr];
    // Call-graph edges (caller -> callee) + the stack-size flag, used after
    // discovery to compute the live-dispatch safety facts (recursion /
    // STACK_SIZE16) without bailing — see `CompiledMemRegion`.
    let mut edges: Vec<(u64, u64)> = Vec::new();
    let mut uses_stack_size = false;
    let mut has_dynamic_call = false;
    while let Some(addr) = worklist.pop() {
        if resolved.contains_key(&addr) {
            continue;
        }
        if resolved.len() >= MAX_REGION_FUNCS {
            return Err(BailReason::RegionTooLarge);
        }
        // SAFETY: compile-time, frozen heap.
        let rc = unsafe { resolve_code(addr) }.ok_or(BailReason::UnresolvableCallee(0))?;
        // Pre-flight: verify the whole bytecode is in the core subset AND
        // collect CCA callees. If any opcode is unsupported, bail the
        // WHOLE region now (before declaring anything).
        let mut pc = 0usize;
        while pc < rc.bytecode.len() {
            let b = rc.bytecode[pc];
            let d = decode(&rc.bytecode, pc);
            if d.total_len == 0 {
                return Err(BailReason::Truncated(pc));
            }
            if !is_supported(b) {
                return Err(BailReason::UnsupportedOpcode {
                    op: b,
                    name: polyml_runtime::interpreter::disasm::opcode_name(b),
                    at: pc,
                });
            }
            if b == op::INSTR_STACK_SIZE16 {
                uses_stack_size = true;
            }
            if b == op::INSTR_CALL_LOCAL_B || b == op::INSTR_CALL_CLOSURE {
                has_dynamic_call = true;
            }
            if is_cca(b) {
                // SAFETY: compile-time.
                let callee = unsafe { cca_target_code_addr(&rc, pc, b) }
                    .ok_or(BailReason::UnresolvableCallee(pc))?;
                edges.push((addr, callee));
                worklist.push(callee);
            }
            pc += d.total_len;
        }
        resolved.insert(addr, rc);
    }

    // Detect a cycle in the CALL_CONST_ADDR call graph (self- or mutual
    // recursion) via Kahn's algorithm: a graph is acyclic iff a topological
    // order covers every node. Nodes are the resolved code-object addresses.
    let recursive = call_graph_has_cycle(&resolved, &edges);

    // 2. Declare every function (so CCA forward references resolve).
    let mut ids: HashMap<u64, (FuncId, usize)> = HashMap::new();
    let sig = region_sig(jit);
    for (addr, rc) in &resolved {
        let name = format!("memregion_{addr:016x}");
        let id = jit
            .module
            .declare_function(&name, Linkage::Local, &sig)
            .map_err(|e| BailReason::ModuleError(e.to_string()))?;
        ids.insert(*addr, (id, rc.arity));
    }

    // 3. Define every function.
    for (addr, rc) in &resolved {
        let (id, _) = ids[addr];
        // SAFETY: compile-time.
        unsafe { define_function(jit, id, rc, &ids, *addr == root_addr)? };
    }

    let (root, root_arity) = ids[&root_addr];
    Ok(CompiledMemRegion {
        root_addr,
        root,
        root_arity,
        funcs: ids,
        recursive,
        uses_stack_size,
        has_dynamic_call,
    })
}

/// True iff the directed call graph (nodes = `resolved` keys, edges =
/// caller->callee) contains a cycle. Kahn's algorithm: repeatedly remove a
/// node with in-degree 0; if any node remains, there is a cycle. Self-edges
/// (a function calling itself) make that node never reach in-degree 0, so
/// they are caught too.
fn call_graph_has_cycle(resolved: &BTreeMap<u64, ResolvedCode>, edges: &[(u64, u64)]) -> bool {
    let mut indeg: HashMap<u64, usize> = resolved.keys().map(|&a| (a, 0usize)).collect();
    for &(_from, to) in edges {
        if let Some(d) = indeg.get_mut(&to) {
            *d += 1;
        }
    }
    let mut queue: Vec<u64> = indeg
        .iter()
        .filter(|&(_, &d)| d == 0)
        .map(|(&a, _)| a)
        .collect();
    let mut removed = 0usize;
    while let Some(n) = queue.pop() {
        removed += 1;
        for &(from, to) in edges {
            if from == n {
                if let Some(d) = indeg.get_mut(&to) {
                    *d -= 1;
                    if *d == 0 {
                        queue.push(to);
                    }
                }
            }
        }
    }
    removed != resolved.len()
}

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

/// Is `op` in the core opcode subset this translator can lower?
fn is_supported(b: u8) -> bool {
    use op::*;
    matches!(
        b,
        // no-op / prologue
        INSTR_NO_OP | INSTR_STACK_SIZE16
        // constants
        | INSTR_CONST_0 | INSTR_CONST_1 | INSTR_CONST_2 | INSTR_CONST_3
        | INSTR_CONST_4 | INSTR_CONST_10 | INSTR_CONST_INT_B | INSTR_CONST_INT_W
        // locals
        | INSTR_LOCAL_0 | INSTR_LOCAL_1 | INSTR_LOCAL_2 | INSTR_LOCAL_3
        | INSTR_LOCAL_4 | INSTR_LOCAL_5 | INSTR_LOCAL_6 | INSTR_LOCAL_7
        | INSTR_LOCAL_8 | INSTR_LOCAL_9 | INSTR_LOCAL_10 | INSTR_LOCAL_11
        | INSTR_LOCAL_12 | INSTR_LOCAL_13 | INSTR_LOCAL_14 | INSTR_LOCAL_15
        | INSTR_LOCAL_B | INSTR_LOCAL_W
        // indirect (heap field read)
        | INSTR_INDIRECT_0 | INSTR_INDIRECT_1 | INSTR_INDIRECT_2 | INSTR_INDIRECT_3
        | INSTR_INDIRECT_4 | INSTR_INDIRECT_5 | INSTR_INDIRECT_B
        | INSTR_INDIRECT_LOCAL_B0 | INSTR_INDIRECT_LOCAL_B1 | INSTR_INDIRECT_0_LOCAL_0
        | INSTR_INDIRECT_LOCAL_BB
        // stack manipulation
        | INSTR_RESET_1 | INSTR_RESET_2 | INSTR_RESET_B
        | INSTR_RESET_R_1 | INSTR_RESET_R_2 | INSTR_RESET_R_3 | INSTR_RESET_R_B
        // jumps
        | INSTR_JUMP8 | INSTR_JUMP16 | INSTR_JUMP_BACK8 | INSTR_JUMP_BACK16
        | INSTR_JUMP8_FALSE | INSTR_JUMP16_FALSE | INSTR_JUMP8_TRUE | INSTR_JUMP16_TRUE
        // fused compare-jump family (3-immediate: depth, want, off) + 2-imm tagged
        | INSTR_JUMP_NEQ_LOCAL | INSTR_JUMP_NEQ_LOCAL_IND | INSTR_JUMP_TAGGED_LOCAL
        // stack-slot store + tag-test-local
        | INSTR_SET_STACK_VAL_B | INSTR_IS_TAGGED_LOCAL_B
        // heap load/store (pure-leaf field access against a base on the stack)
        | INSTR_LOAD_ML_WORD | INSTR_LOAD_ML_BYTE | INSTR_LOAD_UNTAGGED
        | INSTR_STORE_ML_WORD | INSTR_STORE_UNTAGGED
        // cell introspection
        | INSTR_CELL_LENGTH | INSTR_CELL_FLAGS
        // PC-relative constant push (resolved at compile time, heap frozen)
        | INSTR_CONST_ADDR8_0 | INSTR_CONST_ADDR8_1
        | INSTR_CONST_ADDR8_8 | INSTR_CONST_ADDR16_8
        // fixed (tagged) arithmetic
        | INSTR_FIXED_ADD | INSTR_FIXED_SUB | INSTR_FIXED_MULT
        | INSTR_FIXED_QUOT | INSTR_FIXED_REM
        // word arithmetic
        | INSTR_WORD_ADD | INSTR_WORD_SUB | INSTR_WORD_MULT
        | INSTR_WORD_AND | INSTR_WORD_OR | INSTR_WORD_XOR
        | INSTR_WORD_SHIFT_LEFT | INSTR_WORD_SHIFT_R_LOG
        | INSTR_WORD_DIV | INSTR_WORD_MOD
        // comparisons
        | INSTR_EQUAL_WORD | INSTR_LESS_SIGNED | INSTR_LESS_UNSIGNED
        | INSTR_LESS_EQ_SIGNED | INSTR_LESS_EQ_UNSIGNED
        | INSTR_GREATER_SIGNED | INSTR_GREATER_UNSIGNED
        | INSTR_GREATER_EQ_SIGNED | INSTR_GREATER_EQ_UNSIGNED
        // boolean / tag
        | INSTR_NOT_BOOLEAN | INSTR_IS_TAGGED
        // returns
        | INSTR_RETURN_1 | INSTR_RETURN_2 | INSTR_RETURN_3 | INSTR_RETURN_B | INSTR_RETURN_W
        // statically-resolved native call
        | INSTR_CALL_CONST_ADDR8_0 | INSTR_CALL_CONST_ADDR8_1
        | INSTR_CALL_CONST_ADDR8_8 | INSTR_CALL_CONST_ADDR16_8
        // DYNAMIC call (trampolines into the interpreter's do_call)
        | INSTR_CALL_LOCAL_B | INSTR_CALL_CLOSURE
        // S4d — allocation opcodes (heap alloc via the GC-safe trampoline,
        // EXCEPT STACK_CONTAINER_B which is a pure stack push, no heap alloc)
        | INSTR_STACK_CONTAINER_B
        | INSTR_TUPLE_2 | INSTR_TUPLE_3 | INSTR_TUPLE_4 | INSTR_TUPLE_B
        | INSTR_CLOSURE_B
        | INSTR_ALLOC_REF | INSTR_ALLOC_WORD_MEMORY | INSTR_ALLOC_BYTE_MEM
    )
}

/// Is `b` an opcode that performs a HEAP allocation (and therefore must
/// route through the GC-safe `region_alloc` trampoline)? STACK_CONTAINER_B
/// is NOT here — it only pushes zero slots + a stack-relative container
/// pointer onto the shared stack, no heap object is allocated.
fn is_heap_alloc_opcode(b: u8) -> bool {
    use op::*;
    matches!(
        b,
        INSTR_TUPLE_2
            | INSTR_TUPLE_3
            | INSTR_TUPLE_4
            | INSTR_TUPLE_B
            | INSTR_CLOSURE_B
            | INSTR_ALLOC_REF
            | INSTR_ALLOC_WORD_MEMORY
            | INSTR_ALLOC_BYTE_MEM
    )
}

// ---------------------------------------------------------------------
// IR primitives -- DOWNWARD shared stack (mirror mod.rs push/pop/peek).
// ---------------------------------------------------------------------

fn addr_at(b: &mut FunctionBuilder, base: Value, idx: Value) -> Value {
    let eight = b.ins().iconst(types::I64, 8);
    let off = b.ins().imul(idx, eight);
    b.ins().iadd(base, off)
}
fn load_at(b: &mut FunctionBuilder, base: Value, idx: Value) -> Value {
    let a = addr_at(b, base, idx);
    b.ins().load(types::I64, MemFlags::trusted(), a, 0)
}
fn store_at(b: &mut FunctionBuilder, base: Value, idx: Value, v: Value) {
    let a = addr_at(b, base, idx);
    b.ins().store(MemFlags::trusted(), v, a, 0);
}
/// PUSH v: sp -= 1; stack[sp] = v. Returns new sp.
fn emit_push(b: &mut FunctionBuilder, base: Value, sp: Value, v: Value) -> Value {
    let new_sp = b.ins().iadd_imm(sp, -1);
    store_at(b, base, new_sp, v);
    new_sp
}
/// peek depth K: stack[sp+K].
fn emit_peek(b: &mut FunctionBuilder, base: Value, sp: Value, k: i64) -> Value {
    let kk = b.ins().iconst(types::I64, k);
    let idx = b.ins().iadd(sp, kk);
    load_at(b, base, idx)
}
/// untag: (t-1) >> 1 (arithmetic).
fn emit_untag(b: &mut FunctionBuilder, t: Value) -> Value {
    let m1 = b.ins().iadd_imm(t, -1);
    b.ins().sshr_imm(m1, 1)
}
/// tag: 2n+1.
fn emit_tag(b: &mut FunctionBuilder, n: Value) -> Value {
    let m = b.ins().ishl_imm(n, 1);
    b.ins().iadd_imm(m, 1)
}
/// PolyWord::tagged(n) constant.
fn tagged(b: &mut FunctionBuilder, n: i64) -> Value {
    b.ins()
        .iconst(types::I64, n.wrapping_mul(2).wrapping_add(1))
}

// ctx field accessors (handler_sp @ 0, exn_packet @ 8, interp_ptr @ 16,
// live_sp @ 24, gc_used_ptr @ 32, gc_trigger @ 40 — see ExnCtx).
fn load_handler_sp(b: &mut FunctionBuilder, ctx: Value) -> Value {
    b.ins().load(types::I64, MemFlags::trusted(), ctx, 0)
}
fn store_exn_packet(b: &mut FunctionBuilder, ctx: Value, v: Value) {
    b.ins().store(MemFlags::trusted(), v, ctx, 8);
}
/// Store the region's current SSA `sp` into `ctx.live_sp` (offset 24)
/// before a safepoint slow-path call, so `region_safepoint` can publish
/// it as `interp.sp` for the GC root walk.
fn store_live_sp(b: &mut FunctionBuilder, ctx: Value, sp: Value) {
    b.ins().store(MemFlags::trusted(), sp, ctx, 24);
}
/// Load `ctx.gc_used_ptr` (offset 32) — the address of the live heap
/// words-allocated counter.
fn load_gc_used_ptr(b: &mut FunctionBuilder, ctx: Value) -> Value {
    b.ins().load(types::I64, MemFlags::trusted(), ctx, 32)
}
/// Load `ctx.gc_trigger` (offset 40) — the GC trigger word count.
fn load_gc_trigger(b: &mut FunctionBuilder, ctx: Value) -> Value {
    b.ins().load(types::I64, MemFlags::trusted(), ctx, 40)
}

// Tagged-int bounds for FixedInt overflow (mirror poly_word::MIN/MAX_TAGGED
// on 64-bit: 62-bit signed payload range, [-2^62, 2^62-1]).
const MIN_TAGGED: i64 = -(1 << 62);
const MAX_TAGGED: i64 = (1 << 62) - 1;

/// The Overflow / DivByZero exception sentinels the region returns in
/// `ctx.exn_packet`. The boundary maps these onto the interpreter's real
/// `raise_overflow` / `DivByZero` path so the packet + handler_sp are
/// byte-exact. They are NOT tagged ints (so they cannot collide with a
/// real result value).
pub const EXN_OVERFLOW: i64 = 0x0001_0000_0000_0002; // even (untagged sentinel)
pub const EXN_DIVZERO: i64 = 0x0002_0000_0000_0002;
/// StackOverflow sentinel — the faithful `STACK_SIZE16` lowering returns
/// it when `sp < needed`, mirroring the interpreter's hard
/// `InterpError::StackOverflow` at mod.rs:3457. MUST equal
/// `polyml_runtime::REGION_EXN_STACKOVERFLOW`.
pub const EXN_STACKOVERFLOW: i64 = 0x0003_0000_0000_0002;

// =====================================================================
// FUNCTION DEFINITION -- lower one resolved code object's bytecode.
// =====================================================================

/// Per-function translation state for the memory-backed lowering.
struct FnState<'a> {
    rc: &'a ResolvedCode,
    /// byte-offset -> Cranelift block (created for every jump target +
    /// the entry). Each block has ONE param: the live `sp`.
    blocks: BTreeMap<usize, Block>,
    /// FuncRefs for callees referenced in this function (declared up front).
    callee_refs: HashMap<u64, cranelift::codegen::ir::FuncRef>,
    /// FuncRef for the dynamic-call trampoline
    /// (`polyml_jit_region_interp_call`), declared lazily when a
    /// CALL_LOCAL_B / CALL_CLOSURE is lowered. None until then.
    interp_call_ref: Option<cranelift::codegen::ir::FuncRef>,
    /// FuncRef for the GC-safepoint slow path
    /// (`polyml_jit_region_safepoint`), declared up front iff this
    /// function contains a JUMP_BACK back-edge. None when the function has
    /// no back-edge (a straight-line / forward-only function never polls).
    safepoint_ref: Option<cranelift::codegen::ir::FuncRef>,
    /// FuncRef for the GC-SAFE ALLOC trampoline
    /// (`polyml_jit_region_alloc`), declared up front iff this function
    /// contains an allocation opcode (TUPLE / CLOSURE / ALLOC_*). None
    /// otherwise. Signature: `(ctx, n_words, flags) -> body_ptr`.
    alloc_ref: Option<cranelift::codegen::ir::FuncRef>,
}

/// Define one region function: lower its bytecode against the shared
/// stack. `is_root` adds the nativeness-tick bump at entry.
///
/// # Safety
/// `rc` describes a live code object; compile-time only.
unsafe fn define_function(
    jit: &mut Jit,
    id: FuncId,
    rc: &ResolvedCode,
    ids: &HashMap<u64, (FuncId, usize)>,
    is_root: bool,
) -> Result<(), BailReason> {
    let sig = region_sig(jit);
    let mut ctx = jit.module.make_context();
    ctx.func.signature = sig;
    ctx.func.name = UserFuncName::user(0, id.as_u32());

    // Pre-declare callee FuncRefs + the tick trampoline in this function.
    let mut callee_refs: HashMap<u64, cranelift::codegen::ir::FuncRef> = HashMap::new();
    {
        let mut pc = 0usize;
        while pc < rc.bytecode.len() {
            let b = rc.bytecode[pc];
            let d = decode(&rc.bytecode, pc);
            if d.total_len == 0 {
                return Err(BailReason::Truncated(pc));
            }
            if is_cca(b) {
                // SAFETY: compile-time.
                let callee = unsafe { cca_target_code_addr(rc, pc, b) }
                    .ok_or(BailReason::UnresolvableCallee(pc))?;
                let (cid, _) = ids[&callee];
                callee_refs
                    .entry(callee)
                    .or_insert_with(|| jit.module.declare_func_in_func(cid, &mut ctx.func));
            }
            pc += d.total_len;
        }
    }
    let tick_ref = if is_root {
        let tsig = jit.module.make_signature();
        let tid = jit
            .module
            .declare_function("polyml_jit_region_native_tick", Linkage::Import, &tsig)
            .map_err(|e| BailReason::ModuleError(e.to_string()))?;
        Some(jit.module.declare_func_in_func(tid, &mut ctx.func))
    } else {
        None
    };

    // Pre-declare the dynamic-call trampoline iff this function makes a
    // dynamic call (CALL_LOCAL_B / CALL_CLOSURE). Signature:
    //   (interp_ptr, stack_base, sp, closure, ctx) -> (new_sp, raised)
    let interp_call_ref = {
        let mut has_dyn = false;
        let mut pc = 0usize;
        while pc < rc.bytecode.len() {
            let b = rc.bytecode[pc];
            let d = decode(&rc.bytecode, pc);
            if d.total_len == 0 {
                return Err(BailReason::Truncated(pc));
            }
            if b == op::INSTR_CALL_LOCAL_B || b == op::INSTR_CALL_CLOSURE {
                has_dyn = true;
                break;
            }
            pc += d.total_len;
        }
        if has_dyn {
            let mut tsig = jit.module.make_signature();
            tsig.params.push(AbiParam::new(types::I64)); // interp_ptr
            tsig.params.push(AbiParam::new(types::I64)); // stack_base
            tsig.params.push(AbiParam::new(types::I64)); // sp_at_top_arg
            tsig.params.push(AbiParam::new(types::I64)); // closure_bits
            tsig.params.push(AbiParam::new(types::I64)); // ctx ptr
            tsig.returns.push(AbiParam::new(types::I64)); // new_sp
            tsig.returns.push(AbiParam::new(types::I64)); // raised
            let tid = jit
                .module
                .declare_function("polyml_jit_region_interp_call", Linkage::Import, &tsig)
                .map_err(|e| BailReason::ModuleError(e.to_string()))?;
            Some(jit.module.declare_func_in_func(tid, &mut ctx.func))
        } else {
            None
        }
    };

    // Pre-declare the GC-safepoint slow path iff this function contains a
    // JUMP_BACK back-edge (a loop). A function with no back-edge can never
    // loop, so it never needs a safepoint poll (its bounded straight-line
    // /forward work allocates nothing in the core subset). Signature:
    //   (ctx) -> ()
    let safepoint_ref = {
        let mut has_back_edge = false;
        let mut pc = 0usize;
        while pc < rc.bytecode.len() {
            let b = rc.bytecode[pc];
            let d = decode(&rc.bytecode, pc);
            if d.total_len == 0 {
                return Err(BailReason::Truncated(pc));
            }
            if b == op::INSTR_JUMP_BACK8 || b == op::INSTR_JUMP_BACK16 {
                has_back_edge = true;
                break;
            }
            pc += d.total_len;
        }
        if has_back_edge {
            let mut tsig = jit.module.make_signature();
            tsig.params.push(AbiParam::new(types::I64)); // ctx ptr
            // no returns
            let tid = jit
                .module
                .declare_function("polyml_jit_region_safepoint", Linkage::Import, &tsig)
                .map_err(|e| BailReason::ModuleError(e.to_string()))?;
            Some(jit.module.declare_func_in_func(tid, &mut ctx.func))
        } else {
            None
        }
    };

    // Pre-declare the GC-SAFE ALLOC trampoline iff this function contains a
    // HEAP allocation opcode (TUPLE / CLOSURE / ALLOC_*). STACK_CONTAINER_B
    // is a pure stack push (no heap alloc) so it does NOT require this.
    // Signature: (ctx, n_words, flags) -> body_ptr.
    let alloc_ref = {
        let mut has_alloc = false;
        let mut pc = 0usize;
        while pc < rc.bytecode.len() {
            let b = rc.bytecode[pc];
            let d = decode(&rc.bytecode, pc);
            if d.total_len == 0 {
                return Err(BailReason::Truncated(pc));
            }
            if is_heap_alloc_opcode(b) {
                has_alloc = true;
                break;
            }
            pc += d.total_len;
        }
        if has_alloc {
            let mut tsig = jit.module.make_signature();
            tsig.params.push(AbiParam::new(types::I64)); // ctx ptr
            tsig.params.push(AbiParam::new(types::I64)); // n_words
            tsig.params.push(AbiParam::new(types::I64)); // flags
            tsig.returns.push(AbiParam::new(types::I64)); // body ptr (bits)
            let tid = jit
                .module
                .declare_function("polyml_jit_region_alloc", Linkage::Import, &tsig)
                .map_err(|e| BailReason::ModuleError(e.to_string()))?;
            Some(jit.module.declare_func_in_func(tid, &mut ctx.func))
        } else {
            None
        }
    };

    // Compute all block boundaries (jump targets) up front.
    let blocks_offsets = compute_block_offsets(rc)?;

    let mut fbctx = FunctionBuilderContext::new();
    {
        let mut bldr = FunctionBuilder::new(&mut ctx.func, &mut fbctx);

        // Entry block carries the function's (base, sp, ctx) params.
        let entry = bldr.create_block();
        bldr.append_block_params_for_function_params(entry);

        // Create a block per jump target (offset != 0); each takes one
        // param (sp). base/ctx are defined in `entry`, which dominates
        // every reachable block, so they are SSA-visible everywhere.
        let mut blocks: BTreeMap<usize, Block> = BTreeMap::new();
        for &off in &blocks_offsets {
            if off == 0 || off >= rc.bytecode.len() {
                continue;
            }
            let blk = bldr.create_block();
            bldr.append_block_param(blk, types::I64); // sp
            blocks.insert(off, blk);
        }

        let base = bldr.block_params(entry)[0];
        let sp0 = bldr.block_params(entry)[1];
        let cctx = bldr.block_params(entry)[2];

        bldr.switch_to_block(entry);
        if let Some(t) = tick_ref {
            bldr.ins().call(t, &[]);
        }

        let mut st = FnState {
            rc,
            blocks,
            callee_refs,
            interp_call_ref,
            safepoint_ref,
            alloc_ref,
        };

        emit_all_blocks(&mut bldr, &mut st, base, sp0, cctx, entry)?;

        bldr.seal_all_blocks();
        bldr.finalize();
    }

    jit.module
        .define_function(id, &mut ctx)
        .map_err(|e| BailReason::ModuleError(e.to_string()))?;
    jit.module.clear_context(&mut ctx);
    Ok(())
}

/// Compute the set of byte offsets that must start a Cranelift block:
/// every jump target (forward + backward) plus the fallthrough after
/// each conditional/unconditional jump. Targets are validated to be real
/// instruction boundaries.
fn compute_block_offsets(rc: &ResolvedCode) -> Result<BTreeSet<usize>, BailReason> {
    let bc = &rc.bytecode;
    // First pass: record all instruction-boundary offsets.
    let mut boundaries: BTreeSet<usize> = BTreeSet::new();
    let mut pc = 0usize;
    while pc < bc.len() {
        boundaries.insert(pc);
        let d = decode(bc, pc);
        if d.total_len == 0 {
            return Err(BailReason::Truncated(pc));
        }
        pc += d.total_len;
    }
    boundaries.insert(bc.len()); // end sentinel

    // Second pass: collect jump targets + fallthroughs.
    let mut targets: BTreeSet<usize> = BTreeSet::new();
    targets.insert(0);
    let mut pc = 0usize;
    while pc < bc.len() {
        let b = bc[pc];
        let d = decode(bc, pc);
        let total = d.total_len;
        if let Some(t) = jump_target(bc, pc, b, total) {
            if !boundaries.contains(&t) {
                return Err(BailReason::JumpMidInstruction(t));
            }
            targets.insert(t);
            // Both conditional and unconditional jumps make the following
            // offset a block start (the cond's fallthrough; the uncond's
            // following offset is only reachable via a jump but still
            // needs a block to switch to).
            let next = pc + total;
            if boundaries.contains(&next) && next < bc.len() {
                targets.insert(next);
            }
        }
        pc += total;
    }
    Ok(targets)
}

/// The byte-offset destination of a jump opcode at `pc` (with decoded
/// length `total`), or None if `op` is not a jump. Mirrors the
/// interpreter's exact PC arithmetic (mod.rs JUMP handlers).
fn jump_target(bc: &[u8], pc: usize, b: u8, total: usize) -> Option<usize> {
    use op::*;
    let after = pc + total; // pc after fetching the opcode + immediates
    match b {
        INSTR_JUMP8 | INSTR_JUMP8_FALSE | INSTR_JUMP8_TRUE => {
            let off = *bc.get(pc + 1)? as usize;
            Some(after + off)
        }
        INSTR_JUMP16 | INSTR_JUMP16_FALSE | INSTR_JUMP16_TRUE => {
            let off = u16::from_le_bytes([*bc.get(pc + 1)?, *bc.get(pc + 2)?]) as usize;
            Some(after + off)
        }
        INSTR_JUMP_BACK8 => {
            // interp: pc at ic+2, then pc -= off+2 -> ic - off.
            let off = *bc.get(pc + 1)? as usize;
            pc.checked_sub(off)
        }
        INSTR_JUMP_BACK16 => {
            let off = u16::from_le_bytes([*bc.get(pc + 1)?, *bc.get(pc + 2)?]) as usize;
            pc.checked_sub(off)
        }
        // Fused compare-jump (3 immediates: depth, want, off). The interp
        // (mod.rs:4097-4123) fetches depth+want+off then, on mismatch,
        // `pc_offset_signed(off)`. After fetching all immediates pc == after
        // (= pc + total, total = 4), so the taken branch lands at after+off.
        // `off` is the THIRD immediate byte (bc[pc+3]).
        INSTR_JUMP_NEQ_LOCAL | INSTR_JUMP_NEQ_LOCAL_IND => {
            let off = *bc.get(pc + 3)? as usize;
            Some(after + off)
        }
        // JUMP_TAGGED_LOCAL (2 immediates: depth, off). On the tagged-test
        // taken branch (mod.rs:4126-4133) it `pc_offset_signed(off)`; off is
        // the SECOND immediate byte (bc[pc+2]); target = after + off.
        INSTR_JUMP_TAGGED_LOCAL => {
            let off = *bc.get(pc + 2)? as usize;
            Some(after + off)
        }
        _ => None,
    }
}

/// Emit IR for the whole function: walk the bytecode once, switching to
/// the appropriate block at each block boundary and threading `sp`.
fn emit_all_blocks(
    bldr: &mut FunctionBuilder,
    st: &mut FnState,
    base: Value,
    sp0: Value,
    cctx: Value,
    entry: Block,
) -> Result<(), BailReason> {
    let bc = st.rc.bytecode.clone();
    let mut sp = sp0;
    // Whether the current block has been terminated (by a return / jump).
    let mut terminated = false;

    let mut pc = 0usize;
    while pc < bc.len() {
        // If this pc starts a new block, close the current block
        // (fallthrough) and switch to the new one.
        if pc != 0 {
            if let Some(&blk) = st.blocks.get(&pc) {
                if !terminated {
                    bldr.ins().jump(blk, &[BlockArg::from(sp)]);
                }
                bldr.switch_to_block(blk);
                sp = bldr.block_params(blk)[0];
                terminated = false;
            } else if terminated {
                // Unreachable code after a terminator (e.g. NO_OP padding
                // after a RETURN) that is not itself a jump target. It can
                // never execute, so SKIP it -- emitting into a terminated
                // block would be invalid IR. We still advance pc by the
                // decoded length to stay on instruction boundaries.
                let d = decode(&bc, pc);
                if d.total_len == 0 {
                    return Err(BailReason::Truncated(pc));
                }
                pc += d.total_len;
                continue;
            }
        }

        let b = bc[pc];
        let d = decode(&bc, pc);
        let total = d.total_len;
        if total == 0 {
            return Err(BailReason::Truncated(pc));
        }

        sp = emit_one(bldr, st, base, sp, cctx, &bc, pc, b, total, &mut terminated)?;
        pc += total;
    }
    let _ = entry;
    Ok(())
}

/// Emit one opcode. Returns the updated `sp` SSA value. Sets
/// `*terminated` if the opcode ends the block (return / jump).
#[allow(clippy::too_many_arguments)]
fn emit_one(
    bldr: &mut FunctionBuilder,
    st: &mut FnState,
    base: Value,
    sp: Value,
    cctx: Value,
    bc: &[u8],
    pc: usize,
    b: u8,
    total: usize,
    terminated: &mut bool,
) -> Result<Value, BailReason> {
    use op::*;
    let after = pc + total;
    let imm1 = bc.get(pc + 1).copied().unwrap_or(0);
    let imm_u16 = u16::from_le_bytes([
        bc.get(pc + 1).copied().unwrap_or(0),
        bc.get(pc + 2).copied().unwrap_or(0),
    ]);

    let new_sp = match b {
        INSTR_NO_OP => sp,
        // FAITHFUL STACK_SIZE16 (S4b): mirror mod.rs:3457 — if sp < needed,
        // raise StackOverflow (a HARD error the boundary maps onto
        // InterpError::StackOverflow). `needed` is the u16 immediate. This
        // is what makes admitting recursive / stack-size regions SOUND: a
        // dynamic callee or self-recursion that would over-push the shared
        // stack now traps instead of writing past the Box.
        INSTR_STACK_SIZE16 => emit_stack_size_check(bldr, sp, cctx, imm_u16 as i64),

        // ---- constants ----
        INSTR_CONST_0 => push_tagged(bldr, base, sp, 0),
        INSTR_CONST_1 => push_tagged(bldr, base, sp, 1),
        INSTR_CONST_2 => push_tagged(bldr, base, sp, 2),
        INSTR_CONST_3 => push_tagged(bldr, base, sp, 3),
        INSTR_CONST_4 => push_tagged(bldr, base, sp, 4),
        INSTR_CONST_10 => push_tagged(bldr, base, sp, 10),
        // interp: CONST_INT_B uses isize::from(fetch_u8()) -> UNSIGNED byte.
        INSTR_CONST_INT_B => push_tagged(bldr, base, sp, imm1 as i64),
        INSTR_CONST_INT_W => push_tagged(bldr, base, sp, imm_u16 as i64),

        // ---- locals (peek depth + push) ----
        INSTR_LOCAL_0..=INSTR_LOCAL_11 => peek_push(bldr, base, sp, (b - INSTR_LOCAL_0) as i64),
        INSTR_LOCAL_12 => peek_push(bldr, base, sp, 12),
        INSTR_LOCAL_13 => peek_push(bldr, base, sp, 13),
        INSTR_LOCAL_14 => peek_push(bldr, base, sp, 14),
        INSTR_LOCAL_15 => peek_push(bldr, base, sp, 15),
        INSTR_LOCAL_B => peek_push(bldr, base, sp, imm1 as i64),
        INSTR_LOCAL_W => peek_push(bldr, base, sp, imm_u16 as i64),

        // ---- indirect (pop obj, load field, push) ----
        INSTR_INDIRECT_0 => indirect(bldr, base, sp, 0),
        INSTR_INDIRECT_1 => indirect(bldr, base, sp, 1),
        INSTR_INDIRECT_2 => indirect(bldr, base, sp, 2),
        INSTR_INDIRECT_3 => indirect(bldr, base, sp, 3),
        INSTR_INDIRECT_4 => indirect(bldr, base, sp, 4),
        INSTR_INDIRECT_5 => indirect(bldr, base, sp, 5),
        INSTR_INDIRECT_B => indirect(bldr, base, sp, imm1 as i64),

        // ---- fused indirect-local (peek obj, load field, push) ----
        INSTR_INDIRECT_LOCAL_B0 => indirect_local(bldr, base, sp, imm1 as i64, 0),
        INSTR_INDIRECT_LOCAL_B1 => indirect_local(bldr, base, sp, imm1 as i64, 1),
        INSTR_INDIRECT_0_LOCAL_0 => indirect_local(bldr, base, sp, 0, 0),
        INSTR_INDIRECT_LOCAL_BB => {
            let slot = bc.get(pc + 2).copied().unwrap_or(0) as i64;
            indirect_local(bldr, base, sp, imm1 as i64, slot)
        }

        // ---- stack manipulation ----
        INSTR_RESET_1 => bldr.ins().iadd_imm(sp, 1),
        INSTR_RESET_2 => bldr.ins().iadd_imm(sp, 2),
        INSTR_RESET_B => bldr.ins().iadd_imm(sp, imm1 as i64),
        INSTR_RESET_R_1 => reset_r(bldr, base, sp, 1),
        INSTR_RESET_R_2 => reset_r(bldr, base, sp, 2),
        INSTR_RESET_R_3 => reset_r(bldr, base, sp, 3),
        INSTR_RESET_R_B => reset_r(bldr, base, sp, imm1 as i64),

        // ---- forward / unconditional jumps (no safepoint) ----
        INSTR_JUMP8 | INSTR_JUMP16 => {
            let t = jump_target(bc, pc, b, total).ok_or(BailReason::Truncated(pc))?;
            let blk = *st.blocks.get(&t).ok_or(BailReason::JumpMidInstruction(t))?;
            bldr.ins().jump(blk, &[BlockArg::from(sp)]);
            *terminated = true;
            sp
        }
        // ---- BACK-EDGE jumps (the loop latch) — emit the GC-SAFEPOINT
        // POLL here (S4c). This is the ONE place a region can loop, so it
        // is the only place a long-running native region needs to give the
        // GC a chance to fire. The poll is an INLINE, predicted-not-taken
        // check (3 loads + 1 cmp + 1 branch, NO call on the no-GC fast
        // path); only when the alloc threshold is crossed does it take the
        // slow-path `region_safepoint` helper. See `emit_back_edge_jump`.
        INSTR_JUMP_BACK8 | INSTR_JUMP_BACK16 => {
            let t = jump_target(bc, pc, b, total).ok_or(BailReason::Truncated(pc))?;
            emit_back_edge_jump(bldr, st, cctx, t, sp)?;
            *terminated = true;
            sp
        }
        INSTR_JUMP8_FALSE | INSTR_JUMP16_FALSE => {
            cond_jump(
                bldr, st, base, sp, bc, pc, b, total, after, /*jump_if_zero=*/ true,
            )?;
            *terminated = true;
            sp
        }
        INSTR_JUMP8_TRUE | INSTR_JUMP16_TRUE => {
            cond_jump(
                bldr, st, base, sp, bc, pc, b, total, after, /*jump_if_zero=*/ false,
            )?;
            *terminated = true;
            sp
        }

        // ---- fused compare-jump family (peek + tag/compare + brif) ----
        // No stack effect; conditional branch to (after+off) else fallthrough.
        INSTR_JUMP_NEQ_LOCAL => {
            neq_local_jump(bldr, st, base, sp, bc, pc, after, /*indirect=*/ false)?;
            *terminated = true;
            sp
        }
        INSTR_JUMP_NEQ_LOCAL_IND => {
            neq_local_jump(bldr, st, base, sp, bc, pc, after, /*indirect=*/ true)?;
            *terminated = true;
            sp
        }
        INSTR_JUMP_TAGGED_LOCAL => {
            tagged_local_jump(bldr, st, base, sp, bc, pc, after)?;
            *terminated = true;
            sp
        }

        // ---- stack-slot store (mod.rs:4138) ----
        // idx=imm1; v=pop_top; new_sp=sp+1 (the pop); stack[new_sp+idx-1]=v.
        // The interp computes the target AFTER the pop (sp already advanced).
        INSTR_SET_STACK_VAL_B => {
            // Slots are 1-based; the interp computes `idx.checked_sub(1)` and
            // returns StackUnderflow on idx==0 (which the compiler never
            // emits — mod.rs:4138 trusts the bytecode). We share that trusted-
            // bytecode invariant: on the impossible idx==0 the store lands at
            // new_sp-1 (a stray in-bounds slot), never out of bounds.
            let v = load_at(bldr, base, sp); // top before pop
            let new_sp = bldr.ins().iadd_imm(sp, 1); // the pop
            // target = new_sp + (idx - 1)
            let target = bldr.ins().iadd_imm(new_sp, imm1 as i64 - 1);
            store_at(bldr, base, target, v);
            new_sp
        }

        // ---- tag-test local (mod.rs:4085): peek depth, push tagged((v&1)!=0).
        INSTR_IS_TAGGED_LOCAL_B => {
            let v = emit_peek(bldr, base, sp, imm1 as i64);
            let one_bit = bldr.ins().band_imm(v, 1);
            let zero = bldr.ins().iconst(types::I64, 0);
            let is_t = bldr.ins().icmp(IntCC::NotEqual, one_bit, zero);
            let t1 = tagged(bldr, 1);
            let t0 = tagged(bldr, 0);
            let r = bldr.ins().select(is_t, t1, t0);
            emit_push(bldr, base, sp, r)
        }

        // ---- heap load (mod.rs:3696-3779) ----
        // idx = untag(pop top); base = peek(0) (the new top after pop);
        // load base[idx]; replace the top with the loaded value. Net sp = sp.
        INSTR_LOAD_ML_WORD => load_ml(bldr, base, sp, LoadKind::Word),
        INSTR_LOAD_ML_BYTE => load_ml(bldr, base, sp, LoadKind::Byte),
        INSTR_LOAD_UNTAGGED => load_ml(bldr, base, sp, LoadKind::Untagged),

        // ---- heap store (mod.rs:3780-3887) ----
        // val=pop; idx=untag(pop); base=peek(0); base[idx]=val (raw for
        // STORE_UNTAGGED). Net: two pops + replace top with tagged(0)
        // (sp = sp+1 overall: 2 pops then 1 push, peek consumes 1).
        INSTR_STORE_ML_WORD => store_ml(bldr, base, sp, /*untagged=*/ false),
        INSTR_STORE_UNTAGGED => store_ml(bldr, base, sp, /*untagged=*/ true),

        // ---- cell introspection (mod.rs:3617-3634) ----
        // peek obj; load length-word at obj[-1]; decode length / flags; push
        // tagged. Replaces the top (peek + pop + push = sp unchanged).
        INSTR_CELL_LENGTH => cell_intro(bldr, base, sp, CellField::Length),
        INSTR_CELL_FLAGS => cell_intro(bldr, base, sp, CellField::Flags),

        // ---- PC-relative constant push (mod.rs:4195-4216) ----
        // The const-pool word is resolved at COMPILE time (heap frozen) and
        // emitted as an iconst, then pushed — byte-identical to the interp's
        // read_pc_const + push.
        INSTR_CONST_ADDR8_0 | INSTR_CONST_ADDR8_1 | INSTR_CONST_ADDR8_8 | INSTR_CONST_ADDR16_8 => {
            let bits = const_addr_word_bits(st.rc, pc, b).ok_or(BailReason::Truncated(pc))?;
            let w = bldr.ins().iconst(types::I64, bits);
            emit_push(bldr, base, sp, w)
        }

        // ---- fixed (tagged) arithmetic with Overflow / DivByZero ----
        INSTR_FIXED_ADD => fixed_arith(bldr, base, sp, cctx, FixedOp::Add),
        INSTR_FIXED_SUB => fixed_arith(bldr, base, sp, cctx, FixedOp::Sub),
        INSTR_FIXED_MULT => fixed_arith(bldr, base, sp, cctx, FixedOp::Mul),
        INSTR_FIXED_QUOT => fixed_divrem(bldr, base, sp, cctx, true),
        INSTR_FIXED_REM => fixed_divrem(bldr, base, sp, cctx, false),

        // ---- word arithmetic (tag-aware, mirror mod.rs bin_op_word) ----
        INSTR_WORD_ADD => word_bin(bldr, base, sp, WordOp::Add),
        INSTR_WORD_SUB => word_bin(bldr, base, sp, WordOp::Sub),
        INSTR_WORD_MULT => word_bin(bldr, base, sp, WordOp::Mul),
        INSTR_WORD_AND => word_bin(bldr, base, sp, WordOp::And),
        INSTR_WORD_OR => word_bin(bldr, base, sp, WordOp::Or),
        INSTR_WORD_XOR => word_bin(bldr, base, sp, WordOp::Xor),
        INSTR_WORD_SHIFT_LEFT => word_bin(bldr, base, sp, WordOp::Shl),
        INSTR_WORD_SHIFT_R_LOG => word_bin(bldr, base, sp, WordOp::ShrLog),
        INSTR_WORD_DIV => word_divmod(bldr, base, sp, cctx, true),
        INSTR_WORD_MOD => word_divmod(bldr, base, sp, cctx, false),

        // ---- comparisons ----
        INSTR_EQUAL_WORD => cmp(bldr, base, sp, IntCC::Equal),
        INSTR_LESS_SIGNED => cmp(bldr, base, sp, IntCC::SignedLessThan),
        INSTR_LESS_UNSIGNED => cmp(bldr, base, sp, IntCC::UnsignedLessThan),
        INSTR_LESS_EQ_SIGNED => cmp(bldr, base, sp, IntCC::SignedLessThanOrEqual),
        INSTR_LESS_EQ_UNSIGNED => cmp(bldr, base, sp, IntCC::UnsignedLessThanOrEqual),
        INSTR_GREATER_SIGNED => cmp(bldr, base, sp, IntCC::SignedGreaterThan),
        INSTR_GREATER_UNSIGNED => cmp(bldr, base, sp, IntCC::UnsignedGreaterThan),
        INSTR_GREATER_EQ_SIGNED => cmp(bldr, base, sp, IntCC::SignedGreaterThanOrEqual),
        INSTR_GREATER_EQ_UNSIGNED => cmp(bldr, base, sp, IntCC::UnsignedGreaterThanOrEqual),

        // ---- boolean / tag ----
        INSTR_NOT_BOOLEAN => {
            let v = load_at(bldr, base, sp);
            let zero = tagged(bldr, 0);
            let is_false = bldr.ins().icmp(IntCC::Equal, v, zero);
            let one = tagged(bldr, 1);
            let zt = tagged(bldr, 0);
            let r = bldr.ins().select(is_false, one, zt);
            store_at(bldr, base, sp, r);
            sp
        }
        INSTR_IS_TAGGED => {
            let v = load_at(bldr, base, sp);
            let one_bit = bldr.ins().band_imm(v, 1);
            let zero = bldr.ins().iconst(types::I64, 0);
            let is_t = bldr.ins().icmp(IntCC::NotEqual, one_bit, zero);
            let t1 = tagged(bldr, 1);
            let t0 = tagged(bldr, 0);
            let r = bldr.ins().select(is_t, t1, t0);
            store_at(bldr, base, sp, r);
            sp
        }

        // ---- returns (collapse N+2: result + closure + retPC + N args) ----
        INSTR_RETURN_1 => {
            emit_return(bldr, base, sp, 1);
            *terminated = true;
            sp
        }
        INSTR_RETURN_2 => {
            emit_return(bldr, base, sp, 2);
            *terminated = true;
            sp
        }
        INSTR_RETURN_3 => {
            emit_return(bldr, base, sp, 3);
            *terminated = true;
            sp
        }
        INSTR_RETURN_B => {
            emit_return(bldr, base, sp, imm1 as i64);
            *terminated = true;
            sp
        }
        INSTR_RETURN_W => {
            emit_return(bldr, base, sp, imm_u16 as i64);
            *terminated = true;
            sp
        }

        // ---- statically-resolved native call (non-popping) ----
        INSTR_CALL_CONST_ADDR8_0
        | INSTR_CALL_CONST_ADDR8_1
        | INSTR_CALL_CONST_ADDR8_8
        | INSTR_CALL_CONST_ADDR16_8 => emit_call_cca(bldr, st, base, sp, cctx, pc, b, total)?,

        // ---- DYNAMIC call (non-static target) — trampoline into the
        // interpreter's do_call via region_interp_call (S4e). ----
        //
        // CALL_CLOSURE (mod.rs:4223): the closure is on TOP; the interp
        // POPS it (sp += 1) then do_call. So the closure = stack[sp] and
        // the trampoline's sp_at_top_arg = sp + 1 (args after the pop).
        INSTR_CALL_CLOSURE => {
            emit_call_dynamic(bldr, st, base, sp, cctx, /*pop_top=*/ true, 0)?
        }
        // CALL_LOCAL_B (mod.rs:4256): the closure is PEEKED at depth n
        // (NOT popped — it persists), the args are the top values. The
        // trampoline's sp_at_top_arg = sp (unchanged), closure = stack[sp+n].
        INSTR_CALL_LOCAL_B => {
            emit_call_dynamic(
                bldr,
                st,
                base,
                sp,
                cctx,
                /*pop_top=*/ false,
                imm1 as i64,
            )?
        }

        // ---- S4d: stack container (NO heap alloc, do it FIRST) ----
        // STACK_CONTAINER_B N (mod.rs:3849): push N tagged(0) words, then
        // push a container-ref word = address of slot 0 (the most-recently
        // pushed zero). Downward: after pushing N zeros sp1 = sp-N and the
        // last zero (slot 0) is at stack[sp1]; the ref = base + sp1*8; then
        // push the ref (sp2 = sp1-1). The ref is a REAL stack pointer (the
        // interp stores `stack.as_ptr().add(sp)` after the N pushes), so we
        // compute `addr_at(base, sp1)`. NO region_alloc — pure stack work,
        // so NO cache-ptr hazard. (Mirrors the interp do_stack_container.)
        INSTR_STACK_CONTAINER_B => {
            let n = imm1 as i64;
            // Push N tagged(0) words.
            let zero = tagged(bldr, 0);
            let sp1 = bldr.ins().iadd_imm(sp, -n);
            // Zero the N slots [sp1, sp). Write each explicitly (N is a
            // small compile-time constant from the immediate byte).
            let mut k = 0i64;
            while k < n {
                let idx = bldr.ins().iadd_imm(sp1, k);
                store_at(bldr, base, idx, zero);
                k += 1;
            }
            // Container ref = &stack[sp1] = base + sp1*8.
            let ref_ptr = addr_at(bldr, base, sp1);
            // Push the ref word (its raw pointer bits) on top.
            emit_push(bldr, base, sp1, ref_ptr)
        }

        // ---- S4d: HEAP allocation opcodes (via the GC-safe trampoline) ----
        // Each lowering: (1) PUBLISH live_sp = current sp into ctx; (2) call
        // region_alloc(ctx, n_words, flags) -> body_ptr (which may fire a
        // GC, MOVING every heap object); (3) RE-READ every operand from the
        // (forwarded) SHARED STACK *after* the alloc; (4) store the fields
        // into the new object (no alloc between stores, so the to-space body
        // ptr stays valid); (5) collapse sp + push the object pointer.
        // NEVER hold a stack-loaded heap pointer in a register across the
        // alloc — that is the within-block cache-ptr-across-alloc hazard.
        INSTR_TUPLE_2 => emit_alloc_tuple(bldr, st, base, sp, cctx, 2)?,
        INSTR_TUPLE_3 => emit_alloc_tuple(bldr, st, base, sp, cctx, 3)?,
        INSTR_TUPLE_4 => emit_alloc_tuple(bldr, st, base, sp, cctx, 4)?,
        INSTR_TUPLE_B => emit_alloc_tuple(bldr, st, base, sp, cctx, imm1 as i64)?,
        INSTR_CLOSURE_B => emit_alloc_closure(bldr, st, base, sp, cctx, imm1 as i64)?,
        INSTR_ALLOC_REF => emit_alloc_ref(bldr, st, base, sp, cctx)?,
        INSTR_ALLOC_WORD_MEMORY => emit_alloc_word_memory(bldr, st, base, sp, cctx)?,
        INSTR_ALLOC_BYTE_MEM => emit_alloc_byte_mem(bldr, st, base, sp, cctx)?,

        other => {
            return Err(BailReason::UnsupportedOpcode {
                op: other,
                name: polyml_runtime::interpreter::disasm::opcode_name(other),
                at: pc,
            });
        }
    };
    Ok(new_sp)
}

fn push_tagged(b: &mut FunctionBuilder, base: Value, sp: Value, n: i64) -> Value {
    let v = tagged(b, n);
    emit_push(b, base, sp, v)
}
fn peek_push(b: &mut FunctionBuilder, base: Value, sp: Value, depth: i64) -> Value {
    let v = emit_peek(b, base, sp, depth);
    emit_push(b, base, sp, v)
}
/// INDIRECT_N: pop obj (sp+=1), load field N, push (sp-=1). Net sp = sp.
fn indirect(b: &mut FunctionBuilder, base: Value, sp: Value, field: i64) -> Value {
    let obj = load_at(b, base, sp); // top
    let a = b.ins().iadd_imm(obj, field * 8);
    let v = b.ins().load(types::I64, MemFlags::trusted(), a, 0);
    store_at(b, base, sp, v);
    sp
}
/// INDIRECT_LOCAL: peek obj at depth, load field, push. sp -= 1.
fn indirect_local(
    b: &mut FunctionBuilder,
    base: Value,
    sp: Value,
    depth: i64,
    field: i64,
) -> Value {
    let obj = emit_peek(b, base, sp, depth);
    let a = b.ins().iadd_imm(obj, field * 8);
    let v = b.ins().load(types::I64, MemFlags::trusted(), a, 0);
    emit_push(b, base, sp, v)
}
/// RESET_R_N: top=stack[sp]; new_sp=sp+N; stack[new_sp]=top.
fn reset_r(b: &mut FunctionBuilder, base: Value, sp: Value, n: i64) -> Value {
    let top = load_at(b, base, sp);
    let new_sp = b.ins().iadd_imm(sp, n);
    store_at(b, base, new_sp, top);
    new_sp
}

/// BACK-EDGE jump WITH the inline GC-safepoint poll (S4c). At a JUMP_BACK
/// (the loop latch) emit:
///
///   used      = load *(ctx.gc_used_ptr)            ; 2 loads (ptr + deref)
///   trigger   = load ctx.gc_trigger               ; 1 load
///   over?     = used >=u trigger                   ; 1 cmp
///   brif over -> slow_blk(sp)  else target_blk(sp); 1 predicted-not-taken
///                                                    branch (NO call on
///                                                    the no-GC fast path)
///   slow_blk: ctx.live_sp = sp                     ; publish sp
///             call region_safepoint(ctx)           ; collect mid-region
///             jump target_blk(sp)                  ; resume the loop head
///
/// On the common (no-GC) path the region does NOTHING but the cheap
/// compare + a not-taken branch, then jumps to the loop head — preserving
/// the tight-loop speed. The slow path fires only when the words-allocated
/// counter has crossed the trigger (the SAME condition the interpreter's
/// top-of-step check uses).
///
/// If this function has no `safepoint_ref` (no back-edge was detected at
/// declaration time — should be impossible here since we only reach this
/// for a JUMP_BACK), fall back to a plain back-jump (correct, just
/// un-polled) rather than emitting a dangling call.
fn emit_back_edge_jump(
    bldr: &mut FunctionBuilder,
    st: &mut FnState,
    ctx: Value,
    target: usize,
    sp: Value,
) -> Result<(), BailReason> {
    let target_blk = *st
        .blocks
        .get(&target)
        .ok_or(BailReason::JumpMidInstruction(target))?;
    let Some(safepoint) = st.safepoint_ref else {
        // No declared safepoint trampoline (a JUMP_BACK with no back-edge
        // flagged is a contradiction; be safe + just jump).
        bldr.ins().jump(target_blk, &[BlockArg::from(sp)]);
        return Ok(());
    };

    // INLINE POLL (predicted-not-taken). Load the live words-allocated
    // counter via ctx.gc_used_ptr, compare to ctx.gc_trigger.
    let used_ptr = load_gc_used_ptr(bldr, ctx);
    let used = bldr
        .ins()
        .load(types::I64, MemFlags::trusted(), used_ptr, 0);
    let trigger = load_gc_trigger(bldr, ctx);
    // `used >= trigger` (unsigned — both are non-negative word counts).
    let over = bldr
        .ins()
        .icmp(IntCC::UnsignedGreaterThanOrEqual, used, trigger);

    let slow_blk = bldr.create_block();
    // brif: the slow path is the cold side (placed second so the common
    // fall-through is the not-taken edge).
    bldr.ins()
        .brif(over, slow_blk, &[], target_blk, &[BlockArg::from(sp)]);

    // ---- slow path: publish sp, collect, resume the loop head ----
    bldr.switch_to_block(slow_blk);
    bldr.seal_block(slow_blk);
    store_live_sp(bldr, ctx, sp);
    bldr.ins().call(safepoint, &[ctx]);
    bldr.ins().jump(target_blk, &[BlockArg::from(sp)]);
    Ok(())
}

/// Conditional jump: pop the condition, branch to target or fallthrough.
/// `jump_if_zero` = true for JUMP_FALSE (jump when cond == tagged(0)).
#[allow(clippy::too_many_arguments)]
fn cond_jump(
    bldr: &mut FunctionBuilder,
    st: &mut FnState,
    base: Value,
    sp: Value,
    bc: &[u8],
    pc: usize,
    b: u8,
    total: usize,
    after: usize,
    jump_if_zero: bool,
) -> Result<(), BailReason> {
    let t = jump_target(bc, pc, b, total).ok_or(BailReason::Truncated(pc))?;
    let cond = load_at(bldr, base, sp);
    let sp_popped = bldr.ins().iadd_imm(sp, 1);
    let zero = tagged(bldr, 0);
    let cc = if jump_if_zero {
        IntCC::Equal
    } else {
        IntCC::NotEqual
    };
    let take = bldr.ins().icmp(cc, cond, zero);
    let target_blk = *st.blocks.get(&t).ok_or(BailReason::JumpMidInstruction(t))?;
    let fall_blk = *st
        .blocks
        .get(&after)
        .ok_or(BailReason::JumpMidInstruction(after))?;
    bldr.ins().brif(
        take,
        target_blk,
        &[BlockArg::from(sp_popped)],
        fall_blk,
        &[BlockArg::from(sp_popped)],
    );
    Ok(())
}

/// JUMP_NEQ_LOCAL / JUMP_NEQ_LOCAL_IND (mod.rs:4097-4123). Peek the local
/// at `depth` (immediate 1); for the `_IND` variant deref its field 0
/// first (a union-tag test on `*p`). Fall through (equal) iff `u` is
/// tagged AND `u.untag() == want` (immediate 2); else jump to `after+off`
/// (immediate 3). No stack effect. The equality `is_tagged && untag==want`
/// is exactly `u == tagged(want)` (tagged(want)=2*want+1 is always odd, so
/// a non-tagged word can never equal it), so the JUMP-taken condition is a
/// single `u != tagged(want)`.
#[allow(clippy::too_many_arguments)]
fn neq_local_jump(
    bldr: &mut FunctionBuilder,
    st: &mut FnState,
    base: Value,
    sp: Value,
    bc: &[u8],
    pc: usize,
    after: usize,
    indirect: bool,
) -> Result<(), BailReason> {
    let depth = *bc.get(pc + 1).ok_or(BailReason::Truncated(pc))? as i64;
    let want = *bc.get(pc + 2).ok_or(BailReason::Truncated(pc))? as i64;
    let off = *bc.get(pc + 3).ok_or(BailReason::Truncated(pc))? as usize;
    let t = after + off;
    let mut u = emit_peek(bldr, base, sp, depth);
    if indirect {
        // _IND: u = *(local as *PolyWord) — load field 0 of the local.
        u = bldr.ins().load(types::I64, MemFlags::trusted(), u, 0);
    }
    let want_tagged = tagged(bldr, want);
    // JUMP taken iff NOT equal.
    let take = bldr.ins().icmp(IntCC::NotEqual, u, want_tagged);
    let target_blk = *st.blocks.get(&t).ok_or(BailReason::JumpMidInstruction(t))?;
    let fall_blk = *st
        .blocks
        .get(&after)
        .ok_or(BailReason::JumpMidInstruction(after))?;
    bldr.ins().brif(
        take,
        target_blk,
        &[BlockArg::from(sp)],
        fall_blk,
        &[BlockArg::from(sp)],
    );
    Ok(())
}

/// JUMP_TAGGED_LOCAL (mod.rs:4126-4133). Peek the local at `depth`
/// (immediate 1); jump to `after+off` (immediate 2) iff it is tagged
/// ((v&1)!=0); else fall through. No stack effect.
fn tagged_local_jump(
    bldr: &mut FunctionBuilder,
    st: &mut FnState,
    base: Value,
    sp: Value,
    bc: &[u8],
    pc: usize,
    after: usize,
) -> Result<(), BailReason> {
    let depth = *bc.get(pc + 1).ok_or(BailReason::Truncated(pc))? as i64;
    let off = *bc.get(pc + 2).ok_or(BailReason::Truncated(pc))? as usize;
    let t = after + off;
    let u = emit_peek(bldr, base, sp, depth);
    let one_bit = bldr.ins().band_imm(u, 1);
    let zero = bldr.ins().iconst(types::I64, 0);
    let take = bldr.ins().icmp(IntCC::NotEqual, one_bit, zero);
    let target_blk = *st.blocks.get(&t).ok_or(BailReason::JumpMidInstruction(t))?;
    let fall_blk = *st
        .blocks
        .get(&after)
        .ok_or(BailReason::JumpMidInstruction(after))?;
    bldr.ins().brif(
        take,
        target_blk,
        &[BlockArg::from(sp)],
        fall_blk,
        &[BlockArg::from(sp)],
    );
    Ok(())
}

/// What `LOAD_ML_*` reads + how it re-tags.
enum LoadKind {
    /// LOAD_ML_WORD: load an I64 PolyWord at base + idx*8; value used as-is.
    Word,
    /// LOAD_ML_BYTE: load a u8 at base + idx; zero-extend then TAG.
    Byte,
    /// LOAD_UNTAGGED: load an I64 raw word at base + idx*8; TAG the bits.
    Untagged,
}

/// LOAD_ML_WORD / LOAD_ML_BYTE / LOAD_UNTAGGED (mod.rs:3696-3779). The
/// interp: `idx = untag(pop top); base = peek(0) (the new top after the
/// pop); v = load base[idx]; pop; push v`. Net: two pops + one push (= sp
/// rises by 1 from the index pop, the base peek+pop+push nets 0), so the
/// final sp = sp + 1 with the result stored at the new top. Concretely:
///   top    = stack[sp]   (the index, tagged)
///   base   = stack[sp+1] (the object)
///   stack[sp+1] = load(base, untag(index)); new sp = sp+1.
/// LOAD_UNTAGGED's `is_data_ptr` debug-abort is IGNORED (diagnostics only);
/// the fast path is just the load + re-tag.
fn load_ml(b: &mut FunctionBuilder, base: Value, sp: Value, kind: LoadKind) -> Value {
    let index_w = load_at(b, base, sp); // top = the tagged index
    let idx = emit_untag(b, index_w); // untag -> raw index
    let obj = emit_peek(b, base, sp, 1); // base object (below the index)
    let new_sp = b.ins().iadd_imm(sp, 1); // the two pops + one push net +1
    let r = match kind {
        LoadKind::Word => {
            // I64 at base + idx*8.
            let a = addr_at(b, obj, idx);
            b.ins().load(types::I64, MemFlags::trusted(), a, 0)
        }
        LoadKind::Byte => {
            // u8 at base + idx; zero-extend then tag.
            let a = b.ins().iadd(obj, idx);
            let byte = b.ins().load(types::I8, MemFlags::trusted(), a, 0);
            let z = b.ins().uextend(types::I64, byte);
            emit_tag(b, z)
        }
        LoadKind::Untagged => {
            // I64 raw word at base + idx*8; tag the bits (interp:
            // PolyWord::tagged(raw.0 as isize)).
            let a = addr_at(b, obj, idx);
            let raw = b.ins().load(types::I64, MemFlags::trusted(), a, 0);
            emit_tag(b, raw)
        }
    };
    store_at(b, base, new_sp, r);
    new_sp
}

/// STORE_ML_WORD / STORE_UNTAGGED (mod.rs:3780-3887). The interp:
/// `val = pop; idx = untag(pop); base = peek(0); base[idx] = val; pop;
/// push tagged(0)`. Stack layout at entry (top->down):
///   stack[sp]   = val
///   stack[sp+1] = index (tagged)
///   stack[sp+2] = base object
/// After: base[untag(index)] = val (STORE_UNTAGGED writes untag(val) as
/// raw bits; STORE_ML_WORD writes val verbatim), result tagged(0) replaces
/// the base; new sp = sp+2.
fn store_ml(b: &mut FunctionBuilder, base: Value, sp: Value, untagged: bool) -> Value {
    let val = load_at(b, base, sp); // top = value
    let index_w = emit_peek(b, base, sp, 1); // index
    let idx = emit_untag(b, index_w);
    let obj = emit_peek(b, base, sp, 2); // base object
    let to_store = if untagged {
        // STORE_UNTAGGED writes untag(val) as the raw word bits.
        emit_untag(b, val)
    } else {
        val
    };
    let a = addr_at(b, obj, idx);
    b.ins().store(MemFlags::trusted(), to_store, a, 0);
    let new_sp = b.ins().iadd_imm(sp, 2); // two pops + peek/push net +2
    let zero = tagged(b, 0);
    store_at(b, base, new_sp, zero);
    new_sp
}

/// Which length-word field a cell-introspection op decodes.
enum CellField {
    /// CELL_LENGTH: length in words = length-word & LENGTH_MASK.
    Length,
    /// CELL_FLAGS: flag byte = length-word >> FLAGS_SHIFT (top byte).
    Flags,
}

/// CELL_LENGTH / CELL_FLAGS (mod.rs:3617-3634). The length word sits at
/// obj[-1]; length = lw & LENGTH_MASK (mask off the top flag byte); flags
/// = lw >> FLAGS_SHIFT (the top byte). The interp peeks the object, reads
/// the length word, pops, and pushes the tagged decoded field — net sp
/// unchanged (peek + pop + push), replacing the top.
fn cell_intro(b: &mut FunctionBuilder, base: Value, sp: Value, field: CellField) -> Value {
    let obj = load_at(b, base, sp); // top = object pointer
    // length word at obj[-1] (one word below the object body).
    let lw_addr = b.ins().iadd_imm(obj, -8);
    let lw = b.ins().load(types::I64, MemFlags::trusted(), lw_addr, 0);
    let decoded = match field {
        // length_of(word) = word.0 & LENGTH_MASK (= !FLAGS_MASK). FLAGS_MASK
        // is the top byte (0xff << 56), so LENGTH_MASK keeps the low 56 bits.
        CellField::Length => {
            let mask = b
                .ins()
                .iconst(types::I64, polyml_runtime::length_word::LENGTH_MASK as i64);
            b.ins().band(lw, mask)
        }
        // flags_of(word) = (word.0 >> FLAGS_SHIFT) as u8 (the top byte).
        CellField::Flags => {
            let shifted = b
                .ins()
                .ushr_imm(lw, i64::from(polyml_runtime::length_word::FLAGS_SHIFT));
            // mask to a byte (mirrors the `as u8` truncation).
            b.ins().band_imm(shifted, 0xff)
        }
    };
    let r = emit_tag(b, decoded);
    store_at(b, base, sp, r);
    sp
}

enum WordOp {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    Shl,
    ShrLog,
}
/// Word binop (mirror mod.rs bin_op_word + the tag-aware formulas).
/// Stack: x = top (sp), y = below (sp+1). Pop x, pop y, push f(x,y).
/// Net sp = sp+1 (two pops, one push).
fn word_bin(b: &mut FunctionBuilder, base: Value, sp: Value, op: WordOp) -> Value {
    let x = load_at(b, base, sp); // top
    let y = emit_peek(b, base, sp, 1); // below
    let r = match op {
        // (2A+1)+(2B+1)-1 = TAGGED(A+B): y + x - 1.
        WordOp::Add => {
            let s = b.ins().iadd(y, x);
            b.ins().iadd_imm(s, -1)
        }
        // (2A+1)-(2B+1)+1: y - x + 1.
        WordOp::Sub => {
            let s = b.ins().isub(y, x);
            b.ins().iadd_imm(s, 1)
        }
        WordOp::Mul => {
            let ax = b.ins().ushr_imm(x, 1);
            let ay = b.ins().ushr_imm(y, 1);
            let m = b.ins().imul(ax, ay);
            let sh = b.ins().ishl_imm(m, 1);
            b.ins().bor_imm(sh, 1)
        }
        WordOp::And => b.ins().band(y, x),
        WordOp::Or => b.ins().bor(y, x),
        // (y ^ x) | 1 (XOR clears the tag bit; reinstate).
        WordOp::Xor => {
            let xr = b.ins().bxor(y, x);
            b.ins().bor_imm(xr, 1)
        }
        WordOp::Shl => {
            // s = (x>>1)&63; v=y>>1; ((v<<s)<<1)|1.
            let s0 = b.ins().ushr_imm(x, 1);
            let s = b.ins().band_imm(s0, 63);
            let v = b.ins().ushr_imm(y, 1);
            let sh = b.ins().ishl(v, s);
            let sh2 = b.ins().ishl_imm(sh, 1);
            b.ins().bor_imm(sh2, 1)
        }
        WordOp::ShrLog => {
            let s0 = b.ins().ushr_imm(x, 1);
            let s = b.ins().band_imm(s0, 63);
            let v = b.ins().ushr_imm(y, 1);
            let sh = b.ins().ushr(v, s);
            let sh2 = b.ins().ishl_imm(sh, 1);
            b.ins().bor_imm(sh2, 1)
        }
    };
    let new_sp = b.ins().iadd_imm(sp, 1);
    store_at(b, base, new_sp, r);
    new_sp
}

/// Word DIV/MOD with a zero-divisor check that RAISEs (DivByZero). The
/// divisor is x (top), the dividend is y (below). On x==0 -> raise.
fn word_divmod(b: &mut FunctionBuilder, base: Value, sp: Value, ctx: Value, is_div: bool) -> Value {
    let x = load_at(b, base, sp); // divisor (top)
    let y = emit_peek(b, base, sp, 1); // dividend
    let ax = b.ins().ushr_imm(x, 1);
    let ay = b.ins().ushr_imm(y, 1);
    let zero = b.ins().iconst(types::I64, 0);
    let is_zero = b.ins().icmp(IntCC::Equal, ax, zero);
    let raise_blk = b.create_block();
    let ok_blk = b.create_block();
    b.ins().brif(is_zero, raise_blk, &[], ok_blk, &[]);

    b.switch_to_block(raise_blk);
    b.seal_block(raise_blk);
    emit_raise(b, ctx, EXN_DIVZERO);

    b.switch_to_block(ok_blk);
    b.seal_block(ok_blk);
    let q = if is_div {
        b.ins().udiv(ay, ax)
    } else {
        b.ins().urem(ay, ax)
    };
    let sh = b.ins().ishl_imm(q, 1);
    let r = b.ins().bor_imm(sh, 1);
    let new_sp = b.ins().iadd_imm(sp, 1);
    store_at(b, base, new_sp, r);
    new_sp
}

enum FixedOp {
    Add,
    Sub,
    Mul,
}
/// FixedInt add/sub/mult: untag, compute, range-check into the tagged
/// range, tag; raise Overflow if out of range. Stack: x=top(sp),
/// y=below(sp+1). Net sp=sp+1.
fn fixed_arith(b: &mut FunctionBuilder, base: Value, sp: Value, ctx: Value, op: FixedOp) -> Value {
    let x = load_at(b, base, sp);
    let y = emit_peek(b, base, sp, 1);
    let ax = emit_untag(b, x);
    let ay = emit_untag(b, y);
    // interp order: FIXED_ADD = x+y; FIXED_SUB = y-x; FIXED_MULT = x*y.
    let res = match op {
        FixedOp::Add => b.ins().iadd(ax, ay),
        FixedOp::Sub => b.ins().isub(ay, ax),
        FixedOp::Mul => b.ins().imul(ax, ay),
    };
    let min_v = b.ins().iconst(types::I64, MIN_TAGGED);
    let max_v = b.ins().iconst(types::I64, MAX_TAGGED);
    let ge_min = b.ins().icmp(IntCC::SignedGreaterThanOrEqual, res, min_v);
    let le_max = b.ins().icmp(IntCC::SignedLessThanOrEqual, res, max_v);
    let mut in_range = b.ins().band(ge_min, le_max);
    if let FixedOp::Mul = op {
        // Guard against i64 wrap (operands up to 2^62, product up to
        // 2^124 overflows i64): require ax==0 OR res/ax == ay.
        let zero = b.ins().iconst(types::I64, 0);
        let ax_zero = b.ins().icmp(IntCC::Equal, ax, zero);
        let one = b.ins().iconst(types::I64, 1);
        let safe_div = b.ins().select(ax_zero, one, ax);
        let recovered = b.ins().sdiv(res, safe_div);
        let no_wrap = b.ins().icmp(IntCC::Equal, recovered, ay);
        let no_wrap_or_zero = b.ins().bor(ax_zero, no_wrap);
        in_range = b.ins().band(in_range, no_wrap_or_zero);
    }
    let ok_blk = b.create_block();
    let raise_blk = b.create_block();
    b.ins().brif(in_range, ok_blk, &[], raise_blk, &[]);

    b.switch_to_block(raise_blk);
    b.seal_block(raise_blk);
    emit_raise(b, ctx, EXN_OVERFLOW);

    b.switch_to_block(ok_blk);
    b.seal_block(ok_blk);
    let tagged_res = emit_tag(b, res);
    let new_sp = b.ins().iadd_imm(sp, 1);
    store_at(b, base, new_sp, tagged_res);
    new_sp
}

/// FixedInt quot/rem: untag, check divisor != 0 (raise DivByZero), then
/// signed div/rem. Stack: x=divisor(top), y=dividend(below). Mirrors
/// mod.rs bin_op_tagged: FIXED_QUOT = y/x, FIXED_REM = y%x.
fn fixed_divrem(
    b: &mut FunctionBuilder,
    base: Value,
    sp: Value,
    ctx: Value,
    is_quot: bool,
) -> Value {
    let x = load_at(b, base, sp);
    let y = emit_peek(b, base, sp, 1);
    let ax = emit_untag(b, x);
    let ay = emit_untag(b, y);
    let zero = b.ins().iconst(types::I64, 0);
    let is_zero = b.ins().icmp(IntCC::Equal, ax, zero);
    let raise_blk = b.create_block();
    let ok_blk = b.create_block();
    b.ins().brif(is_zero, raise_blk, &[], ok_blk, &[]);

    b.switch_to_block(raise_blk);
    b.seal_block(raise_blk);
    emit_raise(b, ctx, EXN_DIVZERO);

    b.switch_to_block(ok_blk);
    b.seal_block(ok_blk);
    // For the tagged range INT_MIN/-1 cannot occur (operands <= 2^62), so
    // sdiv/srem match wrapping_div/rem.
    let q = if is_quot {
        b.ins().sdiv(ay, ax)
    } else {
        b.ins().srem(ay, ax)
    };
    let tagged_q = emit_tag(b, q);
    let new_sp = b.ins().iadd_imm(sp, 1);
    store_at(b, base, new_sp, tagged_q);
    new_sp
}

/// Comparison: x=top(sp), y=below. pop both, push tagged(bool). Net sp+1.
/// The interp uses `f(x.0, y.0)` with y on the LEFT (e.g. LESS_SIGNED =
/// (y as isize) < (x as isize)). We mirror exactly.
fn cmp(b: &mut FunctionBuilder, base: Value, sp: Value, cc: IntCC) -> Value {
    let x = load_at(b, base, sp);
    let y = emit_peek(b, base, sp, 1);
    let res = b.ins().icmp(cc, y, x);
    let t1 = tagged(b, 1);
    let t0 = tagged(b, 0);
    let r = b.ins().select(res, t1, t0);
    let new_sp = b.ins().iadd_imm(sp, 1);
    store_at(b, base, new_sp, r);
    new_sp
}

/// RETURN_N (real-bytecode frame): at entry stack[sp]=result,
/// stack[sp+1]=closure, stack[sp+2]=retPC, stack[sp+3..sp+2+N]=args.
/// Collapse so result lands at stack[sp+2+N], new sp = sp+2+N. Returns
/// RegionRet{ sp+2+N, 0 }. This is the do_return value-collapse with the
/// closure/retPC ON the shared stack, matching the interpreter exactly.
fn emit_return(b: &mut FunctionBuilder, base: Value, sp: Value, n: i64) {
    let result = load_at(b, base, sp);
    let dst = b.ins().iadd_imm(sp, n + 2);
    store_at(b, base, dst, result);
    let zero = b.ins().iconst(types::I64, 0);
    b.ins().return_(&[dst, zero]);
}

/// Emit a RAISE: set ctx.exn_packet, return new_sp = ctx.handler_sp,
/// raised=1. The region installs no in-region handlers in the core
/// subset, so any raise escapes to ctx.handler_sp -- which the boundary
/// owns. The boundary maps EXN_OVERFLOW/DIVZERO onto the real
/// interpreter raise so the packet + handler_sp are byte-exact.
fn emit_raise(b: &mut FunctionBuilder, ctx: Value, packet: i64) {
    let p = b.ins().iconst(types::I64, packet);
    store_exn_packet(b, ctx, p);
    let hsp = load_handler_sp(b, ctx);
    let one = b.ins().iconst(types::I64, 1);
    b.ins().return_(&[hsp, one]);
}

/// CALL_CONST_ADDR (non-popping native region call). At this point the
/// callee's N args are already pushed (top arg at stack[sp]). The
/// interpreter's do_call then pushes retPC + closure on TOP of the args
/// and jumps; the callee's RETURN_N collapses result+closure+retPC+N
/// args. We replicate: push a retPC placeholder, push the closure word,
/// native-call the callee (base, sp_after_closure, ctx). On a normal
/// return new_sp points at the single result on top. On raised=1,
/// propagate (return raised=1 with new_sp = handler_sp).
#[allow(clippy::too_many_arguments)]
fn emit_call_cca(
    bldr: &mut FunctionBuilder,
    st: &mut FnState,
    base: Value,
    sp: Value,
    ctx: Value,
    pc: usize,
    b: u8,
    total: usize,
) -> Result<Value, BailReason> {
    let _ = total;
    // SAFETY: compile-time; resolve callee code-obj addr + closure word.
    let callee_code =
        unsafe { cca_target_code_addr(st.rc, pc, b) }.ok_or(BailReason::UnresolvableCallee(pc))?;
    let fref = *st
        .callee_refs
        .get(&callee_code)
        .ok_or(BailReason::UnresolvableCallee(pc))?;
    let closure_bits = cca_closure_bits(st.rc, pc, b).ok_or(BailReason::UnresolvableCallee(pc))?;

    // Push retPC placeholder (0). The native call/ret subsumes the real
    // return PC's role; the callee never DEREFERENCES this slot (it only
    // collapses past it in RETURN_N), so 0 keeps the shared-stack
    // contents deterministic.
    let retpc = bldr.ins().iconst(types::I64, 0);
    let sp_ret = emit_push(bldr, base, sp, retpc);
    let closure = bldr.ins().iconst(types::I64, closure_bits);
    let sp_clo = emit_push(bldr, base, sp_ret, closure);

    // Native call.
    let call = bldr.ins().call(fref, &[base, sp_clo, ctx]);
    let callee_sp = bldr.inst_results(call)[0];
    let raised = bldr.inst_results(call)[1];

    // On raised, propagate. Otherwise continue with sp = callee_sp.
    let cont_blk = bldr.create_block();
    bldr.append_block_param(cont_blk, types::I64); // sp
    let prop_blk = bldr.create_block();
    bldr.ins().brif(
        raised,
        prop_blk,
        &[],
        cont_blk,
        &[BlockArg::from(callee_sp)],
    );

    bldr.switch_to_block(prop_blk);
    bldr.seal_block(prop_blk);
    let hsp = load_handler_sp(bldr, ctx);
    let one = bldr.ins().iconst(types::I64, 1);
    bldr.ins().return_(&[hsp, one]);

    bldr.switch_to_block(cont_blk);
    bldr.seal_block(cont_blk);
    let new_sp = bldr.block_params(cont_blk)[0];
    Ok(new_sp)
}

/// Load `ctx.interp_ptr` (offset 16) — the raw `*mut Interpreter` the
/// dynamic-call trampoline re-enters through.
fn load_interp_ptr(b: &mut FunctionBuilder, ctx: Value) -> Value {
    b.ins().load(types::I64, MemFlags::trusted(), ctx, 16)
}

// =====================================================================
// S4d — GC-SAFE HEAP ALLOCATION LOWERINGS.
//
// THE INVARIANT every lowering here upholds (the make-or-break): a GC can
// fire INSIDE region_alloc, moving every heap object. So the lowering must:
//   1. PUBLISH live_sp = the current sp into ctx (so the GC's [sp,len)
//      root walk covers the operands the alloc consumes — they are on the
//      shared stack at indices >= sp), via emit_region_alloc.
//   2. call region_alloc(ctx, n_words, flags) -> body_ptr.
//   3. RE-READ every operand (field/init values, base pointers) from the
//      (now-forwarded) shared stack *AFTER* the alloc — NEVER hold a
//      stack-loaded heap pointer in a register across the alloc.
//   4. store the fields into the new object (no alloc between stores, so
//      the just-returned to-space body ptr stays valid), then collapse sp
//      and push the object pointer.
// Each lowering does exactly ONE alloc, so step 4's stores never straddle
// a second alloc (no spill-the-first-ptr complication arises here).
// =====================================================================

/// Emit the GC-safe alloc: PUBLISH `sp` into `ctx.live_sp`, call
/// `region_alloc(ctx, n_words, flags) -> body_ptr`, and on a 0 (NoAllocator
/// / post-GC exhaustion) RAISE StackOverflow (return new_sp=handler_sp,
/// raised=1) rather than let the region deref null — mirroring the
/// interpreter's hard panic-on-exhaustion as a TRAPPED error. Returns the
/// body_ptr SSA value on the success path (the builder is left positioned in
/// a fresh "ok" block that the caller continues filling).
///
/// `n_words` may be a compile-time constant or an SSA value (for runtime
/// lengths like ALLOC_WORD_MEMORY); `flags` is likewise either.
fn emit_region_alloc(
    bldr: &mut FunctionBuilder,
    st: &FnState,
    ctx: Value,
    sp: Value,
    n_words: Value,
    flags: Value,
) -> Result<Value, BailReason> {
    let aref = st.alloc_ref.ok_or(BailReason::UnresolvableCallee(0))?;
    // (1) Publish the region's live sp BEFORE the alloc so a GC inside the
    //     trampoline forwards [sp, len). The operands the alloc reads are at
    //     indices >= sp (still on the shared stack), so they survive + are
    //     forwarded.
    store_live_sp(bldr, ctx, sp);
    // (2) Call the trampoline.
    let call = bldr.ins().call(aref, &[ctx, n_words, flags]);
    let body_ptr = bldr.inst_results(call)[0];
    // On 0 (exhaustion / no allocator) RAISE StackOverflow.
    let zero = bldr.ins().iconst(types::I64, 0);
    let failed = bldr.ins().icmp(IntCC::Equal, body_ptr, zero);
    let raise_blk = bldr.create_block();
    let ok_blk = bldr.create_block();
    bldr.ins().brif(failed, raise_blk, &[], ok_blk, &[]);

    bldr.switch_to_block(raise_blk);
    bldr.seal_block(raise_blk);
    emit_raise(bldr, ctx, EXN_STACKOVERFLOW);

    bldr.switch_to_block(ok_blk);
    bldr.seal_block(ok_blk);
    Ok(body_ptr)
}

/// TUPLE_N (mod.rs do_tuple): alloc N ordinary words (flags 0), fill from
/// the top N stack values, push the tuple ptr. The interp pops top->p[n-1],
/// next->p[n-2], …, deepest->p[0]; i.e. `p[i] = stack[sp + (n-1-i)]`
/// (pre-alloc sp). RE-READ all N field values from the FORWARDED stack
/// AFTER the alloc, store into the new object, collapse: final sp =
/// sp + n - 1, tuple ptr at stack[sp+n-1].
fn emit_alloc_tuple(
    bldr: &mut FunctionBuilder,
    st: &FnState,
    base: Value,
    sp: Value,
    ctx: Value,
    n: i64,
) -> Result<Value, BailReason> {
    let n_words = bldr.ins().iconst(types::I64, n);
    let flags = bldr.ins().iconst(types::I64, 0); // ordinary word object
    let p = emit_region_alloc(bldr, st, ctx, sp, n_words, flags)?;
    // RE-READ each field from the forwarded shared stack, store into p.
    // p[i] = stack[sp + (n-1-i)].
    for i in 0..n {
        let v = emit_peek(bldr, base, sp, n - 1 - i); // stack[sp + (n-1-i)]
        let dst = bldr.ins().iadd_imm(p, i * 8);
        bldr.ins().store(MemFlags::trusted(), v, dst, 0);
    }
    // Collapse: N pops + 1 push => final sp = sp + n - 1; tuple ptr on top.
    let new_sp = bldr.ins().iadd_imm(sp, n - 1);
    store_at(bldr, base, new_sp, p);
    Ok(new_sp)
}

/// CLOSURE_B N (mod.rs do_create_closure): length = N+1; alloc
/// F_CLOSURE_OBJ. Entry top->down: capture[N-1]=top, …, capture[0], source
/// closure (deepest). The interp pops top->p[N], …, ->p[1] (so
/// `p[N-k+1] = stack[sp + (k-1)]`, i.e. `p[j] = stack[sp + (N-j)]` for j in
/// 1..=N), then copies the source closure's word0 (code addr) into p[0].
/// RE-READ the captures AND the source closure pointer from the FORWARDED
/// stack AFTER the alloc; deref the (forwarded) source for its code addr.
/// Collapse: N+1 pops + 1 push => final sp = sp + N; closure ptr on top.
fn emit_alloc_closure(
    bldr: &mut FunctionBuilder,
    st: &FnState,
    base: Value,
    sp: Value,
    ctx: Value,
    n: i64,
) -> Result<Value, BailReason> {
    use polyml_runtime::length_word::F_CLOSURE_OBJ;
    let length = n + 1;
    let n_words = bldr.ins().iconst(types::I64, length);
    let flags = bldr.ins().iconst(types::I64, i64::from(F_CLOSURE_OBJ));
    let p = emit_region_alloc(bldr, st, ctx, sp, n_words, flags)?;
    // RE-READ the N captures from the forwarded stack: p[j] = stack[sp + (N-j)]
    // for j in 1..=N.
    for j in 1..=n {
        let v = emit_peek(bldr, base, sp, n - j); // stack[sp + (N - j)]
        let dst = bldr.ins().iadd_imm(p, j * 8);
        bldr.ins().store(MemFlags::trusted(), v, dst, 0);
    }
    // RE-READ the source closure pointer (deepest, at stack[sp + N]) AFTER
    // the alloc — it is a heap pointer, so it must be re-read forwarded, NOT
    // cached across the alloc. Deref its word0 (the code address) and store
    // into p[0].
    let src = emit_peek(bldr, base, sp, n); // stack[sp + N] = source closure
    let code_addr = bldr.ins().load(types::I64, MemFlags::trusted(), src, 0);
    bldr.ins().store(MemFlags::trusted(), code_addr, p, 0); // p[0] = code addr
    // Collapse: N+1 pops + 1 push => final sp = sp + N; closure ptr on top.
    let new_sp = bldr.ins().iadd_imm(sp, n);
    store_at(bldr, base, new_sp, p);
    Ok(new_sp)
}

/// ALLOC_REF (mod.rs do_alloc_ref): alloc 1 mutable word, init = the value
/// currently on top, REPLACE the top with the cell ptr (net sp unchanged).
/// RE-READ the init value from the forwarded top AFTER the alloc, store
/// into p[0], replace the top slot with the ptr.
fn emit_alloc_ref(
    bldr: &mut FunctionBuilder,
    st: &FnState,
    base: Value,
    sp: Value,
    ctx: Value,
) -> Result<Value, BailReason> {
    use polyml_runtime::length_word::F_MUTABLE_BIT;
    let n_words = bldr.ins().iconst(types::I64, 1);
    let flags = bldr.ins().iconst(types::I64, i64::from(F_MUTABLE_BIT));
    let p = emit_region_alloc(bldr, st, ctx, sp, n_words, flags)?;
    // RE-READ the init value from the forwarded top (stack[sp]).
    let init = load_at(bldr, base, sp);
    bldr.ins().store(MemFlags::trusted(), init, p, 0); // p[0] = init
    // Replace top with the cell ptr (net sp unchanged: peek + pop + push).
    store_at(bldr, base, sp, p);
    Ok(sp)
}

/// ALLOC_WORD_MEMORY (mod.rs:3821): stack top->down [init, flags, length].
/// length = peek(2); init = pop; flags = pop; alloc(length, flags); fill
/// p[0..length] = init; pop length; push p. RE-READ length/flags/init from
/// the forwarded stack AFTER the alloc. Net: final sp = sp + 2, ptr at
/// stack[sp+2].
///
/// `length` is a RUNTIME tagged int (the loop fill count). We bound it
/// against a sane ceiling at run time is unnecessary — the trampoline's
/// `allocate` itself bails (returns 0 -> StackOverflow raise) on a length
/// that doesn't fit. The fill loop is emitted as a small Cranelift loop
/// over the runtime length so an arbitrary-length region is supported.
fn emit_alloc_word_memory(
    bldr: &mut FunctionBuilder,
    st: &FnState,
    base: Value,
    sp: Value,
    ctx: Value,
) -> Result<Value, BailReason> {
    // length is a tagged int at stack[sp+2]; untag for the word count.
    // We must read it BEFORE the alloc to pass n_words — but `length` is a
    // tagged INT (not a heap pointer), so reading it pre-alloc and passing
    // it by VALUE to region_alloc is safe (an integer cannot go stale). The
    // FIELD operands (init) ARE re-read post-alloc.
    let length_w = emit_peek(bldr, base, sp, 2); // tagged length (an int)
    let length = emit_untag(bldr, length_w);
    let flags_w = emit_peek(bldr, base, sp, 1); // tagged flags (an int)
    let flags = emit_untag(bldr, flags_w);
    let p = emit_region_alloc(bldr, st, ctx, sp, length, flags)?;
    // RE-READ the init value from the forwarded stack (stack[sp] = top).
    let init = load_at(bldr, base, sp);
    // Fill p[0..length] = init via a counted Cranelift loop (length is a
    // runtime value). No alloc inside the loop, so the to-space `p` + the
    // re-read `init` stay valid.
    let loop_hdr = bldr.create_block();
    bldr.append_block_param(loop_hdr, types::I64); // i
    let loop_body = bldr.create_block();
    let loop_done = bldr.create_block();
    let zero = bldr.ins().iconst(types::I64, 0);
    bldr.ins().jump(loop_hdr, &[BlockArg::from(zero)]);

    bldr.switch_to_block(loop_hdr);
    let i = bldr.block_params(loop_hdr)[0];
    let more = bldr.ins().icmp(IntCC::SignedLessThan, i, length);
    bldr.ins().brif(more, loop_body, &[], loop_done, &[]);

    bldr.switch_to_block(loop_body);
    bldr.seal_block(loop_body);
    let off = bldr.ins().imul_imm(i, 8);
    let dst = bldr.ins().iadd(p, off);
    bldr.ins().store(MemFlags::trusted(), init, dst, 0);
    let i_next = bldr.ins().iadd_imm(i, 1);
    bldr.ins().jump(loop_hdr, &[BlockArg::from(i_next)]);
    bldr.seal_block(loop_hdr);

    bldr.switch_to_block(loop_done);
    bldr.seal_block(loop_done);
    // Collapse: pop init + flags (sp += 2), replace length slot with ptr.
    let new_sp = bldr.ins().iadd_imm(sp, 2);
    store_at(bldr, base, new_sp, p);
    Ok(new_sp)
}

/// ALLOC_BYTE_MEM (mod.rs:3809): stack top->down [flags, length]. flags =
/// pop; length = peek(0); alloc(length, flags); pop; push p. Bytes are
/// UNINITIALIZED (the caller fills via STORE_*). flags + length are tagged
/// INTS (not heap pointers), so reading them pre-alloc + passing by value is
/// safe. Net: final sp = sp + 1, ptr at stack[sp+1]. No fields to re-read.
fn emit_alloc_byte_mem(
    bldr: &mut FunctionBuilder,
    st: &FnState,
    base: Value,
    sp: Value,
    ctx: Value,
) -> Result<Value, BailReason> {
    let flags_w = load_at(bldr, base, sp); // top = tagged flags (an int)
    let flags = emit_untag(bldr, flags_w);
    let length_w = emit_peek(bldr, base, sp, 1); // tagged length (an int)
    let length = emit_untag(bldr, length_w);
    let p = emit_region_alloc(bldr, st, ctx, sp, length, flags)?;
    // No field stores (bytes uninitialized). Collapse: pop flags (sp += 1),
    // replace length slot with ptr.
    let new_sp = bldr.ins().iadd_imm(sp, 1);
    store_at(bldr, base, new_sp, p);
    Ok(new_sp)
}

/// FAITHFUL STACK_SIZE16 (S4b): if `sp < needed`, raise StackOverflow
/// (return new_sp = ctx.handler_sp, raised = 1, packet = EXN_STACKOVERFLOW).
/// Else continue with sp unchanged. `needed` is the u16 immediate, in
/// WORDS (the same units as the interpreter's `sp` index — mod.rs:3457
/// compares `self.sp < needed` directly). Returns the (unchanged) sp on
/// the continue path.
fn emit_stack_size_check(bldr: &mut FunctionBuilder, sp: Value, ctx: Value, needed: i64) -> Value {
    let cont_blk = bldr.create_block();
    bldr.append_block_param(cont_blk, types::I64); // sp
    let over_blk = bldr.create_block();
    let needed_v = bldr.ins().iconst(types::I64, needed);
    // interp: `if self.sp < needed { StackOverflow }` (unsigned index).
    let lt = bldr.ins().icmp(IntCC::UnsignedLessThan, sp, needed_v);
    bldr.ins()
        .brif(lt, over_blk, &[], cont_blk, &[BlockArg::from(sp)]);

    // overflow: raise.
    bldr.switch_to_block(over_blk);
    bldr.seal_block(over_blk);
    emit_raise(bldr, ctx, EXN_STACKOVERFLOW);

    bldr.switch_to_block(cont_blk);
    bldr.seal_block(cont_blk);
    bldr.block_params(cont_blk)[0]
}

/// DYNAMIC call lowering (S4e): CALL_LOCAL_B / CALL_CLOSURE. The callee
/// target is a RUNTIME stack value (not a static const-pool closure), so
/// it CANNOT be a native region-to-region call; instead we trampoline
/// back into the interpreter's `do_call` via `region_interp_call`, which
/// runs the callee (interpreted, OR re-enters a registered region) and
/// hands back the result on the shared stack.
///
/// - `pop_top == true`  (CALL_CLOSURE): the closure is on TOP. The interp
///   pops it (sp += 1) BEFORE do_call, so sp_at_top_arg = sp + 1 and the
///   closure = stack[sp].
/// - `pop_top == false` (CALL_LOCAL_B): the closure is at depth `depth`
///   (peeked, NOT popped — it persists across the call), and the args are
///   the values above it; sp_at_top_arg = sp (unchanged), closure =
///   stack[sp + depth].
///
/// The trampoline returns the new sp (result on top, args collapsed by
/// the callee's own RETURN_N exactly as do_return would) and a raised
/// flag; on raised we propagate (return raised = 1 to ctx.handler_sp).
#[allow(clippy::too_many_arguments)]
fn emit_call_dynamic(
    bldr: &mut FunctionBuilder,
    st: &mut FnState,
    base: Value,
    sp: Value,
    ctx: Value,
    pop_top: bool,
    depth: i64,
) -> Result<Value, BailReason> {
    let fref = st
        .interp_call_ref
        .ok_or(BailReason::UnresolvableCallee(0))?;

    // Read the closure word + compute sp_at_top_arg, mirroring the interp.
    let (closure, sp_top_arg) = if pop_top {
        // CALL_CLOSURE: closure = stack[sp]; sp_at_top_arg = sp + 1.
        let clo = load_at(bldr, base, sp);
        let new = bldr.ins().iadd_imm(sp, 1);
        (clo, new)
    } else {
        // CALL_LOCAL_B: closure = stack[sp + depth]; sp_at_top_arg = sp.
        let idx = bldr.ins().iadd_imm(sp, depth);
        let clo = load_at(bldr, base, idx);
        (clo, sp)
    };

    let interp_ptr = load_interp_ptr(bldr, ctx);
    let call = bldr
        .ins()
        .call(fref, &[interp_ptr, base, sp_top_arg, closure, ctx]);
    let callee_sp = bldr.inst_results(call)[0];
    let raised = bldr.inst_results(call)[1];

    // brif raised -> propagate, else continue with sp = callee_sp.
    let cont_blk = bldr.create_block();
    bldr.append_block_param(cont_blk, types::I64);
    let prop_blk = bldr.create_block();
    bldr.ins().brif(
        raised,
        prop_blk,
        &[],
        cont_blk,
        &[BlockArg::from(callee_sp)],
    );

    bldr.switch_to_block(prop_blk);
    bldr.seal_block(prop_blk);
    let hsp = load_handler_sp(bldr, ctx);
    let one = bldr.ins().iconst(types::I64, 1);
    bldr.ins().return_(&[hsp, one]);

    bldr.switch_to_block(cont_blk);
    bldr.seal_block(cont_blk);
    Ok(bldr.block_params(cont_blk)[0])
}

const _: () = {
    // Compile-time link: NO_HANDLER is the boundary's ctx.handler_sp init.
    let _ = NO_HANDLER;
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn core_subset_membership() {
        // The core opcode subset includes the arithmetic / local / jump /
        // return / CALL_CONST_ADDR set...
        for b in [
            op::INSTR_CONST_0,
            op::INSTR_CONST_INT_B,
            op::INSTR_LOCAL_2,
            op::INSTR_LOCAL_B,
            op::INSTR_FIXED_ADD,
            op::INSTR_FIXED_SUB,
            op::INSTR_WORD_ADD,
            op::INSTR_LESS_EQ_SIGNED,
            op::INSTR_JUMP8_FALSE,
            op::INSTR_RETURN_B,
            op::INSTR_CALL_CONST_ADDR8_8,
            op::INSTR_INDIRECT_0,
            op::INSTR_RESET_R_1,
            // ---- S4a additions ----
            op::INSTR_SET_STACK_VAL_B,
            op::INSTR_JUMP_NEQ_LOCAL,
            op::INSTR_JUMP_NEQ_LOCAL_IND,
            op::INSTR_JUMP_TAGGED_LOCAL,
            op::INSTR_IS_TAGGED_LOCAL_B,
            op::INSTR_LOAD_ML_WORD,
            op::INSTR_LOAD_ML_BYTE,
            op::INSTR_LOAD_UNTAGGED,
            op::INSTR_STORE_ML_WORD,
            op::INSTR_STORE_UNTAGGED,
            op::INSTR_CELL_LENGTH,
            op::INSTR_CELL_FLAGS,
            op::INSTR_CONST_ADDR8_0,
            op::INSTR_CONST_ADDR8_1,
            op::INSTR_CONST_ADDR8_8,
            op::INSTR_CONST_ADDR16_8,
        ] {
            assert!(is_supported(b), "0x{b:02x} should be in the core subset");
        }
        // S4e: the DYNAMIC-call opcodes (CALL_CLOSURE / CALL_LOCAL_B) are
        // now in the subset — they trampoline into the interpreter's
        // do_call via region_interp_call (a non-static target cannot be a
        // native region-to-region call).
        for b in [op::INSTR_CALL_CLOSURE, op::INSTR_CALL_LOCAL_B] {
            assert!(
                is_supported(b),
                "0x{b:02x} should be in the core subset (dynamic-call trampoline)"
            );
        }
        // S4d: the ALLOCATION opcodes are NOW in the subset — they route a
        // heap alloc through the GC-safe region_alloc trampoline (publish
        // live_sp + GC threshold check + bump-allocate), with the post-alloc
        // operand re-read discipline (the shared stack is the GC root range
        // [sp,len), so a mid-alloc collection forwards every operand). The
        // STACK_CONTAINER_B opcode is the cheap one (no heap alloc, pure
        // stack push of N zeros + a stack-relative container pointer).
        for b in [
            op::INSTR_STACK_CONTAINER_B,
            op::INSTR_TUPLE_2,
            op::INSTR_TUPLE_3,
            op::INSTR_TUPLE_4,
            op::INSTR_TUPLE_B,
            op::INSTR_CLOSURE_B,
            op::INSTR_ALLOC_REF,
            op::INSTR_ALLOC_WORD_MEMORY,
            op::INSTR_ALLOC_BYTE_MEM,
        ] {
            assert!(
                is_supported(b),
                "0x{b:02x} should be in the core subset (S4d alloc lowering)"
            );
        }
        // STACK_CONTAINER_B does NOT route through region_alloc (no heap
        // alloc); the heap-alloc opcodes DO.
        assert!(!is_heap_alloc_opcode(op::INSTR_STACK_CONTAINER_B));
        for b in [
            op::INSTR_TUPLE_2,
            op::INSTR_TUPLE_B,
            op::INSTR_CLOSURE_B,
            op::INSTR_ALLOC_REF,
            op::INSTR_ALLOC_WORD_MEMORY,
            op::INSTR_ALLOC_BYTE_MEM,
        ] {
            assert!(is_heap_alloc_opcode(b), "0x{b:02x} is a heap alloc");
        }
        // ...and STILL EXCLUDES the genuinely-unsupported opcodes (which bail
        // the whole region to the interpreter).
        for b in [
            op::INSTR_SET_HANDLER8,
            op::INSTR_CALL_FAST_RTS1,
            op::INSTR_TAIL_B_B,
            op::INSTR_ESCAPE,
            op::INSTR_ALLOC_MUT_CLOSURE_B,
            op::INSTR_MOVE_TO_CONTAINER_B,
            op::INSTR_INDIRECT_CONTAINER_B,
        ] {
            assert!(
                !is_supported(b),
                "0x{b:02x} must NOT be in the core subset (region must bail)"
            );
        }
    }

    #[test]
    fn jump_target_arithmetic_matches_interpreter() {
        // JUMP8 at pc=4 with off=10: interp lands at (pc+2)+off = 16.
        let bc = vec![0u8; 32];
        let mut b = bc.clone();
        b[4] = op::INSTR_JUMP8;
        b[5] = 10;
        assert_eq!(jump_target(&b, 4, op::INSTR_JUMP8, 2), Some(16));
        // JUMP_BACK8 at pc=20 with off=8: interp lands at pc - off = 12.
        let mut b2 = bc;
        b2[20] = op::INSTR_JUMP_BACK8;
        b2[21] = 8;
        assert_eq!(jump_target(&b2, 20, op::INSTR_JUMP_BACK8, 2), Some(12));
    }

    #[test]
    fn fused_jump_target_arithmetic_matches_interpreter() {
        // JUMP_NEQ_LOCAL is a 3-immediate op [depth, want, off]; total_len=4.
        // The interp fetches all 3 immediates (pc now at after = pc+4) then,
        // on mismatch, pc_offset_signed(off) => target = after + off.
        let mut b = vec![0u8; 64];
        b[8] = op::INSTR_JUMP_NEQ_LOCAL;
        b[9] = 2; // depth
        b[10] = 5; // want
        b[11] = 12; // off
        // total_len for JUMP_NEQ_LOCAL = 1 opcode + 3 immediates = 4.
        assert_eq!(
            jump_target(&b, 8, op::INSTR_JUMP_NEQ_LOCAL, 4),
            Some(8 + 4 + 12)
        );
        // _IND uses the same operand shape.
        b[8] = op::INSTR_JUMP_NEQ_LOCAL_IND;
        assert_eq!(
            jump_target(&b, 8, op::INSTR_JUMP_NEQ_LOCAL_IND, 4),
            Some(8 + 4 + 12)
        );
        // JUMP_TAGGED_LOCAL is 2-immediate [depth, off]; total_len=3;
        // target = after(=pc+3) + off.
        let mut c = vec![0u8; 64];
        c[16] = op::INSTR_JUMP_TAGGED_LOCAL;
        c[17] = 3; // depth
        c[18] = 7; // off
        assert_eq!(
            jump_target(&c, 16, op::INSTR_JUMP_TAGGED_LOCAL, 3),
            Some(16 + 3 + 7)
        );
    }
}
