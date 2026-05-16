//! PolyML bytecode interpreter.
//!
//! Faithful port of the dispatch shape in
//! `vendor/polyml/libpolyml/bytecode.cpp`. The stack grows **down**
//! (matching PolyML): `push` decrements the stack pointer, `pop`
//! increments it. `sp[N]` peeks N deep (0 = top).
//!
//! ## PC representation
//!
//! PC is a raw `*const u8` pointer into a code object's instruction
//! bytes. This is necessary because:
//!
//! - Calls move PC between code objects (each closure points at its
//!   own code's bytes).
//! - PC-relative addressing (`CONST_ADDR8_8`, `CALL_CONST_ADDR8_8`)
//!   computes constant-pool offsets via raw byte arithmetic — `pc +
//!   imm` must land in the constant pool that immediately follows the
//!   code bytes in the same heap object.
//!
//! ## Calling convention (per bytecode.cpp:411-424)
//!
//! ```text
//! Before CALL: stack top is [closure, arg_last, ..., arg_first]
//!                            ^ sp
//!
//! CALL pops closure, pushes return-PC, pushes closure:
//!
//! After CALL:  stack top is [closure, retPC, arg_last, ..., arg_first]
//!                            ^ sp
//!
//! Callee runs, possibly pushing its own locals on top.
//! ```
//!
//! On RETURN_N (bytecode.cpp:454-465):
//!
//! ```text
//!   result = pop()           ; top
//!   sp++                     ; drop closure
//!   pc = pop().codeAddr      ; restore return PC
//!   sp += N                  ; drop N args
//!   push(result)
//! ```
//!
//! ## Top-level return sentinel
//!
//! The initial return PC is set to **null** by `enter_top_level`.
//! When `RETURN_*` would restore PC to null, the interpreter yields
//! `StepResult::Returned(value)` instead of jumping.
//!
//! ## Scope
//!
//! Implemented:
//! - ALU: const_{0..4,10,int_b,int_w}, fixed_*, word_*, comparisons
//! - Stack: local_*, indirect_*, reset_*, reset_r_*
//! - Control: jump{8,16}{,_back,_true,_false}, no_op
//! - Calls: `call_closure`, `call_const_addr8_8`, `call_const_addr16_8`,
//!   `call_const_addr8_{0,1}`, `call_local_b`
//! - Constants from pool: `const_addr8_8`, `const_addr16_8`,
//!   `const_addr8_{0,1}`
//! - Returns: `return_{1,2,3,b,w}`
//!
//! Not yet implemented (will trap with `Unimplemented`):
//! - Allocation (`tuple_*`, `alloc_*`)
//! - Exceptions (`push_handler`, `raise_ex`, `set_handler*`, `delete_handler`)
//! - Tail calls (`tail_b_b`)
//! - Heap mutation (`store_ml_word`, `store_ml_byte`)
//! - RTS calls (`call_fast_rts*`)
//! - Floats / extended opcodes
//! - Closure construction (`closure_b`, `alloc_mut_closure_b`)
//! - `ldexc`, `lock`, etc.

// Interpreter-wide allows: the signed/unsigned reinterpretation of
// PolyWord bits is intentional (matches PolyML's `UNTAGGED` casting
// pattern in bytecode.cpp). Pointer-alignment casts in the
// PC-relative const loaders are safe because we always use
// `read_unaligned()`, which clippy can't track.
#![allow(clippy::cast_sign_loss)]
#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::manual_div_ceil)]
#![allow(clippy::cast_ptr_alignment)]
#![allow(clippy::similar_names)]
#![allow(clippy::wildcard_imports)]

pub mod opcodes;

use std::sync::Arc;

use crate::poly_word::PolyWord;
use crate::rts::{RtsContext, RtsFn, RtsTable};
use crate::space::{MemorySpace, SpaceKind};
use thiserror::Error;

/// Result of one (`step`) or many (`run`) interpreter steps.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StepResult {
    /// Keep going.
    Continue,
    /// A `return_*` opcode fired with a null return address (the
    /// top-level sentinel). The value carried is the popped result.
    Returned(PolyWord),
    /// The interpreter hit an opcode it doesn't know yet. PC has been
    /// rolled back to point AT the unknown op (or the ESCAPE prefix
    /// for extended opcodes — `extended` is true in that case).
    Unimplemented { op: u8, extended: bool },
}

#[derive(Debug, Clone, Error)]
pub enum InterpError {
    #[error("stack overflow")]
    StackOverflow,
    #[error("stack underflow")]
    StackUnderflow,
    #[error("pc out of bounds (offset {offset} into segment of {size} bytes)")]
    PcOutOfBounds { offset: usize, size: usize },
    #[error("division by zero")]
    DivByZero,
    #[error("call to non-closure value: {0:?}")]
    NotAClosure(PolyWord),
    #[error("interpreter has no allocation space attached")]
    NoAllocator,
    #[error("unhandled exception (no handler in scope)")]
    UnhandledException,
    #[error("CALL_FAST_RTS{n} on an unresolved entry point (token=0)")]
    UnresolvedRts { n: usize },
    #[error("CALL_FAST_RTS{op_arity} on RTS function {name} of arity {fn_arity}")]
    RtsArityMismatch {
        name: &'static str,
        op_arity: usize,
        fn_arity: usize,
    },
}

/// A bytecode interpreter operating on PolyML code objects.
///
/// The PC is a raw `*const u8` pointer; the interpreter does not own
/// the code bytes. For tests, `from_bytes` allocates a backing `Vec<u8>`
/// stored in `_owned_code` so the pointer stays valid for the
/// interpreter's lifetime.
pub struct Interpreter {
    /// Backing storage for the ML stack. Grows down.
    stack: Vec<PolyWord>,
    /// Index of the topmost live element. `sp == stack.len()` means
    /// "empty" (the SP is just past the end, ready for the next push
    /// to decrement-then-write).
    sp: usize,
    /// Pointer to the next byte to fetch.
    pc: *const u8,
    /// Start of the currently-executing code object's byte segment
    /// (for bounds checking and PC-rollback on Unimplemented).
    code_start: *const u8,
    /// One past the end of the code segment (exclusive bound).
    code_end: *const u8,
    /// Per-call side-stack of caller code segment bounds. PolyML's
    /// own interpreter doesn't track these because it doesn't
    /// bounds-check; we use them so safety-net errors surface
    /// instead of out-of-bounds reads.
    /// Entries are (code_start, code_end) pushed on every CALL and
    /// popped on every RETURN.
    frames: Vec<(*const u8, *const u8)>,
    /// Bump-allocation region for objects created at runtime
    /// (closures, tuples, refs). `None` means the interpreter will
    /// trap `InterpError::NoAllocator` on any allocation op.
    alloc_space: Option<MemorySpace>,
    /// "Handler register" — index into `stack` where the most-recent
    /// exception-handler frame sits. `stack.len()` (past-the-end)
    /// means no handler in scope.
    handler_sp: usize,
    /// Current exception packet (set by RAISE_EX, read by LDEXC).
    /// `None` means no exception has been raised yet.
    exception_packet: Option<PolyWord>,
    /// RTS function table — used to dispatch CALL_FAST_RTS<N> opcodes.
    /// `Arc` so it can be shared between interpreter instances (e.g.
    /// threads).
    rts: Arc<RtsTable>,
    /// For test-built interpreters: owns the code bytes so the PC
    /// pointer stays valid.
    _owned_code: Option<Vec<u8>>,
}

impl Interpreter {
    /// Build an interpreter from an owned byte slice. PC starts at
    /// byte 0. The bytes are NOT a real PolyML code object — there's
    /// no constant pool, no length word — so PC-relative addressing
    /// opcodes will produce undefined results. Use this constructor
    /// for hand-crafted ALU/control-flow tests only.
    #[must_use]
    pub fn from_bytes(stack_capacity: usize, code: Vec<u8>) -> Self {
        let code = code.into_boxed_slice().into_vec(); // ensure stable alloc
        let start: *const u8 = code.as_ptr();
        // SAFETY: `code` is non-empty in normal use; for empty input
        // start == end, which is a valid (immediately-EOF) state.
        let end: *const u8 = unsafe { start.add(code.len()) };
        Self {
            stack: vec![PolyWord::ZERO; stack_capacity],
            sp: stack_capacity,
            pc: start,
            code_start: start,
            code_end: end,
            frames: Vec::new(),
            alloc_space: None,
            handler_sp: stack_capacity, // past-the-end = no handler
            exception_packet: None,
            rts: Arc::new(RtsTable::empty()),
            _owned_code: Some(code),
        }
    }

    /// Build an interpreter that will execute the code bytes of an
    /// existing PolyML code object. Reads the length word and the
    /// trailing-offset to figure out where the bytes end (i.e., where
    /// the constant pool begins).
    ///
    /// # Safety
    /// `code_obj` must point at a valid, fully-initialised code
    /// object as laid out by [`crate::loader`]. The object must
    /// remain live for the interpreter's lifetime.
    #[must_use]
    pub unsafe fn from_code_object(stack_capacity: usize, code_obj: *const PolyWord) -> Self {
        use crate::length_word;
        // SAFETY: caller upholds.
        let (consts_start, _consts_count) = unsafe { length_word::const_segment_for_code(code_obj) };
        let start: *const u8 = code_obj.cast::<u8>();
        // Constant pool begins at consts_start; bytes end one word
        // before that (the const-count word). For our bounds, accept
        // bytes up to consts_start cast to u8* — the count word is
        // word-aligned data that compiled code shouldn't try to
        // execute, but it's harmless to allow PC there.
        let end: *const u8 = consts_start.cast::<u8>();
        Self {
            stack: vec![PolyWord::ZERO; stack_capacity],
            sp: stack_capacity,
            pc: start,
            code_start: start,
            code_end: end,
            frames: Vec::new(),
            alloc_space: None,
            handler_sp: stack_capacity,
            exception_packet: None,
            rts: Arc::new(RtsTable::empty()),
            _owned_code: None,
        }
    }

    /// Attach an RTS table. Builder pattern.
    #[must_use]
    pub fn with_rts(mut self, rts: Arc<RtsTable>) -> Self {
        self.rts = rts;
        self
    }

    /// Attach an allocation space. The interpreter will bump-allocate
    /// new objects (closures, tuples, refs) from this space. Sized
    /// once at attach time — runtime growth is a future concern.
    ///
    /// Builder pattern; returns the interpreter for chaining.
    #[must_use]
    pub fn with_alloc_space(mut self, space: MemorySpace) -> Self {
        self.alloc_space = Some(space);
        self
    }

    /// Convenience: attach a freshly-created mutable allocation space
    /// of the given word capacity.
    #[must_use]
    pub fn with_default_alloc_space(self, capacity_words: usize) -> Self {
        self.with_alloc_space(MemorySpace::new(capacity_words, SpaceKind::Mutable))
    }

    // ---- Inspection -----------------------------------------------------

    #[must_use]
    pub fn stack_height(&self) -> usize {
        self.stack.len() - self.sp
    }

    /// Number of saved frames on the call side-stack. Useful for
    /// detecting CALL / RETURN events during external tracing.
    #[must_use]
    pub fn frames_depth(&self) -> usize {
        self.frames.len()
    }

    /// Byte offset of the PC from the start of the current code
    /// segment.
    #[must_use]
    pub fn pc_offset(&self) -> usize {
        // SAFETY: pc and code_start are both within (or one past) the
        // same allocation by construction.
        unsafe { self.pc.offset_from(self.code_start) as usize }
    }

    /// Test/debug API: push a value onto the stack.
    #[doc(hidden)]
    pub fn test_seed_top(&mut self, w: PolyWord) {
        let _ = self.push(w);
    }

    /// Test/debug API: push a synthetic return-to-top sentinel onto
    /// the stack so the interpreter can be used inside a hand-built
    /// call frame.
    ///
    /// Use this after `test_seed_top`s for args + closure to simulate
    /// being called: the stack layout becomes `[closure, retPC=null,
    /// args...]`. When the callee's RETURN fires, it'll find
    /// retPC=null and yield `Returned`.
    #[doc(hidden)]
    pub fn test_seed_return_sentinel(&mut self) {
        // retPC = null pointer encoded as a PolyWord bit pattern.
        let _ = self.push(PolyWord::from_bits(0));
    }

    // ---- Stack primitives ----------------------------------------------

    fn push(&mut self, w: PolyWord) -> Result<(), InterpError> {
        if self.sp == 0 {
            return Err(InterpError::StackOverflow);
        }
        self.sp -= 1;
        self.stack[self.sp] = w;
        Ok(())
    }

    fn pop(&mut self) -> Result<PolyWord, InterpError> {
        if self.sp >= self.stack.len() {
            return Err(InterpError::StackUnderflow);
        }
        let w = self.stack[self.sp];
        self.sp += 1;
        Ok(w)
    }

    fn peek(&self, depth: usize) -> Result<PolyWord, InterpError> {
        let idx = self
            .sp
            .checked_add(depth)
            .filter(|i| *i < self.stack.len())
            .ok_or(InterpError::StackUnderflow)?;
        Ok(self.stack[idx])
    }

    // ---- PC primitives -------------------------------------------------

    fn pc_in_bounds(&self) -> bool {
        // null code_start = bounds disabled (e.g. post-exception
        // unwind, where the new PC may be in any code object we
        // don't track from here).
        if self.code_start.is_null() {
            return true;
        }
        // We allow pc == code_end (about to step past the end is
        // benign until we try to fetch).
        self.pc >= self.code_start && self.pc <= self.code_end
    }

    fn pc_offset_for_err(&self) -> InterpError {
        // SAFETY: code_end - code_start is the segment size; ptr math
        // is within one allocation by construction.
        let size = unsafe { self.code_end.offset_from(self.code_start) as usize };
        let offset = unsafe { self.pc.offset_from(self.code_start) as usize };
        InterpError::PcOutOfBounds { offset, size }
    }

    fn fetch_u8(&mut self) -> Result<u8, InterpError> {
        if self.pc >= self.code_end {
            return Err(self.pc_offset_for_err());
        }
        // SAFETY: bounds-checked above.
        let b = unsafe { *self.pc };
        // SAFETY: bumping a pointer to within or one past the
        // allocation is well-defined.
        self.pc = unsafe { self.pc.add(1) };
        Ok(b)
    }

    fn fetch_u16_le(&mut self) -> Result<u16, InterpError> {
        let lo = self.fetch_u8()?;
        let hi = self.fetch_u8()?;
        Ok(u16::from_le_bytes([lo, hi]))
    }

    /// Add a signed offset to PC. Used by jumps and PC-relative
    /// constant addressing.
    fn pc_offset_signed(&mut self, delta: isize) -> Result<(), InterpError> {
        // SAFETY: bounds checked after the offset; we deliberately do
        // not check before so backward arithmetic out of range surfaces
        // as PcOutOfBounds.
        self.pc = unsafe { self.pc.offset(delta) };
        if !self.pc_in_bounds() {
            // Roll back so the error message has a sensible offset.
            // Actually, leave PC where it is and let bounds reporting
            // reflect the failure.
            return Err(self.pc_offset_for_err());
        }
        Ok(())
    }

    // ---- Run / step ----------------------------------------------------

    /// Run until something interesting happens: a top-level return, an
    /// unimplemented opcode, or an error.
    pub fn run(&mut self) -> Result<StepResult, InterpError> {
        loop {
            match self.step()? {
                StepResult::Continue => {}
                r => return Ok(r),
            }
        }
    }

    /// Execute a single instruction.
    #[allow(clippy::too_many_lines)]
    #[allow(clippy::wildcard_imports)]
    pub fn step(&mut self) -> Result<StepResult, InterpError> {
        use opcodes::*;

        let opcode_pc = self.pc;
        let op = self.fetch_u8()?;
        if crate::rts::is_traced() {
            eprintln!(
                "  [{:5}] op=0x{op:02x} sp_depth={} top={:?}",
                self.pc_offset() - 1,
                self.stack_height(),
                if self.sp < self.stack.len() { Some(self.stack[self.sp]) } else { None }
            );
        }
        match op {
            // ----- No-op
            INSTR_NO_OP => Ok(StepResult::Continue),

            // ----- Constants
            INSTR_CONST_0 => self.push_continue(PolyWord::tagged(0)),
            INSTR_CONST_1 => self.push_continue(PolyWord::tagged(1)),
            INSTR_CONST_2 => self.push_continue(PolyWord::tagged(2)),
            INSTR_CONST_3 => self.push_continue(PolyWord::tagged(3)),
            INSTR_CONST_4 => self.push_continue(PolyWord::tagged(4)),
            INSTR_CONST_10 => self.push_continue(PolyWord::tagged(10)),
            INSTR_CONST_INT_B => {
                let n = isize::from(self.fetch_u8()?);
                self.push_continue(PolyWord::tagged(n))
            }
            INSTR_CONST_INT_W => {
                let raw = self.fetch_u16_le()?;
                self.push_continue(PolyWord::tagged(
                    isize::try_from(raw).expect("u16 fits in isize"),
                ))
            }

            // ----- Local access (push sp[N])
            INSTR_LOCAL_0 => self.dup_local(0),
            INSTR_LOCAL_1 => self.dup_local(1),
            INSTR_LOCAL_2 => self.dup_local(2),
            INSTR_LOCAL_3 => self.dup_local(3),
            INSTR_LOCAL_4 => self.dup_local(4),
            INSTR_LOCAL_5 => self.dup_local(5),
            INSTR_LOCAL_6 => self.dup_local(6),
            INSTR_LOCAL_7 => self.dup_local(7),
            INSTR_LOCAL_8 => self.dup_local(8),
            INSTR_LOCAL_9 => self.dup_local(9),
            INSTR_LOCAL_10 => self.dup_local(10),
            INSTR_LOCAL_11 => self.dup_local(11),
            INSTR_LOCAL_12 => self.dup_local(12),
            INSTR_LOCAL_13 => self.dup_local(13),
            INSTR_LOCAL_14 => self.dup_local(14),
            INSTR_LOCAL_15 => self.dup_local(15),
            INSTR_LOCAL_B => {
                let n = self.fetch_u8()? as usize;
                self.dup_local(n)
            }
            INSTR_LOCAL_W => {
                let n = self.fetch_u16_le()? as usize;
                self.dup_local(n)
            }

            // ----- Allocation
            INSTR_ALLOC_REF => self.do_alloc_ref(),
            INSTR_TUPLE_2 => self.do_tuple(2),
            INSTR_TUPLE_3 => self.do_tuple(3),
            INSTR_TUPLE_4 => self.do_tuple(4),
            INSTR_TUPLE_B => {
                let n = self.fetch_u8()? as usize;
                self.do_tuple(n)
            }
            INSTR_CLOSURE_B => {
                let n = self.fetch_u8()? as usize;
                self.do_create_closure(n)
            }
            INSTR_ALLOC_MUT_CLOSURE_B => {
                let n = self.fetch_u8()? as usize;
                self.do_alloc_mut_closure(n)
            }
            INSTR_MOVE_TO_MUT_CLOSURE_B => {
                let slot = self.fetch_u8()? as usize;
                self.do_move_to_mut_closure(slot)
            }
            INSTR_LOCK => self.clear_mutable_bit(false),
            INSTR_CLEAR_MUTABLE => self.clear_mutable_bit(true),

            // ----- Cell introspection (length / flag-byte of a heap obj)
            INSTR_CELL_LENGTH => {
                let v = self.peek(0)?;
                let p = v.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid object reference
                let lw = unsafe { MemorySpace::length_word_of(p) };
                let len = crate::length_word::length_of(lw);
                self.pop()?;
                self.push_continue(PolyWord::tagged(len as isize))
            }
            INSTR_CELL_FLAGS => {
                let v = self.peek(0)?;
                let p = v.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid object reference
                let lw = unsafe { MemorySpace::length_word_of(p) };
                let f = crate::length_word::flags_of(lw);
                self.pop()?;
                self.push_continue(PolyWord::tagged(isize::from(f)))
            }

            // ----- Thread identity (stubbed for single-threaded interpreter)
            //
            // bytecode.cpp:1167-1168: returns `taskData->threadObject`
            // — a heap-allocated record with thread state fields. The
            // bootstrap dispatcher reads various INDIRECT offsets from
            // it; without a real one we allocate an 8-word zeroed
            // placeholder so those reads don't trap.
            //
            // TODO: real thread state once we have a scheduler.
            INSTR_GET_THREAD_ID => {
                let tid = self.alloc_stub_thread_object()?;
                self.push_continue(tid)
            }

            // ----- RTS calls (stubbed — drops args, returns tagged 0)
            //
            // The compiler emits these as fast paths for builtin C
            // functions (file I/O, arbitrary precision, etc.). The
            // stub on top of the stack is an object whose first word
            // is a raw C function pointer. We don't have an RTS yet,
            // so just consume the args and return zero.
            //
            // This WILL produce incorrect results when actually used.
            // It exists so we can see what opcodes come up further
            // down the bootstrap path.
            INSTR_CALL_FAST_RTS0 => self.rts_call(0),
            INSTR_CALL_FAST_RTS1 => self.rts_call(1),
            INSTR_CALL_FAST_RTS2 => self.rts_call(2),
            INSTR_CALL_FAST_RTS3 => self.rts_call(3),
            INSTR_CALL_FAST_RTS4 => self.rts_call(4),
            INSTR_CALL_FAST_RTS5 => self.rts_call(5),

            // ----- Tail call
            //
            // bytecode.cpp:387-395 + the TAIL_CALL label. The compiler
            // emits `tail_b_b T, L` where:
            //   T = tail-count = number of items at top that constitute
            //       the new frame (= 1 placeholder + 1 closure + N args)
            //   L = skip-count = number of stack slots to "drop" between
            //       the new frame items and the position where they get
            //       moved to (= current function's locals + 1 for its
            //       own closure slot)
            //
            // The copy moves [sp, sp+T) into [sp+L, sp+L+T), overwriting
            // any locals + the current function's closure slot. The
            // current function's retPC (which sits just below the
            // closure slot) is preserved unchanged — the tail-callee
            // inherits it as its own retPC.
            INSTR_TAIL_B_B => {
                let tail_count = self.fetch_u8()? as usize;
                let skip = self.fetch_u8()? as usize;
                self.do_tail_call(tail_count, skip)?;
                Ok(StepResult::Continue)
            }

            // ----- Heap load/store
            //
            // Load: pop index, peek base, replace top with base[index].
            // Store: pop value, pop index, peek base, base[index]=val,
            //        replace base on top with TAGGED(0).
            INSTR_LOAD_ML_WORD => {
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                let p = base.as_ptr::<PolyWord>();
                // SAFETY: caller emits valid offsets
                let v = unsafe { *p.add(index) };
                self.pop()?;
                self.push_continue(v)
            }
            INSTR_LOAD_ML_BYTE => {
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                let p = base.as_ptr::<u8>();
                // SAFETY: caller emits valid offsets
                let b = unsafe { *p.add(index) };
                self.pop()?;
                self.push_continue(PolyWord::tagged(isize::from(b)))
            }
            INSTR_LOAD_UNTAGGED => {
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                let p = base.as_ptr::<PolyWord>();
                // SAFETY: caller emits valid offsets
                let raw = unsafe { *p.add(index) };
                self.pop()?;
                // Re-tag: untag the raw bits as if they were already
                // a numeric value to be tagged.
                self.push_continue(PolyWord::tagged(raw.0 as isize))
            }
            INSTR_STORE_ML_WORD => {
                let to_store = self.pop()?;
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                let p = base.as_ptr::<PolyWord>().cast_mut();
                // SAFETY: caller emits valid offsets; base is mutable
                unsafe { p.add(index).write(to_store) };
                self.pop()?;
                self.push_continue(PolyWord::tagged(0))
            }
            INSTR_STORE_ML_BYTE => {
                let to_store = self.pop()?.untag() as u8;
                let index = self.pop()?.untag() as usize;
                let base = self.peek(0)?;
                let p = base.as_ptr::<u8>().cast_mut();
                // SAFETY: caller emits valid offsets; base is mutable
                unsafe { p.add(index).write(to_store) };
                self.pop()?;
                self.push_continue(PolyWord::tagged(0))
            }

            // ----- Exception handling
            //
            // bytecode.cpp:338-374 (push/set/delete) + 486-498 (raise)
            // + 569 (ldexc). The model is a singly-linked chain on the
            // ML stack: each handler frame is [handler_pc, old_handler_sp]
            // pushed by PUSH_HANDLER + SET_HANDLER; `handler_sp` points
            // at the top slot of the most-recent frame.
            INSTR_PUSH_HANDLER => {
                // Save the OLD handler register on the stack.
                self.push_continue(PolyWord::from_bits(self.handler_sp))
            }
            INSTR_SET_HANDLER8 => {
                let off = self.fetch_u8()? as usize;
                // SAFETY: caller emits valid in-segment offset
                let entry = unsafe { self.pc.add(off) };
                self.push(PolyWord::from_bits(entry as usize))?;
                self.handler_sp = self.sp;
                Ok(StepResult::Continue)
            }
            INSTR_SET_HANDLER16 => {
                let off = self.fetch_u16_le()? as usize;
                let entry = unsafe { self.pc.add(off) };
                self.push(PolyWord::from_bits(entry as usize))?;
                self.handler_sp = self.sp;
                Ok(StepResult::Continue)
            }
            INSTR_DELETE_HANDLER => {
                // bytecode.cpp:366-373
                //   u = pop result
                //   sp = handler_register
                //   sp++ (skip handler_pc slot)
                //   handler_register = sp's slot (old_handler_sp)
                //   *sp = u (replace old_handler_sp slot with result)
                let result = self.pop()?;
                self.sp = self.handler_sp;
                self.sp += 1; // skip handler_pc slot
                let old_handler = self.stack[self.sp];
                self.handler_sp = old_handler.0;
                self.stack[self.sp] = result;
                Ok(StepResult::Continue)
            }
            INSTR_LDEXC => {
                // Push the current exception packet (zero if none).
                let pkt = self
                    .exception_packet
                    .unwrap_or_else(|| PolyWord::tagged(0));
                self.push_continue(pkt)
            }
            INSTR_RAISE_EX => {
                // bytecode.cpp:486-498. Peek (don't pop) the exception
                // on top, record it, then reset SP to the handler frame
                // and jump to the saved handler PC.
                let exn = self.peek(0)?;
                self.exception_packet = Some(exn);
                if self.handler_sp >= self.stack.len() {
                    return Err(InterpError::UnhandledException);
                }
                self.sp = self.handler_sp;
                let handler_pc_word = self.stack[self.sp];
                self.sp += 1; // skip handler_pc slot; next slot is old_handler_sp
                self.pc = handler_pc_word.0 as *const u8;
                // We may have unwound across call frames into a
                // different code object. Without per-handler bounds
                // tracking, disable bounds checking until the next
                // call (which will refresh code_start/code_end).
                self.code_start = std::ptr::null();
                self.code_end = std::ptr::null();
                // Drop any callee frames we abandoned. This is
                // conservative — a true implementation would record
                // the frames-depth at SET_HANDLER and roll back to
                // exactly that. For now: clear all, relying on the
                // null-bounds bypass.
                self.frames.clear();
                Ok(StepResult::Continue)
            }

            // ----- Fused stack/heap access opcodes (peephole-optimised
            // sequences emitted by the PolyML compiler).
            //
            // INDIRECT_LOCAL_B0/B1/BB and INDIRECT_0_LOCAL_0 read a
            // closure-like object N words deep on the stack, then
            // fetch field [0/1] (or arbitrary) of it onto the stack.
            INSTR_INDIRECT_LOCAL_B0 => {
                let depth = self.fetch_u8()? as usize;
                let u = self.peek(depth)?;
                let p = u.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid object reference
                let val = unsafe { *p };
                self.push_continue(val)
            }
            INSTR_INDIRECT_LOCAL_B1 => {
                let depth = self.fetch_u8()? as usize;
                let u = self.peek(depth)?;
                let p = u.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid object reference
                let val = unsafe { *p.add(1) };
                self.push_continue(val)
            }
            INSTR_INDIRECT_0_LOCAL_0 => {
                let u = self.peek(0)?;
                let p = u.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid object reference
                let val = unsafe { *p };
                self.push_continue(val)
            }
            INSTR_INDIRECT_LOCAL_BB => {
                let depth = self.fetch_u8()? as usize;
                let slot = self.fetch_u8()? as usize;
                let u = self.peek(depth)?;
                let p = u.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid object reference + slot
                let val = unsafe { *p.add(slot) };
                self.push_continue(val)
            }
            INSTR_IS_TAGGED_LOCAL_B => {
                let depth = self.fetch_u8()? as usize;
                let u = self.peek(depth)?;
                self.push_continue(if u.is_tagged() {
                    PolyWord::tagged(1)
                } else {
                    PolyWord::tagged(0)
                })
            }
            // Compare a local with a small tagged constant; jump if NOT
            // equal. Immediates: pc[0]=depth, pc[1]=tagged_constant,
            // pc[2]=jump_offset_when_not_equal.
            INSTR_JUMP_NEQ_LOCAL => {
                let depth = self.fetch_u8()? as usize;
                let want = self.fetch_u8()?;
                let off = self.fetch_u8()? as usize;
                let u = self.peek(depth)?;
                if u.is_tagged() && u.untag() == isize::from(want) {
                    // fall through (equal)
                } else {
                    self.pc_offset_signed(off as isize)?;
                }
                Ok(StepResult::Continue)
            }
            // Same but reads field 0 of the local first (union-tag test).
            INSTR_JUMP_NEQ_LOCAL_IND => {
                let depth = self.fetch_u8()? as usize;
                let want = self.fetch_u8()?;
                let off = self.fetch_u8()? as usize;
                let local = self.peek(depth)?;
                let p = local.as_ptr::<PolyWord>();
                // SAFETY: caller emitted a valid tuple reference
                let u = unsafe { *p };
                if u.is_tagged() && u.untag() == isize::from(want) {
                    // fall through
                } else {
                    self.pc_offset_signed(off as isize)?;
                }
                Ok(StepResult::Continue)
            }
            // Peek sp[depth]; if tagged, jump.
            INSTR_JUMP_TAGGED_LOCAL => {
                let depth = self.fetch_u8()? as usize;
                let off = self.fetch_u8()? as usize;
                let u = self.peek(depth)?;
                if u.is_tagged() {
                    self.pc_offset_signed(off as isize)?;
                }
                Ok(StepResult::Continue)
            }

            // SET_STACK_VAL_B: pop value, write into sp[imm - 1].
            // Note the "-1" — bytecode.cpp:613 reads `sp[*pc-1] = u`.
            INSTR_SET_STACK_VAL_B => {
                let idx = self.fetch_u8()? as usize;
                let u = self.pop()?;
                // sp[idx - 1] — we read with depth (idx - 1). If idx is 0
                // this would wrap; trust the compiler not to emit that.
                let target = self
                    .sp
                    .checked_add(idx.checked_sub(1).ok_or(InterpError::StackUnderflow)?)
                    .filter(|i| *i < self.stack.len())
                    .ok_or(InterpError::StackUnderflow)?;
                self.stack[target] = u;
                Ok(StepResult::Continue)
            }

            // ----- Closure field access
            INSTR_INDIRECT_CLOSURE_B0 => self.do_indirect_closure(0),
            INSTR_INDIRECT_CLOSURE_B1 => self.do_indirect_closure(1),
            INSTR_INDIRECT_CLOSURE_B2 => self.do_indirect_closure(2),
            INSTR_INDIRECT_CLOSURE_BB => {
                // depth + slot, both as 1-byte immediates
                let depth = self.fetch_u8()? as usize;
                let slot = self.fetch_u8()? as usize;
                let closure_word = self.peek(depth)?;
                let p = closure_word.as_ptr::<PolyWord>();
                // SAFETY: caller emitted valid slot index
                let val = unsafe { *p.add(1 + slot) };
                self.push_continue(val)
            }

            // ----- Indirect (heap field read)
            INSTR_INDIRECT_0 => self.indirect(0),
            INSTR_INDIRECT_1 => self.indirect(1),
            INSTR_INDIRECT_2 => self.indirect(2),
            INSTR_INDIRECT_3 => self.indirect(3),
            INSTR_INDIRECT_4 => self.indirect(4),
            INSTR_INDIRECT_5 => self.indirect(5),
            INSTR_INDIRECT_B => {
                let n = self.fetch_u8()? as usize;
                self.indirect(n)
            }

            // ----- PC-relative constants
            //
            // bytecode.cpp:529-535 + 442-: constants live AFTER the
            // bytecode in the same code object, so all PC-relative
            // offsets are forward (positive). Upstream treats the
            // immediate bytes as `unsigned char` (promoted to int),
            // so we match: read as `usize`, add forward.
            //
            // Formulas (after the handler has fetched its immediates,
            // making our `self.pc` equivalent to the upstream `pc + N`
            // where N is the number of immediate bytes):
            //
            //   const_addr8_0     val = (PolyWord*)(self.pc + imm)[3]
            //   const_addr8_1     val = (PolyWord*)(self.pc + imm)[4]
            //   const_addr8_8     val = (PolyWord*)(self.pc + imm1)[imm2 + 3]
            //   const_addr16_8    val = (PolyWord*)(self.pc + imm1_16)[imm2 + 3]
            INSTR_CONST_ADDR8_0 => {
                let imm = self.fetch_u8()? as usize;
                let w = unsafe { self.read_pc_const(imm, 3) };
                self.push_continue(w)
            }
            INSTR_CONST_ADDR8_1 => {
                let imm = self.fetch_u8()? as usize;
                let w = unsafe { self.read_pc_const(imm, 4) };
                self.push_continue(w)
            }
            INSTR_CONST_ADDR8_8 => {
                let imm1 = self.fetch_u8()? as usize;
                let imm2 = self.fetch_u8()? as usize;
                let w = unsafe { self.read_pc_const(imm1, imm2 + 3) };
                self.push_continue(w)
            }
            INSTR_CONST_ADDR16_8 => {
                let imm1 = self.fetch_u16_le()? as usize;
                let imm2 = self.fetch_u8()? as usize;
                let w = unsafe { self.read_pc_const(imm1, imm2 + 3) };
                self.push_continue(w)
            }

            // ----- Function calls
            //
            // call_closure: pop closure from top, save retPC, push
            // closure back, jump to closure's first word (which is
            // the code address).
            INSTR_CALL_CLOSURE => {
                let closure = self.pop()?;
                self.do_call(closure)?;
                Ok(StepResult::Continue)
            }
            // call_const_addr*: load a closure from the const pool
            // (same formula as const_addr*) then dispatch as CALL_CLOSURE.
            INSTR_CALL_CONST_ADDR8_0 => {
                let imm = self.fetch_u8()? as usize;
                let closure = unsafe { self.read_pc_const(imm, 3) };
                self.do_call(closure)?;
                Ok(StepResult::Continue)
            }
            INSTR_CALL_CONST_ADDR8_1 => {
                let imm = self.fetch_u8()? as usize;
                let closure = unsafe { self.read_pc_const(imm, 4) };
                self.do_call(closure)?;
                Ok(StepResult::Continue)
            }
            INSTR_CALL_CONST_ADDR8_8 => {
                let imm1 = self.fetch_u8()? as usize;
                let imm2 = self.fetch_u8()? as usize;
                let closure = unsafe { self.read_pc_const(imm1, imm2 + 3) };
                self.do_call(closure)?;
                Ok(StepResult::Continue)
            }
            INSTR_CALL_CONST_ADDR16_8 => {
                let imm1 = self.fetch_u16_le()? as usize;
                let imm2 = self.fetch_u8()? as usize;
                let closure = unsafe { self.read_pc_const(imm1, imm2 + 3) };
                self.do_call(closure)?;
                Ok(StepResult::Continue)
            }
            INSTR_CALL_LOCAL_B => {
                // closure is at sp[N]; treat the same as call_closure
                // after copying the value to top (and removing the
                // source slot? No — call_closure pops, so we push the
                // copy and let pop handle it).
                let n = self.fetch_u8()? as usize;
                let closure = self.peek(n)?;
                self.do_call(closure)?;
                Ok(StepResult::Continue)
            }

            // ----- Jumps
            INSTR_JUMP8 => {
                let off = self.fetch_u8()? as usize;
                self.pc_offset_signed(off as isize)?;
                Ok(StepResult::Continue)
            }
            INSTR_JUMP_BACK8 => {
                let off = self.fetch_u8()? as usize;
                self.pc_offset_signed(-((off as isize) + 1))?;
                Ok(StepResult::Continue)
            }
            INSTR_JUMP16 => {
                let off = self.fetch_u16_le()? as usize;
                self.pc_offset_signed(off as isize)?;
                Ok(StepResult::Continue)
            }
            INSTR_JUMP_BACK16 => {
                let off = self.fetch_u16_le()? as usize;
                self.pc_offset_signed(-((off as isize) + 1))?;
                Ok(StepResult::Continue)
            }
            INSTR_JUMP8_FALSE => {
                let off = self.fetch_u8()? as usize;
                if self.pop()? == PolyWord::tagged(0) {
                    self.pc_offset_signed(off as isize)?;
                }
                Ok(StepResult::Continue)
            }
            INSTR_JUMP8_TRUE => {
                let off = self.fetch_u8()? as usize;
                if self.pop()? != PolyWord::tagged(0) {
                    self.pc_offset_signed(off as isize)?;
                }
                Ok(StepResult::Continue)
            }
            INSTR_JUMP16_FALSE => {
                let off = self.fetch_u16_le()? as usize;
                if self.pop()? == PolyWord::tagged(0) {
                    self.pc_offset_signed(off as isize)?;
                }
                Ok(StepResult::Continue)
            }
            INSTR_JUMP16_TRUE => {
                let off = self.fetch_u16_le()? as usize;
                if self.pop()? != PolyWord::tagged(0) {
                    self.pc_offset_signed(off as isize)?;
                }
                Ok(StepResult::Continue)
            }

            // ----- Fixed (tagged) integer arithmetic (wrapping)
            INSTR_FIXED_ADD => self.bin_op_tagged(|x, y| Ok(x.wrapping_add(y))),
            INSTR_FIXED_SUB => self.bin_op_tagged(|x, y| Ok(y.wrapping_sub(x))),
            INSTR_FIXED_MULT => self.bin_op_tagged(|x, y| Ok(x.wrapping_mul(y))),
            INSTR_FIXED_QUOT => self.bin_op_tagged(|x, y| if x == 0 { Err(()) } else { Ok(y.wrapping_div(x)) }),
            INSTR_FIXED_REM => self.bin_op_tagged(|x, y| if x == 0 { Err(()) } else { Ok(y.wrapping_rem(x)) }),

            // ----- Word (untagged) arithmetic
            INSTR_WORD_ADD => self.bin_op_word(|x, y| y.wrapping_add(x)),
            INSTR_WORD_SUB => self.bin_op_word(|x, y| y.wrapping_sub(x)),
            INSTR_WORD_MULT => self.bin_op_word(|x, y| y.wrapping_mul(x)),
            INSTR_WORD_AND => self.bin_op_word(|x, y| y & x),
            INSTR_WORD_OR => self.bin_op_word(|x, y| y | x),
            INSTR_WORD_XOR => self.bin_op_word(|x, y| y ^ x),
            INSTR_WORD_SHIFT_LEFT => self.bin_op_word(|x, y| y << (x & 63)),
            INSTR_WORD_SHIFT_R_LOG => self.bin_op_word(|x, y| y >> (x & 63)),
            INSTR_WORD_DIV => self.bin_op_word_checked(|x, y| y.checked_div(x).ok_or(())),
            INSTR_WORD_MOD => self.bin_op_word_checked(|x, y| y.checked_rem(x).ok_or(())),

            // ----- Comparisons
            INSTR_EQUAL_WORD => self.bin_op_cmp(|x, y| x == y),
            INSTR_LESS_SIGNED => self.bin_op_cmp(|x, y| (y as isize) < (x as isize)),
            INSTR_LESS_UNSIGNED => self.bin_op_cmp(|x, y| y < x),
            INSTR_LESS_EQ_SIGNED => self.bin_op_cmp(|x, y| (y as isize) <= (x as isize)),
            INSTR_LESS_EQ_UNSIGNED => self.bin_op_cmp(|x, y| y <= x),
            INSTR_GREATER_SIGNED => self.bin_op_cmp(|x, y| (y as isize) > (x as isize)),
            INSTR_GREATER_UNSIGNED => self.bin_op_cmp(|x, y| y > x),
            INSTR_GREATER_EQ_SIGNED => self.bin_op_cmp(|x, y| (y as isize) >= (x as isize)),
            INSTR_GREATER_EQ_UNSIGNED => self.bin_op_cmp(|x, y| y >= x),

            // ----- Boolean / tag tests
            INSTR_NOT_BOOLEAN => {
                let v = self.pop()?;
                self.push_continue(if v == PolyWord::tagged(0) {
                    PolyWord::tagged(1)
                } else {
                    PolyWord::tagged(0)
                })
            }
            INSTR_IS_TAGGED => {
                let v = self.pop()?;
                self.push_continue(if v.is_tagged() {
                    PolyWord::tagged(1)
                } else {
                    PolyWord::tagged(0)
                })
            }

            // ----- Stack manipulation (slide-and-keep-top)
            INSTR_RESET_1 | INSTR_RESET_R_1 => self.reset(1),
            INSTR_RESET_2 | INSTR_RESET_R_2 => self.reset(2),
            INSTR_RESET_R_3 => self.reset(3),
            INSTR_RESET_B | INSTR_RESET_R_B => {
                let n = self.fetch_u8()? as usize;
                self.reset(n)
            }

            // ----- Returns
            INSTR_RETURN_1 => self.do_return(1),
            INSTR_RETURN_2 => self.do_return(2),
            INSTR_RETURN_3 => self.do_return(3),
            INSTR_RETURN_B => {
                let n = self.fetch_u8()? as usize;
                self.do_return(n)
            }
            INSTR_RETURN_W => {
                let n = self.fetch_u16_le()? as usize;
                self.do_return(n)
            }

            // ----- Extended opcodes (one-byte ESCAPE prefix)
            INSTR_ESCAPE => self.dispatch_extended(opcode_pc),

            // ----- Everything else: surface to caller
            _ => {
                // Roll back so PC points AT the unknown op.
                self.pc = opcode_pc;
                Ok(StepResult::Unimplemented { op, extended: false })
            }
        }
    }

    /// Dispatch an extended opcode (the byte after ESCAPE / 0xfe).
    fn dispatch_extended(&mut self, escape_pc: *const u8) -> Result<StepResult, InterpError> {
        use opcodes::ext::*;
        let ext = self.fetch_u8()?;
        match ext {
            // ----- Mutex (single-threaded; pessimistic semantics)
            //
            // For genuine single-thread correctness we'd accurately
            // model the counter (see bytecode.cpp:1496-1532). But the
            // bootstrap's mutex use is entangled with other stubbed
            // RTS calls (PolyBasicIOGeneral etc.) that return wrong
            // values, and "correct" mutex semantics here just exposes
            // those downstream bugs as crashes. So we run the
            // pessimistic version: every lock-attempt is "contested",
            // falling through to PolyThreadMutexBlock which returns
            // zero. Net effect: bootstrap loops in mutex-block until
            // the next non-mutex divergence happens.
            //
            // The right long-term fix is real impls of the RTS
            // functions, not better mutex stubs.
            EXTINSTR_CREATE_MUTEX => {
                use crate::length_word::{F_MUTABLE_BIT, F_NO_OVERWRITE, F_WEAK_BIT};
                let p = self.allocate(1, F_MUTABLE_BIT | F_NO_OVERWRITE | F_WEAK_BIT)?;
                // SAFETY: just allocated 1 word
                unsafe { p.add(0).write(PolyWord::tagged(0)) };
                self.push_continue(PolyWord::from_ptr(p.cast_const()))
            }
            // Mutex / atomic stubs: pessimistic (always contested).
            // See PolyThreadMutexBlock in rts.rs for why optimistic
            // mode exposes a handler-frame-layout issue downstream.
            EXTINSTR_LOCK_MUTEX | EXTINSTR_TRY_LOCK_MUTEX | EXTINSTR_ATOMIC_RESET => {
                let _ = self.pop()?;
                self.push_continue(PolyWord::tagged(0))
            }
            EXTINSTR_ATOMIC_EXCH_ADD => {
                let _ = self.pop()?;
                let _ = self.pop()?;
                self.push_continue(PolyWord::tagged(0))
            }

            // ----- Wide variants of the base opcodes (16-bit immediates)
            EXTINSTR_INDIRECT_W => {
                let idx = self.fetch_u16_le()? as usize;
                let v = self.peek(0)?;
                let p = v.as_ptr::<PolyWord>();
                // SAFETY: caller emits valid offset
                let field = unsafe { *p.add(idx) };
                self.pop()?;
                self.push_continue(field)
            }
            EXTINSTR_TUPLE_W => {
                let n = self.fetch_u16_le()? as usize;
                self.do_tuple(n)
            }
            EXTINSTR_ALLOC_MUT_CLOSURE_W => {
                let n = self.fetch_u16_le()? as usize;
                self.do_alloc_mut_closure(n)
            }
            EXTINSTR_MOVE_TO_MUT_CLOSURE_W => {
                let slot = self.fetch_u16_le()? as usize;
                self.do_move_to_mut_closure(slot)
            }
            EXTINSTR_CLOSURE_W => {
                let n = self.fetch_u16_le()? as usize;
                self.do_create_closure(n)
            }
            EXTINSTR_INDIRECT_CLOSURE_W => {
                let depth = self.fetch_u16_le()? as usize;
                let closure_word = self.peek(depth)?;
                let p = closure_word.as_ptr::<PolyWord>();
                // SAFETY: caller emits valid closure
                let val = unsafe { *p.add(1) };
                self.push_continue(val)
            }
            EXTINSTR_RESET_W | EXTINSTR_RESET_R_W => {
                let n = self.fetch_u16_le()? as usize;
                self.reset(n)
            }

            // ----- Wider jumps / case
            EXTINSTR_JUMP32 => {
                let lo = u32::from(self.fetch_u16_le()?);
                let hi = u32::from(self.fetch_u16_le()?);
                let off = (hi << 16) | lo;
                self.pc_offset_signed(off as isize)?;
                Ok(StepResult::Continue)
            }
            EXTINSTR_JUMP32_FALSE => {
                let lo = u32::from(self.fetch_u16_le()?);
                let hi = u32::from(self.fetch_u16_le()?);
                let off = (hi << 16) | lo;
                if self.pop()? == PolyWord::tagged(0) {
                    self.pc_offset_signed(off as isize)?;
                }
                Ok(StepResult::Continue)
            }
            EXTINSTR_JUMP32_TRUE => {
                let lo = u32::from(self.fetch_u16_le()?);
                let hi = u32::from(self.fetch_u16_le()?);
                let off = (hi << 16) | lo;
                if self.pop()? != PolyWord::tagged(0) {
                    self.pc_offset_signed(off as isize)?;
                }
                Ok(StepResult::Continue)
            }

            // Extended tail call: 16-bit args, falls through to TAIL_CALL.
            EXTINSTR_TAIL => {
                let tail_count = self.fetch_u16_le()? as usize;
                let skip = self.fetch_u16_le()? as usize;
                self.do_tail_call(tail_count, skip)?;
                Ok(StepResult::Continue)
            }

            // Unknown extension — surface to caller, rolled back to ESCAPE byte.
            _ => {
                self.pc = escape_pc;
                Ok(StepResult::Unimplemented { op: ext, extended: true })
            }
        }
    }

    // ---- Helpers ------------------------------------------------------

    fn push_continue(&mut self, w: PolyWord) -> Result<StepResult, InterpError> {
        self.push(w)?;
        Ok(StepResult::Continue)
    }

    fn dup_local(&mut self, depth: usize) -> Result<StepResult, InterpError> {
        let v = self.peek(depth)?;
        self.push_continue(v)
    }

    fn reset(&mut self, n: usize) -> Result<StepResult, InterpError> {
        let top = self.pop()?;
        for _ in 0..n {
            self.pop()?;
        }
        self.push_continue(top)
    }

    fn indirect(&mut self, n: usize) -> Result<StepResult, InterpError> {
        let obj_word = self.pop()?;
        let p = obj_word.as_ptr::<PolyWord>();
        // SAFETY: caller (compiled code) is trusted to emit valid offsets.
        let field = unsafe { *p.add(n) };
        self.push_continue(field)
    }

    // ---- Allocation ---------------------------------------------------

    /// Bump-allocate `n_words` words plus a length word, setting the
    /// length word's flag byte to `flags`. Returns a `*mut` pointer
    /// to the body's first slot.
    fn allocate(&mut self, n_words: usize, flags: u8) -> Result<*mut PolyWord, InterpError> {
        use crate::space;
        let space = self.alloc_space.as_mut().ok_or(InterpError::NoAllocator)?;
        let p = space.alloc(n_words);
        // SAFETY: alloc just returned the matching length-word slot
        unsafe {
            space::set_length_word(p, n_words, flags);
        }
        Ok(p)
    }

    /// `tuple_N`: alloc N-word ordinary object, fill with N popped
    /// values (slot 0 = first popped's neighbour, see bytecode.cpp:2283).
    fn do_tuple(&mut self, n: usize) -> Result<StepResult, InterpError> {
        let p = self.allocate(n, 0)?; // 0 = ordinary word object
        // Upstream: `for (; storeWords > 0; ) p->Set(--storeWords, *sp++)`.
        // That writes slot[n-1] first (popping the top), then slot[n-2], etc.
        for i in (0..n).rev() {
            let v = self.pop()?;
            // SAFETY: i < n_words by construction.
            unsafe { p.add(i).write(v) };
        }
        self.push_continue(PolyWord::from_ptr(p.cast_const()))
    }

    /// `closure_b`: build an immutable closure with N captures.
    /// Stack on entry (top down): source-closure (for code addr),
    /// capture[N-1], ..., capture[0]. Result replaces all of these.
    fn do_create_closure(&mut self, n_captures: usize) -> Result<StepResult, InterpError> {
        use crate::length_word::F_CLOSURE_OBJ;

        let length = n_captures + 1; // +1 for code addr at slot 0
        let p = self.allocate(length, F_CLOSURE_OBJ)?;

        // Upstream: `for (; storeWords > 0; ) t->Set(--storeWords + 1, *sp++)`.
        // So with N captures, slots [length-1, length-2, ..., 1] are
        // filled in that order, popping each from the top.
        for i in (1..length).rev() {
            let v = self.pop()?;
            // SAFETY: i < length
            unsafe { p.add(i).write(v) };
        }
        // Now the source closure is on top. Copy its first word
        // (code address) to slot 0 of the new closure.
        let src_word = self.peek(0)?;
        let src_ptr = src_word.as_ptr::<PolyWord>();
        // SAFETY: src is a valid closure
        let code_addr = unsafe { *src_ptr };
        // SAFETY: slot 0 is in bounds
        unsafe { p.add(0).write(code_addr) };
        // Replace top of stack with new closure.
        self.pop()?;
        self.push_continue(PolyWord::from_ptr(p.cast_const()))
    }

    /// `alloc_mut_closure_b N`: allocate a mutable closure with N
    /// capture slots (initialised to TAGGED(0)). Source closure on top
    /// provides the code address. Result REPLACES the source on top.
    fn do_alloc_mut_closure(&mut self, n_captures: usize) -> Result<StepResult, InterpError> {
        use crate::length_word::{F_CLOSURE_OBJ, F_MUTABLE_BIT};

        let length = n_captures + 1;
        let p = self.allocate(length, F_CLOSURE_OBJ | F_MUTABLE_BIT)?;
        // Source closure is on top: copy its first word (code addr).
        let src_word = self.peek(0)?;
        let src_ptr = src_word.as_ptr::<PolyWord>();
        // SAFETY: src closure invariant
        let code_addr = unsafe { *src_ptr };
        // SAFETY: indices < length
        unsafe {
            p.add(0).write(code_addr);
            for i in 1..length {
                p.add(i).write(PolyWord::tagged(0));
            }
        }
        // Replace top with new closure pointer.
        self.pop()?;
        self.push_continue(PolyWord::from_ptr(p.cast_const()))
    }

    /// `move_to_mut_closure_b N`: pop value `u`, write to slot (N+1)
    /// of the closure that's now on top. Leaves the closure on top
    /// (NOT popped).
    fn do_move_to_mut_closure(&mut self, slot: usize) -> Result<StepResult, InterpError> {
        let u = self.pop()?;
        let target = self.peek(0)?;
        let p = target.as_ptr::<PolyWord>();
        // We need mutable access despite holding a *const. Cast is
        // safe because the closure was allocated mutable.
        let p_mut = p.cast_mut();
        // SAFETY: caller emitted a valid slot index for a closure
        // with at least slot+2 words.
        unsafe { p_mut.add(slot + 1).write(u) };
        Ok(StepResult::Continue)
    }

    /// `alloc_ref`: allocate a 1-word mutable cell initialised to the
    /// value currently on top. REPLACES top with cell pointer (the
    /// initialiser doesn't get popped, just replaced).
    fn do_alloc_ref(&mut self) -> Result<StepResult, InterpError> {
        use crate::length_word::F_MUTABLE_BIT;

        let init = self.peek(0)?;
        let p = self.allocate(1, F_MUTABLE_BIT)?;
        // SAFETY: 1 word allocated
        unsafe { p.add(0).write(init) };
        self.pop()?;
        self.push_continue(PolyWord::from_ptr(p.cast_const()))
    }

    /// Clear the mutable bit on the length word of the object at top
    /// of stack. INSTR_LOCK leaves the object on top; INSTR_CLEAR_MUTABLE
    /// replaces it with TAGGED(0).
    fn clear_mutable_bit(&mut self, replace_with_zero: bool) -> Result<StepResult, InterpError> {
        use crate::length_word::{self, F_MUTABLE_BIT};

        let v = self.peek(0)?;
        let p = v.as_ptr::<PolyWord>().cast_mut();
        // SAFETY: caller upholds top is a mutable heap object.
        unsafe {
            let lw_ptr = p.sub(1);
            let lw = *lw_ptr;
            let new_bits = lw.0 & !((F_MUTABLE_BIT as usize) << length_word::FLAGS_SHIFT);
            lw_ptr.write(PolyWord::from_bits(new_bits));
        }
        if replace_with_zero {
            self.pop()?;
            self.push_continue(PolyWord::tagged(0))
        } else {
            Ok(StepResult::Continue)
        }
    }

    /// `indirect_closure_b{0,1,2}` with depth in pc[0]: read sp[depth]
    /// as a closure pointer, push slot `1 + slot_offset` of that closure.
    fn do_indirect_closure(&mut self, slot_offset: usize) -> Result<StepResult, InterpError> {
        let depth = self.fetch_u8()? as usize;
        let closure_word = self.peek(depth)?;
        let p = closure_word.as_ptr::<PolyWord>();
        // SAFETY: closure has at least slot_offset+2 words.
        let val = unsafe { *p.add(1 + slot_offset) };
        self.push_continue(val)
    }

    fn bin_op_tagged<F>(&mut self, f: F) -> Result<StepResult, InterpError>
    where
        F: FnOnce(isize, isize) -> Result<isize, ()>,
    {
        let x = self.pop()?;
        let y = self.pop()?;
        let r = f(x.untag(), y.untag()).map_err(|()| InterpError::DivByZero)?;
        self.push_continue(PolyWord::tagged(r))
    }

    fn bin_op_word<F>(&mut self, f: F) -> Result<StepResult, InterpError>
    where
        F: FnOnce(usize, usize) -> usize,
    {
        let x = self.pop()?;
        let y = self.pop()?;
        self.push_continue(PolyWord::from_bits(f(x.0, y.0)))
    }

    fn bin_op_word_checked<F>(&mut self, f: F) -> Result<StepResult, InterpError>
    where
        F: FnOnce(usize, usize) -> Result<usize, ()>,
    {
        let x = self.pop()?;
        let y = self.pop()?;
        let r = f(x.0, y.0).map_err(|()| InterpError::DivByZero)?;
        self.push_continue(PolyWord::from_bits(r))
    }

    fn bin_op_cmp<F>(&mut self, f: F) -> Result<StepResult, InterpError>
    where
        F: FnOnce(usize, usize) -> bool,
    {
        let x = self.pop()?;
        let y = self.pop()?;
        self.push_continue(if f(x.0, y.0) {
            PolyWord::tagged(1)
        } else {
            PolyWord::tagged(0)
        })
    }

    // ---- Call / Return -----------------------------------------------

    /// Allocate a placeholder thread object — 8 zeroed mutable words.
    /// Real PolyML returns `taskData->threadObject`, which has known
    /// fields the bootstrap reads via INDIRECT_*. The 8-word stub
    /// gives those reads a defined (zero) value rather than crashing.
    fn alloc_stub_thread_object(&mut self) -> Result<PolyWord, InterpError> {
        use crate::length_word::F_MUTABLE_BIT;
        let length = 8;
        let p = self.allocate(length, F_MUTABLE_BIT)?;
        // SAFETY: just allocated `length` words
        unsafe {
            for i in 0..length {
                p.add(i).write(PolyWord::tagged(0));
            }
        }
        Ok(PolyWord::from_ptr(p.cast_const()))
    }

    /// Dispatch a `CALL_FAST_RTS<N>` opcode through the RTS table.
    /// Stack layout (top down): stub object, arg0, arg1, ..., arg_{n-1}
    /// — matches `bytecode.cpp:681-712`. We pop the stub, read its
    /// word 0 (the dispatch token), look up the function, pop N args,
    /// and push the result.
    fn rts_call(&mut self, n_args: usize) -> Result<StepResult, InterpError> {
        let stub = self.pop()?;
        let p = stub.as_ptr::<PolyWord>();
        // SAFETY: caller (bytecode) guarantees `stub` is a valid
        // EntryPoint object with word 0 holding the dispatch token.
        let token = unsafe { (*p).0 };
        // Copy the entry out so we can drop the immutable borrow on
        // self.rts before pop'ing/allocating.
        let (entry_name, entry_func) = {
            let e = self
                .rts
                .entry(token)
                .ok_or(InterpError::UnresolvedRts { n: n_args })?;
            (e.name, e.func)
        };
        // Pop args (we already popped the stub).
        let mut args: [PolyWord; 5] = [PolyWord::ZERO; 5];
        for slot in args.iter_mut().take(n_args) {
            *slot = self.pop()?;
        }
        // Dispatch by arity, checking it matches the opcode's expectation.
        let fn_arity = entry_func.arity();
        if fn_arity != n_args {
            return Err(InterpError::RtsArityMismatch {
                name: entry_name,
                op_arity: n_args,
                fn_arity,
            });
        }
        crate::rts::trace_call(entry_name, n_args);
        let mut ctx = RtsContext {
            alloc_space: self.alloc_space.as_mut(),
        };
        let result = match entry_func {
            RtsFn::Arity0(f) => f(&mut ctx),
            RtsFn::Arity1(f) => f(&mut ctx, args[0]),
            RtsFn::Arity2(f) => f(&mut ctx, args[0], args[1]),
            RtsFn::Arity3(f) => f(&mut ctx, args[0], args[1], args[2]),
            RtsFn::Arity4(f) => f(&mut ctx, args[0], args[1], args[2], args[3]),
            RtsFn::Arity5(f) => f(&mut ctx, args[0], args[1], args[2], args[3], args[4]),
        };
        self.push_continue(result)
    }

    /// Implement TAIL_B_B (and its extended sibling EXTINSTR_tail).
    /// Mirrors `bytecode.cpp:391-424`.
    fn do_tail_call(&mut self, tail_count: usize, skip: usize) -> Result<(), InterpError> {
        use crate::length_word;

        if tail_count < 2 {
            return Err(InterpError::StackUnderflow);
        }

        // Shift `tail_count` items from [sp, sp+tail_count) to
        // [sp+skip, sp+skip+tail_count). The shift is "downward" in
        // index terms (deeper into the stack); the source range is the
        // current top items.
        let original_sp = self.sp;
        let mut tail_ptr = original_sp + tail_count;
        let mut new_sp = tail_ptr + skip;
        // Boundary check: the destination range must not extend past
        // the stack's end.
        if new_sp > self.stack.len() {
            return Err(InterpError::StackUnderflow);
        }
        for _ in 0..tail_count {
            new_sp -= 1;
            tail_ptr -= 1;
            self.stack[new_sp] = self.stack[tail_ptr];
        }
        self.sp = new_sp; // = original_sp + skip

        // Pop the first item (discarded — it's a slot that becomes the
        // PC field, but PC is overwritten by closure's code addr below).
        let _ = self.pop()?;
        // Pop the new closure.
        let closure = self.pop()?;
        if !closure.is_data_ptr() {
            return Err(InterpError::NotAClosure(closure));
        }
        // Set PC to the closure's first word (the code address) and
        // refresh code-segment bounds.
        let closure_ptr = closure.as_ptr::<PolyWord>();
        // SAFETY: closure invariant
        let code_word = unsafe { *closure_ptr };
        let new_code_obj = code_word.as_ptr::<PolyWord>();
        // SAFETY: code object invariant
        let (consts_start, _) = unsafe { length_word::const_segment_for_code(new_code_obj) };
        self.code_start = new_code_obj.cast::<u8>();
        self.code_end = consts_start.cast::<u8>();
        self.pc = self.code_start;

        // CRUCIAL: do NOT push to `frames`. Tail call replaces the
        // current frame; the eventual RETURN should pop the side-stack
        // entry pushed by our CALLER (already there from when we were
        // called).
        Ok(())
    }

    /// Implement the CALL_CLOSURE common path (bytecode.cpp:412-424).
    ///
    /// At entry, `closure` has already been popped from the stack. We:
    /// 1. push retPC (current pc, encoded as raw bits);
    /// 2. push closure;
    /// 3. jump to closure's first word (which is the code address).
    fn do_call(&mut self, closure: PolyWord) -> Result<(), InterpError> {
        use crate::length_word;

        if !closure.is_data_ptr() || closure.0 & (std::mem::size_of::<usize>() - 1) != 0 {
            // Diagnostic dump (RTS_TRACE only).
            if crate::rts::is_traced() {
                let segment_size =
                    unsafe { self.code_end.offset_from(self.code_start) as usize };
                eprintln!(
                    "  CALL bad closure: {closure:?} | frames depth={} | sp_depth={} | code_segment_bytes={}",
                    self.frames.len(),
                    self.stack_height(),
                    segment_size,
                );
                // Stack window
                let n = std::cmp::min(40, self.stack_height());
                for d in 0..n {
                    let w = self.stack[self.sp + d];
                    let marker = if w == closure { " <-- bad closure" } else { "" };
                    eprintln!("    sp[{d:2}] = {w:?}{marker}");
                }
                // Bytecode window around the failing PC (which has
                // already advanced past the opcode + immediate).
                let cur_off = self.pc_offset();
                let lo = cur_off.saturating_sub(20);
                let hi = std::cmp::min(cur_off + 5, segment_size);
                let bytes: Vec<u8> = (lo..hi)
                    .map(|i| unsafe { *self.code_start.add(i) })
                    .collect();
                let hexdump = bytes
                    .iter()
                    .map(|b| format!("{b:02x}"))
                    .collect::<Vec<_>>()
                    .join(" ");
                eprintln!(
                    "    bytes [{lo}..{hi}] = {hexdump}  (PC after fetch = {cur_off})",
                );
            }
            return Err(InterpError::NotAClosure(closure));
        }
        // Save the *current* PC as the return address. By this point
        // we've already advanced past the call opcode and its immediates,
        // so resuming at this PC after RETURN is correct.
        let ret_pc_bits = self.pc as usize;
        self.push(PolyWord::from_bits(ret_pc_bits))?;
        self.push(closure)?;

        // The closure's first word IS the code object pointer (per
        // F_CLOSURE_OBJ layout). Jump to its byte 0.
        let closure_ptr = closure.as_ptr::<PolyWord>();
        // SAFETY: caller (compiler) is trusted to emit a valid closure.
        let code_word = unsafe { *closure_ptr };
        let new_code_obj = code_word.as_ptr::<PolyWord>();

        // Save caller's bounds on the side-stack before we overwrite.
        self.frames.push((self.code_start, self.code_end));

        // Recompute code segment bounds for the new code object.
        // SAFETY: closure invariant guarantees the code address is a
        // real code object.
        let (consts_start, _) = unsafe { length_word::const_segment_for_code(new_code_obj) };
        self.code_start = new_code_obj.cast::<u8>();
        self.code_end = consts_start.cast::<u8>();
        self.pc = self.code_start;
        Ok(())
    }

    /// Implement RETURN_N (bytecode.cpp:454-465).
    ///
    /// Stack on entry (from top):  result, closure, retPC, args[N]
    ///                              ^ sp
    ///
    /// We pop result, skip closure, pop retPC, drop N args, push
    /// result. If retPC is null, we're returning from the top-level
    /// frame — yield StepResult::Returned(result).
    fn do_return(&mut self, return_count: usize) -> Result<StepResult, InterpError> {
        let result = self.pop()?;        // top: result
        let _closure = self.pop()?;       // closure
        let ret_pc_word = self.pop()?;    // retPC
        for _ in 0..return_count {
            self.pop()?;                  // args
        }
        self.push(result)?;

        let ret_pc_bits = ret_pc_word.0;
        if ret_pc_bits == 0 {
            // Top-level return: yield to host. Result is on top.
            let result = self.pop()?;
            return Ok(StepResult::Returned(result));
        }

        // Restore the caller's code segment bounds from our side-stack.
        let (caller_start, caller_end) = self
            .frames
            .pop()
            .ok_or(InterpError::StackUnderflow)?;
        self.code_start = caller_start;
        self.code_end = caller_end;
        self.pc = ret_pc_bits as *const u8;
        Ok(StepResult::Continue)
    }

    // ---- PC-relative constant access -----------------------------------

    /// Load a `PolyWord` from a PC-relative byte offset plus a
    /// PolyWord-scaled index. Mirrors upstream's
    /// `((PolyWord*)(pc + imm))[idx]` pattern from `bytecode.cpp:530`
    /// (and analogous lines for the `_8_8` and `_16_8` variants).
    ///
    /// Caller is expected to have fetched all immediate bytes; the
    /// upstream `pc + pc[0] + N` becomes `self.pc + imm` in our terms,
    /// where N (the number of immediate bytes) has been absorbed by
    /// our `fetch_u8` calls.
    ///
    /// # Safety
    /// `self.pc + byte_off + idx*sizeof(PolyWord)` must land within
    /// the constant pool of the current code object.
    unsafe fn read_pc_const(&self, byte_off: usize, idx: usize) -> PolyWord {
        // SAFETY: precondition.
        unsafe {
            let base = self.pc.add(byte_off);
            base.cast::<PolyWord>().add(idx).read_unaligned()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::opcodes::*;
    use super::*;
    use crate::length_word::{F_CLOSURE_OBJ, F_CODE_OBJ};
    use crate::space::{MemorySpace, SpaceKind};

    // ---- ALU + control flow tests (carried over, adjusted for new API)

    fn run_to_int(code: Vec<u8>) -> isize {
        let mut interp = Interpreter::from_bytes(64, code);
        // For from_bytes tests we don't have a real call frame, so we
        // seed retPC=null + a dummy closure beneath any args, mimicking
        // the entry-from-top-level shape.
        interp.test_seed_return_sentinel();
        interp.test_seed_top(PolyWord::ZERO); // dummy "closure" placeholder
        // NB: this means our test bytecode runs as if it's the
        // top-level function — its RETURN_N will see retPC=null and
        // yield Returned(result).
        match interp.run() {
            Ok(StepResult::Returned(w)) => w.untag(),
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn const_and_return() {
        // RETURN_1 expects 1 word of args under the [closure, retPC]
        // pair; our test harness seeds only the pair (0 args), so we
        // use RETURN_B 0 here.
        let code = vec![INSTR_CONST_3, INSTR_RETURN_B, 0];
        assert_eq!(run_to_int(code), 3);
    }

    #[test]
    fn fixed_add() {
        let code = vec![
            INSTR_CONST_3,
            INSTR_CONST_4,
            INSTR_FIXED_ADD,
            INSTR_RETURN_B,
            0,
        ];
        assert_eq!(run_to_int(code), 7);
    }

    #[test]
    fn jump_forward_skips_const() {
        // Stack layout: [closure_dummy, retPC=null]; we PUSH 3, then
        // jump past a const_4, then RETURN_B 0.
        // Bytes:
        //   0: CONST_3
        //   1: JUMP8
        //   2: 1            (offset)
        //   3: CONST_4      (skipped)
        //   4: RETURN_B
        //   5: 0
        let code = vec![
            INSTR_CONST_3,
            INSTR_JUMP8,
            1,
            INSTR_CONST_4,
            INSTR_RETURN_B,
            0,
        ];
        assert_eq!(run_to_int(code), 3);
    }

    #[test]
    fn loop_jump_back() {
        // Tight loop: counter starts at 5, subtract 1 each iter, exit
        // when zero. Mirrors the older test but with RETURN_B 0.
        let code = vec![
            INSTR_CONST_INT_B,
            5,
            // .top = pc 2
            INSTR_CONST_INT_B,
            1,
            INSTR_FIXED_SUB,
            INSTR_LOCAL_0,
            INSTR_CONST_0,
            INSTR_EQUAL_WORD,
            INSTR_JUMP8_TRUE,
            2,
            INSTR_JUMP_BACK8,
            9,
            INSTR_RETURN_B,
            0,
        ];
        assert_eq!(run_to_int(code), 0);
    }

    // ---- Call / return tests using real code objects in a MemorySpace

    /// Materialise a code object into `space` with the given bytecode
    /// bytes followed by a constant pool of the given values, plus the
    /// trailing const-count + offset trailer. Returns a pointer to the
    /// new object (one word after its length word).
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
            crate::space::set_length_word(obj_ptr, total_words, F_CODE_OBJ);
            // Code bytes.
            let dst = obj_ptr.cast::<u8>();
            std::ptr::copy_nonoverlapping(code_bytes.as_ptr(), dst, code_bytes.len());
            // Pad final code word with zeros.
            let pad = code_bytes.len().next_multiple_of(word) - code_bytes.len();
            if pad > 0 {
                std::ptr::write_bytes(dst.add(code_bytes.len()), 0, pad);
            }
            // const count at [code_words]
            obj_ptr.add(code_words).write(PolyWord::from_bits(n_consts));
            // constants at [code_words+1 .. total-1]
            for (i, c) in constants.iter().enumerate() {
                obj_ptr.add(code_words + 1 + i).write(*c);
            }
            // trailing offset at [total-1]: matches loader.rs
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

    /// Materialise a closure object pointing at the given code object.
    fn make_closure(space: &mut MemorySpace, code_obj: *const PolyWord) -> *const PolyWord {
        let obj_ptr = space.alloc(1);
        unsafe {
            crate::space::set_length_word(obj_ptr, 1, F_CLOSURE_OBJ);
            obj_ptr.add(0).write(PolyWord::from_ptr(code_obj));
        }
        obj_ptr.cast_const()
    }

    #[test]
    fn synthetic_call_and_return() {
        // Build:
        //   callee: CONST_INT_B 7; RETURN_B 0  -> returns 7 with 0 args
        //   caller: <push closure>; CALL_CLOSURE; RETURN_B 0
        //
        // The caller side is built as bytecode; the closure pointer is
        // pre-seeded onto the stack so the caller's CALL_CLOSURE pops
        // it.
        let mut code_space = MemorySpace::new(64, SpaceKind::Code);
        let callee_bytes = vec![INSTR_CONST_INT_B, 7, INSTR_RETURN_B, 0];
        let callee_code = make_code_object(&mut code_space, &callee_bytes, &[]);
        let callee_closure = make_closure(&mut code_space, callee_code);

        let caller_bytes = vec![INSTR_CALL_CLOSURE, INSTR_RETURN_B, 0];
        let caller_code = make_code_object(&mut code_space, &caller_bytes, &[]);

        let mut interp = unsafe { Interpreter::from_code_object(64, caller_code) };
        // Seed top-of-stack with: [closure_for_caller=dummy,
        // retPC=null, callee_closure_ptr_to_pop_in_CALL]
        interp.test_seed_return_sentinel();
        interp.test_seed_top(PolyWord::ZERO); // caller's "self" closure
        interp.test_seed_top(PolyWord::from_ptr(callee_closure)); // top: callee closure to call

        match interp.run() {
            Ok(StepResult::Returned(v)) => assert_eq!(v.untag(), 7),
            other => panic!("expected Returned(7), got {other:?}"),
        }
    }

    #[test]
    fn const_addr_loads_from_pool() {
        // Test CONST_ADDR8_0 with unsigned-byte semantics (matches
        // upstream bytecode.cpp:529-530). The const-addr formula is
        // PC-relative-forward, so we need enough bytecode bytes
        // BEFORE the constants for the unsigned imm to reach them.
        //
        // Layout: [CONST_ADDR8_0, imm, NOP*N, RETURN_B, 0] followed by
        // the constants area.
        //
        // CONST_ADDR8_0 formula: val = (PolyWord*)(self.pc + imm)[3]
        // where self.pc is *after* fetching opcode+imm (== upstream's
        // `pc` at handler entry, when upstream does `pc + pc[0] + 1`).
        //
        // Choose layout so:
        //   - 1 word of constants (TAGGED 42 at index 0)
        //   - code_bytes occupies ceil(30/8) = 4 words = 32 bytes
        //   - const_count word at byte 32
        //   - constants start at byte 40 (slot code_words + 1)
        //   - self.pc after fetching CONST_ADDR8_0 + imm = byte 2
        //   - formula: 2 + imm + 3*8 = 40 → imm = 14
        let mut code_bytes = vec![INSTR_CONST_ADDR8_0, 14];
        // Pad to 30 bytes total (so code_words = ceil(30/8) = 4).
        // We have 2 bytes already; add 26 NOPs.
        code_bytes.resize(28, INSTR_NO_OP);
        code_bytes.push(INSTR_RETURN_B);
        code_bytes.push(0);
        assert_eq!(code_bytes.len(), 30); // sanity

        let mut code_space = MemorySpace::new(32, SpaceKind::Code);
        let code = make_code_object(&mut code_space, &code_bytes, &[PolyWord::tagged(42)]);

        let mut interp = unsafe { Interpreter::from_code_object(64, code) };
        interp.test_seed_return_sentinel();
        interp.test_seed_top(PolyWord::ZERO);

        match interp.run() {
            Ok(StepResult::Returned(v)) => assert_eq!(v.untag(), 42),
            other => panic!("expected Returned(42), got {other:?}"),
        }
    }

    #[test]
    fn unimplemented_surface() {
        // ESCAPE + an extension byte we don't handle (use a high value
        // that's not in our extension dispatch).
        let code = vec![INSTR_ESCAPE, 0x6e]; // EXTINSTR_REAL_TO_INT — not implemented
        let mut interp = Interpreter::from_bytes(64, code);
        match interp.run().unwrap() {
            StepResult::Unimplemented { op, extended } => {
                assert_eq!(op, 0x6e);
                assert!(extended);
            }
            other => panic!("expected Unimplemented (extended), got {other:?}"),
        }
    }
}
