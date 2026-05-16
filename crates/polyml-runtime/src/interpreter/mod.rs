//! PolyML bytecode interpreter — first cut.
//!
//! This is a faithful port of the dispatch shape in
//! `vendor/polyml/libpolyml/bytecode.cpp`. The stack grows **down**
//! (matching PolyML): `push` decrements the stack pointer, `pop`
//! increments it. `sp[N]` peeks N deep (0 = top).
//!
//! Scope of the *first cut*:
//!
//! - Pure-ALU opcodes: const, local (= dup-N), fixed arithmetic,
//!   word arithmetic, comparisons, boolean negation, tag test.
//! - Unconditional and conditional jumps (`jump8` / `jump_back8` /
//!   `jump8false` / `jump8true`).
//! - `no_op`.
//! - `return_*` halts the interpreter and yields the top-of-stack as
//!   the result. Real call frames + proper return-address handling
//!   come in a second cut.
//!
//! Not yet implemented (will trap with `Unimplemented`):
//!
//! - `call_closure`, `tail_*` — function calls
//! - `alloc_*`, `tuple_*` — allocation (needs GC integration)
//! - `push_handler`, `raise_ex`, `set_handler*`, `delete_handler` —
//!   exception model
//! - `load_*` / `store_*` — memory operations on heap cells
//! - RTS calls
//! - Floats / reals
//! - All extended (0xfe-prefixed) opcodes
//!
//! The first cut's purpose is to validate the dispatch loop end-to-end
//! against hand-crafted bytecode (see the `tests` module).

// Interpreter-wide allows: the signed/unsigned reinterpretation of
// PolyWord bits is intentional (matches PolyML's `UNTAGGED` casting
// pattern in bytecode.cpp). The "manual checked division" lint
// suggests replacing `if x == 0 { Err(()) } else { Ok(y / x) }` with
// `y.checked_div(x).ok_or(())`, but our shape is uniform across
// add/sub/div/mod which makes the explicit form clearer.
#![allow(clippy::cast_sign_loss)]
#![allow(clippy::cast_possible_wrap)]
#![allow(clippy::manual_div_ceil)]

pub mod opcodes;

use crate::poly_word::PolyWord;
use thiserror::Error;

/// Result of one (`step`) or many (`run`) interpreter steps.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StepResult {
    /// Keep going.
    Continue,
    /// A `return_*` opcode fired. The value carried is the
    /// top-of-stack at the moment of return.
    Returned(PolyWord),
    /// The interpreter hit an opcode it doesn't know yet.
    /// Caller can inspect `pc` to find which one.
    Unimplemented(u8),
}

#[derive(Debug, Clone, Error)]
pub enum InterpError {
    #[error("stack overflow at pc={pc}")]
    StackOverflow { pc: usize },
    #[error("stack underflow at pc={pc}")]
    StackUnderflow { pc: usize },
    #[error("pc out of bounds: {pc} (code size {code_size})")]
    PcOutOfBounds { pc: usize, code_size: usize },
    #[error("integer overflow at pc={pc}")]
    IntegerOverflow { pc: usize },
    #[error("division by zero at pc={pc}")]
    DivByZero { pc: usize },
}

/// A bytecode interpreter operating on a single code segment.
///
/// First-cut limitation: `code` is held as an owned `Vec<u8>`. The
/// real loader would point at a code object's byte segment within a
/// `MemorySpace`; we'll wire that up after the dispatch loop is
/// known-good against hand-crafted programs.
pub struct Interpreter {
    /// Backing storage for the ML stack. Grows down.
    stack: Vec<PolyWord>,
    /// Index of the topmost live element. `sp == stack.len()` means
    /// "empty" (the SP is just past the end, ready for the next push
    /// to decrement-then-write).
    sp: usize,
    /// Byte offset into `code` of the next instruction to fetch.
    pc: usize,
    /// The currently-executing code segment.
    code: Vec<u8>,
}

impl Interpreter {
    /// Build a fresh interpreter with `stack_capacity` words of stack
    /// and the given code segment. PC starts at byte 0 of `code`.
    #[must_use]
    pub fn new(stack_capacity: usize, code: Vec<u8>) -> Self {
        let len = stack_capacity;
        Self {
            stack: vec![PolyWord::ZERO; stack_capacity],
            sp: len,
            pc: 0,
            code,
        }
    }

    // ---- Stack primitives (panicking; check bounds in `step` before
    // calling).

    fn push(&mut self, w: PolyWord) -> Result<(), InterpError> {
        if self.sp == 0 {
            return Err(InterpError::StackOverflow { pc: self.pc });
        }
        self.sp -= 1;
        self.stack[self.sp] = w;
        Ok(())
    }

    fn pop(&mut self) -> Result<PolyWord, InterpError> {
        if self.sp >= self.stack.len() {
            return Err(InterpError::StackUnderflow { pc: self.pc });
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
            .ok_or(InterpError::StackUnderflow { pc: self.pc })?;
        Ok(self.stack[idx])
    }

    /// Stack height (number of live words). Useful for tests.
    #[must_use]
    pub fn stack_height(&self) -> usize {
        self.stack.len() - self.sp
    }

    /// Test-only: push a single PolyWord onto the stack before running.
    /// Once the interpreter has proper call-frame setup (Phase 2.1 next
    /// iteration), this stops being a public API.
    #[doc(hidden)]
    pub fn test_seed_top(&mut self, w: PolyWord) {
        // Ignoring overflow — tests build small stacks intentionally.
        let _ = self.push(w);
    }

    #[must_use]
    pub fn pc(&self) -> usize {
        self.pc
    }

    fn fetch_u8(&mut self) -> Result<u8, InterpError> {
        let b = self.code.get(self.pc).copied().ok_or(InterpError::PcOutOfBounds {
            pc: self.pc,
            code_size: self.code.len(),
        })?;
        self.pc += 1;
        Ok(b)
    }

    fn fetch_u16_le(&mut self) -> Result<u16, InterpError> {
        let lo = self.fetch_u8()?;
        let hi = self.fetch_u8()?;
        Ok(u16::from_le_bytes([lo, hi]))
    }

    /// Run until something interesting happens: a `return_*`, an
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
    #[allow(clippy::too_many_lines)] // dispatch loops are intrinsically long
    #[allow(clippy::wildcard_imports)] // opcode names are the natural vocabulary here
    pub fn step(&mut self) -> Result<StepResult, InterpError> {
        use opcodes::*;

        let op = self.fetch_u8()?;
        match op {
            // ----- No-op
            INSTR_NO_OP => Ok(StepResult::Continue),

            // ----- Constants (push tagged int onto stack)
            INSTR_CONST_0 => {
                self.push(PolyWord::tagged(0))?;
                Ok(StepResult::Continue)
            }
            INSTR_CONST_1 => {
                self.push(PolyWord::tagged(1))?;
                Ok(StepResult::Continue)
            }
            INSTR_CONST_2 => {
                self.push(PolyWord::tagged(2))?;
                Ok(StepResult::Continue)
            }
            INSTR_CONST_3 => {
                self.push(PolyWord::tagged(3))?;
                Ok(StepResult::Continue)
            }
            INSTR_CONST_4 => {
                self.push(PolyWord::tagged(4))?;
                Ok(StepResult::Continue)
            }
            INSTR_CONST_10 => {
                self.push(PolyWord::tagged(10))?;
                Ok(StepResult::Continue)
            }
            // const_int_b: TAGGED(*pc) — the byte is treated unsigned
            // (matching bytecode.cpp:621). For negative small ints the
            // compiler emits other sequences (subtraction from 0, etc.).
            INSTR_CONST_INT_B => {
                let n = isize::from(self.fetch_u8()?);
                self.push(PolyWord::tagged(n))?;
                Ok(StepResult::Continue)
            }
            // const_int_w: TAGGED(arg1), arg1 = pc[0] + pc[1]*256.
            INSTR_CONST_INT_W => {
                // u16 -> isize is always lossless on our supported
                // 32+-bit targets; no `From` impl exists because Rust
                // permits 16-bit isize in principle.
                let raw = self.fetch_u16_le()?;
                self.push(PolyWord::tagged(isize::try_from(raw).expect("u16 fits in isize")))?;
                Ok(StepResult::Continue)
            }

            // ----- Local access (push sp[N])
            //
            // bytecode.cpp:623-635: `*(--sp) = sp[N]`. Note that `sp[0]`
            // is the *current top* — `local_0` is `dup`.
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

            // ----- Jumps
            //
            // jump8: pc += *pc + 1  (unsigned 8-bit forward offset)
            // jump_back8: pc -= *pc + 1  — note '+ 1' because the offset
            //   byte itself is *not* counted in the destination.
            // jump16: 16-bit unsigned forward offset.
            // jump_back16: 16-bit unsigned backward offset.
            INSTR_JUMP8 => {
                let off = self.fetch_u8()? as usize;
                self.pc += off;
                Ok(StepResult::Continue)
            }
            INSTR_JUMP_BACK8 => {
                let off = self.fetch_u8()? as usize;
                // After fetch_u8 the pc is past the offset byte; the
                // backward jump distance from that point is `off + 1`
                // bytes (matching bytecode.cpp's `pc -= *pc + 1` pattern
                // before the `pc += 1` of opcode-read happens).
                let new_pc = self
                    .pc
                    .checked_sub(off + 1)
                    .ok_or(InterpError::PcOutOfBounds { pc: self.pc, code_size: self.code.len() })?;
                self.pc = new_pc;
                Ok(StepResult::Continue)
            }
            INSTR_JUMP16 => {
                let off = self.fetch_u16_le()? as usize;
                self.pc += off;
                Ok(StepResult::Continue)
            }
            INSTR_JUMP_BACK16 => {
                let off = self.fetch_u16_le()? as usize;
                let new_pc = self
                    .pc
                    .checked_sub(off + 1)
                    .ok_or(InterpError::PcOutOfBounds { pc: self.pc, code_size: self.code.len() })?;
                self.pc = new_pc;
                Ok(StepResult::Continue)
            }
            INSTR_JUMP8_FALSE => {
                let off = self.fetch_u8()? as usize;
                let test = self.pop()?;
                if test == PolyWord::tagged(0) {
                    self.pc += off;
                }
                Ok(StepResult::Continue)
            }
            INSTR_JUMP8_TRUE => {
                let off = self.fetch_u8()? as usize;
                let test = self.pop()?;
                if test != PolyWord::tagged(0) {
                    self.pc += off;
                }
                Ok(StepResult::Continue)
            }
            INSTR_JUMP16_FALSE => {
                let off = self.fetch_u16_le()? as usize;
                let test = self.pop()?;
                if test == PolyWord::tagged(0) {
                    self.pc += off;
                }
                Ok(StepResult::Continue)
            }
            INSTR_JUMP16_TRUE => {
                let off = self.fetch_u16_le()? as usize;
                let test = self.pop()?;
                if test != PolyWord::tagged(0) {
                    self.pc += off;
                }
                Ok(StepResult::Continue)
            }

            // ----- Fixed (tagged) integer arithmetic
            //
            // bytecode.cpp:926-940 — these check for overflow and trap
            // to long-arithmetic if it occurs. First cut: wrap on
            // overflow; flag a TODO to add the long-arithmetic path
            // once the allocator is in.
            INSTR_FIXED_ADD => self.bin_op_tagged(|x, y| Ok(x.wrapping_add(y))),
            INSTR_FIXED_SUB => self.bin_op_tagged(|x, y| Ok(y.wrapping_sub(x))),
            INSTR_FIXED_MULT => self.bin_op_tagged(|x, y| Ok(x.wrapping_mul(y))),
            INSTR_FIXED_QUOT => self.bin_op_tagged(|x, y| {
                if x == 0 {
                    Err(())
                } else {
                    Ok(y.wrapping_div(x))
                }
            }),
            INSTR_FIXED_REM => self.bin_op_tagged(|x, y| {
                if x == 0 {
                    Err(())
                } else {
                    Ok(y.wrapping_rem(x))
                }
            }),

            // ----- Comparisons (push True/False = TAGGED(1)/TAGGED(0))
            INSTR_EQUAL_WORD => self.bin_op_cmp(|x, y| x == y),
            INSTR_LESS_SIGNED => self.bin_op_cmp(|x, y| (y as isize) < (x as isize)),
            INSTR_LESS_UNSIGNED => self.bin_op_cmp(|x, y| y < x),
            INSTR_LESS_EQ_SIGNED => self.bin_op_cmp(|x, y| (y as isize) <= (x as isize)),
            INSTR_LESS_EQ_UNSIGNED => self.bin_op_cmp(|x, y| y <= x),
            INSTR_GREATER_SIGNED => self.bin_op_cmp(|x, y| (y as isize) > (x as isize)),
            INSTR_GREATER_UNSIGNED => self.bin_op_cmp(|x, y| y > x),
            INSTR_GREATER_EQ_SIGNED => self.bin_op_cmp(|x, y| (y as isize) >= (x as isize)),
            INSTR_GREATER_EQ_UNSIGNED => self.bin_op_cmp(|x, y| y >= x),

            // ----- Indirect (heap field read)
            //
            // bytecode.cpp:573-574 (`indirect_b`) and :570-... (`indirect_0..5`):
            //   *sp = (*sp).w().AsObjPtr()->Get(N)
            // — pop the object pointer from top, read its Nth word,
            // push it back as the new top.
            //
            // No bounds check on the object — matches PolyML; the
            // compiler is trusted not to emit out-of-bounds offsets.
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

            // ----- Word (untagged) arithmetic — operates on raw bits
            //
            // bytecode.cpp:1011-: word ops treat values as
            // *un*-tagged native integers. Useful for bit-manip
            // routines and pointer arithmetic in the basis library.
            // Our wrapping-isize ops here are bitwise-equivalent.
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

            // ----- Boolean / tag tests
            INSTR_NOT_BOOLEAN => {
                let v = self.pop()?;
                let r = if v == PolyWord::tagged(0) {
                    PolyWord::tagged(1)
                } else {
                    PolyWord::tagged(0)
                };
                self.push(r)?;
                Ok(StepResult::Continue)
            }
            INSTR_IS_TAGGED => {
                let v = self.pop()?;
                let r = if v.is_tagged() {
                    PolyWord::tagged(1)
                } else {
                    PolyWord::tagged(0)
                };
                self.push(r)?;
                Ok(StepResult::Continue)
            }

            // ----- Stack manipulation
            //
            // reset_N: pop N words, then push top. Equivalent to "slide".
            // reset_r_N: pop N words but keep the result that was on top.
            // In our flat-stack first-cut they collapse to the same
            // operation (they only differ when multiple results need
            // to be preserved, which is a feature not yet exercised).
            INSTR_RESET_1 | INSTR_RESET_R_1 => self.reset(1),
            INSTR_RESET_2 | INSTR_RESET_R_2 => self.reset(2),
            INSTR_RESET_R_3 => self.reset(3),
            INSTR_RESET_B | INSTR_RESET_R_B => {
                let n = self.fetch_u8()? as usize;
                self.reset(n)
            }

            // ----- Returns
            //
            // bytecode.cpp:467-470: returnCount is the number of words
            // to drop from the stack BELOW the return value. For our
            // first-cut interpreter without proper call frames, just
            // yield the top-of-stack and let the caller decide what to
            // do with the rest of the stack.
            INSTR_RETURN_1 => {
                let v = self.pop()?;
                Ok(StepResult::Returned(v))
            }
            INSTR_RETURN_2 => {
                let v = self.pop()?;
                let _ = self.pop()?;
                Ok(StepResult::Returned(v))
            }
            INSTR_RETURN_3 => {
                let v = self.pop()?;
                let _ = self.pop()?;
                let _ = self.pop()?;
                Ok(StepResult::Returned(v))
            }
            INSTR_RETURN_B => {
                let n = self.fetch_u8()? as usize;
                let v = self.pop()?;
                for _ in 0..n {
                    let _ = self.pop()?;
                }
                Ok(StepResult::Returned(v))
            }
            INSTR_RETURN_W => {
                let n = self.fetch_u16_le()? as usize;
                let v = self.pop()?;
                for _ in 0..n {
                    let _ = self.pop()?;
                }
                Ok(StepResult::Returned(v))
            }

            // ----- Everything else: surface to caller
            _ => {
                // Roll back the fetch so PC points at the unknown op for
                // the caller's inspection.
                self.pc -= 1;
                Ok(StepResult::Unimplemented(op))
            }
        }
    }

    fn dup_local(&mut self, depth: usize) -> Result<StepResult, InterpError> {
        let v = self.peek(depth)?;
        self.push(v)?;
        Ok(StepResult::Continue)
    }

    /// Slide-N-and-keep-top: pop the top, drop N words below, push the
    /// top back on. Used to clear scratch temporaries before returns or
    /// jumps.
    fn reset(&mut self, n: usize) -> Result<StepResult, InterpError> {
        let top = self.pop()?;
        for _ in 0..n {
            let _ = self.pop()?;
        }
        self.push(top)?;
        Ok(StepResult::Continue)
    }

    /// Pop two tagged ints, apply `f(x, y)` where `x` was popped first
    /// (so x is what was on TOP) and y was below it, push the result
    /// as a tagged int. Wrapping on overflow. `Err(())` from `f`
    /// signals divide-by-zero.
    fn bin_op_tagged<F>(&mut self, f: F) -> Result<StepResult, InterpError>
    where
        F: FnOnce(isize, isize) -> Result<isize, ()>,
    {
        let x = self.pop()?;
        let y = self.pop()?;
        let r = f(x.untag(), y.untag()).map_err(|()| InterpError::DivByZero { pc: self.pc })?;
        self.push(PolyWord::tagged(r))?;
        Ok(StepResult::Continue)
    }

    /// Pop two words, apply `f(x_bits, y_bits)`, push True/False.
    fn bin_op_cmp<F>(&mut self, f: F) -> Result<StepResult, InterpError>
    where
        F: FnOnce(usize, usize) -> bool,
    {
        let x = self.pop()?;
        let y = self.pop()?;
        let r = if f(x.0, y.0) {
            PolyWord::tagged(1)
        } else {
            PolyWord::tagged(0)
        };
        self.push(r)?;
        Ok(StepResult::Continue)
    }

    /// Word-level arithmetic: pop two raw `usize`s, apply `f`, push
    /// the result as a raw `PolyWord` (not re-tagged).
    fn bin_op_word<F>(&mut self, f: F) -> Result<StepResult, InterpError>
    where
        F: FnOnce(usize, usize) -> usize,
    {
        let x = self.pop()?;
        let y = self.pop()?;
        self.push(PolyWord::from_bits(f(x.0, y.0)))?;
        Ok(StepResult::Continue)
    }

    fn bin_op_word_checked<F>(&mut self, f: F) -> Result<StepResult, InterpError>
    where
        F: FnOnce(usize, usize) -> Result<usize, ()>,
    {
        let x = self.pop()?;
        let y = self.pop()?;
        let r = f(x.0, y.0).map_err(|()| InterpError::DivByZero { pc: self.pc })?;
        self.push(PolyWord::from_bits(r))?;
        Ok(StepResult::Continue)
    }

    /// `INDIRECT_N`: pop object pointer from top, push the Nth word
    /// of that object as the new top.
    ///
    /// # Safety considerations
    /// The pointer at the top of the stack MUST point at a valid
    /// PolyML heap object owned by a `MemorySpace` that out-lives the
    /// interpreter call. The interpreter cannot validate this; the
    /// caller (loader + compiled code, ultimately) is responsible.
    fn indirect(&mut self, n: usize) -> Result<StepResult, InterpError> {
        let obj_word = self.pop()?;
        let p = obj_word.as_ptr::<PolyWord>();
        // SAFETY: see method-level comment. We're trusting the caller.
        let field = unsafe { *p.add(n) };
        self.push(field)?;
        Ok(StepResult::Continue)
    }
}

#[cfg(test)]
mod tests {
    use super::opcodes::*;
    use super::*;

    /// Helper: build an interpreter, run, and assert the returned
    /// value's untagged integer matches.
    fn run_to_int(code: Vec<u8>) -> isize {
        let mut interp = Interpreter::new(64, code);
        match interp.run() {
            Ok(StepResult::Returned(w)) => w.untag(),
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn const_and_return() {
        // const_3; return_1  ->  3
        let code = vec![INSTR_CONST_3, INSTR_RETURN_1];
        assert_eq!(run_to_int(code), 3);
    }

    #[test]
    fn const_int_b() {
        // const_int_b 42; return_1  ->  42
        let code = vec![INSTR_CONST_INT_B, 42, INSTR_RETURN_1];
        assert_eq!(run_to_int(code), 42);
    }

    #[test]
    fn const_int_w() {
        // const_int_w 1234; return_1  ->  1234
        let code = vec![INSTR_CONST_INT_W, 0xd2, 0x04, INSTR_RETURN_1];
        assert_eq!(run_to_int(code), 1234);
    }

    #[test]
    fn fixed_add() {
        // const_3; const_4; fixedAdd; return_1  ->  7
        let code = vec![
            INSTR_CONST_3,
            INSTR_CONST_4,
            INSTR_FIXED_ADD,
            INSTR_RETURN_1,
        ];
        assert_eq!(run_to_int(code), 7);
    }

    #[test]
    fn fixed_sub_orientation() {
        // sub semantics: bytecode.cpp:931 — `t = UNTAGGED(y) - UNTAGGED(x)`
        // where x was on top. So const_10; const_3; fixedSub -> 10-3 = 7.
        let code = vec![
            INSTR_CONST_10,
            INSTR_CONST_3,
            INSTR_FIXED_SUB,
            INSTR_RETURN_1,
        ];
        assert_eq!(run_to_int(code), 7);
    }

    #[test]
    fn fixed_mult() {
        // 3 * 4 = 12
        let code = vec![
            INSTR_CONST_3,
            INSTR_CONST_4,
            INSTR_FIXED_MULT,
            INSTR_RETURN_1,
        ];
        assert_eq!(run_to_int(code), 12);
    }

    #[test]
    fn local_dup() {
        // const_4; local_0 (dup); fixedAdd  ->  4 + 4 = 8
        let code = vec![
            INSTR_CONST_4,
            INSTR_LOCAL_0,
            INSTR_FIXED_ADD,
            INSTR_RETURN_1,
        ];
        assert_eq!(run_to_int(code), 8);
    }

    #[test]
    fn local_n_deep() {
        // push 3, push 4, push 5; local_2 (peek 2 down = 3); return_1
        // Stack from top:  5, 4, 3   ; local_2 grabs 3.
        let code = vec![
            INSTR_CONST_3,
            INSTR_CONST_4,
            INSTR_CONST_INT_B,
            5,
            INSTR_LOCAL_2,
            INSTR_RETURN_1,
        ];
        assert_eq!(run_to_int(code), 3);
    }

    #[test]
    fn jump_forward() {
        // const_3; jump8 1 (skip the next byte); const_4; return_1
        // After jump we skip the const_4, leaving const_3 on top -> 3.
        // But "jump 1" skips ONE byte past the offset byte, which lands
        // us on the byte AFTER the const_4 opcode... hmm, let me build:
        // bytes:  [CONST_3, JUMP8, 1, CONST_4, RETURN_1]
        // After fetch jump8 at pc=1, fetch_u8 puts pc=3 and off=1.
        // `pc += 1` -> pc=4 (the RETURN_1).
        let code = vec![
            INSTR_CONST_3, // pc=0
            INSTR_JUMP8,   // pc=1
            1,             // pc=2: offset
            INSTR_CONST_4, // pc=3 (skipped)
            INSTR_RETURN_1, // pc=4 (landing)
        ];
        assert_eq!(run_to_int(code), 3);
    }

    #[test]
    fn jump_false_taken() {
        // const_0 (False); jump8_false 1; const_4; const_3; return_1
        // Stack: pop False; condition is False -> jump taken; skip const_4;
        // run const_3; return_1 -> 3.
        let code = vec![
            INSTR_CONST_0,
            INSTR_JUMP8_FALSE,
            1,
            INSTR_CONST_4,
            INSTR_CONST_3,
            INSTR_RETURN_1,
        ];
        assert_eq!(run_to_int(code), 3);
    }

    #[test]
    fn jump_false_not_taken() {
        // const_1 (True); jump8_false 1; const_4; const_3; return_1
        // Stack: pop True; condition is not False -> no jump;
        // const_4 runs; const_3 runs; return_1 returns top = 3.
        let code = vec![
            INSTR_CONST_1,
            INSTR_JUMP8_FALSE,
            1,
            INSTR_CONST_4,
            INSTR_CONST_3,
            INSTR_RETURN_1,
        ];
        assert_eq!(run_to_int(code), 3);
        // To distinguish from previous: make const_4 the one returned
        // when falsity does NOT cause a jump:
        let code = vec![
            INSTR_CONST_1,
            INSTR_JUMP8_FALSE,
            2,
            INSTR_CONST_4,
            INSTR_RETURN_1, // executed when no jump
            INSTR_CONST_3,
            INSTR_RETURN_1,
        ];
        assert_eq!(run_to_int(code), 4);
    }

    #[test]
    fn equality() {
        // 3 == 3 -> True (1)
        let code = vec![
            INSTR_CONST_3,
            INSTR_CONST_3,
            INSTR_EQUAL_WORD,
            INSTR_RETURN_1,
        ];
        assert_eq!(run_to_int(code), 1);
        // 3 == 4 -> False (0)
        let code = vec![
            INSTR_CONST_3,
            INSTR_CONST_4,
            INSTR_EQUAL_WORD,
            INSTR_RETURN_1,
        ];
        assert_eq!(run_to_int(code), 0);
    }

    #[test]
    fn less_signed() {
        // 3 < 4 -> True. bin_op_cmp: y < x with x popped first.
        // So we push y first (3), then x (4): "(y=3) < (x=4)" -> True.
        let code = vec![
            INSTR_CONST_3,
            INSTR_CONST_4,
            INSTR_LESS_SIGNED,
            INSTR_RETURN_1,
        ];
        assert_eq!(run_to_int(code), 1);
        // 4 < 3 -> False
        let code = vec![
            INSTR_CONST_4,
            INSTR_CONST_3,
            INSTR_LESS_SIGNED,
            INSTR_RETURN_1,
        ];
        assert_eq!(run_to_int(code), 0);
    }

    #[test]
    fn not_boolean() {
        // const_0; not -> True
        let code = vec![INSTR_CONST_0, INSTR_NOT_BOOLEAN, INSTR_RETURN_1];
        assert_eq!(run_to_int(code), 1);
        // const_1; not -> False
        let code = vec![INSTR_CONST_1, INSTR_NOT_BOOLEAN, INSTR_RETURN_1];
        assert_eq!(run_to_int(code), 0);
    }

    #[test]
    fn is_tagged() {
        // const_3 is tagged -> True
        let code = vec![INSTR_CONST_3, INSTR_IS_TAGGED, INSTR_RETURN_1];
        assert_eq!(run_to_int(code), 1);
    }

    #[test]
    fn reset_slide() {
        // const_1, const_2, const_3, reset_2; return_1
        //   pushes 1, 2, 3; reset_2 pops the top (3), pops 2 more (2, 1),
        //   pushes 3 back. Net: stack has just [3]. return_1 returns 3.
        let code = vec![
            INSTR_CONST_1,
            INSTR_CONST_2,
            INSTR_CONST_3,
            INSTR_RESET_2,
            INSTR_RETURN_1,
        ];
        assert_eq!(run_to_int(code), 3);
    }

    #[test]
    fn loop_via_jump_back() {
        // Tight loop: count from 1 down to 0, return 0.
        //
        //   const_int_b 5            ; push counter=5
        //   .top:
        //   const_int_b 1            ; push 1
        //   fixedSub                 ; counter -= 1
        //   local_0                  ; dup counter
        //   const_0                  ; push 0
        //   equalWord                ; counter == 0 ?
        //   jump8_false (offset to .top, taken when False)
        //   return_1
        //
        // Layout (byte offsets):
        //   0: CONST_INT_B
        //   1: 5
        //   2: CONST_INT_B   <- .top
        //   3: 1
        //   4: FIXED_SUB
        //   5: LOCAL_0
        //   6: CONST_0
        //   7: EQUAL_WORD
        //   8: JUMP8_FALSE
        //   9: offset byte
        //  10: RETURN_1
        //
        // The jump_false at pc=8 fetches the offset at pc=9, advances
        // pc to 10. To jump back to .top (pc=2), we need a backward
        // offset — but jump8_false takes an UNSIGNED forward offset.
        // For the loop we'd need jump_back8 instead, and a different
        // control structure. Let me build that.
        //
        //   const_int_b 5      pc 0-1
        //   .top:              pc 2
        //   const_int_b 1      pc 2-3
        //   fixedSub           pc 4
        //   local_0            pc 5
        //   const_0            pc 6
        //   equalWord          pc 7  (top is True if counter==0)
        //   jump8_true 2       pc 8-9 (forward to RETURN_1)
        //   jump_back8 N       pc 10-11 (back to .top = pc 2)
        //   return_1           pc 12
        //
        // jump_back8 at pc=10: fetches offset at pc=11, then pc=12,
        // then subtracts (off + 1). For destination pc=2: 12 - (off+1) = 2,
        // so off = 9.
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
            2, // forward 2 -> skip jump_back8 to RETURN_1
            INSTR_JUMP_BACK8,
            9, // back to pc=2
            INSTR_RETURN_1,
        ];
        assert_eq!(run_to_int(code), 0);
    }

    #[test]
    fn unimplemented_surface_correctly() {
        // INSTR_CALL_CLOSURE (0x0c) isn't implemented yet.
        let code = vec![INSTR_CALL_CLOSURE];
        let mut interp = Interpreter::new(64, code);
        match interp.run().unwrap() {
            StepResult::Unimplemented(op) => assert_eq!(op, INSTR_CALL_CLOSURE),
            other => panic!("expected Unimplemented, got {other:?}"),
        }
        // PC should point AT the unimplemented op, not past it.
        assert_eq!(interp.pc(), 0);
    }
}
