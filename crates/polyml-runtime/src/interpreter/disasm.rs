//! Bytecode disassembler.
//!
//! Decodes PolyML bytecode into human-readable form. Useful for:
//! - The `poly disasm` CLI subcommand
//! - JIT translation error messages ("unsupported X at pc=Y")
//! - The profiler's hot-PC dump
//! - The diff tester's `--list` view
//!
//! The decoder is best-effort: unknown opcodes get a `?` mnemonic
//! and `total_len=1`. For known opcodes, it returns the mnemonic,
//! the total length of the instruction (opcode + immediates), and
//! a human-readable summary of the immediate operands.
//!
//! Notable variable-length opcodes:
//! - `CASE16` (0x0a): `[op] [arg1 u16 LE] [arg1 entries of u16 LE]`.
//!   Total length = `1 + 2 + arg1*2`.
//! - `ESCAPE` (0xfe): one-byte prefix; the actual opcode is the next
//!   byte. Total length = 2 (we don't yet decode extended mnemonics).
//!
//! Both are handled.

use crate::interpreter::opcodes::*;

/// A single decoded instruction.
#[derive(Debug, Clone)]
pub struct DecodedOp {
    /// Raw opcode byte at this PC.
    pub op: u8,
    /// Stable mnemonic, or "?" for unknown opcodes.
    pub mnemonic: &'static str,
    /// Total length of this instruction in bytes (opcode + all
    /// immediate bytes). Caller advances `pc` by this amount.
    pub total_len: usize,
    /// Human-readable summary of the immediates, if any.
    /// e.g., `"depth=4 off=42"` for JUMP_TAGGED_LOCAL,
    /// `"+3"` for JUMP8, `"7 cases, default at +14"` for CASE16.
    pub imm_text: Option<String>,
}

/// Decode the instruction at `bytecode[pc]`. Returns a `DecodedOp`
/// with `total_len=1` and `mnemonic="?"` for unknown opcodes (or
/// truncated bytecode), so the caller can keep walking.
#[must_use]
pub fn decode(bytecode: &[u8], pc: usize) -> DecodedOp {
    if pc >= bytecode.len() {
        return DecodedOp {
            op: 0,
            mnemonic: "<EOF>",
            total_len: 0,
            imm_text: None,
        };
    }
    let op = bytecode[pc];
    let mnemonic = opcode_name(op);

    // Variable-length: CASE16 has a u16 count + count*u16 entries.
    if op == INSTR_CASE16 {
        if pc + 2 < bytecode.len() {
            let arg1 = u16::from_le_bytes([bytecode[pc + 1], bytecode[pc + 2]]) as usize;
            return DecodedOp {
                op,
                mnemonic,
                total_len: 1 + 2 + arg1 * 2,
                imm_text: Some(format!("{arg1} cases")),
            };
        }
        return DecodedOp {
            op,
            mnemonic,
            total_len: 1,
            imm_text: Some("truncated".into()),
        };
    }

    // ESCAPE: 1 prefix byte + 1 extended opcode byte. We don't decode
    // the extended opcode here, just note its raw value.
    if op == INSTR_ESCAPE {
        let ext = bytecode.get(pc + 1).copied().unwrap_or(0);
        return DecodedOp {
            op,
            mnemonic,
            total_len: 2,
            imm_text: Some(format!("ext=0x{ext:02x}")),
        };
    }

    let imm = imm_bytes(op);
    let total_len = 1 + imm;
    let imm_text = if imm == 0 || pc + imm >= bytecode.len() {
        None
    } else {
        Some(format_imm(op, &bytecode[pc + 1..pc + 1 + imm]))
    };
    DecodedOp {
        op,
        mnemonic,
        total_len,
        imm_text,
    }
}

/// Format the immediate bytes of a known opcode into a readable
/// summary. Falls back to hex on unknown shapes.
fn format_imm(op: u8, imm: &[u8]) -> String {
    match op {
        // Single byte: a small unsigned operand.
        INSTR_JUMP8 | INSTR_JUMP8_FALSE | INSTR_JUMP8_TRUE | INSTR_JUMP_BACK8 => {
            format!("+{}", imm[0])
        }
        INSTR_LOCAL_B => format!("depth={}", imm[0]),
        INSTR_INDIRECT_B => format!("idx={}", imm[0]),
        INSTR_CONST_INT_B => format!("={}", imm[0] as i8),
        INSTR_RESET_B | INSTR_RESET_R_B | INSTR_RETURN_B => format!("n={}", imm[0]),
        INSTR_TUPLE_B => format!("n={}", imm[0]),
        INSTR_CLOSURE_B => format!("captures={}", imm[0]),
        INSTR_SET_HANDLER8 => format!("off=+{}", imm[0]),
        INSTR_PUSH_HANDLER => "".into(),
        INSTR_CALL_FAST_RTS0 | INSTR_CALL_FAST_RTS1 | INSTR_CALL_FAST_RTS2
        | INSTR_CALL_FAST_RTS3 | INSTR_CALL_FAST_RTS4 | INSTR_CALL_FAST_RTS5 => {
            format!("stub_op={}", imm[0])
        }
        INSTR_MOVE_TO_CONTAINER_B | INSTR_SET_STACK_VAL_B => format!("slot={}", imm[0]),
        INSTR_STACK_CONTAINER_B => format!("n={}", imm[0]),
        INSTR_INDIRECT_CONTAINER_B => format!("slot={}", imm[0]),
        INSTR_INDIRECT_CLOSURE_B0 | INSTR_INDIRECT_CLOSURE_B1 | INSTR_INDIRECT_CLOSURE_B2 => {
            format!("depth={}", imm[0])
        }
        INSTR_INDIRECT_LOCAL_B0 | INSTR_INDIRECT_LOCAL_B1 => format!("depth={}", imm[0]),
        INSTR_MOVE_TO_MUT_CLOSURE_B | INSTR_ALLOC_MUT_CLOSURE_B => format!("n={}", imm[0]),
        INSTR_CALL_LOCAL_B => format!("n_args={}", imm[0]),
        INSTR_CONST_ADDR8_0 | INSTR_CONST_ADDR8_1 => format!("off=+{}", imm[0]),
        INSTR_CALL_CONST_ADDR8_0 | INSTR_CALL_CONST_ADDR8_1 => format!("off=+{}", imm[0]),

        // Two bytes: usually a u16 LE.
        INSTR_JUMP16 | INSTR_JUMP16_FALSE | INSTR_JUMP16_TRUE | INSTR_JUMP_BACK16 => {
            let v = u16::from_le_bytes([imm[0], imm[1]]);
            format!("+{v}")
        }
        INSTR_LOCAL_W => {
            let v = u16::from_le_bytes([imm[0], imm[1]]);
            format!("depth={v}")
        }
        INSTR_CONST_INT_W | INSTR_RETURN_W => {
            let v = u16::from_le_bytes([imm[0], imm[1]]);
            format!("={v}")
        }
        INSTR_SET_HANDLER16 => {
            let v = u16::from_le_bytes([imm[0], imm[1]]);
            format!("off=+{v}")
        }
        INSTR_INDIRECT_LOCAL_BB | INSTR_INDIRECT_CLOSURE_BB => {
            format!("depth={} slot={}", imm[0], imm[1])
        }
        INSTR_TAIL_B_B => {
            format!("tc={} rc={}", imm[0], imm[1])
        }
        INSTR_CONST_ADDR8_8 | INSTR_CALL_CONST_ADDR8_8 => {
            format!("off=+{} idx={}", imm[0], imm[1])
        }
        INSTR_JUMP_TAGGED_LOCAL => format!("depth={} off=+{}", imm[0], imm[1]),
        INSTR_JUMP_NEQ_LOCAL | INSTR_JUMP_NEQ_LOCAL_IND => {
            // 3-byte imm but our table says 2 for INDIRECT_*. This
            // branch handles the 2-byte case; the 3-byte is fixed
            // up in imm_bytes if you call this with 3.
            format!("depth={} want={}", imm[0], imm[1])
        }

        // Three+ bytes: render as hex by default.
        _ => imm
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<Vec<_>>()
            .join(" "),
    }
}

/// Mnemonic for an opcode byte. Returns `"?"` for unknown opcodes.
#[must_use]
pub fn opcode_name(op: u8) -> &'static str {
    match op {
        INSTR_JUMP8 => "JUMP8",
        INSTR_JUMP8_FALSE => "JUMP8_FALSE",
        INSTR_JUMP8_TRUE => "JUMP8_TRUE",
        INSTR_JUMP16 => "JUMP16",
        INSTR_JUMP16_FALSE => "JUMP16_FALSE",
        INSTR_JUMP16_TRUE => "JUMP16_TRUE",
        INSTR_JUMP_BACK8 => "JUMP_BACK8",
        INSTR_JUMP_BACK16 => "JUMP_BACK16",
        INSTR_LOAD_ML_WORD => "LOAD_ML_WORD",
        INSTR_LOAD_ML_BYTE => "LOAD_ML_BYTE",
        INSTR_STORE_ML_WORD => "STORE_ML_WORD",
        INSTR_STORE_ML_BYTE => "STORE_ML_BYTE",
        INSTR_LOAD_UNTAGGED => "LOAD_UNTAGGED",
        INSTR_STORE_UNTAGGED => "STORE_UNTAGGED",
        INSTR_ALLOC_REF => "ALLOC_REF",
        INSTR_ALLOC_WORD_MEMORY => "ALLOC_WORD_MEMORY",
        INSTR_ALLOC_BYTE_MEM => "ALLOC_BYTE_MEM",
        INSTR_ALLOC_MUT_CLOSURE_B => "ALLOC_MUT_CLOSURE_B",
        INSTR_BLOCK_MOVE_WORD => "BLOCK_MOVE_WORD",
        INSTR_BLOCK_MOVE_BYTE => "BLOCK_MOVE_BYTE",
        INSTR_BLOCK_EQUAL_BYTE => "BLOCK_EQUAL_BYTE",
        INSTR_BLOCK_COMPARE_BYTE => "BLOCK_COMPARE_BYTE",
        INSTR_CASE16 => "CASE16",
        INSTR_CALL_CLOSURE => "CALL_CLOSURE",
        INSTR_CALL_LOCAL_B => "CALL_LOCAL_B",
        INSTR_CALL_CONST_ADDR8_0 => "CALL_CONST_ADDR8_0",
        INSTR_CALL_CONST_ADDR8_1 => "CALL_CONST_ADDR8_1",
        INSTR_CALL_CONST_ADDR8_8 => "CALL_CONST_ADDR8_8",
        INSTR_CALL_CONST_ADDR16_8 => "CALL_CONST_ADDR16_8",
        INSTR_CALL_FAST_RTS0 => "CALL_FAST_RTS0",
        INSTR_CALL_FAST_RTS1 => "CALL_FAST_RTS1",
        INSTR_CALL_FAST_RTS2 => "CALL_FAST_RTS2",
        INSTR_CALL_FAST_RTS3 => "CALL_FAST_RTS3",
        INSTR_CALL_FAST_RTS4 => "CALL_FAST_RTS4",
        INSTR_CALL_FAST_RTS5 => "CALL_FAST_RTS5",
        INSTR_RETURN_W => "RETURN_W",
        INSTR_RETURN_B => "RETURN_B",
        INSTR_RETURN_1 => "RETURN_1",
        INSTR_RETURN_2 => "RETURN_2",
        INSTR_RETURN_3 => "RETURN_3",
        INSTR_STACK_CONTAINER_B => "STACK_CONTAINER_B",
        INSTR_STACK_SIZE16 => "STACK_SIZE16",
        INSTR_RAISE_EX => "RAISE_EX",
        INSTR_CONST_ADDR16_8 => "CONST_ADDR16_8",
        INSTR_CONST_ADDR8_8 => "CONST_ADDR8_8",
        INSTR_CONST_ADDR8_0 => "CONST_ADDR8_0",
        INSTR_CONST_ADDR8_1 => "CONST_ADDR8_1",
        INSTR_CONST_INT_W => "CONST_INT_W",
        INSTR_INDIRECT_LOCAL_BB => "INDIRECT_LOCAL_BB",
        INSTR_INDIRECT_LOCAL_B0 => "INDIRECT_LOCAL_B0",
        INSTR_INDIRECT_LOCAL_B1 => "INDIRECT_LOCAL_B1",
        INSTR_INDIRECT_CLOSURE_BB => "INDIRECT_CLOSURE_BB",
        INSTR_INDIRECT_CLOSURE_B0 => "INDIRECT_CLOSURE_B0",
        INSTR_INDIRECT_CLOSURE_B1 => "INDIRECT_CLOSURE_B1",
        INSTR_INDIRECT_CLOSURE_B2 => "INDIRECT_CLOSURE_B2",
        INSTR_INDIRECT_CONTAINER_B => "INDIRECT_CONTAINER_B",
        INSTR_INDIRECT_0_LOCAL_0 => "INDIRECT_0_LOCAL_0",
        INSTR_LOCAL_W => "LOCAL_W",
        INSTR_LOCAL_B => "LOCAL_B",
        INSTR_INDIRECT_B => "INDIRECT_B",
        INSTR_MOVE_TO_CONTAINER_B => "MOVE_TO_CONTAINER_B",
        INSTR_MOVE_TO_MUT_CLOSURE_B => "MOVE_TO_MUT_CLOSURE_B",
        INSTR_SET_STACK_VAL_B => "SET_STACK_VAL_B",
        INSTR_RESET_B => "RESET_B",
        INSTR_RESET_R_B => "RESET_R_B",
        INSTR_RESET_1 => "RESET_1",
        INSTR_RESET_2 => "RESET_2",
        INSTR_RESET_R_1 => "RESET_R_1",
        INSTR_RESET_R_2 => "RESET_R_2",
        INSTR_RESET_R_3 => "RESET_R_3",
        INSTR_CONST_INT_B => "CONST_INT_B",
        INSTR_LOCAL_0 => "LOCAL_0",
        INSTR_LOCAL_1 => "LOCAL_1",
        INSTR_LOCAL_2 => "LOCAL_2",
        INSTR_LOCAL_3 => "LOCAL_3",
        INSTR_LOCAL_4 => "LOCAL_4",
        INSTR_LOCAL_5 => "LOCAL_5",
        INSTR_LOCAL_6 => "LOCAL_6",
        INSTR_LOCAL_7 => "LOCAL_7",
        INSTR_LOCAL_8 => "LOCAL_8",
        INSTR_LOCAL_9 => "LOCAL_9",
        INSTR_LOCAL_10 => "LOCAL_10",
        INSTR_LOCAL_11 => "LOCAL_11",
        INSTR_LOCAL_12 => "LOCAL_12",
        INSTR_LOCAL_13 => "LOCAL_13",
        INSTR_LOCAL_14 => "LOCAL_14",
        INSTR_LOCAL_15 => "LOCAL_15",
        INSTR_INDIRECT_0 => "INDIRECT_0",
        INSTR_INDIRECT_1 => "INDIRECT_1",
        INSTR_INDIRECT_2 => "INDIRECT_2",
        INSTR_INDIRECT_3 => "INDIRECT_3",
        INSTR_INDIRECT_4 => "INDIRECT_4",
        INSTR_INDIRECT_5 => "INDIRECT_5",
        INSTR_CONST_0 => "CONST_0",
        INSTR_CONST_1 => "CONST_1",
        INSTR_CONST_2 => "CONST_2",
        INSTR_CONST_3 => "CONST_3",
        INSTR_CONST_4 => "CONST_4",
        INSTR_CONST_10 => "CONST_10",
        INSTR_NO_OP => "NO_OP",
        INSTR_TUPLE_B => "TUPLE_B",
        INSTR_TUPLE_2 => "TUPLE_2",
        INSTR_TUPLE_3 => "TUPLE_3",
        INSTR_TUPLE_4 => "TUPLE_4",
        INSTR_LOCK => "LOCK",
        INSTR_LDEXC => "LDEXC",
        INSTR_PUSH_HANDLER => "PUSH_HANDLER",
        INSTR_TAIL_B_B => "TAIL_B_B",
        INSTR_SET_HANDLER8 => "SET_HANDLER8",
        INSTR_SET_HANDLER16 => "SET_HANDLER16",
        INSTR_DELETE_HANDLER => "DELETE_HANDLER",
        INSTR_NOT_BOOLEAN => "NOT_BOOLEAN",
        INSTR_IS_TAGGED => "IS_TAGGED",
        INSTR_IS_TAGGED_LOCAL_B => "IS_TAGGED_LOCAL_B",
        INSTR_CELL_LENGTH => "CELL_LENGTH",
        INSTR_CELL_FLAGS => "CELL_FLAGS",
        INSTR_CLEAR_MUTABLE => "CLEAR_MUTABLE",
        INSTR_EQUAL_WORD => "EQUAL_WORD",
        INSTR_LESS_SIGNED => "LESS_SIGNED",
        INSTR_LESS_UNSIGNED => "LESS_UNSIGNED",
        INSTR_LESS_EQ_SIGNED => "LESS_EQ_SIGNED",
        INSTR_LESS_EQ_UNSIGNED => "LESS_EQ_UNSIGNED",
        INSTR_GREATER_SIGNED => "GREATER_SIGNED",
        INSTR_GREATER_UNSIGNED => "GREATER_UNSIGNED",
        INSTR_GREATER_EQ_SIGNED => "GREATER_EQ_SIGNED",
        INSTR_GREATER_EQ_UNSIGNED => "GREATER_EQ_UNSIGNED",
        INSTR_FIXED_ADD => "FIXED_ADD",
        INSTR_FIXED_SUB => "FIXED_SUB",
        INSTR_FIXED_MULT => "FIXED_MULT",
        INSTR_FIXED_QUOT => "FIXED_QUOT",
        INSTR_FIXED_REM => "FIXED_REM",
        INSTR_WORD_ADD => "WORD_ADD",
        INSTR_WORD_SUB => "WORD_SUB",
        INSTR_WORD_MULT => "WORD_MULT",
        INSTR_WORD_DIV => "WORD_DIV",
        INSTR_WORD_MOD => "WORD_MOD",
        INSTR_WORD_AND => "WORD_AND",
        INSTR_WORD_OR => "WORD_OR",
        INSTR_WORD_XOR => "WORD_XOR",
        INSTR_WORD_SHIFT_LEFT => "WORD_SHIFT_LEFT",
        INSTR_WORD_SHIFT_R_LOG => "WORD_SHIFT_R_LOG",
        INSTR_ARB_ADD => "ARB_ADD",
        INSTR_ARB_SUBTRACT => "ARB_SUBTRACT",
        INSTR_ARB_MULTIPLY => "ARB_MULTIPLY",
        INSTR_ATOMIC_INCR => "ATOMIC_INCR",
        INSTR_ATOMIC_DECR => "ATOMIC_DECR",
        INSTR_GET_THREAD_ID => "GET_THREAD_ID",
        INSTR_JUMP_TAGGED_LOCAL => "JUMP_TAGGED_LOCAL",
        INSTR_JUMP_NEQ_LOCAL => "JUMP_NEQ_LOCAL",
        INSTR_JUMP_NEQ_LOCAL_IND => "JUMP_NEQ_LOCAL_IND",
        INSTR_CLOSURE_B => "CLOSURE_B",
        INSTR_ESCAPE => "ESCAPE",
        INSTR_ENTER_INT_X86 => "ENTER_INT_X86",
        INSTR_ENTER_INT_ARM64 => "ENTER_INT_ARM64",
        _ => "?",
    }
}

/// Number of immediate bytes (NOT including the opcode itself) for
/// a given opcode. Returns 0 for unknown/zero-arg opcodes.
///
/// CASE16 and ESCAPE are special-cased in [`decode`] because their
/// length isn't constant.
#[must_use]
pub fn imm_bytes(op: u8) -> usize {
    match op {
        INSTR_JUMP8
        | INSTR_JUMP8_FALSE
        | INSTR_JUMP8_TRUE
        | INSTR_JUMP_BACK8
        | INSTR_LOCAL_B
        | INSTR_INDIRECT_B
        | INSTR_CONST_INT_B
        | INSTR_RESET_B
        | INSTR_RESET_R_B
        | INSTR_RETURN_B
        | INSTR_TUPLE_B
        | INSTR_CLOSURE_B
        | INSTR_SET_HANDLER8
        | INSTR_PUSH_HANDLER
        | INSTR_MOVE_TO_CONTAINER_B
        | INSTR_SET_STACK_VAL_B
        | INSTR_STACK_CONTAINER_B
        | INSTR_INDIRECT_CONTAINER_B
        | INSTR_INDIRECT_CLOSURE_B0
        | INSTR_INDIRECT_CLOSURE_B1
        | INSTR_INDIRECT_CLOSURE_B2
        | INSTR_INDIRECT_LOCAL_B0
        | INSTR_INDIRECT_LOCAL_B1
        | INSTR_IS_TAGGED_LOCAL_B
        | INSTR_MOVE_TO_MUT_CLOSURE_B
        | INSTR_ALLOC_MUT_CLOSURE_B
        | INSTR_CALL_LOCAL_B
        | INSTR_CONST_ADDR8_0
        | INSTR_CONST_ADDR8_1
        | INSTR_CALL_CONST_ADDR8_0
        | INSTR_CALL_CONST_ADDR8_1
        | INSTR_CALL_FAST_RTS0
        | INSTR_CALL_FAST_RTS1
        | INSTR_CALL_FAST_RTS2
        | INSTR_CALL_FAST_RTS3
        | INSTR_CALL_FAST_RTS4
        | INSTR_CALL_FAST_RTS5 => 1,
        INSTR_JUMP16 | INSTR_JUMP16_FALSE | INSTR_JUMP16_TRUE | INSTR_JUMP_BACK16
        | INSTR_LOCAL_W | INSTR_CONST_INT_W | INSTR_RETURN_W | INSTR_SET_HANDLER16
        | INSTR_STACK_SIZE16 => 2,
        INSTR_INDIRECT_LOCAL_BB
        | INSTR_INDIRECT_CLOSURE_BB
        | INSTR_CONST_ADDR8_8
        | INSTR_CALL_CONST_ADDR8_8
        | INSTR_JUMP_TAGGED_LOCAL
        | INSTR_TAIL_B_B => 2,
        INSTR_JUMP_NEQ_LOCAL | INSTR_JUMP_NEQ_LOCAL_IND => 3,
        INSTR_CONST_ADDR16_8 | INSTR_CALL_CONST_ADDR16_8 => 3,
        _ => 0,
    }
}

/// Disassemble an entire bytecode body. Returns one `DecodedOp` per
/// instruction, terminating at the body length.
#[must_use]
pub fn disassemble(bytecode: &[u8]) -> Vec<(usize, DecodedOp)> {
    let mut out = Vec::new();
    let mut pc = 0;
    while pc < bytecode.len() {
        let d = decode(bytecode, pc);
        let step = d.total_len.max(1); // never advance by 0
        out.push((pc, d));
        pc += step;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_simple_arith() {
        // LOCAL_2; CONST_INT_B 3; FIXED_ADD; RETURN_1
        let bc = vec![0x2b, 0x28, 0x03, 0xaa, 0x42];
        let decoded = disassemble(&bc);
        assert_eq!(decoded.len(), 4);
        assert_eq!(decoded[0].1.mnemonic, "LOCAL_2");
        assert_eq!(decoded[0].1.total_len, 1);
        assert_eq!(decoded[1].1.mnemonic, "CONST_INT_B");
        assert_eq!(decoded[1].1.imm_text.as_deref(), Some("=3"));
        assert_eq!(decoded[1].1.total_len, 2);
        assert_eq!(decoded[2].1.mnemonic, "FIXED_ADD");
        assert_eq!(decoded[3].1.mnemonic, "RETURN_1");
    }

    #[test]
    fn decode_case16_variable_length() {
        // CASE16 [0x03 0x00] = 3 cases, then 3 u16 entries.
        let bc = vec![0x0a, 0x03, 0x00, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff];
        let d = decode(&bc, 0);
        assert_eq!(d.mnemonic, "CASE16");
        assert_eq!(d.total_len, 1 + 2 + 3 * 2); // = 9
        assert_eq!(d.imm_text.as_deref(), Some("3 cases"));
    }

    #[test]
    fn decode_jump_tagged_local() {
        // JUMP_TAGGED_LOCAL depth=4 off=42
        let bc = vec![0xc4, 0x04, 0x2a];
        let d = decode(&bc, 0);
        assert_eq!(d.mnemonic, "JUMP_TAGGED_LOCAL");
        assert_eq!(d.total_len, 3);
        assert_eq!(d.imm_text.as_deref(), Some("depth=4 off=+42"));
    }

    #[test]
    fn decode_unknown_returns_question() {
        // Use a byte that's not a known opcode.
        let d = decode(&[0xfd], 0); // 0xfd alone (not after ESCAPE)
        assert_eq!(d.mnemonic, "?");
    }

    #[test]
    fn decode_is_tagged_local_b_has_operand() {
        // Regression: IS_TAGGED_LOCAL_B (0xc2) takes a 1-byte local index.
        // It was missing from imm_bytes, so it decoded as length 1 and
        // MISALIGNED every following instruction — which made the IntInf.andb
        // bytecode (task #72) undecodable until fixed.
        let d = decode(&[INSTR_IS_TAGGED_LOCAL_B, 0x01], 0);
        assert_eq!(d.mnemonic, "IS_TAGGED_LOCAL_B");
        assert_eq!(d.total_len, 2, "0xc2 must consume its local-index operand");
        // A two-instruction stream must decode to exactly two ops, in step.
        let stream = vec![INSTR_IS_TAGGED_LOCAL_B, 0x01, INSTR_JUMP8_FALSE, 0x05];
        let ops = disassemble(&stream);
        assert_eq!(
            ops.len(),
            2,
            "operand must not be mis-decoded as a second opcode"
        );
        assert_eq!(ops[1].1.mnemonic, "JUMP8_FALSE");
    }
}
