//! Opcode constants for PolyML's bytecode interpreter.
//!
//! Ported verbatim from `vendor/polyml/libpolyml/int_opcodes.h`. The
//! original numbering is sparse and historically driven (gaps for
//! removed opcodes, legacy aliases); we preserve the same byte values
//! so a dispatch table indexed by `pc[0]` works identically to the
//! C++ interpreter.
//!
//! All names are `SCREAMING_SNAKE_CASE` for Rust conventions; the
//! original `INSTR_camelCase` names are referenced in comments where
//! useful.
//!
//! Extended opcodes (preceded by [`INSTR_ESCAPE`] = 0xfe) live in a
//! separate `ext` submodule below.

// ----- Base opcodes ----------------------------------------------------

pub const INSTR_JUMP8: u8 = 0x02;
pub const INSTR_JUMP8_FALSE: u8 = 0x03;
pub const INSTR_LOAD_ML_WORD: u8 = 0x04;
pub const INSTR_STORE_ML_WORD: u8 = 0x05;
pub const INSTR_ALLOC_REF: u8 = 0x06;
pub const INSTR_BLOCK_MOVE_WORD: u8 = 0x07;
pub const INSTR_LOAD_UNTAGGED: u8 = 0x08;
pub const INSTR_STORE_UNTAGGED: u8 = 0x09;
pub const INSTR_CASE16: u8 = 0x0a;
pub const INSTR_CALL_CLOSURE: u8 = 0x0c;
pub const INSTR_RETURN_W: u8 = 0x0d;
pub const INSTR_STACK_CONTAINER_B: u8 = 0x0e;
pub const INSTR_RAISE_EX: u8 = 0x10;
pub const INSTR_CALL_CONST_ADDR16: u8 = 0x11; // Legacy
pub const INSTR_CALL_CONST_ADDR8: u8 = 0x12; // Legacy
pub const INSTR_LOCAL_W: u8 = 0x13;
pub const INSTR_CONST_ADDR16_8: u8 = 0x14;
pub const INSTR_CONST_ADDR8_8: u8 = 0x15;
pub const INSTR_CALL_LOCAL_B: u8 = 0x16;
pub const INSTR_CALL_CONST_ADDR8_8: u8 = 0x17;
pub const INSTR_CALL_CONST_ADDR16_8: u8 = 0x18;
pub const INSTR_CONST_ADDR16: u8 = 0x1a; // Legacy
pub const INSTR_CONST_INT_W: u8 = 0x1b;
pub const INSTR_JUMP_BACK8: u8 = 0x1e;
pub const INSTR_RETURN_B: u8 = 0x1f;
pub const INSTR_JUMP_BACK16: u8 = 0x20;
pub const INSTR_INDIRECT_LOCAL_BB: u8 = 0x21;
pub const INSTR_LOCAL_B: u8 = 0x22;
pub const INSTR_INDIRECT_B: u8 = 0x23;
pub const INSTR_MOVE_TO_CONTAINER_B: u8 = 0x24;
pub const INSTR_SET_STACK_VAL_B: u8 = 0x25;
pub const INSTR_RESET_B: u8 = 0x26;
pub const INSTR_RESET_R_B: u8 = 0x27;
pub const INSTR_CONST_INT_B: u8 = 0x28;
pub const INSTR_LOCAL_0: u8 = 0x29;
pub const INSTR_LOCAL_1: u8 = 0x2a;
pub const INSTR_LOCAL_2: u8 = 0x2b;
pub const INSTR_LOCAL_3: u8 = 0x2c;
pub const INSTR_LOCAL_4: u8 = 0x2d;
pub const INSTR_LOCAL_5: u8 = 0x2e;
pub const INSTR_LOCAL_6: u8 = 0x2f;
pub const INSTR_LOCAL_7: u8 = 0x30;
pub const INSTR_LOCAL_8: u8 = 0x31;
pub const INSTR_LOCAL_9: u8 = 0x32;
pub const INSTR_LOCAL_10: u8 = 0x33;
pub const INSTR_LOCAL_11: u8 = 0x34;
pub const INSTR_INDIRECT_0: u8 = 0x35;
pub const INSTR_INDIRECT_1: u8 = 0x36;
pub const INSTR_INDIRECT_2: u8 = 0x37;
pub const INSTR_INDIRECT_3: u8 = 0x38;
pub const INSTR_INDIRECT_4: u8 = 0x39;
pub const INSTR_INDIRECT_5: u8 = 0x3a;
pub const INSTR_CONST_0: u8 = 0x3b;
pub const INSTR_CONST_1: u8 = 0x3c;
pub const INSTR_CONST_2: u8 = 0x3d;
pub const INSTR_CONST_3: u8 = 0x3e;
pub const INSTR_CONST_4: u8 = 0x3f;
pub const INSTR_CONST_10: u8 = 0x40;
pub const INSTR_RETURN_1: u8 = 0x42;
pub const INSTR_RETURN_2: u8 = 0x43;
pub const INSTR_RETURN_3: u8 = 0x44;
pub const INSTR_LOCAL_12: u8 = 0x45;
pub const INSTR_JUMP8_TRUE: u8 = 0x46;
pub const INSTR_JUMP16_TRUE: u8 = 0x47;
pub const INSTR_LOCAL_13: u8 = 0x49;
pub const INSTR_LOCAL_14: u8 = 0x4a;
pub const INSTR_LOCAL_15: u8 = 0x4b;
pub const INSTR_ARB_ADD: u8 = 0x4c;
pub const INSTR_ARB_SUBTRACT: u8 = 0x4d;
pub const INSTR_ARB_MULTIPLY: u8 = 0x4e;
pub const INSTR_RESET_1: u8 = 0x50;
pub const INSTR_RESET_2: u8 = 0x51;
pub const INSTR_NO_OP: u8 = 0x52;
pub const INSTR_INDIRECT_CLOSURE_BB: u8 = 0x54;
pub const INSTR_CONST_ADDR8_0: u8 = 0x55;
pub const INSTR_CONST_ADDR8_1: u8 = 0x56;
pub const INSTR_CALL_CONST_ADDR8_0: u8 = 0x57;
pub const INSTR_CALL_CONST_ADDR8_1: u8 = 0x58;
pub const INSTR_RESET_R_1: u8 = 0x64;
pub const INSTR_RESET_R_2: u8 = 0x65;
pub const INSTR_RESET_R_3: u8 = 0x66;
pub const INSTR_TUPLE_B: u8 = 0x68;
pub const INSTR_TUPLE_2: u8 = 0x69;
pub const INSTR_TUPLE_3: u8 = 0x6a;
pub const INSTR_TUPLE_4: u8 = 0x6b;
pub const INSTR_LOCK: u8 = 0x6c;
pub const INSTR_LDEXC: u8 = 0x6d;
pub const INSTR_INDIRECT_CONTAINER_B: u8 = 0x74;
pub const INSTR_MOVE_TO_MUT_CLOSURE_B: u8 = 0x75;
pub const INSTR_ALLOC_MUT_CLOSURE_B: u8 = 0x76;
pub const INSTR_INDIRECT_CLOSURE_B0: u8 = 0x77;
pub const INSTR_PUSH_HANDLER: u8 = 0x78;
pub const INSTR_INDIRECT_CLOSURE_B1: u8 = 0x7a;
pub const INSTR_TAIL_B_B: u8 = 0x7b;
pub const INSTR_INDIRECT_CLOSURE_B2: u8 = 0x7c;
pub const INSTR_SET_HANDLER8: u8 = 0x81;
pub const INSTR_CALL_FAST_RTS0: u8 = 0x83;
pub const INSTR_CALL_FAST_RTS1: u8 = 0x84;
pub const INSTR_CALL_FAST_RTS2: u8 = 0x85;
pub const INSTR_CALL_FAST_RTS3: u8 = 0x86;
pub const INSTR_CALL_FAST_RTS4: u8 = 0x87;
pub const INSTR_CALL_FAST_RTS5: u8 = 0x88;
pub const INSTR_NOT_BOOLEAN: u8 = 0x91;
pub const INSTR_IS_TAGGED: u8 = 0x92;
pub const INSTR_CELL_LENGTH: u8 = 0x93;
pub const INSTR_CELL_FLAGS: u8 = 0x94;
pub const INSTR_CLEAR_MUTABLE: u8 = 0x95;
pub const INSTR_ATOMIC_INCR: u8 = 0x97; // Legacy
pub const INSTR_ATOMIC_DECR: u8 = 0x98; // Legacy
pub const INSTR_EQUAL_WORD: u8 = 0xa0;
pub const INSTR_LESS_SIGNED: u8 = 0xa2;
pub const INSTR_LESS_UNSIGNED: u8 = 0xa3;
pub const INSTR_LESS_EQ_SIGNED: u8 = 0xa4;
pub const INSTR_LESS_EQ_UNSIGNED: u8 = 0xa5;
pub const INSTR_GREATER_SIGNED: u8 = 0xa6;
pub const INSTR_GREATER_UNSIGNED: u8 = 0xa7;
pub const INSTR_GREATER_EQ_SIGNED: u8 = 0xa8;
pub const INSTR_GREATER_EQ_UNSIGNED: u8 = 0xa9;
pub const INSTR_FIXED_ADD: u8 = 0xaa;
pub const INSTR_FIXED_SUB: u8 = 0xab;
pub const INSTR_FIXED_MULT: u8 = 0xac;
pub const INSTR_FIXED_QUOT: u8 = 0xad;
pub const INSTR_FIXED_REM: u8 = 0xae;
pub const INSTR_WORD_ADD: u8 = 0xb1;
pub const INSTR_WORD_SUB: u8 = 0xb2;
pub const INSTR_WORD_MULT: u8 = 0xb3;
pub const INSTR_WORD_DIV: u8 = 0xb4;
pub const INSTR_WORD_MOD: u8 = 0xb5;
pub const INSTR_WORD_AND: u8 = 0xb7;
pub const INSTR_WORD_OR: u8 = 0xb8;
pub const INSTR_WORD_XOR: u8 = 0xb9;
pub const INSTR_WORD_SHIFT_LEFT: u8 = 0xba;
pub const INSTR_WORD_SHIFT_R_LOG: u8 = 0xbb;
pub const INSTR_ALLOC_BYTE_MEM: u8 = 0xbd;
pub const INSTR_INDIRECT_LOCAL_B1: u8 = 0xc1;
pub const INSTR_IS_TAGGED_LOCAL_B: u8 = 0xc2;
pub const INSTR_JUMP_NEQ_LOCAL_IND: u8 = 0xc3;
pub const INSTR_JUMP_TAGGED_LOCAL: u8 = 0xc4;
pub const INSTR_JUMP_NEQ_LOCAL: u8 = 0xc5;
pub const INSTR_INDIRECT_0_LOCAL_0: u8 = 0xc6;
pub const INSTR_INDIRECT_LOCAL_B0: u8 = 0xc7;
pub const INSTR_CLOSURE_B: u8 = 0xd0;
pub const INSTR_GET_THREAD_ID: u8 = 0xd9;
pub const INSTR_ALLOC_WORD_MEMORY: u8 = 0xda;
pub const INSTR_LOAD_ML_BYTE: u8 = 0xdc;
pub const INSTR_STORE_ML_BYTE: u8 = 0xe4;
pub const INSTR_ENTER_INT_ARM64: u8 = 0xe9;
pub const INSTR_BLOCK_MOVE_BYTE: u8 = 0xec;
pub const INSTR_BLOCK_EQUAL_BYTE: u8 = 0xed;
pub const INSTR_BLOCK_COMPARE_BYTE: u8 = 0xee;
pub const INSTR_DELETE_HANDLER: u8 = 0xf1;
pub const INSTR_JUMP16: u8 = 0xf7;
pub const INSTR_JUMP16_FALSE: u8 = 0xf8;
pub const INSTR_SET_HANDLER16: u8 = 0xf9;
pub const INSTR_CONST_ADDR8: u8 = 0xfa; // Legacy
pub const INSTR_STACK_SIZE16: u8 = 0xfc;
pub const INSTR_ESCAPE: u8 = 0xfe;
pub const INSTR_ENTER_INT_X86: u8 = 0xff;

// ----- Extended opcodes (preceded by INSTR_ESCAPE) ---------------------

pub mod ext {
    pub const EXTINSTR_STACK_CONTAINER_W: u8 = 0x0b;
    pub const EXTINSTR_ALLOC_MUT_CLOSURE_W: u8 = 0x0f;
    pub const EXTINSTR_INDIRECT_CLOSURE_W: u8 = 0x10;
    pub const EXTINSTR_INDIRECT_CONTAINER_W: u8 = 0x11;
    pub const EXTINSTR_INDIRECT_W: u8 = 0x14;
    pub const EXTINSTR_MOVE_TO_CONTAINER_W: u8 = 0x15;
    pub const EXTINSTR_MOVE_TO_MUT_CLOSURE_W: u8 = 0x16;
    pub const EXTINSTR_SET_STACK_VAL_W: u8 = 0x17;
    pub const EXTINSTR_RESET_W: u8 = 0x18;
    pub const EXTINSTR_RESET_R_W: u8 = 0x19;
    pub const EXTINSTR_CALL_FAST_RR_TO_R: u8 = 0x1c;
    pub const EXTINSTR_CALL_FAST_RG_TO_R: u8 = 0x1d;
    pub const EXTINSTR_LOAD_POLY_WORD: u8 = 0x20;
    pub const EXTINSTR_LOAD_NATIVE_WORD: u8 = 0x21;
    pub const EXTINSTR_STORE_POLY_WORD: u8 = 0x22;
    pub const EXTINSTR_STORE_NATIVE_WORD: u8 = 0x23;
    pub const EXTINSTR_JUMP32_TRUE: u8 = 0x48;
    pub const EXTINSTR_FLOAT_ABS: u8 = 0x56;
    pub const EXTINSTR_FLOAT_NEG: u8 = 0x57;
    pub const EXTINSTR_FIXED_INT_TO_FLOAT: u8 = 0x58;
    pub const EXTINSTR_FLOAT_TO_REAL: u8 = 0x59;
    pub const EXTINSTR_REAL_TO_FLOAT: u8 = 0x5a;
    pub const EXTINSTR_FLOAT_EQUAL: u8 = 0x5b;
    pub const EXTINSTR_FLOAT_LESS: u8 = 0x5c;
    pub const EXTINSTR_FLOAT_LESS_EQ: u8 = 0x5d;
    pub const EXTINSTR_FLOAT_GREATER: u8 = 0x5e;
    pub const EXTINSTR_FLOAT_GREATER_EQ: u8 = 0x5f;
    pub const EXTINSTR_FLOAT_ADD: u8 = 0x60;
    pub const EXTINSTR_FLOAT_SUB: u8 = 0x61;
    pub const EXTINSTR_FLOAT_MULT: u8 = 0x62;
    pub const EXTINSTR_FLOAT_DIV: u8 = 0x63;
    pub const EXTINSTR_TUPLE_W: u8 = 0x67;
    pub const EXTINSTR_REAL_TO_INT: u8 = 0x6e;
    pub const EXTINSTR_FLOAT_TO_INT: u8 = 0x6f;
    pub const EXTINSTR_CALL_FAST_F_TO_F: u8 = 0x70;
    pub const EXTINSTR_CALL_FAST_G_TO_F: u8 = 0x71;
    pub const EXTINSTR_CALL_FAST_FF_TO_F: u8 = 0x72;
    pub const EXTINSTR_CALL_FAST_FG_TO_F: u8 = 0x73;
    pub const EXTINSTR_REAL_UNORDERED: u8 = 0x79;
    pub const EXTINSTR_FLOAT_UNORDERED: u8 = 0x7a;
    pub const EXTINSTR_TAIL: u8 = 0x7c;
    pub const EXTINSTR_CALL_FAST_R_TO_R: u8 = 0x8f;
    pub const EXTINSTR_CALL_FAST_G_TO_R: u8 = 0x90;
    pub const EXTINSTR_CREATE_MUTEX: u8 = 0x91;
    pub const EXTINSTR_LOCK_MUTEX: u8 = 0x92;
    pub const EXTINSTR_TRY_LOCK_MUTEX: u8 = 0x93;
    pub const EXTINSTR_ATOMIC_EXCH_ADD: u8 = 0x96; // Legacy
    pub const EXTINSTR_ATOMIC_RESET: u8 = 0x99;
    pub const EXTINSTR_LONG_W_TO_TAGGED: u8 = 0x9a;
    pub const EXTINSTR_SIGNED_TO_LONG_W: u8 = 0x9b;
    pub const EXTINSTR_UNSIGNED_TO_LONG_W: u8 = 0x9c;
    pub const EXTINSTR_REAL_ABS: u8 = 0x9d;
    pub const EXTINSTR_REAL_NEG: u8 = 0x9e;
    pub const EXTINSTR_FIXED_INT_TO_REAL: u8 = 0x9f;
    pub const EXTINSTR_FIXED_DIV: u8 = 0xaf;
    pub const EXTINSTR_FIXED_MOD: u8 = 0xb0;
    pub const EXTINSTR_WORD_SHIFT_R_ARITH: u8 = 0xbc;
    pub const EXTINSTR_LG_WORD_EQUAL: u8 = 0xbe;
    pub const EXTINSTR_LG_WORD_LESS: u8 = 0xc0;
    pub const EXTINSTR_LG_WORD_LESS_EQ: u8 = 0xc1;
    pub const EXTINSTR_LG_WORD_GREATER: u8 = 0xc2;
    pub const EXTINSTR_LG_WORD_GREATER_EQ: u8 = 0xc3;
    pub const EXTINSTR_LG_WORD_ADD: u8 = 0xc4;
    pub const EXTINSTR_LG_WORD_SUB: u8 = 0xc5;
    pub const EXTINSTR_LG_WORD_MULT: u8 = 0xc6;
    pub const EXTINSTR_LG_WORD_DIV: u8 = 0xc7;
    pub const EXTINSTR_LG_WORD_MOD: u8 = 0xc8;
    pub const EXTINSTR_LG_WORD_AND: u8 = 0xc9;
    pub const EXTINSTR_LG_WORD_OR: u8 = 0xca;
    pub const EXTINSTR_LG_WORD_XOR: u8 = 0xcb;
    pub const EXTINSTR_LG_WORD_SHIFT_LEFT: u8 = 0xcc;
    pub const EXTINSTR_LG_WORD_SHIFT_R_LOG: u8 = 0xcd;
    pub const EXTINSTR_LG_WORD_SHIFT_R_ARITH: u8 = 0xce;
    pub const EXTINSTR_REAL_EQUAL: u8 = 0xcf;
    pub const EXTINSTR_CLOSURE_W: u8 = 0xd0;
    pub const EXTINSTR_REAL_LESS: u8 = 0xd1;
    pub const EXTINSTR_REAL_LESS_EQ: u8 = 0xd2;
    pub const EXTINSTR_REAL_GREATER: u8 = 0xd3;
    pub const EXTINSTR_REAL_GREATER_EQ: u8 = 0xd4;
    pub const EXTINSTR_REAL_ADD: u8 = 0xd5;
    pub const EXTINSTR_REAL_SUB: u8 = 0xd6;
    pub const EXTINSTR_REAL_MULT: u8 = 0xd7;
    pub const EXTINSTR_REAL_DIV: u8 = 0xd8;
    pub const EXTINSTR_LOAD_C8: u8 = 0xdd;
    pub const EXTINSTR_LOAD_C16: u8 = 0xde;
    pub const EXTINSTR_LOAD_C32: u8 = 0xdf;
    pub const EXTINSTR_LOAD_C64: u8 = 0xe0;
    pub const EXTINSTR_LOAD_C_FLOAT: u8 = 0xe1;
    pub const EXTINSTR_LOAD_C_DOUBLE: u8 = 0xe2;
    pub const EXTINSTR_STORE_C8: u8 = 0xe5;
    pub const EXTINSTR_STORE_C16: u8 = 0xe6;
    pub const EXTINSTR_STORE_C32: u8 = 0xe7;
    pub const EXTINSTR_STORE_C64: u8 = 0xe8;
    pub const EXTINSTR_STORE_C_FLOAT: u8 = 0xe9;
    pub const EXTINSTR_STORE_C_DOUBLE: u8 = 0xea;
    pub const EXTINSTR_LOG2_WORD: u8 = 0xef;
    pub const EXTINSTR_CONST_ADDR32_16: u8 = 0xf0;
    pub const EXTINSTR_JUMP32: u8 = 0xf2;
    pub const EXTINSTR_JUMP32_FALSE: u8 = 0xf3;
    pub const EXTINSTR_CONST_ADDR32: u8 = 0xf4; // Legacy
    pub const EXTINSTR_SET_HANDLER32: u8 = 0xf5;
    pub const EXTINSTR_CASE32: u8 = 0xf6;
    pub const EXTINSTR_ALLOC_C_SPACE: u8 = 0xfd;
    pub const EXTINSTR_FREE_C_SPACE: u8 = 0xfe;
}

/// Read a little-endian 16-bit value from a byte slice cursor.
/// PolyML's `arg1 = pc[0] + pc[1]*256` macro from
/// `vendor/polyml/libpolyml/bytecode.cpp:83`.
#[must_use]
pub fn read_u16_le(bytes: &[u8], offset: usize) -> u16 {
    u16::from_le_bytes([bytes[offset], bytes[offset + 1]])
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Sanity: the opcode constants should be distinct from each other.
    /// (Doesn't catch sparse overlaps with reserved slots, but catches
    /// typos like "= 0x29; ... = 0x29;".)
    #[test]
    fn base_opcodes_are_distinct() {
        let all = [
            INSTR_JUMP8,
            INSTR_JUMP8_FALSE,
            INSTR_LOAD_ML_WORD,
            INSTR_STORE_ML_WORD,
            INSTR_ALLOC_REF,
            INSTR_BLOCK_MOVE_WORD,
            INSTR_LOAD_UNTAGGED,
            INSTR_STORE_UNTAGGED,
            INSTR_CASE16,
            INSTR_CALL_CLOSURE,
            INSTR_RETURN_W,
            INSTR_STACK_CONTAINER_B,
            INSTR_RAISE_EX,
            INSTR_LOCAL_W,
            INSTR_LOCAL_B,
            INSTR_LOCAL_0,
            INSTR_LOCAL_1,
            INSTR_LOCAL_2,
            INSTR_LOCAL_3,
            INSTR_LOCAL_4,
            INSTR_LOCAL_5,
            INSTR_LOCAL_6,
            INSTR_LOCAL_7,
            INSTR_LOCAL_8,
            INSTR_LOCAL_9,
            INSTR_LOCAL_10,
            INSTR_LOCAL_11,
            INSTR_LOCAL_12,
            INSTR_LOCAL_13,
            INSTR_LOCAL_14,
            INSTR_LOCAL_15,
            INSTR_CONST_0,
            INSTR_CONST_1,
            INSTR_CONST_2,
            INSTR_CONST_3,
            INSTR_CONST_4,
            INSTR_CONST_10,
            INSTR_CONST_INT_B,
            INSTR_CONST_INT_W,
            INSTR_FIXED_ADD,
            INSTR_FIXED_SUB,
            INSTR_FIXED_MULT,
            INSTR_EQUAL_WORD,
            INSTR_LESS_SIGNED,
            INSTR_GREATER_SIGNED,
            INSTR_RETURN_B,
            INSTR_RETURN_1,
            INSTR_RETURN_2,
            INSTR_RETURN_3,
            INSTR_NO_OP,
            INSTR_ESCAPE,
        ];
        let mut seen = std::collections::HashSet::new();
        for op in all {
            assert!(seen.insert(op), "duplicate opcode 0x{op:02x}");
        }
    }

    #[test]
    fn read_u16_le_works() {
        // pc[0]=0x34, pc[1]=0x12 -> 0x1234
        assert_eq!(read_u16_le(&[0x34, 0x12], 0), 0x1234);
        // matches the PolyML formula: pc[0] + pc[1]*256
        assert_eq!(0x34u16 + 0x12u16 * 256, 0x1234);
    }
}
