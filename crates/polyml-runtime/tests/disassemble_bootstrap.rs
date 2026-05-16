//! Diagnostic test: extract the bootstrap entry's code-object bytes
//! and print them as opcode mnemonics. Helps decide which opcodes to
//! implement next.

// This test is a long printout-style diagnostic, and the `imm_bytes`
// table groups opcodes semantically — clippy's "identical arms" lint
// would merge groups that should stay distinct for readability.
#![allow(clippy::too_many_lines)]
#![allow(clippy::match_same_arms)]

use std::path::PathBuf;

use polyml_image::pexport::{Image, ObjectBody};
use polyml_runtime::interpreter::opcodes::*;

fn workspace_root() -> PathBuf {
    let mut p: PathBuf = env!("CARGO_MANIFEST_DIR").into();
    loop {
        let cargo = p.join("Cargo.toml");
        if cargo.exists()
            && let Ok(text) = std::fs::read_to_string(&cargo)
            && text.contains("[workspace]")
        {
            return p;
        }
        assert!(
            p.pop(),
            "could not find workspace root from {}",
            env!("CARGO_MANIFEST_DIR")
        );
    }
}

#[test]
fn disassemble_bootstrap_entry() {
    let path = workspace_root().join("vendor/polyml/bootstrap/bootstrap64.txt");
    let Ok(bytes) = std::fs::read(&path) else {
        eprintln!("SKIP: {} not present", path.display());
        return;
    };
    let image = Image::parse(&bytes).expect("parse");
    let root = &image.objects[image.root as usize];
    let code_id = match &root.body {
        ObjectBody::Closure { code_addr, .. } => *code_addr,
        other => panic!("root is not a closure: {other:?}"),
    };
    let code_obj = &image.objects[code_id as usize];
    let code_bytes = match &code_obj.body {
        ObjectBody::Code { code_bytes, .. } => code_bytes.clone(),
        other => panic!("closure code addr is not a Code object: {other:?}"),
    };

    eprintln!("Bootstrap entry: closure @{} -> code @{}", image.root, code_id);
    eprintln!("Code bytes ({} total): ", code_bytes.len());

    // Walk byte-by-byte, printing each opcode with its mnemonic and any
    // immediate-arg byte(s). This isn't a real disassembler — we don't
    // know each opcode's exact arg count without a per-opcode table —
    // but it gives a rough sense of what's going on.
    let mut pc = 0;
    while pc < code_bytes.len() {
        let op = code_bytes[pc];
        let mnemonic = opcode_name(op);
        let imm = imm_bytes(op);
        let arg_bytes_str = if imm > 0 {
            let end = (pc + 1 + imm).min(code_bytes.len());
            let raw = &code_bytes[pc + 1..end];
            format!(" {raw:02x?}")
        } else {
            String::new()
        };
        eprintln!("  {pc:4}: {op:02x} {mnemonic:<22}{arg_bytes_str}");
        pc += 1 + imm;
    }
    eprintln!("(stopped at pc={pc})");

    // Tally distinct opcodes used.
    let mut histogram = std::collections::BTreeMap::<u8, usize>::new();
    for &b in &code_bytes {
        // This double-counts immediate bytes; for an exact histogram
        // we'd skip the immediates, but we just want a rough sense.
        *histogram.entry(b).or_default() += 1;
    }
    eprintln!("\nByte-frequency in code (raw, includes immediates):");
    let mut sorted: Vec<_> = histogram.iter().collect();
    sorted.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
    for (op, count) in sorted.iter().take(10) {
        eprintln!("  0x{op:02x} {:<22} {count}", opcode_name(**op));
    }
}

/// Best-effort opcode name. For unknown bytes returns "?". Note we
/// don't yet have constants for every opcode; this maps the common
/// ones plus everything in our `opcodes::` module.
fn opcode_name(op: u8) -> &'static str {
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
        INSTR_STORE_ML_WORD => "STORE_ML_WORD",
        INSTR_ALLOC_REF => "ALLOC_REF",
        INSTR_BLOCK_MOVE_WORD => "BLOCK_MOVE_WORD",
        INSTR_CASE16 => "CASE16",
        INSTR_CALL_CLOSURE => "CALL_CLOSURE",
        INSTR_RETURN_W => "RETURN_W",
        INSTR_RETURN_B => "RETURN_B",
        INSTR_RETURN_1 => "RETURN_1",
        INSTR_RETURN_2 => "RETURN_2",
        INSTR_RETURN_3 => "RETURN_3",
        INSTR_STACK_CONTAINER_B => "STACK_CONTAINER_B",
        INSTR_RAISE_EX => "RAISE_EX",
        INSTR_CALL_LOCAL_B => "CALL_LOCAL_B",
        INSTR_CALL_CONST_ADDR8_8 => "CALL_CONST_ADDR8_8",
        INSTR_CALL_CONST_ADDR16_8 => "CALL_CONST_ADDR16_8",
        INSTR_CONST_ADDR16_8 => "CONST_ADDR16_8",
        INSTR_CONST_ADDR8_8 => "CONST_ADDR8_8",
        INSTR_CONST_INT_W => "CONST_INT_W",
        INSTR_INDIRECT_LOCAL_BB => "INDIRECT_LOCAL_BB",
        INSTR_LOCAL_W => "LOCAL_W",
        INSTR_LOCAL_B => "LOCAL_B",
        INSTR_INDIRECT_B => "INDIRECT_B",
        INSTR_MOVE_TO_CONTAINER_B => "MOVE_TO_CONTAINER_B",
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
        INSTR_INDIRECT_CLOSURE_BB => "INDIRECT_CLOSURE_BB",
        INSTR_CONST_ADDR8_0 => "CONST_ADDR8_0",
        INSTR_CONST_ADDR8_1 => "CONST_ADDR8_1",
        INSTR_CALL_CONST_ADDR8_0 => "CALL_CONST_ADDR8_0",
        INSTR_CALL_CONST_ADDR8_1 => "CALL_CONST_ADDR8_1",
        INSTR_TUPLE_B => "TUPLE_B",
        INSTR_TUPLE_2 => "TUPLE_2",
        INSTR_TUPLE_3 => "TUPLE_3",
        INSTR_TUPLE_4 => "TUPLE_4",
        INSTR_LOCK => "LOCK",
        INSTR_LDEXC => "LDEXC",
        INSTR_INDIRECT_CONTAINER_B => "INDIRECT_CONTAINER_B",
        INSTR_MOVE_TO_MUT_CLOSURE_B => "MOVE_TO_MUT_CLOSURE_B",
        INSTR_ALLOC_MUT_CLOSURE_B => "ALLOC_MUT_CLOSURE_B",
        INSTR_INDIRECT_CLOSURE_B0 => "INDIRECT_CLOSURE_B0",
        INSTR_INDIRECT_CLOSURE_B1 => "INDIRECT_CLOSURE_B1",
        INSTR_INDIRECT_CLOSURE_B2 => "INDIRECT_CLOSURE_B2",
        INSTR_PUSH_HANDLER => "PUSH_HANDLER",
        INSTR_TAIL_B_B => "TAIL_B_B",
        INSTR_SET_HANDLER8 => "SET_HANDLER8",
        INSTR_SET_HANDLER16 => "SET_HANDLER16",
        INSTR_DELETE_HANDLER => "DELETE_HANDLER",
        INSTR_CALL_FAST_RTS0 => "CALL_FAST_RTS0",
        INSTR_CALL_FAST_RTS1 => "CALL_FAST_RTS1",
        INSTR_CALL_FAST_RTS2 => "CALL_FAST_RTS2",
        INSTR_CALL_FAST_RTS3 => "CALL_FAST_RTS3",
        INSTR_CALL_FAST_RTS4 => "CALL_FAST_RTS4",
        INSTR_CALL_FAST_RTS5 => "CALL_FAST_RTS5",
        INSTR_NOT_BOOLEAN => "NOT_BOOLEAN",
        INSTR_IS_TAGGED => "IS_TAGGED",
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
        INSTR_INDIRECT_LOCAL_B0 => "INDIRECT_LOCAL_B0",
        INSTR_INDIRECT_LOCAL_B1 => "INDIRECT_LOCAL_B1",
        INSTR_CLOSURE_B => "CLOSURE_B",
        INSTR_ALLOC_WORD_MEMORY => "ALLOC_WORD_MEMORY",
        INSTR_LOAD_ML_BYTE => "LOAD_ML_BYTE",
        INSTR_STORE_ML_BYTE => "STORE_ML_BYTE",
        INSTR_ARB_ADD => "ARB_ADD",
        INSTR_ARB_SUBTRACT => "ARB_SUBTRACT",
        INSTR_ARB_MULTIPLY => "ARB_MULTIPLY",
        INSTR_ESCAPE => "ESCAPE",
        _ => "?",
    }
}

/// Best-effort: how many immediate bytes follow each opcode. For
/// 16-bit immediates returns 2; for 8-bit, 1; for none, 0.
/// For opcodes with multiple args this returns the total. Imprecise
/// for ones we don't model yet.
fn imm_bytes(op: u8) -> usize {
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
        | INSTR_CALL_FAST_RTS0
        | INSTR_MOVE_TO_CONTAINER_B
        | INSTR_SET_STACK_VAL_B
        | INSTR_STACK_CONTAINER_B
        | INSTR_INDIRECT_CONTAINER_B
        | INSTR_INDIRECT_CLOSURE_B0
        | INSTR_INDIRECT_CLOSURE_B1
        | INSTR_INDIRECT_CLOSURE_B2
        | INSTR_MOVE_TO_MUT_CLOSURE_B
        | INSTR_ALLOC_MUT_CLOSURE_B
        | INSTR_CONST_ADDR8 => 1,
        INSTR_JUMP16
        | INSTR_JUMP16_FALSE
        | INSTR_JUMP16_TRUE
        | INSTR_JUMP_BACK16
        | INSTR_LOCAL_W
        | INSTR_CONST_INT_W
        | INSTR_RETURN_W
        | INSTR_SET_HANDLER16
        | INSTR_CONST_ADDR16
        | INSTR_CASE16 => 2,
        INSTR_INDIRECT_LOCAL_BB
        | INSTR_TAIL_B_B
        | INSTR_INDIRECT_CLOSURE_BB
        | INSTR_CONST_ADDR8_8
        | INSTR_INDIRECT_LOCAL_B0
        | INSTR_INDIRECT_LOCAL_B1
        | INSTR_CALL_CONST_ADDR8_8 => 2,
        INSTR_CONST_ADDR16_8 | INSTR_CALL_CONST_ADDR16_8 => 3,
        _ => 0,
    }
}
