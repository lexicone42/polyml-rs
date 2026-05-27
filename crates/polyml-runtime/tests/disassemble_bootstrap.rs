//! Diagnostic test: extract the bootstrap entry's code-object bytes
//! and print them as opcode mnemonics. Helps decide which opcodes to
//! implement next.

#![allow(clippy::too_many_lines)]

use std::path::PathBuf;

use polyml_image::pexport::{Image, ObjectBody};
use polyml_runtime::interpreter::disasm;

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

    // Decode + print each instruction.
    let decoded = disasm::disassemble(&code_bytes);
    for (pc, d) in &decoded {
        let imm = d.imm_text.as_deref().unwrap_or("");
        eprintln!("  {pc:4}: {:02x} {:<22} {imm}", d.op, d.mnemonic);
    }
    eprintln!("(stopped at pc={})", code_bytes.len());

    // Tally distinct opcodes used (raw byte frequency, double-counts
    // immediates — gives a rough sense of what's hot).
    let mut histogram = std::collections::BTreeMap::<u8, usize>::new();
    for &b in &code_bytes {
        *histogram.entry(b).or_default() += 1;
    }
    eprintln!("\nByte-frequency in code (raw, includes immediates):");
    let mut sorted: Vec<_> = histogram.iter().collect();
    sorted.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
    for (op, count) in sorted.iter().take(10) {
        eprintln!("  0x{op:02x} {:<22} {count}", disasm::opcode_name(**op));
    }
}

