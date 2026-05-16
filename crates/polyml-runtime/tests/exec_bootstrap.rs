//! Try to execute the bootstrap heap entry until we hit an
//! unimplemented opcode or an error. Tells us empirically what to
//! implement next.

use std::path::PathBuf;

use std::sync::Arc;

use polyml_image::pexport::Image;
use polyml_runtime::{
    interpreter::{StepResult, opcodes},
    load_image, patch_entry_points, Interpreter, PolyWord, RtsTable,
};

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
        assert!(p.pop());
    }
}

#[test]
fn step_bootstrap_entry_as_far_as_possible() {
    let path = workspace_root().join("vendor/polyml/bootstrap/bootstrap64.txt");
    let Ok(bytes) = std::fs::read(&path) else {
        eprintln!("SKIP: {} not present", path.display());
        return;
    };
    let image = Image::parse(&bytes).expect("parse");
    let mut loaded = load_image(&image).expect("load_image");

    // Register RTS functions and patch entry points.
    // Toggle RTS tracing here when debugging which functions get called.
    // polyml_runtime::rts::set_rts_trace(true);
    let rts = Arc::new(RtsTable::new());
    let (patched, missing) = patch_entry_points(&mut loaded, &rts);
    eprintln!("RTS patch: {patched} resolved, {} unresolved.", missing.len());
    if !missing.is_empty() {
        eprintln!("Unresolved entry-point names (first 10):");
        for name in missing.iter().take(10) {
            eprintln!("  - {name}");
        }
    }

    // The root is a closure. Its first word is the code address (= the
    // bytecode entry point). To "call into" it from a fresh
    // interpreter, simulate the post-CALL state: top of stack is
    // [closure, retPC=null].
    let root_closure_word = PolyWord::from_ptr(loaded.root);
    // The closure's first word is the code object pointer.
    let code_obj = unsafe { *loaded.root };
    let code_obj_ptr = code_obj.as_ptr::<PolyWord>();

    // 4 MiB heap for runtime allocations. Bootstrap exercises a lot
    // of compiler-internal allocation; this is a guess on the high
    // side. We'll resize once we know.
    let mut interp = unsafe { Interpreter::from_code_object(8192, code_obj_ptr) }
        .with_default_alloc_space(512 * 1024)
        .with_rts(rts);
    interp.test_seed_return_sentinel();
    interp.test_seed_top(root_closure_word);

    // Step until something happens. Cap iterations to keep the test
    // bounded.
    let max_steps = 100_000;
    let mut steps = 0;
    let result = loop {
        if steps >= max_steps {
            break Ok::<_, polyml_runtime::InterpError>(StepResult::Unimplemented {
                op: 0,
                extended: false,
            });
        }
        steps += 1;
        match interp.step() {
            Ok(StepResult::Continue) => {}
            Ok(other) => break Ok(other),
            Err(e) => break Err(e),
        }
    };

    eprintln!("Executed {steps} step(s).");
    match result {
        Ok(StepResult::Returned(v)) => {
            eprintln!("✓ Bootstrap returned: {v:?}");
        }
        Ok(StepResult::Unimplemented { op, extended }) => {
            let kind = if extended { "extended" } else { "base" };
            eprintln!(
                "Unimplemented {kind} opcode 0x{op:02x} at pc_offset={} (after {} steps)",
                interp.pc_offset(),
                steps
            );
            eprintln!("Opcode name: {}", opcode_label(op));
        }
        Ok(StepResult::Continue) => {
            eprintln!("Hit step cap of {max_steps} without progress.");
        }
        Err(e) => {
            eprintln!("Error after {steps} steps at pc_offset={}: {e}", interp.pc_offset());
        }
    }
    // Don't fail; the goal is observation.
}

fn opcode_label(op: u8) -> &'static str {
    match op {
        opcodes::INSTR_TUPLE_2 => "TUPLE_2",
        opcodes::INSTR_TUPLE_3 => "TUPLE_3",
        opcodes::INSTR_TUPLE_4 => "TUPLE_4",
        opcodes::INSTR_TUPLE_B => "TUPLE_B",
        opcodes::INSTR_ALLOC_REF => "ALLOC_REF",
        opcodes::INSTR_ALLOC_WORD_MEMORY => "ALLOC_WORD_MEMORY",
        opcodes::INSTR_ALLOC_BYTE_MEM => "ALLOC_BYTE_MEM",
        opcodes::INSTR_PUSH_HANDLER => "PUSH_HANDLER",
        opcodes::INSTR_SET_HANDLER8 => "SET_HANDLER8",
        opcodes::INSTR_SET_HANDLER16 => "SET_HANDLER16",
        opcodes::INSTR_DELETE_HANDLER => "DELETE_HANDLER",
        opcodes::INSTR_RAISE_EX => "RAISE_EX",
        opcodes::INSTR_LDEXC => "LDEXC",
        opcodes::INSTR_TAIL_B_B => "TAIL_B_B",
        opcodes::INSTR_STORE_ML_WORD => "STORE_ML_WORD",
        opcodes::INSTR_STORE_ML_BYTE => "STORE_ML_BYTE",
        opcodes::INSTR_LOAD_ML_WORD => "LOAD_ML_WORD",
        opcodes::INSTR_LOAD_ML_BYTE => "LOAD_ML_BYTE",
        opcodes::INSTR_CALL_FAST_RTS0 => "CALL_FAST_RTS0",
        opcodes::INSTR_CALL_FAST_RTS1 => "CALL_FAST_RTS1",
        opcodes::INSTR_CALL_FAST_RTS2 => "CALL_FAST_RTS2",
        opcodes::INSTR_CALL_FAST_RTS3 => "CALL_FAST_RTS3",
        opcodes::INSTR_CALL_FAST_RTS4 => "CALL_FAST_RTS4",
        opcodes::INSTR_CALL_FAST_RTS5 => "CALL_FAST_RTS5",
        opcodes::INSTR_ARB_ADD => "ARB_ADD",
        opcodes::INSTR_ARB_SUBTRACT => "ARB_SUBTRACT",
        opcodes::INSTR_ARB_MULTIPLY => "ARB_MULTIPLY",
        opcodes::INSTR_CLOSURE_B => "CLOSURE_B",
        opcodes::INSTR_ALLOC_MUT_CLOSURE_B => "ALLOC_MUT_CLOSURE_B",
        opcodes::INSTR_MOVE_TO_MUT_CLOSURE_B => "MOVE_TO_MUT_CLOSURE_B",
        opcodes::INSTR_INDIRECT_CLOSURE_B0 => "INDIRECT_CLOSURE_B0",
        opcodes::INSTR_INDIRECT_CLOSURE_B1 => "INDIRECT_CLOSURE_B1",
        opcodes::INSTR_INDIRECT_CLOSURE_B2 => "INDIRECT_CLOSURE_B2",
        opcodes::INSTR_INDIRECT_CLOSURE_BB => "INDIRECT_CLOSURE_BB",
        opcodes::INSTR_ESCAPE => "ESCAPE (extended opcode)",
        _ => "?",
    }
}
