//! Try to execute the bootstrap heap entry until we hit an
//! unimplemented opcode or an error. Tells us empirically what to
//! implement next.

use std::path::PathBuf;

use std::collections::VecDeque;
use std::sync::Arc;

use polyml_image::pexport::Image;
use polyml_runtime::{
    interpreter::{StepResult, opcodes},
    load_image, patch_entry_points, Interpreter, PolyWord, RtsTable,
};

/// Snapshot of one step for the failure-time trace dump.
#[derive(Debug)]
#[allow(dead_code)] // fields used via Debug derivation
struct StepInfo {
    n: usize,
    pc_offset: usize,
    op: u8,
    sp_depth: usize,
    top: Option<PolyWord>,
    /// `Some(N)` when the immediately following step is in a different
    /// code object — i.e., this step performed a CALL or tail-call.
    new_frame_depth: Option<usize>,
}

const RECENT_CAP: usize = 200;

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

// Diagnostic test. As of mutex+wordop+rts-arg-order+basicio fixes,
// the bootstrap runs cleanly to its step cap (no crash). The cap is
// set low enough that the test finishes in a few seconds; bump
// max_steps when investigating deeper.
#[allow(clippy::too_many_lines)]
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
        // 64 MB of allocator space — bootstrap allocates a lot and we
        // have no GC yet.
        .with_default_alloc_space_words(8 * 1024 * 1024)
        .with_rts(rts);
    interp.test_seed_return_sentinel();
    interp.test_seed_top(root_closure_word);

    // Step until something happens. Cap iterations to keep the test
    // bounded. Keep a ring buffer of the most recent ~80 steps so we
    // can dump them on failure.
    let max_steps = 10_000_000;
    eprintln!("Stepping up to {max_steps}…");
    let mut steps = 0;
    let mut recent: VecDeque<StepInfo> = VecDeque::with_capacity(RECENT_CAP);
    let mut hit_cap = false;
    let result = loop {
        if steps >= max_steps {
            hit_cap = true;
            break Ok::<_, polyml_runtime::InterpError>(StepResult::Continue);
        }
        let pc_before = interp.pc_offset();
        steps += 1;
        // Periodic heartbeat so SIGSEGV/panic gives us a step floor.
        if steps % 10_000 == 0 {
            eprintln!("  …step {steps}");
        }
        let stack_depth_before = interp.stack_height();
        let frames_before = interp.frames_depth();
        let outcome = interp.step();
        let op = match outcome {
            Ok(StepResult::Unimplemented { op, .. }) => Some(op),
            _ => None,
        };
        let frames_after = interp.frames_depth();
        let new_frame_depth = (frames_after != frames_before).then_some(frames_after);
        if recent.len() == RECENT_CAP {
            recent.pop_front();
        }
        recent.push_back(StepInfo {
            n: steps,
            pc_offset: pc_before,
            op: op.unwrap_or(0xff),
            sp_depth: stack_depth_before,
            top: None, // peeking pre-step requires a method we don't have; skip
            new_frame_depth,
        });
        match outcome {
            Ok(StepResult::Continue) => {}
            Ok(other) => break Ok(other),
            Err(e) => break Err(e),
        }
    };

    let dump_recent = |recent: &VecDeque<StepInfo>| {
        eprintln!("--- Last {} steps before halt ---", recent.len());
        for s in recent {
            let frame = s
                .new_frame_depth
                .map(|d| format!(" → frame depth {d}"))
                .unwrap_or_default();
            eprintln!(
                "  #{:6} pc={:5} sp_depth={:3}{}",
                s.n, s.pc_offset, s.sp_depth, frame
            );
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
            dump_recent(&recent);
        }
        Ok(StepResult::Continue) if hit_cap => {
            eprintln!("Hit step cap of {max_steps} steps. Bootstrap is still running.");
        }
        Ok(StepResult::Continue) => {
            eprintln!("(shouldn't happen) Unexpected Continue result.");
        }
        Err(e) => {
            eprintln!("Error after {steps} steps at pc_offset={}: {e}", interp.pc_offset());
            dump_recent(&recent);
            // Hex-dump the bytes around the failing PC in the current
            // code object. The PC reported above is the byte just
            // after the failing opcode's last fetch.
            let code_addr = interp.code_start_addr();
            let pc_off = interp.pc_offset();
            let lo = pc_off.saturating_sub(60);
            let hi = pc_off + 12;
            eprintln!(
                "--- Bytes at code=0x{code_addr:016x} [{lo}..{hi}] (crash PC = {pc_off}) ---"
            );
            // SAFETY: code_start lives for the interpreter's lifetime;
            // we read within the same allocation by induction (PC was
            // valid as recently as the crash).
            let code_ptr = code_addr as *const u8;
            for off in lo..hi {
                let b = unsafe { *code_ptr.add(off) };
                let marker = if off == pc_off { " ← crash PC" } else { "" };
                eprintln!("  +{off:4}: 0x{b:02x}{marker}");
            }
            // Dump top of stack.
            eprintln!("Stack depth at crash: {}.", interp.stack_height());
            for (i, w) in interp.dump_stack_top(10).into_iter().enumerate() {
                eprintln!("  sp[{i:2}] = {w:?}");
            }
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
