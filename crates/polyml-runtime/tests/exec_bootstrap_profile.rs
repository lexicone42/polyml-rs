//! Run bootstrap for N steps with per-PC diagnostics enabled and
//! print a hot-PC / hot-function report. Use this when bootstrap
//! makes no observable RTS calls but consumes lots of bytecode —
//! distinguishes "real progress in a big initialization loop" from
//! "stuck in a tight cycle".
#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_precision_loss)]
#![allow(clippy::match_same_arms)]
#![allow(clippy::items_after_statements)]

use std::path::PathBuf;
use std::sync::Arc;

use polyml_image::pexport::Image;
use polyml_runtime::{
    Interpreter, PolyWord, RtsTable, StepResult, interpreter::diag::DiagState, load_image,
    patch_entry_points,
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

/// Run bootstrap with diag, find the hottest PC, then re-run a fresh
/// interpreter stopping just before the first hit of that PC, and
/// dump the stack. Lets us see what values the loop is actually
/// reading — important for figuring out why a "filling buffer with
/// spaces" loop terminates after 3.5M iterations and counting.
#[test]
#[ignore = "diagnostic; run explicitly with --ignored"]
fn dump_stack_at_hot_loop_entry() {
    let path = workspace_root().join("vendor/polyml/bootstrap/bootstrap64.txt");
    let Ok(bytes) = std::fs::read(&path) else {
        eprintln!("SKIP: {} not present", path.display());
        return;
    };
    let image = Image::parse(&bytes).expect("parse");

    // Phase 1: profile to find the hot PC.
    let mut loaded1 = load_image(&image).expect("load_image phase 1");
    let rts1 = Arc::new(RtsTable::new());
    let _ = patch_entry_points(&mut loaded1, &rts1);
    let root_closure_word = PolyWord::from_ptr(loaded1.root);
    let code_obj_ptr = unsafe { *loaded1.root }.as_ptr::<PolyWord>();
    let mut interp1 = unsafe { Interpreter::from_code_object(8192, code_obj_ptr) }
        .with_default_alloc_space_words(8 * 1024 * 1024)
        .with_rts(rts1)
        .enable_diagnostics();
    interp1.seed_return_sentinel();
    interp1.seed_push(root_closure_word);
    for _ in 0..2_000_000 {
        if !matches!(interp1.step(), Ok(StepResult::Continue)) {
            break;
        }
    }
    let diag = interp1.take_diagnostics().unwrap();
    let Some(((hot_code1, hot_off), _)) = diag.hot_pcs(1).into_iter().next() else {
        eprintln!("No hot PC; bootstrap may have stopped early.");
        return;
    };
    eprintln!(
        "Phase 1: hottest PC is code=0x{hot_code1:016x}+{hot_off} ({} visits).",
        diag.pc_visits
            .get(&(hot_code1, hot_off))
            .copied()
            .unwrap_or(0)
    );

    // Phase 2: fresh load (note: addresses change), but the hot PC
    // *offset* is stable. Step until we hit any (code, offset) pair
    // whose offset matches and whose code object is the same one we
    // expect (largest visited).
    let mut loaded2 = load_image(&image).expect("load_image phase 2");
    let rts2 = Arc::new(RtsTable::new());
    let _ = patch_entry_points(&mut loaded2, &rts2);
    let root_closure_word2 = PolyWord::from_ptr(loaded2.root);
    let code_obj_ptr2 = unsafe { *loaded2.root }.as_ptr::<PolyWord>();
    let mut interp2 = unsafe { Interpreter::from_code_object(8192, code_obj_ptr2) }
        .with_default_alloc_space_words(8 * 1024 * 1024)
        .with_rts(rts2)
        .enable_diagnostics();
    interp2.seed_return_sentinel();
    interp2.seed_push(root_closure_word2);

    // Walk until we've hit the same `(code, hot_off)` pair N times,
    // dumping stack at iterations 1, 2, 100, 1000, 10000. If the
    // counter actually advances, we'll see it ticking up; if not,
    // it's stuck (= the bug).
    use std::collections::HashMap;
    let mut visit_counts: HashMap<(usize, usize), u32> = HashMap::new();
    let mut steps = 0;
    let snapshots = [1u32, 2, 100, 1000, 10000, 100_000];
    let mut snap_idx = 0;
    loop {
        steps += 1;
        if steps > 10_000_000 {
            eprintln!("Phase 2: ran out of steps at step {steps}");
            return;
        }
        let here = (interp2.code_start_addr(), interp2.pc_offset());
        if here.1 == hot_off as usize {
            let c = visit_counts.entry(here).or_insert(0);
            *c += 1;
            if snap_idx < snapshots.len() && *c == snapshots[snap_idx] {
                eprintln!(
                    "--- Iteration {} (step {steps}) at PC=0x{:016x}+{} ---",
                    *c, here.0, here.1
                );
                eprintln!("Stack depth: {}.", interp2.stack_height());
                for (i, w) in interp2.dump_stack_top(15).into_iter().enumerate() {
                    eprintln!("  sp[{i:2}] = {w:?}");
                }
                snap_idx += 1;
                if snap_idx == snapshots.len() {
                    return;
                }
            }
        }
        if !matches!(interp2.step(), Ok(StepResult::Continue)) {
            eprintln!("Phase 2: stopped early at step {steps}");
            return;
        }
    }
}

#[test]
#[ignore = "diagnostic; run explicitly with --ignored"]
fn profile_bootstrap_hot_pcs() {
    let path = workspace_root().join("vendor/polyml/bootstrap/bootstrap64.txt");
    let Ok(bytes) = std::fs::read(&path) else {
        eprintln!("SKIP: {} not present", path.display());
        return;
    };
    let image = Image::parse(&bytes).expect("parse");
    let mut loaded = load_image(&image).expect("load_image");

    let rts = Arc::new(RtsTable::new());
    let (patched, _) = patch_entry_points(&mut loaded, &rts);
    eprintln!("RTS patch: {patched} resolved.");

    let root_closure_word = PolyWord::from_ptr(loaded.root);
    let code_obj = unsafe { *loaded.root };
    let code_obj_ptr = code_obj.as_ptr::<PolyWord>();

    let mut interp = unsafe { Interpreter::from_code_object(8192, code_obj_ptr) }
        .with_default_alloc_space_words(8 * 1024 * 1024)
        .with_rts(rts)
        .enable_diagnostics();
    interp.seed_return_sentinel();
    interp.seed_push(root_closure_word);

    // 5M steps is enough to see the dominant loop without taking
    // ages. Bumping this gives more accurate ratios but doesn't
    // change which PCs are hottest.
    let max_steps = 5_000_000;
    let mut last_steps = 0u64;
    for n in 0..max_steps {
        if n % 50_000 == 0 {
            last_steps = n;
            eprintln!("  step {n}");
        }
        match interp.step() {
            Ok(StepResult::Continue) => {}
            other => {
                eprintln!("Stopped early at step {n}: {other:?}");
                break;
            }
        }
    }
    eprintln!("Last successful checkpoint: step {last_steps}");

    let diag = interp.take_diagnostics().expect("diagnostics enabled");
    report(&diag);
    disassemble_hottest_loop(&diag);
}

/// Take the hottest code object and disassemble a window covering
/// all of its hot PCs (smallest to largest offset). Reads the bytes
/// straight out of memory via the stored pointer — safe because the
/// loaded heap is alive until the test ends.
fn disassemble_hottest_loop(d: &DiagState) {
    let Some((hot_code, _)) = d.hot_code_objects(1).into_iter().next() else {
        return;
    };
    let offsets: Vec<u32> = d
        .pc_visits
        .iter()
        .filter_map(|((c, o), _)| if *c == hot_code { Some(*o) } else { None })
        .collect();
    let lo = *offsets.iter().min().unwrap_or(&0);
    let hi = *offsets.iter().max().unwrap_or(&0);
    let win_end = (hi + 6).min(hi.saturating_add(20));

    eprintln!();
    eprintln!("--- Disassembly of hottest code object's hot region (offsets {lo}..={hi}) ---");
    eprintln!("(reading raw bytes at 0x{hot_code:016x}+[{lo}..{win_end}])");
    let code_ptr = hot_code as *const u8;
    let mut pc = lo as usize;
    while pc <= win_end as usize {
        // SAFETY: pointer comes from a live, loaded code object; we
        // bound pc to within the observed offset range plus a small
        // tail, which is well within the original allocation.
        let op = unsafe { *code_ptr.add(pc) };
        let imm = imm_bytes(op);
        let arg_str = (0..imm)
            .map(|i| unsafe { *code_ptr.add(pc + 1 + i) })
            .map(|b| format!("{b:02x}"))
            .collect::<Vec<_>>()
            .join(" ");
        let visits = d
            .pc_visits
            .get(&(hot_code, pc as u32))
            .copied()
            .unwrap_or(0);
        let visit_marker = if visits > 0 {
            format!("  [×{visits}]")
        } else {
            String::new()
        };
        eprintln!(
            "  +{pc:4}: {op:02x} {:<22} {arg_str}{visit_marker}",
            opcode_name(op)
        );
        pc += 1 + imm;
    }
}

// --- minimal disassembler tables (copied from disassemble_bootstrap.rs) -----
// Kept in-file because tests can't share helper modules easily.
use polyml_runtime::interpreter::opcodes::*;

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
        INSTR_INDIRECT_0 => "INDIRECT_0",
        INSTR_INDIRECT_1 => "INDIRECT_1",
        INSTR_INDIRECT_2 => "INDIRECT_2",
        INSTR_CONST_0 => "CONST_0",
        INSTR_CONST_1 => "CONST_1",
        INSTR_CONST_2 => "CONST_2",
        INSTR_EQUAL_WORD => "EQUAL_WORD",
        INSTR_LESS_SIGNED => "LESS_SIGNED",
        INSTR_LESS_UNSIGNED => "LESS_UNSIGNED",
        INSTR_LESS_EQ_SIGNED => "LESS_EQ_SIGNED",
        INSTR_LESS_EQ_UNSIGNED => "LESS_EQ_UNSIGNED",
        INSTR_GREATER_SIGNED => "GREATER_SIGNED",
        INSTR_GREATER_UNSIGNED => "GREATER_UNSIGNED",
        INSTR_GREATER_EQ_SIGNED => "GREATER_EQ_SIGNED",
        INSTR_GREATER_EQ_UNSIGNED => "GREATER_EQ_UNSIGNED",
        INSTR_NOT_BOOLEAN => "NOT_BOOLEAN",
        INSTR_FIXED_ADD => "FIXED_ADD",
        INSTR_FIXED_SUB => "FIXED_SUB",
        INSTR_FIXED_MULT => "FIXED_MULT",
        INSTR_WORD_ADD => "WORD_ADD",
        INSTR_WORD_SUB => "WORD_SUB",
        INSTR_LOAD_ML_BYTE => "LOAD_ML_BYTE",
        INSTR_STORE_ML_BYTE => "STORE_ML_BYTE",
        INSTR_CALL_FAST_RTS0 => "CALL_FAST_RTS0",
        INSTR_CALL_FAST_RTS1 => "CALL_FAST_RTS1",
        INSTR_CALL_FAST_RTS2 => "CALL_FAST_RTS2",
        INSTR_CALL_FAST_RTS3 => "CALL_FAST_RTS3",
        INSTR_CALL_FAST_RTS4 => "CALL_FAST_RTS4",
        INSTR_CALL_FAST_RTS5 => "CALL_FAST_RTS5",
        INSTR_ESCAPE => "ESCAPE",
        _ => "?",
    }
}

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
        | INSTR_CLOSURE_B
        | INSTR_SET_HANDLER8
        | INSTR_PUSH_HANDLER
        | INSTR_CALL_FAST_RTS0
        | INSTR_MOVE_TO_CONTAINER_B
        | INSTR_SET_STACK_VAL_B
        | INSTR_STACK_CONTAINER_B
        | INSTR_INDIRECT_CONTAINER_B
        | INSTR_CONST_ADDR8 => 1,
        INSTR_JUMP16 | INSTR_JUMP16_FALSE | INSTR_JUMP16_TRUE | INSTR_JUMP_BACK16
        | INSTR_LOCAL_W | INSTR_CONST_INT_W | INSTR_RETURN_W | INSTR_SET_HANDLER16
        | INSTR_CONST_ADDR16 | INSTR_CASE16 => 2,
        INSTR_INDIRECT_LOCAL_BB
        | INSTR_TAIL_B_B
        | INSTR_CONST_ADDR8_8
        | INSTR_CALL_CONST_ADDR8_8 => 2,
        INSTR_CONST_ADDR16_8 | INSTR_CALL_CONST_ADDR16_8 => 3,
        _ => 0,
    }
}

fn report(d: &DiagState) {
    eprintln!();
    eprintln!("================ Bootstrap execution profile ================");
    eprintln!("Total steps observed: {}", d.total_steps);
    eprintln!("Unique (code, offset) pairs visited: {}", d.pc_visits.len());
    eprintln!(
        "Unique code objects visited: {}",
        d.hot_code_objects(usize::MAX).len()
    );
    eprintln!("Unique CALL targets: {}", d.call_targets.len());

    eprintln!();
    eprintln!("--- Top 20 hottest code objects (by steps spent) ---");
    let total = d.total_steps as f64;
    for (code, cnt) in d.hot_code_objects(20) {
        let pct = 100.0 * cnt as f64 / total;
        eprintln!("  code=0x{code:016x}  steps={cnt:10}  ({pct:5.1}%)");
    }

    eprintln!();
    eprintln!("--- Top 20 hottest (code, offset) PCs ---");
    for ((code, off), cnt) in d.hot_pcs(20) {
        let pct = 100.0 * cnt as f64 / total;
        eprintln!("  code=0x{code:016x}+{off:5}  visits={cnt:10}  ({pct:5.1}%)");
    }

    eprintln!();
    eprintln!("--- Top 20 CALL targets (functions entered most) ---");
    let call_total: u64 = d.call_targets.values().sum();
    for (code, cnt) in d.hot_call_targets(20) {
        let pct = if call_total == 0 {
            0.0
        } else {
            100.0 * cnt as f64 / call_total as f64
        };
        eprintln!("  code=0x{code:016x}  calls={cnt:8}  ({pct:5.1}%)");
    }
    eprintln!();
    eprintln!("Hint: if a handful of code objects dominate AND the hot");
    eprintln!("PCs in them form a small offset window, that's a loop.");
    eprintln!("Diverse PCs = bootstrap is making real forward progress.");
}
