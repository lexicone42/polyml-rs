//! The `poly` binary entry point.
//!
//! Monday-milestone scope: load a pexport heap image, transfer control
//! to its root function, exit cleanly. We're not at the "transfer
//! control" part yet — Phase 2.1 (bytecode interpreter port) unlocks
//! that. For now this binary loads + reports.

use std::path::PathBuf;
use std::process::ExitCode;
use std::sync::Arc;

use clap::{Parser, Subcommand};
use polyml_image::pexport::{Image, ObjectBody};
use polyml_runtime::{
    interpreter::diag::DiagState, length_word, load_image, patch_entry_points, Interpreter,
    MemorySpace, PolyWord, RtsTable, StepResult,
};

#[derive(Parser, Debug)]
#[command(name = "poly", version, about = "polyml-rs runtime CLI (work in progress)")]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand, Debug)]
enum Cmd {
    /// Parse a pexport heap image and print a summary.
    Inspect {
        /// Path to a pexport (text) image.
        image: PathBuf,
    },
    /// Parse + load a pexport heap image into in-memory `MemorySpace`s
    /// and verify basic invariants.
    Load {
        /// Path to a pexport (text) image.
        image: PathBuf,
    },
    /// Execute a pexport heap image: load it, register RTS functions,
    /// transfer control to the root closure, run until it returns or
    /// hits an unimplemented opcode. Prints the result and a brief
    /// execution profile.
    Run {
        /// Path to a pexport (text) image.
        image: PathBuf,
        /// Cap on bytecode instructions to execute. Default 5,000,000
        /// is plenty for the standard bootstrap (~1.1M steps).
        #[arg(long, default_value_t = 5_000_000)]
        max_steps: u64,
        /// Print an execution profile (hot code objects + PCs) after
        /// the run. Adds a small per-step cost.
        #[arg(long)]
        profile: bool,
        /// Trace each RTS function call as it happens.
        #[arg(long)]
        trace_rts: bool,
        /// After the run, dump raw bytecode bytes for the hottest
        /// code object's hot PC range. Requires --profile.
        #[arg(long)]
        disasm_hottest: bool,
    },
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match run(&cli) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("poly: {e}");
            ExitCode::from(1)
        }
    }
}

fn run(cli: &Cli) -> Result<(), Box<dyn std::error::Error>> {
    match &cli.cmd {
        Cmd::Inspect { image } => inspect(image),
        Cmd::Load { image } => load(image),
        Cmd::Run {
            image,
            max_steps,
            profile,
            trace_rts,
            disasm_hottest,
        } => run_image(image, *max_steps, *profile, *trace_rts, *disasm_hottest),
    }
}

fn run_image(
    path: &PathBuf,
    max_steps: u64,
    profile: bool,
    trace_rts: bool,
    disasm_hottest: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let bytes = std::fs::read(path)?;
    let image = Image::parse(&bytes)?;
    let mut loaded = load_image(&image)?;

    if trace_rts {
        polyml_runtime::rts::set_rts_trace(true);
    }
    polyml_runtime::rts::clear_finish_requested();

    let rts = Arc::new(RtsTable::new());
    let (patched, missing) = patch_entry_points(&mut loaded, &rts);
    println!("Loaded {}", path.display());
    println!("  RTS patch: {patched} resolved, {} unresolved", missing.len());
    if !missing.is_empty() {
        println!("  unresolved entry points (first 10):");
        for name in missing.iter().take(10) {
            println!("    - {name}");
        }
    }

    // Set up the call frame manually (no main loop yet — we pretend
    // we're in the middle of a CALL on the root closure).
    let root_closure_word = PolyWord::from_ptr(loaded.root);
    // SAFETY: image is loaded; root is a valid closure.
    let code_obj_ptr = unsafe { *loaded.root }.as_ptr::<PolyWord>();
    let mut interp = unsafe { Interpreter::from_code_object(64 * 1024, code_obj_ptr) }
        .with_default_alloc_space(256 * 1024 * 1024)
        .with_rts(rts);
    if profile {
        interp = interp.enable_diagnostics();
    }
    interp.test_seed_return_sentinel();
    interp.test_seed_top(root_closure_word);

    println!("Executing (cap {max_steps} steps)…");
    let mut steps = 0u64;
    let outcome = loop {
        if steps >= max_steps {
            break Ok::<_, polyml_runtime::InterpError>(StepResult::Continue);
        }
        steps += 1;
        match interp.step() {
            Ok(StepResult::Continue) => {}
            Ok(other) => break Ok(other),
            Err(e) => break Err(e),
        }
    };

    println!();
    println!("Executed {steps} bytecode step(s).");
    match outcome {
        Ok(StepResult::Returned(v)) => {
            if v.is_tagged() {
                println!(
                    "Result: Tagged({}) — clean return (exit code in PolyFinish convention)",
                    v.untag()
                );
            } else {
                println!("Result: {v:?}");
            }
        }
        Ok(StepResult::Continue) => {
            println!("Hit step cap of {max_steps}. Bootstrap was still running.");
        }
        Ok(StepResult::Unimplemented { op, extended }) => {
            let kind = if extended { "extended" } else { "base" };
            println!("Stopped on unimplemented {kind} opcode 0x{op:02x}.");
        }
        Err(e) => {
            println!("Halted with error: {e}");
        }
    }

    if let Some(d) = interp.take_diagnostics() {
        print_profile(&d);
        if disasm_hottest {
            dump_hottest_bytecode(&d);
        }
    }
    Ok(())
}

#[allow(clippy::cast_possible_truncation)]
fn dump_hottest_bytecode(d: &DiagState) {
    let Some((hot_code, total)) = d.hot_code_objects(1).into_iter().next() else {
        return;
    };
    let offsets: Vec<u32> = d
        .pc_visits
        .iter()
        .filter_map(|((c, o), _)| if *c == hot_code { Some(*o) } else { None })
        .collect();
    let lo = *offsets.iter().min().unwrap_or(&0) as usize;
    let hi = *offsets.iter().max().unwrap_or(&0) as usize;
    let win_end = (hi + 6).min(hi.saturating_add(20));

    println!();
    println!(
        "--- Hottest code object disassembly (steps={total}, offsets {lo}..={hi}) ---"
    );
    let code_ptr = hot_code as *const u8;
    for pc in lo..=win_end {
        // SAFETY: code object is live for the program's lifetime.
        let b = unsafe { *code_ptr.add(pc) };
        let visits = d
            .pc_visits
            .get(&(hot_code, pc as u32))
            .copied()
            .unwrap_or(0);
        let marker = if visits > 0 {
            format!("  [×{visits}]")
        } else {
            String::new()
        };
        println!("  +{pc:4}: 0x{b:02x}{marker}");
    }
}

fn print_profile(d: &DiagState) {
    println!();
    println!("--- Execution profile ---");
    println!("Total steps observed:           {}", d.total_steps);
    println!("Unique (code,offset) PCs:       {}", d.pc_visits.len());
    println!(
        "Unique code objects visited:    {}",
        d.hot_code_objects(usize::MAX).len()
    );
    println!(
        "Unique CALL targets:            {}",
        d.hot_call_targets(usize::MAX).len()
    );
    println!();
    #[allow(clippy::cast_precision_loss)]
    let total = d.total_steps as f64;
    println!("Top 10 hottest code objects:");
    for (code, cnt) in d.hot_code_objects(10) {
        #[allow(clippy::cast_precision_loss)]
        let pct = 100.0 * cnt as f64 / total;
        println!("  code=0x{code:016x}  steps={cnt:10}  ({pct:5.1}%)");
    }
    println!();
    println!("Top 10 CALL targets (most-entered functions):");
    for (code, cnt) in d.hot_call_targets(10) {
        println!("  code=0x{code:016x}  calls={cnt:10}");
    }
}

fn inspect(path: &PathBuf) -> Result<(), Box<dyn std::error::Error>> {
    let bytes = std::fs::read(path)?;
    let image = Image::parse(&bytes)?;

    let mut hist = std::collections::BTreeMap::<&'static str, usize>::new();
    let mut total_payload_words = 0_usize;
    for obj in &image.objects {
        *hist.entry(variant_name(&obj.body)).or_default() += 1;
        total_payload_words += body_word_count_estimate(&obj.body);
    }

    let root_variant = image
        .objects
        .get(image.root as usize)
        .map_or("<out-of-bounds>", |o| variant_name(&o.body));

    println!("Image:   {}", path.display());
    println!("Bytes:   {}", bytes.len());
    println!("Objects: {}", image.objects.len());
    println!("Root:    {} ({})", image.root, root_variant);
    println!("Arch:    {:?}", image.arch);
    println!("Word:    {} bytes", image.word_size.bytes());
    println!(
        "Body:    {} words ({:.2} MB)",
        total_payload_words,
        words_to_mb(total_payload_words)
    );
    println!();
    println!("Histogram by variant:");
    for (k, v) in &hist {
        println!("  {k:<14} {v}");
    }
    Ok(())
}

fn variant_name(body: &ObjectBody) -> &'static str {
    match body {
        ObjectBody::Ordinary(_) => "Ordinary",
        ObjectBody::Closure { .. } => "Closure",
        ObjectBody::LegacyClosure { .. } => "LegacyClosure",
        ObjectBody::String(_) => "String",
        ObjectBody::Bytes(_) => "Bytes",
        ObjectBody::Code { .. } => "Code",
        ObjectBody::EntryPoint(_) => "EntryPoint",
        ObjectBody::WeakRef => "WeakRef",
    }
}

fn load(path: &PathBuf) -> Result<(), Box<dyn std::error::Error>> {
    let bytes = std::fs::read(path)?;
    let image = Image::parse(&bytes)?;
    let loaded = load_image(&image)?;

    println!("Loaded {}", path.display());
    println!(
        "  immutable: {} words ({:.2} MB capacity)",
        loaded.immutable.used_words(),
        words_to_mb(loaded.immutable.capacity_words())
    );
    println!(
        "  mutable:   {} words ({:.2} MB capacity)",
        loaded.mutable.used_words(),
        words_to_mb(loaded.mutable.capacity_words())
    );
    println!(
        "  code:      {} words ({:.2} MB capacity)",
        loaded.code.used_words(),
        words_to_mb(loaded.code.capacity_words())
    );

    let root_lw = unsafe { MemorySpace::length_word_of(loaded.root) };
    println!("  root: length-word len={} flags=0x{:02x}",
             length_word::length_of(root_lw),
             length_word::flags_of(root_lw));
    if length_word::is_closure_object(root_lw) {
        let code_ptr_word = unsafe { *loaded.root };
        if code_ptr_word.is_data_ptr() {
            let code_ptr: *const PolyWord = code_ptr_word.as_ptr();
            let code_lw = unsafe { MemorySpace::length_word_of(code_ptr) };
            println!("        root closure -> code object, len={} bytes={}, is_code={}",
                     length_word::length_of(code_lw),
                     length_word::length_of(code_lw) * 8,
                     length_word::is_code_object(code_lw));
        }
    }

    println!("\n(execution not implemented yet — see PLAN.md Phase 2.1)");
    Ok(())
}

// f64 precision is fine for MB display: a heap image of more than
// 2^52 bytes would not fit in RAM.
#[allow(clippy::cast_precision_loss)]
fn words_to_mb(words: usize) -> f64 {
    (words * std::mem::size_of::<usize>()) as f64 / 1_048_576.0
}

/// Rough body word count (mirrors `loader::body_word_count` but kept
/// inline so the CLI doesn't need access to a private function).
fn body_word_count_estimate(body: &ObjectBody) -> usize {
    match body {
        ObjectBody::Ordinary(vs) | ObjectBody::LegacyClosure { values: vs } => vs.len(),
        ObjectBody::Closure { values, .. } => 1 + values.len(),
        ObjectBody::String(b) => 1 + b.len().div_ceil(8),
        ObjectBody::Bytes(b) => b.len().div_ceil(8),
        ObjectBody::Code { code_bytes, constants, .. } => {
            code_bytes.len().div_ceil(8) + constants.len() + 2
        }
        ObjectBody::EntryPoint(n) => (n.len() + 16) / 8,
        ObjectBody::WeakRef => 1,
    }
}
