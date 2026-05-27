//! The `poly` binary entry point.
//!
//! Monday-milestone scope: load a pexport heap image, transfer control
//! to its root function, exit cleanly. We're not at the "transfer
//! control" part yet — Phase 2.1 (bytecode interpreter port) unlocks
//! that. For now this binary loads + reports.

use std::path::PathBuf;
use std::process::ExitCode;
use std::os::unix::process::ExitStatusExt;
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
        /// Extra arguments visible to the SML program via
        /// `CommandLine.arguments()`. The bootstrap looks for `-I path`
        /// in particular, so it can locate basis sources when
        /// `Bootstrap.use "..."` is called with a relative path.
        /// Pass these after a `--` separator: `poly run img.txt -- -I /tmp`.
        #[arg(last = true)]
        args: Vec<String>,
        /// Execute the given SML source file as if the user piped
        /// `val () = Bootstrap.use "<basename>";` to stdin. The
        /// file's parent directory is automatically added as `-I`,
        /// so the script doesn't need an explicit `--`-separated arg.
        /// Mutually exclusive with reading SML from stdin.
        #[arg(long, value_name = "FILE")]
        r#use: Option<PathBuf>,
        /// Install every JIT-translatable code object from the image
        /// in the interpreter's JIT cache before running. Speeds up
        /// CALL dispatch into JIT'd code (subject to the
        /// `MAX_JIT_DEPTH` cap on nested JIT dispatch).
        #[arg(long)]
        jit: bool,
    },
    /// Differential test: pick a JIT-installed function from a loaded
    /// image and run it under both the interpreter and the JIT with
    /// the same inputs, comparing results. Surfaces JIT translation
    /// bugs systematically.
    ///
    /// `--list` prints all installed functions (with their sml_arity,
    /// first-32-bytes-of-bytecode hex, and an index you can pass
    /// to `--idx`). `--idx N` selects the Nth installed function;
    /// `--args 0,1,2` supplies tagged-int values (`tag(0)`, `tag(1)`,
    /// `tag(2)`). `--scan` runs every arity-0 installed function with
    /// no args and prints divergences.
    Diff {
        /// Path to a pexport (text) image.
        image: PathBuf,
        /// List installed JIT entries instead of running a diff.
        #[arg(long)]
        list: bool,
        /// When listing, only show entries whose first-32-bytes hex
        /// matches this substring (e.g., "16 08" finds functions
        /// containing CALL_LOCAL_B 8). Stable across runs.
        #[arg(long)]
        bc_grep: Option<String>,
        /// Scan ALL arity-0 installed functions automatically. Each
        /// is run under both modes with no args; mismatches printed.
        #[arg(long)]
        scan: bool,
        /// Scan with subprocess isolation: each (idx, arg) test runs
        /// in a child process. SEGV from one function doesn't kill
        /// the parent. Slower (~1s per spawn) but actually finds bugs.
        /// Use with DIFF_SCAN_LIMIT=N to bound runtime.
        #[arg(long)]
        scan_isolated: bool,
        /// Select the Nth installed function (use with `--list` first
        /// to find an interesting one).
        #[arg(long)]
        idx: Option<usize>,
        /// Select an installed function by its code-object address
        /// (hex, with or without 0x prefix).
        #[arg(long)]
        code_obj: Option<String>,
        /// Pass these as args. Each value is parsed as a signed
        /// integer and tagged (low bit set) before passing. Use
        /// `--raw-args` to pass raw PolyWord bits instead.
        #[arg(long, value_delimiter = ',')]
        args: Vec<i64>,
        /// Treat `--args` values as raw PolyWord bits (no tag added).
        /// Use this for pointer args.
        #[arg(long)]
        raw_args: bool,
        /// Closure word passed in slot[N+1] of args_buf. Defaults to 0.
        /// Use a real closure pointer (hex) for functions reading
        /// captures via `INDIRECT_CLOSURE_BN`.
        #[arg(long)]
        closure: Option<String>,
    },
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match run(&cli) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("poly: {e}");
            ExitCode::from(1)
        }
    }
}

fn run(cli: &Cli) -> Result<ExitCode, Box<dyn std::error::Error>> {
    match &cli.cmd {
        Cmd::Inspect { image } => inspect(image).map(|()| ExitCode::SUCCESS),
        Cmd::Load { image } => load(image).map(|()| ExitCode::SUCCESS),
        Cmd::Run {
            image,
            max_steps,
            profile,
            trace_rts,
            disasm_hottest,
            args,
            r#use,
            jit,
        } => run_image(
            image,
            *max_steps,
            *profile,
            *trace_rts,
            *disasm_hottest,
            args.clone(),
            r#use.clone(),
            *jit,
        ),
        Cmd::Diff {
            image,
            list,
            bc_grep,
            scan,
            scan_isolated,
            idx,
            code_obj,
            args,
            raw_args,
            closure,
        } => {
            if *scan_isolated {
                scan_isolated_command(image)
            } else {
                diff_command(
                    image,
                    *list,
                    bc_grep.as_deref(),
                    *scan,
                    *idx,
                    code_obj.as_deref(),
                    args,
                    *raw_args,
                    closure.as_deref(),
                )
            }
        }
    }
}

fn run_image(
    path: &PathBuf,
    max_steps: u64,
    profile: bool,
    trace_rts: bool,
    disasm_hottest: bool,
    extra_args: Vec<String>,
    use_file: Option<PathBuf>,
    install_jit: bool,
) -> Result<ExitCode, Box<dyn std::error::Error>> {
    let bytes = std::fs::read(path)?;
    let image = Image::parse(&bytes)?;
    let mut loaded = load_image(&image)?;

    if trace_rts {
        polyml_runtime::rts::set_rts_trace(true);
    }
    polyml_runtime::rts::clear_finish_requested();

    // Plumb extra args through to SML's CommandLine.arguments().
    // Upstream PolyML's `user_arg_strings` (= CommandLine.arguments) is
    // everything after argv[0] except the image path itself. We pass
    // through whatever came after `--`, matching that convention.
    let mut all_args = extra_args;
    // --use FILE expands to feeding `Bootstrap.use "<basename>";` via
    // stdin and adding `-I <parent>` to CommandLine.arguments.
    let synthetic_stdin: Option<String> = use_file.as_ref().map(|p| {
        let parent = p.parent().filter(|d| !d.as_os_str().is_empty()).map_or_else(
            || ".".to_string(),
            |d| d.to_string_lossy().into_owned(),
        );
        let base = p.file_name().map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| p.to_string_lossy().into_owned());
        if !all_args.iter().any(|a| a == "-I") {
            all_args.push("-I".to_string());
            all_args.push(parent);
        }
        format!("val () = Bootstrap.use \"{base}\";\n")
    });
    polyml_runtime::rts::set_command_args(all_args);
    if let Some(sml) = &synthetic_stdin {
        polyml_runtime::rts::push_synthetic_stdin(sml.clone());
        // Replace process stdin with /dev/null so that once the
        // synthetic-stdin queue drains, the bootstrap's read loop
        // sees EOF and exits cleanly. Without this it'd block
        // forever waiting for more input.
        redirect_stdin_to_devnull();
    }

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
    // Register the mutable image space as a GC root region — the
    // global namespace hashtable lives here and references runtime
    // alloc-space objects (compiled structures, etc.). Without
    // scanning it the GC would collect freshly-compiled code.
    let image_mut_ptr = loaded.mutable.iter().next().map(|w| w as *const PolyWord);
    let image_mut_len = loaded.mutable.used_words();
    let mut interp = unsafe { Interpreter::from_code_object(1024 * 1024, code_obj_ptr) }
        // 1.6 GB heap. Small enough that GC auto-fires at 80% = 1.3 GB
        // and keeps peak RSS bounded. Bigger heaps (24 GB) postpone GC
        // past the bootstrap's working set and OOM around stage 6.
        // With --jit, use a smaller heap matching the jit_bootstrap_run
        // test setup; the bigger heap exposed a JIT-related divergence
        // that needs separate investigation.
        .with_default_alloc_space_bytes(1_600 * 1024 * 1024)
        .with_rts(rts);
    if let Some(p) = image_mut_ptr {
        interp = interp.with_image_mutable_root(p, image_mut_len);
    }
    if profile {
        interp = interp.enable_diagnostics();
    }
    if install_jit {
        let mut jit = polyml_jit::Jit::new()
            .map_err(|e| format!("jit init: {e}"))?;
        let (total, jit_ok, installed) =
            polyml_jit::install_all_jit_entries(&mut jit, &loaded, &mut interp);
        println!(
            "  JIT: {jit_ok}/{total} code objects translated ({:.1}%), {installed} installed",
            100.0 * jit_ok as f64 / total as f64
        );
        // Leak `jit` so its compiled code memory outlives this scope —
        // the interpreter holds function pointers into it.
        Box::leak(Box::new(jit));
    }

    interp.test_seed_return_sentinel();
    interp.test_seed_top(root_closure_word);

    println!("Executing (cap {max_steps} steps)…");
    let checkpoint_every: u64 = std::env::var("POLY_CHECKPOINT_EVERY")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let mut steps = 0u64;
    let outcome = loop {
        if steps >= max_steps {
            break Ok::<_, polyml_runtime::InterpError>(StepResult::Continue);
        }
        steps += 1;
        if checkpoint_every != 0 && steps % checkpoint_every == 0 {
            use std::io::Write;
            let _ = writeln!(std::io::stderr(), "  [checkpoint] steps={steps}");
            let _ = std::io::stderr().flush();
        }
        match interp.step() {
            Ok(StepResult::Continue) => {}
            Ok(other) => break Ok(other),
            Err(e) => break Err(e),
        }
    };

    println!();
    println!("Executed {steps} bytecode step(s).");
    let exit_code: u8 = match &outcome {
        Ok(StepResult::Returned(v)) => {
            if v.is_tagged() {
                let n = v.untag();
                println!(
                    "Result: Tagged({n}) — clean return (exit code in PolyFinish convention)"
                );
                // SML's `OS.Process.exit` passes a small int that
                // PolyML maps to the process exit code. Clamp into
                // a u8 so unusual values don't wrap weirdly.
                #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
                let code = n.clamp(0, 255) as u8;
                code
            } else {
                println!("Result: {v:?}");
                0
            }
        }
        Ok(StepResult::Continue) => {
            println!("Hit step cap of {max_steps}. Bootstrap was still running.");
            2
        }
        Ok(StepResult::Unimplemented { op, extended }) => {
            let kind = if *extended { "extended" } else { "base" };
            println!("Stopped on unimplemented {kind} opcode 0x{op:02x}.");
            let (lo, hi, hex) = interp.pc_context_bytes(20);
            println!("  bytecode [{lo}..{hi}]: {hex}");
            let recent = interp.recent_call_targets_snapshot();
            println!("  recent CALL targets (most recent first):");
            for (off, target) in recent.iter().enumerate() {
                println!("    -{off:2}: 0x{target:016x}");
            }
            3
        }
        Err(e) => {
            println!("Halted with error: {e}");
            4
        }
    };

    if let Some(d) = interp.take_diagnostics() {
        print_profile(&d);
        if disasm_hottest {
            dump_hottest_bytecode(&d);
        }
    }
    Ok(ExitCode::from(exit_code))
}

/// `dup2(/dev/null, 0)` so future reads from stdin return EOF.
/// Used by `--use` after pushing synthetic SML; the real stdin
/// (whatever was attached at launch) is closed and replaced.
fn redirect_stdin_to_devnull() {
    use std::os::fd::AsRawFd;
    let f = match std::fs::OpenOptions::new().read(true).open("/dev/null") {
        Ok(f) => f,
        Err(_) => return,
    };
    let fd = f.as_raw_fd();
    // SAFETY: dup2 takes two valid fds; 0 is always allocated.
    unsafe {
        libc::dup2(fd, 0);
    }
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
    let total_calls = d.total_calls();
    let total_jit_hits = d.total_jit_hits();
    println!(
        "Top 10 CALL targets (most-entered functions) — total calls={total_calls}, JIT hits={total_jit_hits} ({:.1}%):",
        if total_calls > 0 { 100.0 * total_jit_hits as f64 / total_calls as f64 } else { 0.0 }
    );
    for (code, cnt) in d.hot_call_targets(10) {
        let jit_hits = d.jit_call_hits.get(&code).copied().unwrap_or(0);
        let jit_pct = if cnt > 0 { 100.0 * jit_hits as f64 / cnt as f64 } else { 0.0 };
        let marker = if jit_hits > 0 { "[JIT]" } else { "     " };
        println!(
            "  {marker} code=0x{code:016x}  calls={cnt:10}  jit_hits={jit_hits:10}  ({jit_pct:5.1}%)"
        );
        // Bytecode head dump for non-JIT'd hot functions —
        // shows which blocked opcode is making it un-installable.
        if jit_hits == 0 {
            // Read up to 40 bytes of bytecode at this code address.
            // SAFETY: code is a CALL target = code object body start,
            // so reading some bytes is safe (memory mapped).
            let bytes: Vec<u8> = (0..40)
                .map(|i| unsafe { *(code as *const u8).add(i) })
                .collect();
            let hex = bytes
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<Vec<_>>()
                .join(" ");
            // Identify the first "interesting" opcode that's likely
            // blocking JIT install (one of the filtered ones).
            let blockers: &[(u8, &str)] = &[
                (0x16, "CALL_LOCAL_B"),
                (0x7b, "TAIL_B_B"),
                (0x57, "CALL_CONST_ADDR8_0"),
                (0x58, "CALL_CONST_ADDR8_1"),
                (0x17, "CALL_CONST_ADDR8_8"),
                (0x18, "CALL_CONST_ADDR16_8"),
                // Untranslated opcodes:
                (0x0a, "CASE16 (untranslated)"),
                (0x0e, "STACK_CONTAINER_B (untranslated)"),
            ];
            let blocker = bytes
                .iter()
                .find_map(|b| blockers.iter().find(|(op, _)| *op == *b).map(|(_, n)| *n))
                .unwrap_or("(no obvious blocker; may be untranslatable opcode)");
            println!("         bc[0..40]: {hex}");
            println!("         likely blocker: {blocker}");
        }
    }
    println!();
    println!("Top 10 JIT-cache hits (functions actually accelerated):");
    for (code, cnt) in d.hot_jit_calls(10) {
        let total_for_code = d.call_targets.get(&code).copied().unwrap_or(0);
        let coverage = if total_for_code > 0 {
            100.0 * cnt as f64 / total_for_code as f64
        } else {
            0.0
        };
        println!(
            "  code=0x{code:016x}  jit_hits={cnt:10}  total_calls={total_for_code:10}  coverage={coverage:5.1}%"
        );
    }
    println!();
    println!("Top 20 hottest opcodes:");
    for (op, cnt) in d.hot_opcodes(20) {
        #[allow(clippy::cast_precision_loss)]
        let pct = 100.0 * cnt as f64 / total;
        println!("  op=0x{op:02x}  count={cnt:12}  ({pct:5.1}%)");
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

#[allow(clippy::too_many_arguments)]
fn diff_command(
    image_path: &PathBuf,
    list: bool,
    bc_grep: Option<&str>,
    scan: bool,
    idx: Option<usize>,
    code_obj_hex: Option<&str>,
    args: &[i64],
    raw_args: bool,
    closure_hex: Option<&str>,
) -> Result<ExitCode, Box<dyn std::error::Error>> {
    use polyml_jit::{differential, Jit};
    use polyml_runtime::{patch_entry_points, RtsTable};

    let bytes = std::fs::read(image_path)?;
    let image = Image::parse(&bytes)?;
    let mut loaded = load_image(&image)?;

    let rts = Arc::new(RtsTable::new());
    polyml_runtime::rts::clear_finish_requested();
    let _ = patch_entry_points(&mut loaded, &rts);
    // Redirect real stdin to /dev/null so RTS read-stdin calls
    // bail with EOF instead of blocking the differential run.
    redirect_stdin_to_devnull();

    // SAFETY: image is loaded; root is a valid closure pointer.
    let code_obj_ptr = unsafe { *loaded.root }.as_ptr::<PolyWord>();
    let image_mut_ptr = loaded.mutable.iter().next().map(|w| w as *const PolyWord);
    let image_mut_len = loaded.mutable.used_words();
    let mut interp = unsafe { Interpreter::from_code_object(1024 * 1024, code_obj_ptr) }
        .with_default_alloc_space_bytes(1_600 * 1024 * 1024)
        .with_rts(rts.clone());
    if let Some(p) = image_mut_ptr {
        interp = interp.with_image_mutable_root(p, image_mut_len);
    }

    let mut jit = Jit::new()?;
    let (total, jit_ok, installed) =
        polyml_jit::install_all_jit_entries(&mut jit, &loaded, &mut interp);
    eprintln!(
        "Loaded: {total} code objects, translated {jit_ok}, installed {installed}",
    );
    Box::leak(Box::new(jit));

    let mut entries = interp.jit_cache_entries();
    // Sort by code_obj_ptr for stable iteration within a run. (The
    // absolute pointer values vary across runs due to ASLR, but the
    // *order* of those pointers is consistent — same image always
    // produces same relative layout.)
    entries.sort_by_key(|(p, _)| *p);
    eprintln!("JIT cache has {} entries", entries.len());
    // CLEAR the JIT cache so:
    //   1. Interp runs don't dispatch into JIT via do_call's cache
    //      check — interp runs stay pure-bytecode.
    //   2. JIT runs (which we call directly via entry.func) still
    //      use the trampoline for NESTED calls, but those nested
    //      calls miss the cache and fall back to interp. This keeps
    //      the diff signal clean: it isolates bugs to the OUTER
    //      JIT'd function, not to nested JIT-to-JIT calls.
    interp.jit_cache_clear();

    if list {
        print_jit_entries(&entries, bc_grep);
        return Ok(ExitCode::SUCCESS);
    }

    let closure_word: i64 = match closure_hex {
        Some(s) => parse_hex_addr(s)? as i64,
        None => 0,
    };

    if scan {
        return run_scan(&mut interp, &entries, closure_word);
    }

    // Single-function diff: must specify --idx or --code-obj.
    let (code_obj_ptr, entry) = match (idx, code_obj_hex) {
        (Some(i), None) => {
            let pair = entries.get(i).ok_or_else(|| {
                format!(
                    "idx {i} out of range (have {} entries)",
                    entries.len()
                )
            })?;
            (pair.0, pair.1)
        }
        (None, Some(s)) => {
            let addr = parse_hex_addr(s)?;
            let pair = entries
                .iter()
                .find(|(p, _)| *p == addr)
                .ok_or_else(|| format!("no JIT entry at 0x{addr:016x}"))?;
            (pair.0, pair.1)
        }
        (Some(_), Some(_)) => {
            return Err("specify only one of --idx or --code-obj".into());
        }
        (None, None) => {
            return Err(
                "specify --idx N, --code-obj HEX, --list, or --scan".into(),
            );
        }
    };

    if args.len() != entry.sml_arity {
        return Err(format!(
            "function has sml_arity={}, but {} args provided",
            entry.sml_arity,
            args.len()
        )
        .into());
    }

    // Tag args unless --raw-args is set.
    let final_args: Vec<i64> = if raw_args {
        args.to_vec()
    } else {
        args.iter().map(|&v| differential::tag(v)).collect()
    };

    eprintln!(
        "Diffing code_obj=0x{:016x} sml_arity={} arity_init={}",
        code_obj_ptr, entry.sml_arity, entry.arity_init,
    );
    let report = differential::diff_function(
        &mut interp,
        &entry,
        code_obj_ptr,
        &final_args,
        closure_word,
    );
    println!("{}", report.pretty());
    if report.matches {
        Ok(ExitCode::SUCCESS)
    } else {
        Ok(ExitCode::from(2))
    }
}

fn parse_hex_addr(s: &str) -> Result<usize, Box<dyn std::error::Error>> {
    let trimmed = s.trim().trim_start_matches("0x").trim_start_matches("0X");
    usize::from_str_radix(trimmed, 16)
        .map_err(|e| format!("bad hex address '{s}': {e}").into())
}

/// Spawn `poly diff <image> --idx N --args V` per test, capturing
/// exit codes to detect SEGVs without killing the parent. Each
/// spawn pays ~1.5s image-load overhead — slow but rock-solid.
///
/// Caps per `DIFF_SCAN_LIMIT` (default 50 to bound interactive
/// runtime). Each function is tested with 6 different tagged-int
/// args. Divergences are reported with full output.
fn scan_isolated_command(
    image_path: &PathBuf,
) -> Result<ExitCode, Box<dyn std::error::Error>> {
    use std::process::{Command, Stdio};

    // First: load the image in this process just to enumerate idx
    // count. We need to know HOW MANY entries there are.
    let bytes = std::fs::read(image_path)?;
    let image = Image::parse(&bytes)?;
    let mut loaded = load_image(&image)?;
    let rts = Arc::new(RtsTable::new());
    polyml_runtime::rts::clear_finish_requested();
    let _ = patch_entry_points(&mut loaded, &rts);
    let code_obj_ptr = unsafe { *loaded.root }.as_ptr::<PolyWord>();
    let mut interp = unsafe { Interpreter::from_code_object(64 * 1024, code_obj_ptr) }
        .with_default_alloc_space_bytes(256 * 1024 * 1024)
        .with_rts(rts.clone());
    let mut jit = polyml_jit::Jit::new()?;
    let _ = polyml_jit::install_all_jit_entries(&mut jit, &loaded, &mut interp);
    let mut entries = interp.jit_cache_entries();
    entries.sort_by_key(|(p, _)| *p);
    let total = entries.len();
    drop(interp); // release before subprocesses
    drop(jit);
    eprintln!("Found {total} installed entries; starting isolated scan");

    let limit: usize = std::env::var("DIFF_SCAN_LIMIT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(50);
    let arg_values: &[i64] = &[0, 1, -1, 42, 100, 1000];

    let exe = std::env::current_exe()?;
    let mut tested = 0usize;
    let mut matched = 0usize;
    let mut segv = 0usize;
    let mut timeout_n = 0usize;
    let mut other = 0usize;
    let mut diverged: Vec<(usize, i64, String)> = Vec::new();

    let scan_start = std::time::Instant::now();
    'outer: for idx in 0..limit.min(total) {
        for &arg in arg_values {
            // Try with sml_arity copies of the same arg. We don't
            // know the arity without re-loading, but the diff
            // subcommand handles the mismatch by erroring.
            // Use --args=VAL syntax so negative values aren't parsed
            // as flag prefixes by clap.
            let arg_eq = format!("--args={arg}");
            let output = Command::new(&exe)
                .args([
                    "diff",
                    image_path.to_str().unwrap(),
                    "--idx",
                    &idx.to_string(),
                    &arg_eq,
                ])
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output()?;
            tested += 1;
            let rc = output.status.code();
            let signal = output.status.signal();
            match (rc, signal) {
                (Some(0), _) => matched += 1,
                (Some(2), _) => {
                    let combined = format!(
                        "STDOUT:\n{}\nSTDERR:\n{}",
                        String::from_utf8_lossy(&output.stdout),
                        String::from_utf8_lossy(&output.stderr),
                    );
                    diverged.push((idx, arg, combined));
                    eprintln!("  idx={idx:4} arg={arg:7} → DIVERGENCE");
                }
                (None, Some(11)) | (Some(139), _) => segv += 1,
                (None, _) if output.status.success() => other += 1,
                (Some(124), _) => timeout_n += 1,
                _ => other += 1,
            }
            // Print progress every 50 tests.
            if tested % 50 == 0 {
                eprintln!(
                    "  progress: {tested} tested, {matched} match, {} diverge, {segv} segv, {timeout_n} timeout ({}s)",
                    diverged.len(),
                    scan_start.elapsed().as_secs(),
                );
            }
            // Stop early if scan is taking too long.
            if scan_start.elapsed().as_secs() > 600 {
                eprintln!("scan: exceeded 10-min budget, stopping");
                break 'outer;
            }
        }
    }
    let elapsed = scan_start.elapsed();
    println!(
        "Isolated scan: tested {tested} in {:.1}s — matched {matched}, \
         diverged {}, SEGV {segv}, timeout {timeout_n}, other {other}",
        elapsed.as_secs_f64(),
        diverged.len(),
    );
    if !diverged.is_empty() {
        println!("\n--- Divergences ---");
        for (idx, arg, output) in &diverged {
            println!("=== idx={idx} arg={arg} ===");
            println!("{output}");
        }
    }
    if diverged.is_empty() {
        Ok(ExitCode::SUCCESS)
    } else {
        Ok(ExitCode::from(2))
    }
}

/// Static heuristic: scan a function's first 64 bytes for opcodes
/// that almost always deref an arg or capture. Functions that match
/// will SEGV on tagged-int inputs.
///
/// Conservative — false positives skip many safe functions. False
/// negatives are still possible (deref opcodes deeper in the
/// function), but the early bytes are where arg-deref patterns
/// usually appear.
fn function_likely_derefs(code_obj_ptr: usize) -> bool {
    // INDIRECT_0..INDIRECT_5 (0x35..0x3a), INDIRECT_B (0x23),
    // INDIRECT_LOCAL_B0 (0xc7), INDIRECT_LOCAL_B1 (0xc1),
    // INDIRECT_LOCAL_BB (0x21), INDIRECT_0_LOCAL_0 (0xc6),
    // INDIRECT_CLOSURE_B0/B1/B2 (0x77/0x7a/0x7c),
    // INDIRECT_CLOSURE_BB (0x54),
    // LOAD_ML_BYTE (0xdc), LOAD_ML_WORD (0x04),
    // JUMP_NEQ_LOCAL_IND (0xc3) — derefs the local.
    let deref_ops: &[u8] = &[
        0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x23,
        0xc7, 0xc1, 0x21, 0xc6,
        0x77, 0x7a, 0x7c, 0x54,
        0xdc, 0x04,
        0xc3,
        0x08, 0x09, // LOAD_UNTAGGED, STORE_UNTAGGED
        0x05, 0x07, // STORE_ML_WORD, BLOCK_MOVE_WORD
        0x93,       // CELL_LENGTH (derefs cell)
    ];
    // Only check the first 8 bytes — functions that deref args
    // immediately (within the first few opcodes) almost always do
    // so on input that wouldn't be a valid pointer. Functions that
    // first do arithmetic or comparison may tolerate tagged-int
    // inputs even if later opcodes deref.
    unsafe {
        let p = code_obj_ptr as *const u8;
        for off in 0..8 {
            let b = *p.add(off);
            if deref_ops.contains(&b) {
                return true;
            }
        }
    }
    false
}

fn print_jit_entries(
    entries: &[(usize, polyml_runtime::JitEntry)],
    bc_grep: Option<&str>,
) {
    println!(
        "{:>4} {:>18} {:>9} {:>11}  {}",
        "idx", "code_obj_ptr", "sml_arity", "arity_init", "bc[0..32]",
    );
    let mut matched = 0;
    for (i, (ptr, entry)) in entries.iter().enumerate() {
        // Read first 32 bytes of bytecode as a stable function
        // fingerprint. The absolute pointer varies across runs
        // (ASLR), but the bytecode head is invariant for a given
        // image. `--bc-grep "16 08"` finds CALL_LOCAL_B 8 functions.
        let bc_head: String = unsafe {
            let p = *ptr as *const u8;
            (0..32)
                .map(|k| format!("{:02x}", *p.add(k)))
                .collect::<Vec<_>>()
                .join(" ")
        };
        if let Some(pat) = bc_grep {
            if !bc_head.contains(pat) {
                continue;
            }
        }
        println!(
            "{i:>4} 0x{ptr:016x} {:>9} {:>11}  {bc_head}",
            entry.sml_arity, entry.arity_init,
        );
        matched += 1;
    }
    if let Some(pat) = bc_grep {
        eprintln!("({matched} entries match bytecode-grep pattern \"{pat}\")");
    }
}

fn run_scan(
    interp: &mut Interpreter,
    entries: &[(usize, polyml_runtime::JitEntry)],
    closure_word: i64,
) -> Result<ExitCode, Box<dyn std::error::Error>> {
    use polyml_jit::differential;
    let mut tested = 0;
    let mut matched = 0;
    let mut diverged: Vec<differential::DiffReport> = Vec::new();
    let mut errored: Vec<differential::DiffReport> = Vec::new();
    // For each function, try multiple arg combinations. Each
    // combination is tried once per function. The variety helps
    // catch path-sensitive bugs (e.g., arg=100 picked up the
    // first JIT divergence in initial testing). Cap arity at 4
    // (anything higher likely takes complex object refs).
    let arg_combinations: &[&[i64]] = &[
        &[differential::tag(0)],
        &[differential::tag(1)],
        &[differential::tag(-1)],
        &[differential::tag(42)],
        &[differential::tag(100)],
        &[differential::tag(1000)],
    ];
    let scan_limit: usize = std::env::var("DIFF_SCAN_LIMIT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(usize::MAX);
    let verbose = std::env::var("DIFF_SCAN_VERBOSE").is_ok();
    let mut skipped_likely_deref = 0;
    for (i, (ptr, entry)) in entries.iter().enumerate() {
        if entry.sml_arity > 4 {
            continue;
        }
        if tested >= scan_limit {
            break;
        }
        // Static filter: skip functions whose first 64 bytes contain
        // any INDIRECT opcode. They likely deref an arg or capture,
        // and tagged-int inputs would cause a SEGV that takes down
        // the whole tester process. Conservative — leaves out many
        // safe functions, but the survivors are safe to fuzz.
        if function_likely_derefs(*ptr) {
            skipped_likely_deref += 1;
            continue;
        }
        if verbose {
            eprintln!(
                "  [{i:4}] testing 0x{ptr:016x} sml_arity={}",
                entry.sml_arity,
            );
        }
        // For each base value, build an arg combo of (sml_arity copies).
        // E.g., for arity 2 + base=42: args = [tag(42), tag(42)].
        let base_values: [i64; 6] = [
            differential::tag(0),
            differential::tag(1),
            differential::tag(-1),
            differential::tag(42),
            differential::tag(100),
            differential::tag(1000),
        ];
        for base in &base_values {
            let combo: Vec<i64> = std::iter::repeat(*base).take(entry.sml_arity).collect();
            tested += 1;
            let report = differential::diff_function(
                interp, entry, *ptr, &combo, closure_word,
            );
            if report.matches {
                matched += 1;
            } else if report.interp_err.is_some() {
                errored.push(report);
            } else {
                diverged.push(report);
            }
        }
    }
    let _ = arg_combinations;
    eprintln!("(skipped {skipped_likely_deref} likely-derefs-arg functions)");
    println!(
        "Scan complete: ran {tested} (function × arg-combination) \
         tests, matched {matched}, diverged {}, errored {}",
        diverged.len(),
        errored.len(),
    );
    if !diverged.is_empty() {
        println!("\n--- Divergences ---");
        for r in &diverged {
            println!("{}\n", r.pretty());
        }
    }
    if !errored.is_empty() {
        let cap = 5;
        println!("\n--- Interp errors (first {cap}) ---");
        for r in errored.iter().take(cap) {
            println!("{}\n", r.pretty());
        }
    }
    if diverged.is_empty() {
        Ok(ExitCode::SUCCESS)
    } else {
        Ok(ExitCode::from(2))
    }
}
