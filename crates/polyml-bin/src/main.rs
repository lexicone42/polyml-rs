//! The `poly` binary entry point.
//!
//! Monday-milestone scope: load a pexport heap image, transfer control
//! to its root function, exit cleanly. We're not at the "transfer
//! control" part yet — Phase 2.1 (bytecode interpreter port) unlocks
//! that. For now this binary loads + reports.

use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use polyml_image::pexport::{Image, ObjectBody};
use polyml_runtime::{length_word, load_image, MemorySpace, PolyWord};

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
