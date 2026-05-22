//! JIT-coverage sanity test against the real bootstrap64.txt image.
//!
//! Loads the image, walks every F_CODE_OBJ, and attempts to JIT each
//! one. Counts (compiled-ok, first-unsupported-opcode histogram).
//!
//! This is a *roadmap* test: as the JIT translator gains support
//! for more opcodes, the "ok" fraction should grow. The opcode
//! histogram shows which opcodes appear most often in the failing
//! cases — i.e. which ones to implement next for maximum coverage.
//!
//! Currently SKIPS if vendor/polyml/bootstrap isn't present.

use std::path::PathBuf;

use polyml_image::pexport::Image;
use polyml_jit::{translate, Jit};
use polyml_runtime::{length_word::{self, length_of}, load_image, MemorySpace, PolyWord};

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
fn jit_coverage_on_bootstrap_code_objects() {
    let bs = workspace_root().join("vendor/polyml/bootstrap/bootstrap64.txt");
    if !bs.exists() {
        eprintln!("SKIP: bootstrap64.txt not present");
        return;
    }
    let bytes = std::fs::read(&bs).unwrap();
    let image = Image::parse(&bytes).unwrap();
    let loaded = load_image(&image).unwrap();

    // Walk every space, find code objects, try to JIT each.
    let mut total = 0usize;
    let mut ok = 0usize;
    // First-unsupported-opcode histogram for diagnosis.
    let mut blockers: std::collections::BTreeMap<String, usize> = Default::default();
    let mut shortest_ok: Option<usize> = None;
    let mut shortest_ok_bytes: Vec<u8> = Vec::new();

    let mut jit = Jit::new().unwrap();

    for space in [&loaded.immutable, &loaded.mutable, &loaded.code] {
        walk_code_objects(space, |code_obj_ptr, lw| {
            total += 1;
            let n_words = length_of(lw);
            // Bytecode lives at offset 0 up to where the const segment
            // starts. Use const_segment_for_code to find the boundary.
            let (cp, _count) = unsafe { length_word::const_segment_for_code(code_obj_ptr) };
            let body_start = code_obj_ptr as usize;
            let cp_start = cp as usize;
            // bytecode area ends one PolyWord before the constant area:
            // the loader writes a count word immediately before the
            // constants segment. Without this subtraction the JIT
            // would read the count word as opcodes (often 0x00 high
            // bytes, blocking ~20% of functions).
            let bytecode_len = cp_start
                .saturating_sub(body_start)
                .saturating_sub(std::mem::size_of::<usize>());
            // Bound sanity: shouldn't exceed the object body.
            let max_bytes = n_words * std::mem::size_of::<usize>();
            let bytecode_len = bytecode_len.min(max_bytes);
            // Full body extends through all n_words: bytecode +
            // constant pool + trailer. compile_with_consts walks
            // only [0..bytecode_len) for opcodes; CONST_ADDR8_*
            // reads land in the constants area at higher offsets.
            let full_body: &[u8] = unsafe {
                std::slice::from_raw_parts(code_obj_ptr.cast::<u8>(), max_bytes)
            };
            match translate::compile_with_consts(&mut jit, full_body, bytecode_len) {
                Ok(_) => {
                    ok += 1;
                    if shortest_ok.map_or(true, |s| bytecode_len < s) {
                        shortest_ok = Some(bytecode_len);
                        shortest_ok_bytes = full_body[..bytecode_len].to_vec();
                    }
                }
                Err(translate::TranslateError::Unsupported { op, .. }) => {
                    *blockers.entry(format!("op 0x{op:02x}")).or_insert(0) += 1;
                }
                Err(translate::TranslateError::Truncated(_)) => {
                    *blockers.entry("truncated".into()).or_insert(0) += 1;
                }
                Err(translate::TranslateError::Underflow(_)) => {
                    *blockers.entry("underflow".into()).or_insert(0) += 1;
                }
                Err(translate::TranslateError::FellOffEnd) => {
                    *blockers.entry("fell-off-end".into()).or_insert(0) += 1;
                }
                Err(translate::TranslateError::Jit(je)) => {
                    // Categorise by the verifier-error message body.
                    // Cranelift's `VerifierError { message: ... }` field
                    // is the human-readable diagnostic.
                    let s = format!("{je}");
                    let key = if let Some(start) = s.find("message: \"") {
                        let after = &s[start + "message: \"".len()..];
                        let end = after.find('"').unwrap_or(80);
                        let msg: &str = &after[..end.min(80)];
                        format!("verifier: {msg}")
                    } else {
                        let short: String = s.chars().take(80).collect();
                        format!("jit: {short}")
                    };
                    *blockers.entry(key).or_insert(0) += 1;
                }
            }
        });
    }

    eprintln!("JIT coverage over bootstrap64.txt:");
    eprintln!("  total code objects:  {total}");
    eprintln!("  JIT-compiled OK:     {ok} ({:.2}%)", 100.0 * ok as f64 / total as f64);
    if let Some(s) = shortest_ok {
        eprintln!("  shortest JIT'd bytecode: {s} bytes = {:?}", shortest_ok_bytes);
    }
    eprintln!("  top 10 blockers (first-failure reason per failing function):");
    let mut blockers_vec: Vec<(String, usize)> = blockers.into_iter().collect();
    blockers_vec.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for (kind, n) in blockers_vec.iter().take(10) {
        eprintln!("    {kind:<22}: {n}");
    }

    // Don't assert any specific coverage — just print the report. This
    // is a roadmap test; failures wouldn't be informative until we
    // commit to a coverage SLA.
    assert!(total > 0, "should have walked some code objects");
}

/// Walk every F_CODE_OBJ in a space, calling `f(body_ptr, length_word)`
/// for each. Length-word and trailing-offset must be well-formed.
fn walk_code_objects<F: FnMut(*const PolyWord, PolyWord)>(
    space: &MemorySpace,
    mut f: F,
) {
    // We don't have a public iterator over (body, length_word) pairs;
    // walk the storage manually by re-using the bump-allocated layout
    // (1 length word + body of N words, repeated).
    let mut i = 0usize;
    let used = space.used_words();
    let start = space.iter().next().map(|w| w as *const PolyWord);
    let Some(base) = start else { return };
    while i < used {
        let lw = unsafe { *base.add(i) };
        let n = length_of(lw);
        if n == 0 || i + 1 + n > used {
            break;
        }
        let body = unsafe { base.add(i + 1) };
        if length_word::is_code_object(lw) {
            f(body, lw);
        }
        i += 1 + n;
    }
}
