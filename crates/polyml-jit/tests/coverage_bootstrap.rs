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

    // Capture shortest "mismatched argument count" failure for offline trace.
    let mut shortest_jump_fail: Option<(usize, Vec<u8>, usize, String)> = None;

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
                Err(translate::TranslateError::Unsupported { op, .. }) if op == 0xfd => {
                    if shortest_jump_fail.as_ref().is_none_or(|(sz, ..)| bytecode_len < *sz) {
                        shortest_jump_fail = Some((
                            bytecode_len,
                            full_body[..bytecode_len].to_vec(),
                            max_bytes,
                            "depth_mismatch (0xfd)".into(),
                        ));
                    }
                    *blockers.entry("op 0xfd".into()).or_insert(0) += 1;
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
                    let s = format!("{je}");
                    let msg = if let Some(start) = s.find("message: \"") {
                        let after = &s[start + "message: \"".len()..];
                        let end = after.find('"').unwrap_or(80);
                        Some(&after[..end.min(80)])
                    } else {
                        None
                    };
                    let key = match msg {
                        Some(m) => format!("verifier: {m}"),
                        None => {
                            let short: String = s.chars().take(80).collect();
                            format!("jit: {short}")
                        }
                    };
                    // Capture the shortest function that fails with a
                    // jump-arg-count mismatch, for offline trace.
                    if msg.is_some_and(|m| m.contains("mismatched argument count")) {
                        if shortest_jump_fail.as_ref().is_none_or(|(sz, ..)| bytecode_len < *sz) {
                            shortest_jump_fail = Some((
                                bytecode_len,
                                full_body[..bytecode_len].to_vec(),
                                max_bytes,
                                s,
                            ));
                        }
                    }
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
    if let Some((sz, bytes, total_sz, msg)) = &shortest_jump_fail {
        eprintln!(
            "  shortest jump-mismatch fail: {sz} bytecode bytes (total {total_sz}):",
        );
        eprintln!("    bytes = {bytes:02x?}");
        eprintln!("    msg head: {}", msg.chars().take(160).collect::<String>());
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

/// Focused probe: count how many CASE16 (0x0a) -containing code
/// objects translate, and report the first-failure reason for the rest.
/// Run with: cargo test --release -p polyml-jit --test coverage_bootstrap
///   -- --nocapture case16_coverage
#[test]
fn case16_coverage() {
    let bs = workspace_root().join("vendor/polyml/bootstrap/bootstrap64.txt");
    if !bs.exists() {
        eprintln!("SKIP: bootstrap64.txt not present");
        return;
    }
    let bytes = std::fs::read(&bs).unwrap();
    let image = Image::parse(&bytes).unwrap();
    let loaded = load_image(&image).unwrap();

    let mut with_case16 = 0usize;
    let mut case16_ok = 0usize;
    let mut blockers: std::collections::BTreeMap<String, usize> = Default::default();
    let mut first_fail_bytes: Option<(usize, Vec<u8>)> = None;
    // (full_body, bytecode_len) of the first jit-error CASE16 fn, for IR dump.
    let mut first_jit_fail: Option<(Vec<u8>, usize)> = None;
    let mut jit = Jit::new().unwrap();

    for space in [&loaded.immutable, &loaded.mutable, &loaded.code] {
        walk_code_objects(space, |code_obj_ptr, lw| {
            let n_words = length_of(lw);
            let (cp, _count) = unsafe { length_word::const_segment_for_code(code_obj_ptr) };
            let body_start = code_obj_ptr as usize;
            let cp_start = cp as usize;
            let bytecode_len = cp_start
                .saturating_sub(body_start)
                .saturating_sub(std::mem::size_of::<usize>());
            let max_bytes = n_words * std::mem::size_of::<usize>();
            let bytecode_len = bytecode_len.min(max_bytes);
            let full_body: &[u8] = unsafe {
                std::slice::from_raw_parts(code_obj_ptr.cast::<u8>(), max_bytes)
            };
            let bc = &full_body[..bytecode_len];
            if !translate::has_real_case16(bc) {
                return;
            }
            // Exclude functions that ALSO contain a TRANSLATION blocker
            // unrelated to CASE16 (ESCAPE 0xfe, CALL_CLOSURE 0x0c). Note
            // CALL_LOCAL_B/TAIL_B_B/CALL_CONST_ADDR DO translate (they're
            // only filtered at install time), so they don't block the
            // coverage count and are NOT excluded here.
            let other_blocker = bc.iter().any(|&b| matches!(b, 0x0c | 0xfe));
            if other_blocker {
                return;
            }
            with_case16 += 1;
            match translate::compile_with_consts(&mut jit, full_body, bytecode_len) {
                Ok(_) => case16_ok += 1,
                Err(e) => {
                    let key = match &e {
                        translate::TranslateError::Unsupported { op, .. } => format!("op 0x{op:02x}"),
                        translate::TranslateError::Truncated(_) => "truncated".into(),
                        translate::TranslateError::Underflow(_) => "underflow".into(),
                        translate::TranslateError::FellOffEnd => "fell-off-end".into(),
                        translate::TranslateError::Jit(_) => "jit".into(),
                    };
                    if matches!(e, translate::TranslateError::Jit(_))
                        && first_jit_fail.is_none()
                    {
                        first_jit_fail = Some((full_body.to_vec(), bytecode_len));
                    }
                    // Capture the SMALLEST failing function for offline
                    // tracing (now that non-CASE16 blockers are excluded,
                    // any failure here is CASE16-related).
                    if first_fail_bytes.as_ref().is_none_or(|(s, _)| bytecode_len < *s)
                    {
                        first_fail_bytes = Some((bytecode_len, bc.to_vec()));
                    }
                    *blockers.entry(key).or_insert(0) += 1;
                }
            }
        });
    }

    eprintln!("CASE16 coverage over bootstrap64.txt:");
    eprintln!("  code objects containing 0x0a: {with_case16}");
    eprintln!("  of those, JIT-translate OK:    {case16_ok}");
    let mut bv: Vec<(String, usize)> = blockers.into_iter().collect();
    bv.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    eprintln!("  first-failure reasons:");
    for (k, n) in &bv {
        eprintln!("    {k:<14}: {n}");
    }
    if let Some((len, bytes)) = &first_fail_bytes {
        eprintln!("  first failing function ({len} bytes):");
        let hex: Vec<String> = bytes.iter().map(|b| format!("{b:02x}")).collect();
        eprintln!("    {}", hex.join(" "));
    }
    if let Some((full_body, bclen)) = &first_jit_fail {
        eprintln!("\n=== Re-translating first jit-error CASE16 fn with IR dump ===");
        // Safety: JIT_DUMP_IR is read inside compile; set it for this one.
        unsafe { std::env::set_var("JIT_DUMP_IR", "1"); }
        let mut j2 = Jit::new().unwrap();
        let r = translate::compile_with_consts(&mut j2, full_body, *bclen);
        unsafe { std::env::remove_var("JIT_DUMP_IR"); }
        eprintln!("=== jit-fail re-translate result: {:?}", r.map(|_| ()));
    }
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

/// Offline trace of the smallest CASE16 function that fails to
/// translate. Bytes captured from `case16_coverage`.
#[test]
fn trace_one_case16() {
    let bc: Vec<u8> = vec![
        0x2c,0x57,0x5d,0x29,0x16,0x04,0x2f,0x16,0x01,0x64,0xc7,0x01,0x0a,0x07,0x00,0x19,
        0x00,0x1c,0x00,0x1f,0x00,0x31,0x00,0x3d,0x00,0x40,0x00,0x0e,0x00,0xc1,0x01,0xc6,
        0x2b,0x2a,0x31,0x30,0x32,0x7b,0x05,0x09,0x29,0x02,0x31,0x29,0x02,0x2e,0xc1,0x01,
        0x21,0x02,0x02,0x2b,0x2a,0x31,0x16,0x07,0x29,0x2c,0x32,0x31,0x33,0x7b,0x05,0x0a,
        0xc1,0x01,0x29,0x2d,0x30,0x2d,0x56,0x18,0x32,0x7b,0x06,0x08,0x29,0x02,0x0d,0xc1,
        0x01,0x29,0x2d,0x30,0x2d,0x15,0x08,0x02,0x32,0x7b,0x06,0x08,0x65,0x44,0x3b,0x3b,
    ];
    let mut jit = Jit::new().unwrap();
    // This function reads CONST_ADDR (0x57/0x56...) which need a const
    // pool; with bytecode-only it'll fail on those. Pad full_body.
    let r = translate::compile_with_consts(&mut jit, &bc, bc.len());
    eprintln!("trace result: {r:?}");
}
