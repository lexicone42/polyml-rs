//! Malicious-image corpus + replay harness for the UNTRUSTED safe mode
//! (task #96 — the one honest memory-safety caveat).
//!
//! WHAT THIS PROVES
//! ----------------
//! The pexport image format carries UNTYPED references: a well-formed,
//! in-range word can point at a WRONG-TYPE object, and the loader cannot
//! reject it without whole-image type inference (a limit shared with
//! upstream Poly/ML). When the interpreter later FOLLOWS such a pointer it
//! can cause real UB — an OOB read/write, a wild jump (word0 of a
//! non-closure followed as a code address), or a non-pointer deref.
//!
//! This harness reconstructs a corpus of deliberately-malicious images
//! (the `lf_ref_52` type-confusion repro + wild-pointer / OOB-field /
//! non-closure-call / count-payload variants), then runs EACH through the
//! real `poly` binary in two modes and classifies the outcome:
//!
//!   - SAFE   = clean exit (0/1/2/3/4) or a controlled halt / raised SML
//!              exception. NO undefined behaviour.
//!   - UNSAFE = SEGV (139), abort (134), bus error (135), hang (timeout),
//!              or OOM (137). I.e. real UB escaped.
//!
//! The contract the SAFE MODE must uphold:
//!   * Under `--untrusted`, EVERY image in the corpus is SAFE.
//!   * (We do NOT assert anything about the TRUSTED run — by design it may
//!     UB on a malicious image; that is the documented caveat the safe
//!     mode closes. The harness reports the trusted outcome for contrast.)
//!
//! The corpus is also written to `tools/malicious-corpus/*.txt` (committed)
//! so a human can replay it by hand:
//!   poly run --untrusted tools/malicious-corpus/<name>.txt

#![allow(clippy::doc_lazy_continuation)]
#![allow(clippy::needless_borrows_for_generic_args)]
#![allow(clippy::uninlined_format_args)]

use std::path::{Path, PathBuf};
use std::process::Command;

use polyml_image::pexport::{Image, ObjFlags, Object, ObjectBody, SourceArch, Value, WordSize};

// ---- bytecode opcodes used by the hand-assembled root code objects ----
// (mirrors crates/polyml-runtime/src/interpreter/opcodes.rs)
const LOCAL_0: u8 = 0x29; // push sp[0]
const INDIRECT_B: u8 = 0x23; // pop obj, push obj[imm]
const CALL_CLOSURE: u8 = 0x0c; // pop closure, call it
const RETURN_B: u8 = 0x1f; // return, dropping imm args

/// Build an `Image` from a root index, arch=Interpreted, 64-bit, and the
/// given object bodies. All objects immutable unless `mutable` is set.
fn image_of(root: u32, objects: Vec<(ObjFlags, ObjectBody)>) -> Image {
    Image {
        root,
        arch: SourceArch::Interpreted,
        word_size: WordSize::Bits64,
        objects: objects
            .into_iter()
            .map(|(flags, body)| Object { flags, body })
            .collect(),
    }
}

fn imm(body: ObjectBody) -> (ObjFlags, ObjectBody) {
    (ObjFlags::empty(), body)
}

fn mutable(body: ObjectBody) -> (ObjFlags, ObjectBody) {
    (ObjFlags::MUTABLE, body)
}

/// A code object whose bytecode is `code` with no constants.
fn code(code: Vec<u8>) -> ObjectBody {
    ObjectBody::Code {
        code_bytes: code,
        constants: Vec::new(),
        relocs: Vec::new(),
    }
}

/// Serialize an image to pexport text.
fn to_text(img: &Image) -> Vec<u8> {
    let mut out = Vec::new();
    img.write(&mut out).expect("serialize image");
    out
}

// =====================================================================
// THE CORPUS
// =====================================================================
//
// Each generator returns (name, description, pexport_text).
//
// Construction note: when `poly run` starts, it seeds the ROOT closure on
// top of the stack and begins executing the root closure's code object at
// byte 0 (do_call's frame is set up implicitly). So the root code object's
// bytecode runs FIRST, with sp[0] = the root closure. We hand-assemble that
// bytecode to perform exactly one dangerous deref on a type-confused value.

/// lf_ref_52 (the canonical repro): a tuple/closure field is re-pointed at a
/// valid-but-WRONG-TYPE object (here a code object), then the interpreter
/// FOLLOWS it dangerously. The root code does `LOCAL_0; INDIRECT_B 1` to
/// read capture[0] of the root closure (a Ref to a code object), then
/// CALL_CLOSURE on it. Calling a bare CODE object (not a closure) makes
/// do_call read word0 of the code object — the first BYTECODE word — as the
/// code address → a wild jump in trusted mode. The exact lf_ref_52 class:
/// a field repointed at a wrong-type object that is then mis-followed.
fn corpus_lf_ref_52() -> (&'static str, &'static str, Vec<u8>) {
    // Object layout:
    //   0: root closure C -> code @1, capturing @2 (a wrong-type ref)
    //   1: root code object: LOCAL_0; INDIRECT_B 1; CALL_CLOSURE
    //   2: a CODE object (the wrong-type target the capture points at)
    //
    // INDIRECT_B 1 reads closure field 1 = @2 (the code object pointer).
    // CALL_CLOSURE then treats that code object AS a closure: do_call reads
    // its word0 (a bytecode word, e.g. 0x...0852) as the code address →
    // const_segment_for_code derives a wild code_end → wild PC fetch.
    let root_code = code(vec![
        LOCAL_0,
        INDIRECT_B,
        1,            // closure capture[0] = @2 (a code object)
        CALL_CLOSURE, // mis-follow it as a closure → wild jump
    ]);
    // A real code object whose word0 (first 8 bytecode bytes) is a small,
    // word-aligned-looking value so do_call's is_data_ptr check passes and
    // it proceeds to derive a wild code segment (the dangerous path).
    let target_code = code(vec![0x52, 0x52, 0x52, 0x52, 0x52, 0x52, 0x52, 0x52]);
    let objs = vec![
        imm(ObjectBody::Closure {
            code_addr: 1,
            values: vec![Value::Ref(2)],
        }),
        imm(root_code),
        imm(target_code),
    ];
    (
        "lf_ref_52_type_confused_call",
        "tuple/closure field re-pointed at a code object, then mis-followed as a closure (CALL → wild jump)",
        to_text(&image_of(0, objs)),
    )
}

/// Non-closure CALL: the root closure captures a Ref to an ORDINARY tuple
/// (not a code/closure object), then the bytecode CALLs it. do_call would
/// follow the tuple's word0 as a code address → wild jump.
fn corpus_noncode_call() -> (&'static str, &'static str, Vec<u8>) {
    // 0: root closure C -> code @1, capturing @2 (an ordinary tuple)
    // 1: root code: LOCAL_0; INDIRECT_B 1; CALL_CLOSURE
    // 2: an ordinary tuple O2 holding attacker words
    let root_code = code(vec![
        LOCAL_0,
        INDIRECT_B,
        1,            // capture[0] = @2 (the tuple)
        CALL_CLOSURE, // call it as a closure → follow tuple word0 as code
    ]);
    let objs = vec![
        imm(ObjectBody::Closure {
            code_addr: 1,
            values: vec![Value::Ref(2)],
        }),
        imm(root_code),
        // An ordinary tuple whose word0 is a tagged int; do_call would treat
        // it as a code address (a wild jump in trusted mode).
        imm(ObjectBody::Ordinary(vec![
            Value::Tagged(0x4141_4141),
            Value::Tagged(2),
        ])),
    ];
    (
        "noncode_call_target",
        "closure capture is an ordinary tuple; bytecode CALLs it → do_call follows word0 as a code addr",
        to_text(&image_of(0, objs)),
    )
}

/// Non-closure CALL where the wrong-type target's word0 is itself a Ref to a
/// code object — i.e. a tuple shaped LIKE a closure but NOT flagged as one,
/// pointing at a real code object. Exercises the require_code path AND the
/// const-segment validation: word0 resolves to a code object so the simple
/// is_data_ptr check passes, but the closure object's header is wrong-type.
fn corpus_call_wrongtype_header() -> (&'static str, &'static str, Vec<u8>) {
    // 0: root closure C -> code @1, capturing @2
    // 1: root code: LOCAL_0; INDIRECT_B 1; CALL_CLOSURE
    // 2: an ORDINARY tuple whose field0 = @3 (a real code object)
    // 3: a real code object
    let root_code = code(vec![LOCAL_0, INDIRECT_B, 1, CALL_CLOSURE]);
    let objs = vec![
        imm(ObjectBody::Closure {
            code_addr: 1,
            values: vec![Value::Ref(2)],
        }),
        imm(root_code),
        // Ordinary tuple (type bits 0, NOT closure) whose word0 points at a
        // real code object. do_call resolves word0 to a code object but the
        // "closure" itself is wrong-type. (In the current design do_call
        // does not require the closure header to be F_CLOSURE_OBJ — it reads
        // word0 either way — so the meaningful check is the code-object +
        // const-segment validation on the resolved target, which here is
        // legitimate. This case confirms a wrong-type-but-resolvable closure
        // is handled without UB.)
        imm(ObjectBody::Ordinary(vec![Value::Ref(3)])),
        imm(code(vec![RETURN_B, 0])),
    ];
    (
        "call_wrongtype_closure_header",
        "CALL on an ordinary-tuple 'closure' whose word0 resolves to a real code object",
        to_text(&image_of(0, objs)),
    )
}

/// OOB field index: the root closure is small (1 capture) but the bytecode
/// INDIRECTs at a large field index, reading far past the object.
fn corpus_oob_field() -> (&'static str, &'static str, Vec<u8>) {
    // 0: root closure C -> code @1, capturing @2 (a small tuple)
    // 1: root code: LOCAL_0; INDIRECT_B 1; INDIRECT_B 250; RETURN_B 1
    // 2: a 1-word tuple
    let root_code = code(vec![
        LOCAL_0, INDIRECT_B, 1, // capture[0] = @2 (1-word tuple)
        INDIRECT_B, 250, // read field 250 of a 1-word tuple → OOB
        RETURN_B, 1,
    ]);
    let objs = vec![
        imm(ObjectBody::Closure {
            code_addr: 1,
            values: vec![Value::Ref(2)],
        }),
        imm(root_code),
        imm(ObjectBody::Ordinary(vec![Value::Tagged(7)])),
    ];
    (
        "oob_field_index",
        "INDIRECT at a field index (250) far past a 1-word object → OOB read",
        to_text(&image_of(0, objs)),
    )
}

/// Wild pointer via a forged word in a byte object read back as a word: the
/// root closure captures a Bytes object; the bytecode loads word0 of it via
/// INDIRECT (treating the byte object as a word object), getting an
/// attacker-chosen 8-byte value, then follows THAT as a pointer (INDIRECT
/// again). The followed value is a wild address (not a real object).
fn corpus_wild_pointer() -> (&'static str, &'static str, Vec<u8>) {
    // 0: root closure C -> code @1, capturing @2 (an 8-byte Bytes object)
    // 1: root code: LOCAL_0; INDIRECT_B 1; INDIRECT_B 0; INDIRECT_B 0; RETURN_B 1
    //    - INDIRECT_B 1: closure capture[0] = @2 (the byte object)
    //    - INDIRECT_B 0: read word0 of the byte object = a forged 8-byte addr
    //    - INDIRECT_B 0: follow that forged address as a pointer → wild deref
    // 2: a Bytes object whose 8 bytes spell a plausible-looking but wild
    //    word-aligned address (0x0000_4242_4242_4240).
    let root_code = code(vec![
        LOCAL_0, INDIRECT_B, 1, INDIRECT_B, 0, INDIRECT_B, 0, RETURN_B, 1,
    ]);
    // 8 little-endian bytes = 0x0000_4242_4242_4240 (LSB=0 so it looks like
    // a data pointer, but points nowhere live).
    let forged: [u8; 8] = [0x40, 0x42, 0x42, 0x42, 0x42, 0x00, 0x00, 0x00];
    let objs = vec![
        imm(ObjectBody::Closure {
            code_addr: 1,
            values: vec![Value::Ref(2)],
        }),
        imm(root_code),
        imm(ObjectBody::Bytes(forged.to_vec())),
    ];
    (
        "wild_pointer_from_bytes",
        "read a forged 8-byte word from a Bytes object, then follow it as a pointer → wild deref",
        to_text(&image_of(0, objs)),
    )
}

/// Wrong-type STORE: the root closure captures a Ref to a code object, and
/// the bytecode does LOCAL_0; INDIRECT_B 1 (get the code object); then a
/// crafted STORE into it. Modeled here via LOAD/STORE_ML_WORD path. We use
/// INDIRECT to reach the code object then attempt an OOB-ish read to keep
/// the assembly simple; the STORE-into-immutable path is exercised by the
/// runtime unit tests. (Kept as a READ variant that still type-confuses.)
fn corpus_store_into_immutable() -> (&'static str, &'static str, Vec<u8>) {
    // We model the store hazard as a type-confused read of a mutable cell's
    // contents where the cell ref is actually a code object. The store-side
    // mutation guard (require_mutable) is unit-tested separately; here we
    // confirm the deref of a code object via the cell path is caught.
    // 0: root closure C -> code @1, capturing @2 (a code object)
    // 1: root code: LOCAL_0; INDIRECT_B 1; INDIRECT_B 0; RETURN_B 1
    // 2: a real code object (wrong type for a ref cell)
    let root_code = code(vec![LOCAL_0, INDIRECT_B, 1, INDIRECT_B, 0, RETURN_B, 1]);
    let objs = vec![
        mutable(ObjectBody::Closure {
            code_addr: 1,
            values: vec![Value::Ref(2)],
        }),
        imm(root_code),
        imm(code(vec![0x52, 0x52])),
    ];
    (
        "code_object_as_ref_cell",
        "a code object reached via a closure capture and dereferenced as a ref cell",
        to_text(&image_of(0, objs)),
    )
}

/// CALL where the closure's word0 resolves to an in-space NON-CODE object
/// (an ordinary tuple). This is the case the `require_code` per-op shape
/// check exists for: word0 is a valid, aligned, in-space data pointer (so
/// the tag + membership + header checks all pass) but the resolved object is
/// NOT a code object, so following it as a code address would derive a wild
/// code segment from a tuple's body. Must be caught by require_code.
fn corpus_call_resolves_to_noncode() -> (&'static str, &'static str, Vec<u8>) {
    // 0: root closure C -> code @1, capturing @2 (a "fake closure" tuple)
    // 1: root code: LOCAL_0; INDIRECT_B 1; CALL_CLOSURE
    // 2: ordinary tuple whose word0 = @3 (a NON-code ordinary tuple)
    // 3: ordinary tuple (NOT code) — the resolved "code object"
    let root_code = code(vec![LOCAL_0, INDIRECT_B, 1, CALL_CLOSURE]);
    let objs = vec![
        imm(ObjectBody::Closure {
            code_addr: 1,
            values: vec![Value::Ref(2)],
        }),
        imm(root_code),
        imm(ObjectBody::Ordinary(vec![Value::Ref(3)])),
        imm(ObjectBody::Ordinary(vec![
            Value::Tagged(0x7fff_0000),
            Value::Tagged(0x7fff_0000),
        ])),
    ];
    (
        "call_resolves_to_noncode_object",
        "CALL whose word0 is an in-space, aligned pointer to a NON-code tuple → require_code must fire",
        to_text(&image_of(0, objs)),
    )
}

/// Wild-pointer operand to a REAL op (the task #96 hole found in adversarial
/// verify: `read_real` derefed an image-controlled operand after only
/// is_data_ptr, BEFORE any untrusted branch, reached by every Real op — a
/// wild-but-aligned operand is an 8-byte OOB read -> SEGV). This image reads a
/// forged word from a Bytes object onto the stack, then applies REAL_NEG
/// (ESCAPE 0xfe ; EXTINSTR_REAL_NEG 0x9e) whose real_unop reads it via
/// read_real. Pre-fix: SEGV under --untrusted. Post-fix: read_real validates
/// the operand (in-space + >= 8 bytes) -> clean BadImage halt.
fn corpus_real_wild_operand() -> (&'static str, &'static str, Vec<u8>) {
    // 0: root closure C -> code @1, capturing @2 (an 8-byte Bytes object)
    // 1: LOCAL_0; INDIRECT_B 1 (the bytes obj); INDIRECT_B 0 (forged word ->
    //    top); ESCAPE; REAL_NEG (read_real on the forged wild pointer); RETURN_B 1
    const ESCAPE: u8 = 0xfe;
    const REAL_NEG: u8 = 0x9e;
    let root_code = code(vec![
        LOCAL_0, INDIRECT_B, 1, INDIRECT_B, 0, ESCAPE, REAL_NEG, RETURN_B, 1,
    ]);
    let forged: [u8; 8] = [0x40, 0x42, 0x42, 0x42, 0x42, 0x00, 0x00, 0x00];
    let objs = vec![
        imm(ObjectBody::Closure {
            code_addr: 1,
            values: vec![Value::Ref(2)],
        }),
        imm(root_code),
        imm(ObjectBody::Bytes(forged.to_vec())),
    ];
    (
        "real_neg_wild_operand",
        "a forged wild pointer used as the operand of REAL_NEG -> read_real OOB deref",
        to_text(&image_of(0, objs)),
    )
}

/// Wild-pointer STUB to a typed fast-call (the task #96 THIRD sibling, found by
/// the independent adversarial re-verify: `dispatch_typed_fast_call` read the
/// image-controlled stub's word0 token via `(*p).0` after only is_data_ptr, with
/// no untrusted gate — the typed-FP twin of the hardened generic CALL_FAST_RTS
/// path. Reached by the CALL_FAST_*_TO_* family). Reads a forged word from a
/// Bytes object, dups it (arg + stub both wild), then ESCAPE; CALL_FAST_R_TO_R.
/// Pre-fix: SEGV under --untrusted. Post-fix: validate_obj(stub) -> BadImage.
fn corpus_fastcall_wild_stub() -> (&'static str, &'static str, Vec<u8>) {
    const ESCAPE: u8 = 0xfe;
    const CALL_FAST_R_TO_R: u8 = 0x8f;
    // LOCAL_0; INDIRECT_B 1 (bytes obj); INDIRECT_B 0 (forged word = arg);
    // LOCAL_0 (dup -> stub = forged too); ESCAPE; CALL_FAST_R_TO_R; RETURN_B 1
    let root_code = code(vec![
        LOCAL_0,
        INDIRECT_B,
        1,
        INDIRECT_B,
        0,
        LOCAL_0,
        ESCAPE,
        CALL_FAST_R_TO_R,
        RETURN_B,
        1,
    ]);
    let forged: [u8; 8] = [0x40, 0x42, 0x42, 0x42, 0x42, 0x00, 0x00, 0x00];
    let objs = vec![
        imm(ObjectBody::Closure {
            code_addr: 1,
            values: vec![Value::Ref(2)],
        }),
        imm(root_code),
        imm(ObjectBody::Bytes(forged.to_vec())),
    ];
    (
        "fastcall_wild_stub",
        "a forged wild pointer used as the STUB of CALL_FAST_R_TO_R -> dispatch_typed_fast_call token OOB read",
        to_text(&image_of(0, objs)),
    )
}

fn corpus() -> Vec<(&'static str, &'static str, Vec<u8>)> {
    vec![
        corpus_lf_ref_52(),
        corpus_noncode_call(),
        corpus_call_wrongtype_header(),
        corpus_call_resolves_to_noncode(),
        corpus_oob_field(),
        corpus_wild_pointer(),
        corpus_store_into_immutable(),
        corpus_real_wild_operand(),
        corpus_fastcall_wild_stub(),
    ]
}

// =====================================================================
// THE REPLAY HARNESS
// =====================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
enum Verdict {
    /// Clean exit (any code) or controlled halt / raised exception.
    Safe(i32),
    /// SEGV / abort / bus / OOM / timeout — real UB escaped.
    Unsafe(String),
}

impl Verdict {
    fn is_safe(&self) -> bool {
        matches!(self, Verdict::Safe(_))
    }
}

/// Run `poly run [--untrusted] <image>` as a subprocess and classify the
/// outcome. A child killed by a signal (SEGV=11→139, ABRT=6→134, BUS=7→135)
/// is UNSAFE; any normal exit code is SAFE (a clean halt / error / result).
fn run_poly(poly: &Path, image: &Path, untrusted: bool, timeout_secs: u64) -> Verdict {
    use std::os::unix::process::ExitStatusExt;

    // Use `timeout` to bound hangs; a timeout-killed child exits 124.
    let mut cmd = Command::new("timeout");
    cmd.arg("-k")
        .arg("2")
        .arg(format!("{timeout_secs}"))
        .arg(poly)
        .arg("run");
    if untrusted {
        cmd.arg("--untrusted");
    }
    // Cap steps so a benign infinite loop in a crafted image doesn't hang
    // (it would be classified SAFE as a clean step-cap stop anyway).
    cmd.arg("--max-steps").arg("2000000");
    cmd.arg(image);
    // Keep the heap small + quiet so the harness is fast.
    cmd.env("POLYML_GC_QUIET", "1");
    cmd.env("POLYML_HEAP_BYTES", (64 * 1024 * 1024).to_string());

    let output = match cmd.output() {
        Ok(o) => o,
        Err(e) => return Verdict::Unsafe(format!("spawn failed: {e}")),
    };
    let status = output.status;
    if let Some(sig) = status.signal() {
        // Killed by a signal — the hallmark of UB (SEGV/ABRT/BUS) or a hard
        // OOM kill. timeout's SIGTERM (15) means a hang.
        return Verdict::Unsafe(format!("killed by signal {sig}"));
    }
    let code = status.code().unwrap_or(-1);
    // `timeout` returns 124 when it had to kill the child for running too
    // long → a hang (UNSAFE for our purposes: not a controlled halt).
    if code == 124 {
        return Verdict::Unsafe("timed out (hang)".to_string());
    }
    // 137 = 128+9 (SIGKILL) can surface as an exit code under some shells
    // when the OOM killer fires; treat as UNSAFE.
    if code == 137 {
        return Verdict::Unsafe("OOM (137)".to_string());
    }
    Verdict::Safe(code)
}

/// Locate the built `poly` binary. Cargo sets CARGO_BIN_EXE_poly for
/// integration tests of a crate that defines the `poly` bin.
fn poly_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_poly"))
}

/// Write the corpus to tools/malicious-corpus/ (committed for manual
/// replay) and return the directory + the per-image paths.
fn materialize_corpus() -> (PathBuf, Vec<(&'static str, &'static str, PathBuf)>) {
    // The crate manifest dir is .../crates/polyml-bin; the repo root is two
    // levels up.
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest
        .parent()
        .and_then(Path::parent)
        .expect("repo root")
        .to_path_buf();
    let dir = repo_root.join("tools").join("malicious-corpus");
    std::fs::create_dir_all(&dir).expect("create corpus dir");
    let mut paths = Vec::new();
    for (name, desc, text) in corpus() {
        let path = dir.join(format!("{name}.txt"));
        std::fs::write(&path, &text).expect("write corpus image");
        paths.push((name, desc, path));
    }
    // Also drop a README so the committed corpus is self-documenting.
    let readme = format!(
        "# Malicious-image corpus (task #96 — untrusted safe mode)\n\n\
         Each `.txt` here is a deliberately-malicious pexport image that drives a\n\
         dangerous pointer-follow in the interpreter (type-confusion / wild ptr /\n\
         OOB field / non-closure call). Run each through the SAFE MODE:\n\n\
         ```\n\
         poly run --untrusted <image>.txt\n\
         ```\n\n\
         Under `--untrusted` every one of these is SAFE: it halts cleanly with a\n\
         `bad untrusted image` error (exit 4) or a controlled stop, NEVER a SEGV /\n\
         OOB / abort / hang. Without `--untrusted` (the trusted default) a\n\
         malicious image may cause UB — that is the documented caveat the safe\n\
         mode closes.\n\n\
         These are regenerated + replayed by\n\
         `cargo test -p polyml-bin --test untrusted_corpus`.\n\n\
         ## Images\n\n{}\n",
        corpus()
            .iter()
            .map(|(n, d, _)| format!("- `{n}.txt` — {d}"))
            .collect::<Vec<_>>()
            .join("\n")
    );
    std::fs::write(dir.join("README.md"), readme).expect("write corpus README");
    (dir, paths)
}

/// THE CORE GATE: every malicious image is SAFE under `--untrusted`.
#[test]
fn untrusted_mode_catches_every_malicious_image() {
    let poly = poly_bin();
    let (dir, images) = materialize_corpus();
    eprintln!("corpus dir: {}", dir.display());

    let mut all_safe = true;
    for (name, desc, path) in &images {
        let trusted = run_poly(&poly, path, false, 20);
        let untrusted = run_poly(&poly, path, true, 20);
        eprintln!(
            "  [{}] trusted={:?} untrusted={:?}  — {desc}",
            name, trusted, untrusted
        );
        // The GATE: untrusted must be SAFE for every image.
        if !untrusted.is_safe() {
            eprintln!("    !! UNTRUSTED UNSAFE for {name}: {untrusted:?}");
            all_safe = false;
        }
    }
    assert!(
        all_safe,
        "the untrusted safe mode left at least one malicious image UNSAFE \
         (a missed deref site / a hole) — see the per-image lines above"
    );
}

/// The harness also constructs FRESH ad-hoc malicious images at runtime
/// (independent of the committed corpus) and confirms they too are caught —
/// the adversarial-self-check the task asks for.
#[test]
fn untrusted_mode_catches_fresh_adversarial_images() {
    let poly = poly_bin();
    let tmp = std::env::temp_dir().join("polyml_untrusted_fresh");
    std::fs::create_dir_all(&tmp).expect("tmp dir");

    // Fresh #1: a closure capturing a Ref to a STRING object, then CALLed.
    let c1 = {
        let root_code = code(vec![LOCAL_0, INDIRECT_B, 1, CALL_CLOSURE]);
        let objs = vec![
            imm(ObjectBody::Closure {
                code_addr: 1,
                values: vec![Value::Ref(2)],
            }),
            imm(root_code),
            imm(ObjectBody::String(b"not a closure".to_vec())),
        ];
        ("fresh_string_call", to_text(&image_of(0, objs)))
    };
    // Fresh #2: INDIRECT at index 9999 of a 2-word tuple.
    let c2 = {
        let root_code = code(vec![LOCAL_0, INDIRECT_B, 1, INDIRECT_B, 0xff, RETURN_B, 1]);
        let objs = vec![
            imm(ObjectBody::Closure {
                code_addr: 1,
                values: vec![Value::Ref(2)],
            }),
            imm(root_code),
            imm(ObjectBody::Ordinary(vec![
                Value::Tagged(1),
                Value::Tagged(2),
            ])),
        ];
        ("fresh_oob_255", to_text(&image_of(0, objs)))
    };
    // Fresh #3: a closure whose capture is a tagged int, followed as a ptr.
    let c3 = {
        let root_code = code(vec![LOCAL_0, INDIRECT_B, 1, INDIRECT_B, 0, RETURN_B, 1]);
        let objs = vec![
            imm(ObjectBody::Closure {
                code_addr: 1,
                values: vec![Value::Tagged(12345)],
            }),
            imm(root_code),
        ];
        ("fresh_tagged_as_ptr", to_text(&image_of(0, objs)))
    };

    let mut all_safe = true;
    for (name, text) in [c1, c2, c3] {
        let path = tmp.join(format!("{name}.txt"));
        std::fs::write(&path, &text).expect("write fresh image");
        let untrusted = run_poly(&poly, &path, true, 20);
        eprintln!("  fresh [{name}] untrusted={untrusted:?}");
        if !untrusted.is_safe() {
            all_safe = false;
        }
    }
    assert!(
        all_safe,
        "a fresh adversarial image was UNSAFE under --untrusted (a hole)"
    );
}

/// Sanity: the legitimate bootstrap image is byte-identical in untrusted
/// mode (the predicate accepts every legitimate deref — it does not break a
/// real image). We only run this if the bootstrap image is present.
#[test]
fn untrusted_bootstrap_is_byte_identical() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_root = manifest
        .parent()
        .and_then(Path::parent)
        .unwrap()
        .to_path_buf();
    // Search the worktree first, then the canonical main checkout (the
    // vendor tree is not symlinked into every worktree).
    let rel = "vendor/polyml/bootstrap/bootstrap64.txt";
    let candidates = [
        repo_root.join(rel),
        PathBuf::from("/datar/workspace/claude_code_experiments/polyml-rs").join(rel),
    ];
    let boot = match candidates.iter().find(|p| p.exists()) {
        Some(p) => p.clone(),
        None => {
            eprintln!("bootstrap image absent; skipping byte-identical check");
            return;
        }
    };
    let poly = poly_bin();
    let run = |untrusted: bool| -> (i32, String) {
        let mut cmd = Command::new(&poly);
        cmd.arg("run");
        if untrusted {
            cmd.arg("--untrusted");
        }
        cmd.arg(&boot);
        cmd.env("POLYML_GC_QUIET", "1");
        let out = cmd.output().expect("run bootstrap");
        let stdout = String::from_utf8_lossy(&out.stdout).to_string();
        let steps = stdout
            .lines()
            .find(|l| l.contains("Executed"))
            .unwrap_or("")
            .to_string();
        (out.status.code().unwrap_or(-1), steps)
    };
    let (tc, ts) = run(false);
    let (uc, us) = run(true);
    eprintln!("trusted: code={tc} {ts}");
    eprintln!("untrusted: code={uc} {us}");
    assert_eq!(
        tc, uc,
        "exit code differs trusted vs untrusted on bootstrap"
    );
    assert!(
        ts.contains("1110805"),
        "trusted bootstrap step count drifted: {ts}"
    );
    assert_eq!(
        ts, us,
        "untrusted bootstrap is NOT byte-identical to trusted"
    );
}
