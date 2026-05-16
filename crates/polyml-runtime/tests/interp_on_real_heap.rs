//! Cross-cutting test: the interpreter can read fields out of objects
//! placed in `MemorySpace`s by the real loader.
//!
//! This is the smallest end-to-end demonstration that the value
//! representation chosen by the loader and the value representation
//! consumed by the interpreter are compatible.

use std::path::PathBuf;

use polyml_image::pexport::Image;
use polyml_runtime::{
    interpreter::opcodes::*, load_image, Interpreter, MemorySpace, PolyWord, StepResult,
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
        assert!(
            p.pop(),
            "could not find workspace root from {}",
            env!("CARGO_MANIFEST_DIR")
        );
    }
}

#[test]
fn interpreter_reads_real_heap_via_indirect() {
    let path = workspace_root().join("vendor/polyml/bootstrap/bootstrap64.txt");
    let Ok(bytes) = std::fs::read(&path) else {
        eprintln!("SKIP: {} not present", path.display());
        return;
    };
    let image = Image::parse(&bytes).expect("parse");
    let loaded = load_image(&image).expect("load_image");

    // Bootstrap root is a Closure: 1 word = code address.
    // Hand-build a tiny program that, given the closure pointer
    // pre-seeded on top of the stack, reads its first word via
    // INDIRECT_0 and returns it.
    let code = vec![INSTR_INDIRECT_0, INSTR_RETURN_1];
    let mut interp = Interpreter::new(64, code);
    interp.test_seed_top(PolyWord::from_ptr(loaded.root));

    let result = interp.run().expect("run");
    let StepResult::Returned(code_word) = result else {
        panic!("expected Returned, got {result:?}");
    };
    assert!(code_word.is_data_ptr(), "code_word should be a pointer, got {code_word:?}");

    // The fetched value should be the same as what reading the root
    // object directly would yield — namely the code pointer stored at
    // the closure's first word.
    let direct = unsafe { *loaded.root };
    assert_eq!(
        code_word.0, direct.0,
        "INDIRECT_0 should match a direct read"
    );

    // And following that pointer one more level: the code object's
    // length word should mark it as a Code object.
    let code_ptr: *const PolyWord = code_word.as_ptr();
    let code_lw = unsafe { MemorySpace::length_word_of(code_ptr) };
    assert!(
        polyml_runtime::length_word::is_code_object(code_lw),
        "closure should point at a Code object (got flags 0x{:02x})",
        polyml_runtime::length_word::flags_of(code_lw)
    );

    eprintln!(
        "OK: interpreter followed root closure -> code object \
         (code len = {} words)",
        polyml_runtime::length_word::length_of(code_lw)
    );
}
