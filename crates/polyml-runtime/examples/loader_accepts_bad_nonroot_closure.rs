//! Reachability half of AUDIT finding index 1/2: prove the LOADER +
//! `ensure_runnable` ACCEPT an image whose ROOT is well-formed but whose
//! NON-ROOT closure has a word0 (code_addr) pointing at a NON-CODE object.
//!
//! The interpreter's `do_call` (mod.rs:4305-4352) then trusts that word0
//! is a code object with zero release-time validation (see the companion
//! `do_call_bad_code_word` example for the resulting SIGSEGV / wild
//! code_end). Together they show the bug is reachable on the supported
//! `poly run <image>` path, not just via the `test_invoke_do_call` hook.
//!
//!   cargo run --release -p polyml-runtime --example loader_accepts_bad_nonroot_closure

use polyml_image::pexport::Image;
use polyml_runtime::load_image;

fn main() {
    // Object 0: root closure -> code object 1 (well-formed; passes runnable).
    // Object 1: a real F-code object (empty bytecode, no consts).
    // Object 2: a NON-ROOT closure whose code address @3 points at...
    // Object 3: an ORDINARY tuple (NOT a code object).
    //
    // The root reaches object 2 via a captured ref (@2). When the running
    // SML eventually CALLs that captured closure, do_call derefs @3 as a
    // code object -> wild.
    let src = b"Objects\t4\n\
                Root\t0 I 8\n\
                0:C2|@1,@2\n\
                1:F0,0|||\n\
                2:C1|@3\n\
                3:O1|42\n";

    let image = Image::parse(src).expect("image parses");
    println!(
        "parsed image: {} objects, root={}",
        image.objects.len(),
        image.root
    );

    let loaded = load_image(&image).expect("image loads into memory spaces");
    match loaded.runnable {
        Ok(()) => println!(
            "ensure_runnable: ACCEPTED — the loader is happy even though object 2 \n\
             (a NON-root closure) has word0 -> object 3 (an ORDINARY tuple, NOT code)."
        ),
        Err(why) => {
            println!("ensure_runnable: REJECTED ({why}) — would be the safe outcome.");
            std::process::exit(1);
        }
    }

    // Confirm object 2's word0 really points at the non-code tuple.
    // Find object 2's pointer by walking: root captures @2 at body[2].
    // (We just assert the load succeeded; the deref crash is proven in the
    // companion example. This example's job is the loader-acceptance half.)
    println!(
        "REACHABILITY CONFIRMED: a corrupted image with a type-confused NON-ROOT \n\
         closure passes load + ensure_runnable; only the ROOT closure's code \n\
         address is type-checked (loader.rs:260-275). do_call trusts every \n\
         other closure's word0 with no release-time code-object check."
    );
    let _ = loaded;
}
