//! HOL4 reconnaissance: try to compile pieces of the HOL4 source
//! tree through our runtime, growing the list as more compile.
//!
//! Each test case is a single HOL4 module (or a small group). The
//! test loads the basis, then `PolyML.use`s the file(s), then
//! prints a sentinel. We assert the sentinel appears in output.
//!
//! All tests are `#[ignore]` because they each take ~3 minutes
//! (most of that is basis load). Run with:
//!
//! ```sh
//! cargo test -p polyml-bin --test hol4_recon -- --ignored --nocapture
//! ```

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

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

fn poly_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_poly"))
}

fn bootstrap_image() -> Option<PathBuf> {
    let p = workspace_root().join("vendor/polyml/bootstrap/bootstrap64.txt");
    p.exists().then_some(p)
}

fn vendor_polyml_dir() -> Option<PathBuf> {
    let p = workspace_root().join("vendor/polyml");
    p.exists().then_some(p)
}

fn hol4_dir() -> Option<PathBuf> {
    let p = workspace_root().join("vendor/hol4");
    p.exists().then_some(p)
}

/// Run our `poly run` on bootstrap64.txt, piping `sml_driver` on
/// stdin from `vendor/polyml/` as cwd. Returns (combined output,
/// exit code).
fn run_with_driver(
    sml_driver: &str,
    max_steps: u64,
) -> std::io::Result<(String, i32)> {
    let image = bootstrap_image().expect("bootstrap image");
    let vendor = vendor_polyml_dir().expect("vendor polyml");
    let mut child = Command::new(poly_bin())
        .current_dir(&vendor)
        .arg("run")
        .arg("--max-steps")
        .arg(max_steps.to_string())
        .arg(&image)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .env("POLYML_GC_THRESHOLD", "99") // minimise GC overhead
        .env("POLYML_GC_QUIET", "1")
        .spawn()?;
    child.stdin.as_mut().unwrap().write_all(sml_driver.as_bytes())?;
    drop(child.stdin.take());
    let out = child.wait_with_output()?;
    let combined = format!(
        "{}\n---STDERR---\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    Ok((combined, out.status.code().unwrap_or(-1)))
}

fn skip_if_missing() -> Option<()> {
    bootstrap_image()?;
    hol4_dir()?;
    Some(())
}

/// Path to the basis-loaded checkpoint built by:
///
/// ```sh
/// cd vendor/polyml
/// echo 'val () = Bootstrap.use "basis/build.sml";
///       val () = PolyML.export("/tmp/basis_loaded", PolyML.rootFunction);' \
///   | ../../target/release/poly run --max-steps 10000000000 \
///       bootstrap/bootstrap64.txt
/// ```
///
/// Re-using this skips the 3-5 min basis-load on every test. The
/// helper functions below check for it and skip the test cleanly
/// if it's absent.
fn checkpoint_path() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/basis_loaded");
    p.exists().then_some(p)
}

fn run_through_checkpoint(sml: &str, max_steps: u64) -> Option<(String, i32)> {
    let ckpt = checkpoint_path()?;
    let mut child = Command::new(poly_bin())
        .arg("run")
        .arg("--max-steps")
        .arg(max_steps.to_string())
        .arg(&ckpt)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .env("POLYML_GC_QUIET", "1")
        .spawn()
        .ok()?;
    child.stdin.as_mut()?.write_all(sml.as_bytes()).ok()?;
    drop(child.stdin.take());
    let out = child.wait_with_output().ok()?;
    let combined = format!(
        "{}\n---STDERR---\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    Some((combined, out.status.code().unwrap_or(-1)))
}

/// Strict pass check: sentinel present AND no compile errors.
///
/// HOL4 source uses `PolyML.use` per file. Each use compiles the
/// file with the toplevel REPL, which prints errors to stderr but
/// continues to the next statement. So a test that only checks for
/// the trailing sentinel is a false positive whenever earlier files
/// fail. This helper rejects both modes.
fn assert_compile_clean(out: &str, sentinel: &str) {
    let errs: Vec<&str> = out
        .lines()
        .filter(|l| {
            l.contains(": error:")
                || l.contains("Static Errors")
                || l.contains("Exception- Fail \"Static Errors\"")
        })
        .take(10)
        .collect();
    if !errs.is_empty() {
        let tail: String = out
            .lines()
            .rev()
            .take(20)
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect::<Vec<_>>()
            .join("\n");
        panic!(
            "compile errors in HOL4 source (showing up to 10):\n{}\n\
             ---tail---\n{}",
            errs.join("\n"),
            tail,
        );
    }
    assert!(
        out.contains(sentinel),
        "missing sentinel {sentinel}. Output (tail):\n{}",
        out.lines()
            .rev()
            .take(20)
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

#[test]
fn recon_via_checkpoint_compiles_simple_buffer() {
    let Some(_) = checkpoint_path() else {
        eprintln!("SKIP: /tmp/basis_loaded not present (build via README)");
        return;
    };
    if hol4_dir().is_none() {
        eprintln!("SKIP: vendor/hol4 not present");
        return;
    }
    let hol = hol4_dir().unwrap();
    let driver = format!(
        "PolyML.use \"{path}/tools/util/SimpleBuffer.sig\";\n\
         PolyML.use \"{path}/tools/util/SimpleBuffer.sml\";\n\
         print \"HOL_OK\\n\";\n",
        path = hol.display(),
    );
    let Some((out, code)) = run_through_checkpoint(&driver, 1_000_000_000) else {
        panic!("subprocess failure");
    };
    assert_compile_clean(&out, "HOL_OK");
    assert_eq!(code, 0, "non-zero exit. Output:\n{out}");
}

#[test]
fn recon_via_checkpoint_compiles_portable() {
    let Some(_) = checkpoint_path() else {
        eprintln!("SKIP: /tmp/basis_loaded not present");
        return;
    };
    if hol4_dir().is_none() {
        eprintln!("SKIP: vendor/hol4 not present");
        return;
    }
    let hol = hol4_dir().unwrap();
    let pm = format!("{}/src/portableML", hol.display());
    let hfs = format!("{}/tools/Holmake/hfs", hol.display());
    let hpoly = format!("{}/tools/Holmake/poly", hol.display());
    let driver = format!(
        "fun U f = PolyML.use (\"{pm}/\" ^ f);\n\
         fun H f = PolyML.use (\"{hfs}/\" ^ f);\n\
         fun HP f = PolyML.use (\"{hpoly}/\" ^ f);\n\
         U \"quotation_dtype.sml\";\n\
         U \"poly/PrettyImpl.sml\";\n\
         U \"poly/Exn.sig\"; U \"poly/Exn.sml\";\n\
         U \"Uref.sig\"; U \"Uref.sml\";\n\
         U \"UTF8.sig\"; U \"UTF8.sml\";\n\
         U \"HOLPP.sig\"; U \"HOLPP.sml\";\n\
         U \"OldPP.sig\"; U \"OldPP.sml\";\n\
         U \"poly/Arbnumcore.sig\"; U \"poly/Arbnumcore.sml\";\n\
         U \"Arbnum.sig\"; U \"Arbnum.sml\";\n\
         H \"HOLFS_dtype.sml\";\n\
         H \"HFS_NameMunge.sig\";\n\
         HP \"HFS_NameMunge.sml\";\n\
         H \"HOLFileSys.sig\"; H \"HOLFileSys.sml\";\n\
         U \"poly/MD5.sig\"; U \"poly/MD5.sml\";\n\
         U \"poly/Susp.sig\"; U \"poly/Susp.sml\";\n\
         U \"poly/Thread_Attributes.sml\";\n\
         U \"poly/Thread_Data.sml\";\n\
         U \"poly/Unsynchronized.sml\";\n\
         U \"poly/ConcIsaLib.sml\";\n\
         U \"poly/Multithreading.sml\";\n\
         U \"poly/Synchronized.sml\";\n\
         U \"HOLquotation.sig\"; U \"HOLquotation.sml\";\n\
         U \"poly/MLSYSPortable.sml\";\n\
         U \"Portable.sig\"; U \"Portable.sml\";\n\
         print \"HOL_PORTABLE_OK\\n\";\n",
    );
    let Some((out, _)) = run_through_checkpoint(&driver, 5_000_000_000) else {
        panic!("subprocess failure");
    };
    assert_compile_clean(&out, "HOL_PORTABLE_OK");
}

#[test]
fn recon_via_checkpoint_compiles_prekernel_lib() {
    let Some(_) = checkpoint_path() else {
        eprintln!("SKIP: /tmp/basis_loaded not present");
        return;
    };
    if hol4_dir().is_none() {
        eprintln!("SKIP: vendor/hol4 not present");
        return;
    }
    let hol = hol4_dir().unwrap();
    let pm = format!("{}/src/portableML", hol.display());
    let pk = format!("{}/src/prekernel", hol.display());
    let hfs = format!("{}/tools/Holmake/hfs", hol.display());
    let hpoly = format!("{}/tools/Holmake/poly", hol.display());
    let driver = format!(
        "fun PMu f = PolyML.use (\"{pm}/\" ^ f);\n\
         fun PKu f = PolyML.use (\"{pk}/\" ^ f);\n\
         fun H f = PolyML.use (\"{hfs}/\" ^ f);\n\
         fun HP f = PolyML.use (\"{hpoly}/\" ^ f);\n\
         (* Holmake-generated Systeml stub: HOL4 expects it to exist. *)\n\
         structure Systeml = struct\n\
           val HOLDIR = \"\";\n\
           val release = \"polyml-rs\";\n\
           val version = 0;\n\
         end;\n\
         structure Path = OS.Path;\n\
         PMu \"quotation_dtype.sml\";\n\
         PMu \"poly/PrettyImpl.sml\";\n\
         PMu \"poly/Exn.sig\"; PMu \"poly/Exn.sml\";\n\
         PMu \"Uref.sig\"; PMu \"Uref.sml\";\n\
         PMu \"UTF8.sig\"; PMu \"UTF8.sml\";\n\
         PMu \"HOLPP.sig\"; PMu \"HOLPP.sml\";\n\
         PMu \"OldPP.sig\"; PMu \"OldPP.sml\";\n\
         PMu \"poly/Arbnumcore.sig\"; PMu \"poly/Arbnumcore.sml\";\n\
         PMu \"Arbnum.sig\"; PMu \"Arbnum.sml\";\n\
         H \"HOLFS_dtype.sml\";\n\
         H \"HFS_NameMunge.sig\"; HP \"HFS_NameMunge.sml\";\n\
         H \"HOLFileSys.sig\"; H \"HOLFileSys.sml\";\n\
         PMu \"poly/MD5.sig\"; PMu \"poly/MD5.sml\";\n\
         PMu \"poly/Susp.sig\"; PMu \"poly/Susp.sml\";\n\
         PMu \"poly/Thread_Attributes.sml\";\n\
         PMu \"poly/Thread_Data.sml\";\n\
         PMu \"poly/Unsynchronized.sml\";\n\
         PMu \"poly/ConcIsaLib.sml\";\n\
         PMu \"poly/Multithreading.sml\";\n\
         PMu \"poly/Synchronized.sml\";\n\
         PMu \"HOLquotation.sig\"; PMu \"HOLquotation.sml\";\n\
         PMu \"poly/MLSYSPortable.sml\";\n\
         PMu \"Portable.sig\"; PMu \"Portable.sml\";\n\
         PMu \"Redblackmap.sig\"; PMu \"Redblackmap.sml\";\n\
         PMu \"Redblackset.sig\"; PMu \"Redblackset.sml\";\n\
         PMu \"HOLset.sig\"; PMu \"HOLset.sml\";\n\
         PMu \"Table.sml\";\n\
         PMu \"Symtab.sml\";\n\
         PMu \"Inttab.sml\";\n\
         PMu \"locn.sig\"; PMu \"locn.sml\";\n\
         PMu \"poly/CoreReplVARS.sml\";\n\
         PKu \"Feedback_dtype.sml\";\n\
         PKu \"Globals.sig\"; PKu \"Globals.sml\";\n\
         PKu \"Feedback.sig\"; PKu \"Feedback.sml\";\n\
         PKu \"Lib.sig\"; PKu \"Lib.sml\";\n\
         print \"HOL_LIB_OK\\n\";\n",
    );
    let Some((out, _)) = run_through_checkpoint(&driver, 10_000_000_000) else {
        panic!("subprocess failure");
    };
    assert_compile_clean(&out, "HOL_LIB_OK");
}

#[test]
fn recon_via_checkpoint_compiles_hol4_kernel() {
    let Some(_) = checkpoint_path() else {
        eprintln!("SKIP: /tmp/basis_loaded not present");
        return;
    };
    if hol4_dir().is_none() {
        eprintln!("SKIP: vendor/hol4 not present");
        return;
    }
    let hol = hol4_dir().unwrap();
    let pm = format!("{}/src/portableML", hol.display());
    let pk = format!("{}/src/prekernel", hol.display());
    let k0 = format!("{}/src/0", hol.display());
    let tp = format!("{}/tools-poly/poly", hol.display());
    let hfs = format!("{}/tools/Holmake/hfs", hol.display());
    let hpoly = format!("{}/tools/Holmake/poly", hol.display());
    let driver = format!(
        "fun PMu f = PolyML.use (\"{pm}/\" ^ f);\n\
         fun PKu f = PolyML.use (\"{pk}/\" ^ f);\n\
         fun K0u f = PolyML.use (\"{k0}/\" ^ f);\n\
         fun TPu f = PolyML.use (\"{tp}/\" ^ f);\n\
         fun H f = PolyML.use (\"{hfs}/\" ^ f);\n\
         fun HP f = PolyML.use (\"{hpoly}/\" ^ f);\n\
         (* Holmake-generated Systeml stub: HOL4 expects it to exist. *)\n\
         structure Systeml = struct\n\
           val HOLDIR = \"\";\n\
           val release = \"polyml-rs\";\n\
           val version = 0;\n\
         end;\n\
         structure Path = OS.Path;\n\
         PMu \"quotation_dtype.sml\";\n\
         PMu \"poly/PrettyImpl.sml\";\n\
         PMu \"poly/Exn.sig\"; PMu \"poly/Exn.sml\";\n\
         PMu \"Uref.sig\"; PMu \"Uref.sml\";\n\
         PMu \"UTF8.sig\"; PMu \"UTF8.sml\";\n\
         PMu \"HOLPP.sig\"; PMu \"HOLPP.sml\";\n\
         PMu \"OldPP.sig\"; PMu \"OldPP.sml\";\n\
         PMu \"poly/Arbnumcore.sig\"; PMu \"poly/Arbnumcore.sml\";\n\
         PMu \"Arbnum.sig\"; PMu \"Arbnum.sml\";\n\
         H \"HOLFS_dtype.sml\";\n\
         H \"HFS_NameMunge.sig\"; HP \"HFS_NameMunge.sml\";\n\
         H \"HOLFileSys.sig\"; H \"HOLFileSys.sml\";\n\
         PMu \"poly/MD5.sig\"; PMu \"poly/MD5.sml\";\n\
         PMu \"poly/Susp.sig\"; PMu \"poly/Susp.sml\";\n\
         PMu \"poly/Thread_Attributes.sml\";\n\
         PMu \"poly/Thread_Data.sml\";\n\
         PMu \"poly/Unsynchronized.sml\";\n\
         PMu \"poly/ConcIsaLib.sml\";\n\
         PMu \"poly/Multithreading.sml\";\n\
         PMu \"poly/Synchronized.sml\";\n\
         PMu \"HOLquotation.sig\"; PMu \"HOLquotation.sml\";\n\
         PMu \"poly/MLSYSPortable.sml\";\n\
         PMu \"Portable.sig\"; PMu \"Portable.sml\";\n\
         PMu \"Redblackmap.sig\"; PMu \"Redblackmap.sml\";\n\
         PMu \"Redblackset.sig\"; PMu \"Redblackset.sml\";\n\
         PMu \"HOLset.sig\"; PMu \"HOLset.sml\";\n\
         PMu \"Table.sml\";\n\
         PMu \"Symtab.sml\";\n\
         PMu \"Inttab.sml\";\n\
         PMu \"locn.sig\"; PMu \"locn.sml\";\n\
         PMu \"poly/CoreReplVARS.sml\";\n\
         PMu \"poly/concurrent/Sref.sig\"; PMu \"poly/concurrent/Sref.sml\";\n\
         PKu \"Feedback_dtype.sml\";\n\
         PKu \"Globals.sig\"; PKu \"Globals.sml\";\n\
         PKu \"Feedback.sig\"; PKu \"Feedback.sml\";\n\
         PKu \"Lib.sig\"; PKu \"Lib.sml\";\n\
         PKu \"Count.sig\"; PKu \"Count.sml\";\n\
         PKu \"Nonce.sig\"; PKu \"Nonce.sml\";\n\
         PKu \"Dep.sig\"; PKu \"Dep.sml\";\n\
         PKu \"Tag.sig\"; PKu \"Tag.sml\";\n\
         TPu \"Binarymap.sig\"; TPu \"Binarymap.sml\";\n\
         PKu \"KernelSig.sig\"; PKu \"KernelSig.sml\";\n\
         PKu \"FinalType-sig.sml\";\n\
         PKu \"FinalTerm-sig.sml\";\n\
         PKu \"FinalThm-sig.sml\";\n\
         PKu \"FinalNet-sig.sml\";\n\
         PKu \"FinalTag-sig.sml\";\n\
         TPu \"Binaryset.sig\"; TPu \"Binaryset.sml\";\n\
         PMu \"UnicodeChars.sig\"; PMu \"UnicodeChars.sml\";\n\
         PKu \"Lexis.sig\"; PKu \"Lexis.sml\";\n\
         K0u \"Subst.sig\"; K0u \"Subst.sml\";\n\
         K0u \"KernelTypes.sml\";\n\
         K0u \"Type.sig\"; K0u \"Type.sml\";\n\
         K0u \"Term.sig\"; K0u \"Term.sml\";\n\
         K0u \"Net.sig\"; K0u \"Net.sml\";\n\
         print \"HOL_KERNEL_OK\\n\";\n",
    );
    let Some((out, _)) = run_through_checkpoint(&driver, 100_000_000_000) else {
        panic!("subprocess failure");
    };
    assert_compile_clean(&out, "HOL_KERNEL_OK");
}

/// Real HOL4 proofs through our runtime: REFL, ASSUME, DISCH —
/// the three primitive inference rules that ground propositional
/// reasoning. Each produces a `Thm` value with verifiable
/// conclusion and hypothesis-set.
#[test]
fn recon_via_checkpoint_proves_implication_self() {
    let Some(_) = checkpoint_path() else {
        eprintln!("SKIP: /tmp/basis_loaded not present");
        return;
    };
    if hol4_dir().is_none() {
        eprintln!("SKIP: vendor/hol4 not present");
        return;
    }
    let hol = hol4_dir().unwrap();
    let pm = format!("{}/src/portableML", hol.display());
    let pk = format!("{}/src/prekernel", hol.display());
    let k0 = format!("{}/src/0", hol.display());
    let tp = format!("{}/tools-poly/poly", hol.display());
    let hfs = format!("{}/tools/Holmake/hfs", hol.display());
    let hpoly = format!("{}/tools/Holmake/poly", hol.display());
    let thm = format!("{}/src/thm", hol.display());
    let driver = format!(
        "fun PMu f = PolyML.use (\"{pm}/\" ^ f);\n\
         fun PKu f = PolyML.use (\"{pk}/\" ^ f);\n\
         fun K0u f = PolyML.use (\"{k0}/\" ^ f);\n\
         fun TPu f = PolyML.use (\"{tp}/\" ^ f);\n\
         fun H f = PolyML.use (\"{hfs}/\" ^ f);\n\
         fun HP f = PolyML.use (\"{hpoly}/\" ^ f);\n\
         fun Tu f = PolyML.use (\"{thm}/\" ^ f);\n\
         structure Systeml = struct\n\
           val HOLDIR = \"\"; val release = \"polyml-rs\"; val version = 0;\n\
         end;\n\
         structure Path = OS.Path;\n\
         PMu \"quotation_dtype.sml\"; PMu \"poly/PrettyImpl.sml\";\n\
         PMu \"poly/Exn.sig\"; PMu \"poly/Exn.sml\";\n\
         PMu \"Uref.sig\"; PMu \"Uref.sml\";\n\
         PMu \"UTF8.sig\"; PMu \"UTF8.sml\";\n\
         PMu \"HOLPP.sig\"; PMu \"HOLPP.sml\";\n\
         PMu \"OldPP.sig\"; PMu \"OldPP.sml\";\n\
         PMu \"poly/Arbnumcore.sig\"; PMu \"poly/Arbnumcore.sml\";\n\
         PMu \"Arbnum.sig\"; PMu \"Arbnum.sml\";\n\
         H \"HOLFS_dtype.sml\";\n\
         H \"HFS_NameMunge.sig\"; HP \"HFS_NameMunge.sml\";\n\
         H \"HOLFileSys.sig\"; H \"HOLFileSys.sml\";\n\
         PMu \"poly/MD5.sig\"; PMu \"poly/MD5.sml\";\n\
         PMu \"poly/Susp.sig\"; PMu \"poly/Susp.sml\";\n\
         PMu \"poly/Thread_Attributes.sml\"; PMu \"poly/Thread_Data.sml\";\n\
         PMu \"poly/Unsynchronized.sml\"; PMu \"poly/ConcIsaLib.sml\";\n\
         PMu \"poly/Multithreading.sml\"; PMu \"poly/Synchronized.sml\";\n\
         PMu \"HOLquotation.sig\"; PMu \"HOLquotation.sml\";\n\
         PMu \"poly/MLSYSPortable.sml\";\n\
         PMu \"Portable.sig\"; PMu \"Portable.sml\";\n\
         PMu \"Redblackmap.sig\"; PMu \"Redblackmap.sml\";\n\
         PMu \"Redblackset.sig\"; PMu \"Redblackset.sml\";\n\
         PMu \"HOLset.sig\"; PMu \"HOLset.sml\";\n\
         PMu \"Table.sml\"; PMu \"Symtab.sml\"; PMu \"Inttab.sml\";\n\
         PMu \"locn.sig\"; PMu \"locn.sml\";\n\
         PMu \"poly/CoreReplVARS.sml\";\n\
         PMu \"poly/concurrent/Sref.sig\"; PMu \"poly/concurrent/Sref.sml\";\n\
         PKu \"Feedback_dtype.sml\";\n\
         PKu \"Globals.sig\"; PKu \"Globals.sml\";\n\
         PKu \"Feedback.sig\"; PKu \"Feedback.sml\";\n\
         PKu \"Lib.sig\"; PKu \"Lib.sml\";\n\
         PKu \"Count.sig\"; PKu \"Count.sml\";\n\
         PKu \"Nonce.sig\"; PKu \"Nonce.sml\";\n\
         PKu \"Dep.sig\"; PKu \"Dep.sml\";\n\
         PKu \"Tag.sig\"; PKu \"Tag.sml\";\n\
         TPu \"Binarymap.sig\"; TPu \"Binarymap.sml\";\n\
         TPu \"Listsort.sig\"; TPu \"Listsort.sml\";\n\
         PKu \"KernelSig.sig\"; PKu \"KernelSig.sml\";\n\
         PKu \"FinalType-sig.sml\"; PKu \"FinalTerm-sig.sml\";\n\
         PKu \"FinalThm-sig.sml\"; PKu \"FinalNet-sig.sml\";\n\
         PKu \"FinalTag-sig.sml\";\n\
         TPu \"Binaryset.sig\"; TPu \"Binaryset.sml\";\n\
         PMu \"UnicodeChars.sig\"; PMu \"UnicodeChars.sml\";\n\
         PKu \"Lexis.sig\"; PKu \"Lexis.sml\";\n\
         K0u \"Subst.sig\"; K0u \"Subst.sml\";\n\
         K0u \"KernelTypes.sml\";\n\
         K0u \"Type.sig\"; K0u \"Type.sml\";\n\
         K0u \"Term.sig\"; K0u \"Term.sml\";\n\
         Tu \"Compute.sig\"; Tu \"Compute.sml\";\n\
         Tu \"std-thmsig.ML\"; Tu \"std-thm.ML\";\n\
         (* Five primitive inference rules: REFL, ASSUME, DISCH, MP, TRANS. *)\n\
         val bool_ty = Type.mk_type(\"bool\", []);\n\
         val p = Term.mk_var(\"p\", bool_ty);\n\
         val q = Term.mk_var(\"q\", bool_ty);\n\
         val r = Term.mk_var(\"r\", bool_ty);\n\
         val th_refl = Thm.REFL p;\n\
         val (l1, r1, _) = Term.dest_eq_ty (Thm.concl th_refl);\n\
         val () = print (\"REFL: hyps=\" ^ Int.toString (List.length (Thm.hyp th_refl)) ^ \" lhs=\" ^ Bool.toString (Term.aconv l1 p) ^ \" rhs=\" ^ Bool.toString (Term.aconv r1 p) ^ \"\\n\");\n\
         val th_assume = Thm.ASSUME p;\n\
         val () = print (\"ASSUME: hyps=\" ^ Int.toString (List.length (Thm.hyp th_assume)) ^ \" concl=p:\" ^ Bool.toString (Term.aconv (Thm.concl th_assume) p) ^ \"\\n\");\n\
         val th_imp_self = Thm.DISCH p th_assume;\n\
         val (Rator0, Rand0) = Term.dest_comb (Thm.concl th_imp_self);\n\
         val (_, lhs0) = Term.dest_comb Rator0;\n\
         val () = print (\"DISCH: hyps=\" ^ Int.toString (List.length (Thm.hyp th_imp_self)) ^ \" lhs=\" ^ Bool.toString (Term.aconv lhs0 p) ^ \" rhs=\" ^ Bool.toString (Term.aconv Rand0 p) ^ \"\\n\");\n\
         (* MP: from `p ==> q` and `p`, derive `q`. *)\n\
         val pq = Term.prim_mk_imp p q;\n\
         val th_pq = Thm.ASSUME pq;        (* p==>q |- p==>q *)\n\
         val th_p  = Thm.ASSUME p;         (* p |- p *)\n\
         val th_mp = Thm.MP th_pq th_p;    (* p, p==>q |- q *)\n\
         val () = print (\"MP: hyps=\" ^ Int.toString (List.length (Thm.hyp th_mp)) ^ \" concl=q:\" ^ Bool.toString (Term.aconv (Thm.concl th_mp) q) ^ \"\\n\");\n\
         (* TRANS: from `p = q` and `q = r`, derive `p = r`. *)\n\
         val pq_eq = Term.prim_mk_eq bool_ty p q;\n\
         val qr_eq = Term.prim_mk_eq bool_ty q r;\n\
         val th_pq_eq = Thm.ASSUME pq_eq;\n\
         val th_qr_eq = Thm.ASSUME qr_eq;\n\
         val th_pr_eq = Thm.TRANS th_pq_eq th_qr_eq;\n\
         val (l2, r2, _) = Term.dest_eq_ty (Thm.concl th_pr_eq);\n\
         val () = print (\"TRANS: hyps=\" ^ Int.toString (List.length (Thm.hyp th_pr_eq)) ^ \" lhs=p:\" ^ Bool.toString (Term.aconv l2 p) ^ \" rhs=r:\" ^ Bool.toString (Term.aconv r2 r) ^ \"\\n\");\n\
         print \"HOL_PROOF_OK\\n\";\n",
    );
    let Some((out, _)) = run_through_checkpoint(&driver, 100_000_000_000) else {
        panic!("subprocess failure");
    };
    assert_compile_clean(&out, "HOL_PROOF_OK");
    // REFL p produces |- p = p with no hypotheses.
    assert!(out.contains("REFL: hyps=0 lhs=true rhs=true"),
        "REFL inference incorrect. Output:\n{out}");
    // ASSUME p produces p |- p (one hypothesis = p, concl = p).
    assert!(out.contains("ASSUME: hyps=1 concl=p:true"),
        "ASSUME inference incorrect. Output:\n{out}");
    // DISCH p (ASSUME p) produces |- p ==> p (no hypotheses, concl is p ==> p).
    assert!(out.contains("DISCH: hyps=0 lhs=true rhs=true"),
        "DISCH inference incorrect. Output:\n{out}");
    // MP th_pq th_p produces (p, p==>q) |- q with two hypotheses.
    assert!(out.contains("MP: hyps=2 concl=q:true"),
        "MP inference incorrect. Output:\n{out}");
    // TRANS th_pq_eq th_qr_eq produces (p=q, q=r) |- p=r with two hypotheses.
    assert!(out.contains("TRANS: hyps=2 lhs=p:true rhs=r:true"),
        "TRANS inference incorrect. Output:\n{out}");
}

/// Beyond compilation: actually USE the HOL4 kernel by constructing
/// the type `bool` and a `Var` term, then printing them. This proves
/// our interpreter doesn't just compile the source — it runs the
/// compiled code correctly.
#[test]
fn recon_via_checkpoint_executes_kernel() {
    let Some(_) = checkpoint_path() else {
        eprintln!("SKIP: /tmp/basis_loaded not present");
        return;
    };
    if hol4_dir().is_none() {
        eprintln!("SKIP: vendor/hol4 not present");
        return;
    }
    let hol = hol4_dir().unwrap();
    let pm = format!("{}/src/portableML", hol.display());
    let pk = format!("{}/src/prekernel", hol.display());
    let k0 = format!("{}/src/0", hol.display());
    let tp = format!("{}/tools-poly/poly", hol.display());
    let hfs = format!("{}/tools/Holmake/hfs", hol.display());
    let hpoly = format!("{}/tools/Holmake/poly", hol.display());
    let driver = format!(
        "fun PMu f = PolyML.use (\"{pm}/\" ^ f);\n\
         fun PKu f = PolyML.use (\"{pk}/\" ^ f);\n\
         fun K0u f = PolyML.use (\"{k0}/\" ^ f);\n\
         fun TPu f = PolyML.use (\"{tp}/\" ^ f);\n\
         fun H f = PolyML.use (\"{hfs}/\" ^ f);\n\
         fun HP f = PolyML.use (\"{hpoly}/\" ^ f);\n\
         structure Systeml = struct\n\
           val HOLDIR = \"\"; val release = \"polyml-rs\"; val version = 0;\n\
         end;\n\
         structure Path = OS.Path;\n\
         PMu \"quotation_dtype.sml\"; PMu \"poly/PrettyImpl.sml\";\n\
         PMu \"poly/Exn.sig\"; PMu \"poly/Exn.sml\";\n\
         PMu \"Uref.sig\"; PMu \"Uref.sml\";\n\
         PMu \"UTF8.sig\"; PMu \"UTF8.sml\";\n\
         PMu \"HOLPP.sig\"; PMu \"HOLPP.sml\";\n\
         PMu \"OldPP.sig\"; PMu \"OldPP.sml\";\n\
         PMu \"poly/Arbnumcore.sig\"; PMu \"poly/Arbnumcore.sml\";\n\
         PMu \"Arbnum.sig\"; PMu \"Arbnum.sml\";\n\
         H \"HOLFS_dtype.sml\";\n\
         H \"HFS_NameMunge.sig\"; HP \"HFS_NameMunge.sml\";\n\
         H \"HOLFileSys.sig\"; H \"HOLFileSys.sml\";\n\
         PMu \"poly/MD5.sig\"; PMu \"poly/MD5.sml\";\n\
         PMu \"poly/Susp.sig\"; PMu \"poly/Susp.sml\";\n\
         PMu \"poly/Thread_Attributes.sml\"; PMu \"poly/Thread_Data.sml\";\n\
         PMu \"poly/Unsynchronized.sml\"; PMu \"poly/ConcIsaLib.sml\";\n\
         PMu \"poly/Multithreading.sml\"; PMu \"poly/Synchronized.sml\";\n\
         PMu \"HOLquotation.sig\"; PMu \"HOLquotation.sml\";\n\
         PMu \"poly/MLSYSPortable.sml\";\n\
         PMu \"Portable.sig\"; PMu \"Portable.sml\";\n\
         PMu \"Redblackmap.sig\"; PMu \"Redblackmap.sml\";\n\
         PMu \"Redblackset.sig\"; PMu \"Redblackset.sml\";\n\
         PMu \"HOLset.sig\"; PMu \"HOLset.sml\";\n\
         PMu \"Table.sml\"; PMu \"Symtab.sml\"; PMu \"Inttab.sml\";\n\
         PMu \"locn.sig\"; PMu \"locn.sml\";\n\
         PMu \"poly/CoreReplVARS.sml\";\n\
         PMu \"poly/concurrent/Sref.sig\"; PMu \"poly/concurrent/Sref.sml\";\n\
         PKu \"Feedback_dtype.sml\";\n\
         PKu \"Globals.sig\"; PKu \"Globals.sml\";\n\
         PKu \"Feedback.sig\"; PKu \"Feedback.sml\";\n\
         PKu \"Lib.sig\"; PKu \"Lib.sml\";\n\
         PKu \"Count.sig\"; PKu \"Count.sml\";\n\
         PKu \"Nonce.sig\"; PKu \"Nonce.sml\";\n\
         PKu \"Dep.sig\"; PKu \"Dep.sml\";\n\
         PKu \"Tag.sig\"; PKu \"Tag.sml\";\n\
         TPu \"Binarymap.sig\"; TPu \"Binarymap.sml\";\n\
         PKu \"KernelSig.sig\"; PKu \"KernelSig.sml\";\n\
         PKu \"FinalType-sig.sml\"; PKu \"FinalTerm-sig.sml\";\n\
         PKu \"FinalThm-sig.sml\"; PKu \"FinalNet-sig.sml\";\n\
         PKu \"FinalTag-sig.sml\";\n\
         TPu \"Binaryset.sig\"; TPu \"Binaryset.sml\";\n\
         PMu \"UnicodeChars.sig\"; PMu \"UnicodeChars.sml\";\n\
         PKu \"Lexis.sig\"; PKu \"Lexis.sml\";\n\
         K0u \"Subst.sig\"; K0u \"Subst.sml\";\n\
         K0u \"KernelTypes.sml\";\n\
         K0u \"Type.sig\"; K0u \"Type.sml\";\n\
         K0u \"Term.sig\"; K0u \"Term.sml\";\n\
         (* Now actually exercise the kernel. *)\n\
         val bool_ty = Type.mk_type(\"bool\", []);\n\
         val () = print (\"bool_ty.is_type = \" ^ Bool.toString (Type.is_type bool_ty) ^ \"\\n\");\n\
         val p_var = Term.mk_var(\"p\", bool_ty);\n\
         val () = print (\"p_var.is_var = \" ^ Bool.toString (Term.is_var p_var) ^ \"\\n\");\n\
         val (name, _) = Term.dest_var p_var;\n\
         val () = print (\"p_var name = \" ^ name ^ \"\\n\");\n\
         print \"HOL_EXEC_OK\\n\";\n",
    );
    let Some((out, _)) = run_through_checkpoint(&driver, 100_000_000_000) else {
        panic!("subprocess failure");
    };
    assert_compile_clean(&out, "HOL_EXEC_OK");
    assert!(out.contains("bool_ty.is_type = true"), "kernel didn't run. Output:\n{out}");
    assert!(out.contains("p_var.is_var = true"), "kernel didn't run. Output:\n{out}");
    assert!(out.contains("p_var name = p"), "kernel didn't run. Output:\n{out}");
}

#[test]
#[ignore = "slow: loads HOL4 source through full basis (~3-5 min)"]
fn recon_compiles_simple_buffer() {
    if skip_if_missing().is_none() {
        eprintln!("SKIP: vendor/polyml or vendor/hol4 not present");
        return;
    }
    let hol = hol4_dir().unwrap();
    let driver = format!(
        "val () = Bootstrap.use \"basis/build.sml\";\n\
         val () = PolyML.use \"{path}/tools/util/SimpleBuffer.sig\";\n\
         val () = PolyML.use \"{path}/tools/util/SimpleBuffer.sml\";\n\
         print \"HOL_OK\\n\";\n",
        path = hol.display(),
    );
    let (out, code) = run_with_driver(&driver, 10_000_000_000)
        .expect("run");
    assert_eq!(code, 0, "exit non-zero. Output:\n{out}");
    assert!(
        out.contains("HOL_OK"),
        "did not print HOL_OK. Output:\n{out}"
    );
    assert!(
        !out.contains("Error-"),
        "compiler error during HOL4 compile. Output:\n{out}"
    );
}

#[test]
#[ignore = "slow: loads HOL4 source through full basis (~5-7 min)"]
fn recon_compiles_portable() {
    if skip_if_missing().is_none() {
        eprintln!("SKIP: missing vendor dirs");
        return;
    }
    let hol = hol4_dir().unwrap();
    let driver = format!(
        "val () = Bootstrap.use \"basis/build.sml\";\n\
         val () = PolyML.use \"{path}/src/portableML/Portable.sig\";\n\
         val () = PolyML.use \"{path}/src/portableML/Portable.sml\";\n\
         print \"HOL_OK\\n\";\n",
        path = hol.display(),
    );
    let (out, code) = run_with_driver(&driver, 20_000_000_000)
        .expect("run");
    // Note: this may fail today — that's the point of recon.
    // We capture the output for diagnosis even on failure.
    if code != 0 || !out.contains("HOL_OK") {
        panic!(
            "Portable.sml didn't compile (code={code}).\n\
             First few errors:\n{}",
            out.lines()
                .filter(|l| l.contains("Error-") || l.contains("not been declared")
                    || l.contains("Halted") || l.contains("Result:"))
                .take(10)
                .collect::<Vec<_>>()
                .join("\n")
        );
    }
}
