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
    let mut cmd = Command::new(poly_bin());
    cmd.arg("run").arg("--max-steps").arg(max_steps.to_string());
    if std::env::var("HOL4_TEST_JIT").is_ok() {
        cmd.arg("--jit");
    }
    let mut child = cmd
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
         (* Primitive inference rules of HOL: REFL, ASSUME, DISCH, MP,\n\
            TRANS, SYM, EQ_MP, AP_TERM, BETA_CONV. *)\n\
         val bool_ty = Type.mk_type(\"bool\", []);\n\
         val alpha = Type.mk_vartype \"'a\";\n\
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
         val th_pq = Thm.ASSUME pq;\n\
         val th_p  = Thm.ASSUME p;\n\
         val th_mp = Thm.MP th_pq th_p;\n\
         val () = print (\"MP: hyps=\" ^ Int.toString (List.length (Thm.hyp th_mp)) ^ \" concl=q:\" ^ Bool.toString (Term.aconv (Thm.concl th_mp) q) ^ \"\\n\");\n\
         (* TRANS: from `p = q` and `q = r`, derive `p = r`. *)\n\
         val pq_eq = Term.prim_mk_eq bool_ty p q;\n\
         val qr_eq = Term.prim_mk_eq bool_ty q r;\n\
         val th_pq_eq = Thm.ASSUME pq_eq;\n\
         val th_qr_eq = Thm.ASSUME qr_eq;\n\
         val th_pr_eq = Thm.TRANS th_pq_eq th_qr_eq;\n\
         val (l2, r2, _) = Term.dest_eq_ty (Thm.concl th_pr_eq);\n\
         val () = print (\"TRANS: hyps=\" ^ Int.toString (List.length (Thm.hyp th_pr_eq)) ^ \" lhs=p:\" ^ Bool.toString (Term.aconv l2 p) ^ \" rhs=r:\" ^ Bool.toString (Term.aconv r2 r) ^ \"\\n\");\n\
         (* SYM: from `p = q` derive `q = p`. *)\n\
         val th_sym = Thm.SYM th_pq_eq;\n\
         val (l3, r3, _) = Term.dest_eq_ty (Thm.concl th_sym);\n\
         val () = print (\"SYM: hyps=\" ^ Int.toString (List.length (Thm.hyp th_sym)) ^ \" lhs=q:\" ^ Bool.toString (Term.aconv l3 q) ^ \" rhs=p:\" ^ Bool.toString (Term.aconv r3 p) ^ \"\\n\");\n\
         (* EQ_MP: from `p = q` and `p`, derive `q`. *)\n\
         val th_eqmp = Thm.EQ_MP th_pq_eq th_p;\n\
         val () = print (\"EQ_MP: hyps=\" ^ Int.toString (List.length (Thm.hyp th_eqmp)) ^ \" concl=q:\" ^ Bool.toString (Term.aconv (Thm.concl th_eqmp) q) ^ \"\\n\");\n\
         (* AP_TERM: from `p = q` and term `f : bool->bool`, derive `f p = f q`. *)\n\
         val bb_ty = Type.--> (bool_ty, bool_ty);\n\
         val f = Term.mk_var(\"f\", bb_ty);\n\
         val th_ap = Thm.AP_TERM f th_pq_eq;\n\
         val (l4, r4, _) = Term.dest_eq_ty (Thm.concl th_ap);\n\
         val () = print (\"AP_TERM: hyps=\" ^ Int.toString (List.length (Thm.hyp th_ap)) ^ \" lhs=f(p):\" ^ Bool.toString (Term.aconv l4 (Term.mk_comb(f, p))) ^ \"\\n\");\n\
         (* BETA_CONV: `(\\x. x) p = p`. The lambda is over a:'a, applied to p. *)\n\
         val x_var = Term.mk_var(\"x\", bool_ty);\n\
         val lam_id = Term.mk_abs(x_var, x_var);   (* \\x. x *)\n\
         val app = Term.mk_comb(lam_id, p);         (* (\\x. x) p *)\n\
         val th_beta = Thm.BETA_CONV app;\n\
         val (l5, r5, _) = Term.dest_eq_ty (Thm.concl th_beta);\n\
         val () = print (\"BETA_CONV: hyps=\" ^ Int.toString (List.length (Thm.hyp th_beta)) ^ \" lhs=(\\\\x.x)p:\" ^ Bool.toString (Term.aconv l5 app) ^ \" rhs=p:\" ^ Bool.toString (Term.aconv r5 p) ^ \"\\n\");\n\
         (* ABS: from `|- M = N` derive `|- (\\x. M) = (\\x. N)`.\n\
            Use REFL p as the equality; abstract x_var. *)\n\
         val th_abs = Thm.ABS x_var th_refl;\n\
         val (l_abs, r_abs, _) = Term.dest_eq_ty (Thm.concl th_abs);\n\
         val () = print (\"ABS: hyps=\" ^ Int.toString (List.length (Thm.hyp th_abs)) ^ \" lhs_is_abs:\" ^ Bool.toString (Term.is_abs l_abs) ^ \" rhs_is_abs:\" ^ Bool.toString (Term.is_abs r_abs) ^ \"\\n\");\n\
         (* MK_COMB: from `|- f = g` and `|- x = y`, derive `|- f x = g y`.\n\
            Build `|- f = f` via REFL(f) and `|- p = q` from ASSUME(p=q). *)\n\
         val th_refl_f = Thm.REFL f;\n\
         val th_mkcomb = Thm.MK_COMB (th_refl_f, th_pq_eq);\n\
         val (l_mk, r_mk, _) = Term.dest_eq_ty (Thm.concl th_mkcomb);\n\
         val () = print (\"MK_COMB: hyps=\" ^ Int.toString (List.length (Thm.hyp th_mkcomb)) ^ \" lhs=fp:\" ^ Bool.toString (Term.aconv l_mk (Term.mk_comb(f, p))) ^ \" rhs=fq:\" ^ Bool.toString (Term.aconv r_mk (Term.mk_comb(f, q))) ^ \"\\n\");\n\
         (* INST_TYPE: REFL of polymorphic x:'a; instantiate 'a:=bool.\n\
            The resulting theorem has both sides re-typed to bool. *)\n\
         val x_alpha = Term.mk_var(\"x\", alpha);\n\
         val th_refl_alpha = Thm.REFL x_alpha;\n\
         val th_inst = Thm.INST_TYPE [{{redex=alpha, residue=bool_ty}}] th_refl_alpha;\n\
         val (l6, r6, ty6) = Term.dest_eq_ty (Thm.concl th_inst);\n\
         val () = print (\"INST_TYPE: hyps=\" ^ Int.toString (List.length (Thm.hyp th_inst)) ^ \" ty=bool:\" ^ Bool.toString (ty6 = bool_ty) ^ \" lhs_eq_rhs:\" ^ Bool.toString (Term.aconv l6 r6) ^ \"\\n\");\n\
         (* GEN/SPEC would require register_forall (loading boolTheory's\n\
            forall axiom); that's a deeper dependency. Stop at the\n\
            primitives that don't need boolean theory wiring. *)\n\
         (* A composed proof: prove `(p ==> q), p |- q` using MP, then\n\
            wrap with DISCH twice to get `|- p ==> (p==>q) ==> q`. *)\n\
         val th_step1 = Thm.MP (Thm.ASSUME pq) (Thm.ASSUME p);\n\
         val th_step2 = Thm.DISCH pq th_step1;\n\
         val th_step3 = Thm.DISCH p th_step2;\n\
         val () = print (\"COMPOSED: hyps=\" ^ Int.toString (List.length (Thm.hyp th_step3)) ^ \"\\n\");\n\
         (* Real derived theorem: transitivity of implication.\n\
            From p==>q and q==>r derive p==>r. Discharge all three. *)\n\
         val qr = Term.prim_mk_imp q r;\n\
         val h_pq  = Thm.ASSUME pq;        (* p==>q |- p==>q *)\n\
         val h_qr  = Thm.ASSUME qr;        (* q==>r |- q==>r *)\n\
         val h_p   = Thm.ASSUME p;         (* p |- p *)\n\
         val mp1   = Thm.MP h_pq h_p;      (* p, p==>q |- q *)\n\
         val mp2   = Thm.MP h_qr mp1;      (* p, p==>q, q==>r |- r *)\n\
         val d1    = Thm.DISCH p mp2;      (* p==>q, q==>r |- p==>r *)\n\
         val d2    = Thm.DISCH qr d1;      (* p==>q |- (q==>r)==>(p==>r) *)\n\
         val d3    = Thm.DISCH pq d2;      (* |- (p==>q)==>(q==>r)==>(p==>r) *)\n\
         val () = print (\"TRANS_IMP_HYPS: \" ^ Int.toString (List.length (Thm.hyp d3)) ^ \"\\n\");\n\
         (* The conclusion should be `(p==>q) ==> (q==>r) ==> (p==>r)`. *)\n\
         val c = Thm.concl d3;\n\
         val (op1, a1) = Term.dest_comb c;       (* op1=(==> pq, rest); a1 = (q==>r)==>(p==>r) *)\n\
         val (_, lhs_outer) = Term.dest_comb op1;\n\
         val () = print (\"TRANS_IMP_LHS_OUTER: \" ^ Bool.toString (Term.aconv lhs_outer pq) ^ \"\\n\");\n\
         val (op2, a2) = Term.dest_comb a1;\n\
         val (_, lhs_mid) = Term.dest_comb op2;\n\
         val () = print (\"TRANS_IMP_LHS_MID: \" ^ Bool.toString (Term.aconv lhs_mid qr) ^ \"\\n\");\n\
         val (op3, rhs_inner) = Term.dest_comb a2;\n\
         val (_, lhs_inner) = Term.dest_comb op3;\n\
         val () = print (\"TRANS_IMP_INNER: \" ^ Bool.toString (Term.aconv lhs_inner p) ^ \" \" ^ Bool.toString (Term.aconv rhs_inner r) ^ \"\\n\");\n\
         (* Leibniz substitution: from |- p = q and |- P p, derive |- P q.\n\
            Proof: AP_TERM P (premise: p=q) → |- P p = P q, then EQ_MP. *)\n\
         val Pp = Term.mk_comb(f, p);                  (* P p, where P=f *)\n\
         val th_Pp = Thm.ASSUME Pp;                    (* P p |- P p *)\n\
         val th_Peq = Thm.AP_TERM f th_pq_eq;          (* p=q |- P p = P q *)\n\
         val th_Pq = Thm.EQ_MP th_Peq th_Pp;           (* p=q, P p |- P q *)\n\
         val Pq = Term.mk_comb(f, q);\n\
         val () = print (\"LEIBNIZ: hyps=\" ^ Int.toString (List.length (Thm.hyp th_Pq)) ^ \" concl=fq:\" ^ Bool.toString (Term.aconv (Thm.concl th_Pq) Pq) ^ \"\\n\");\n\
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
    // SYM of (p=q) produces (p=q) |- q=p.
    assert!(out.contains("SYM: hyps=1 lhs=q:true rhs=p:true"),
        "SYM inference incorrect. Output:\n{out}");
    // EQ_MP th_pq_eq th_p produces (p=q, p) |- q with two hypotheses.
    assert!(out.contains("EQ_MP: hyps=2 concl=q:true"),
        "EQ_MP inference incorrect. Output:\n{out}");
    // AP_TERM f th_pq_eq produces (p=q) |- f p = f q.
    assert!(out.contains("AP_TERM: hyps=1 lhs=f(p):true"),
        "AP_TERM inference incorrect. Output:\n{out}");
    // BETA_CONV of `(\x. x) p` produces |- (\x.x) p = p with no hypotheses.
    assert!(out.contains("BETA_CONV: hyps=0 lhs=(\\x.x)p:true rhs=p:true"),
        "BETA_CONV inference incorrect. Output:\n{out}");
    // ABS x_var on REFL(p) → |- (\x. p) = (\x. p), both sides are abstractions.
    assert!(out.contains("ABS: hyps=0 lhs_is_abs:true rhs_is_abs:true"),
        "ABS inference incorrect. Output:\n{out}");
    // MK_COMB(REFL(f), ASSUME(p=q)) → (p=q) |- f p = f q.
    assert!(out.contains("MK_COMB: hyps=1 lhs=fp:true rhs=fq:true"),
        "MK_COMB inference incorrect. Output:\n{out}");
    // INST_TYPE 'a := bool on REFL(x:'a) → |- (x:bool) = (x:bool).
    assert!(out.contains("INST_TYPE: hyps=0 ty=bool:true lhs_eq_rhs:true"),
        "INST_TYPE inference incorrect. Output:\n{out}");
    // Composed: discharging both hyps gives a closed theorem.
    assert!(out.contains("COMPOSED: hyps=0"),
        "Composed proof incorrect. Output:\n{out}");
    // Transitivity of implication, derived from primitives:
    // |- (p==>q) ==> (q==>r) ==> (p==>r), no hypotheses.
    assert!(out.contains("TRANS_IMP_HYPS: 0"),
        "Transitivity-of-impl hyps wrong. Output:\n{out}");
    assert!(out.contains("TRANS_IMP_LHS_OUTER: true"),
        "Transitivity-of-impl outer LHS wrong. Output:\n{out}");
    assert!(out.contains("TRANS_IMP_LHS_MID: true"),
        "Transitivity-of-impl middle LHS wrong. Output:\n{out}");
    assert!(out.contains("TRANS_IMP_INNER: true true"),
        "Transitivity-of-impl inner LHS/RHS wrong. Output:\n{out}");
    // Leibniz substitution: (p=q, P p) |- P q. Two hypotheses.
    assert!(out.contains("LEIBNIZ: hyps=2 concl=fq:true"),
        "Leibniz substitution wrong. Output:\n{out}");
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

/// SML prelude that loads enough of HOL4 to expose the kernel
/// `Thm`, `Term`, `Type`, `Subst`, `KernelSig` modules. Used by
/// tests that exercise theorem proving via the kernel.
///
/// Mirrors the inline prelude in
/// `recon_via_checkpoint_proves_implication_self` — extracted here
/// so additional kernel-using tests don't have to duplicate it.
fn hol4_kernel_prelude(hol: &std::path::Path) -> String {
    let pm = format!("{}/src/portableML", hol.display());
    let pk = format!("{}/src/prekernel", hol.display());
    let k0 = format!("{}/src/0", hol.display());
    let tp = format!("{}/tools-poly/poly", hol.display());
    let hfs = format!("{}/tools/Holmake/hfs", hol.display());
    let hpoly = format!("{}/tools/Holmake/poly", hol.display());
    let thm = format!("{}/src/thm", hol.display());
    format!(
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
         Tu \"std-thmsig.ML\"; Tu \"std-thm.ML\";\n",
    )
}

/// Build a longer equational chain via a user-defined `EQ_TRANS_LIST`
/// tactic, then verify the resulting theorem structure.
///
/// Concretely:
/// 1. Define `EQ_TRANS_LIST : thm list -> thm` that folds `Thm.TRANS`
///    over a list of equality theorems.
/// 2. Build the assumptions `a=b`, `b=c`, `c=d`, `d=e` over bool vars.
/// 3. Apply the tactic to get `[a=b, b=c, c=d, d=e] |- a=e`.
/// 4. Sanity-check: the result's LHS is `a`, RHS is `e`, and it has
///    exactly 4 hypotheses (one per ASSUMEd link).
///
/// This is a "user code on top of the kernel" demo — the SML test
/// itself extends the kernel with a higher-order tactic and uses
/// it to prove a theorem of arbitrary chain length. Same pattern
/// as HOL4's `tactics/` build on top of `kernel/`.
#[test]
#[ignore = "slow: needs /tmp/basis_loaded checkpoint (~3-5 min)"]
fn recon_via_checkpoint_proves_4link_eq_chain() {
    let Some(_) = checkpoint_path() else {
        eprintln!("SKIP: /tmp/basis_loaded not present");
        return;
    };
    if hol4_dir().is_none() {
        eprintln!("SKIP: vendor/hol4 not present");
        return;
    }
    let hol = hol4_dir().unwrap();
    let prelude = hol4_kernel_prelude(&hol);
    let test_block = "\
val bool_ty = Type.mk_type(\"bool\", []);\n\
val a = Term.mk_var(\"a\", bool_ty);\n\
val b = Term.mk_var(\"b\", bool_ty);\n\
val c = Term.mk_var(\"c\", bool_ty);\n\
val d = Term.mk_var(\"d\", bool_ty);\n\
val e = Term.mk_var(\"e\", bool_ty);\n\
val ab = Term.prim_mk_eq bool_ty a b;\n\
val bc = Term.prim_mk_eq bool_ty b c;\n\
val cd = Term.prim_mk_eq bool_ty c d;\n\
val de = Term.prim_mk_eq bool_ty d e;\n\
(* User-defined tactic: fold Thm.TRANS over a list of equalities.\n\
   Empty list raises; singleton is identity; chain is left-folded. *)\n\
fun EQ_TRANS_LIST [] = raise Fail \"EQ_TRANS_LIST: empty\"\n\
  | EQ_TRANS_LIST [th] = th\n\
  | EQ_TRANS_LIST (th1 :: th2 :: rest) =\n\
      EQ_TRANS_LIST (Thm.TRANS th1 th2 :: rest);\n\
val links = [Thm.ASSUME ab, Thm.ASSUME bc, Thm.ASSUME cd, Thm.ASSUME de];\n\
val chain = EQ_TRANS_LIST links;\n\
val (lhs_c, rhs_c, _) = Term.dest_eq_ty (Thm.concl chain);\n\
val n_hyps = List.length (Thm.hyp chain);\n\
val () = print (\"CHAIN4_LHS_A: \" ^ Bool.toString (Term.aconv lhs_c a) ^ \"\\n\");\n\
val () = print (\"CHAIN4_RHS_E: \" ^ Bool.toString (Term.aconv rhs_c e) ^ \"\\n\");\n\
val () = print (\"CHAIN4_HYPS: \" ^ Int.toString n_hyps ^ \"\\n\");\n\
(* Now apply SYM to the chain — should give |- e = a with same hyps. *)\n\
val chain_sym = Thm.SYM chain;\n\
val (lhs_s, rhs_s, _) = Term.dest_eq_ty (Thm.concl chain_sym);\n\
val () = print (\"CHAIN4_SYM_LHS_E: \" ^ Bool.toString (Term.aconv lhs_s e) ^ \"\\n\");\n\
val () = print (\"CHAIN4_SYM_RHS_A: \" ^ Bool.toString (Term.aconv rhs_s a) ^ \"\\n\");\n\
(* Compose: chain THEN chain_sym should give |- a = a, but TRANS-ing\n\
   them goes through (a=e) THEN (e=a), yielding (a=a) with 4 hyps. *)\n\
val round_trip = Thm.TRANS chain chain_sym;\n\
val (lhs_rt, rhs_rt, _) = Term.dest_eq_ty (Thm.concl round_trip);\n\
val () = print (\"ROUND_TRIP_A: \" ^ Bool.toString (Term.aconv lhs_rt a)\n\
              ^ \" \" ^ Bool.toString (Term.aconv rhs_rt a)\n\
              ^ \" hyps=\" ^ Int.toString (List.length (Thm.hyp round_trip)) ^ \"\\n\");\n\
print \"CHAIN_PROOF_OK\\n\";\n";
    let driver = format!("{prelude}{test_block}");
    let Some((out, _)) = run_through_checkpoint(&driver, 100_000_000_000) else {
        panic!("subprocess failure");
    };
    assert_compile_clean(&out, "CHAIN_PROOF_OK");
    assert!(
        out.contains("CHAIN4_LHS_A: true"),
        "chain LHS should be `a`. Output:\n{out}"
    );
    assert!(
        out.contains("CHAIN4_RHS_E: true"),
        "chain RHS should be `e`. Output:\n{out}"
    );
    assert!(
        out.contains("CHAIN4_HYPS: 4"),
        "chain should have 4 hypotheses (one per ASSUMEd link). Output:\n{out}"
    );
    assert!(
        out.contains("CHAIN4_SYM_LHS_E: true"),
        "SYM(chain) LHS should be `e`. Output:\n{out}"
    );
    assert!(
        out.contains("CHAIN4_SYM_RHS_A: true"),
        "SYM(chain) RHS should be `a`. Output:\n{out}"
    );
    assert!(
        out.contains("ROUND_TRIP_A: true true hyps=4"),
        "round trip should give |- a=a from same 4 hyps. Output:\n{out}"
    );
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
