//! Isabelle's LCF THEOREM kernel (`Pure/thm.ML`) runs on the polyml-rs interpreter.
//!
//! Beyond the term/type kernel (`isabelle_kernel.rs`), the full LCF theorem kernel
//! `thm.ML` loads on the arbitrary-int image and we derive real Isabelle theorems
//! with its primitive inferences: `reflexive` (⊢ x ≡ x), `symmetric`, `transitive`,
//! `beta_conversion` (⊢ (λu. u) x ≡ x), and — after declaring the `prop` type into
//! the empty proto-Pure theory — the implication laws `⊢ A ⟹ A` (assume +
//! implies_intr), the weakening law `⊢ A ⟹ B ⟹ A` (nested implies_intr), and modus
//! ponens via `implies_elim` (discharging A, B from `⊢ A ⟹ B ⟹ A` to get `A, B ⊢ A`).
//! Each is a checked `thm` from Isabelle's actual kernel — the Isabelle analogue of
//! the HOL4 LCF-kernel milestone.
//!
//! The keystone that unlocked this was a runtime fix: `INSTR_GET_THREAD_ID` now
//! returns a STABLE singleton object, so `Thread.self()`/`Thread_Data` work and
//! Isabelle's generic context (the proto-Pure theory installed at context.ML:731)
//! persists — taking the Pure load 124→182/282 and bringing `thm.ML` (#136) in.
//!
//! `#[ignore]` (slow ~1min; needs /tmp/arbint_image from tools/intflip-bootstrap.sh
//! + vendored Isabelle/Pure with patches applied via tools/isabelle-pure-probe.sh):
//! ```sh
//! tools/intflip-bootstrap.sh && tools/isabelle-pure-probe.sh  # builds image + applies patches
//! cargo test --release -p polyml-bin --test isabelle_theorem_kernel -- --ignored --nocapture
//! ```

mod common;
use common::*;

use std::path::PathBuf;

fn arbint_image() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/arbint_image");
    p.exists().then_some(p)
}

fn pure_ml_files(pure: &std::path::Path) -> Vec<String> {
    let mut out = Vec::new();
    for root in ["ROOT0.ML", "ROOT.ML"] {
        let Ok(text) = std::fs::read_to_string(pure.join(root)) else { continue };
        for line in text.lines() {
            if let Some(rest) = line.trim().strip_prefix("ML_file ") {
                if let Some(s) = rest.find('"') {
                    if let Some(e) = rest[s + 1..].find('"') {
                        out.push(rest[s + 1..s + 1 + e].to_string());
                    }
                }
            }
        }
    }
    out
}

#[test]
#[ignore = "needs /tmp/arbint_image + vendor/isabelle (patches applied)"]
fn lcf_kernel_derives_theorems() {
    let (Some(pure), Some(image)) = (isabelle_pure_dir(), arbint_image()) else {
        eprintln!("SKIP: /tmp/arbint_image or vendor/isabelle/src/Pure missing");
        return;
    };
    let files = pure_ml_files(&pure);
    let upto = files.iter().position(|f| f == "thm.ML").map_or(files.len(), |i| i + 1);
    let p = pure.to_str().unwrap();
    let q = |f: &str| format!("\"{p}/{f}\"");
    let ph0 = files[..27.min(files.len())].iter().map(|f| q(f)).collect::<Vec<_>>().join(",");
    let mid = files[27..upto].iter().map(|f| q(f)).collect::<Vec<_>>().join(",");

    let driver = format!(
        r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
fun qP f = (PolyML.use f) handle _ => ();
val () = List.app qP [{ph0}];
fun qM f = (ML_file f) handle _ => ();
val () = List.app qM [{mid}];
pr "=THM= start\n";
val thy = Context.the_global_context ();
val aT = TFree ("a", []);
fun isEq th = case Thm.prop_of th of (Const("Pure.eq",_) $ _) $ _ => true | _ => false;
val cx = Thm.global_cterm_of thy (Free ("x", aT));
val r = Thm.reflexive cx;
val () = pr ("=THM= reflexive " ^ Bool.toString (isEq r andalso null (Thm.hyps_of r)) ^ "\n");
val () = pr ("=THM= symmetric " ^ Bool.toString (isEq (Thm.symmetric r)) ^ "\n");
val () = pr ("=THM= transitive " ^ Bool.toString (isEq (Thm.transitive r r)) ^ "\n");
val cbeta = Thm.global_cterm_of thy ((Abs ("u", aT, Bound 0)) $ Free ("x", aT));
val b = Thm.beta_conversion false cbeta;
val brhs = case Thm.prop_of b of (Const("Pure.eq",_) $ _) $ Free("x",_) => true | _ => false;
val () = pr ("=THM= beta " ^ Bool.toString (isEq b andalso brhs) ^ "\n");
(* Implication kernel: declare the `prop` type (proto-Pure is empty), then derive
   |- A ==> A and the weakening law |- A ==> B ==> A via assume/implies_intr. *)
val pthy = Sign.add_types_global [(Binding.name "prop", 0, NoSyn)] thy;
val propT = Type ("prop", []);
val cA = Thm.global_cterm_of pthy (Free ("A", propT));
val cB = Thm.global_cterm_of pthy (Free ("B", propT));
val thAA = Thm.implies_intr cA (Thm.assume cA);                 (* |- A ==> A *)
val okAA = (case Thm.prop_of thAA of (Const("Pure.imp",_) $ Free("A",_)) $ Free("A",_) => true | _ => false)
           andalso Thm.nprems_of thAA = 1 andalso null (Thm.hyps_of thAA);
val () = pr ("=THM= imp_refl " ^ Bool.toString okAA ^ "\n");
val thK = Thm.implies_intr cA (Thm.implies_intr cB (Thm.assume cA));  (* |- A ==> B ==> A *)
val okK = (case Thm.prop_of thK of
             (Const("Pure.imp",_) $ Free("A",_)) $ ((Const("Pure.imp",_) $ Free("B",_)) $ Free("A",_)) => true
           | _ => false) andalso null (Thm.hyps_of thK);
val () = pr ("=THM= imp_weaken " ^ Bool.toString okK ^ "\n");
(* Modus ponens (implies_elim): from |- A ==> B ==> A discharge the premises A, B
   (as assumptions) to obtain A,B |- A. *)
val mp = Thm.implies_elim (Thm.implies_elim thK (Thm.assume cA)) (Thm.assume cB);
val okMP = (case Thm.prop_of mp of Free ("A", _) => true | _ => false)
           andalso length (Thm.hyps_of mp) = 2;
val () = pr ("=THM= mp " ^ Bool.toString okMP ^ "\n");
pr "=THM= DONE\n";
"#
    );

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        80_000_000_000,
        &[("ML_SYSTEM", "polyml"), ("ML_PLATFORM", "x86_64-linux"), ("ISABELLE_HOME", "/tmp/isa")],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(out.contains("=THM= DONE"), "theorem kernel demo did not finish.\n{}", tail(&out, 40));
    for op in ["reflexive", "symmetric", "transitive", "beta", "imp_refl", "imp_weaken", "mp"] {
        assert!(
            out.contains(&format!("=THM= {op} true")),
            "LCF primitive `{op}` did not produce a checked theorem.\n{}",
            tail(&out, 40)
        );
    }
}
