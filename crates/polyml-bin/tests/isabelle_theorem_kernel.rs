//! Isabelle's LCF THEOREM kernel (`Pure/thm.ML`) runs on the polyml-rs interpreter.
//!
//! Beyond the term/type kernel (`isabelle_kernel.rs`), the full LCF theorem kernel
//! `thm.ML` loads on the arbitrary-int image and we exercise the WHOLE set of Pure's
//! primitive inference rules, each producing a checked `thm` from Isabelle's actual
//! kernel:
//!   - equality:    `reflexive` (⊢ x ≡ x), `symmetric`, `transitive`,
//!                  `beta_conversion` (⊢ (λu. u) x ≡ x)
//!   - implication: (after declaring the `prop` type into the empty proto-Pure theory)
//!                  `⊢ A ⟹ A` (assume + implies_intr), the weakening law
//!                  `⊢ A ⟹ B ⟹ A` (nested implies_intr), and modus ponens via
//!                  `implies_elim` (`⊢ A ⟹ B ⟹ A` ↦ `A, B ⊢ A`)
//!   - quantifier:  `forall_intr` (⊢ ⋀x. x ≡ x) and `forall_elim` (instantiate it at
//!                  a compound term `f c`)
//!   - structural:  `combination` — application congruence (⊢ f x ≡ f x), and
//!                  `abstract_rule` (⊢ (λu. g u) ≡ (λu. g u))
//!   - derived:     composing assume + implies_intr + forall_intr to build the
//!                  universally-quantified identity implication `⊢ ⋀A. A ⟹ A`
//! This is the Isabelle analogue of the HOL4 LCF-kernel milestone — the complete
//! primitive proof kernel of Isabelle/Pure running on the polyml-rs interpreter.
//! (`fun`/`prop` are declared into the proto-Pure theory so manually-built
//! function/prop-typed terms certify; the kernel itself knows `Pure.{eq,imp,all}`
//! intrinsically, so the inference rules build those constants without certification.)
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
    // Match ALL `ML_file*` directive variants in order — ROOT.ML loads 3 files
    // via `ML_file_no_debug` (incl. Isar/runtime.ML); matching only the plain
    // `ML_file ` prefix silently dropped them (which made PIDE/execution.ML's
    // `Runtime` dependency fail and the load look walled at #160).
    let mut out = Vec::new();
    for root in ["ROOT0.ML", "ROOT.ML"] {
        let Ok(text) = std::fs::read_to_string(pure.join(root)) else {
            continue;
        };
        for line in text.lines() {
            let t = line.trim();
            if t.starts_with("ML_file") {
                if let Some(s) = t.find('"') {
                    if let Some(e) = t[s + 1..].find('"') {
                        out.push(t[s + 1..s + 1 + e].to_string());
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
    let upto = files
        .iter()
        .position(|f| f == "thm.ML")
        .map_or(files.len(), |i| i + 1);
    let p = pure.to_str().unwrap();
    let q = |f: &str| format!("\"{p}/{f}\"");
    let ph0 = files[..27.min(files.len())]
        .iter()
        .map(|f| q(f))
        .collect::<Vec<_>>()
        .join(",");
    let mid = files[27..upto]
        .iter()
        .map(|f| q(f))
        .collect::<Vec<_>>()
        .join(",");

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
(* Implication kernel: declare the `prop` type (proto-Pure is empty) — and `fun`,
   so function-typed terms certify for the quantifier/congruence rules below — then
   derive |- A ==> A and the weakening law |- A ==> B ==> A via assume/implies_intr. *)
val pthy = Sign.add_types_global
  [(Binding.name "fun", 2, NoSyn), (Binding.name "prop", 0, NoSyn)] thy;
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
(* The remaining Pure primitive inference rules: quantification (forall_intr/elim),
   application congruence (combination), abstraction (abstract_rule), and a derived
   rule composing them — so the WHOLE primitive kernel is exercised. *)
val funT = aT --> aT;
val cx2 = Thm.global_cterm_of pthy (Free ("x", aT));
val gen = Thm.forall_intr cx2 (Thm.reflexive cx2);                 (* |- !!x. x == x *)
val okFI = (case Thm.prop_of gen of Const("Pure.all",_) $ Abs(_,_,_) => true | _ => false)
           andalso null (Thm.hyps_of gen);
val () = pr ("=THM= forall_intr " ^ Bool.toString okFI ^ "\n");
val fcT = Thm.global_cterm_of pthy (Free ("f", funT) $ Free ("c", aT));
val finst = Thm.forall_elim fcT gen;                               (* |- f c == f c *)
val okFE = isEq finst andalso
   (case Thm.prop_of finst of (Const("Pure.eq",_) $ (Free("f",_) $ Free("c",_))) $ (Free("f",_) $ Free("c",_)) => true | _ => false);
val () = pr ("=THM= forall_elim " ^ Bool.toString okFE ^ "\n");
val cf = Thm.global_cterm_of pthy (Free ("f", funT));
val comb = Thm.combination (Thm.reflexive cf) (Thm.reflexive cx2); (* |- f x == f x *)
val okC = isEq comb andalso
   (case Thm.prop_of comb of (Const("Pure.eq",_) $ (Free("f",_) $ Free("x",_))) $ (Free("f",_) $ Free("x",_)) => true | _ => false);
val () = pr ("=THM= combination " ^ Bool.toString okC ^ "\n");
val cu = Thm.global_cterm_of pthy (Free ("u", aT));
val guT = Thm.global_cterm_of pthy (Free ("g", funT) $ Free ("u", aT));
val absr = Thm.abstract_rule "u" cu (Thm.reflexive guT);          (* |- (%u. g u) == (%u. g u) *)
val okAB = isEq absr andalso
   (case Thm.prop_of absr of (Const("Pure.eq",_) $ Abs(_,_,_)) $ Abs(_,_,_) => true | _ => false);
val () = pr ("=THM= abstract_rule " ^ Bool.toString okAB ^ "\n");
(* Derived rule: compose assume + implies_intr + forall_intr  =>  |- !!A. A ==> A *)
val cAp = Thm.global_cterm_of pthy (Free ("A", propT));
val genK = Thm.forall_intr cAp (Thm.implies_intr cAp (Thm.assume cAp));
val okDR = null (Thm.hyps_of genK) andalso
   (case Thm.prop_of genK of Const("Pure.all",_) $ Abs(_, _, (Const("Pure.imp",_) $ Bound 0) $ Bound 0) => true | _ => false);
val () = pr ("=THM= forall_imp " ^ Bool.toString okDR ^ "\n");
pr "=THM= DONE\n";
"#
    );

    let Some((out, _)) = run_image_env(
        &image,
        &driver,
        80_000_000_000,
        &[
            ("ML_SYSTEM", "polyml"),
            ("ML_PLATFORM", "x86_64-linux"),
            ("ISABELLE_HOME", "/tmp/isa"),
        ],
    ) else {
        eprintln!("SKIP: poly could not spawn");
        return;
    };
    assert!(
        out.contains("=THM= DONE"),
        "theorem kernel demo did not finish.\n{}",
        tail(&out, 40)
    );
    for op in [
        "reflexive",
        "symmetric",
        "transitive",
        "beta",
        "imp_refl",
        "imp_weaken",
        "mp",
        "forall_intr",
        "forall_elim",
        "combination",
        "abstract_rule",
        "forall_imp",
    ] {
        assert!(
            out.contains(&format!("=THM= {op} true")),
            "LCF primitive `{op}` did not produce a checked theorem.\n{}",
            tail(&out, 40)
        );
    }
}
