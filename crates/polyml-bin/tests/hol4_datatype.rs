//! Stage 8 (FINAL) of the roadmap: HOL4's `Datatype` package RUNS on the
//! interpreter. Declaring a recursive datatype builds the type, its
//! constructors, the structural induction theorem, the case nchotomy, and the
//! recursion theorem, and registers it all in TypeBase — after which `Define`
//! can define recursive functions over the new type.
//!
//! `/tmp/hol4_datatype` is the full stack: … → ind_type (JRH inductive types)
//! → ParseDatatype → ind_types (define_type) → DataSize/EnumType/RecordType →
//! Datatype, on top of the Define/TFL machinery.
//!
//! Build: tools/build-hol4-checkpoints.sh datatype

mod common;

use common::run_image_env;
use std::path::PathBuf;

fn ckpt() -> Option<PathBuf> {
    let p = PathBuf::from("/tmp/hol4_datatype");
    p.exists().then_some(p)
}

#[test]
#[ignore = "needs /tmp/hol4_datatype (tools/build-hol4-checkpoints.sh datatype)"]
fn datatype_builds_recursive_type_and_registers_it() {
    let Some(image) = ckpt() else { return };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val () = Datatype.Datatype [QUOTE "tree = Leaf | Node tree tree"];
val ty = Type.mk_thy_type {Thy = Theory.current_theory(), Tyop = "tree", Args = []};
val () = case TypeBase.fetch ty of
             SOME _ => pr "TREE_REGISTERED\n"
           | NONE => pr "TREE_MISSING\n";
val () = pr "OK\n";
"#;
    let (out, _) = run_image_env(&image, driver, 100_000_000_000, &[]).expect("run");
    assert!(out.contains("TREE_REGISTERED"), "tree not in TypeBase:\n{out}");
    assert!(!out.contains("Exception-"), "exception:\n{out}");
}

#[test]
#[ignore = "needs /tmp/hol4_datatype (tools/build-hol4-checkpoints.sh datatype)"]
fn datatype_generates_induction_and_recursion() {
    // The full datatype workflow: declare a recursive type carrying data, get
    // its induction/nchotomy, then define a recursive function over it.
    let Some(image) = ckpt() else { return };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
infix THEN;
val () = Datatype.Datatype [QUOTE "btree = BLeaf num | BNode btree btree"];
val ty = Type.mk_thy_type {Thy = Theory.current_theory(), Tyop = "btree", Args = []};
val SOME tyi = TypeBase.fetch ty;
val ind = TypeBasePure.induction_of tyi;
val () = pr ("IND " ^ Parse.thm_to_string ind ^ "\n");
val cnt = TotalDefn.Define
  [QUOTE "(count (BLeaf n) = 1) /\\ (count (BNode l r) = count l + count r)"];
val () = if List.null (Thm.hyp cnt) then pr "REC_DEF_OK\n" else pr "HYPS\n";
"#;
    let (out, _) = run_image_env(&image, driver, 200_000_000_000, &[]).expect("run");
    assert!(out.contains("IND "), "no induction theorem:\n{out}");
    assert!(
        out.contains("REC_DEF_OK"),
        "recursive function over the new datatype failed:\n{out}"
    );
}

#[test]
#[ignore = "needs /tmp/hol4_datatype (tools/build-hol4-checkpoints.sh datatype)"]
fn polymorphic_list_theory_by_induction() {
    // The capstone: build the canonical POLYMORPHIC list datatype, define
    // app/rev via Define, and prove REVERSE_REVERSE (rev (rev l) = l) and its
    // lemma REVERSE_APPEND by structural induction — a complete little theory.
    let Some(image) = ckpt() else { return };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
infix THEN;
open boolLib;
val () = Datatype.Datatype [QUOTE "lst = Nil | Cons 'a lst"];
val ty = Type.mk_thy_type {Thy=Theory.current_theory(), Tyop="lst", Args=[Type.alpha]};
val SOME tyi = TypeBase.fetch ty;
val list_ind = TypeBasePure.induction_of tyi;
fun byInduction tac =
    Tactical.THEN (Tactic.HO_MATCH_MP_TAC list_ind,
      Tactical.THEN (Tactical.REPEAT Tactic.STRIP_TAC, tac));
val APP = TotalDefn.Define [QUOTE "(app Nil m = m) /\\ (app (Cons a l) m = Cons a (app l m))"];
val REV = TotalDefn.Define [QUOTE "(rev Nil = Nil) /\\ (rev (Cons a l) = app (rev l) (Cons a Nil))"];
val app_Nil = Tactical.prove(Parse.Term [QUOTE "!l. app l Nil = l"],
  byInduction (ASM_REWRITE_TAC [APP]));
val app_assoc = Tactical.prove(
  Parse.Term [QUOTE "!l1 l2 l3. app (app l1 l2) l3 = app l1 (app l2 l3)"],
  byInduction (ASM_REWRITE_TAC [APP]));
val rev_app = Tactical.prove(
  Parse.Term [QUOTE "!l1 l2. rev (app l1 l2) = app (rev l2) (rev l1)"],
  byInduction (ASM_REWRITE_TAC [APP, REV, app_Nil, app_assoc]));
val rev_rev = Tactical.prove(
  Parse.Term [QUOTE "!l. rev (rev l) = l"],
  byInduction (ASM_REWRITE_TAC [REV, rev_app, APP]));
val () = if List.null (Thm.hyp rev_rev) then pr "REV_REV_OK\n" else pr "HYPS\n";
"#;
    let (out, _) = run_image_env(&image, driver, 300_000_000_000, &[]).expect("run");
    assert!(
        out.contains("REV_REV_OK"),
        "polymorphic list theory (rev(rev l)=l) failed:\n{out}"
    );
    assert!(!out.contains("Exception-"), "exception:\n{out}");
}
