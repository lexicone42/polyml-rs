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
fn computelib_reduces_numeral_multiplication() {
    // The numeral sweep banked degraded DB theorems (numeral_distrib = |- T),
    // so the global computeLib compset could pull NUMERAL out over * but not
    // reduce the bit-level product, leaving 3*4 stuck as NUMERAL(BIT*BIT). The
    // datatype-checkpoint build repairs it by re-adding the correct
    // structure-value numeralTheory.numeral_mult family to the_compset. This
    // fences that fix: computeLib EVAL must reduce 3*4 -> 12.
    let Some(image) = ckpt() else { return };
    let driver = r#"
fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
val cs = computeLib.copy (!computeLib.the_compset);
fun ev s = Parse.term_to_string (boolSyntax.rhs (Thm.concl
             (computeLib.CBV_CONV cs (Parse.Term [QUOTE s]))));
val () = pr ("3*4 = " ^ ev "3 * 4" ^ "\n");
val () = pr ("12*13 = " ^ ev "12 * 13" ^ "\n");
val () = pr ("(2+3)*5 = " ^ ev "(2 + 3) * 5" ^ "\n");
val () = pr "MULT_EVAL_DONE\n";
"#;
    let (out, _) = run_image_env(&image, driver, 50_000_000_000, &[]).expect("run");
    assert!(out.contains("3*4 = 12"), "computeLib did not reduce 3*4 to 12:\n{out}");
    assert!(out.contains("12*13 = 156"), "computeLib did not reduce 12*13 to 156:\n{out}");
    assert!(out.contains("(2+3)*5 = 25"), "computeLib did not reduce (2+3)*5 to 25:\n{out}");
    assert!(out.contains("MULT_EVAL_DONE"), "incomplete:\n{out}");
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

#[test]
#[ignore = "needs /tmp/hol4_datatype (tools/build-hol4-checkpoints.sh datatype)"]
fn verified_insertion_sort() {
    // The whole point of a theorem prover: a VERIFIED PROGRAM. Define insertion
    // sort over a datatype, prove it outputs a SORTED list (sorted_isort) that
    // is a PERMUTATION of its input (count_isort, multiset-preserving). The
    // proof chain (ins_leall / leall_trans / ins_sorted / ins_count) was
    // engineered by a 3-seat proof fleet.
    let Some(image) = ckpt() else { return };
    let driver = std::fs::read_to_string(
        common::support_file("insertion_sort_verified.sml"),
    )
    .expect("read insertion_sort_verified.sml");
    let (out, _) = run_image_env(&image, &driver, 300_000_000_000, &[]).expect("run");
    assert!(out.contains("OK sorted_isort"), "sortedness failed:\n{out}");
    assert!(out.contains("OK count_isort"), "permutation failed:\n{out}");
    // and the algorithm RUNS (computeLib EVAL over the user datatype): the
    // computed sort of [3,1,4,1,5,9,2,6] is kernel-checked equal to the sorted
    // list — proved correct AND executed, both certified by the kernel.
    assert!(
        out.contains("EVAL_SORTED_OK"),
        "EVAL of isort did not produce the sorted list:\n{out}"
    );
    assert!(out.contains("ALL_DONE"), "verification incomplete:\n{out}");
}

#[test]
#[ignore = "needs /tmp/hol4_datatype (tools/build-hol4-checkpoints.sh datatype)"]
fn verified_euclid_gcd() {
    // NON-STRUCTURAL recursion verified: define Euclid's gcd by `tDefine` with a
    // `measure SND` and an auto-discharged termination obligation (a MOD b < b),
    // then FULLY CHARACTERISE it via the recursion-induction principle gcd_ind
    // (which tDefine emits), threading divisibility through the Euclid step
    // a = (a DIV b)*b + (a MOD b):
    //   gcd_divides  : |- !a b. divides (gcd a b) a /\ divides (gcd a b) b
    //                  (gcd is a COMMON DIVISOR)
    //   gcd_greatest : |- !a b d. divides d a /\ divides d b
    //                             ==> divides d (gcd a b)
    //                  (it is the GREATEST common divisor)
    // Both ZERO-hypothesis theorems, engineered by two 3-seat fleets
    // (wf_dac9e4a5-fe2 / wf_9aa3fd1e-5a7, all seats converged independently).
    let Some(image) = ckpt() else { return };
    let driver =
        std::fs::read_to_string(common::support_file("gcd_verified.sml")).expect("read gcd_verified.sml");
    let (out, _) = run_image_env(&image, &driver, 200_000_000_000, &[]).expect("run");
    assert!(out.contains("GCD_SETUP_OK"), "gcd tDefine setup failed:\n{out}");
    assert!(
        out.contains("OK gcd_divides"),
        "gcd common-divisor theorem failed:\n{out}"
    );
    assert!(
        out.contains("OK gcd_greatest"),
        "gcd greatest-common-divisor (universal property) failed:\n{out}"
    );
    assert!(out.contains("SAVED gcd_greatest"), "gcd_greatest not saved:\n{out}");
    // commutativity proved ALGEBRAICALLY from the characterisation (no induction)
    assert!(
        out.contains("OK gcd_comm"),
        "gcd commutativity (via divides antisymmetry) failed:\n{out}"
    );
    // lcm via gcd + the classic gcd*lcm = a*b duality
    assert!(
        out.contains("OK gcd_lcm"),
        "gcd-lcm duality (gcd a b * lcm a b = a * b) failed:\n{out}"
    );
    assert!(out.contains("ALL_DONE"), "verification incomplete:\n{out}");
    assert!(!out.contains("Exception-"), "exception:\n{out}");
}

#[test]
#[ignore = "needs /tmp/hol4_datatype (tools/build-hol4-checkpoints.sh datatype)"]
fn verified_compiler() {
    // The crown-jewel formal-methods result (Bahr-Hutton): compile an
    // arithmetic-expression language (expr = Const|Plus|Times) to a stack
    // machine (instr = Push|Add|Mul over user-defined code/stack list types)
    // and PROVE the compiler correct:
    //   compile_correct : |- !e s. exec (compile e) s = SPush (eval e) s
    // a ZERO-hypothesis theorem, by structural induction on e resting on the
    // exec-distributes-over-concatenation lemma exec_capp (code induction).
    // Then EVAL a concrete program: the compiled code RUNS on the stack
    // machine and agrees with the source eval. (3-seat fleet wf_a9867385-1d0.)
    //
    // PLUS the OPTIMIZING-COMPILER extension (CompCert-style compositional
    // verification): a constant-folding optimizer `simplify` proved
    // semantics-preserving (simplify_correct: eval (simplify e) = eval e) and
    // COMPOSED with the compiler into opt_compile_correct:
    //   |- !e s. exec (compile (simplify e)) s = SPush (eval e) s
    // a 2-line corollary of the two passes. (3-seat fleet wf_b7e907bb-345.)
    let Some(image) = ckpt() else { return };
    let driver = std::fs::read_to_string(common::support_file("verified_compiler.sml"))
        .expect("read verified_compiler.sml");
    let (out, _) = run_image_env(&image, &driver, 200_000_000_000, &[]).expect("run");
    assert!(out.contains("OK exec_capp"), "exec_capp lemma failed:\n{out}");
    assert!(
        out.contains("OK compile_correct"),
        "compiler correctness theorem failed:\n{out}"
    );
    assert!(out.contains("ZERO_HYP_OK"), "compile_correct has hypotheses:\n{out}");
    // the compiled code actually RUNS and agrees with eval (kernel-checked)
    assert!(out.contains("EVAL_OK"), "EVAL demo (machine run = source eval) failed:\n{out}");
    // OPTIMIZING-COMPILER EXTENSION: a constant-folding optimizer proved
    // semantics-preserving (simplify_correct) and COMPOSED with the compiler
    // (opt_compile_correct) — CompCert-style two-pass composition.
    assert!(
        out.contains("OK simplify_correct"),
        "optimizer correctness (eval (simplify e) = eval e) failed:\n{out}"
    );
    assert!(
        out.contains("OK opt_compile_correct"),
        "optimization-through-compilation composition failed:\n{out}"
    );
    assert!(!out.contains("Exception-"), "exception:\n{out}");
}

#[test]
#[ignore = "needs /tmp/hol4_datatype (tools/build-hol4-checkpoints.sh datatype)"]
fn verified_merge_sort() {
    // A harder verified sort than insertion sort: NON-STRUCTURAL recursion,
    // tamed with a FUEL parameter so the top-level msort is structurally
    // recursive (plain Define), with `merge`/`split` via tDefine (measure on
    // length). Prove BOTH correctness properties, each zero-hypothesis:
    //   msort_count  : |- !z l. count z (msort l) = count z l   (PERMUTATION)
    //   msort_sorted : |- !l. sorted (msort l)                  (SORTEDNESS)
    // then EVAL a concrete sort ([3,1,2,5,4] -> [1,2,3,4,5]), kernel-checked.
    // Engineered by a 3-seat fleet (wf_0158176e-c65); all 3 got both + EVAL.
    let Some(image) = ckpt() else { return };
    let driver = std::fs::read_to_string(common::support_file("merge_sort_verified.sml"))
        .expect("read merge_sort_verified.sml");
    let (out, _) = run_image_env(&image, &driver, 150_000_000_000, &[]).expect("run");
    assert!(out.contains("OK msort_count"), "merge sort permutation property failed:\n{out}");
    assert!(out.contains("OK msort_sorted"), "merge sort sortedness failed:\n{out}");
    assert!(out.contains("msort_count hyps=0"), "msort_count has hypotheses:\n{out}");
    assert!(out.contains("msort_sorted hyps=0"), "msort_sorted has hypotheses:\n{out}");
    assert!(out.contains("EVAL_OK"), "EVAL of msort did not produce the sorted list:\n{out}");
    assert!(out.contains("ALL_DONE"), "verification incomplete:\n{out}");
    assert!(!out.contains("Exception-"), "exception:\n{out}");
}

#[test]
#[ignore = "needs /tmp/hol4_datatype (tools/build-hol4-checkpoints.sh datatype)"]
fn verified_bst() {
    // Data-structure verification with an INVARIANT: a binary search tree
    // (tree = Leaf | Node tree num tree) with insert/member. Prove BOTH
    //   member_insert : |- !t x y. member x (insert y t) <=> (x=y) \/ member x t
    //                   (membership is correct: insert adds exactly y)
    //   insert_bst    : |- !t x. bst t ==> bst (insert x t)
    //                   (insert PRESERVES the BST ordering invariant)
    // both zero-hypothesis, by structural tree induction. Then EVAL membership
    // on a concrete tree (member 3 -> T, member 4 -> F). Engineered by a 3-seat
    // fleet (wf_6bef35bc-140); all three seats verified independently.
    let Some(image) = ckpt() else { return };
    let driver = std::fs::read_to_string(common::support_file("verified_bst.sml"))
        .expect("read verified_bst.sml");
    let (out, _) = run_image_env(&image, &driver, 200_000_000_000, &[]).expect("run");
    assert!(out.contains("OK member_insert [0 hyps]"), "membership-correctness failed:\n{out}");
    assert!(out.contains("OK insert_bst [0 hyps]"), "BST-invariant preservation failed:\n{out}");
    // membership actually computes on a concrete tree (kernel-checked)
    assert!(out.contains("EVAL_OK"), "EVAL of member on a concrete tree failed:\n{out}");
    assert!(out.contains("BST_DONE"), "verification incomplete:\n{out}");
    assert!(!out.contains("Exception-"), "exception:\n{out}");
}
