(* list_theory_demo.sml — a complete polymorphic list theory built on HOL4's
   Datatype package (Stage 8 capstone), all on the Rust interpreter:
     Datatype `lst = Nil | Cons 'a lst`  (POLYMORPHIC), then app/len/rev/map via
     Define, then app_Nil / app_assoc / len_app / map_app / rev_app /
     rev_rev (REVERSE_REVERSE) proved by structural induction on the
     auto-generated list induction principle.
   Run: tools/sml-exp.sh /tmp/hol4_datatype list_theory_demo.sml *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
infix THEN THENL;
open boolLib;
fun ARITH tm = Drule.EQT_ELIM (Arith.ARITH_CONV tm);
fun ARITH_TAC g = Tactic.CONV_TAC (Drule.EQT_INTRO o ARITH) g;

(* === Build the polymorphic list datatype === *)
val () = Datatype.Datatype [QUOTE "lst = Nil | Cons 'a lst"];
val ty = Type.mk_thy_type {Thy=Theory.current_theory(), Tyop="lst", Args=[Type.alpha]};
val SOME tyi = TypeBase.fetch ty;
val list_ind = TypeBasePure.induction_of tyi;
fun byInduction tac =
    Tactical.THEN (Tactic.HO_MATCH_MP_TAC list_ind,
      Tactical.THEN (Tactical.REPEAT Tactic.STRIP_TAC, tac));

(* === Define the core list functions === *)
val APP = TotalDefn.Define [QUOTE "(app Nil m = m) /\\ (app (Cons a l) m = Cons a (app l m))"];
val LEN = TotalDefn.Define [QUOTE "(len Nil = 0) /\\ (len (Cons a l) = SUC (len l))"];
val REV = TotalDefn.Define [QUOTE "(rev Nil = Nil) /\\ (rev (Cons a l) = app (rev l) (Cons a Nil))"];
val MAP = TotalDefn.Define [QUOTE "(map f Nil = Nil) /\\ (map f (Cons a l) = Cons (f a) (map f l))"];
val () = pr "=== list functions defined (app/len/rev/map) ===\n";

fun show nm th = pr (nm ^ ": " ^ Parse.thm_to_string th ^ "\n");

(* === Prove the canonical theorems BY LIST INDUCTION === *)
val app_Nil = Tactical.prove(Parse.Term [QUOTE "!l. app l Nil = l"],
  byInduction (ASM_REWRITE_TAC [APP]));
val () = show "app_Nil" app_Nil;

val app_assoc = Tactical.prove(
  Parse.Term [QUOTE "!l1 l2 l3. app (app l1 l2) l3 = app l1 (app l2 l3)"],
  byInduction (ASM_REWRITE_TAC [APP]));
val () = show "app_assoc" app_assoc;

val len_app = Tactical.prove(
  Parse.Term [QUOTE "!l1 l2. len (app l1 l2) = len l1 + len l2"],
  byInduction (ASM_REWRITE_TAC [APP, LEN, arithmeticTheory.ADD_CLAUSES]));
val () = show "len_app" len_app;

val map_app = Tactical.prove(
  Parse.Term [QUOTE "!f l1 l2. map f (app l1 l2) = app (map f l1) (map f l2)"],
  Tactical.THEN (Tactic.GEN_TAC, byInduction (ASM_REWRITE_TAC [APP, MAP])));
val () = show "map_app" map_app;

val rev_app = Tactical.prove(
  Parse.Term [QUOTE "!l1 l2. rev (app l1 l2) = app (rev l2) (rev l1)"],
  byInduction (ASM_REWRITE_TAC [APP, REV, app_Nil, app_assoc]));
val () = show "rev_app" rev_app;

(* THE CROWN JEWEL: reverse of reverse is identity *)
val rev_rev = Tactical.prove(
  Parse.Term [QUOTE "!l. rev (rev l) = l"],
  byInduction (ASM_REWRITE_TAC [REV, rev_app, APP]));
val () = show "rev_rev" rev_rev;

val () = pr "\n=== A COMPLETE LIST THEORY, PROVED ON THE RUST INTERPRETER ===\n";
