(* hol4_listlaws_rewrite.sml — classic LIST-FUNCTION correctness laws on HOL4's
   real LCF kernel, running on the Rust PolyML interpreter (/tmp/hol4_datatype).
   NO listTheory: we define our OWN polymorphic list datatype lst = Nil | Cons 'a lst.

   SEAT = rewrite: plain structural Induct (HO_MATCH_MP_TAC the auto-generated
   list induction) + unfold defs + ASM_REWRITE_TAC, minimal automation.

   Laws proved (each a 0-hyp theorem, BY STRUCTURAL INDUCTION):
     append_assoc   : append (append a b) c = append a (append b c)
     append_nil     : append l Nil = l
     revacc_correct : revacc l a = append (reverse l) a
     revacc_reverse : revacc l Nil = reverse l          (corollary)
     map_fusion     : lmap f (lmap g l) = lmap (\x. f (g x)) l
     len_append     : llen (append a b) = llen a + llen b *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
infix THEN THENL;
open boolLib;

(* === Build the polymorphic list datatype === *)
val () = Datatype.Datatype [QUOTE "lst = Nil | Cons 'a lst"];
val ty = Type.mk_thy_type {Thy=Theory.current_theory(), Tyop="lst", Args=[Type.alpha]};
val SOME tyi = TypeBase.fetch ty;
val lst_ind = TypeBasePure.induction_of tyi;
(* plain structural induction: apply the list induction principle, strip the
   universally-quantified Cons-case vars + IH into assumptions, then run tac. *)
fun byInduction tac =
    Tactical.THEN (Tactic.HO_MATCH_MP_TAC lst_ind,
      Tactical.THEN (Tactical.REPEAT Tactic.STRIP_TAC, tac));
val () = pr "DATATYPE_OK\n";

(* === Define the list functions === *)
val APPEND  = TotalDefn.Define
   [QUOTE "(append Nil m = m) /\\ (append (Cons h t) m = Cons h (append t m))"];
val REVERSE = TotalDefn.Define
   [QUOTE "(reverse Nil = Nil) /\\ (reverse (Cons h t) = append (reverse t) (Cons h Nil))"];
val REVACC  = TotalDefn.Define
   [QUOTE "(revacc Nil a = a) /\\ (revacc (Cons h t) a = revacc t (Cons h a))"];
val LMAP    = TotalDefn.Define
   [QUOTE "(lmap f Nil = Nil) /\\ (lmap f (Cons h t) = Cons (f h) (lmap f t))"];
val LLEN    = TotalDefn.Define
   [QUOTE "(llen Nil = 0) /\\ (llen (Cons h t) = SUC (llen t))"];
val () = pr "DEFS_OK\n";

(* show a theorem and assert it has NO hypotheses, then emit its OK marker *)
fun show nm th =
  (pr (nm ^ ": " ^ Parse.thm_to_string th ^ "\n");
   if List.null (Thm.hyp th) then pr ("OK " ^ nm ^ "\n")
   else pr ("HYPS " ^ nm ^ " (" ^ Int.toString (List.length (Thm.hyp th)) ^ ")\n"));

(* === HELPER 1: append_nil — append l Nil = l, by induction on l === *)
val append_nil = Tactical.prove(
  Parse.Term [QUOTE "!l. append l Nil = l"],
  byInduction (ASM_REWRITE_TAC [APPEND]));
val () = show "append_nil" append_nil;

(* === HELPER 2: append_assoc, by induction on the first list === *)
val append_assoc = Tactical.prove(
  Parse.Term [QUOTE "!a b c. append (append a b) c = append a (append b c)"],
  byInduction (ASM_REWRITE_TAC [APPEND]));
val () = show "append_assoc" append_assoc;

(* === HEADLINE: revacc_correct — revacc l a = append (reverse l) a.
   Induct on l; the Cons case needs the IH (specialized by ASM_REWRITE to the
   acc) plus append_assoc to re-associate append (reverse t) (Cons h Nil) a.
   Generalize the accumulator FIRST (it changes across the recursion). === *)
val revacc_correct = Tactical.prove(
  Parse.Term [QUOTE "!l a. revacc l a = append (reverse l) a"],
  byInduction (ASM_REWRITE_TAC [REVACC, REVERSE, append_assoc, APPEND]));
val () = show "revacc_correct" revacc_correct;

(* COROLLARY: revacc l Nil = reverse l — specialize a := Nil, use append_nil. *)
val revacc_reverse = Tactical.prove(
  Parse.Term [QUOTE "!l. revacc l Nil = reverse l"],
  Tactical.THEN (Tactic.GEN_TAC,
    Rewrite.REWRITE_TAC [revacc_correct, append_nil]));
val () = show "revacc_reverse" revacc_reverse;

(* === HEADLINE: map_fusion — lmap f (lmap g l) = lmap (\x. f (g x)) l.
   Functor law. GEN the function args first, then induct on l. The Cons case
   produces ((\x. f (g x)) h) on the RHS which ASM_REWRITE won't beta-reduce,
   so add BETA_TAC after the rewrite to discharge the lambda application. === *)
val map_fusion = Tactical.prove(
  Parse.Term [QUOTE "!f g l. lmap f (lmap g l) = lmap (\\x. f (g x)) l"],
  Tactical.THEN (Tactic.GEN_TAC, Tactical.THEN (Tactic.GEN_TAC,
    byInduction (Tactical.THEN (
      Rewrite.ASM_REWRITE_TAC [LMAP],
      Tactical.THEN (
        Tactical.TRY (Tactic.CONV_TAC (DEPTH_CONV BETA_CONV)),
        Rewrite.REWRITE_TAC []))))));   (* close the now-reflexive goal *)
val () = show "map_fusion" map_fusion;

(* === HEADLINE: len_append — llen (append a b) = llen a + llen b.
   Induct on a; arithmetic SUC(x)+y = SUC(x+y) via ADD_CLAUSES. === *)
val len_append = Tactical.prove(
  Parse.Term [QUOTE "!a b. llen (append a b) = llen a + llen b"],
  byInduction (ASM_REWRITE_TAC [APPEND, LLEN, arithmeticTheory.ADD_CLAUSES]));
val () = show "len_append" len_append;

val () = pr "LIST_LAWS_DONE\n";
