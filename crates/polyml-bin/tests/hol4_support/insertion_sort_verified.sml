(* insertion_sort_verified.sml — a VERIFIED PROGRAM on HOL4's Datatype package
   (Stage 8 capstone), all on the Rust interpreter: define insertion sort over
   `lst = Nil | Cons num lst`, then prove it correct —
     sorted_isort:  !l. sorted (isort l)            (output is SORTED)
     count_isort:   !x l. count x (isort l) = count x l   (output is a PERMUTATION)
   The proof chain (ins_leall -> ins_sorted -> sorted_isort; ins_count ->
   count_isort) was engineered by a 3-seat proof fleet (wf_370857d4).
   Run: tools/sml-exp.sh /tmp/hol4_datatype insertion_sort_verified.sml *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
infix THEN THENL ORELSE;
open boolLib;
fun ARITH tm = Drule.EQT_ELIM (Arith.ARITH_CONV tm);
fun ARITH_TAC g = Tactic.CONV_TAC (Drule.EQT_INTRO o ARITH) g;
val () = Datatype.Datatype [QUOTE "lst = Nil | Cons num lst"];
val ty = Type.mk_thy_type {Thy=Theory.current_theory(), Tyop="lst", Args=[]};
val SOME tyi = TypeBase.fetch ty;
val list_ind = TypeBasePure.induction_of tyi;
fun byInduction tac = Tactical.THEN (Tactic.HO_MATCH_MP_TAC list_ind,
      Tactical.THEN (Tactical.REPEAT Tactic.STRIP_TAC, tac));
val INS = TotalDefn.Define [QUOTE "(ins x Nil = Cons x Nil) /\\ (ins x (Cons a l) = if x <= a then Cons x (Cons a l) else Cons a (ins x l))"];
val ISORT = TotalDefn.Define [QUOTE "(isort Nil = Nil) /\\ (isort (Cons a l) = ins a (isort l))"];
val LEALL = TotalDefn.Define [QUOTE "(leall x Nil = T) /\\ (leall x (Cons a l) = ((x <= a) /\\ leall x l))"];
val SORTED = TotalDefn.Define [QUOTE "(sorted Nil = T) /\\ (sorted (Cons a l) = (leall a l /\\ sorted l))"];
val COUNT = TotalDefn.Define [QUOTE "(count x Nil = 0) /\\ (count x (Cons a l) = (if x = a then 1 else 0) + count x l)"];
val () = pr "ISORT_SETUP_OK\n";

(* === fleet-verified correctness proofs appended below === *)
(* ===================== PROOFS (append after the SETUP block) ===================== *)

(* A selective arithmetic closer that lifts ONLY pure-numeric assumptions
   (those mentioning none of our list/predicate constants) into the goal,
   then calls the real arithmetic decision procedure ARITH.  This is the
   key robustness trick: ARITH (= Drule.EQT_ELIM o Arith.ARITH_CONV) decides
   a CLOSED arithmetic goal and does NOT read assumptions, so subgoals like
   `y <= n` that need transitivity (`y<=x`, `x<=n` in the hyps) must first
   have those inequalities discharged into the goal -- but NOT the leall/sorted
   hyps, which would make the goal non-arithmetic and break ARITH. *)
val blocked = ["leall","sorted","count","ins","isort","Cons","Nil"];
fun mentions_blocked tm =
  not (null (HolKernel.find_terms
        (fn t => Term.is_const t andalso
                 List.exists (fn nm => nm = #1 (Term.dest_const t)) blocked) tm));
val ASM_ARITH_TAC : Tactic.tactic =
  fn (asl,w) =>
    let val good = List.filter (fn a => not (mentions_blocked a)) asl
    in (Tactical.MAP_EVERY (fn a => Tactic.MP_TAC (Thm.ASSUME a)) good
        THEN ARITH_TAC) (asl,w)
    end;

(* ins_leall: ins keeps a lower bound. *)
val ins_leall = Tactical.prove(
  Parse.Term [QUOTE "!l y x. y <= x /\\ leall y l ==> leall y (ins x l)"],
  byInduction(
    Tactical.TRY(simpLib.FULL_SIMP_TAC boolSimps.bool_ss [LEALL])
    THEN Rewrite.REWRITE_TAC[INS]
    THEN Tactical.TRY Tactic.COND_CASES_TAC
    THEN Rewrite.ASM_REWRITE_TAC[LEALL]
    THEN Tactical.REPEAT Tactic.CONJ_TAC
    THEN Tactical.TRY Tactic.RES_TAC
    THEN Tactical.TRY(Tactical.FIRST_X_ASSUM Tactic.MATCH_MP_TAC)
    THEN Rewrite.ASM_REWRITE_TAC[]
    THEN Tactical.TRY ASM_ARITH_TAC));
val () = pr "OK ins_leall\n";

(* leall_trans: lower the bound through <=. *)
val leall_trans = Tactical.prove(
  Parse.Term [QUOTE "!l y z. y <= z /\\ leall z l ==> leall y l"],
  byInduction(
    Tactical.TRY(simpLib.FULL_SIMP_TAC boolSimps.bool_ss [LEALL])
    THEN Rewrite.ASM_REWRITE_TAC[LEALL]
    THEN Tactical.REPEAT Tactic.CONJ_TAC
    THEN Tactical.TRY Tactic.RES_TAC
    THEN Rewrite.ASM_REWRITE_TAC[]
    THEN Tactical.TRY ASM_ARITH_TAC));
val () = pr "OK leall_trans\n";

(* ins_sorted: ins keeps a sorted list sorted. *)
val ins_sorted = Tactical.prove(
  Parse.Term [QUOTE "!l x. sorted l ==> sorted (ins x l)"],
  byInduction(
    Tactical.TRY(simpLib.FULL_SIMP_TAC boolSimps.bool_ss [SORTED])
    THEN Rewrite.REWRITE_TAC[INS]
    THEN Tactical.TRY Tactic.COND_CASES_TAC
    THEN Rewrite.ASM_REWRITE_TAC[SORTED, LEALL]
    THEN Tactical.REPEAT Tactic.CONJ_TAC
    THEN Rewrite.ASM_REWRITE_TAC[]
    THEN Tactical.TRY (Tactic.MATCH_MP_TAC leall_trans THEN Tactic.EXISTS_TAC (Parse.Term [QUOTE "n:num"]) THEN Rewrite.ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC)
    THEN Tactical.TRY (Tactic.MATCH_MP_TAC ins_leall THEN Rewrite.ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC)
    THEN Tactical.TRY Tactic.RES_TAC
    THEN Rewrite.ASM_REWRITE_TAC[]));
val () = pr "OK ins_sorted\n";

(* (A) sorted_isort: insertion sort outputs a SORTED list. *)
val sorted_isort = Tactical.prove(
  Parse.Term [QUOTE "!l. sorted (isort l)"],
  byInduction(
    Rewrite.REWRITE_TAC[ISORT, SORTED]
    THEN Tactical.TRY (Tactic.MATCH_MP_TAC ins_sorted THEN Rewrite.ASM_REWRITE_TAC[])
    THEN Rewrite.ASM_REWRITE_TAC[]));
val _ = Theory.save_thm("sorted_isort", sorted_isort);
val () = pr "OK sorted_isort\n";

(* ins_count: ins preserves the multiset (count of an arbitrary element). *)
val ins_count = Tactical.prove(
  Parse.Term [QUOTE "!l y x. count y (ins x l) = (if y = x then 1 else 0) + count y l"],
  byInduction(
    Rewrite.REWRITE_TAC[INS]
    THEN Tactical.TRY Tactic.COND_CASES_TAC
    THEN Rewrite.ASM_REWRITE_TAC[COUNT]
    THEN Tactical.TRY ASM_ARITH_TAC));
val () = pr "OK ins_count\n";

(* (B) count_isort: insertion sort is a PERMUTATION of its input. *)
val count_isort = Tactical.prove(
  Parse.Term [QUOTE "!l x. count x (isort l) = count x l"],
  byInduction(
    Rewrite.ASM_REWRITE_TAC[ISORT, COUNT, ins_count]));
val _ = Theory.save_thm("count_isort", count_isort);
val () = pr "OK count_isort\n";

(* === COMPUTE, not just prove: actually RUN the verified algorithm via the
   computeLib call-by-value engine. Each result is a kernel-checked theorem
   (the global compset carries bool/COND + numeral <= reductions; we copy it
   and add the isort equations — EVAL over a USER datatype). === *)
val cs = computeLib.copy (!computeLib.the_compset);
val _ = computeLib.add_thms [INS, ISORT] cs;
fun runsort q =
    let val th = computeLib.CBV_CONV cs (Parse.Term [QUOTE q])
    in pr ("  EVAL isort: " ^ Parse.term_to_string (rhs (concl th)) ^ "\n"); th end;
val sort_demo = runsort "isort (Cons 3 (Cons 1 (Cons 4 (Cons 1 (Cons 5 (Cons 9 (Cons 2 (Cons 6 Nil))))))))";
(* assert the computed result IS the sorted list (kernel-checked equality) *)
val expected = Parse.Term [QUOTE "Cons 1 (Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 5 (Cons 6 (Cons 9 Nil)))))))"];
val () = if Term.aconv (rhs (concl sort_demo)) expected
         then pr "EVAL_SORTED_OK\n" else pr "EVAL_SORTED_WRONG\n";

val () = pr "ALL_DONE\n";
