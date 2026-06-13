(* hol4_qsort_simp.sml — VERIFIED QUICKSORT on HOL4's real LCF kernel,
   running on the Rust PolyML interpreter (/tmp/hol4_datatype).  NO listTheory:
   we define our own num-list `lst = Nil | Cons num lst`.

   SEAT: simp — lean on SIMP_TAC / FULL_SIMP_TAC with the defs + arithmetic,
   mirroring merge_sort_verified.sml.

   qsort is genuinely non-structural recursion (recurses on filtered sublists),
   so we use tDefine with measure (llen) and a termination side-lemma that the
   filters do not increase length.

   HEADLINE 1 (REQUIRED): qsort_count : |- !x l. count x (qsort l) = count x l
     (qsort is a PERMUTATION of its input — preserves the multiset).
   HEADLINE 2 (REQUIRED): qsort_sorted : |- !l. sorted (qsort l)
     (qsort outputs a SORTED list). *)

fun pr s = (print s; TextIO.flushOut TextIO.stdOut);
infix THEN THENL ORELSE;
open boolLib;
fun ARITH tm = Drule.EQT_ELIM (Arith.ARITH_CONV tm);
fun ARITH_TAC g = Tactic.CONV_TAC (Drule.EQT_INTRO o ARITH) g;
val q = fn s => Parse.Term [QUOTE s];

(* === DATATYPE === *)
val () = Datatype.Datatype [QUOTE "lst = Nil | Cons num lst"];
val ty = Type.mk_thy_type {Thy=Theory.current_theory(), Tyop="lst", Args=[]};
val SOME tyi = TypeBase.fetch ty;
val lst_ind = TypeBasePure.induction_of tyi;
fun byLstInduction tac = Tactical.THEN (Tactic.HO_MATCH_MP_TAC lst_ind,
      Tactical.THEN (Tactical.REPEAT Tactic.STRIP_TAC, tac));
val () = pr "DATATYPE_OK\n";

(* Selective arithmetic closer: lift ONLY the pure-numeric assumptions (those
   mentioning none of our list/predicate constants), so the count/leall/sorted
   IHs aren't dumped into the goal (which would make it non-arithmetic), then
   call the closed-arithmetic decision procedure ARITH. *)
val blocked = ["leall","geall","sorted","count","qsort","le_filter","gt_filter",
               "append","llen","Cons","Nil"];
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
(* Non-selective variant: lift ALL assumptions (used where the IH itself is a
   linear (in)equality over opaque llen atoms). *)
val ALL_ARITH_TAC : Tactic.tactic =
  fn (asl,w) =>
    (Tactical.MAP_EVERY (fn a => Tactic.MP_TAC (Thm.ASSUME a)) asl THEN ARITH_TAC) (asl,w);

(* === DEFINITIONS === *)
val LLEN  = TotalDefn.Define [QUOTE "(llen Nil = 0) /\\ (llen (Cons a l) = SUC (llen l))"];
val APPEND= TotalDefn.Define [QUOTE "(append Nil m = m) /\\ (append (Cons a l) m = Cons a (append l m))"];
val LEALL = TotalDefn.Define [QUOTE "(leall x Nil = T) /\\ (leall x (Cons a l) = ((x <= a) /\\ leall x l))"];
val GEALL = TotalDefn.Define [QUOTE "(geall x Nil = T) /\\ (geall x (Cons a l) = ((a <= x) /\\ geall x l))"];
val SORTED= TotalDefn.Define [QUOTE "(sorted Nil = T) /\\ (sorted (Cons a l) = (leall a l /\\ sorted l))"];
val COUNT = TotalDefn.Define [QUOTE "(count x Nil = 0) /\\ (count x (Cons a l) = (if x = a then 1 else 0) + count x l)"];
val LEF   = TotalDefn.Define [QUOTE "(le_filter p Nil = Nil) /\\ (le_filter p (Cons a l) = if a <= p then Cons a (le_filter p l) else le_filter p l)"];
val GTF   = TotalDefn.Define [QUOTE "(gt_filter p Nil = Nil) /\\ (gt_filter p (Cons a l) = if p < a then Cons a (gt_filter p l) else gt_filter p l)"];
val () = pr "BASIC_DEFS_OK\n";

(* Termination side-lemmas: filters do not increase length. *)
val lef_len = Tactical.prove(
  q "!p l. llen (le_filter p l) <= llen l",
  Tactic.GEN_TAC THEN byLstInduction(
    simpLib.FULL_SIMP_TAC boolSimps.bool_ss [LEF, LLEN]
    THEN Tactical.TRY Tactic.COND_CASES_TAC
    THEN simpLib.FULL_SIMP_TAC boolSimps.bool_ss [LLEN]
    THEN ALL_ARITH_TAC));
val () = pr "OK lef_len\n";

val gtf_len = Tactical.prove(
  q "!p l. llen (gt_filter p l) <= llen l",
  Tactic.GEN_TAC THEN byLstInduction(
    simpLib.FULL_SIMP_TAC boolSimps.bool_ss [GTF, LLEN]
    THEN Tactical.TRY Tactic.COND_CASES_TAC
    THEN simpLib.FULL_SIMP_TAC boolSimps.bool_ss [LLEN]
    THEN ALL_ARITH_TAC));
val () = pr "OK gtf_len\n";

(* qsort via tDefine, measure (llen).  Termination: the two recursive calls are
   on le_filter/gt_filter of the tail t, each of which has llen <= llen t <
   llen (Cons h t).  After WF_REL_TAC unfold measure, then close with the
   filter-length bounds + arithmetic. *)
val (QSORT, _) = TotalDefn.tDefine "qsort"
   [QUOTE "(qsort Nil = Nil) /\\ (qsort (Cons h t) = append (qsort (le_filter h t)) (Cons h (qsort (gt_filter h t))))"]
   (TotalDefn.WF_REL_TAC [QUOTE "measure llen"]
      THEN Rewrite.REWRITE_TAC [prim_recTheory.measure_thm, LLEN]
      THEN Tactical.REPEAT Tactic.STRIP_TAC
      THENL [ Tactic.MP_TAC (Q.SPECL [[QUOTE "h:num"],[QUOTE "t:lst"]] gtf_len) THEN ALL_ARITH_TAC,
              Tactic.MP_TAC (Q.SPECL [[QUOTE "h:num"],[QUOTE "t:lst"]] lef_len) THEN ALL_ARITH_TAC ]);
val qsort_ind = #2 (valOf (List.find (fn (n,_) => n = "qsort_ind")
                  (Theory.current_theorems () @ Theory.current_definitions ())));
val () = pr "QSORT_DEF_OK\n";

(* ============================================================== *)
(* === HEADLINE 1 : PERMUTATION (qsort preserves the multiset)  === *)
(* ============================================================== *)

(* count_append: count x (append a b) = count x a + count x b.  Induct on a,
   keeping b,x general; the IH (!b x. ...) is then in scope for ASM_REWRITE. *)
val count_append = Tactical.prove(
  q "!a b x. count x (append a b) = count x a + count x b",
  Tactic.HO_MATCH_MP_TAC lst_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Rewrite.ASM_REWRITE_TAC[APPEND, COUNT] THEN
  ARITH_TAC);
val () = pr "OK count_append\n";

(* filter_count: the two partitions together preserve the count.  Induct on l;
   each COND_CASES (a<=p vs p<a) leaves count atoms that arithmetic closes once
   the IH (specialised to p,x) and the pure-numeric case conditions are lifted.
   In the contradictory COND combinations the numeric assumptions are
   inconsistent, so ARITH closes regardless of the count atoms. *)
val filter_count = Tactical.prove(
  q "!l p x. count x (le_filter p l) + count x (gt_filter p l) = count x l",
  Tactic.HO_MATCH_MP_TAC lst_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THENL
  [ Rewrite.REWRITE_TAC[LEF, GTF, COUNT] THEN ARITH_TAC,
    Rewrite.REWRITE_TAC[LEF, GTF] THEN
    Tactical.REPEAT Tactic.COND_CASES_TAC THEN
    Rewrite.REWRITE_TAC[COUNT] THEN
    Tactical.TRY (Tactical.FIRST_X_ASSUM
        (fn ih => Tactic.MP_TAC (Q.SPECL [[QUOTE "p:num"],[QUOTE "x:num"]] ih))) THEN
    ALL_ARITH_TAC ]);
val () = pr "OK filter_count\n";

(* qsort_count: by the qsort recursion-induction.  After qsort_ind the Nil case
   self-closes under REWRITE[QSORT]; the single Cons goal is
     count x (append (qsort (le_filter h t)) (Cons h (qsort (gt_filter h t))))
       = count x (Cons h t)
   with the two IHs in scope.  Push count through append (count_append) and the
   pivot Cons (COUNT), rewrite both recursive sorts away via the IHs
   (ASM_REWRITE), specialise filter_count to (t,h,x), and close arithmetically. *)
val qsort_count = Tactical.prove(
  q "!l x. count x (qsort l) = count x l",
  Tactic.HO_MATCH_MP_TAC qsort_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Rewrite.REWRITE_TAC[QSORT] THEN
  Rewrite.ASM_REWRITE_TAC[count_append, COUNT] THEN
  Tactic.MP_TAC (Q.SPECL [[QUOTE "t:lst"],[QUOTE "h:num"],[QUOTE "x:num"]] filter_count) THEN
  ARITH_TAC);
val _ = Theory.save_thm("qsort_count", qsort_count);
val () = pr (Parse.thm_to_string qsort_count ^ "\n");
val () = pr ("qsort_count hyps=" ^ Int.toString (List.length (Thm.hyp qsort_count)) ^ "\n");
val () = pr "OK qsort_count\n";
val () = pr "PERMUTATION_DONE\n";

(* ============================================================== *)
(* === HEADLINE 2 : SORTEDNESS (qsort outputs a sorted list)   === *)
(* ============================================================== *)

(* leall_append: leall x distributes over append.  Induct on a (append reduces
   structurally on its first arg), keeping b,x general. *)
val leall_append = Tactical.prove(
  q "!a b x. leall x (append a b) <=> leall x a /\\ leall x b",
  Tactic.HO_MATCH_MP_TAC lst_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Rewrite.ASM_REWRITE_TAC[APPEND, LEALL, boolTheory.CONJ_ASSOC]);
val () = pr "OK leall_append\n";

(* le_filter / gt_filter give the pivot bounds:
   - every elt of le_filter p l is <= p   (geall p (le_filter p l))
   - every elt of gt_filter p l is >  p, hence p <= it (leall p (gt_filter p l)) *)
val geall_lef = Tactical.prove(
  q "!l p. geall p (le_filter p l)",
  byLstInduction(
    simpLib.FULL_SIMP_TAC boolSimps.bool_ss [LEF]
    THEN Tactical.TRY Tactic.COND_CASES_TAC
    THEN simpLib.FULL_SIMP_TAC boolSimps.bool_ss [GEALL]
    THEN Rewrite.ASM_REWRITE_TAC[]));
val () = pr "OK geall_lef\n";

val leall_gtf = Tactical.prove(
  q "!l p. leall p (gt_filter p l)",
  byLstInduction(
    simpLib.FULL_SIMP_TAC boolSimps.bool_ss [GTF]
    THEN Tactical.TRY Tactic.COND_CASES_TAC
    THEN simpLib.FULL_SIMP_TAC boolSimps.bool_ss [LEALL]
    THEN Rewrite.ASM_REWRITE_TAC[]
    THEN ASM_ARITH_TAC));
val () = pr "OK leall_gtf\n";

(* geall_append: geall x distributes over append.  Induct on a. *)
val geall_append = Tactical.prove(
  q "!a b x. geall x (append a b) <=> geall x a /\\ geall x b",
  Tactic.HO_MATCH_MP_TAC lst_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Rewrite.ASM_REWRITE_TAC[APPEND, GEALL, boolTheory.CONJ_ASSOC]);
val () = pr "OK geall_append\n";

(* filter sublists preserve a global bound (a bound on l bounds le_filter/
   gt_filter of l, since they only drop elements). *)
val leall_lef = Tactical.prove(
  q "!l x p. leall x l ==> leall x (le_filter p l)",
  byLstInduction(
    simpLib.FULL_SIMP_TAC boolSimps.bool_ss [LEF, LEALL]
    THEN Tactical.REPEAT Tactic.STRIP_TAC
    THEN Tactical.TRY Tactic.COND_CASES_TAC
    THEN simpLib.FULL_SIMP_TAC boolSimps.bool_ss [LEALL]
    THEN Tactical.REPEAT Tactic.CONJ_TAC
    THEN Tactical.TRY (Tactical.FIRST_X_ASSUM Tactic.MATCH_MP_TAC THEN Rewrite.ASM_REWRITE_TAC[])
    THEN Rewrite.ASM_REWRITE_TAC[]));
val () = pr "OK leall_lef\n";

val leall_gtf2 = Tactical.prove(
  q "!l x p. leall x l ==> leall x (gt_filter p l)",
  byLstInduction(
    simpLib.FULL_SIMP_TAC boolSimps.bool_ss [GTF, LEALL]
    THEN Tactical.REPEAT Tactic.STRIP_TAC
    THEN Tactical.TRY Tactic.COND_CASES_TAC
    THEN simpLib.FULL_SIMP_TAC boolSimps.bool_ss [LEALL]
    THEN Tactical.REPEAT Tactic.CONJ_TAC
    THEN Tactical.TRY (Tactical.FIRST_X_ASSUM Tactic.MATCH_MP_TAC THEN Rewrite.ASM_REWRITE_TAC[])
    THEN Rewrite.ASM_REWRITE_TAC[]));
val () = pr "OK leall_gtf2\n";

val geall_lef2 = Tactical.prove(
  q "!l x p. geall x l ==> geall x (le_filter p l)",
  byLstInduction(
    simpLib.FULL_SIMP_TAC boolSimps.bool_ss [LEF, GEALL]
    THEN Tactical.REPEAT Tactic.STRIP_TAC
    THEN Tactical.TRY Tactic.COND_CASES_TAC
    THEN simpLib.FULL_SIMP_TAC boolSimps.bool_ss [GEALL]
    THEN Tactical.REPEAT Tactic.CONJ_TAC
    THEN Tactical.TRY (Tactical.FIRST_X_ASSUM Tactic.MATCH_MP_TAC THEN Rewrite.ASM_REWRITE_TAC[])
    THEN Rewrite.ASM_REWRITE_TAC[]));
val () = pr "OK geall_lef2\n";

val geall_gtf2 = Tactical.prove(
  q "!l x p. geall x l ==> geall x (gt_filter p l)",
  byLstInduction(
    simpLib.FULL_SIMP_TAC boolSimps.bool_ss [GTF, GEALL]
    THEN Tactical.REPEAT Tactic.STRIP_TAC
    THEN Tactical.TRY Tactic.COND_CASES_TAC
    THEN simpLib.FULL_SIMP_TAC boolSimps.bool_ss [GEALL]
    THEN Tactical.REPEAT Tactic.CONJ_TAC
    THEN Tactical.TRY (Tactical.FIRST_X_ASSUM Tactic.MATCH_MP_TAC THEN Rewrite.ASM_REWRITE_TAC[])
    THEN Rewrite.ASM_REWRITE_TAC[]));
val () = pr "OK geall_gtf2\n";

(* leall_qsort: a lower bound on the input is a lower bound on the output. *)
val leall_qsort = Tactical.prove(
  q "!l x. leall x l ==> leall x (qsort l)",
  Tactic.HO_MATCH_MP_TAC qsort_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Rewrite.REWRITE_TAC[QSORT] THENL
  [ Rewrite.REWRITE_TAC[LEALL],
    simpLib.FULL_SIMP_TAC boolSimps.bool_ss [LEALL] THEN
    Rewrite.REWRITE_TAC[leall_append, LEALL] THEN
    Tactical.REPEAT Tactic.CONJ_TAC THENL
    [ (* leall x (qsort (le_filter h t)) *)
      Tactical.FIRST_X_ASSUM Tactic.MATCH_MP_TAC THEN
      Tactic.MATCH_MP_TAC leall_lef THEN Rewrite.ASM_REWRITE_TAC[],
      (* x <= h *)
      Rewrite.ASM_REWRITE_TAC[],
      (* leall x (qsort (gt_filter h t)) *)
      Tactical.FIRST_X_ASSUM Tactic.MATCH_MP_TAC THEN
      Tactic.MATCH_MP_TAC leall_gtf2 THEN Rewrite.ASM_REWRITE_TAC[] ] ]);
val () = pr "OK leall_qsort\n";

(* geall_qsort: an upper bound on the input is an upper bound on the output. *)
val geall_qsort = Tactical.prove(
  q "!l x. geall x l ==> geall x (qsort l)",
  Tactic.HO_MATCH_MP_TAC qsort_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Rewrite.REWRITE_TAC[QSORT] THENL
  [ Rewrite.REWRITE_TAC[GEALL],
    simpLib.FULL_SIMP_TAC boolSimps.bool_ss [GEALL] THEN
    Rewrite.REWRITE_TAC[geall_append, GEALL] THEN
    Tactical.REPEAT Tactic.CONJ_TAC THENL
    [ Tactical.FIRST_X_ASSUM Tactic.MATCH_MP_TAC THEN
      Tactic.MATCH_MP_TAC geall_lef2 THEN Rewrite.ASM_REWRITE_TAC[],
      Rewrite.ASM_REWRITE_TAC[],
      Tactical.FIRST_X_ASSUM Tactic.MATCH_MP_TAC THEN
      Tactic.MATCH_MP_TAC geall_gtf2 THEN Rewrite.ASM_REWRITE_TAC[] ] ]);
val () = pr "OK geall_qsort\n";

(* leall_trans: lower a list's lower bound through <=. *)
val leall_trans = Tactical.prove(
  q "!l y z. y <= z /\\ leall z l ==> leall y l",
  byLstInduction(
    Tactical.TRY(simpLib.FULL_SIMP_TAC boolSimps.bool_ss [LEALL])
    THEN Rewrite.ASM_REWRITE_TAC[LEALL]
    THEN Tactical.REPEAT Tactic.CONJ_TAC
    THEN Tactical.TRY (Tactical.FIRST_X_ASSUM Tactic.MATCH_MP_TAC THEN
                       Tactic.EXISTS_TAC (q "z:num") THEN Rewrite.ASM_REWRITE_TAC[])
    THEN Tactical.TRY ASM_ARITH_TAC));
val () = pr "OK leall_trans\n";

(* sorted_append: induct on a (append reduces on its first arg).  Nil case
   self-closes.  In the Cons (n :: a) case, expand the Cons-wrapped hyps
   sorted (Cons n a) -> leall n a /\ sorted a and geall p (Cons n a) -> n<=p /\
   geall p a (FULL_SIMP[SORTED,GEALL]), then the goal
     sorted (Cons n (append a (Cons p b)))
   = leall n (append a (Cons p b)) /\ sorted (append a (Cons p b)).
   leall n (append ..) splits (leall_append + LEALL) into leall n a (have),
   n<=p (have) and leall n b (= leall_trans n<=p, leall p b); sorted (append ..)
   is the IH. *)
val sorted_append = Tactical.prove(
  q "!a b p. sorted a /\\ sorted b /\\ geall p a /\\ leall p b ==> sorted (append a (Cons p b))",
  Tactic.HO_MATCH_MP_TAC lst_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  simpLib.FULL_SIMP_TAC boolSimps.bool_ss [APPEND, SORTED, GEALL] THEN
  Rewrite.ASM_REWRITE_TAC[SORTED, leall_append, LEALL] THEN
  Tactical.REPEAT Tactic.CONJ_TAC THEN
  Tactical.TRY (Tactic.MATCH_MP_TAC leall_trans THEN Tactic.EXISTS_TAC (q "p:num") THEN
                Rewrite.ASM_REWRITE_TAC[]) THEN
  Tactical.TRY (Tactical.FIRST_X_ASSUM Tactic.MATCH_MP_TAC THEN Rewrite.ASM_REWRITE_TAC[]) THEN
  Rewrite.ASM_REWRITE_TAC[]);
val () = pr "OK sorted_append\n";

(* qsort_sorted: the main event.  By qsort_ind.  Nil is trivially sorted; for
   Cons h t, qsort (Cons h t) = append (qsort (le_filter h t)) (Cons h (qsort
   (gt_filter h t))).  Apply sorted_append with p=h: both recursive sorts are
   sorted (the two IHs), and the bounds:
     geall h (qsort (le_filter h t))  — from geall_qsort + geall_lef (everything
        in le_filter h t is <= h)
     leall h (qsort (gt_filter h t))  — from leall_qsort + leall_gtf. *)
val qsort_sorted = Tactical.prove(
  q "!l. sorted (qsort l)",
  Tactic.HO_MATCH_MP_TAC qsort_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Rewrite.REWRITE_TAC[QSORT] THENL
  [ Rewrite.REWRITE_TAC[SORTED],
    Tactic.MATCH_MP_TAC sorted_append THEN
    Rewrite.ASM_REWRITE_TAC[] THEN
    Tactical.REPEAT Tactic.CONJ_TAC THENL
    [ (* geall h (qsort (le_filter h t)) — geall_qsort on geall_lef(t,h) *)
      Tactic.MATCH_MP_TAC geall_qsort THEN
      Rewrite.REWRITE_TAC[Q.SPECL [[QUOTE "t:lst"],[QUOTE "h:num"]] geall_lef],
      (* leall h (qsort (gt_filter h t)) — leall_qsort on leall_gtf(t,h) *)
      Tactic.MATCH_MP_TAC leall_qsort THEN
      Rewrite.REWRITE_TAC[Q.SPECL [[QUOTE "t:lst"],[QUOTE "h:num"]] leall_gtf] ] ]);
val _ = Theory.save_thm("qsort_sorted", qsort_sorted);
val () = pr (Parse.thm_to_string qsort_sorted ^ "\n");
val () = pr ("qsort_sorted hyps=" ^ Int.toString (List.length (Thm.hyp qsort_sorted)) ^ "\n");
val () = pr "OK qsort_sorted\n";
val () = pr "SORTEDNESS_DONE\n";

(* ============================================================== *)
(* === EVAL: actually RUN the verified algorithm via computeLib === *)
(* === CBV (kernel-checked).  qsort recurses on filtered tails;  === *)
(* === the equations are structural-on-the-argument once the     === *)
(* === filters reduce, so CBV over the compset + our equations    === *)
(* === fires directly (no fuel gymnastics needed).               === *)
val cs = computeLib.copy (!computeLib.the_compset);
val _ = computeLib.add_thms [APPEND, LEF, GTF, QSORT] cs;
val () = (let
    val th  = computeLib.CBV_CONV cs
                (q "qsort (Cons 3 (Cons 1 (Cons 4 (Cons 1 (Cons 5 (Cons 9 (Cons 2 (Cons 6 Nil))))))))")
    val () = pr ("  EVAL qsort = " ^ Parse.term_to_string (rhs (concl th)) ^ "\n")
    val expected = q "Cons 1 (Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 5 (Cons 6 (Cons 9 Nil)))))))"
  in if Term.aconv (rhs (concl th)) expected then pr "EVAL_QSORT_OK\n" else pr "EVAL_QSORT_WRONG\n" end)
  handle e => pr ("EVAL EXN: " ^ General.exnMessage e ^ "\n");

val () = pr "QSORT_DONE\n";
