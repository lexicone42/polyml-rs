(* merge_sort_verified.sml — VERIFIED MERGE SORT on HOL4's real LCF kernel,
   running on the Rust PolyML interpreter (/tmp/hol4_datatype).  NO listTheory:
   we define our own num-list `lst = Nil | Cons num lst`.

   Structural trick: a FUEL parameter makes the top-level merge-sort recursion
   structural (msortn recurses SUC n -> n), so plain Define needs no termination
   proof.  `merge` is the one genuinely non-structural function
   (tDefine + measure (len xs + len ys)); `split` returns a pair so its recursive
   calls hide inside FST/SND where Define's auto-termination can't see the
   structural decrease, so it too uses tDefine (measure len).

   HEADLINE 1 (REQUIRED): msort_count : |- !z l. count z (msort l) = count z l
     (msort is a PERMUTATION of its input — preserves the multiset).
   HEADLINE 2 (BONUS):     msort_sorted : |- !l. sorted (msort l)
     (msort outputs a SORTED list). *)

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
(* num induction = INDUCT_TAC (induct on the fuel) *)
val INDUCT_TAC = Prim_rec.INDUCT_THEN numTheory.INDUCTION Tactic.ASSUME_TAC;
val () = pr "DATATYPE_OK\n";

(* A selective arithmetic closer: lift only the assumptions that mention NONE of
   our list/predicate constants (so the count/leall/sorted IHs aren't dumped into
   the goal, which would make it non-arithmetic), then call the closed-arithmetic
   decision procedure ARITH (= EQT_ELIM o ARITH_CONV, which ignores assumptions). *)
val blocked = ["leall","sorted","count","merge","split","msortn","msort","Cons","Nil"];
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
(* A non-selective variant: lift ALL assumptions.  Used where the IH is itself a
   linear (in)equality over opaque len/count atoms (split_len) and MUST be lifted. *)
val ALL_ARITH_TAC : Tactic.tactic =
  fn (asl,w) =>
    (Tactical.MAP_EVERY (fn a => Tactic.MP_TAC (Thm.ASSUME a)) asl THEN ARITH_TAC) (asl,w);

(* === DEFINITIONS === *)
val LEN   = TotalDefn.Define [QUOTE "(len Nil = 0) /\\ (len (Cons a l) = SUC (len l))"];
val LEALL = TotalDefn.Define [QUOTE "(leall x Nil = T) /\\ (leall x (Cons a l) = ((x <= a) /\\ leall x l))"];
val SORTED= TotalDefn.Define [QUOTE "(sorted Nil = T) /\\ (sorted (Cons a l) = (leall a l /\\ sorted l))"];
val COUNT = TotalDefn.Define [QUOTE "(count x Nil = 0) /\\ (count x (Cons a l) = (if x = a then 1 else 0) + count x l)"];
val () = pr "BASIC_DEFS_OK\n";

(* merge via tDefine, measure (len xs + len ys).  Termination: after WF_REL_TAC
   the measure must be unfolded (measure_thm), the PAIRED lambda beta-reduced
   (pairLib.PAIRED_BETA_CONV — plain FST/SND rewrites do NOT reduce a (\(x,y).e)
   application), then LEN rewrites and the leftover is linear -> ARITH_TAC. *)
val (MERGE, _) = TotalDefn.tDefine "merge"
   [QUOTE "(merge Nil ys = ys) /\\ (merge (Cons a xs) Nil = Cons a xs) /\\ (merge (Cons a xs) (Cons b ys) = if a <= b then Cons a (merge xs (Cons b ys)) else Cons b (merge (Cons a xs) ys))"]
   (TotalDefn.WF_REL_TAC [QUOTE "measure (\\(xs,ys). len xs + len ys)"]
      THEN Rewrite.REWRITE_TAC [prim_recTheory.measure_thm]
      THEN Tactic.CONV_TAC (Conv.DEPTH_CONV pairLib.PAIRED_BETA_CONV)
      THEN Rewrite.REWRITE_TAC [LEN]
      THEN Tactical.REPEAT Tactic.STRIP_TAC
      THEN ARITH_TAC);
val merge_ind = #2 (valOf (List.find (fn (n,_) => n = "merge_ind")
                  (Theory.current_theorems () @ Theory.current_definitions ())));
val () = pr "MERGE_OK\n";

(* split: recurses on l two-at-a-time.  Returns a pair, so the recursive calls
   sit inside FST/SND and Define's auto-termination can't see the structural
   decrease — use tDefine with measure len. *)
val (SPLIT, _) = TotalDefn.tDefine "split"
   [QUOTE "(split Nil = (Nil, Nil)) /\\ (split (Cons a Nil) = (Cons a Nil, Nil)) /\\ (split (Cons a (Cons b l)) = (Cons a (FST (split l)), Cons b (SND (split l))))"]
   (TotalDefn.WF_REL_TAC [QUOTE "measure len"]
      THEN Rewrite.REWRITE_TAC [prim_recTheory.measure_thm, LEN]
      THEN Tactical.REPEAT Tactic.STRIP_TAC
      THEN ARITH_TAC);
val split_ind = #2 (valOf (List.find (fn (n,_) => n = "split_ind")
                  (Theory.current_theorems () @ Theory.current_definitions ())));
val () = pr "SPLIT_OK\n";

(* fuel-based merge sort.  msortn is structural on n -> plain Define, no
   termination proof.  msort seeds the fuel with len l (always enough). *)
val MSORTN = TotalDefn.Define
   [QUOTE "(msortn 0 l = l) /\\ (msortn (SUC n) l = (if len l <= 1 then l else merge (msortn n (FST (split l))) (msortn n (SND (split l)))))"];
val MSORT = TotalDefn.Define [QUOTE "msort l = msortn (len l) l"];
val () = pr "MSORT_DEFS_OK\n";

(* ============================================================== *)
(* === HEADLINE 1 : PERMUTATION (msort preserves the multiset) === *)
(* ============================================================== *)

(* merge_count: count z (merge xs ys) = count z xs + count z ys.  By merge_ind.
   After COND_CASES on a<=b, the conditional induction hypotheses
   (a<=b ==> ... / ~(a<=b) ==> ...) must be discharged with RES_TAC before
   ASM_REWRITE[COUNT] can fire them; ARITH closes the linear remainder. *)
val merge_count = Tactical.prove(
  q "!xs ys z. count z (merge xs ys) = count z xs + count z ys",
  Tactic.HO_MATCH_MP_TAC merge_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Rewrite.REWRITE_TAC[MERGE] THEN
  Tactical.TRY Tactic.COND_CASES_TAC THEN
  Tactical.TRY Tactic.RES_TAC THEN
  Rewrite.ASM_REWRITE_TAC[COUNT] THEN
  ARITH_TAC);
val () = pr "OK merge_count\n";

(* split_count: count z (FST (split l)) + count z (SND (split l)) = count z l.
   By split_ind (Nil / Cons a Nil / Cons a (Cons b l)).  The IH is `!z. ...`, so
   it must be SPECIALIZED to z and lifted into the goal (ARITH is assumption-blind
   and the count-terms are opaque atoms) before ARITH closes the linear goal. *)
val split_count = Tactical.prove(
  q "!l z. count z (FST (split l)) + count z (SND (split l)) = count z l",
  Tactic.HO_MATCH_MP_TAC split_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Rewrite.ASM_REWRITE_TAC[SPLIT, COUNT, pairTheory.FST, pairTheory.SND] THEN
  Tactical.TRY (Tactical.FIRST_X_ASSUM (fn ih => Tactic.MP_TAC (Q.SPEC [QUOTE "z:num"] ih))) THEN
  ARITH_TAC);
val () = pr "OK split_count\n";

(* msortn_count: count z (msortn n l) = count z l.  Induct on the FUEL n,
   GEN l (and z) INSIDE the induction.  Step: COND_CASES on len l <= 1; the
   else-branch is merge_count o (two IHs) o split_count via ASM_REWRITE. *)
val msortn_count = Tactical.prove(
  q "!n l z. count z (msortn n l) = count z l",
  INDUCT_TAC THEN
  Tactical.REPEAT Tactic.GEN_TAC THEN
  Rewrite.REWRITE_TAC[MSORTN] THEN
  Tactical.TRY Tactic.COND_CASES_TAC THEN
  Rewrite.ASM_REWRITE_TAC[merge_count, split_count]);
val () = pr "OK msortn_count\n";

val msort_count = Tactical.prove(
  q "!z l. count z (msort l) = count z l",
  Tactical.REPEAT Tactic.GEN_TAC THEN
  Rewrite.REWRITE_TAC[MSORT, msortn_count]);
val _ = Theory.save_thm("msort_count", msort_count);
val () = pr (Parse.thm_to_string msort_count ^ "\n");
val () = pr ("msort_count hyps=" ^ Int.toString (List.length (Thm.hyp msort_count)) ^ "\n");
val () = pr "OK msort_count\n";
val () = pr "PERMUTATION_DONE\n";

(* ============================================================== *)
(* === HEADLINE 2 : SORTEDNESS (msort outputs a sorted list)   === *)
(* ============================================================== *)

(* leall_merge: merge of two lists each bounded below by x is bounded below by x.
   The conditional merge_ind IHs are discharged by RES_TAC. *)
val leall_merge = Tactical.prove(
  q "!xs ys x. leall x xs /\\ leall x ys ==> leall x (merge xs ys)",
  Tactic.HO_MATCH_MP_TAC merge_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Tactical.TRY (simpLib.FULL_SIMP_TAC boolSimps.bool_ss [LEALL]) THEN
  Rewrite.REWRITE_TAC[MERGE] THEN
  Tactical.TRY Tactic.COND_CASES_TAC THEN
  Tactical.TRY Tactic.RES_TAC THEN
  Rewrite.ASM_REWRITE_TAC[LEALL] THEN
  Tactical.REPEAT Tactic.CONJ_TAC THEN
  Rewrite.ASM_REWRITE_TAC[]);
val () = pr "OK leall_merge\n";

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

(* merge_sorted: merge of two sorted lists is sorted.  Head-bound residuals
   (leall a/b ...) are closed by leall_merge then leall_trans with whichever of
   the two pivots (a,b) is the right witness — FIRST backtracks between them. *)
val close_leall = fn wit =>
  (Tactic.MATCH_MP_TAC leall_trans THEN Tactic.EXISTS_TAC (q wit) THEN
   Rewrite.ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);
val finish_leaf =
  Tactical.FIRST [ Rewrite.ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC,
                   close_leall "a:num", close_leall "b:num",
                   Rewrite.ASM_REWRITE_TAC[] ];
val merge_sorted = Tactical.prove(
  q "!xs ys. sorted xs /\\ sorted ys ==> sorted (merge xs ys)",
  Tactic.HO_MATCH_MP_TAC merge_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Tactical.TRY (simpLib.FULL_SIMP_TAC boolSimps.bool_ss [SORTED]) THEN
  Rewrite.REWRITE_TAC[MERGE] THEN
  Tactical.TRY Tactic.COND_CASES_TAC THEN
  Tactical.TRY Tactic.RES_TAC THEN
  Rewrite.ASM_REWRITE_TAC[SORTED] THEN
  Tactical.REPEAT Tactic.CONJ_TAC THEN
  Tactical.TRY (Tactic.MATCH_MP_TAC leall_merge) THEN
  Rewrite.ASM_REWRITE_TAC[LEALL] THEN
  Tactical.REPEAT Tactic.CONJ_TAC THEN
  Tactical.TRY finish_leaf);
val () = pr "OK merge_sorted\n";

(* split_len: each half is no longer than the whole (IHs are linear, lift ALL). *)
val split_len = Tactical.prove(
  q "!l. len (FST (split l)) <= len l /\\ len (SND (split l)) <= len l",
  Tactic.HO_MATCH_MP_TAC split_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Rewrite.ASM_REWRITE_TAC[SPLIT, LEN, pairTheory.FST, pairTheory.SND] THEN
  ALL_ARITH_TAC);
val () = pr "OK split_len\n";

(* split_len_strict: each half is STRICTLY shorter once the list has >= 2 elements
   (this is what makes the fuel `len l` suffice for the recursion). *)
val split_len_strict = Tactical.prove(
  q "!l. 2 <= len l ==> len (FST (split l)) < len l /\\ len (SND (split l)) < len l",
  Tactic.HO_MATCH_MP_TAC split_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  simpLib.FULL_SIMP_TAC boolSimps.bool_ss [SPLIT, LEN, pairTheory.FST, pairTheory.SND] THEN
  Tactical.TRY (Tactic.MP_TAC (Q.SPEC [QUOTE "l:lst"] split_len)) THEN
  ASM_ARITH_TAC);
val () = pr "OK split_len_strict\n";

(* len_0_nil + short_sorted: a list of length <= 1 (Nil or singleton) is sorted. *)
val len_0_nil = Tactical.prove(
  q "!l. (len l = 0) ==> (l = Nil)",
  Tactic.HO_MATCH_MP_TAC lst_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Tactical.TRY (simpLib.FULL_SIMP_TAC boolSimps.bool_ss [LEN, numTheory.NOT_SUC]) THEN
  Rewrite.ASM_REWRITE_TAC[]);
val short_sorted = Tactical.prove(
  q "!l. len l <= 1 ==> sorted l",
  Tactic.HO_MATCH_MP_TAC lst_ind THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Rewrite.REWRITE_TAC[SORTED] THEN
  Tactical.TRY (
    simpLib.FULL_SIMP_TAC boolSimps.bool_ss [LEN] THEN
    Tactical.SUBGOAL_THEN (q "l = Nil") (fn th => Rewrite.REWRITE_TAC[th, SORTED, LEALL]) THEN
    Tactic.MATCH_MP_TAC len_0_nil THEN
    ALL_ARITH_TAC) THEN
  Rewrite.REWRITE_TAC[SORTED, LEALL]);
val () = pr "OK short_sorted\n";

(* msortn_sorted: enough fuel -> sorted output.  Induct on the FUEL n.
   - base n=0 / step len l<=1: the list is short -> short_sorted.
   - step ~(len l<=1): merge_sorted of the two recursive sorts; each IH precond
     `len(FST/SND(split l)) <= n` follows from split_len_strict (strict <) and
     len l <= SUC n. *)
val msortn_sorted = Tactical.prove(
  q "!n l. len l <= n ==> sorted (msortn n l)",
  INDUCT_TAC THEN
  Tactical.REPEAT Tactic.STRIP_TAC THEN
  Rewrite.REWRITE_TAC[MSORTN] THEN
  Tactical.TRY Tactic.COND_CASES_TAC THENL
  [ Tactic.MATCH_MP_TAC short_sorted THEN ASM_ARITH_TAC,
    Tactic.MATCH_MP_TAC short_sorted THEN ASM_ARITH_TAC,
    Tactic.MATCH_MP_TAC merge_sorted THEN
    Tactic.CONJ_TAC THEN
    Tactical.FIRST_X_ASSUM Tactic.MATCH_MP_TAC THEN
    Tactic.MP_TAC (Q.SPEC [QUOTE "l:lst"] split_len_strict) THEN
    ASM_ARITH_TAC ]);
val () = pr "OK msortn_sorted\n";

val msort_sorted = Tactical.prove(
  q "!l. sorted (msort l)",
  Tactic.GEN_TAC THEN
  Rewrite.REWRITE_TAC[MSORT] THEN
  Tactic.MATCH_MP_TAC msortn_sorted THEN
  Rewrite.REWRITE_TAC[arithmeticTheory.LESS_EQ_REFL]);
val _ = Theory.save_thm("msort_sorted", msort_sorted);
val () = pr (Parse.thm_to_string msort_sorted ^ "\n");
val () = pr ("msort_sorted hyps=" ^ Int.toString (List.length (Thm.hyp msort_sorted)) ^ "\n");
val () = pr "OK msort_sorted\n";
val () = pr "SORTEDNESS_DONE\n";

(* ============================================================== *)
(* === EVAL: RUN the verified algorithm via a kernel-checked     === *)
(* === conversion.  computeLib's CBV won't fire a SUC-pattern    === *)
(* === Define clause (msortn (SUC n)) against a NUMERAL fuel, and === *)
(* === this minimal checkpoint doesn't expose numLib.SUC_RULE,   === *)
(* === so we drive the fuel explicitly: REWRITE msort -> msortn   === *)
(* === (len l) l, CBV the len to a numeral (list-structural, this === *)
(* === DOES fire), then unfold the fuel one SUC at a time with    === *)
(* === Num_conv.num_CONV, normalising merge/split/<= each step.   === *)
(* === Every step is a real theorem, so the result is sound.      === *)
val list_cs = computeLib.copy (!computeLib.the_compset);
val _ = computeLib.add_thms [LEN, MERGE, SPLIT] list_cs;
fun fuelStep th =
  let val exposeOne =
        Conv.ONCE_DEPTH_CONV (fn s =>
          let val (f,args) = strip_comb s
          in if Term.is_const f andalso #1 (Term.dest_const f) = "msortn"
                andalso not (null args) andalso numSyntax.is_numeral (hd args)
                andalso not (hd args ~~ numSyntax.zero_tm)
             then Conv.RATOR_CONV (Conv.RAND_CONV Num_conv.num_CONV) s
             else Conv.NO_CONV s
          end)
      val c = Conv.THENC (exposeOne,
              Conv.THENC (Rewrite.ONCE_REWRITE_CONV [MSORTN],
              Conv.THENC (computeLib.CBV_CONV list_cs, reduceLib.REDUCE_CONV)))
  in Conv.RIGHT_CONV_RULE (Conv.TRY_CONV c) th end;
fun nSteps 0 th = th | nSteps k th = nSteps (k-1) (fuelStep th);
val () = (let
    val th0 = Rewrite.REWRITE_CONV [MSORT]
                (q "msort (Cons 3 (Cons 1 (Cons 2 (Cons 5 (Cons 4 Nil)))))")
    val th1 = Conv.RIGHT_CONV_RULE (computeLib.CBV_CONV list_cs) th0   (* len -> 5 *)
    val th  = nSteps 6 th1
    val () = pr ("  EVAL msort = " ^ Parse.term_to_string (rhs (concl th)) ^ "\n")
    val expected = q "Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 5 Nil))))"
  in if Term.aconv (rhs (concl th)) expected then pr "EVAL_OK\n" else pr "EVAL_WRONG\n" end)
  handle e => pr ("EVAL EXN: " ^ General.exnMessage e ^ "\n");

val () = pr "ALL_DONE\n";
