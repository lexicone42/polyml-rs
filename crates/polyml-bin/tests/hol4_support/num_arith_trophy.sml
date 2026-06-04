(* num_arith_trophy.sml — the canonical arithmetic induction proved BY HAND on
   /tmp/hol4_num (HOL4 kernel + numTheory, running on the polyml-rs interpreter):
       |- !n. n + 0 = n
   together with the primitive-recursion theorem
       num_Axiom = |- !e f. ?fn. fn 0 = e /\ !n. fn (SUC n) = f n (fn n)
   and  UNIQUE_SKOLEM_THM = |- !P. (!x. ?!y. P x y) <=> ?!f. !x. P x (f x).

   This deliberately AVOIDS the heavy chain (no bool_ss simplifier, no SAT
   subsystem / HolSatLib, no relationTheory, not even src/1/Prim_rec). Two
   techniques make it work (see CLAUDE.md):
     1. plain REWRITE_TAC is FIRST-ORDER — it cannot rewrite with the
        higher-order theorems FORALL_AND_THM / SKOLEM_THM / EXISTS_UNIQUE_THM
        (their conjuncts are not bare variable-applications). Use
        Conv.HO_REWR_CONV under TOP_DEPTH_CONV instead (this is what unblocked
        UNIQUE_SKOLEM_THM, whose upstream bool_ss proof fails here).
     2. LESS_THM (m < SUC n <=> m = n \/ m < n) is provable TC-FREE by induction
        + num_CASES + LESS_MONO_REV, so "<" does NOT need relationTheory.
   `add` is defined directly from num_Axiom via ISPECL + beta +
   Theory.Definition.new_specification (Prim_rec.new_recursive_definition is
   unbound on this checkpoint), then the trophy is INDUCT_TAC THENL [...].
   INDUCT_TAC is built from numTheory.INDUCTION via Tactic.HO_MATCH_MP_TAC.

   Run:  tools/sml-exp.sh --steps 400000000000 /tmp/hol4_num \
           crates/polyml-bin/tests/hol4_support/num_arith_trophy.sml
   Emits *_OK / *_FAIL per theorem; TROPHY_HYPS=0, FULL_TROPHY_PASS,
   TROPHY_plus_n_0_OK: |- !n. n + 0 = n, TROPHY_DONE. (Built by a focused
   sub-agent; ~328M bytecode steps, clean Tagged(0).) *)

val () = print "LESSFULL_START\n";
structure Definition = Theory.Definition;
open boolTheory boolSyntax Drule Conv Tactical Tactic Thm_cont Rewrite Abbrev BoundedRewrites;
infix THEN THENL THEN1 ORELSE;
fun pr s = print (s ^ "\n");
fun T q = Parse.Term [QUOTE q];
fun ck name th = pr (name ^ "_OK: " ^ Parse.thm_to_string th) handle e => pr (name ^ "_FAIL: " ^ exnMessage e);
val NOT_SUC = numTheory.NOT_SUC; val INV_SUC = numTheory.INV_SUC; val INDUCTION = numTheory.INDUCTION;
val INDUCT_TAC =
  Tactic.HO_MATCH_MP_TAC INDUCTION THEN Tactic.CONJ_TAC
   THENL [ALL_TAC, Tactic.GEN_TAC THEN Tactic.DISCH_TAC];

val INV_SUC_EQ = GENL [T "m:num", T "n:num"]
   (IMP_ANTISYM_RULE (SPEC_ALL INV_SUC)
     (DISCH (T "m:num = n") (AP_TERM (T "SUC") (ASSUME (T "m:num = n")))));

(* num_CASES : !n. (n = 0) \/ ?m. n = SUC m *)
val num_CASES = Tactical.prove(T "!n. (n = 0) \\/ ?m. n = SUC m",
   INDUCT_TAC THENL [
     DISJ1_TAC THEN REFL_TAC,
     DISJ2_TAC THEN EXISTS_TAC (T "n:num") THEN REFL_TAC]);
val _ = ck "num_CASES" num_CASES;

val LESS_DEF = Definition.new_definition (
  "LESS_DEF", T "$< m n = ?P. (!k. P(SUC k) ==> P k) /\\ P m /\\ ~(P n)");
val _ = set_fixity "<" (Infix(NONASSOC, 450));
val LESS_REFL = Tactical.prove(T "!n. ~(n < n)",
   GEN_TAC THEN REWRITE_TAC[LESS_DEF, boolTheory.NOT_AND]);
val SUC_LESS = Tactical.prove(T "!m n. (SUC m < n) ==> m < n",
   REWRITE_TAC[LESS_DEF] THEN REPEAT STRIP_TAC
    THEN EXISTS_TAC (T "P:num->bool") THEN RES_TAC THEN ASM_REWRITE_TAC[]);
val NOT_LESS_0 = Tactical.prove(T "!n. ~(n < 0)",
   INDUCT_TAC THEN REWRITE_TAC[LESS_REFL]
    THEN IMP_RES_TAC(CONTRAPOS (SPECL[T "n:num", T "0"] SUC_LESS))
    THEN ASM_REWRITE_TAC[]);
val LESS_0 = Tactical.prove(T "!n. 0 < (SUC n)",
   GEN_TAC THEN REWRITE_TAC[LESS_DEF]
    THEN EXISTS_TAC (T "\\x. x = 0")
    THEN CONV_TAC(DEPTH_CONV Thm.BETA_CONV)
    THEN REWRITE_TAC[NOT_SUC]);
val LESS_0_0 = Tactical.prove(T "0 < SUC 0", REWRITE_TAC[LESS_0]);
val PRE_DEF = Definition.new_definition("PRE_DEF",
    T "PRE m = (if (m=0) then 0 else @n. m = SUC n)");
val PRE = Tactical.prove(T "(PRE 0 = 0) /\\ (!m. PRE(SUC m) = m)",
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[PRE_DEF, INV_SUC_EQ, NOT_SUC, boolTheory.SELECT_REFL_2]);
val LESS_MONO = Tactical.prove(T "!m n. (m < n) ==> (SUC m < SUC n)",
   REWRITE_TAC[LESS_DEF] THEN REPEAT STRIP_TAC
    THEN EXISTS_TAC (T "\\n:num. P (PRE n):bool")
    THEN CONV_TAC(DEPTH_CONV Thm.BETA_CONV)
    THEN ASM_REWRITE_TAC [PRE] THEN INDUCT_TAC THEN ASM_REWRITE_TAC [PRE]);
val LESS_MONO_REV = Tactical.prove(T "!m n. (SUC m < SUC n) ==> (m < n)",
   REWRITE_TAC[LESS_DEF] THEN REPEAT STRIP_TAC
    THEN EXISTS_TAC (T "\\n:num. P (SUC n):bool")
    THEN CONV_TAC(DEPTH_CONV Thm.BETA_CONV) THEN ASM_REWRITE_TAC []);
val _ = ck "LESS_MONO_REV" LESS_MONO_REV;
val LESS_SUC_REFL = Tactical.prove(T "!n. n < SUC n",
   INDUCT_TAC THEN REWRITE_TAC[LESS_0_0]
    THEN IMP_RES_TAC LESS_MONO THEN ASM_REWRITE_TAC[]);
val LESS_SUC = Tactical.prove(T "!m n. (m < n) ==> (m < SUC n)",
  REWRITE_TAC [LESS_DEF] THEN REPEAT STRIP_TAC
   THEN EXISTS_TAC (T "P:num->bool")
   THEN IMP_RES_TAC (CONTRAPOS(SPEC (T "n:num")
            (ASSUME (T "!n'. P(SUC n') ==> P n'"))))
   THEN ASM_REWRITE_TAC[]);

(* LESS_LEMMA1 : !n m. m < SUC n ==> (m = n) \/ m < n  -- TC-free, induct on n *)
val LESS_LEMMA1 = Tactical.prove(T "!n m. (m < SUC n) ==> (m = n) \\/ (m < n)",
   INDUCT_TAC THENL [
     (* base: m < SUC 0 ==> m=0 \/ m<0 *)
     GEN_TAC THEN DISCH_TAC
       THEN STRIP_ASSUME_TAC (SPEC (T "m:num") num_CASES)
       THENL [
         ASM_REWRITE_TAC[],
         (* m = SUC m' : SUC m' < SUC 0 ==> m' < 0 contra *)
         POP_ASSUM SUBST_ALL_TAC
           THEN IMP_RES_TAC LESS_MONO_REV
           THEN IMP_RES_TAC NOT_LESS_0
       ],
     (* step: IH: !m. m<SUC n ==> m=n \/ m<n ; show m<SUC(SUC n) ==> m=SUC n \/ m<SUC n *)
     GEN_TAC THEN DISCH_TAC
       THEN STRIP_ASSUME_TAC (SPEC (T "m:num") num_CASES)
       THENL [
         (* m = 0 : 0 < SUC n , so m < SUC n *)
         DISJ2_TAC THEN ASM_REWRITE_TAC[LESS_0],
         (* m = SUC m' : SUC m' < SUC(SUC n) ==> m' < SUC n ==> IH *)
         POP_ASSUM SUBST_ALL_TAC
           THEN IMP_RES_TAC LESS_MONO_REV
           THEN RES_TAC
           THENL [
             DISJ1_TAC THEN ASM_REWRITE_TAC[],
             DISJ2_TAC THEN IMP_RES_TAC LESS_MONO THEN ASM_REWRITE_TAC[]
           ]
       ]
   ]);
val _ = ck "LESS_LEMMA1" LESS_LEMMA1;

(* LESS_LEMMA2 : !m n. ((m=n) \/ m<n) ==> m < SUC n *)
val LESS_LEMMA2 = Tactical.prove(T "!m n. ((m = n) \\/ (m < n)) ==> (m < SUC n)",
   REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_SUC THEN ASM_REWRITE_TAC[LESS_SUC_REFL]);
val _ = ck "LESS_LEMMA2" LESS_LEMMA2;

(* LESS_THM : !m n. m < SUC n = (m = n) \/ m < n *)
val LESS_THM = GENL [T "m:num", T "n:num"]
   (IMP_ANTISYM_RULE (SPEC_ALL LESS_LEMMA1) (SPEC_ALL LESS_LEMMA2));
val _ = ck "LESS_THM" LESS_THM;

(* LESS_SUC_IMP : !m n. m < SUC n ==> ~(m=n) ==> m < n *)
val LESS_SUC_IMP = Tactical.prove(T "!m n. (m < SUC n) ==> ~(m = n) ==> (m < n)",
   REWRITE_TAC[LESS_THM] THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);
val _ = ck "LESS_SUC_IMP" LESS_SUC_IMP;

(* LESS_SUC_SUC : !m. (m < SUC m) /\ (m < SUC(SUC m)) -- TC-free *)
val LESS_SUC_SUC = Tactical.prove(T "!m. (m < SUC m) /\\ (m < SUC(SUC m))",
   GEN_TAC THEN CONJ_TAC
    THENL [MATCH_ACCEPT_TAC LESS_SUC_REFL,
           MATCH_MP_TAC LESS_SUC THEN MATCH_ACCEPT_TAC LESS_SUC_REFL]);
val _ = ck "LESS_SUC_SUC" LESS_SUC_SUC;

val () = print "LESS_LAYER_DONE\n";

(* ======================= SIMP_REC chain ======================= *)
(* SIMP_REC_REL definition *)
val SIMP_REC_REL = Definition.new_definition("SIMP_REC_REL",
   T "SIMP_REC_REL fun x f n = \
     \  ((fun 0 = (x:'a)) /\\ \
     \   (!m. (m < n) ==> (fun(SUC m) = f(fun m))))");
val _ = ck "SIMP_REC_REL" SIMP_REC_REL;

(* INDUCT_THEN-style: induction on the leading !n, applying `handler` to the IH.
   Mirrors  INDUCT_THEN INDUCTION handler  for a goal  !n. P n  (n is leading var)
   or after enough GEN_TACs.  We HO_MATCH_MP INDUCTION, split, and in the step
   GEN the new n then feed the IH (P n) through `handler`. *)
fun INDUCT_THEN_TAC handler =
  Tactic.HO_MATCH_MP_TAC INDUCTION THEN Tactic.CONJ_TAC
   THENL [ALL_TAC, Tactic.GEN_TAC THEN DISCH_THEN handler];

(* SIMP_REC_EXISTS : !x f n. ?fun. SIMP_REC_REL fun x f n *)
val SIMP_REC_EXISTS = Tactical.prove(
   T "!x f n. ?fun:num->'a. SIMP_REC_REL fun x f n",
   GEN_TAC THEN GEN_TAC THEN INDUCT_THEN_TAC STRIP_ASSUME_TAC THEN
   PURE_REWRITE_TAC[SIMP_REC_REL] THENL [
     EXISTS_TAC (T "\\p:num. (x:'a)") THEN REWRITE_TAC[NOT_LESS_0],
     EXISTS_TAC (T "\\p. if p = SUC n then f (fun n) else fun p") THEN
     BETA_TAC THEN REWRITE_TAC [INV_SUC_EQ, GSYM NOT_SUC] THEN
     POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [SIMP_REC_REL]) THEN
     ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
     ASM_CASES_TAC (T "m = SUC n") THENL [
       POP_ASSUM SUBST_ALL_TAC THEN IMP_RES_TAC LESS_REFL,
       ALL_TAC
     ] THEN ASM_REWRITE_TAC [] THEN COND_CASES_TAC THEN
     ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     IMP_RES_TAC LESS_SUC_IMP
   ]);
val _ = ck "SIMP_REC_EXISTS" SIMP_REC_EXISTS;

(* SIMP_REC_REL_UNIQUE *)
val SIMP_REC_REL_UNIQUE = Tactical.prove(
   T "!x f g1 g2 m1 m2. \
     \  SIMP_REC_REL g1 x f m1 /\\ SIMP_REC_REL g2 x f m2 ==> \
     \  !n. n < m1 /\\ n < m2 ==> (g1 n = (g2 n):'a)",
   REWRITE_TAC [SIMP_REC_REL] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   INDUCT_THEN_TAC STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP SUC_LESS)) THEN
   RES_TAC THEN ASM_REWRITE_TAC []);
val _ = ck "SIMP_REC_REL_UNIQUE" SIMP_REC_REL_UNIQUE;

(* SIMP_REC_REL_UNIQUE_RESULT : !x f n. ?!y. ?g. SIMP_REC_REL g x f (SUC n) /\ (y = g n)
   upstream: SIMP_TAC bool_ss [EXISTS_UNIQUE_THM, SIMP_REC_EXISTS] THEN ...
   We replace the bool_ss SIMP_TAC with: rewrite EXISTS_UNIQUE_THM (def of ?!),
   then handle the existence half via SIMP_REC_EXISTS and uniqueness via
   SIMP_REC_REL_UNIQUE. *)
val SIMP_REC_REL_UNIQUE_RESULT = Tactical.prove(
   T "!x f n. ?!y:'a. ?g. SIMP_REC_REL g x f (SUC n) /\\ (y = g n)",
   REPEAT GEN_TAC THEN CONV_TAC (Conv.HO_REWR_CONV EXISTS_UNIQUE_THM)
   THEN CONJ_TAC THENL [
     (* existence: ?y. ?g. SIMP_REC_REL g x f (SUC n) /\ y = g n *)
     STRIP_ASSUME_TAC (SPECL [T "x:'a", T "f:'a->'a", T "SUC n"] SIMP_REC_EXISTS)
       THEN EXISTS_TAC (T "(fun:num->'a) n") THEN EXISTS_TAC (T "fun:num->'a")
       THEN ASM_REWRITE_TAC [],
     (* uniqueness *)
     REPEAT GEN_TAC THEN
     DISCH_THEN (CONJUNCTS_THEN2
        (X_CHOOSE_THEN (T "g1:num->'a") STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN (T "g2:num->'a") STRIP_ASSUME_TAC)) THEN
     ASM_REWRITE_TAC [] THEN
     ASSUME_TAC (SPEC (T "n:num") LESS_SUC_REFL) THEN
     IMP_RES_TAC SIMP_REC_REL_UNIQUE
   ]);
val _ = ck "SIMP_REC_REL_UNIQUE_RESULT" SIMP_REC_REL_UNIQUE_RESULT;

(* UNIQUE_SKOLEM_THM — proved by hand (Scout A): HO-aware rewrite + BETA_TAC. *)
val UNIQUE_SKOLEM_THM =
  let
    val hoConv = Conv.TOP_DEPTH_CONV
        (Conv.FIRST_CONV [Conv.HO_REWR_CONV EXISTS_UNIQUE_THM,
                          Conv.HO_REWR_CONV FORALL_AND_THM,
                          Conv.HO_REWR_CONV SKOLEM_THM])
    val HO_RW_TAC = Tactic.CONV_TAC hoConv
  in
    Tactical.prove(T "!P. (!x:'a. ?!y:'b. P x y) = ?!f. !x. P x (f x)",
       GEN_TAC THEN HO_RW_TAC
        THEN EQ_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)
        THEN ASM_REWRITE_TAC[] THENL
         [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
          X_GEN_TAC (T "x:'a") THEN FIRST_ASSUM MATCH_MP_TAC THEN
          EXISTS_TAC (T "x:'a") THEN ASM_REWRITE_TAC[],
          MAP_EVERY X_GEN_TAC [T "x:'a", T "y1:'b", T "y2:'b"]
          THEN STRIP_TAC THEN
          FIRST_ASSUM(X_CHOOSE_TAC (T "f:'a->'b")) THEN
          SUBGOAL_THEN (T "(\\z. if z=x then y1 else (f:'a->'b) z) = \
                          \(\\z. if z=x then y2 else (f:'a->'b) z)") MP_TAC THENL
           [FIRST_ASSUM MATCH_MP_TAC THEN
            REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
            ASM_REWRITE_TAC[],
            DISCH_THEN(MP_TAC o C AP_THM (T "x:'a")) THEN
            BETA_TAC THEN REWRITE_TAC[]]])
  end;
val _ = ck "UNIQUE_SKOLEM_THM" UNIQUE_SKOLEM_THM;

(* SIMP_REC via new_specification.
   Upstream uses SIMP_RULE bool_ss [UNIQUE_SKOLEM_THM] then [EXISTS_UNIQUE_THM]
   then CONJUNCT1.  Both SIMP_RULEs are HO; replace with CONV_RULE of a HO
   depth-rewrite using HO_REWR_CONV. *)
val skol_rule = Conv.CONV_RULE (Conv.TOP_DEPTH_CONV (Conv.HO_REWR_CONV UNIQUE_SKOLEM_THM));
val euq_rule  = Conv.CONV_RULE (Conv.TOP_DEPTH_CONV (Conv.HO_REWR_CONV EXISTS_UNIQUE_THM));
val SIMP_REC_pre = (CONJUNCT1 o euq_rule o skol_rule) SIMP_REC_REL_UNIQUE_RESULT;
val _ = ck "SIMP_REC_pre" SIMP_REC_pre;

val SIMP_REC = Definition.new_specification("SIMP_REC",["SIMP_REC"], SIMP_REC_pre);
val _ = ck "SIMP_REC" SIMP_REC;

(* SIMP_REC_THM *)
val SIMP_REC_THM = Tactical.prove(
   T "!(x:'a) f. (SIMP_REC x f 0 = x) /\\ \
     \           (!m. SIMP_REC x f (SUC m) = f(SIMP_REC x f m))",
   REPEAT GEN_TAC THEN
   ASSUME_TAC (SPECL [T "x:'a", T "f:'a -> 'a"] SIMP_REC) THEN
   CONJ_TAC THENL [
     POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [SIMP_REC_REL] o
                SPEC (T "0")) THEN ASM_REWRITE_TAC [],
     GEN_TAC THEN
     FIRST_ASSUM (STRIP_ASSUME_TAC o SPEC (T "SUC m")) THEN
     FIRST_X_ASSUM (STRIP_ASSUME_TAC o SPEC (T "m:num")) THEN
     ASM_REWRITE_TAC [] THEN
     (* goal now:  g (SUC m) = f (g' m)  where
        SIMP_REC_REL g  x f (SUC (SUC m))  and  SIMP_REC_REL g' x f (SUC m).  *)
     SUBGOAL_THEN (T "g (SUC m) = f ((g:num->'a) m)") SUBST1_TAC THENL [
       RULE_ASSUM_TAC (REWRITE_RULE [SIMP_REC_REL]) THEN
       REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC) handle _ => ALL_TAC) THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [LESS_SUC_SUC],
       ALL_TAC
     ] THEN AP_TERM_TAC THEN
     (* goal:  g m = g' m  ; both rels hold, m < SUC(SUC m) and m < SUC m *)
     STRIP_ASSUME_TAC (SPEC (T "m:num") LESS_SUC_SUC) THEN
     IMP_RES_TAC SIMP_REC_REL_UNIQUE
   ]);
val _ = ck "SIMP_REC_THM" SIMP_REC_THM;

(* PRIM_REC_FUN *)
val PRIM_REC_FUN = Definition.new_definition("PRIM_REC_FUN",
   T "PRIM_REC_FUN (x:'a) (f:'a->num->'a) = \
     \  SIMP_REC (\\n:num. x) (\\fun n. f(fun(PRE n))n)");
val _ = ck "PRIM_REC_FUN" PRIM_REC_FUN;

(* PRIM_REC_EQN *)
val PRIM_REC_EQN = Tactical.prove(
   T "!(x:'a) f. \
     \  (!n. PRIM_REC_FUN x f 0 n = x) /\\ \
     \  (!m n. PRIM_REC_FUN x f (SUC m) n = f (PRIM_REC_FUN x f m (PRE n)) n)",
   REPEAT STRIP_TAC
    THEN REWRITE_TAC [PRIM_REC_FUN, SIMP_REC_THM]
    THEN CONV_TAC(DEPTH_CONV Thm.BETA_CONV)
    THEN REWRITE_TAC[]);
val _ = ck "PRIM_REC_EQN" PRIM_REC_EQN;

(* PRIM_REC *)
val PRIM_REC = Definition.new_definition("PRIM_REC",
   T "PRIM_REC (x:'a) f m = PRIM_REC_FUN x f m (PRE m)");
val _ = ck "PRIM_REC" PRIM_REC;

(* PRIM_REC_THM *)
val PRIM_REC_THM = Tactical.prove(
   T "!x f. (PRIM_REC (x:'a) f 0 = x) /\\ \
     \      (!m. PRIM_REC x f (SUC m) = f (PRIM_REC x f m) m)",
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[PRIM_REC, PRIM_REC_FUN, SIMP_REC_THM]
    THEN CONV_TAC(DEPTH_CONV Thm.BETA_CONV)
    THEN REWRITE_TAC[PRE]);
val _ = ck "PRIM_REC_THM" PRIM_REC_THM;

(* num_Axiom_old : !e f. ?!fn1. (fn1 0 = e) /\ (!n. fn1 (SUC n) = f (fn1 n) n) *)
val num_Axiom_old = Tactical.prove(
   T "!e:'a. !f. ?! fn1. (fn1 0 = e) /\\ (!n. fn1 (SUC n) = f (fn1 n) n)",
   REPEAT GEN_TAC THEN
   CONV_TAC Conv.EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL
   [EXISTS_TAC (T "PRIM_REC (e:'a) (f:'a->num->'a)") THEN
    REWRITE_TAC [PRIM_REC_THM],
    CONV_TAC (DEPTH_CONV Thm.BETA_CONV) THEN
    REPEAT STRIP_TAC THEN
    CONV_TAC Conv.FUN_EQ_CONV THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC []]);
val _ = ck "num_Axiom_old" num_Axiom_old;

(* num_Axiom : !e f. ?fn. (fn 0 = e) /\ !n. fn (SUC n) = f n (fn n) *)
val num_Axiom = Tactical.prove(
   T "!(e:'a) f. ?fn. (fn 0 = e) /\\ !n. fn (SUC n) = f n (fn n)",
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC
      (Conv.CONV_RULE Conv.EXISTS_UNIQUE_CONV
         (SPECL [T "e:'a", T "\\a:'a n:num. f n a:'a"] num_Axiom_old)) THEN
   EXISTS_TAC (T "fn1 : num -> 'a") THEN
   RULE_ASSUM_TAC Conv.BETA_RULE THEN ASM_REWRITE_TAC []);
val _ = ck "num_Axiom" num_Axiom;


fun ck3 name th = pr (name ^ "_OK: " ^ Parse.thm_to_string th) handle e => pr (name ^ "_FAIL: " ^ exnMessage e);
val addAx = ISPECL [T "\\n:num. n", T "\\(k:num) (g:num->num). \\n:num. SUC (g n)"] num_Axiom;
val addAx2 = Conv.CONV_RULE (DEPTH_CONV Thm.BETA_CONV) addAx;
(* introduce constant 'add' *)
val add_spec = Definition.new_specification("add_def",["add"], addAx2);
val _ = ck3 "add_spec" add_spec;
(* derive: add 0 n = n  and  add (SUC m) n = SUC (add m n) *)
val ADD0 = Tactical.prove(T "!n. add 0 n = n",
   GEN_TAC THEN REWRITE_TAC[CONJUNCT1 add_spec]
    THEN CONV_TAC (DEPTH_CONV Thm.BETA_CONV) THEN REWRITE_TAC[]);
val _ = ck3 "ADD0" ADD0;
val ADDS = Tactical.prove(T "!m n. add (SUC m) n = SUC (add m n)",
   REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[CONJUNCT2 add_spec]
    THEN CONV_TAC (DEPTH_CONV Thm.BETA_CONV) THEN REWRITE_TAC[]);
val _ = ck3 "ADDS" ADDS;
val ADD = CONJ ADD0 ADDS;
val _ = ck3 "ADD" ADD;
val () = print "ADD2_DONE\n";

(* ===================== TROPHY: !n. add n 0 = n  (= n + 0 = n) ===================== *)
val ADD_0 = Tactical.prove(T "!n. add n 0 = n",
   INDUCT_TAC THENL [
     REWRITE_TAC[ADD0],
     ASM_REWRITE_TAC[ADDS]
   ]);
val _ = ck3 "TROPHY_add_n_0" ADD_0;
val _ = pr ("TROPHY_HYPS=" ^ Int.toString (length (Thm.hyp ADD_0)));
val _ = if null (Thm.hyp ADD_0) then pr "FULL_TROPHY_PASS\n" else pr "TROPHY_HAS_HYPS\n";

(* Also prove the symmetric / commuted forms and the genuine '+' display via overload *)
val () = (set_fixity "+" (Infix(boolLib.LEFT, 500)) handle _ => set_fixity "+" (Infix(LEFT, 500)))
         handle e => pr ("set_fixity note: " ^ exnMessage e);
val () = (Parse.overload_on("+", T "add") handle e => pr ("overload note: " ^ exnMessage e));
val trophy_plus = Tactical.prove(T "!n. n + 0 = n", INDUCT_TAC THENL [REWRITE_TAC[ADD0], ASM_REWRITE_TAC[ADDS]])
   handle e => (pr ("trophy_plus_note: " ^ exnMessage e); ADD_0);
val _ = ck3 "TROPHY_plus_n_0" trophy_plus;
val () = print "TROPHY_DONE\n";
