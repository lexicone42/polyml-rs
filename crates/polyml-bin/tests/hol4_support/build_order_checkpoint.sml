(* le_suite.sml — Scout A: ORDERING THEORY (LE) on /tmp/hol4_num.
   Prelude copied verbatim from num_arith_trophy.sml (num_Axiom + add +
   ADD0/ADDS + the LESS layer + INDUCT_TAC), plus the addition laws
   (ADD_0_R, ADD_SUC_R, ADD_COMM, ADD_ASSOC, ADD_EQ_0, ADD_RCANCEL)
   re-proved from build_arith_checkpoint.sml.  Then define LE and prove
   LE_REFL, ZERO_LE, LE_ADD, LE_TRANS, LE_ANTISYM, SUC_LE. *)

val () = print "LE_SUITE_START\n";
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

(* ===== num_Axiom (re-derived) ===== *)
val INV_SUC_EQ = GENL [T "m:num", T "n:num"]
   (IMP_ANTISYM_RULE (SPEC_ALL INV_SUC)
     (DISCH (T "m:num = n") (AP_TERM (T "SUC") (ASSUME (T "m:num = n")))));

val num_CASES = Tactical.prove(T "!n. (n = 0) \\/ ?m. n = SUC m",
   INDUCT_TAC THENL [
     DISJ1_TAC THEN REFL_TAC,
     DISJ2_TAC THEN EXISTS_TAC (T "n:num") THEN REFL_TAC]);

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
val LESS_SUC_REFL = Tactical.prove(T "!n. n < SUC n",
   INDUCT_TAC THEN REWRITE_TAC[LESS_0_0]
    THEN IMP_RES_TAC LESS_MONO THEN ASM_REWRITE_TAC[]);
val LESS_SUC = Tactical.prove(T "!m n. (m < n) ==> (m < SUC n)",
  REWRITE_TAC [LESS_DEF] THEN REPEAT STRIP_TAC
   THEN EXISTS_TAC (T "P:num->bool")
   THEN IMP_RES_TAC (CONTRAPOS(SPEC (T "n:num")
            (ASSUME (T "!n'. P(SUC n') ==> P n'"))))
   THEN ASM_REWRITE_TAC[]);
val LESS_LEMMA1 = Tactical.prove(T "!n m. (m < SUC n) ==> (m = n) \\/ (m < n)",
   INDUCT_TAC THENL [
     GEN_TAC THEN DISCH_TAC
       THEN STRIP_ASSUME_TAC (SPEC (T "m:num") num_CASES)
       THENL [
         ASM_REWRITE_TAC[],
         POP_ASSUM SUBST_ALL_TAC
           THEN IMP_RES_TAC LESS_MONO_REV
           THEN IMP_RES_TAC NOT_LESS_0
       ],
     GEN_TAC THEN DISCH_TAC
       THEN STRIP_ASSUME_TAC (SPEC (T "m:num") num_CASES)
       THENL [
         DISJ2_TAC THEN ASM_REWRITE_TAC[LESS_0],
         POP_ASSUM SUBST_ALL_TAC
           THEN IMP_RES_TAC LESS_MONO_REV
           THEN RES_TAC
           THENL [
             DISJ1_TAC THEN ASM_REWRITE_TAC[],
             DISJ2_TAC THEN IMP_RES_TAC LESS_MONO THEN ASM_REWRITE_TAC[]
           ]
       ]
   ]);
val LESS_LEMMA2 = Tactical.prove(T "!m n. ((m = n) \\/ (m < n)) ==> (m < SUC n)",
   REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_SUC THEN ASM_REWRITE_TAC[LESS_SUC_REFL]);
val LESS_THM = GENL [T "m:num", T "n:num"]
   (IMP_ANTISYM_RULE (SPEC_ALL LESS_LEMMA1) (SPEC_ALL LESS_LEMMA2));
val () = print "LESS_LAYER_DONE\n";

(* ===== num_Axiom (the big one, ~300M steps) ===== *)
val SIMP_REC_REL = Definition.new_definition("SIMP_REC_REL",
   T "SIMP_REC_REL fun x f n = \
     \  ((fun 0 = (x:'a)) /\\ \
     \   (!m. (m < n) ==> (fun(SUC m) = f(fun m))))");
fun INDUCT_THEN_TAC handler =
  Tactic.HO_MATCH_MP_TAC INDUCTION THEN Tactic.CONJ_TAC
   THENL [ALL_TAC, Tactic.GEN_TAC THEN DISCH_THEN handler];
val LESS_SUC_IMP = Tactical.prove(T "!m n. (m < SUC n) ==> ~(m = n) ==> (m < n)",
   REWRITE_TAC[LESS_THM] THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);
val LESS_SUC_SUC = Tactical.prove(T "!m. (m < SUC m) /\\ (m < SUC(SUC m))",
   GEN_TAC THEN CONJ_TAC
    THENL [MATCH_ACCEPT_TAC LESS_SUC_REFL,
           MATCH_MP_TAC LESS_SUC THEN MATCH_ACCEPT_TAC LESS_SUC_REFL]);
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
val SIMP_REC_REL_UNIQUE = Tactical.prove(
   T "!x f g1 g2 m1 m2. \
     \  SIMP_REC_REL g1 x f m1 /\\ SIMP_REC_REL g2 x f m2 ==> \
     \  !n. n < m1 /\\ n < m2 ==> (g1 n = (g2 n):'a)",
   REWRITE_TAC [SIMP_REC_REL] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   INDUCT_THEN_TAC STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP SUC_LESS)) THEN
   RES_TAC THEN ASM_REWRITE_TAC []);
val SIMP_REC_REL_UNIQUE_RESULT = Tactical.prove(
   T "!x f n. ?!y:'a. ?g. SIMP_REC_REL g x f (SUC n) /\\ (y = g n)",
   REPEAT GEN_TAC THEN CONV_TAC (Conv.HO_REWR_CONV EXISTS_UNIQUE_THM)
   THEN CONJ_TAC THENL [
     STRIP_ASSUME_TAC (SPECL [T "x:'a", T "f:'a->'a", T "SUC n"] SIMP_REC_EXISTS)
       THEN EXISTS_TAC (T "(fun:num->'a) n") THEN EXISTS_TAC (T "fun:num->'a")
       THEN ASM_REWRITE_TAC [],
     REPEAT GEN_TAC THEN
     DISCH_THEN (CONJUNCTS_THEN2
        (X_CHOOSE_THEN (T "g1:num->'a") STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN (T "g2:num->'a") STRIP_ASSUME_TAC)) THEN
     ASM_REWRITE_TAC [] THEN
     ASSUME_TAC (SPEC (T "n:num") LESS_SUC_REFL) THEN
     IMP_RES_TAC SIMP_REC_REL_UNIQUE
   ]);
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
val skol_rule = Conv.CONV_RULE (Conv.TOP_DEPTH_CONV (Conv.HO_REWR_CONV UNIQUE_SKOLEM_THM));
val euq_rule  = Conv.CONV_RULE (Conv.TOP_DEPTH_CONV (Conv.HO_REWR_CONV EXISTS_UNIQUE_THM));
val SIMP_REC_pre = (CONJUNCT1 o euq_rule o skol_rule) SIMP_REC_REL_UNIQUE_RESULT;
val SIMP_REC = Definition.new_specification("SIMP_REC",["SIMP_REC"], SIMP_REC_pre);
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
     SUBGOAL_THEN (T "g (SUC m) = f ((g:num->'a) m)") SUBST1_TAC THENL [
       RULE_ASSUM_TAC (REWRITE_RULE [SIMP_REC_REL]) THEN
       REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC) handle _ => ALL_TAC) THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [LESS_SUC_SUC],
       ALL_TAC
     ] THEN AP_TERM_TAC THEN
     STRIP_ASSUME_TAC (SPEC (T "m:num") LESS_SUC_SUC) THEN
     IMP_RES_TAC SIMP_REC_REL_UNIQUE
   ]);
val PRIM_REC_FUN = Definition.new_definition("PRIM_REC_FUN",
   T "PRIM_REC_FUN (x:'a) (f:'a->num->'a) = \
     \  SIMP_REC (\\n:num. x) (\\fun n. f(fun(PRE n))n)");
val PRIM_REC_EQN = Tactical.prove(
   T "!(x:'a) f. \
     \  (!n. PRIM_REC_FUN x f 0 n = x) /\\ \
     \  (!m n. PRIM_REC_FUN x f (SUC m) n = f (PRIM_REC_FUN x f m (PRE n)) n)",
   REPEAT STRIP_TAC
    THEN REWRITE_TAC [PRIM_REC_FUN, SIMP_REC_THM]
    THEN CONV_TAC(DEPTH_CONV Thm.BETA_CONV)
    THEN REWRITE_TAC[]);
val PRIM_REC = Definition.new_definition("PRIM_REC",
   T "PRIM_REC (x:'a) f m = PRIM_REC_FUN x f m (PRE m)");
val PRIM_REC_THM = Tactical.prove(
   T "!x f. (PRIM_REC (x:'a) f 0 = x) /\\ \
     \      (!m. PRIM_REC x f (SUC m) = f (PRIM_REC x f m) m)",
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[PRIM_REC, PRIM_REC_FUN, SIMP_REC_THM]
    THEN CONV_TAC(DEPTH_CONV Thm.BETA_CONV)
    THEN REWRITE_TAC[PRE]);
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
val num_Axiom = Tactical.prove(
   T "!(e:'a) f. ?fn. (fn 0 = e) /\\ !n. fn (SUC n) = f n (fn n)",
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC
      (Conv.CONV_RULE Conv.EXISTS_UNIQUE_CONV
         (SPECL [T "e:'a", T "\\a:'a n:num. f n a:'a"] num_Axiom_old)) THEN
   EXISTS_TAC (T "fn1 : num -> 'a") THEN
   RULE_ASSUM_TAC Conv.BETA_RULE THEN ASM_REWRITE_TAC []);
val _ = ck "num_Axiom" num_Axiom;

(* ===== add ===== *)
val addAx = ISPECL [T "\\n:num. n", T "\\(k:num) (g:num->num). \\n:num. SUC (g n)"] num_Axiom;
val addAx2 = Conv.CONV_RULE (DEPTH_CONV Thm.BETA_CONV) addAx;
val add_spec = Definition.new_specification("add_def",["add"], addAx2);
val ADD0 = Tactical.prove(T "!n. add 0 n = n",
   GEN_TAC THEN REWRITE_TAC[CONJUNCT1 add_spec]
    THEN CONV_TAC (DEPTH_CONV Thm.BETA_CONV) THEN REWRITE_TAC[]);
val _ = ck "ADD0" ADD0;
val ADDS = Tactical.prove(T "!m n. add (SUC m) n = SUC (add m n)",
   REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[CONJUNCT2 add_spec]
    THEN CONV_TAC (DEPTH_CONV Thm.BETA_CONV) THEN REWRITE_TAC[]);
val _ = ck "ADDS" ADDS;
val () = print "ADD_DONE\n";

(* ===== addition laws ===== *)
val ADD_0_R = Tactical.prove(T "!n. add n 0 = n",
   INDUCT_TAC THENL [REWRITE_TAC[ADD0], ASM_REWRITE_TAC[ADDS]]);
val _ = ck "ADD_0_R" ADD_0_R;
val ADD_SUC_R = Tactical.prove(T "!m n. add m (SUC n) = SUC (add m n)",
   INDUCT_TAC THENL [
     REWRITE_TAC[ADD0],
     GEN_TAC THEN ASM_REWRITE_TAC[ADDS]]);
val _ = ck "ADD_SUC_R" ADD_SUC_R;
val ADD_COMM = Tactical.prove(T "!m n. add m n = add n m",
   INDUCT_TAC THENL [
     GEN_TAC THEN REWRITE_TAC[ADD0, ADD_0_R],
     GEN_TAC THEN ASM_REWRITE_TAC[ADDS, ADD_SUC_R]]);
val _ = ck "ADD_COMM" ADD_COMM;
val ADD_ASSOC = Tactical.prove(T "!m n p. add m (add n p) = add (add m n) p",
   INDUCT_TAC THENL [
     REWRITE_TAC[ADD0],
     REPEAT GEN_TAC THEN ASM_REWRITE_TAC[ADDS]]);
val _ = ck "ADD_ASSOC" ADD_ASSOC;
val ADD_EQ_0 = Tactical.prove(
   T "!m n. (add m n = 0) <=> (m = 0) /\\ (n = 0)",
   INDUCT_TAC THENL [ REWRITE_TAC[ADD0], REWRITE_TAC[ADDS, NOT_SUC] ]);
val _ = ck "ADD_EQ_0" ADD_EQ_0;
val ADD_RCANCEL = Tactical.prove(
   T "!m n p. (add m p = add n p) ==> (m = n)",
   GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL [
     REWRITE_TAC[ADD_0_R],
     REWRITE_TAC[ADD_SUC_R, INV_SUC_EQ] THEN DISCH_TAC THEN RES_TAC ]);
val _ = ck "ADD_RCANCEL" ADD_RCANCEL;
(* ADD_LCANCEL : !m n p. (add p m = add p n) ==> (m = n)  (induct on p) *)
val ADD_LCANCEL = Tactical.prove(
   T "!m n p. (add p m = add p n) ==> (m = n)",
   GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL [
     REWRITE_TAC[ADD0],
     REWRITE_TAC[ADDS, INV_SUC_EQ] THEN DISCH_TAC THEN RES_TAC ]);
val _ = ck "ADD_LCANCEL" ADD_LCANCEL;
val () = print "ADD_LAWS_DONE\n";

(* ============================================================
   ORDERING THEORY: LE m n  <=>  ?p. n = add m p
   ============================================================ *)
val () = print "LE_DEF_START\n";
val LE_DEF = Definition.new_definition("LE_DEF",
   T "LE m n = ?p. n = add m p");
val _ = ck "LE_DEF" LE_DEF;

(* LE_REFL : !n. LE n n   (witness p = 0, n = add n 0 by ADD_0_R) *)
val LE_REFL = Tactical.prove(T "!n. LE n n",
   GEN_TAC THEN REWRITE_TAC[LE_DEF]
    THEN EXISTS_TAC (T "0")
    THEN REWRITE_TAC[ADD_0_R]);
val _ = ck "LE_REFL" LE_REFL;

(* ZERO_LE : !n. LE 0 n   (witness p = n, n = add 0 n by ADD0) *)
val ZERO_LE = Tactical.prove(T "!n. LE 0 n",
   GEN_TAC THEN REWRITE_TAC[LE_DEF]
    THEN EXISTS_TAC (T "n:num")
    THEN REWRITE_TAC[ADD0]);
val _ = ck "ZERO_LE" ZERO_LE;

(* LE_ADD : !m n. LE m (add m n)   (witness p = n) *)
val LE_ADD = Tactical.prove(T "!m n. LE m (add m n)",
   REPEAT GEN_TAC THEN REWRITE_TAC[LE_DEF]
    THEN EXISTS_TAC (T "n:num")
    THEN REFL_TAC);
val _ = ck "LE_ADD" LE_ADD;

(* LE_TRANS : !m n p. LE m n /\ LE n p ==> LE m p
   from n = add m a, p = add n b : p = add (add m a) b = add m (add a b) [ADD_ASSOC]. *)
val LE_TRANS = Tactical.prove(
   T "!m n p. LE m n /\\ LE n p ==> LE m p",
   REWRITE_TAC[LE_DEF] THEN REPEAT STRIP_TAC
    THEN EXISTS_TAC (T "add p' p''")
    THEN ASM_REWRITE_TAC[ADD_ASSOC]);
val _ = ck "LE_TRANS" LE_TRANS;

(* SUC_LE : !m n. LE (SUC m) (SUC n) <=> LE m n
   LE (SUC m) (SUC n) = ?p. SUC n = add (SUC m) p = SUC (add m p)
                      <=> ?p. n = add m p   [INV_SUC_EQ]  = LE m n. *)
val SUC_LE = Tactical.prove(
   T "!m n. LE (SUC m) (SUC n) <=> LE m n",
   REPEAT GEN_TAC THEN REWRITE_TAC[LE_DEF, ADDS, INV_SUC_EQ]);
val _ = ck "SUC_LE" SUC_LE;

(* LE_ANTISYM : !m n. LE m n /\ LE n m ==> (m = n)
   from n = add m p, m = add n p'.  Substitute: n = add (add n p') p
   = add n (add p' p)  [GSYM ADD_ASSOC].  Also n = add n 0 [GSYM ADD_0_R].
   ADD_LCANCEL: add p' p = 0.  ADD_EQ_0: p = 0 (and p' = 0).  So n = add m 0 = m. *)
val LE_ANTISYM = Tactical.prove(
   T "!m n. LE m n /\\ LE n m ==> (m = n)",
   REWRITE_TAC[LE_DEF] THEN REPEAT STRIP_TAC
    (* asm0: n = add m p   asm1: m = add n p'   goal: m = n *)
    (* Key: derive  p = 0  (then n = add m p = add m 0 = m).
       From asm0 and asm1: n = add m p = add (add n p') p = add n (add p' p)
       [ASSOC].  Cancel n on the left against n = add n 0 [ADD_0_R]:
       add p' p = 0  ==>  p = 0  [ADD_EQ_0]. *)
    (* Subgoal 1: add p' p = 0. *)
    THEN SUBGOAL_THEN (T "add p' p = 0") MP_TAC THENL [
      (* add p' p = 0  <==  add n (add p' p) = add n 0  [ADD_LCANCEL].
         LHS = add (add n p') p [ASSOC] = add m p [asm1] = n [asm0] = add n 0. *)
      MATCH_MP_TAC (SPECL [T "add p' p", T "0", T "n:num"] ADD_LCANCEL) THEN
      (* goal now: add n (add p' p) = add n 0 *)
      REWRITE_TAC[ADD_0_R, ADD_ASSOC] THEN
      (* goal: add (add n p') p = n *)
      POP_ASSUM (fn a1 => POP_ASSUM (fn a0 =>
         REWRITE_TAC[GSYM a1] THEN REWRITE_TAC[GSYM a0])),
      (* Subgoal 2: (add p' p = 0) ==> m = n.  asm0,asm1 still present. *)
      (* drop the dangerous asm1 (m = add n p', on top) BEFORE finishing. *)
      POP_ASSUM (fn _ => ALL_TAC) THEN
      DISCH_THEN (fn ppz =>
         let val conj = EQ_MP (SPECL [T "p':num", T "p:num"] ADD_EQ_0) ppz
             val p0   = CONJUNCT2 conj                 (* p = 0 *)
         in SUBST_ALL_TAC p0 end)
        (* asm0 now: n = add m 0 ; goal m = n. *)
        THEN ASM_REWRITE_TAC[ADD_0_R]
    ]);
val _ = ck "LE_ANTISYM" LE_ANTISYM;

val () = print "LE_SUITE_DONE\n";

(* ---- bake the ordering library into a structure + smoke gate + export ---- *)
structure numOrder = struct
  val LE_DEF = LE_DEF
  val LE_REFL = LE_REFL  val ZERO_LE = ZERO_LE  val LE_ADD = LE_ADD
  val LE_TRANS = LE_TRANS  val SUC_LE = SUC_LE  val LE_ANTISYM = LE_ANTISYM
  val ADD_LCANCEL = ADD_LCANCEL   (* required by LE_ANTISYM; not in numArith *)
end;
val smokeThms = [LE_REFL, ZERO_LE, LE_ADD, LE_TRANS, SUC_LE, LE_ANTISYM];
val () = if List.all (fn th => null (Thm.hyp th)) smokeThms then ()
         else raise Fail "ORDER SMOKE: a headline theorem has hypotheses";
val () = print ("SMOKE_LE_TRANS:   " ^ Parse.thm_to_string LE_TRANS ^ "\n");
val () = print ("SMOKE_LE_ANTISYM: " ^ Parse.thm_to_string LE_ANTISYM ^ "\n");
val () = (print "EXPORTING /tmp/hol4_order\n";
          PolyML.export("/tmp/hol4_order", PolyML.rootFunction);
          print "ORDER_CHECKPOINT_DONE\n");
