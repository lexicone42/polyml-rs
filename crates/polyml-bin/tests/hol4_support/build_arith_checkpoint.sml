(* build_arith_checkpoint.sml — a real arithmetic library proved BY INDUCTION on
   /tmp/hol4_num (HOL4 kernel + numTheory, running on the polyml-rs interpreter),
   exported as /tmp/hol4_arith. Headline results (all 0 hypotheses):
     ADD_COMM   |- !m n. m + n = n + m
     ADD_ASSOC  |- !m n p. m + (n + p) = (m + n) + p
     MULT_COMM  |- !m n. mult m n = mult n m
     RIGHT_ADD_DISTRIB, ADD_RCANCEL, ADD_EQ_0
     EVEN_ADD   |- !m n. EVEN (m + n) <=> (EVEN m <=> EVEN n)   (parity)
   Built on num_Axiom (primitive recursion), itself proved by hand without
   bool_ss / the SAT subsystem (see num_arith_trophy.sml + CLAUDE.md: plain
   REWRITE_TAC is first-order, so UNIQUE_SKOLEM_THM uses Conv.HO_REWR_CONV;
   "<" is TC-free). `add` and `mult` are defined directly from num_Axiom via
   ISPECL + beta + Theory.Definition.new_specification (Prim_rec is unbound).

   The body below is the proven multiplication driver (prelude + add laws + mult
   laws) followed by an appendix (the + overload, cancellation/EQ_0/CLAUSES, the
   EVEN/ODD parity stack, the numArith structure, a smoke gate, and the export).
   INDUCT_TAC gotcha: its step branch is GEN_TAC THEN DISCH_TAC, so a SINGLE-
   quantifier goal (!n. ...) has no leftover inner quantifier — do not add an
   extra GEN_TAC there; multi-quantifier goals keep REPEAT GEN_TAC.

   Run (cwd vendor/polyml, or HOL4_DIR set):
     tools/sml-exp.sh --steps 400000000000 /tmp/hol4_num \
       crates/polyml-bin/tests/hol4_support/build_arith_checkpoint.sml
   Emits *_OK per theorem, SMOKE_* lines, EXPORTING /tmp/hol4_arith,
   ARITH_CHECKPOINT_DONE. (Found by a 3-scout workflow; ~310M steps.) *)

(* mult.sml — Scout B: multiplication on /tmp/hol4_num.
   Copies the add prelude (num_Axiom + add + ADD0/ADDS + INDUCT_TAC) from
   num_arith_trophy.sml verbatim, then defines mult and proves
   MULT_0_R, MULT_SUC, RIGHT_ADD_DISTRIB, MULT_COMM. *)

val () = print "MULT_START\n";
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

(* ===== num_Axiom (re-derived, ~300M steps) ===== *)
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
val LESS_SUC_IMP = Tactical.prove(T "!m n. (m < SUC n) ==> ~(m = n) ==> (m < n)",
   REWRITE_TAC[LESS_THM] THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);
val LESS_SUC_SUC = Tactical.prove(T "!m. (m < SUC m) /\\ (m < SUC(SUC m))",
   GEN_TAC THEN CONJ_TAC
    THENL [MATCH_ACCEPT_TAC LESS_SUC_REFL,
           MATCH_MP_TAC LESS_SUC THEN MATCH_ACCEPT_TAC LESS_SUC_REFL]);
val () = print "LESS_LAYER_DONE\n";

val SIMP_REC_REL = Definition.new_definition("SIMP_REC_REL",
   T "SIMP_REC_REL fun x f n = \
     \  ((fun 0 = (x:'a)) /\\ \
     \   (!m. (m < n) ==> (fun(SUC m) = f(fun m))))");
fun INDUCT_THEN_TAC handler =
  Tactic.HO_MATCH_MP_TAC INDUCTION THEN Tactic.CONJ_TAC
   THENL [ALL_TAC, Tactic.GEN_TAC THEN DISCH_THEN handler];
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

(* ===== addition lemmas needed for distrib / comm ===== *)
(* ADD_0_R : !n. add n 0 = n  (induct on n) *)
val ADD_0_R = Tactical.prove(T "!n. add n 0 = n",
   INDUCT_TAC THENL [REWRITE_TAC[ADD0], ASM_REWRITE_TAC[ADDS]]);
val _ = ck "ADD_0_R" ADD_0_R;
(* ADD_SUC_R : !m n. add m (SUC n) = SUC (add m n)  (induct on m) *)
val ADD_SUC_R = Tactical.prove(T "!m n. add m (SUC n) = SUC (add m n)",
   INDUCT_TAC THENL [
     REWRITE_TAC[ADD0],
     GEN_TAC THEN ASM_REWRITE_TAC[ADDS]]);
val _ = ck "ADD_SUC_R" ADD_SUC_R;
(* ADD_COMM : !m n. add m n = add n m  (induct on m, use ADD0 + ADD_0_R + ADDS + ADD_SUC_R) *)
val ADD_COMM = Tactical.prove(T "!m n. add m n = add n m",
   INDUCT_TAC THENL [
     GEN_TAC THEN REWRITE_TAC[ADD0, ADD_0_R],
     GEN_TAC THEN ASM_REWRITE_TAC[ADDS, ADD_SUC_R]]);
val _ = ck "ADD_COMM" ADD_COMM;
(* ADD_ASSOC : !m n p. add m (add n p) = add (add m n) p  (induct on m) *)
val ADD_ASSOC = Tactical.prove(T "!m n p. add m (add n p) = add (add m n) p",
   INDUCT_TAC THENL [
     REWRITE_TAC[ADD0],
     REPEAT GEN_TAC THEN ASM_REWRITE_TAC[ADDS]]);
val _ = ck "ADD_ASSOC" ADD_ASSOC;
val () = print "ADD_LEMMAS_DONE\n";

(* ===== mult : mirror add's derivation exactly =====
   We want   mult 0 n = 0   and   mult (SUC m) n = add (mult m n) n.
   num_Axiom : !e f. ?fn. fn 0 = e /\ !n. fn (SUC n) = f n (fn n).
   Take fn = mult (a num -> (num->num)).  e = (\n. 0).  Step:
     mult (SUC m) = f m (mult m) = (\(k:num) (g:num->num). \n:num. add (g n) n) m (mult m)
                  = \n. add (mult m n) n.  *)
val multAx = ISPECL [T "\\n:num. 0", T "\\(k:num) (g:num->num). \\n:num. add (g n) n"] num_Axiom;
val multAx2 = Conv.CONV_RULE (DEPTH_CONV Thm.BETA_CONV) multAx;
val _ = ck "multAx2" multAx2;
val mult_spec = Definition.new_specification("mult_def",["mult"], multAx2);
val _ = ck "mult_spec" mult_spec;
(* MULT0 : !n. mult 0 n = 0 *)
val MULT0 = Tactical.prove(T "!n. mult 0 n = 0",
   GEN_TAC THEN REWRITE_TAC[CONJUNCT1 mult_spec]
    THEN CONV_TAC (DEPTH_CONV Thm.BETA_CONV) THEN REWRITE_TAC[]);
val _ = ck "MULT0" MULT0;
(* MULTS : !m n. mult (SUC m) n = add (mult m n) n *)
val MULTS = Tactical.prove(T "!m n. mult (SUC m) n = add (mult m n) n",
   REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[CONJUNCT2 mult_spec]
    THEN CONV_TAC (DEPTH_CONV Thm.BETA_CONV) THEN REWRITE_TAC[]);
val _ = ck "MULTS" MULTS;
val () = print "MULT_DEF_DONE\n";

(* ===== Target theorems ===== *)
(* MULT_0_R : !n. mult n 0 = 0   (induct on n) *)
val MULT_0_R = Tactical.prove(T "!n. mult n 0 = 0",
   INDUCT_TAC THENL [
     REWRITE_TAC[MULT0],
     ASM_REWRITE_TAC[MULTS, ADD0]]);
val _ = ck "MULT_0_R" MULT_0_R;

(* MULT_SUC : !m n. mult m (SUC n) = add (mult m n) m   (induct on m)
   base: mult 0 (SUC n) = 0 = add 0 0 = add (mult 0 n) 0   via MULT0, ADD_0_R/ADD0
   step: mult (SUC m) (SUC n)
       = add (mult m (SUC n)) (SUC n)           [MULTS]
       = add (add (mult m n) m) (SUC n)         [IH]
       = SUC (add (add (mult m n) m) n)         [ADD_SUC_R]
     target = add (mult (SUC m) n) (SUC m)
       = add (add (mult m n) n) (SUC m)         [MULTS]
       = SUC (add (add (mult m n) n) m)         [ADD_SUC_R]
   both reduce to SUC(...): need (add (mult m n) m) + n = (add (mult m n) n) + m,
   which is associativity+commutativity of add.  Rely on ADD_ASSOC/ADD_COMM rewriting. *)
val MULT_SUC = Tactical.prove(T "!m n. mult m (SUC n) = add (mult m n) m",
   INDUCT_TAC THENL [
     GEN_TAC THEN REWRITE_TAC[MULT0, ADD_0_R],
     REPEAT GEN_TAC THEN
       ASM_REWRITE_TAC[MULTS, ADD_SUC_R] THEN
       (* goal: SUC (add (add (mult m n) m) n) = SUC (add (add (mult m n) n) m)
          i.e. add (add (mult m n) m) n = add (add (mult m n) n) m *)
       AP_TERM_TAC THEN
       REWRITE_TAC[GSYM ADD_ASSOC] THEN
       (* add (mult m n) (add m n) = add (mult m n) (add n m) *)
       AP_TERM_TAC THEN
       MATCH_ACCEPT_TAC ADD_COMM]);
val _ = ck "MULT_SUC" MULT_SUC;

(* RIGHT_ADD_DISTRIB : !m n p. mult (add m n) p = add (mult m p) (mult n p)
   induct on m.
   base: mult (add 0 n) p = mult n p ; add (mult 0 p) (mult n p) = add 0 (mult n p) = mult n p.
   step: mult (add (SUC m) n) p = mult (SUC (add m n)) p   [ADDS]
        = add (mult (add m n) p) p                          [MULTS]
        = add (add (mult m p) (mult n p)) p                 [IH]
     target: add (mult (SUC m) p) (mult n p)
        = add (add (mult m p) p) (mult n p)                 [MULTS]
   need: add (add (mult m p) (mult n p)) p = add (add (mult m p) p) (mult n p)
   = assoc/comm of add. *)
val RIGHT_ADD_DISTRIB = Tactical.prove(
   T "!m n p. mult (add m n) p = add (mult m p) (mult n p)",
   INDUCT_TAC THENL [
     REPEAT GEN_TAC THEN REWRITE_TAC[ADD0, MULT0],
     REPEAT GEN_TAC THEN
       ASM_REWRITE_TAC[ADDS, MULTS] THEN
       (* add (add (mult m p) (mult n p)) p = add (add (mult m p) p) (mult n p) *)
       REWRITE_TAC[GSYM ADD_ASSOC] THEN
       AP_TERM_TAC THEN
       MATCH_ACCEPT_TAC ADD_COMM]);
val _ = ck "RIGHT_ADD_DISTRIB" RIGHT_ADD_DISTRIB;

(* MULT_COMM : !m n. mult m n = mult n m
   induct on m.
   base: mult 0 n = 0 = mult n 0   [MULT0, MULT_0_R]
   step: mult (SUC m) n = add (mult m n) n   [MULTS]
                        = add (mult n m) n    [IH]
        target: mult n (SUC m) = add (mult n m) n  [MULT_SUC: mult n (SUC m) = add (mult n m) n]
   So both sides equal add (mult n m) n.  *)
val MULT_COMM = Tactical.prove(T "!m n. mult m n = mult n m",
   INDUCT_TAC THENL [
     GEN_TAC THEN REWRITE_TAC[MULT0, MULT_0_R],
     REPEAT GEN_TAC THEN
       ASM_REWRITE_TAC[MULTS, MULT_SUC]]);
val _ = ck "MULT_COMM" MULT_COMM;

val () = print "MULT_ALL_DONE\n";

(* =====================================================================
   APPENDIX — overload "+", cancellation / EQ_0 / CLAUSES, parity, export.
   Uses the bindings from the body above: ck, add, ADD0, ADDS, ADD_0_R,
   ADD_SUC_R, ADD_COMM, ADD_ASSOC, mult, MULT*, INDUCT_TAC, num_CASES,
   NOT_SUC, INV_SUC_EQ, num_Axiom, T.
   ===================================================================== *)
val () = print "ARITH_APPENDIX_START\n";

(* display "+" as infix for `add` (boolLib unbound here, hence the fallback). *)
val () = (set_fixity "+" (Infix(boolLib.LEFT, 500))
          handle _ => set_fixity "+" (Infix(LEFT, 500)));
val () = (Parse.overload_on("+", T "add") handle e => pr ("overload note: " ^ exnMessage e));

val ADD_CLAUSES = Tactical.prove(
   T "(add 0 n = n) /\\ (add m 0 = m) /\\ (add (SUC m) n = SUC (add m n)) /\\ (add m (SUC n) = SUC (add m n))",
   REWRITE_TAC[ADD0, ADDS, SPEC_ALL ADD_0_R, SPEC_ALL ADD_SUC_R]);
val _ = ck "ADD_CLAUSES" ADD_CLAUSES;

val ADD_RCANCEL = Tactical.prove(
   T "!m n p. (add m p = add n p) ==> (m = n)",
   GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL [
     REWRITE_TAC[ADD_0_R],
     REWRITE_TAC[ADD_SUC_R, INV_SUC_EQ] THEN DISCH_TAC THEN RES_TAC ]);
val _ = ck "ADD_RCANCEL" ADD_RCANCEL;

val ADD_EQ_0 = Tactical.prove(
   T "!m n. (add m n = 0) <=> (m = 0) /\\ (n = 0)",
   INDUCT_TAC THENL [ REWRITE_TAC[ADD0], REWRITE_TAC[ADDS, NOT_SUC] ]);
val _ = ck "ADD_EQ_0" ADD_EQ_0;

(* ---- parity: EVEN / ODD from num_Axiom ---- *)
val evenAx  = ISPECL [T "T", T "\\(k:num) (b:bool). ~b"] num_Axiom;
val evenAx2 = Conv.CONV_RULE (DEPTH_CONV Thm.BETA_CONV) evenAx;
val even_spec = Definition.new_specification("EVEN_def",["EVEN"], evenAx2);
val EVEN_0  = Tactical.prove(T "EVEN 0 = T", REWRITE_TAC[CONJUNCT1 even_spec]);
val EVEN_SUC = Tactical.prove(T "!n. EVEN (SUC n) = ~(EVEN n)", REWRITE_TAC[CONJUNCT2 even_spec]);
val oddAx   = ISPECL [T "F", T "\\(k:num) (b:bool). ~b"] num_Axiom;
val oddAx2  = Conv.CONV_RULE (DEPTH_CONV Thm.BETA_CONV) oddAx;
val odd_spec = Definition.new_specification("ODD_def",["ODD"], oddAx2);
val ODD_0  = Tactical.prove(T "ODD 0 = F", REWRITE_TAC[CONJUNCT1 odd_spec]);
val ODD_SUC = Tactical.prove(T "!n. ODD (SUC n) = ~(ODD n)", REWRITE_TAC[CONJUNCT2 odd_spec]);
val ODD_EVEN = Tactical.prove(T "!n. ODD n = ~(EVEN n)",
   INDUCT_TAC THENL [REWRITE_TAC[ODD_0, EVEN_0], ASM_REWRITE_TAC[ODD_SUC, EVEN_SUC]]);
val EVEN_OR_ODD = Tactical.prove(T "!n. EVEN n \\/ ODD n",
   GEN_TAC THEN REWRITE_TAC[ODD_EVEN] THEN ASM_CASES_TAC (T "EVEN n") THEN ASM_REWRITE_TAC[]);
val _ = ck "EVEN_OR_ODD" EVEN_OR_ODD;
val EVEN_AND_ODD = Tactical.prove(T "!n. ~(EVEN n /\\ ODD n)",
   GEN_TAC THEN REWRITE_TAC[ODD_EVEN] THEN ASM_CASES_TAC (T "EVEN n") THEN ASM_REWRITE_TAC[]);
val _ = ck "EVEN_AND_ODD" EVEN_AND_ODD;
val EVEN_ADD = Tactical.prove(
   T "!m n. EVEN (add m n) <=> (EVEN m <=> EVEN n)",
   INDUCT_TAC THENL [
     REWRITE_TAC[ADD0, EVEN_0],
     GEN_TAC THEN REWRITE_TAC[ADDS, EVEN_SUC]
       THEN POP_ASSUM (fn ih => REWRITE_TAC[SPEC (T "n:num") ih])
       THEN ASM_CASES_TAC (T "EVEN m") THEN ASM_CASES_TAC (T "EVEN n")
       THEN ASM_REWRITE_TAC[] ]);
val _ = ck "EVEN_ADD" EVEN_ADD;

(* ---- bake the library into a structure so reloaders skip re-derivation ---- *)
structure numArith = struct
  val num_Axiom = num_Axiom
  val ADD0 = ADD0  val ADDS = ADDS
  val ADD_0_R = ADD_0_R  val ADD_SUC_R = ADD_SUC_R
  val ADD_COMM = ADD_COMM  val ADD_ASSOC = ADD_ASSOC
  val ADD_CLAUSES = ADD_CLAUSES  val ADD_RCANCEL = ADD_RCANCEL  val ADD_EQ_0 = ADD_EQ_0
  val mult_spec = mult_spec  val MULT0 = MULT0  val MULTS = MULTS
  val MULT_0_R = MULT_0_R  val MULT_SUC = MULT_SUC
  val RIGHT_ADD_DISTRIB = RIGHT_ADD_DISTRIB  val MULT_COMM = MULT_COMM
  val EVEN_OR_ODD = EVEN_OR_ODD  val EVEN_AND_ODD = EVEN_AND_ODD  val EVEN_ADD = EVEN_ADD
  val INDUCT_TAC = INDUCT_TAC  val num_CASES = num_CASES
end;

(* ---- smoke gate: headline theorems must be hypothesis-free ---- *)
val smokeThms = [ADD_COMM, ADD_ASSOC, MULT_COMM, RIGHT_ADD_DISTRIB, ADD_RCANCEL, EVEN_ADD];
val () = if List.all (fn th => null (Thm.hyp th)) smokeThms then ()
         else raise Fail "ARITH SMOKE: a headline theorem has hypotheses";
val () = print ("SMOKE_ADD_COMM:  " ^ Parse.thm_to_string ADD_COMM ^ "\n");
val () = print ("SMOKE_MULT_COMM: " ^ Parse.thm_to_string MULT_COMM ^ "\n");
val () = print ("SMOKE_EVEN_ADD:  " ^ Parse.thm_to_string EVEN_ADD ^ "\n");
val () = (print "EXPORTING /tmp/hol4_arith\n";
          PolyML.export("/tmp/hol4_arith", PolyML.rootFunction);
          print "ARITH_CHECKPOINT_DONE\n");
