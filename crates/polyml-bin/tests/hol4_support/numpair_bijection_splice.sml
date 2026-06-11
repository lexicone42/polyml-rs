open boolLib;
val _ = print "=== START ===\n";

(* ---- infrastructure ---- *)
val DECIDE = fn tm => Drule.EQT_ELIM (Arith.ARITH_CONV tm);
fun DECIDE_TAC g = CONV_TAC (Drule.EQT_INTRO o DECIDE) g;
fun TM q = Parse.Term [QUOTE q];
val INDUCT_TAC = Prim_rec.INDUCT_THEN numTheory.INDUCTION ASSUME_TAC;
val arith_ss = simpLib.++(boolSimps.bool_ss, numSimps.ARITH_ss);
val DB = Theory.current_theorems() @ Theory.current_definitions();
fun get n = #2 (valOf (List.find (fn(nm,_)=>nm=n) DB));
val invtri0_ind = get "invtri0_ind";
val invtri0_def = get "invtri0_def";
val tri_def     = get "tri_def";
val invtri_def  = get "invtri_def";
val npair_def   = get "npair_def";
val nfst_def    = get "nfst_def";
val nsnd_def    = get "nsnd_def";
val tri0 = CONJUNCT1 tri_def;  (* tri 0 = 0 *)

fun save nm th = (Theory.save_thm (nm, th); print ("OK " ^ nm ^ "\n"); th);

(* ---- tri (a+1) = (a+1) + tri a ---- *)
val tri_ADD1 = Tactical.prove(
  TM "!a. tri (a + 1) = (a + 1) + tri a",
  GEN_TAC THEN REWRITE_TAC [GSYM arithmeticTheory.ADD1] THEN REWRITE_TAC [tri_def]);
val _ = save "tri_ADD1" tri_ADD1;

(* ---- tri_le : n <= tri n ---- *)
val tri_le = Tactical.prove(
  TM "!n. n <= tri n",
  INDUCT_TAC THEN SIMP_TAC arith_ss [tri_def]);
val _ = save "tri_le" tri_le;

(* ---- tri monotonicity : m <= n ==> tri m <= tri n ---- *)
val tri_LE_add = Tactical.prove(
  TM "!d m. tri m <= tri (m + d)",
  INDUCT_TAC THENL [
    GEN_TAC THEN SIMP_TAC arith_ss [],
    GEN_TAC THEN MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS THEN
    EXISTS_TAC (TM "tri (m + d)") THEN CONJ_TAC THENL [
      POP_ASSUM (fn ih => ACCEPT_TAC (SPEC (TM "m:num") ih)),
      SUBGOAL_THEN (TM "m + SUC d = SUC (m + d)") SUBST1_TAC THEN1 DECIDE_TAC THEN
      SIMP_TAC arith_ss [tri_def]]]);
val tri_LE = Tactical.prove(
  TM "!m n. m <= n ==> tri m <= tri n",
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN (TM "n = m + (n - m)") (fn th => ONCE_REWRITE_TAC [th]) THEN1
    (POP_ASSUM MP_TAC THEN DECIDE_TAC) THEN
  MATCH_ACCEPT_TAC tri_LE_add);
val _ = save "tri_LE" tri_LE;

(* ---- invtri0_thm ---- *)
val invtri0_thm = Tactical.prove(
  TM "!n a. tri (SND (invtri0 n a)) + FST (invtri0 n a) = n + tri a",
  HO_MATCH_MP_TAC invtri0_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC [invtri0_def] THEN COND_CASES_TAC THENL [
    REWRITE_TAC [pairTheory.FST, pairTheory.SND] THEN DECIDE_TAC,
    FIRST_X_ASSUM (fn ih => REWRITE_TAC [MP ih (ASSUME (TM "~(n < a + 1)"))] handle _ => NO_TAC) THEN
    REWRITE_TAC [tri_ADD1] THEN FIRST_ASSUM (fn notlt => MP_TAC notlt) THEN DECIDE_TAC]);
val _ = save "invtri0_thm" invtri0_thm;

(* ---- SND_invtri0 ---- *)
val SND_invtri0 = Tactical.prove(
  TM "!n a. FST (invtri0 n a) < SUC (SND (invtri0 n a))",
  HO_MATCH_MP_TAC invtri0_ind THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC [invtri0_def] THEN COND_CASES_TAC THENL [
    REWRITE_TAC [pairTheory.FST, pairTheory.SND] THEN FIRST_ASSUM (fn lt => MP_TAC lt) THEN DECIDE_TAC,
    FIRST_X_ASSUM (fn ih => ACCEPT_TAC (MP ih (ASSUME (TM "~(n < a + 1)"))) handle _ => NO_TAC)]);
val _ = save "SND_invtri0" SND_invtri0;

(* ---- invtri_lower : tri (invtri n) <= n ---- *)
val invtri_lower = Tactical.prove(
  TM "!n. tri (invtri n) <= n",
  GEN_TAC THEN REWRITE_TAC [invtri_def] THEN
  MP_TAC (SPECL [TM "n:num", TM "0"] invtri0_thm) THEN
  REWRITE_TAC [tri0] THEN DECIDE_TAC);
val _ = save "invtri_lower" invtri_lower;

(* ---- invtri_upper : n < tri (invtri n + 1) ---- *)
val invtri_upper = Tactical.prove(
  TM "!n. n < tri (invtri n + 1)",
  GEN_TAC THEN REWRITE_TAC [invtri_def, tri_ADD1] THEN
  MP_TAC (SPECL [TM "n:num", TM "0"] invtri0_thm) THEN
  MP_TAC (SPECL [TM "n:num", TM "0"] SND_invtri0) THEN
  REWRITE_TAC [tri0] THEN DECIDE_TAC);
val _ = save "invtri_upper" invtri_upper;

(* ---- invtri_unique : tri y <= n /\ n < tri (y+1) ==> invtri n = y ---- *)
val invtri_unique = Tactical.prove(
  TM "!n y. tri y <= n /\\ n < tri (y + 1) ==> (invtri n = y)",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC (SPECL [TM "invtri n", TM "y:num"] arithmeticTheory.LESS_LESS_CASES) THENL [
    ASM_REWRITE_TAC [],
    POP_ASSUM (DISJ_CASES_TAC) THENL [
      MP_TAC (SPEC (TM "n:num") invtri_upper) THEN
      MP_TAC (SPECL [TM "invtri n + 1", TM "y:num"] tri_LE) THEN
      POP_ASSUM_LIST (MAP_EVERY MP_TAC) THEN DECIDE_TAC,
      MP_TAC (SPEC (TM "n:num") invtri_lower) THEN
      MP_TAC (SPECL [TM "y + 1", TM "invtri n"] tri_LE) THEN
      POP_ASSUM_LIST (MAP_EVERY MP_TAC) THEN DECIDE_TAC]]);
val _ = save "invtri_unique" invtri_unique;

(* ---- invtri_linverse : invtri (tri n) = n ---- *)
val invtri_linverse = Tactical.prove(
  TM "!n. invtri (tri n) = n",
  GEN_TAC THEN MATCH_MP_TAC invtri_unique THEN
  REWRITE_TAC [tri_ADD1] THEN DECIDE_TAC);
val _ = save "invtri_linverse" invtri_linverse;

(* ---- invtri_linverse_r : y <= x ==> invtri (tri x + y) = x ---- *)
val invtri_linverse_r = Tactical.prove(
  TM "!x y. y <= x ==> (invtri (tri x + y) = x)",
  REPEAT STRIP_TAC THEN MATCH_MP_TAC invtri_unique THEN
  REWRITE_TAC [tri_ADD1] THEN
  POP_ASSUM MP_TAC THEN DECIDE_TAC);
val _ = save "invtri_linverse_r" invtri_linverse_r;

(* ---- nfst_npair : nfst (npair x y) = x ---- *)
val nfst_npair = Tactical.prove(
  TM "!x y. nfst (npair x y) = x",
  REPEAT GEN_TAC THEN REWRITE_TAC [nfst_def, npair_def] THEN
  SUBGOAL_THEN (TM "invtri (tri (x + y) + y) = x + y")
    (fn th => REWRITE_TAC [th]) THEN1
    (MATCH_MP_TAC invtri_linverse_r THEN DECIDE_TAC) THEN
  DECIDE_TAC);
val _ = save "nfst_npair" nfst_npair;

(* ---- nsnd_npair : nsnd (npair x y) = y ---- *)
val nsnd_npair = Tactical.prove(
  TM "!x y. nsnd (npair x y) = y",
  REPEAT GEN_TAC THEN REWRITE_TAC [nsnd_def, npair_def] THEN
  SUBGOAL_THEN (TM "invtri (tri (x + y) + y) = x + y")
    (fn th => REWRITE_TAC [th]) THEN1
    (MATCH_MP_TAC invtri_linverse_r THEN DECIDE_TAC) THEN
  DECIDE_TAC);
val _ = save "nsnd_npair" nsnd_npair;

(* ---- npair_11 : (npair x1 y1 = npair x2 y2) <=> (x1=x2) /\ (y1=y2) ---- *)
val npair_11 = Tactical.prove(
  TM "!x1 y1 x2 y2. (npair x1 y1 = npair x2 y2) <=> (x1 = x2) /\\ (y1 = y2)",
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    STRIP_TAC THEN
    CONJ_TAC THENL [
      POP_ASSUM (fn eq => MP_TAC (AP_TERM (TM "nfst") eq)) THEN
      REWRITE_TAC [nfst_npair],
      POP_ASSUM (fn eq => MP_TAC (AP_TERM (TM "nsnd") eq)) THEN
      REWRITE_TAC [nsnd_npair]
    ],
    STRIP_TAC THEN ASM_REWRITE_TAC []
  ]);
val _ = save "npair_11" npair_11;

(* ---- npair_cases : !n. ?x y. n = npair x y ---- *)
(* witnesses nfst n, nsnd n; let s = invtri n.  nfst n = tri s + s - n,
   nsnd n = n - tri s.  Bounds tri s <= n < (s+1)+tri s give nfst+nsnd = s,
   and n = tri s + (n - tri s). *)
val npair_cases = Tactical.prove(
  TM "!n. ?x y. n = npair x y",
  GEN_TAC THEN
  EXISTS_TAC (TM "nfst n") THEN EXISTS_TAC (TM "nsnd n") THEN
  REWRITE_TAC [npair_def, nfst_def, nsnd_def] THEN
  SUBGOAL_THEN (TM "tri (invtri n) + invtri n - n + (n - tri (invtri n)) = invtri n")
    (fn th => REWRITE_TAC [th]) THEN1
    (MP_TAC (SPEC (TM "n:num") invtri_lower) THEN
     MP_TAC (SPEC (TM "n:num") invtri_upper) THEN
     REWRITE_TAC [tri_ADD1] THEN DECIDE_TAC) THEN
  MP_TAC (SPEC (TM "n:num") invtri_lower) THEN DECIDE_TAC);
val _ = save "npair_cases" npair_cases;

val _ = print "=== END ===\n";
