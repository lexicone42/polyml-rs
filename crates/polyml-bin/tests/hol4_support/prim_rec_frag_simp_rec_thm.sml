(* prim_rec Stage-1 fragment: SIMP_REC_THM.
   The upstream proof's AP_TERM_TAC step fails on this chain ("functions on
   lhs and rhs differ" — the goal reaches that step in a different shape).
   This is num_arith_trophy.sml's proof, which restructures the step case
   with an explicit SUBGOAL_THEN before AP_TERM_TAC. *)

val SIMP_REC_THM = Tactical.prove(
  Parse.Term [QUOTE
    "!(x:'a) f. (SIMP_REC x f 0 = x) /\\ (!m. SIMP_REC x f (SUC m) = f(SIMP_REC x f m))"],
  REPEAT GEN_TAC THEN
  ASSUME_TAC (SPECL [Parse.Term [QUOTE "x:'a"], Parse.Term [QUOTE "f:'a -> 'a"]] SIMP_REC) THEN
  CONJ_TAC THENL [
    POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [SIMP_REC_REL] o
               SPEC (Parse.Term [QUOTE "0"])) THEN ASM_REWRITE_TAC [],
    GEN_TAC THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o SPEC (Parse.Term [QUOTE "SUC m"])) THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o SPEC (Parse.Term [QUOTE "m:num"])) THEN
    ASM_REWRITE_TAC [] THEN
    (* goal: g (SUC m) = f (g' m) where SIMP_REC_REL g x f (SUC (SUC m))
       and SIMP_REC_REL g' x f (SUC m). *)
    SUBGOAL_THEN (Parse.Term [QUOTE "g (SUC m) = f ((g:num->'a) m)"]) SUBST1_TAC THENL [
      RULE_ASSUM_TAC (REWRITE_RULE [SIMP_REC_REL]) THEN
      REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC) handle _ => ALL_TAC) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [LESS_SUC_SUC],
      ALL_TAC
    ] THEN AP_TERM_TAC THEN
    (* goal: g m = g' m ; both rels hold, m < SUC(SUC m) and m < SUC m *)
    STRIP_ASSUME_TAC (SPEC (Parse.Term [QUOTE "m:num"]) LESS_SUC_SUC) THEN
    IMP_RES_TAC SIMP_REC_REL_UNIQUE
  ]);

val SIMP_REC_THM = Theory.save_thm("SIMP_REC_THM", SIMP_REC_THM);
