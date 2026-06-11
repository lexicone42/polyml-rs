(* fleet-verified 2026-06-10: sidesteps the hung expbase_le/lt_mono + METIS
   route entirely. EXP_BASE_LT_HELPER IS expbase_lt_mono (curried) — reusable
   if more of the expbase family is ever needed. All THENL counts structural.
   Gotcha log: Drule.GSYM doesn't exist here (use bare GSYM); LESS_TRANS must
   be MP'd with explicit SPECL (MATCH_MP_TAC can't bind the middle term). *)
val ONE_LT_IMP_ZERO_LT = Tactical.prove(
  Parse.Term [QUOTE "!b. 1 < b ==> 0 < b"],
  INDUCT_TAC THEN REWRITE_TAC [prim_recTheory.NOT_LESS_0, prim_recTheory.LESS_0]);

val EXP_STEP_LT = Tactical.prove(
  Parse.Term [QUOTE "!b k. 1 < b ==> b EXP k < b * b EXP k"],
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC (Conv.LAND_CONV (Conv.REWR_CONV (GSYM arithmeticTheory.MULT_LEFT_1))) THEN
  REWRITE_TAC [arithmeticTheory.LT_MULT_RCANCEL] THEN
  ASM_REWRITE_TAC [arithmeticTheory.ZERO_LT_EXP] THEN
  DISJ1_TAC THEN MATCH_MP_TAC ONE_LT_IMP_ZERO_LT THEN FIRST_ASSUM ACCEPT_TAC);

val EXP_BASE_LT_HELPER = Tactical.prove(
  Parse.Term [QUOTE "!b. 1 < b ==> !n m. m < n ==> b EXP m < b EXP n"],
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL [
    GEN_TAC THEN REWRITE_TAC [prim_recTheory.NOT_LESS_0],
    GEN_TAC THEN REWRITE_TAC [prim_recTheory.LESS_THM] THEN STRIP_TAC THENL [
      ASM_REWRITE_TAC [arithmeticTheory.EXP] THEN
      MATCH_MP_TAC EXP_STEP_LT THEN FIRST_ASSUM ACCEPT_TAC,
      RES_TAC THEN REWRITE_TAC [arithmeticTheory.EXP] THEN
      MP_TAC (SPECL [Parse.Term [QUOTE "b EXP m"],
                     Parse.Term [QUOTE "b EXP n"],
                     Parse.Term [QUOTE "b * b EXP n"]] arithmeticTheory.LESS_TRANS) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC EXP_STEP_LT THEN FIRST_ASSUM ACCEPT_TAC
    ]
  ]);

val EXP_BASE_INJECTIVE = Tactical.prove(
  Parse.Term [QUOTE "!b. 1 < b ==> !n m. (b EXP n = b EXP m) = (n = m)"],
  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN EQ_TAC THENL [
    DISCH_TAC THEN
    MP_TAC (SPECL [Parse.Term [QUOTE "m:num"], Parse.Term [QUOTE "n:num"]]
              (Drule.MATCH_MP EXP_BASE_LT_HELPER
                 (Thm.ASSUME (Parse.Term [QUOTE "1 < b"])))) THEN
    MP_TAC (SPECL [Parse.Term [QUOTE "n:num"], Parse.Term [QUOTE "m:num"]]
              (Drule.MATCH_MP EXP_BASE_LT_HELPER
                 (Thm.ASSUME (Parse.Term [QUOTE "1 < b"])))) THEN
    MP_TAC (SPECL [Parse.Term [QUOTE "n:num"], Parse.Term [QUOTE "m:num"]]
              arithmeticTheory.LESS_CASES) THEN
    ASM_REWRITE_TAC [arithmeticTheory.LESS_OR_EQ, prim_recTheory.LESS_REFL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [],
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC []
  ]);
val EXP_BASE_INJECTIVE = Theory.save_thm("EXP_BASE_INJECTIVE", EXP_BASE_INJECTIVE);
val () = print "SPLICE_OK\n";
