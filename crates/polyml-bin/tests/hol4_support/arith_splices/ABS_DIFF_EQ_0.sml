val ABS_DIFF_EQ_0 = Tactical.prove(
  Parse.Term [QUOTE "!n m. (ABS_DIFF n m = 0) <=> (n = m)"],
  REPEAT GEN_TAC THEN REWRITE_TAC [ABS_DIFF_def] THEN
  Tactic.ASM_CASES_TAC (Parse.Term [QUOTE "n < m"]) THEN
  ASM_REWRITE_TAC [SUB_EQ_0] THEN
  mesonLib.ASM_MESON_TAC [NOT_LESS, LESS_OR_EQ, LESS_EQUAL_ANTISYM,
                          LESS_ANTISYM, prim_recTheory.LESS_REFL,
                          prim_recTheory.LESS_NOT_EQ]);
val ABS_DIFF_EQ_0 = Theory.save_thm("ABS_DIFF_EQ_0", ABS_DIFF_EQ_0);
val () = print "SPLICE_OK\n";

