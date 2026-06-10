(* EXP_LE_1: x ** y <= 1n <=> x <= 1 \/ y = 0
   EXP_EQ_1 lives AFTER this theorem in arithmeticScript, so we prove its
   content as a local lemma by induction on y, then rewrite + MESON. *)
val EXP_LE_1_eq1_lemma = Tactical.prove(
  Parse.Term [QUOTE "!y x. (x ** y = 1n) <=> (x = 1) \\/ (y = 0)"],
  Prim_rec.INDUCT_THEN numTheory.INDUCTION Tactic.ASSUME_TAC THENL [
    REWRITE_TAC [EXP],
    ASM_REWRITE_TAC [EXP, MULT_EQ_1, numTheory.NOT_SUC] THEN GEN_TAC THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC []
  ]);

val EXP_LE_1 = Tactical.prove(
  Parse.Term [QUOTE "x ** y <= 1n \226\135\148 x <= 1 \226\136\168 y = 0"],
  REWRITE_TAC [LE_LT, EXP_LT_1, LT1_EQ0, EXP_EQ_0, EXP_LE_1_eq1_lemma,
               GSYM NOT_ZERO_LT_ZERO] THEN
  mesonLib.MESON_TAC []);
val EXP_LE_1 = Theory.save_thm("EXP_LE_1", EXP_LE_1);
val () = print "SPLICE_OK\n";

