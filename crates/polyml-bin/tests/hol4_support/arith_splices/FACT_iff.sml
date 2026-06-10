val FACT_iff = Tactical.prove(
  Parse.Term [QUOTE "!f. f = FACT <=> f 0 = 1 /\\ !n. f (SUC n) = SUC n * f n"],
  GEN_TAC THEN EQ_TAC THENL [
    DISCH_TAC THEN ASM_REWRITE_TAC [FACT],
    STRIP_TAC THEN REWRITE_TAC [boolTheory.FUN_EQ_THM] THEN
    Prim_rec.INDUCT_THEN numTheory.INDUCTION Tactic.ASSUME_TAC THEN
    ASM_REWRITE_TAC [FACT]
  ]);
val FACT_iff = Theory.save_thm("FACT_iff", FACT_iff);
val () = print "SPLICE_OK\n";

