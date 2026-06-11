(* fleet-verified 2026-06-10: see MIN_0.sml. *)
val MAX_0 = Tactical.prove(
  Parse.Term [QUOTE "!n. (MAX n 0 = n) /\\ (MAX 0 n = n)"],
  GEN_TAC THEN CONJ_TAC THENL [
    REWRITE_TAC [arithmeticTheory.MAX_DEF, prim_recTheory.NOT_LESS_0,
                 boolTheory.COND_CLAUSES],
    REWRITE_TAC [arithmeticTheory.MAX_DEF] THEN Tactic.COND_CASES_TAC THENL [
      REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN
      REWRITE_TAC [arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_OR_EQ,
                   prim_recTheory.NOT_LESS_0] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC []
    ]
  ]);
val MAX_0 = Theory.save_thm("MAX_0", MAX_0);
val () = print "SPLICE_OK\n";
