(* fleet-verified 2026-06-11: upstream's `REWRITE_TAC [MIN_0] THEN REWRITE_TAC
   [MIN_DEF, NUMERAL_DEF]` no-ops here because the checkpoint's MIN_0 is stated
   over a STALE MIN constant (MIN was redefined during the arithmetic build
   after MIN_0 was captured). Re-prove from MIN_DEF directly via COND_CASES.
   Exact upstream statement. *)
val numeral_MIN = Tactical.prove(
  Parse.Term [QUOTE "(MIN 0 x = 0) /\\ (MIN x 0 = 0) /\\ (MIN (NUMERAL x) (NUMERAL y) = NUMERAL (if x < y then x else y))"],
  REWRITE_TAC [arithmeticTheory.MIN_DEF, arithmeticTheory.NUMERAL_DEF, prim_recTheory.NOT_LESS_0]
  THEN Tactic.COND_CASES_TAC THENL
  [ REWRITE_TAC [],
    POP_ASSUM MP_TAC THEN REWRITE_TAC [arithmeticTheory.NOT_LT_ZERO_EQ_ZERO]
    THEN DISCH_TAC THEN ASM_REWRITE_TAC [] ]);
val numeral_MIN = Theory.save_thm("numeral_MIN", numeral_MIN);
val () = print "SPLICE_OK\n";
