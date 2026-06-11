(* fleet-verified 2026-06-10: MIN/MAX section is skip-prefixed (hangs under
   the simp shims) but MIN_DEF/MAX_DEF ARE saved; numeralScript needs MIN_0.
   COND_CASES_TAC pattern; NOT_LESS_0 lives in prim_recTheory on this image. *)
val MIN_0 = Tactical.prove(
  Parse.Term [QUOTE "!n. (MIN n 0 = 0) /\\ (MIN 0 n = 0)"],
  GEN_TAC THEN CONJ_TAC THENL [
    REWRITE_TAC [arithmeticTheory.MIN_DEF, prim_recTheory.NOT_LESS_0,
                 boolTheory.COND_CLAUSES],
    REWRITE_TAC [arithmeticTheory.MIN_DEF] THEN Tactic.COND_CASES_TAC THENL [
      REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN
      REWRITE_TAC [arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_OR_EQ,
                   prim_recTheory.NOT_LESS_0] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC []
    ]
  ]);
val MIN_0 = Theory.save_thm("MIN_0", MIN_0);
val () = print "SPLICE_OK\n";
