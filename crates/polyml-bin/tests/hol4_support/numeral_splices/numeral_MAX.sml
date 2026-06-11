(* fleet-verified 2026-06-11: see numeral_MIN.sml (stale MAX_0 same story).
   Exact upstream statement. *)
val numeral_MAX = Tactical.prove(
  Parse.Term [QUOTE "(MAX 0 x = x) /\\ (MAX x 0 = x) /\\ (MAX (NUMERAL x) (NUMERAL y) = NUMERAL (if x < y then y else x))"],
  REWRITE_TAC [arithmeticTheory.MAX_DEF, arithmeticTheory.NUMERAL_DEF,
               prim_recTheory.NOT_LESS_0] THEN
  Tactic.COND_CASES_TAC THENL [
    REWRITE_TAC [],
    MP_TAC (SPEC (Parse.Term [QUOTE "x:num"]) arithmeticTheory.LESS_0_CASES) THEN
    ASM_REWRITE_TAC []
  ]);
val numeral_MAX = Theory.save_thm("numeral_MAX", numeral_MAX);
val () = print "SPLICE_OK\n";
