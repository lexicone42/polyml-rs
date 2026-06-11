(* fleet-verified 2026-06-10: upstream proof needs Q.ABBREV_TAC (markerLib
   raise-stub) + SRW counts. Rebuilt LCF-style. Reusable idiom: positional
   constant-conversion `CONV_TAC (LAND_CONV (RAND_CONV (fn _ => e1)))` to
   expand DIVISION at ONE occurrence (REWRITE matches every subterm; SUBST
   would also hit the m1 inside `m1 DIV n`). MOD_TIMES here is the modern
   UNCONDITIONAL form (q*n + r) MOD n = r MOD n. *)
val mneq_th1 = Drule.SPECL [Parse.Term [QUOTE "n:num"], Parse.Term [QUOTE "a:num"],
                            Parse.Term [QUOTE "m1:num"]] arithmeticTheory.MOD_TIMES;
val mneq_th2 = Drule.SPECL [Parse.Term [QUOTE "n:num"], Parse.Term [QUOTE "b:num"],
                            Parse.Term [QUOTE "m2:num"]] arithmeticTheory.MOD_TIMES;
val mneq_divn = Drule.MATCH_MP arithmeticTheory.DIVISION
                               (Thm.ASSUME (Parse.Term [QUOTE "0 < n"]));
val mneq_e1 = Thm.CONJUNCT1 (Thm.SPEC (Parse.Term [QUOTE "m1:num"]) mneq_divn);
val mneq_e2 = Thm.CONJUNCT1 (Thm.SPEC (Parse.Term [QUOTE "m2:num"]) mneq_divn);

val MODEQ_NONZERO_MODEQUALITY = Tactical.prove(
  Parse.Term [QUOTE "0 < n ==> (MODEQ n m1 m2 <=> (m1 MOD n = m2 MOD n))"],
  DISCH_TAC THEN
  REWRITE_TAC [arithmeticTheory.MODEQ_DEF] THEN
  EQ_TAC THENL [
    STRIP_TAC THEN
    Tactic.SUBST_TAC [Thm.SYM mneq_th1, Thm.SYM mneq_th2] THEN
    ASM_REWRITE_TAC [],
    DISCH_TAC THEN
    EXISTS_TAC (Parse.Term [QUOTE "m2 DIV n"]) THEN
    EXISTS_TAC (Parse.Term [QUOTE "m1 DIV n"]) THEN
    CONV_TAC (Conv.LAND_CONV (Conv.RAND_CONV (fn _ => mneq_e1))) THEN
    CONV_TAC (Conv.RAND_CONV (Conv.RAND_CONV (fn _ => mneq_e2))) THEN
    ASM_REWRITE_TAC [arithmeticTheory.ADD_ASSOC] THEN
    CONV_TAC (Conv.LAND_CONV (Conv.LAND_CONV (Conv.REWR_CONV arithmeticTheory.ADD_SYM))) THEN
    REFL_TAC
  ]);
val MODEQ_NONZERO_MODEQUALITY =
    Theory.save_thm("MODEQ_NONZERO_MODEQUALITY", MODEQ_NONZERO_MODEQUALITY);
val () = print "SPLICE_OK\n";
