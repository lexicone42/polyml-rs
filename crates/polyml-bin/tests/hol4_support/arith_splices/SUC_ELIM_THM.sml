val SUC_ELIM_THM = Tactical.prove(
  Parse.Term [QUOTE "!P. (!n. P (SUC n) n) = (!n. (0 < n ==> P n (n-1)))"],
  GEN_TAC THEN EQ_TAC THENL [
    DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    Tactic.STRIP_ASSUME_TAC (SPEC (Parse.Term [QUOTE "n:num"]) num_CASES) THENL [
      simpLib.FULL_SIMP_TAC boolSimps.bool_ss [prim_recTheory.NOT_LESS_0],
      POP_ASSUM Tactic.SUBST_ALL_TAC THEN
      ASM_REWRITE_TAC [SUC_SUB1]
    ],
    DISCH_TAC THEN GEN_TAC THEN
    FIRST_ASSUM (Tactic.MP_TAC o SPEC (Parse.Term [QUOTE "SUC n"])) THEN
    REWRITE_TAC [prim_recTheory.LESS_0, SUC_SUB1] THEN
    DISCH_TAC THEN FIRST_ASSUM ACCEPT_TAC
  ]);
val SUC_ELIM_THM = Theory.save_thm("SUC_ELIM_THM", SUC_ELIM_THM);
val () = print "SPLICE_OK\n";

