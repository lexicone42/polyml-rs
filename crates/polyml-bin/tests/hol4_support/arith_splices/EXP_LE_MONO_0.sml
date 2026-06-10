local
  val EXP_LE_MONO_0_lemma = Tactical.prove(
    Parse.Term [QUOTE "!n a b. a <= b ==> a EXP n <= b EXP n"],
    Prim_rec.INDUCT_THEN numTheory.INDUCTION Tactic.ASSUME_TAC THENL [
      REWRITE_TAC [EXP, LESS_EQ_REFL],
      REWRITE_TAC [EXP] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC LESS_MONO_MULT2 THEN CONJ_TAC THENL [
        FIRST_ASSUM ACCEPT_TAC,
        FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC
      ]
    ])
in
val EXP_LE_MONO_0 = Tactical.prove(
  Parse.Term [QUOTE "!n. 0 < n ==> !a b. a <= b ==> a EXP n <= b EXP n"],
  REWRITE_TAC [EXP_LE_MONO_0_lemma])
end;
val EXP_LE_MONO_0 = Theory.save_thm("EXP_LE_MONO_0", EXP_LE_MONO_0);
val () = print "SPLICE_OK\n";

