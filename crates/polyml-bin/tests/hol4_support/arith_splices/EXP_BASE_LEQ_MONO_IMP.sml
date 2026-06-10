val EXP_BASE_LEQ_MONO_IMP = Tactical.prove(
  Parse.Term [QUOTE "!n m b. 0 < b /\\ m <= n ==> b ** m <= b ** n"],
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC LESS_EQUAL_ADD THEN
  ASM_REWRITE_TAC [EXP_ADD, LE_MULT_CANCEL_LBARE, ZERO_LT_EXP]);
val EXP_BASE_LEQ_MONO_IMP = Theory.save_thm("EXP_BASE_LEQ_MONO_IMP", EXP_BASE_LEQ_MONO_IMP);
val () = print "SPLICE_OK\n";

