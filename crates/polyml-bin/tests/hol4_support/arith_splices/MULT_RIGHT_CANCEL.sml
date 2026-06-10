val MULT_RIGHT_CANCEL = Tactical.prove(
  Parse.Term [QUOTE "!m n p. (n * p = m * p) <=> (p = 0) \\/ (n = m)"],
  REWRITE_TAC [EQ_MULT_RCANCEL]);
val MULT_RIGHT_CANCEL = Theory.save_thm("MULT_RIGHT_CANCEL", MULT_RIGHT_CANCEL);
val () = print "SPLICE_OK\n";

