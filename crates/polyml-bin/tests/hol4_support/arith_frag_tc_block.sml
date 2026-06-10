(* arithmetic Stage-4 fragment: prim_rec's TC block, restored.
   Stage 1 cut prim_recScript's TC block (lines 180-232) because
   relationTheory didn't exist yet; arithmeticScript references LESS_ALT /
   TC_IM_RTC_SUC / RTC_IM_TC unqualified (ancestor-open). relationTheory's
   TC/RTC machinery is on the chain now, so these are the UPSTREAM proofs
   ported verbatim (irule -> MATCH_MP_TAC; quotations expanded). Bound as
   SML vals (their save-home is prim_rec; a fidelity pass can re-home). *)

val INDUCT_TAC_tc =
    Prim_rec.INDUCT_THEN numTheory.INDUCTION Tactic.ASSUME_TAC;

val TC_LESS_0 = Tactical.prove(
  Parse.Term [QUOTE "!n. TC (\\x y. y = SUC x) 0 (SUC n)"],
  INDUCT_TAC_tc
  THENL [ MATCH_MP_TAC relationTheory.TC_SUBSET THEN BETA_TAC THEN REFL_TAC,
    ONCE_REWRITE_TAC [relationTheory.TC_CASES2] THEN DISJ2_TAC
    THEN EXISTS_TAC (Parse.Term [QUOTE "SUC n"]) THEN BETA_TAC
    THEN ASM_REWRITE_TAC [] ]);

val TC_NOT_LESS_0 = Tactical.prove(
  Parse.Term [QUOTE "!n. ~(TC (\\x y. y = SUC x) n 0)"],
  ONCE_REWRITE_TAC [relationTheory.TC_CASES2]
  THEN BETA_TAC THEN REWRITE_TAC [GSYM numTheory.NOT_SUC]);

val TC_IM_RTC_SUC = Tactical.prove(
  Parse.Term [QUOTE
    "!m n. TC (\\x y. y = SUC x) m (SUC n) = RTC (\\x y. y = SUC x) m n"],
  ONCE_REWRITE_TAC [relationTheory.TC_CASES2] THEN BETA_TAC
    THEN REWRITE_TAC [relationTheory.RTC_CASES_TC, prim_recTheory.INV_SUC_EQ]
    THEN REPEAT (STRIP_TAC ORELSE EQ_TAC)
    THEN ASM_REWRITE_TAC []
    THEN DISJ2_TAC THEN EXISTS_TAC (Parse.Term [QUOTE "n : num"])
    THEN ASM_REWRITE_TAC []);

val RTC_IM_TC = Tactical.prove(
  Parse.Term [QUOTE
    "!m n. RTC (\\x y. y = f x) (f m) n = TC (\\x y. y = f x) m n"],
  REWRITE_TAC [relationTheory.EXTEND_RTC_TC_EQN]
   THEN BETA_TAC THEN REPEAT (STRIP_TAC ORELSE EQ_TAC)
   THENL [Q.EXISTS_TAC [QUOTE "f m"],
     FIRST_X_ASSUM (ASSUME_TAC o SYM)]
   THEN ASM_REWRITE_TAC []);

val TC_LESS_MONO_EQ = Tactical.prove(
  Parse.Term [QUOTE
    "!m n. TC (\\x y. y = SUC x) (SUC m) (SUC n) = TC (\\x y. y = SUC x) m n"],
  REWRITE_TAC [TC_IM_RTC_SUC, RTC_IM_TC]);

val LESS_ALT = Tactical.prove(
  Parse.Term [QUOTE "$< = TC (\\x y. y = SUC x)"],
  REWRITE_TAC [boolTheory.FUN_EQ_THM] THEN
  INDUCT_TAC_tc THEN INDUCT_TAC_tc THEN
  REWRITE_TAC [prim_recTheory.NOT_LESS_0, TC_NOT_LESS_0,
    prim_recTheory.LESS_0, TC_LESS_0,
    TC_LESS_MONO_EQ, prim_recTheory.LESS_MONO_EQ]
  THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val () = print "TC_BLOCK_OK\n";
