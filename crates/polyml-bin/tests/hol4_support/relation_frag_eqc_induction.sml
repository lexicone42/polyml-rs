(* relation Stage-2 fragment: EQC_INDUCTION.
   Upstream's proof finds the TC assumption with Q.PAT_X_ASSUM after a
   FULL_SIMP — the pattern match fails on this chain (assumption shape
   differs). Restructured: rewrite EQC/RC first, STRIP case-splits the
   disjunction, so the TC assumption is simply on top (POP_ASSUM). *)

val EQC_INDUCTION = Tactical.prove(
  Parse.Term [QUOTE
    "!R P. (!x y. R x y ==> P x y) /\\ (!x. P x x) /\\ (!x y. P x y ==> P y x) /\\ (!x y z. P x y /\\ P y z ==> P x z) ==> (!x y. EQC R x y ==> P x y)"],
  REPEAT GEN_TAC THEN STRIP_TAC
   THEN REWRITE_TAC [EQC_DEF, RC_DEF]
   THEN REPEAT GEN_TAC THEN STRIP_TAC
   THENL [
     (* x = y *)
     POP_ASSUM SUBST1_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC,
     (* TC (SC R) x y *)
     POP_ASSUM MP_TAC
       THEN MAP_EVERY Q.ID_SPEC_TAC [[QUOTE "y"], [QUOTE "x"]]
       THEN HO_MATCH_MP_TAC TC_INDUCT
       THEN REWRITE_TAC [SC_DEF]
       THEN ASM_MESON_TAC []
   ]);

val EQC_INDUCTION = Theory.save_thm("EQC_INDUCTION", EQC_INDUCTION);
