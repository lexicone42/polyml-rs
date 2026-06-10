(* prim_rec Stage-1 fragment: TC-free LESS_LEMMA1.
   Upstream proves LESS_LEMMA1 via the LESS_ALT transitive-closure
   characterization (relationTheory.TC/RTC), which this chain doesn't carry.
   This is the TC-free proof from num_arith_trophy.sml: induct on n with
   num_CASES + LESS_MONO_REV (both relationTheory-free). num_CASES is proved
   LOCALLY and not saved — the real one belongs to arithmeticTheory.
   Runs in the prim_recScript file context (boolLib open, INDUCT_TAC bound
   at script line 73 as INDUCT_THEN INDUCTION ASSUME_TAC). *)

val num_CASES_local = Tactical.prove(
  Parse.Term [QUOTE "!n. (n = 0) \\/ ?m. n = SUC m"],
  INDUCT_TAC THENL [
    DISJ1_TAC THEN REFL_TAC,
    DISJ2_TAC THEN EXISTS_TAC (Parse.Term [QUOTE "n:num"]) THEN REFL_TAC]);

val LESS_LEMMA1_AUX = Tactical.prove(
  Parse.Term [QUOTE "!n m. (m < SUC n) ==> (m = n) \\/ (m < n)"],
  INDUCT_TAC THENL [
    (* base: m < SUC 0 ==> m = 0 \/ m < 0 *)
    GEN_TAC THEN DISCH_TAC
      THEN STRIP_ASSUME_TAC (SPEC (Parse.Term [QUOTE "m:num"]) num_CASES_local)
      THENL [
        ASM_REWRITE_TAC[],
        (* m = SUC m': SUC m' < SUC 0 ==> m' < 0, contradiction *)
        POP_ASSUM SUBST_ALL_TAC
          THEN IMP_RES_TAC LESS_MONO_REV
          THEN IMP_RES_TAC NOT_LESS_0
      ],
    (* step: IH !m. m < SUC n ==> m = n \/ m < n *)
    GEN_TAC THEN DISCH_TAC
      THEN STRIP_ASSUME_TAC (SPEC (Parse.Term [QUOTE "m:num"]) num_CASES_local)
      THENL [
        DISJ2_TAC THEN ASM_REWRITE_TAC[LESS_0],
        POP_ASSUM SUBST_ALL_TAC
          THEN IMP_RES_TAC LESS_MONO_REV
          THEN RES_TAC
          THENL [
            DISJ1_TAC THEN ASM_REWRITE_TAC[],
            DISJ2_TAC THEN IMP_RES_TAC LESS_MONO THEN ASM_REWRITE_TAC[]
          ]
      ]
  ]);

(* Re-generalize to upstream's !m n. quantifier order before saving. *)
val LESS_LEMMA1 = Theory.save_thm("LESS_LEMMA1",
  GENL [Parse.Term [QUOTE "m:num"], Parse.Term [QUOTE "n:num"]]
       (SPEC_ALL LESS_LEMMA1_AUX));
