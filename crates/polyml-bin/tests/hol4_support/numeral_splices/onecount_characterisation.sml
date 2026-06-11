(* fleet-verified 2026-06-11: upstream onecount_characterisation uses SRW/
   sub_eq' (THENL-fragile here). Self-contained re-proof: re-proves the
   onecount_lemma1/2/3 as ocl1/2/3 with plain tactics + a BIT1 helper ocl4,
   routing around sub_eq'/sub_add'. NOTE the first line: the raw checkpoint
   grammar lost the segment-local 'onecount' constant (parses as a free var,
   silently no-ops REWRITE_TAC [onecount_def]); overload_on re-binds it
   (idempotent). Avoid REWRITE_TAC[BIT1, GSYM ONE] together — VM-halt loop. *)
val () = Parse.overload_on ("onecount", Term.prim_mk_const {Name = "onecount", Thy = "numeral"});
val oc0 = REWRITE_RULE [arithmeticTheory.ALT_ZERO] (CONJUNCT1 onecount_def);
val ocl1 = Tactical.prove(
  Parse.Term [QUOTE "!n a. 0 < onecount n a ==> a <= onecount n a"],
  Prim_rec.INDUCT_THEN bit_induction ASSUME_TAC THENL [
    REWRITE_TAC [onecount_def, arithmeticTheory.LESS_EQ_REFL],
    REWRITE_TAC [onecount_def] THEN GEN_TAC THEN DISCH_TAC THEN RES_TAC THEN
    ASSUME_TAC (SPEC (Parse.Term [QUOTE "a:num"]) arithmeticTheory.LESS_EQ_SUC_REFL) THEN
    IMP_RES_TAC arithmeticTheory.LESS_EQ_TRANS THEN FIRST_ASSUM ACCEPT_TAC,
    REWRITE_TAC [onecount_def, arithmeticTheory.ALT_ZERO, prim_recTheory.LESS_REFL]
  ]);
val ocl2 = Tactical.prove(
  Parse.Term [QUOTE "!n. 0 < n ==> !a b. (onecount n a = 0) = (onecount n b = 0)"],
  Prim_rec.INDUCT_THEN bit_induction ASSUME_TAC THENL [
    REWRITE_TAC [arithmeticTheory.ALT_ZERO, prim_recTheory.LESS_REFL],
    REWRITE_TAC [onecount_def] THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
    ASM_CASES_TAC (Parse.Term [QUOTE "0 < n"]) THENL [
      FIRST_ASSUM (fn th => ACCEPT_TAC
        (SPECL [Parse.Term [QUOTE "SUC a"], Parse.Term [QUOTE "SUC b"]]
               (MP th (ASSUME (Parse.Term [QUOTE "0 < n"]))))),
      POP_ASSUM (SUBST_ALL_TAC o REWRITE_RULE [arithmeticTheory.NOT_LT_ZERO_EQ_ZERO]) THEN
      REWRITE_TAC [oc0, numTheory.NOT_SUC]
    ],
    REWRITE_TAC [onecount_def]
  ]);
val ocl3 = Tactical.prove(
  Parse.Term [QUOTE "!n a. 0 < onecount n (SUC a) ==> (onecount n (SUC a) = SUC (onecount n a))"],
  Prim_rec.INDUCT_THEN bit_induction ASSUME_TAC THENL [
    REWRITE_TAC [onecount_def],
    REWRITE_TAC [onecount_def] THEN GEN_TAC THEN DISCH_TAC THEN RES_TAC THEN
    FIRST_ASSUM ACCEPT_TAC,
    REWRITE_TAC [onecount_def, arithmeticTheory.ALT_ZERO, prim_recTheory.LESS_REFL]
  ]);
val oc_two_exp_pos = REWRITE_RULE [GSYM arithmeticTheory.TWO]
  (SPECL [Parse.Term [QUOTE "x:num"], Parse.Term [QUOTE "1"]] arithmeticTheory.ZERO_LESS_EXP);
val oc_one_le = REWRITE_RULE [arithmeticTheory.LESS_EQ, GSYM arithmeticTheory.ONE] oc_two_exp_pos;
val oc_sad = MP (SPECL [Parse.Term [QUOTE "2 EXP x"], Parse.Term [QUOTE "1"]] arithmeticTheory.SUB_ADD) oc_one_le;
val oc_les = SPEC (Parse.Term [QUOTE "2 EXP x"])
  (MP (SPECL [Parse.Term [QUOTE "1"], Parse.Term [QUOTE "2 EXP x"]] arithmeticTheory.LESS_EQ_ADD_SUB) oc_one_le);
val ocl4 = Tactical.prove(
  Parse.Term [QUOTE "!x. BIT1 (2 EXP x - 1) = 2 EXP (SUC x) - 1"],
  GEN_TAC THEN
  CONV_TAC (Conv.LAND_CONV (Conv.REWR_CONV arithmeticTheory.BIT1)) THEN
  REWRITE_TAC [GSYM arithmeticTheory.ONE, arithmeticTheory.EXP,
               arithmeticTheory.TIMES2, oc_sad, oc_les] THEN
  CONV_TAC (Conv.LAND_CONV (Conv.REWR_CONV arithmeticTheory.ADD_SYM)) THEN
  REWRITE_TAC []);
val onecount_characterisation = Tactical.prove(
  Parse.Term [QUOTE "!n a. 0 < onecount n a /\\ 0 < n ==> (n = 2 EXP (onecount n a - a) - 1)"],
  Prim_rec.INDUCT_THEN bit_induction ASSUME_TAC THENL [
    REWRITE_TAC [arithmeticTheory.ALT_ZERO, prim_recTheory.LESS_REFL],
    REWRITE_TAC [onecount_def] THEN GEN_TAC THEN STRIP_TAC THEN
    IMP_RES_TAC ocl3 THEN
    ASM_CASES_TAC (Parse.Term [QUOTE "0 < n"]) THENL [
      SUBGOAL_THEN (Parse.Term [QUOTE "0 < onecount n a"]) ASSUME_TAC THENL [
        REWRITE_TAC [GSYM arithmeticTheory.NOT_ZERO_LT_ZERO] THEN DISCH_TAC THEN
        MP_TAC (SPECL [Parse.Term [QUOTE "SUC a"], Parse.Term [QUOTE "a:num"]]
                  (MP (SPEC (Parse.Term [QUOTE "n:num"]) ocl2)
                      (ASSUME (Parse.Term [QUOTE "0 < n"])))) THEN
        ASM_REWRITE_TAC [numTheory.NOT_SUC],
        IMP_RES_TAC ocl1 THEN
        SUBGOAL_THEN (Parse.Term [QUOTE "n = 2 EXP (onecount n a - a) - 1"]) ASSUME_TAC THENL [
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
          REWRITE_TAC [ASSUME (Parse.Term [QUOTE "onecount n (SUC a) = SUC (onecount n a)"]),
                       arithmeticTheory.SUB,
                       REWRITE_RULE [GSYM arithmeticTheory.NOT_LESS]
                         (ASSUME (Parse.Term [QUOTE "a <= onecount n a"]))] THEN
          CONV_TAC (Conv.LAND_CONV (Conv.RAND_CONV (Conv.REWR_CONV
                       (ASSUME (Parse.Term [QUOTE "n = 2 EXP (onecount n a - a) - 1"]))))) THEN
          REWRITE_TAC [ocl4]
        ]
      ],
      POP_ASSUM (SUBST_ALL_TAC o REWRITE_RULE [arithmeticTheory.NOT_LT_ZERO_EQ_ZERO]) THEN
      REWRITE_TAC [oc0] THEN
      REWRITE_TAC [arithmeticTheory.SUB, prim_recTheory.LESS_REFL, prim_recTheory.LESS_0,
                   arithmeticTheory.SUB_EQUAL_0, arithmeticTheory.EXP,
                   arithmeticTheory.MULT_CLAUSES, arithmeticTheory.NUMERAL_DEF,
                   arithmeticTheory.BIT1, arithmeticTheory.BIT2,
                   arithmeticTheory.ALT_ZERO, arithmeticTheory.ADD_CLAUSES]
    ],
    REWRITE_TAC [onecount_def, arithmeticTheory.ALT_ZERO, prim_recTheory.LESS_REFL]
  ]);

val () = print "SPLICE_OK\n";
