(* prim_rec Stage-1 fragment: SIMP_REC specification without bool_ss SIMP_RULE.
   Upstream: new_specification over
     (CONJUNCT1 o SIMP_RULE bool_ss [EXISTS_UNIQUE_THM]
                o SIMP_RULE bool_ss [UNIQUE_SKOLEM_THM]) SIMP_REC_REL_UNIQUE_RESULT
   Our synthesized boolTheory lacks UNIQUE_SKOLEM_THM, and both SIMP_RULEs are
   higher-order rewrites. This is the num_arith_trophy.sml replacement: prove
   UNIQUE_SKOLEM_THM by hand (HO-aware depth rewrite + explicit witness), then
   apply the two rewrites via CONV_RULE/TOP_DEPTH_CONV/HO_REWR_CONV.
   UNIQUE_SKOLEM_THM is a local SML binding, not saved (it belongs to bool). *)

val UNIQUE_SKOLEM_THM =
  let
    val hoConv = Conv.TOP_DEPTH_CONV
        (Conv.FIRST_CONV [Conv.HO_REWR_CONV EXISTS_UNIQUE_THM,
                          Conv.HO_REWR_CONV FORALL_AND_THM,
                          Conv.HO_REWR_CONV SKOLEM_THM])
    val HO_RW_TAC = Tactic.CONV_TAC hoConv
  in
    Tactical.prove(
      Parse.Term [QUOTE "!P. (!x:'a. ?!y:'b. P x y) = ?!f. !x. P x (f x)"],
      GEN_TAC THEN HO_RW_TAC
       THEN EQ_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)
       THEN ASM_REWRITE_TAC[] THENL
        [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
         X_GEN_TAC (Parse.Term [QUOTE "x:'a"]) THEN FIRST_ASSUM MATCH_MP_TAC THEN
         EXISTS_TAC (Parse.Term [QUOTE "x:'a"]) THEN ASM_REWRITE_TAC[],
         MAP_EVERY X_GEN_TAC
           [Parse.Term [QUOTE "x:'a"], Parse.Term [QUOTE "y1:'b"],
            Parse.Term [QUOTE "y2:'b"]]
         THEN STRIP_TAC THEN
         FIRST_ASSUM(X_CHOOSE_TAC (Parse.Term [QUOTE "f:'a->'b"])) THEN
         SUBGOAL_THEN
           (Parse.Term [QUOTE
              "(\\z. if z=x then y1 else (f:'a->'b) z) = (\\z. if z=x then y2 else (f:'a->'b) z)"])
           MP_TAC THENL
          [FIRST_ASSUM MATCH_MP_TAC THEN
           REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
           ASM_REWRITE_TAC[],
           DISCH_THEN(MP_TAC o C AP_THM (Parse.Term [QUOTE "x:'a"])) THEN
           BETA_TAC THEN REWRITE_TAC[]]])
  end;

val skol_rule =
  Conv.CONV_RULE (Conv.TOP_DEPTH_CONV (Conv.HO_REWR_CONV UNIQUE_SKOLEM_THM));
val euq_rule =
  Conv.CONV_RULE (Conv.TOP_DEPTH_CONV (Conv.HO_REWR_CONV EXISTS_UNIQUE_THM));

val SIMP_REC = new_specification
  ("SIMP_REC", ["SIMP_REC"],
   (CONJUNCT1 o euq_rule o skol_rule) SIMP_REC_REL_UNIQUE_RESULT);
