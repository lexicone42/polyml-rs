(* numeral fragment: prim_rec's WF_LESS, restored from the cut WF tail.
   Upstream proofs verbatim (prim_recScript:636-664); all deps now exist
   (LESS_ALT via arith_frag_tc_block, relationTheory.WF_TC_EQN/WF_DEF,
   Ho_Rewrite). prim_recTheory is widened so the qualified references in
   numeralScript resolve. *)

val WF_PRED = Tactical.prove(
  Parse.Term [QUOTE "WF \\x y. y = SUC x"],
  REWRITE_TAC [relationTheory.WF_DEF] THEN BETA_TAC THEN GEN_TAC
   THEN Tactic.CONV_TAC Conv.CONTRAPOS_CONV
   THEN Ho_Rewrite.REWRITE_TAC
         [boolTheory.NOT_FORALL_THM, boolTheory.NOT_EXISTS_THM,
          boolTheory.NOT_IMP, boolTheory.DE_MORGAN_THM]
   THEN REWRITE_TAC [GSYM boolTheory.IMP_DISJ_THM]
   THEN DISCH_TAC
   THEN Prim_rec.INDUCT_THEN numTheory.INDUCTION Tactic.ASSUME_TAC
   THEN CCONTR_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [])
   THEN RES_TAC
   THEN RULE_ASSUM_TAC
          (REWRITE_RULE [prim_recTheory.INV_SUC_EQ, GSYM numTheory.NOT_SUC])
   THENL (map FIRST_ASSUM [ACCEPT_TAC, MATCH_MP_TAC])
   THEN Rewrite.FILTER_ASM_REWRITE_TAC boolSyntax.is_eq []
   THEN ASM_REWRITE_TAC []);

val WF_LESS = Tactical.prove(
  Parse.Term [QUOTE "WF $<"],
  REWRITE_TAC [LESS_ALT, relationTheory.WF_TC_EQN, WF_PRED]);

structure prim_recTheory = struct
  open prim_recTheory
  val WF_LESS = WF_LESS
end;

val () = print "WF_LESS_OK\n";
