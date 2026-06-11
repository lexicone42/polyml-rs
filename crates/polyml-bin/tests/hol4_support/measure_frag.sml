(* measure_def / WF_measure / measure_thm: prim_recScript:669-690, cut with
   Stage 1's WF tail but needed by TotalDefn (the default termination relation
   is measure-based). Rebuilt from inv_image + WF_inv_image + WF_LESS, all of
   which DID land (relation stage). Defined into the current segment; a
   `structure prim_recTheory` shim re-exports them alongside the existing ones. *)
fun msr_pr s = (print s; TextIO.flushOut TextIO.stdOut);
local open boolLib in
val measure_def = Theory.Definition.new_definition
  ("measure_def", Parse.Term [QUOTE "measure = inv_image $<"]);
val WF_measure = Tactical.prove(
  Parse.Term [QUOTE "!m. WF (measure m)"],
  REWRITE_TAC [measure_def]
  THEN MATCH_MP_TAC relationTheory.WF_inv_image
  THEN ACCEPT_TAC prim_recTheory.WF_LESS);
val WF_measure = Theory.save_thm ("WF_measure", WF_measure);
val measure_thm = Tactical.prove(
  Parse.Term [QUOTE "!f x y. measure f x y <=> f x < f y"],
  REWRITE_TAC [measure_def, relationTheory.inv_image_def] THEN BETA_TAC THEN
  REWRITE_TAC []);
val measure_thm = Theory.save_thm ("measure_thm", measure_thm);
(* WF_PRED (prim_rec): TotalDefn's tfl_WF initial set needs it; cut with the
   WF tail. Proof from numeral_frag_wf_less. *)
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
val WF_PRED = Theory.save_thm ("WF_PRED", WF_PRED);
end;
(* widen prim_recTheory so TotalDefn's `open prim_recTheory`-style refs see
   measure_def/WF_measure/measure_thm/WF_PRED. *)
structure prim_recTheory = struct
  open prim_recTheory
  val measure_def = measure_def
  val WF_measure = WF_measure
  val measure_thm = measure_thm
  val WF_PRED = WF_PRED
end;
val () = msr_pr "MEASURE_FRAG_OK\n";
