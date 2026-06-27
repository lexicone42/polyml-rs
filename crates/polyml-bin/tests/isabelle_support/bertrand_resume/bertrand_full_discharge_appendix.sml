(* ============================================================================
   FULL DISCHARGE : feed the REAL (PROVED) bertrand_chain into bertrand_given_chain
   to obtain the UNCONDITIONAL bertrand.  Appended after ch_appendix (which proves
   bertrand_chain via prime2_via_check up to 631) + the jewel (bertrand_given_chain).
   ============================================================================ *)
val () = out "FULL_DISCHARGE_BEGIN\n";

(* bertrand_chain (real, from ch_appendix) is varified : schematic ?n_chn.
   Convert to the meta-universal form !!n_chn. ... to match bertrand_given_chain's premise. *)
val bc_real_vars = Term.add_vars (Thm.prop_of bertrand_chain) [];
val () = out ("real bertrand_chain vars : " ^ String.concatWith "," (map (fn ((nm,_),_) => nm) bc_real_vars) ^ "\n");
val nChainFree = Free("n_chn", natT);
val bc_inst = beta_norm (Drule.infer_instantiate ctxtBL
      (map (fn (ix,_) => (ix, ctermBL nChainFree)) bc_real_vars) bertrand_chain);   (* lt 0 n ==> lt n 631 ==> Ex ... *)
val bc_meta = Thm.forall_intr (ctermBL nChainFree) bc_inst;   (* !!n. lt 0 n ==> lt n 631 ==> Ex ... *)
val () = out ("bc_meta 0hyp=" ^ Bool.toString (zhBL bc_meta) ^ "\n");
(* it must aconv bertrand_given_chain's premise (bertrand_chain_stmt) *)
val bc_meta_matches = (Thm.prop_of bc_meta) aconv bertrand_chain_stmt;
val () = out ("bc_meta aconv premise = " ^ Bool.toString bc_meta_matches ^ "\n");

val bertrand =
  (case bertrand_given_chain of
     SOME bgc => SOME (Thm.implies_elim bgc bc_meta)   (* the UNCONDITIONAL bertrand *)
   | NONE => NONE)
  handle e => (out ("bertrand EXN : " ^ General.exnMessage e ^ "\n"); NONE);

val bert_0hyp = (case bertrand of SOME th => (null (Thm.hyps_of th) andalso null (Thm.extra_shyps th)) | NONE => false);
val bert_aconv =
  (case bertrand of
     SOME th =>
       let val nF = Free("n_bert", natT)
           val bertGoal = Logic.all nF (Logic.mk_implies (jT (lt ZeroC nF), jT (mkEx (bert_body nF))))
       in (Thm.prop_of th) aconv bertGoal end
   | NONE => false);
val () = out ("bertrand 0hyp=" ^ Bool.toString bert_0hyp ^ " aconv=" ^ Bool.toString bert_aconv ^ "\n");

(* range soundness : bertrand must NOT be the weakened le p n form *)
val bert_range =
  (case bertrand of
     SOME th =>
       let val nF = Free("n_bert", natT)
           val bbW = Term.lambda (Free("p_bw", natT))
                       (mkConj (prime2 (Free("p_bw", natT)))
                               (mkConj (lt nF (Free("p_bw", natT)))(le (Free("p_bw", natT)) nF)))
           val bertGoalW = Logic.all nF (Logic.mk_implies (jT (lt ZeroC nF), jT (mkEx bbW)))
       in not ((Thm.prop_of th) aconv bertGoalW) end
   | NONE => false);
val () = if bert_range then out "BERTRAND_FULL_RANGE_PROBE_OK (strict prime in (n,2n], prime2 structural)\n"
         else out "BERTRAND_FULL_RANGE_PROBE_FAIL\n";

val () = if bert_0hyp andalso bert_aconv then out "BERTRAND_OK\n" else out "BERTRAND_FAIL\n";

(* ---- final axiom audit : only ex_middle classical + the 2 bitlen conservative eqns ;
   NO smuggled prime-existence / bertrand / seb / crude / inequality / chain axiom. ---- *)
val () =
  let
    val thy = Proof_Context.theory_of ctxtBL
    val names = map fst (Theory.all_axioms_of thy)
    val classical = List.filter (fn s => String.isSubstring "ex_middle" s orelse String.isSubstring "excluded" s) names
    val bitlenAx = List.filter (fn s => String.isSubstring "bitlen" s) names
    val suspicious = List.filter (fn s =>
         String.isSubstring "bertrand" s orelse String.isSubstring "prime_exist" s
         orelse String.isSubstring "chebyshev" s orelse String.isSubstring "postulate" s
         orelse String.isSubstring "seb" s orelse String.isSubstring "threshold" s
         orelse String.isSubstring "window" s orelse String.isSubstring "crude" s
         orelse String.isSubstring "pow_bound" s orelse String.isSubstring "poly_ineq" s
         orelse String.isSubstring "inequality" s orelse String.isSubstring "chain" s
         orelse String.isSubstring "163" s orelse String.isSubstring "317" s orelse String.isSubstring "631" s) names
  in out ("BERTRAND_FINAL_AXIOM_AUDIT total=" ^ Int.toString (length names)
          ^ " classical=" ^ Int.toString (length classical)
          ^ " bitlen_axioms=" ^ Int.toString (length bitlenAx)
          ^ " suspicious=" ^ Int.toString (length suspicious) ^ "\n");
     app (fn s => out ("  CLASSICAL: " ^ s ^ "\n")) classical;
     app (fn s => out ("  BITLEN AXIOM: " ^ s ^ "\n")) bitlenAx;
     app (fn s => out ("  SUSPICIOUS AXIOM: " ^ s ^ "\n")) suspicious
  end;

val () = if bert_0hyp andalso bert_aconv andalso bert_range then out "BERTRAND_PROVED\n"
         else out "BERTRAND_NOT_PROVED\n";
val () = out "FULL_DISCHARGE_DONE\n";
val () = OS.Process.exit OS.Process.success;
