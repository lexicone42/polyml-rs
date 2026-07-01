(* ============================================================================
   SHARED SOUNDNESS AUDIT  (sound_audit.sml)
   ----------------------------------------------------------------------------
   ONE machine-checked marker certifying an Isabelle/Pure theorem is sound:

     SOUND_AUDIT_OK   <name>              (all checks pass)
     SOUND_AUDIT_FAIL <name> <reasons>    (any check fails; details follow)

   Given the driver's final theorem(s) `ths`, `sound_audit` checks:
     (a) ORACLE-FREE : Thm_Deps.all_oracles ths = []  (detects add_oracle /
         Skip_Proof taint; works even under Proofterm.proofs := 0, which the
         heavy proofs set).  hyps_of=[] does NOT catch oracle taint, so this is
         a genuinely new gate.
     (b) AXIOM ALLOWLIST : every axiom base-name in the final theory
         (Theory.all_axioms_of, via Long_Name.base_name) is a recognized
         CONSERVATIVE name — a member of sound_audit_driver_axioms union the 11
         Pure built-ins — AND the classical count (base-name = "ex_middle") is
         EXACTLY 1.  This is an ALLOWLIST (strictly stronger than the previous
         name-substring blacklist): a substantive axiom under an innocuous name
         is caught because it is simply NOT a recognized conservative name.
     (c) 0-HYP : hyps_of = [] AND extra_shyps = [] on every thm.

   This is prepended (as an epilogue) by the Rust test harness
   (common::with_sound_audit); it depends only on Isabelle/Pure structures, so
   it runs uniformly on both the with_nt_helpers-spliced drivers and the big
   self-contained ones (bertrand / QR / four_square / two_square).
   ============================================================================ *)

(* --- 235 driver axiom base-names (object-logic ND rules + Peano + fresh-
   constant defining/recursion equations); the single classical axiom is
   ex_middle. Authoritative: every add_axiom_global in the driver tree uses a
   LITERAL Binding.name; this is the audit enumeration union the committed
   extraction (harmless over-inclusion of absent names is sound). --- *)
val sound_audit_driver_axioms : string list =
 [
  "LallE", "LallI", "Suc_inj", "Suc_neq_Zero", "add_0", "add_Suc", "allE", "allI",
  "all_prime_Cons_bwd", "all_prime_Cons_fwd", "all_prime_Nil", "append_Cons", "append_Nil",
  "bAll_E", "bAll_I", "badd_BD_BD", "badd_BD_BS", "badd_BD_BZ", "badd_BS_BD", "badd_BS_BS",
  "badd_BS_BZ", "badd_BZ", "baddc_BD_BD", "baddc_BD_BS", "baddc_BD_BZ", "baddc_BS_BD",
  "baddc_BS_BS", "baddc_BS_BZ", "baddc_BZ", "beq_refl", "beq_subst", "binom_0_Suc",
  "binom_Suc_Suc", "binom_n_0", "bitlen_Suc", "bitlen_Zero", "bmul_BD", "bmul_BS",
  "bmul_BZ", "bnat_induct", "bres_suc", "bres_zero", "bsucc_BD", "bsucc_BS", "bsucc_BZ",
  "cnt_0", "cnt_Suc_f", "cnt_Suc_t", "conjE1", "conjE2", "conjI", "conjunct1", "conjunct2",
  "count_Cons_eq", "count_Cons_neq", "count_Nil", "cpf_0", "cpf_step_nonprime",
  "cpf_step_prime", "dbl_0", "dbl_S", "disjE", "disjI1", "disjI2", "div_mod_eq",
  "divlist_0", "divlist_Suc", "divmod_id", "dl2_0", "dl2_Suc", "dvl_def", "dvla_0",
  "dvla_dvd", "dvla_ndvd", "exE", "exE_L", "exI", "exI_L", "ex_middle", "ezQ_fold",
  "ezQ_unfold", "fact_0", "fact_Suc", "fdecA", "fdecB", "fib_0", "fib_1", "fib_SS",
  "fibsum_0", "fibsum_Suc", "finv_def", "fsearch_cons_eq", "fsearch_cons_neq",
  "fsearch_nil", "gcdf_step", "gcdf_zero", "gridres_suc", "gridres_zero", "impE", "impI",
  "in_list_Cons_bwd", "in_list_Cons_fwd", "in_list_Nil_elim", "ixlist_induct", "lallE",
  "lallI", "lappend_cons", "lappend_nil", "lar_hi", "lar_lo", "lcQ_fold", "lcQ_unfold",
  "length_Cons", "length_Nil", "leqL_refl", "leqL_subst", "leq_refl", "leq_refl_ll",
  "leq_subst", "leq_subst_ll", "lhd_cons", "list_induct", "list_induct_ll", "llen_cons",
  "llen_nil", "lmap2_cons", "lmap2_nil", "lmap_cons", "lmap_nil", "lmem_cons_bwd",
  "lmem_cons_fwd", "lmem_nil_elim", "lnodup_cons_bwd", "lnodup_cons_fwd", "lnodup_nil",
  "lprod_cons", "lprod_nil", "lremove_cons_eq", "lremove_cons_neq", "lremove_nil",
  "lsumf_cons", "lsumf_nil", "ltl_cons", "meta_nat_induct", "mp", "mprod_0", "mprod_Suc",
  "mult_0", "mult_Suc", "natOf_BD", "natOf_BS", "natOf_BZ", "nat_induct", "oFalse_elim",
  "oeq_refl", "oeq_subst", "oimpE", "oimpI", "osum_0", "osum_Suc", "parity_0",
  "parity_Suc", "pfree_0", "pfree_dvd", "pfree_ndvd", "phiU_def", "phi_def", "pow_Suc",
  "pow_Zero", "prime_cases", "primorial_0", "primorial_Suc_nonprime",
  "primorial_Suc_prime", "prodf_0", "prodf_Suc", "product_Cons", "product_Nil", "rallE",
  "rallI", "rangelist_suc", "rangelist_zero", "remove1_Cons_eq", "remove1_Cons_neq",
  "remove1_Nil", "rep_ICons", "rep_INil", "req_cons", "req_cons_nil", "req_nil_cons",
  "req_refl", "reverse_Cons", "reverse_Nil", "rexE", "rexI", "rfilter_cons_in",
  "rfilter_cons_out", "rfilter_nil", "rmod_lt", "rmod_lt_th", "rrl_def", "sigma_def",
  "spec", "sub_0", "sub_0_Suc", "sub_SS", "sub_Suc_Suc", "sub_Z", "sub_n_0", "sub_recover",
  "sum_0", "sum_Suc", "sumf_0", "sumf_Suc", "swt_dvd", "swt_ndvd", "ufilter_cons_in",
  "ufilter_cons_out", "ufilter_nil", "uprod_0", "uprod_Suc", "upto_suc", "upto_zero",
  "urrl_def", "valid_INil", "valid_fold", "valid_unfold", "vb_INil", "vb_cons", "vb_lt",
  "vb_tl", "vp_step_dvd", "vp_step_ndvd", "zfib_0", "zfib_1", "zfib_SS"
 ];

(* --- the 11 Pure built-in axioms (base names, enumerated live from a bare
   restore_pure_context ()) --- *)
val sound_audit_pure_axioms : string list =
 [
  "prop_def", "term_def", "reflexive", "symmetric", "equal_elim", "equal_intr",
  "transitive", "combination", "abstract_rule", "conjunction_def", "sort_constraint_def"
 ];

local
  fun mem (x:string) xs = List.exists (fn y => y = x) xs
  val allow = sound_audit_driver_axioms @ sound_audit_pure_axioms
  fun pr s = (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut)
in
  (* sound_audit : string -> thm list -> unit *)
  fun sound_audit name (ths : thm list) =
    let
      val ths = if null ths then raise Fail "sound_audit: empty thm list" else ths
      val thy = Thm.theory_of_thm (List.last ths)
      val axnames = map (Long_Name.base_name o fst) (Theory.all_axioms_of thy)
      val notAllowed = List.filter (fn n => not (mem n allow)) axnames
      val classical = List.filter (fn n => n = "ex_middle") axnames
      val oracleNames = map (fn ((nm,_),_) => nm) (Thm_Deps.all_oracles ths)
      val nh = List.foldl (fn (t,a) => a + length (Thm.hyps_of t)) 0 ths
      val nshy = List.foldl (fn (t,a) => a + length (Thm.extra_shyps t)) 0 ths
      val okOracle   = null oracleNames
      val okAxioms   = null notAllowed
      val okClassical= (length classical = 1)
      val okHyps     = (nh = 0)
      val okShyps    = (nshy = 0)
    in
      if okOracle andalso okAxioms andalso okClassical andalso okHyps andalso okShyps
      then pr ("SOUND_AUDIT_OK " ^ name ^ "\n")
      else
        (pr ("SOUND_AUDIT_FAIL " ^ name
             ^ " oracle=" ^ Int.toString (length oracleNames)
             ^ " nonallowlisted_axioms=" ^ Int.toString (length notAllowed)
             ^ " classical=" ^ Int.toString (length classical)
             ^ " hyps=" ^ Int.toString nh
             ^ " extra_shyps=" ^ Int.toString nshy ^ "\n");
         app (fn n => pr ("  NONALLOWLISTED_AXIOM " ^ n ^ "\n")) notAllowed;
         app (fn n => pr ("  ORACLE " ^ n ^ "\n")) oracleNames)
    end
    handle e => (pr ("SOUND_AUDIT_FAIL " ^ name ^ " EXN "
                     ^ (General.exnMessage e) ^ "\n"))
end;
