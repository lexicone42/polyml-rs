
(* ############################################################################
   ####  EISENSTEIN LEMMA  --  CLOSE  (fleet F2b)  #############################
   APPENDED to (qr_f1_toolbox.sml ++ qr_f2_appendix.sml).
   The base ends at QR_F2_ALL_OK on ctxtT/ctermT/thyT, with:
     * lprod_perm_of_inj / lar_perm   (PRODUCT permutation, ctxtGG, banked)
     * floor_sum_kr_parity            (HALF the Eisenstein parity, ctxtT, banked)
     * gauss_lemma                    (S = (-1)^mu, ctxtGG, banked)
   F2 floored on the SECOND half : it needs the SUM-permutation invariance of the
   least-absolute-residue map (sum_{k=1..m} lar(q*k) = sum_{k=1..m} k).  The tower
   has lar permutation only as a PRODUCT (lprod_perm_of_inj).  This fleet BUILDS the
   list-SUM infrastructure (lsumf) MIRRORING the product machinery, proves the
   sum-permutation lemma, and CLOSES the Eisenstein lemma.

   Stages (each a distinct GATED _OK marker):
     (LS) lsumf : natlist-sum combinator + lsumf_nil/lsumf_cons recursion axioms +
          lsumf_extract (sum analogue of `extract`).             marker LSUMF_OK
     (LP) lsumf_perm_of_inj : SUM analogue of lprod_perm_of_inj. marker LSUMF_PERM_OK
     (LK) lar_sum_perm : sum_{k=1..m} lar(q*k) = sum_{k=1..m} k. marker LAR_SUM_PERM_OK
     (PH) second parity half : sum r == sum k + mu (mod 2).      marker EIS_PARITY_HALF2_OK
     (EP) eisenstein_parity : mu == sum floor (mod 2).           marker EIS_PARITY_OK
     (EL) eisenstein_lemma  : gauss sign = (-1)^(sum floor).     marker EIS_LEMMA_OK
   ############################################################################ *)
val () = out "EISENSTEIN_CLOSE_BEGIN\n";

(* ============================================================================
   (LS)  lsumf : a natlist-sum combinator.  NEW const on the FINAL theory thyT
   (which already carries lprod/lmem/lremove/llen/lnodup/lmap/upto/lar/rdiv/rmod/
    parity/cnt).  Extend to thyU with ONE new const + TWO conservative recursion
    axioms (lsumf_nil, lsumf_cons).  Build ctxtU/ctermU; re-varify every reused
    base lemma onto ctxtU (schematic 0-hyp theorems survive a context change).
   ============================================================================ *)
val thyUc = Sign.add_consts
  [(Binding.name "lsumf", natlistT --> natT, NoSyn)] thyT;
val lsumfC = Const (Sign.full_name thyUc (Binding.name "lsumf"), natlistT --> natT);
fun lsumf l = lsumfC $ l;
val xUu = Free("x", natT); val tUu = Free("t", natlistT);
val ((_,lsumf_nil_ax),  thyU1) = Thm.add_axiom_global (Binding.name "lsumf_nil",
      jT (oeq (lsumf lnilC) ZeroC)) thyUc;
val ((_,lsumf_cons_ax), thyU)  = Thm.add_axiom_global (Binding.name "lsumf_cons",
      jT (oeq (lsumf (lcons xUu tUu)) (add xUu (lsumf tUu)))) thyU1;

val ctxtU  = Proof_Context.init_global thyU;
val ctermU = Thm.cterm_of ctxtU;
val () = out "LSUMF_CTX_READY\n";

(* transfer + varify : everything reused below, onto thyU. *)
fun toU th = Thm.transfer thyU th;
fun varifyU th = toU (varify th);

(* core logic / arithmetic *)
val oeq_refl_U    = varifyU oeq_refl;
val oeq_subst_U   = varifyU oeq_subst;
val exI_U         = varifyU exI_ax;
val exE_U         = varifyU exE_ax;
val disjE_U       = varifyU disjE_ax;
val disjI1_U      = varifyU disjI1_ax;
val disjI2_U      = varifyU disjI2_ax;
val mp_U          = varifyU mp_ax;
val impI_U        = varifyU impI_ax;
val conjI_U       = varifyU conjI_ax;
val conjunct1_U   = varifyU conjunct1_ax;
val conjunct2_U   = varifyU conjunct2_ax;
val oFalse_elim_U = varifyU oFalse_elim_ax;
val ex_middle_U   = varifyU ex_middle_ax;
val allI_U        = varifyU allI_ax;
val allE_U        = varifyU allE_ax;
val Suc_neq_Zero_U= varifyU Suc_neq_Zero_ax;
val Suc_cong_U    = varifyU Suc_cong;
val Suc_inj_U     = varifyU Suc_inj_ax;
val add_0_right_U = varifyU add_0_right;
val add_Suc_U     = varifyU add_Suc;
val add_comm_U    = varifyU add_comm;
val add_assoc_U   = varifyU add_assoc;
val mult_comm_U   = varifyU mult_comm;
val mult_assoc_U  = varifyU mult_assoc;
val mult_1_left_U = varifyU mult_1_left;
val lt_suc_U      = varifyU lt_suc;
val lt_suc_cases_U= varifyU lt_suc_cases;
val meta_nat_induct_U = varifyU meta_nat_induct_ax2;

(* natlist + lmap + upto + lhd/ltl axioms, varified onto ctxtU *)
val leq_refl_U    = varifyU leq_refl_ax;
val leq_subst_U   = varifyU leq_subst_ax;
val list_induct_U = varifyU list_induct_ax;
val lmem_nil_elim_U = varifyU lmem_nil_elim_ax;
val lmem_cons_fwd_U = varifyU lmem_cons_fwd_ax;
val lmem_cons_bwd_U = varifyU lmem_cons_bwd_ax;
val lremove_nil_U = varifyU lremove_nil_ax;
val lremove_cons_eq_U  = varifyU lremove_cons_eq_ax;
val lremove_cons_neq_U = varifyU lremove_cons_neq_ax;
val llen_nil_U    = varifyU llen_nil_ax;
val llen_cons_U   = varifyU llen_cons_ax;
val lnodup_nil_U  = varifyU lnodup_nil_ax;
val lnodup_cons_fwd_U = varifyU lnodup_cons_fwd_ax;
val lnodup_cons_bwd_U = varifyU lnodup_cons_bwd_ax;
val lmap_nil_U    = varifyU lmap_nil_ax;
val lmap_cons_U   = varifyU lmap_cons_ax;
val upto_zero_U   = varifyU upto_zero_ax;
val upto_suc_U    = varifyU upto_suc_ax;
val lhd_cons_U    = varifyU lhd_cons_ax;
val ltl_cons_U    = varifyU ltl_cons_ax;

(* the new lsumf axioms, varified onto ctxtU *)
val lsumf_nil_U   = varifyU lsumf_nil_ax;
val lsumf_cons_U  = varifyU lsumf_cons_ax;
val () = out "LSUMF_VARIFY_DONE\n";

(* ----------------------------------------------------------------------------
   ground instantiators on ctxtU (suffix _U; mirror the _GG layer 1:1)
   ---------------------------------------------------------------------------- *)
fun oeqRefl_U t = beta_norm (Drule.infer_instantiate ctxtU [(("a",0), ctermU t)] oeq_refl_U);
fun oeq_rw_U (Pabs, xT, yT) hxy hPx =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("P",0), ctermU Pabs), (("a",0), ctermU xT), (("b",0), ctermU yT)] oeq_subst_U)
  in (inst OF [hxy]) OF [hPx] end;
fun leq_rw_U (Pabs, xT, yT) hxy hPx =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("P",0), ctermU Pabs), (("a",0), ctermU xT), (("b",0), ctermU yT)] leq_subst_U)
  in (inst OF [hxy]) OF [hPx] end;
fun leqRefl_U l = beta_norm (Drule.infer_instantiate ctxtU [(("a",0), ctermU l)] leq_refl_U);
fun leq_sym_U hab =
  let val (aT, bT) = case Thm.prop_of hab of
          _ $ (_ $ a $ b) => (a, b)
        | _ => raise Fail "leq_sym_U: shape";
      val Pabs = Abs("z", natlistT, leq (Bound 0) aT);
      val refl = leqRefl_U aT;
  in leq_rw_U (Pabs, aT, bT) hab refl end;

(* oeq_trans / oeq_sym are 0-hyp schematic; OF auto-merges theories *)
val oeq_sym_U   = oeq_sym;
val oeq_trans_U = oeq_trans;

fun exI_U_at (Pabs, w) hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("P",0), ctermU Pabs), (("a",0), ctermU w)] exI_U)
  in Thm.implies_elim inst hbody end;
fun exE_U_at (Pabs, goalC) exThm wName bodyFn =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtU
          [(("P",0), ctermU Pabs), (("Q",0), ctermU goalC)] exE_U);
    val p1 = Thm.implies_elim inst exThm;
    val wF = Free (wName, natT);
    val hyp = Thm.assume (ctermU (jT (Term.betapply (Pabs, wF))));
    val body = bodyFn wF hyp;
    val minor = Thm.forall_intr (ctermU wF) (Thm.implies_intr (ctermU (jT (Term.betapply (Pabs, wF)))) body);
  in Thm.implies_elim p1 minor end;
fun disjE_U_at (At, Bt, Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("A",0), ctermU At), (("B",0), ctermU Bt), (("C",0), ctermU Ct)] disjE_U)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB end;
fun disjI1_U_at (At, Bt) hA =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
        [(("A",0), ctermU At), (("B",0), ctermU Bt)] disjI1_U)) hA;
fun disjI2_U_at (At, Bt) hB =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
        [(("A",0), ctermU At), (("B",0), ctermU Bt)] disjI2_U)) hB;
fun mp_U_at (At, Bt) hImp hA =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
        [(("A",0), ctermU At), (("B",0), ctermU Bt)] mp_U)) hImp) hA;
fun impI_U_at (At, Bt) hMeta =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
        [(("A",0), ctermU At), (("B",0), ctermU Bt)] impI_U)) hMeta;
fun conjI_U_at (At, Bt) hA hB =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
        [(("A",0), ctermU At), (("B",0), ctermU Bt)] conjI_U)) hA) hB;
fun conjunct1_U_at (At, Bt) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
        [(("A",0), ctermU At), (("B",0), ctermU Bt)] conjunct1_U)) h;
fun conjunct2_U_at (At, Bt) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
        [(("A",0), ctermU At), (("B",0), ctermU Bt)] conjunct2_U)) h;
fun oFalse_elim_U_at Rt =
  beta_norm (Drule.infer_instantiate ctxtU [(("R",0), ctermU Rt)] oFalse_elim_U);
fun ex_middle_U_at At =
  beta_norm (Drule.infer_instantiate ctxtU [(("A",0), ctermU At)] ex_middle_U);
fun allI_U_at Pabs hAll =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU [(("P",0), ctermU Pabs)] allI_U)) hAll;
fun allE_U_at Pabs at hForall =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
        [(("P",0), ctermU Pabs), (("a",0), ctermU at)] allE_U)) hForall;

(* Suc / add helpers on ctxtU *)
fun Succong_U h = Suc_cong_U OF [h];
fun add0r_U t = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU t)] add_0_right_U);
fun addSuc_U (mt,nt) = beta_norm (Drule.infer_instantiate ctxtU
        [(("m",0), ctermU mt),(("n",0), ctermU nt)] add_Suc_U);
fun Suc_neq_Zero_U_at nt heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU nt)] Suc_neq_Zero_U)) heq;
fun Suc_inj_U_at (at,bt) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
        [(("a",0), ctermU at),(("b",0), ctermU bt)] Suc_inj_U)) h;
fun addcomm_U (mt,nt) = beta_norm (Drule.infer_instantiate ctxtU
        [(("m",0), ctermU mt),(("n",0), ctermU nt)] add_comm_U);
fun addassoc_U (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtU
        [(("m",0), ctermU mt),(("n",0), ctermU nt),(("k",0), ctermU kt)] add_assoc_U);
fun add_cong_l_U (pT,qT,kT) hpq =
  let val Pabs = Abs("z", natT, oeq (add (Bound 0) kT) (add qT kT))
  in oeq_rw_U (Pabs, qT, pT) (oeq_sym_U OF [hpq]) (oeqRefl_U (add qT kT)) end;
fun add_cong_r_U (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)))
  in oeq_rw_U (Pabs, pT, qT) hpq (oeqRefl_U (add hT pT)) end;

(* lt helpers on ctxtU *)
fun lt_suc_U_at nt = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU nt)] lt_suc_U);
fun lt_suc_cases_U_at (mt,nt) hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
        [(("m",0), ctermU mt),(("n",0), ctermU nt)] lt_suc_cases_U)) hlt;

(* natlist op instantiators on ctxtU *)
fun lsumfNil_U () = lsumf_nil_U;
fun lsumfCons_U (h,t) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU h),(("t",0), ctermU t)] lsumf_cons_U);
fun llenNil_U () = llen_nil_U;
fun llenCons_U (h,t) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU h),(("t",0), ctermU t)] llen_cons_U);
fun lmemNilElim_U x = beta_norm (Drule.infer_instantiate ctxtU [(("x",0), ctermU x)] lmem_nil_elim_U);
fun lmemConsFwd_U (x,y,t) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU x),(("y",0), ctermU y),(("t",0), ctermU t)] lmem_cons_fwd_U);
fun lmemConsBwd_U (x,y,t) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU x),(("y",0), ctermU y),(("t",0), ctermU t)] lmem_cons_bwd_U);
fun lremoveNil_U x = beta_norm (Drule.infer_instantiate ctxtU [(("x",0), ctermU x)] lremove_nil_U);
fun lremoveConsEq_U (x,y,t) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU x),(("y",0), ctermU y),(("t",0), ctermU t)] lremove_cons_eq_U);
fun lremoveConsNeq_U (x,y,t) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU x),(("y",0), ctermU y),(("t",0), ctermU t)] lremove_cons_neq_U);
fun lnodupConsFwd_U (x,t) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU x),(("t",0), ctermU t)] lnodup_cons_fwd_U);
fun lnodupConsBwd_U (x,t) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU x),(("t",0), ctermU t)] lnodup_cons_bwd_U);
val lnodupNil_U = lnodup_nil_U;
fun lmapNil_U f = beta_norm (Drule.infer_instantiate ctxtU [(("f",0), ctermU f)] lmap_nil_U);
fun lmapCons_U (f,h,t) = beta_norm (Drule.infer_instantiate ctxtU
      [(("f",0), ctermU f),(("x",0), ctermU h),(("t",0), ctermU t)] lmap_cons_U);
fun uptoZero_U () = upto_zero_U;
fun uptoSuc_U nt = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU nt)] upto_suc_U);
fun lhdCons_U (h,t) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU h),(("t",0), ctermU t)] lhd_cons_U);
fun ltlCons_U (h,t) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU h),(("t",0), ctermU t)] ltl_cons_U);

(* congruences under list ops via leq_subst / oeq_subst *)
fun lsumf_cong_U (aT,bT) hab =
  let val Pabs = Abs("z", natlistT, oeq (lsumf aT) (lsumf (Bound 0)))
  in leq_rw_U (Pabs, aT, bT) hab (oeqRefl_U (lsumf aT)) end;
fun llen_cong_U (aT,bT) hab =
  let val Pabs = Abs("z", natlistT, oeq (llen aT) (llen (Bound 0)))
  in leq_rw_U (Pabs, aT, bT) hab (oeqRefl_U (llen aT)) end;
fun lmem_transfer_U (yT, aT, bT) hleq hmem =
  let val Pabs = Abs("z", natlistT, lmem yT (Bound 0))
  in leq_rw_U (Pabs, aT, bT) hleq hmem end;
fun lnodup_transfer_U (aT, bT) hleq hnd =
  let val Pabs = Abs("z", natlistT, lnodup (Bound 0))
  in leq_rw_U (Pabs, aT, bT) hleq hnd end;
val () = out "LSUMF_INSTANTIATORS_READY\n";

(* clean gate for U-context lemmas *)
fun cleanU th = (length (Thm.hyps_of th) = 0) andalso (length (Thm.extra_shyps th) = 0);
fun checkU (nm, th, intended) =
  let val ok = cleanU th andalso ((Thm.prop_of th) aconv intended)
  in (if ok then out ("OK " ^ nm ^ "\n")
      else (out ("FAIL " ^ nm ^ "\n");
            out ("  got      = " ^ Syntax.string_of_term ctxtU (Thm.prop_of th) ^ "\n");
            out ("  intended = " ^ Syntax.string_of_term ctxtU intended ^ "\n"));
      ok) end;

(* ----------------------------------------------------------------------------
   The banked structural natlist lemmas (extract is lprod-specific so we rebuild
   a SUM version; the others are op-agnostic so we transfer + varify them up onto
   ctxtU as schematic 0-hyp theorems).
   ---------------------------------------------------------------------------- *)
val mem_remove_fwd_U   = varifyU mem_remove_fwd;
val mem_remove_bwd_U   = varifyU mem_remove_bwd;
val mem_remove_neq_U   = varifyU mem_remove_neq;
val llen_remove_eq_U   = varifyU llen_remove_eq;
val nodup_remove_U     = varifyU nodup_remove;

fun llen_remove_eq_U_at (xt, Lt) hmem =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU xt),(("L",0), ctermU Lt)] llen_remove_eq_U)) hmem;
fun nodup_remove_U_at (xt, Lt) hnd =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU xt),(("L",0), ctermU Lt)] nodup_remove_U)) hnd;
fun mem_remove_bwd_U_at (yt, xt, Lt) hconj =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("y",0), ctermU yt),(("x",0), ctermU xt),(("L",0), ctermU Lt)] mem_remove_bwd_U)) hconj;
val () = out "LSUMF_STRUCT_LEMMAS_READY\n";

(* ----------------------------------------------------------------------------
   list_cases on ctxtU : !!L. Disj (leq L lnil)(leq L (lcons (lhd L)(ltl L)))
   (transfer the banked list_cases_thm up; rebuild the disjE dispatcher on ctxtU)
   ---------------------------------------------------------------------------- *)
fun list_cases_U (LT, goalC) caseNilFn caseConsFn =
  let
    val (LFc, casesL) = list_cases_thm;     (* banked on ctxtGG; the prop is schematic *)
    val casesAtL = beta_norm (Drule.infer_instantiate ctxtU
          [(("L_c",0), ctermU LT)] (varifyU (Thm.forall_intr (Thm.cterm_of ctxtGG LFc) casesL)));
    val nilP  = leq LT lnilC;
    val consP = leq LT (lcons (lhd LT)(ltl LT));
    val cA = let val h = Thm.assume (ctermU (jT nilP))
             in Thm.implies_intr (ctermU (jT nilP)) (caseNilFn h) end;
    val cB = let val h = Thm.assume (ctermU (jT consP))
             in Thm.implies_intr (ctermU (jT consP)) (caseConsFn (lhd LT, ltl LT) h) end;
  in disjE_U_at (nilP, consP, goalC) casesAtL cA cB end;

(* lt_zero_elim on ctxtU *)
fun lt_zero_elim_U mT goalC hlt =
  let
    val Pabs = Abs("p", natT, oeq ZeroC (add (suc mT) (Bound 0)));
    fun body w (hw : thm) =
      let
        val aS    = addSuc_U (mT, w);
        val z_S   = oeq_trans_U OF [hw, aS];
        val S_z   = oeq_sym_U OF [z_S];
        val fls   = Suc_neq_Zero_U_at (add mT w) S_z;
      in Thm.implies_elim (oFalse_elim_U_at goalC) fls end;
  in exE_U_at (Pabs, goalC) hlt "w_lz" body end;
val () = out "LSUMF_LISTCASES_READY\n";

(* ============================================================================
   lsumf_extract : lmem x L ==> oeq (lsumf L) (add x (lsumf (lremove x L)))
   (the SUM analogue of `extract`; list_induct, EXACT mirror with add for mult)
   ============================================================================ *)
val lsumf_extract =
  let
    val xF = Free("x", natT);
    fun concBody zt = oeq (lsumf zt) (add xF (lsumf (lremove xF zt)));
    fun predBody zt = mkImp (lmem xF zt) (concBody zt);
    val Qpred = Abs("z", natlistT, predBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtU
          [(("P",0), ctermU Qpred), (("a",0), ctermU LF)] list_induct_U);
    val base =
      let
        val hmem = Thm.assume (ctermU (jT (lmem xF lnilC)));
        val ff   = Thm.implies_elim (lmemNilElim_U xF) hmem;
        val conc = Thm.implies_elim (oFalse_elim_U_at (concBody lnilC)) ff;
        val dis  = Thm.implies_intr (ctermU (jT (lmem xF lnilC))) conc;
      in impI_U_at (lmem xF lnilC, concBody lnilC) dis end;
    val yF = Free("y", natT); val tF = Free("t", natlistT);
    val ihprop = jT (predBody tF);
    val IH = Thm.assume (ctermU ihprop);
    val stepConcl =
      let
        val hmem = Thm.assume (ctermU (jT (lmem xF (lcons yF tF))));
        val disjmem = Thm.implies_elim (lmemConsFwd_U (xF, yF, tF)) hmem;
        val lpc = lsumfCons_U (yF, tF);            (* lsumf(y::t)=add y (lsumf t) *)
        val caseEq =
          let
            val heq = Thm.assume (ctermU (jT (oeq xF yF)));
            val lrm = Thm.implies_elim (lremoveConsEq_U (xF, yF, tF)) heq;
            val lp_lrm = lsumf_cong_U (lremove xF (lcons yF tF), tF) lrm;
            val rhs_eq = add_cong_r_U (xF, lsumf (lremove xF (lcons yF tF)), lsumf tF) lp_lrm;
            (* lsumf(y::t)=add y (lsumf t) ; y=x -> add y (lsumf t) = add x (lsumf t) ;
               add x (lsumf t) = add x (lsumf (lremove x (y::t))) [rhs_eq sym] *)
            val yx = oeq_sym_U OF [heq];   (* y=x *)
            val my_mx = add_cong_l_U (yF, xF, lsumf tF) yx;   (* add y (lsumf t)=add x (lsumf t) *)
            val rhs_eq_sym = oeq_sym_U OF [rhs_eq];           (* add x (lsumf t)=add x (lsumf(remove)) *)
            val conc = oeq_trans_U OF [oeq_trans_U OF [lpc, my_mx], rhs_eq_sym];
          in Thm.implies_intr (ctermU (jT (oeq xF yF))) conc end;
        val caseNeq =
          let
            val hneq = Thm.assume (ctermU (jT (neg (oeq xF yF))));
            val memT =
              let
                val cA = let val hxy = Thm.assume (ctermU (jT (oeq xF yF)))
                             val ff  = mp_U_at (oeq xF yF, oFalseC) hneq hxy
                             val r   = Thm.implies_elim (oFalse_elim_U_at (lmem xF tF)) ff
                         in Thm.implies_intr (ctermU (jT (oeq xF yF))) r end;
                val cB = let val hm = Thm.assume (ctermU (jT (lmem xF tF)))
                         in Thm.implies_intr (ctermU (jT (lmem xF tF))) hm end;
              in disjE_U_at (oeq xF yF, lmem xF tF, lmem xF tF) disjmem cA cB end;
            val ihconc = mp_U_at (lmem xF tF, concBody tF) IH memT;
                         (* lsumf t = add x (lsumf (lremove x t)) *)
            val lrm = Thm.implies_elim (lremoveConsNeq_U (xF, yF, tF)) hneq;
                      (* leq (lremove x (y::t)) (y :: lremove x t) *)
            val rmtl = lremove xF tF;
            val lp_lrm = lsumf_cong_U (lremove xF (lcons yF tF), lcons yF rmtl) lrm;
                         (* lsumf(lremove x (y::t)) = lsumf(y :: lremove x t) *)
            val lp_cons = lsumfCons_U (yF, rmtl);    (* lsumf(y::lremove x t)=add y (lsumf(lremove x t)) *)
            val lp_lrm2 = oeq_trans_U OF [lp_lrm, lp_cons];
                          (* lsumf(lremove x (y::t)) = add y (lsumf(lremove x t)) *)
            val rhs1 = add_cong_r_U (xF, lsumf (lremove xF (lcons yF tF)), add yF (lsumf rmtl)) lp_lrm2;
                       (* add x (lsumf(lremove x (y::t))) = add x (add y (lsumf(lremove x t))) *)
            val q = lsumf rmtl;
            (* lhs : lsumf(y::t)=add y (lsumf t) ; rewrite lsumf t = add x q via IH *)
            val mut = add_cong_r_U (yF, lsumf tF, add xF q) ihconc;   (* add y (lsumf t)=add y (add x q) *)
            val lhs1 = oeq_trans_U OF [lpc, mut];                     (* lsumf(y::t)=add y (add x q) *)
            (* bridge : add y (add x q) = add x (add y q)
                 add y (add x q) = add (add y x) q [assoc^-1]
                                 = add (add x y) q [comm]
                                 = add x (add y q) [assoc] *)
            val assoc1 = addassoc_U (yF, xF, q);          (* (y+x)+q = y+(x+q) *)
            val assoc1s = oeq_sym_U OF [assoc1];          (* y+(x+q) = (y+x)+q *)
            val comm = addcomm_U (yF, xF);                (* (y+x)=(x+y) *)
            val commc = add_cong_l_U (add yF xF, add xF yF, q) comm;  (* (y+x)+q=(x+y)+q *)
            val assoc2 = addassoc_U (xF, yF, q);          (* (x+y)+q = x+(y+q) *)
            val bridge = oeq_trans_U OF [oeq_trans_U OF [assoc1s, commc], assoc2];
                         (* y+(x+q) = x+(y+q) *)
            val rhs1s = oeq_sym_U OF [rhs1];   (* add x (add y q) = add x (lsumf(lremove x (y::t))) *)
            val conc = oeq_trans_U OF [oeq_trans_U OF [lhs1, bridge], rhs1s];
          in Thm.implies_intr (ctermU (jT (neg (oeq xF yF)))) conc end;
        val em = ex_middle_U_at (oeq xF yF);
        val conc = disjE_U_at (oeq xF yF, neg (oeq xF yF), concBody (lcons yF tF)) em caseEq caseNeq;
        val dis = Thm.implies_intr (ctermU (jT (lmem xF (lcons yF tF)))) conc;
      in impI_U_at (lmem xF (lcons yF tF), concBody (lcons yF tF)) dis end;
    val step1 = Thm.forall_intr (ctermU yF)
                  (Thm.forall_intr (ctermU tF) (Thm.implies_intr (ctermU ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hmemL = Thm.assume (ctermU (jT (lmem xF LF)));
    val concL = mp_U_at (lmem xF LF, concBody LF) r2 hmemL;
    val d1 = Thm.implies_intr (ctermU (jT (lmem xF LF))) concL;
  in varify d1 end;
val xVse = Var (("x",0), natT);  val LVse = Var (("L",0), natlistT);
val i_lsumf_extract = Logic.mk_implies (jT (lmem xVse LVse),
      jT (oeq (lsumf LVse) (add xVse (lsumf (lremove xVse LVse)))));
val r_lsumf_extract = checkU ("lsumf_extract", lsumf_extract, i_lsumf_extract);
fun lsumf_extract_U_at (xt, Lt) hmem =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU xt),(("L",0), ctermU Lt)] (toU lsumf_extract))) hmem;

(* llen_zero_nil on ctxtU : oeq (llen L) 0 ==> leq L lnil  (mirror) *)
val llen_zero_nil_U =
  let
    val LF = Free("L_lz", natlistT);
    val goalC = leq LF lnilC;
    val hz = Thm.assume (ctermU (jT (oeq (llen LF) ZeroC)));
    fun caseNil hnil = hnil
    fun caseCons (a, rest) hcons =
      let
        val llc = llenCons_U (a, rest);
        val llen_L_cons = llen_cong_U (LF, lcons a rest) hcons;
        val llen_L_suc = oeq_trans_U OF [llen_L_cons, llc];
        val suc_eq_z = oeq_trans_U OF [oeq_sym_U OF [llen_L_suc], hz];
        val fls = Suc_neq_Zero_U_at (llen rest) suc_eq_z;
      in Thm.implies_elim (oFalse_elim_U_at goalC) fls end
    val res = list_cases_U (LF, goalC) caseNil caseCons;
  in varify (Thm.implies_intr (ctermU (jT (oeq (llen LF) ZeroC))) res) end;
val () = if length (Thm.hyps_of llen_zero_nil_U) = 0 then out "OK llen_zero_nil_U\n" else out "FAIL llen_zero_nil_U\n";
fun llen_zero_nil_U_at L hz =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("L_lz",0), ctermU L)] (toU llen_zero_nil_U))) hz;

val r_LS = r_lsumf_extract andalso (length (Thm.hyps_of llen_zero_nil_U) = 0);
val () = if r_LS then out "LSUMF_OK\n" else out "LSUMF_FAILED\n";

(* ############################################################################
   ###################  (LP)  lsumf_perm_of_inj  ##############################
   ----------------------------------------------------------------------------
   The SUM analogue of lprod_perm_of_inj.  Two-list injection form:
     lnodup A ==> lnodup B ==> oeq (llen A)(llen B) ==>
     (forall x. lmem x A ==> lmem (g x) B) ==>
     (forall x y. lmem x A ==> lmem y A ==> oeq (g x)(g y) ==> oeq x y) ==>
     oeq (lsumf (lmap g A)) (lsumf B)
   EXACT mirror of the product proof : lprod->lsumf, mult->add, extract->lsumf_extract.
   ############################################################################ *)
val () = out "STAGE_LP_BEGIN\n";

(* lmap leq-transfer : leq A B ==> leq (lmap g A)(lmap g B) *)
fun lmap_cong_U g (aT,bT) hab =
  let val Pabs = Abs("z", natlistT, leq (lmap g aT) (lmap g (Bound 0)))
  in leq_rw_U (Pabs, aT, bT) hab (leqRefl_U (lmap g aT)) end;

(* the function g is a fixed Free of type lfnT throughout *)
val gFu = Free("g_inj", lfnT);
fun g_appU x = gFu $ x;

fun IntoBodyU B L = mkForall (Term.lambda (Free("xi", natT))
      (mkImp (lmem (Free("xi", natT)) L) (lmem (g_appU (Free("xi", natT))) B)));
fun InjBodyU L = mkForall (Term.lambda (Free("xj", natT))
      (mkForall (Term.lambda (Free("yj", natT))
        (mkImp (lmem (Free("xj", natT)) L)
          (mkImp (lmem (Free("yj", natT)) L)
            (mkImp (oeq (g_appU (Free("xj", natT))) (g_appU (Free("yj", natT))))
                   (oeq (Free("xj", natT)) (Free("yj", natT)))))))));

fun useIntoU B L hInto z hmem =
  let val xf = Free("xi", natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (lmem (g_appU xf) B))
      val inst = allE_U_at Pabs z hInto
  in mp_U_at (lmem z L, lmem (g_appU z) B) inst hmem end;
fun useInjU L hInj z w hmz hmw heq =
  let val xf = Free("xj", natT); val yf = Free("yj", natT)
      val Pabs = Term.lambda xf (mkForall (Term.lambda yf
            (mkImp (lmem xf L) (mkImp (lmem yf L)
              (mkImp (oeq (g_appU xf)(g_appU yf)) (oeq xf yf))))))
      val instX = allE_U_at Pabs z hInj
      val Qabs = Term.lambda yf (mkImp (lmem z L) (mkImp (lmem yf L)
                    (mkImp (oeq (g_appU z)(g_appU yf)) (oeq z yf))))
      val instY = allE_U_at Qabs w instX
      val s1 = mp_U_at (lmem z L, mkImp (lmem w L)(mkImp (oeq (g_appU z)(g_appU w))(oeq z w))) instY hmz
      val s2 = mp_U_at (lmem w L, mkImp (oeq (g_appU z)(g_appU w))(oeq z w)) s1 hmw
      val s3 = mp_U_at (oeq (g_appU z)(g_appU w), oeq z w) s2 heq
  in s3 end;
val () = out "STAGE_LP_HELPERS_READY\n";

(* ----------------------------------------------------------------------------
   THE PROOF (meta-B strong induction), mirror of lprod_perm_meta.
   ---------------------------------------------------------------------------- *)
val lsumf_perm_meta =
  let
    val Lm = Free("L_pm", natlistT);
    val Bm = Free("B_pm", natlistT);
    fun chain L B =
      Logic.mk_implies (jT (lnodup L),
        Logic.mk_implies (jT (lnodup B),
          Logic.mk_implies (jT (oeq (llen L)(llen B)),
            Logic.mk_implies (jT (IntoBodyU B L),
              Logic.mk_implies (jT (InjBodyU L),
                jT (oeq (lsumf (lmap gFu L)) (lsumf B)))))));
    fun auxBody nt =
      Logic.all Lm (Logic.mk_implies (jT (lt (llen Lm) nt),
                      Logic.all Bm (chain Lm Bm)));
    val nMeta = Free("n_pm", natT);
    val PhiMetaAbs = Term.lambda nMeta (auxBody nMeta);

    fun dischChain L B eqThm =
      let
        val d5 = Thm.implies_intr (ctermU (jT (InjBodyU L))) eqThm;
        val d4 = Thm.implies_intr (ctermU (jT (IntoBodyU B L))) d5;
        val d3 = Thm.implies_intr (ctermU (jT (oeq (llen L)(llen B)))) d4;
        val d2 = Thm.implies_intr (ctermU (jT (lnodup B))) d3;
        val d1 = Thm.implies_intr (ctermU (jT (lnodup L))) d2;
      in d1 end;

    (* BASE : !!L. jT(lt (llen L) 0) ==> !!B. chain L B *)
    val base =
      let
        val LB = Free("L_pb", natlistT);
        val hlt = Thm.assume (ctermU (jT (lt (llen LB) ZeroC)));
        val BB = Free("B_pb", natlistT);
        val hND_A = Thm.assume (ctermU (jT (lnodup LB)));
        val hND_B = Thm.assume (ctermU (jT (lnodup BB)));
        val hLen  = Thm.assume (ctermU (jT (oeq (llen LB)(llen BB))));
        val hInto = Thm.assume (ctermU (jT (IntoBodyU BB LB)));
        val hInj  = Thm.assume (ctermU (jT (InjBodyU LB)));
        val concl0 = lt_zero_elim_U (llen LB) (oeq (lsumf (lmap gFu LB)) (lsumf BB)) hlt;
        val chainLB = dischChain LB BB concl0;
        val allB = Thm.forall_intr (ctermU BB) chainLB;
        val disch = Thm.implies_intr (ctermU (jT (lt (llen LB) ZeroC))) allB;
      in Thm.forall_intr (ctermU LB) disch end;

    (* STEP : !!x. (aux x) ==> (aux (Suc x)) *)
    val step =
      let
        val xS = Free("x_pm", natT);
        val auxX = auxBody xS;
        val IHmeta = Thm.assume (ctermU auxX);
        fun applyAUXx L2 hlt = Thm.implies_elim (Thm.forall_elim (ctermU L2) IHmeta) hlt;
        val LS = Free("L_ps", natlistT);
        val hltS = Thm.assume (ctermU (jT (lt (llen LS) (suc xS))));
        val dThm = lt_suc_cases_U_at (llen LS, xS) hltS;
        val BS = Free("B_ps", natlistT);
        val hND_A = Thm.assume (ctermU (jT (lnodup LS)));
        val hND_B = Thm.assume (ctermU (jT (lnodup BS)));
        val hLen  = Thm.assume (ctermU (jT (oeq (llen LS)(llen BS))));
        val hInto = Thm.assume (ctermU (jT (IntoBodyU BS LS)));
        val hInj  = Thm.assume (ctermU (jT (InjBodyU LS)));
        val goalC = oeq (lsumf (lmap gFu LS)) (lsumf BS);

        val caseLt =
          let
            val hA = Thm.assume (ctermU (jT (lt (llen LS) xS)))
            val chainLS = applyAUXx LS hA
            val chainLS_BS = Thm.forall_elim (ctermU BS) chainLS
            val e1 = Thm.implies_elim chainLS_BS hND_A
            val e2 = Thm.implies_elim e1 hND_B
            val e3 = Thm.implies_elim e2 hLen
            val e4 = Thm.implies_elim e3 hInto
            val eqv = Thm.implies_elim e4 hInj
          in Thm.implies_intr (ctermU (jT (lt (llen LS) xS))) eqv end;

        val caseEq =
          let
            val hB = Thm.assume (ctermU (jT (oeq (llen LS) xS)))
            fun applyIH L2 (h_lt:thm) =
              let val zpr = Free("z_prP", natT)
                  val Pr = Term.lambda zpr (lt (llen L2) zpr)
                  val h_lt_x = oeq_rw_U (Pr, llen LS, xS) hB h_lt
              in applyAUXx L2 h_lt_x end

            fun caseNil hnil =
              let
                val lmAS = lmap_cong_U gFu (LS, lnilC) hnil;
                val lmnil = lmapNil_U gFu;
                val lp_lmAS = lsumf_cong_U (lmap gFu LS, lmap gFu lnilC) lmAS;
                val lp_lmnil = lsumf_cong_U (lmap gFu lnilC, lnilC) lmnil;
                val lpn = lsumfNil_U ();
                val lhs1 = oeq_trans_U OF [oeq_trans_U OF [lp_lmAS, lp_lmnil], lpn];
                val llAS = llen_cong_U (LS, lnilC) hnil;
                val lln = llenNil_U ();
                val llAS0 = oeq_trans_U OF [llAS, lln];
                val llB0 = oeq_trans_U OF [oeq_sym_U OF [hLen], llAS0];
                val Bnil = llen_zero_nil_U_at BS llB0;
                val lpB = lsumf_cong_U (BS, lnilC) Bnil;
                val lpB1 = oeq_trans_U OF [lpB, lpn];
                val lpB1s = oeq_sym_U OF [lpB1];
              in oeq_trans_U OF [lhs1, lpB1s] end;

            fun caseCons (a, rest) hcons =
              let
                val consA = lcons a rest;
                val hcons_s = leq_sym_U hcons;
                val ga = g_appU a;
                val a_in_cons = Thm.implies_elim (lmemConsBwd_U (a, a, rest))
                                  (disjI1_U_at (oeq a a, lmem a rest) (oeqRefl_U a));
                val memA = lmem_transfer_U (a, consA, LS) hcons_s a_in_cons;
                val ga_in_B = useIntoU BS LS hInto a memA;
                val hND_consA = lnodup_transfer_U (LS, consA) hcons hND_A;
                val cjND = Thm.implies_elim (lnodupConsFwd_U (a, rest)) hND_consA;
                val a_notin_rest = conjunct1_U_at (neg (lmem a rest), lnodup rest) cjND;
                val ndRest = conjunct2_U_at (neg (lmem a rest), lnodup rest) cjND;
                val Bp = lremove ga BS;

                val lmAS_cons = lmap_cong_U gFu (LS, consA) hcons;
                val lm_cons = lmapCons_U (gFu, a, rest);
                val lp_lmAS = lsumf_cong_U (lmap gFu LS, lmap gFu consA) lmAS_cons;
                val lp_lmcons = lsumf_cong_U (lmap gFu consA, lcons ga (lmap gFu rest)) lm_cons;
                val lp_cons_eq = lsumfCons_U (ga, lmap gFu rest);
                val lhsChain = oeq_trans_U OF [oeq_trans_U OF [lp_lmAS, lp_lmcons], lp_cons_eq];
                            (* lsumf(lmap g LS) = add ga (lsumf(lmap g rest)) *)

                val lp_B_extract = lsumf_extract_U_at (ga, BS) ga_in_B;
                            (* lsumf B = add ga (lsumf (lremove ga B)) *)

                val llc = llenCons_U (a, rest);
                val llAS_cons = llen_cong_U (LS, consA) hcons;
                val llAS_suc = oeq_trans_U OF [llAS_cons, llc];
                val lt_self = lt_suc_U_at (llen rest);
                val zlt = Free("z_ltP", natT);
                val Plt = Term.lambda zlt (lt (llen rest) zlt);
                val llAS_suc_s = oeq_sym_U OF [llAS_suc];
                val ltRest_AS = oeq_rw_U (Plt, suc (llen rest), llen LS) llAS_suc_s lt_self;
                val ihMeta = applyIH rest ltRest_AS;

                val ndBp = nodup_remove_U_at (ga, BS) hND_B;
                val llBv_eq = llen_remove_eq_U_at (ga, BS) ga_in_B;
                val s_rest_s_Bp = oeq_trans_U OF [oeq_trans_U OF [oeq_sym_U OF [llAS_suc], hLen], llBv_eq];
                val llRest_Bp = Suc_inj_U_at (llen rest, llen Bp) s_rest_s_Bp;

                val intoBpRest =
                  let
                    val yf = Free("y_into", natT);
                    val Pabs = Term.lambda yf (mkImp (lmem yf rest) (lmem (g_appU yf) Bp));
                    val hyR = Thm.assume (ctermU (jT (lmem yf rest)));
                    val y_in_cons = Thm.implies_elim (lmemConsBwd_U (yf, a, rest))
                                      (disjI2_U_at (oeq yf a, lmem yf rest) hyR);
                    val y_in_AS = lmem_transfer_U (yf, consA, LS) hcons_s y_in_cons;
                    val gy_in_B = useIntoU BS LS hInto yf y_in_AS;
                    val gy_neq_ga =
                      let
                        val heq = Thm.assume (ctermU (jT (oeq (g_appU yf) ga)));
                        val yEqa = useInjU LS hInj yf a y_in_AS memA heq;
                        val Pr = Abs("z", natT, lmem (Bound 0) rest);
                        val a_in_rest = oeq_rw_U (Pr, yf, a) yEqa hyR;
                        val ff = mp_U_at (lmem a rest, oFalseC) a_notin_rest a_in_rest;
                      in impI_U_at (oeq (g_appU yf) ga, oFalseC)
                           (Thm.implies_intr (ctermU (jT (oeq (g_appU yf) ga))) ff) end;
                    val conjBwd = conjI_U_at (lmem (g_appU yf) BS, neg (oeq (g_appU yf) ga)) gy_in_B gy_neq_ga;
                    val gy_in_Bp = mem_remove_bwd_U_at (g_appU yf, ga, BS) conjBwd;
                    val imp = impI_U_at (lmem yf rest, lmem (g_appU yf) Bp)
                                (Thm.implies_intr (ctermU (jT (lmem yf rest))) gy_in_Bp);
                  in allI_U_at Pabs (Thm.forall_intr (ctermU yf) imp) end;

                val injRest =
                  let
                    val xf = Free("x_inj", natT); val yf = Free("y_inj", natT);
                    val Pabs = Term.lambda xf (mkForall (Term.lambda yf
                                  (mkImp (lmem xf rest) (mkImp (lmem yf rest)
                                    (mkImp (oeq (g_appU xf)(g_appU yf)) (oeq xf yf))))));
                    val hxR = Thm.assume (ctermU (jT (lmem xf rest)));
                    val hyR = Thm.assume (ctermU (jT (lmem yf rest)));
                    val heq = Thm.assume (ctermU (jT (oeq (g_appU xf)(g_appU yf))));
                    val x_in_cons = Thm.implies_elim (lmemConsBwd_U (xf, a, rest))
                                      (disjI2_U_at (oeq xf a, lmem xf rest) hxR);
                    val x_in_AS = lmem_transfer_U (xf, consA, LS) hcons_s x_in_cons;
                    val y_in_cons = Thm.implies_elim (lmemConsBwd_U (yf, a, rest))
                                      (disjI2_U_at (oeq yf a, lmem yf rest) hyR);
                    val y_in_AS = lmem_transfer_U (yf, consA, LS) hcons_s y_in_cons;
                    val xy = useInjU LS hInj xf yf x_in_AS y_in_AS heq;
                    val impE = impI_U_at (oeq (g_appU xf)(g_appU yf), oeq xf yf)
                                 (Thm.implies_intr (ctermU (jT (oeq (g_appU xf)(g_appU yf)))) xy);
                    val impY = impI_U_at (lmem yf rest, mkImp (oeq (g_appU xf)(g_appU yf)) (oeq xf yf))
                                 (Thm.implies_intr (ctermU (jT (lmem yf rest))) impE);
                    val impX = impI_U_at (lmem xf rest, mkImp (lmem yf rest)(mkImp (oeq (g_appU xf)(g_appU yf)) (oeq xf yf)))
                                 (Thm.implies_intr (ctermU (jT (lmem xf rest))) impY);
                    val Qabs = Term.lambda yf (mkImp (lmem xf rest) (mkImp (lmem yf rest)
                                  (mkImp (oeq (g_appU xf)(g_appU yf)) (oeq xf yf))));
                    val innerAll = allI_U_at Qabs (Thm.forall_intr (ctermU yf) impX);
                  in allI_U_at Pabs (Thm.forall_intr (ctermU xf) innerAll) end;

                val chainRestBp = Thm.forall_elim (ctermU Bp) ihMeta;
                val e1 = Thm.implies_elim chainRestBp ndRest;
                val e2 = Thm.implies_elim e1 ndBp;
                val e3 = Thm.implies_elim e2 llRest_Bp;
                val e4 = Thm.implies_elim e3 intoBpRest;
                val ihEq = Thm.implies_elim e4 injRest;
                            (* lsumf(lmap g rest) = lsumf Bp *)
                val ga_add = add_cong_r_U (ga, lsumf (lmap gFu rest), lsumf Bp) ihEq;
                            (* add ga (lsumf(lmap g rest)) = add ga (lsumf Bp) *)
                val lp_B_extract_s = oeq_sym_U OF [lp_B_extract];
                            (* add ga (lsumf Bp) = lsumf B *)
                val rhsChain = oeq_trans_U OF [ga_add, lp_B_extract_s];
                            (* add ga (lsumf(lmap g rest)) = lsumf B *)
              in oeq_trans_U OF [lhsChain, rhsChain] end;

            val eqv = list_cases_U (LS, goalC) caseNil caseCons;
          in Thm.implies_intr (ctermU (jT (oeq (llen LS) xS))) eqv end;

        val eqGoal = disjE_U_at (lt (llen LS) xS, oeq (llen LS) xS, goalC) dThm caseLt caseEq;
        val chainLS = dischChain LS BS eqGoal;
        val allB = Thm.forall_intr (ctermU BS) chainLS;
        val dischLt = Thm.implies_intr (ctermU (jT (lt (llen LS) (suc xS)))) allB;
        val auxSucx = Thm.forall_intr (ctermU LS) dischLt;
      in Thm.forall_intr (ctermU xS) (Thm.implies_intr (ctermU auxX) auxSucx) end;

    val AF = Free("A_fin", natlistT);
    val kFin = suc (llen AF);
    val indK = beta_norm (Drule.infer_instantiate ctxtU
                 [(("Phi",0), ctermU PhiMetaAbs),(("k",0), ctermU kFin)] meta_nat_induct_U);
    val auxK = Thm.implies_elim (Thm.implies_elim indK base) step;
    val auxKA = Thm.forall_elim (ctermU AF) auxK;
    val selfLt = lt_suc_U_at (llen AF);
    val chainAFall = Thm.implies_elim auxKA selfLt;
  in (AF, chainAFall) end;
val () = out "STAGE_LP_PHI_BUILT\n";

val lsumf_perm_of_inj =
  let
    val (AF, chainAFall) = lsumf_perm_meta;
    val Bf = Free("B_ext", natlistT);
    val chainAF = Thm.forall_elim (ctermU Bf) chainAFall;
  in varify chainAF end;

(* ---- validate lsumf_perm_of_inj : 0-hyp + aconv ---- *)
val gVpu = Var(("g_inj",0), lfnT);
fun IntoBodyVU B A = mkForall (Term.lambda (Free("xi", natT))
      (mkImp (lmem (Free("xi", natT)) A) (lmem (gVpu $ (Free("xi", natT))) B)));
fun InjBodyVU A = mkForall (Term.lambda (Free("xj", natT))
      (mkForall (Term.lambda (Free("yj", natT))
        (mkImp (lmem (Free("xj", natT)) A)
          (mkImp (lmem (Free("yj", natT)) A)
            (mkImp (oeq (gVpu $ (Free("xj", natT))) (gVpu $ (Free("yj", natT))))
                   (oeq (Free("xj", natT)) (Free("yj", natT)))))))));
val AVpu = Var(("A_fin",0), natlistT);  val BVpu = Var(("B_ext",0), natlistT);
val i_lsumf_perm =
  Logic.mk_implies (jT (lnodup AVpu),
    Logic.mk_implies (jT (lnodup BVpu),
      Logic.mk_implies (jT (oeq (llen AVpu)(llen BVpu)),
        Logic.mk_implies (jT (IntoBodyVU BVpu AVpu),
          Logic.mk_implies (jT (InjBodyVU AVpu),
            jT (oeq (lsumf (lmapC $ gVpu $ AVpu)) (lsumf BVpu)))))));
val r_lsumf_perm = (length (Thm.hyps_of lsumf_perm_of_inj) = 0)
                   andalso ((Thm.prop_of lsumf_perm_of_inj) aconv i_lsumf_perm);
val () = if r_lsumf_perm then out "OK lsumf_perm_of_inj\n" else out "FAIL lsumf_perm_of_inj\n";
val probe_sperm_needs_inj =
  let val bogus = Logic.mk_implies (jT (lnodup AVpu),
        Logic.mk_implies (jT (lnodup BVpu),
          Logic.mk_implies (jT (oeq (llen AVpu)(llen BVpu)),
            Logic.mk_implies (jT (IntoBodyVU BVpu AVpu),
              jT (oeq (lsumf (lmapC $ gVpu $ AVpu)) (lsumf BVpu))))))
  in not ((Thm.prop_of lsumf_perm_of_inj) aconv bogus) end;
val () = if probe_sperm_needs_inj then out "PROBE_OK lsumf_perm_of_inj keeps injectivity\n"
         else out "PROBE_FAIL lsumf_perm_of_inj\n";
val sperm_clean = length (Thm.extra_shyps lsumf_perm_of_inj) = 0;
val () = if r_lsumf_perm andalso probe_sperm_needs_inj andalso sperm_clean
         then out "LSUMF_PERM_OK\n" else out "LSUMF_PERM_FAILED\n";
val () = out "STAGE_LP_END\n";

(* ############################################################################
   ###########################  (LK)  lar_sum_perm  ##########################
   ----------------------------------------------------------------------------
   sum_{k=1..m} lar(a*k) = sum_{k=1..m} k :
     prime2 p ==> ~(dvd p a) ==> oeq (sub p 1)(add m m) ==>
       oeq (lsumf (lmap (%k. lar a p k) (uptoF m))) (lsumf (uptoF m))
   Apply lsumf_perm_of_inj to g = (%k. lar a p k), A = B = uptoF m, discharging
   EXACTLY the lar_perm Into/Inj/nodup/llen hypotheses (reuse the banked ctxtGG
   helpers : lnodup_upto, lmem_upto_*, not_dvd_in_range, lar_in_range_at,
   lar_inj_dichotomy, abs_inj_at).  The Into/Inj/nodup/llen facts are built on
   ctxtGG (they live in thyGG terms) then transferred up to ctxtU to feed the
   U-instance of lsumf_perm_of_inj.
   ############################################################################ *)
val () = out "STAGE_LK_BEGIN\n";

val lar_sum_perm =
  let
    val pF = Free("p", natT); val aF = Free("a", natT); val mF = Free("m", natT);
    val hPrime = Thm.assume (ctermGG (jT (prime2 pF)));
    val hNa    = Thm.assume (ctermGG (jT (neg (dvd pF aF))));
    val hOdd   = Thm.assume (ctermGG (jT (oeq (sub pF oneC) (add mF mF))));
    val U = uptoF mF;
    val gLam = Abs("k_g", natT, lar aF pF (Bound 0));
    fun gOf k = lar aF pF k;

    (* (1) lnodup U  (ctxtGG) *)
    val hND_GG = beta_norm (Drule.infer_instantiate ctxtGG [(("k_nd",0), ctermGG mF)] (toGG lnodup_upto));
    (* (2) llen U = llen U : refl (ctxtGG) *)
    val hLen_GG = oeqRefl_GG (llen U);
    (* (3) Into U U  (ctxtGG, mirror lar_perm intoThm) *)
    val intoThm_GG =
      let
        val xi = Free("xi", natT);
        val Pabs = Term.lambda xi (mkImp (lmem xi U) (lmem (gOf xi) U));
        val hmem = Thm.assume (ctermGG (jT (lmem xi U)));
        val cj = lmem_upto_fwd_at (xi, mF) hmem;
        val h1 = conjunct1_GG_at (lt ZeroC xi, le xi mF) cj;
        val h2 = conjunct2_GG_at (lt ZeroC xi, le xi mF) cj;
        val nNk = not_dvd_in_range pF mF xi hPrime hOdd h1 h2;
        val rng = lar_in_range_at (pF, aF, xi, mF) hPrime hNa nNk hOdd;
        val r1 = conjunct1_GG_at (le (suc ZeroC) (gOf xi), le (gOf xi) mF) rng;
        val r2 = conjunct2_GG_at (le (suc ZeroC) (gOf xi), le (gOf xi) mF) rng;
        val conj = conjI_GG_at (lt ZeroC (gOf xi), le (gOf xi) mF) r1 r2;
        val memU = lmem_upto_bwd_at (gOf xi, mF) conj;
        val imp = impI_GG_at (lmem xi U, lmem (gOf xi) U)
                    (Thm.implies_intr (ctermGG (jT (lmem xi U))) memU);
      in allI_GG_at Pabs (Thm.forall_intr (ctermGG xi) imp) end;
    (* (4) Inj U  (ctxtGG, mirror lar_perm injThm) *)
    val injThm_GG =
      let
        val xj = Free("xj", natT); val yj = Free("yj", natT);
        val Pabs = Term.lambda xj (mkForall (Term.lambda yj
                      (mkImp (lmem xj U) (mkImp (lmem yj U)
                        (mkImp (oeq (gOf xj)(gOf yj)) (oeq xj yj))))));
        val hmx = Thm.assume (ctermGG (jT (lmem xj U)));
        val hmy = Thm.assume (ctermGG (jT (lmem yj U)));
        val hEq = Thm.assume (ctermGG (jT (oeq (gOf xj)(gOf yj))));
        val cjx = lmem_upto_fwd_at (xj, mF) hmx;
        val x1 = conjunct1_GG_at (lt ZeroC xj, le xj mF) cjx;
        val x2 = conjunct2_GG_at (lt ZeroC xj, le xj mF) cjx;
        val nNkx = not_dvd_in_range pF mF xj hPrime hOdd x1 x2;
        val cjy = lmem_upto_fwd_at (yj, mF) hmy;
        val y1 = conjunct1_GG_at (lt ZeroC yj, le yj mF) cjy;
        val y2 = conjunct2_GG_at (lt ZeroC yj, le yj mF) cjy;
        val nNky = not_dvd_in_range pF mF yj hPrime hOdd y1 y2;
        val dicho = lar_inj_dichotomy pF aF xj yj hPrime hNa nNkx nNky hEq;
        val xjEq = abs_inj_at (pF, aF, xj, yj, mF) hPrime hNa hOdd x1 x2 y1 y2 dicho;
        val impE = impI_GG_at (oeq (gOf xj)(gOf yj), oeq xj yj)
                     (Thm.implies_intr (ctermGG (jT (oeq (gOf xj)(gOf yj)))) xjEq);
        val impY = impI_GG_at (lmem yj U, mkImp (oeq (gOf xj)(gOf yj)) (oeq xj yj))
                     (Thm.implies_intr (ctermGG (jT (lmem yj U))) impE);
        val impX = impI_GG_at (lmem xj U, mkImp (lmem yj U)(mkImp (oeq (gOf xj)(gOf yj)) (oeq xj yj)))
                     (Thm.implies_intr (ctermGG (jT (lmem xj U))) impY);
        val Qabs = Term.lambda yj (mkImp (lmem xj U) (mkImp (lmem yj U)
                      (mkImp (oeq (gOf xj)(gOf yj)) (oeq xj yj))));
        val innerAll = allI_GG_at Qabs (Thm.forall_intr (ctermGG yj) impX);
      in allI_GG_at Pabs (Thm.forall_intr (ctermGG xj) innerAll) end;

    (* transfer the four discharge facts up to ctxtU *)
    val hND   = toU hND_GG;
    val hLen  = toU hLen_GG;
    val intoThm = toU intoThm_GG;
    val injThm  = toU injThm_GG;

    (* instantiate lsumf_perm_of_inj (ctxtU) at g := gLam, A := U, B := U *)
    val permI = beta_norm (Drule.infer_instantiate ctxtU
          [(("g_inj",0), ctermU gLam), (("A_fin",0), ctermU U), (("B_ext",0), ctermU U)]
          (toU lsumf_perm_of_inj));
    val e1 = Thm.implies_elim permI hND;
    val e2 = Thm.implies_elim e1 hND;
    val e3 = Thm.implies_elim e2 hLen;
    val e4 = Thm.implies_elim e3 intoThm;
    val eqv = Thm.implies_elim e4 injThm;
        (* jT (oeq (lsumf (lmap gLam U)) (lsumf U)) *)
    val d3 = Thm.implies_intr (ctermU (jT (oeq (sub pF oneC) (add mF mF)))) eqv;
    val d2 = Thm.implies_intr (ctermU (jT (neg (dvd pF aF)))) d3;
    val d1 = Thm.implies_intr (ctermU (jT (prime2 pF))) d2;
  in varify d1 end;

(* ---- validate lar_sum_perm : 0-hyp + aconv ---- *)
val pVls = Var(("p",0), natT); val aVls = Var(("a",0), natT); val mVls = Var(("m",0), natT);
val gPartVs = larC $ aVls $ pVls;
val gLamVs  = Abs("k_g", natT, lar aVls pVls (Bound 0));
fun mk_i_lar_sum_perm gform =
  Logic.mk_implies (jT (prime2 pVls),
    Logic.mk_implies (jT (neg (dvd pVls aVls)),
      Logic.mk_implies (jT (oeq (sub pVls oneC) (add mVls mVls)),
        jT (oeq (lsumf (lmapC $ gform $ (uptoF mVls))) (lsumf (uptoF mVls))))));
val i_lar_sum_perm     = mk_i_lar_sum_perm gPartVs;
val i_lar_sum_perm_lam = mk_i_lar_sum_perm gLamVs;
val r_lar_sum_perm = (length (Thm.hyps_of lar_sum_perm) = 0)
                 andalso (((Thm.prop_of lar_sum_perm) aconv i_lar_sum_perm)
                          orelse ((Thm.prop_of lar_sum_perm) aconv i_lar_sum_perm_lam))
                 andalso (length (Thm.extra_shyps lar_sum_perm) = 0);
val () = if r_lar_sum_perm then out "OK lar_sum_perm\n" else out "FAIL lar_sum_perm\n";
val probe_lar_sum_perm_needs_ndvd =
  let val bogus = Logic.mk_implies (jT (prime2 pVls),
        Logic.mk_implies (jT (oeq (sub pVls oneC) (add mVls mVls)),
          jT (oeq (lsumf (lmapC $ gLamVs $ (uptoF mVls))) (lsumf (uptoF mVls)))))
  in not ((Thm.prop_of lar_sum_perm) aconv bogus) end;
val () = if probe_lar_sum_perm_needs_ndvd then out "PROBE_OK lar_sum_perm keeps ~(dvd p a)\n"
         else out "PROBE_FAIL lar_sum_perm\n";
val () = if r_lar_sum_perm andalso probe_lar_sum_perm_needs_ndvd
         then out "LAR_SUM_PERM_OK\n" else out "LAR_SUM_PERM_FAILED\n";
val () = out "STAGE_LK_END\n";


(* ############################################################################
   ##########  (PH)  SECOND PARITY HALF :  sum r == sum k + mu (mod 2)  ########
   ----------------------------------------------------------------------------
   The per-k absolute-least-residue decomposition gives, for each k :
     2r <= p (NO flip) : lar = r       ; r + lar = 2r       ; parity = 0
     p < 2r  (FLIP)    : lar = p - r    ; r + lar = p        ; parity = parity p = 1
   So  parity(add (rmod k)(lar k)) = flipBit k  (0 / 1), and the flip COUNT over
   1..n is exactly mu = cnt flipPred n.  Combined-induction lemma rmod_lar_cnt :
     0<p ==> parity p = 1 ==>
       parity(add (sumf rmodAbs n)(sumf larAbs n)) = parity(cnt flipPred n).
   Then with lar_sum_perm (sum lar = sum k) :
     parity(sumf rmodAbs m) = parity(add (sumf idAbs m) (cnt flipPred m)).   (PH)
   mu := cnt flipPred m  is the genuine number of absolute-least-residue flips.
   ############################################################################ *)
val () = out "STAGE_PH_BEGIN\n";

(* ---- U-versions of the F2 parity / sum / cnt / lar / order infra ---- *)
val parity_0_U      = varifyU parity_0_ax;
val parity_Suc_U    = varifyU parity_Suc_ax;
val parity_add_U    = varifyU parity_add;
val parity_double_U = varifyU parity_double;
val parity_idem_U   = varifyU parity_idem;
val parity_bounded_U= varifyU parity_bounded;
val parity1_eq_U    = varifyU parity1_eq;
val sumf_0_U        = varifyU sumf_0_ax;
val sumf_Suc_U      = varifyU sumf_Suc_ax;
val sum_add_U       = varifyU sum_add;
val cnt_0_U         = varifyU cnt_0_ax;
val cnt_Suc_t_U     = varifyU cnt_Suc_t_ax;
val cnt_Suc_f_U     = varifyU cnt_Suc_f_ax;
val lar_lo_U        = varifyU lar_lo_ax;
val lar_hi_U        = varifyU lar_hi_ax;
val rmod_lt_U       = varifyU rmod_lt_ax;
val div_mod_eq_U    = varifyU div_mod_eq_ax;
val nat_induct_U2   = varifyU nat_induct;
val le_refl_U2      = varifyU le_refl;
val le_total_U      = varifyU le_total;
val le_neq_lt_U     = varifyU le_neq_lt;
val le_add_U        = varifyU le_add;
val le_trans_U      = varifyU le_trans;
val lt_irrefl_U     = varifyU lt_irrefl;
val sub_add_l_U     = varifyU sub_add_l;
val mult_0_right_U  = varifyU mult_0_right;
val add_eq_zero_left_U = varifyU add_eq_zero_left;

fun parity_double_U_at t = beta_norm (Drule.infer_instantiate ctxtU [(("z",0),ctermU t)] parity_double_U);
fun parity_bounded_U_at t = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU t)] parity_bounded_U);
fun parity_idem_U_at t = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU t)] parity_idem_U);
fun parityAdd_U_at (at,bt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("a",0), ctermU at),(("b",0), ctermU bt)] parity_add_U);
fun sumf0_U fT = beta_norm (Drule.infer_instantiate ctxtU [(("f",0), ctermU fT)] sumf_0_U);
fun sumfSuc_U (fT,nt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("f",0), ctermU fT),(("n",0), ctermU nt)] sumf_Suc_U);
fun sum_add_U_at (fT, gT, nt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("f",0), ctermU fT),(("g",0), ctermU gT),(("n",0), ctermU nt)] sum_add_U);
fun cnt0_U Pt = beta_norm (Drule.infer_instantiate ctxtU [(("P",0), ctermU Pt)] cnt_0_U);
fun cntSucT_U (Pt, nt) hP = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("P",0), ctermU Pt),(("n",0), ctermU nt)] cnt_Suc_t_U)) hP;
fun cntSucF_U (Pt, nt) hNP = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("P",0), ctermU Pt),(("n",0), ctermU nt)] cnt_Suc_f_U)) hNP;
fun rmod_lt_U_at (at, pt) hpos =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("a",0), ctermU at),(("p",0), ctermU pt)] rmod_lt_U)) hpos;
fun div_mod_eq_U_at (at, pt) hpos =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("a",0), ctermU at),(("p",0), ctermU pt)] div_mod_eq_U)) hpos;
fun lar_lo_U_at (at, pt, kt) hle =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("a",0), ctermU at),(("p",0), ctermU pt),(("k",0), ctermU kt)] lar_lo_U)) hle;
fun lar_hi_U_at (at, pt, kt) hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("a",0), ctermU at),(("p",0), ctermU pt),(("k",0), ctermU kt)] lar_hi_U)) hlt;
fun mult0r_U t = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU t)] mult_0_right_U);
fun add_eq_zero_left_U_at (at, bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("a",0), ctermU at),(("b",0), ctermU bt)] add_eq_zero_left_U)) h;
fun le_add_U_at (mt,pt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("p",0), ctermU pt)] le_add_U);

(* nat induction runner on ctxtU *)
fun nat_induct_U_run Pabs kF base step =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("P",0), ctermU Pabs), (("k",0), ctermU kF)] nat_induct_U2)
  in beta_norm (Thm.implies_elim (Thm.implies_elim inst base) step) end;

(* le helpers on ctxtU *)
fun le_refl_U_at t = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU t)] le_refl_U2);
fun le_total_U_at (mT, nT) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mT), (("n",0), ctermU nT)] le_total_U);
fun le_neq_lt_U_at (dT, nT) hle hneq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("d",0), ctermU dT), (("n",0), ctermU nT)] le_neq_lt_U)
  in (inst OF [hle]) OF [hneq] end;
fun sub_add_l_U_at (kT, jT_) = beta_norm (Drule.infer_instantiate ctxtU
      [(("k",0), ctermU kT),(("j",0), ctermU jT_)] sub_add_l_U);
fun le_trans_U_at (mt,nt,kt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("m",0), ctermU mt),(("n",0), ctermU nt),(("k",0), ctermU kt)] le_trans_U)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun lt_irrefl_U_at nt h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU nt)] lt_irrefl_U)) h;

(* le_or_lt on ctxtU : Disj (le x y)(lt y x)  (mirror le_or_lt) *)
fun le_or_lt_U (xT, yT) =
  let
    val goalC = mkDisj (le xT yT) (lt yT xT);
    val tot = le_total_U_at (xT, yT);
    val cA =
      let val h = Thm.assume (ctermU (jT (le xT yT)))
      in Thm.implies_intr (ctermU (jT (le xT yT))) (disjI1_U_at (le xT yT, lt yT xT) h) end;
    val cB =
      let
        val hyx = Thm.assume (ctermU (jT (le yT xT)));
        val em = ex_middle_U_at (oeq yT xT);
        val sA =
          let
            val heq = Thm.assume (ctermU (jT (oeq yT xT)));
            val lerx = le_refl_U_at xT;
            val zF = Free("z_lol", natT);
            val Pz = Term.lambda zF (le xT zF);
            val lexy = oeq_rw_U (Pz, xT, yT) (oeq_sym_U OF [heq]) lerx;
          in Thm.implies_intr (ctermU (jT (oeq yT xT)))
               (disjI1_U_at (le xT yT, lt yT xT) lexy) end;
        val sB =
          let
            val hneq = Thm.assume (ctermU (jT (neg (oeq yT xT))));
            val ltyx = le_neq_lt_U_at (yT, xT) hyx hneq;
          in Thm.implies_intr (ctermU (jT (neg (oeq yT xT))))
               (disjI2_U_at (le xT yT, lt yT xT) ltyx) end;
        val r = disjE_U_at (oeq yT xT, neg (oeq yT xT), goalC) em sA sB;
      in Thm.implies_intr (ctermU (jT (le yT xT))) r end;
  in disjE_U_at (le xT yT, le yT xT, goalC) tot cA cB end;

(* recover : lt r p ==> contFn given hPeq : oeq p (add r (sub p r))  (mirror recover_p_r) *)
fun recover_p_r_U (rT, pT) hRlt goalC contFn =
  let
    val Pabs = Abs("w", natT, oeq pT (add (suc rT) (Bound 0)));
    fun body wF (hw : thm) =
      let
        val aS = addSuc_U (rT, wF);
        val c1 = addcomm_U (rT, suc wF);
        val aS2 = addSuc_U (wF, rT);
        val cwr = addcomm_U (wF, rT);
        val swr = Succong_U cwr;
        val rSucw_eq = oeq_trans_U OF [oeq_trans_U OF [c1, aS2], swr];
        val aSr = oeq_trans_U OF [aS, oeq_sym_U OF [rSucw_eq]];
        val hw2 = oeq_trans_U OF [hw, aSr];
        val sal = sub_add_l_U_at (rT, suc wF);
        val zF = Free("z_rec", natT);
        val Pz = Term.lambda zF (oeq (sub zF rT) (suc wF));
        val hSub = oeq_rw_U (Pz, add rT (suc wF), pT) (oeq_sym_U OF [hw2]) sal;
        val zF2 = Free("z_rec2", natT);
        val Pz2 = Term.lambda zF2 (oeq pT (add rT zF2));
        val hPeq = oeq_rw_U (Pz2, suc wF, sub pT rT) (oeq_sym_U OF [hSub]) hw2;
      in contFn wF hPeq hSub end;
  in exE_U_at (Pabs, goalC) hRlt "w_rec" body end;
val () = out "STAGE_PH_HELPERS_READY\n";

(* rOf / flipPred / abstractions on ctxtU *)
fun rOfU a p k = rmod (mult a k) p;
fun flipPredU a p k = lt p (add (rOfU a p k) (rOfU a p k));
fun flipAbsU a p = let val zk = Free("k_fl", natT) in Term.lambda zk (flipPredU a p zk) end;
fun rmodAbsU q p = let val zk = Free("k_ra", natT) in Term.lambda zk (rmod (mult q zk) p) end;
(* lar q p is eta-contractible (k is the LAST arg); use the eta-contracted form so the
   sumf/cnt term shapes the proof produces (which beta/eta-normalise lar q p) match Pabs. *)
fun larAbsU  q p = larC $ q $ p;
val idAbsU = let val zk = Free("k_id", natT) in Term.lambda zk zk end;

(* ----------------------------------------------------------------------------
   per-k CORE :  0<p ==>
     parity(add (rmod(q*k)p)(lar q p k))
       = (1 if flipPred q p k else 0)   -- expressed as TWO conditional lemmas:
   coreNo  : le (2r) p ==> parity(add r (lar..)) = 0
   coreYes : lt p (2r) ==> parity(add r (lar..)) = parity p   (= 1 under odd p)
   ---------------------------------------------------------------------------- *)
fun coreNo_U (qF, pF, kt) =      (* le (2r) p ==> parity(add r lar) = 0 *)
  let
    val r = rOfU qF pF kt;
    val larT = lar qF pF kt;
    val hle = Thm.assume (ctermU (jT (le (add r r) pF)));
    val larEq = lar_lo_U_at (qF, pF, kt) hle;   (* lar = r *)
    val rwAbs = Abs("z", natT, oeq (parity (add r larT)) (parity (add r (Bound 0))));
    val rw = oeq_rw_U (rwAbs, larT, r) larEq (oeqRefl_U (parity (add r larT)));
             (* parity(add r lar) = parity(add r r) *)
    val pd = parity_double_U_at r;   (* parity(add r r) = 0 *)
    val res = oeq_trans_U OF [rw, pd];
  in Thm.implies_intr (ctermU (jT (le (add r r) pF))) res end;

fun coreYes_U (qF, pF, kt) hpos =   (* lt p (2r) ==> parity(add r lar) = parity p *)
  let
    val r = rOfU qF pF kt;
    val larT = lar qF pF kt;
    val hlt = Thm.assume (ctermU (jT (lt pF (add r r))));
    val larEq = lar_hi_U_at (qF, pF, kt) hlt;    (* lar = sub p r *)
    val rltp = rmod_lt_U_at (mult qF kt, pF) hpos;  (* lt r p *)
    val goalC = oeq (parity (add r larT)) (parity pF);
    fun cont wF hPeq hSub =     (* hPeq : oeq p (add r (sub p r)) *)
      let
        val rwAbs = Abs("z", natT, oeq (parity (add r larT)) (parity (add r (Bound 0))));
        val rw = oeq_rw_U (rwAbs, larT, sub pF r) larEq (oeqRefl_U (parity (add r larT)));
                 (* parity(add r lar) = parity(add r (sub p r)) *)
        val to_p_Abs = Abs("z", natT, oeq (parity (add r (sub pF r))) (parity (Bound 0)));
        val to_p = oeq_rw_U (to_p_Abs, add r (sub pF r), pF) (oeq_sym_U OF [hPeq])
                      (oeqRefl_U (parity (add r (sub pF r))));
                 (* parity(add r (sub p r)) = parity p *)
      in oeq_trans_U OF [rw, to_p] end;
    val res = recover_p_r_U (r, pF) rltp goalC cont;
  in Thm.implies_intr (ctermU (jT (lt pF (add r r)))) res end;

(* rmod0_U : 0<p ==> oeq (rmod (mult q 0) p) 0 *)
fun rmod0_U (qF, pF) hpos =
  let
    val ak0 = mult qF ZeroC;
    val d = rdiv ak0 pF;  val r = rmod ak0 pF;
    val divEq = div_mod_eq_U_at (ak0, pF) hpos;   (* oeq (q*0)(add (mult p d) r) *)
    val m0 = mult0r_U qF;                          (* oeq (mult q 0) 0 *)
    (* rewrite q*0 -> 0 on LHS : oeq 0 (add (mult p d) r) *)
    val zF = Free("z_rm0", natT);
    val Pz = Term.lambda zF (oeq zF (add (mult pF d) r));
    val z_eq = oeq_rw_U (Pz, ak0, ZeroC) m0 divEq;   (* oeq 0 (add (mult p d) r) *)
    val sumEq0 = oeq_sym_U OF [z_eq];                (* oeq (add (mult p d) r) 0 *)
    val comm = addcomm_U (mult pF d, r);            (* (mult p d + r)=(r + mult p d) *)
    val sumEq0' = oeq_trans_U OF [oeq_sym_U OF [comm], sumEq0];  (* oeq (add r (mult p d)) 0 *)
    val rZero = add_eq_zero_left_U_at (r, mult pF d) sumEq0';   (* oeq r 0 *)
  in rZero end;
val () = out "STAGE_PH_CORE_READY\n";

(* ----------------------------------------------------------------------------
   rmod_lar_cnt : 0<p ==> parity p = 1 ==>
     parity(add (sumf rmA n)(sumf laA n)) = parity(cnt flP n)   BY INDUCTION on n
   ---------------------------------------------------------------------------- *)
val rmod_lar_cnt =
  let
    val qF = Free("q", natT); val pF = Free("p", natT); val nF = Free("n", natT);
    val hpos  = Thm.assume (ctermU (jT (lt ZeroC pF)));
    val hoddP = Thm.assume (ctermU (jT (oeq (parity pF) oneC)));
    val rmA = rmodAbsU qF pF;
    val laA = larAbsU  qF pF;
    val flP = flipAbsU qF pF;
    val Pabs = Abs("z", natT, oeq (parity (add (sumf rmA (Bound 0))(sumf laA (Bound 0))))
                                  (parity (cnt flP (Bound 0))));

    (* BASE n=0 *)
    val r0 = rOfU qF pF ZeroC;   val lar0 = lar qF pF ZeroC;
    val baseThm =
      let
        val sr0 = beta_norm (sumf0_U rmA);  (* sumf rmA 0 = rmod(q*0)p *)
        val sl0 = beta_norm (sumf0_U laA);  (* sumf laA 0 = lar q p 0 *)
        val c0  = cnt0_U flP;               (* cnt flP 0 = 0 *)
        (* LHS -> parity(add r0 lar0) *)
        val l1Abs = Abs("z", natT, oeq (parity (add (sumf rmA ZeroC)(sumf laA ZeroC)))
                                       (parity (add (Bound 0)(sumf laA ZeroC))));
        val l1 = oeq_rw_U (l1Abs, sumf rmA ZeroC, r0) sr0
                    (oeqRefl_U (parity (add (sumf rmA ZeroC)(sumf laA ZeroC))));
        val l2Abs = Abs("z", natT, oeq (parity (add r0 (sumf laA ZeroC)))
                                       (parity (add r0 (Bound 0))));
        val l2 = oeq_rw_U (l2Abs, sumf laA ZeroC, lar0) sl0
                    (oeqRefl_U (parity (add r0 (sumf laA ZeroC))));
        val lhsTo = oeq_trans_U OF [l1, l2];   (* = parity(add r0 lar0) *)
        (* RHS -> 0 *)
        val rTo0Abs = Abs("z", natT, oeq (parity (cnt flP ZeroC)) (parity (Bound 0)));
        val rTo0 = oeq_rw_U (rTo0Abs, cnt flP ZeroC, ZeroC) c0 (oeqRefl_U (parity (cnt flP ZeroC)));
        val rhsTo = oeq_trans_U OF [rTo0, parity_0_U];   (* parity(cnt flP 0) = 0 *)
        (* CORE : parity(add r0 lar0) = 0.  rmod0 -> r0 = 0 -> 2*0=0 le p (le_add) -> lar_lo lar0=0 *)
        val r0zero = rmod0_U (qF, pF) hpos;   (* oeq r0 0 *)
        (* rewrite r0 -> 0 in lar0's lo-condition : le (add r0 r0) p ; with r0=0 -> le (add 0 0) p *)
        (* easier : directly compute lar0 via lo branch using le (2 r0) p from r0=0 *)
        (* le (add r0 r0) p : rewrite r0->0 then le 0 p... use le_add (le 0 (0 + p))?  Build le 0 p. *)
        (* le 0 p : le_add (0, p) gives le 0 (0 + p); but we want le 0 p.  Simpler: le (add r0 r0) p
           via r0=0 : add r0 r0 = add 0 0 = 0 ; then le 0 p.  le 0 p : from hpos lt 0 p = le (Suc 0) p,
           and le 0 (Suc 0)... Cleanest: le_add (ZeroC, p) : le 0 (add 0 p); add 0 p = p so le 0 p. *)
        val le0_0p = le_add_U_at (ZeroC, pF);    (* le 0 (add 0 p) *)
        (* add 0 p = p : varifyU add_0 *)
        val add0p_U = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU pF)] (varifyU add_0));
        val zF = Free("z_le0p", natT);
        val Pz0 = Term.lambda zF (le ZeroC zF);
        val le0p = oeq_rw_U (Pz0, add ZeroC pF, pF) add0p_U le0_0p;   (* le 0 p *)
        (* le (add r0 r0) p : rewrite 0 -> add r0 r0 ?  We have le 0 p ; want le (add r0 r0) p.
           add r0 r0 = add 0 0 = 0 [r0=0].  rewrite the term add r0 r0 to 0 then back: build
           oeq (add r0 r0) 0 then rewrite le (.) p. *)
        val rr_eq0 =
          let
            val s1 = add_cong_l_U (r0, ZeroC, r0) r0zero;   (* (r0 + r0)=(0 + r0) *)
            val s2 = add_cong_r_U (ZeroC, r0, ZeroC) r0zero;(* (0 + r0)=(0 + 0) *)
            val a00 = add0r_U ZeroC;                        (* (0 + 0)=0 *)
          in oeq_trans_U OF [oeq_trans_U OF [s1, s2], a00] end;  (* (r0 + r0)=0 *)
        val Pz1 = Term.lambda zF (le zF pF);
        val hle_rr = oeq_rw_U (Pz1, ZeroC, add r0 r0) (oeq_sym_U OF [rr_eq0]) le0p;  (* le (add r0 r0) p *)
        val coreNoImp = coreNo_U (qF, pF, ZeroC);   (* le (2 r0) p ==> parity(add r0 lar0)=0 *)
        val core = Thm.implies_elim coreNoImp hle_rr;   (* parity(add r0 lar0)=0 *)
      in oeq_trans_U OF [oeq_trans_U OF [lhsTo, core], oeq_sym_U OF [rhsTo]] end;

    (* STEP n -> Suc n *)
    val xF = Free("x", natT);
    val ihP = jT (oeq (parity (add (sumf rmA xF)(sumf laA xF))) (parity (cnt flP xF)));
    val IH  = Thm.assume (ctermU ihP);
    val rSx = rOfU qF pF (suc xF);   val larSx = lar qF pF (suc xF);
    val stepConcl =
      let
        val srS = beta_norm (sumfSuc_U (rmA, xF));  (* sumf rmA (Suc x)=add(sumf rmA x)(rmod(q*Sucx)p) *)
        val slS = beta_norm (sumfSuc_U (laA, xF));  (* sumf laA (Suc x)=add(sumf laA x)(lar q p (Suc x)) *)
        val SR = sumf rmA xF; val SL = sumf laA xF;
        (* LHS : parity(add (sumf rmA (Suc x))(sumf laA (Suc x)))
                 -> parity(add (add SR rSx)(add SL larSx))  via srS,slS *)
        val lAbs1 = Abs("z", natT, oeq (parity (add (sumf rmA (suc xF))(sumf laA (suc xF))))
                                       (parity (add (Bound 0)(sumf laA (suc xF)))));
        val lc1 = oeq_rw_U (lAbs1, sumf rmA (suc xF), add SR rSx) srS
                    (oeqRefl_U (parity (add (sumf rmA (suc xF))(sumf laA (suc xF)))));
        val lAbs2 = Abs("z", natT, oeq (parity (add (add SR rSx)(sumf laA (suc xF))))
                                       (parity (add (add SR rSx)(Bound 0))));
        val lc2 = oeq_rw_U (lAbs2, sumf laA (suc xF), add SL larSx) slS
                    (oeqRefl_U (parity (add (add SR rSx)(sumf laA (suc xF)))));
        val lhsExp = oeq_trans_U OF [lc1, lc2];
                     (* parity(add(sumf..Sucx)(sumf..Sucx)) = parity(add (add SR rSx)(add SL larSx)) *)
        (* parity(add (add SR rSx)(add SL larSx))
             = parity(add (add SR SL)(add rSx larSx))   [reassoc + comm, via parity_add twice]
           Use parity_add to split into parts and recombine.  Concretely:
             P(add(SR+rSx)(SL+larSx)) = P(add(P(SR+rSx))(P(SL+larSx)))   [parity_add]
           and similarly P(add(SR+SL)(rSx+larSx)) = P(add(P(SR+SL))(P(rSx+larSx))).
           We will instead use the additive structure on PARITY via the commutative monoid
           of parities.  Cleaner: prove
             parity(add (add SR rSx)(add SL larSx)) = parity(add (add SR SL)(add rSx larSx))
           by a pure add-rearrangement (assoc/comm) congruence (no parity needed). *)
        val rearr =
          let
            (* (SR+rSx)+(SL+larSx) = (SR+SL)+(rSx+larSx)
               LHS = SR + (rSx + (SL + larSx))            [assoc]
                   = SR + ((rSx + SL) + larSx)            [assoc^-1 inner]
                   = SR + ((SL + rSx) + larSx)            [comm]
                   = SR + (SL + (rSx + larSx))            [assoc inner]
                   = (SR + SL) + (rSx + larSx)            [assoc^-1] *)
            val a1 = addassoc_U (SR, rSx, add SL larSx);  (* (SR+rSx)+(SL+larSx) = SR+(rSx+(SL+larSx)) *)
            val inner1 = addassoc_U (rSx, SL, larSx);     (* (rSx+SL)+larSx = rSx+(SL+larSx) *)
            val inner1s = oeq_sym_U OF [inner1];          (* rSx+(SL+larSx) = (rSx+SL)+larSx *)
            val c_in = addcomm_U (rSx, SL);               (* (rSx+SL)=(SL+rSx) *)
            val c_in_c = add_cong_l_U (add rSx SL, add SL rSx, larSx) c_in;  (* (rSx+SL)+larSx=(SL+rSx)+larSx *)
            val inner2 = addassoc_U (SL, rSx, larSx);     (* (SL+rSx)+larSx = SL+(rSx+larSx) *)
            val innerChain = oeq_trans_U OF [oeq_trans_U OF [inner1s, c_in_c], inner2];
                             (* rSx+(SL+larSx) = SL+(rSx+larSx) *)
            val innerCong = add_cong_r_U (SR, add rSx (add SL larSx), add SL (add rSx larSx)) innerChain;
                            (* SR+(rSx+(SL+larSx)) = SR+(SL+(rSx+larSx)) *)
            val a2 = addassoc_U (SR, SL, add rSx larSx);  (* (SR+SL)+(rSx+larSx) = SR+(SL+(rSx+larSx)) *)
            val a2s = oeq_sym_U OF [a2];                  (* SR+(SL+(rSx+larSx)) = (SR+SL)+(rSx+larSx) *)
          in oeq_trans_U OF [oeq_trans_U OF [a1, innerCong], a2s] end;
                (* (SR+rSx)+(SL+larSx) = (SR+SL)+(rSx+larSx) *)
        val rearrP = let val pAbs = Abs("z", natT, oeq (parity (add (add SR rSx)(add SL larSx)))
                                                       (parity (Bound 0)))
                     in oeq_rw_U (pAbs, add (add SR rSx)(add SL larSx), add (add SR SL)(add rSx larSx))
                          rearr (oeqRefl_U (parity (add (add SR rSx)(add SL larSx)))) end;
                (* parity(add(SR+rSx)(SL+larSx)) = parity(add (SR+SL)(rSx+larSx)) *)
        (* parity(add (SR+SL)(rSx+larSx)) = parity(add (parity(SR+SL))(parity(rSx+larSx))) [parity_add] *)
        val pa = parityAdd_U_at (add SR SL, add rSx larSx);
        (* IH : parity(SR+SL) = parity(cnt flP x).  rewrite inside add (.)(parity(rSx+larSx)) *)
        val ihAbs = Abs("z", natT, oeq (parity (add (parity (add SR SL))(parity (add rSx larSx))))
                                       (parity (add (Bound 0)(parity (add rSx larSx)))));
        val ihRw = oeq_rw_U (ihAbs, parity (add SR SL), parity (cnt flP xF)) IH
                     (oeqRefl_U (parity (add (parity (add SR SL))(parity (add rSx larSx)))));
                   (* = parity(add (parity(cnt flP x))(parity(rSx+larSx))) *)
        (* now CASE on flipPred(Suc x) = lt p (2 rSx) via le_or_lt (2 rSx) p *)
        val tri = le_or_lt_U (add rSx rSx, pF);   (* Disj (le (2 rSx) p)(lt p (2 rSx)) *)
        val goalStep = oeq (parity (add (sumf rmA (suc xF))(sumf laA (suc xF))))
                           (parity (cnt flP (suc xF)));
        (* common pre-chain to "parity(add (parity(cnt flP x))(parity(rSx+larSx)))" *)
        val preChain = oeq_trans_U OF [lhsExp, oeq_trans_U OF [rearrP, oeq_trans_U OF [pa, ihRw]]];
                       (* parity(LHS) = parity(add (parity(cnt flP x))(parity(rSx+larSx))) *)
        val cNo =
          let
            val hle = Thm.assume (ctermU (jT (le (add rSx rSx) pF)))
            (* parity(rSx+larSx) = 0 *)
            val core0 = Thm.implies_elim (coreNo_U (qF, pF, suc xF)) hle;  (* parity(add rSx larSx)=0 *)
            (* rewrite parity(rSx+larSx) -> 0 : parity(add (parity(cnt flP x)) 0) = parity(parity(cnt flP x)) = parity(cnt flP x) *)
            val rwAbs = Abs("z", natT, oeq (parity (add (parity (cnt flP xF))(parity (add rSx larSx))))
                                           (parity (add (parity (cnt flP xF))(Bound 0))));
            val rw0 = oeq_rw_U (rwAbs, parity (add rSx larSx), ZeroC) core0
                        (oeqRefl_U (parity (add (parity (cnt flP xF))(parity (add rSx larSx)))));
                      (* = parity(add (parity(cnt flP x)) 0) *)
            val a0 = add0r_U (parity (cnt flP xF));   (* add (parity(cnt flP x)) 0 = parity(cnt flP x) *)
            val a0Abs = Abs("z", natT, oeq (parity (add (parity (cnt flP xF)) ZeroC)) (parity (Bound 0)));
            val a0p = oeq_rw_U (a0Abs, add (parity (cnt flP xF)) ZeroC, parity (cnt flP xF)) a0
                        (oeqRefl_U (parity (add (parity (cnt flP xF)) ZeroC)));
                      (* parity(add (parity(cnt flP x)) 0) = parity(parity(cnt flP x)) *)
            val idem = parity_idem_U_at (cnt flP xF);   (* parity(parity(cnt flP x))=parity(cnt flP x) *)
            val toCnt = oeq_trans_U OF [oeq_trans_U OF [rw0, a0p], idem];
                        (* parity(add(parity(cnt flP x))(parity(rSx+larSx))) = parity(cnt flP x) *)
            (* RHS : cnt flP (Suc x) = cnt flP x  (NO flip)  -> parity(cnt flP (Suc x))=parity(cnt flP x) *)
            (* ~flipPred(Suc x) from hle : ~(lt p (2 rSx)).  flipPred(Suc x)=lt p (2 rSx). *)
            val notFlip =
              let
                val hflip = Thm.assume (ctermU (jT (flipPredU qF pF (suc xF))));  (* lt p (2 rSx) = le (Suc p)(2 rSx) *)
                (* hle : le (2 rSx) p ; hflip : le (Suc p)(2 rSx) ; le_trans -> le (Suc p) p = lt p p -> false *)
                val le_Sp_p = le_trans_U_at (suc pF, add rSx rSx, pF) hflip hle;  (* le (Suc p) p = lt p p *)
                val ff = lt_irrefl_U_at pF le_Sp_p;
              in impI_U_at (flipPredU qF pF (suc xF), oFalseC)
                   (Thm.implies_intr (ctermU (jT (flipPredU qF pF (suc xF)))) ff) end;
            val cntStep = cntSucF_U (flP, xF) notFlip;   (* cnt flP (Suc x) = cnt flP x *)
            val cntStepP = let val pAbs = Abs("z", natT, oeq (parity (cnt flP (suc xF))) (parity (Bound 0)))
                           in oeq_rw_U (pAbs, cnt flP (suc xF), cnt flP xF) cntStep
                                (oeqRefl_U (parity (cnt flP (suc xF)))) end;
                           (* parity(cnt flP (Suc x)) = parity(cnt flP x) *)
            val res = oeq_trans_U OF [oeq_trans_U OF [preChain, toCnt], oeq_sym_U OF [cntStepP]];
                      (* parity(LHS) = parity(cnt flP (Suc x)) *)
          in Thm.implies_intr (ctermU (jT (le (add rSx rSx) pF))) res end;
        val cYes =
          let
            val hlt = Thm.assume (ctermU (jT (lt pF (add rSx rSx))))
            (* parity(rSx+larSx) = parity p = 1 *)
            val coreP = Thm.implies_elim (coreYes_U (qF, pF, suc xF) hpos) hlt;  (* parity(add rSx larSx)=parity p *)
            val core1 = oeq_trans_U OF [coreP, hoddP];   (* parity(add rSx larSx) = 1 *)
            (* parity(add (parity(cnt flP x)) (parity(rSx+larSx))) -> parity(add (parity(cnt flP x)) 1) *)
            val rwAbs = Abs("z", natT, oeq (parity (add (parity (cnt flP xF))(parity (add rSx larSx))))
                                           (parity (add (parity (cnt flP xF))(Bound 0))));
            val rw1 = oeq_rw_U (rwAbs, parity (add rSx larSx), oneC) core1
                        (oeqRefl_U (parity (add (parity (cnt flP xF))(parity (add rSx larSx)))));
                      (* = parity(add (parity(cnt flP x)) 1) *)
            (* RHS : cnt flP (Suc x) = Suc(cnt flP x)  (FLIP).
               parity(cnt flP (Suc x)) = parity(Suc(cnt flP x)).
               We must show parity(add (parity(cnt flP x)) 1) = parity(Suc(cnt flP x)).
               add (parity(cnt flP x)) 1 : compute parity.  parity(add z 1) where z=parity(cnt flP x).
               parity(add z (Suc 0)) = parity(Suc(add z 0)) = parity(Suc z) = sub 1(parity z).
               And parity(Suc(cnt flP x)) = sub 1(parity(cnt flP x)) = sub 1(parity z) [idem].
               So both equal sub 1(parity(cnt flP x)). *)
            val flipPredSx = flipPredU qF pF (suc xF);   (* = lt p (2 rSx) ; hlt has this *)
            val cntStep = cntSucT_U (flP, xF) hlt;       (* cnt flP (Suc x) = Suc(cnt flP x) *)
            val cntStepP = let val pAbs = Abs("z", natT, oeq (parity (cnt flP (suc xF))) (parity (Bound 0)))
                           in oeq_rw_U (pAbs, cnt flP (suc xF), suc (cnt flP xF)) cntStep
                                (oeqRefl_U (parity (cnt flP (suc xF)))) end;
                           (* parity(cnt flP (Suc x)) = parity(Suc(cnt flP x)) *)
            (* parity(Suc(cnt flP x)) = sub 1(parity(cnt flP x))  [parity_Suc] *)
            val pSucCnt = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU (cnt flP xF))] parity_Suc_U);
            (* parity(add (parity(cnt flP x)) 1) : let z = parity(cnt flP x).
               add z (Suc 0) = Suc(add z 0) ? no: add z (Suc 0) needs add_Suc on (?, ?). add z (Suc 0)
               = Suc(add z 0)? add_Suc is (Suc m + n)=Suc(m+n).  For (z + Suc 0) use comm:
                 z + Suc 0 = Suc 0 + z [comm] = Suc(0 + z) [add_Suc] = Suc(z) [add_0_left]. *)
            val zc = parity (cnt flP xF);
            val c1 = addcomm_U (zc, suc ZeroC);       (* (z + Suc 0)=(Suc 0 + z) *)
            val aS = addSuc_U (ZeroC, zc);            (* (Suc 0 + z)=Suc(0 + z) *)
            val a0l = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU zc)] (varifyU add_0)); (* (0 + z)=z *)
            val sCong = Succong_U a0l;                (* Suc(0 + z)=Suc z *)
            val zSuc0_eq = oeq_trans_U OF [oeq_trans_U OF [c1, aS], sCong];  (* (z + Suc 0)=Suc z *)
            (* parity(add z (Suc 0)) = parity(Suc z) *)
            val pAbsZ = Abs("w", natT, oeq (parity (add zc (suc ZeroC))) (parity (Bound 0)));
            val pz1 = oeq_rw_U (pAbsZ, add zc (suc ZeroC), suc zc) zSuc0_eq
                        (oeqRefl_U (parity (add zc (suc ZeroC))));
                      (* parity(add z 1) = parity(Suc z) *)
            val pSucz = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU zc)] parity_Suc_U);
                        (* parity(Suc z) = sub 1(parity z) *)
            (* idem : parity z = parity(parity(cnt flP x)) ... z is already parity(cnt flP x); parity z = parity(parity(cnt flP x)) *)
            (* parity(Suc z) = sub 1(parity z) ; parity(Suc(cnt flP x)) = sub 1(parity(cnt flP x)) = sub 1(parity z')
               but z = parity(cnt flP x), so parity z = parity(parity(cnt flP x)) = parity(cnt flP x) [idem] = z.
               Hence sub 1(parity z) = sub 1 z' where... let's chain directly:
                 LHS path: parity(add z 1) = parity(Suc z) = sub 1(parity z)
                 RHS path: parity(Suc(cnt flP x)) = sub 1(parity(cnt flP x))
               Need sub 1(parity z) = sub 1(parity(cnt flP x)).  z = parity(cnt flP x), so
               parity z = parity(parity(cnt flP x)) = parity(cnt flP x) [idem].  So
               sub 1(parity z) = sub 1(parity(cnt flP x)) via rewriting parity z -> parity(cnt flP x). *)
            val idemC = parity_idem_U_at (cnt flP xF);  (* parity(parity(cnt flP x)) = parity(cnt flP x) *)
            (* sub 1(parity z) -> sub 1(parity(cnt flP x)) : z = parity(cnt flP x), parity z = parity(parity(cnt flP x)) *)
            val subAbs = Abs("w", natT, oeq (sub oneC (parity zc)) (sub oneC (Bound 0)));
            val subRw = oeq_rw_U (subAbs, parity zc, parity (cnt flP xF)) idemC
                          (oeqRefl_U (sub oneC (parity zc)));
                        (* sub 1(parity z) = sub 1(parity(cnt flP x)) *)
            (* LHS chain : parity(add z 1) = parity(Suc z) [pz1] = sub 1(parity z) [pSucz]
                          = sub 1(parity(cnt flP x)) [subRw] *)
            val lhsToSub = oeq_trans_U OF [pz1, oeq_trans_U OF [pSucz, subRw]];
                           (* parity(add z 1) = sub 1(parity(cnt flP x)) *)
            (* RHS chain : parity(cnt flP (Suc x)) = parity(Suc(cnt flP x)) [cntStepP]
                          = sub 1(parity(cnt flP x)) [pSucCnt] *)
            val rhsToSub = oeq_trans_U OF [cntStepP, pSucCnt];
                           (* parity(cnt flP (Suc x)) = sub 1(parity(cnt flP x)) *)
            val res = oeq_trans_U OF [oeq_trans_U OF [preChain, oeq_trans_U OF [rw1, lhsToSub]],
                                      oeq_sym_U OF [rhsToSub]];
                      (* parity(LHS) = parity(cnt flP (Suc x)) *)
          in Thm.implies_intr (ctermU (jT (lt pF (add rSx rSx)))) res end;
        val stepRes = disjE_U_at (le (add rSx rSx) pF, lt pF (add rSx rSx), goalStep) tri cNo cYes;
      in stepRes end;
    val stepF = Thm.forall_intr (ctermU xF) (Thm.implies_intr (ctermU ihP) stepConcl);
    val run = nat_induct_U_run Pabs nF baseThm stepF;
    val d2 = Thm.implies_intr (ctermU (jT (oeq (parity pF) oneC))) run;
    val d1 = Thm.implies_intr (ctermU (jT (lt ZeroC pF))) d2;
  in varify d1 end;
val () = out "STAGE_PH_RLC_BUILT\n";

(* validate rmod_lar_cnt : 0-hyp-mod-2-premises + aconv *)
val qV_rlc = Var(("q",0),natT); val pV_rlc = Var(("p",0),natT); val nV_rlc = Var(("n",0),natT);
val rmAv_rlc = rmodAbsU qV_rlc pV_rlc;
val laAv_rlc = larAbsU  qV_rlc pV_rlc;
val flPv_rlc = flipAbsU qV_rlc pV_rlc;
val i_rmod_lar_cnt =
  Logic.mk_implies (jT (lt ZeroC pV_rlc),
    Logic.mk_implies (jT (oeq (parity pV_rlc) oneC),
      jT (oeq (parity (add (sumf rmAv_rlc nV_rlc)(sumf laAv_rlc nV_rlc)))
              (parity (cnt flPv_rlc nV_rlc)))));
val r_rmod_lar_cnt =
  let val ok = (length (Thm.hyps_of rmod_lar_cnt) = 0)
               andalso (length (Thm.extra_shyps rmod_lar_cnt) = 0)
               andalso ((Thm.prop_of rmod_lar_cnt) aconv i_rmod_lar_cnt)
  in (if ok then out "OK rmod_lar_cnt\n"
      else (out "FAIL rmod_lar_cnt\n";
            out ("  got = " ^ Syntax.string_of_term ctxtU (Thm.prop_of rmod_lar_cnt) ^ "\n");
            out ("  int = " ^ Syntax.string_of_term ctxtU i_rmod_lar_cnt ^ "\n"));
      ok) end;

(* ----------------------------------------------------------------------------
   bridge sumf_via_lsumf :  oeq (add (f 0) (lsumf (lmap f (upto n)))) (sumf f n)
   (sumf is 0..n inclusive; upto n = [1..n]; the f 0 term is the missing head)
   BY INDUCTION on n.
   ---------------------------------------------------------------------------- *)
val sumf_via_lsumf =
  let
    val fF = Free("f", lfnT);
    val nF = Free("n", natT);
    fun lhs z = add (fF $ ZeroC) (lsumf (lmap fF (uptoF z)));
    val Pabs = Abs("z", natT, oeq (lhs (Bound 0)) (sumf fF (Bound 0)));
    (* BASE n=0 : add (f 0)(lsumf(lmap f (upto 0))) = sumf f 0
       upto 0 = lnil ; lmap f lnil = lnil ; lsumf lnil = 0 ; add (f 0) 0 = f 0 ; sumf f 0 = f 0 *)
    val baseThm =
      let
        val uz = uptoZero_U ();           (* leq (upto 0) lnil *)
        (* lmap f (upto 0) : rewrite upto 0 -> lnil then lmap f lnil = lnil *)
        val lmU = lmap_cong_U fF (uptoF ZeroC, lnilC) uz;   (* leq (lmap f (upto 0))(lmap f lnil) *)
        val lmN = lmapNil_U fF;                              (* leq (lmap f lnil) lnil *)
        val lmZero = oeqRefl_U (lhs ZeroC);
        (* lsumf(lmap f (upto 0)) -> lsumf(lmap f lnil) -> lsumf lnil -> 0 *)
        val s1 = lsumf_cong_U (lmap fF (uptoF ZeroC), lmap fF lnilC) lmU;  (* lsumf(lmap f(upto0))=lsumf(lmap f lnil) *)
        val s2 = lsumf_cong_U (lmap fF lnilC, lnilC) lmN;                  (* =lsumf lnil *)
        val s3 = lsumfNil_U ();                                            (* lsumf lnil = 0 *)
        val lsZero = oeq_trans_U OF [oeq_trans_U OF [s1, s2], s3];         (* lsumf(lmap f(upto0))=0 *)
        (* add (f 0)(lsumf..) -> add (f 0) 0 -> f 0 *)
        val rwAbs = Abs("z", natT, oeq (lhs ZeroC) (add (fF $ ZeroC)(Bound 0)));
        val toAdd0 = oeq_rw_U (rwAbs, lsumf (lmap fF (uptoF ZeroC)), ZeroC) lsZero (oeqRefl_U (lhs ZeroC));
                     (* lhs 0 = add (f 0) 0 *)
        val a0 = add0r_U (fF $ ZeroC);   (* add (f 0) 0 = f 0 *)
        val lhsTo = oeq_trans_U OF [toAdd0, a0];   (* lhs 0 = f 0 *)
        (* sumf f 0 = f 0 *)
        val sf0 = sumf0_U fF;
      in oeq_trans_U OF [lhsTo, oeq_sym_U OF [sf0]] end;   (* lhs 0 = sumf f 0 *)
    (* STEP n -> Suc n *)
    val xF = Free("x", natT);
    val ihP = jT (oeq (lhs xF) (sumf fF xF));
    val IH  = Thm.assume (ctermU ihP);
    val stepConcl =
      let
        (* upto(Suc x) = (Suc x)::upto x *)
        val us = uptoSuc_U xF;     (* leq (upto(Suc x))((Suc x)::upto x) *)
        (* lmap f (upto(Suc x)) : rewrite -> lmap f ((Suc x)::upto x) -> (f(Suc x))::lmap f (upto x) *)
        val lmCong = lmap_cong_U fF (uptoF (suc xF), lcons (suc xF)(uptoF xF)) us;
                     (* leq (lmap f(upto(Suc x)))(lmap f((Suc x)::upto x)) *)
        val lmCons = lmapCons_U (fF, suc xF, uptoF xF);
                     (* leq (lmap f((Suc x)::upto x))((f(Suc x))::lmap f(upto x)) *)
        (* lsumf(lmap f(upto(Suc x))) = lsumf((f(Suc x))::lmap f(upto x)) = add (f(Suc x))(lsumf(lmap f(upto x))) *)
        val ls1 = lsumf_cong_U (lmap fF (uptoF (suc xF)), lmap fF (lcons (suc xF)(uptoF xF))) lmCong;
        val ls2 = lsumf_cong_U (lmap fF (lcons (suc xF)(uptoF xF)), lcons (fF $ (suc xF))(lmap fF (uptoF xF))) lmCons;
        val ls3 = lsumfCons_U (fF $ (suc xF), lmap fF (uptoF xF));
                  (* lsumf((f(Suc x))::lmap f(upto x))=add (f(Suc x))(lsumf(lmap f(upto x))) *)
        val lsSx = oeq_trans_U OF [oeq_trans_U OF [ls1, ls2], ls3];
                   (* lsumf(lmap f(upto(Suc x)))=add (f(Suc x))(lsumf(lmap f(upto x))) *)
        (* lhs(Suc x) = add (f 0)(lsumf(lmap f(upto(Suc x))))
                      -> add (f 0)(add (f(Suc x))(lsumf(lmap f(upto x)))) *)
        val rwAbs = Abs("z", natT, oeq (lhs (suc xF)) (add (fF $ ZeroC)(Bound 0)));
        val lhsExp = oeq_rw_U (rwAbs, lsumf (lmap fF (uptoF (suc xF))),
                                      add (fF $ (suc xF))(lsumf (lmap fF (uptoF xF)))) lsSx
                       (oeqRefl_U (lhs (suc xF)));
                     (* lhs(Suc x) = add (f 0)(add (f(Suc x))(lsumf(lmap f(upto x)))) *)
        (* rearrange : add (f 0)(add (f(Suc x)) L) = add (add (f 0) L)(f(Suc x))
             add (f 0)(f(Sx) + L) = (f 0 + f(Sx)) + L   [assoc^-1]
                                   = (f(Sx) + f 0) + L   [comm]
                                   = f(Sx) + (f 0 + L)   [assoc]
                                   = (f 0 + L) + f(Sx)   [comm]   *)
        val L = lsumf (lmap fF (uptoF xF));
        val f0 = fF $ ZeroC; val fSx = fF $ (suc xF);
        val a1 = addassoc_U (f0, fSx, L);            (* (f0+fSx)+L = f0+(fSx+L) *)
        val a1s = oeq_sym_U OF [a1];                 (* f0+(fSx+L) = (f0+fSx)+L *)
        val c1 = addcomm_U (f0, fSx);                (* (f0+fSx)=(fSx+f0) *)
        val c1c = add_cong_l_U (add f0 fSx, add fSx f0, L) c1;  (* (f0+fSx)+L=(fSx+f0)+L *)
        val a2 = addassoc_U (fSx, f0, L);            (* (fSx+f0)+L = fSx+(f0+L) *)
        val c2 = addcomm_U (fSx, add f0 L);          (* (fSx+(f0+L))=((f0+L)+fSx) *)
        val rearr = oeq_trans_U OF [oeq_trans_U OF [oeq_trans_U OF [a1s, c1c], a2], c2];
                    (* f0+(fSx+L) = (f0+L)+fSx *)
        (* lhs(Suc x) = (f0+L)+fSx ; IH: f0+L = sumf f x ; so = (sumf f x)+fSx *)
        val lhsRe = oeq_trans_U OF [lhsExp, rearr];   (* lhs(Suc x) = add (add f0 L) fSx *)
        val ihRw = add_cong_l_U (add f0 L, sumf fF xF, fSx) IH;  (* (f0+L)+fSx = (sumf f x)+fSx *)
        val lhsSumf = oeq_trans_U OF [lhsRe, ihRw];   (* lhs(Suc x) = add (sumf f x)(f(Suc x)) *)
        (* sumf f (Suc x) = add (sumf f x)(f(Suc x)) *)
        val sfS = sumfSuc_U (fF, xF);
      in oeq_trans_U OF [lhsSumf, oeq_sym_U OF [sfS]] end;   (* lhs(Suc x) = sumf f (Suc x) *)
    val stepF = Thm.forall_intr (ctermU xF) (Thm.implies_intr (ctermU ihP) stepConcl);
    val run = nat_induct_U_run Pabs nF baseThm stepF;
  in varify run end;
val fV_svl = Var(("f",0),lfnT); val nV_svl = Var(("n",0),natT);
val i_sumf_via_lsumf =
  jT (oeq (add (fV_svl $ ZeroC) (lsumf (lmapC $ fV_svl $ (uptoF nV_svl)))) (sumf fV_svl nV_svl));
val r_sumf_via_lsumf = checkU ("sumf_via_lsumf", sumf_via_lsumf, i_sumf_via_lsumf);
fun sumf_via_lsumf_U_at fT nt = beta_norm (Drule.infer_instantiate ctxtU
      [(("f",0), ctermU fT),(("n",0), ctermU nt)] (toU sumf_via_lsumf));
val () = out "STAGE_PH_BRIDGE_BUILT\n";

(* ----------------------------------------------------------------------------
   lmap_id : leq (lmap (\k.k) L) L   (by list_induct)  -- to identify
   lsumf(lmap id (upto m)) with lsumf(upto m).
   ---------------------------------------------------------------------------- *)
val lmap_id =
  let
    val idF = idAbsU;    (* (\k.k) *)
    fun concBody zt = leq (lmap idF zt) zt;
    val Qpred = Abs("z", natlistT, concBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtU
          [(("P",0), ctermU Qpred), (("a",0), ctermU LF)] list_induct_U);
    val base = lmapNil_U idF;    (* leq (lmap id lnil) lnil *)
    val yF = Free("y", natT); val tF = Free("t", natlistT);
    val ihprop = jT (concBody tF);
    val IH = Thm.assume (ctermU ihprop);
    val stepConcl =
      let
        val lmc = lmapCons_U (idF, yF, tF);   (* leq (lmap id (y::t)) ((id y)::lmap id t) *)
        (* id y = y (beta) ; lmap id t leq t (IH) ; so (id y)::lmap id t leq y::t *)
        (* leq ((id y)::lmap id t)(y :: t) : need leq on cons via cong.  Build via leq_subst on
           the tail and the head id-beta.  Use lcons cong : since (id y) beta y, the term
           lcons (idF$y) (lmap idF t) is DEFINITIONALLY lcons y (lmap idF t) after beta. *)
        val lmcB = beta_norm lmc;   (* leq (lmap id(y::t))(lcons y (lmap id t)) *)
        (* leq (lcons y (lmap id t))(lcons y t) : from IH (leq (lmap id t) t) via cong on tail *)
        val tailCong =
          let val Pabs = Abs("z", natlistT, leq (lcons yF (lmap idF tF)) (lcons yF (Bound 0)))
          in leq_rw_U (Pabs, lmap idF tF, tF) IH (leqRefl_U (lcons yF (lmap idF tF))) end;
                      (* leq (lcons y (lmap id t))(lcons y t) *)
        (* chain leq : lmap id (y::t) -> lcons y (lmap id t) -> y::t.  leq is transitive via leq_subst. *)
        val chain =
          let val Pabs = Abs("z", natlistT, leq (lmap idF (lcons yF tF)) (Bound 0))
          in leq_rw_U (Pabs, lcons yF (lmap idF tF), lcons yF tF) tailCong lmcB end;
                      (* leq (lmap id(y::t))(y::t) *)
      in chain end;
    val step1 = Thm.forall_intr (ctermU yF)
                  (Thm.forall_intr (ctermU tF) (Thm.implies_intr (ctermU ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;
val LV_lmid = Var(("L",0), natlistT);
val i_lmap_id = jT (leq (lmapC $ idAbsU $ LV_lmid) LV_lmid);
val r_lmap_id = checkU ("lmap_id", lmap_id, i_lmap_id);
fun lmap_id_U_at Lt = beta_norm (Drule.infer_instantiate ctxtU [(("L",0), ctermU Lt)] (toU lmap_id));

(* lar0_zero : 0<p ==> oeq (lar q p 0) 0   (rmod0 + lar_lo at k=0) *)
fun lar0_zero_U (qF, pF) hpos =
  let
    val r0 = rOfU qF pF ZeroC;   val lar0 = lar qF pF ZeroC;
    val r0zero = rmod0_U (qF, pF) hpos;      (* oeq r0 0 *)
    (* le (add r0 r0) p from r0=0 (same as base) *)
    val le0_0p = le_add_U_at (ZeroC, pF);
    val add0p_U = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU pF)] (varifyU add_0));
    val zF = Free("z_l0z", natT);
    val Pz0 = Term.lambda zF (le ZeroC zF);
    val le0p = oeq_rw_U (Pz0, add ZeroC pF, pF) add0p_U le0_0p;   (* le 0 p *)
    val rr_eq0 =
      let
        val s1 = add_cong_l_U (r0, ZeroC, r0) r0zero;
        val s2 = add_cong_r_U (ZeroC, r0, ZeroC) r0zero;
        val a00 = add0r_U ZeroC;
      in oeq_trans_U OF [oeq_trans_U OF [s1, s2], a00] end;   (* (r0+r0)=0 *)
    val Pz1 = Term.lambda zF (le zF pF);
    val hle_rr = oeq_rw_U (Pz1, ZeroC, add r0 r0) (oeq_sym_U OF [rr_eq0]) le0p;  (* le (2r0) p *)
    val larEq = lar_lo_U_at (qF, pF, ZeroC) hle_rr;   (* oeq lar0 r0 *)
  in oeq_trans_U OF [larEq, r0zero] end;   (* oeq lar0 0 *)

(* prime2_gt1_U : prime2 p ==> lt 1 p  (conjunct1) ; lt0_of_prime_U : prime2 p ==> lt 0 p *)
fun prime2_gt1_U p hPrime =
  conjunct1_U_at (lt (suc ZeroC) p, mkForall (ppAbs p)) hPrime;   (* lt 1 p = le 2 p *)
fun lt0_of_prime_U p hPrime =
  let
    val gt1 = prime2_gt1_U p hPrime;                   (* le (Suc(Suc 0)) p *)
    val le12a = le_add_U_at (suc ZeroC, suc ZeroC);    (* le 1 (1 + 1) *)
    val addS = addSuc_U (ZeroC, suc ZeroC);            (* (Suc 0 + Suc 0)=Suc(0 + Suc 0) *)
    val a0 = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU (suc ZeroC))] (varifyU add_0)); (* (0 + Suc 0)=Suc 0 *)
    val sucCong = Succong_U a0;                         (* Suc(0+Suc 0)=Suc(Suc 0) *)
    val addeq = oeq_trans_U OF [addS, sucCong];
    val zF = Free("z_lt0u", natT);
    val Pz = Term.lambda zF (le (suc ZeroC) zF);
    val le12 = oeq_rw_U (Pz, add (suc ZeroC)(suc ZeroC), suc (suc ZeroC)) addeq le12a;
  in le_trans_U_at (suc ZeroC, suc (suc ZeroC), p) le12 gt1 end;   (* lt 0 p *)

(* ----------------------------------------------------------------------------
   sum_lar_eq_sum_id :  prime2 p ==> ~(dvd p q) ==> oeq (sub p 1)(add m m) ==>
       oeq (sumf (lar q p) m) (sumf (\k.k) m)
   from lar_sum_perm (lsumf form) + sumf_via_lsumf bridge + lmap_id + lar0_zero.
   (needs 0<p for rmod0/lar0_zero, derived from prime2.)
   ---------------------------------------------------------------------------- *)
val sum_lar_eq_sum_id =
  let
    val qF = Free("q", natT); val pF = Free("p", natT); val mF = Free("m", natT);
    val hPrime = Thm.assume (ctermU (jT (prime2 pF)));
    val hNq    = Thm.assume (ctermU (jT (neg (dvd pF qF))));
    val hOdd   = Thm.assume (ctermU (jT (oeq (sub pF oneC) (add mF mF))));
    val laA = larAbsU qF pF;     (* lar q p *)
    val U = uptoF mF;
    (* 0<p from prime2 : lt0_of_prime on ctxtU *)
    val hpos = lt0_of_prime_U pF hPrime;   (* lt 0 p *)
    (* lar_sum_perm instance : lsumf(lmap (lar q p) U) = lsumf U *)
    val lspI = beta_norm (Drule.infer_instantiate ctxtU
                 [(("p",0), ctermU pF),(("a",0), ctermU qF),(("m",0), ctermU mF)] (toU lar_sum_perm));
    val lspEq = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim lspI hPrime) hNq) hOdd;
                (* oeq (lsumf(lmap (lar q p) U)) (lsumf U) *)
    (* bridge at f = lar q p : add (lar q p 0)(lsumf(lmap (lar q p) U)) = sumf (lar q p) m *)
    val brLar = sumf_via_lsumf_U_at laA mF;   (* oeq (add (laA 0)(lsumf(lmap laA U))) (sumf laA m) *)
    val brLarB = beta_norm brLar;             (* laA 0 beta -> lar q p 0 *)
    (* bridge at f = idAbs : add (idAbs 0)(lsumf(lmap idAbs U)) = sumf idAbs m *)
    val brId = sumf_via_lsumf_U_at idAbsU mF;
    val brIdB = beta_norm brId;               (* idAbs 0 beta -> 0 *)
    (* lar q p 0 = 0 *)
    val lar0 = lar0_zero_U (qF, pF) hpos;     (* oeq (lar q p 0) 0 *)
    (* lmap idAbs U leq U -> lsumf(lmap id U) = lsumf U *)
    val lmid = lmap_id_U_at U;                (* leq (lmap id U) U *)
    val lsmid = lsumf_cong_U (lmap idAbsU U, U) lmid;   (* lsumf(lmap id U)=lsumf U *)
    (* RHS-lar : sumf laA m = add (lar q p 0)(lsumf(lmap laA U))   [brLarB sym]
                            = add 0 (lsumf(lmap laA U))            [lar0]
                            = add 0 (lsumf U)                       [lspEq]   *)
    val SL = sumf laA mF; val SI = sumf idAbsU mF;
    (* Build : sumf laA m -> add 0 (lsumf U) *)
    val brLarS = oeq_sym_U OF [brLarB];   (* sumf laA m = add (lar q p 0)(lsumf(lmap laA U)) *)
    val rwLar0Abs = Abs("z", natT, oeq (sumf laA mF) (add (Bound 0)(lsumf (lmap laA U))));
    val toAdd0Lar = oeq_rw_U (rwLar0Abs, lar qF pF ZeroC, ZeroC) lar0 brLarS;
                    (* sumf laA m = add 0 (lsumf(lmap laA U)) *)
    val rwLspAbs = Abs("z", natT, oeq (sumf laA mF) (add ZeroC (Bound 0)));
    val toLspLar = oeq_rw_U (rwLspAbs, lsumf (lmap laA U), lsumf U) lspEq toAdd0Lar;
                    (* sumf laA m = add 0 (lsumf U) *)
    (* Build : sumf idAbs m -> add 0 (lsumf U) *)
    val brIdS = oeq_sym_U OF [brIdB];   (* sumf idAbs m = add (idAbs 0)(lsumf(lmap idAbs U)) *)
    (* idAbs 0 beta = 0 already in brIdB? brIdB beta-normed so head is add 0 (lsumf(lmap id U)) *)
    val rwIdAbs = Abs("z", natT, oeq (sumf idAbsU mF) (add ZeroC (Bound 0)));
    val toLspId = oeq_rw_U (rwIdAbs, lsumf (lmap idAbsU U), lsumf U) lsmid brIdS;
                    (* sumf idAbs m = add 0 (lsumf U) *)
    val res = oeq_trans_U OF [toLspLar, oeq_sym_U OF [toLspId]];   (* sumf laA m = sumf idAbs m *)
    val d3 = Thm.implies_intr (ctermU (jT (oeq (sub pF oneC) (add mF mF)))) res;
    val d2 = Thm.implies_intr (ctermU (jT (neg (dvd pF qF)))) d3;
    val d1 = Thm.implies_intr (ctermU (jT (prime2 pF))) d2;
  in varify d1 end;
val qV_sli = Var(("q",0),natT); val pV_sli = Var(("p",0),natT); val mV_sli = Var(("m",0),natT);
val i_sum_lar_eq_sum_id =
  Logic.mk_implies (jT (prime2 pV_sli),
    Logic.mk_implies (jT (neg (dvd pV_sli qV_sli)),
      Logic.mk_implies (jT (oeq (sub pV_sli oneC) (add mV_sli mV_sli)),
        jT (oeq (sumf (larAbsU qV_sli pV_sli) mV_sli) (sumf idAbsU mV_sli)))));
val r_sum_lar_eq_sum_id = checkU ("sum_lar_eq_sum_id", sum_lar_eq_sum_id, i_sum_lar_eq_sum_id);
val () = out "STAGE_PH_SUMLAR_BUILT\n";

(* ----------------------------------------------------------------------------
   eis_parity_half2  (PH) :
     lt 0 p ==> oeq (parity p) 1 ==> prime2 p ==> ~(dvd p q) ==> oeq (sub p 1)(add m m)
       ==> oeq (parity (sumf (rmodAbs q p) m))
               (parity (add (sumf idAbs m) (cnt (flipAbs q p) m)))
   mu := cnt (flipAbs q p) m  (the genuine flip count).
   From rmod_lar_cnt (parity(A+B)=parity C, A=sum rmod, B=sum lar, C=cnt flip)
   + sum_lar_eq_sum_id (B = sum id) + parity arithmetic (A == B + C  (mod 2)).
   ---------------------------------------------------------------------------- *)
val () = out "STAGE_PH_ASSEMBLE_BEGIN\n";
val eis_parity_half2 =
  let
    val qF = Free("q", natT); val pF = Free("p", natT); val mF = Free("m", natT);
    val hpos  = Thm.assume (ctermU (jT (lt ZeroC pF)));
    val hoddP = Thm.assume (ctermU (jT (oeq (parity pF) oneC)));
    val hPrime= Thm.assume (ctermU (jT (prime2 pF)));
    val hNq   = Thm.assume (ctermU (jT (neg (dvd pF qF))));
    val hOdd  = Thm.assume (ctermU (jT (oeq (sub pF oneC) (add mF mF))));
    val rmA = rmodAbsU qF pF;   val laA = larAbsU qF pF;   val flP = flipAbsU qF pF;
    val A = sumf rmA mF;  val B = sumf laA mF;  val Bid = sumf idAbsU mF;  val C = cnt flP mF;
    (* rmod_lar_cnt : parity(add A B) = parity C *)
    val rlcI = beta_norm (Drule.infer_instantiate ctxtU
                 [(("q",0), ctermU qF),(("p",0), ctermU pF),(("n",0), ctermU mF)] (toU rmod_lar_cnt));
    val rlcE = Thm.implies_elim (Thm.implies_elim rlcI hpos) hoddP;   (* parity(add A B) = parity C *)
    (* sum_lar_eq_sum_id : B = Bid *)
    val sliI = beta_norm (Drule.infer_instantiate ctxtU
                 [(("q",0), ctermU qF),(("p",0), ctermU pF),(("m",0), ctermU mF)] (toU sum_lar_eq_sum_id));
    val sliE = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim sliI hPrime) hNq) hOdd;  (* B = Bid *)
    (* rewrite B -> Bid inside rlcE's LHS : Pabs z = (parity(add A z) = parity C) ; Pabs B = rlcE *)
    val rwBAbs = Abs("z", natT, oeq (parity (add A (Bound 0))) (parity C));
    val rlcId = oeq_rw_U (rwBAbs, B, Bid) sliE rlcE;   (* parity(add A Bid) = parity C *)
    (* GOAL : parity A = parity(add Bid C).  Derive parity(add Bid C) = parity A. *)
    (* parity(add Bid C) = parity(add (parity Bid)(parity C))  [parity_add] *)
    val pa1 = parityAdd_U_at (Bid, C);
    (* rewrite parity C -> parity(add A Bid)  [rlcId sym] inside add (parity Bid)(.) *)
    val rwCAbs = Abs("z", natT, oeq (parity (add (parity Bid)(parity C)))
                                    (parity (add (parity Bid)(Bound 0))));
    val pa2 = oeq_rw_U (rwCAbs, parity C, parity (add A Bid)) (oeq_sym_U OF [rlcId])
                (oeqRefl_U (parity (add (parity Bid)(parity C))));
              (* parity(add (parity Bid)(parity C)) = parity(add (parity Bid)(parity(add A Bid))) *)
    (* parity(add (parity Bid)(parity(add A Bid))) = parity(add Bid (add A Bid))  [parity_add rev] *)
    val pa3 = parityAdd_U_at (Bid, add A Bid);   (* parity(add Bid (add A Bid)) = parity(add (parity Bid)(parity(add A Bid))) *)
    (* add Bid (add A Bid) = add A (add Bid Bid)  [rearrange]
         Bid + (A + Bid) = (Bid + A) + Bid [assoc^-1] = (A + Bid) + Bid [comm] = A + (Bid + Bid) [assoc] *)
    val a1 = addassoc_U (Bid, A, Bid);          (* (Bid+A)+Bid = Bid+(A+Bid) *)
    val a1s = oeq_sym_U OF [a1];                (* Bid+(A+Bid) = (Bid+A)+Bid *)
    val c1 = addcomm_U (Bid, A);                (* (Bid+A)=(A+Bid) *)
    val c1c = add_cong_l_U (add Bid A, add A Bid, Bid) c1;  (* (Bid+A)+Bid=(A+Bid)+Bid *)
    val a2 = addassoc_U (A, Bid, Bid);          (* (A+Bid)+Bid = A+(Bid+Bid) *)
    val rearr = oeq_trans_U OF [oeq_trans_U OF [a1s, c1c], a2];  (* Bid+(A+Bid) = A+(Bid+Bid) *)
    val rearrP = let val pAbs = Abs("z", natT, oeq (parity (add Bid (add A Bid))) (parity (Bound 0)))
                 in oeq_rw_U (pAbs, add Bid (add A Bid), add A (add Bid Bid)) rearr
                      (oeqRefl_U (parity (add Bid (add A Bid)))) end;
                 (* parity(add Bid (add A Bid)) = parity(add A (add Bid Bid)) *)
    (* parity(add A (add Bid Bid)) = parity(add (parity A)(parity(add Bid Bid)))  [parity_add] *)
    val pa4 = parityAdd_U_at (A, add Bid Bid);
    (* parity(add Bid Bid) = 0  [parity_double] -> rewrite *)
    val pd = parity_double_U_at Bid;   (* parity(add Bid Bid) = 0 *)
    val rwDAbs = Abs("z", natT, oeq (parity (add (parity A)(parity (add Bid Bid))))
                                    (parity (add (parity A)(Bound 0))));
    val pa5 = oeq_rw_U (rwDAbs, parity (add Bid Bid), ZeroC) pd
                (oeqRefl_U (parity (add (parity A)(parity (add Bid Bid)))));
              (* parity(add(parity A)(parity(add Bid Bid))) = parity(add(parity A) 0) *)
    (* parity(add(parity A) 0) = parity(parity A) = parity A *)
    val a0 = add0r_U (parity A);   (* add(parity A) 0 = parity A *)
    val a0Abs = Abs("z", natT, oeq (parity (add (parity A) ZeroC)) (parity (Bound 0)));
    val a0p = oeq_rw_U (a0Abs, add (parity A) ZeroC, parity A) a0 (oeqRefl_U (parity (add (parity A) ZeroC)));
              (* parity(add(parity A)0) = parity(parity A) *)
    val idem = parity_idem_U_at A;   (* parity(parity A) = parity A *)
    (* full chain : parity(add Bid C) = ... = parity A *)
    val addBidC_eq_A =
      oeq_trans_U OF [pa1,
        oeq_trans_U OF [pa2,
          oeq_trans_U OF [oeq_sym_U OF [pa3],
            oeq_trans_U OF [rearrP,
              oeq_trans_U OF [pa4,
                oeq_trans_U OF [pa5,
                  oeq_trans_U OF [a0p, idem]]]]]]];
      (* parity(add Bid C) = parity A *)
    val res = oeq_sym_U OF [addBidC_eq_A];   (* parity A = parity(add Bid C) *)
    val d5 = Thm.implies_intr (ctermU (jT (oeq (sub pF oneC) (add mF mF)))) res;
    val d4 = Thm.implies_intr (ctermU (jT (neg (dvd pF qF)))) d5;
    val d3 = Thm.implies_intr (ctermU (jT (prime2 pF))) d4;
    val d2 = Thm.implies_intr (ctermU (jT (oeq (parity pF) oneC))) d3;
    val d1 = Thm.implies_intr (ctermU (jT (lt ZeroC pF))) d2;
  in varify d1 end;
val qV_ph = Var(("q",0),natT); val pV_ph = Var(("p",0),natT); val mV_ph = Var(("m",0),natT);
val rmAv_ph = rmodAbsU qV_ph pV_ph;
val flPv_ph = flipAbsU qV_ph pV_ph;
val i_eis_parity_half2 =
  Logic.mk_implies (jT (lt ZeroC pV_ph),
    Logic.mk_implies (jT (oeq (parity pV_ph) oneC),
      Logic.mk_implies (jT (prime2 pV_ph),
        Logic.mk_implies (jT (neg (dvd pV_ph qV_ph)),
          Logic.mk_implies (jT (oeq (sub pV_ph oneC) (add mV_ph mV_ph)),
            jT (oeq (parity (sumf rmAv_ph mV_ph))
                    (parity (add (sumf idAbsU mV_ph) (cnt flPv_ph mV_ph)))))))));
val r_eis_parity_half2 = checkU ("eis_parity_half2", eis_parity_half2, i_eis_parity_half2);
(* soundness probe : dropping ~(dvd p q) must change the statement *)
val probe_ph_needs_ndvd =
  let val bogus = Logic.mk_implies (jT (lt ZeroC pV_ph),
        Logic.mk_implies (jT (oeq (parity pV_ph) oneC),
          Logic.mk_implies (jT (prime2 pV_ph),
            Logic.mk_implies (jT (oeq (sub pV_ph oneC) (add mV_ph mV_ph)),
              jT (oeq (parity (sumf rmAv_ph mV_ph))
                      (parity (add (sumf idAbsU mV_ph) (cnt flPv_ph mV_ph))))))))
  in not ((Thm.prop_of eis_parity_half2) aconv bogus) end;
val () = if probe_ph_needs_ndvd then out "PROBE_OK eis_parity_half2 keeps ~(dvd p q)\n"
         else out "PROBE_FAIL eis_parity_half2\n";
val () = if r_eis_parity_half2 andalso probe_ph_needs_ndvd
         then out "EIS_PARITY_HALF2_OK\n" else out "EIS_PARITY_HALF2_FAILED\n";
val () = out "STAGE_PH_END\n";

(* ############################################################################
   ##########  (EP)  EISENSTEIN PARITY :  mu == sum floor (mod 2)  #############
   ----------------------------------------------------------------------------
   floor_sum_kr_parity (F2, banked) : parity(sum floor) = parity((sum id)+(sum rmod))
   eis_parity_half2    (PH)         : parity(sum rmod)  = parity((sum id) + mu)
   ==> parity(sum floor) = parity((sum id)+((sum id)+mu)) = parity(mu)  [parity_double kills 2*sum id]
   i.e.  mu == sum_{k=1..m} floor(q*k/p)  (mod 2),  mu = cnt flipPred m.
   ############################################################################ *)
val () = out "STAGE_EP_BEGIN\n";

(* floor abstraction matching F2's flAv : (\k_fa. rdiv (q*k) p) *)
fun floorAbsU q p = let val zk = Free("k_fa", natT) in Term.lambda zk (rdiv (mult q zk) p) end;
(* floor_sum_kr_parity onto ctxtU *)
val floor_sum_kr_parity_U = varifyU floor_sum_kr_parity;

val eisenstein_parity =
  let
    val qF = Free("q", natT); val pF = Free("p", natT); val mF = Free("m", natT);
    val hpos  = Thm.assume (ctermU (jT (lt ZeroC pF)));
    val hoddQ = Thm.assume (ctermU (jT (oeq (parity qF) oneC)));
    val hoddP = Thm.assume (ctermU (jT (oeq (parity pF) oneC)));
    val hPrime= Thm.assume (ctermU (jT (prime2 pF)));
    val hNq   = Thm.assume (ctermU (jT (neg (dvd pF qF))));
    val hOdd  = Thm.assume (ctermU (jT (oeq (sub pF oneC) (add mF mF))));
    val flA = floorAbsU qF pF;   val rmA = rmodAbsU qF pF;   val flP = flipAbsU qF pF;
    val Bid = sumf idAbsU mF;  val SR = sumf rmA mF;  val FL = sumf flA mF;  val mu = cnt flP mF;
    (* floor_sum_kr_parity instance : parity FL = parity(add Bid SR) *)
    val fkI = beta_norm (Drule.infer_instantiate ctxtU
                [(("q",0), ctermU qF),(("p",0), ctermU pF),(("m",0), ctermU mF)] floor_sum_kr_parity_U);
    val fkE = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim fkI hpos) hoddQ) hoddP;
              (* parity FL = parity(add Bid SR) *)
    (* PH instance : parity SR = parity(add Bid mu) *)
    val phI = beta_norm (Drule.infer_instantiate ctxtU
                [(("q",0), ctermU qF),(("p",0), ctermU pF),(("m",0), ctermU mF)] (toU eis_parity_half2));
    val phE = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim
                (Thm.implies_elim phI hpos) hoddP) hPrime) hNq) hOdd;
              (* parity SR = parity(add Bid mu) *)
    (* parity(add Bid SR) = parity(add (parity Bid)(parity SR))  [parity_add] *)
    val pa1 = parityAdd_U_at (Bid, SR);
    (* rewrite parity SR -> parity(add Bid mu) [phE] inside add (parity Bid)(.) *)
    val rwAbs = Abs("z", natT, oeq (parity (add (parity Bid)(parity SR)))
                                   (parity (add (parity Bid)(Bound 0))));
    val pa2 = oeq_rw_U (rwAbs, parity SR, parity (add Bid mu)) phE
                (oeqRefl_U (parity (add (parity Bid)(parity SR))));
              (* = parity(add (parity Bid)(parity(add Bid mu))) *)
    (* = parity(add Bid (add Bid mu))  [parity_add rev] *)
    val pa3 = parityAdd_U_at (Bid, add Bid mu);  (* parity(add Bid (add Bid mu)) = parity(add(parity Bid)(parity(add Bid mu))) *)
    (* add Bid (add Bid mu) = add (add Bid Bid) mu  [assoc^-1] *)
    val a1 = addassoc_U (Bid, Bid, mu);   (* (Bid+Bid)+mu = Bid+(Bid+mu) *)
    val a1s = oeq_sym_U OF [a1];          (* Bid+(Bid+mu) = (Bid+Bid)+mu *)
    val rearrP = let val pAbs = Abs("z", natT, oeq (parity (add Bid (add Bid mu))) (parity (Bound 0)))
                 in oeq_rw_U (pAbs, add Bid (add Bid mu), add (add Bid Bid) mu) a1s
                      (oeqRefl_U (parity (add Bid (add Bid mu)))) end;
                 (* parity(add Bid (add Bid mu)) = parity(add (add Bid Bid) mu) *)
    (* parity(add (add Bid Bid) mu) = parity(add (parity(add Bid Bid))(parity mu)) [parity_add] *)
    val pa4 = parityAdd_U_at (add Bid Bid, mu);
    val pd = parity_double_U_at Bid;   (* parity(add Bid Bid) = 0 *)
    val rwDAbs = Abs("z", natT, oeq (parity (add (parity (add Bid Bid))(parity mu)))
                                    (parity (add (Bound 0)(parity mu))));
    val pa5 = oeq_rw_U (rwDAbs, parity (add Bid Bid), ZeroC) pd
                (oeqRefl_U (parity (add (parity (add Bid Bid))(parity mu))));
              (* = parity(add 0 (parity mu)) *)
    (* parity(add 0 (parity mu)) = parity(parity mu) = parity mu  [add_0_left + idem] *)
    val add0l = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU (parity mu))] (varifyU add_0));
                (* add 0 (parity mu) = parity mu *)
    val a0Abs = Abs("z", natT, oeq (parity (add ZeroC (parity mu))) (parity (Bound 0)));
    val a0p = oeq_rw_U (a0Abs, add ZeroC (parity mu), parity mu) add0l
                (oeqRefl_U (parity (add ZeroC (parity mu))));
              (* parity(add 0 (parity mu)) = parity(parity mu) *)
    val idem = parity_idem_U_at mu;   (* parity(parity mu) = parity mu *)
    (* full : parity FL = parity(add Bid SR) [fkE] = ... = parity mu *)
    val flToMu =
      oeq_trans_U OF [fkE,
        oeq_trans_U OF [pa1,
          oeq_trans_U OF [pa2,
            oeq_trans_U OF [oeq_sym_U OF [pa3],
              oeq_trans_U OF [rearrP,
                oeq_trans_U OF [pa4,
                  oeq_trans_U OF [pa5,
                    oeq_trans_U OF [a0p, idem]]]]]]]];
      (* parity FL = parity mu *)
    val res = oeq_sym_U OF [flToMu];   (* parity mu = parity (sumf floor m) *)
    val d6 = Thm.implies_intr (ctermU (jT (oeq (sub pF oneC) (add mF mF)))) res;
    val d5 = Thm.implies_intr (ctermU (jT (neg (dvd pF qF)))) d6;
    val d4 = Thm.implies_intr (ctermU (jT (prime2 pF))) d5;
    val d3 = Thm.implies_intr (ctermU (jT (oeq (parity pF) oneC))) d4;
    val d2 = Thm.implies_intr (ctermU (jT (oeq (parity qF) oneC))) d3;
    val d1 = Thm.implies_intr (ctermU (jT (lt ZeroC pF))) d2;
  in varify d1 end;
val qV_ep = Var(("q",0),natT); val pV_ep = Var(("p",0),natT); val mV_ep = Var(("m",0),natT);
val flAv_ep = floorAbsU qV_ep pV_ep;
val flPv_ep = flipAbsU qV_ep pV_ep;
val i_eisenstein_parity =
  Logic.mk_implies (jT (lt ZeroC pV_ep),
    Logic.mk_implies (jT (oeq (parity qV_ep) oneC),
      Logic.mk_implies (jT (oeq (parity pV_ep) oneC),
        Logic.mk_implies (jT (prime2 pV_ep),
          Logic.mk_implies (jT (neg (dvd pV_ep qV_ep)),
            Logic.mk_implies (jT (oeq (sub pV_ep oneC) (add mV_ep mV_ep)),
              jT (oeq (parity (cnt flPv_ep mV_ep))
                      (parity (sumf flAv_ep mV_ep)))))))));
val r_eisenstein_parity = checkU ("eisenstein_parity", eisenstein_parity, i_eisenstein_parity);
val probe_ep_needs_oddq =
  let val bogus = Logic.mk_implies (jT (lt ZeroC pV_ep),
        Logic.mk_implies (jT (oeq (parity pV_ep) oneC),
          Logic.mk_implies (jT (prime2 pV_ep),
            Logic.mk_implies (jT (neg (dvd pV_ep qV_ep)),
              Logic.mk_implies (jT (oeq (sub pV_ep oneC) (add mV_ep mV_ep)),
                jT (oeq (parity (cnt flPv_ep mV_ep))
                        (parity (sumf flAv_ep mV_ep))))))))
  in not ((Thm.prop_of eisenstein_parity) aconv bogus) end;
val () = if probe_ep_needs_oddq then out "PROBE_OK eisenstein_parity keeps parity q = 1\n"
         else out "PROBE_FAIL eisenstein_parity\n";
val () = if r_eisenstein_parity andalso probe_ep_needs_oddq
         then out "EIS_PARITY_OK\n" else out "EIS_PARITY_FAILED\n";
val () = out "STAGE_EP_END\n";

(* ############################################################################
   ##########  (EL)  EISENSTEIN LEMMA  --  STATUS  ############################
   ----------------------------------------------------------------------------
   The deliverable  legendre(q,p) = (-1)^(sum floor)  follows from
     gauss_lemma  (S in {1,p-1}, cong p (a^m) S)
   THE MOMENT a link  S == (-1)^mu (mod p)  with  mu = cnt flipPred m  is in hand.
   This fleet PROVED the parity bridge  eisenstein_parity : mu == sum floor (mod 2)
   (the arithmetic HEART of the Eisenstein lemma) plus the full list-SUM
   permutation infrastructure (lsumf / lsumf_perm_of_inj / lar_sum_perm).

   BLOCKER for the final EL closure : the banked gauss_lemma delivers the sign S
   ONLY as an EXISTENTIAL element of {1, p-1} (isSign p S), built MULTIPLICATIVELY
   per residue in prod_split_sign (Snew = mult sk St, sk = 1 no-flip / p-1 flip).
   It NEVER materialises the flip COUNT mu = cnt flipPred m, so there is NO banked
   theorem  S == (-1)^mu (mod p) / S == (p-1)^(cnt flipPred m) (mod p)  to rewrite
   the Gauss sign into  (-1)^(sum floor).  Closing EL requires re-running the S2
   induction tracking cnt (a fresh "sign == (p-1)^cnt" lemma) — a separate fleet.
   Hence EL is NOT closed here; eisenstein_parity (mu == sum floor mod 2) is the
   strongest honest deliverable.  NO fabricated eisenstein / legendre axiom.
   ############################################################################ *)
val eisLemmaFull = false;   (* honest : the gauss-sign -> (-1)^(sum floor) closure is NOT done *)
val () = out "EIS_LEMMA_STATUS_NOTE\n";

(* ############################################################################
   SOUNDNESS  +  AXIOM AUDIT  (the F2b delta)
   Every banked F2b lemma is 0-hyp (mod its stated premises) + aconv; the ONLY new
   axioms are the TWO conservative lsumf recursion equations (lsumf_nil/lsumf_cons);
   the ONLY classical axiom is ex_middle; NOTHING fabricated.
   ############################################################################ *)
val () = out "F2B_AUDIT_BEGIN\n";
val allAxU = Theory.all_axioms_of thyU;
val () = out ("f2b_axiom_count=" ^ Int.toString (length allAxU) ^ "\n");
val hasEMu = List.exists (fn (nm,_) => String.isSuffix "ex_middle" nm orelse nm = "ex_middle") allAxU;
val () = out ("f2b_ex_middle_present=" ^ Bool.toString hasEMu ^ "\n");
(* the new lsumf axioms must be present, named exactly *)
val lsumfAx = List.filter (fn nm => String.isSubstring "lsumf" (String.map Char.toLower nm)) (map fst allAxU);
val () = out ("f2b_lsumf_axioms=[" ^ String.concatWith "," lsumfAx ^ "]\n");
(* assert NO fabricated eisenstein/legendre/reciprocity/permutation/mu/cnt-link axiom *)
val badU = List.filter (fn nm => let val l = String.map Char.toLower nm in
              String.isSubstring "eisenstein" l orelse String.isSubstring "legendre" l
              orelse String.isSubstring "reciprocity" l orelse String.isSubstring "perm" l
              orelse String.isSubstring "lar_sum" l orelse String.isSubstring "sum_perm" l
              orelse String.isSubstring "musum" l end)
            (map fst allAxU);
val () = out ("f2b_fabricated_axioms=[" ^ String.concatWith "," badU ^ "]\n");
(* enumerate ALL axiom names whose const is NEW vs the F2 base (should be only the 2 lsumf) *)
val newConstAx = List.filter (fn nm => let val l = String.map Char.toLower nm in
                   String.isSubstring "lsumf" l end) (map fst allAxU);
val () = out ("f2b_new_const_axioms=[" ^ String.concatWith "," newConstAx ^ "]\n");
val () = out "F2B_AUDIT_END\n";

(* ---- master gate ---- *)
val f2bAllOK = r_LS andalso r_lsumf_perm andalso probe_sperm_needs_inj andalso sperm_clean
               andalso r_lar_sum_perm andalso probe_lar_sum_perm_needs_ndvd
               andalso r_rmod_lar_cnt andalso r_sumf_via_lsumf andalso r_lmap_id
               andalso r_sum_lar_eq_sum_id andalso r_eis_parity_half2 andalso probe_ph_needs_ndvd
               andalso r_eisenstein_parity andalso probe_ep_needs_oddq
               andalso hasEMu andalso (badU = [])
               andalso (length lsumfAx = 2);
val () = if f2bAllOK then out "QR_F2B_ALL_OK\n" else out "QR_F2B_PARTIAL\n";
val () = out ("F2B_SUMMARY lsumfBuilt=true larSumPermProved=" ^ Bool.toString r_lar_sum_perm
              ^ " eisensteinParityProved=" ^ Bool.toString r_eisenstein_parity
              ^ " eisensteinLemmaProved=" ^ Bool.toString eisLemmaFull ^ "\n");
val () = out "EISENSTEIN_CLOSE_END\n";
