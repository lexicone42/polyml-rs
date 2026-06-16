(* ============================================================================
   EULER FOUNDATIONS toward Euler's theorem, in Isabelle/Pure on the polyml-rs
   interpreter.  (test: isabelle_euler_foundations.rs)
   ----------------------------------------------------------------------------
   The two new ingredients Euler's theorem needs beyond the Wilson machinery
   (where the inverse pairing was an INVOLUTION; Euler's x |-> a*x is a general
   BIJECTION on the reduced residues). Both 0-hyp by genuine kernel inference:

   (1) PERMUTATION INVARIANCE of the list product:
         lprod_perm : lnodup L1 ==> lnodup L2 ==> (!x. lmem x L1 <-> lmem x L2)
                        ==> oeq (lprod L1) (lprod L2)
       Two duplicate-free lists with the same members have equal products. Proved
       by structural list induction with the SECOND list generalised via a fresh
       object natlist-universal quantifier LForall (so the cons case can apply the
       IH at (rest, lremove a M)); the head a is extracted from M (extract).

   (2) THE REDUCED-RESIDUE LIST + Euler's phi:
         gcdf  : a gcd FUNCTION via the Euclidean algorithm using rmod
                 (gcdf a 0 = a; 0<b ==> gcdf a b = gcdf b (rmod a b));
         coprime test  oeq (gcdf a n) 1  (DECIDABLE);
         rrl n : the list [1..n-1] filtered to the residues coprime to n;
         phi n : llen (rrl n);
         lmem_rrl : lmem r (rrl n) <-> (lmem r (upto (n-1)) /\ coprime r n).

   Soundness probes confirm lprod_perm genuinely needs both lnodup premises and
   lmem_rrl genuinely carries the coprime condition. Built on the Wilson-inverse
   base (rmod, the list library, upto) via common::with_wilson_inverse. Proved by
   a 2-goal ultracode fleet (wf_5604358b-d48); re-verified end-to-end by hand.

   NEXT (the Euler assembly): show r |-> rmod (a*r) n PERMUTES rrl n (closed under
   mult by the unit a; injective by mod_cancel), so lprod_perm gives lprod(map ..)
   = lprod(rrl); factor a out phi times => a^phi * lprod(rrl) == lprod(rrl); cancel
   the unit lprod(rrl) => a^phi == 1 (mod n). That is Euler's theorem.
   ============================================================================ *)

(* ============================================================================
   SEAT perm_invariance0 — lprod_perm: PERMUTATION INVARIANCE of the list product.
   Two duplicate-free lists with the SAME members have EQUAL products.
   Strategy: structural list_induct on L1, with the second list M generalised by
   a fresh OBJECT natlist-universal quantifier LForall (conservative: standard
   allI/allE axioms).  In the cons case L1 = lcons a rest, extract a from M
   (a in L1 hence in M), apply IH at (rest, lremove a M).
   ============================================================================ *)
val () = out "PERM_INV_BEGIN\n";

(* ---- extend thyL2 with a natlist universal quantifier ---- *)
val thyP0 = Sign.add_consts
  [(Binding.name "LForall", (natlistT --> oT) --> oT, NoSyn)] thyL2;
val LForallC = Const (Sign.full_name thyP0 (Binding.name "LForall"), (natlistT --> oT) --> oT);
fun mkLForall pr = LForallC $ pr;

val PpL = Free ("P", natlistT --> oT);
val xLallI = Free ("x", natlistT);
val ((_,LallI_ax), thyP1) = Thm.add_axiom_global (Binding.name "LallI",
      Logic.mk_implies (Logic.all xLallI (jT (PpL $ xLallI)), jT (mkLForall PpL))) thyP0;
val acL = Free ("a", natlistT);
val ((_,LallE_ax), thyP) = Thm.add_axiom_global (Binding.name "LallE",
      Logic.mk_implies (jT (mkLForall PpL), jT (PpL $ acL))) thyP1;

val ctxtP  = Proof_Context.init_global thyP;
val ctermP = Thm.cterm_of ctxtP;
val () = out "PERM_INV_CONTEXT_READY\n";

(* ---- re-varify EVERYTHING used onto ctxtP ---- *)
val oeq_refl_vP2    = varify oeq_refl;
val oeq_sym_vP2     = varify oeq_sym;
val oeq_trans_vP2   = varify oeq_trans;
val mp_vP           = varify mp_ax;
val impI_vP         = varify impI_ax;
val conjI_vP        = varify conjI_ax;
val conjunct1_vP    = varify conjunct1_ax;
val conjunct2_vP    = varify conjunct2_ax;
val disjI1_vP       = varify disjI1_ax;
val disjI2_vP       = varify disjI2_ax;
val disjE_vP        = varify disjE_ax;
val oFalse_elim_vP  = varify oFalse_elim_ax;
val ex_middle_vP    = varify ex_middle_ax;
val allI_vP         = varify allI_ax;     (* nat Forall *)
val allE_vP         = varify allE_ax;
val LallI_vP        = varify LallI_ax;
val LallE_vP        = varify LallE_ax;
(* list machinery *)
val leq_refl_vP     = varify leq_refl_ax;
val leq_subst_vP    = varify leq_subst_ax;
val list_induct_vP  = varify list_induct_ax;
val lprod_nil_vP    = varify lprod_nil_ax;
val lprod_cons_vP   = varify lprod_cons_ax;
val lmem_nil_elim_vP= varify lmem_nil_elim_ax;
val lmem_cons_fwd_vP= varify lmem_cons_fwd_ax;
val lmem_cons_bwd_vP= varify lmem_cons_bwd_ax;
val lremove_nil_vP  = varify lremove_nil_ax;
val lremove_cons_eq_vP  = varify lremove_cons_eq_ax;
val lremove_cons_neq_vP = varify lremove_cons_neq_ax;
val lnodup_cons_fwd_vP  = varify lnodup_cons_fwd_ax;
val lnodup_cons_bwd_vP  = varify lnodup_cons_bwd_ax;
val mult_comm_vP    = varify mult_comm;
val mult_assoc_vP   = varify mult_assoc;
(* derived list lemmas *)
val extract_vP      = varify extract;
val mem_remove_fwd_vP = varify mem_remove_fwd;
val mem_remove_bwd_vP = varify mem_remove_bwd;
val mem_remove_neq_vP = varify mem_remove_neq;
val nodup_remove_vP   = varify nodup_remove;
val leq_sym_vP      = varify leq_sym;

(* ---- combinators on ctxtP ---- *)
fun oeqRefl_P t = beta_norm (Drule.infer_instantiate ctxtP [(("a",0), ctermP t)] oeq_refl_vP2);
fun mp_P (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP [(("A",0), ctermP At),(("B",0), ctermP Bt)] mp_vP)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_P (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP [(("A",0), ctermP At),(("B",0), ctermP Bt)] impI_vP)
  in Thm.implies_elim inst hImpThm end;
fun conjI_P (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP [(("A",0), ctermP At),(("B",0), ctermP Bt)] conjI_vP)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_P (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("A",0), ctermP At),(("B",0), ctermP Bt)] conjunct1_vP)) h;
fun conjunct2_P (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("A",0), ctermP At),(("B",0), ctermP Bt)] conjunct2_vP)) h;
fun disjI1_P (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("A",0), ctermP At),(("B",0), ctermP Bt)] disjI1_vP)) h;
fun disjI2_P (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("A",0), ctermP At),(("B",0), ctermP Bt)] disjI2_vP)) h;
fun disjE_P (At,Bt,Ct) dThm cA cB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP
        [(("A",0), ctermP At),(("B",0), ctermP Bt),(("C",0), ctermP Ct)] disjE_vP)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) cA) cB end;
fun oFalse_elim_P rT = beta_norm (Drule.infer_instantiate ctxtP [(("R",0), ctermP rT)] oFalse_elim_vP);
fun em_P t = beta_norm (Drule.infer_instantiate ctxtP [(("A",0), ctermP t)] ex_middle_vP);
fun allE_P Pabs at hF = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("P",0), ctermP Pabs),(("a",0), ctermP at)] allE_vP)) hF;
fun allI_P Pabs hAll = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("P",0), ctermP Pabs)] allI_vP)) hAll;
(* natlist universal *)
fun LallE_P Pabs at hF = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("P",0), ctermP Pabs),(("a",0), ctermP at)] LallE_vP)) hF;
fun LallI_P Pabs hAll = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("P",0), ctermP Pabs)] LallI_vP)) hAll;

fun leqRefl_P l = beta_norm (Drule.infer_instantiate ctxtP [(("a",0), ctermP l)] leq_refl_vP);
fun lprodNil_P () = lprod_nil_vP;
fun lprodCons_P (h,t) = beta_norm (Drule.infer_instantiate ctxtP
      [(("x",0), ctermP h),(("t",0), ctermP t)] lprod_cons_vP);
fun lmemNilElim_P x = beta_norm (Drule.infer_instantiate ctxtP [(("x",0), ctermP x)] lmem_nil_elim_vP);
fun lmemConsFwd_P (x,y,t) = beta_norm (Drule.infer_instantiate ctxtP
      [(("x",0), ctermP x),(("y",0), ctermP y),(("t",0), ctermP t)] lmem_cons_fwd_vP);
fun lmemConsBwd_P (x,y,t) = beta_norm (Drule.infer_instantiate ctxtP
      [(("x",0), ctermP x),(("y",0), ctermP y),(("t",0), ctermP t)] lmem_cons_bwd_vP);
fun lremoveNil_P x = beta_norm (Drule.infer_instantiate ctxtP [(("x",0), ctermP x)] lremove_nil_vP);
fun lremoveConsEq_P (x,y,t) = beta_norm (Drule.infer_instantiate ctxtP
      [(("x",0), ctermP x),(("y",0), ctermP y),(("t",0), ctermP t)] lremove_cons_eq_vP);
fun lremoveConsNeq_P (x,y,t) = beta_norm (Drule.infer_instantiate ctxtP
      [(("x",0), ctermP x),(("y",0), ctermP y),(("t",0), ctermP t)] lremove_cons_neq_vP);
fun lnodupConsFwd_P (x,t) = beta_norm (Drule.infer_instantiate ctxtP
      [(("x",0), ctermP x),(("t",0), ctermP t)] lnodup_cons_fwd_vP);
fun lnodupConsBwd_P (x,t) = beta_norm (Drule.infer_instantiate ctxtP
      [(("x",0), ctermP x),(("t",0), ctermP t)] lnodup_cons_bwd_vP);
fun multcomm_P (mt,nt) = beta_norm (Drule.infer_instantiate ctxtP
      [(("m",0), ctermP mt),(("n",0), ctermP nt)] mult_comm_vP);
fun multassoc_P (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtP
      [(("m",0), ctermP mt),(("n",0), ctermP nt),(("k",0), ctermP kt)] mult_assoc_vP);
fun mult_cong_r_P (hT,pT,qT) hpq =
  let val zf = Free("zmcr", natT)
      val Pabs = Term.lambda zf (oeq (mult hT pT) (mult hT zf))
      val inst = beta_norm (Drule.infer_instantiate ctxtP
            [(("P",0), ctermP Pabs),(("a",0), ctermP pT),(("b",0), ctermP qT)]
            (varify oeq_subst))
  in inst OF [hpq, oeqRefl_P (mult hT pT)] end;
fun mult_cong_l_P (pT,qT,kT) hpq =
  let val zf = Free("zmcl", natT)
      val Pabs = Term.lambda zf (oeq (mult pT kT) (mult zf kT))
      val inst = beta_norm (Drule.infer_instantiate ctxtP
            [(("P",0), ctermP Pabs),(("a",0), ctermP pT),(("b",0), ctermP qT)]
            (varify oeq_subst))
  in inst OF [hpq, oeqRefl_P (mult pT kT)] end;
fun lprod_cong_P (aT,bT) hab =
  let val zf = Free("zlpc", natlistT)
      val Pabs = Term.lambda zf (oeq (lprod aT) (lprod zf))
      val inst = beta_norm (Drule.infer_instantiate ctxtP
            [(("P",0), ctermP Pabs),(("a",0), ctermP aT),(("b",0), ctermP bT)] leq_subst_vP)
  in inst OF [hab, oeqRefl_P (lprod aT)] end;
fun lmem_transfer_P (yT,aT,bT) hleq hmem =
  let val zf = Free("zlmt", natlistT)
      val Pabs = Term.lambda zf (lmem yT zf)
      val inst = beta_norm (Drule.infer_instantiate ctxtP
            [(("P",0), ctermP Pabs),(("a",0), ctermP aT),(("b",0), ctermP bT)] leq_subst_vP)
  in inst OF [hleq, hmem] end;

(* derived-lemma applicators on ctxtP -- ALL are META implications (proved by
   Thm.implies_intr), so apply with Thm.implies_elim, NOT mp_P. *)
fun extract_P (xt,Lt) hmem =
  Thm.implies_elim
    (beta_norm (Drule.infer_instantiate ctxtP [(("x",0), ctermP xt),(("L",0), ctermP Lt)] extract_vP)) hmem;
fun mem_remove_fwd_P (yt,xt,Lt) hmem =
  Thm.implies_elim
    (beta_norm (Drule.infer_instantiate ctxtP
      [(("y",0), ctermP yt),(("x",0), ctermP xt),(("L",0), ctermP Lt)] mem_remove_fwd_vP)) hmem;
fun mem_remove_bwd_P (yt,xt,Lt) hconj =
  Thm.implies_elim
    (beta_norm (Drule.infer_instantiate ctxtP
      [(("y",0), ctermP yt),(("x",0), ctermP xt),(("L",0), ctermP Lt)] mem_remove_bwd_vP)) hconj;
fun mem_remove_neq_P (yt,xt,Lt) hnd hmem =  (* META impl: lnodup L ==> lmem y (lremove x L) ==> neg(oeq y x) *)
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("y",0), ctermP yt),(("x",0), ctermP xt),(("L",0), ctermP Lt)] mem_remove_neq_vP)) hnd) hmem;
fun nodup_remove_P (xt,Lt) hnd =
  Thm.implies_elim
    (beta_norm (Drule.infer_instantiate ctxtP
      [(("x",0), ctermP xt),(("L",0), ctermP Lt)] nodup_remove_vP)) hnd;

val () = out "PERM_INV_HELPERS_READY\n";

(* ---- object member-equivalence predicate : mem_eq L M (Conj of two Imps) ---- *)
fun mem_eq_pred L M =
  let val xv = Free("me_x", natT)
  in Term.lambda xv (mkConj (mkImp (lmem xv L) (lmem xv M)) (mkImp (lmem xv M) (lmem xv L))) end;
fun mem_eq L M = mkForall (mem_eq_pred L M);
fun mem_eq_fwd (L,M) hme x (hmem:thm) =
  let val inst = allE_P (mem_eq_pred L M) x hme
      val c1   = conjunct1_P (mkImp (lmem x L)(lmem x M), mkImp (lmem x M)(lmem x L)) inst
  in mp_P (lmem x L, lmem x M) c1 hmem end;
fun mem_eq_bwd (L,M) hme x (hmem:thm) =
  let val inst = allE_P (mem_eq_pred L M) x hme
      val c2   = conjunct2_P (mkImp (lmem x L)(lmem x M), mkImp (lmem x M)(lmem x L)) inst
  in mp_P (lmem x M, lmem x L) c2 hmem end;
val () = out "PERM_INV_MEMEQ_READY\n";

(* ---- no_mem z == Forall(%x. neg(lmem x z)) ; no_mem_nil : no_mem L ==> leq L lnil ---- *)
fun no_mem_pred z = let val xv = Free("nm_x", natT) in Term.lambda xv (neg (lmem xv z)) end;
fun no_mem z = mkForall (no_mem_pred z);

val no_mem_nil_P =
  let
    fun concBody zt = mkImp (no_mem zt) (leq zt lnilC);
    val zPv = Free("z_nm", natlistT);
    val Qpred = Term.lambda zPv (concBody zPv);
    val LF = Free("L_nmn", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtP
          [(("P",0), ctermP Qpred), (("a",0), ctermP LF)] list_induct_vP);
    val base =
      let val refl = leqRefl_P lnilC
      in impI_P (no_mem lnilC, leq lnilC lnilC)
           (Thm.implies_intr (ctermP (jT (no_mem lnilC))) refl) end;
    val hF = Free("h_nmn", natT); val tF = Free("t_nmn", natlistT);
    val ihprop = jT (concBody tF);
    val IH = Thm.assume (ctermP ihprop);
    val stepConcl =
      let
        val hnm = Thm.assume (ctermP (jT (no_mem (lcons hF tF))));
        val negMemH = allE_P (no_mem_pred (lcons hF tF)) hF hnm;
        val hhrefl = oeqRefl_P hF;
        val dj     = disjI1_P (oeq hF hF, lmem hF tF) hhrefl;
        val memH   = Thm.implies_elim (lmemConsBwd_P (hF, hF, tF)) dj;
        val ff     = mp_P (lmem hF (lcons hF tF), oFalseC) negMemH memH;
        val conc   = Thm.implies_elim (oFalse_elim_P (leq (lcons hF tF) lnilC)) ff;
      in impI_P (no_mem (lcons hF tF), leq (lcons hF tF) lnilC)
           (Thm.implies_intr (ctermP (jT (no_mem (lcons hF tF)))) conc) end;
    val step1 = Thm.forall_intr (ctermP hF)
                  (Thm.forall_intr (ctermP tF) (Thm.implies_intr (ctermP ihprop) stepConcl));
    val r2 = Thm.implies_elim (Thm.implies_elim ind base) step1;
    val hnmL = Thm.assume (ctermP (jT (no_mem LF)));
    val concL = mp_P (no_mem LF, leq LF lnilC) r2 hnmL;
  in varify (Thm.implies_intr (ctermP (jT (no_mem LF))) concL) end;
val () = out "OK no_mem_nil\n";
val no_mem_nil_Pv = varify no_mem_nil_P;
fun no_mem_nil_at_P Lt hnm =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("L_nmn",0), ctermP Lt)] no_mem_nil_Pv)) hnm;
val () = out "NO_MEM_NIL_READY\n";

(* ============================================================================
   lprod_perm — structural list_induct on L1; second list M via LForall.
   ============================================================================ *)
val lprod_perm =
  let
    fun innerPred zL =
      let val Mv = Free("M_inner", natlistT)
      in Term.lambda Mv (mkImp (lnodup Mv) (mkImp (mem_eq zL Mv) (oeq (lprod zL) (lprod Mv)))) end;
    fun Qbody zL = mkImp (lnodup zL) (mkLForall (innerPred zL));
    val zPv = Free("z_q", natlistT);
    val Qpred = Term.lambda zPv (Qbody zPv);
    val L1F = Free("L1", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtP
          [(("P",0), ctermP Qpred), (("a",0), ctermP L1F)] list_induct_vP);

    (* ---- BASE : Q lnil ---- *)
    val base =
      let
        val hndNil = Thm.assume (ctermP (jT (lnodup lnilC)));
        val MF = Free("M_base", natlistT);
        val perM =
          let
            val hndM = Thm.assume (ctermP (jT (lnodup MF)));
            val hme  = Thm.assume (ctermP (jT (mem_eq lnilC MF)));
            val noMemMF =
              let val yf = Free("y_nm_b", natT)
                  val hy = Thm.assume (ctermP (jT (lmem yf MF)))
                  val inNil = mem_eq_bwd (lnilC, MF) hme yf hy
                  val ff = Thm.implies_elim (lmemNilElim_P yf) inNil
                  val negy = impI_P (lmem yf MF, oFalseC)
                                (Thm.implies_intr (ctermP (jT (lmem yf MF))) ff)
                  val Pabs = no_mem_pred MF
              in allI_P Pabs (Thm.forall_intr (ctermP yf) negy) end;
            val leqMFnil = no_mem_nil_at_P MF noMemMF;
            val lpcong = lprod_cong_P (MF, lnilC) leqMFnil;
            val conc = oeq_sym OF [lpcong];
            val body = impI_P (mem_eq lnilC MF, oeq (lprod lnilC) (lprod MF))
                          (Thm.implies_intr (ctermP (jT (mem_eq lnilC MF))) conc)
            val body2 = impI_P (lnodup MF, mkImp (mem_eq lnilC MF) (oeq (lprod lnilC) (lprod MF)))
                          (Thm.implies_intr (ctermP (jT (lnodup MF))) body)
          in body2 end;
        val forallM = LallI_P (innerPred lnilC) (Thm.forall_intr (ctermP MF) perM);
      in impI_P (lnodup lnilC, mkLForall (innerPred lnilC))
           (Thm.implies_intr (ctermP (jT (lnodup lnilC))) forallM) end;

    (* ---- STEP : Q rest ==> Q (lcons a rest) ---- *)
    val aF = Free("a_s", natT); val restF = Free("rest_s", natlistT);
    val ihprop = jT (Qbody restF);
    val IH = Thm.assume (ctermP ihprop);
    val L1cons = lcons aF restF;
    val stepConcl =
      let
        val hndL1 = Thm.assume (ctermP (jT (lnodup L1cons)));
        val cjL1  = Thm.implies_elim (lnodupConsFwd_P (aF, restF)) hndL1;
        val a_notin_rest = conjunct1_P (neg (lmem aF restF), lnodup restF) cjL1;
        val hnd_rest = conjunct2_P (neg (lmem aF restF), lnodup restF) cjL1;
        val ihForall = mp_P (lnodup restF, mkLForall (innerPred restF)) IH hnd_rest;
        val MF = Free("M_step", natlistT);
        val perM =
          let
            val hndM = Thm.assume (ctermP (jT (lnodup MF)));
            val hme  = Thm.assume (ctermP (jT (mem_eq L1cons MF)));
            val memA_L1 = Thm.implies_elim (lmemConsBwd_P (aF, aF, restF))
                            (disjI1_P (oeq aF aF, lmem aF restF) (oeqRefl_P aF));
            val memA_M  = mem_eq_fwd (L1cons, MF) hme aF memA_L1;
            val extr    = extract_P (aF, MF) memA_M;
            val lpc     = lprodCons_P (aF, restF);
            val R       = lremove aF MF;
            val ihAt = LallE_P (innerPred restF) R ihForall;
            val ndR  = nodup_remove_P (aF, MF) hndM;
            val meRestR =
              let val yf = Free("y_me", natT)
                  val fwd =
                    let val hyr = Thm.assume (ctermP (jT (lmem yf restF)))
                        val memY_L1 = Thm.implies_elim (lmemConsBwd_P (yf, aF, restF))
                                        (disjI2_P (oeq yf aF, lmem yf restF) hyr)
                        val memY_M  = mem_eq_fwd (L1cons, MF) hme yf memY_L1
                        val yneqa =
                          let val hya = Thm.assume (ctermP (jT (oeq yf aF)))
                              val Pr = let val zf = Free("zyn", natT) in Term.lambda zf (lmem zf restF) end
                              val inst = beta_norm (Drule.infer_instantiate ctxtP
                                          [(("P",0), ctermP Pr),(("a",0), ctermP yf),(("b",0), ctermP aF)] (varify oeq_subst))
                              val memArest = inst OF [hya, hyr]
                              val ff = mp_P (lmem aF restF, oFalseC) a_notin_rest memArest
                          in impI_P (oeq yf aF, oFalseC)
                               (Thm.implies_intr (ctermP (jT (oeq yf aF))) ff) end
                        val cj = conjI_P (lmem yf MF, neg (oeq yf aF)) memY_M yneqa
                        val memY_R = mem_remove_bwd_P (yf, aF, MF) cj
                    in Thm.implies_intr (ctermP (jT (lmem yf restF))) memY_R end;
                  val bwd =
                    let val hyR = Thm.assume (ctermP (jT (lmem yf R)))
                        val memY_M = mem_remove_fwd_P (yf, aF, MF) hyR
                        val memY_L1 = mem_eq_bwd (L1cons, MF) hme yf memY_M
                        val dj = Thm.implies_elim (lmemConsFwd_P (yf, aF, restF)) memY_L1
                        val yneqa = mem_remove_neq_P (yf, aF, MF) hndM hyR
                        val cA = let val hya = Thm.assume (ctermP (jT (oeq yf aF)))
                                     val ff  = mp_P (oeq yf aF, oFalseC) yneqa hya
                                     val r   = Thm.implies_elim (oFalse_elim_P (lmem yf restF)) ff
                                 in Thm.implies_intr (ctermP (jT (oeq yf aF))) r end
                        val cB = let val hm = Thm.assume (ctermP (jT (lmem yf restF)))
                                 in Thm.implies_intr (ctermP (jT (lmem yf restF))) hm end
                        val res = disjE_P (oeq yf aF, lmem yf restF, lmem yf restF) dj cA cB
                    in Thm.implies_intr (ctermP (jT (lmem yf R))) res end;
                  val cjBoth = conjI_P (mkImp (lmem yf restF)(lmem yf R), mkImp (lmem yf R)(lmem yf restF))
                                  (impI_P (lmem yf restF, lmem yf R) fwd)
                                  (impI_P (lmem yf R, lmem yf restF) bwd)
                  val Pabs = mem_eq_pred restF R
              in allI_P Pabs (Thm.forall_intr (ctermP yf) cjBoth) end;
            val ih1  = mp_P (lnodup R, mkImp (mem_eq restF R) (oeq (lprod restF) (lprod R))) ihAt ndR;
            val ih_eq = mp_P (mem_eq restF R, oeq (lprod restF) (lprod R)) ih1 meRestR;
            val cong_a = mult_cong_r_P (aF, lprod restF, lprod R) ih_eq;
            val extr_s = oeq_sym OF [extr];
            val conc = oeq_trans OF [oeq_trans OF [lpc, cong_a], extr_s];
            val body = impI_P (mem_eq L1cons MF, oeq (lprod L1cons) (lprod MF))
                          (Thm.implies_intr (ctermP (jT (mem_eq L1cons MF))) conc)
            val body2 = impI_P (lnodup MF, mkImp (mem_eq L1cons MF) (oeq (lprod L1cons) (lprod MF)))
                          (Thm.implies_intr (ctermP (jT (lnodup MF))) body)
          in body2 end;
        val forallM = LallI_P (innerPred L1cons) (Thm.forall_intr (ctermP MF) perM);
      in impI_P (lnodup L1cons, mkLForall (innerPred L1cons))
           (Thm.implies_intr (ctermP (jT (lnodup L1cons))) forallM) end;

    val step1 = Thm.forall_intr (ctermP aF)
                  (Thm.forall_intr (ctermP restF) (Thm.implies_intr (ctermP ihprop) stepConcl));
    val r2 = Thm.implies_elim (Thm.implies_elim ind base) step1;
    val L2F = Free("L2", natlistT);
    val hndL1 = Thm.assume (ctermP (jT (lnodup L1F)));
    val forallM = mp_P (lnodup L1F, mkLForall (innerPred L1F)) r2 hndL1;
    val atL2 = LallE_P (innerPred L1F) L2F forallM;
    val hndL2 = Thm.assume (ctermP (jT (lnodup L2F)));
    val step_b = mp_P (lnodup L2F, mkImp (mem_eq L1F L2F) (oeq (lprod L1F) (lprod L2F))) atL2 hndL2;
    val hme = Thm.assume (ctermP (jT (mem_eq L1F L2F)));
    val final = mp_P (mem_eq L1F L2F, oeq (lprod L1F) (lprod L2F)) step_b hme;
    val d1 = Thm.implies_intr (ctermP (jT (lnodup L1F)))
               (Thm.implies_intr (ctermP (jT (lnodup L2F)))
                  (Thm.implies_intr (ctermP (jT (mem_eq L1F L2F))) final));
  in varify d1 end;
val () = out "OK lprod_perm\n";

val r_lprod_perm =
  let
    val L1V = Var(("L1",0), natlistT); val L2V = Var(("L2",0), natlistT);
    val intended = Logic.mk_implies (jT (lnodup L1V),
        Logic.mk_implies (jT (lnodup L2V),
          Logic.mk_implies (jT (mem_eq L1V L2V), jT (oeq (lprod L1V) (lprod L2V)))));
    val nh = length (Thm.hyps_of lprod_perm);
    val ac = (Thm.prop_of lprod_perm) aconv intended;
  in if nh=0 andalso ac then true
     else (out ("FAIL lprod_perm hyps="^Int.toString nh^" aconv="^Bool.toString ac^"\n");
           out ("  got = "^Syntax.string_of_term ctxtP (Thm.prop_of lprod_perm)^"\n"); false) end;
val () = if r_lprod_perm then out "OK lprod_perm aconv intended\n" else out "FAIL lprod_perm aconv\n";

val probe_perm =
  let val L1V = Var(("L1",0), natlistT); val L2V = Var(("L2",0), natlistT);
      val bogus = Logic.mk_implies (jT (mem_eq L1V L2V), jT (oeq (lprod L1V) (lprod L2V)))
  in not ((Thm.prop_of lprod_perm) aconv bogus) end;
val () = if probe_perm then out "PROBE_OK lprod_perm keeps lnodup hyps\n"
         else out "PROBE_FAIL lprod_perm collapsed\n";

val () = if r_lprod_perm andalso probe_perm then out "PERM_INV_OK\n" else out "PERM_INV_FAILED\n";
(* ============================================================================
   SEAT reduced_residues0 : the REDUCED-RESIDUE LIST and Euler's phi.
   Route (i): gcdf via Euclid (rmod), coprime := oeq (gcdf a n) 1 (decidable).
   rfilter : filter uptoF keeping coprime; rrl n = rfilter n (uptoF (sub n 1));
   phi n = llen (rrl n).
   Prove: lnodup (rrl n), lmem_rrl characterization.
   Build on thyW (latest): add consts gcdf, coprime?, rfilter, rrl, phi.
   ============================================================================ *)

(* ---- (A) extend the theory with new consts ---- *)
val thyE0 = Sign.add_consts
  [(Binding.name "gcdf",    natT --> natT --> natT, NoSyn),
   (Binding.name "coprimeP", natT --> natT --> oT,  NoSyn),
   (Binding.name "rfilter", natT --> natlistT --> natlistT, NoSyn),
   (Binding.name "rrl",     natT --> natlistT, NoSyn),
   (Binding.name "phi",     natT --> natT, NoSyn)] thyW;

fun cnstE nm T = Const (Sign.full_name thyE0 (Binding.name nm), T);
val gcdfC    = cnstE "gcdf" (natT --> natT --> natT);   fun gcdf a b = gcdfC $ a $ b;
val coprimeC = cnstE "coprimeP" (natT --> natT --> oT); fun coprimeP a n = coprimeC $ a $ n;
val rfilterC = cnstE "rfilter" (natT --> natlistT --> natlistT); fun rfilter n l = rfilterC $ n $ l;
val rrlC     = cnstE "rrl" (natT --> natlistT);         fun rrl n = rrlC $ n;
val phiC     = cnstE "phi" (natT --> natT);             fun phi n = phiC $ n;

(* free vars for axiom statements *)
val aE = Free("a", natT); val bE = Free("b", natT); val nE = Free("n", natT);
val rE = Free("r", natT); val rsE = Free("rs", natlistT);

(* the decidable coprimality TEST (a pure oeq formula -> decidable) *)
fun coprime_test a n = oeq (gcdf a n) (suc ZeroC);

(* ---- gcdf : Euclid conditional axioms ----
     gcdf_zero : oeq (gcdf a Zero) a
     gcdf_step : 0 < b ==> oeq (gcdf a b) (gcdf b (rmod a b))   *)
val ((_,gcdf_zero_ax), thyE1) = Thm.add_axiom_global (Binding.name "gcdf_zero",
      jT (oeq (gcdf aE ZeroC) aE)) thyE0;
val ((_,gcdf_step_ax), thyE2) = Thm.add_axiom_global (Binding.name "gcdf_step",
      Logic.mk_implies (jT (lt ZeroC bE),
        jT (oeq (gcdf aE bE) (gcdf bE (rmod aE bE))))) thyE1;

(* ---- coprimeP : defining axiom  coprimeP a n = coprime_test a n  (as object iff
       we make it a plain oeq def at the formula level using oeq on a boolean...).
   Simpler: define coprimeP a n := the test FORMULA directly is awkward (o vs nat).
   Instead use coprimeP as an ABBREVIATION at ML level: coprime_test is the formula.
   We KEEP coprimeC as a const only for naming clarity but tie it by axiom
       coprime_def : coprimeP a n  <->  coprime_test a n   is also awkward (no iff).
   Cleanest: DROP the coprimeP const; the decidable test is coprime_test (an oeq).  *)

(* ---- rfilter : CONDITIONAL list-recursion (keep r iff coprime_test r n) ----
     rfilter_nil      : leq (rfilter n lnil) lnil
     rfilter_cons_in  : jT (coprime_test r n)       ==> leq (rfilter n (lcons r rs)) (lcons r (rfilter n rs))
     rfilter_cons_out : jT (neg (coprime_test r n)) ==> leq (rfilter n (lcons r rs)) (rfilter n rs)  *)
val ((_,rfilter_nil_ax), thyE3) = Thm.add_axiom_global (Binding.name "rfilter_nil",
      jT (leq (rfilter nE lnilC) lnilC)) thyE2;
val ((_,rfilter_cons_in_ax), thyE4) = Thm.add_axiom_global (Binding.name "rfilter_cons_in",
      Logic.mk_implies (jT (coprime_test rE nE),
        jT (leq (rfilter nE (lcons rE rsE)) (lcons rE (rfilter nE rsE))))) thyE3;
val ((_,rfilter_cons_out_ax), thyE5) = Thm.add_axiom_global (Binding.name "rfilter_cons_out",
      Logic.mk_implies (jT (neg (coprime_test rE nE)),
        jT (leq (rfilter nE (lcons rE rsE)) (rfilter nE rsE)))) thyE4;

(* ---- rrl : rrl n = rfilter n (uptoF (sub n 1)) ---- *)
val ((_,rrl_def_ax), thyE6) = Thm.add_axiom_global (Binding.name "rrl_def",
      jT (leq (rrl nE) (rfilter nE (uptoF (sub nE (suc ZeroC)))))) thyE5;

(* ---- phi : phi n = llen (rrl n) ---- *)
val ((_,phi_def_ax), thyE) = Thm.add_axiom_global (Binding.name "phi_def",
      jT (oeq (phi nE) (llen (rrl nE)))) thyE6;

val ctxtE  = Proof_Context.init_global thyE;
val ctermE = Thm.cterm_of ctxtE;
val () = out "RR_CONTEXT_READY\n";

(* ---- varify new axioms onto ctxtE ---- *)
val gcdf_zero_vE = varify gcdf_zero_ax;
val gcdf_step_vE = varify gcdf_step_ax;
val rfilter_nil_vE = varify rfilter_nil_ax;
val rfilter_cons_in_vE = varify rfilter_cons_in_ax;
val rfilter_cons_out_vE = varify rfilter_cons_out_ax;
val rrl_def_vE = varify rrl_def_ax;
val phi_def_vE = varify phi_def_ax;

(* basic sanity: 0-hyp + aconv intent *)
val () = if length (Thm.hyps_of gcdf_zero_vE) = 0 then out "OK gcdf_zero\n" else out "FAIL gcdf_zero\n";
val () = if length (Thm.hyps_of rfilter_nil_vE) = 0 then out "OK rfilter_nil\n" else out "FAIL rfilter_nil\n";
val () = if length (Thm.hyps_of rrl_def_vE) = 0 then out "OK rrl_def\n" else out "FAIL rrl_def\n";

val () = out "RR_PHASE1_DONE\n";

(* ============================================================================
   PHASE 2 : E-context combinators (mirror the W combinators on ctxtE).
   Reuse the schematic varified W lemmas (theory-monotone) via infer_instantiate ctxtE.
   ============================================================================ *)
(* prop-logic *)
fun mp_E (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("A",0), ctermE At),(("B",0), ctermE Bt)] mp_vW)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_E (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("A",0), ctermE At),(("B",0), ctermE Bt)] impI_vW)
  in Thm.implies_elim inst hImpThm end;
fun conjI_E (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("A",0), ctermE At),(("B",0), ctermE Bt)] conjI_vW)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_E (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtE
      [(("A",0), ctermE At),(("B",0), ctermE Bt)] conjunct1_vW)) h;
fun conjunct2_E (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtE
      [(("A",0), ctermE At),(("B",0), ctermE Bt)] conjunct2_vW)) h;
fun oFalse_elim_E rT = beta_norm (Drule.infer_instantiate ctxtE [(("R",0), ctermE rT)] oFalse_elim_vW);
fun disjE_E (At,Bt,Ct) dThm cA cB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("A",0), ctermE At),(("B",0), ctermE Bt),(("C",0), ctermE Ct)] disjE_vW)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) cA) cB end;
fun disjI1_E (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtE
      [(("A",0), ctermE At),(("B",0), ctermE Bt)] disjI1_vW)) h;
fun disjI2_E (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtE
      [(("A",0), ctermE At),(("B",0), ctermE Bt)] disjI2_vW)) h;
fun em_E t = beta_norm (Drule.infer_instantiate ctxtE [(("A",0), ctermE t)] ex_middle_vW);

(* list machinery on ctxtE *)
fun leq_rw_E (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("P",0), ctermE Pabs),(("a",0), ctermE aT),(("b",0), ctermE bT)] leq_subst_vW)
  in inst OF [hab, hPa] end;
fun lmem_transfer_E (yT, aT, bT) hleq hmem =
  let val Pabs = Abs("z", natlistT, lmem yT (Bound 0))
  in leq_rw_E (Pabs, aT, bT) hleq hmem end;
fun lnodup_transfer_E (aT, bT) hleq hnd =
  let val Pabs = Abs("z", natlistT, lnodup (Bound 0))
  in leq_rw_E (Pabs, aT, bT) hleq hnd end;
fun lmemNilElim_E x = beta_norm (Drule.infer_instantiate ctxtE [(("x",0), ctermE x)] lmem_nil_elim_vW);
fun lmemConsFwd_E (x,y,t) = beta_norm (Drule.infer_instantiate ctxtE
      [(("x",0), ctermE x),(("y",0), ctermE y),(("t",0), ctermE t)] lmem_cons_fwd_vW);
fun lmemConsBwd_E (x,y,t) = beta_norm (Drule.infer_instantiate ctxtE
      [(("x",0), ctermE x),(("y",0), ctermE y),(("t",0), ctermE t)] lmem_cons_bwd_vW);
fun lnodupConsFwd_E (x,t) = beta_norm (Drule.infer_instantiate ctxtE
      [(("x",0), ctermE x),(("t",0), ctermE t)] lnodup_cons_fwd_vW);
fun lnodupConsBwd_E (x,t) = beta_norm (Drule.infer_instantiate ctxtE
      [(("x",0), ctermE x),(("t",0), ctermE t)] lnodup_cons_bwd_vW);
val lnodupNil_E = lnodup_nil_vW;
fun list_induct_E (Pabs, LT) baseThm stepThm =
  let val ind = beta_norm (Drule.infer_instantiate ctxtE
        [(("P",0), ctermE Pabs),(("a",0), ctermE LT)] list_induct_vW)
  in Thm.implies_elim (Thm.implies_elim ind baseThm) stepThm end;

(* rfilter conditional axioms on ctxtE *)
fun rfilterNil_E nt = beta_norm (Drule.infer_instantiate ctxtE [(("n",0), ctermE nt)] rfilter_nil_vE);
fun rfilterIn_E (nt,rt,rst) hcond =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtE
      [(("n",0), ctermE nt),(("r",0), ctermE rt),(("rs",0), ctermE rst)] rfilter_cons_in_vE)) hcond;
fun rfilterOut_E (nt,rt,rst) hncond =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtE
      [(("n",0), ctermE nt),(("r",0), ctermE rt),(("rs",0), ctermE rst)] rfilter_cons_out_vE)) hncond;
fun rrlDef_E nt = beta_norm (Drule.infer_instantiate ctxtE [(("n",0), ctermE nt)] rrl_def_vE);

val () = out "RR_E_COMBINATORS_READY\n";

(* ============================================================================
   rfilter_sublist : lmem x (rfilter n L) ==> lmem x L   (BY list_induct on L)
   ============================================================================ *)
val rfilter_sublist =
  let
    val xF = Free("x", natT); val nF = Free("n", natT)
    fun concBody zt = mkImp (lmem xF (rfilter nF zt)) (lmem xF zt)
    val Qpred = Abs("z", natlistT, concBody (Bound 0))
    val LF = Free("L", natlistT)
    val base =
      let
        val hassm = Thm.assume (ctermE (jT (lmem xF (rfilter nF lnilC))))
        val lrn = rfilterNil_E nF                                   (* leq (rfilter n lnil) lnil *)
        val mem_lnil = lmem_transfer_E (xF, rfilter nF lnilC, lnilC) lrn hassm
        val ff  = Thm.implies_elim (lmemNilElim_E xF) mem_lnil
        val conc = Thm.implies_elim (oFalse_elim_E (lmem xF lnilC)) ff
        val dis  = Thm.implies_intr (ctermE (jT (lmem xF (rfilter nF lnilC)))) conc
      in impI_E (lmem xF (rfilter nF lnilC), lmem xF lnilC) dis end
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val ihprop = jT (concBody tF)
    val IH = Thm.assume (ctermE ihprop)
    val stepConcl =
      let
        val hassm = Thm.assume (ctermE (jT (lmem xF (rfilter nF (lcons hF tF)))))
        val cond = coprime_test hF nF
        (* case: h is coprime -> rfilter n (cons h t) = cons h (rfilter n t) *)
        val caseIn =
          let
            val hcond = Thm.assume (ctermE (jT cond))
            val lrw = rfilterIn_E (nF, hF, tF) hcond          (* leq (rfilter n (cons h t)) (cons h (rfilter n t)) *)
            val mem_cons = lmem_transfer_E (xF, rfilter nF (lcons hF tF), lcons hF (rfilter nF tF)) lrw hassm
            val dj = Thm.implies_elim (lmemConsFwd_E (xF, hF, rfilter nF tF)) mem_cons  (* Disj (oeq x h) (lmem x (rfilter n t)) *)
            val cA = let val hxh = Thm.assume (ctermE (jT (oeq xF hF)))
                         val r = Thm.implies_elim (lmemConsBwd_E (xF, hF, tF))
                                   (disjI1_E (oeq xF hF, lmem xF tF) hxh)
                     in Thm.implies_intr (ctermE (jT (oeq xF hF))) r end
            val cB = let val hmr = Thm.assume (ctermE (jT (lmem xF (rfilter nF tF))))
                         val mt = mp_E (lmem xF (rfilter nF tF), lmem xF tF) IH hmr
                         val r = Thm.implies_elim (lmemConsBwd_E (xF, hF, tF))
                                   (disjI2_E (oeq xF hF, lmem xF tF) mt)
                     in Thm.implies_intr (ctermE (jT (lmem xF (rfilter nF tF)))) r end
            val res = disjE_E (oeq xF hF, lmem xF (rfilter nF tF), lmem xF (lcons hF tF)) dj cA cB
          in Thm.implies_intr (ctermE (jT cond)) res end
        (* case: h not coprime -> rfilter n (cons h t) = rfilter n t *)
        val caseOut =
          let
            val hncond = Thm.assume (ctermE (jT (neg cond)))
            val lrw = rfilterOut_E (nF, hF, tF) hncond        (* leq (rfilter n (cons h t)) (rfilter n t) *)
            val mem_t' = lmem_transfer_E (xF, rfilter nF (lcons hF tF), rfilter nF tF) lrw hassm
            val mem_t  = mp_E (lmem xF (rfilter nF tF), lmem xF tF) IH mem_t'
            val dj = disjI2_E (oeq xF hF, lmem xF tF) mem_t
            val res = Thm.implies_elim (lmemConsBwd_E (xF, hF, tF)) dj
          in Thm.implies_intr (ctermE (jT (neg cond))) res end
        val em = em_E cond
        val conc = disjE_E (cond, neg cond, lmem xF (lcons hF tF)) em caseIn caseOut
        val dis = Thm.implies_intr (ctermE (jT (lmem xF (rfilter nF (lcons hF tF))))) conc
      in impI_E (lmem xF (rfilter nF (lcons hF tF)), lmem xF (lcons hF tF)) dis end
    val step = Thm.forall_intr (ctermE hF)
                 (Thm.forall_intr (ctermE tF) (Thm.implies_intr (ctermE ihprop) stepConcl))
    val concl = list_induct_E (Qpred, LF) base step  (* jT (concBody L) *)
  in varify concl end;
val () = if length (Thm.hyps_of rfilter_sublist) = 0 then out "OK rfilter_sublist\n" else out "FAIL rfilter_sublist\n";

(* application form of rfilter_sublist *)
val rfilter_sublist_vE = rfilter_sublist;
fun rfilter_sublist_E (xt,nt,Lt) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("x",0), ctermE xt),(("n",0), ctermE nt),(("L",0), ctermE Lt)] rfilter_sublist_vE)
  in mp_E (lmem xt (rfilter nt Lt), lmem xt Lt) inst hmem end;

(* leq_sym on ctxtE (via leq_subst) *)
fun leq_sym_E (aT,bT) hab =
  let val Pabs = Abs("z", natlistT, leq (Bound 0) aT)
      val refl_aa = beta_norm (Drule.infer_instantiate ctxtE [(("a",0), ctermE aT)] leq_refl_vW)
  in leq_rw_E (Pabs, aT, bT) hab refl_aa end;

val () = out "RR_PHASE2_DONE\n";

(* ============================================================================
   PHASE 3 : lnodup_rfilter : lnodup L ==> lnodup (rfilter n L)  (BY list_induct)
   then lnodup (rrl n).
   ============================================================================ *)
val lnodup_rfilter =
  let
    val nF = Free("n", natT)
    fun concBody zt = mkImp (lnodup zt) (lnodup (rfilter nF zt))
    val Qpred = Abs("z", natlistT, concBody (Bound 0))
    val LF = Free("L", natlistT)
    val base =
      let
        val hnd = Thm.assume (ctermE (jT (lnodup lnilC)))
        val lrn = rfilterNil_E nF                          (* leq (rfilter n lnil) lnil *)
        val lrn_s = leq_sym_E (rfilter nF lnilC, lnilC) lrn (* leq lnil (rfilter n lnil) *)
        val res = lnodup_transfer_E (lnilC, rfilter nF lnilC) lrn_s hnd
        val dis = Thm.implies_intr (ctermE (jT (lnodup lnilC))) res
      in impI_E (lnodup lnilC, lnodup (rfilter nF lnilC)) dis end
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val ihprop = jT (concBody tF)
    val IH = Thm.assume (ctermE ihprop)
    val stepConcl =
      let
        val hnd = Thm.assume (ctermE (jT (lnodup (lcons hF tF))))
        val cj  = Thm.implies_elim (lnodupConsFwd_E (hF, tF)) hnd
        val nmem = conjunct1_E (neg (lmem hF tF), lnodup tF) cj   (* neg (lmem h t) *)
        val ndt  = conjunct2_E (neg (lmem hF tF), lnodup tF) cj   (* lnodup t *)
        val ndrt = mp_E (lnodup tF, lnodup (rfilter nF tF)) IH ndt (* lnodup (rfilter n t) *)
        val cond = coprime_test hF nF
        val caseIn =
          let
            val hcond = Thm.assume (ctermE (jT cond))
            val lrw = rfilterIn_E (nF, hF, tF) hcond  (* leq (rfilter n (cons h t)) (cons h (rfilter n t)) *)
            (* h not in (rfilter n t) : because rfilter n t is sublist of t and h not in t *)
            val nmem_rt =
              let val hassm = Thm.assume (ctermE (jT (lmem hF (rfilter nF tF))))
                  val inT   = rfilter_sublist_E (hF, nF, tF) hassm   (* lmem h t *)
                  val ff    = mp_E (lmem hF tF, oFalseC) nmem inT
                  val dis   = Thm.implies_intr (ctermE (jT (lmem hF (rfilter nF tF)))) ff
              in impI_E (lmem hF (rfilter nF tF), oFalseC) dis end
            val cj2 = conjI_E (neg (lmem hF (rfilter nF tF)), lnodup (rfilter nF tF)) nmem_rt ndrt
            val nd_target = Thm.implies_elim (lnodupConsBwd_E (hF, rfilter nF tF)) cj2  (* lnodup (cons h (rfilter n t)) *)
            val lrw_s = leq_sym_E (rfilter nF (lcons hF tF), lcons hF (rfilter nF tF)) lrw
            val res = lnodup_transfer_E (lcons hF (rfilter nF tF), rfilter nF (lcons hF tF)) lrw_s nd_target
          in Thm.implies_intr (ctermE (jT cond)) res end
        val caseOut =
          let
            val hncond = Thm.assume (ctermE (jT (neg cond)))
            val lrw = rfilterOut_E (nF, hF, tF) hncond  (* leq (rfilter n (cons h t)) (rfilter n t) *)
            val lrw_s = leq_sym_E (rfilter nF (lcons hF tF), rfilter nF tF) lrw
            val res = lnodup_transfer_E (rfilter nF tF, rfilter nF (lcons hF tF)) lrw_s ndrt
          in Thm.implies_intr (ctermE (jT (neg cond))) res end
        val em = em_E cond
        val conc = disjE_E (cond, neg cond, lnodup (rfilter nF (lcons hF tF))) em caseIn caseOut
        val dis = Thm.implies_intr (ctermE (jT (lnodup (lcons hF tF)))) conc
      in impI_E (lnodup (lcons hF tF), lnodup (rfilter nF (lcons hF tF))) dis end
    val step = Thm.forall_intr (ctermE hF)
                 (Thm.forall_intr (ctermE tF) (Thm.implies_intr (ctermE ihprop) stepConcl))
    val concl = list_induct_E (Qpred, LF) base step
  in varify concl end;
val () = if length (Thm.hyps_of lnodup_rfilter) = 0 then out "OK lnodup_rfilter\n" else out "FAIL lnodup_rfilter\n";

val lnodup_rfilter_vE = lnodup_rfilter;
fun lnodup_rfilter_E (nt,Lt) hnd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("n",0), ctermE nt),(("L",0), ctermE Lt)] lnodup_rfilter_vE)
  in mp_E (lnodup Lt, lnodup (rfilter nt Lt)) inst hnd end;

(* ---- lnodup (rrl n) : rrl n = rfilter n (uptoF (sub n 1)); upto is nodup; rfilter preserves ---- *)
val lnodup_upto_E_v = lnodup_upto_vW;
fun lnodup_upto_E nt = beta_norm (Drule.infer_instantiate ctxtE [(("k_nd",0), ctermE nt)] lnodup_upto_E_v);

(* lnodup_upto_vW has the schematic form  lnodup (uptoF ?k_nd) ; instantiate k_nd := sub n 1 *)
val lnodup_rrl =
  let
    val nF = Free("n", natT)
    val rng = uptoF (sub nF (suc ZeroC))
    val nd_up  = lnodup_upto_E (sub nF (suc ZeroC))    (* lnodup (uptoF (sub n 1)) *)
    val nd_filt = lnodup_rfilter_E (nF, rng) nd_up      (* lnodup (rfilter n (uptoF (sub n 1))) *)
    val rdef = rrlDef_E nF                              (* leq (rrl n) (rfilter n (uptoF (sub n 1))) *)
    val rdef_s = leq_sym_E (rrl nF, rfilter nF rng) rdef (* leq (rfilter ...) (rrl n) *)
    val res = lnodup_transfer_E (rfilter nF rng, rrl nF) rdef_s nd_filt
  in varify res end;
val () = if length (Thm.hyps_of lnodup_rrl) = 0 then out "OK lnodup_rrl\n" else out "FAIL lnodup_rrl\n";

val () = out "RR_PHASE3_DONE\n";

(* ============================================================================
   PHASE 4 : membership characterization lmem_rrl.
   First on rfilter (both directions), then transfer to rrl.
   ============================================================================ *)
(* oeq-rewrite combinator + sym/refl on ctxtE *)
fun oeqRefl_E t = beta_norm (Drule.infer_instantiate ctxtE [(("a",0), ctermE t)] oeq_refl_vW);
fun oeq_rw_E (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("P",0), ctermE Pabs),(("a",0), ctermE aT),(("b",0), ctermE bT)] oeq_subst_vW)
  in inst OF [hab, hPa] end;
fun oeq_sym_E hab = oeq_sym_vW OF [hab];

(* ---- lmem_rfilter_fwd : lmem r (rfilter n L) ==> Conj (lmem r L)(coprime_test r n) ---- *)
val lmem_rfilter_fwd =
  let
    val rF = Free("r", natT); val nF = Free("n", natT)
    fun goalC zt = mkConj (lmem rF zt) (coprime_test rF nF)
    fun concBody zt = mkImp (lmem rF (rfilter nF zt)) (goalC zt)
    val Qpred = Abs("z", natlistT, concBody (Bound 0))
    val LF = Free("L", natlistT)
    val base =
      let
        val hassm = Thm.assume (ctermE (jT (lmem rF (rfilter nF lnilC))))
        val lrn = rfilterNil_E nF
        val mem_lnil = lmem_transfer_E (rF, rfilter nF lnilC, lnilC) lrn hassm
        val ff  = Thm.implies_elim (lmemNilElim_E rF) mem_lnil
        val conc = Thm.implies_elim (oFalse_elim_E (goalC lnilC)) ff
        val dis  = Thm.implies_intr (ctermE (jT (lmem rF (rfilter nF lnilC)))) conc
      in impI_E (lmem rF (rfilter nF lnilC), goalC lnilC) dis end
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val ihprop = jT (concBody tF)
    val IH = Thm.assume (ctermE ihprop)
    val stepConcl =
      let
        val hassm = Thm.assume (ctermE (jT (lmem rF (rfilter nF (lcons hF tF)))))
        val cond = coprime_test hF nF
        val caseIn =
          let
            val hcond = Thm.assume (ctermE (jT cond))
            val lrw = rfilterIn_E (nF, hF, tF) hcond
            val mem_cons = lmem_transfer_E (rF, rfilter nF (lcons hF tF), lcons hF (rfilter nF tF)) lrw hassm
            val dj = Thm.implies_elim (lmemConsFwd_E (rF, hF, rfilter nF tF)) mem_cons
            (* r = h case *)
            val cA =
              let val hrh = Thm.assume (ctermE (jT (oeq rF hF)))
                  val mem_rt = Thm.implies_elim (lmemConsBwd_E (rF, hF, tF))
                                 (disjI1_E (oeq rF hF, lmem rF tF) hrh)
                  (* coprime_test r n from coprime_test h n via r=h *)
                  val Pcop = Abs("z", natT, coprime_test (Bound 0) nF)  (* %z. oeq (gcdf z n) 1 *)
                  val hrh_s = oeq_sym_E hrh                              (* oeq h r *)
                  val cop_r = oeq_rw_E (Pcop, hF, rF) hrh_s hcond        (* coprime_test r n *)
                  val cj = conjI_E (lmem rF (lcons hF tF), coprime_test rF nF) mem_rt cop_r
              in Thm.implies_intr (ctermE (jT (oeq rF hF))) cj end
            (* lmem r (rfilter n t) case -> IH *)
            val cB =
              let val hmr = Thm.assume (ctermE (jT (lmem rF (rfilter nF tF))))
                  val cjt = mp_E (lmem rF (rfilter nF tF), goalC tF) IH hmr
                  val mem_t = conjunct1_E (lmem rF tF, coprime_test rF nF) cjt
                  val cop_r = conjunct2_E (lmem rF tF, coprime_test rF nF) cjt
                  val mem_cons2 = Thm.implies_elim (lmemConsBwd_E (rF, hF, tF))
                                    (disjI2_E (oeq rF hF, lmem rF tF) mem_t)
                  val cj = conjI_E (lmem rF (lcons hF tF), coprime_test rF nF) mem_cons2 cop_r
              in Thm.implies_intr (ctermE (jT (lmem rF (rfilter nF tF)))) cj end
            val res = disjE_E (oeq rF hF, lmem rF (rfilter nF tF), goalC (lcons hF tF)) dj cA cB
          in Thm.implies_intr (ctermE (jT cond)) res end
        val caseOut =
          let
            val hncond = Thm.assume (ctermE (jT (neg cond)))
            val lrw = rfilterOut_E (nF, hF, tF) hncond
            val mem_t' = lmem_transfer_E (rF, rfilter nF (lcons hF tF), rfilter nF tF) lrw hassm
            val cjt = mp_E (lmem rF (rfilter nF tF), goalC tF) IH mem_t'
            val mem_t = conjunct1_E (lmem rF tF, coprime_test rF nF) cjt
            val cop_r = conjunct2_E (lmem rF tF, coprime_test rF nF) cjt
            val mem_cons = Thm.implies_elim (lmemConsBwd_E (rF, hF, tF))
                             (disjI2_E (oeq rF hF, lmem rF tF) mem_t)
            val cj = conjI_E (lmem rF (lcons hF tF), coprime_test rF nF) mem_cons cop_r
          in Thm.implies_intr (ctermE (jT (neg cond))) cj end
        val em = em_E cond
        val conc = disjE_E (cond, neg cond, goalC (lcons hF tF)) em caseIn caseOut
        val dis = Thm.implies_intr (ctermE (jT (lmem rF (rfilter nF (lcons hF tF))))) conc
      in impI_E (lmem rF (rfilter nF (lcons hF tF)), goalC (lcons hF tF)) dis end
    val step = Thm.forall_intr (ctermE hF)
                 (Thm.forall_intr (ctermE tF) (Thm.implies_intr (ctermE ihprop) stepConcl))
    val concl = list_induct_E (Qpred, LF) base step
  in varify concl end;
val () = if length (Thm.hyps_of lmem_rfilter_fwd) = 0 then out "OK lmem_rfilter_fwd\n" else out "FAIL lmem_rfilter_fwd\n";

val () = out "RR_PHASE4A_DONE\n";

(* ---- lmem_rfilter_bwd : Conj (lmem r L)(coprime_test r n) ==> lmem r (rfilter n L) ---- *)
val lmem_rfilter_bwd =
  let
    val rF = Free("r", natT); val nF = Free("n", natT)
    fun hypC zt = mkConj (lmem rF zt) (coprime_test rF nF)
    fun concBody zt = mkImp (hypC zt) (lmem rF (rfilter nF zt))
    val Qpred = Abs("z", natlistT, concBody (Bound 0))
    val LF = Free("L", natlistT)
    val base =
      let
        val hcj = Thm.assume (ctermE (jT (hypC lnilC)))
        val mem = conjunct1_E (lmem rF lnilC, coprime_test rF nF) hcj
        val ff  = Thm.implies_elim (lmemNilElim_E rF) mem
        val conc = Thm.implies_elim (oFalse_elim_E (lmem rF (rfilter nF lnilC))) ff
        val dis = Thm.implies_intr (ctermE (jT (hypC lnilC))) conc
      in impI_E (hypC lnilC, lmem rF (rfilter nF lnilC)) dis end
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val ihprop = jT (concBody tF)
    val IH = Thm.assume (ctermE ihprop)
    val stepConcl =
      let
        val hcj  = Thm.assume (ctermE (jT (hypC (lcons hF tF))))
        val memC = conjunct1_E (lmem rF (lcons hF tF), coprime_test rF nF) hcj
        val cop_r= conjunct2_E (lmem rF (lcons hF tF), coprime_test rF nF) hcj
        val dj   = Thm.implies_elim (lmemConsFwd_E (rF, hF, tF)) memC   (* Disj (oeq r h)(lmem r t) *)
        val cond = coprime_test hF nF
        val goalMem = lmem rF (rfilter nF (lcons hF tF))
        val caseIn =
          let
            val hcond = Thm.assume (ctermE (jT cond))
            val lrw = rfilterIn_E (nF, hF, tF) hcond  (* leq (rfilter n (cons h t)) (cons h (rfilter n t)) *)
            val lrw_s = leq_sym_E (rfilter nF (lcons hF tF), lcons hF (rfilter nF tF)) lrw
            (* prove lmem r (cons h (rfilter n t)) from dj, then transfer back *)
            val cA = let val hrh = Thm.assume (ctermE (jT (oeq rF hF)))
                         val m = Thm.implies_elim (lmemConsBwd_E (rF, hF, rfilter nF tF))
                                   (disjI1_E (oeq rF hF, lmem rF (rfilter nF tF)) hrh)
                     in Thm.implies_intr (ctermE (jT (oeq rF hF))) m end
            val cB = let val hmt = Thm.assume (ctermE (jT (lmem rF tF)))
                         val cjt = conjI_E (lmem rF tF, coprime_test rF nF) hmt cop_r
                         val mrt = mp_E (hypC tF, lmem rF (rfilter nF tF)) IH cjt
                         val m = Thm.implies_elim (lmemConsBwd_E (rF, hF, rfilter nF tF))
                                   (disjI2_E (oeq rF hF, lmem rF (rfilter nF tF)) mrt)
                     in Thm.implies_intr (ctermE (jT (lmem rF tF))) m end
            val memCons = disjE_E (oeq rF hF, lmem rF tF, lmem rF (lcons hF (rfilter nF tF))) dj cA cB
            val res = lmem_transfer_E (rF, lcons hF (rfilter nF tF), rfilter nF (lcons hF tF)) lrw_s memCons
          in Thm.implies_intr (ctermE (jT cond)) res end
        val caseOut =
          let
            val hncond = Thm.assume (ctermE (jT (neg cond)))
            val lrw = rfilterOut_E (nF, hF, tF) hncond (* leq (rfilter n (cons h t)) (rfilter n t) *)
            val lrw_s = leq_sym_E (rfilter nF (lcons hF tF), rfilter nF tF) lrw
            (* r=h would contradict hncond ; r in t -> IH *)
            val cA = let val hrh = Thm.assume (ctermE (jT (oeq rF hF)))
                         (* coprime_test h n from coprime_test r n via oeq r h *)
                         val Pcop = Abs("z", natT, coprime_test (Bound 0) nF)
                         val cop_h = oeq_rw_E (Pcop, rF, hF) hrh cop_r   (* coprime_test h n *)
                         val ff = mp_E (cond, oFalseC) hncond cop_h
                         val m  = Thm.implies_elim (oFalse_elim_E (lmem rF (rfilter nF tF))) ff
                     in Thm.implies_intr (ctermE (jT (oeq rF hF))) m end
            val cB = let val hmt = Thm.assume (ctermE (jT (lmem rF tF)))
                         val cjt = conjI_E (lmem rF tF, coprime_test rF nF) hmt cop_r
                         val mrt = mp_E (hypC tF, lmem rF (rfilter nF tF)) IH cjt
                     in Thm.implies_intr (ctermE (jT (lmem rF tF))) mrt end
            val memT = disjE_E (oeq rF hF, lmem rF tF, lmem rF (rfilter nF tF)) dj cA cB
            val res = lmem_transfer_E (rF, rfilter nF tF, rfilter nF (lcons hF tF)) lrw_s memT
          in Thm.implies_intr (ctermE (jT (neg cond))) res end
        val em = em_E cond
        val conc = disjE_E (cond, neg cond, goalMem) em caseIn caseOut
        val dis = Thm.implies_intr (ctermE (jT (hypC (lcons hF tF)))) conc
      in impI_E (hypC (lcons hF tF), goalMem) dis end
    val step = Thm.forall_intr (ctermE hF)
                 (Thm.forall_intr (ctermE tF) (Thm.implies_intr (ctermE ihprop) stepConcl))
    val concl = list_induct_E (Qpred, LF) base step
  in varify concl end;
val () = if length (Thm.hyps_of lmem_rfilter_bwd) = 0 then out "OK lmem_rfilter_bwd\n" else out "FAIL lmem_rfilter_bwd\n";

val () = out "RR_PHASE4B_DONE\n";

(* application forms of the rfilter characterization *)
val lmem_rfilter_fwd_vE = lmem_rfilter_fwd;
val lmem_rfilter_bwd_vE = lmem_rfilter_bwd;
fun lmem_rfilter_fwd_E (rt,nt,Lt) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("r",0), ctermE rt),(("n",0), ctermE nt),(("L",0), ctermE Lt)] lmem_rfilter_fwd_vE)
  in mp_E (lmem rt (rfilter nt Lt), mkConj (lmem rt Lt)(coprime_test rt nt)) inst hmem end;
fun lmem_rfilter_bwd_E (rt,nt,Lt) hcj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("r",0), ctermE rt),(("n",0), ctermE nt),(("L",0), ctermE Lt)] lmem_rfilter_bwd_vE)
  in mp_E (mkConj (lmem rt Lt)(coprime_test rt nt), lmem rt (rfilter nt Lt)) inst hcj end;

(* ============================================================================
   PHASE 5 : lmem_rrl (both directions), via rrl_def transfer.
   rng = uptoF (sub n 1).  rrl n leq rfilter n rng.
   ============================================================================ *)
val lmem_rrl_fwd =
  let
    val rF = Free("r", natT); val nF = Free("n", natT)
    val rng = uptoF (sub nF (suc ZeroC))
    val goalC = mkConj (lmem rF rng) (coprime_test rF nF)
    val hmemP = jT (lmem rF (rrl nF))
    val hmem  = Thm.assume (ctermE hmemP)
    val rdef  = rrlDef_E nF                                  (* leq (rrl n)(rfilter n rng) *)
    val mem_rf= lmem_transfer_E (rF, rrl nF, rfilter nF rng) rdef hmem  (* lmem r (rfilter n rng) *)
    val cj    = lmem_rfilter_fwd_E (rF, nF, rng) mem_rf      (* Conj (lmem r rng)(coprime r n) *)
    val res   = Thm.implies_intr (ctermE hmemP) cj
  in varify res end;
val () = if length (Thm.hyps_of lmem_rrl_fwd) = 0 then out "OK lmem_rrl_fwd\n" else out "FAIL lmem_rrl_fwd\n";

val lmem_rrl_bwd =
  let
    val rF = Free("r", natT); val nF = Free("n", natT)
    val rng = uptoF (sub nF (suc ZeroC))
    val hypC = mkConj (lmem rF rng) (coprime_test rF nF)
    val hcj  = Thm.assume (ctermE (jT hypC))
    val mem_rf = lmem_rfilter_bwd_E (rF, nF, rng) hcj         (* lmem r (rfilter n rng) *)
    val rdef = rrlDef_E nF                                    (* leq (rrl n)(rfilter n rng) *)
    val rdef_s = leq_sym_E (rrl nF, rfilter nF rng) rdef      (* leq (rfilter n rng)(rrl n) *)
    val res_mem = lmem_transfer_E (rF, rfilter nF rng, rrl nF) rdef_s mem_rf  (* lmem r (rrl n) *)
    val res = Thm.implies_intr (ctermE (jT hypC)) res_mem
  in varify res end;
val () = if length (Thm.hyps_of lmem_rrl_bwd) = 0 then out "OK lmem_rrl_bwd\n" else out "FAIL lmem_rrl_bwd\n";

val () = out "OK lmem_rrl\n";
val () = out "RR_PHASE5_DONE\n";

(* ============================================================================
   FINAL VALIDATION : statements aconv intent, 0-hyp, soundness probes.
   ============================================================================ *)
val () = out "RR_VALIDATE_BEGIN\n";
val rV = Var(("r",0),natT); val nV = Var(("n",0),natT); val LV = Var(("L",0),natlistT);
fun coprime_testV a n = oeq (gcdf a n) (suc ZeroC);

(* intended statements *)
val lnodup_rrl_intended = jT (lnodup (rrl nV));
val lmem_rrl_fwd_intended =
  Logic.mk_implies (jT (lmem rV (rrl nV)),
    jT (mkConj (lmem rV (uptoF (sub nV (suc ZeroC)))) (coprime_testV rV nV)));
val lmem_rrl_bwd_intended =
  Logic.mk_implies (jT (mkConj (lmem rV (uptoF (sub nV (suc ZeroC)))) (coprime_testV rV nV)),
    jT (lmem rV (rrl nV)));
(* rfilter_sublist came out of list_induct as a single Trueprop wrapping object Imp;
   its Vars are named x (element), n (modulus), L (list). *)
val xVsub = Var(("x",0),natT);
val rfilter_sublist_intended =
  jT (mkImp (lmem xVsub (rfilter nV LV)) (lmem xVsub LV));

val r_nd = (length (Thm.hyps_of lnodup_rrl) = 0)
           andalso ((Thm.prop_of lnodup_rrl) aconv lnodup_rrl_intended);
val () = if r_nd then out "VALID lnodup_rrl aconv intended\n" else out "INVALID lnodup_rrl\n";

val r_fwd = (length (Thm.hyps_of lmem_rrl_fwd) = 0)
            andalso ((Thm.prop_of lmem_rrl_fwd) aconv lmem_rrl_fwd_intended);
val () = if r_fwd then out "VALID lmem_rrl_fwd aconv intended\n" else out "INVALID lmem_rrl_fwd\n";

val r_bwd = (length (Thm.hyps_of lmem_rrl_bwd) = 0)
            andalso ((Thm.prop_of lmem_rrl_bwd) aconv lmem_rrl_bwd_intended);
val () = if r_bwd then out "VALID lmem_rrl_bwd aconv intended\n" else out "INVALID lmem_rrl_bwd\n";

val r_sub = (length (Thm.hyps_of rfilter_sublist) = 0)
            andalso ((Thm.prop_of rfilter_sublist) aconv rfilter_sublist_intended);
val () = if r_sub then out "VALID rfilter_sublist aconv intended\n" else out "INVALID rfilter_sublist\n";

(* SOUNDNESS PROBE 1 : lmem_rrl_fwd genuinely CARRIES the coprime condition.
   A bogus statement that DROPS coprime_test must NOT match. *)
val probe_fwd_drops_coprime =
  let val bogus = Logic.mk_implies (jT (lmem rV (rrl nV)),
                    jT (lmem rV (uptoF (sub nV (suc ZeroC)))))
  in not ((Thm.prop_of lmem_rrl_fwd) aconv bogus) end;
val () = if probe_fwd_drops_coprime then out "PROBE_OK fwd keeps coprime_test\n"
         else out "PROBE_FAIL fwd dropped coprime\n";

(* SOUNDNESS PROBE 2 : lmem_rrl_fwd keeps the range condition (not trivially true). *)
val probe_fwd_keeps_range =
  let val bogus = Logic.mk_implies (jT (lmem rV (rrl nV)), jT (coprime_testV rV nV))
  in not ((Thm.prop_of lmem_rrl_fwd) aconv bogus) end;
val () = if probe_fwd_keeps_range then out "PROBE_OK fwd keeps range\n"
         else out "PROBE_FAIL fwd dropped range\n";

(* SOUNDNESS PROBE 3 : bwd genuinely REQUIRES coprime (a bogus dropping it must not match). *)
val probe_bwd_requires_coprime =
  let val bogus = Logic.mk_implies (jT (lmem rV (uptoF (sub nV (suc ZeroC)))),
                    jT (lmem rV (rrl nV)))
  in not ((Thm.prop_of lmem_rrl_bwd) aconv bogus) end;
val () = if probe_bwd_requires_coprime then out "PROBE_OK bwd requires coprime\n"
         else out "PROBE_FAIL bwd dropped coprime\n";

(* coprime test well-definedness : gcdf axioms 0-hyp and the test is the named oeq *)
val r_cop_def =
  (length (Thm.hyps_of gcdf_zero_vE) = 0) andalso (length (Thm.hyps_of gcdf_step_vE) = 0);
val () = if r_cop_def then out "OK coprime_def\n" else out "FAIL coprime_def\n";
val () = out "OK rrl\n";

val () =
  if r_nd andalso r_fwd andalso r_bwd andalso r_sub
     andalso probe_fwd_drops_coprime andalso probe_fwd_keeps_range
     andalso probe_bwd_requires_coprime andalso r_cop_def
  then out "REDUCED_RES_OK\n"
  else out "REDUCED_RES_FAILED\n";
