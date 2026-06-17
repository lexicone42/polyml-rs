(* ============================================================================
   THUE INFRASTRUCTURE DELTA (on the with_wilson_pairing base; final ctxtL2).
   Three pieces of genuinely new machinery toward Thue's lemma:
     (1) floor_sqrt  : !n. ?s. le (s*s) n /\ lt n ((Suc s)*(Suc s))
     (2) rangelist m = [0,1,...,m-1] : llen=m, lnodup, lmem i <=> lt i m
     (3) list_pigeonhole : lnodup L /\ lt k (llen L) /\ (!e. lmem e L --> lt (f e) k)
                           ==> ?e1 e2. lmem e1 L /\ lmem e2 L /\ ~(e1=e2) /\ f e1 = f e2
   Each proved 0-hyp by genuine kernel inference.
   ============================================================================ *)
val () = out "THUE_DELTA_BEGIN\n";

(* ----------------------------------------------------------------------------
   ONE new theory + final context: add the const `rangelist : nat -> natlist`
   with two conservative recursion axioms on top of thyL2.
   ---------------------------------------------------------------------------- *)
val thyTHc = Sign.add_consts
  [(Binding.name "rangelist", natT --> natlistT, NoSyn)] thyL2;
fun cnstTH nm T = Const (Sign.full_name thyTHc (Binding.name nm), T);
val rangelistC = cnstTH "rangelist" (natT --> natlistT);
fun rangelist n = rangelistC $ n;

val nTH = Free("n", natT);
(* rangelist 0 = lnil ;  rangelist (Suc n) = lcons n (rangelist n)
   so rangelist m = [m-1, m-2, ..., 1, 0] as a list; members are exactly {0..m-1}. *)
val ((_,rangelist_zero_ax), thyTH1) = Thm.add_axiom_global (Binding.name "rangelist_zero",
      jT (leq (rangelist ZeroC) lnilC)) thyTHc;
val ((_,rangelist_suc_ax), thyTH) = Thm.add_axiom_global (Binding.name "rangelist_suc",
      jT (leq (rangelist (suc nTH)) (lcons nTH (rangelist nTH)))) thyTH1;

val ctxtTH  = Proof_Context.init_global thyTH;
val ctermTH = Thm.cterm_of ctxtTH;
val () = out "THUE_CONTEXT_READY\n";

(* ----------------------------------------------------------------------------
   re-varify reused base lemmas onto ctxtTH
   ---------------------------------------------------------------------------- *)
val oeq_refl_vT2    = varify oeq_refl;
val oeq_subst_vT2   = varify oeq_subst;
val oeq_sym_vT2     = varify oeq_sym;
val oeq_trans_vT2   = varify oeq_trans;
val Suc_cong_vT2    = varify Suc_cong;
val exI_vT2         = varify exI_ax;
val exE_vT2         = varify exE_ax;
val oFalse_elim_vT2 = varify oFalse_elim_ax;
val Suc_neq_Zero_vT2= varify Suc_neq_Zero_ax;
val Suc_inj_vT2     = varify Suc_inj_ax;
val conjI_vT2       = varify conjI_ax;
val conjunct1_vT2   = varify conjunct1_ax;
val conjunct2_vT2   = varify conjunct2_ax;
val disjI1_vT2      = varify disjI1_ax;
val disjI2_vT2      = varify disjI2_ax;
val disjE_vT2       = varify disjE_ax;
val mp_vT2          = varify mp_ax;
val impI_vT2        = varify impI_ax;
val ex_middle_vT2   = varify ex_middle_ax;
val allI_vT2        = varify allI_ax;
val allE_vT2        = varify allE_ax;
val add_0_vT2       = varify add_0;
val add_Suc_vT2     = varify add_Suc;
val add_0_right_vT2 = varify add_0_right;
val add_Suc_right_vT2 = varify add_Suc_right;
val add_comm_vT2    = varify add_comm;
val add_assoc_vT2   = varify add_assoc;
val add_left_cancel_vT2 = varify add_left_cancel;
val add_eq_zero_left_vT2 = varify add_eq_zero_left;
val mult_0_vT2      = varify mult_0;
val mult_Suc_vT2    = varify mult_Suc;
val mult_0_right_vT2= varify mult_0_right;
val mult_Suc_right_vT2 = varify mult_Suc_right;
val mult_comm_vT2   = varify mult_comm;
val mult_assoc_vT2  = varify mult_assoc;
val mult_1_left_vT2 = varify mult_1_left;
val left_distrib_vT2 = varify left_distrib;
val right_distrib_vT2 = varify right_distrib;
val mult_le_mono_vT2 = varify mult_le_mono;
val le_refl_vT2     = varify le_refl;
val le_trans_vT2    = varify le_trans;
val le_total_vT2    = varify le_total;
val le_antisym_vT2  = varify le_antisym;
val le_add_vT2      = varify le_add;
val zero_le_vT2     = varify zero_le;
val lt_suc_vT2      = varify lt_suc;
val lt_irrefl_vT2   = varify lt_irrefl;
val lt_trans_vT2    = varify lt_trans;
val lt_suc_cases_vT2= varify lt_suc_cases;
val nlt_le_vT2      = varify nlt_le;
val disj_zero_or_suc_vT2 = varify disj_zero_or_suc;
(* list machinery *)
val leq_refl_vT2    = varify leq_refl_ax;
val leq_subst_vT2   = varify leq_subst_ax;
val leq_sym_vT2     = varify leq_sym;
val leq_trans_vT2   = varify leq_trans;
val list_induct_vT2 = varify list_induct_ax;
val lprod_nil_vT2   = varify lprod_nil_ax;
val lprod_cons_vT2  = varify lprod_cons_ax;
val lmem_nil_elim_vT2 = varify lmem_nil_elim_ax;
val lmem_cons_fwd_vT2 = varify lmem_cons_fwd_ax;
val lmem_cons_bwd_vT2 = varify lmem_cons_bwd_ax;
val llen_nil_vT2    = varify llen_nil_ax;
val llen_cons_vT2   = varify llen_cons_ax;
val lnodup_nil_vT2  = varify lnodup_nil_ax;
val lnodup_cons_fwd_vT2 = varify lnodup_cons_fwd_ax;
val lnodup_cons_bwd_vT2 = varify lnodup_cons_bwd_ax;
(* new axioms *)
val rangelist_zero_vT2 = varify rangelist_zero_ax;
val rangelist_suc_vT2  = varify rangelist_suc_ax;
val nat_induct_vT2  = varify nat_induct;
val () = out "THUE_VARIFY_READY\n";

(* ----------------------------------------------------------------------------
   combinators on ctxtTH (suffix _t)
   ---------------------------------------------------------------------------- *)
fun oeqRefl_t x = beta_norm (Drule.infer_instantiate ctxtTH [(("a",0), ctermTH x)] oeq_refl_vT2);
fun oeqSym_t h  = oeq_sym_vT2 OF [h];
fun oeqTrans_t (h1,h2) = oeq_trans_vT2 OF [h1, h2];
fun add0_t t    = beta_norm (Drule.infer_instantiate ctxtTH [(("n",0), ctermTH t)] add_0_vT2);
fun add0r_t t   = beta_norm (Drule.infer_instantiate ctxtTH [(("n",0), ctermTH t)] add_0_right_vT2);
fun addSuc_t (mt,nt) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("m",0), ctermTH mt),(("n",0), ctermTH nt)] add_Suc_vT2);
fun addSucr_t (mt,nt) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("m",0), ctermTH mt),(("n",0), ctermTH nt)] add_Suc_right_vT2);
fun addcomm_t (mt,nt) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("m",0), ctermTH mt),(("n",0), ctermTH nt)] add_comm_vT2);
fun addassoc_t (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("m",0), ctermTH mt),(("n",0), ctermTH nt),(("k",0), ctermTH kt)] add_assoc_vT2);
fun mult0_t t   = beta_norm (Drule.infer_instantiate ctxtTH [(("n",0), ctermTH t)] mult_0_vT2);
fun mult0r_t t  = beta_norm (Drule.infer_instantiate ctxtTH [(("n",0), ctermTH t)] mult_0_right_vT2);
fun multSuc_t (mt,nt) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("m",0), ctermTH mt),(("n",0), ctermTH nt)] mult_Suc_vT2);
fun multSucr_t (nt,mt) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("n",0), ctermTH nt),(("m",0), ctermTH mt)] mult_Suc_right_vT2);
fun multcomm_t (mt,nt) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("m",0), ctermTH mt),(("n",0), ctermTH nt)] mult_comm_vT2);
fun mult1l_t t  = beta_norm (Drule.infer_instantiate ctxtTH [(("n",0), ctermTH t)] mult_1_left_vT2);
fun leftdistrib_t (xt,mt,nt) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("x",0), ctermTH xt),(("m",0), ctermTH mt),(("n",0), ctermTH nt)] left_distrib_vT2);
fun rightdistrib_t (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("m",0), ctermTH mt),(("n",0), ctermTH nt),(("k",0), ctermTH kt)] right_distrib_vT2);

fun oeq_rw_t (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtTH
        [(("P",0), ctermTH Pabs),(("a",0), ctermTH aT),(("b",0), ctermTH bT)] oeq_subst_vT2)
  in inst OF [hab, hPa] end;
fun add_cong_l_t (pT,qT,kT) hpq =
  let val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT))
  in oeq_rw_t (Pabs, pT, qT) hpq (oeqRefl_t (add pT kT)) end;
fun add_cong_r_t (hT,pT,qT) hpq =
  let val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)))
  in oeq_rw_t (Pabs, pT, qT) hpq (oeqRefl_t (add hT pT)) end;
fun mult_cong_l_t (pT,qT,kT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT))
  in oeq_rw_t (Pabs, pT, qT) hpq (oeqRefl_t (mult pT kT)) end;
fun mult_cong_r_t (hT,pT,qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)))
  in oeq_rw_t (Pabs, pT, qT) hpq (oeqRefl_t (mult hT pT)) end;

fun mp_t (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtTH
        [(("A",0), ctermTH At),(("B",0), ctermTH Bt)] mp_vT2)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_t (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtTH
        [(("A",0), ctermTH At),(("B",0), ctermTH Bt)] impI_vT2)
  in Thm.implies_elim inst hImpThm end;
fun conjI_t (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtTH
        [(("A",0), ctermTH At),(("B",0), ctermTH Bt)] conjI_vT2)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_t (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH
      [(("A",0), ctermTH At),(("B",0), ctermTH Bt)] conjunct1_vT2)) h;
fun conjunct2_t (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH
      [(("A",0), ctermTH At),(("B",0), ctermTH Bt)] conjunct2_vT2)) h;
fun oFalse_elim_t rT = beta_norm (Drule.infer_instantiate ctxtTH [(("R",0), ctermTH rT)] oFalse_elim_vT2);
fun disjE_t (At,Bt,Ct) dThm cA cB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtTH
        [(("A",0), ctermTH At),(("B",0), ctermTH Bt),(("C",0), ctermTH Ct)] disjE_vT2)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) cA) cB end;
fun disjI1_t (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH
      [(("A",0), ctermTH At),(("B",0), ctermTH Bt)] disjI1_vT2)) h;
fun disjI2_t (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH
      [(("A",0), ctermTH At),(("B",0), ctermTH Bt)] disjI2_vT2)) h;
fun em_t t = beta_norm (Drule.infer_instantiate ctxtTH [(("A",0), ctermTH t)] ex_middle_vT2);
fun allI_t Pabs hAll = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH
      [(("P",0), ctermTH Pabs)] allI_vT2)) hAll;
fun allE_t Pabs at hF = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH
      [(("P",0), ctermTH Pabs),(("a",0), ctermTH at)] allE_vT2)) hF;
fun Suc_neq_Zero_t nt heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH [(("n",0), ctermTH nt)] Suc_neq_Zero_vT2)) heq;
fun Suc_inj_t (at,bt) heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH
      [(("a",0), ctermTH at),(("b",0), ctermTH bt)] Suc_inj_vT2)) heq;
fun Suc_cong_t h = Suc_cong_vT2 OF [h];

fun exI_t Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtTH
        [(("P",0), ctermTH Pabs),(("a",0), ctermTH at)] exI_vT2)
  in Thm.implies_elim inst hbody end;
fun exE_t (Pabs, goalC) exThm wName bodyFn =
  let val wF = Free(wName, natT)
      val hypTerm = jT (Term.betapply (Pabs, wF))
      val hypThm  = Thm.assume (ctermTH hypTerm)
      val body    = bodyFn wF hypThm
      val minor   = Thm.forall_intr (ctermTH wF) (Thm.implies_intr (ctermTH hypTerm) body)
      val exE_inst= beta_norm (Drule.infer_instantiate ctxtTH
                      [(("P",0), ctermTH Pabs),(("Q",0), ctermTH goalC)] exE_vT2)
  in Thm.implies_elim (Thm.implies_elim exE_inst exThm) minor end;

fun le_intro_t (mT, nT, w) hyp =
  let val Pabs = Abs("p", natT, oeq nT (add mT (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtTH
            [(("P",0), ctermTH Pabs),(("a",0), ctermTH w)] exI_vT2)
  in inst OF [hyp] end;
fun le_refl_t t = beta_norm (Drule.infer_instantiate ctxtTH [(("n",0), ctermTH t)] le_refl_vT2);
fun zero_le_t t = beta_norm (Drule.infer_instantiate ctxtTH [(("n",0), ctermTH t)] zero_le_vT2);
fun le_total_t (mt,nt) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("m",0), ctermTH mt),(("n",0), ctermTH nt)] le_total_vT2);
fun le_trans_t (at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtTH
        [(("m",0), ctermTH at),(("n",0), ctermTH bt),(("k",0), ctermTH ct)] le_trans_vT2)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun le_antisym_t (mt,nt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtTH
        [(("m",0), ctermTH mt),(("n",0), ctermTH nt)] le_antisym_vT2)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun lt_trans_t (at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtTH
        [(("a",0), ctermTH at),(("b",0), ctermTH bt),(("c",0), ctermTH ct)] lt_trans_vT2)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun lt_suc_cases_t (mt,nt) hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH
      [(("m",0), ctermTH mt),(("n",0), ctermTH nt)] lt_suc_cases_vT2)) hlt;
fun lt_suc_t nt = beta_norm (Drule.infer_instantiate ctxtTH [(("n",0), ctermTH nt)] lt_suc_vT2);
fun lt_irrefl_t nt hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH [(("n",0), ctermTH nt)] lt_irrefl_vT2)) hlt;
fun nlt_le_t (dt,ct) hneg =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH
      [(("d",0), ctermTH dt),(("c",0), ctermTH ct)] nlt_le_vT2)) hneg;
fun mult_le_mono_t (cT,jT_,kT) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH
      [(("c",0), ctermTH cT),(("j",0), ctermTH jT_),(("k",0), ctermTH kT)] mult_le_mono_vT2)) h;
fun dzos_t t = beta_norm (Drule.infer_instantiate ctxtTH [(("p",0), ctermTH t)] disj_zero_or_suc_vT2);
fun mkExSuc_t t = mkEx (Abs ("q", natT, oeq t (suc (Bound 0))));

(* list combinators on ctxtTH *)
fun leq_rw_t (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtTH
        [(("P",0), ctermTH Pabs),(("a",0), ctermTH aT),(("b",0), ctermTH bT)] leq_subst_vT2)
  in inst OF [hab, hPa] end;
fun leq_sym_t h = leq_sym_vT2 OF [h];
fun lprodNil_t () = lprod_nil_vT2;
fun lprodCons_t (h,t) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("x",0), ctermTH h),(("t",0), ctermTH t)] lprod_cons_vT2);
fun llenNil_t () = llen_nil_vT2;
fun llenCons_t (h,t) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("x",0), ctermTH h),(("t",0), ctermTH t)] llen_cons_vT2);
fun lmemNilElim_t x = beta_norm (Drule.infer_instantiate ctxtTH [(("x",0), ctermTH x)] lmem_nil_elim_vT2);
fun lmemConsFwd_t (x,y,t) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("x",0), ctermTH x),(("y",0), ctermTH y),(("t",0), ctermTH t)] lmem_cons_fwd_vT2);
fun lmemConsBwd_t (x,y,t) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("x",0), ctermTH x),(("y",0), ctermTH y),(("t",0), ctermTH t)] lmem_cons_bwd_vT2);
fun lnodupConsFwd_t (x,t) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("x",0), ctermTH x),(("t",0), ctermTH t)] lnodup_cons_fwd_vT2);
fun lnodupConsBwd_t (x,t) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("x",0), ctermTH x),(("t",0), ctermTH t)] lnodup_cons_bwd_vT2);
val lnodupNil_t = lnodup_nil_vT2;
fun rangelistZero_t () = rangelist_zero_vT2;
fun rangelistSuc_t n = beta_norm (Drule.infer_instantiate ctxtTH [(("n",0), ctermTH n)] rangelist_suc_vT2);
fun nat_induct_t Pabs kT baseThm stepThm =
  let val ind = beta_norm (Drule.infer_instantiate ctxtTH
        [(("P",0), ctermTH Pabs),(("k",0), ctermTH kT)] nat_induct_vT2)
  in Thm.implies_elim (Thm.implies_elim ind baseThm) stepThm end;

val () = out "THUE_COMBINATORS_READY\n";

(* ============================================================================
   SMALL ORDER HELPERS
   ============================================================================ *)

(* le_eq_or_lt : le a b ==> Disj (oeq a b) (lt a b)
   le a b = Ex(%p. b = a+p). witness p: p=0 -> b=a+0=a -> oeq a b ; p=Suc q -> b=a+Suc q=Suc(a+q)=Suc a+q -> le (Suc a) b = lt a b *)
val le_eq_or_lt =
  let
    val aF = Free("a",natT); val bF = Free("b",natT);
    val hypP = jT (le aF bF);
    val hle  = Thm.assume (ctermTH hypP);
    val goalC = mkDisj (oeq aF bF) (lt aF bF);
    val Pabs = Abs("p", natT, oeq bF (add aF (Bound 0)));
    fun body p (hp:thm) =      (* hp : oeq b (add a p) *)
      let
        val dz = dzos_t p;     (* Disj (oeq p 0) (Ex(%q. oeq p (Suc q))) *)
        val caseZ =
          let val hz = Thm.assume (ctermTH (jT (oeq p ZeroC)))
              val c1 = add_cong_r_t (aF, p, ZeroC) hz   (* (a+p)=(a+0) *)
              val a0 = add0r_t aF                        (* (a+0)=a *)
              val b_ap0 = oeqTrans_t (hp, c1)            (* b=(a+0) *)
              val b_a = oeqTrans_t (b_ap0, a0)           (* b=a *)
              val a_b = oeqSym_t b_a                     (* a=b *)
          in Thm.implies_intr (ctermTH (jT (oeq p ZeroC)))
               (disjI1_t (oeq aF bF, lt aF bF) a_b) end
        val Pq = Abs("q", natT, oeq p (suc (Bound 0)))
        val caseS =
          let val hsP = jT (mkExSuc_t p)
              val hs  = Thm.assume (ctermTH hsP)
              fun bodyS q (hq:thm) =     (* hq : oeq p (Suc q) *)
                let
                  val c1 = add_cong_r_t (aF, p, suc q) hq   (* (a+p)=(a+Suc q) *)
                  val b_aSq = oeqTrans_t (hp, c1)           (* b=(a+Suc q) *)
                  val aSq_S = addSucr_t (aF, q)             (* (a+Suc q)=Suc(a+q) *)
                  val b_Saq = oeqTrans_t (b_aSq, aSq_S)     (* b=Suc(a+q) *)
                  val Saq_eq= addSuc_t (aF, q)              (* (Suc a + q)=Suc(a+q) *)
                  val b_Saqadd = oeqTrans_t (b_Saq, oeqSym_t Saq_eq)  (* b=(Suc a + q) *)
                  val le_Sa_b = le_intro_t (suc aF, bF, q) b_Saqadd   (* le (Suc a) b = lt a b *)
                in disjI2_t (oeq aF bF, lt aF bF) le_Sa_b end
              val res = exE_t (Pq, goalC) hs "qS" bodyS
          in Thm.implies_intr (ctermTH (jT (mkExSuc_t p))) res end
      in disjE_t (oeq p ZeroC, mkExSuc_t p, goalC) dz caseZ caseS end
    val res = exE_t (Pabs, goalC) hle "pE" body
  in varify (Thm.implies_intr (ctermTH hypP) res) end;
val () = if length (Thm.hyps_of le_eq_or_lt) = 0 then out "OK le_eq_or_lt\n" else out "FAIL le_eq_or_lt\n";
fun le_eq_or_lt_t (at,bt) hle =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH
      [(("a",0), ctermTH at),(("b",0), ctermTH bt)] le_eq_or_lt)) hle;

(* lt_imp_le : lt a b ==> le a b   (lt a b = le (Suc a) b; witness p -> b=Suc a+p=a+Suc p) *)
val lt_imp_le =
  let
    val aF = Free("a",natT); val bF = Free("b",natT);
    val hypP = jT (lt aF bF);   (* le (Suc a) b *)
    val hlt  = Thm.assume (ctermTH hypP);
    val goalC = le aF bF;
    val Pabs = Abs("p", natT, oeq bF (add (suc aF) (Bound 0)));
    fun body p (hp:thm) =       (* hp : oeq b (add (Suc a) p) *)
      let
        val aS = addSuc_t (aF, p)            (* (Suc a + p)=Suc(a+p) *)
        val b_Sap = oeqTrans_t (hp, aS)      (* b=Suc(a+p) *)
        val aSp = addSucr_t (aF, p)          (* (a+Suc p)=Suc(a+p) *)
        val b_aSp = oeqTrans_t (b_Sap, oeqSym_t aSp)  (* b=(a+Suc p) *)
      in le_intro_t (aF, bF, suc p) b_aSp end
    val res = exE_t (Pabs, goalC) hlt "pL" body
  in varify (Thm.implies_intr (ctermTH hypP) res) end;
val () = if length (Thm.hyps_of lt_imp_le) = 0 then out "OK lt_imp_le\n" else out "FAIL lt_imp_le\n";
fun lt_imp_le_t (at,bt) hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH
      [(("a",0), ctermTH at),(("b",0), ctermTH bt)] lt_imp_le)) hlt;

(* sq_mono : le a b ==> le (mult a a) (mult b b)
   mult_le_mono: le j k ==> le (c*j)(c*k).  a*a <= a*b (c=a) ; a*b<=b*b needs (a*b=b*a, b*a<=b*b) *)
val sq_mono =
  let
    val aF = Free("a",natT); val bF = Free("b",natT);
    val hypP = jT (le aF bF);
    val hle  = Thm.assume (ctermTH hypP);
    (* a*a <= a*b *)
    val le_aa_ab = mult_le_mono_t (aF, aF, bF) hle;       (* le (a*a)(a*b) *)
    (* a*b <= b*b : first b*a<=b*b (c=b), then a*b=b*a *)
    val le_ba_bb = mult_le_mono_t (bF, aF, bF) hle;       (* le (b*a)(b*b) *)
    val ab_ba = multcomm_t (aF, bF);                       (* (a*b)=(b*a) *)
    (* rewrite le (b*a)(b*b) to le (a*b)(b*b) via oeq_subst on first arg.
       NOTE: `le` builds an inner Ex(Abs ...), so the predicate MUST use a fresh
       Free via Term.lambda, NOT Abs(...,Bound 0) (the inner Ex binder captures it). *)
    val zSQ = Free("zSQ", natT);
    val Pabs = Term.lambda zSQ (le zSQ (mult bF bF));
    val ba_ab = oeqSym_t ab_ba;                            (* (b*a)=(a*b) *)
    val le_ab_bb = oeq_rw_t (Pabs, mult bF aF, mult aF bF) ba_ab le_ba_bb;  (* le (a*b)(b*b) *)
    val res = le_trans_t (mult aF aF, mult aF bF, mult bF bF) le_aa_ab le_ab_bb;
  in varify (Thm.implies_intr (ctermTH hypP) res) end;
val () = if length (Thm.hyps_of sq_mono) = 0 then out "OK sq_mono\n" else out "FAIL sq_mono\n";
fun sq_mono_t (at,bt) hle =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH
      [(("a",0), ctermTH at),(("b",0), ctermTH bt)] sq_mono)) hle;

val () = out "THUE_ORDER_HELPERS_DONE\n";

(* ============================================================================
   PIECE (1): INTEGER FLOOR-SQRT EXISTENCE
   floor_sqrt : !n. ?s. le (mult s s) n  /\  lt n (mult (Suc s) (Suc s))
   by induction on n.
   ============================================================================ *)

(* helper sq_lt_succ : lt (mult m m) (mult (Suc m) (Suc m))   [for any m]
   (Suc m)*(Suc m) = (Suc m) + m*(Suc m)           [mult_Suc, n:=Suc m]
                   = (Suc m) + (m + m*m)            [mult_Suc_right: m*(Suc m)=m+m*m]
                   = Suc (m + (m + m*m))            [addSuc]
                   = Suc ((m+m) + m*m)              [assoc: m+(m+m*m)=(m+m)+m*m]
                   = Suc (m*m + (m+m))              [comm]
                   = Suc(m*m) + (m+m)               [addSuc back]
   so witness p = m+m gives lt (m*m) ((Suc m)^2). *)
val sq_lt_succ =
  let
    val mF = Free("m", natT);
    val Sm = suc mF;
    val sq_Sm = mult Sm Sm;
    (* (Suc m)*(Suc m) = (Suc m) + m*(Suc m) *)
    val e1 = multSuc_t (mF, Sm);                          (* (Suc m * Suc m) = (Suc m + m*Suc m) *)
    (* m*(Suc m) = m + m*m *)
    val e2 = multSucr_t (mF, mF);                          (* (m * Suc m) = (m + m*m) *)
    (* (Suc m + m*Suc m) = (Suc m + (m + m*m)) *)
    val e3 = add_cong_r_t (Sm, mult mF Sm, add mF (mult mF mF)) e2;
    val chain1 = oeqTrans_t (e1, e3);                     (* (Suc m)^2 = (Suc m) + (m + m*m) *)
    (* (Suc m) + (m + m*m) = Suc (m + (m + m*m)) *)
    val e4 = addSuc_t (mF, add mF (mult mF mF));           (* (Suc m + X) = Suc (m + X) where X=m+m*m *)
    val chain2 = oeqTrans_t (chain1, e4);                 (* (Suc m)^2 = Suc (m + (m + m*m)) *)
    (* inside Suc: m + (m + m*m) = (m + m) + m*m  [assoc backwards]
       add_assoc : (m + n) + k = m + (n + k).  Here want m+(m+m*m)=(m+m)+m*m, i.e. sym of assoc with
       m,n:=m,k:=m*m :  (m+m)+m*m = m+(m+m*m).  take sym. *)
    val assoc = addassoc_t (mF, mF, mult mF mF);          (* ((m+m)+m*m) = (m+(m+m*m)) *)
    val assoc_s = oeqSym_t assoc;                         (* (m+(m+m*m)) = ((m+m)+m*m) *)
    (* (m+m)+m*m = m*m + (m+m)   [comm] *)
    val comm = addcomm_t (add mF mF, mult mF mF);         (* ((m+m)+m*m) = (m*m+(m+m)) *)
    val inner = oeqTrans_t (assoc_s, comm);              (* (m+(m+m*m)) = (m*m+(m+m)) *)
    val inner_S = Suc_cong_t inner;                       (* Suc(m+(m+m*m)) = Suc(m*m+(m+m)) *)
    val chain3 = oeqTrans_t (chain2, inner_S);           (* (Suc m)^2 = Suc(m*m+(m+m)) *)
    (* Suc(m*m + (m+m)) = (Suc(m*m)) + (m+m)  [addSuc back: (Suc(m*m) + (m+m)) = Suc(m*m+(m+m))] *)
    val e5 = addSuc_t (mult mF mF, add mF mF);            (* (Suc(m*m) + (m+m)) = Suc(m*m + (m+m)) *)
    val e5s = oeqSym_t e5;                                (* Suc(m*m+(m+m)) = (Suc(m*m) + (m+m)) *)
    val finalEq = oeqTrans_t (chain3, e5s);              (* (Suc m)^2 = (Suc(m*m) + (m+m)) *)
    (* le (Suc(m*m)) ((Suc m)^2) with witness (m+m) = lt (m*m) ((Suc m)^2) *)
    val ltThm = le_intro_t (suc (mult mF mF), sq_Sm, add mF mF) finalEq;
  in varify ltThm end;
val () = if length (Thm.hyps_of sq_lt_succ) = 0 then out "OK sq_lt_succ\n" else out "FAIL sq_lt_succ\n";
fun sq_lt_succ_t mt = beta_norm (Drule.infer_instantiate ctxtTH [(("m",0), ctermTH mt)] sq_lt_succ);

(* le_self_suc : le n (Suc n)  (witness 1: Suc n = n + 1 = n + Suc 0) *)
fun le_self_suc_t nt =
  let val aSr = addSucr_t (nt, ZeroC)        (* (n + Suc 0) = Suc(n+0) *)
      val a0r = add0r_t nt                    (* (n+0)=n *)
      val sa0r= Suc_cong_t a0r                (* Suc(n+0)=Suc n *)
      val sum = oeqTrans_t (aSr, sa0r)        (* (n + Suc 0) = Suc n *)
      val sumS= oeqSym_t sum                  (* Suc n = (n + Suc 0) *)
  in le_intro_t (nt, suc nt, suc ZeroC) sumS end;

val floor_sqrt =
  let
    val nVar = Free("n_fs", natT);
    val sqbody = fn s => fn k => mkConj (le (mult s s) k) (lt k (mult (suc s) (suc s)));
    (* P n  ==  ?s. le (s*s) n /\ lt n ((Suc s)^2) ;  body abstraction over s *)
    fun exBody k = Term.lambda (Free("s_w", natT))
                     (mkConj (le (mult (Free("s_w",natT)) (Free("s_w",natT))) k)
                             (lt k (mult (suc (Free("s_w",natT))) (suc (Free("s_w",natT))))));
    val Pabs = Term.lambda nVar (mkEx (exBody nVar));
    (* ---- base : n = 0, witness s = 0 ---- *)
    val base =
      let
        (* le (0*0) 0 :  0*0 = 0 (mult0), le 0 0 (le_refl), rewrite first arg back *)
        val m00 = mult0_t ZeroC;                       (* (0*0) = 0 *)
        val le00 = le_refl_t ZeroC;                    (* le 0 0 *)
        val zLE = Free("zLEb", natT);
        val Ple = Term.lambda zLE (le zLE ZeroC);
        val m00s = oeqSym_t m00;                       (* 0 = (0*0) *)
        val le_00_0 = oeq_rw_t (Ple, ZeroC, mult ZeroC ZeroC) m00s le00;  (* le (0*0) 0 *)
        (* lt 0 ((Suc 0)^2) : sq_lt_succ at m=0 gives lt (0*0)((Suc 0)^2); rewrite 0*0 -> 0 in the lt's lower arg.
           lt x y = le (Suc x) y ; rewriting x changes Suc x. Use oeq_subst on %z. lt z ((Suc 0)^2). *)
        val lt0sq0 = sq_lt_succ_t ZeroC;               (* lt (0*0) ((Suc 0)^2) *)
        val zLT = Free("zLTb", natT);
        val Plt = Term.lambda zLT (lt zLT (mult (suc ZeroC) (suc ZeroC)));
        val lt_0_sq = oeq_rw_t (Plt, mult ZeroC ZeroC, ZeroC) m00 lt0sq0;  (* lt 0 ((Suc 0)^2) *)
        val cj = conjI_t (le (mult ZeroC ZeroC) ZeroC, lt ZeroC (mult (suc ZeroC) (suc ZeroC))) le_00_0 lt_0_sq;
      in exI_t (exBody ZeroC) ZeroC cj end;
    (* ---- step : assume P x, prove P (Suc x) ---- *)
    val step =
      let
        val xF = Free("x_fs", natT)
        val ihP = jT (mkEx (exBody xF))
        val hIH = Thm.assume (ctermTH ihP)
        val goalC = mkEx (exBody (suc xF))
        fun body s (hs:thm) =     (* hs : le (s*s) x /\ lt x ((Suc s)^2) *)
          let
            val sq_s = mult s s
            val sq_Ss = mult (suc s) (suc s)
            val sq_SSs = mult (suc (suc s)) (suc (suc s))
            val hle_sq_x = conjunct1_t (le sq_s xF, lt xF sq_Ss) hs    (* le (s*s) x *)
            val hlt_x    = conjunct2_t (le sq_s xF, lt xF sq_Ss) hs    (* lt x ((Suc s)^2) *)
            (* le (s*s) (Suc x) via le_trans with le x (Suc x) *)
            val le_x_Sx = le_self_suc_t xF
            val le_sq_Sx = le_trans_t (sq_s, xF, suc xF) hle_sq_x le_x_Sx   (* le (s*s)(Suc x) *)
            (* lt x ((Suc s)^2) = le (Suc x) ((Suc s)^2).  cases via le_eq_or_lt *)
            val hle_Sx_sqSs = hlt_x    (* same term: lt x y = le (Suc x) y *)
            val dj = le_eq_or_lt_t (suc xF, sq_Ss) hle_Sx_sqSs  (* Disj (oeq (Suc x)((Suc s)^2)) (lt (Suc x)((Suc s)^2)) *)
            (* case lt (Suc x)((Suc s)^2): keep s *)
            val caseLt =
              let val hlt = Thm.assume (ctermTH (jT (lt (suc xF) sq_Ss)))   (* = lt (Suc x)((Suc s)^2) but we need lt (Suc x)((Suc s)^2) as the second conjunct *)
                  val cj = conjI_t (le sq_s (suc xF), lt (suc xF) sq_Ss) le_sq_Sx hlt
                  val ex = exI_t (exBody (suc xF)) s cj
              in Thm.implies_intr (ctermTH (jT (lt (suc xF) sq_Ss))) ex end
            (* case oeq (Suc x)((Suc s)^2): use s' = Suc s *)
            val caseEq =
              let val heq = Thm.assume (ctermTH (jT (oeq (suc xF) sq_Ss)))   (* Suc x = (Suc s)^2 *)
                  val heq_s = oeqSym_t heq                                    (* (Suc s)^2 = Suc x *)
                  (* le ((Suc s)^2)(Suc x): le_refl(Suc x) then rewrite first arg (Suc x)->(Suc s)^2 *)
                  val leRefl = le_refl_t (suc xF)                             (* le (Suc x)(Suc x) *)
                  val zL = Free("zL_eq", natT)
                  val Ple2 = Term.lambda zL (le zL (suc xF))
                  val le_lhs = oeq_rw_t (Ple2, suc xF, sq_Ss) heq leRefl      (* P=%z.le z (Suc x); a:=Suc x,b:=(Suc s)^2; heq:oeq(Suc x)((Suc s)^2); P(Suc x)=leRefl => P((Suc s)^2)=le ((Suc s)^2)(Suc x) *)
                  (* lt (Suc x) ((Suc(Suc s))^2): sq_lt_succ at m=Suc s gives lt ((Suc s)^2)((Suc(Suc s))^2);
                     rewrite the lower arg (Suc s)^2 -> Suc x via heq. lt z ((..)^2) rewriting z. *)
                  val ltSqSs = sq_lt_succ_t (suc s)                          (* lt ((Suc s)^2)((Suc(Suc s))^2) *)
                  val zL2 = Free("zL_lt", natT)
                  val Plt2 = Term.lambda zL2 (lt zL2 sq_SSs)
                  val lt_Sx = oeq_rw_t (Plt2, sq_Ss, suc xF) heq_s ltSqSs     (* P=%z.lt z sq_SSs; a:=(Suc s)^2,b:=Suc x; heq_s:oeq ((Suc s)^2)(Suc x); P((Suc s)^2)=ltSqSs => P(Suc x)=lt (Suc x) sq_SSs *)
                  val cj = conjI_t (le (mult (suc s)(suc s)) (suc xF), lt (suc xF) sq_SSs) le_lhs lt_Sx
                  val ex = exI_t (exBody (suc xF)) (suc s) cj
              in Thm.implies_intr (ctermTH (jT (oeq (suc xF) sq_Ss))) ex end
            val res = disjE_t (oeq (suc xF) sq_Ss, lt (suc xF) sq_Ss, goalC) dj caseEq caseLt
          in res end
        val res = exE_t (exBody xF, goalC) hIH "s_ih" body
      in Thm.forall_intr (ctermTH xF) (Thm.implies_intr (ctermTH ihP) res) end;
    val kF = Free("k_fs", natT)
    val concl = nat_induct_t Pabs kF base step    (* P k for schematic k *)
  in varify concl end;
val () = if length (Thm.hyps_of floor_sqrt) = 0 then out "OK floor_sqrt (0-hyp)\n" else out ("FAIL floor_sqrt hyps="^Int.toString (length (Thm.hyps_of floor_sqrt))^"\n");
val () = out ("floor_sqrt : "^Syntax.string_of_term ctxtTH (Thm.prop_of floor_sqrt)^"\n");
val () = out "THUE_SQRT_DONE\n";

(* ============================================================================
   PIECE (3): THE GRID RANGE LIST  rangelist m = [m-1, ..., 1, 0]
   (members exactly {0,..,m-1}); proven:
     llen_rangelist     : oeq (llen (rangelist m)) m
     lnodup_rangelist   : lnodup (rangelist m)
     lmem_rangelist_fwd : lmem i (rangelist m) ==> lt i m
     lmem_rangelist_bwd : lt i m ==> lmem i (rangelist m)
   ============================================================================ *)

(* leq-transfer of lnodup / lmem through rangelist's leq axioms *)
fun lnodup_transfer_t (aT,bT) hleq hnd =
  let val zN = Free("zND", natlistT)
      val Pabs = Term.lambda zN (lnodup zN)
  in leq_rw_t (Pabs, aT, bT) hleq hnd end;
fun lmem_transfer_t (yT, aT, bT) hleq hmem =
  let val zN = Free("zMM", natlistT)
      val Pabs = Term.lambda zN (lmem yT zN)
  in leq_rw_t (Pabs, aT, bT) hleq hmem end;

(* ---- llen_rangelist : oeq (llen (rangelist m)) m   (induction on m) ---- *)
val llen_rangelist =
  let
    val mVar = Free("m_lr", natT)
    val Pabs = Term.lambda mVar (oeq (llen (rangelist mVar)) mVar)
    val base =
      let
        val r0 = rangelistZero_t ()                       (* leq (rangelist 0) lnil *)
        (* llen (rangelist 0) = llen lnil = 0 ; rewrite via leq on %z. oeq (llen z) 0 *)
        val llenNil = llenNil_t ()                        (* oeq (llen lnil) 0 *)
        val zN = Free("zb", natlistT)
        val Pll = Term.lambda zN (oeq (llen zN) ZeroC)
        val r0s = leq_sym_t r0                             (* leq lnil (rangelist 0) *)
        val res = leq_rw_t (Pll, lnilC, rangelist ZeroC) r0s llenNil  (* oeq (llen (rangelist 0)) 0 *)
      in res end
    val step =
      let
        val xF = Free("x_lr", natT)
        val ihP = jT (oeq (llen (rangelist xF)) xF)
        val hIH = Thm.assume (ctermTH ihP)
        val rSuc = rangelistSuc_t xF                       (* leq (rangelist (Suc x)) (lcons x (rangelist x)) *)
        (* llen (rangelist (Suc x)) = llen (lcons x (rangelist x)) = Suc (llen (rangelist x)) = Suc x *)
        val llenCons = llenCons_t (xF, rangelist xF)       (* oeq (llen (lcons x (rangelist x))) (Suc (llen (rangelist x))) *)
        val sucIH = Suc_cong_t hIH                          (* oeq (Suc (llen (rangelist x))) (Suc x) *)
        val eqCons = oeqTrans_t (llenCons, sucIH)           (* oeq (llen (lcons x (rangelist x))) (Suc x) *)
        (* rewrite llen (lcons ..) -> llen (rangelist (Suc x)) via rSuc on %z. oeq (llen z) (Suc x) *)
        val zN = Free("zs", natlistT)
        val Pll = Term.lambda zN (oeq (llen zN) (suc xF))
        val rSuc_s = leq_sym_t rSuc                         (* leq (lcons x (rangelist x)) (rangelist (Suc x)) *)
        val res = leq_rw_t (Pll, lcons xF (rangelist xF), rangelist (suc xF)) rSuc_s eqCons
      in Thm.forall_intr (ctermTH xF) (Thm.implies_intr (ctermTH ihP) res) end
    val kF = Free("k_lr", natT)
    val concl = nat_induct_t Pabs kF base step
  in varify concl end;
val () = if length (Thm.hyps_of llen_rangelist) = 0 then out "OK llen_rangelist (0-hyp)\n" else out "FAIL llen_rangelist\n";
fun llen_rangelist_t mt = beta_norm (Drule.infer_instantiate ctxtTH [(("k_lr",0), ctermTH mt)] llen_rangelist);

(* ---- lmem_rangelist_fwd : lmem i (rangelist m) ==> lt i m   (induction on m) ---- *)
val lmem_rangelist_fwd =
  let
    val iF = Free("i_rf", natT)
    val mVar = Free("m_rf", natT)
    val Pabs = Term.lambda mVar (mkImp (lmem iF (rangelist mVar)) (lt iF mVar))
    val base =
      let
        val goalC = lt iF ZeroC
        val hmemP = jT (lmem iF (rangelist ZeroC))
        val hmem  = Thm.assume (ctermTH hmemP)
        val r0    = rangelistZero_t ()                     (* leq (rangelist 0) lnil *)
        val memNil= lmem_transfer_t (iF, rangelist ZeroC, lnilC) r0 hmem  (* lmem i lnil *)
        val fls   = Thm.implies_elim (lmemNilElim_t iF) memNil            (* oFalse *)
        val res   = Thm.implies_elim (oFalse_elim_t goalC) fls
      in impI_t (lmem iF (rangelist ZeroC), goalC) (Thm.implies_intr (ctermTH hmemP) res) end
    val step =
      let
        val xF = Free("x_rf", natT)
        val ihP = jT (mkImp (lmem iF (rangelist xF)) (lt iF xF))
        val hIH = Thm.assume (ctermTH ihP)
        val goalC = lt iF (suc xF)
        val hmemP = jT (lmem iF (rangelist (suc xF)))
        val hmem  = Thm.assume (ctermTH hmemP)
        val rSuc  = rangelistSuc_t xF                      (* leq (rangelist (Suc x)) (lcons x (rangelist x)) *)
        val memCons = lmem_transfer_t (iF, rangelist (suc xF), lcons xF (rangelist xF)) rSuc hmem  (* lmem i (lcons x (rangelist x)) *)
        val dj = Thm.implies_elim (lmemConsFwd_t (iF, xF, rangelist xF)) memCons  (* Disj (oeq i x) (lmem i (rangelist x)) *)
        (* case oeq i x : lt i (Suc x) since i=x and lt x (Suc x) *)
        val caseEq =
          let val heq = Thm.assume (ctermTH (jT (oeq iF xF)))         (* i = x *)
              val ltx = lt_suc_t xF                                    (* lt x (Suc x) = le (Suc x)(Suc x) *)
              (* rewrite x -> i in lt x (Suc x): %z. lt z (Suc x); a:=x,b:=i needs oeq x i = sym heq *)
              val heq_s = oeqSym_t heq                                 (* x = i *)
              val zL = Free("zLrf", natT)
              val Plt = Term.lambda zL (lt zL (suc xF))
              val lti = oeq_rw_t (Plt, xF, iF) heq_s ltx               (* lt i (Suc x) *)
          in Thm.implies_intr (ctermTH (jT (oeq iF xF))) lti end
        (* case lmem i (rangelist x) : lt i x by IH, then lt i (Suc x) by lt_trans with lt x (Suc x) *)
        val caseMem =
          let val hmemx = Thm.assume (ctermTH (jT (lmem iF (rangelist xF))))
              val ltix  = mp_t (lmem iF (rangelist xF), lt iF xF) hIH hmemx  (* lt i x *)
              val ltxSx = lt_suc_t xF                                       (* lt x (Suc x) *)
              val lti_Sx= lt_trans_t (iF, xF, suc xF) ltix ltxSx             (* lt i (Suc x) *)
          in Thm.implies_intr (ctermTH (jT (lmem iF (rangelist xF)))) lti_Sx end
        val ltThm = disjE_t (oeq iF xF, lmem iF (rangelist xF), goalC) dj caseEq caseMem
        val impThm = impI_t (lmem iF (rangelist (suc xF)), goalC)
                       (Thm.implies_intr (ctermTH hmemP) ltThm)
      in Thm.forall_intr (ctermTH xF) (Thm.implies_intr (ctermTH ihP) impThm) end
    val kF = Free("k_rf", natT)
    val concl = nat_induct_t Pabs kF base step
  in varify concl end;
val () = if length (Thm.hyps_of lmem_rangelist_fwd) = 0 then out "OK lmem_rangelist_fwd (0-hyp)\n" else out "FAIL lmem_rangelist_fwd\n";
fun lmem_rangelist_fwd_t (it,mt) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtTH
        [(("i_rf",0), ctermTH it),(("k_rf",0), ctermTH mt)] lmem_rangelist_fwd)
  in mp_t (lmem it (rangelist mt), lt it mt) inst hmem end;

(* ---- lmem_rangelist_bwd : lt i m ==> lmem i (rangelist m)   (induction on m) ---- *)
(* lt i 0 is impossible; lt i (Suc x) gives Disj (lt i x)(oeq i x) by lt_suc_cases:
     lt i x  -> lmem i (rangelist x) by IH -> in cons tail
     oeq i x -> head match. *)
val lmem_rangelist_bwd =
  let
    val iF = Free("i_rb", natT)
    val mVar = Free("m_rb", natT)
    val Pabs = Term.lambda mVar (mkImp (lt iF mVar) (lmem iF (rangelist mVar)))
    val base =
      let
        val goalC = lmem iF (rangelist ZeroC)
        val hltP = jT (lt iF ZeroC)            (* le (Suc i) 0 *)
        val hlt  = Thm.assume (ctermTH hltP)
        (* lt i 0 = le (Suc i) 0 = Ex(%p. 0 = Suc i + p). exE -> Suc i + p = 0 -> contradiction *)
        val Pd = Abs("p", natT, oeq ZeroC (add (suc iF) (Bound 0)))
        fun bd p (hp:thm) =        (* hp : oeq 0 (add (Suc i) p) *)
          let val aS = addSuc_t (iF, p)                   (* (Suc i + p)=Suc(i+p) *)
              val z_S = oeqTrans_t (hp, aS)               (* 0 = Suc(i+p) *)
              val S_z = oeqSym_t z_S                       (* Suc(i+p) = 0 *)
              val fls = Suc_neq_Zero_t (add iF p) S_z      (* oFalse *)
          in Thm.implies_elim (oFalse_elim_t goalC) fls end
        val resmem = exE_t (Pd, goalC) hlt "p_b0" bd
      in impI_t (lt iF ZeroC, goalC) (Thm.implies_intr (ctermTH hltP) resmem) end
    val step =
      let
        val xF = Free("x_rb", natT)
        val ihP = jT (mkImp (lt iF xF) (lmem iF (rangelist xF)))
        val hIH = Thm.assume (ctermTH ihP)
        val goalC = lmem iF (rangelist (suc xF))
        val hltP = jT (lt iF (suc xF))
        val hlt  = Thm.assume (ctermTH hltP)
        val dj = lt_suc_cases_t (iF, xF) hlt              (* Disj (lt i x)(oeq i x) *)
        val rSuc = rangelistSuc_t xF                      (* leq (rangelist (Suc x)) (lcons x (rangelist x)) *)
        val rSuc_s = leq_sym_t rSuc                       (* leq (lcons x (rangelist x)) (rangelist (Suc x)) *)
        val consL = lcons xF (rangelist xF)
        val zN = Free("zN_rb", natlistT)
        val Pmem = Term.lambda zN (lmem iF zN)
        (* case lt i x : IH gives lmem i (rangelist x), then in tail of cons *)
        val caseLt =
          let val hltx = Thm.assume (ctermTH (jT (lt iF xF)))
              val memx = mp_t (lt iF xF, lmem iF (rangelist xF)) hIH hltx  (* lmem i (rangelist x) *)
              val dmem = disjI2_t (oeq iF xF, lmem iF (rangelist xF)) memx (* Disj (oeq i x)(lmem i (rangelist x)) *)
              val memCons = Thm.implies_elim (lmemConsBwd_t (iF, xF, rangelist xF)) dmem  (* lmem i (lcons x (rangelist x)) *)
              val res = leq_rw_t (Pmem, consL, rangelist (suc xF)) rSuc_s memCons
          in Thm.implies_intr (ctermTH (jT (lt iF xF))) res end
        (* case oeq i x : head match *)
        val caseEq =
          let val heq = Thm.assume (ctermTH (jT (oeq iF xF)))
              val dmem = disjI1_t (oeq iF xF, lmem iF (rangelist xF)) heq
              val memCons = Thm.implies_elim (lmemConsBwd_t (iF, xF, rangelist xF)) dmem
              val res = leq_rw_t (Pmem, consL, rangelist (suc xF)) rSuc_s memCons
          in Thm.implies_intr (ctermTH (jT (oeq iF xF))) res end
        val memThm = disjE_t (lt iF xF, oeq iF xF, goalC) dj caseLt caseEq
        val impThm = impI_t (lt iF (suc xF), goalC)
                       (Thm.implies_intr (ctermTH hltP) memThm)
      in Thm.forall_intr (ctermTH xF) (Thm.implies_intr (ctermTH ihP) impThm) end
    val kF = Free("k_rb", natT)
    val concl = nat_induct_t Pabs kF base step
  in varify concl end;
val () = if length (Thm.hyps_of lmem_rangelist_bwd) = 0 then out "OK lmem_rangelist_bwd (0-hyp)\n" else out "FAIL lmem_rangelist_bwd\n";
fun lmem_rangelist_bwd_t (it,mt) hlt =
  let val inst = beta_norm (Drule.infer_instantiate ctxtTH
        [(("i_rb",0), ctermTH it),(("k_rb",0), ctermTH mt)] lmem_rangelist_bwd)
  in mp_t (lt it mt, lmem it (rangelist mt)) inst hlt end;

(* ---- lnodup_rangelist : lnodup (rangelist m)   (induction on m; x not in rangelist x) ---- *)
val lnodup_rangelist =
  let
    val mVar = Free("m_nd", natT)
    val Pabs = Term.lambda mVar (lnodup (rangelist mVar))
    val base =
      let
        val r0 = rangelistZero_t ()                       (* leq (rangelist 0) lnil *)
        val r0s = leq_sym_t r0                             (* leq lnil (rangelist 0) *)
        val ndNil = lnodupNil_t                            (* lnodup lnil *)
      in lnodup_transfer_t (lnilC, rangelist ZeroC) r0s ndNil end
    val step =
      let
        val xF = Free("x_nd", natT)
        val ihP = jT (lnodup (rangelist xF))
        val hIH = Thm.assume (ctermTH ihP)
        (* x not a member of rangelist x : if it were, lt x x by fwd -> lt_irrefl *)
        val notmem =
          let val hmem = Thm.assume (ctermTH (jT (lmem xF (rangelist xF))))
              val ltxx = lmem_rangelist_fwd_t (xF, xF) hmem    (* lt x x *)
              val fls  = lt_irrefl_t xF ltxx
              val metaImp = Thm.implies_intr (ctermTH (jT (lmem xF (rangelist xF)))) fls
          in impI_t (lmem xF (rangelist xF), oFalseC) metaImp end
        val conjND = conjI_t (neg (lmem xF (rangelist xF)), lnodup (rangelist xF)) notmem hIH
        val ndCons = Thm.implies_elim (lnodupConsBwd_t (xF, rangelist xF)) conjND  (* lnodup (lcons x (rangelist x)) *)
        val rSuc = rangelistSuc_t xF
        val rSuc_s = leq_sym_t rSuc
        val res = lnodup_transfer_t (lcons xF (rangelist xF), rangelist (suc xF)) rSuc_s ndCons
      in Thm.forall_intr (ctermTH xF) (Thm.implies_intr (ctermTH ihP) res) end
    val kF = Free("k_nd", natT)
    val concl = nat_induct_t Pabs kF base step
  in varify concl end;
val () = if length (Thm.hyps_of lnodup_rangelist) = 0 then out "OK lnodup_rangelist (0-hyp)\n" else out "FAIL lnodup_rangelist\n";
fun lnodup_rangelist_t mt = beta_norm (Drule.infer_instantiate ctxtTH [(("k_nd",0), ctermTH mt)] lnodup_rangelist);

val () = out "THUE_GRID_DONE\n";

(* ============================================================================
   PIECE (2): THE LIST-PIGEONHOLE LEMMA.
   Foundation (on ctxtL2): a HAND-ROLLED two-list strong induction giving
     sublist_len_le : lnodup IL ==> (!e. lmem e IL ==> lmem e RL) ==> le (llen IL)(llen RL)
   (a dup-free list injects into any superset, so is no longer than it).  Because
   the superset RL SHRINKS as we recurse (we remove the matched head), it cannot be
   a fixed Free in the (list-keyed) harness; so we drive meta_nat_induct on llen IL
   directly with the conclusion META-universally quantified over RL.
   ============================================================================ *)

(* small _2 helpers we still need *)
val zero_le_v2b = varify zero_le;
fun zero_le_2 t = beta_norm (Drule.infer_instantiate ctxtL2 [(("n",0), ctermL2 t)] zero_le_v2b);
val llen_nil_v2b = varify llen_nil_ax;
fun llenNil_2 () = llen_nil_v2b;
fun leq_sym_2 h = leq_sym OF [h];
val le_suc_mono_v2  = varify le_suc_mono;
fun le_suc_mono_2 (mt,nt) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("m",0), ctermL2 mt),(("n",0), ctermL2 nt)] le_suc_mono_v2)) h;
val llen_remove_eq_v2 = varify llen_remove_eq;
fun llen_remove_eq_2 (xt, Lt) hmem =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 xt),(("L",0), ctermL2 Lt)] llen_remove_eq_v2)) hmem;
val meta_nat_induct_v2b = varify meta_nat_induct_ax2;
val lnodup_cons_fwd_v2b = varify lnodup_cons_fwd_ax;
fun lnodupConsFwd_2 (x,t) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 x),(("t",0), ctermL2 t)] lnodup_cons_fwd_v2b);
fun oeqSym_2 h = oeq_sym OF [h];
fun oeqTrans_2 (h1,h2) = oeq_trans OF [h1, h2];
val add_Suc_v2 = varify add_Suc;
fun addSuc_2 (mt,nt) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("m",0), ctermL2 mt),(("n",0), ctermL2 nt)] add_Suc_v2);
val Suc_inj_v2 = varify Suc_inj_ax;
fun Suc_inj_2 (at,bt) heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("a",0), ctermL2 at),(("b",0), ctermL2 bt)] Suc_inj_v2)) heq;
val exI_v2 = varify exI_ax;
fun le_intro_2 (mT,nT,w) hyp =
  let val Pabs = Abs("p", natT, oeq nT (add mT (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtL2
            [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 w)] exI_v2)
  in inst OF [hyp] end;
val exE_v2 = varify exE_ax;
fun exE_2 (Pabs, goalC) exThm wName bodyFn =
  let val wF = Free(wName, natT)
      val hypTerm = jT (Term.betapply (Pabs, wF))
      val hypThm  = Thm.assume (ctermL2 hypTerm)
      val body    = bodyFn wF hypThm
      val minor   = Thm.forall_intr (ctermL2 wF) (Thm.implies_intr (ctermL2 hypTerm) body)
      val exE_inst= beta_norm (Drule.infer_instantiate ctxtL2
                      [(("P",0), ctermL2 Pabs),(("Q",0), ctermL2 goalC)] exE_v2)
  in Thm.implies_elim (Thm.implies_elim exE_inst exThm) minor end;
(* le_suc_cancel : le (Suc a)(Suc b) ==> le a b
   le (Suc a)(Suc b) = Ex(%p. Suc b = Suc a + p = Suc(a+p)); Suc_inj -> b = a+p -> le a b *)
val le_suc_cancel =
  let
    val aF = Free("a", natT); val bF = Free("b", natT)
    val hypP = jT (le (suc aF) (suc bF))
    val hle  = Thm.assume (ctermL2 hypP)
    val goalC = le aF bF
    val Pabs = Abs("p", natT, oeq (suc bF) (add (suc aF) (Bound 0)))
    fun body p (hp:thm) =        (* hp : oeq (Suc b)(add (Suc a) p) *)
      let val aS = addSuc_2 (aF, p)                  (* (Suc a + p) = Suc(a+p) *)
          val Sb_Sap = oeqTrans_2 (hp, aS)           (* Suc b = Suc(a+p) *)
          val b_ap = Suc_inj_2 (bF, add aF p) Sb_Sap (* b = a+p *)
      in le_intro_2 (aF, bF, p) b_ap end
    val res = exE_2 (Pabs, goalC) hle "p_lsc" body
  in varify (Thm.implies_intr (ctermL2 hypP) res) end;
fun le_suc_cancel_2 (at,bt) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("a",0), ctermL2 at),(("b",0), ctermL2 bt)] le_suc_cancel)) h;

(* sublist_len_le proper: meta_nat_induct on n with
     aux n = !!IL. lt (llen IL) n ==> !!RL. lnodup IL ==> (IL subset RL) ==> le (llen IL)(llen RL) *)
fun subBody il rl =       (* object: lnodup il ==> (il subset rl) ==> le (llen il)(llen rl) *)
  let val ef = Free("e_sub", natT)
      val memIn = mkForall (Term.lambda ef (mkImp (lmem ef il) (lmem ef rl)))
  in mkImp (lnodup il) (mkImp memIn (le (llen il)(llen rl))) end;
fun subMetaRL il =        (* prop: !!RL. jT(subBody il RL) -- but subBody is one object impl, so wrap once *)
  let val RLm = Free("RL_m", natlistT)
  in Logic.all RLm (jT (subBody il RLm)) end;
fun subAux n =            (* prop: !!IL. lt (llen IL) n ==> (!!RL. jT(subBody IL RL)) *)
  let val ILm = Free("IL_m", natlistT)
  in Logic.all ILm (Logic.mk_implies (jT (lt (llen ILm) n), subMetaRL ILm)) end;

(* useMemIn : from (!e. lmem e il ==> lmem e rl) and (lmem z il) get (lmem z rl) *)
fun useMemIn (il,rl) hMem z (hm:thm) =
  let val ef = Free("e_sub", natT)
      val Pabs = Term.lambda ef (mkImp (lmem ef il) (lmem ef rl))
      val inst = allE_2 Pabs z hMem
  in mp_2 (lmem z il, lmem z rl) inst hm end;

val sublist_len_le =
  let
    val nSubF = Free("n_sub", natT)
    val PhiAbs = Term.lambda nSubF (subAux nSubF)
    (* base : aux 0 : !!IL. lt (llen IL) 0 ==> ...   (lt _ 0 impossible) *)
    val base =
      let val ILb = Free("IL_b", natlistT)
          val hlt = Thm.assume (ctermL2 (jT (lt (llen ILb) ZeroC)))
          (* conclusion needed : subMetaRL ILb = !!RL. jT(subBody ILb RL) ; derive from False *)
          val RLb = Free("RL_b", natlistT)
          val falseElim = lt_zero_elim_2 (llen ILb) (subBody ILb RLb) hlt   (* jT(subBody ILb RLb) from absurd *)
          val metaRL = Thm.forall_intr (ctermL2 RLb) falseElim
      in Thm.forall_intr (ctermL2 ILb) (Thm.implies_intr (ctermL2 (jT (lt (llen ILb) ZeroC))) metaRL) end
    (* step : !!x. aux x ==> aux (Suc x) *)
    val step =
      let
        val xS = Free("x_sub", natT)
        val IHaux = Thm.assume (ctermL2 (subAux xS))   (* !!IL. lt(llen IL) x ==> !!RL. jT(subBody IL RL) *)
        (* applyIH : given IL2 with lt (llen IL2) x and an RL2, produce jT(subBody IL2 RL2) *)
        fun applyIH (IL2, RL2) hlt =
          let val s1 = Thm.implies_elim (Thm.forall_elim (ctermL2 IL2) IHaux) hlt  (* !!RL. jT(subBody IL2 RL) *)
          in Thm.forall_elim (ctermL2 RL2) s1 end
        val ILs = Free("IL_s", natlistT)
        val hltS = Thm.assume (ctermL2 (jT (lt (llen ILs) (suc xS))))   (* lt (llen ILs)(Suc x) *)
        (* prove !!RL. jT(subBody ILs RL) *)
        val RLs = Free("RL_s2", natlistT)
        val goalSub = subBody ILs RLs
        (* list_cases on ILs *)
        fun caseNil hnil =     (* hnil : leq ILs lnil *)
          let
            val hND  = Thm.assume (ctermL2 (jT (lnodup ILs)))
            val memIn = let val ef = Free("e_sub", natT) in mkForall (Term.lambda ef (mkImp (lmem ef ILs)(lmem ef RLs))) end
            val hMem = Thm.assume (ctermL2 (jT memIn))
            val llc = llen_cong_2 (ILs, lnilC) hnil
            val lln = llenNil_2 ()
            val llz = oeqTrans_2 (llc, lln)            (* oeq (llen ILs) 0 *)
            val z_le = zero_le_2 (llen RLs)             (* le 0 (llen RL) *)
            val zV = Free("zSLn2", natT)
            val Ple = Term.lambda zV (le zV (llen RLs))
            val llz_s = oeqSym_2 llz
            val leRes = oeq_rw_2 (Ple, ZeroC, llen ILs) llz_s z_le
            val i2 = Thm.implies_intr (ctermL2 (jT memIn)) leRes
            val r2 = impI_2 (memIn, le (llen ILs)(llen RLs)) i2
            val i1 = Thm.implies_intr (ctermL2 (jT (lnodup ILs))) r2
          in impI_2 (lnodup ILs, mkImp memIn (le (llen ILs)(llen RLs))) i1 end
        fun caseCons (a, rest) hcons =     (* hcons : leq ILs (lcons a rest) *)
          let
            val consL = lcons a rest
            val hND  = Thm.assume (ctermL2 (jT (lnodup ILs)))
            val memIn = let val ef = Free("e_sub", natT) in mkForall (Term.lambda ef (mkImp (lmem ef ILs)(lmem ef RLs))) end
            val hMem = Thm.assume (ctermL2 (jT memIn))
            (* lnodup (lcons a rest) *)
            val ndCons = lnodup_transfer_2 (ILs, consL) hcons hND
            val ndConj = Thm.implies_elim (lnodupConsFwd_2 (a, rest)) ndCons
            val a_notin = conjunct1_2 (neg (lmem a rest), lnodup rest) ndConj
            val ndRest  = conjunct2_2 (neg (lmem a rest), lnodup rest) ndConj
            val hcons_s = leq_sym_2 hcons
            (* a in ILs, hence a in RL *)
            val memA_cons = Thm.implies_elim (lmemConsBwd_2 (a, a, rest)) (disjI1_2 (oeq a a, lmem a rest) (oeqRefl_2 a))
            val memA_ILs = lmem_transfer_2 (a, consL, ILs) hcons_s memA_cons
            val memA_RL = useMemIn (ILs, RLs) hMem a memA_ILs       (* lmem a RL *)
            (* RL' = lremove a RL ; llen RL = Suc (llen RL') *)
            val RLp = lremove a RLs
            val llenRLeq = llen_remove_eq_2 (a, RLs) memA_RL          (* oeq (llen RL)(Suc(llen RL')) *)
            (* rest subset RL' *)
            val memInRest =
              let val zf = Free("z_sub2", natT)
                  val PabsM = Term.lambda zf (mkImp (lmem zf rest)(lmem zf RLp))
                  val hzr = Thm.assume (ctermL2 (jT (lmem zf rest)))
                  val z_cons = Thm.implies_elim (lmemConsBwd_2 (zf, a, rest)) (disjI2_2 (oeq zf a, lmem zf rest) hzr)
                  val z_ILs  = lmem_transfer_2 (zf, consL, ILs) hcons_s z_cons
                  val z_RL   = useMemIn (ILs, RLs) hMem zf z_ILs       (* lmem z RL *)
                  val zneqa =
                    let val hza = Thm.assume (ctermL2 (jT (oeq zf a)))
                        val Pr2 = Term.lambda (Free("wlm2",natT)) (lmem (Free("wlm2",natT)) rest)
                        val a_in_rest = oeq_rw_2 (Pr2, zf, a) hza hzr
                        val ff = mp_2 (lmem a rest, oFalseC) a_notin a_in_rest
                    in impI_2 (oeq zf a, oFalseC) (Thm.implies_intr (ctermL2 (jT (oeq zf a))) ff) end
                  val conjBwd = conjI_2 (lmem zf RLs, neg (oeq zf a)) z_RL zneqa
                  val z_RLp = mem_remove_bwd_2 (zf, a, RLs) conjBwd
                  val imp = impI_2 (lmem zf rest, lmem zf RLp)
                              (Thm.implies_intr (ctermL2 (jT (lmem zf rest))) z_RLp)
              in allI_2 (Term.lambda zf (mkImp (lmem zf rest)(lmem zf RLp)))
                   (Thm.forall_intr (ctermL2 zf) imp) end
            (* llen ILs = Suc(llen rest), and lt (llen rest) x (from lt (llen ILs)(Suc x)) *)
            val llenLScons = llen_cong_2 (ILs, consL) hcons
            val llenCons   = llenCons_2 (a, rest)
            val llenLS_Sr  = oeqTrans_2 (llenLScons, llenCons)       (* oeq (llen ILs)(Suc(llen rest)) *)
            (* lt (llen ILs)(Suc x) -> lt (Suc(llen rest))(Suc x) -> lt (llen rest) x *)
            val zlt = Free("zltSub", natT)
            val Plt = Term.lambda zlt (lt zlt (suc xS))
            val ltSr_Sx = oeq_rw_2 (Plt, llen ILs, suc (llen rest)) llenLS_Sr hltS  (* lt (Suc(llen rest))(Suc x) *)
            (* lt (Suc m)(Suc x) = le (Suc(Suc m))(Suc x). want lt (llen rest) x = le (Suc(llen rest)) x.
               use lt_suc_cases on (Suc(llen rest)) < Suc x giving Disj (lt (Suc(llen rest)) x)(oeq (Suc(llen rest)) x).
               Actually simpler: lt m (Suc x) with m=Suc(llen rest): lt_suc_cases (m, x): Disj (lt m x)(oeq m x).
               but we want lt (llen rest) x. From lt (Suc(llen rest))(Suc x): by "Suc-strip" -> lt (llen rest) x.
               Build via: lt (Suc r)(Suc x) = le (Suc(Suc r))(Suc x); we want le (Suc r) x = lt r x.
               Use lemma: le (Suc a)(Suc b) ==> le a b (Suc-cancel on le). Provide via le_pred. *)
            val ltrx = (* lt (llen rest) x *) le_suc_cancel_2 (suc (llen rest), xS) ltSr_Sx
            val phiRest = applyIH (rest, RLp) ltrx                    (* jT(subBody rest RL') *)
            val s1 = mp_2 (lnodup rest, mkImp (let val ef=Free("e_sub",natT) in mkForall (Term.lambda ef (mkImp (lmem ef rest)(lmem ef RLp))) end)(le (llen rest)(llen RLp))) phiRest ndRest
            val memInRestBody = let val ef=Free("e_sub",natT) in mkForall (Term.lambda ef (mkImp (lmem ef rest)(lmem ef RLp))) end
            val leRest_RLp = mp_2 (memInRestBody, le (llen rest)(llen RLp)) s1 memInRest  (* le (llen rest)(llen RL') *)
            (* le (Suc(llen rest))(Suc(llen RL')) ; Suc(llen RL') = llen RL ; Suc(llen rest) = llen ILs *)
            val leSucc = le_suc_mono_2 (llen rest, llen RLp) leRest_RLp   (* le (Suc(llen rest))(Suc(llen RL')) *)
            (* rewrite Suc(llen RL') -> llen RL via llenRLeq (sym) on %z. le (Suc(llen rest)) z *)
            val zr = Free("zrRL", natT)
            val PleR = Term.lambda zr (le (suc (llen rest)) zr)
            val llenRLeq_s = oeqSym_2 llenRLeq                          (* oeq (Suc(llen RL'))(llen RL) *)
            val le1 = oeq_rw_2 (PleR, suc (llen RLp), llen RLs) llenRLeq_s leSucc  (* le (Suc(llen rest))(llen RL) *)
            (* rewrite Suc(llen rest) -> llen ILs via llenLS_Sr (sym) on %z. le z (llen RL) *)
            val zl = Free("zlIL", natT)
            val PleL = Term.lambda zl (le zl (llen RLs))
            val llenLS_Sr_s = oeqSym_2 llenLS_Sr                        (* oeq (Suc(llen rest))(llen ILs) *)
            val leFinal = oeq_rw_2 (PleL, suc (llen rest), llen ILs) llenLS_Sr_s le1  (* le (llen ILs)(llen RL) *)
            val i2 = Thm.implies_intr (ctermL2 (jT memIn)) leFinal
            val r2 = impI_2 (memIn, le (llen ILs)(llen RLs)) i2
            val i1 = Thm.implies_intr (ctermL2 (jT (lnodup ILs))) r2
          in impI_2 (lnodup ILs, mkImp memIn (le (llen ILs)(llen RLs))) i1 end
        val subResRL = list_cases (ILs, goalSub) caseNil caseCons    (* jT(subBody ILs RLs) *)
        val metaRL = Thm.forall_intr (ctermL2 RLs) subResRL            (* !!RL. jT(subBody ILs RL) *)
        val dischLt = Thm.implies_intr (ctermL2 (jT (lt (llen ILs) (suc xS)))) metaRL
        val auxSucx = Thm.forall_intr (ctermL2 ILs) dischLt
      in Thm.forall_intr (ctermL2 xS) (Thm.implies_intr (ctermL2 (subAux xS)) auxSucx) end
    (* tie via meta_nat_induct at k = Suc (llen ILfin) *)
    val ILfin = Free("IL_fin", natlistT)
    val kFin = suc (llen ILfin)
    val indK = beta_norm (Drule.infer_instantiate ctxtL2
                 [(("Phi",0), ctermL2 PhiAbs),(("k",0), ctermL2 kFin)] meta_nat_induct_v2b)
    val auxK = Thm.implies_elim (Thm.implies_elim indK base) step    (* aux (Suc(llen ILfin)) *)
    (* aux (Suc(llen ILfin)) = !!IL. lt(llen IL)(Suc(llen ILfin)) ==> !!RL. jT(subBody IL RL) *)
    val auxAtIL = Thm.forall_elim (ctermL2 ILfin) auxK                (* lt(llen ILfin)(Suc(llen ILfin)) ==> !!RL. ... *)
    val ltSelfFin = lt_suc_2 (llen ILfin)                             (* lt(llen ILfin)(Suc(llen ILfin)) *)
    val metaRLfin = Thm.implies_elim auxAtIL ltSelfFin                (* !!RL. jT(subBody ILfin RL) *)
    val RLfin = Free("RL_fin", natlistT)
    val subFin = Thm.forall_elim (ctermL2 RLfin) metaRLfin            (* jT(subBody ILfin RLfin) *)
  in varify subFin end;
val () = if length (Thm.hyps_of sublist_len_le) = 0 then out "OK sublist_len_le (0-hyp)\n" else out ("FAIL sublist_len_le hyps="^Int.toString (length (Thm.hyps_of sublist_len_le))^"\n");
val () = out "THUE_SUBLIST_DONE\n";

(* ============================================================================
   PIECE (2) cont.: nodup_bounded_len (on ctxtTH; the bounded-length pigeonhole).
     nodup_bounded_len : lnodup IL ==> (!e. lmem e IL ==> lt e k) ==> le (llen IL) k
   A dup-free list whose every member is < k has length <= k.  COROLLARY of
   sublist_len_le with the superset RL = rangelist k:  membership <e in IL> gives
   <e < k> (hyp) gives <e in rangelist k> (lmem_rangelist_bwd); so le (llen IL)(llen (rangelist k))
   = le (llen IL) k (llen_rangelist).
   ============================================================================ *)
val sublist_len_le_vTH = varify sublist_len_le;   (* on ctxtTH : lnodup IL ==> (IL subset RL) ==> le (llen IL)(llen RL) *)
fun sublist_len_le_TH (ILt, RLt) hnd hmemin =
  let val inst = beta_norm (Drule.infer_instantiate ctxtTH
        [(("IL_fin",0), ctermTH ILt),(("RL_fin",0), ctermTH RLt)] sublist_len_le_vTH)
      val ef = Free("e_sub", natT)
      val memInT = mkForall (Term.lambda ef (mkImp (lmem ef ILt) (lmem ef RLt)))
      (* sublist_len_le is OBJECT-implication shaped: Imp (lnodup IL)(Imp memIn (le ...)) *)
      val s1 = mp_t (lnodup ILt, mkImp memInT (le (llen ILt)(llen RLt))) inst hnd
  in mp_t (memInT, le (llen ILt)(llen RLt)) s1 hmemin end;

val nodup_bounded_len =
  let
    val ILf = Free("IL_nb", natlistT)
    val kf  = Free("k_nb", natT)
    val hndP  = jT (lnodup ILf)
    val ef0 = Free("e_nb", natT)
    val boundedP = jT (mkForall (Term.lambda ef0 (mkImp (lmem ef0 ILf) (lt ef0 kf))))
    val hnd = Thm.assume (ctermTH hndP)
    val hbnd = Thm.assume (ctermTH boundedP)
    (* build (IL subset rangelist k) : !e. lmem e IL ==> lmem e (rangelist k) *)
    val memInRL =
      let val zf = Free("z_nb", natT)
          val Pabs = Term.lambda zf (mkImp (lmem zf ILf)(lmem zf (rangelist kf)))
          val hz = Thm.assume (ctermTH (jT (lmem zf ILf)))
          (* z < k from hbnd *)
          val Pbnd = Term.lambda zf (mkImp (lmem zf ILf)(lt zf kf))
          val zlt = mp_t (lmem zf ILf, lt zf kf) (allE_t Pbnd zf hbnd) hz   (* lt z k *)
          val zmem = lmem_rangelist_bwd_t (zf, kf) zlt                       (* lmem z (rangelist k) *)
          val imp = impI_t (lmem zf ILf, lmem zf (rangelist kf))
                      (Thm.implies_intr (ctermTH (jT (lmem zf ILf))) zmem)
      in allI_t (Term.lambda zf (mkImp (lmem zf ILf)(lmem zf (rangelist kf))))
           (Thm.forall_intr (ctermTH zf) imp) end
    val leLen = sublist_len_le_TH (ILf, rangelist kf) hnd memInRL   (* le (llen IL)(llen (rangelist k)) *)
    (* llen (rangelist k) = k *)
    val llenEq = llen_rangelist_t kf                                 (* oeq (llen (rangelist k)) k *)
    val zr = Free("zr_nb", natT)
    val Ple = Term.lambda zr (le (llen ILf) zr)
    val leK = oeq_rw_t (Ple, llen (rangelist kf), kf) llenEq leLen    (* le (llen IL) k *)
    val i2 = Thm.implies_intr (ctermTH boundedP) leK
    val r2 = impI_t (mkForall (Term.lambda ef0 (mkImp (lmem ef0 ILf) (lt ef0 kf))), le (llen ILf) kf) i2
    val i1 = Thm.implies_intr (ctermTH hndP) r2
  in varify (impI_t (lnodup ILf, mkImp (mkForall (Term.lambda ef0 (mkImp (lmem ef0 ILf) (lt ef0 kf)))) (le (llen ILf) kf)) i1) end;
val () = if length (Thm.hyps_of nodup_bounded_len) = 0 then out "OK nodup_bounded_len (0-hyp)\n" else out ("FAIL nodup_bounded_len hyps="^Int.toString (length (Thm.hyps_of nodup_bounded_len))^"\n");
val () = out "THUE_BOUNDED_DONE\n";

(* ============================================================================
   PIECE (2) FINALE: list_pigeonhole on ctxtTH.
   ============================================================================ *)

(* lt_zero_elim_t : jT (lt m Zero) ==> jT goal   (lt m 0 absurd) *)
fun lt_zero_elim_t mT goalC hlt =
  let val Pd = Abs("p", natT, oeq ZeroC (add (suc mT) (Bound 0)))
      fun bd p (hp:thm) =
        let val aS = addSuc_t (mT, p)
            val z_S = oeqTrans_t (hp, aS)
            val S_z = oeqSym_t z_S
            val fls = Suc_neq_Zero_t (add mT p) S_z
        in Thm.implies_elim (oFalse_elim_t goalC) fls end
  in exE_t (Pd, goalC) hlt "p_lz" bd end;

(* ---- ctxtTH list accessors needed below ---- *)
val lhd_cons_vTH = varify lhd_cons_ax;
val ltl_cons_vTH = varify ltl_cons_ax;
fun lhdCons_t (h,t) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("x",0), ctermTH h),(("t",0), ctermTH t)] lhd_cons_vTH);
fun ltlCons_t (h,t) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("x",0), ctermTH h),(("t",0), ctermTH t)] ltl_cons_vTH);
fun leqRefl_t l = beta_norm (Drule.infer_instantiate ctxtTH [(("a",0), ctermTH l)] leq_refl_vT2);

(* ---- list_cases on ctxtTH (re-derive list_cases_thm) ---- *)
val lhdC_th = Const (Sign.full_name thyL2 (Binding.name "lhd"), natlistT --> natT);
val ltlC_th = Const (Sign.full_name thyL2 (Binding.name "ltl"), natlistT --> natT) handle _ => Term.dummy;
fun lhdF l = lhdC_th $ l;
val ltlC_th2 = Const (Sign.full_name thyL2 (Binding.name "ltl"), natlistT --> natlistT);
fun ltlF l = ltlC_th2 $ l;
fun casesBody_t L = mkDisj (leq L lnilC) (leq L (lcons (lhdF L) (ltlF L)));
fun disjI1_L2t (At,Bt) h = disjI1_t (At,Bt) h;
fun disjI2_L2t (At,Bt) h = disjI2_t (At,Bt) h;
fun leq_rw_th (Pabs,aT,bT) hab hPa = leq_rw_t (Pabs,aT,bT) hab hPa;
fun oeq_rw_th (Pabs,aT,bT) hab hPa = oeq_rw_t (Pabs,aT,bT) hab hPa;

val list_cases_thm_t =
  let
    val Qpred = Term.lambda (Free("zlc", natlistT)) (casesBody_t (Free("zlc", natlistT)))
    val LF = Free("L_c", natlistT)
    val ind = beta_norm (Drule.infer_instantiate ctxtTH
          [(("P",0), ctermTH Qpred), (("a",0), ctermTH LF)] list_induct_vT2)
    val base =
      let val nilRefl = leqRefl_t lnilC
      in disjI1_t (leq lnilC lnilC, leq lnilC (lcons (lhdF lnilC)(ltlF lnilC))) nilRefl end
    val hF = Free("h_c", natT); val tF = Free("t_c", natlistT)
    val ihprop = jT (casesBody_t tF)
    val stepConcl =
      let
        val consL = lcons hF tF
        val refl0 = leqRefl_t consL
        val hLhd = lhdCons_t (hF, tF)          (* oeq (lhd (lcons h t)) h *)
        val hLhd_s = oeqSym_t hLhd             (* oeq h (lhd (lcons h t)) *)
        val hLtl = ltlCons_t (hF, tF)          (* leq (ltl (lcons h t)) t *)
        val hLtl_s = leq_sym_t hLtl            (* leq t (ltl (lcons h t)) *)
        val P1 = Term.lambda (Free("z1lc",natT)) (leq consL (lcons (Free("z1lc",natT)) tF))
        val r1 = oeq_rw_th (P1, hF, lhdF consL) hLhd_s refl0
        val P2 = Term.lambda (Free("z2lc",natlistT)) (leq consL (lcons (lhdF consL) (Free("z2lc",natlistT))))
        val r2 = leq_rw_th (P2, tF, ltlF consL) hLtl_s r1
      in disjI2_t (leq consL lnilC, leq consL (lcons (lhdF consL)(ltlF consL))) r2 end
    val step1 = Thm.forall_intr (ctermTH hF)
                  (Thm.forall_intr (ctermTH tF) (Thm.implies_intr (ctermTH ihprop) stepConcl))
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in (LF, r2) end;

fun list_cases_t (LT, goalC) caseNilFn caseConsFn =
  let
    val (LFc, casesL) = list_cases_thm_t
    val casesAtL = beta_norm (Drule.infer_instantiate ctxtTH
          [(("L_c",0), ctermTH LT)] (varify (Thm.forall_intr (ctermTH LFc) casesL)))
    val nilP  = leq LT lnilC
    val consP = leq LT (lcons (lhdF LT)(ltlF LT))
    val cA = let val h = Thm.assume (ctermTH (jT nilP))
             in Thm.implies_intr (ctermTH (jT nilP)) (caseNilFn h) end
    val cB = let val h = Thm.assume (ctermTH (jT consP))
             in Thm.implies_intr (ctermTH (jT consP)) (caseConsFn (lhdF LT, ltlF LT) h) end
  in disjE_t (nilP, consP, goalC) casesAtL cA cB end;
val () = out "THUE_FINALE_CASES_READY\n";

(* ---- list strong induction on ctxtTH ---- *)
val meta_nat_induct_vTH = varify meta_nat_induct_ax2;
fun list_strong_induct_t PhiBody stepFn =
  let
    val LMeta = Free("L_lsiTH", natlistT)
    fun auxBody nt = Logic.all LMeta (Logic.mk_implies (jT (lt (llen LMeta) nt), jT (PhiBody LMeta)))
    val nMeta = Free("n_lsiTH", natT)
    val PhiMetaAbs = Term.lambda nMeta (auxBody nMeta)
    val base =
      let val LB = Free("L_bTH", natlistT)
          val hlt = Thm.assume (ctermTH (jT (lt (llen LB) ZeroC)))
          val res = lt_zero_elim_t (llen LB) (PhiBody LB) hlt
      in Thm.forall_intr (ctermTH LB) (Thm.implies_intr (ctermTH (jT (lt (llen LB) ZeroC))) res) end
    val step =
      let
        val xS = Free("x_lsiTH", natT)
        val auxX = auxBody xS
        val IHmeta = Thm.assume (ctermTH auxX)
        fun applyAUXx L2 hlt = Thm.implies_elim (Thm.forall_elim (ctermTH L2) IHmeta) hlt
        val LS = Free("L_sTH", natlistT)
        val hltS = Thm.assume (ctermTH (jT (lt (llen LS) (suc xS))))
        val dThm = lt_suc_cases_t (llen LS, xS) hltS
        val goalC = PhiBody LS
        val caseA = let val hA = Thm.assume (ctermTH (jT (lt (llen LS) xS)))
                    in Thm.implies_intr (ctermTH (jT (lt (llen LS) xS))) (applyAUXx LS hA) end
        val caseB =
          let val hB = Thm.assume (ctermTH (jT (oeq (llen LS) xS)))
              fun applyIH L2 (h_lt:thm) =
                let val zpr = Free("z_prTH", natT)
                    val Pr = Term.lambda zpr (lt (llen L2) zpr)
                    val h_lt_x = oeq_rw_t (Pr, llen LS, xS) hB h_lt
                in applyAUXx L2 h_lt_x end
              val r = stepFn LS applyIH
          in Thm.implies_intr (ctermTH (jT (oeq (llen LS) xS))) r end
        val inst = beta_norm (Drule.infer_instantiate ctxtTH
              [(("A",0), ctermTH (lt (llen LS) xS)),(("B",0), ctermTH (oeq (llen LS) xS)),
               (("C",0), ctermTH goalC)] disjE_vT2)
        val pm = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB
        val dischLt = Thm.implies_intr (ctermTH (jT (lt (llen LS) (suc xS)))) pm
        val auxSucx = Thm.forall_intr (ctermTH LS) dischLt
      in Thm.forall_intr (ctermTH xS) (Thm.implies_intr (ctermTH auxX) auxSucx) end
    val LF = Free("L_finTH", natlistT)
    val kFin = suc (llen LF)
    val indK = beta_norm (Drule.infer_instantiate ctxtTH
                 [(("Phi",0), ctermTH PhiMetaAbs),(("k",0), ctermTH kFin)] meta_nat_induct_vTH)
    val auxK = Thm.implies_elim (Thm.implies_elim indK base) step
    val auxKL = Thm.forall_elim (ctermTH LF) auxK
    val ltSelf = lt_suc_t (llen LF)
    val resPhi = Thm.implies_elim auxKL ltSelf
  in (LF, resPhi) end;
val () = out "THUE_FINALE_LSI_READY\n";

(* the metavariable function f and bound k (Frees; generalized by varify at the end) *)
val fFun = Free("f_ph", natT --> natT);  fun fap x = fFun $ x;
val kPH  = Free("k_ph", natT);

(* tail_search : !L. Disj (?b. lmem b L /\ oeq (f b)(f a)) (!b. lmem b L ==> ~oeq (f b)(f a))
   for fixed a, by list_induct on L. *)
fun ts_ex a L = let val bf = Free("b_ts",natT)
                in mkEx (Term.lambda bf (mkConj (lmem bf L) (oeq (fap bf)(fap a)))) end;
fun ts_all a L = let val bf = Free("b_ts",natT)
                 in mkForall (Term.lambda bf (mkImp (lmem bf L) (neg (oeq (fap bf)(fap a))))) end;
fun ts_goal a L = mkDisj (ts_ex a L)(ts_all a L);

val tail_search =
  let
    val aF = Free("a_ts", natT)
    val Pabs = Term.lambda (Free("L_ts", natlistT)) (ts_goal aF (Free("L_ts", natlistT)))
    val LF = Free("Lk_ts", natlistT)
    val ind = beta_norm (Drule.infer_instantiate ctxtTH
          [(("P",0), ctermTH Pabs),(("a",0), ctermTH LF)] list_induct_vT2)
    (* base : L = lnil -> right disjunct (vacuous all) *)
    val base =
      let
        val bf = Free("b_ts", natT)
        val PallAbs = Term.lambda bf (mkImp (lmem bf lnilC)(neg (oeq (fap bf)(fap aF))))
        val body =
          let val hm = Thm.assume (ctermTH (jT (lmem bf lnilC)))
              val fls = Thm.implies_elim (lmemNilElim_t bf) hm
              val concl = Thm.implies_elim (oFalse_elim_t (neg (oeq (fap bf)(fap aF)))) fls
          in impI_t (lmem bf lnilC, neg (oeq (fap bf)(fap aF)))
               (Thm.implies_intr (ctermTH (jT (lmem bf lnilC))) concl) end
        val allThm = allI_t PallAbs (Thm.forall_intr (ctermTH bf) body)   (* ts_all aF lnil *)
      in disjI2_t (ts_ex aF lnilC, ts_all aF lnilC) allThm end
    (* step : P t -> P (lcons h t) *)
    val hF = Free("h_ts", natT); val tF = Free("t_ts", natlistT)
    val ihprop = jT (ts_goal aF tF)
    val IH = Thm.assume (ctermTH ihprop)
    val stepConcl =
      let
        val consL = lcons hF tF
        (* EM on oeq (f h)(f a) *)
        val em = em_t (oeq (fap hF)(fap aF))
        val caseHeq =
          let val heq = Thm.assume (ctermTH (jT (oeq (fap hF)(fap aF))))
              (* h is a witness in cons *)
              val memh = Thm.implies_elim (lmemConsBwd_t (hF, hF, tF)) (disjI1_t (oeq hF hF, lmem hF tF) (oeqRefl_t hF))
              val cj = conjI_t (lmem hF consL, oeq (fap hF)(fap aF)) memh heq
              val exb = exI_t (Term.lambda (Free("b_ts",natT)) (mkConj (lmem (Free("b_ts",natT)) consL)(oeq (fap (Free("b_ts",natT)))(fap aF)))) hF cj
              val res = disjI1_t (ts_ex aF consL, ts_all aF consL) exb
          in Thm.implies_intr (ctermTH (jT (oeq (fap hF)(fap aF)))) res end
        val caseHneq =
          let val hneq = Thm.assume (ctermTH (jT (neg (oeq (fap hF)(fap aF)))))
              (* use IH on t : either ex in t (lift to cons) or all in t (extend by h via hneq) *)
              fun caseExt hex =     (* hex : ts_ex aF tF *)
                let val Pb = Term.lambda (Free("b_ts",natT)) (mkConj (lmem (Free("b_ts",natT)) tF)(oeq (fap (Free("b_ts",natT)))(fap aF)))
                    fun bodyE b (hb:thm) =   (* hb : lmem b t /\ oeq (f b)(f a) *)
                      let val memb_t = conjunct1_t (lmem b tF, oeq (fap b)(fap aF)) hb
                          val feq = conjunct2_t (lmem b tF, oeq (fap b)(fap aF)) hb
                          val memb_cons = Thm.implies_elim (lmemConsBwd_t (b, hF, tF)) (disjI2_t (oeq b hF, lmem b tF) memb_t)
                          val cj = conjI_t (lmem b consL, oeq (fap b)(fap aF)) memb_cons feq
                          val exb = exI_t (Term.lambda (Free("b_ts",natT)) (mkConj (lmem (Free("b_ts",natT)) consL)(oeq (fap (Free("b_ts",natT)))(fap aF)))) b cj
                      in disjI1_t (ts_ex aF consL, ts_all aF consL) exb end
                in exE_t (Pb, ts_goal aF consL) hex "be_ts" bodyE end
              fun caseAll hall =    (* hall : ts_all aF tF *)
                let val bf = Free("b_ts", natT)
                    val PallAbs = Term.lambda bf (mkImp (lmem bf consL)(neg (oeq (fap bf)(fap aF))))
                    val body =
                      let val hm = Thm.assume (ctermTH (jT (lmem bf consL)))
                          val dj = Thm.implies_elim (lmemConsFwd_t (bf, hF, tF)) hm   (* Disj (oeq b h)(lmem b t) *)
                          val cEq = let val hbh = Thm.assume (ctermTH (jT (oeq bf hF)))
                                        (* b=h -> f b = f h <> f a *)
                                        val Pf = Term.lambda (Free("zfts",natT)) (neg (oeq (fap (Free("zfts",natT)))(fap aF)))
                                        val hbh_s = oeqSym_t hbh   (* h = b *)
                                        val res = oeq_rw_t (Pf, hF, bf) hbh_s hneq   (* ~oeq (f b)(f a) *)
                                    in Thm.implies_intr (ctermTH (jT (oeq bf hF))) res end
                          val cMem = let val hbt = Thm.assume (ctermTH (jT (lmem bf tF)))
                                         val PallBody = Term.lambda bf (mkImp (lmem bf tF)(neg (oeq (fap bf)(fap aF))))
                                         val inst = allE_t PallBody bf hall
                                         val res = mp_t (lmem bf tF, neg (oeq (fap bf)(fap aF))) inst hbt
                                     in Thm.implies_intr (ctermTH (jT (lmem bf tF))) res end
                          val res = disjE_t (oeq bf hF, lmem bf tF, neg (oeq (fap bf)(fap aF))) dj cEq cMem
                      in impI_t (lmem bf consL, neg (oeq (fap bf)(fap aF)))
                           (Thm.implies_intr (ctermTH (jT (lmem bf consL))) res) end
                    val allThm = allI_t PallAbs (Thm.forall_intr (ctermTH bf) body)
                in disjI2_t (ts_ex aF consL, ts_all aF consL) allThm end
              val cExt = let val h = Thm.assume (ctermTH (jT (ts_ex aF tF)))
                         in Thm.implies_intr (ctermTH (jT (ts_ex aF tF))) (caseExt h) end
              val cAll = let val h = Thm.assume (ctermTH (jT (ts_all aF tF)))
                         in Thm.implies_intr (ctermTH (jT (ts_all aF tF))) (caseAll h) end
              val res = disjE_t (ts_ex aF tF, ts_all aF tF, ts_goal aF consL) IH cExt cAll
          in Thm.implies_intr (ctermTH (jT (neg (oeq (fap hF)(fap aF))))) res end
      in disjE_t (oeq (fap hF)(fap aF), neg (oeq (fap hF)(fap aF)), ts_goal aF consL) em caseHeq caseHneq end
    val step1 = Thm.forall_intr (ctermTH hF)
                  (Thm.forall_intr (ctermTH tF) (Thm.implies_intr (ctermTH ihprop) stepConcl))
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in varify r2 end;
val () = if length (Thm.hyps_of tail_search) = 0 then out "OK tail_search (0-hyp)\n" else out ("FAIL tail_search hyps="^Int.toString (length (Thm.hyps_of tail_search))^"\n");
val () = out "THUE_FINALE_TAILSEARCH_DONE\n";

(* ============================================================================
   PIECE (2) — THE USABLE PIGEONHOLE (contrapositive of nodup_bounded_len):
     pigeonhole_dup : (!e. lmem e RL ==> lt e k) ==> lt k (llen RL) ==> neg (lnodup RL)
   "A list of values all < k that is longer than k cannot be duplicate-free."
   Directly from nodup_bounded_len: if lnodup RL then le (llen RL) k, contradicting
   lt k (llen RL).  This is the pigeonhole in the form a residue-collision argument
   uses: map the (s+1)^2 grid points to residues in [0,k); the residue list is
   longer than k, so by pigeonhole_dup it has a duplicate (two equal residues),
   i.e. two grid points collide.
   ============================================================================ *)
val nodup_bounded_len_vTH = nodup_bounded_len;   (* already varified, on ctxtTH *)
fun nodup_bounded_len_TH (RLt, kt) hnd hbnd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtTH
        [(("IL_nb",0), ctermTH RLt),(("k_nb",0), ctermTH kt)] nodup_bounded_len_vTH)
      val ef = Free("e_nb", natT)
      val bndT = mkForall (Term.lambda ef (mkImp (lmem ef RLt) (lt ef kt)))
      val s1 = mp_t (lnodup RLt, mkImp bndT (le (llen RLt) kt)) inst hnd
  in mp_t (bndT, le (llen RLt) kt) s1 hbnd end;
(* le m k and lt k m -> oFalse : lt k m = le (Suc k) m ; le m k + le (Suc k) m -> le (Suc k) k -> lt k k -> oFalse *)
val list_pigeonhole =
  let
    val RLf = Free("RL_ph", natlistT)
    val kf  = Free("k_ph", natT)
    val ef0 = Free("e_ph", natT)
    val bndP = jT (mkForall (Term.lambda ef0 (mkImp (lmem ef0 RLf) (lt ef0 kf))))
    val ltP  = jT (lt kf (llen RLf))
    val hbnd = Thm.assume (ctermTH bndP)
    val hlt  = Thm.assume (ctermTH ltP)
    (* goal : neg (lnodup RL) = Imp (lnodup RL) oFalse *)
    val hnd  = Thm.assume (ctermTH (jT (lnodup RLf)))
    val leLenK = nodup_bounded_len_TH (RLf, kf) hnd hbnd     (* le (llen RL) k *)
    (* lt k (llen RL) and le (llen RL) k -> oFalse.
       lt k (llen RL) = le (Suc k)(llen RL).  le_trans (Suc k)(llen RL) k -> le (Suc k) k = lt k k -> lt_irrefl *)
    val le_Sk_len = hlt    (* lt k (llen RL) = le (Suc k)(llen RL) definitionally *)
    val le_Sk_k = le_trans_t (suc kf, llen RLf, kf) le_Sk_len leLenK   (* le (Suc k) k = lt k k *)
    val fls = lt_irrefl_t kf le_Sk_k     (* oFalse *)
    val negND = impI_t (lnodup RLf, oFalseC) (Thm.implies_intr (ctermTH (jT (lnodup RLf))) fls)  (* neg (lnodup RL) *)
    val i2 = Thm.implies_intr (ctermTH ltP) negND
    val r2 = impI_t (lt kf (llen RLf), neg (lnodup RLf)) i2
    val i1 = Thm.implies_intr (ctermTH bndP) r2
    val full = impI_t (mkForall (Term.lambda ef0 (mkImp (lmem ef0 RLf) (lt ef0 kf))),
                       mkImp (lt kf (llen RLf)) (neg (lnodup RLf))) i1
  in varify full end;
val () = if length (Thm.hyps_of list_pigeonhole) = 0 then out "OK list_pigeonhole (0-hyp)\n" else out ("FAIL list_pigeonhole hyps="^Int.toString (length (Thm.hyps_of list_pigeonhole))^"\n");
val () = out ("list_pigeonhole : "^Syntax.string_of_term ctxtTH (Thm.prop_of list_pigeonhole)^"\n");
val () = out "THUE_PIGEONHOLE_DONE\n";

(* ============================================================================
   FINAL VALIDATION SUMMARY
   ============================================================================ *)
val r_sqrt   = (length (Thm.hyps_of floor_sqrt) = 0);
val r_grid   = (length (Thm.hyps_of llen_rangelist) = 0) andalso (length (Thm.hyps_of lnodup_rangelist) = 0)
               andalso (length (Thm.hyps_of lmem_rangelist_fwd) = 0) andalso (length (Thm.hyps_of lmem_rangelist_bwd) = 0);
val r_ph     = (length (Thm.hyps_of sublist_len_le) = 0) andalso (length (Thm.hyps_of nodup_bounded_len) = 0)
               andalso (length (Thm.hyps_of tail_search) = 0) andalso (length (Thm.hyps_of list_pigeonhole) = 0);
val () = out ("THUE_SUMMARY sqrt="^Bool.toString r_sqrt^" grid="^Bool.toString r_grid^" pigeonhole="^Bool.toString r_ph^"\n");
val () = out "THUE_ALL_DONE\n";
(* ============================================================================
   THUE'S LEMMA (collision form) on top of the thue foundation (ctxtTH).
   Target (0-hyp):
     0<p ==> exists s x1 x2 y1 y2.
        (le (mult s s) p AND lt p (mult (Suc s)(Suc s)))
        AND le x1 s AND le x2 s AND le y1 s AND le y2 s
        AND NOT (x1=x2 AND y1=y2)
        AND cong p (add x1 (mult a y2)) (add x2 (mult a y1)).
   (We prove the `le (mult s s) p` form -- the strongest form provable for all
    0<p; the literal `lt (mult s s) p` requires p be a non-square (prime), a
    separate fact. The collision proof never uses that bound.)
   ============================================================================ *)
val () = out "THUE_GRID_BEGIN\n";

(* re-varify base cong + extra arith onto ctxtTH *)
val cong_refl_vTH  = varify cong_refl;
val cong_sym_vTH   = varify cong_sym;
val cong_add_vTH   = varify cong_add;
val cong_trans_vTH = varify cong_trans;
val mult_assoc_vTHb = varify mult_assoc;
val le_suc_mono_vTHb = varify le_suc_mono;
val le_add_vTHb    = varify le_add;

fun cong_refl_t (mt,at) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("m",0), ctermTH mt),(("a",0), ctermTH at)] cong_refl_vTH);
fun cong_sym_t (mt,at,bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH
      [(("m",0), ctermTH mt),(("a",0), ctermTH at),(("b",0), ctermTH bt)] cong_sym_vTH)) h;
fun cong_trans_t (mt,at,bt,ct) h1 h2 = Thm.implies_elim (Thm.implies_elim
      (beta_norm (Drule.infer_instantiate ctxtTH
        [(("m",0), ctermTH mt),(("a",0), ctermTH at),(("b",0), ctermTH bt),(("c",0), ctermTH ct)] cong_trans_vTH)) h1) h2;
(* cong_add : cong m a a2 ==> cong m b b2 ==> cong m (add a b)(add a2 b2) *)
fun cong_add_t (mt,at,a2t,bt,b2t) h1 h2 = Thm.implies_elim (Thm.implies_elim
      (beta_norm (Drule.infer_instantiate ctxtTH
        [(("m",0), ctermTH mt),(("a",0), ctermTH at),(("a2",0), ctermTH a2t),
         (("b",0), ctermTH bt),(("b2",0), ctermTH b2t)] cong_add_vTH)) h1) h2;
fun multassoc_t (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("m",0), ctermTH mt),(("n",0), ctermTH nt),(("k",0), ctermTH kt)] mult_assoc_vTHb);
fun le_suc_mono_t (mt,nt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtTH
      [(("m",0), ctermTH mt),(("n",0), ctermTH nt)] le_suc_mono_vTHb)) h;
fun le_add_t (mt,pt) = beta_norm (Drule.infer_instantiate ctxtTH
      [(("m",0), ctermTH mt),(("p",0), ctermTH pt)] le_add_vTHb);

(* cong intro from an equality witness: oeq b (add a (mult m w)) ==> cong m a b *)
fun cong_introL_t (m,a,b,w) hyp =
  let val LAbs = Abs("k", natT, oeq b (add a (mult m (Bound 0))))
      val exThm = exI_t LAbs w hyp
  in disjI1_t (mkEx (Abs("k", natT, oeq b (add a (mult m (Bound 0))))),
               mkEx (Abs("k", natT, oeq a (add b (mult m (Bound 0)))))) exThm end;

val () = out "THUE_GRID_CONG_READY\n";

(* ============================================================================
   STAGE 1.  TRUNCATED SUBTRACTION (conservative) + recovery.
   New const `subv : nat->nat->nat`.  Single conservative axiom:
     sub_recover : le j s ==> oeq (add (subv s j) j) s.
   (subv = real subtraction satisfies it; sound over a fresh const.)
   ============================================================================ *)
val thySUBc = Sign.add_consts [(Binding.name "subv", natT --> natT --> natT, NoSyn)] thyTH;
fun cnstSUB nm T = Const (Sign.full_name thySUBc (Binding.name nm), T);
val subvC = cnstSUB "subv" (natT --> natT --> natT);
fun subv s j = subvC $ s $ j;

val sJ = Free("s_sub", natT); val jJ = Free("j_sub", natT);
val ((_,sub_recover_ax), thySUB) = Thm.add_axiom_global (Binding.name "sub_recover",
      Logic.mk_implies (jT (le jJ sJ), jT (oeq (add (subv sJ jJ) jJ) sJ))) thySUBc;

(* ============================================================================
   STAGE 2.  DIVISION / MOD BY A PARAMETER (conservative).
   New consts rdivv, rmodv : nat->nat->nat.  Two conservative axioms (0<d):
     divmod_id : 0<d ==> oeq c (add (mult d (rdivv c d)) (rmodv c d))
     rmod_lt   : 0<d ==> lt (rmodv c d) d
   ============================================================================ *)
val thyDMc = Sign.add_consts
  [(Binding.name "rdivv", natT --> natT --> natT, NoSyn),
   (Binding.name "rmodv", natT --> natT --> natT, NoSyn)] thySUB;
fun cnstDM nm T = Const (Sign.full_name thyDMc (Binding.name nm), T);
val rdivvC = cnstDM "rdivv" (natT --> natT --> natT); fun rdivv c d = rdivvC $ c $ d;
val rmodvC = cnstDM "rmodv" (natT --> natT --> natT); fun rmodv c d = rmodvC $ c $ d;

val cD = Free("c_dm", natT); val dD = Free("d_dm", natT);
val ((_,divmod_id_ax), thyDM1) = Thm.add_axiom_global (Binding.name "divmod_id",
      Logic.mk_implies (jT (lt ZeroC dD),
        jT (oeq cD (add (mult dD (rdivv cD dD)) (rmodv cD dD))))) thyDMc;
val ((_,rmod_lt_ax), thyDM) = Thm.add_axiom_global (Binding.name "rmod_lt",
      Logic.mk_implies (jT (lt ZeroC dD),
        jT (lt (rmodv cD dD) dD))) thyDM1;

(* ----- ONE final context covering all the new consts ----- *)
val ctxtG  = Proof_Context.init_global thyDM;
val ctermG = Thm.cterm_of ctxtG;
val () = out "THUE_GRID_CONSTS_READY\n";

(* ----- re-varify EVERYTHING we use onto ctxtG (suffix _g) ----- *)
val sub_recover_vG = varify sub_recover_ax;
val divmod_id_vG   = varify divmod_id_ax;
val rmod_lt_vG     = varify rmod_lt_ax;
(* base arith / logic re-varified to ctxtG *)
val oeq_refl_vG = varify oeq_refl;   val oeq_subst_vG = varify oeq_subst;
val oeq_sym_vG  = varify oeq_sym;    val oeq_trans_vG = varify oeq_trans;
val Suc_cong_vG = varify Suc_cong;
val exI_vG = varify exI_ax;          val exE_vG = varify exE_ax;
val conjI_vG = varify conjI_ax;      val conjunct1_vG = varify conjunct1_ax; val conjunct2_vG = varify conjunct2_ax;
val disjI1_vG = varify disjI1_ax;    val disjI2_vG = varify disjI2_ax;       val disjE_vG = varify disjE_ax;
val mp_vG = varify mp_ax;            val impI_vG = varify impI_ax;
val allI_vG = varify allI_ax;        val allE_vG = varify allE_ax;
val ex_middle_vG = varify ex_middle_ax;
val oFalse_elim_vG = varify oFalse_elim_ax;
val Suc_neq_Zero_vG = varify Suc_neq_Zero_ax; val Suc_inj_vG = varify Suc_inj_ax;
val add_0_vG=varify add_0; val add_Suc_vG=varify add_Suc; val add_0_right_vG=varify add_0_right;
val add_Suc_right_vG=varify add_Suc_right; val add_comm_vG=varify add_comm; val add_assoc_vG=varify add_assoc;
val mult_0_vG=varify mult_0; val mult_Suc_vG=varify mult_Suc; val mult_0_right_vG=varify mult_0_right;
val mult_Suc_right_vG=varify mult_Suc_right; val mult_comm_vG=varify mult_comm; val mult_assoc_vG=varify mult_assoc;
val mult_1_left_vG=varify mult_1_left; val left_distrib_vG=varify left_distrib; val right_distrib_vG=varify right_distrib;
val mult_le_mono_vG=varify mult_le_mono;
val le_refl_vG=varify le_refl; val le_trans_vG=varify le_trans; val le_total_vG=varify le_total;
val le_antisym_vG=varify le_antisym; val le_add_vG=varify le_add; val zero_le_vG=varify zero_le;
val le_suc_mono_vG=varify le_suc_mono;
val lt_suc_vG=varify lt_suc; val lt_irrefl_vG=varify lt_irrefl; val lt_trans_vG=varify lt_trans;
val lt_suc_cases_vG=varify lt_suc_cases; val nlt_le_vG=varify nlt_le;
val cong_refl_vG=varify cong_refl; val cong_sym_vG=varify cong_sym;
val cong_add_vG=varify cong_add;   val cong_trans_vG=varify cong_trans;
(* list lib onto ctxtG *)
val leq_refl_vG=varify leq_refl_ax; val leq_subst_vG=varify leq_subst_ax; val leq_sym_vG=varify leq_sym;
val list_induct_vG=varify list_induct_ax;
val lmem_nil_elim_vG=varify lmem_nil_elim_ax; val lmem_cons_fwd_vG=varify lmem_cons_fwd_ax; val lmem_cons_bwd_vG=varify lmem_cons_bwd_ax;
val llen_nil_vG=varify llen_nil_ax; val llen_cons_vG=varify llen_cons_ax;
val lnodup_nil_vG=varify lnodup_nil_ax; val lnodup_cons_fwd_vG=varify lnodup_cons_fwd_ax; val lnodup_cons_bwd_vG=varify lnodup_cons_bwd_ax;
val () = out "THUE_GRID_VARIFY_READY\n";

(* ----- _g combinators ----- *)
fun oeqRefl_g x = beta_norm (Drule.infer_instantiate ctxtG [(("a",0), ctermG x)] oeq_refl_vG);
fun oeqSym_g h = oeq_sym_vG OF [h];
fun oeqTrans_g (h1,h2) = oeq_trans_vG OF [h1,h2];
fun Suc_cong_g h = Suc_cong_vG OF [h];
fun add0_g t = beta_norm (Drule.infer_instantiate ctxtG [(("n",0), ctermG t)] add_0_vG);
fun add0r_g t = beta_norm (Drule.infer_instantiate ctxtG [(("n",0), ctermG t)] add_0_right_vG);
fun addSuc_g (m,n) = beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG m),(("n",0), ctermG n)] add_Suc_vG);
fun addSucr_g (m,n) = beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG m),(("n",0), ctermG n)] add_Suc_right_vG);
fun addcomm_g (m,n) = beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG m),(("n",0), ctermG n)] add_comm_vG);
fun addassoc_g (m,n,k) = beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG m),(("n",0), ctermG n),(("k",0), ctermG k)] add_assoc_vG);
fun mult0_g t = beta_norm (Drule.infer_instantiate ctxtG [(("n",0), ctermG t)] mult_0_vG);
fun mult0r_g t = beta_norm (Drule.infer_instantiate ctxtG [(("n",0), ctermG t)] mult_0_right_vG);
fun multcomm_g (m,n) = beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG m),(("n",0), ctermG n)] mult_comm_vG);
fun multassoc_g (m,n,k) = beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG m),(("n",0), ctermG n),(("k",0), ctermG k)] mult_assoc_vG);
fun mult1l_g t = beta_norm (Drule.infer_instantiate ctxtG [(("n",0), ctermG t)] mult_1_left_vG);
fun leftdistrib_g (x,m,n) = beta_norm (Drule.infer_instantiate ctxtG [(("x",0), ctermG x),(("m",0), ctermG m),(("n",0), ctermG n)] left_distrib_vG);
fun rightdistrib_g (m,n,k) = beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG m),(("n",0), ctermG n),(("k",0), ctermG k)] right_distrib_vG);
fun oeq_rw_g (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtG
        [(("P",0), ctermG Pabs),(("a",0), ctermG aT),(("b",0), ctermG bT)] oeq_subst_vG)
  in inst OF [hab, hPa] end;
fun add_cong_l_g (p,q,k) hpq = let val P=Term.lambda (Free("zalg",natT)) (oeq (add p k)(add (Free("zalg",natT)) k)) in oeq_rw_g (P,p,q) hpq (oeqRefl_g (add p k)) end;
fun add_cong_r_g (h,p,q) hpq = let val P=Term.lambda (Free("zarg",natT)) (oeq (add h p)(add h (Free("zarg",natT)))) in oeq_rw_g (P,p,q) hpq (oeqRefl_g (add h p)) end;
fun mult_cong_l_g (p,q,k) hpq = let val P=Term.lambda (Free("zmlg",natT)) (oeq (mult p k)(mult (Free("zmlg",natT)) k)) in oeq_rw_g (P,p,q) hpq (oeqRefl_g (mult p k)) end;
fun mult_cong_r_g (h,p,q) hpq = let val P=Term.lambda (Free("zmrg",natT)) (oeq (mult h p)(mult h (Free("zmrg",natT)))) in oeq_rw_g (P,p,q) hpq (oeqRefl_g (mult h p)) end;
fun mp_g (At,Bt) hImp hA = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("A",0), ctermG At),(("B",0), ctermG Bt)] mp_vG)) hImp) hA;
fun impI_g (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("A",0), ctermG At),(("B",0), ctermG Bt)] impI_vG)) h;
fun conjI_g (At,Bt) hA hB = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("A",0), ctermG At),(("B",0), ctermG Bt)] conjI_vG)) hA) hB;
fun conjunct1_g (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("A",0), ctermG At),(("B",0), ctermG Bt)] conjunct1_vG)) h;
fun conjunct2_g (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("A",0), ctermG At),(("B",0), ctermG Bt)] conjunct2_vG)) h;
fun oFalse_elim_g rT = beta_norm (Drule.infer_instantiate ctxtG [(("R",0), ctermG rT)] oFalse_elim_vG);
fun disjE_g (At,Bt,Ct) dThm cA cB = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("A",0), ctermG At),(("B",0), ctermG Bt),(("C",0), ctermG Ct)] disjE_vG)) dThm) cA) cB;
fun disjI1_g (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("A",0), ctermG At),(("B",0), ctermG Bt)] disjI1_vG)) h;
fun disjI2_g (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("A",0), ctermG At),(("B",0), ctermG Bt)] disjI2_vG)) h;
fun em_g t = beta_norm (Drule.infer_instantiate ctxtG [(("A",0), ctermG t)] ex_middle_vG);
fun allI_g Pabs h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("P",0), ctermG Pabs)] allI_vG)) h;
fun allE_g Pabs at h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("P",0), ctermG Pabs),(("a",0), ctermG at)] allE_vG)) h;
fun Suc_neq_Zero_g nt heq = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("n",0), ctermG nt)] Suc_neq_Zero_vG)) heq;
fun Suc_inj_g (a,b) heq = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("a",0), ctermG a),(("b",0), ctermG b)] Suc_inj_vG)) heq;
fun exI_g Pabs at hbody = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("P",0), ctermG Pabs),(("a",0), ctermG at)] exI_vG)) hbody;
fun exE_g (Pabs, goalC) exThm wName wT bodyFn =
  let val wF = Free(wName, wT)
      val hypTerm = jT (Term.betapply (Pabs, wF))
      val hypThm  = Thm.assume (ctermG hypTerm)
      val body    = bodyFn wF hypThm
      val minor   = Thm.forall_intr (ctermG wF) (Thm.implies_intr (ctermG hypTerm) body)
      val exE_inst= beta_norm (Drule.infer_instantiate ctxtG [(("P",0), ctermG Pabs),(("Q",0), ctermG goalC)] exE_vG)
  in Thm.implies_elim (Thm.implies_elim exE_inst exThm) minor end;
fun le_intro_g (mT,nT,w) hyp =
  let val Pabs = Abs("p", natT, oeq nT (add mT (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtG [(("P",0), ctermG Pabs),(("a",0), ctermG w)] exI_vG)
  in inst OF [hyp] end;
fun le_refl_g t = beta_norm (Drule.infer_instantiate ctxtG [(("n",0), ctermG t)] le_refl_vG);
fun zero_le_g t = beta_norm (Drule.infer_instantiate ctxtG [(("n",0), ctermG t)] zero_le_vG);
fun le_total_g (m,n) = beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG m),(("n",0), ctermG n)] le_total_vG);
fun le_trans_g (a,b,c) h1 h2 = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG a),(("n",0), ctermG b),(("k",0), ctermG c)] le_trans_vG)) h1) h2;
fun le_antisym_g (m,n) h1 h2 = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG m),(("n",0), ctermG n)] le_antisym_vG)) h1) h2;
fun le_add_g (m,p) = beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG m),(("p",0), ctermG p)] le_add_vG);
fun le_suc_mono_g (m,n) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG m),(("n",0), ctermG n)] le_suc_mono_vG)) h;
fun lt_trans_g (a,b,c) h1 h2 = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("a",0), ctermG a),(("b",0), ctermG b),(("c",0), ctermG c)] lt_trans_vG)) h1) h2;
fun lt_suc_cases_g (m,n) hlt = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG m),(("n",0), ctermG n)] lt_suc_cases_vG)) hlt;
fun lt_suc_g n = beta_norm (Drule.infer_instantiate ctxtG [(("n",0), ctermG n)] lt_suc_vG);
fun lt_irrefl_g n hlt = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("n",0), ctermG n)] lt_irrefl_vG)) hlt;
fun nlt_le_g (d,c) hneg = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("d",0), ctermG d),(("c",0), ctermG c)] nlt_le_vG)) hneg;
fun mult_le_mono_g (c,j,k) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("c",0), ctermG c),(("j",0), ctermG j),(("k",0), ctermG k)] mult_le_mono_vG)) h;
(* cong on ctxtG *)
fun cong_refl_g (m,a) = beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG m),(("a",0), ctermG a)] cong_refl_vG);
fun cong_sym_g (m,a,b) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG m),(("a",0), ctermG a),(("b",0), ctermG b)] cong_sym_vG)) h;
fun cong_trans_g (m,a,b,c) h1 h2 = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG m),(("a",0), ctermG a),(("b",0), ctermG b),(("c",0), ctermG c)] cong_trans_vG)) h1) h2;
fun cong_add_g (m,a,a2,b,b2) h1 h2 = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG [(("m",0), ctermG m),(("a",0), ctermG a),(("a2",0), ctermG a2),(("b",0), ctermG b),(("b2",0), ctermG b2)] cong_add_vG)) h1) h2;
fun cong_introL_g (m,a,b,w) hyp =
  let val LAbs = Abs("k", natT, oeq b (add a (mult m (Bound 0))))
      val exThm = exI_g LAbs w hyp
  in disjI1_g (mkEx (Abs("k", natT, oeq b (add a (mult m (Bound 0))))),
               mkEx (Abs("k", natT, oeq a (add b (mult m (Bound 0)))))) exThm end;

(* new-const accessors *)
fun sub_recover_g (st,jt) hle = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG
      [(("s_sub",0), ctermG st),(("j_sub",0), ctermG jt)] sub_recover_vG)) hle;
fun divmod_id_g (ct,dt) hpos = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG
      [(("c_dm",0), ctermG ct),(("d_dm",0), ctermG dt)] divmod_id_vG)) hpos;
fun rmod_lt_g (ct,dt) hpos = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG
      [(("c_dm",0), ctermG ct),(("d_dm",0), ctermG dt)] rmod_lt_vG)) hpos;
val () = out "THUE_GRID_COMBINATORS_READY\n";

(* quick check the new axioms are usable *)
val () =
  let val pp = Free("pp", natT)
      val pos = Thm.assume (ctermG (jT (lt ZeroC pp)))
      val t = rmod_lt_g (Free("cc",natT), pp) pos
  in if length (Thm.hyps_of t) = 1 then out "OK rmod_lt usable\n" else out "FAIL rmod_lt usable\n" end;
val () = out "THUE_STAGE12_DONE\n";

(* ============================================================================
   STAGE 3a.  THE REARRANGEMENT LEMMA (the algebraic heart).
   Given le y1 s, le y2 s, and
     cong p (x1 + a*(subv s y1)) (x2 + a*(subv s y2))
   derive
     cong p (x1 + a*y2) (x2 + a*y1).
   Method: add the SAME quantity D = a*y1 + a*y2 to both sides via cong_add
   (with cong_refl on D), then rewrite using a*(s-y)+a*y = a*s (distrib +
   sub_recover) and cancel the common a*s.  Concretely:
     LHS + D = x1 + a*(s-y1) + (a*y1 + a*y2)
             = x1 + a*y2 + (a*(s-y1)+a*y1)         [reassoc/comm]
             = x1 + a*y2 + a*s.
     RHS + D = x2 + a*(s-y2) + (a*y1 + a*y2)
             = x2 + a*y1 + (a*(s-y2)+a*y2)
             = x2 + a*y1 + a*s.
   So cong p (x1 + a*y2 + a*s) (x2 + a*y1 + a*s).  Then "cancel a*s" is just
   the SAME extra summand on both -- but it's already there, so we instead build
   the cong on the (x1+a*y2) vs (x2+a*y1) cores by adding a*s and using cong_add
   in REVERSE: actually we PROVE the target then add a*s.  Cleaner: derive the
   target directly: from the +D cong above, the two sides equal (target side)+a*s;
   we need to remove a*s.  cong is NOT cancellative in general, so instead build
   FORWARD: take the target's two cores, add a*s via cong_add(cong_refl (a*s)),
   show that equals the hypothesis+D rearranged.  We go the other way:

   GIVEN H : cong p L R, with L=x1+a*(s-y1), R=x2+a*(s-y2).
   target T : cong p (x1+a*y2) (x2+a*y1).
   We show:  (x1+a*y2) + a*s  ==  L + (a*y1+a*y2)   (an EQUALITY, oeq)
        and  (x2+a*y1) + a*s  ==  R + (a*y1+a*y2)   (an EQUALITY, oeq)
   Then cong_add H (cong_refl p (a*y1+a*y2)) : cong p (L+D) (R+D).
   Rewrite both sides by the equalities (oeq, both directions) to get
        cong p ((x1+a*y2)+a*s) ((x2+a*y1)+a*s).
   Then we need: cong p ((x1+a*y2)+w) ((x2+a*y1)+w) ==> cong p (x1+a*y2)(x2+a*y1)
   i.e. cong RIGHT-cancellation by a common addend.  We prove cong_radd_cancel.
   ============================================================================ *)
val () = out "THUE_STAGE3A_BEGIN\n";

(* cong_radd_cancel : cong m (add a w)(add b w) ==> cong m a b
   cong m (a+w)(b+w) = Disj (Ex k. b+w = (a+w)+m*k) (Ex k. a+w = (b+w)+m*k).
   left: b+w = a+w+m*k = (a+m*k)+w  [reassoc/comm] ; cancel w (add_left/right cancel)
         -> b = a+m*k -> congL -> disjI1.  right symmetric. *)
(* need add right-cancel : oeq (add a w)(add b w) ==> oeq a b. Derive from add_left_cancel + comm. *)
val add_left_cancel_vG = varify add_left_cancel;
(* add_left_cancel : oeq (add m a)(add m b) ==> oeq a b ; args (prefix m, a, b) *)
fun add_left_cancel_g (m,a,b) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG
      [(("m",0), ctermG m),(("a",0), ctermG a),(("b",0), ctermG b)] add_left_cancel_vG)) h;

val cong_radd_cancel =
  let
    val mF=Free("m_cc",natT); val aF=Free("a_cc",natT); val bF=Free("b_cc",natT); val wF=Free("w_cc",natT)
    val hypP = jT (cong mF (add aF wF) (add bF wF))
    val hyp  = Thm.assume (ctermG hypP)
    val goalC = cong mF aF bF
    val LAbs = Abs("k", natT, oeq (add bF wF) (add (add aF wF) (mult mF (Bound 0))))
    val RAbs = Abs("k", natT, oeq (add aF wF) (add (add bF wF) (mult mF (Bound 0))))
    (* from (b+w) = (a+w)+m*k  derive  b = a+m*k *)
    fun leftBody k (hk:thm) =     (* hk : oeq (b+w)((a+w)+m*k) *)
      let
        (* (a+w)+m*k = (a+m*k)+w :  (a+w)+mk = a+(w+mk) [assoc] = a+(mk+w) [comm] = (a+mk)+w [assoc back] *)
        val e1 = addassoc_g (aF, wF, mult mF k)          (* (a+w)+mk = a+(w+mk) *)
        val e2 = addcomm_g (wF, mult mF k)                (* (w+mk) = (mk+w) *)
        val e3 = add_cong_r_g (aF, add wF (mult mF k), add (mult mF k) wF) e2  (* a+(w+mk) = a+(mk+w) *)
        val e4 = addassoc_g (aF, mult mF k, wF)           (* (a+mk)+w = a+(mk+w) *)
        val e4s = oeqSym_g e4                             (* a+(mk+w) = (a+mk)+w *)
        val chain = oeqTrans_g (oeqTrans_g (e1, e3), e4s) (* (a+w)+mk = (a+mk)+w *)
        val bw_eq = oeqTrans_g (hk, chain)                (* (b+w) = (a+mk)+w *)
        (* commute both to w+... then cancel left w *)
        val cb = addcomm_g (bF, wF)                        (* (b+w) = (w+b) *)
        val ca = addcomm_g (add aF (mult mF k), wF)        (* ((a+mk)+w) = (w+(a+mk)) *)
        val wb_eq = oeqTrans_g (oeqTrans_g (oeqSym_g cb, bw_eq), ca)  (* (w+b) = (w+(a+mk)) *)
        val b_eq = add_left_cancel_g (wF, bF, add aF (mult mF k)) wb_eq  (* b = a+mk *)
      in cong_introL_g (mF, aF, bF, k) b_eq end
    fun rightBody k (hk:thm) =    (* hk : oeq (a+w)((b+w)+m*k) -> a = b+m*k -> congR -> disjI2 *)
      let
        val e1 = addassoc_g (bF, wF, mult mF k)
        val e2 = addcomm_g (wF, mult mF k)
        val e3 = add_cong_r_g (bF, add wF (mult mF k), add (mult mF k) wF) e2
        val e4 = addassoc_g (bF, mult mF k, wF)
        val e4s = oeqSym_g e4
        val chain = oeqTrans_g (oeqTrans_g (e1, e3), e4s)  (* (b+w)+mk = (b+mk)+w *)
        val aw_eq = oeqTrans_g (hk, chain)                 (* (a+w) = (b+mk)+w *)
        val cb = addcomm_g (aF, wF)
        val ca = addcomm_g (add bF (mult mF k), wF)
        val wa_eq = oeqTrans_g (oeqTrans_g (oeqSym_g cb, aw_eq), ca)  (* (w+a) = (w+(b+mk)) *)
        val a_eq = add_left_cancel_g (wF, aF, add bF (mult mF k)) wa_eq  (* a = b+mk *)
        val RAbsG = Abs("k", natT, oeq aF (add bF (mult mF (Bound 0))))
        val exThm = exI_g RAbsG k a_eq
      in disjI2_g (mkEx (Abs("k",natT, oeq bF (add aF (mult mF (Bound 0))))),
                   mkEx (Abs("k",natT, oeq aF (add bF (mult mF (Bound 0)))))) exThm end
    val caseL = let val h=Thm.assume (ctermG (jT (mkEx LAbs)))
                in Thm.implies_intr (ctermG (jT (mkEx LAbs))) (exE_g (LAbs, goalC) h "kL" natT leftBody) end
    val caseR = let val h=Thm.assume (ctermG (jT (mkEx RAbs)))
                in Thm.implies_intr (ctermG (jT (mkEx RAbs))) (exE_g (RAbs, goalC) h "kR" natT rightBody) end
    val concl = disjE_g (mkEx LAbs, mkEx RAbs, goalC) hyp caseL caseR
  in varify (Thm.implies_intr (ctermG hypP) concl) end;
val () = if length (Thm.hyps_of cong_radd_cancel) = 0 then out "OK cong_radd_cancel (0-hyp)\n" else out ("FAIL cong_radd_cancel hyps="^Int.toString (length (Thm.hyps_of cong_radd_cancel))^"\n");
fun cong_radd_cancel_g (m,a,b,w) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtG
      [(("m_cc",0), ctermG m),(("a_cc",0), ctermG a),(("b_cc",0), ctermG b),(("w_cc",0), ctermG w)] cong_radd_cancel)) h;
val () = out "THUE_STAGE3A_RADDCANCEL_DONE\n";

(* ============================================================================
   STAGE 3b.  THE REARRANGEMENT LEMMA.
   Parameters a (Free, the lemma's 'a'), p (Free), s (Free).
   ============================================================================ *)
val () = out "THUE_STAGE3B_BEGIN\n";
val aTH = Free("a", natT);   (* the lemma parameter 'a' (kept Free; never generalized) *)

(* a_sub_recover : le y s ==> oeq (add (mult a (subv s y))(mult a y)) (mult a s) *)
fun a_sub_recover (aP, sP, yP) hle =
  let
    val rec0 = sub_recover_g (sP, yP) hle                 (* oeq (add (subv s y) y) s *)
    val dist = leftdistrib_g (aP, subv sP yP, yP)         (* a*((s-y)+y) = a*(s-y) + a*y *)
    (* a*((s-y)+y) = a*s via mult_cong_r with rec0 *)
    val mc = mult_cong_r_g (aP, add (subv sP yP) yP, sP) rec0  (* a*((s-y)+y) = a*s *)
    val dist_s = oeqSym_g dist                            (* (a*(s-y)+a*y) = a*((s-y)+y) *)
  in oeqTrans_g (dist_s, mc) end;                         (* (a*(s-y)+a*y) = a*s *)

(* main rearrangement: rearrange_collision *)
fun rearrange_collision (x1P,x2P,y1P,y2P) hle1 hle2 H =
  let
    val sP = Free("s_rc", natT)   (* placeholder; real s passed via closures below *)
  in H end;
(* We instead inline rearrange at the call-site (s is in scope there).  But to
   keep it reusable, define with explicit s: *)
fun rearrange (sP, x1P,x2P,y1P,y2P) hle1 hle2 H =
  (* H : cong p (x1 + a*(subv s y1)) (x2 + a*(subv s y2)) ; le y1 s, le y2 s
     goal : cong p (x1 + a*y2)(x2 + a*y1) *)
  let
    val pP = Free("p", natT)      (* the lemma parameter p (Free) *)
    val a = aTH
    val Lc = add x1P (mult a (subv sP y1P))     (* L *)
    val Rc = add x2P (mult a (subv sP y2P))     (* R *)
    val D  = add (mult a y1P) (mult a y2P)       (* D = a*y1 + a*y2 *)
    val as_ = mult a sP                           (* a*s *)
    (* cong p (L+D)(R+D) *)
    val crefl = cong_refl_g (pP, D)               (* cong p D D *)
    val congLD_RD = cong_add_g (pP, Lc, Rc, D, D) H crefl   (* cong p (add L D)(add R D) *)
    (* E1 : (x1+a*y2)+a*s == L + D *)
    val asr1 = a_sub_recover (a, sP, y1P) hle1     (* (a*(s-y1)+a*y1) = a*s *)
    val asr2 = a_sub_recover (a, sP, y2P) hle2     (* (a*(s-y2)+a*y2) = a*s *)
    (* Build L+D = x1 + a*(s-y1) + (a*y1 + a*y2)  step by step into (x1+a*y2)+a*s. *)
    (* L + D = (x1 + a*(s-y1)) + (a*y1 + a*y2)
            = x1 + (a*(s-y1) + (a*y1 + a*y2))         [assoc]
            = x1 + ((a*(s-y1) + a*y1) + a*y2)         [assoc back inside]
            = x1 + (a*s + a*y2)                        [asr1 on first part]
            = x1 + (a*y2 + a*s)                        [comm]
            = (x1 + a*y2) + a*s                        [assoc back]
       so  L+D = (x1+a*y2)+a*s.  Build LHS->target forward then sym for rewrite. *)
    val ld1 = addassoc_g (x1P, mult a (subv sP y1P), D)         (* (x1+a(s-y1))+D = x1 + (a(s-y1)+D) *)
    (* a(s-y1)+D = a(s-y1)+(a*y1+a*y2) = (a(s-y1)+a*y1)+a*y2 [assoc back] *)
    val inAssoc = addassoc_g (mult a (subv sP y1P), mult a y1P, mult a y2P)  (* (a(s-y1)+a*y1)+a*y2 = a(s-y1)+(a*y1+a*y2) *)
    val inAssoc_s = oeqSym_g inAssoc                          (* a(s-y1)+(a*y1+a*y2) = (a(s-y1)+a*y1)+a*y2 *)
    (* (a(s-y1)+a*y1)+a*y2 = a*s + a*y2 [asr1] *)
    val toAs = add_cong_l_g (add (mult a (subv sP y1P)) (mult a y1P), as_, mult a y2P) asr1
                                                              (* ((a(s-y1)+a*y1)+a*y2) = (a*s + a*y2) *)
    val inner1 = oeqTrans_g (inAssoc_s, toAs)                 (* a(s-y1)+D = a*s + a*y2 *)
    val ld2 = oeqTrans_g (ld1, add_cong_r_g (x1P, add (mult a (subv sP y1P)) D, add as_ (mult a y2P)) inner1)
    (* ld2 : L+D = x1 + (a*s + a*y2).  Now x1 + (a*s+a*y2) = x1 + (a*y2+a*s) [comm] = (x1+a*y2)+a*s [assoc] *)
    val commAs = addcomm_g (as_, mult a y2P)                  (* (a*s + a*y2) = (a*y2 + a*s) *)
    val ld3 = oeqTrans_g (ld2, add_cong_r_g (x1P, add as_ (mult a y2P), add (mult a y2P) as_) commAs)
                                                              (* L+D = x1 + (a*y2 + a*s) *)
    val assocBack1 = addassoc_g (x1P, mult a y2P, as_)        (* (x1+a*y2)+a*s = x1+(a*y2+a*s) *)
    val ld_final = oeqTrans_g (ld3, oeqSym_g assocBack1)      (* L+D = (x1+a*y2)+a*s *)
    (* similarly R+D = (x2+a*y1)+a*s, but with the y1<->y2 roles:
       R = x2 + a*(s-y2) ; D = a*y1 + a*y2.
       R+D = x2 + (a*(s-y2) + (a*y1+a*y2))
       want (x2+a*y1)+a*s.  Inside: a(s-y2)+(a*y1+a*y2).  We want (a(s-y2)+a*y2)+a*y1 = a*s + a*y1.
       But D = a*y1+a*y2 (order!). Reassoc: a(s-y2)+(a*y1+a*y2) = a(s-y2)+(a*y2+a*y1) [comm inside D]
         = (a(s-y2)+a*y2)+a*y1 [assoc back] = a*s + a*y1 [asr2]. *)
    val rd1 = addassoc_g (x2P, mult a (subv sP y2P), D)       (* R+D = x2 + (a(s-y2)+D) *)
    val commD = addcomm_g (mult a y1P, mult a y2P)            (* (a*y1+a*y2) = (a*y2+a*y1) *)
    val dswap = add_cong_r_g (mult a (subv sP y2P), D, add (mult a y2P) (mult a y1P)) commD
                                                              (* a(s-y2)+D = a(s-y2)+(a*y2+a*y1) *)
    val rInAssoc = addassoc_g (mult a (subv sP y2P), mult a y2P, mult a y1P)  (* (a(s-y2)+a*y2)+a*y1 = a(s-y2)+(a*y2+a*y1) *)
    val rInAssoc_s = oeqSym_g rInAssoc                        (* a(s-y2)+(a*y2+a*y1) = (a(s-y2)+a*y2)+a*y1 *)
    val rToAs = add_cong_l_g (add (mult a (subv sP y2P)) (mult a y2P), as_, mult a y1P) asr2
                                                              (* ((a(s-y2)+a*y2)+a*y1) = (a*s + a*y1) *)
    val rInner = oeqTrans_g (oeqTrans_g (dswap, rInAssoc_s), rToAs)  (* a(s-y2)+D = a*s + a*y1 *)
    val rd2 = oeqTrans_g (rd1, add_cong_r_g (x2P, D, add as_ (mult a y1P)) rInner)  (* R+D = x2 + (a*s + a*y1) *)
    val rcommAs = addcomm_g (as_, mult a y1P)                 (* (a*s+a*y1) = (a*y1+a*s) *)
    val rd3 = oeqTrans_g (rd2, add_cong_r_g (x2P, add as_ (mult a y1P), add (mult a y1P) as_) rcommAs)
    val rassocBack = addassoc_g (x2P, mult a y1P, as_)        (* (x2+a*y1)+a*s = x2+(a*y1+a*s) *)
    val rd_final = oeqTrans_g (rd3, oeqSym_g rassocBack)      (* R+D = (x2+a*y1)+a*s *)
    (* rewrite congLD_RD : cong p (L+D)(R+D) using ld_final (sym) and rd_final (sym) *)
    val ld_final_s = oeqSym_g ld_final     (* (x1+a*y2)+a*s = L+D *)
    val rd_final_s = oeqSym_g rd_final     (* (x2+a*y1)+a*s = R+D *)
    (* rewrite first arg L+D -> (x1+a*y2)+a*s via oeq_rw on %z. cong p z (R+D) *)
    val zc1 = Free("zc1_rc", natT)
    val P1 = Term.lambda zc1 (cong pP zc1 (add Rc D))
    val st1 = oeq_rw_g (P1, add Lc D, add (add x1P (mult a y2P)) as_) ld_final congLD_RD
                                            (* cong p ((x1+a*y2)+a*s)(R+D) *)
    val zc2 = Free("zc2_rc", natT)
    val P2 = Term.lambda zc2 (cong pP (add (add x1P (mult a y2P)) as_) zc2)
    val st2 = oeq_rw_g (P2, add Rc D, add (add x2P (mult a y1P)) as_) rd_final st1
                                            (* cong p ((x1+a*y2)+a*s)((x2+a*y1)+a*s) *)
    val res = cong_radd_cancel_g (pP, add x1P (mult a y2P), add x2P (mult a y1P), as_) st2
  in res end;
val () = out "THUE_STAGE3B_FNS_READY\n";

(* instrumented sanity-check pieces *)
val sP=Free("ss",natT); val x1=Free("x1t",natT); val x2=Free("x2t",natT);
val y1=Free("y1t",natT); val y2=Free("y2t",natT); val pP=Free("p",natT)
val hle1 = Thm.assume (ctermG (jT (le y1 sP)))
val hle2 = Thm.assume (ctermG (jT (le y2 sP)))
val a = aTH
val Lc = add x1 (mult a (subv sP y1))
val Rc = add x2 (mult a (subv sP y2))
val D  = add (mult a y1) (mult a y2)
val as_ = mult a sP
val () = out "DBG_terms_built\n";
val asr1 = a_sub_recover (a, sP, y1) hle1
val () = out ("DBG_asr1="^Syntax.string_of_term ctxtG (Thm.prop_of asr1)^"\n");
val ld1 = addassoc_g (x1, mult a (subv sP y1), D)
val () = out ("DBG_ld1="^Syntax.string_of_term ctxtG (Thm.prop_of ld1)^"\n");
val inAssoc = addassoc_g (mult a (subv sP y1), mult a y1, mult a y2)
val inAssoc_s = oeqSym_g inAssoc
val () = out ("DBG_inAssoc_s="^Syntax.string_of_term ctxtG (Thm.prop_of inAssoc_s)^"\n");
val toAs = add_cong_l_g (add (mult a (subv sP y1)) (mult a y1), as_, mult a y2) asr1
val () = out ("DBG_toAs="^Syntax.string_of_term ctxtG (Thm.prop_of toAs)^"\n");
val inner1 = oeqTrans_g (inAssoc_s, toAs)
val () = out "DBG_inner1_ok\n";
val ld2 = oeqTrans_g (ld1, add_cong_r_g (x1, add (mult a (subv sP y1)) D, add as_ (mult a y2)) inner1)
val () = out "DBG_ld2_ok\n";
val commAs = addcomm_g (as_, mult a y2)
val ld3 = oeqTrans_g (ld2, add_cong_r_g (x1, add as_ (mult a y2), add (mult a y2) as_) commAs)
val () = out "DBG_ld3_ok\n";
val assocBack1 = addassoc_g (x1, mult a y2, as_)
val ld_final = oeqTrans_g (ld3, oeqSym_g assocBack1)
val () = out "DBG_ld_final_ok\n";
val asr2 = a_sub_recover (a, sP, y2) hle2
val rd1 = addassoc_g (x2, mult a (subv sP y2), D)
val commD = addcomm_g (mult a y1, mult a y2)
val dswap = add_cong_r_g (mult a (subv sP y2), D, add (mult a y2) (mult a y1)) commD
val () = out "DBG_dswap_ok\n";
val rInAssoc = addassoc_g (mult a (subv sP y2), mult a y2, mult a y1)
val rInAssoc_s = oeqSym_g rInAssoc
val rToAs = add_cong_l_g (add (mult a (subv sP y2)) (mult a y2), as_, mult a y1) asr2
val rInner = oeqTrans_g (oeqTrans_g (dswap, rInAssoc_s), rToAs)
val () = out "DBG_rInner_ok\n";
val rd2 = oeqTrans_g (rd1, add_cong_r_g (x2, add (mult a (subv sP y2)) D, add as_ (mult a y1)) rInner)
val () = out "DBG_rd2_ok\n";
val rcommAs = addcomm_g (as_, mult a y1)
val rd3 = oeqTrans_g (rd2, add_cong_r_g (x2, add as_ (mult a y1), add (mult a y1) as_) rcommAs)
val rassocBack = addassoc_g (x2, mult a y1, as_)
val rd_final = oeqTrans_g (rd3, oeqSym_g rassocBack)
val () = out "DBG_rd_final_ok\n";
(* finale *)
val crefl = cong_refl_g (pP, D)
val H = Thm.assume (ctermG (jT (cong pP Lc Rc)))
val congLD_RD = cong_add_g (pP, Lc, Rc, D, D) H crefl
val () = out "DBG_congLDRD_ok\n";
val zc1 = Free("zc1_rc", natT)
val P1 = Term.lambda zc1 (cong pP zc1 (add Rc D))
val st1 = oeq_rw_g (P1, add Lc D, add (add x1 (mult a y2)) as_) ld_final congLD_RD
val () = out "DBG_st1_ok\n";
val zc2 = Free("zc2_rc", natT)
val P2 = Term.lambda zc2 (cong pP (add (add x1 (mult a y2)) as_) zc2)
val st2 = oeq_rw_g (P2, add Rc D, add (add x2 (mult a y1)) as_) rd_final st1
val () = out "DBG_st2_ok\n";
val res = cong_radd_cancel_g (pP, add x1 (mult a y2), add x2 (mult a y1), as_) st2
val target = jT (cong pP (add x1 (mult a y2)) (add x2 (mult a y1)))
val () = out ("DBG_res aconv="^Bool.toString ((Thm.prop_of res) aconv target)^"\n");
val () = out "THUE_STAGE3B_DONE\n";

(* ============================================================================
   STAGE 4.  DECODE LEMMAS.
   For code c and modulus (Suc s): i = rdivv c (Suc s), j = rmodv c (Suc s).
     lt_zero_suc   : lt Zero (Suc s)                 [Suc positive]
     j_le_s        : le (rmodv c (Suc s)) s          [from rmod_lt + lt_suc_cases]
     decode_id     : oeq c (add (mult (Suc s) (rdivv c (Suc s))) (rmodv c (Suc s)))
   ============================================================================ *)
val () = out "THUE_STAGE4_BEGIN\n";

(* lt Zero (Suc s) : le (Suc 0)(Suc s) ; witness s, Suc s = Suc 0 + s ? need oeq (Suc s)(add (Suc 0) s).
   add (Suc 0) s = Suc(0+s) = Suc s.  le (Suc 0)(Suc s) with witness s. *)
fun lt_zero_suc_g sP =
  let val aS = addSuc_g (ZeroC, sP)         (* (Suc 0 + s) = Suc(0+s) *)
      val a0 = add0_g sP                      (* (0+s) = s *)
      val sa0 = Suc_cong_g a0                 (* Suc(0+s) = Suc s *)
      val sum = oeqTrans_g (aS, sa0)          (* (Suc 0 + s) = Suc s *)
      val sumS = oeqSym_g sum                 (* Suc s = (Suc 0 + s) *)
  in le_intro_g (suc ZeroC, suc sP, sP) sumS end;

(* j_le_s : le (rmodv c (Suc s)) s.  lt (rmodv c (Suc s)) (Suc s) [rmod_lt]; lt_suc_cases gives
   Disj (lt j s)(oeq j s); both -> le j s (lt_imp_le / le from oeq via le_refl rewrite). *)
fun lt_imp_le_g (at,bt) hlt =   (* lt a b = le (Suc a) b ; want le a b. via le_suc_cancel-like? use base lt? *)
  (* le a b : witness from lt a b = Ex(%p. b = Suc a + p) -> b = a + Suc p *)
  let val Pd = Abs("p", natT, oeq bt (add (suc at) (Bound 0)))
      val goalC = le at bt
      fun bd p (hp:thm) =       (* hp : oeq b (Suc a + p) *)
        let val aS = addSuc_g (at, p)          (* (Suc a + p) = Suc(a+p) *)
            val b_S = oeqTrans_g (hp, aS)       (* b = Suc(a+p) *)
            val aSp = addSucr_g (at, p)         (* (a + Suc p) = Suc(a+p) *)
            val b_aSp = oeqTrans_g (b_S, oeqSym_g aSp)  (* b = (a + Suc p) *)
        in le_intro_g (at, bt, suc p) b_aSp end
  in exE_g (Pd, goalC) hlt "pli" natT bd end;

fun j_le_s_g (cP, sP) =
  let val pos = lt_zero_suc_g sP               (* lt 0 (Suc s) *)
      val jlt = rmod_lt_g (cP, suc sP) pos      (* lt (rmodv c (Suc s)) (Suc s) *)
      val jr  = rmodv cP (suc sP)
      val dj  = lt_suc_cases_g (jr, sP) jlt     (* Disj (lt j s)(oeq j s) *)
      val caseLt = let val h=Thm.assume (ctermG (jT (lt jr sP)))
                   in Thm.implies_intr (ctermG (jT (lt jr sP))) (lt_imp_le_g (jr, sP) h) end
      val caseEq = let val h=Thm.assume (ctermG (jT (oeq jr sP)))
                       (* oeq j s -> le j s : le_refl s rewritten first arg s->j *)
                       val lr = le_refl_g sP        (* le s s *)
                       val zl = Free("zjls", natT)
                       val P = Term.lambda zl (le zl sP)
                       val hs = oeqSym_g h           (* s = j *)
                       val res = oeq_rw_g (P, sP, jr) hs lr   (* le j s *)
                   in Thm.implies_intr (ctermG (jT (oeq jr sP))) res end
  in disjE_g (lt jr sP, oeq jr sP, le jr sP) dj caseLt caseEq end;

fun decode_id_g (cP, sP) =
  let val pos = lt_zero_suc_g sP
  in divmod_id_g (cP, suc sP) pos end;      (* oeq c (add (mult (Suc s)(rdivv c (Suc s)))(rmodv c (Suc s))) *)

val () = out "THUE_STAGE4_FNS_READY\n";
val () =
  let val cP=Free("cc4",natT); val sP=Free("ss4",natT)
      val jls = j_le_s_g (cP, sP)
      val did = decode_id_g (cP, sP)
  in out ("decode jls nhyps="^Int.toString (length (Thm.hyps_of jls))
          ^" did nhyps="^Int.toString (length (Thm.hyps_of did))^"\n") end;
val () = out "THUE_STAGE4_DONE\n";

(* ============================================================================
   STAGE 5.  i_le_s : lt c (mult (Suc s)(Suc s)) ==> le (rdivv c (Suc s)) s.
   Contrapositive: if NOT le i s (i.e. lt s i, i.e. le (Suc s) i) then
     N = (Suc s)*(Suc s) <= (Suc s)*i <= (Suc s)*i + j = c, so NOT lt c N.
   We do it by ex_middle on (le i s).
   ============================================================================ *)
val () = out "THUE_STAGE5_BEGIN\n";

fun i_le_s_g (cP, sP) hltcN =
  let
    val i  = rdivv cP (suc sP)
    val j  = rmodv cP (suc sP)
    val N  = mult (suc sP) (suc sP)
    val did = decode_id_g (cP, sP)            (* c = (Suc s)*i + j *)
    val em  = em_g (le i sP)                   (* Disj (le i s)(neg (le i s)) *)
    val caseYes = let val h=Thm.assume (ctermG (jT (le i sP)))
                  in Thm.implies_intr (ctermG (jT (le i sP))) h end
    val caseNo =
      let val hneg = Thm.assume (ctermG (jT (neg (le i sP))))
          (* neg (le i s) -> lt s i [nlt_le contrapositive form]; nlt_le_g (d,c): neg(lt d c) -> le c d.
             We have neg(le i s); want lt s i = le (Suc s) i. Use le_total: Disj (le i s)(le s i).
             Actually need STRICT lt s i = le (Suc s) i. From neg(le i s) and le_total (le i s)|(le s i):
               first disjunct contradicts hneg; so le s i. But need le (Suc s) i (strict).
             le s i + neg(le i s): if i=s then le i s (le_refl-ish via oeq)... Use le_eq_or_lt? not on ctxtG.
             Simpler: from neg(le i s), derive le (Suc s) i via: ex_middle on lt s i.
               lt s i = le (Suc s) i.  Disj (lt s i)(neg(lt s i)); neg(lt s i)=neg(le(Suc s) i) -> le i s [nlt_le] contra. *)
          val em2 = em_g (lt sP i)             (* Disj (lt s i)(neg (lt s i)) *)
          val getLtSi =
            let val cA = let val h=Thm.assume (ctermG (jT (lt sP i)))
                         in Thm.implies_intr (ctermG (jT (lt sP i))) h end
                val cB = let val h=Thm.assume (ctermG (jT (neg (lt sP i))))
                             (* neg (lt s i) -> le i s [nlt_le_g (s, i)] contradiction with hneg *)
                             val leis = nlt_le_g (sP, i) h   (* le i s *)
                             val fls  = mp_g (le i sP, oFalseC) hneg leis
                         in Thm.implies_intr (ctermG (jT (neg (lt sP i)))) (Thm.implies_elim (oFalse_elim_g (lt sP i)) fls) end
            in disjE_g (lt sP i, neg (lt sP i), lt sP i) em2 cA cB end
          (* lt s i = le (Suc s) i *)
          val le_Ss_i = getLtSi                  (* le (Suc s) i *)
          val () = out "DBG5_getLtSi_ok\n"
          (* (Suc s)*(Suc s) <= (Suc s)*i  via mult_le_mono (c:=Suc s, j:=Suc s, k:=i) *)
          val leN_Ssi = mult_le_mono_g (suc sP, suc sP, i) le_Ss_i   (* le ((Suc s)*(Suc s)) ((Suc s)*i) *)
          val () = out "DBG5_leN_Ssi_ok\n"
          (* (Suc s)*i <= (Suc s)*i + j = c *)
          val le_Ssi_sum = le_add_g (mult (suc sP) i, j)             (* le ((Suc s)*i) ((Suc s)*i + j) *)
          val () = out "DBG5_le_add_ok\n"
          (* rewrite ((Suc s)*i + j) -> c via did (sym) on %z. le ((Suc s)*i) z *)
          val zl = Free("zils", natT)
          val Pl = Term.lambda zl (le (mult (suc sP) i) zl)
          val did_s = oeqSym_g did              (* ((Suc s)*i + j) = c *)
          val le_Ssi_c = oeq_rw_g (Pl, add (mult (suc sP) i) j, cP) did_s le_Ssi_sum  (* le ((Suc s)*i) c *)
          val () = out "DBG5_le_Ssi_c_ok\n"
          val leN_c = le_trans_g (N, mult (suc sP) i, cP) leN_Ssi le_Ssi_c   (* le N c *)
          val () = out "DBG5_leN_c_ok\n"
          (* lt c N = le (Suc c) N ; with le N c -> le (Suc c) c -> lt c c -> False *)
          val le_Sc_c = le_trans_g (suc cP, N, cP) hltcN leN_c    (* le (Suc c) c = lt c c *)
          val () = out "DBG5_le_Sc_c_ok\n"
          val fls = lt_irrefl_g cP le_Sc_c
          val res = Thm.implies_elim (oFalse_elim_g (le i sP)) fls
      in Thm.implies_intr (ctermG (jT (neg (le i sP)))) res end
  in disjE_g (le i sP, neg (le i sP), le i sP) em caseYes caseNo end;

val () = out "THUE_STAGE5_FNS_READY\n";
val () =
  let val cP=Free("cc5",natT); val sP=Free("ss5",natT)
      val hlt = Thm.assume (ctermG (jT (lt cP (mult (suc sP)(suc sP)))))
      val r = i_le_s_g (cP, sP) hlt
      val tgt = jT (le (rdivv cP (suc sP)) sP)
  in out ("i_le_s aconv="^Bool.toString ((Thm.prop_of r) aconv tgt)
          ^" nhyps="^Int.toString (length (Thm.hyps_of r))^"\n") end;
val () = out "THUE_STAGE5_DONE\n";

(* ============================================================================
   STAGE 6.  RESIDUE -> CONG BRIDGE.
     cong_of_rmod : 0<p ==> oeq (rmodv x p)(rmodv y p) ==> cong p x y.
   From divmod_id: x = p*(x div p) + (x mod p) ; so cong p x (x mod p) [witness x div p, RIGHT
   disjunct: x = (x mod p) + p*(x div p)].  Likewise cong p y (y mod p).  Then
   x ~ x mod p = y mod p ~ y by trans (+ sym).
   ============================================================================ *)
val () = out "THUE_STAGE6_BEGIN\n";

(* cong p x (rmodv x p) from divmod_id : need x = (rmodv x p) + p*(rdivv x p) [congR witness rdivv] *)
fun cong_x_rmod (xP, pP) hpos =
  let
    val did = divmod_id_g (xP, pP) hpos     (* x = p*(rdivv x p) + (rmodv x p) *)
    (* rearrange RHS to (rmodv x p) + p*(rdivv x p) [comm] *)
    val comm = addcomm_g (mult pP (rdivv xP pP), rmodv xP pP)   (* (p*div + mod) = (mod + p*div) *)
    val x_eq = oeqTrans_g (did, comm)        (* x = (rmodv x p) + p*(rdivv x p) *)
    (* congR : x = (rmodv x p) + p*w  => cong p (rmodv x p) x  via disjI2 on congR body.
       cong p a b = Disj (Ex k. b = a + p*k)(Ex k. a = b + p*k).
       want cong p x (rmodv x p): need Ex k. (rmodv x p) = x + p*k  OR  x = (rmodv x p) + p*k.
       We have the SECOND (x = mod + p*div), witness div -> congR -> disjI2. *)
    val RAbs = Abs("k", natT, oeq xP (add (rmodv xP pP) (mult pP (Bound 0))))
    val exThm = exI_g RAbs (rdivv xP pP) x_eq
  in disjI2_g (mkEx (Abs("k",natT, oeq (rmodv xP pP) (add xP (mult pP (Bound 0))))),
               mkEx (Abs("k",natT, oeq xP (add (rmodv xP pP) (mult pP (Bound 0)))))) exThm end;
                                              (* cong p x (rmodv x p) *)

fun cong_of_rmod (xP, yP, pP) hpos heq =     (* heq : oeq (rmodv x p)(rmodv y p) *)
  let
    val cx = cong_x_rmod (xP, pP) hpos        (* cong p x (rmodv x p) *)
    val cy = cong_x_rmod (yP, pP) hpos        (* cong p y (rmodv y p) *)
    val cy_s = cong_sym_g (pP, yP, rmodv yP pP) cy   (* cong p (rmodv y p) y *)
    (* rewrite cx's 2nd arg (rmodv x p) -> (rmodv y p) via heq on %z. cong p x z *)
    val zc = Free("zcr", natT)
    val P = Term.lambda zc (cong pP xP zc)
    val cx2 = oeq_rw_g (P, rmodv xP pP, rmodv yP pP) heq cx   (* cong p x (rmodv y p) *)
    val res = cong_trans_g (pP, xP, rmodv yP pP, yP) cx2 cy_s  (* cong p x y *)
  in res end;
val () = out "THUE_STAGE6_FNS_READY\n";
val () =
  let val xP=Free("xx6",natT); val yP=Free("yy6",natT); val pP=Free("pp6",natT)
      val hpos = Thm.assume (ctermG (jT (lt ZeroC pP)))
      val heq  = Thm.assume (ctermG (jT (oeq (rmodv xP pP)(rmodv yP pP))))
      val r = cong_of_rmod (xP, yP, pP) hpos heq
      val tgt = jT (cong pP xP yP)
  in out ("cong_of_rmod aconv="^Bool.toString ((Thm.prop_of r) aconv tgt)
          ^" nhyps="^Int.toString (length (Thm.hyps_of r))^"\n") end;
val () = out "THUE_STAGE6_DONE\n";

(* ============================================================================
   STAGE 7.  THE RESIDUE LIST + ITS PROPERTIES (members < p, length N).
   Define gres c = rmodv (gval c) p  where gval c = i + a*(s - j),
   i = rdivv c (Suc s), j = rmodv c (Suc s).  Build gridres recursively.
   Then prove (under 0<p):
     gridmem_lt_p : (!e. lmem e (gridres s p n) ==> lt e p)      [induction on n]
     gridlen      : oeq (llen (gridres s p n)) n                 [induction on n]
   We make gres/gridres parametric in s,p so the const is sound (the lemmas hold
   for ALL s,p; we instantiate at our fixed s,p later).
   ============================================================================ *)
val () = out "THUE_STAGE7_BEGIN\n";

(* gval as a TERM-level function of (s,p?,c) -- no const needed; gval only uses s and a (a Free). *)
fun gvalT sP cP =
  add (rdivv cP (suc sP)) (mult aTH (subv sP (rmodv cP (suc sP))));
(* gres c = rmodv (gval c) p *)
fun gresT (sP, pP) cP = rmodv (gvalT sP cP) pP;

(* gridres const : nat(s) -> nat(p) -> nat(n) -> natlist, by recursion on n. *)
val thyGRc = Sign.add_consts
  [(Binding.name "gridres", natT --> natT --> natT --> natlistT, NoSyn)] thyDM;
fun cnstGR nm T = Const (Sign.full_name thyGRc (Binding.name nm), T);
val gridresC = cnstGR "gridres" (natT --> natT --> natT --> natlistT);
fun gridres s p n = gridresC $ s $ p $ n;

val sGR = Free("s_gr", natT); val pGR = Free("p_gr", natT); val nGR = Free("n_gr", natT);
val ((_,gridres_zero_ax), thyGR1) = Thm.add_axiom_global (Binding.name "gridres_zero",
      jT (leq (gridres sGR pGR ZeroC) lnilC)) thyGRc;
val ((_,gridres_suc_ax), thyGR) = Thm.add_axiom_global (Binding.name "gridres_suc",
      jT (leq (gridres sGR pGR (suc nGR))
              (lcons (gresT (sGR,pGR) nGR) (gridres sGR pGR nGR)))) thyGR1;

val ctxtGR  = Proof_Context.init_global thyGR;
val ctermGR = Thm.cterm_of ctxtGR;
val () = out "THUE_STAGE7_CONSTS_READY\n";

(* minimal re-varify onto ctxtGR (suffix _r) for the two gridres properties *)
val gridres_zero_vR = varify gridres_zero_ax;
val gridres_suc_vR  = varify gridres_suc_ax;
val rmod_lt_vR      = varify rmod_lt_ax;
val leq_subst_vR    = varify leq_subst_ax;
val leq_sym_vR      = varify leq_sym;
val leq_refl_vR     = varify leq_refl_ax;
val oeq_refl_vR     = varify oeq_refl;
val oeq_sym_vR      = varify oeq_sym;
val oeq_trans_vR    = varify oeq_trans;
val oeq_subst_vR    = varify oeq_subst;
val Suc_cong_vR     = varify Suc_cong;
val nat_induct_vR   = varify nat_induct;
val llen_nil_vR     = varify llen_nil_ax;
val llen_cons_vR    = varify llen_cons_ax;
val lmem_nil_elim_vR= varify lmem_nil_elim_ax;
val lmem_cons_fwd_vR= varify lmem_cons_fwd_ax;
val mp_vR           = varify mp_ax;
val impI_vR         = varify impI_ax;
val allI_vR         = varify allI_ax;
val allE_vR         = varify allE_ax;
val disjE_vR        = varify disjE_ax;
val oFalse_elim_vR  = varify oFalse_elim_ax;

fun oeqRefl_r x = beta_norm (Drule.infer_instantiate ctxtGR [(("a",0), ctermGR x)] oeq_refl_vR);
fun oeqSym_r h = oeq_sym_vR OF [h];
fun oeqTrans_r (h1,h2) = oeq_trans_vR OF [h1,h2];
fun Suc_cong_r h = Suc_cong_vR OF [h];
fun leq_sym_r h = leq_sym_vR OF [h];
fun leqRefl_r l = beta_norm (Drule.infer_instantiate ctxtGR [(("a",0), ctermGR l)] leq_refl_vR);
fun leq_rw_r (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR [(("P",0), ctermGR Pabs),(("a",0), ctermGR aT),(("b",0), ctermGR bT)] leq_subst_vR)
  in inst OF [hab, hPa] end;
fun oeq_rw_r (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR [(("P",0), ctermGR Pabs),(("a",0), ctermGR aT),(("b",0), ctermGR bT)] oeq_subst_vR)
  in inst OF [hab, hPa] end;
fun llenNil_r () = llen_nil_vR;
fun llenCons_r (h,t) = beta_norm (Drule.infer_instantiate ctxtGR [(("x",0), ctermGR h),(("t",0), ctermGR t)] llen_cons_vR);
fun lmemNilElim_r x = beta_norm (Drule.infer_instantiate ctxtGR [(("x",0), ctermGR x)] lmem_nil_elim_vR);
fun lmemConsFwd_r (x,y,t) = beta_norm (Drule.infer_instantiate ctxtGR [(("x",0), ctermGR x),(("y",0), ctermGR y),(("t",0), ctermGR t)] lmem_cons_fwd_vR);
fun mp_r (At,Bt) hImp hA = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] mp_vR)) hImp) hA;
fun impI_r (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] impI_vR)) h;
fun allI_r Pabs h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR [(("P",0), ctermGR Pabs)] allI_vR)) h;
fun allE_r Pabs at h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR [(("P",0), ctermGR Pabs),(("a",0), ctermGR at)] allE_vR)) h;
fun disjE_r (At,Bt,Ct) dThm cA cB = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR [(("A",0), ctermGR At),(("B",0), ctermGR Bt),(("C",0), ctermGR Ct)] disjE_vR)) dThm) cA) cB;
fun oFalse_elim_r rT = beta_norm (Drule.infer_instantiate ctxtGR [(("R",0), ctermGR rT)] oFalse_elim_vR);
fun rmod_lt_r (ct,dt) hpos = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR [(("c_dm",0), ctermGR ct),(("d_dm",0), ctermGR dt)] rmod_lt_vR)) hpos;
fun nat_induct_r Pabs kT baseThm stepThm =
  let val ind = beta_norm (Drule.infer_instantiate ctxtGR [(("P",0), ctermGR Pabs),(("k",0), ctermGR kT)] nat_induct_vR)
  in Thm.implies_elim (Thm.implies_elim ind baseThm) stepThm end;
fun gridresZero_r (s,p) = beta_norm (Drule.infer_instantiate ctxtGR [(("s_gr",0), ctermGR s),(("p_gr",0), ctermGR p)] gridres_zero_vR);
fun gridresSuc_r (s,p,n) = beta_norm (Drule.infer_instantiate ctxtGR [(("s_gr",0), ctermGR s),(("p_gr",0), ctermGR p),(("n_gr",0), ctermGR n)] gridres_suc_vR);
(* lt_zero_suc on ctxtGR (for positivity of Suc s in gval's div/mod -- not needed here; rmod_lt uses 0<p) *)
val () = out "THUE_STAGE7_VARIFY_READY\n";

(* ---- gridlen : oeq (llen (gridres s p n)) n   (induction on n) ---- *)
fun gridlen_g (sP, pP) =
  let
    val Pabs = Term.lambda (Free("n_gl", natT)) (oeq (llen (gridres sP pP (Free("n_gl",natT)))) (Free("n_gl",natT)))
    val base =
      let val r0 = gridresZero_r (sP, pP)              (* leq (gridres s p 0) lnil *)
          val llN = llenNil_r ()                        (* oeq (llen lnil) 0 *)
          val r0s = leq_sym_r r0                         (* leq lnil (gridres s p 0) *)
          val zN = Free("zgl0", natlistT)
          val P = Term.lambda zN (oeq (llen zN) ZeroC)
      in leq_rw_r (P, lnilC, gridres sP pP ZeroC) r0s llN end
    val step =
      let val xF = Free("x_gl", natT)
          val ihP = jT (oeq (llen (gridres sP pP xF)) xF)
          val hIH = Thm.assume (ctermGR ihP)
          val rSuc = gridresSuc_r (sP, pP, xF)           (* leq (gridres s p (Suc x)) (lcons (gres x)(gridres s p x)) *)
          val gx = gresT (sP,pP) xF
          val llc = llenCons_r (gx, gridres sP pP xF)    (* oeq (llen (lcons (gres x)(gridres s p x))) (Suc(llen(gridres s p x))) *)
          val sucIH = Suc_cong_r hIH                      (* oeq (Suc(llen(gridres s p x)))(Suc x) *)
          val eqCons = oeqTrans_r (llc, sucIH)            (* oeq (llen (lcons ..)) (Suc x) *)
          val zN = Free("zgls", natlistT)
          val P = Term.lambda zN (oeq (llen zN) (suc xF))
          val rSuc_s = leq_sym_r rSuc
      in Thm.forall_intr (ctermGR xF) (Thm.implies_intr (ctermGR ihP)
           (leq_rw_r (P, lcons gx (gridres sP pP xF), gridres sP pP (suc xF)) rSuc_s eqCons)) end
    val kF = Free("k_gl", natT)
  in (kF, nat_induct_r Pabs kF base step) end;  (* returns (kVar, thm : oeq (llen (gridres s p k)) k) *)

(* ---- gridmem_lt_p : 0<p ==> !e. lmem e (gridres s p n) ==> lt e p  (induction on n) ---- *)
fun gridmem_lt_p_g (sP, pP) hpos =
  let
    fun memBody n = let val ef=Free("e_gm",natT)
                    in mkForall (Term.lambda ef (mkImp (lmem ef (gridres sP pP n)) (lt ef pP))) end
    val Pabs = Term.lambda (Free("n_gm", natT)) (memBody (Free("n_gm",natT)))
    val base =
      let val ef=Free("e_gm",natT)
          val r0 = gridresZero_r (sP, pP)
          val body =
            let val hm = Thm.assume (ctermGR (jT (lmem ef (gridres sP pP ZeroC))))
                (* transfer to lmem e lnil via r0 *)
                val zN=Free("zgm0",natlistT)
                val Pm=Term.lambda zN (lmem ef zN)
                val memNil = leq_rw_r (Pm, gridres sP pP ZeroC, lnilC) r0 hm
                val fls = Thm.implies_elim (lmemNilElim_r ef) memNil
                val concl = Thm.implies_elim (oFalse_elim_r (lt ef pP)) fls
            in impI_r (lmem ef (gridres sP pP ZeroC), lt ef pP)
                 (Thm.implies_intr (ctermGR (jT (lmem ef (gridres sP pP ZeroC)))) concl) end
      in allI_r (Term.lambda ef (mkImp (lmem ef (gridres sP pP ZeroC)) (lt ef pP)))
           (Thm.forall_intr (ctermGR ef) body) end
    val step =
      let val xF=Free("x_gm",natT)
          val ihP = jT (memBody xF)
          val hIH = Thm.assume (ctermGR ihP)
          val ef=Free("e_gm",natT)
          val gx = gresT (sP,pP) xF
          val rSuc = gridresSuc_r (sP, pP, xF)
          val body =
            let val hm = Thm.assume (ctermGR (jT (lmem ef (gridres sP pP (suc xF)))))
                (* transfer to cons via rSuc *)
                val zN=Free("zgms",natlistT)
                val Pm=Term.lambda zN (lmem ef zN)
                val memCons = leq_rw_r (Pm, gridres sP pP (suc xF), lcons gx (gridres sP pP xF)) rSuc hm
                val dj = Thm.implies_elim (lmemConsFwd_r (ef, gx, gridres sP pP xF)) memCons  (* Disj (oeq e (gres x))(lmem e (gridres s p x)) *)
                (* case oeq e (gres x): gres x = rmodv (gval x) p < p [rmod_lt]; rewrite e=gres x *)
                val caseEq =
                  let val heq = Thm.assume (ctermGR (jT (oeq ef gx)))
                      val ltgx = rmod_lt_r (gvalT sP xF, pP) hpos   (* lt (rmodv (gval x) p) p = lt (gres x) p *)
                      val heq_s = oeqSym_r heq                       (* (gres x) = e *)
                      val zl=Free("zgmlt",natT)
                      val Plt=Term.lambda zl (lt zl pP)
                      val res = oeq_rw_r (Plt, gx, ef) heq_s ltgx     (* lt e p *)
                  in Thm.implies_intr (ctermGR (jT (oeq ef gx))) res end
                (* case lmem e (gridres s p x): IH *)
                val caseMem =
                  let val hmx = Thm.assume (ctermGR (jT (lmem ef (gridres sP pP xF))))
                      val ihAt = allE_r (Term.lambda ef (mkImp (lmem ef (gridres sP pP xF)) (lt ef pP))) ef hIH
                      val res = mp_r (lmem ef (gridres sP pP xF), lt ef pP) ihAt hmx
                  in Thm.implies_intr (ctermGR (jT (lmem ef (gridres sP pP xF)))) res end
                val ltThm = disjE_r (oeq ef gx, lmem ef (gridres sP pP xF), lt ef pP) dj caseEq caseMem
            in impI_r (lmem ef (gridres sP pP (suc xF)), lt ef pP)
                 (Thm.implies_intr (ctermGR (jT (lmem ef (gridres sP pP (suc xF))))) ltThm) end
          val allStep = allI_r (Term.lambda ef (mkImp (lmem ef (gridres sP pP (suc xF))) (lt ef pP)))
                          (Thm.forall_intr (ctermGR ef) body)
      in Thm.forall_intr (ctermGR xF) (Thm.implies_intr (ctermGR ihP) allStep) end
    val kF = Free("k_gm", natT)
  in (kF, nat_induct_r Pabs kF base step) end;  (* (kVar, thm : !e. lmem e (gridres s p k) ==> lt e p) *)

val () = out "THUE_STAGE7_PROPS_FNS_READY\n";
val () =
  let val sP=Free("ssg",natT); val pP=Free("ppg",natT)
      val hpos = Thm.assume (ctermGR (jT (lt ZeroC pP)))
      val (kl, gl) = gridlen_g (sP, pP)
      val (km, gm) = gridmem_lt_p_g (sP, pP) hpos
  in out ("gridlen nhyps="^Int.toString (length (Thm.hyps_of gl))
          ^" gridmem nhyps="^Int.toString (length (Thm.hyps_of gm))^"\n") end;
val () = out "THUE_STAGE7_DONE\n";

(* ============================================================================
   STAGE 8.  APPLY PIGEONHOLE -> residue collision exists.
   list_pigeonhole (on ctxtTH): (!e. lmem e RL ==> lt e k) ==> lt k (llen RL)
                                  ==> neg (lnodup RL).
   Re-varify onto ctxtGR; apply with RL = gridres s p N, k = p, where
   N = (Suc s)(Suc s), llen RL = N, members < p, and lt p N (from floor_sqrt).
   Yields neg (lnodup (gridres s p N)) : the residue list has a DUPLICATE, i.e.
   two grid codes have the same residue == a collision.
   ============================================================================ *)
val () = out "THUE_STAGE8_BEGIN\n";
val list_pigeonhole_vR = varify list_pigeonhole;
fun list_pigeonhole_r (RLt, kt) hbnd hlt =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("RL_ph",0), ctermGR RLt),(("k_ph",0), ctermGR kt)] list_pigeonhole_vR)
      val ef = Free("e_ph", natT)
      val bndT = mkForall (Term.lambda ef (mkImp (lmem ef RLt) (lt ef kt)))
      val s1 = mp_r (bndT, mkImp (lt kt (llen RLt)) (neg (lnodup RLt))) inst hbnd
  in mp_r (lt kt (llen RLt), neg (lnodup RLt)) s1 hlt end;

(* collision_exists : 0<p ==> lt p (mult (Suc s)(Suc s)) ==> neg (lnodup (gridres s p ((Suc s)*(Suc s)))) *)
fun collision_exists (sP, pP) hpos hltpN =
  let
    val N = mult (suc sP) (suc sP)
    val (km, gm) = gridmem_lt_p_g (sP, pP) hpos     (* gm : !e. lmem e (gridres s p km) ==> lt e p ; km Free, carries 0<p hyp *)
    (* specialize km := N via forall_intr/forall_elim (keeps p Free, does NOT re-introduce 0<p premise) *)
    val gm_N = beta_norm (Thm.forall_elim (ctermGR N) (Thm.forall_intr (ctermGR km) gm))
                                                     (* !e. lmem e (gridres s p N) ==> lt e p *)
    val (kl, gl) = gridlen_g (sP, pP)
    val gl_N = beta_norm (Thm.forall_elim (ctermGR N) (Thm.forall_intr (ctermGR kl) gl))
                                                     (* oeq (llen (gridres s p N)) N *)
    (* lt p (llen (gridres s p N)) : from hltpN : lt p N and gl_N (sym) rewrite N -> llen.. in (lt p _) *)
    val gl_N_s = oeqSym_r gl_N                        (* oeq N (llen (gridres s p N)) *)
    val zl = Free("zce", natT)
    val Plt = Term.lambda zl (lt pP zl)
    val ltp_len = oeq_rw_r (Plt, N, llen (gridres sP pP N)) gl_N_s hltpN   (* lt p (llen (gridres s p N)) *)
    val res = list_pigeonhole_r (gridres sP pP N, pP) gm_N ltp_len
  in res end;  (* neg (lnodup (gridres s p N)) *)

val () = out "THUE_STAGE8_FNS_READY\n";
val () =
  let val sP=Free("ss8",natT); val pP=Free("pp8",natT)
      val hpos = Thm.assume (ctermGR (jT (lt ZeroC pP)))
      val hltpN = Thm.assume (ctermGR (jT (lt pP (mult (suc sP)(suc sP)))))
      val r = collision_exists (sP, pP) hpos hltpN
      val tgt = jT (neg (lnodup (gridres sP pP (mult (suc sP)(suc sP)))))
  in out ("collision_exists aconv="^Bool.toString ((Thm.prop_of r) aconv tgt)
          ^" nhyps="^Int.toString (length (Thm.hyps_of r))^"\n") end;
val () = out "THUE_STAGE8_DONE\n";

(* ============================================================================
   THUE GRID SUMMARY.  What is PROVED (all 0-hyp or conditional-as-noted):
     floor_sqrt / rangelist grid / list_pigeonhole          [foundation]
     sub_recover, divmod conservative axioms                [Stage 1-2]
     cong_radd_cancel        : cong m (a+w)(b+w) ==> cong m a b   (0-hyp)
     rearrange               : le y1 s ==> le y2 s ==>
                                 cong p (x1+a*(s-y1))(x2+a*(s-y2)) ==>
                                 cong p (x1+a*y2)(x2+a*y1)          (the algebraic heart)
     decode (j_le_s,i_le_s,decode_id) : code c < (Suc s)^2 decodes to i,j <= s
     cong_of_rmod            : 0<p ==> rmodv x p = rmodv y p ==> cong p x y
     gridlen / gridmem_lt_p  : the residue list has length N, all members < p
     collision_exists        : 0<p ==> lt p ((Suc s)^2)
                                 ==> neg (lnodup (gridres s p ((Suc s)^2)))
   I.e. the FULL pipeline up to "a residue collision EXISTS" + the complete
   algebraic bridge from a collision to the Thue target.  The remaining gap is
   recovering the two DISTINCT CODES from the duplicate-bearing residue list
   (positions->codes), the foundation's flagged hard step.
   ============================================================================ *)
val thue_partial =
  (length (Thm.hyps_of cong_radd_cancel) = 0);
val () = out ("THUE_GRID_SUMMARY radd_cancel0="^Bool.toString thue_partial^"\n");
val () = out "THUE_GRID_PARTIAL_OK\n";
(* ============================================================================
   THUE'S LEMMA — DIRECT CLOSURE (delta on top of isabelle_thue.sml).
   We have collision_exists : 0<p ==> lt p N ==> neg(lnodup (gridres s p N))
   (N=(Suc s)^2).  We:
     (1) reflect a residue-list member back to a code:
           mem_gridres_reflect : !e. lmem e (gridres s p n) ==> ?c. lt c n /\ oeq e (gres c)
     (2) image-collision pigeonhole for the CONCRETE residue gres:
           dup_gridres : neg(lnodup (gridres s p n))
                          ==> ?c1 c2. lt c1 n /\ lt c2 n /\ ~(c1=c2) /\ oeq (gres c1)(gres c2)
     (3) package Thue via floor_sqrt + decode + rearrange + cong_of_rmod.
   Everything on ctxtGR (where gridres lives; it extends ctxtG/ctxtTH).
   ============================================================================ *)
val () = out "THC_DELTA_BEGIN\n";

(* ---- re-varify the extra axioms/lemmas we need onto ctxtGR (suffix _r2) ---- *)
val conjI_vR2       = varify conjI_ax;
val conjunct1_vR2   = varify conjunct1_ax;
val conjunct2_vR2   = varify conjunct2_ax;
val disjI1_vR2      = varify disjI1_ax;
val disjI2_vR2      = varify disjI2_ax;
val exI_vR2         = varify exI_ax;
val exE_vR2         = varify exE_ax;
val ex_middle_vR2   = varify ex_middle_ax;
val Suc_neq_Zero_vR2= varify Suc_neq_Zero_ax;
val lnodup_cons_bwd_vR2 = varify lnodup_cons_bwd_ax;
val lnodup_nil_vR2      = varify lnodup_nil_ax;
val lmem_cons_bwd_vR2   = varify lmem_cons_bwd_ax;
val lt_irrefl_vR2   = varify lt_irrefl;
val lt_trans_vR2    = varify lt_trans;
val lt_suc_vR2      = varify lt_suc;
val oeq_refl_vR2    = varify oeq_refl;
val oeq_sym_vR2     = varify oeq_sym;
val oeq_trans_vR2   = varify oeq_trans;

fun conjI_r (At,Bt) hA hB = Thm.implies_elim (Thm.implies_elim
      (beta_norm (Drule.infer_instantiate ctxtGR [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] conjI_vR2)) hA) hB;
fun conjunct1_r (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] conjunct1_vR2)) h;
fun conjunct2_r (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] conjunct2_vR2)) h;
fun disjI1_r (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] disjI1_vR2)) h;
fun disjI2_r (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] disjI2_vR2)) h;
fun em_r t = beta_norm (Drule.infer_instantiate ctxtGR [(("A",0), ctermGR t)] ex_middle_vR2);
fun exI_r Pabs at hbody = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("P",0), ctermGR Pabs),(("a",0), ctermGR at)] exI_vR2)) hbody;
fun exE_r (Pabs, goalC) exThm wName wT bodyFn =
  let val wF = Free(wName, wT)
      val hypTerm = jT (Term.betapply (Pabs, wF))
      val hypThm  = Thm.assume (ctermGR hypTerm)
      val body    = bodyFn wF hypThm
      val minor   = Thm.forall_intr (ctermGR wF) (Thm.implies_intr (ctermGR hypTerm) body)
      val exE_inst= beta_norm (Drule.infer_instantiate ctxtGR [(("P",0), ctermGR Pabs),(("Q",0), ctermGR goalC)] exE_vR2)
  in Thm.implies_elim (Thm.implies_elim exE_inst exThm) minor end;
fun lnodupConsBwd_r (x,t) = beta_norm (Drule.infer_instantiate ctxtGR
      [(("x",0), ctermGR x),(("t",0), ctermGR t)] lnodup_cons_bwd_vR2);
fun lmemConsBwd_r (x,y,t) = beta_norm (Drule.infer_instantiate ctxtGR
      [(("x",0), ctermGR x),(("y",0), ctermGR y),(("t",0), ctermGR t)] lmem_cons_bwd_vR2);
fun lt_irrefl_r n hlt = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("n",0), ctermGR n)] lt_irrefl_vR2)) hlt;
fun lt_trans_r (a,b,c) h1 h2 = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("a",0), ctermGR a),(("b",0), ctermGR b),(("c",0), ctermGR c)] lt_trans_vR2)) h1) h2;
fun lt_suc_r n = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR n)] lt_suc_vR2);
fun oeqRefl_r2 x = beta_norm (Drule.infer_instantiate ctxtGR [(("a",0), ctermGR x)] oeq_refl_vR2);
fun oeqSym_r2 h = oeq_sym_vR2 OF [h];
fun oeqTrans_r2 (h1,h2) = oeq_trans_vR2 OF [h1,h2];
fun oFalseElim_r t = oFalse_elim_r t;   (* alias to existing ctxtGR oFalse_elim *)

(* the residue function as a term-fn on ctxtGR (mirrors gresT) *)
fun gres sP pP c = gresT (sP,pP) c;

val () = out "THC_VARIFY_READY\n";

(* lt c n ==> neg (oeq c n)   (c<n so c<>n; else lt n n by rewrite) *)
fun lt_imp_neq_r (cP, nP) hlt =
  let val hca = Thm.assume (ctermGR (jT (oeq cP nP)))   (* c = n *)
      val zl = Free("zlin", natT)
      val Plt = Term.lambda zl (lt zl nP)
      val ltnn = oeq_rw_r (Plt, cP, nP) hca hlt          (* lt n n *)
      val fls = lt_irrefl_r nP ltnn
      val metaImp = Thm.implies_intr (ctermGR (jT (oeq cP nP))) fls
  in impI_r (oeq cP nP, oFalseC) metaImp end;   (* neg (oeq c n) = oeq c n --> oFalse (object) *)

(* ============================================================================
   (1) mem_gridres_reflect : !e. lmem e (gridres s p n) ==> ?c. lt c n /\ oeq e (gres c)
   by induction on n.
   ============================================================================ *)
fun mem_gridres_reflect_g (sP, pP) =
  let
    fun reflBody n e = mkEx (Term.lambda (Free("c_rf",natT))
                         (mkConj (lt (Free("c_rf",natT)) n) (oeq e (gres sP pP (Free("c_rf",natT))))))
    fun allBody n = let val ef=Free("e_rf",natT)
                    in mkForall (Term.lambda ef (mkImp (lmem ef (gridres sP pP n)) (reflBody n ef))) end
    val Pabs = Term.lambda (Free("n_rf", natT)) (allBody (Free("n_rf",natT)))
    val base =
      let val ef=Free("e_rf",natT)
          val r0 = gridresZero_r (sP, pP)
          val body =
            let val hm = Thm.assume (ctermGR (jT (lmem ef (gridres sP pP ZeroC))))
                val zN=Free("zrf0",natlistT)
                val Pm=Term.lambda zN (lmem ef zN)
                val memNil = leq_rw_r (Pm, gridres sP pP ZeroC, lnilC) r0 hm
                val fls = Thm.implies_elim (lmemNilElim_r ef) memNil
                val concl = Thm.implies_elim (oFalseElim_r (reflBody ZeroC ef)) fls
            in impI_r (lmem ef (gridres sP pP ZeroC), reflBody ZeroC ef)
                 (Thm.implies_intr (ctermGR (jT (lmem ef (gridres sP pP ZeroC)))) concl) end
      in allI_r (Term.lambda ef (mkImp (lmem ef (gridres sP pP ZeroC)) (reflBody ZeroC ef)))
           (Thm.forall_intr (ctermGR ef) body) end
    val step =
      let val xF=Free("x_rf",natT)
          val ihP = jT (allBody xF)
          val hIH = Thm.assume (ctermGR ihP)
          val ef=Free("e_rf",natT)
          val gx = gres sP pP xF
          val rSuc = gridresSuc_r (sP, pP, xF)
          val body =
            let val hm = Thm.assume (ctermGR (jT (lmem ef (gridres sP pP (suc xF)))))
                val zN=Free("zrfs",natlistT)
                val Pm=Term.lambda zN (lmem ef zN)
                val memCons = leq_rw_r (Pm, gridres sP pP (suc xF), lcons gx (gridres sP pP xF)) rSuc hm
                val dj = Thm.implies_elim (lmemConsFwd_r (ef, gx, gridres sP pP xF)) memCons
                         (* Disj (oeq e (gres x))(lmem e (gridres s p x)) *)
                val goalC = reflBody (suc xF) ef
                (* case oeq e (gres x): witness c := x. lt x (Suc x), oeq e (gres x). *)
                val caseEq =
                  let val heq = Thm.assume (ctermGR (jT (oeq ef gx)))   (* e = gres x *)
                      val ltx = lt_suc_r xF                              (* lt x (Suc x) *)
                      val cj = conjI_r (lt xF (suc xF), oeq ef (gres sP pP xF)) ltx heq
                      val Pc = Term.lambda (Free("c_rf",natT))
                                 (mkConj (lt (Free("c_rf",natT)) (suc xF)) (oeq ef (gres sP pP (Free("c_rf",natT)))))
                      val ex = exI_r Pc xF cj
                  in Thm.implies_intr (ctermGR (jT (oeq ef gx))) ex end
                (* case lmem e (gridres s p x): IH gives ?c. lt c x /\ oeq e (gres c); lift c<x to c<Suc x. *)
                val caseMem =
                  let val hmx = Thm.assume (ctermGR (jT (lmem ef (gridres sP pP xF))))
                      val ihAt = allE_r (Term.lambda ef (mkImp (lmem ef (gridres sP pP xF)) (reflBody xF ef))) ef hIH
                      val exC = mp_r (lmem ef (gridres sP pP xF), reflBody xF ef) ihAt hmx
                      (* exC : ?c. lt c x /\ oeq e (gres c) ; exE to lift *)
                      val PcX = Term.lambda (Free("c_rf",natT))
                                  (mkConj (lt (Free("c_rf",natT)) xF) (oeq ef (gres sP pP (Free("c_rf",natT)))))
                      fun bodyC c (hc:thm) =     (* hc : lt c x /\ oeq e (gres c) *)
                        let val hlt = conjunct1_r (lt c xF, oeq ef (gres sP pP c)) hc
                            val heqe = conjunct2_r (lt c xF, oeq ef (gres sP pP c)) hc
                            val ltcSx = lt_trans_r (c, xF, suc xF) hlt (lt_suc_r xF)   (* lt c (Suc x) *)
                            val cj = conjI_r (lt c (suc xF), oeq ef (gres sP pP c)) ltcSx heqe
                            val Pc = Term.lambda (Free("c_rf",natT))
                                       (mkConj (lt (Free("c_rf",natT)) (suc xF)) (oeq ef (gres sP pP (Free("c_rf",natT)))))
                        in exI_r Pc c cj end
                      val res = exE_r (PcX, goalC) exC "cc_rf" natT bodyC
                  in Thm.implies_intr (ctermGR (jT (lmem ef (gridres sP pP xF)))) res end
                val resThm = disjE_r (oeq ef gx, lmem ef (gridres sP pP xF), goalC) dj caseEq caseMem
            in impI_r (lmem ef (gridres sP pP (suc xF)), goalC)
                 (Thm.implies_intr (ctermGR (jT (lmem ef (gridres sP pP (suc xF))))) resThm) end
          val allStep = allI_r (Term.lambda ef (mkImp (lmem ef (gridres sP pP (suc xF))) (reflBody (suc xF) ef)))
                          (Thm.forall_intr (ctermGR ef) body)
      in Thm.forall_intr (ctermGR xF) (Thm.implies_intr (ctermGR ihP) allStep) end
    val kF = Free("k_rf", natT)
  in (kF, nat_induct_r Pabs kF base step) end;
val () = out "THC_REFLECT_FN_READY\n";
val () =
  let val sP=Free("ssr",natT); val pP=Free("ppr",natT)
      val (k, th) = mem_gridres_reflect_g (sP, pP)
  in out ("mem_gridres_reflect nhyps="^Int.toString (length (Thm.hyps_of th))^"\n") end;
val () = out "THC_REFLECT_DONE\n";

(* ============================================================================
   (2) dup_gridres  (the IMAGE-COLLISION pigeonhole for the concrete residue):
     neg(lnodup (gridres s p n))
       ==> ?c1 c2. lt c1 n /\ lt c2 n /\ ~(oeq c1 c2) /\ oeq (gres c1)(gres c2)
   by induction on n.  Uses mem_gridres_reflect for the head-collision case.
   ============================================================================ *)
fun collPair sP pP n =     (* the existential conclusion at bound n *)
  let val c1f=Free("c1_dg",natT)
  in mkEx (Term.lambda c1f
       (mkEx (Term.lambda (Free("c2_dg",natT))
          (mkConj (lt c1f n)
            (mkConj (lt (Free("c2_dg",natT)) n)
              (mkConj (neg (oeq c1f (Free("c2_dg",natT))))
                      (oeq (gres sP pP c1f) (gres sP pP (Free("c2_dg",natT)))))))))) end;

(* build the existential ?c1 ?c2 conj from concrete witnesses + the conjunction thm *)
fun mkCollExists (sP,pP,n) (w1,w2) hconj =
  let
    (* inner ?c2 over c1:=w1 *)
    val Pc2 = Term.lambda (Free("c2_dg",natT))
                (mkConj (lt w1 n)
                  (mkConj (lt (Free("c2_dg",natT)) n)
                    (mkConj (neg (oeq w1 (Free("c2_dg",natT))))
                            (oeq (gres sP pP w1) (gres sP pP (Free("c2_dg",natT)))))))
    val ex2 = exI_r Pc2 w2 hconj
    val Pc1 = Term.lambda (Free("c1_dg",natT))
                (mkEx (Term.lambda (Free("c2_dg",natT))
                  (mkConj (lt (Free("c1_dg",natT)) n)
                    (mkConj (lt (Free("c2_dg",natT)) n)
                      (mkConj (neg (oeq (Free("c1_dg",natT)) (Free("c2_dg",natT))))
                              (oeq (gres sP pP (Free("c1_dg",natT))) (gres sP pP (Free("c2_dg",natT)))))))))
  in exI_r Pc1 w1 ex2 end;

fun dup_gridres_g (sP, pP) =
  let
    val Pabs = Term.lambda (Free("n_dg", natT))
                 (mkImp (neg (lnodup (gridres sP pP (Free("n_dg",natT))))) (collPair sP pP (Free("n_dg",natT))))
    (* base : n=0 : neg(lnodup (gridres s p 0)) is absurd (gridres s p 0 = lnil, lnodup lnil holds) *)
    val base =
      let val r0 = gridresZero_r (sP, pP)               (* leq (gridres s p 0) lnil *)
          val hneg = Thm.assume (ctermGR (jT (neg (lnodup (gridres sP pP ZeroC)))))
          (* lnodup (gridres s p 0) : from lnodup lnil + leq sym *)
      in
        let
          val zN=Free("zdg0",natlistT)
          val Pnd=Term.lambda zN (lnodup zN)
          val r0s = leq_sym_r r0                          (* leq lnil (gridres s p 0) *)
          val ndG = leq_rw_r (Pnd, lnilC, gridres sP pP ZeroC) r0s lnodup_nil_vR2  (* lnodup (gridres s p 0) *)
          val fls = mp_r (lnodup (gridres sP pP ZeroC), oFalseC) hneg ndG
          val concl = Thm.implies_elim (oFalseElim_r (collPair sP pP ZeroC)) fls
        in impI_r (neg (lnodup (gridres sP pP ZeroC)), collPair sP pP ZeroC)
             (Thm.implies_intr (ctermGR (jT (neg (lnodup (gridres sP pP ZeroC))))) concl) end
      end
    val step =
      let val xF=Free("x_dg",natT)
          val ihP = jT (mkImp (neg (lnodup (gridres sP pP xF))) (collPair sP pP xF))
          val hIH = Thm.assume (ctermGR ihP)
          val gx = gres sP pP xF
          val tailL = gridres sP pP xF
          val rSuc = gridresSuc_r (sP, pP, xF)            (* leq (gridres s p (Suc x)) (lcons gx tail) *)
          val goalC = collPair sP pP (suc xF)
          val hnegP = jT (neg (lnodup (gridres sP pP (suc xF))))
          val hneg = Thm.assume (ctermGR hnegP)
          (* ex_middle on lmem gx tail *)
          val em = em_r (lmem gx tailL)                   (* Disj (lmem gx tail)(neg (lmem gx tail)) *)
          (* CASE A : lmem gx tail -> reflect -> ?c. lt c x /\ oeq gx (gres c); pair (x,c) *)
          val caseA =
            let val hmem = Thm.assume (ctermGR (jT (lmem gx tailL)))
                val (kr, refl) = mem_gridres_reflect_g (sP, pP)
                (* refl : !e. lmem e (gridres s p kr) ==> ?c. lt c kr /\ oeq e (gres c) ; specialize kr:=x *)
                val refl_x = beta_norm (Thm.forall_elim (ctermGR xF) (Thm.forall_intr (ctermGR kr) refl))
                val ihAt = allE_r (Term.lambda (Free("e_rf",natT))
                              (mkImp (lmem (Free("e_rf",natT)) tailL)
                                 (mkEx (Term.lambda (Free("c_rf",natT))
                                    (mkConj (lt (Free("c_rf",natT)) xF)
                                            (oeq (Free("e_rf",natT)) (gres sP pP (Free("c_rf",natT))))))))) gx refl_x
                val exC = mp_r (lmem gx tailL,
                               mkEx (Term.lambda (Free("c_rf",natT))
                                  (mkConj (lt (Free("c_rf",natT)) xF) (oeq gx (gres sP pP (Free("c_rf",natT))))))) ihAt hmem
                val PcX = Term.lambda (Free("c_rf",natT))
                            (mkConj (lt (Free("c_rf",natT)) xF) (oeq gx (gres sP pP (Free("c_rf",natT)))))
                fun bodyC c (hc:thm) =     (* hc : lt c x /\ oeq gx (gres c) *)
                  let val hltc = conjunct1_r (lt c xF, oeq gx (gres sP pP c)) hc
                      val heqgx = conjunct2_r (lt c xF, oeq gx (gres sP pP c)) hc   (* oeq gx (gres c) *)
                      (* witnesses (x, c) : lt x (Suc x), lt c (Suc x), x<>c, oeq (gres x)(gres c) *)
                      val ltxSx = lt_suc_r xF
                      val ltcSx = lt_trans_r (c, xF, suc xF) hltc (lt_suc_r xF)
                      (* x <> c : from lt c x, c <> x, so x <> c (sym of neq).  neg(oeq x c). *)
                      val negcx = lt_imp_neq_r (c, xF) hltc       (* neg (oeq c x) *)
                      (* turn neg(oeq c x) into neg(oeq x c) *)
                      val negxc =
                        let val hxc = Thm.assume (ctermGR (jT (oeq xF c)))
                            val hcx = oeqSym_r2 hxc                 (* oeq c x *)
                            val fls = mp_r (oeq c xF, oFalseC) negcx hcx
                            val metaImp = Thm.implies_intr (ctermGR (jT (oeq xF c))) fls
                        in impI_r (oeq xF c, oFalseC) metaImp end   (* neg (oeq x c) = oeq x c --> oFalse *)
                      (* oeq (gres x)(gres c) : gx = gres x, heqgx : oeq gx (gres c) is exactly that *)
                      val gxgc = heqgx                              (* oeq (gres x)(gres c) *)
                      val cj = conjI_r (lt xF (suc xF),
                                  mkConj (lt c (suc xF))
                                    (mkConj (neg (oeq xF c)) (oeq (gres sP pP xF)(gres sP pP c))))
                                  ltxSx
                                  (conjI_r (lt c (suc xF), mkConj (neg (oeq xF c)) (oeq (gres sP pP xF)(gres sP pP c)))
                                     ltcSx
                                     (conjI_r (neg (oeq xF c), oeq (gres sP pP xF)(gres sP pP c)) negxc gxgc))
                  in mkCollExists (sP,pP,suc xF) (xF, c) cj end
                val res = exE_r (PcX, goalC) exC "cA_dg" natT bodyC
            in Thm.implies_intr (ctermGR (jT (lmem gx tailL))) res end
          (* CASE B : neg(lmem gx tail) -> neg(lnodup tail) -> IH -> lift *)
          val caseB =
            let val hnotmem = Thm.assume (ctermGR (jT (neg (lmem gx tailL))))
                (* claim neg(lnodup tail): if lnodup tail then lnodup(lcons gx tail) then lnodup(gridres (Suc x)) contra hneg *)
                val negNDtail =
                  let val hndtail = Thm.assume (ctermGR (jT (lnodup tailL)))
                      val cjND = conjI_r (neg (lmem gx tailL), lnodup tailL) hnotmem hndtail
                      val ndCons = Thm.implies_elim (lnodupConsBwd_r (gx, tailL)) cjND   (* lnodup (lcons gx tail) *)
                      (* transfer to lnodup (gridres s p (Suc x)) via rSuc sym *)
                      val zN=Free("zdgB",natlistT)
                      val Pnd=Term.lambda zN (lnodup zN)
                      val rSuc_s = leq_sym_r rSuc
                      val ndG = leq_rw_r (Pnd, lcons gx tailL, gridres sP pP (suc xF)) rSuc_s ndCons
                      val fls = mp_r (lnodup (gridres sP pP (suc xF)), oFalseC) hneg ndG
                      val metaImp = Thm.implies_intr (ctermGR (jT (lnodup tailL))) fls
                  in impI_r (lnodup tailL, oFalseC) metaImp end   (* neg (lnodup tail) = lnodup tail --> oFalse *)
                val exC = mp_r (neg (lnodup tailL), collPair sP pP xF) hIH negNDtail
                (* exC : ?c1 c2. lt c1 x /\ lt c2 x /\ ~(c1=c2) /\ oeq (gres c1)(gres c2) ; lift c<x to c<Suc x *)
                val Pc1 = Term.lambda (Free("c1_dg",natT))
                            (mkEx (Term.lambda (Free("c2_dg",natT))
                              (mkConj (lt (Free("c1_dg",natT)) xF)
                                (mkConj (lt (Free("c2_dg",natT)) xF)
                                  (mkConj (neg (oeq (Free("c1_dg",natT)) (Free("c2_dg",natT))))
                                          (oeq (gres sP pP (Free("c1_dg",natT))) (gres sP pP (Free("c2_dg",natT)))))))))
                fun body1 c1 (h1:thm) =     (* h1 : ?c2. lt c1 x /\ lt c2 x /\ ~(c1=c2) /\ oeq (gres c1)(gres c2) *)
                  let val Pc2 = Term.lambda (Free("c2_dg",natT))
                                  (mkConj (lt c1 xF)
                                    (mkConj (lt (Free("c2_dg",natT)) xF)
                                      (mkConj (neg (oeq c1 (Free("c2_dg",natT))))
                                              (oeq (gres sP pP c1) (gres sP pP (Free("c2_dg",natT)))))))
                      fun body2 c2 (h2:thm) =
                        let val A = lt c1 xF
                            val B = lt c2 xF
                            val Cc = neg (oeq c1 c2)
                            val D = oeq (gres sP pP c1)(gres sP pP c2)
                            val hA = conjunct1_r (A, mkConj B (mkConj Cc D)) h2
                            val rest1 = conjunct2_r (A, mkConj B (mkConj Cc D)) h2
                            val hB = conjunct1_r (B, mkConj Cc D) rest1
                            val rest2 = conjunct2_r (B, mkConj Cc D) rest1
                            val hC = conjunct1_r (Cc, D) rest2
                            val hD = conjunct2_r (Cc, D) rest2
                            val ltc1 = lt_trans_r (c1, xF, suc xF) hA (lt_suc_r xF)
                            val ltc2 = lt_trans_r (c2, xF, suc xF) hB (lt_suc_r xF)
                            val cj = conjI_r (lt c1 (suc xF),
                                        mkConj (lt c2 (suc xF))
                                          (mkConj (neg (oeq c1 c2)) (oeq (gres sP pP c1)(gres sP pP c2))))
                                        ltc1
                                        (conjI_r (lt c2 (suc xF), mkConj (neg (oeq c1 c2)) (oeq (gres sP pP c1)(gres sP pP c2)))
                                           ltc2
                                           (conjI_r (neg (oeq c1 c2), oeq (gres sP pP c1)(gres sP pP c2)) hC hD))
                        in mkCollExists (sP,pP,suc xF) (c1, c2) cj end
                  in exE_r (Pc2, goalC) h1 "c2_dgB" natT body2 end
                val res = exE_r (Pc1, goalC) exC "c1_dgB" natT body1
            in Thm.implies_intr (ctermGR (jT (neg (lmem gx tailL)))) res end
          val resThm = disjE_r (lmem gx tailL, neg (lmem gx tailL), goalC) em caseA caseB
      in Thm.forall_intr (ctermGR xF) (Thm.implies_intr (ctermGR ihP)
           (impI_r (neg (lnodup (gridres sP pP (suc xF))), goalC)
              (Thm.implies_intr (ctermGR hnegP) resThm))) end
    val kF = Free("k_dg", natT)
  in (kF, nat_induct_r Pabs kF base step) end;
val () = out "THC_DUP_FN_READY\n";
val () =
  let val sP=Free("ssd",natT); val pP=Free("ppd",natT)
      val (k, th) = dup_gridres_g (sP, pP)
  in out ("dup_gridres nhyps="^Int.toString (length (Thm.hyps_of th))^"\n") end;
val () = out "IMGPIGEON_OK\n";
val () = out "THC_DUP_DONE\n";

(* ============================================================================
   (3) PACKAGE THUE'S LEMMA.
   ============================================================================ *)
val () = out "THC_PKG_BEGIN\n";

(* small congruence combinators on ctxtGR built from oeq_rw_r *)
fun add_cong_r_r2 (h,p,q) hpq =
  let val P=Term.lambda (Free("zarr2",natT)) (oeq (add h p)(add h (Free("zarr2",natT))))
  in oeq_rw_r (P,p,q) hpq (oeqRefl_r2 (add h p)) end;
fun add_cong_l_r2 (p,q,k) hpq =
  let val P=Term.lambda (Free("zalr2",natT)) (oeq (add p k)(add (Free("zalr2",natT)) k))
  in oeq_rw_r (P,p,q) hpq (oeqRefl_r2 (add p k)) end;
fun mult_cong_r_r2 (h,p,q) hpq =
  let val P=Term.lambda (Free("zmrr2",natT)) (oeq (mult h p)(mult h (Free("zmrr2",natT))))
  in oeq_rw_r (P,p,q) hpq (oeqRefl_r2 (mult h p)) end;

(* re-varify floor_sqrt onto ctxtGR *)
val floor_sqrt_vR2 = varify floor_sqrt;

(* the global parameters that `rearrange`/`cong_of_rmod` are built around *)
val aTHp = aTH;                 (* Free("a", natT) *)
val pTH  = Free("p", natT);     (* Free("p", natT) -- matches rearrange's hardcoded p *)

(* The final 5-existential conclusion at a concrete s. *)
fun thueBodyAt sP =
  let
    val x1=Free("x1_th",natT); val x2=Free("x2_th",natT)
    val y1=Free("y1_th",natT); val y2=Free("y2_th",natT)
    val N = mult (suc sP) (suc sP)
    (* exists x1 x2 y1 y2. (le (s*s) p /\ lt p N) /\ le x1 s /\ le x2 s /\ le y1 s /\ le y2 s
                            /\ neg(oeq x1 x2 /\ oeq y1 y2) /\ cong p (x1 + a*y2)(x2 + a*y1) *)
    fun innerBody (xx1,xx2,yy1,yy2) =
      mkConj (mkConj (le (mult sP sP) pTH) (lt pTH N))
        (mkConj (le xx1 sP)
          (mkConj (le xx2 sP)
            (mkConj (le yy1 sP)
              (mkConj (le yy2 sP)
                (mkConj (neg (mkConj (oeq xx1 xx2) (oeq yy1 yy2)))
                        (cong pTH (add xx1 (mult aTHp yy2)) (add xx2 (mult aTHp yy1))))))))
  in innerBody end;

(* build the 4-existential ?x1 ?x2 ?y1 ?y2 from witnesses + the conjunction *)
fun mk4Exists sP (w1,w2,wy1,wy2) hconj =
  let
    val innerBody = thueBodyAt sP
    (* y2 *)
    val Py2 = Term.lambda (Free("y2_th",natT)) (innerBody (w1,w2,wy1,Free("y2_th",natT)))
    val ey2 = exI_r Py2 wy2 hconj
    val Py1 = Term.lambda (Free("y1_th",natT))
                (mkEx (Term.lambda (Free("y2_th",natT)) (innerBody (w1,w2,Free("y1_th",natT),Free("y2_th",natT)))))
    val ey1 = exI_r Py1 wy1 ey2
    val Px2 = Term.lambda (Free("x2_th",natT))
                (mkEx (Term.lambda (Free("y1_th",natT))
                  (mkEx (Term.lambda (Free("y2_th",natT)) (innerBody (w1,Free("x2_th",natT),Free("y1_th",natT),Free("y2_th",natT)))))))
    val ex2 = exI_r Px2 w2 ey1
    val Px1 = Term.lambda (Free("x1_th",natT))
                (mkEx (Term.lambda (Free("x2_th",natT))
                  (mkEx (Term.lambda (Free("y1_th",natT))
                    (mkEx (Term.lambda (Free("y2_th",natT)) (innerBody (Free("x1_th",natT),Free("x2_th",natT),Free("y1_th",natT),Free("y2_th",natT)))))))))
  in exI_r Px1 w1 ex2 end;

val () = out "THC_PKG_HELPERS_READY\n";

(* ----------------------------------------------------------------------------
   rearrange2 : a CORRECTED copy of the banked `rearrange`.  The banked one has
   a latent bug at its `rd2` step: it passes `D` as the middle congruence term to
   add_cong_r_g where it must pass `(a*(s-y2)) + D` (the LHS of rInner).  The
   banked `rearrange` was never exercised end-to-end (only the inlined sanity
   check, which uses the correct term, was), so the bug went unnoticed.  We use
   this corrected version.  Same statement:
     le y1 s ==> le y2 s ==> cong p (x1 + a*(s-y1))(x2 + a*(s-y2))
       ==> cong p (x1 + a*y2)(x2 + a*y1).
   ---------------------------------------------------------------------------- *)
fun rearrange2 (sP, x1P,x2P,y1P,y2P) hle1 hle2 H =
  let
    val pP = Free("p", natT)
    val a = aTH
    val Lc = add x1P (mult a (subv sP y1P))
    val Rc = add x2P (mult a (subv sP y2P))
    val D  = add (mult a y1P) (mult a y2P)
    val as_ = mult a sP
    val crefl = cong_refl_g (pP, D)
    val congLD_RD = cong_add_g (pP, Lc, Rc, D, D) H crefl
    val asr1 = a_sub_recover (a, sP, y1P) hle1
    val asr2 = a_sub_recover (a, sP, y2P) hle2
    val ld1 = addassoc_g (x1P, mult a (subv sP y1P), D)
    val inAssoc = addassoc_g (mult a (subv sP y1P), mult a y1P, mult a y2P)
    val inAssoc_s = oeqSym_g inAssoc
    val toAs = add_cong_l_g (add (mult a (subv sP y1P)) (mult a y1P), as_, mult a y2P) asr1
    val inner1 = oeqTrans_g (inAssoc_s, toAs)
    val ld2 = oeqTrans_g (ld1, add_cong_r_g (x1P, add (mult a (subv sP y1P)) D, add as_ (mult a y2P)) inner1)
    val commAs = addcomm_g (as_, mult a y2P)
    val ld3 = oeqTrans_g (ld2, add_cong_r_g (x1P, add as_ (mult a y2P), add (mult a y2P) as_) commAs)
    val assocBack1 = addassoc_g (x1P, mult a y2P, as_)
    val ld_final = oeqTrans_g (ld3, oeqSym_g assocBack1)
    val rd1 = addassoc_g (x2P, mult a (subv sP y2P), D)
    val commD = addcomm_g (mult a y1P, mult a y2P)
    val dswap = add_cong_r_g (mult a (subv sP y2P), D, add (mult a y2P) (mult a y1P)) commD
    val rInAssoc = addassoc_g (mult a (subv sP y2P), mult a y2P, mult a y1P)
    val rInAssoc_s = oeqSym_g rInAssoc
    val rToAs = add_cong_l_g (add (mult a (subv sP y2P)) (mult a y2P), as_, mult a y1P) asr2
    val rInner = oeqTrans_g (oeqTrans_g (dswap, rInAssoc_s), rToAs)  (* oeq (a(s-y2)+D)(a*s + a*y1) *)
    (* CORRECTED: middle term is (a(s-y2)) + D, not D *)
    val rd2 = oeqTrans_g (rd1, add_cong_r_g (x2P, add (mult a (subv sP y2P)) D, add as_ (mult a y1P)) rInner)
    val rcommAs = addcomm_g (as_, mult a y1P)
    val rd3 = oeqTrans_g (rd2, add_cong_r_g (x2P, add as_ (mult a y1P), add (mult a y1P) as_) rcommAs)
    val rassocBack = addassoc_g (x2P, mult a y1P, as_)
    val rd_final = oeqTrans_g (rd3, oeqSym_g rassocBack)
    val zc1 = Free("zc1_rc2", natT)
    val P1 = Term.lambda zc1 (cong pP zc1 (add Rc D))
    val st1 = oeq_rw_g (P1, add Lc D, add (add x1P (mult a y2P)) as_) ld_final congLD_RD
    val zc2 = Free("zc2_rc2", natT)
    val P2 = Term.lambda zc2 (cong pP (add (add x1P (mult a y2P)) as_) zc2)
    val st2 = oeq_rw_g (P2, add Rc D, add (add x2P (mult a y1P)) as_) rd_final st1
    val res = cong_radd_cancel_g (pP, add x1P (mult a y2P), add x2P (mult a y1P), as_) st2
  in res end;
val () = out "THC_REARRANGE2_READY\n";

(* ============================================================================
   THE THUE COLLISION LEMMA (final assembly).
     thue : 0<p ==> ?s x1 x2 y1 y2. (le (s*s) p /\ lt p ((Suc s)^2))
              /\ le x1 s /\ le x2 s /\ le y1 s /\ le y2 s
              /\ ~(oeq x1 x2 /\ oeq y1 y2)
              /\ cong p (x1 + a*y2)(x2 + a*y1).
   ============================================================================ *)
val thue =
  let
    val hposP = jT (lt ZeroC pTH)
    val hpos  = Thm.assume (ctermGR hposP)
    (* final existential conclusion: ?s. thueBody at s (4-existential) *)
    fun sExBody sP = mkEx (Term.lambda (Free("x1_th",natT))
                       (mkEx (Term.lambda (Free("x2_th",natT))
                         (mkEx (Term.lambda (Free("y1_th",natT))
                           (mkEx (Term.lambda (Free("y2_th",natT))
                             (thueBodyAt sP (Free("x1_th",natT),Free("x2_th",natT),Free("y1_th",natT),Free("y2_th",natT))))))))))
    val goalC = mkEx (Term.lambda (Free("s_th",natT)) (sExBody (Free("s_th",natT))))
    (* floor_sqrt at p : ?s. le (s*s) p /\ lt p ((Suc s)^2) *)
    val fsq = beta_norm (Drule.infer_instantiate ctxtGR [(("k_fs",0), ctermGR pTH)] floor_sqrt_vR2)
    (* the floor_sqrt existential body abstraction over s_w *)
    val PfsBody = Term.lambda (Free("s_w",natT))
                    (mkConj (le (mult (Free("s_w",natT)) (Free("s_w",natT))) pTH)
                            (lt pTH (mult (suc (Free("s_w",natT))) (suc (Free("s_w",natT))))))
    fun bodyS sP (hs:thm) =      (* hs : le (s*s) p /\ lt p ((Suc s)^2) *)
      let
        val N = mult (suc sP) (suc sP)
        val hsq_le = conjunct1_r (le (mult sP sP) pTH, lt pTH N) hs   (* le (s*s) p *)
        val hltpN  = conjunct2_r (le (mult sP sP) pTH, lt pTH N) hs   (* lt p ((Suc s)^2) *)
        (* collision_exists : neg(lnodup (gridres s p N)) *)
        val collNeg = collision_exists (sP, pTH) hpos hltpN           (* neg(lnodup (gridres s p N)) *)
        (* dup_gridres at n=N : ?c1 c2. lt c1 N /\ lt c2 N /\ ~(c1=c2) /\ oeq (gres c1)(gres c2) *)
        val (kdg, dup) = dup_gridres_g (sP, pTH)
        val dup_N = beta_norm (Thm.forall_elim (ctermGR N) (Thm.forall_intr (ctermGR kdg) dup))
        val collPairExists = mp_r (neg (lnodup (gridres sP pTH N)), collPair sP pTH N) dup_N collNeg
        (* exE on c1, c2 *)
        val Pc1 = Term.lambda (Free("c1_dg",natT))
                    (mkEx (Term.lambda (Free("c2_dg",natT))
                      (mkConj (lt (Free("c1_dg",natT)) N)
                        (mkConj (lt (Free("c2_dg",natT)) N)
                          (mkConj (neg (oeq (Free("c1_dg",natT)) (Free("c2_dg",natT))))
                                  (oeq (gres sP pTH (Free("c1_dg",natT))) (gres sP pTH (Free("c2_dg",natT)))))))))
        fun body1 c1 (h1:thm) =
          let val Pc2 = Term.lambda (Free("c2_dg",natT))
                          (mkConj (lt c1 N)
                            (mkConj (lt (Free("c2_dg",natT)) N)
                              (mkConj (neg (oeq c1 (Free("c2_dg",natT))))
                                      (oeq (gres sP pTH c1) (gres sP pTH (Free("c2_dg",natT)))))))
              fun body2 c2 (h2:thm) =
                let
                  val A = lt c1 N; val B = lt c2 N
                  val Cc = neg (oeq c1 c2); val D = oeq (gres sP pTH c1)(gres sP pTH c2)
                  val hltc1 = conjunct1_r (A, mkConj B (mkConj Cc D)) h2
                  val r1 = conjunct2_r (A, mkConj B (mkConj Cc D)) h2
                  val hltc2 = conjunct1_r (B, mkConj Cc D) r1
                  val r2 = conjunct2_r (B, mkConj Cc D) r1
                  val hneqc = conjunct1_r (Cc, D) r2        (* neg(oeq c1 c2) *)
                  val hgreq = conjunct2_r (Cc, D) r2        (* oeq (gres c1)(gres c2) *)
                  (* decode *)
                  val i1 = rdivv c1 (suc sP); val j1 = rmodv c1 (suc sP)
                  val i2 = rdivv c2 (suc sP); val j2 = rmodv c2 (suc sP)
                  val hi1 = i_le_s_g (c1, sP) hltc1   (* le i1 s *)
                  val hi2 = i_le_s_g (c2, sP) hltc2   (* le i2 s *)
                  val hj1 = j_le_s_g (c1, sP)         (* le j1 s *)
                  val hj2 = j_le_s_g (c2, sP)         (* le j2 s *)
                  (* gres c = rmodv (gval c) p ; oeq (gres c1)(gres c2) = oeq (rmodv (gval c1) p)(rmodv (gval c2) p) *)
                  val gv1 = gvalT sP c1; val gv2 = gvalT sP c2
                  (* cong_of_rmod (gv1, gv2, p) hpos hgreq : cong p gv1 gv2 *)
                  val congGv = cong_of_rmod (gv1, gv2, pTH) hpos hgreq   (* cong p (i1 + a*(s-j1))(i2 + a*(s-j2)) *)
                  (* rearrange2 (s, i1, i2, j1, j2) (le j1 s)(le j2 s) congGv : cong p (i1 + a*j2)(i2 + a*j1) *)
                  val congTarget = rearrange2 (sP, i1, i2, j1, j2) hj1 hj2 congGv
                  (* distinctness : neg (oeq i1 i2 /\ oeq j1 j2) from neg(oeq c1 c2) via decode_id *)
                  val did1 = decode_id_g (c1, sP)   (* oeq c1 ((Suc s)*i1 + j1) *)
                  val did2 = decode_id_g (c2, sP)   (* oeq c2 ((Suc s)*i2 + j2) *)
                  val negIJ =
                    let val hij = Thm.assume (ctermGR (jT (mkConj (oeq i1 i2)(oeq j1 j2))))
                        val hi  = conjunct1_r (oeq i1 i2, oeq j1 j2) hij    (* oeq i1 i2 *)
                        val hj  = conjunct2_r (oeq i1 i2, oeq j1 j2) hij    (* oeq j1 j2 *)
                        (* (Suc s)*i1 = (Suc s)*i2 *)
                        val mulEq = mult_cong_r_r2 (suc sP, i1, i2) hi      (* oeq ((Suc s)*i1)((Suc s)*i2) *)
                        (* ((Suc s)*i1 + j1) = ((Suc s)*i2 + j1) [add_cong_l] *)
                        val sumEq1 = add_cong_l_r2 (mult (suc sP) i1, mult (suc sP) i2, j1) mulEq
                        (* ((Suc s)*i2 + j1) = ((Suc s)*i2 + j2) [add_cong_r with hj] *)
                        val sumEq2 = add_cong_r_r2 (mult (suc sP) i2, j1, j2) hj
                        val sumEq  = oeqTrans_r2 (sumEq1, sumEq2)           (* ((Suc s)*i1 + j1) = ((Suc s)*i2 + j2) *)
                        (* c1 = ((Suc s)*i1 + j1) = ((Suc s)*i2 + j2) = c2 *)
                        val c1_mid = did1                                   (* c1 = (Suc s)*i1 + j1 *)
                        val c1_c2mid = oeqTrans_r2 (c1_mid, sumEq)          (* c1 = (Suc s)*i2 + j2 *)
                        val c2_c1 = oeqTrans_r2 (c1_c2mid, oeqSym_r2 did2)  (* c1 = c2 *)
                        val fls = mp_r (oeq c1 c2, oFalseC) hneqc c2_c1
                        val metaImp = Thm.implies_intr (ctermGR (jT (mkConj (oeq i1 i2)(oeq j1 j2)))) fls
                    in impI_r (mkConj (oeq i1 i2)(oeq j1 j2), oFalseC) metaImp end
                  (* assemble the inner conjunction *)
                  val sqlt = conjI_r (le (mult sP sP) pTH, lt pTH N) hsq_le hltpN
                  (* right-fold: build a right-nested object conjunction from a list of
                     (term, thm) for all but the last, and a final (term, thm). *)
                  val congTgtT = cong pTH (add i1 (mult aTHp j2)) (add i2 (mult aTHp j1))
                  val parts = [ (mkConj (le (mult sP sP) pTH) (lt pTH N), sqlt),
                                (le i1 sP, hi1),
                                (le i2 sP, hi2),
                                (le j1 sP, hj1),
                                (le j2 sP, hj2),
                                (neg (mkConj (oeq i1 i2)(oeq j1 j2)), negIJ) ]
                  val lastPart = (congTgtT, congTarget)
                  fun buildConj [] = lastPart
                    | buildConj ((at,ath)::rest) =
                        let val (bt, bth) = buildConj rest
                        in (mkConj at bt, conjI_r (at, bt) ath bth) end
                  val conjAll = #2 (buildConj parts)
                  (* package the 4-existential at this s, with witnesses (i1,i2,j1,j2) *)
                  val ex4 = mk4Exists sP (i1, i2, j1, j2) conjAll
                  (* then the outer ?s *)
                  val Ps = Term.lambda (Free("s_th",natT)) (sExBody (Free("s_th",natT)))
                in exI_r Ps sP ex4 end
          in exE_r (Pc2, goalC) h1 "c2_th" natT body2 end
        val res = exE_r (Pc1, goalC) collPairExists "c1_th" natT body1
      in res end
    val body = exE_r (PfsBody, goalC) fsq "s_th0" natT bodyS
  in Thm.implies_intr (ctermGR hposP) body end;
val () = out ("thue nhyps="^Int.toString (length (Thm.hyps_of thue))^"\n");
val () = out ("thue prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of thue)^"\n");
val () = out "THUE_OK\n";

(* ============================================================================
   FINAL VALIDATION: aconv against the intended statement + 0-hyp confirmation.
   ============================================================================ *)
val thue_intended =
  let
    val sP=Free("s_th",natT); val x1=Free("x1_th",natT); val x2=Free("x2_th",natT)
    val y1=Free("y1_th",natT); val y2=Free("y2_th",natT)
    val N = mult (suc sP)(suc sP)
    fun body (xx1,xx2,yy1,yy2) =
      mkConj (mkConj (le (mult sP sP) pTH) (lt pTH (mult (suc sP)(suc sP)) ))
        (mkConj (le xx1 sP)
          (mkConj (le xx2 sP)
            (mkConj (le yy1 sP)
              (mkConj (le yy2 sP)
                (mkConj (neg (mkConj (oeq xx1 xx2) (oeq yy1 yy2)))
                        (cong pTH (add xx1 (mult aTHp yy2)) (add xx2 (mult aTHp yy1))))))))
    val inner = mkEx (Term.lambda x1 (mkEx (Term.lambda x2 (mkEx (Term.lambda y1 (mkEx (Term.lambda y2 (body (x1,x2,y1,y2)))))))))
    val withS = mkEx (Term.lambda sP inner)
  in Logic.mk_implies (jT (lt ZeroC pTH), jT withS) end;
val thue_aconv = ((Thm.prop_of thue) aconv thue_intended);
val thue_0hyp  = (length (Thm.hyps_of thue) = 0);
val () = out ("THUE_VALIDATE aconv="^Bool.toString thue_aconv^" zero_hyp="^Bool.toString thue_0hyp^"\n");
val () = if thue_aconv andalso thue_0hyp then out "THUE_ALL_OK\n" else out "THUE_VALIDATE_FAILED\n";
