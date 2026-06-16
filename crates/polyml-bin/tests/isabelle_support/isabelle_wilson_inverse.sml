(* ============================================================================
   THE MODULAR-INVERSE FUNCTION + RESIDUE RANGE toward Wilson's theorem, in
   Isabelle/Pure on the polyml-rs interpreter.  (test: isabelle_wilson_inverse.rs)
   ----------------------------------------------------------------------------
   The pairing_lemma (proved in isabelle_wilson_pairing.sml) needs the modular
   inverse as a literal FUNCTION (an involution on the residue list). But the
   object logic has no choice operator and `cong` is not directly decidable. The
   unlock here: a `mod` function makes congruence decidable, so the inverse can be
   built by a list search. Proved by genuine kernel inference:

   (A) RANGE + MOD (range-mod phase):
       rmod / rdiv (remainder/quotient) via conservative axioms from the division
       theorem, the BRIDGE  cong_iff_rmod : 0<p ==> (cong p a b <-> rmod a p = rmod b p)
       (both directions -- this makes congruence DECIDABLE), and the residue range
       upto n = [1,..,n] with lnodup (upto n) and lmem_upto (membership = 1<=b<=n).

   (B) THE INVERSE FUNCTION (inverse-fn phase):
       finv p x = search upto(p-1) for x's inverse (decidable now via rmod), proved
       for prime p and x in [1..p-1]:
         finv_inv   : cong p (x * finv p x) 1        (it IS an inverse)
         finv_mem   : lmem (finv p x) (upto (p-1))   (lands back in range)
         finv_invol : finv p (finv p x) = x          (LITERAL involution, via inverse_unique)
         finv_neq   : on [2..p-2], finv p x <> x     (fixed-point free, via lagrange_roots)

   These are exactly pairing_lemma's hypotheses. Each lemma is 0-hyp, aconv the
   intended statement, with soundness probes. Built on the Wilson-pairing base via
   common::with_wilson_pairing. Proved by a 2-phase ultracode fleet (wf_a22d8bd7-115);
   re-verified end-to-end by hand. NEXT (the finale): apply pairing_lemma to [2..p-2]
   with finv to get lprod[2..p-2] == 1, then (p-1)! = 1 * lprod[2..p-2] * (p-1) == -1.
   ============================================================================ *)

(* ============================================================================
   PHASE 1 (seat rm0): rmod / rdiv + cong_iff_rmod ; upto + lnodup + lmem_upto
   Built on the FINAL base context (thyL2 / ctxtL2 / ctermL2).
   NOTE: `upto` is an SML basis infix; the term builder is named uptoF.
   ============================================================================ *)
val () = out "RM_PHASE1_BEGIN\n";

(* ---- new theory: add consts rmod, rdiv, upto ---- *)
val thyRMc = Sign.add_consts
  [(Binding.name "rmod", natT --> natT --> natT, NoSyn),
   (Binding.name "rdiv", natT --> natT --> natT, NoSyn),
   (Binding.name "upto", natT --> natlistT, NoSyn)] thyL2;

fun cnstRM nm T = Const (Sign.full_name thyRMc (Binding.name nm), T);
val rmodC = cnstRM "rmod" (natT --> natT --> natT); fun rmod a p = rmodC $ a $ p;
val rdivC = cnstRM "rdiv" (natT --> natT --> natT); fun rdiv a p = rdivC $ a $ p;
val uptoC = cnstRM "upto" (natT --> natlistT);      fun uptoF n = uptoC $ n;

(* free vars for axiom statements *)
val aRM = Free("a", natT); val bRM = Free("b", natT); val pRM = Free("p", natT);
val nRM = Free("n", natT);

(* ---- (A) division-derived conservative axioms ---- *)
val ((_,div_mod_eq_ax), thyRM1) = Thm.add_axiom_global (Binding.name "div_mod_eq",
      Logic.mk_implies (jT (lt ZeroC pRM),
        jT (oeq aRM (add (mult pRM (rdiv aRM pRM)) (rmod aRM pRM))))) thyRMc;
val ((_,rmod_lt_ax), thyRM2) = Thm.add_axiom_global (Binding.name "rmod_lt",
      Logic.mk_implies (jT (lt ZeroC pRM), jT (lt (rmod aRM pRM) pRM))) thyRM1;

(* ---- (B) uptoF recursion axioms ---- *)
val ((_,upto_zero_ax), thyRM3) = Thm.add_axiom_global (Binding.name "upto_zero",
      jT (leq (uptoF ZeroC) lnilC)) thyRM2;
val ((_,upto_suc_ax), thyRM) = Thm.add_axiom_global (Binding.name "upto_suc",
      jT (leq (uptoF (suc nRM)) (lcons (suc nRM) (uptoF nRM)))) thyRM3;

val ctxtRM  = Proof_Context.init_global thyRM;
val ctermRM = Thm.cterm_of ctxtRM;
val () = out "RM_CONTEXT_READY\n";

(* ============================================================================
   re-varify reused base axioms/lemmas onto ctxtRM
   ============================================================================ *)
val oeq_refl_vR    = varify oeq_refl;
val oeq_subst_vR   = varify oeq_subst;
val oeq_sym_vR     = varify oeq_sym;
val oeq_trans_vR   = varify oeq_trans;
val Suc_cong_vR    = varify Suc_cong;
val exI_vR         = varify exI_ax;
val exE_vR         = varify exE_ax;
val oFalse_elim_vR = varify oFalse_elim_ax;
val Suc_neq_Zero_vR= varify Suc_neq_Zero_ax;
val Suc_inj_vR     = varify Suc_inj_ax;
val conjI_vR       = varify conjI_ax;
val conjunct1_vR   = varify conjunct1_ax;
val conjunct2_vR   = varify conjunct2_ax;
val disjI1_vR      = varify disjI1_ax;
val disjI2_vR      = varify disjI2_ax;
val disjE_vR       = varify disjE_ax;
val mp_vR          = varify mp_ax;
val impI_vR        = varify impI_ax;
val ex_middle_vR   = varify ex_middle_ax;
val allI_vR        = varify allI_ax;
val allE_vR        = varify allE_ax;
val add_0_vR       = varify add_0;
val add_Suc_vR     = varify add_Suc;
val add_0_right_vR = varify add_0_right;
val add_comm_vR    = varify add_comm;
val add_assoc_vR   = varify add_assoc;
val add_left_cancel_vR = varify add_left_cancel;
val mult_0_vR      = varify mult_0;
val mult_Suc_vR    = varify mult_Suc;
val mult_0_right_vR= varify mult_0_right;
val mult_Suc_right_vR = varify mult_Suc_right;
val mult_comm_vR   = varify mult_comm;
val mult_assoc_vR  = varify mult_assoc;
val mult_1_left_vR = varify mult_1_left;
val left_distrib_vR = varify left_distrib;
val right_distrib_vR = varify right_distrib;
val le_refl_vR     = varify le_refl;
val le_trans_vR    = varify le_trans;
val le_total_vR    = varify le_total;
val le_antisym_vR  = varify le_antisym;
val le_add_vR      = varify le_add;
val zero_le_vR     = varify zero_le;
val lt_suc_vR      = varify lt_suc;
val lt_trans_vR    = varify lt_trans;
val lt_suc_cases_vR= varify lt_suc_cases;
val nlt_le_vR      = varify nlt_le;
val div_mod_unique_vR = varify div_mod_unique;
(* list machinery *)
val leq_refl_vR    = varify leq_refl_ax;
val leq_subst_vR   = varify leq_subst_ax;
val list_induct_vR = varify list_induct_ax;
val lmem_nil_elim_vR = varify lmem_nil_elim_ax;
val lmem_cons_fwd_vR = varify lmem_cons_fwd_ax;
val lmem_cons_bwd_vR = varify lmem_cons_bwd_ax;
val lnodup_nil_vR  = varify lnodup_nil_ax;
val lnodup_cons_fwd_vR = varify lnodup_cons_fwd_ax;
val lnodup_cons_bwd_vR = varify lnodup_cons_bwd_ax;
(* new axioms *)
val div_mod_eq_vR  = varify div_mod_eq_ax;
val rmod_lt_vR     = varify rmod_lt_ax;
val upto_zero_vR   = varify upto_zero_ax;
val upto_suc_vR    = varify upto_suc_ax;
val () = out "RM_VARIFY_READY\n";

(* ============================================================================
   combinators on ctxtRM (suffix _R)
   ============================================================================ *)
fun oeqRefl_R t = beta_norm (Drule.infer_instantiate ctxtRM [(("a",0), ctermRM t)] oeq_refl_vR);
fun add0_R t    = beta_norm (Drule.infer_instantiate ctxtRM [(("n",0), ctermRM t)] add_0_vR);
fun add0r_R t   = beta_norm (Drule.infer_instantiate ctxtRM [(("n",0), ctermRM t)] add_0_right_vR);
fun addSuc_R (mt,nt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("n",0), ctermRM nt)] add_Suc_vR);
fun addcomm_R (mt,nt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("n",0), ctermRM nt)] add_comm_vR);
fun addassoc_R (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("n",0), ctermRM nt),(("k",0), ctermRM kt)] add_assoc_vR);
fun mult0r_R t  = beta_norm (Drule.infer_instantiate ctxtRM [(("n",0), ctermRM t)] mult_0_right_vR);
fun multcomm_R (mt,nt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("n",0), ctermRM nt)] mult_comm_vR);
fun multassoc_R (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("n",0), ctermRM nt),(("k",0), ctermRM kt)] mult_assoc_vR);
fun leftdistrib_R (xt,mt,nt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("x",0), ctermRM xt),(("m",0), ctermRM mt),(("n",0), ctermRM nt)] left_distrib_vR);

fun oeq_rw_R (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("P",0), ctermRM Pabs),(("a",0), ctermRM aT),(("b",0), ctermRM bT)] oeq_subst_vR)
  in inst OF [hab, hPa] end;
fun add_cong_l_R (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT))
  in oeq_rw_R (Pabs, pT, qT) hpq (oeqRefl_R (add pT kT)) end;
fun add_cong_r_R (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)))
  in oeq_rw_R (Pabs, pT, qT) hpq (oeqRefl_R (add hT pT)) end;
fun mult_cong_l_R (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT))
  in oeq_rw_R (Pabs, pT, qT) hpq (oeqRefl_R (mult pT kT)) end;
fun mult_cong_r_R (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)))
  in oeq_rw_R (Pabs, pT, qT) hpq (oeqRefl_R (mult hT pT)) end;

fun mp_R (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("A",0), ctermRM At),(("B",0), ctermRM Bt)] mp_vR)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_R (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("A",0), ctermRM At),(("B",0), ctermRM Bt)] impI_vR)
  in Thm.implies_elim inst hImpThm end;
fun conjI_R (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("A",0), ctermRM At),(("B",0), ctermRM Bt)] conjI_vR)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_R (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("A",0), ctermRM At),(("B",0), ctermRM Bt)] conjunct1_vR)) h;
fun conjunct2_R (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("A",0), ctermRM At),(("B",0), ctermRM Bt)] conjunct2_vR)) h;
fun oFalse_elim_R rT = beta_norm (Drule.infer_instantiate ctxtRM [(("R",0), ctermRM rT)] oFalse_elim_vR);
fun disjE_R (At,Bt,Ct) dThm cA cB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("A",0), ctermRM At),(("B",0), ctermRM Bt),(("C",0), ctermRM Ct)] disjE_vR)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) cA) cB end;
fun disjI1_R (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("A",0), ctermRM At),(("B",0), ctermRM Bt)] disjI1_vR)) h;
fun disjI2_R (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("A",0), ctermRM At),(("B",0), ctermRM Bt)] disjI2_vR)) h;
fun em_R t = beta_norm (Drule.infer_instantiate ctxtRM [(("A",0), ctermRM t)] ex_middle_vR);
fun allI_R Pabs hAll = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("P",0), ctermRM Pabs)] allI_vR)) hAll;
fun allE_R Pabs at hF = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("P",0), ctermRM Pabs),(("a",0), ctermRM at)] allE_vR)) hF;
fun Suc_neq_Zero_R nt heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM [(("n",0), ctermRM nt)] Suc_neq_Zero_vR)) heq;
fun Suc_inj_R (at,bt) heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("a",0), ctermRM at),(("b",0), ctermRM bt)] Suc_inj_vR)) heq;

fun exI_R Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("P",0), ctermRM Pabs),(("a",0), ctermRM at)] exI_vR)
  in Thm.implies_elim inst hbody end;
fun exE_R (Pabs, goalC) exThm wName bodyFn =
  let val wF = Free(wName, natT)
      val hypTerm = jT (Term.betapply (Pabs, wF))
      val hypThm  = Thm.assume (ctermRM hypTerm)
      val body    = bodyFn wF hypThm
      val minor   = Thm.forall_intr (ctermRM wF) (Thm.implies_intr (ctermRM hypTerm) body)
      val exE_inst= beta_norm (Drule.infer_instantiate ctxtRM
                      [(("P",0), ctermRM Pabs),(("Q",0), ctermRM goalC)] exE_vR)
  in Thm.implies_elim (Thm.implies_elim exE_inst exThm) minor end;

fun le_intro_R (mT, nT, w) hyp =
  let val Pabs = Abs("p", natT, oeq nT (add mT (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtRM
            [(("P",0), ctermRM Pabs),(("a",0), ctermRM w)] exI_vR)
  in inst OF [hyp] end;
fun le_total_R (mt,nt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("n",0), ctermRM nt)] le_total_vR);
fun le_trans_R (at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("m",0), ctermRM at),(("n",0), ctermRM bt),(("k",0), ctermRM ct)] le_trans_vR)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun lt_trans_R (at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("a",0), ctermRM at),(("b",0), ctermRM bt),(("c",0), ctermRM ct)] lt_trans_vR)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun lt_suc_cases_R (mt,nt) hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("n",0), ctermRM nt)] lt_suc_cases_vR)) hlt;
fun nlt_le_R (dt, ct) hneg =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("d",0), ctermRM dt),(("c",0), ctermRM ct)] nlt_le_vR)) hneg;
fun lt_suc_R nt = beta_norm (Drule.infer_instantiate ctxtRM [(("n",0), ctermRM nt)] lt_suc_vR);
fun le_antisym_R (mt,nt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("m",0), ctermRM mt),(("n",0), ctermRM nt)] le_antisym_vR)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun le_add_R (mt,pt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("p",0), ctermRM pt)] le_add_vR);

fun div_mod_eq_R (at,pt) hpos =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("a",0), ctermRM at),(("p",0), ctermRM pt)] div_mod_eq_vR)) hpos;
fun rmod_lt_R (at,pt) hpos =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("a",0), ctermRM at),(("p",0), ctermRM pt)] rmod_lt_vR)) hpos;
fun div_mod_unique_R (b,q1,r1,q2,r2) heq hlt1 hlt2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("b",0), ctermRM b),(("q1",0), ctermRM q1),(("r1",0), ctermRM r1),
         (("q2",0), ctermRM q2),(("r2",0), ctermRM r2)] div_mod_unique_vR)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst heq) hlt1) hlt2 end;

val () = out "RM_COMBINATORS_READY\n";

(* ============================================================================
   cong constructors on ctxtRM (cong/congL/congR defined in base).
   congL m a b = ?k. b = a + m*k ; congR m a b = ?k. a = b + m*k.
   ============================================================================ *)
fun cong_introL_R (m,a,b,w) hyp =
  let val Pabs = Abs("k", natT, oeq b (add a (mult m (Bound 0))))
      val ex = exI_R Pabs w hyp
  in disjI1_R (congL m a b, congR m a b) ex end;
fun cong_introR_R (m,a,b,w) hyp =
  let val Pabs = Abs("k", natT, oeq a (add b (mult m (Bound 0))))
      val ex = exI_R Pabs w hyp
  in disjI2_R (congL m a b, congR m a b) ex end;

(* ============================================================================
   cong_imp_rmodeq : 0<p ==> cong p a b ==> oeq (rmod a p) (rmod b p)
   ============================================================================ *)
val cong_imp_rmodeq =
  let
    val aF = Free("a",natT); val bF = Free("b",natT); val pF = Free("p",natT);
    val posP = jT (lt ZeroC pF);
    val hpos = Thm.assume (ctermRM posP);
    val congP = jT (cong pF aF bF);
    val hcong = Thm.assume (ctermRM congP);
    val goalC = oeq (rmod aF pF) (rmod bF pF);
    val hAeq = div_mod_eq_R (aF, pF) hpos;
    val hBeq = div_mod_eq_R (bF, pF) hpos;
    val hAlt = rmod_lt_R (aF, pF) hpos;
    val hBlt = rmod_lt_R (bF, pF) hpos;
    val qa = rdiv aF pF; val ra = rmod aF pF;
    val qb = rdiv bF pF; val rb = rmod bF pF;
    val caseL =
      let
        val hL = Thm.assume (ctermRM (jT (congL pF aF bF)))
        val Pabs = Abs("k", natT, oeq bF (add aF (mult pF (Bound 0))))
        fun body k (hk:thm) =
          let
            val c1 = add_cong_l_R (aF, add (mult pF qa) ra, mult pF k) hAeq;
            val b_e1 = oeq_trans_vR OF [hk, c1];
            val assoc1 = addassoc_R (mult pF qa, ra, mult pF k);
            val b_e2 = oeq_trans_vR OF [b_e1, assoc1];
            val comm1 = addcomm_R (ra, mult pF k);
            val c_inner = add_cong_r_R (mult pF qa, add ra (mult pF k), add (mult pF k) ra) comm1;
            val b_e3 = oeq_trans_vR OF [b_e2, c_inner];
            val assoc2 = addassoc_R (mult pF qa, mult pF k, ra);
            val b_e4 = oeq_trans_vR OF [b_e3, oeq_sym_vR OF [assoc2]];
            val ld = leftdistrib_R (pF, qa, k);
            val c_fold = add_cong_l_R (add (mult pF qa)(mult pF k), mult pF (add qa k), ra) (oeq_sym_vR OF [ld]);
            val b_final = oeq_trans_vR OF [b_e4, c_fold];
            val eqUnique = oeq_trans_vR OF [oeq_sym_vR OF [b_final], hBeq];
            val uniq = div_mod_unique_R (pF, add qa k, ra, qb, rb) eqUnique hAlt hBlt;
            val ra_rb = conjunct2_R (oeq (add qa k) qb, oeq ra rb) uniq;
          in ra_rb end
        val res = exE_R (Pabs, goalC) hL "kL" body
      in Thm.implies_intr (ctermRM (jT (congL pF aF bF))) res end;
    val caseR =
      let
        val hR = Thm.assume (ctermRM (jT (congR pF aF bF)))
        val Pabs = Abs("k", natT, oeq aF (add bF (mult pF (Bound 0))))
        fun body k (hk:thm) =
          let
            val c1 = add_cong_l_R (bF, add (mult pF qb) rb, mult pF k) hBeq;
            val a_e1 = oeq_trans_vR OF [hk, c1];
            val assoc1 = addassoc_R (mult pF qb, rb, mult pF k);
            val a_e2 = oeq_trans_vR OF [a_e1, assoc1];
            val comm1 = addcomm_R (rb, mult pF k);
            val c_inner = add_cong_r_R (mult pF qb, add rb (mult pF k), add (mult pF k) rb) comm1;
            val a_e3 = oeq_trans_vR OF [a_e2, c_inner];
            val assoc2 = addassoc_R (mult pF qb, mult pF k, rb);
            val a_e4 = oeq_trans_vR OF [a_e3, oeq_sym_vR OF [assoc2]];
            val ld = leftdistrib_R (pF, qb, k);
            val c_fold = add_cong_l_R (add (mult pF qb)(mult pF k), mult pF (add qb k), rb) (oeq_sym_vR OF [ld]);
            val a_final = oeq_trans_vR OF [a_e4, c_fold];
            val eqUnique = oeq_trans_vR OF [oeq_sym_vR OF [a_final], hAeq];
            val uniq = div_mod_unique_R (pF, add qb k, rb, qa, ra) eqUnique hBlt hAlt;
            val rb_ra = conjunct2_R (oeq (add qb k) qa, oeq rb ra) uniq;
          in oeq_sym_vR OF [rb_ra] end
        val res = exE_R (Pabs, goalC) hR "kR" body
      in Thm.implies_intr (ctermRM (jT (congR pF aF bF))) res end;
    val res = disjE_R (congL pF aF bF, congR pF aF bF, goalC) hcong caseL caseR;
    val disch2 = Thm.implies_intr (ctermRM congP) res;
    val disch1 = Thm.implies_intr (ctermRM posP) disch2;
  in varify disch1 end;
val () = if length (Thm.hyps_of cong_imp_rmodeq) = 0 then out "OK cong_imp_rmodeq\n" else out "FAIL cong_imp_rmodeq\n";
val () = out "RM_DIR1_DONE\n";

(* ============================================================================
   DIRECTION 2 : rmodeq_imp_cong : 0<p ==> oeq (rmod a p)(rmod b p) ==> cong p a b
   ============================================================================ *)
val rmodeq_imp_cong =
  let
    val aF = Free("a",natT); val bF = Free("b",natT); val pF = Free("p",natT);
    val posP = jT (lt ZeroC pF);
    val hpos = Thm.assume (ctermRM posP);
    val eqP  = jT (oeq (rmod aF pF) (rmod bF pF));
    val heq  = Thm.assume (ctermRM eqP);
    val goalC = cong pF aF bF;
    val qa = rdiv aF pF; val ra = rmod aF pF;
    val qb = rdiv bF pF; val rb = rmod bF pF;
    val hAeq = div_mod_eq_R (aF, pF) hpos;
    val hBeq = div_mod_eq_R (bF, pF) hpos;
    val tot = le_total_R (qa, qb);
    val caseLe =
      let
        val hle = Thm.assume (ctermRM (jT (le qa qb)))
        val Pabs = Abs("d", natT, oeq qb (add qa (Bound 0)))
        fun body d (hd:thm) =
          let
            val c_qb = mult_cong_r_R (pF, qb, add qa d) hd;
            val c1 = add_cong_l_R (mult pF qb, mult pF (add qa d), rb) c_qb;
            val b_e1 = oeq_trans_vR OF [hBeq, c1];
            val ld = leftdistrib_R (pF, qa, d);
            val c2 = add_cong_l_R (mult pF (add qa d), add (mult pF qa)(mult pF d), rb) ld;
            val b_e2 = oeq_trans_vR OF [b_e1, c2];
            val assoc1 = addassoc_R (mult pF qa, mult pF d, rb);
            val b_e3 = oeq_trans_vR OF [b_e2, assoc1];
            val comm1 = addcomm_R (mult pF d, rb);
            val c3 = add_cong_r_R (mult pF qa, add (mult pF d) rb, add rb (mult pF d)) comm1;
            val b_e4 = oeq_trans_vR OF [b_e3, c3];
            val assoc2 = addassoc_R (mult pF qa, rb, mult pF d);
            val b_e5 = oeq_trans_vR OF [b_e4, oeq_sym_vR OF [assoc2]];
            val rb_ra = oeq_sym_vR OF [heq];
            val c4 = add_cong_r_R (mult pF qa, rb, ra) rb_ra;
            val c4b = add_cong_l_R (add (mult pF qa) rb, add (mult pF qa) ra, mult pF d) c4;
            val b_e6 = oeq_trans_vR OF [b_e5, c4b];
            val a_eq = oeq_sym_vR OF [hAeq];
            val c5 = add_cong_l_R (add (mult pF qa) ra, aF, mult pF d) a_eq;
            val b_final = oeq_trans_vR OF [b_e6, c5];
          in cong_introL_R (pF, aF, bF, d) b_final end
        val res = exE_R (Pabs, goalC) hle "dLe" body
      in Thm.implies_intr (ctermRM (jT (le qa qb))) res end;
    val caseGe =
      let
        val hle = Thm.assume (ctermRM (jT (le qb qa)))
        val Pabs = Abs("d", natT, oeq qa (add qb (Bound 0)))
        fun body d (hd:thm) =
          let
            val c_qa = mult_cong_r_R (pF, qa, add qb d) hd;
            val c1 = add_cong_l_R (mult pF qa, mult pF (add qb d), ra) c_qa;
            val a_e1 = oeq_trans_vR OF [hAeq, c1];
            val ld = leftdistrib_R (pF, qb, d);
            val c2 = add_cong_l_R (mult pF (add qb d), add (mult pF qb)(mult pF d), ra) ld;
            val a_e2 = oeq_trans_vR OF [a_e1, c2];
            val assoc1 = addassoc_R (mult pF qb, mult pF d, ra);
            val a_e3 = oeq_trans_vR OF [a_e2, assoc1];
            val comm1 = addcomm_R (mult pF d, ra);
            val c3 = add_cong_r_R (mult pF qb, add (mult pF d) ra, add ra (mult pF d)) comm1;
            val a_e4 = oeq_trans_vR OF [a_e3, c3];
            val assoc2 = addassoc_R (mult pF qb, ra, mult pF d);
            val a_e5 = oeq_trans_vR OF [a_e4, oeq_sym_vR OF [assoc2]];
            val c4 = add_cong_r_R (mult pF qb, ra, rb) heq;
            val c4b = add_cong_l_R (add (mult pF qb) ra, add (mult pF qb) rb, mult pF d) c4;
            val a_e6 = oeq_trans_vR OF [a_e5, c4b];
            val b_eq = oeq_sym_vR OF [hBeq];
            val c5 = add_cong_l_R (add (mult pF qb) rb, bF, mult pF d) b_eq;
            val a_final = oeq_trans_vR OF [a_e6, c5];
          in cong_introR_R (pF, aF, bF, d) a_final end
        val res = exE_R (Pabs, goalC) hle "dGe" body
      in Thm.implies_intr (ctermRM (jT (le qb qa))) res end;
    val res = disjE_R (le qa qb, le qb qa, goalC) tot caseLe caseGe;
    val disch2 = Thm.implies_intr (ctermRM eqP) res;
    val disch1 = Thm.implies_intr (ctermRM posP) disch2;
  in varify disch1 end;
val () = if length (Thm.hyps_of rmodeq_imp_cong) = 0 then out "OK rmodeq_imp_cong\n" else out "FAIL rmodeq_imp_cong\n";
val () = out "RM_DIR2_DONE\n";
val () = out "RM_CONG_IFF_BOTH_DONE\n";

(* ============================================================================
   UPTO lemmas.  uptoF characterized by leq axioms; transfer lmem/lnodup through leq.
   ============================================================================ *)
val nat_induct_vR  = varify nat_induct;
val leq_sym_vR     = varify leq_sym;
val leq_trans_vR   = varify leq_trans;
val disj_zero_or_suc_vR = varify disj_zero_or_suc;
val add_eq_zero_left_vR = varify add_eq_zero_left;
val add_Suc_right_vR = varify add_Suc_right;

fun mkExSuc_R t = mkEx (Abs ("q", natT, oeq t (suc (Bound 0))));
fun dzos_R t = beta_norm (Drule.infer_instantiate ctxtRM [(("p",0), ctermRM t)] disj_zero_or_suc_vR);
fun add_eq_zero_left_R (at,bt) heq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("a",0), ctermRM at),(("b",0), ctermRM bt)] add_eq_zero_left_vR)
  in inst OF [heq] end;
fun addSr_at_R (mt,nt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("n",0), ctermRM nt)] add_Suc_right_vR);
fun nat_induct_R Pabs kT baseThm stepThm =
  let val ind = beta_norm (Drule.infer_instantiate ctxtRM
        [(("P",0), ctermRM Pabs),(("k",0), ctermRM kT)] nat_induct_vR)
  in Thm.implies_elim (Thm.implies_elim ind baseThm) stepThm end;
fun uptoSuc_R nt = beta_norm (Drule.infer_instantiate ctxtRM [(("n",0), ctermRM nt)] upto_suc_vR);
val uptoZero_R = upto_zero_vR;
fun leq_rw_R (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("P",0), ctermRM Pabs),(("a",0), ctermRM aT),(("b",0), ctermRM bT)] leq_subst_vR)
  in inst OF [hab, hPa] end;
fun leq_sym_R h = leq_sym_vR OF [h];
fun lmemNilElim_R x = beta_norm (Drule.infer_instantiate ctxtRM [(("x",0), ctermRM x)] lmem_nil_elim_vR);
fun lmemConsFwd_R (x,y,t) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("x",0), ctermRM x),(("y",0), ctermRM y),(("t",0), ctermRM t)] lmem_cons_fwd_vR);
fun lmemConsBwd_R (x,y,t) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("x",0), ctermRM x),(("y",0), ctermRM y),(("t",0), ctermRM t)] lmem_cons_bwd_vR);
fun lnodupCons_bwd_R (x,t) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("x",0), ctermRM x),(("t",0), ctermRM t)] lnodup_cons_bwd_vR);
fun lnodupCons_fwd_R (x,t) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("x",0), ctermRM x),(("t",0), ctermRM t)] lnodup_cons_fwd_vR);
val lnodupNil_R = lnodup_nil_vR;
val () = out "RM_UPTO_COMB_READY\n";

(* ============================================================================
   le_suc_split : le b (Suc n) ==> Disj (oeq b (Suc n)) (le b n)
   ============================================================================ *)
val le_suc_split =
  let
    val bF = Free("b",natT); val nF = Free("n",natT);
    val hypP = jT (le bF (suc nF));
    val hle  = Thm.assume (ctermRM hypP);
    val goalC = mkDisj (oeq bF (suc nF)) (le bF nF);
    val Pabs = Abs("d", natT, oeq (suc nF) (add bF (Bound 0)));
    fun body d (hd:thm) =
      let
        val dz = dzos_R d;
        val caseZ =
          let val hz = Thm.assume (ctermRM (jT (oeq d ZeroC)))
              val c1 = add_cong_r_R (bF, d, ZeroC) hz
              val b0 = add0r_R bF
              val c2 = oeq_trans_vR OF [c1, b0]
              val Sn_b = oeq_trans_vR OF [hd, c2]
              val b_Sn = oeq_sym_vR OF [Sn_b]
          in Thm.implies_intr (ctermRM (jT (oeq d ZeroC)))
               (disjI1_R (oeq bF (suc nF), le bF nF) b_Sn) end;
        val caseS =
          let val hsP = jT (mkExSuc_R d)
              val hs  = Thm.assume (ctermRM hsP)
              val Pq = Abs("q", natT, oeq d (suc (Bound 0)))
              fun bodyS e (he:thm) =
                let
                  val c1 = add_cong_r_R (bF, d, suc e) he
                  val Sn_bSe = oeq_trans_vR OF [hd, c1]
                  val bSe = addSr_at_R (bF, e)
                  val Sn_Sbe = oeq_trans_vR OF [Sn_bSe, bSe]
                  val n_be = Suc_inj_R (nF, add bF e) Sn_Sbe
                  val le_bn = le_intro_R (bF, nF, e) n_be
                in disjI2_R (oeq bF (suc nF), le bF nF) le_bn end
              val res = exE_R (Pq, goalC) hs "eSS" bodyS
          in Thm.implies_intr (ctermRM (jT (mkExSuc_R d))) res end;
      in disjE_R (oeq d ZeroC, mkExSuc_R d, goalC) dz caseZ caseS end;
    val res = exE_R (Pabs, goalC) hle "dSS" body;
  in varify (Thm.implies_intr (ctermRM hypP) res) end;
val () = if length (Thm.hyps_of le_suc_split) = 0 then out "OK le_suc_split\n" else out "FAIL le_suc_split\n";
val le_suc_split_vR = le_suc_split;
fun le_suc_split_R (bt,nt) hle =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("b",0), ctermRM bt),(("n",0), ctermRM nt)] le_suc_split_vR)) hle;

(* ============================================================================
   lmem_upto_bwd : Conj (lt 0 b) (le b n) ==> lmem b (uptoF n)   (induction on n)
   ============================================================================ *)
val lmem_upto_bwd =
  let
    val bF = Free("b",natT);
    val nVar = Free("n_iu", natT);
    val Pabs = Term.lambda nVar (mkImp (mkConj (lt ZeroC bF) (le bF nVar)) (lmem bF (uptoF nVar)));
    val base =
      let
        val hypA = jT (mkConj (lt ZeroC bF) (le bF ZeroC))
        val hA   = Thm.assume (ctermRM hypA)
        val hpos = conjunct1_R (lt ZeroC bF, le bF ZeroC) hA
        val hleb0= conjunct2_R (lt ZeroC bF, le bF ZeroC) hA
        val Pd = Abs("d", natT, oeq ZeroC (add bF (Bound 0)))
        fun bd d (hd:thm) =
          let
            val hbd = oeq_sym_vR OF [hd]
            val b0  = add_eq_zero_left_R (bF, d) hbd
            val zLt = Free("z_lt", natT)
            val Plt = Term.lambda zLt (lt ZeroC zLt)
            val lt00 = oeq_rw_R (Plt, bF, ZeroC) b0 hpos
            val Pe = Abs("e", natT, oeq ZeroC (add (suc ZeroC) (Bound 0)))
            fun be e (he:thm) =
              let val aS = addSuc_R (ZeroC, e)
                  val z_S = oeq_trans_vR OF [he, aS]
                  val S_z = oeq_sym_vR OF [z_S]
                  val fls = Suc_neq_Zero_R (add ZeroC e) S_z
              in Thm.implies_elim (oFalse_elim_R (lmem bF (uptoF ZeroC))) fls end
            val res = exE_R (Pe, lmem bF (uptoF ZeroC)) lt00 "e_b0" be
          in res end
        val resmem = exE_R (Pd, lmem bF (uptoF ZeroC)) hleb0 "d_b0" bd
      in impI_R (mkConj (lt ZeroC bF)(le bF ZeroC), lmem bF (uptoF ZeroC)) (Thm.implies_intr (ctermRM hypA) resmem) end;
    val step =
      let
        val xF = Free("x_iu", natT)
        val ihP = jT (mkImp (mkConj (lt ZeroC bF)(le bF xF)) (lmem bF (uptoF xF)))
        val hIH = Thm.assume (ctermRM ihP)
        val hypA = jT (mkConj (lt ZeroC bF)(le bF (suc xF)))
        val hA   = Thm.assume (ctermRM hypA)
        val hpos = conjunct1_R (lt ZeroC bF, le bF (suc xF)) hA
        val hle  = conjunct2_R (lt ZeroC bF, le bF (suc xF)) hA
        val dj = le_suc_split_R (bF, xF) hle
        val goalMem = lmem bF (uptoF (suc xF))
        val hupto = uptoSuc_R xF
        val hupto_s = leq_sym_R hupto
        val consL = lcons (suc xF) (uptoF xF)
        val caseEq =
          let val heq = Thm.assume (ctermRM (jT (oeq bF (suc xF))))
              val dmem = disjI1_R (oeq bF (suc xF), lmem bF (uptoF xF)) heq
              val memCons = Thm.implies_elim (lmemConsBwd_R (bF, suc xF, uptoF xF)) dmem
              val Pmem = Abs("z", natlistT, lmem bF (Bound 0))
              val res = leq_rw_R (Pmem, consL, uptoF (suc xF)) hupto_s memCons
          in Thm.implies_intr (ctermRM (jT (oeq bF (suc xF)))) res end
        val caseLe =
          let val hlex = Thm.assume (ctermRM (jT (le bF xF)))
              val conjx = conjI_R (lt ZeroC bF, le bF xF) hpos hlex
              val memUx = mp_R (mkConj (lt ZeroC bF)(le bF xF), lmem bF (uptoF xF)) hIH conjx
              val dmem = disjI2_R (oeq bF (suc xF), lmem bF (uptoF xF)) memUx
              val memCons = Thm.implies_elim (lmemConsBwd_R (bF, suc xF, uptoF xF)) dmem
              val Pmem = Abs("z", natlistT, lmem bF (Bound 0))
              val res = leq_rw_R (Pmem, consL, uptoF (suc xF)) hupto_s memCons
          in Thm.implies_intr (ctermRM (jT (le bF xF))) res end
        val memThm = disjE_R (oeq bF (suc xF), le bF xF, goalMem) dj caseEq caseLe
        val impThm = impI_R (mkConj (lt ZeroC bF)(le bF (suc xF)), goalMem)
                       (Thm.implies_intr (ctermRM hypA) memThm)
      in Thm.forall_intr (ctermRM xF) (Thm.implies_intr (ctermRM ihP) impThm) end;
    val kF = Free("k_iu", natT)
    val concl = nat_induct_R Pabs kF base step
  in varify concl end;
val () = if length (Thm.hyps_of lmem_upto_bwd) = 0 then out "OK lmem_upto_bwd\n" else out "FAIL lmem_upto_bwd\n";

(* ---- small order helpers on ctxtRM ---- *)
fun le_refl_R t = beta_norm (Drule.infer_instantiate ctxtRM [(("n",0), ctermRM t)] le_refl_vR);
fun lt_0_suc_R nt =
  let val a1 = addSuc_R (ZeroC, nt)
      val a0 = add0_R nt
      val sa0 = Suc_cong_vR OF [a0]
      val sum = oeq_trans_vR OF [a1, sa0]
      val sumS = oeq_sym_vR OF [sum]
  in le_intro_R (suc ZeroC, suc nt, nt) sumS end;
fun le_self_suc_R nt =
  let val aSr = addSr_at_R (nt, ZeroC)
      val a0r = add0r_R nt
      val sa0r = Suc_cong_vR OF [a0r]
      val sum = oeq_trans_vR OF [aSr, sa0r]
      val sumS = oeq_sym_vR OF [sum]
  in le_intro_R (nt, suc nt, suc ZeroC) sumS end;

(* ============================================================================
   lmem_upto_fwd : lmem b (uptoF n) ==> Conj (lt 0 b) (le b n)   (induction on n)
   ============================================================================ *)
val lmem_upto_fwd =
  let
    val bF = Free("b",natT);
    val nVar = Free("n_if", natT);
    val Pabs = Term.lambda nVar (mkImp (lmem bF (uptoF nVar)) (mkConj (lt ZeroC bF) (le bF nVar)));
    val base =
      let
        val goalC = mkConj (lt ZeroC bF) (le bF ZeroC)
        val hmemP = jT (lmem bF (uptoF ZeroC))
        val hmem  = Thm.assume (ctermRM hmemP)
        val hu0   = uptoZero_R
        val Pmem = Abs("z", natlistT, lmem bF (Bound 0))
        val memNil = leq_rw_R (Pmem, uptoF ZeroC, lnilC) hu0 hmem
        val fls = Thm.implies_elim (lmemNilElim_R bF) memNil
        val res = Thm.implies_elim (oFalse_elim_R goalC) fls
      in impI_R (lmem bF (uptoF ZeroC), goalC) (Thm.implies_intr (ctermRM hmemP) res) end;
    val step =
      let
        val xF = Free("x_if", natT)
        val ihP = jT (mkImp (lmem bF (uptoF xF)) (mkConj (lt ZeroC bF) (le bF xF)))
        val hIH = Thm.assume (ctermRM ihP)
        val goalC = mkConj (lt ZeroC bF) (le bF (suc xF))
        val hmemP = jT (lmem bF (uptoF (suc xF)))
        val hmem  = Thm.assume (ctermRM hmemP)
        val hupto = uptoSuc_R xF
        val consL = lcons (suc xF) (uptoF xF)
        val Pmem = Abs("z", natlistT, lmem bF (Bound 0))
        val memCons = leq_rw_R (Pmem, uptoF (suc xF), consL) hupto hmem
        val dj = Thm.implies_elim (lmemConsFwd_R (bF, suc xF, uptoF xF)) memCons
        val caseEq =
          let val heq = Thm.assume (ctermRM (jT (oeq bF (suc xF))))
              val lt0Sx = lt_0_suc_R xF
              val heq_s = oeq_sym_vR OF [heq]
              val Plt = Term.lambda (Free("z_lf",natT)) (lt ZeroC (Free("z_lf",natT)))
              val lt0b = oeq_rw_R (Plt, suc xF, bF) heq_s lt0Sx
              val leRefl = le_refl_R (suc xF)
              val Ple = Term.lambda (Free("z_le",natT)) (le (Free("z_le",natT)) (suc xF))
              val leb = oeq_rw_R (Ple, suc xF, bF) heq_s leRefl
              val cj = conjI_R (lt ZeroC bF, le bF (suc xF)) lt0b leb
          in Thm.implies_intr (ctermRM (jT (oeq bF (suc xF)))) cj end
        val caseMem =
          let val hmemx = Thm.assume (ctermRM (jT (lmem bF (uptoF xF))))
              val cjx = mp_R (lmem bF (uptoF xF), mkConj (lt ZeroC bF)(le bF xF)) hIH hmemx
              val lt0b = conjunct1_R (lt ZeroC bF, le bF xF) cjx
              val lebx = conjunct2_R (lt ZeroC bF, le bF xF) cjx
              val lex_Sx = le_self_suc_R xF
              val leb_Sx = le_trans_R (bF, xF, suc xF) lebx lex_Sx
              val cj = conjI_R (lt ZeroC bF, le bF (suc xF)) lt0b leb_Sx
          in Thm.implies_intr (ctermRM (jT (lmem bF (uptoF xF)))) cj end
        val cjThm = disjE_R (oeq bF (suc xF), lmem bF (uptoF xF), goalC) dj caseEq caseMem
        val impThm = impI_R (lmem bF (uptoF (suc xF)), goalC)
                       (Thm.implies_intr (ctermRM hmemP) cjThm)
      in Thm.forall_intr (ctermRM xF) (Thm.implies_intr (ctermRM ihP) impThm) end;
    val kF = Free("k_if", natT)
    val concl = nat_induct_R Pabs kF base step
  in varify concl end;
val () = if length (Thm.hyps_of lmem_upto_fwd) = 0 then out "OK lmem_upto_fwd\n" else out "FAIL lmem_upto_fwd\n";
fun lmem_upto_fwd_R (bt,nt) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
          [(("b",0), ctermRM bt),(("k_if",0), ctermRM nt)] lmem_upto_fwd)
  in mp_R (lmem bt (uptoF nt), mkConj (lt ZeroC bt)(le bt nt)) inst hmem end;
val () = out "RM_FWD_DONE\n";

(* ============================================================================
   lnodup_upto : lnodup (uptoF n)   (induction on n; Suc n not already in uptoF n)
   ============================================================================ *)
val lt_irrefl_vR = varify lt_irrefl;
fun lt_irrefl_R nt hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM [(("n",0), ctermRM nt)] lt_irrefl_vR)) hlt;
fun lnodup_transfer_R (aT,bT) hleq hnd =
  let val Pabs = Abs("z", natlistT, lnodup (Bound 0))
  in leq_rw_R (Pabs, aT, bT) hleq hnd end;
val lnodup_upto =
  let
    val nVar = Free("n_nd", natT);
    val Pabs = Term.lambda nVar (lnodup (uptoF nVar));
    val base =
      let
        val hu0 = uptoZero_R
        val hu0s = leq_sym_R hu0
        val ndNil = lnodupNil_R
      in lnodup_transfer_R (lnilC, uptoF ZeroC) hu0s ndNil end;
    val step =
      let
        val xF = Free("x_nd", natT)
        val ihP = jT (lnodup (uptoF xF))
        val hIH = Thm.assume (ctermRM ihP)
        val notmem =
          let val hmem = Thm.assume (ctermRM (jT (lmem (suc xF) (uptoF xF))))
              val cj = lmem_upto_fwd_R (suc xF, xF) hmem
              val leSxx = conjunct2_R (lt ZeroC (suc xF), le (suc xF) xF) cj
              val fls = lt_irrefl_R xF leSxx
              val metaImp = Thm.implies_intr (ctermRM (jT (lmem (suc xF) (uptoF xF)))) fls
          in impI_R (lmem (suc xF) (uptoF xF), oFalseC) metaImp end;
        val conjND = conjI_R (neg (lmem (suc xF) (uptoF xF)), lnodup (uptoF xF)) notmem hIH
        val ndCons = Thm.implies_elim (lnodupCons_bwd_R (suc xF, uptoF xF)) conjND
        val hupto = uptoSuc_R xF
        val hupto_s = leq_sym_R hupto
        val res = lnodup_transfer_R (lcons (suc xF) (uptoF xF), uptoF (suc xF)) hupto_s ndCons
      in Thm.forall_intr (ctermRM xF) (Thm.implies_intr (ctermRM ihP) res) end;
    val kF = Free("k_nd", natT)
    val concl = nat_induct_R Pabs kF base step
  in varify concl end;
val () = if length (Thm.hyps_of lnodup_upto) = 0 then out "OK lnodup_upto\n" else out "FAIL lnodup_upto\n";
val () = out "RM_NODUP_DONE\n";

(* ============================================================================
   PHASE 1 FINAL VALIDATION : statements aconv intent, 0-hyp, soundness probes.
   ============================================================================ *)
val () = out "RM_VALIDATE_BEGIN\n";
val aV = Var(("a",0),natT); val bV = Var(("b",0),natT); val pV = Var(("p",0),natT);
val cong_imp_rmodeq_intended =
  Logic.mk_implies (jT (lt ZeroC pV),
    Logic.mk_implies (jT (cong pV aV bV), jT (oeq (rmod aV pV) (rmod bV pV))));
val r_dir1 = (length (Thm.hyps_of cong_imp_rmodeq) = 0)
             andalso ((Thm.prop_of cong_imp_rmodeq) aconv cong_imp_rmodeq_intended);
val () = if r_dir1 then out "OK cong_imp_rmodeq aconv intended\n" else out "FAIL cong_imp_rmodeq aconv\n";
val rmodeq_imp_cong_intended =
  Logic.mk_implies (jT (lt ZeroC pV),
    Logic.mk_implies (jT (oeq (rmod aV pV) (rmod bV pV)), jT (cong pV aV bV)));
val r_dir2 = (length (Thm.hyps_of rmodeq_imp_cong) = 0)
             andalso ((Thm.prop_of rmodeq_imp_cong) aconv rmodeq_imp_cong_intended);
val () = if r_dir2 then out "OK rmodeq_imp_cong aconv intended\n" else out "FAIL rmodeq_imp_cong aconv\n";
val probe_dir1_needs_pos =
  let val bogus = Logic.mk_implies (jT (cong pV aV bV), jT (oeq (rmod aV pV)(rmod bV pV)))
  in not ((Thm.prop_of cong_imp_rmodeq) aconv bogus) end;
val () = if probe_dir1_needs_pos then out "PROBE_OK cong_imp_rmodeq keeps 0<p premise\n"
         else out "PROBE_FAIL cong_imp_rmodeq dropped 0<p!\n";
val probe_dir2_needs_pos =
  let val bogus = Logic.mk_implies (jT (oeq (rmod aV pV)(rmod bV pV)), jT (cong pV aV bV))
  in not ((Thm.prop_of rmodeq_imp_cong) aconv bogus) end;
val () = if probe_dir2_needs_pos then out "PROBE_OK rmodeq_imp_cong keeps 0<p premise\n"
         else out "PROBE_FAIL rmodeq_imp_cong dropped 0<p!\n";
val rmod_lt_check =
  let val h = rmod_lt_R (Free("aa",natT), suc ZeroC) (lt_suc_R ZeroC)
  in (length (Thm.hyps_of h) = 0) end;
val () = if rmod_lt_check then out "PROBE_OK rmod a p < p usable (rmod_lt)\n" else out "PROBE_FAIL rmod_lt\n";
val div_mod_eq_check =
  let val h = div_mod_eq_R (Free("aa",natT), suc ZeroC) (lt_suc_R ZeroC)
  in (length (Thm.hyps_of h) = 0) end;
val () = if div_mod_eq_check then out "PROBE_OK div_mod_eq usable\n" else out "PROBE_FAIL div_mod_eq\n";
val r_upto_nodup = (length (Thm.hyps_of lnodup_upto) = 0);
val r_upto_fwd   = (length (Thm.hyps_of lmem_upto_fwd) = 0);
val r_upto_bwd   = (length (Thm.hyps_of lmem_upto_bwd) = 0);
val () =
  if r_dir1 andalso r_dir2 andalso probe_dir1_needs_pos andalso probe_dir2_needs_pos
     andalso rmod_lt_check andalso div_mod_eq_check
     andalso r_upto_nodup andalso r_upto_fwd andalso r_upto_bwd
  then out "RANGE_MOD_OK\n"
  else out "RANGE_MOD_FAILED\n";

(* ============================================================================
   PHASE 2 (seat iv0): the MODULAR INVERSE FUNCTION as a literal involution.
   Define fsearch (list-recursive, conditional on rmod decision) + finv, prove
   finv_inv / finv_mem / finv_invol / finv_neq.  Built on the Phase-1 final
   context (thyRM / ctxtRM / ctermRM).
   ============================================================================ *)
val () = out "WI_PHASE2_BEGIN\n";

(* ---- new consts: sub (truncated subtraction), fsearch, finv ---- *)
val thyWc = Sign.add_consts
  [(Binding.name "sub",     natT --> natT --> natT, NoSyn),
   (Binding.name "fsearch", natT --> natT --> natlistT --> natT, NoSyn),
   (Binding.name "finv",    natT --> natT --> natT, NoSyn)] thyRM;

fun cnstW nm T = Const (Sign.full_name thyWc (Binding.name nm), T);
val subC     = cnstW "sub" (natT --> natT --> natT);  fun sub a b = subC $ a $ b;
val fsearchC = cnstW "fsearch" (natT --> natT --> natlistT --> natT);
fun fsearch p x l = fsearchC $ p $ x $ l;
val finvC    = cnstW "finv" (natT --> natT --> natT); fun finv p x = finvC $ p $ x;

(* free vars for axiom statements *)
val pW = Free("p", natT); val xW0 = Free("x", natT); val bW = Free("b", natT);
val bsW = Free("bs", natlistT); val nW = Free("n", natT); val mW0 = Free("m", natT);

(* the decidable search condition : oeq (rmod (mult x b) p) (Suc Zero) *)
fun searchCond pt xt bt = oeq (rmod (mult xt bt) pt) (suc ZeroC);

(* ---- sub : recursion axioms (truncated subtraction) ----
     sub_0   : oeq (sub n Zero) n
     sub_SS  : oeq (sub (Suc n) (Suc m)) (sub n m)        *)
val ((_,sub_0_ax), thyW1) = Thm.add_axiom_global (Binding.name "sub_0",
      jT (oeq (sub nW ZeroC) nW)) thyWc;
val ((_,sub_SS_ax), thyW2) = Thm.add_axiom_global (Binding.name "sub_SS",
      jT (oeq (sub (suc nW) (suc mW0)) (sub nW mW0))) thyW1;

(* ---- fsearch : CONDITIONAL list-recursion axioms ----
     fsearch_nil      : oeq (fsearch p x lnil) Zero
     fsearch_cons_eq  : jT (searchCond p x b)        ==> oeq (fsearch p x (lcons b bs)) b
     fsearch_cons_neq : jT (neg (searchCond p x b))  ==> oeq (fsearch p x (lcons b bs)) (fsearch p x bs)  *)
val ((_,fsearch_nil_ax), thyW3) = Thm.add_axiom_global (Binding.name "fsearch_nil",
      jT (oeq (fsearch pW xW0 lnilC) ZeroC)) thyW2;
val ((_,fsearch_cons_eq_ax), thyW4) = Thm.add_axiom_global (Binding.name "fsearch_cons_eq",
      Logic.mk_implies (jT (searchCond pW xW0 bW),
        jT (oeq (fsearch pW xW0 (lcons bW bsW)) bW))) thyW3;
val ((_,fsearch_cons_neq_ax), thyW5) = Thm.add_axiom_global (Binding.name "fsearch_cons_neq",
      Logic.mk_implies (jT (neg (searchCond pW xW0 bW)),
        jT (oeq (fsearch pW xW0 (lcons bW bsW)) (fsearch pW xW0 bsW)))) thyW4;

(* ---- finv : defining axiom  finv p x = fsearch p x (upto (sub p (Suc Zero))) ---- *)
val ((_,finv_def_ax), thyW) = Thm.add_axiom_global (Binding.name "finv_def",
      jT (oeq (finv pW xW0) (fsearch pW xW0 (uptoF (sub pW (suc ZeroC)))))) thyW5;

val ctxtW  = Proof_Context.init_global thyW;
val ctermW = Thm.cterm_of ctxtW;
val () = out "WI_CONTEXT_READY\n";

(* ============================================================================
   re-varify reused base axioms/lemmas + Phase-1 lemmas onto ctxtW
   ============================================================================ *)
(* FOL / foundation *)
val oeq_refl_vW    = varify oeq_refl;
val oeq_subst_vW   = varify oeq_subst;
val oeq_sym_vW     = varify oeq_sym;
val oeq_trans_vW   = varify oeq_trans;
val Suc_cong_vW    = varify Suc_cong;
val exI_vW         = varify exI_ax;
val exE_vW         = varify exE_ax;
val oFalse_elim_vW = varify oFalse_elim_ax;
val Suc_neq_Zero_vW= varify Suc_neq_Zero_ax;
val Suc_inj_vW     = varify Suc_inj_ax;
val conjI_vW       = varify conjI_ax;
val conjunct1_vW   = varify conjunct1_ax;
val conjunct2_vW   = varify conjunct2_ax;
val disjI1_vW      = varify disjI1_ax;
val disjI2_vW      = varify disjI2_ax;
val disjE_vW       = varify disjE_ax;
val mp_vW          = varify mp_ax;
val impI_vW        = varify impI_ax;
val ex_middle_vW   = varify ex_middle_ax;
val allI_vW        = varify allI_ax;
val allE_vW        = varify allE_ax;
(* arithmetic *)
val add_0_vW       = varify add_0;
val add_Suc_vW     = varify add_Suc;
val add_0_right_vW = varify add_0_right;
val add_Suc_right_vW = varify add_Suc_right;
val add_comm_vW    = varify add_comm;
val add_assoc_vW   = varify add_assoc;
val add_left_cancel_vW = varify add_left_cancel;
val mult_0_vW      = varify mult_0;
val mult_Suc_vW    = varify mult_Suc;
val mult_0_right_vW= varify mult_0_right;
val mult_Suc_right_vW = varify mult_Suc_right;
val mult_comm_vW   = varify mult_comm;
val mult_assoc_vW  = varify mult_assoc;
val mult_1_left_vW = varify mult_1_left;
val mult_1_right_vW= varify mult_1_right;
val left_distrib_vW= varify left_distrib;
val right_distrib_vW = varify right_distrib;
(* order *)
val le_refl_vW     = varify le_refl;
val le_trans_vW    = varify le_trans;
val le_total_vW    = varify le_total;
val le_antisym_vW  = varify le_antisym;
val le_add_vW      = varify le_add;
val zero_le_vW     = varify zero_le;
val lt_suc_vW      = varify lt_suc;
val lt_trans_vW    = varify lt_trans;
val lt_irrefl_vW   = varify lt_irrefl;
val nlt_le_vW      = varify nlt_le;
val disj_zero_or_suc_vW = varify disj_zero_or_suc;
val add_eq_zero_left_vW = varify add_eq_zero_left;
val nat_induct_vW  = varify nat_induct;
val div_mod_unique_vW = varify div_mod_unique;
(* dvd / prime / cong base theorems *)
val dvd_le_vW      = varify dvd_le;
val mod_inverse_vW = varify mod_inverse;
val inverse_unique_vW = varify inverse_unique;
val lagrange_roots_vW = varify lagrange_roots;
val cong_refl_vW   = varify cong_refl;
val cong_sym_vW    = varify cong_sym;
val cong_trans_vW  = varify cong_trans;
val cong_mult_vW   = varify cong_mult;
(* Phase-1 lemmas *)
val cong_imp_rmodeq_vW = varify cong_imp_rmodeq;
val rmodeq_imp_cong_vW = varify rmodeq_imp_cong;
val lmem_upto_fwd_vW = varify lmem_upto_fwd;
val lmem_upto_bwd_vW = varify lmem_upto_bwd;
val lnodup_upto_vW   = varify lnodup_upto;
val div_mod_eq_vW  = varify div_mod_eq_ax;
val rmod_lt_vW     = varify rmod_lt_ax;
val upto_zero_vW   = varify upto_zero_ax;
val upto_suc_vW    = varify upto_suc_ax;
(* list machinery *)
val leq_refl_vW    = varify leq_refl_ax;
val leq_subst_vW   = varify leq_subst_ax;
val list_induct_vW = varify list_induct_ax;
val lmem_nil_elim_vW = varify lmem_nil_elim_ax;
val lmem_cons_fwd_vW = varify lmem_cons_fwd_ax;
val lmem_cons_bwd_vW = varify lmem_cons_bwd_ax;
val lnodup_nil_vW  = varify lnodup_nil_ax;
val lnodup_cons_fwd_vW = varify lnodup_cons_fwd_ax;
val lnodup_cons_bwd_vW = varify lnodup_cons_bwd_ax;
(* new W axioms *)
val sub_0_vW       = varify sub_0_ax;
val sub_SS_vW      = varify sub_SS_ax;
val fsearch_nil_vW = varify fsearch_nil_ax;
val fsearch_cons_eq_vW = varify fsearch_cons_eq_ax;
val fsearch_cons_neq_vW = varify fsearch_cons_neq_ax;
val finv_def_vW    = varify finv_def_ax;
val () = out "WI_VARIFY_READY\n";

(* ============================================================================
   combinators on ctxtW (suffix _W)
   ============================================================================ *)
fun oeqRefl_W t = beta_norm (Drule.infer_instantiate ctxtW [(("a",0), ctermW t)] oeq_refl_vW);
fun add0_W t    = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] add_0_vW);
fun add0r_W t   = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] add_0_right_vW);
fun addSuc_W (mt,nt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt)] add_Suc_vW);
fun addSr_W (mt,nt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt)] add_Suc_right_vW);
fun addcomm_W (mt,nt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt)] add_comm_vW);
fun addassoc_W (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt),(("k",0), ctermW kt)] add_assoc_vW);
fun mult0r_W t  = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] mult_0_right_vW);
fun mult1r_W t  = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] mult_1_right_vW);
fun mult1l_W t  = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] mult_1_left_vW);
fun multcomm_W (mt,nt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt)] mult_comm_vW);
fun multassoc_W (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt),(("k",0), ctermW kt)] mult_assoc_vW);
fun multSuc_W (mt,nt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt)] mult_Suc_vW);

fun oeq_rw_W (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("P",0), ctermW Pabs),(("a",0), ctermW aT),(("b",0), ctermW bT)] oeq_subst_vW)
  in inst OF [hab, hPa] end;
fun add_cong_l_W (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT))
  in oeq_rw_W (Pabs, pT, qT) hpq (oeqRefl_W (add pT kT)) end;
fun add_cong_r_W (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)))
  in oeq_rw_W (Pabs, pT, qT) hpq (oeqRefl_W (add hT pT)) end;
fun mult_cong_l_W (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT))
  in oeq_rw_W (Pabs, pT, qT) hpq (oeqRefl_W (mult pT kT)) end;
fun mult_cong_r_W (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)))
  in oeq_rw_W (Pabs, pT, qT) hpq (oeqRefl_W (mult hT pT)) end;

fun mp_W (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("A",0), ctermW At),(("B",0), ctermW Bt)] mp_vW)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_W (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("A",0), ctermW At),(("B",0), ctermW Bt)] impI_vW)
  in Thm.implies_elim inst hImpThm end;
fun conjI_W (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("A",0), ctermW At),(("B",0), ctermW Bt)] conjI_vW)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_W (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("A",0), ctermW At),(("B",0), ctermW Bt)] conjunct1_vW)) h;
fun conjunct2_W (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("A",0), ctermW At),(("B",0), ctermW Bt)] conjunct2_vW)) h;
fun oFalse_elim_W rT = beta_norm (Drule.infer_instantiate ctxtW [(("R",0), ctermW rT)] oFalse_elim_vW);
fun disjE_W (At,Bt,Ct) dThm cA cB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("A",0), ctermW At),(("B",0), ctermW Bt),(("C",0), ctermW Ct)] disjE_vW)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) cA) cB end;
fun disjI1_W (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("A",0), ctermW At),(("B",0), ctermW Bt)] disjI1_vW)) h;
fun disjI2_W (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("A",0), ctermW At),(("B",0), ctermW Bt)] disjI2_vW)) h;
fun em_W t = beta_norm (Drule.infer_instantiate ctxtW [(("A",0), ctermW t)] ex_middle_vW);
fun Suc_neq_Zero_W nt heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW nt)] Suc_neq_Zero_vW)) heq;
fun Suc_inj_W (at,bt) heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("a",0), ctermW at),(("b",0), ctermW bt)] Suc_inj_vW)) heq;

fun exI_W Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("P",0), ctermW Pabs),(("a",0), ctermW at)] exI_vW)
  in Thm.implies_elim inst hbody end;
fun exE_W (Pabs, goalC) exThm wName bodyFn =
  let val wF = Free(wName, natT)
      val hypTerm = jT (Term.betapply (Pabs, wF))
      val hypThm  = Thm.assume (ctermW hypTerm)
      val body    = bodyFn wF hypThm
      val minor   = Thm.forall_intr (ctermW wF) (Thm.implies_intr (ctermW hypTerm) body)
      val exE_inst= beta_norm (Drule.infer_instantiate ctxtW
                      [(("P",0), ctermW Pabs),(("Q",0), ctermW goalC)] exE_vW)
  in Thm.implies_elim (Thm.implies_elim exE_inst exThm) minor end;

fun le_intro_W (mT, nT, w) hyp =
  let val Pabs = Abs("p", natT, oeq nT (add mT (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtW
            [(("P",0), ctermW Pabs),(("a",0), ctermW w)] exI_vW)
  in inst OF [hyp] end;
fun le_total_W (mt,nt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt)] le_total_vW);
fun le_trans_W (at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("m",0), ctermW at),(("n",0), ctermW bt),(("k",0), ctermW ct)] le_trans_vW)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun lt_trans_W (at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("a",0), ctermW at),(("b",0), ctermW bt),(("c",0), ctermW ct)] lt_trans_vW)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun lt_irrefl_W nt hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW nt)] lt_irrefl_vW)) hlt;
fun le_refl_W t = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] le_refl_vW);
fun le_antisym_W (mt,nt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("m",0), ctermW mt),(("n",0), ctermW nt)] le_antisym_vW)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun le_add_W (mt,pt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("p",0), ctermW pt)] le_add_vW);
fun lt_suc_W nt = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW nt)] lt_suc_vW);
fun nlt_le_W (dt,ct) hneg =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("d",0), ctermW dt),(("c",0), ctermW ct)] nlt_le_vW)) hneg;
fun dzos_W t = beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW t)] disj_zero_or_suc_vW);
fun mkExSuc_W t = mkEx (Abs ("q", natT, oeq t (suc (Bound 0))));

fun div_mod_eq_W (at,pt) hpos =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("a",0), ctermW at),(("p",0), ctermW pt)] div_mod_eq_vW)) hpos;
fun rmod_lt_W (at,pt) hpos =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("a",0), ctermW at),(("p",0), ctermW pt)] rmod_lt_vW)) hpos;
fun div_mod_unique_W (b,q1,r1,q2,r2) heq hlt1 hlt2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("b",0), ctermW b),(("q1",0), ctermW q1),(("r1",0), ctermW r1),
         (("q2",0), ctermW q2),(("r2",0), ctermW r2)] div_mod_unique_vW)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst heq) hlt1) hlt2 end;

(* upto recursion on ctxtW *)
fun uptoSuc_W nt = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW nt)] upto_suc_vW);
val uptoZero_W = upto_zero_vW;
fun leq_rw_W (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("P",0), ctermW Pabs),(("a",0), ctermW aT),(("b",0), ctermW bT)] leq_subst_vW)
  in inst OF [hab, hPa] end;
fun lmemConsFwd_W (x,y,t) = beta_norm (Drule.infer_instantiate ctxtW
      [(("x",0), ctermW x),(("y",0), ctermW y),(("t",0), ctermW t)] lmem_cons_fwd_vW);
fun lmemConsBwd_W (x,y,t) = beta_norm (Drule.infer_instantiate ctxtW
      [(("x",0), ctermW x),(("y",0), ctermW y),(("t",0), ctermW t)] lmem_cons_bwd_vW);
fun lmemNilElim_W x = beta_norm (Drule.infer_instantiate ctxtW [(("x",0), ctermW x)] lmem_nil_elim_vW);

(* sub / fsearch / finv recursion on ctxtW *)
fun sub0_W t = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] sub_0_vW);
fun subSS_W (nt,mt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("n",0), ctermW nt),(("m",0), ctermW mt)] sub_SS_vW);
val fsearchNil_W = fsearch_nil_vW;
fun fsearchNil_at (pt,xt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt),(("x",0), ctermW xt)] fsearch_nil_vW);
fun fsearchEq_W (pt,xt,bt,bst) hcond =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt),(("x",0), ctermW xt),(("b",0), ctermW bt),(("bs",0), ctermW bst)]
      fsearch_cons_eq_vW)) hcond;
fun fsearchNeq_W (pt,xt,bt,bst) hncond =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt),(("x",0), ctermW xt),(("b",0), ctermW bt),(("bs",0), ctermW bst)]
      fsearch_cons_neq_vW)) hncond;
fun finvDef_W (pt,xt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt),(("x",0), ctermW xt)] finv_def_vW);

(* cong combinators on ctxtW *)
fun cong_refl_W (mt,at) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("a",0), ctermW at)] cong_refl_vW);
fun cong_sym_W (mt,at,bt) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("a",0), ctermW at),(("b",0), ctermW bt)] cong_sym_vW)) h;
fun cong_trans_W (mt,at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("m",0), ctermW mt),(("a",0), ctermW at),(("b",0), ctermW bt),(("c",0), ctermW ct)] cong_trans_vW)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun cong_mult_W (mt,at,a2t,bt,b2t) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("m",0), ctermW mt),(("a",0), ctermW at),(("a2",0), ctermW a2t),
         (("b",0), ctermW bt),(("b2",0), ctermW b2t)] cong_mult_vW)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
(* cong_of_eq on ctxtW : from heq : oeq X Y build jT (cong p X Y) (capture-safe) *)
fun cong_of_eq_W (pT, X, Y) heq =
  let val zF = Free("z_coe", natT)
      val Pabs = Term.lambda zF (cong pT X zF)
      val inst = beta_norm (Drule.infer_instantiate ctxtW
            [(("P",0), ctermW Pabs),(("a",0), ctermW X),(("b",0), ctermW Y)] oeq_subst_vW)
      val crefl = cong_refl_W (pT, X)
  in inst OF [heq, crefl] end;

(* cong_imp_rmodeq / rmodeq_imp_cong on ctxtW *)
fun cong_imp_rmodeq_W (pt,at,bt) hpos hcong =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("a",0), ctermW at),(("b",0), ctermW bt)] cong_imp_rmodeq_vW)
  in Thm.implies_elim (Thm.implies_elim inst hpos) hcong end;
fun rmodeq_imp_cong_W (pt,at,bt) hpos heq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("a",0), ctermW at),(("b",0), ctermW bt)] rmodeq_imp_cong_vW)
  in Thm.implies_elim (Thm.implies_elim inst hpos) heq end;

(* lmem_upto on ctxtW *)
fun lmem_upto_fwd_W (bt,nt) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
          [(("b",0), ctermW bt),(("k_if",0), ctermW nt)] lmem_upto_fwd_vW)
  in mp_W (lmem bt (uptoF nt), mkConj (lt ZeroC bt)(le bt nt)) inst hmem end;
fun lmem_upto_bwd_W (bt,nt) hconj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
          [(("b",0), ctermW bt),(("k_iu",0), ctermW nt)] lmem_upto_bwd_vW)
  in mp_W (mkConj (lt ZeroC bt)(le bt nt), lmem bt (uptoF nt)) inst hconj end;

(* prime2 destructors on ctxtW *)
fun prime2_gt1_W pt hprime = conjunct1_W (lt (suc ZeroC) pt, mkForall (ppAbs pt)) hprime;
fun prime2_div_W pt hprime = conjunct2_W (lt (suc ZeroC) pt, mkForall (ppAbs pt)) hprime;
fun allE_W Pabs at hF = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("P",0), ctermW Pabs),(("a",0), ctermW at)] allE_vW)) hF;

(* dvd helpers on ctxtW *)
fun dvd_intro_W (aT, bT, w) hyp =
  let val Pabs = Abs("k", natT, oeq bT (mult aT (Bound 0)))
  in exI_W Pabs w hyp end;
fun dvd_le_W (dt,nt) hdvd hnz =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("d",0), ctermW dt),(("n",0), ctermW nt)] dvd_le_vW)
  in Thm.implies_elim (Thm.implies_elim inst hdvd) hnz end;

(* mod_inverse / inverse_unique / lagrange_roots on ctxtW.
   mod_inverse goal binder is `b_mi` ; build the same lambda. *)
fun mi_innerAbs_W (pt, at) =
  let val bF = Free("b_mi", natT) in Term.lambda bF (cong pt (mult at bF) (suc ZeroC)) end;
fun mod_inverse_W (pt,at) hPrime hNdvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("a",0), ctermW at)] mod_inverse_vW)
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hNdvd end;
fun inverse_unique_W (pt,at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("a",0), ctermW at),(("b",0), ctermW bt),(("c",0), ctermW ct)] inverse_unique_vW)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun lagrange_roots_W (pt,at) hPrime hsq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("a",0), ctermW at)] lagrange_roots_vW)
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hsq end;

val () = out "WI_COMBINATORS_READY\n";

(* ============================================================================
   SMOKE TEST : sub p 1 = p-1 when p = Suc q.  sub_suc_one : oeq (sub (Suc q) (Suc Zero)) q
   ============================================================================ *)
val sub_suc_one =
  let val qF = Free("q", natT)
      val e1 = subSS_W (qF, ZeroC)          (* oeq (sub (Suc q)(Suc 0)) (sub q 0) *)
      val e2 = sub0_W qF                     (* oeq (sub q 0) q *)
  in varify (oeq_trans_vW OF [e1, e2]) end;
val () = if length (Thm.hyps_of sub_suc_one) = 0 then out "OK sub_suc_one\n" else out "FAIL sub_suc_one\n";

val () = out "WI_SMOKE_DONE\n";

(* ============================================================================
   list_induct combinator on ctxtW.  Predicate Pabs : natlist => o, target list LT.
   baseThm : jT (Pabs $ lnil) ; stepThm : !!x.!!l. jT (Pabs $ l) ==> jT (Pabs $ (lcons x l)).
   ============================================================================ *)
fun list_induct_W (Pabs, LT) baseThm stepThm =
  let val ind = beta_norm (Drule.infer_instantiate ctxtW
        [(("P",0), ctermW Pabs),(("a",0), ctermW LT)] list_induct_vW)
  in Thm.implies_elim (Thm.implies_elim ind baseThm) stepThm end;

(* ============================================================================
   rmod_one : 1 < p ==> oeq (rmod (Suc Zero) p) (Suc Zero)
   ============================================================================ *)
val rmod_one =
  let
    val pF = Free("p", natT)
    val hp1P = jT (lt (suc ZeroC) pF)
    val hp1  = Thm.assume (ctermW hp1P)
    val one = suc ZeroC
    val le_1_2 =
      let val aSr = addSr_W (one, ZeroC)
          val a0r = add0r_W one
          val s   = Suc_cong_vW OF [a0r]
          val sum = oeq_trans_vW OF [aSr, s]
          val sumS= oeq_sym_vW OF [sum]
      in le_intro_W (one, suc one, suc ZeroC) sumS end
    val hp0 = le_trans_W (one, suc one, pF) le_1_2 hp1
    val hEq = div_mod_eq_W (one, pF) hp0
    val q1 = rdiv one pF ; val r1 = rmod one pF
    val hr1lt = rmod_lt_W (one, pF) hp0
    val p0 = mult0r_W pF
    val pol = add_cong_l_W (mult pF ZeroC, ZeroC, one) p0
    val z1 = add0_W one
    val eq2 = oeq_trans_vW OF [pol, z1]
    val eqWit = oeq_sym_vW OF [eq2]
    val combined = oeq_trans_vW OF [oeq_sym_vW OF [hEq], eqWit]
    val uniq = div_mod_unique_W (pF, q1, r1, ZeroC, one) combined hr1lt hp1
    val r1_one = conjunct2_W (oeq q1 ZeroC, oeq r1 one) uniq
  in varify (Thm.implies_intr (ctermW hp1P) r1_one) end;
val () = if length (Thm.hyps_of rmod_one) = 0 then out "OK rmod_one\n" else out "FAIL rmod_one\n";
fun rmod_one_W pt hp1 =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pt)] rmod_one)) hp1;

fun lt1_imp_lt0_W pt hp1 =
  let val one = suc ZeroC
      val aSr = addSr_W (one, ZeroC)
      val a0r = add0r_W one
      val s   = Suc_cong_vW OF [a0r]
      val sum = oeq_trans_vW OF [aSr, s]
      val sumS= oeq_sym_vW OF [sum]
      val le_1_2 = le_intro_W (one, suc one, suc ZeroC) sumS
  in le_trans_W (one, suc one, pt) le_1_2 hp1 end;

val () = out "WI_RMOD_ONE_DONE\n";

(* ============================================================================
   searchCond <-> cong  bridges (under 1 < p).
   ============================================================================ *)
val scond_imp_cong =
  let
    val pF = Free("p", natT); val xF = Free("x", natT); val bF = Free("b", natT)
    val one = suc ZeroC
    val hp1P = jT (lt one pF) ; val hp1 = Thm.assume (ctermW hp1P)
    val hcP  = jT (searchCond pF xF bF) ; val hc = Thm.assume (ctermW hcP)
    val hp0  = lt1_imp_lt0_W pF hp1
    val r1 = rmod_one_W pF hp1
    val r1s = oeq_sym_vW OF [r1]
    val eqr = oeq_trans_vW OF [hc, r1s]
    val congXB = rmodeq_imp_cong_W (pF, mult xF bF, one) hp0 eqr
    val d2 = Thm.implies_intr (ctermW hcP) congXB
    val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of scond_imp_cong) = 0 then out "OK scond_imp_cong\n" else out "FAIL scond_imp_cong\n";
fun scond_imp_cong_W (pt,xt,bt) hp1 hc =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("x",0), ctermW xt),(("b",0), ctermW bt)] scond_imp_cong)
  in Thm.implies_elim (Thm.implies_elim inst hp1) hc end;

val cong_imp_scond =
  let
    val pF = Free("p", natT); val xF = Free("x", natT); val bF = Free("b", natT)
    val one = suc ZeroC
    val hp1P = jT (lt one pF) ; val hp1 = Thm.assume (ctermW hp1P)
    val hcgP = jT (cong pF (mult xF bF) one) ; val hcg = Thm.assume (ctermW hcgP)
    val hp0  = lt1_imp_lt0_W pF hp1
    val eqr  = cong_imp_rmodeq_W (pF, mult xF bF, one) hp0 hcg
    val r1   = rmod_one_W pF hp1
    val sc   = oeq_trans_vW OF [eqr, r1]
    val d2 = Thm.implies_intr (ctermW hcgP) sc
    val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of cong_imp_scond) = 0 then out "OK cong_imp_scond\n" else out "FAIL cong_imp_scond\n";
fun cong_imp_scond_W (pt,xt,bt) hp1 hcg =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("x",0), ctermW xt),(("b",0), ctermW bt)] cong_imp_scond)
  in Thm.implies_elim (Thm.implies_elim inst hp1) hcg end;

val () = out "WI_SCOND_BRIDGE_DONE\n";

(* ============================================================================
   fsearch_found : (Ex b. Conj (lmem b L)(searchCond p x b))
                   ==> Conj (searchCond p x (fsearch p x L)) (lmem (fsearch p x L) L)
   by list induction on L (p, x fixed Frees).  KEY: build the induction predicate
   over a FRESH Free list var (Term.lambda does NOT shift loose Bounds).
   ============================================================================ *)
val fsearch_found =
  let
    val pF = Free("p", natT); val xF = Free("x", natT)
    fun existsCond zt = mkEx (Term.lambda (Free("b_fe", natT))
                          (mkConj (lmem (Free("b_fe", natT)) zt) (searchCond pF xF (Free("b_fe", natT)))))
    fun goodConc zt = mkConj (searchCond pF xF (fsearch pF xF zt)) (lmem (fsearch pF xF zt) zt)
    fun concBody zt = mkImp (existsCond zt) (goodConc zt)
    val zPF = Free("z_lst", natlistT)
    val Pabs = Term.lambda zPF (concBody zPF)
    val LF = Free("L", natlistT)
    val base =
      let
        val hexP = jT (existsCond lnilC)
        val hex  = Thm.assume (ctermW hexP)
        val goalC = goodConc lnilC
        val PexAbs = Term.lambda (Free("b_fe", natT))
                       (mkConj (lmem (Free("b_fe", natT)) lnilC) (searchCond pF xF (Free("b_fe", natT))))
        fun ebody w (hw:thm) =
          let val memNil = conjunct1_W (lmem w lnilC, searchCond pF xF w) hw
              val fls = Thm.implies_elim (lmemNilElim_W w) memNil
          in Thm.implies_elim (oFalse_elim_W goalC) fls end
        val res = exE_W (PexAbs, goalC) hex "w_fb" ebody
      in impI_W (existsCond lnilC, goalC) (Thm.implies_intr (ctermW hexP) res) end
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val ihP = jT (concBody tF)
    val IH  = Thm.assume (ctermW ihP)
    val step =
      let
        val consL = lcons hF tF
        val hexP = jT (existsCond consL)
        val hex  = Thm.assume (ctermW hexP)
        val goalC = goodConc consL
        val emH = em_W (searchCond pF xF hF)
        val caseEq =
          let
            val hch = Thm.assume (ctermW (jT (searchCond pF xF hF)))
            val fEq = fsearchEq_W (pF, xF, hF, tF) hch
            val fEqS = oeq_sym_vW OF [fEq]
            val Pcond = Term.lambda (Free("z_sc", natT)) (searchCond pF xF (Free("z_sc", natT)))
            val condFs = oeq_rw_W (Pcond, hF, fsearch pF xF consL) fEqS hch
            val memH = Thm.implies_elim (lmemConsBwd_W (hF, hF, tF))
                         (disjI1_W (oeq hF hF, lmem hF tF) (oeqRefl_W hF))
            val Pmem = Term.lambda (Free("z_m", natT)) (lmem (Free("z_m", natT)) consL)
            val memFs = oeq_rw_W (Pmem, hF, fsearch pF xF consL) fEqS memH
            val cj = conjI_W (searchCond pF xF (fsearch pF xF consL), lmem (fsearch pF xF consL) consL) condFs memFs
          in Thm.implies_intr (ctermW (jT (searchCond pF xF hF))) cj end
        val caseNeq =
          let
            val hnch = Thm.assume (ctermW (jT (neg (searchCond pF xF hF))))
            val fNeq = fsearchNeq_W (pF, xF, hF, tF) hnch
            val PexAbs = Term.lambda (Free("b_fe", natT))
                           (mkConj (lmem (Free("b_fe", natT)) consL) (searchCond pF xF (Free("b_fe", natT))))
            val existsT = existsCond tF
            fun ebody w (hw:thm) =
              let
                val memCons = conjunct1_W (lmem w consL, searchCond pF xF w) hw
                val scw     = conjunct2_W (lmem w consL, searchCond pF xF w) hw
                val dj      = Thm.implies_elim (lmemConsFwd_W (w, hF, tF)) memCons
                val cWh =
                  let val hwh = Thm.assume (ctermW (jT (oeq w hF)))
                      val Pcond = Term.lambda (Free("z_sc2", natT)) (searchCond pF xF (Free("z_sc2", natT)))
                      val sch = oeq_rw_W (Pcond, w, hF) hwh scw
                      val fls = mp_W (searchCond pF xF hF, oFalseC) hnch sch
                      val any = Thm.implies_elim (oFalse_elim_W existsT) fls
                  in Thm.implies_intr (ctermW (jT (oeq w hF))) any end
                val cWt =
                  let val hwt = Thm.assume (ctermW (jT (lmem w tF)))
                      val cj  = conjI_W (lmem w tF, searchCond pF xF w) hwt scw
                      val PexT = Term.lambda (Free("b_fe", natT))
                                   (mkConj (lmem (Free("b_fe", natT)) tF) (searchCond pF xF (Free("b_fe", natT))))
                      val ex  = exI_W PexT w cj
                  in Thm.implies_intr (ctermW (jT (lmem w tF))) ex end
              in disjE_W (oeq w hF, lmem w tF, existsT) dj cWh cWt end
            val exT = exE_W (PexAbs, existsT) hex "w_fn" ebody
            val goodT = mp_W (existsCond tF, goodConc tF) IH exT
            val condT = conjunct1_W (searchCond pF xF (fsearch pF xF tF), lmem (fsearch pF xF tF) tF) goodT
            val memT  = conjunct2_W (searchCond pF xF (fsearch pF xF tF), lmem (fsearch pF xF tF) tF) goodT
            val fNeqS = oeq_sym_vW OF [fNeq]
            val Pcond = Term.lambda (Free("z_c3", natT)) (searchCond pF xF (Free("z_c3", natT)))
            val condCons = oeq_rw_W (Pcond, fsearch pF xF tF, fsearch pF xF consL) fNeqS condT
            val memConsT = Thm.implies_elim (lmemConsBwd_W (fsearch pF xF tF, hF, tF))
                             (disjI2_W (oeq (fsearch pF xF tF) hF, lmem (fsearch pF xF tF) tF) memT)
            val Pmem = Term.lambda (Free("z_m3", natT)) (lmem (Free("z_m3", natT)) consL)
            val memCons = oeq_rw_W (Pmem, fsearch pF xF tF, fsearch pF xF consL) fNeqS memConsT
            val cj = conjI_W (searchCond pF xF (fsearch pF xF consL), lmem (fsearch pF xF consL) consL) condCons memCons
          in Thm.implies_intr (ctermW (jT (neg (searchCond pF xF hF)))) cj end
        val conc = disjE_W (searchCond pF xF hF, neg (searchCond pF xF hF), goalC) emH caseEq caseNeq
      in impI_W (existsCond consL, goalC) (Thm.implies_intr (ctermW hexP) conc) end
    val step1 = Thm.forall_intr (ctermW hF)
                  (Thm.forall_intr (ctermW tF) (Thm.implies_intr (ctermW ihP) step))
    val full = list_induct_W (Pabs, LF) base step1
  in varify full end;
val () = if length (Thm.hyps_of fsearch_found) = 0 then out "OK fsearch_found\n" else out "FAIL fsearch_found\n";

val () = out "WI_FSEARCH_FOUND_DONE\n";

(* ============================================================================
   cong intro combinators on ctxtW + a few order helpers.
   ============================================================================ *)
fun cong_introL_W (m,a,b,w) hyp =
  let val Pabs = Abs("k", natT, oeq b (add a (mult m (Bound 0))))
      val ex = exI_W Pabs w hyp
  in disjI1_W (congL m a b, congR m a b) ex end;
fun cong_introR_W (m,a,b,w) hyp =
  let val Pabs = Abs("k", natT, oeq a (add b (mult m (Bound 0))))
      val ex = exI_W Pabs w hyp
  in disjI2_W (congL m a b, congR m a b) ex end;

(* pos_pred : lt 1 p ==> Ex q. oeq p (Suc q) *)
val pos_pred =
  let
    val pF = Free("p", natT)
    val hp1P = jT (lt (suc ZeroC) pF) ; val hp1 = Thm.assume (ctermW hp1P)
    val goalC = mkExSuc_W pF
    val Pd = Abs("d", natT, oeq pF (add (suc (suc ZeroC)) (Bound 0)))
    fun body d (hd:thm) =
      let
        val aS = addSuc_W (suc ZeroC, d)
        val p_suc = oeq_trans_vW OF [hd, aS]
        val Pq = Abs("q", natT, oeq pF (suc (Bound 0)))
        val ex = exI_W Pq (add (suc ZeroC) d) p_suc
      in ex end
    val res = exE_W (Pd, goalC) hp1 "d_pp" body
  in varify (Thm.implies_intr (ctermW hp1P) res) end;
val () = if length (Thm.hyps_of pos_pred) = 0 then out "OK pos_pred\n" else out "FAIL pos_pred\n";

(* sub_lt_self : oeq p (Suc q) ==> lt (sub p (Suc Zero)) p *)
val sub_lt_self =
  let
    val pF = Free("p", natT); val qF = Free("q", natT)
    val hpqP = jT (oeq pF (suc qF)) ; val hpq = Thm.assume (ctermW hpqP)
    val Psub = Term.lambda (Free("z_su", natT)) (oeq (sub (Free("z_su", natT)) (suc ZeroC)) qF)
    val e1 = subSS_W (qF, ZeroC)
    val e2 = sub0_W qF
    val subSucq = oeq_trans_vW OF [e1, e2]
    val hpq_s = oeq_sym_vW OF [hpq]
    val subP = oeq_rw_W (Psub, suc qF, pF) hpq_s subSucq
    val lt_q_Sq = lt_suc_W qF
    val Plt = Term.lambda (Free("z_lt2", natT)) (lt qF (Free("z_lt2", natT)))
    val lt_q_p = oeq_rw_W (Plt, suc qF, pF) hpq_s lt_q_Sq
    val subP_s = oeq_sym_vW OF [subP]
    val Plt2 = Term.lambda (Free("z_lt3", natT)) (lt (Free("z_lt3", natT)) pF)
    val res = oeq_rw_W (Plt2, qF, sub pF (suc ZeroC)) subP_s lt_q_p
    val d1 = Thm.implies_intr (ctermW hpqP) res
  in varify d1 end;
val () = if length (Thm.hyps_of sub_lt_self) = 0 then out "OK sub_lt_self\n" else out "FAIL sub_lt_self\n";

val () = out "WI_ORDER_HELPERS_DONE\n";

(* ============================================================================
   not_dvd_in_range : 1 < p ==> lmem x (upto (sub p 1)) ==> ~(dvd p x)
   ============================================================================ *)
val not_dvd_in_range =
  let
    val pF = Free("p", natT); val xF = Free("x", natT)
    val hp1P = jT (lt (suc ZeroC) pF) ; val hp1 = Thm.assume (ctermW hp1P)
    val hmemP = jT (lmem xF (uptoF (sub pF (suc ZeroC)))) ; val hmem = Thm.assume (ctermW hmemP)
    val cj = lmem_upto_fwd_W (xF, sub pF (suc ZeroC)) hmem
    val hx0 = conjunct1_W (lt ZeroC xF, le xF (sub pF (suc ZeroC))) cj
    val hxle= conjunct2_W (lt ZeroC xF, le xF (sub pF (suc ZeroC))) cj
    val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pF)] pos_pred)) hp1
    val goalC = neg (dvd pF xF)
    fun predBody q (hq:thm) =
      let
        val subLt = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
                      [(("p",0), ctermW pF),(("q",0), ctermW q)] sub_lt_self)) hq
        val subp1 = sub pF (suc ZeroC)
        val Pd = Abs("d", natT, oeq subp1 (add xF (Bound 0)))
        fun leSucBody d (hd:thm) =
          let val sc = Suc_cong_vW OF [hd]
              val sx = addSuc_W (xF, d)
              val sxs= oeq_sym_vW OF [sx]
              val fin= oeq_trans_vW OF [sc, sxs]
          in le_intro_W (suc xF, suc subp1, d) fin end
        val leSucSuc = exE_W (Pd, le (suc xF) (suc subp1)) hxle "d_lr" leSucBody
        val ltxp = le_trans_W (suc xF, suc subp1, pF) leSucSuc subLt
        val notDvd =
          let
            val hdvd = Thm.assume (ctermW (jT (dvd pF xF)))
            val xnz =
              let val hz = Thm.assume (ctermW (jT (oeq xF ZeroC)))
                  val Plez = Term.lambda (Free("z_xz", natT)) (le (suc ZeroC) (Free("z_xz", natT)))
                  val le10 = oeq_rw_W (Plez, xF, ZeroC) hz hx0
                  val fls = lt_irrefl_W ZeroC le10
              in Thm.implies_intr (ctermW (jT (oeq xF ZeroC))) fls end
            val lepx = dvd_le_W (pF, xF) hdvd xnz
            val leSxx = le_trans_W (suc xF, pF, xF) ltxp lepx
            val fls = lt_irrefl_W xF leSxx
          in Thm.implies_intr (ctermW (jT (dvd pF xF))) fls end
      in impI_W (dvd pF xF, oFalseC) notDvd end
    val res = exE_W (Abs("q", natT, oeq pF (suc (Bound 0))), goalC) predEx "q_dr" predBody
    val d2 = Thm.implies_intr (ctermW hmemP) res
    val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of not_dvd_in_range) = 0 then out "OK not_dvd_in_range\n" else out "FAIL not_dvd_in_range\n";

val () = out "WI_NOT_DVD_RANGE_DONE\n";

(* ============================================================================
   more order helpers + cong_self_rmod + range membership of remainder.
   ============================================================================ *)
val lt_suc_cases_vW = varify lt_suc_cases;
fun lt_suc_cases_W (mt,nt) hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt)] lt_suc_cases_vW)) hlt;
fun le_self_suc_W nt =
  let val aSr = addSr_W (nt, ZeroC)
      val a0r = add0r_W nt
      val sa0r = Suc_cong_vW OF [a0r]
      val sum = oeq_trans_vW OF [aSr, sa0r]
      val sumS = oeq_sym_vW OF [sum]
  in le_intro_W (nt, suc nt, suc ZeroC) sumS end;
fun lt_imp_le_W (bt,qt) hlt =
  let val lebsb = le_self_suc_W bt
  in le_trans_W (bt, suc bt, qt) lebsb hlt end;
fun lt_suc_imp_le_W (bt,qt) hlt =
  let val dj = lt_suc_cases_W (bt, qt) hlt
      val cA = let val h = Thm.assume (ctermW (jT (lt bt qt)))
                   val r = lt_imp_le_W (bt, qt) h
               in Thm.implies_intr (ctermW (jT (lt bt qt))) r end
      val cB = let val h = Thm.assume (ctermW (jT (oeq bt qt)))
                   val Ple = Term.lambda (Free("z_lq", natT)) (le bt (Free("z_lq", natT)))
                   val r = oeq_rw_W (Ple, bt, qt) h (le_refl_W bt)
               in Thm.implies_intr (ctermW (jT (oeq bt qt))) r end
  in disjE_W (lt bt qt, oeq bt qt, le bt qt) dj cA cB end;

val cong_self_rmod =
  let
    val pF = Free("p", natT); val aF = Free("a", natT)
    val hp0P = jT (lt ZeroC pF) ; val hp0 = Thm.assume (ctermW hp0P)
    val q = rdiv aF pF; val r = rmod aF pF
    val hEq = div_mod_eq_W (aF, pF) hp0
    val comm = addcomm_W (mult pF q, r)
    val aEq = oeq_trans_vW OF [hEq, comm]
    val congAR = cong_introR_W (pF, aF, r, q) aEq
  in varify (Thm.implies_intr (ctermW hp0P) congAR) end;
val () = if length (Thm.hyps_of cong_self_rmod) = 0 then out "OK cong_self_rmod\n" else out "FAIL cong_self_rmod\n";
fun cong_self_rmod_W (pt,at) hp0 =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt),(("a",0), ctermW at)] cong_self_rmod)) hp0;

val () = out "WI_CONG_SELF_RMOD_DONE\n";

(* ============================================================================
   mem_range_inverse_exists :
     prime2 p ==> lmem x (upto (sub p 1)) ==> Ex b. Conj (lmem b (upto (sub p 1)))(searchCond p x b)
   ============================================================================ *)
val mem_range_inverse_exists =
  let
    val pF = Free("p", natT); val xF = Free("x", natT)
    val one = suc ZeroC
    val subp1 = sub pF one
    val hPrimeP = jT (prime2 pF) ; val hPrime = Thm.assume (ctermW hPrimeP)
    val hmemP = jT (lmem xF (uptoF subp1)) ; val hmem = Thm.assume (ctermW hmemP)
    val hp1 = prime2_gt1_W pF hPrime
    val hp0 = lt1_imp_lt0_W pF hp1
    val ndvd =
      let val inst = beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pF),(("x",0), ctermW xF)] not_dvd_in_range)
      in Thm.implies_elim (Thm.implies_elim inst hp1) hmem end
    val miEx = mod_inverse_W (pF, xF) hPrime ndvd
    val goalC = mkEx (Term.lambda (Free("b_re", natT))
                  (mkConj (lmem (Free("b_re", natT)) (uptoF subp1)) (searchCond pF xF (Free("b_re", natT)))))
    val miAbs = mi_innerAbs_W (pF, xF)
    fun miBody b0 (hcg0:thm) =
      let
        val b = rmod b0 pF
        val congb0b = cong_self_rmod_W (pF, b0) hp0
        val creflx = cong_refl_W (pF, xF)
        val congXprod = cong_mult_W (pF, xF, xF, b0, b) creflx congb0b
        val congXprodS = cong_sym_W (pF, mult xF b0, mult xF b) congXprod
        val congXB1 = cong_trans_W (pF, mult xF b, mult xF b0, one) congXprodS hcg0
        val scb = cong_imp_scond_W (pF, xF, b) hp1 congXB1
        val bltp = rmod_lt_W (b0, pF) hp0
        val dzb = dzos_W b
        val hb0pos =
          let
            val caseZ = let val hbz = Thm.assume (ctermW (jT (oeq b ZeroC)))
                            val xbcong = mult_cong_r_W (xF, b, ZeroC) hbz
                            val x0 = mult0r_W xF
                            val xb0 = oeq_trans_vW OF [xbcong, x0]
                            val Pc = Term.lambda (Free("z_cz2", natT)) (cong pF (Free("z_cz2", natT)) one)
                            val cong01 = oeq_rw_W (Pc, mult xF b, ZeroC) xb0 congXB1
                            val caseL =
                              let val hL = Thm.assume (ctermW (jT (congL pF ZeroC one)))
                                  val Pk = Abs("k", natT, oeq one (add ZeroC (mult pF (Bound 0))))
                                  fun kb k (hk:thm) =
                                    let val z0 = add0_W (mult pF k)
                                        val one_pk = oeq_trans_vW OF [hk, z0]
                                        val dvdp1 = dvd_intro_W (pF, one, k) one_pk
                                        val onenz = let val h00 = Thm.assume (ctermW (jT (oeq one ZeroC)))
                                                    in Thm.implies_intr (ctermW (jT (oeq one ZeroC))) (Suc_neq_Zero_W ZeroC h00) end
                                        val lep1 = dvd_le_W (pF, one) dvdp1 onenz
                                        val le21 = le_trans_W (suc one, pF, one) hp1 lep1
                                    in lt_irrefl_W one le21 end
                                  val r = exE_W (Pk, oFalseC) hL "k_cl2" kb
                              in Thm.implies_intr (ctermW (jT (congL pF ZeroC one))) r end
                            val caseR =
                              let val hR = Thm.assume (ctermW (jT (congR pF ZeroC one)))
                                  val Pk = Abs("k", natT, oeq ZeroC (add one (mult pF (Bound 0))))
                                  fun kb k (hk:thm) =
                                    let val aS = addSuc_W (ZeroC, mult pF k)
                                        val zSuc = oeq_trans_vW OF [hk, aS]
                                        val sucz = oeq_sym_vW OF [zSuc]
                                    in Suc_neq_Zero_W (add ZeroC (mult pF k)) sucz end
                                  val r = exE_W (Pk, oFalseC) hR "k_cr2" kb
                              in Thm.implies_intr (ctermW (jT (congR pF ZeroC one))) r end
                            val fls = disjE_W (congL pF ZeroC one, congR pF ZeroC one, oFalseC) cong01 caseL caseR
                            val ltb = Thm.implies_elim (oFalse_elim_W (lt ZeroC b)) fls
                        in Thm.implies_intr (ctermW (jT (oeq b ZeroC))) ltb end
            val caseS = let val hsP = jT (mkExSuc_W b)
                            val hs = Thm.assume (ctermW hsP)
                            val Pq = Abs("q", natT, oeq b (suc (Bound 0)))
                            fun sb k (hk:thm) =
                              let
                                  val lt0Sk =
                                    let val a1 = addSuc_W (ZeroC, k)
                                        val a0 = add0_W k
                                        val sa0= Suc_cong_vW OF [a0]
                                        val sum= oeq_trans_vW OF [a1, sa0]
                                        val sumS = oeq_sym_vW OF [sum]
                                    in le_intro_W (suc ZeroC, suc k, k) sumS end
                                  val hk_s = oeq_sym_vW OF [hk]
                                  val Plt = Term.lambda (Free("z_p0", natT)) (lt ZeroC (Free("z_p0", natT)))
                              in oeq_rw_W (Plt, suc k, b) hk_s lt0Sk end
                            val r = exE_W (Pq, lt ZeroC b) hs "k_bs" sb
                        in Thm.implies_intr (ctermW (jT (mkExSuc_W b))) r end
          in disjE_W (oeq b ZeroC, mkExSuc_W b, lt ZeroC b) dzb caseZ caseS end
        val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pF)] pos_pred)) hp1
        fun predBody q (hq:thm) =
          let
            val Plt = Term.lambda (Free("z_bp", natT)) (lt b (Free("z_bp", natT)))
            val ltbSq = oeq_rw_W (Plt, pF, suc q) hq bltp
            val lebq = lt_suc_imp_le_W (b, q) ltbSq
            val e1 = subSS_W (q, ZeroC)
            val e2 = sub0_W q
            val subSucq = oeq_trans_vW OF [e1, e2]
            val hq_s = oeq_sym_vW OF [hq]
            val Psub = Term.lambda (Free("z_sb2", natT)) (oeq (sub (Free("z_sb2", natT)) one) q)
            val subP = oeq_rw_W (Psub, suc q, pF) hq_s subSucq
            val subP_s = oeq_sym_vW OF [subP]
            val Ple = Term.lambda (Free("z_le2", natT)) (le b (Free("z_le2", natT)))
            val lebsub = oeq_rw_W (Ple, q, subp1) subP_s lebq
            val cj = conjI_W (lt ZeroC b, le b subp1) hb0pos lebsub
            val memB = lmem_upto_bwd_W (b, subp1) cj
            val resCj = conjI_W (lmem b (uptoF subp1), searchCond pF xF b) memB scb
            val PgoalAbs = Term.lambda (Free("b_re", natT))
                  (mkConj (lmem (Free("b_re", natT)) (uptoF subp1)) (searchCond pF xF (Free("b_re", natT))))
            val ex = exI_W PgoalAbs b resCj
          in ex end
        val res = exE_W (Abs("q", natT, oeq pF (suc (Bound 0))), goalC) predEx "q_mr" predBody
      in res end
    val res = exE_W (miAbs, goalC) miEx "b0_mi" miBody
    val d2 = Thm.implies_intr (ctermW hmemP) res
    val d1 = Thm.implies_intr (ctermW hPrimeP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of mem_range_inverse_exists) = 0 then out "OK mem_range_inverse_exists\n" else out "FAIL mem_range_inverse_exists\n";

val () = out "WI_MEM_RANGE_INV_EXISTS_DONE\n";

(* accessor : fsearch_found applied at (p,x,L) to an existence proof. *)
fun fsearch_found_W (pt,xt,Lt) hex =
  let
    val existsAbs = Term.lambda (Free("b_fe", natT))
                      (mkConj (lmem (Free("b_fe", natT)) Lt) (searchCond pt xt (Free("b_fe", natT))))
    val existsT = mkEx existsAbs
    val goodT = mkConj (searchCond pt xt (fsearch pt xt Lt)) (lmem (fsearch pt xt Lt) Lt)
    val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("x",0), ctermW xt),(("L",0), ctermW Lt)] fsearch_found)
  in mp_W (existsT, goodT) inst hex end;

val () = out "WI_FSEARCH_FOUND_ACCESSOR_DONE\n";

fun mem_range_inverse_exists_W (pt,xt) hPrime hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("x",0), ctermW xt)] mem_range_inverse_exists)
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hmem end;

(* ============================================================================
   TARGET 1 : finv_inv : prime2 p ==> lmem x (upto (sub p 1)) ==> cong p (mult x (finv p x)) 1
   ============================================================================ *)
val finv_inv =
  let
    val pF = Free("p", natT); val xF = Free("x", natT)
    val one = suc ZeroC ; val subp1 = sub pF one ; val rng = uptoF subp1
    val hPrimeP = jT (prime2 pF) ; val hPrime = Thm.assume (ctermW hPrimeP)
    val hmemP = jT (lmem xF rng) ; val hmem = Thm.assume (ctermW hmemP)
    val hp1 = prime2_gt1_W pF hPrime
    val hex = mem_range_inverse_exists_W (pF, xF) hPrime hmem
    val good = fsearch_found_W (pF, xF, rng) hex
    val scFs = conjunct1_W (searchCond pF xF (fsearch pF xF rng), lmem (fsearch pF xF rng) rng) good
    val congFs = scond_imp_cong_W (pF, xF, fsearch pF xF rng) hp1 scFs
    val fdef = finvDef_W (pF, xF)
    val fdef_s = oeq_sym_vW OF [fdef]
    val Pc = Term.lambda (Free("z_fi", natT)) (cong pF (mult xF (Free("z_fi", natT))) one)
    val res = oeq_rw_W (Pc, fsearch pF xF rng, finv pF xF) fdef_s congFs
    val d2 = Thm.implies_intr (ctermW hmemP) res
    val d1 = Thm.implies_intr (ctermW hPrimeP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of finv_inv) = 0 then out "OK finv_inv\n" else out "FAIL finv_inv\n";

(* ============================================================================
   TARGET 2 : finv_mem : prime2 p ==> lmem x (upto (sub p 1)) ==> lmem (finv p x) (upto (sub p 1))
   ============================================================================ *)
val finv_mem =
  let
    val pF = Free("p", natT); val xF = Free("x", natT)
    val one = suc ZeroC ; val subp1 = sub pF one ; val rng = uptoF subp1
    val hPrimeP = jT (prime2 pF) ; val hPrime = Thm.assume (ctermW hPrimeP)
    val hmemP = jT (lmem xF rng) ; val hmem = Thm.assume (ctermW hmemP)
    val hex = mem_range_inverse_exists_W (pF, xF) hPrime hmem
    val good = fsearch_found_W (pF, xF, rng) hex
    val memFs = conjunct2_W (searchCond pF xF (fsearch pF xF rng), lmem (fsearch pF xF rng) rng) good
    val fdef = finvDef_W (pF, xF)
    val fdef_s = oeq_sym_vW OF [fdef]
    val Pm = Term.lambda (Free("z_fm", natT)) (lmem (Free("z_fm", natT)) rng)
    val res = oeq_rw_W (Pm, fsearch pF xF rng, finv pF xF) fdef_s memFs
    val d2 = Thm.implies_intr (ctermW hmemP) res
    val d1 = Thm.implies_intr (ctermW hPrimeP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of finv_mem) = 0 then out "OK finv_mem\n" else out "FAIL finv_mem\n";

val () = out "WI_FINV_INV_MEM_DONE\n";

(* ============================================================================
   lmem_range_lt : 1 < p ==> lmem x (upto (sub p 1)) ==> lt x p
   ============================================================================ *)
val lmem_range_lt =
  let
    val pF = Free("p", natT); val xF = Free("x", natT)
    val one = suc ZeroC ; val subp1 = sub pF one
    val hp1P = jT (lt one pF) ; val hp1 = Thm.assume (ctermW hp1P)
    val hmemP = jT (lmem xF (uptoF subp1)) ; val hmem = Thm.assume (ctermW hmemP)
    val cj = lmem_upto_fwd_W (xF, subp1) hmem
    val hxle = conjunct2_W (lt ZeroC xF, le xF subp1) cj
    val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pF)] pos_pred)) hp1
    val goalC = lt xF pF
    fun predBody q (hq:thm) =
      let
        val subLt = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
                      [(("p",0), ctermW pF),(("q",0), ctermW q)] sub_lt_self)) hq
        val Pd = Abs("d", natT, oeq subp1 (add xF (Bound 0)))
        fun leSucBody d (hd:thm) =
          let val sc = Suc_cong_vW OF [hd]
              val sx = addSuc_W (xF, d)
              val sxs= oeq_sym_vW OF [sx]
              val fin= oeq_trans_vW OF [sc, sxs]
          in le_intro_W (suc xF, suc subp1, d) fin end
        val leSucSuc = exE_W (Pd, le (suc xF) (suc subp1)) hxle "d_lrl" leSucBody
        val ltxp = le_trans_W (suc xF, suc subp1, pF) leSucSuc subLt
      in ltxp end
    val res = exE_W (Abs("q", natT, oeq pF (suc (Bound 0))), goalC) predEx "q_lrl" predBody
    val d2 = Thm.implies_intr (ctermW hmemP) res
    val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of lmem_range_lt) = 0 then out "OK lmem_range_lt\n" else out "FAIL lmem_range_lt\n";
fun lmem_range_lt_W (pt,xt) hp1 hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pt),(("x",0), ctermW xt)] lmem_range_lt)
  in Thm.implies_elim (Thm.implies_elim inst hp1) hmem end;

(* rmod_id : 0 < p ==> lt a p ==> oeq (rmod a p) a *)
val rmod_id =
  let
    val pF = Free("p", natT); val aF = Free("a", natT)
    val hp0P = jT (lt ZeroC pF) ; val hp0 = Thm.assume (ctermW hp0P)
    val haltP = jT (lt aF pF) ; val halt = Thm.assume (ctermW haltP)
    val q1 = rdiv aF pF ; val r1 = rmod aF pF
    val hEq = div_mod_eq_W (aF, pF) hp0
    val hr1lt = rmod_lt_W (aF, pF) hp0
    val p0 = mult0r_W pF
    val pol = add_cong_l_W (mult pF ZeroC, ZeroC, aF) p0
    val z1 = add0_W aF
    val eq2 = oeq_trans_vW OF [pol, z1]
    val eqWit = oeq_sym_vW OF [eq2]
    val combined = oeq_trans_vW OF [oeq_sym_vW OF [hEq], eqWit]
    val uniq = div_mod_unique_W (pF, q1, r1, ZeroC, aF) combined hr1lt halt
    val r1a = conjunct2_W (oeq q1 ZeroC, oeq r1 aF) uniq
    val d2 = Thm.implies_intr (ctermW haltP) r1a
    val d1 = Thm.implies_intr (ctermW hp0P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of rmod_id) = 0 then out "OK rmod_id\n" else out "FAIL rmod_id\n";
fun rmod_id_W (pt,at) hp0 halt =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pt),(("a",0), ctermW at)] rmod_id)
  in Thm.implies_elim (Thm.implies_elim inst hp0) halt end;

(* cong_range_unique : 1 < p ==> lt a p ==> lt b p ==> cong p a b ==> oeq a b *)
val cong_range_unique =
  let
    val pF = Free("p", natT); val aF = Free("a", natT); val bF = Free("b", natT)
    val one = suc ZeroC
    val hp1P = jT (lt one pF) ; val hp1 = Thm.assume (ctermW hp1P)
    val haltP = jT (lt aF pF) ; val halt = Thm.assume (ctermW haltP)
    val hbltP = jT (lt bF pF) ; val hblt = Thm.assume (ctermW hbltP)
    val hcgP = jT (cong pF aF bF) ; val hcg = Thm.assume (ctermW hcgP)
    val hp0 = lt1_imp_lt0_W pF hp1
    val req = cong_imp_rmodeq_W (pF, aF, bF) hp0 hcg
    val ria = rmod_id_W (pF, aF) hp0 halt
    val rib = rmod_id_W (pF, bF) hp0 hblt
    val a_rmodb = oeq_trans_vW OF [oeq_sym_vW OF [ria], req]
    val a_b = oeq_trans_vW OF [a_rmodb, rib]
    val d4 = Thm.implies_intr (ctermW hcgP) a_b
    val d3 = Thm.implies_intr (ctermW hbltP) d4
    val d2 = Thm.implies_intr (ctermW haltP) d3
    val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of cong_range_unique) = 0 then out "OK cong_range_unique\n" else out "FAIL cong_range_unique\n";
fun cong_range_unique_W (pt,at,bt) hp1 halt hblt hcg =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("a",0), ctermW at),(("b",0), ctermW bt)] cong_range_unique)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hp1) halt) hblt) hcg end;

val () = out "WI_RANGE_UNIQUE_DONE\n";

fun finv_inv_W (pt,xt) hPrime hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pt),(("x",0), ctermW xt)] finv_inv)
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hmem end;
fun finv_mem_W (pt,xt) hPrime hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pt),(("x",0), ctermW xt)] finv_mem)
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hmem end;

(* ============================================================================
   TARGET 3 : finv_invol : prime2 p ==> lmem x (upto (sub p 1)) ==> oeq (finv p (finv p x)) x
   ============================================================================ *)
val finv_invol =
  let
    val pF = Free("p", natT); val xF = Free("x", natT)
    val one = suc ZeroC ; val subp1 = sub pF one ; val rng = uptoF subp1
    val hPrimeP = jT (prime2 pF) ; val hPrime = Thm.assume (ctermW hPrimeP)
    val hmemP = jT (lmem xF rng) ; val hmem = Thm.assume (ctermW hmemP)
    val hp1 = prime2_gt1_W pF hPrime
    val y = finv pF xF
    val cong_xy_1 = finv_inv_W (pF, xF) hPrime hmem
    val memY = finv_mem_W (pF, xF) hPrime hmem
    val cong_y_fyinv_1 = finv_inv_W (pF, y) hPrime memY
    val memFy = finv_mem_W (pF, y) hPrime memY
    val comm_xy = multcomm_W (xF, y)
    val Pc = Term.lambda (Free("z_iv", natT)) (cong pF (Free("z_iv", natT)) one)
    val cong_yx_1 = oeq_rw_W (Pc, mult xF y, mult y xF) comm_xy cong_xy_1
    val cong_fy_x = inverse_unique_W (pF, y, finv pF y, xF) cong_y_fyinv_1 cong_yx_1
    val lt_fy = lmem_range_lt_W (pF, finv pF y) hp1 memFy
    val lt_x  = lmem_range_lt_W (pF, xF) hp1 hmem
    val res = cong_range_unique_W (pF, finv pF y, xF) hp1 lt_fy lt_x cong_fy_x
    val d2 = Thm.implies_intr (ctermW hmemP) res
    val d1 = Thm.implies_intr (ctermW hPrimeP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of finv_invol) = 0 then out "OK finv_invol\n" else out "FAIL finv_invol\n";

val () = out "WI_FINV_INVOL_DONE\n";

(* le_cases_W : le a b ==> Disj (oeq a b)(lt a b) *)
val le_cases =
  let
    val aF = Free("a", natT); val bF = Free("b", natT)
    val hleP = jT (le aF bF) ; val hle = Thm.assume (ctermW hleP)
    val goalC = mkDisj (oeq aF bF) (lt aF bF)
    val Pd = Abs("d", natT, oeq bF (add aF (Bound 0)))
    fun body d (hd:thm) =
      let
        val dz = dzos_W d
        val caseZ = let val hz = Thm.assume (ctermW (jT (oeq d ZeroC)))
                        val c1 = add_cong_r_W (aF, d, ZeroC) hz
                        val a0 = add0r_W aF
                        val c2 = oeq_trans_vW OF [c1, a0]
                        val b_a = oeq_trans_vW OF [hd, c2]
                        val a_b = oeq_sym_vW OF [b_a]
                    in Thm.implies_intr (ctermW (jT (oeq d ZeroC))) (disjI1_W (oeq aF bF, lt aF bF) a_b) end
        val caseS = let val hsP = jT (mkExSuc_W d)
                        val hs = Thm.assume (ctermW hsP)
                        val Pq = Abs("q", natT, oeq d (suc (Bound 0)))
                        fun sb e (he:thm) =
                          let val c1 = add_cong_r_W (aF, d, suc e) he
                              val b_aSe = oeq_trans_vW OF [hd, c1]
                              val aSe = addSr_W (aF, e)
                              val b_Sae = oeq_trans_vW OF [b_aSe, aSe]
                              val saS = addSuc_W (aF, e)
                              val saS_s = oeq_sym_vW OF [saS]
                              val b_Sae2 = oeq_trans_vW OF [b_Sae, saS_s]
                              val ltab = le_intro_W (suc aF, bF, e) b_Sae2
                          in disjI2_W (oeq aF bF, lt aF bF) ltab end
                        val r = exE_W (Pq, goalC) hs "e_lc" sb
                    in Thm.implies_intr (ctermW (jT (mkExSuc_W d))) r end
      in disjE_W (oeq d ZeroC, mkExSuc_W d, goalC) dz caseZ caseS end
    val res = exE_W (Pd, goalC) hle "d_lc" body
  in varify (Thm.implies_intr (ctermW hleP) res) end;
val () = if length (Thm.hyps_of le_cases) = 0 then out "OK le_cases\n" else out "FAIL le_cases\n";
fun le_cases_W (at,bt) hle =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("a",0), ctermW at),(("b",0), ctermW bt)] le_cases)) hle;

(* ============================================================================
   TARGET 4 : finv_neq :
     prime2 p ==> lmem x (upto (sub p 1)) ==> ~(oeq x 1) ==> ~(oeq x (sub p 1))
       ==> ~(oeq (finv p x) x)         [x in [2..p-2]]
   ============================================================================ *)
val finv_neq =
  let
    val pF = Free("p", natT); val xF = Free("x", natT)
    val one = suc ZeroC ; val subp1 = sub pF one ; val rng = uptoF subp1
    val hPrimeP = jT (prime2 pF) ; val hPrime = Thm.assume (ctermW hPrimeP)
    val hmemP = jT (lmem xF rng) ; val hmem = Thm.assume (ctermW hmemP)
    val hne1P = jT (neg (oeq xF one)) ; val hne1 = Thm.assume (ctermW hne1P)
    val hneqP = jT (neg (oeq xF subp1)) ; val hneq = Thm.assume (ctermW hneqP)
    val hp1 = prime2_gt1_W pF hPrime
    val hp0 = lt1_imp_lt0_W pF hp1
    val hfxP = jT (oeq (finv pF xF) xF) ; val hfx = Thm.assume (ctermW hfxP)
    val cong_xfx = finv_inv_W (pF, xF) hPrime hmem
    val Pc = Term.lambda (Free("z_fn", natT)) (cong pF (mult xF (Free("z_fn", natT))) one)
    val cong_xx = oeq_rw_W (Pc, finv pF xF, xF) hfx cong_xfx
    val lr = lagrange_roots_W (pF, xF) hPrime cong_xx
    val ltx = lmem_range_lt_W (pF, xF) hp1 hmem
    val caseA =
      let val hcg = Thm.assume (ctermW (jT (cong pF xF one)))
          val oxx1 = cong_range_unique_W (pF, xF, one) hp1 ltx hp1 hcg
          val fls = mp_W (oeq xF one, oFalseC) hne1 oxx1
      in Thm.implies_intr (ctermW (jT (cong pF xF one))) fls end
    val caseB =
      let
        val hcg = Thm.assume (ctermW (jT (cong pF (suc xF) ZeroC)))
        val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pF)] pos_pred)) hp1
        fun predBody q (hq:thm) =
          let
            val cjm = lmem_upto_fwd_W (xF, subp1) hmem
            val hxle = conjunct2_W (lt ZeroC xF, le xF subp1) cjm
            val e1 = subSS_W (q, ZeroC) ; val e2 = sub0_W q
            val subSucq = oeq_trans_vW OF [e1, e2]
            val hq_s = oeq_sym_vW OF [hq]
            val Psub = Term.lambda (Free("z_sb3", natT)) (oeq (sub (Free("z_sb3", natT)) one) q)
            val subPq = oeq_rw_W (Psub, suc q, pF) hq_s subSucq
            val Plex = Term.lambda (Free("z_lx", natT)) (le xF (Free("z_lx", natT)))
            val lexq = oeq_rw_W (Plex, subp1, q) subPq hxle
            val Pd = Abs("d", natT, oeq q (add xF (Bound 0)))
            fun leSucBody d (hd:thm) =
              let val sc = Suc_cong_vW OF [hd]
                  val sx = addSuc_W (xF, d)
                  val sxs= oeq_sym_vW OF [sx]
                  val fin= oeq_trans_vW OF [sc, sxs]
              in le_intro_W (suc xF, suc q, d) fin end
            val leSxSq = exE_W (Pd, le (suc xF) (suc q)) lexq "d_sn" leSucBody
            val hq_sB = oeq_sym_vW OF [hq]
            val Pleq = Term.lambda (Free("z_lp", natT)) (le (suc xF) (Free("z_lp", natT)))
            val leSxp = oeq_rw_W (Pleq, suc q, pF) hq_sB leSxSq
            val req = cong_imp_rmodeq_W (pF, suc xF, ZeroC) hp0 hcg
            val rmod0 = rmod_id_W (pF, ZeroC) hp0 hp0
            val rmodSx_0 = oeq_trans_vW OF [req, rmod0]
            val dj = le_cases_W (suc xF, pF) leSxp
            val subB1 =
              let val heqSxp = Thm.assume (ctermW (jT (oeq (suc xF) pF)))
                  val SxSq = oeq_trans_vW OF [heqSxp, hq]
                  val x_q = Suc_inj_W (xF, q) SxSq
                  val subPq_s = oeq_sym_vW OF [subPq]
                  val x_subp1 = oeq_trans_vW OF [x_q, subPq_s]
                  val fls = mp_W (oeq xF subp1, oFalseC) hneq x_subp1
              in Thm.implies_intr (ctermW (jT (oeq (suc xF) pF))) fls end
            val subB2 =
              let val hltSxp = Thm.assume (ctermW (jT (lt (suc xF) pF)))
                  val ridSx = rmod_id_W (pF, suc xF) hp0 hltSxp
                  val ridSx_s = oeq_sym_vW OF [ridSx]
                  val Sx_0 = oeq_trans_vW OF [ridSx_s, rmodSx_0]
                  val fls = Suc_neq_Zero_W xF Sx_0
              in Thm.implies_intr (ctermW (jT (lt (suc xF) pF))) fls end
            val fls = disjE_W (oeq (suc xF) pF, lt (suc xF) pF, oFalseC) dj subB1 subB2
          in fls end
        val fls = exE_W (Abs("q", natT, oeq pF (suc (Bound 0))), oFalseC) predEx "q_fn" predBody
      in Thm.implies_intr (ctermW (jT (cong pF (suc xF) ZeroC))) fls end
    val flsTop = disjE_W (cong pF xF one, cong pF (suc xF) ZeroC, oFalseC) lr caseA caseB
    val metaNeg = Thm.implies_intr (ctermW hfxP) flsTop
    val negThm = impI_W (oeq (finv pF xF) xF, oFalseC) metaNeg
    val d4 = Thm.implies_intr (ctermW hneqP) negThm
    val d3 = Thm.implies_intr (ctermW hne1P) d4
    val d2 = Thm.implies_intr (ctermW hmemP) d3
    val d1 = Thm.implies_intr (ctermW hPrimeP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of finv_neq) = 0 then out "OK finv_neq\n" else out "FAIL finv_neq\n";

val () = out "WI_FINV_NEQ_DONE\n";

(* ============================================================================
   PHASE 2 FINAL VALIDATION : aconv intent, 0-hyp, soundness probes.
   ============================================================================ *)
val () = out "WI_VALIDATE_BEGIN\n";
val pV = Var(("p",0),natT); val xV = Var(("x",0),natT);
val oneV = suc ZeroC; val subp1V = sub pV oneV; val rngV = uptoF subp1V;

val finv_inv_intended =
  Logic.mk_implies (jT (prime2 pV),
    Logic.mk_implies (jT (lmem xV rngV),
      jT (cong pV (mult xV (finv pV xV)) oneV)));
val r_fi = (length (Thm.hyps_of finv_inv) = 0) andalso ((Thm.prop_of finv_inv) aconv finv_inv_intended);
val () = if r_fi then out "OK finv_inv aconv intended\n" else out "FAIL finv_inv aconv\n";

val finv_mem_intended =
  Logic.mk_implies (jT (prime2 pV),
    Logic.mk_implies (jT (lmem xV rngV),
      jT (lmem (finv pV xV) rngV)));
val r_fm = (length (Thm.hyps_of finv_mem) = 0) andalso ((Thm.prop_of finv_mem) aconv finv_mem_intended);
val () = if r_fm then out "OK finv_mem aconv intended\n" else out "FAIL finv_mem aconv\n";

val finv_invol_intended =
  Logic.mk_implies (jT (prime2 pV),
    Logic.mk_implies (jT (lmem xV rngV),
      jT (oeq (finv pV (finv pV xV)) xV)));
val r_fv = (length (Thm.hyps_of finv_invol) = 0) andalso ((Thm.prop_of finv_invol) aconv finv_invol_intended);
val () = if r_fv then out "OK finv_invol aconv intended\n" else out "FAIL finv_invol aconv\n";

val finv_neq_intended =
  Logic.mk_implies (jT (prime2 pV),
    Logic.mk_implies (jT (lmem xV rngV),
      Logic.mk_implies (jT (neg (oeq xV oneV)),
        Logic.mk_implies (jT (neg (oeq xV subp1V)),
          jT (neg (oeq (finv pV xV) xV))))));
val r_fn = (length (Thm.hyps_of finv_neq) = 0) andalso ((Thm.prop_of finv_neq) aconv finv_neq_intended);
val () = if r_fn then out "OK finv_neq aconv intended\n" else out "FAIL finv_neq aconv\n";

val probe_fi =
  let val bogus = Logic.mk_implies (jT (prime2 pV), jT (cong pV (mult xV (finv pV xV)) oneV))
  in not ((Thm.prop_of finv_inv) aconv bogus) end;
val () = if probe_fi then out "PROBE_OK finv_inv keeps lmem x rng\n" else out "PROBE_FAIL finv_inv\n";

val probe_fv =
  let val bogus = Logic.mk_implies (jT (prime2 pV), jT (oeq (finv pV (finv pV xV)) xV))
  in not ((Thm.prop_of finv_invol) aconv bogus) end;
val () = if probe_fv then out "PROBE_OK finv_invol keeps lmem x rng\n" else out "PROBE_FAIL finv_invol\n";

val probe_fn_drop1 =
  let val bogus = Logic.mk_implies (jT (prime2 pV),
        Logic.mk_implies (jT (lmem xV rngV),
          Logic.mk_implies (jT (neg (oeq xV subp1V)), jT (neg (oeq (finv pV xV) xV)))))
  in not ((Thm.prop_of finv_neq) aconv bogus) end;
val probe_fn_dropP =
  let val bogus = Logic.mk_implies (jT (prime2 pV),
        Logic.mk_implies (jT (lmem xV rngV),
          Logic.mk_implies (jT (neg (oeq xV oneV)), jT (neg (oeq (finv pV xV) xV)))))
  in not ((Thm.prop_of finv_neq) aconv bogus) end;
val () = if probe_fn_drop1 andalso probe_fn_dropP then out "PROBE_OK finv_neq keeps both x<>1 and x<>p-1\n" else out "PROBE_FAIL finv_neq\n";

val () =
  if r_fi andalso r_fm andalso r_fv andalso r_fn
     andalso probe_fi andalso probe_fv andalso probe_fn_drop1 andalso probe_fn_dropP
  then out "INVERSE_FN_OK\n"
  else out "INVERSE_FN_FAILED\n";
