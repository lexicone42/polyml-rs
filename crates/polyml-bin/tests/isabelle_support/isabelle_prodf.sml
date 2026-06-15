(* ============================================================================
   THE FINITE-PRODUCT COMBINATOR prodf in Isabelle/Pure on the polyml-rs interp.
   (test: isabelle_prodf.rs)
   ----------------------------------------------------------------------------
   prodf is the multiplicative mirror of the higher-order finite sum sumf:
   a NEW higher-order constant prodf : (nat=>nat)=>nat=>nat defined (conservatively,
   via two asserted recursion axioms, exactly as sumf/fact/pow are) by

     prodf f 0 = f 0 ;   prodf f (Suc n) = (prodf f n) * (f (Suc n))

   (so prodf f n = f 0 * f 1 * ... * f n), with its core algebra proved by genuine
   LCF kernel induction, each 0-hypothesis:

     prod_cong         : (!!k. k <= n ==> f k = g k) ==> prodf f n = prodf g n
     prod_const_pow    : prodf (%k. c) n = pow c (Suc n)          (constant product = power)
     prod_mult_combine : (prodf f n) * (prodf g n) = prodf (%k. f k * g k) n

   This is the one structural piece the tower lacked toward Wilson's theorem and
   Euler's theorem (both reduce to a finite product over a residue range). Adding
   the const EXTENDS the theory, so the development builds ONE final context and
   re-varifies every reused base lemma onto it (the standard new-const discipline).
   prod_const_pow has a soundness probe (the kernel rejects the wrong exponent).

   Built on the finite-sum / binomial development (isabelle_binom_thm.sml, the
   sumf template) over the classical foundation, spliced in by with_binom_thm.
   Proved by a 3-seat ultracode fleet (wf_66aae28d-292); re-verified by hand.
   ============================================================================ *)

(* ============================================================================
   PRODF SEAT prodf0  —  the multiplicative mirror of sumf.
   Extend thySub with a NEW const  prodf : (nat=>nat)=>nat=>nat
   with recursion axioms prodf_0 / prodf_Suc, then prove
     prod_cong, prod_const_pow, prod_mult_combine.
   FINAL CONTEXT : ctxtPr / ctermPr (theory thyPr : prodf on top of thySub).
   Route ALL cterms through ctermPr; re-varify EVERY reused base lemma.
   ============================================================================ *)
val () = out "PRODF_BEGIN\n";

(* ---- ONE theory extension with the new const ---- *)
val thyPr0 = Sign.add_consts
  [(Binding.name "prodf", fnT --> natT --> natT, NoSyn)] thySub;
val prodfC = Const (Sign.full_name thyPr0 (Binding.name "prodf"), fnT --> natT --> natT);
fun prodf f n = prodfC $ f $ n;

(* ---- recursion axioms (conservative definition) ---- *)
val fPr = Free("f", fnT);
val nPr = Free("n", natT);
val ((_,prodf_0_ax),  thyPr1) = Thm.add_axiom_global (Binding.name "prodf_0",
      jT (oeq (prodf fPr ZeroC) (fPr $ ZeroC))) thyPr0;
val ((_,prodf_Suc_ax), thyPr) = Thm.add_axiom_global (Binding.name "prodf_Suc",
      jT (oeq (prodf fPr (suc nPr)) (mult (prodf fPr nPr) (fPr $ (suc nPr))))) thyPr1;

(* ---- THE ONE FINAL CONTEXT ctxtPr / ctermPr ---- *)
val ctxtPr  = Proof_Context.init_global thyPr;
val ctermPr = Thm.cterm_of ctxtPr;

(* ---- re-varify every reused axiom/lemma onto ctxtPr ---- *)
val oeq_refl_vP2     = varify oeq_refl;
val oeq_subst_vP2    = varify oeq_subst;
val nat_induct_vP2   = varify nat_induct;
val mult_comm_vP2    = varify mult_comm;     (* oeq (mult ?m ?n) (mult ?n ?m) *)
val mult_assoc_vP2   = varify mult_assoc;    (* oeq (mult (mult ?m ?n) ?k) (mult ?m (mult ?n ?k)) *)
val mult_1_right_vP2 = varify mult_1_right;  (* oeq (mult ?n (Suc 0)) ?n *)
val mult_Suc_vP2     = varify mult_Suc;      (* oeq (mult (Suc ?m) ?n) (add ?n (mult ?m ?n)) *)
val pow_Zero_vP2     = varify pow_Zero_ax;   (* oeq (pow ?a 0) (Suc 0) *)
val pow_Suc_vP2      = varify pow_Suc_ax;    (* oeq (pow ?a (Suc ?n)) (mult ?a (pow ?a ?n)) *)
val add_0_right_vP2  = varify add_0_right;
val add_Suc_right_vP2= varify add_Suc_right;
val exI_vP2          = varify exI_ax;
val le_refl_vP2      = varify le_refl;
val le_trans_vP2     = varify le_trans;
val impI_vP2         = varify impI_ax;
val mp_vP2           = varify mp_ax;
val allI_vP2         = varify allI_ax;
val allE_vP2         = varify allE_ax;
val prodf_0_vP2      = varify prodf_0_ax;
val prodf_Suc_vP2    = varify prodf_Suc_ax;

(* ---- ground instantiators on ctxtPr ---- *)
fun oeqreflP_at t   = beta_norm (Drule.infer_instantiate ctxtPr [(("a",0), ctermPr t)] oeq_refl_vP2);
fun add0rP_at t     = beta_norm (Drule.infer_instantiate ctxtPr [(("n",0), ctermPr t)] add_0_right_vP2);
fun addSrP_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtPr
                            [(("m",0), ctermPr mt),(("n",0), ctermPr nt)] add_Suc_right_vP2);

fun mult_comm_atP (mt,nt)     = beta_norm (Drule.infer_instantiate ctxtPr
        [(("m",0), ctermPr mt),(("n",0), ctermPr nt)] mult_comm_vP2);
fun mult_assoc_atP (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtPr
        [(("m",0), ctermPr mt),(("n",0), ctermPr nt),(("k",0), ctermPr kt)] mult_assoc_vP2);
fun mult1rP_at t              = beta_norm (Drule.infer_instantiate ctxtPr
        [(("n",0), ctermPr t)] mult_1_right_vP2);

fun powZeroP2_at t      = beta_norm (Drule.infer_instantiate ctxtPr [(("a",0), ctermPr t)] pow_Zero_vP2);
fun powSucP2_at (at,nt) = beta_norm (Drule.infer_instantiate ctxtPr
                            [(("a",0), ctermPr at),(("n",0), ctermPr nt)] pow_Suc_vP2);

fun nat_induct_atP (Qabs, kT) = beta_norm (Drule.infer_instantiate ctxtPr
          [(("P",0), ctermPr Qabs), (("k",0), ctermPr kT)] nat_induct_vP2);

(* prodf ground instantiators on ctxtPr *)
fun prodf0_at fT       = beta_norm (Drule.infer_instantiate ctxtPr [(("f",0), ctermPr fT)] prodf_0_vP2);
fun prodfSuc_at (fT,nt)= beta_norm (Drule.infer_instantiate ctxtPr
                          [(("f",0), ctermPr fT),(("n",0), ctermPr nt)] prodf_Suc_vP2);

(* congruence helpers on ctxtPr : left/right operand of mult *)
fun mult_cong_lP (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtPr
          [(("P",0), ctermPr Pabs), (("a",0), ctermPr pT), (("b",0), ctermPr qT)] oeq_subst_vP2);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtPr [(("a",0), ctermPr (mult pT kT))] oeq_refl_vP2);
  in inst OF [hpq, refl_pk] end;
fun mult_cong_rP (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtPr
          [(("P",0), ctermPr Pabs), (("a",0), ctermPr pT), (("b",0), ctermPr qT)] oeq_subst_vP2);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtPr [(("a",0), ctermPr (mult hT pT))] oeq_refl_vP2);
  in inst OF [hpq, refl_hp] end;

(* le helpers on ctxtPr *)
fun le_introP (mT, nT, w) hyp =
  let
    val Pabs = Abs ("p", natT, oeq nT (add mT (Bound 0)));
    val exI_inst = beta_norm (Drule.infer_instantiate ctxtPr
          [(("P",0), ctermPr Pabs), (("a",0), ctermPr w)] exI_vP2);
  in exI_inst OF [hyp] end;
fun le_reflP_at t = beta_norm (Drule.infer_instantiate ctxtPr [(("n",0), ctermPr t)] le_refl_vP2);
fun le_transP_at (mt, nt, kt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtPr
        [(("m",0), ctermPr mt), (("n",0), ctermPr nt), (("k",0), ctermPr kt)] le_trans_vP2)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
(* le_suc_self on ctxtPr : le b (Suc b).  witness Suc 0 : Suc b = b + Suc 0. *)
fun le_suc_selfP_at bT =
  let
    val asr  = addSrP_at (bT, ZeroC);            (* oeq (add b (Suc 0)) (Suc (add b 0)) *)
    val a0r  = add0rP_at bT;                      (* oeq (add b 0) b *)
    val a0rS = Suc_cong OF [a0r];                 (* oeq (Suc (add b 0)) (Suc b) *)
    val chain = oeq_trans OF [asr, a0rS];         (* oeq (add b (Suc 0)) (Suc b) *)
    val chainSym = oeq_sym OF [chain];            (* oeq (Suc b) (add b (Suc 0)) *)
  in le_introP (bT, suc bT, suc ZeroC) chainSym end;

(* object Imp / Forall helpers on ctxtPr *)
fun impI_P (At, Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtPr
        [(("A",0), ctermPr At), (("B",0), ctermPr Bt)] impI_vP2)
  in Thm.implies_elim inst hImpThm end;
fun mp_P (At, Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtPr
        [(("A",0), ctermPr At), (("B",0), ctermPr Bt)] mp_vP2)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun allI_P Pabs hAll =
  let val inst = beta_norm (Drule.infer_instantiate ctxtPr
        [(("P",0), ctermPr Pabs)] allI_vP2)
  in Thm.implies_elim inst hAll end;
fun allE_P Pabs at hForall =
  let val inst = beta_norm (Drule.infer_instantiate ctxtPr
        [(("P",0), ctermPr Pabs), (("a",0), ctermPr at)] allE_vP2)
  in Thm.implies_elim inst hForall end;

(* ---- uniform 0-hyp + aconv validator on ctxtPr ---- *)
fun checkPr (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtPr (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtPr intended ^ "\n");
          false)
  end;

(* schematic Vars for intended statements on ctxtPr *)
val nVp = Var (("n",0), natT);
val cVp = Var (("c",0), natT);
val fVp = Var (("f",0), fnT);
val gVp = Var (("g",0), fnT);

(* ---- SANITY : prodf_0 / prodf_Suc instantiate cleanly ---- *)
val i_prodf_0   = jT (oeq (prodf fVp ZeroC) (fVp $ ZeroC));
val i_prodf_Suc = jT (oeq (prodf fVp (suc nVp)) (mult (prodf fVp nVp) (fVp $ (suc nVp))));
val r_prodf_0   = checkPr ("prodf_0_ax",   prodf_0_vP2,   i_prodf_0);
val r_prodf_Suc = checkPr ("prodf_Suc_ax", prodf_Suc_vP2, i_prodf_Suc);
val () =
  if r_prodf_0 andalso r_prodf_Suc then out "OK prodf_def\n"
  else out "FAIL prodf_def\n";

(* ============================================================================
   (1) prod_cong :
        (!!k. jT (le k n) ==> jT (oeq (f k)(g k))) ==> jT (oeq (prodf f n)(prodf g n))
       MIRRORS sum_cong EXACTLY : add -> mult.
   ============================================================================ *)
val prod_cong =
  let
    val fF = Free("f", fnT); val gF = Free("g", fnT);
    val kAbsV = Free("k", natT);
    fun hypObjAbs zt =
      Term.lambda kAbsV (mkImp (le kAbsV zt) (oeq (fF $ kAbsV) (gF $ kAbsV)));
    fun hypObj zt = mkForall (hypObjAbs zt);
    fun concBody zt = oeq (prodf fF zt) (prodf gF zt);

    val zAbsV = Free("z", natT);
    val Qpred = Term.lambda zAbsV (mkImp (hypObj zAbsV) (concBody zAbsV));
    val nIndV = Free("n", natT);
    val ind = nat_induct_atP (Qpred, nIndV);

    (* ---- BASE : jT (Imp (hypObj 0)(concBody 0)) ---- *)
    val base =
      let
        val hyp0 = Thm.assume (ctermPr (jT (hypObj ZeroC)));
        val imp00 = allE_P (hypObjAbs ZeroC) ZeroC hyp0;
        val le00 = le_reflP_at ZeroC;
        val f0g0 = mp_P (le ZeroC ZeroC, oeq (fF $ ZeroC) (gF $ ZeroC)) imp00 le00;
        val pf0 = prodf0_at fF;                                (* prodf f 0 = f 0 *)
        val pg0 = prodf0_at gF;                                (* prodf g 0 = g 0 *)
        val pg0sym = oeq_sym OF [pg0];                         (* g 0 = prodf g 0 *)
        val concl0 = oeq_trans OF [oeq_trans OF [pf0, f0g0], pg0sym];
        val dis = Thm.implies_intr (ctermPr (jT (hypObj ZeroC))) concl0;
      in impI_P (hypObj ZeroC, concBody ZeroC) dis end;

    (* ---- STEP ---- *)
    val xF = Free("x", natT);
    val ihprop = jT (mkImp (hypObj xF) (concBody xF));
    val IH = Thm.assume (ctermPr ihprop);
    val stepConcl =
      let
        val hypSx = Thm.assume (ctermPr (jT (hypObj (suc xF))));
        val kk = Free("k", natT);
        val impSx_k = allE_P (hypObjAbs (suc xF)) kk hypSx;
        val le_k_x = Thm.assume (ctermPr (jT (le kk xF)));
        val le_x_Sx = le_suc_selfP_at xF;
        val le_k_Sx = le_transP_at (kk, xF, suc xF) le_k_x le_x_Sx;
        val fk_gk = mp_P (le kk (suc xF), oeq (fF $ kk) (gF $ kk)) impSx_k le_k_Sx;
        val impx_k_dis = Thm.implies_intr (ctermPr (jT (le kk xF))) fk_gk;
        val impx_k = impI_P (le kk xF, oeq (fF $ kk) (gF $ kk)) impx_k_dis;
        val allMinor = Thm.forall_intr (ctermPr kk) impx_k;
        val hypObjx = allI_P (hypObjAbs xF) allMinor;
        val prodfx_eq = mp_P (hypObj xF, concBody xF) IH hypObjx;   (* prodf f x = prodf g x *)
        val impSx_Sx = allE_P (hypObjAbs (suc xF)) (suc xF) hypSx;
        val le_Sx_Sx = le_reflP_at (suc xF);
        val fSx_gSx = mp_P (le (suc xF) (suc xF), oeq (fF $ (suc xF)) (gF $ (suc xF))) impSx_Sx le_Sx_Sx;
        val pfS = prodfSuc_at (fF, xF);                        (* prodf f (Sx) = mult (prodf f x)(f Sx) *)
        val pgS = prodfSuc_at (gF, xF);                        (* prodf g (Sx) = mult (prodf g x)(g Sx) *)
        val cL = mult_cong_lP (prodf fF xF, prodf gF xF, fF $ (suc xF)) prodfx_eq;
        val cR = mult_cong_rP (prodf gF xF, fF $ (suc xF), gF $ (suc xF)) fSx_gSx;
        val mid = oeq_trans OF [cL, cR];
        val pgS_s = oeq_sym OF [pgS];
        val concl = oeq_trans OF [oeq_trans OF [pfS, mid], pgS_s];
        val dis = Thm.implies_intr (ctermPr (jT (hypObj (suc xF)))) concl;
      in impI_P (hypObj (suc xF), concBody (suc xF)) dis end;
    val step1 = Thm.forall_intr (ctermPr xF) (Thm.implies_intr (ctermPr ihprop) stepConcl);

    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;

    (* ---- CONVERT meta-hyp -> jT (hypObj n) -> concBody n ; discharge meta-hyp ---- *)
    val kk2 = Free("k", natT);
    val metaHyp = Logic.all kk2 (Logic.mk_implies (jT (le kk2 nIndV), jT (oeq (fF $ kk2) (gF $ kk2))));
    val Hm = Thm.assume (ctermPr metaHyp);
    val Hm_k = Thm.forall_elim (ctermPr kk2) Hm;
    val impn_k = impI_P (le kk2 nIndV, oeq (fF $ kk2) (gF $ kk2)) Hm_k;
    val allMinor2 = Thm.forall_intr (ctermPr kk2) impn_k;
    val hypObjn = allI_P (hypObjAbs nIndV) allMinor2;
    val concln = mp_P (hypObj nIndV, concBody nIndV) r2 hypObjn;
    val d1 = Thm.implies_intr (ctermPr metaHyp) concln;
  in varify d1 end;

val i_prod_cong =
  let
    val kk = Free("k", natT)
  in
    Logic.mk_implies (
      Logic.all kk (Logic.mk_implies (jT (le kk nVp), jT (oeq (fVp $ kk) (gVp $ kk)))),
      jT (oeq (prodf fVp nVp) (prodf gVp nVp)))
  end;
val r_prod_cong = checkPr ("prod_cong", prod_cong, i_prod_cong);

(* ============================================================================
   (2) prod_const_pow :  prodf (%k. c) n = pow c (Suc n)
       induction on n.
   ============================================================================ *)
val prod_const_pow =
  let
    val cF = Free("c", natT);
    val constAbs = Abs("k", natT, cF);                         (* %k. c *)

    val Qpred = Abs("z", natT, oeq (prodf constAbs (Bound 0)) (pow cF (suc (Bound 0))));
    val nF = Free("n", natT);
    val ind = nat_induct_atP (Qpred, nF);

    (* ---- BASE n=0 : prodf (%k.c) 0 = c ; pow c (Suc 0) = mult c (pow c 0) = mult c (Suc 0) = c ---- *)
    val base =
      let
        val p0 = prodf0_at constAbs;                           (* prodf (%k.c) 0 = (%k.c) 0 = c [beta] *)
        (* RHS : pow c (Suc 0) = mult c (pow c 0) [pow_Suc] = mult c (Suc 0) [pow_Zero,cong_r] = c [mult_1_right] *)
        val ps = powSucP2_at (cF, ZeroC);                      (* pow c (Suc 0) = mult c (pow c 0) *)
        val pz = powZeroP2_at cF;                              (* pow c 0 = Suc 0 *)
        val cr = mult_cong_rP (cF, pow cF ZeroC, suc ZeroC) pz; (* mult c (pow c 0) = mult c (Suc 0) *)
        val m1 = mult1rP_at cF;                                (* mult c (Suc 0) = c *)
        val rhs = oeq_trans OF [oeq_trans OF [ps, cr], m1];    (* pow c (Suc 0) = c *)
        val rhsSym = oeq_sym OF [rhs];                         (* c = pow c (Suc 0) *)
      in oeq_trans OF [p0, rhsSym] end;

    (* ---- STEP : assume prodf (%k.c) x = pow c (Suc x) ; prove for Suc x ---- *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (prodf constAbs xF) (pow cF (suc xF)));
    val IH = Thm.assume (ctermPr ihprop);
    val stepconcl =
      let
        (* LHS : prodf (%k.c)(Suc x) = mult (prodf (%k.c) x)(c) [prodf_Suc,beta on (%k.c)(Sx)=c] *)
        val pS = prodfSuc_at (constAbs, xF);                   (* prodf cAbs (Sx) = mult (prodf cAbs x)((%k.c)(Sx)) ; (%k.c)(Sx) beta = c *)
        (* rewrite the (prodf cAbs x) factor via IH : mult (prodf cAbs x) c = mult (pow c (Suc x)) c *)
        val cIH = mult_cong_lP (prodf constAbs xF, pow cF (suc xF), cF) IH;
        val lhs1 = oeq_trans OF [pS, cIH];                     (* prodf cAbs (Sx) = mult (pow c (Suc x)) c *)
        (* commute : mult (pow c (Suc x)) c = mult c (pow c (Suc x)) *)
        val comm = mult_comm_atP (pow cF (suc xF), cF);
        val lhs2 = oeq_trans OF [lhs1, comm];                  (* = mult c (pow c (Suc x)) *)
        (* RHS : pow c (Suc (Suc x)) = mult c (pow c (Suc x)) [pow_Suc] *)
        val rS = powSucP2_at (cF, suc xF);                     (* pow c (Suc (Suc x)) = mult c (pow c (Suc x)) *)
        val rSsym = oeq_sym OF [rS];                           (* mult c (pow c (Suc x)) = pow c (Suc (Suc x)) *)
      in oeq_trans OF [lhs2, rSsym] end;
    val step1 = Thm.forall_intr (ctermPr xF) (Thm.implies_intr (ctermPr ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_prod_const_pow =
  let val cAbs = Abs("k", natT, cVp)
  in jT (oeq (prodf cAbs nVp) (pow cVp (suc nVp))) end;
val r_prod_const_pow = checkPr ("prod_const_pow", prod_const_pow, i_prod_const_pow);

(* soundness probe : kernel must REJECT a false exponent (pow c n instead of pow c (Suc n)) *)
val s_prod_const_pow_nontrivial =
  not ((Thm.prop_of prod_const_pow) aconv
       (let val cAbs = Abs("k", natT, cVp) in jT (oeq (prodf cAbs nVp) (pow cVp nVp)) end));
val () =
  if s_prod_const_pow_nontrivial then out "PROBE_OK prod_const_pow exponent is Suc n\n"
  else out "PROBE_FAIL prod_const_pow collapsed!\n";

(* ============================================================================
   (3) prod_mult_combine :
        mult (prodf f n)(prodf g n) = prodf (%k. mult (f k)(g k)) n
       MIRRORS sum_add : add -> mult, add4_swap -> mult4_swap.
   ============================================================================ *)
(* mult4_swap on ctxtPr : reorder (A*B)*(C*D) -> (A*C)*(B*D) *)
fun mult4_swapP (A,B,C,D) =
  let
    val asbcd = mult_assoc_atP (A, B, mult C D);              (* (A*B)*(C*D) = A*(B*(C*D)) *)
    val i1 = mult_assoc_atP (B, C, D);                        (* (B*C)*D = B*(C*D) *)
    val i1s = oeq_sym OF [i1];                                (* B*(C*D) = (B*C)*D *)
    val icc = mult_comm_atP (B, C);                           (* B*C = C*B *)
    val i2 = mult_cong_lP (mult B C, mult C B, D) icc;        (* (B*C)*D = (C*B)*D *)
    val i3 = mult_assoc_atP (C, B, D);                        (* (C*B)*D = C*(B*D) *)
    val inner = oeq_trans OF [oeq_trans OF [i1s, i2], i3];    (* B*(C*D) = C*(B*D) *)
    val cInner = mult_cong_rP (A, mult B (mult C D), mult C (mult B D)) inner;
                                                              (* A*(B*(C*D)) = A*(C*(B*D)) *)
    val r1 = oeq_trans OF [asbcd, cInner];                    (* (A*B)*(C*D) = A*(C*(B*D)) *)
    val r2assoc = mult_assoc_atP (A, C, mult B D);            (* (A*C)*(B*D) = A*(C*(B*D)) *)
    val r2assoc_s = oeq_sym OF [r2assoc];                     (* A*(C*(B*D)) = (A*C)*(B*D) *)
  in oeq_trans OF [r1, r2assoc_s] end;

val prod_mult_combine =
  let
    val fF = Free("f", fnT); val gF = Free("g", fnT);
    val hAbs = Abs("k", natT, mult (fF $ (Bound 0)) (gF $ (Bound 0)));  (* %k. mult (f k)(g k) *)

    val Qpred = Abs("z", natT, oeq (mult (prodf fF (Bound 0)) (prodf gF (Bound 0))) (prodf hAbs (Bound 0)));
    val nF = Free("n", natT);
    val ind = nat_induct_atP (Qpred, nF);

    (* ---- BASE n=0 : mult (prodf f 0)(prodf g 0) = mult (f 0)(g 0) = prodf h 0 ---- *)
    val base =
      let
        val pf0 = prodf0_at fF;                                (* prodf f 0 = f 0 *)
        val pg0 = prodf0_at gF;                                (* prodf g 0 = g 0 *)
        val cL  = mult_cong_lP (prodf fF ZeroC, fF $ ZeroC, prodf gF ZeroC) pf0;
                  (* mult (prodf f 0)(prodf g 0) = mult (f 0)(prodf g 0) *)
        val cR  = mult_cong_rP (fF $ ZeroC, prodf gF ZeroC, gF $ ZeroC) pg0;
                  (* mult (f 0)(prodf g 0) = mult (f 0)(g 0) *)
        val ph0 = prodf0_at hAbs;                              (* prodf h 0 = h 0 = mult (f 0)(g 0) [beta] *)
        val ph0sym = oeq_sym OF [ph0];
      in oeq_trans OF [oeq_trans OF [cL, cR], ph0sym] end;

    (* ---- STEP ---- *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (mult (prodf fF xF) (prodf gF xF)) (prodf hAbs xF));
    val IH = Thm.assume (ctermPr ihprop);
    val stepconcl =
      let
        val pfS = prodfSuc_at (fF, xF);                        (* prodf f (Sx) = mult (prodf f x)(f Sx) *)
        val pgS = prodfSuc_at (gF, xF);                        (* prodf g (Sx) = mult (prodf g x)(g Sx) *)
        (* LHS = mult (prodf f (Sx))(prodf g (Sx)) = mult (mult (prodf f x)(f Sx))(mult (prodf g x)(g Sx)) *)
        val cL  = mult_cong_lP (prodf fF (suc xF), mult (prodf fF xF) (fF $ (suc xF)), prodf gF (suc xF)) pfS;
        val cR  = mult_cong_rP (mult (prodf fF xF) (fF $ (suc xF)), prodf gF (suc xF), mult (prodf gF xF) (gF $ (suc xF))) pgS;
        val lhs1 = oeq_trans OF [cL, cR];
        (* reshuffle to mult (mult (prodf f x)(prodf g x))(mult (f Sx)(g Sx)) *)
        val swap = mult4_swapP (prodf fF xF, fF $ (suc xF), prodf gF xF, gF $ (suc xF));
        val lhs2 = oeq_trans OF [lhs1, swap];
        (* IH on left factor : mult (prodf f x)(prodf g x) = prodf h x *)
        val cIH = mult_cong_lP (mult (prodf fF xF) (prodf gF xF), prodf hAbs xF, mult (fF $ (suc xF)) (gF $ (suc xF))) IH;
        val lhs3 = oeq_trans OF [lhs2, cIH];
                  (* = mult (prodf h x)(mult (f Sx)(g Sx)) *)
        (* RHS : prodf h (Sx) = mult (prodf h x)(h Sx) ; h Sx beta = mult (f Sx)(g Sx) *)
        val phS = prodfSuc_at (hAbs, xF);
        val phSsym = oeq_sym OF [phS];
      in oeq_trans OF [lhs3, phSsym] end;
    val step1 = Thm.forall_intr (ctermPr xF) (Thm.implies_intr (ctermPr ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_prod_mult_combine =
  let val hV = Abs("k", natT, mult (fVp $ (Bound 0)) (gVp $ (Bound 0)))
  in jT (oeq (mult (prodf fVp nVp) (prodf gVp nVp)) (prodf hV nVp)) end;
val r_prod_mult_combine = checkPr ("prod_mult_combine", prod_mult_combine, i_prod_mult_combine);

(* ============================================================================
   FINAL VERDICT
   ============================================================================ *)
val () =
  if r_prodf_0 andalso r_prodf_Suc
     andalso r_prod_cong andalso r_prod_const_pow andalso s_prod_const_pow_nontrivial
     andalso r_prod_mult_combine
  then out "PRODF_OK\n"
  else out "PRODF_INCOMPLETE\n";
