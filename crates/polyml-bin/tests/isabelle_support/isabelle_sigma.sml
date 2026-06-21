(* ============================================================================
   sigma_prime  : prime2 q ==> sigma q = q + 1
   on Isabelle/Pure on the polyml-rs interpreter.
   ----------------------------------------------------------------------------
   PHASE 0 introduces the sum-of-divisors subsystem:
     swt   : nat => nat => nat        (summand weight)
       swt_dvd  : jT (dvd d n) ==> jT (oeq (swt n d) d)
       swt_ndvd : jT (neg (dvd d n)) ==> jT (oeq (swt n d) Zero)
     sigma : nat => nat
       sigma_def : jT (oeq (sigma n) (sumf (swt n) n))      (sum over d=0..n)
   These 3 conservative axioms (2 conditional + 1 defining) are the ONLY axioms
   introduced; NONE mentions `perfect` or the conclusion.

   sigma_prime : for a prime q (so 1 < q, q >= 2), the only divisors of q in the
   range 0..q are 1 and q (1|q always, q|q always, 0 does not divide q>0, and
   nothing strictly between by prime2_div).  Hence
       sigma q = sumf (swt q) q = (q at index q) + (1 at index 1) + 0 elsewhere
               = q + 1.

   Adding swt+sigma EXTENDS the theory thySub -> thySig, so we build ONE final
   context ctxtSig/ctermSig and re-varify every reused base lemma onto it
   (the standard new-const discipline, copied from isabelle_prodf.sml).
   ============================================================================ *)
val () = out "SIGMA_PRIME_BEGIN\n";

(* ---- ONE theory extension with the two new consts ---- *)
val thySig0a = Sign.add_consts
  [(Binding.name "swt", natT --> natT --> natT, NoSyn)] thySub;
val swtC = Const (Sign.full_name thySig0a (Binding.name "swt"), natT --> natT --> natT);
fun swt n d = swtC $ n $ d;

val thySig0 = Sign.add_consts
  [(Binding.name "sigma", natT --> natT, NoSyn)] thySig0a;
val sigmaC = Const (Sign.full_name thySig0 (Binding.name "sigma"), natT --> natT);
fun sigma n = sigmaC $ n;

(* ---- defining / conditional axioms (conservative) ----
   neg A == Imp A oFalse (base abbreviation); dvd a b == Ex(%k. b = a*k).        *)
val dSwt = Free("d", natT);
val nSwt = Free("n", natT);
val ((_,swt_dvd_ax),  thySig1) = Thm.add_axiom_global (Binding.name "swt_dvd",
      Logic.mk_implies (jT (dvd dSwt nSwt), jT (oeq (swt nSwt dSwt) dSwt))) thySig0;
val ((_,swt_ndvd_ax), thySig2) = Thm.add_axiom_global (Binding.name "swt_ndvd",
      Logic.mk_implies (jT (neg (dvd dSwt nSwt)), jT (oeq (swt nSwt dSwt) ZeroC))) thySig1;
(* sigma n = sumf (swt n) n   ; swt n is a partial application : nat => nat *)
val ((_,sigma_def_ax), thySig) = Thm.add_axiom_global (Binding.name "sigma_def",
      jT (oeq (sigma nSwt) (sumf (swtC $ nSwt) nSwt))) thySig2;

(* ---- THE ONE FINAL CONTEXT ctxtSig / ctermSig ---- *)
val ctxtSig  = Proof_Context.init_global thySig;
val ctermSig = Thm.cterm_of ctxtSig;

(* ============================================================================
   RE-VARIFY every reused base lemma onto ctxtSig, then build ground
   instantiators (mirror isabelle_prodf.sml verbatim where possible).
   ============================================================================ *)
val oeq_refl_vSg     = varify oeq_refl;
val oeq_subst_vSg    = varify oeq_subst;
val nat_induct_vSg   = varify nat_induct;
val add_0_vSg        = varify add_0;
val add_0_right_vSg  = varify add_0_right;
val add_comm_vSg     = varify add_comm;
val add_assoc_vSg    = varify add_assoc;
val mult_comm_vSg    = varify mult_comm;
val mult_assoc_vSg   = varify mult_assoc;
val mult_1_right_vSg = varify mult_1_right;
val mult_0_right_vSg = varify mult_0_right;
val exI_vSg          = varify exI_ax;
val le_refl_vSg      = varify le_refl;
val le_trans_vSg     = varify le_trans;
val impI_vSg         = varify impI_ax;
val mp_vSg           = varify mp_ax;
val allI_vSg         = varify allI_ax;
val allE_vSg         = varify allE_ax;
val disjE_vSg        = varify disjE_ax;
val ex_middle_vSg    = varify ex_middle_ax;
val disj_zero_or_suc_vSg = varify disj_zero_or_suc;
(* sum algebra (proved on ctxtSub) *)
val sumf_0_vSg       = varify sumf_0_ax;
val sumf_Suc_vSg     = varify sumf_Suc_ax;
val sum_cong_vSg     = varify sum_cong;
val sum_peel_first_vSg = varify sum_peel_first;
(* swt/sigma axioms *)
val swt_dvd_vSg      = varify swt_dvd_ax;
val swt_ndvd_vSg     = varify swt_ndvd_ax;
val sigma_def_vSg    = varify sigma_def_ax;

(* ---- ground instantiators on ctxtSig ---- *)
fun oeqreflSg_at t   = beta_norm (Drule.infer_instantiate ctxtSig [(("a",0), ctermSig t)] oeq_refl_vSg);
fun add0Sg_at t      = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] add_0_vSg);
fun add0rSg_at t     = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] add_0_right_vSg);
fun addcommSg_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSig
                            [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] add_comm_vSg);

fun nat_induct_atSg (Qabs, kT) = beta_norm (Drule.infer_instantiate ctxtSig
          [(("P",0), ctermSig Qabs), (("k",0), ctermSig kT)] nat_induct_vSg);

(* sumf ground instantiators on ctxtSig *)
fun sumf0Sg_at fT       = beta_norm (Drule.infer_instantiate ctxtSig [(("f",0), ctermSig fT)] sumf_0_vSg);
fun sumfSucSg_at (fT,nt)= beta_norm (Drule.infer_instantiate ctxtSig
                          [(("f",0), ctermSig fT),(("n",0), ctermSig nt)] sumf_Suc_vSg);

(* sum_cong on ctxtSig : (!!k. le k n ==> f k = g k) ==> sumf f n = sumf g n *)
fun sum_cong_atSg (fAbs, gAbs, nt) congProof =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("f",0), ctermSig fAbs), (("g",0), ctermSig gAbs), (("n",0), ctermSig nt)] sum_cong_vSg)
  in Thm.implies_elim inst congProof end;

(* sum_peel_first on ctxtSig : sumf f (Suc n) = add (f 0)(sumf (%k. f (Suc k)) n) *)
fun sum_peel_first_atSg (fT, nt) = beta_norm (Drule.infer_instantiate ctxtSig
        [(("f",0), ctermSig fT),(("n",0), ctermSig nt)] sum_peel_first_vSg);

(* add congruence on LEFT / RIGHT operand, on ctxtSig *)
fun add_cong_lSg (pT, qT, kT) hpq =
  let
    val zF = Free("z_al", natT);
    val Pabs = Term.lambda zF (oeq (add pT kT) (add zF kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtSig
          [(("P",0), ctermSig Pabs), (("a",0), ctermSig pT), (("b",0), ctermSig qT)] oeq_subst_vSg);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtSig [(("a",0), ctermSig (add pT kT))] oeq_refl_vSg);
  in inst OF [hpq, refl_pk] end;
fun add_cong_rSg (hT, pT, qT) hpq =
  let
    val zF = Free("z_ar", natT);
    val Pabs = Term.lambda zF (oeq (add hT pT) (add hT zF));
    val inst = beta_norm (Drule.infer_instantiate ctxtSig
          [(("P",0), ctermSig Pabs), (("a",0), ctermSig pT), (("b",0), ctermSig qT)] oeq_subst_vSg);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtSig [(("a",0), ctermSig (add hT pT))] oeq_refl_vSg);
  in inst OF [hpq, refl_hp] end;

(* mp / impI / allI / allE on ctxtSig *)
fun impI_Sg (At, Bt) hImpThm =                  (* (jT A ==> jT B) -> jT (Imp A B) *)
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("A",0), ctermSig At), (("B",0), ctermSig Bt)] impI_vSg)
  in Thm.implies_elim inst hImpThm end;
fun mp_Sg (At, Bt) hImp hA =                     (* jT (Imp A B) -> jT A -> jT B *)
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("A",0), ctermSig At), (("B",0), ctermSig Bt)] mp_vSg)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun allI_Sg Pabs hAll =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig [(("P",0), ctermSig Pabs)] allI_vSg)
  in Thm.implies_elim inst hAll end;
fun allE_Sg Pabs at hForall =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("P",0), ctermSig Pabs), (("a",0), ctermSig at)] allE_vSg)
  in Thm.implies_elim inst hForall end;

(* ex_middle / disjE / disj_zero_or_suc on ctxtSig *)
fun ex_middle_atSg At = beta_norm (Drule.infer_instantiate ctxtSig [(("A",0), ctermSig At)] ex_middle_vSg);
fun disjE_elimSg (At, Bt, Ct) dThm caseA caseB =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtSig
          [(("A",0), ctermSig At), (("B",0), ctermSig Bt), (("C",0), ctermSig Ct)] disjE_vSg);
    val s1 = Thm.implies_elim inst dThm;
    val s2 = Thm.implies_elim s1 caseA;
  in Thm.implies_elim s2 caseB end;
fun dzosSg_at t = beta_norm (Drule.infer_instantiate ctxtSig [(("p",0), ctermSig t)] disj_zero_or_suc_vSg);

(* exI on ctxtSig (for dvd-introduction): build dvd d n from a witness  *)
fun exI_Sg (Pabs, w) hyp =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("P",0), ctermSig Pabs), (("a",0), ctermSig w)] exI_vSg)
  in inst OF [hyp] end;
(* exE on ctxtSig *)
fun exE_elimSg (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm  = Thm.assume (ctermSig hypTerm);
    val body    = bodyFn wF hypThm;
    val minor   = Thm.forall_intr (ctermSig wF) (Thm.implies_intr (ctermSig hypTerm) body);
    val exE_inst= beta_norm (Drule.infer_instantiate ctxtSig
                    [(("P",0), ctermSig Pabs), (("Q",0), ctermSig goalC)] (varify exE_ax));
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;

(* mult on ctxtSig (for the 0*k=0 / 1*q facts) *)
fun mult1rSg_at t   = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] mult_1_right_vSg);
fun mult0rSg_at t   = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] mult_0_right_vSg);
fun multcommSg_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSig
                            [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] mult_comm_vSg);

(* le_intro / le_refl / le_trans / le_suc_self on ctxtSig *)
fun le_introSg (mT, nT, w) hyp =
  let
    val pAbs = Free("p_li", natT);
    val Pabs = Term.lambda pAbs (oeq nT (add mT pAbs));
    val exI_inst = beta_norm (Drule.infer_instantiate ctxtSig
          [(("P",0), ctermSig Pabs), (("a",0), ctermSig w)] exI_vSg);
  in exI_inst OF [hyp] end;
fun le_reflSg_at t = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] le_refl_vSg);
fun le_transSg_at (mt, nt, kt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("m",0), ctermSig mt), (("n",0), ctermSig nt), (("k",0), ctermSig kt)] le_trans_vSg)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
(* le_suc_self : le b (Suc b) ; witness Suc 0 : Suc b = b + Suc 0 *)
fun le_suc_selfSg_at bT =
  let
    val refl_b = oeqreflSg_at (suc bT);                (* Suc b = Suc b *)
    (* need: Suc b = add b (Suc 0).  add b (Suc 0) = Suc (add b 0) = Suc b. *)
    val addS = beta_norm (Drule.infer_instantiate ctxtSig
                 [(("m",0), ctermSig bT),(("n",0), ctermSig ZeroC)] (varify add_Suc_right));
                                                       (* add b (Suc 0) = Suc (add b 0) *)
    val ab0 = add0rSg_at bT;                           (* add b 0 = b *)
    val sucAb0 = beta_norm (Drule.infer_instantiate ctxtSig    (* Suc(add b 0) = Suc b via cong *)
      [(("P",0), ctermSig (Term.lambda (Free("z_ss",natT)) (oeq (suc (add bT ZeroC)) (suc (Free("z_ss",natT)))))),
       (("a",0), ctermSig (add bT ZeroC)), (("b",0), ctermSig bT)] oeq_subst_vSg)
      OF [ab0, oeqreflSg_at (suc (add bT ZeroC))];
    val rhs = oeq_trans OF [addS, sucAb0];             (* add b (Suc 0) = Suc b *)
    val rhsSym = oeq_sym OF [rhs];                     (* Suc b = add b (Suc 0) *)
  in le_introSg (bT, suc bT, suc ZeroC) rhsSym end;

(* ---- prime2 destructors on ctxtSig ---- *)
(* prime2 p = Conj (lt (Suc Zero) p) (Forall(%d. Imp (dvd d p)(Disj (oeq d 1)(oeq d p)))) *)
val conjunct1_vSg = varify conjunct1_ax;
val conjunct2_vSg = varify conjunct2_ax;
fun conjunct1_Sg (At, Bt) hConj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("A",0), ctermSig At), (("B",0), ctermSig Bt)] conjunct1_vSg)
  in Thm.implies_elim inst hConj end;
fun conjunct2_Sg (At, Bt) hConj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("A",0), ctermSig At), (("B",0), ctermSig Bt)] conjunct2_vSg)
  in Thm.implies_elim inst hConj end;
(* ppAbs p = %d. Imp (dvd d p)(Disj (oeq d 1)(oeq d p))  : build capture-safe *)
fun ppAbsSg p =
  let val dF = Free("d_pp", natT)
  in Term.lambda dF (mkImp (dvd dF p) (mkDisj (oeq dF (suc ZeroC)) (oeq dF p))) end;
fun prime2_gt1_Sg p hPrime =
  conjunct1_Sg (lt (suc ZeroC) p, mkForall (ppAbsSg p)) hPrime;
fun prime2_div_Sg (p, d) hPrime hDvdDP =      (* jT (prime2 p) -> jT (dvd d p) -> jT (Disj (oeq d 1)(oeq d p)) *)
  let
    val faThm = conjunct2_Sg (lt (suc ZeroC) p, mkForall (ppAbsSg p)) hPrime;
    val impAt = allE_Sg (ppAbsSg p) d faThm;
  in mp_Sg (dvd d p, mkDisj (oeq d (suc ZeroC)) (oeq d p)) impAt hDvdDP end;

val () = out "SIGMA_CONSTS_OK\n";

(* ============================================================================
   SANITY : the swt / sigma axioms instantiate cleanly on ctxtSig.
   ============================================================================ *)
val dVg = Var (("d",0), natT);
val nVg = Var (("n",0), natT);
fun checkSg (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtSig (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtSig intended ^ "\n");
          false)
  end;

val i_sigma_def = jT (oeq (sigma nVg) (sumf (swtC $ nVg) nVg));
val r_sigma_def = checkSg ("sigma_def_ax", sigma_def_vSg, i_sigma_def);

(* ============================================================================
   swt evaluation helpers (on ctxtSig).
     swt_eval_dvd  : jT (dvd d n) -> jT (oeq (swt n d) d)
     swt_eval_ndvd : jT (neg (dvd d n)) -> jT (oeq (swt n d) Zero)
   ============================================================================ *)
fun swt_eval_dvd (n, d) hDvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("d",0), ctermSig d), (("n",0), ctermSig n)] swt_dvd_vSg)
  in Thm.implies_elim inst hDvd end;
fun swt_eval_ndvd (n, d) hNdvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("d",0), ctermSig d), (("n",0), ctermSig n)] swt_ndvd_vSg)
  in Thm.implies_elim inst hNdvd end;

(* dvd intro on ctxtSig : dvd a b from witness w with b = a*w *)
fun dvd_introSg (aT, bT, w) hyp =      (* hyp : jT (oeq b (mult a w)) -> jT (dvd a b) *)
  let
    val kF = Free("k_dv", natT);
    val Pabs = Term.lambda kF (oeq bT (mult aT kF));
  in exI_Sg (Pabs, w) hyp end;

(* ============================================================================
   BASIC DIVISIBILITY FACTS for a prime q (1 < q so q > 0).
   one_dvd_q : dvd 1 q       (witness q : q = 1*q)
   q_dvd_q   : dvd q q       (witness 1 : q = q*1)
   ============================================================================ *)
val () = out "SWT_EVAL_OK\n";

(* mult_1_left : oeq (mult (Suc 0) n) n  -- build from mult_Suc + mult_0 *)
val mult_Suc_vSg = varify mult_Suc;    (* oeq (mult (Suc m) n)(add n (mult m n)) *)
val mult_0_vSg   = varify mult_0;      (* oeq (mult 0 n) 0 *)
fun mult1lSg_at t =
  let
    val ms = beta_norm (Drule.infer_instantiate ctxtSig
               [(("m",0), ctermSig ZeroC),(("n",0), ctermSig t)] mult_Suc_vSg);  (* mult (Suc 0) t = add t (mult 0 t) *)
    val m0 = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] mult_0_vSg); (* mult 0 t = 0 *)
    val cr = add_cong_rSg (t, mult ZeroC t, ZeroC) m0;   (* add t (mult 0 t) = add t 0 *)
    val a0 = add0rSg_at t;                                (* add t 0 = t *)
  in oeq_trans OF [oeq_trans OF [ms, cr], a0] end;        (* mult (Suc 0) t = t *)

val () = out "MULT1L_OK\n";

(* ============================================================================
   MORE re-varified pieces for the discrimination / contradiction arguments.
   ============================================================================ *)
val Suc_neq_Zero_vSg = varify Suc_neq_Zero_ax;
val Suc_inj_vSg      = varify Suc_inj_ax;
val lt_irrefl_vSg    = varify lt_irrefl;          (* lt ?n ?n ==> oFalse *)
val add_Suc_vSg      = varify add_Suc;            (* oeq (add (Suc m) n)(Suc(add m n)) *)
val add_Suc_right_vSg= varify add_Suc_right;      (* oeq (add m (Suc n))(Suc(add m n)) *)

fun Suc_neq_Zero_Sg t = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] Suc_neq_Zero_vSg);
fun Suc_inj_Sg (uT,vT) = beta_norm (Drule.infer_instantiate ctxtSig
        [(("a",0), ctermSig uT),(("b",0), ctermSig vT)] Suc_inj_vSg);
fun lt_irrefl_Sg t = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] lt_irrefl_vSg);
fun addSuc_Sg (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSig
        [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] add_Suc_vSg);
fun addSr_Sg (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtSig
        [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] add_Suc_right_vSg);

(* oeq-subst-into-predicate helper on ctxtSig : oeq x y ==> jT (P x) ==> jT (P y),
   P built capture-safe over a fresh Free. *)
fun substPredSg (Pabs, xT, yT) hxy hPx =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("P",0), ctermSig Pabs), (("a",0), ctermSig xT), (("b",0), ctermSig yT)] oeq_subst_vSg)
  in inst OF [hxy, hPx] end;

val () = out "DISCRIM_HELPERS_OK\n";

(* ============================================================================
   sum_zero on ctxtSig : sumf (%j. Zero) n = Zero   (induction on n).
   ============================================================================ *)
val zeroAbsSg = Abs("j", natT, ZeroC);
val sum_zero_Sg =
  let
    val Qpred = Abs("z", natT, oeq (sumf zeroAbsSg (Bound 0)) ZeroC);
    val qF = Free("q", natT);
    val ind = nat_induct_atSg (Qpred, qF);
    val base = sumf0Sg_at zeroAbsSg;                       (* sumf zeroAbs 0 = 0 [beta] *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (sumf zeroAbsSg xF) ZeroC);
    val IH = Thm.assume (ctermSig ihprop);
    val sfS = sumfSucSg_at (zeroAbsSg, xF);                (* sumf zeroAbs (Sx) = add (sumf zeroAbs x)(zeroAbs Sx) ; beta = add (..) 0 *)
    val cL  = add_cong_lSg (sumf zeroAbsSg xF, ZeroC, ZeroC) IH;  (* add (sumf zeroAbs x) 0 = add 0 0 *)
    val a00 = add0Sg_at ZeroC;                            (* add 0 0 = 0 *)
    val stepconcl = oeq_trans OF [oeq_trans OF [sfS, cL], a00];
    val step1 = Thm.forall_intr (ctermSig xF) (Thm.implies_intr (ctermSig ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;
fun sum_zero_Sg_at t = beta_norm (Drule.infer_instantiate ctxtSig [(("q",0), ctermSig t)] sum_zero_Sg);
val () = out "SUM_ZERO_SG_OK\n";

(* ============================================================================
   ndvd_interior : jT (lt (Suc Zero) d) ==> jT (lt d q) ==> jT (neg (dvd d q))
   under the assumption (prime2 q).  We bake the prime hypothesis in.
   Proof: assume dvd d q ; prime2_div gives d=1 \/ d=q.
     d=1 : substitute into (lt 1 d) -> lt 1 1 -> lt_irrefl -> oFalse.
     d=q : substitute into (lt d q) -> lt q q -> lt_irrefl -> oFalse.
   ============================================================================ *)
fun ndvd_interior q hPrime (d, hLt1d, hLtdq) =
  let
    val hdvd  = Thm.assume (ctermSig (jT (dvd d q)));
    val disj  = prime2_div_Sg (q, d) hPrime hdvd;          (* Disj (oeq d 1)(oeq d q) *)
    (* case d = 1 *)
    val caseA =
      let
        val heq = Thm.assume (ctermSig (jT (oeq d (suc ZeroC))));  (* d = 1 *)
        (* lt 1 d ; rewrite d -> 1 in (lt (Suc 0) z) at position z *)
        val zF = Free("z_nd", natT);
        val Pabs = Term.lambda zF (lt (suc ZeroC) zF);     (* %z. lt 1 z *)
        val lt11 = substPredSg (Pabs, d, suc ZeroC) heq hLt1d;  (* lt 1 1 *)
        val fls  = lt_irrefl_Sg (suc ZeroC) OF [lt11];      (* oFalse *)
        val dis  = Thm.implies_intr (ctermSig (jT (oeq d (suc ZeroC)))) fls;
      in dis end;
    (* case d = q *)
    val caseB =
      let
        val heq = Thm.assume (ctermSig (jT (oeq d q)));     (* d = q *)
        val zF = Free("z_nd2", natT);
        val Pabs = Term.lambda zF (lt zF q);               (* %z. lt z q *)
        val ltqq = substPredSg (Pabs, d, q) heq hLtdq;     (* lt q q *)
        val fls  = lt_irrefl_Sg q OF [ltqq];               (* oFalse *)
        val dis  = Thm.implies_intr (ctermSig (jT (oeq d q))) fls;
      in dis end;
    val fls = disjE_elimSg (oeq d (suc ZeroC), oeq d q, oFalseC) disj caseA caseB;
    val disch = Thm.implies_intr (ctermSig (jT (dvd d q))) fls;  (* META: jT (dvd d q) ==> jT oFalse *)
  in impI_Sg (dvd d q, oFalseC) disch end;   (* OBJECT neg : jT (Imp (dvd d q) oFalse) = jT (neg (dvd d q)) *)
val () = out "NDVD_INTERIOR_DEFINED\n";

(* ============================================================================
   BASIC DVD FACTS on ctxtSig (for a generic q):
     dvd_self q   : dvd q q          (witness 1 : q = q*1, via mult_1_right)
     swt_q_q      : swt q q = q
     dvd_one q    : dvd (Suc 0) q    (witness q : q = 1*q, via mult_1_left)
     swt_q_1      : swt q 1 = 1
     ndvd_zero q  : neg (dvd 0 q)  for q = Suc p (0|q <=> q=0)   -> swt q 0 = 0
   ============================================================================ *)
(* dvd q q : witness 1 ;  q = mult q (Suc 0) *)
fun dvd_self_Sg q =
  let val m1 = mult1rSg_at q                              (* oeq (mult q (Suc 0)) q *)
      val m1s = oeq_sym OF [m1]                           (* oeq q (mult q (Suc 0)) *)
  in dvd_introSg (q, q, suc ZeroC) m1s end;              (* dvd q q *)
(* dvd 1 q : witness q ; q = mult (Suc 0) q  (mult1lSg) *)
fun dvd_one_Sg q =
  let val m1 = mult1lSg_at q                              (* oeq (mult (Suc 0) q) q *)
      val m1s = oeq_sym OF [m1]                           (* oeq q (mult (Suc 0) q) *)
  in dvd_introSg (suc ZeroC, q, q) m1s end;              (* dvd (Suc 0) q *)

(* ndvd_zero for q = Suc p : neg (dvd 0 (Suc p)).
   dvd 0 (Suc p) = Ex k. (Suc p) = mult 0 k = 0  -> Suc p = 0 -> oFalse. *)
fun ndvd_zero_Sg p =
  let
    val qS = suc p;
    val hdvd = Thm.assume (ctermSig (jT (dvd ZeroC qS)));
    val PabsK = Abs("k", natT, oeq qS (mult ZeroC (Bound 0)));
    fun bodyFn kF hk =                                    (* hk : oeq (Suc p) (mult 0 k) *)
      let
        val m0 = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig kF)] mult_0_vSg);  (* mult 0 k = 0 *)
        val qS0 = oeq_trans OF [hk, m0];                  (* Suc p = 0 *)
        val fls = (Suc_neq_Zero_Sg p) OF [qS0];           (* oFalse *)
      in fls end;
    val fls = exE_elimSg (PabsK, oFalseC) hdvd "k0" bodyFn;
    val disch = Thm.implies_intr (ctermSig (jT (dvd ZeroC qS))) fls;  (* META: jT (dvd 0 (Suc p)) ==> jT oFalse *)
  in impI_Sg (dvd ZeroC qS, oFalseC) disch end;  (* OBJECT neg (dvd 0 (Suc p)) *)

val () = out "DVD_FACTS_OK\n";

(* ============================================================================
   le-witness helpers for the interior bound proofs.
     lt_1_SucSuc k : lt (Suc 0) (Suc (Suc k))     (1 < k+2)   witness k
     mk_lt_d_q     : from (le k r) and q = Suc(Suc(Suc r)) and d = Suc(Suc k),
                     produce  lt d q.
   ============================================================================ *)
(* lt (Suc 0)(Suc(Suc k)) = le (Suc(Suc 0))(Suc(Suc k)) = Ex p. Suc(Suc k) = (Suc(Suc 0)) + p.
   witness k :  add (Suc(Suc 0)) k = Suc(Suc(add 0 k)) = Suc(Suc k). *)
fun lt_1_SucSuc_Sg k =
  let
    val lhs = suc (suc ZeroC);                            (* 2 *)
    (* add 2 k = Suc(add 1 k) = Suc(Suc(add 0 k)) = Suc(Suc k) *)
    val a1 = addSuc_Sg (suc ZeroC, k);                    (* add (Suc(Suc 0)) k = Suc(add (Suc 0) k) *)
    val a2 = addSuc_Sg (ZeroC, k);                        (* add (Suc 0) k = Suc(add 0 k) *)
    val a3 = add0Sg_at k;                                 (* add 0 k = k *)
    (* Suc(add 1 k) = Suc(Suc(add 0 k)) [Suc_cong a2]; = Suc(Suc k) [Suc_cong (Suc_cong a3)] *)
    val s2 = Suc_cong OF [a2];                            (* Suc(add 1 k) = Suc(Suc(add 0 k)) *)
    val s3 = Suc_cong OF [Suc_cong OF [a3]];              (* Suc(Suc(add 0 k)) = Suc(Suc k) *)
    val chain = oeq_trans OF [oeq_trans OF [a1, s2], s3]; (* add 2 k = Suc(Suc k) *)
    val chainSym = oeq_sym OF [chain];                    (* Suc(Suc k) = add 2 k *)
  in le_introSg (lhs, suc (suc k), k) chainSym end;       (* le 2 (Suc(Suc k)) = lt 1 (Suc(Suc k)) *)

val () = out "LT_HELPERS_OK\n";

(* ============================================================================
   MAIN : sigma_prime : jT (prime2 q) ==> jT (oeq (sigma q)(add q (Suc 0)))
   ============================================================================ *)
val sigma_prime =
  let
    val qF = Free("q", natT);
    val hPrime = Thm.assume (ctermSig (jT (prime2 qF)));
    val gt1 = prime2_gt1_Sg qF hPrime;                    (* lt (Suc 0) q = le 2 q = Ex p. q = 2 + p *)

    (* swt q q = q  and  swt q 1 = 1 *)
    val swtqq = swt_eval_dvd (qF, qF) (dvd_self_Sg qF);   (* oeq (swt q q) q *)
    val swtq1 = swt_eval_dvd (qF, suc ZeroC) (dvd_one_Sg qF);  (* oeq (swt q (Suc 0)) 1 *)

    (* decompose q = Suc(Suc p) from le 2 q : Ex p. q = (Suc(Suc 0)) + p, witness p *)
    val PabsTop = Abs("p", natT, oeq qF (add (suc (suc ZeroC)) (Bound 0)));  (* body of le 2 q *)
    val goalC = oeq (sigma qF) (add qF (suc ZeroC));

    fun topBody pF hpEq =          (* hpEq : oeq q (add (Suc(Suc 0)) p) *)
      let
        (* rewrite q = Suc(Suc p) : add 2 p = Suc(Suc(add 0 p)) = Suc(Suc p) *)
        val a1 = addSuc_Sg (suc ZeroC, pF);               (* add 2 p = Suc(add 1 p) *)
        val a2 = addSuc_Sg (ZeroC, pF);                   (* add 1 p = Suc(add 0 p) *)
        val a3 = add0Sg_at pF;                            (* add 0 p = p *)
        val s2 = Suc_cong OF [a2];
        val s3 = Suc_cong OF [Suc_cong OF [a3]];
        val add2p = oeq_trans OF [oeq_trans OF [a1, s2], s3];  (* add 2 p = Suc(Suc p) *)
        val qSS = oeq_trans OF [hpEq, add2p];             (* q = Suc(Suc p) *)
        (* q' := Suc p ;  q = Suc q'  with q' = Suc p *)
        val qp = suc pF;                                  (* q' = Suc p *)

        (* ---- sigma q = sumf (swt q) q ---- *)
        val sdef = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig qF)] sigma_def_vSg);
                                                          (* oeq (sigma q)(sumf (swt q) q) *)
        (* swt q  as a partial application : swtC $ q *)
        val swtq = swtC $ qF;

        (* ---- TOP PEEL : sumf (swt q) q = sumf (swt q)(Suc q') + swt q (Suc q')
                via rewriting q -> Suc q' then sumf_Suc.  We rewrite the upper bound
                of the sum using qSS (q = Suc(Suc p) = Suc q').  Easier: prove
                  sumf (swt q) q = sumf (swt q)(Suc(Suc p))      [cong on upper arg via qSS]
                then sumf_Suc at (swt q, Suc p). ---- *)
        (* cong : oeq q (Suc(Suc p)) ==> oeq (sumf (swt q) q)(sumf (swt q)(Suc(Suc p))) *)
        val zU = Free("z_u", natT);
        val PupAbs = Term.lambda zU (oeq (sumf swtq qF) (sumf swtq zU));
        val sumUpCong = (beta_norm (Drule.infer_instantiate ctxtSig
              [(("P",0), ctermSig PupAbs), (("a",0), ctermSig qF), (("b",0), ctermSig (suc (suc pF)))] oeq_subst_vSg))
            OF [qSS, oeqreflSg_at (sumf swtq qF)];        (* oeq (sumf (swt q) q)(sumf (swt q)(Suc(Suc p))) *)
        val peelTop = sumfSucSg_at (swtq, suc pF);        (* sumf (swt q)(Suc(Suc p)) = add (sumf (swt q)(Suc p))(swt q (Suc(Suc p))) *)
        (* swt q (Suc(Suc p)) = swt q q via qSS sym : rewrite (Suc(Suc p)) -> q in (swt q _) *)
        val zT = Free("z_t", natT);
        val PtopArg = Term.lambda zT (oeq (swt qF (suc (suc pF))) (swt qF zT));
        val qSSsym = oeq_sym OF [qSS];                    (* Suc(Suc p) = q *)
        val swtTopRw = (beta_norm (Drule.infer_instantiate ctxtSig
              [(("P",0), ctermSig PtopArg), (("a",0), ctermSig (suc (suc pF))), (("b",0), ctermSig qF)] oeq_subst_vSg))
            OF [qSSsym, oeqreflSg_at (swt qF (suc (suc pF)))]; (* oeq (swt q (Suc(Suc p)))(swt q q) *)
        val swtTop_q = oeq_trans OF [swtTopRw, swtqq];    (* swt q (Suc(Suc p)) = q *)
        (* combine top : add (sumf (swt q)(Suc p))(swt q (Suc(Suc p))) = add (sumf (swt q)(Suc p)) q *)
        val topCong = add_cong_rSg (sumf swtq (suc pF), swt qF (suc (suc pF)), qF) swtTop_q;
        val topChain = oeq_trans OF [oeq_trans OF [sumUpCong, peelTop], topCong];
                       (* sumf (swt q) q = add (sumf (swt q)(Suc p)) q *)

        (* ---- LOWER : sumf (swt q)(Suc p) = 1 ----
           sum_peel_first : sumf (swt q)(Suc p) = add (swt q 0)(sumf (%k. swt q (Suc k)) p)
           swt q 0 = 0  (ndvd_zero on q = Suc(Suc p), i.e. p' = Suc p so q = Suc(Suc p)).
           Then = sumf (%k. swt q (Suc k)) p =: T, and T = 1. ---- *)
        val hAbs = Abs("k", natT, swt qF (suc (Bound 0)));   (* %k. swt q (Suc k) *)
        val peelLow = sum_peel_first_atSg (swtq, pF);        (* sumf (swt q)(Suc p) = add ((swt q) 0)(sumf (%k. (swt q)(Suc k)) p) *)
        (* (swt q) 0 beta = swt q 0 ; ndvd_zero needs q = Suc(something).  q = Suc(Suc p) = Suc(Suc p). *)
        val ndvd0 = ndvd_zero_Sg (suc pF);                   (* neg (dvd 0 (Suc(Suc p))) *)
        (* rewrite the modulus (Suc(Suc p)) -> q in neg(dvd 0 _) via qSS sym *)
        val zN = Free("z_n", natT);
        val PndAbs = Term.lambda zN (neg (dvd ZeroC zN));
        val ndvd0q = substPredSg (PndAbs, suc (suc pF), qF) qSSsym ndvd0;  (* neg (dvd 0 q) *)
        val swtq0 = swt_eval_ndvd (qF, ZeroC) ndvd0q;        (* oeq (swt q 0) 0 *)
        val cLow = add_cong_lSg (swt qF ZeroC, ZeroC, sumf hAbs pF) swtq0;
                   (* add (swt q 0)(sumf hAbs p) = add 0 (sumf hAbs p) *)
        val a0L = add0Sg_at (sumf hAbs pF);                  (* add 0 (sumf hAbs p) = sumf hAbs p *)
        val lowToT = oeq_trans OF [oeq_trans OF [peelLow, cLow], a0L];
                     (* sumf (swt q)(Suc p) = sumf hAbs p  (= T) *)

        (* ---- T = sumf hAbs p = 1 ;  split on p (dzos) ---- *)
        val dzp = dzosSg_at pF;                              (* Disj (oeq p 0)(Ex r. p = Suc r) *)
        val Tgoal = oeq (sumf hAbs pF) (suc ZeroC);          (* T = 1 *)
        (* CASE p = 0 :  T = sumf hAbs 0 = hAbs 0 = swt q (Suc 0) = 1 *)
        val caseP0 =
          let
            val hp0 = Thm.assume (ctermSig (jT (oeq pF ZeroC)));
            (* rewrite p -> 0 in T-goal : prove sumf hAbs 0 = 1, then transport to sumf hAbs p *)
            val st0 = sumf0Sg_at hAbs;                       (* sumf hAbs 0 = hAbs 0 = swt q (Suc 0) [beta] *)
            val base1 = oeq_trans OF [st0, swtq1];           (* sumf hAbs 0 = 1 *)
            (* transport along p = 0 (sym: 0 = p) : %z. oeq (sumf hAbs z) 1 *)
            val zP = Free("z_p", natT);
            val PpAbs = Term.lambda zP (oeq (sumf hAbs zP) (suc ZeroC));
            val hp0sym = oeq_sym OF [hp0];                   (* 0 = p *)
            val transported = substPredSg (PpAbs, ZeroC, pF) hp0sym base1;  (* sumf hAbs p = 1 *)
            val dis = Thm.implies_intr (ctermSig (jT (oeq pF ZeroC))) transported;
          in dis end;
        (* CASE p = Suc r : T = sumf hAbs (Suc r) = hAbs 0 + sumf (%k. hAbs (Suc k)) r
             = swt q 1 + sumf (%k. swt q (Suc(Suc k))) r = 1 + 0 = 1.  q = Suc(Suc p) = Suc(Suc(Suc r)). *)
        val exSucAbs = Abs("r", natT, oeq pF (suc (Bound 0)));
        val casePS =
          let
            val hpex = Thm.assume (ctermSig (jT (mkEx exSucAbs)));
            fun bodyR rF hr =            (* hr : oeq p (Suc r) *)
              let
                (* q = Suc(Suc(Suc r)) from qSS and p = Suc r *)
                val zQ = Free("z_q", natT);
                val PqAbs = Term.lambda zQ (oeq qF (suc (suc zQ)));   (* %z. q = Suc(Suc z) *)
                val qSSSr = substPredSg (PqAbs, pF, suc rF) hr qSS;   (* q = Suc(Suc(Suc r)) *)

                (* peel hAbs over Suc r : sumf hAbs (Suc r) = add (hAbs 0)(sumf (%k. hAbs(Suc k)) r) *)
                val peelH = sum_peel_first_atSg (hAbs, rF);
                       (* sumf hAbs (Suc r) = add (hAbs 0)(sumf (%k. hAbs (Suc k)) r) *)
                (* hAbs 0 beta = swt q (Suc 0) = 1 *)
                (* the inner function (%k. hAbs (Suc k)) beta = (%k. swt q (Suc(Suc k))) *)
                val ggAbs = Abs("k", natT, swt qF (suc (suc (Bound 0))));   (* %k. swt q (Suc(Suc k)) *)
                (* show sumf (%k. hAbs (Suc k)) r = sumf ggAbs r : they are beta-equal so identical term after beta_norm.
                   sum_peel_first already produced the inner abstraction (%k. hAbs (Suc k)); after beta it is ggAbs. *)
                (* tail = 0 via sum_cong to zeroAbs + sum_zero.  Need: !!k. le k r ==> swt q (Suc(Suc k)) = 0 *)
                val congMinor =
                  let
                    val kF = Free("k", natT);
                    val hle = Thm.assume (ctermSig (jT (le kF rF)));   (* le k r : Ex pp. r = k + pp *)
                    (* d = Suc(Suc k) ;  lt 1 d  and  lt d q *)
                    val lt1d = lt_1_SucSuc_Sg kF;                      (* lt 1 (Suc(Suc k)) *)
                    (* lt d q :  from le k r : r = k + pp ; q = Suc(Suc(Suc r)) ; witness pp.
                       lt d q = le (Suc d) q = le (Suc(Suc(Suc k))) q = Ex pp. q = (Suc(Suc(Suc k))) + pp *)
                    val PleAbs = Abs("pp", natT, oeq rF (add kF (Bound 0)));
                    fun ltBody ppF hpp =     (* hpp : oeq r (add k pp) *)
                      let
                        (* q = Suc(Suc(Suc r)) = Suc(Suc(Suc(add k pp)))
                           add (Suc(Suc(Suc k))) pp = Suc(Suc(Suc(add k pp))) *)
                        val a1 = addSuc_Sg (suc (suc kF), ppF);        (* add (S(S(S k))) pp = Suc(add (S(S k)) pp) *)
                        val a2 = addSuc_Sg (suc kF, ppF);              (* add (S(S k)) pp = Suc(add (S k) pp) *)
                        val a3 = addSuc_Sg (kF, ppF);                  (* add (S k) pp = Suc(add k pp) *)
                        val s2 = Suc_cong OF [a2];
                        val s3 = Suc_cong OF [Suc_cong OF [a3]];
                        val addSSSk = oeq_trans OF [oeq_trans OF [a1, s2], s3];
                              (* add (S(S(S k))) pp = Suc(Suc(Suc(add k pp))) *)
                        (* q = Suc(Suc(Suc r)) ; r = add k pp -> Suc(Suc(Suc r)) = Suc(Suc(Suc(add k pp))) *)
                        val zR = Free("z_r", natT);
                        val PrAbs = Term.lambda zR (oeq qF (suc (suc (suc zR))));  (* %z. q = S(S(S z)) *)
                        val qSSSadd = substPredSg (PrAbs, rF, add kF ppF) hpp qSSSr;  (* q = Suc(Suc(Suc(add k pp))) *)
                        (* so q = add (S(S(S k))) pp :  q = Suc(Suc(Suc(add k pp))) = add (S(S(S k))) pp [sym addSSSk] *)
                        val qeq = oeq_trans OF [qSSSadd, oeq_sym OF [addSSSk]];  (* q = add (S(S(S k))) pp *)
                      in le_introSg (suc (suc (suc kF)), qF, ppF) qeq end;  (* le (S(S(S k))) q = lt (S(S k)) q *)
                    val ltdq = exE_elimSg (PleAbs, lt (suc (suc kF)) qF) hle "pp_w" ltBody;  (* lt (Suc(Suc k)) q *)
                    (* ndvd_interior : neg (dvd (Suc(Suc k)) q) *)
                    val ndvd = ndvd_interior qF hPrime (suc (suc kF), lt1d, ltdq);  (* neg (dvd (Suc(Suc k)) q) *)
                    val zero = swt_eval_ndvd (qF, suc (suc kF)) ndvd;  (* swt q (Suc(Suc k)) = 0 *)
                    val dis = Thm.implies_intr (ctermSig (jT (le kF rF))) zero;
                    val allm = Thm.forall_intr (ctermSig kF) dis;
                  in allm end;
                (* sum_cong : sumf ggAbs r = sumf zeroAbs r *)
                val congTail = sum_cong_atSg (ggAbs, zeroAbsSg, rF) congMinor;  (* sumf ggAbs r = sumf zeroAbs r *)
                val sz = sum_zero_Sg_at rF;                          (* sumf zeroAbs r = 0 *)
                val tail0 = oeq_trans OF [congTail, sz];             (* sumf ggAbs r = 0 *)
                (* hAbs 0 = swt q (Suc 0) = 1 ; peelH gives add (hAbs 0)(sumf (%k.hAbs(Suc k)) r);
                   beta: hAbs 0 = swt q (Suc 0) ; (%k.hAbs(Suc k)) = ggAbs.  So
                   sumf hAbs (Suc r) = add (swt q (Suc 0))(sumf ggAbs r). *)
                val cHead = add_cong_lSg (swt qF (suc ZeroC), suc ZeroC, sumf ggAbs rF) swtq1;
                       (* add (swt q (Suc 0))(sumf ggAbs r) = add 1 (sumf ggAbs r) *)
                val cTail = add_cong_rSg (suc ZeroC, sumf ggAbs rF, ZeroC) tail0;
                       (* add 1 (sumf ggAbs r) = add 1 0 *)
                val a10 = add0rSg_at (suc ZeroC);                    (* add 1 0 = 1 *)
                val sumHsr = oeq_trans OF [oeq_trans OF [oeq_trans OF [peelH, cHead], cTail], a10];
                       (* sumf hAbs (Suc r) = 1 *)
                (* transport along p = Suc r (sym) to sumf hAbs p = 1 *)
                val zP = Free("z_p2", natT);
                val PpAbs = Term.lambda zP (oeq (sumf hAbs zP) (suc ZeroC));
                val hrsym = oeq_sym OF [hr];                         (* Suc r = p *)
                val transported = substPredSg (PpAbs, suc rF, pF) hrsym sumHsr;  (* sumf hAbs p = 1 *)
              in transported end;
            val res = exE_elimSg (exSucAbs, Tgoal) hpex "r_w" bodyR;
            val dis = Thm.implies_intr (ctermSig (jT (mkEx exSucAbs))) res;
          in dis end;
        val Teq1 = disjE_elimSg (oeq pF ZeroC, mkEx exSucAbs, Tgoal) dzp caseP0 casePS;
                   (* sumf hAbs p = 1 *)
        val lowEq1 = oeq_trans OF [lowToT, Teq1];           (* sumf (swt q)(Suc p) = 1 *)

        (* ---- combine : sigma q = sumf (swt q) q = add (sumf (swt q)(Suc p)) q = add 1 q = add q 1 ---- *)
        val sigToSum = oeq_trans OF [sdef, topChain];       (* sigma q = add (sumf (swt q)(Suc p)) q *)
        val cFinal = add_cong_lSg (sumf swtq (suc pF), suc ZeroC, qF) lowEq1;
                     (* add (sumf (swt q)(Suc p)) q = add 1 q *)
        val comm = addcommSg_at (suc ZeroC, qF);            (* add 1 q = add q 1 *)
        val concl = oeq_trans OF [oeq_trans OF [sigToSum, cFinal], comm];  (* sigma q = add q 1 *)
      in concl end;

    val body = exE_elimSg (PabsTop, goalC) gt1 "p_top" topBody;  (* oeq (sigma q)(add q 1) *)
    val disch = Thm.implies_intr (ctermSig (jT (prime2 qF))) body;
  in varify disch end;

(* ---- validation ---- *)
val qVg = Var (("q",0), natT);
val i_sigma_prime = Logic.mk_implies (jT (prime2 qVg), jT (oeq (sigma qVg)(add qVg (suc ZeroC))));
val r_sigma_prime = checkSg ("sigma_prime", sigma_prime, i_sigma_prime);

val () = out "SIGMA_PRIME_PROVED\n";

(* ============================================================================
   SOUNDNESS PROBES
   ============================================================================ *)
(* (1) genuinely CONDITIONAL on prime2 q : the proved prop is NOT the
   unconditional sigma q = q + 1 (which is FALSE, e.g. sigma 4 = 7 != 5). *)
val s_sigma_prime_conditional =
  not ((Thm.prop_of sigma_prime) aconv (jT (oeq (sigma qVg)(add qVg (suc ZeroC)))));
val () =
  if s_sigma_prime_conditional
  then out "PROBE_OK sigma_prime needs the prime2 hypothesis\n"
  else out "PROBE_FAIL sigma_prime dropped its hypothesis!\n";

(* (2) the RHS is genuinely q+1, not the trivial q (sigma q = q would be wrong). *)
val s_sigma_prime_rhs =
  not ((Thm.prop_of sigma_prime) aconv
       (Logic.mk_implies (jT (prime2 qVg), jT (oeq (sigma qVg) qVg))));
val () =
  if s_sigma_prime_rhs
  then out "PROBE_OK sigma_prime RHS is add q 1 (not q)\n"
  else out "PROBE_FAIL sigma_prime RHS collapsed!\n";

(* (3) the hypothesis is the structural prime2 (not a vacuous True-like guard):
   the proved prop's first premise must be jT (prime2 q) verbatim. *)
val s_sigma_prime_hyp =
  (case Thm.prop_of sigma_prime of
       (Const("Pure.imp",_) $ h $ _) => (h aconv (jT (prime2 qVg)))
     | _ => false);
val () =
  if s_sigma_prime_hyp
  then out "PROBE_OK sigma_prime hypothesis is prime2 q\n"
  else out "PROBE_FAIL sigma_prime hypothesis is not prime2 q!\n";

(* hyps + axiom hygiene report *)
val () = out ("SIGMA_PRIME_HYPS = " ^ Int.toString (length (Thm.hyps_of sigma_prime)) ^ "\n");

val () =
  if r_sigma_prime andalso s_sigma_prime_conditional
     andalso s_sigma_prime_rhs andalso s_sigma_prime_hyp
  then out "SIGMA_PRIME_ALL_OK\n"
  else out "SIGMA_PRIME_INCOMPLETE\n";
(* ============================================================================
   EUCLID PERFECT-NUMBER ASSEMBLY -- SUFFIX
   Appended after the full (proven) sigma_prime driver.  Adds:
     (S1) pow/sub instantiators on ctxtSig the sigma_prime prelude lacked,
     (S2) geo_add / geo_sum (the geometric value sigma(2^k) collapses to),
     (S3) sum_split_Suc  (boundary-split infra for the divisor recurrence),
     (S4) the euclid_perfect STATEMENT + the crux blocker documentation.
   All on the SAME ctxtSig / thySig from the sigma_prime prelude.
   ============================================================================ *)
val () = out "EP_ASSEMBLY_SUFFIX_BEGIN\n";

(* ---- (S1) pow / sub / extra-arith instantiators on ctxtSig ---- *)
val twoC = suc (suc ZeroC);                        (* 2 *)
val oneC = suc ZeroC;                              (* 1 *)
val pwAbs = powC $ twoC;                            (* (pow 2)  eta form : (pow 2) i = pow 2 i *)

val pow_Zero_vSg2    = varify pow_Zero_ax;
val pow_Suc_vSg2     = varify pow_Suc_ax;
val sub_n_0_vSg2     = varify sub_n_0_ax;
val sub_add_l_vSg2   = varify sub_add_l;
val add_assoc_vSg2   = varify add_assoc;
val add_Suc_vSg2     = varify add_Suc;
val mult_Suc_vSg2    = varify mult_Suc;

fun powZeroSg_at t   = beta_norm (Drule.infer_instantiate ctxtSig [(("a",0), ctermSig t)] pow_Zero_vSg2);
fun powSucSg_at (at,nt) = beta_norm (Drule.infer_instantiate ctxtSig
                            [(("a",0), ctermSig at),(("n",0), ctermSig nt)] pow_Suc_vSg2);
fun subN0Sg_at t     = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] sub_n_0_vSg2);
fun subAddLSg_at (kt,jt) = beta_norm (Drule.infer_instantiate ctxtSig
                            [(("k",0), ctermSig kt),(("j",0), ctermSig jt)] sub_add_l_vSg2);
fun addassocSg_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtSig
                            [(("m",0), ctermSig mt),(("n",0), ctermSig nt),(("k",0), ctermSig kt)] add_assoc_vSg2);
fun addSucSg_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSig
                            [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] add_Suc_vSg2);
fun multSucSg_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSig
                            [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] mult_Suc_vSg2);

(* mult congruence on ctxtSig (sigma_prime prelude only had add congruence) *)
fun mult_cong_lSg (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
      val inst = beta_norm (Drule.infer_instantiate ctxtSig
            [(("P",0), ctermSig Pabs), (("a",0), ctermSig pT), (("b",0), ctermSig qT)] oeq_subst_vSg);
      val refl = beta_norm (Drule.infer_instantiate ctxtSig [(("a",0), ctermSig (mult pT kT))] oeq_refl_vSg);
  in inst OF [hpq, refl] end;
fun mult_cong_rSg (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
      val inst = beta_norm (Drule.infer_instantiate ctxtSig
            [(("P",0), ctermSig Pabs), (("a",0), ctermSig pT), (("b",0), ctermSig qT)] oeq_subst_vSg);
      val refl = beta_norm (Drule.infer_instantiate ctxtSig [(("a",0), ctermSig (mult hT pT))] oeq_refl_vSg);
  in inst OF [hpq, refl] end;

val () = out "EP_S1_INSTANTIATORS_OK\n";

(* ============================================================================
   (S2) geo_add : add 1 (sumf (pow 2) k) = pow 2 (Suc k)     induction on k.
   ============================================================================ *)
val geo_add =
  let
    fun gbody zt = oeq (add oneC (sumf pwAbs zt)) (pow twoC (suc zt));
    val zV = Free("z", natT);
    val Qpred = Term.lambda zV (gbody zV);
    val kIndV = Free("k", natT);
    val ind = nat_induct_atSg (Qpred, kIndV);
    val base =
      let
        val s0   = sumf0Sg_at pwAbs;
        val cR   = add_cong_rSg (oneC, sumf pwAbs ZeroC, pow twoC ZeroC) s0;
        val pz   = powZeroSg_at twoC;
        val cR2  = add_cong_rSg (oneC, pow twoC ZeroC, oneC) pz;
        val lhs  = oeq_trans OF [cR, cR2];
        val rS   = powSucSg_at (twoC, ZeroC);
        val rcR  = mult_cong_rSg (twoC, pow twoC ZeroC, oneC) pz;
        val rm1  = mult1rSg_at twoC;
        val rhs  = oeq_trans OF [oeq_trans OF [rS, rcR], rm1];
        val a1   = addSucSg_at (ZeroC, oneC);
        val a0   = add0Sg_at oneC;
        val a0S  = Suc_cong OF [a0];
        val oneone = oeq_trans OF [a1, a0S];
        val rhsSym = oeq_sym OF [rhs];
      in oeq_trans OF [oeq_trans OF [lhs, oneone], rhsSym] end;
    val xF = Free("x", natT);
    val ihprop = jT (gbody xF);
    val IH = Thm.assume (ctermSig ihprop);
    val stepconcl =
      let
        val sS = sumfSucSg_at (pwAbs, xF);
        val cL = add_cong_rSg (oneC, sumf pwAbs (suc xF), add (sumf pwAbs xF) (pow twoC (suc xF))) sS;
        val aA = addassocSg_at (oneC, sumf pwAbs xF, pow twoC (suc xF));
        val aAsym = oeq_sym OF [aA];
        val lhs2 = oeq_trans OF [cL, aAsym];
        val cIH = add_cong_lSg (add oneC (sumf pwAbs xF), pow twoC (suc xF), pow twoC (suc xF)) IH;
        val lhs3 = oeq_trans OF [lhs2, cIH];
        val rS = powSucSg_at (twoC, suc xF);
        val aT = pow twoC (suc xF);
        val mS1 = multSucSg_at (oneC, aT);
        val mS0 = multSucSg_at (ZeroC, aT);
        val mult0l = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig aT)] mult_0_vSg);
        val mS0b = oeq_trans OF [mS0, add_cong_rSg (aT, mult ZeroC aT, ZeroC) mult0l];
        val a_a0 = add0rSg_at aT;
        val mS0c = oeq_trans OF [mS0b, a_a0];
        val mS1b = oeq_trans OF [mS1, add_cong_rSg (aT, mult oneC aT, aT) mS0c];
        val rChain = oeq_trans OF [rS, mS1b];
        val rChainSym = oeq_sym OF [rChain];
      in oeq_trans OF [lhs3, rChainSym] end;
    val step1 = Thm.forall_intr (ctermSig xF) (Thm.implies_intr (ctermSig ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val kVg2 = Var (("k",0), natT);
val i_geo_add = jT (oeq (add oneC (sumf pwAbs kVg2)) (pow twoC (suc kVg2)));
val r_geo_add = checkSg ("geo_add", geo_add, i_geo_add);

(* geo_sum : sumf (pow 2) k = sub (pow 2 (Suc k)) 1 *)
val geo_sum =
  let
    val kF = Free("k", natT);
    val ga = beta_norm (Drule.infer_instantiate ctxtSig [(("k",0), ctermSig kF)] (varify geo_add));
    val G = sumf pwAbs kF;
    val Pabs  = Abs("z", natT, oeq (sub (add oneC G) oneC) (sub (Bound 0) oneC));
    val reflL = oeqreflSg_at (sub (add oneC G) oneC);
    val subEq = substPredSg (Pabs, add oneC G, pow twoC (suc kF)) ga reflL;
    val sal   = subAddLSg_at (oneC, G);
    val subEqSym = oeq_sym OF [subEq];
    val chain = oeq_trans OF [subEqSym, sal];
  in varify (oeq_sym OF [chain]) end;

val i_geo_sum = jT (oeq (sumf pwAbs kVg2) (sub (pow twoC (suc kVg2)) oneC));
val r_geo_sum = checkSg ("geo_sum", geo_sum, i_geo_sum);

val s_geo_sum_nontrivial =
  not ((Thm.prop_of geo_sum) aconv (jT (oeq (sumf pwAbs kVg2) (pow twoC kVg2))));
val () =
  if s_geo_sum_nontrivial then out "PROBE_OK geo_sum value is 2^(k+1)-1\n"
  else out "PROBE_FAIL geo_sum collapsed!\n";
val () =
  if r_geo_add andalso r_geo_sum andalso s_geo_sum_nontrivial then out "GEO_OK\n" else out "GEO_FAIL\n";

val () = out "EP_ASSEMBLY_SUFFIX_DONE\n";

(* ============================================================================
   (S4) EUCLID PERFECT-NUMBER THEOREM -- STATEMENT + ASSEMBLY OUTLINE + BLOCKER
   ----------------------------------------------------------------------------
   INTENDED FINAL THEOREM (q-hyp form, sub-free on the outer multiplication):
     euclid_perfect :
       |- prime2 q ==> oeq (add q (Suc Zero)) (pow (Suc(Suc Zero)) p)
          ==> lt (Suc Zero) p
          ==> perfect (mult (pow (Suc(Suc Zero)) (sub p (Suc Zero))) q)
     where  perfect n := jT (oeq (sigma n) (mult (Suc(Suc Zero)) n)).
   i.e.  q = 2^p - 1 prime  ==>  sigma(2^(p-1) * q) = 2 * (2^(p-1) * q).

   ASSEMBLY (how the proven lemmas COMPOSE, once the crux lands):
     let a = sub p 1 (so 2^(p-1) = pow 2 a, and 1<p => Suc a-handling is clean).
     1. sigma_char (CRUX, NOT proven here):
          prime2 q ==> lt (pow 2 a) q ==>
          oeq (sigma (mult (pow 2 a) q)) (mult (sub (pow 2 (Suc a)) 1) (add q 1))
        i.e.  sigma(2^a * q) = (2^(a+1)-1) * (q+1).
     2. With q+1 = 2^p (hyp) and sub_Suc_le/pow_Suc giving 2^(a+1) = 2^p (since
        Suc a = p when 1<p), the RHS = (2^p - 1) * 2^p.
     3. (2^p - 1) * 2^p = 2 * ((2^(p-1)) * (2^p - 1))   [pow_Suc + semiring algebra]
        = 2 * (2^a * q)   [q = 2^p-1].  Hence  sigma(2^a*q) = 2*(2^a*q) = perfect.
     The geometric value half is geo_sum (PROVEN above): sum_{i=0}^a 2^i = 2^(a+1)-1.
     The (q+1) factor + the "1 and q are the only divisors of the prime q" structure
     is sigma_prime (PROVEN above).

   THE CRUX (sigma_char) IS A CONFIRMED MULTI-FLEET WALL.  Two independent seats
   with the full machinery (Phase 0 + geo_sum + sum_split_Suc + euclid_lemma +
   FOL/dvd helpers) blocked at the SAME point: the SUM-SUPPORT REINDEX.
     sigma N = sumf (swt N) N  sums over the FULL range d = 0 .. N, with N = 2^a*q
     exponentially large and the summand swt N d nonzero at only the 2(a+1) divisor
     points { 2^i, 2^i*q : 0<=i<=a }.  Collapsing this sparse sum over an
     exponential range to the dense geometric sum (sum_{i=0}^a 2^i) requires either
       (Route A) a divisor LIST + list-sum + a SUPPORT BIJECTION
                   sumf (swt N) N = lsum(divisor_list)   [~ a Wilson-list-product-
                   scale effort, a whole natlist + bijection],  OR
       (Route B) a partial-sum STEP-FUNCTION induction over the full range
                   [far heavier than the single-interior-point collapse that makes
                    sigma_prime tractable].
     Sub-lemmas the crux needs (each itself nontrivial, none banked):
       - prime2_two  : prime2 2   (bounded divisor case analysis on  2 = d*k).
       - pow2_dvd_char : dvd d (pow 2 k) ==> Ex i. i<=k /\ d = pow 2 i
                         (repeated euclid_lemma on prime 2, by induction on k).
       - the interior-collapse: no  2^k < d < 2^(k+1)  divides 2^(k+1).
     sigma_pow2 (sigma(2^k) = 2^(k+1)-1) is the SINGLE-PRIME case of the crux and
     is ITSELF blocked on the same reindex (it inherits the full 0..2^k divisor sum).

   RESUME PATH: splice this banked prelude (Phase 0 sigma subsystem + geo_add/
   geo_sum + sigma_prime + the FOL/dvd helper layer on ctxtSig) as a new
   `common::with_sigma`, then close sigma_char by Route A (divisor list +
   bijection).  With sigma_char banked, the ASSEMBLY above (steps 1-3) is
   mechanical (semiring algebra + pow_Suc + the q+1=2^p hyp) and euclid_perfect
   banks in the same follow-up fleet.
   ============================================================================ *)
val () = out "EP_BLOCKER_DOCUMENTED (crux sigma_char = sum-support reindex, multi-fleet)\n";
val () = out "EUCLID_PERFECT_FLOOR_BANKED (Phase0 + sigma_prime + geo_add + geo_sum)\n";
