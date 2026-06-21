(* ============================================================================
   IF-DIRECTION + FULL IFF for FERMAT'S TWO-SQUARE, on the twosquare monolith
   base (final context ctxtGR / ctermGR).

   This delta is appended AFTER isabelle_twosquare.sml.  It builds a fuller
   toolkit on ctxtGR (extending the minimal `_r` family the monolith ships),
   then proves:
     - brahmagupta (sum-of-two-squares multiplicativity)  [ported]
     - per-prime-power sum-of-two-squares helpers
     - the if-direction by strong induction
     - re-establish only-if on this base
     - the full iff
   ============================================================================ *)

val () = out "IF_TOOLKIT_BEGIN\n";

(* ---- shorthand ---- *)
fun sq x = mult x x;
fun dbl t = add t t;

(* ---- varify every base lemma/axiom onto ctxtGR (suffix _gr) ---- *)
val oeq_refl_gr    = varify oeq_refl;
val oeq_sym_gr     = varify oeq_sym;
val oeq_trans_gr   = varify oeq_trans;
val oeq_subst_gr   = varify oeq_subst;
val Suc_cong_gr    = varify Suc_cong;
val add_0_gr       = varify add_0;
val add_Suc_gr     = varify add_Suc;
val mult_0_gr      = varify mult_0;
val mult_Suc_gr    = varify mult_Suc;
val add_assoc_gr   = varify add_assoc;
val add_comm_gr    = varify add_comm;
val mult_assoc_gr  = varify mult_assoc;
val mult_comm_gr   = varify mult_comm;
val left_distrib_gr  = varify left_distrib;
val right_distrib_gr = varify right_distrib;
val add_left_cancel_gr = varify add_left_cancel;
val mult_1_left_gr = varify mult_1_left;
val mult_1_right_gr= varify mult_1_right;
val le_total_gr    = varify le_total;
val exI_gr         = varify exI_ax;
val exE_gr         = varify exE_ax;
val disjI1_gr      = varify disjI1_ax;
val disjI2_gr      = varify disjI2_ax;
val disjE_gr       = varify disjE_ax;
val pow_Zero_gr    = varify pow_Zero_ax;
val pow_Suc_gr     = varify pow_Suc_ax;

(* ---- ground instantiators on ctxtGR ---- *)
fun oeqRefl_gr t = beta_norm (Drule.infer_instantiate ctxtGR [(("a",0), ctermGR t)] oeq_refl_gr);
fun oeqSym_gr h  = oeq_sym_gr OF [h];
fun oeqTrans_gr (h1,h2) = oeq_trans_gr OF [h1,h2];
fun Suc_cong_gr2 h = Suc_cong_gr OF [h];

fun add0_gr t   = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] add_0_gr);
fun addSuc_gr (mt,nt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt)] add_Suc_gr);
fun mult0_gr t  = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] mult_0_gr);
fun multSuc_gr (mt,nt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt)] mult_Suc_gr);
fun mult1l_gr t = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] mult_1_left_gr);
fun mult1r_gr t = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] mult_1_right_gr);
fun addassoc_gr (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt),(("k",0), ctermGR kt)] add_assoc_gr);
fun addcomm_gr (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt)] add_comm_gr);
fun multassoc_gr (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt),(("k",0), ctermGR kt)] mult_assoc_gr);
fun multcomm_gr (mt,nt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt)] mult_comm_gr);
fun leftdistrib_gr (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtGR [(("x",0), ctermGR mt),(("m",0), ctermGR nt),(("n",0), ctermGR kt)] left_distrib_gr);
fun rightdistrib_gr (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt),(("k",0), ctermGR kt)] right_distrib_gr);
fun powZero_gr t = beta_norm (Drule.infer_instantiate ctxtGR [(("a",0), ctermGR t)] pow_Zero_gr);
fun powSuc_gr (at,nt) = beta_norm (Drule.infer_instantiate ctxtGR [(("a",0), ctermGR at),(("n",0), ctermGR nt)] pow_Suc_gr);

(* oeq_subst rewrite on ctxtGR : oeq a b -> Tp(P a) -> Tp(P b) *)
fun oeq_subst_gr_at (Pabs, aT, bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("P",0), ctermGR Pabs), (("a",0), ctermGR aT), (("b",0), ctermGR bT)] oeq_subst_gr)
  in inst OF [hab, hPa] end;

(* multiplicative / additive congruence on each operand *)
fun mult_cong_l_gr (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT))
  in oeq_subst_gr_at (Pabs, pT, qT) hpq (oeqRefl_gr (mult pT kT)) end;
fun mult_cong_r_gr (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)))
  in oeq_subst_gr_at (Pabs, pT, qT) hpq (oeqRefl_gr (mult hT pT)) end;
fun add_cong_l_gr (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT))
  in oeq_subst_gr_at (Pabs, pT, qT) hpq (oeqRefl_gr (add pT kT)) end;
fun add_cong_r_gr (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)))
  in oeq_subst_gr_at (Pabs, pT, qT) hpq (oeqRefl_gr (add hT pT)) end;

(* exI / exE / disjE / le_total on ctxtGR *)
fun exI_gr_at Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("P",0), ctermGR Pabs), (("a",0), ctermGR at)] exI_gr)
  in Thm.implies_elim inst hbody end;
fun exE_gr_elim (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm  = Thm.assume (ctermGR hypTerm);
    val body    = bodyFn wF hypThm;
    val minor   = Thm.forall_intr (ctermGR wF) (Thm.implies_intr (ctermGR hypTerm) body);
    val exE_inst= beta_norm (Drule.infer_instantiate ctxtGR
                    [(("P",0), ctermGR Pabs), (("Q",0), ctermGR goalC)] exE_gr);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;
fun disjE_gr_elim (At, Bt, Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("A",0), ctermGR At),(("B",0), ctermGR Bt),(("C",0), ctermGR Ct)] disjE_gr)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB end;
fun disjI1_gr_at (At,Bt) h = (beta_norm (Drule.infer_instantiate ctxtGR
      [(("A",0), ctermGR At), (("B",0), ctermGR Bt)] disjI1_gr)) OF [h];
fun disjI2_gr_at (At,Bt) h = (beta_norm (Drule.infer_instantiate ctxtGR
      [(("A",0), ctermGR At), (("B",0), ctermGR Bt)] disjI2_gr)) OF [h];
fun le_total_gr_at (mt, nt) = beta_norm (Drule.infer_instantiate ctxtGR
      [(("m",0), ctermGR mt),(("n",0), ctermGR nt)] le_total_gr);

(* conjI / conjunct on ctxtGR : need conjI_ax / conjunct1_ax / conjunct2_ax varified.
   These live on thyT. Re-varify them. *)
val conjI_gr      = varify conjI_ax;
val conjunct1_gr  = varify conjunct1_ax;
val conjunct2_gr  = varify conjunct2_ax;
fun conjI_gr_at (At,Bt) hA hB =
  (beta_norm (Drule.infer_instantiate ctxtGR [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] conjI_gr)) OF [hA, hB];
fun conjunct1_gr_at (At,Bt) hC =
  (beta_norm (Drule.infer_instantiate ctxtGR [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] conjunct1_gr)) OF [hC];
fun conjunct2_gr_at (At,Bt) hC =
  (beta_norm (Drule.infer_instantiate ctxtGR [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] conjunct2_gr)) OF [hC];

val () = out "IF_TOOLKIT_READY\n";
