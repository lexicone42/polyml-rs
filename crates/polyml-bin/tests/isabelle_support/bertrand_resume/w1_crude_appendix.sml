(* ============================================================================
   W1 CRUDE ROUTE DELTA.  Appended AFTER bertrand_f7_full.sml (ctxtV4/thyV4 live;
   pow_Suc/pow_Zero/pow_add/pow_le_exp/pow_le_mono_base, the (le,lt) order,
   mult_le_mono/mult_le_mono2, rdiv with div_mod_eq/rmod_lt, strong_induct, all the
   _4 helpers + _v4 varified lemmas, mkNum/le_eval/lt_eval/add_eval/mult_eval).

   GOAL : close the CRUDE route — SEB body for ALL s >= S0, NO windows :
     crude_tail : le S0 s ==> le (mult s s)(add n n) ==> lt (add n n)(mult (Suc s)(Suc s))
                  ==> lt (mult (Suc (add n n))(pow (add n n)(Suc s))) (pow 4 (rdiv n 3))

   ROUTE :
     (BL)  bitlen : nat=>nat conservative recursion (bitlen 0 = 0 ; bitlen (Suc m) =
           Suc (bitlen (rdiv (Suc m) 2)))   -> PROVE bitlen_ub : lt m (pow 2 (bitlen m)).
     (LE)  bitlen_le_of_lt : lt m (pow 2 k) ==> le (bitlen m) k   (upper char.).
     (SQ)  bitlen_sq : le (bitlen (mult a a)) (mult 2 (bitlen a)).
     (PP)  pow_pow : oeq (pow (pow a m) e)(pow a (mult m e))      [(a^m)^e = a^(m*e)].
     (TR)  seb_tail_reduce : le ((s+1)^2)(pow 2 b) ==> lt (mult (s+2) b)(mult 2 D)
                             ==> lt (pow ((s+1)^2)(s+2)) (pow 4 D).
     (POLY) polynomial inequality for s>=S0.
     (CT)  crude_tail assembly.

   NEW const bitlen extends thyV4 -> thyBL/ctxtBL/ctermBL ; route every bitlen
   cterm through ctxtBL ; re-instantiate the _v4 varified lemmas on ctxtBL.
   ============================================================================ *)
val () = (Proofterm.proofs := 0);
val () = out "W1_CRUDE_DELTA_BEGIN\n";

(* ---------------------------------------------------------------------------
   (BL.0) bitlen const + conservative recursion axioms ; final context ctxtBL.
   --------------------------------------------------------------------------- *)
val thyBL0 = Sign.add_consts
  [(Binding.name "bitlen", natT --> natT, NoSyn)] thyV4;
val bitlenC = Const (Sign.full_name thyBL0 (Binding.name "bitlen"), natT --> natT);
fun bitlen m = bitlenC $ m;

val twoC = suc (suc ZeroC);   (* 2 *)

(* bitlen 0 = 0 *)
val ((_,bitlen_Zero_ax), thyBL1) = Thm.add_axiom_global (Binding.name "bitlen_Zero",
      jT (oeq (bitlen ZeroC) ZeroC)) thyBL0;
(* bitlen (Suc m) = Suc (bitlen (rdiv (Suc m) 2)) *)
val mBL = Free("m", natT);
val ((_,bitlen_Suc_ax), thyBL) = Thm.add_axiom_global (Binding.name "bitlen_Suc",
      jT (oeq (bitlen (suc mBL)) (suc (bitlen (rdiv (suc mBL) twoC))))) thyBL1;

val ctxtBL  = Proof_Context.init_global thyBL;
val ctermBL = Thm.cterm_of ctxtBL;
fun zhBL th = (length (Thm.hyps_of th) = 0) andalso (null (Thm.extra_shyps th));

val bitlen_Zero_vBL = varify bitlen_Zero_ax;
val bitlen_Suc_vBL  = varify bitlen_Suc_ax;
fun bitlen_Zero_at () = bitlen_Zero_vBL;   (* closed *)
fun bitlen_Suc_at m = beta_norm (Drule.infer_instantiate ctxtBL [(("m",0), ctermBL m)] bitlen_Suc_vBL);

val () = out ("bitlen_Zero : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of bitlen_Zero_vBL) ^ "\n");
val () = out ("bitlen_Suc  : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of bitlen_Suc_vBL) ^ "\n");

(* ---------------------------------------------------------------------------
   (BL.1) re-instantiate the _v4 varified lemmas on ctxtBL (for bitlen-cterms).
   --------------------------------------------------------------------------- *)
val mult_le_mono2_v4 = varify mult_le_mono2;   (* le a b ==> le c d ==> le (mult a c)(mult b d) *)
val pow_Zero_v4_loc  = varify pow_Zero_ax;     (* oeq (pow a 0)(Suc 0) *)
val pow_Suc_v4_loc   = varify pow_Suc_ax;      (* oeq (pow a (Suc n))(mult a (pow a n)) *)
fun oeqreflBL_at t = beta_norm (Drule.infer_instantiate ctxtBL [(("a",0), ctermBL t)] oeq_refl_v4);
fun oeqsymBL h = oeq_sym OF [h];        (* oeq_sym/oeq_trans are theory-poly; reuse *)
val oeqtransBL = oeq_trans;
val Suc_congBL = Suc_cong;

fun substPredBL (Pabs, aT, bT) hab hPa =
  let val subst = beta_norm (Drule.infer_instantiate ctxtBL
        [(("a",0), ctermBL aT),(("b",0), ctermBL bT),(("P",0), ctermBL Pabs)] oeq_subst_v4)
  in Thm.implies_elim (Thm.implies_elim subst hab) hPa end;

fun le_reflBL_at t = beta_norm (Drule.infer_instantiate ctxtBL [(("n",0), ctermBL t)] le_refl_v4);
fun le_transBL_at (mT,nT,kT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtBL
        [(("m",0), ctermBL mT),(("n",0), ctermBL nT),(("k",0), ctermBL kT)] le_trans_v4)
  in (inst OF [h1]) OF [h2] end;
fun le_suc_monoBL_at (mT,nT) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtBL
        [(("m",0), ctermBL mT),(("n",0), ctermBL nT)] le_suc_mono_v4)) h;
fun lt_irreflBL_at t = beta_norm (Drule.infer_instantiate ctxtBL [(("n",0), ctermBL t)] lt_irrefl_v4);
fun nlt_leBL (dT,cT) hneg = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtBL
        [(("d",0), ctermBL dT),(("c",0), ctermBL cT)] nlt_le_v4)) hneg;
fun le_cong_lBL (pT,qT,bT) hpq hle =
  let val zF = Free("zlcBL", natT) val Pabs = Term.lambda zF (le zF bT)
  in substPredBL (Pabs, pT, qT) hpq hle end;
fun le_cong_rBL (aT,pT,qT) hpq hle =
  let val zF = Free("zrcBL", natT) val Pabs = Term.lambda zF (le aT zF)
  in substPredBL (Pabs, pT, qT) hpq hle end;
fun le_totalBL (mt,nt) = beta_norm (Drule.infer_instantiate ctxtBL [(("m",0),ctermBL mt),(("n",0),ctermBL nt)] le_total_v4);
fun le_eq_or_succ_leBL (kt,nt) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtBL [(("k",0),ctermBL kt),(("n",0),ctermBL nt)] le_eq_or_succ_le_v4)) h;
fun le_antisymBL (at,bt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtBL [(("m",0),ctermBL at),(("n",0),ctermBL bt)] le_antisym_v4)
  in (inst OF [h1]) OF [h2] end;
fun mult_le_monoBL (cT,jT_,kT) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtBL
        [(("c",0), ctermBL cT),(("j",0), ctermBL jT_),(("k",0), ctermBL kT)] mult_le_mono_v4)) h;
fun mult_le_mono2BL (aT,bT,cT,dT) hab hcd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtBL
        [(("a",0),ctermBL aT),(("b",0),ctermBL bT),(("c",0),ctermBL cT),(("d",0),ctermBL dT)] mult_le_mono2_v4)
  in (inst OF [hab]) OF [hcd] end;
fun le_add_monoBL (aT,bT,cT) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtBL
        [(("a",0), ctermBL aT),(("b",0), ctermBL bT),(("c",0), ctermBL cT)] le_add_mono_v4)) h;
fun oFalse_elimBL rT = beta_norm (Drule.infer_instantiate ctxtBL [(("R",0), ctermBL rT)] oFalse_elim_v4);
fun disjEBL (At,Bt,Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtBL
        [(("A",0),ctermBL At),(("B",0),ctermBL Bt),(("C",0),ctermBL Ct)] disjE_v4)
  in (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB) end;

fun add0BL_at t = beta_norm (Drule.infer_instantiate ctxtBL [(("n",0), ctermBL t)] add_0_v4);
fun add0r_BL_at t = beta_norm (Drule.infer_instantiate ctxtBL [(("n",0), ctermBL t)] add_0_right_v4);
fun addcommBL_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtBL [(("m",0), ctermBL mt),(("n",0), ctermBL nt)] add_comm_v4);
fun addSucBL_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtBL [(("m",0), ctermBL mt),(("n",0), ctermBL nt)] add_Suc_v4);
fun add_Sr_BL_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtBL [(("m",0), ctermBL mt),(("n",0), ctermBL nt)] add_Suc_right_v4);
fun multSucBL_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtBL [(("m",0), ctermBL mt),(("n",0), ctermBL nt)] mult_Suc_v4);
fun mult_Sr_BL_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtBL [(("n",0), ctermBL mt),(("m",0), ctermBL nt)] mult_Suc_right_v4_);
fun mult0BL_at t = beta_norm (Drule.infer_instantiate ctxtBL [(("n",0), ctermBL t)] mult_0_v4);
fun mult0r_BL_at t = beta_norm (Drule.infer_instantiate ctxtBL [(("n",0), ctermBL t)] mult_0_right_v4);
fun multcommBL_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtBL [(("m",0), ctermBL mt),(("n",0), ctermBL nt)] mult_comm_v4);
fun powZeroBL_at t = beta_norm (Drule.infer_instantiate ctxtBL [(("a",0), ctermBL t)] pow_Zero_v4_loc);
fun powSucBL_at (at,nt) = beta_norm (Drule.infer_instantiate ctxtBL [(("a",0), ctermBL at),(("n",0), ctermBL nt)] pow_Suc_v4_loc);
fun add_cong_lBL (pT,qT,bT) hpq =   (* hpq : oeq p q -> oeq (add p b)(add q b) *)
  let val zF = Free("zalBL", natT) val Pabs = Term.lambda zF (oeq (add pT bT)(add zF bT))
  in substPredBL (Pabs, pT, qT) hpq (oeqreflBL_at (add pT bT)) end;
fun add_cong_rBL (aT,pT,qT) hpq =   (* hpq : oeq p q -> oeq (add a p)(add a q) *)
  let val zF = Free("zarBL", natT) val Pabs = Term.lambda zF (oeq (add aT pT)(add aT zF))
  in substPredBL (Pabs, pT, qT) hpq (oeqreflBL_at (add aT pT)) end;
fun mult_cong_lBL (pT,qT,kT) hpq =  (* hpq : oeq p q -> oeq (mult p k)(mult q k) *)
  let val zF = Free("zmlBL", natT) val Pabs = Term.lambda zF (oeq (mult pT kT)(mult zF kT))
  in substPredBL (Pabs, pT, qT) hpq (oeqreflBL_at (mult pT kT)) end;
fun mult_cong_rBL (hT,pT,qT) hpq =  (* hpq : oeq p q -> oeq (mult h p)(mult h q) *)
  let val zF = Free("zmrBL", natT) val Pabs = Term.lambda zF (oeq (mult hT pT)(mult hT zF))
  in substPredBL (Pabs, pT, qT) hpq (oeqreflBL_at (mult hT pT)) end;
fun bitlen_cong (aT,bT) heq =   (* heq : oeq a b -> oeq (bitlen a)(bitlen b) *)
  let val zF = Free("zblc", natT) val Pabs = Term.lambda zF (oeq (bitlen aT)(bitlen zF))
  in substPredBL (Pabs, aT, bT) heq (oeqreflBL_at (bitlen aT)) end;
fun pow_cong_eBL (pT,iT,jT_) hij =   (* oeq i j -> oeq (pow p i)(pow p j) *)
  let val zF = Free("zpeBL", natT) val Pabs = Term.lambda zF (oeq (pow pT iT)(pow pT zF))
  in substPredBL (Pabs, iT, jT_) hij (oeqreflBL_at (pow pT iT)) end;
fun pow_cong_bBL (pT,qT,kT) hpq =    (* oeq p q -> oeq (pow p k)(pow q k) *)
  let val zF = Free("zpbBL", natT) val Pabs = Term.lambda zF (oeq (pow pT kT)(pow zF kT))
  in substPredBL (Pabs, pT, qT) hpq (oeqreflBL_at (pow pT kT)) end;
(* le_suc_inv : le (Suc a)(Suc b) -> le a b *)
fun le_suc_inv_BL (aT, bT) hS =
  let
    val tot = le_totalBL (aT, bT)
    val hA = Thm.assume (ctermBL (jT (le aT bT)))
    val caseA = Thm.implies_intr (ctermBL (jT (le aT bT))) hA
    val hB = Thm.assume (ctermBL (jT (le bT aT)))
    val leSbSa = le_suc_monoBL_at (bT, aT) hB
    val eqSucs = le_antisymBL (suc aT, suc bT) hS leSbSa
    val eqAB = beta_norm (Drule.infer_instantiate ctxtBL [(("a",0),ctermBL aT),(("b",0),ctermBL bT)] Suc_inj_v4) OF [eqSucs]
    val leAB = le_cong_rBL (aT, aT, bT) eqAB (le_reflBL_at aT)
    val caseB = Thm.implies_intr (ctermBL (jT (le bT aT))) leAB
  in disjEBL (le aT bT, le bT aT, le aT bT) tot caseA caseB end;
(* mp with B = oFalse : neg A (=Imp A oFalse) applied to jT A gives jT oFalse *)
fun mp_BL_oF hImp hA =
  let val Aterm = (case Thm.prop_of hA of _ $ a => a | _ => raise Fail "mp_BL_oF")
      val inst = beta_norm (Drule.infer_instantiate ctxtBL [(("A",0), ctermBL Aterm),(("B",0), ctermBL oFalseC)] mp_v4)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
(* nle_lt_BL : neg (le c d) ==> lt d c (= le (Suc d) c). *)
fun nle_lt_BL (cT, dT) hneg =
  let
    val tot = le_totalBL (suc dT, cT)
    val hA = Thm.assume (ctermBL (jT (le (suc dT) cT)))
    val caseA = Thm.implies_intr (ctermBL (jT (le (suc dT) cT))) hA
    val hB = Thm.assume (ctermBL (jT (le cT (suc dT))))
    val dj = le_eq_or_succ_leBL (cT, suc dT) hB   (* Disj (oeq c (Suc d))(le (Suc c)(Suc d)) *)
    val hEq = Thm.assume (ctermBL (jT (oeq cT (suc dT))))
    val leEq = le_cong_rBL (suc dT, suc dT, cT) (oeqsymBL hEq) (le_reflBL_at (suc dT))
    val caseEq = Thm.implies_intr (ctermBL (jT (oeq cT (suc dT)))) leEq
    val hLt = Thm.assume (ctermBL (jT (le (suc cT)(suc dT))))
    val le_c_d = le_suc_inv_BL (cT, dT) hLt
    val ff = mp_BL_oF hneg le_c_d
    val anyg = oFalse_elimBL (le (suc dT) cT) OF [ff]
    val caseLt = Thm.implies_intr (ctermBL (jT (le (suc cT)(suc dT)))) anyg
    val underB = disjEBL (oeq cT (suc dT), le (suc cT)(suc dT), le (suc dT) cT) dj caseEq caseLt
    val caseB = Thm.implies_intr (ctermBL (jT (le cT (suc dT)))) underB
  in disjEBL (le (suc dT) cT, le cT (suc dT), le (suc dT) cT) tot caseA caseB end;

fun pow_le_expBL (pt,it,jt_) hpos hle =
  let val inst = beta_norm (Drule.infer_instantiate ctxtBL [(("p",0),ctermBL pt),(("i",0),ctermBL it),(("j",0),ctermBL jt_)] pow_le_exp_v4)
  in (inst OF [hpos]) OF [hle] end;
fun pow_le_mono_baseBL (at,bt,nt) hle =
  let val inst = beta_norm (Drule.infer_instantiate ctxtBL [(("a",0),ctermBL at),(("b",0),ctermBL bt),(("n",0),ctermBL nt)] pow_le_mono_base_v4)
  in inst OF [hle] end;
fun pow_addBL_at (at,mt,nt) = beta_norm (Drule.infer_instantiate ctxtBL [(("a",0),ctermBL at),(("m",0),ctermBL mt),(("n",0),ctermBL nt)] pow_add_v4);

fun div_mod_eqBL (aT,pT) hpos = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtBL
        [(("a",0), ctermBL aT),(("p",0), ctermBL pT)] div_mod_eq_v4)) hpos;
fun rmod_ltBL (aT,pT) hpos = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtBL
        [(("a",0), ctermBL aT),(("p",0), ctermBL pT)] rmod_lt_v4)) hpos;

(* le_intro on ctxtBL : le m n from oeq n (add m w) *)
fun le_introBL (mT, nT, w) hyp =
  let val Pabs = Abs("p", natT, oeq nT (add mT (Bound 0)))
  in (beta_norm (Drule.infer_instantiate ctxtBL [(("P",0), ctermBL Pabs),(("a",0), ctermBL w)] exI_v4)) OF [hyp] end;
fun le_zeroBL_at t = le_introBL (ZeroC, t, t) (oeqsymBL (add0BL_at t));
fun le_suc_selfBL_at nt =   (* le n (Suc n) *)
  let val eqn = oeqsymBL (oeqtransBL OF [add_Sr_BL_at (nt, ZeroC), Suc_congBL OF [add0r_BL_at nt]])
                (* oeq (Suc n)(add n (Suc 0)) ; add n (Suc 0) = Suc(add n 0) = Suc n *)
  in le_introBL (nt, suc nt, suc ZeroC) eqn end;

fun impI_BL (At, Bt) hImpThm =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtBL [(("A",0),ctermBL At),(("B",0),ctermBL Bt)]
    impI_v4)) hImpThm;

fun strong_induct_BL (Pabs, kT) hStep =
  let val inst = beta_norm (Drule.infer_instantiate ctxtBL [(("P",0), ctermBL Pabs),(("k",0), ctermBL kT)] strong_induct_v4)
  in Thm.implies_elim inst hStep end;

(* exE_elim on ctxtBL *)
fun exE_elimBL (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT)
    val hypTerm = jT (Term.betapply (Pabs, wF))
    val hypThm  = Thm.assume (ctermBL hypTerm)
    val bdy     = bodyFn wF hypThm
    val minor   = Thm.forall_intr (ctermBL wF) (Thm.implies_intr (ctermBL hypTerm) bdy)
    val exE_inst= beta_norm (Drule.infer_instantiate ctxtBL
                    [(("P",0), ctermBL Pabs), (("Q",0), ctermBL goalC)] exE_v4)
    val partial = Thm.implies_elim exE_inst exThm
  in Thm.implies_elim partial minor end;

fun disj_zero_or_sucBL t =
  beta_norm (Drule.infer_instantiate ctxtBL [(("p",0), ctermBL t)] disj_zero_or_suc_v4);

val () = out "BL_HELPERS_DEFINED\n";

(* sanity smoke : a trivial bitlen rewrite through ctxtBL *)
val () =
  (let val th = bitlen_Suc_at (mkNum 0)   (* bitlen 1 = Suc(bitlen (rdiv 1 2)) *)
   in out ("BL smoke bitlen_Suc(0) : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of th) ^ "\n") end)
  handle e => out ("BL smoke EXN : " ^ General.exnMessage e ^ "\n");

val () = out "W1_CRUDE_BLHEADER_DONE\n";

(* le_add on ctxtBL : le m (add m p) *)
fun le_addBL_at (mT,pT) = beta_norm (Drule.infer_instantiate ctxtBL [(("m",0), ctermBL mT),(("p",0), ctermBL pT)] le_add_v4);

(* numeral lt/le helpers on ctxtBL : le 1 2 = lt 0 2, etc. (route le_eval through ctxtBL) *)
fun le_evalBL ai bi =
  let val aT = mkNum ai val w = mkNum (bi - ai)
      val (r, th) = add_eval aT w   (* add_eval uses ctxtV4 congs; oeq is theory-poly, fine on BL *)
  in le_introBL (aT, r, w) (oeqsymBL th) end;
fun lt_evalBL ai bi = le_evalBL (ai+1) bi;

(* mult 2 x = add x x  (on ctxtBL) :  mult 2 x = x + mult 1 x = x + (x + mult 0 x) = x + (x + 0) = x + x *)
fun mult2_is_double_BL x =
  let
    val ms2 = multSucBL_at (suc ZeroC, x)     (* oeq (mult 2 x)(add x (mult 1 x)) *)
    val ms1 = multSucBL_at (ZeroC, x)         (* oeq (mult 1 x)(add x (mult 0 x)) *)
    val m0  = mult0BL_at x                     (* oeq (mult 0 x) 0 *)
    val inner = oeqtransBL OF [ms1, oeqtransBL OF [add_cong_rBL (x, mult ZeroC x, ZeroC) m0, add0r_BL_at x]]
                (* oeq (mult 1 x) x *)
  in oeqtransBL OF [ms2, add_cong_rBL (x, mult (suc ZeroC) x, x) inner] end;   (* oeq (mult 2 x)(add x x) *)

val () = out "BL_NUM_HELPERS_DEFINED\n";

(* ---------------------------------------------------------------------------
   half_lt : lt (rdiv (Suc k) 2) (Suc k)   for all k.
   --------------------------------------------------------------------------- *)
val lt0_2_BL = lt_evalBL 0 2;   (* le 1 2 = lt 0 2 *)

fun half_lt kT =
  let
    val Sk = suc kT
    val h  = rdiv Sk twoC
    val r  = rmod Sk twoC
    (* Suc k = 2*h + r *)
    val dme = div_mod_eqBL (Sk, twoC) lt0_2_BL      (* oeq (Suc k)(add (mult 2 h) r) *)
    (* le (mult 2 h)(add (mult 2 h) r) = le (mult 2 h)(Suc k) *)
    val le2h_sum = le_addBL_at (mult twoC h, r)      (* le (mult 2 h)(add (mult 2 h) r) *)
    val le2h_Sk  = le_cong_rBL (mult twoC h, add (mult twoC h) r, Sk) (oeqsymBL dme) le2h_sum   (* le (mult 2 h)(Suc k) *)
    (* prove neg (lt k h) : suppose le (Suc k) h. *)
    val hAss = Thm.assume (ctermBL (jT (le (suc kT) h)))   (* lt k h = le (Suc k) h *)
    val m2le = mult_le_monoBL (twoC, suc kT, h) hAss        (* le (mult 2 (Suc k))(mult 2 h) *)
    val le_2Sk_Sk = le_transBL_at (mult twoC Sk, mult twoC h, Sk) m2le le2h_Sk   (* le (mult 2 (Suc k))(Suc k) *)
    (* lt (Suc k)(mult 2 (Suc k)) : mult 2 (Suc k) = Suc k + Suc k >= Suc k + 1 = Suc(Suc k) *)
    val dbl = mult2_is_double_BL Sk                         (* oeq (mult 2 (Suc k))(add Sk Sk) *)
    (* le (Suc Sk)(add Sk Sk) : Suc Sk = Sk + 1 <= Sk + Sk  [le_add_mono with le 1 Sk] *)
    val le1Sk = le_suc_monoBL_at (ZeroC, kT) (le_zeroBL_at kT)   (* le 1 (Suc k) *)
    val leAdd = le_add_monoBL (suc ZeroC, Sk, Sk) le1Sk    (* le (add 1 Sk)(add Sk Sk) *)
    (* add 1 Sk = Suc Sk *)
    val a1Sk = oeqtransBL OF [addSucBL_at (ZeroC, Sk), Suc_congBL OF [add0BL_at Sk]]   (* oeq (add 1 Sk)(Suc Sk) *)
    val leSucSk_sum = le_cong_lBL (add (suc ZeroC) Sk, suc Sk, add Sk Sk) a1Sk leAdd   (* le (Suc Sk)(add Sk Sk) *)
    val leSucSk_m2 = le_cong_rBL (suc Sk, add Sk Sk, mult twoC Sk) (oeqsymBL dbl) leSucSk_sum   (* le (Suc Sk)(mult 2 Sk) = lt Sk (mult 2 Sk) *)
    (* chain : le (Suc Sk)(mult 2 Sk) and le (mult 2 Sk)(Sk) -> le (Suc Sk) Sk = lt Sk Sk -> oFalse *)
    val ltself = le_transBL_at (suc Sk, mult twoC Sk, Sk) leSucSk_m2 le_2Sk_Sk   (* le (Suc Sk)(Sk) *)
    val ff = lt_irreflBL_at Sk OF [ltself]
    val hngMeta = Thm.implies_intr (ctermBL (jT (le (suc kT) h))) ff   (* (lt k h) ==> oFalse *)
    val hng = impI_BL (lt kT h, oFalseC) hngMeta   (* neg (lt k h) *)
    val le_h_k = nlt_leBL (kT, h) hng   (* le h k *)
  in le_suc_monoBL_at (h, kT) le_h_k end;   (* le (Suc h)(Suc k) = lt h (Suc k) *)

val () =
  (let val kF = Free("k_hl", natT)
       val th = half_lt kF
   in out ("half_lt smoke : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of th) ^ "\n") end)
  handle e => out ("half_lt EXN : " ^ General.exnMessage e ^ "\n");
val () = out "BL_HALFLT_DONE\n";

(* ---------------------------------------------------------------------------
   (BL) bitlen_ub : lt m (pow 2 (bitlen m))   [m < 2^bitlen m]   by strong induction.
     m = 0     : 0 < 2^(bitlen 0) = 2^0 = 1.
     m = Suc k : h := rdiv (Suc k) 2.  IH at h (half_lt : h < Suc k) gives h < 2^(bitlen h),
       i.e. le (Suc h)(2^bitlen h).  Suc k = 2h + r, r < 2 so r <= 1, so Suc k <= 2h+1 < 2(h+1)
       = 2*Suc h <= 2*2^bitlen h = 2^(Suc(bitlen h)) = 2^(bitlen(Suc k)).
   --------------------------------------------------------------------------- *)
val ub_pred = Term.lambda (Free("m_ub", natT)) (lt (Free("m_ub",natT)) (pow twoC (bitlen (Free("m_ub",natT)))));

(* le (Suc r) 2 ==> le r 1  : from rmod < 2 get rmod <= 1 (le_suc_inv style). *)
fun le1_of_lt2 rT hlt =   (* hlt : lt r 2 = le (Suc r) 2 ; result le r 1 *)
  le_suc_inv_BL (rT, suc ZeroC) hlt;

val bitlen_ub =
  let
    fun stepFn nF (gThm : thm) =   (* gThm : !!m. lt m nF ==> lt m (pow 2 (bitlen m)) ; goal lt nF (pow 2 (bitlen nF)) *)
      let
        (* case split nF = 0 or nF = Suc k *)
        val dz = disj_zero_or_sucBL nF   (* Disj (oeq nF 0)(Ex q. oeq nF (Suc q)) *)
        val goalC = lt nF (pow twoC (bitlen nF))
        val caseZ =
          let val hz = Thm.assume (ctermBL (jT (oeq nF ZeroC)))
              val bz = bitlen_Zero_vBL                       (* oeq (bitlen 0) 0 *)
              val pz = powZeroBL_at twoC                      (* oeq (pow 2 0)(Suc 0) *)
              val lt01 = le_reflBL_at (suc ZeroC)            (* le 1 1 = lt 0 (Suc 0) *)
              (* lt 0 (pow 2 0) : rewrite (Suc 0) RHS -> (pow 2 0) via sym pz *)
              val lt0_p20 = le_cong_rBL (suc ZeroC, suc ZeroC, pow twoC ZeroC) (oeqsymBL pz) lt01   (* le 1 (pow 2 0) = lt 0 (pow 2 0) *)
              (* lt 0 (pow 2 (bitlen 0)) : rewrite exponent 0 -> bitlen 0 via sym bz *)
              val zEz = Free("zEz", natT)
              val Pexp0 = Term.lambda zEz (lt ZeroC (pow twoC zEz))
              val lt0_p2b0 = substPredBL (Pexp0, ZeroC, bitlen ZeroC) (oeqsymBL bz) lt0_p20   (* lt 0 (pow 2 (bitlen 0)) *)
              (* rewrite 0 -> nF using sym hz : oeq 0 nF *)
              val zEn = Free("zEn", natT)
              val Pgoal = Term.lambda zEn (lt zEn (pow twoC (bitlen zEn)))
              val g = substPredBL (Pgoal, ZeroC, nF) (oeqsymBL hz) lt0_p2b0
          in Thm.implies_intr (ctermBL (jT (oeq nF ZeroC))) g end
        val PabsQ = Abs("q_ub", natT, oeq nF (suc (Bound 0)))
        val caseS =
          let val hex = Thm.assume (ctermBL (jT (mkEx PabsQ)))
              fun body kF (hk : thm) =   (* hk : oeq nF (Suc k) *)
                let
                  val Sk = suc kF
                  val h  = rdiv Sk twoC
                  val r  = rmod Sk twoC
                  (* IH at h : need lt h Sk = half_lt k ; apply gThm... but gThm needs lt h nF.
                     nF = Suc k (via hk).  half_lt gives lt h (Suc k).  rewrite Suc k -> nF. *)
                  val lt_h_Sk = half_lt kF                  (* lt h (Suc k) *)
                  val zF2 = Free("zih", natT)
                  val lt_h_nF = substPredBL (Term.lambda zF2 (lt h zF2), Sk, nF) (oeqsymBL hk) lt_h_Sk   (* lt h nF *)
                  val ihAt = Thm.forall_elim (ctermBL h) gThm   (* lt h nF ==> lt h (pow 2 (bitlen h)) *)
                  val ihH = Thm.implies_elim ihAt lt_h_nF       (* lt h (pow 2 (bitlen h)) = le (Suc h)(pow 2 (bitlen h)) *)
                  (* Suc k = 2h + r *)
                  val dme = div_mod_eqBL (Sk, twoC) lt0_2_BL   (* oeq (Suc k)(add (mult 2 h) r) *)
                  val rlt = rmod_ltBL (Sk, twoC) lt0_2_BL      (* lt r 2 = le (Suc r) 2 *)
                  val r_le1 = le1_of_lt2 r rlt                  (* le r 1 *)
                  (* Suc k = 2h + r <= 2h + 1  [le_add_mono on r<=1, left fixed 2h] *)
                  val le_2hr_2h1 = le_add_monoBL (r, suc ZeroC, mult twoC h) r_le1   (* le (add r (2h))(add 1 (2h)) *)
                  (* but dme is add (2h) r ; commute *)
                  val cm = addcommBL_at (mult twoC h, r)         (* oeq (add (2h) r)(add r (2h)) *)
                  val sk_eq_radd = oeqtransBL OF [dme, cm]       (* oeq (Suc k)(add r (2h)) *)
                  val le_Sk_2h1 = le_cong_lBL (add r (mult twoC h), Sk, add (suc ZeroC) (mult twoC h)) (oeqsymBL sk_eq_radd) le_2hr_2h1
                                  (* le (Suc k)(add 1 (2h)) *)
                  (* add 1 (2h) = Suc (2h) *)
                  val a1_2h = oeqtransBL OF [addSucBL_at (ZeroC, mult twoC h), Suc_congBL OF [add0BL_at (mult twoC h)]]   (* oeq (add 1 (2h))(Suc(2h)) *)
                  val le_Sk_S2h = le_cong_rBL (Sk, add (suc ZeroC) (mult twoC h), suc (mult twoC h)) a1_2h le_Sk_2h1   (* le (Suc k)(Suc(2h)) *)
                  (* 2*Suc h = 2h + 2 ; want Suc(2h) < 2*Suc h, i.e. le (Suc(Suc(2h)))(2*Suc h) *)
                  (* 2*(Suc h) = add (Suc h)(Suc h) [double] = Suc(add (Suc h) h)... compute: = Suc(Suc(add h h)) *)
                  val dblSh = mult2_is_double_BL (suc h)         (* oeq (mult 2 (Suc h))(add (Suc h)(Suc h)) *)
                  (* add (Suc h)(Suc h) = Suc(add h (Suc h)) = Suc(Suc(add h h)) *)
                  val e1 = addSucBL_at (h, suc h)                (* oeq (add (Suc h)(Suc h))(Suc(add h (Suc h))) *)
                  val e2 = add_Sr_BL_at (h, h)                   (* oeq (add h (Suc h))(Suc(add h h)) *)
                  val addShSh = oeqtransBL OF [e1, Suc_congBL OF [e2]]   (* oeq (add (Suc h)(Suc h))(Suc(Suc(add h h))) *)
                  (* 2h = add h h *)
                  val twoh = mult2_is_double_BL h                (* oeq (mult 2 h)(add h h) *)
                  (* Suc(2h) = Suc(add h h) *)
                  val S2h_eq = Suc_congBL OF [twoh]              (* oeq (Suc(2h))(Suc(add h h)) *)
                  (* le (Suc(Suc(2h)))(2*Suc h) : Suc(Suc(2h)) = Suc(Suc(add h h)) = add(Suc h)(Suc h) = 2*Suc h *)
                  val SS2h_eq = Suc_congBL OF [S2h_eq]           (* oeq (Suc(Suc(2h)))(Suc(Suc(add h h))) *)
                  val SS2h_to_2Sh = oeqtransBL OF [SS2h_eq, oeqtransBL OF [oeqsymBL addShSh, oeqsymBL dblSh]]   (* oeq (Suc(Suc(2h)))(mult 2 (Suc h)) *)
                  (* le (Suc(Suc(2h)))(mult 2 (Suc h)) via refl + cong *)
                  val le_SS2h_2Sh = le_cong_rBL (suc (suc (mult twoC h)), suc (suc (mult twoC h)), mult twoC (suc h)) SS2h_to_2Sh (le_reflBL_at (suc (suc (mult twoC h))))
                  (* le (Suc(Suc k))(Suc(Suc(2h))) from le (Suc k)(Suc(2h)) [le_suc_mono] *)
                  val le_SSk_SS2h = le_suc_monoBL_at (suc kF, suc (mult twoC h)) le_Sk_S2h   (* le (Suc(Suc k))(Suc(Suc(2h))) *)
                  (* le (Suc(Suc k))(mult 2 (Suc h)) *)
                  val le_SSk_2Sh = le_transBL_at (suc (suc kF), suc (suc (mult twoC h)), mult twoC (suc h)) le_SSk_SS2h le_SS2h_2Sh
                  (* note Suc(Suc k) = Suc(Suc k) ; we want le (Suc(Suc k))(...) where Suc k = nF -> stays *)
                  (* 2*Suc h <= 2 * 2^bitlen h = 2^(Suc bitlen h) : mult_le_mono 2 (Suc h <= 2^bitlen h) *)
                  (* ihH : le (Suc h)(pow 2 (bitlen h)) *)
                  val le_2Sh_2pow = mult_le_monoBL (twoC, suc h, pow twoC (bitlen h)) ihH   (* le (mult 2 (Suc h))(mult 2 (pow 2 (bitlen h))) *)
                  (* mult 2 (pow 2 (bitlen h)) = pow 2 (Suc(bitlen h)) [pow_Suc sym] *)
                  val pSuc = powSucBL_at (twoC, bitlen h)        (* oeq (pow 2 (Suc(bitlen h)))(mult 2 (pow 2 (bitlen h))) *)
                  val le_2Sh_powS = le_cong_rBL (mult twoC (suc h), mult twoC (pow twoC (bitlen h)), pow twoC (suc (bitlen h))) (oeqsymBL pSuc) le_2Sh_2pow
                                    (* le (mult 2 (Suc h))(pow 2 (Suc(bitlen h))) *)
                  (* chain : le (Suc(Suc k))(2*Suc h) and le (2*Suc h)(2^(Suc bitlen h)) -> le (Suc(Suc k))(2^(Suc bitlen h)) *)
                  val le_SSk_powS = le_transBL_at (suc (suc kF), mult twoC (suc h), pow twoC (suc (bitlen h))) le_SSk_2Sh le_2Sh_powS
                                    (* le (Suc(Suc k))(pow 2 (Suc(bitlen h))) = lt (Suc k)(pow 2 (Suc(bitlen h))) *)
                  (* pow 2 (Suc(bitlen h)) = pow 2 (bitlen (Suc k)) [bitlen_Suc sym] *)
                  val blSk = bitlen_Suc_at kF                    (* oeq (bitlen (Suc k))(Suc(bitlen (rdiv (Suc k) 2))) = Suc(bitlen h) *)
                  (* rewrite exponent Suc(bitlen h) -> bitlen(Suc k) on RHS *)
                  val zF3 = Free("zexp", natT)
                  val Pexp = Term.lambda zF3 (le (suc (suc kF)) (pow twoC zF3))
                  val le_SSk_powBl = substPredBL (Pexp, suc (bitlen h), bitlen Sk) (oeqsymBL blSk) le_SSk_powS
                                     (* le (Suc(Suc k))(pow 2 (bitlen (Suc k))) = lt (Suc k)(pow 2 (bitlen(Suc k))) *)
                  (* rewrite Suc k -> nF via hk *)
                  val zF4 = Free("znf", natT)
                  val Pnf = Term.lambda zF4 (lt zF4 (pow twoC (bitlen zF4)))
                  val g = substPredBL (Pnf, Sk, nF) (oeqsymBL hk) le_SSk_powBl
                in g end
          in Thm.implies_intr (ctermBL (jT (mkEx PabsQ))) (exE_elimBL (PabsQ, goalC) hex "k_ub" body) end
      in disjEBL (oeq nF ZeroC, mkEx PabsQ, goalC) dz caseZ caseS end
    (* assemble strong_induct's H : !!n. (!!m. lt m n ==> P m) ==> P n *)
    val nF = Free("n_ub", natT)
    val Gprop =
      let val mB = Free("m_g_ub", natT)
      in Logic.all mB (Logic.mk_implies (jT (lt mB nF), jT (lt mB (pow twoC (bitlen mB))))) end
    val Gthm = Thm.assume (ctermBL Gprop)
    val Pn   = stepFn nF Gthm
    val Hbody = Thm.implies_intr (ctermBL Gprop) Pn
    val Hthm  = Thm.forall_intr (ctermBL nF) Hbody
    val kF = Free("k_ub_top", natT)
    val concl = strong_induct_BL (ub_pred, kF) Hthm   (* P k = lt k (pow 2 (bitlen k)) *)
  in varify concl end;

val () = out ("bitlen_ub 0hyp=" ^ Bool.toString (zhBL bitlen_ub) ^ "\n");
val () = out ("bitlen_ub : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of bitlen_ub) ^ "\n");
(* instantiator : bitlen_ub at a term ; the schematic var of bitlen_ub (whatever its
   name) is the SOLE Var, so instantiate by position-free dest. *)
val bitlen_ub_var = hd (Term.add_vars (Thm.prop_of bitlen_ub) []);   (* (indexname, T) *)
fun bitlen_ub_at t = beta_norm (Drule.infer_instantiate ctxtBL [(fst bitlen_ub_var, ctermBL t)] bitlen_ub);
val () =
  (let val mF = Free("m_chk_ub", natT)
   in out ("bitlen_ub_at(m) : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of (bitlen_ub_at mF)) ^ "\n") end)
  handle e => out ("bitlen_ub_at EXN : " ^ General.exnMessage e ^ "\n");
val bitlen_ub_aconv =
  let val mF = Free("m_chk_ub", natT)
      val got = Thm.prop_of (bitlen_ub_at mF)
      val want = jT (lt mF (pow twoC (bitlen mF)))
  in got aconv want end;
val () = out ("bitlen_ub aconv(at m)=" ^ Bool.toString bitlen_ub_aconv ^ "\n");
val bitlen_ok = zhBL bitlen_ub andalso bitlen_ub_aconv;
val () = if bitlen_ok then out "BITLEN_OK\n" else out "BITLEN_FAIL\n";
val () = out "W1_CRUDE_BITLEN_DONE\n";

(* ---------------------------------------------------------------------------
   Object-logic BL helpers (forall/imp/mp/nat_induct) for the LE stage.
   --------------------------------------------------------------------------- *)
val allI_v4_l_BL = varify allI_ax;
fun allI_BL_pre Pabs hAllThm =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtBL [(("P",0), ctermBL Pabs)] allI_v4_l_BL)) hAllThm;
fun allI_BL Pabs bodyThmFn =
  let val dF = Free("d_aiBL", natT) val body = bodyThmFn dF
  in allI_BL_pre Pabs (Thm.forall_intr (ctermBL dF) body) end;
fun allE_BL Pabs at hForall =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtBL [(("P",0), ctermBL Pabs),(("a",0), ctermBL at)] allE_v4)) hForall;
fun mp_BL (At, Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtBL [(("A",0), ctermBL At),(("B",0), ctermBL Bt)] mp_v4)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun nat_induct_BL (Pabs, kT) =
  beta_norm (Drule.infer_instantiate ctxtBL [(("P",0), ctermBL Pabs),(("k",0), ctermBL kT)] nat_induct_v4);

val () = out "BL_OBJLOGIC_HELPERS_DEFINED\n";

(* ---------------------------------------------------------------------------
   (LE) bitlen_le_of_lt : lt m (pow 2 k) ==> le (bitlen m) k.
   Proof by nat_induct on k of  Q k := Forall m. Imp (lt m (pow 2 k))(le (bitlen m) k).
   --------------------------------------------------------------------------- *)
(* Q-predicate as a unary nat=>o abstraction over k. *)
val mQ = Free("m_le", natT);
fun Qbody k = mkForall (Term.lambda mQ (mkImp (lt mQ (pow twoC k))(le (bitlen mQ) k)));
val Qpred = Term.lambda (Free("k_le", natT)) (Qbody (Free("k_le", natT)));

(* base : Q 0 = Forall m. Imp (lt m (pow 2 0))(le (bitlen m) 0).
   lt m (pow 2 0) = lt m 1 = le (Suc m) 1.  This forces m = 0 (else le (Suc(Suc j)) 1 false).
   Then bitlen m = bitlen 0 = 0 = k. *)
val Qbase =
  let
    fun bodyFor mF =   (* prove Imp (lt mF (pow 2 0))(le (bitlen mF) 0) *)
      let
        val hlt = Thm.assume (ctermBL (jT (lt mF (pow twoC ZeroC))))   (* le (Suc m)(pow 2 0) *)
        (* pow 2 0 = Suc 0 *)
        val pz = powZeroBL_at twoC                  (* oeq (pow 2 0)(Suc 0) *)
        val hlt1 = le_cong_rBL (suc mF, pow twoC ZeroC, suc ZeroC) pz hlt   (* le (Suc m)(Suc 0) *)
        (* le (Suc m)(Suc 0) -> le m 0 [le_suc_inv] -> m = 0 *)
        val le_m_0 = le_suc_inv_BL (mF, ZeroC) hlt1   (* le m 0 *)
        (* le m 0 -> oeq m 0 : witness, m = 0 + w and ... use le_antisym with le 0 m *)
        val eq_m_0 = le_antisymBL (mF, ZeroC) le_m_0 (le_zeroBL_at mF)   (* oeq m 0 *)
        (* bitlen m = bitlen 0 = 0 ; goal le (bitlen m) 0 *)
        val blm_eq = oeqtransBL OF [bitlen_cong (mF, ZeroC) eq_m_0, bitlen_Zero_vBL]   (* oeq (bitlen m) 0 *)
        val g = le_cong_lBL (ZeroC, bitlen mF, ZeroC) (oeqsymBL blm_eq) (le_reflBL_at ZeroC)   (* le (bitlen m) 0 *)
        val impThm = Thm.implies_intr (ctermBL (jT (lt mF (pow twoC ZeroC)))) g
      in impI_BL (lt mF (pow twoC ZeroC), le (bitlen mF) ZeroC) impThm end
    val Pabs0 = Term.lambda mQ (mkImp (lt mQ (pow twoC ZeroC))(le (bitlen mQ) ZeroC))
  in allI_BL Pabs0 bodyFor end;

val () = out "BL_LE_BASE_DEFINED\n";

(* step : !!k'. Q k' ==> Q (Suc k').  Given m with lt m (pow 2 (Suc k')), prove le (bitlen m)(Suc k'). *)
fun Qstep kpF QkThm =   (* QkThm : Forall m. Imp (lt m (pow 2 k'))(le (bitlen m) k') *)
  let
    val Sk = suc kpF
    fun bodyFor mF =
      let
        val hlt = Thm.assume (ctermBL (jT (lt mF (pow twoC Sk))))   (* le (Suc m)(pow 2 (Suc k')) *)
        val goalLe = le (bitlen mF) Sk
        (* case m = 0 or m = Suc j *)
        val dz = disj_zero_or_sucBL mF
        val caseZ =
          let val hz = Thm.assume (ctermBL (jT (oeq mF ZeroC)))
              (* bitlen m = bitlen 0 = 0 <= Suc k' *)
              val blm_eq = oeqtransBL OF [bitlen_cong (mF, ZeroC) hz, bitlen_Zero_vBL]   (* oeq (bitlen m) 0 *)
              val le0Sk = le_zeroBL_at Sk    (* le 0 (Suc k') *)
              val g = le_cong_lBL (ZeroC, bitlen mF, Sk) (oeqsymBL blm_eq) le0Sk   (* le (bitlen m)(Suc k') *)
          in Thm.implies_intr (ctermBL (jT (oeq mF ZeroC))) g end
        val PabsJ = Abs("j_le", natT, oeq mF (suc (Bound 0)))
        val caseS =
          let val hex = Thm.assume (ctermBL (jT (mkEx PabsJ)))
              fun body jF (hj : thm) =   (* hj : oeq m (Suc j) *)
                let
                  val Sj = suc jF
                  val h  = rdiv Sj twoC
                  (* lt m (pow 2 (Suc k')) ; rewrite m -> Suc j *)
                  val zF = Free("zmj", natT)
                  val Pm = Term.lambda zF (lt zF (pow twoC Sk))
                  val hlt_Sj = substPredBL (Pm, mF, Sj) hj hlt   (* le (Suc (Suc j))(pow 2 (Suc k')) = lt (Suc j)(pow 2 (Suc k')) *)
                  (* pow 2 (Suc k') = mult 2 (pow 2 k') *)
                  val pS = powSucBL_at (twoC, kpF)               (* oeq (pow 2 (Suc k'))(mult 2 (pow 2 k')) *)
                  val hlt_Sj2 = le_cong_rBL (suc Sj, pow twoC Sk, mult twoC (pow twoC kpF)) pS hlt_Sj
                                (* le (Suc(Suc j))(mult 2 (pow 2 k')) = lt (Suc j)(mult 2 (pow 2 k')) *)
                  (* need lt h (pow 2 k') : 2h <= Suc j < 2*(pow 2 k') -> h < pow 2 k'. *)
                  (* Suc j = 2h + r, le (mult 2 h)(Suc j) *)
                  val dme = div_mod_eqBL (Sj, twoC) lt0_2_BL     (* oeq (Suc j)(add (mult 2 h) r) where r = rmod (Suc j) 2 *)
                  val r  = rmod Sj twoC
                  val le2h_Sj = le_cong_rBL (mult twoC h, add (mult twoC h) r, Sj) (oeqsymBL dme) (le_addBL_at (mult twoC h, r))   (* le (mult 2 h)(Suc j) *)
                  (* le (Suc(mult 2 h))(Suc(Suc j)) ... actually want : 2h < 2*(pow 2 k').  From le (mult 2 h)(Suc j) and lt (Suc j)(mult 2 (pow 2 k')) :
                     le (Suc (mult 2 h))(Suc(Suc j)) [le_suc_mono] ; le (Suc(Suc j))(mult 2 (pow 2 k')) [hlt_Sj2 = le (Suc(Suc j))(...)] -> le (Suc(mult 2 h))(mult 2 (pow 2 k')) = lt (mult 2 h)(mult 2 (pow 2 k')). *)
                  val leS2h_SSj = le_suc_monoBL_at (mult twoC h, Sj) le2h_Sj   (* le (Suc(mult 2 h))(Suc(Suc j)) *)
                  val lt_2h_2pk = le_transBL_at (suc (mult twoC h), suc Sj, mult twoC (pow twoC kpF)) leS2h_SSj hlt_Sj2
                                  (* le (Suc(mult 2 h))(mult 2 (pow 2 k')) = lt (mult 2 h)(mult 2 (pow 2 k')) *)
                  (* lt (mult 2 h)(mult 2 (pow 2 k')) -> lt h (pow 2 k')  [cancel factor 2 : mult_lt_cancel].
                     Derive via contradiction : suppose le (pow 2 k') h.  Then mult 2 (pow 2 k') <= mult 2 h [mult_le_mono],
                     contradicting lt (mult 2 h)(mult 2 (pow 2 k')). *)
                  (* lt (mult 2 h)(mult 2 X) -> lt h X  via : neg(le X h) (else 2X<=2h contra) then nle_lt. *)
                  val lt_h_pk_clean =
                    let
                      val X = pow twoC kpF
                      val hXh = Thm.assume (ctermBL (jT (le X h)))                 (* X <= h *)
                      val m2 = mult_le_monoBL (twoC, X, h) hXh                      (* le (mult 2 X)(mult 2 h) *)
                      val ltself = le_transBL_at (suc (mult twoC h), mult twoC X, mult twoC h) lt_2h_2pk m2   (* le (Suc(2h))(2h) *)
                      val ff = lt_irreflBL_at (mult twoC h) OF [ltself]
                      val negXh = impI_BL (le X h, oFalseC) (Thm.implies_intr (ctermBL (jT (le X h))) ff)   (* neg (le X h) *)
                    in nle_lt_BL (X, h) negXh end   (* lt h X = le (Suc h) X *)
                  (* bitlen m = bitlen (Suc j) = Suc (bitlen h) *)
                  val blSj = bitlen_Suc_at jF                    (* oeq (bitlen (Suc j))(Suc(bitlen h)) *)
                  val blm = oeqtransBL OF [bitlen_cong (mF, Sj) hj, blSj]   (* oeq (bitlen m)(Suc(bitlen h)) *)
                  (* Q k' at h : le (bitlen h) k' from lt h (pow 2 k') *)
                  val QkAtH = allE_BL (Term.lambda mQ (mkImp (lt mQ (pow twoC kpF))(le (bitlen mQ) kpF))) h QkThm
                              (* Imp (lt h (pow 2 k'))(le (bitlen h) k') *)
                  val le_blh_kp = mp_BL (lt h (pow twoC kpF), le (bitlen h) kpF) QkAtH lt_h_pk_clean   (* le (bitlen h) k' *)
                  val le_Sblh_Sk = le_suc_monoBL_at (bitlen h, kpF) le_blh_kp   (* le (Suc(bitlen h))(Suc k') *)
                  (* rewrite bitlen m -> Suc(bitlen h) on LHS *)
                  val g = le_cong_lBL (suc (bitlen h), bitlen mF, Sk) (oeqsymBL blm) le_Sblh_Sk   (* le (bitlen m)(Suc k') *)
                in g end
          in Thm.implies_intr (ctermBL (jT (mkEx PabsJ))) (exE_elimBL (PabsJ, goalLe) hex "j_le" body) end
        val gImp = disjEBL (oeq mF ZeroC, mkEx PabsJ, goalLe) dz caseZ caseS
      in impI_BL (lt mF (pow twoC Sk), goalLe) (Thm.implies_intr (ctermBL (jT (lt mF (pow twoC Sk)))) gImp) end
    val PabsS = Term.lambda mQ (mkImp (lt mQ (pow twoC Sk))(le (bitlen mQ) Sk))
  in allI_BL PabsS bodyFor end;

(* assemble : nat_induct on k of Q ; then specialise to get the meta form. *)
val bitlen_le_of_lt =
  let
    val kTop = Free("k_le_top", natT)
    val indThm = nat_induct_BL (Qpred, kTop)   (* Q 0 ==> (!!x. Q x ==> Q(Suc x)) ==> Q kTop *)
    (* step as a meta-rule : !!x. Q x ==> Q (Suc x) *)
    val xF = Free("x_le_step", natT)
    val QxProp = jT (Qbody xF)
    val Qx = Thm.assume (ctermBL QxProp)
    val QSx = Qstep xF Qx
    val stepMeta = Thm.forall_intr (ctermBL xF) (Thm.implies_intr (ctermBL QxProp) QSx)
    val QkTop = Thm.implies_elim (Thm.implies_elim indThm Qbase) stepMeta   (* Q kTop = Forall m. Imp (lt m (2^kTop))(le (bitlen m) kTop) *)
    (* specialise : for a Free m, get the object Imp, then to META form lt m (2^k) ==> le (bitlen m) k. *)
    val mF = Free("m_le_fin", natT)
    val PabsK = Term.lambda mQ (mkImp (lt mQ (pow twoC kTop))(le (bitlen mQ) kTop))
    val impAtM = allE_BL PabsK mF QkTop   (* Imp (lt m (2^kTop))(le (bitlen m) kTop) *)
    (* to meta : assume jT(lt m (2^kTop)), mp -> le (bitlen m) kTop, then discharge *)
    val hLt = Thm.assume (ctermBL (jT (lt mF (pow twoC kTop))))
    val leRes = mp_BL (lt mF (pow twoC kTop), le (bitlen mF) kTop) impAtM hLt
    val metaForm = Thm.implies_intr (ctermBL (jT (lt mF (pow twoC kTop)))) leRes
  in varify metaForm end;

val () = out ("bitlen_le_of_lt 0hyp=" ^ Bool.toString (zhBL bitlen_le_of_lt) ^ "\n");
val () = out ("bitlen_le_of_lt : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of bitlen_le_of_lt) ^ "\n");
(* instantiator *)
val ble_vars = Term.add_vars (Thm.prop_of bitlen_le_of_lt) [];
fun bitlen_le_of_lt_at (mT, kT) hlt =
  let
    (* find the m-var and k-var by their position : the conclusion le (bitlen ?m) ?k ; premise lt ?m (pow 2 ?k) *)
    val inst = beta_norm (Drule.infer_instantiate ctxtBL
                 (map (fn (ix as (nm,_), _) =>
                          if nm = "m_le_fin" then (ix, ctermBL mT)
                          else (ix, ctermBL kT)) ble_vars)
                 bitlen_le_of_lt)
  in Thm.implies_elim inst hlt end;
val () =
  (let val mF = Free("mm", natT) val kF = Free("kk", natT)
       val hlt = Thm.assume (ctermBL (jT (lt mF (pow twoC kF))))
       val th = bitlen_le_of_lt_at (mF, kF) hlt
   in out ("bitlen_le_of_lt_at smoke : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of th) ^ "\n") end)
  handle e => out ("bitlen_le_of_lt_at EXN : " ^ General.exnMessage e ^ "\n");
val le_ok = zhBL bitlen_le_of_lt;
val () = if le_ok then out "BITLEN_LE_OK\n" else out "BITLEN_LE_FAIL\n";
val () = out "W1_CRUDE_LE_DONE\n";

(* ===========================================================================
   (PP) pow_pow : oeq (pow (pow a m) e)(pow a (mult m e))   by nat_induct on e.
   =========================================================================== *)
val pow_pow =
  (let
    val aF = Free("a_pp", natT) val mF = Free("m_pp", natT)
    (* predicate over e : oeq (pow (pow a m) e)(pow a (mult m e)) *)
    val Ppp = Term.lambda (Free("e_pp", natT)) (oeq (pow (pow aF mF)(Free("e_pp",natT)))(pow aF (mult mF (Free("e_pp",natT)))))
    val eTop = Free("e_pp_top", natT)
    val indThm = nat_induct_BL (Ppp, eTop)
    (* base : e=0 : pow (pow a m) 0 = 1 = pow a 0 = pow a (m*0) *)
    val base =
      let
        val l0 = powZeroBL_at (pow aF mF)          (* oeq (pow (pow a m) 0)(Suc 0) *)
        val r0 = powZeroBL_at aF                    (* oeq (pow a 0)(Suc 0) *)
        val m00 = mult0r_BL_at mF                   (* oeq (mult m 0) 0 *)
        (* pow a (mult m 0) = pow a 0 [cong exp] = Suc 0 *)
        val pe = oeqtransBL OF [pow_cong_eBL (aF, mult mF ZeroC, ZeroC) m00, r0]   (* oeq (pow a (mult m 0))(Suc 0) *)
      in oeqtransBL OF [l0, oeqsymBL pe] end       (* oeq (pow (pow a m) 0)(pow a (mult m 0)) *)
    (* step : !!e'. P e' ==> P (Suc e') *)
    val ePF = Free("ep_pp", natT)
    val IHprop = jT (oeq (pow (pow aF mF) ePF)(pow aF (mult mF ePF)))
    val IH = Thm.assume (ctermBL IHprop)
    val stepConcl =
      let
        val Se = suc ePF
        val pS = powSucBL_at (pow aF mF, ePF)       (* oeq (pow (pow a m)(Suc e'))(mult (pow a m)(pow (pow a m) e')) *)
        (* rewrite inner pow (pow a m) e' -> pow a (m*e') via IH *)
        val rwInner = mult_cong_rBL (pow aF mF, pow (pow aF mF) ePF, pow aF (mult mF ePF)) IH
                      (* oeq (mult (pow a m)(pow (pow a m) e'))(mult (pow a m)(pow a (m*e'))) *)
        val lhs2 = oeqtransBL OF [pS, rwInner]      (* oeq (pow (pow a m)(Suc e'))(mult (pow a m)(pow a (m*e'))) *)
        (* mult (pow a m)(pow a (m*e')) = pow a (add m (m*e')) [pow_add sym] *)
        val pa = pow_addBL_at (aF, mF, mult mF ePF)  (* oeq (pow a (add m (m*e')))(mult (pow a m)(pow a (m*e'))) *)
        val lhs3 = oeqtransBL OF [lhs2, oeqsymBL pa]  (* oeq (pow (pow a m)(Suc e'))(pow a (add m (m*e'))) *)
        (* add m (m*e') = m*(Suc e') [mult_Sr sym] *)
        val msr = mult_Sr_BL_at (mF, ePF)            (* oeq (mult m (Suc e'))(add m (mult m e')) *)
        val rwexp = pow_cong_eBL (aF, add mF (mult mF ePF), mult mF Se) (oeqsymBL msr)
                    (* oeq (pow a (add m (m*e')))(pow a (m*(Suc e'))) *)
      in oeqtransBL OF [lhs3, rwexp] end            (* oeq (pow (pow a m)(Suc e'))(pow a (m*(Suc e'))) *)
    val stepMeta = Thm.forall_intr (ctermBL ePF) (Thm.implies_intr (ctermBL IHprop) stepConcl)
    val concl = Thm.implies_elim (Thm.implies_elim indThm base) stepMeta   (* P eTop *)
   in SOME (varify concl) end)
  handle e => (out ("pow_pow EXN : " ^ General.exnMessage e ^ "\n"); NONE);

val () = (case pow_pow of SOME th => out ("pow_pow 0hyp=" ^ Bool.toString (zhBL th) ^ " : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of th) ^ "\n")
                        | NONE => out "pow_pow NONE\n");
(* instantiator : pow_pow_at (a,m,e) *)
fun pow_pow_at (aT,mT,eT) = (case pow_pow of
    SOME th => let val vs = Term.add_vars (Thm.prop_of th) []
                   (* vars : a_pp, m_pp, e_pp_top *)
                   fun pick (ix as (nm,_), _) = if nm="a_pp" then (ix, ctermBL aT) else if nm="m_pp" then (ix, ctermBL mT) else (ix, ctermBL eT)
               in beta_norm (Drule.infer_instantiate ctxtBL (map pick vs) th) end
  | NONE => raise Fail "pow_pow unavailable");
val pp_ok = (case pow_pow of SOME th => zhBL th | NONE => false);
val () = if pp_ok then out "POW_POW_OK\n" else out "POW_POW_FAIL\n";
val () = out "W1_CRUDE_PP_DONE\n";

(* ===========================================================================
   (SQ) bitlen_sq : le (bitlen (mult a a))(mult 2 (bitlen a)).
   a*a < (Suc a)^2 <= (2^bla)^2 = 2^bla*2^bla = 2^(2 bla) ; bitlen_le_of_lt.
   =========================================================================== *)
val bitlen_sq =
  (let
    val aF = Free("a_sq", natT)
    val bla = bitlen aF
    val ub = bitlen_ub_at aF          (* lt a (pow 2 bla) = le (Suc a)(pow 2 bla) *)
    (* le ((Suc a)*(Suc a))((2^bla)*(2^bla)) *)
    val mlm = mult_le_mono2BL (suc aF, pow twoC bla, suc aF, pow twoC bla) ub ub
              (* le (mult (Suc a)(Suc a))(mult (pow 2 bla)(pow 2 bla)) *)
    (* a*a < (Suc a)^2 *)
    val sqlt = sq_lt_succ_4 aF        (* le (Suc(mult a a))(mult (Suc a)(Suc a)) = lt (a*a)((Suc a)^2) *)
    val lt_aa_pp = le_transBL_at (suc (mult aF aF), mult (suc aF)(suc aF), mult (pow twoC bla)(pow twoC bla)) sqlt mlm
                   (* le (Suc(a*a))(mult (2^bla)(2^bla)) = lt (a*a)(mult (2^bla)(2^bla)) *)
    (* mult (2^bla)(2^bla) = pow 2 (add bla bla) [pow_add sym] *)
    val pa = pow_addBL_at (twoC, bla, bla)   (* oeq (pow 2 (add bla bla))(mult (pow 2 bla)(pow 2 bla)) *)
    val lt_aa_padd = le_cong_rBL (suc (mult aF aF), mult (pow twoC bla)(pow twoC bla), pow twoC (add bla bla)) (oeqsymBL pa) lt_aa_pp
                     (* lt (a*a)(pow 2 (add bla bla)) *)
    (* add bla bla = mult 2 bla *)
    val dbl = mult2_is_double_BL bla   (* oeq (mult 2 bla)(add bla bla) *)
    val lt_aa_2bla = le_cong_rBL (suc (mult aF aF), pow twoC (add bla bla), pow twoC (mult twoC bla)) (pow_cong_eBL (twoC, add bla bla, mult twoC bla) (oeqsymBL dbl)) lt_aa_padd
                     (* lt (a*a)(pow 2 (mult 2 bla)) *)
    (* bitlen_le_of_lt : le (bitlen (a*a))(mult 2 bla) *)
    val g = bitlen_le_of_lt_at (mult aF aF, mult twoC bla) lt_aa_2bla
   in SOME (varify g) end)
  handle e => (out ("bitlen_sq EXN : " ^ General.exnMessage e ^ "\n"); NONE);

val () = (case bitlen_sq of SOME th => out ("bitlen_sq 0hyp=" ^ Bool.toString (zhBL th) ^ " : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of th) ^ "\n")
                          | NONE => out "bitlen_sq NONE\n");
fun bitlen_sq_at aT = (case bitlen_sq of
    SOME th => let val vs = Term.add_vars (Thm.prop_of th) []
               in beta_norm (Drule.infer_instantiate ctxtBL (map (fn (ix,_) => (ix, ctermBL aT)) vs) th) end
  | NONE => raise Fail "bitlen_sq unavailable");
val sq_ok = (case bitlen_sq of SOME th => zhBL th | NONE => false);
val () = if sq_ok then out "BITLEN_SQ_OK\n" else out "BITLEN_SQ_FAIL\n";
val () = out "W1_CRUDE_SQ_DONE\n";

(* ===========================================================================
   helpers for TR : pow4_eq on BL ; pow2_pos_BL : le 1 (pow 2 x).
   =========================================================================== *)
val pow4_eq_vBL = varify pow4_eq;   (* oeq (pow 2 (add n n))(pow 4 n) *)
fun pow4_eq_BL nT = beta_norm (Drule.infer_instantiate ctxtBL [(("n",0),ctermBL nT)] pow4_eq_vBL);
val fourCBL = suc (suc (suc (suc ZeroC)));   (* 4 *)

val pow2_pos_BL =   (* le 1 (pow 2 x) for all x (a nat=>o induction) *)
  let
    val Pp = Term.lambda (Free("x_p2p", natT)) (le (suc ZeroC) (pow twoC (Free("x_p2p",natT))))
    val xTop = Free("x_p2p_top", natT)
    val indThm = nat_induct_BL (Pp, xTop)
    val base =   (* le 1 (pow 2 0) : pow 2 0 = 1, le 1 1 *)
      let val p0 = powZeroBL_at twoC   (* oeq (pow 2 0)(Suc 0) *)
      in le_cong_rBL (suc ZeroC, suc ZeroC, pow twoC ZeroC) (oeqsymBL p0) (le_reflBL_at (suc ZeroC)) end
    val xF = Free("x_p2p_s", natT)
    val IHp = jT (le (suc ZeroC)(pow twoC xF))
    val IH = Thm.assume (ctermBL IHp)
    val step =
      let
        (* pow 2 (Suc x) = mult 2 (pow 2 x) ; le 1 (pow 2 x) -> le 1 (mult 2 (pow 2 x)) since mult 2 y >= y >= 1 *)
        val pS = powSucBL_at (twoC, xF)   (* oeq (pow 2 (Suc x))(mult 2 (pow 2 x)) *)
        (* mult 2 (pow 2 x) = add (pow 2 x)(pow 2 x) ; le 1 (pow 2 x) -> le 1 (add ..) via le_trans le (pow 2 x)(add ..) *)
        val dbl = mult2_is_double_BL (pow twoC xF)   (* oeq (mult 2 (pow 2 x))(add (pow 2 x)(pow 2 x)) *)
        val le_y_2y = le_addBL_at (pow twoC xF, pow twoC xF)   (* le (pow 2 x)(add (pow 2 x)(pow 2 x)) *)
        val le1_2y = le_transBL_at (suc ZeroC, pow twoC xF, add (pow twoC xF)(pow twoC xF)) IH le_y_2y   (* le 1 (add ..) *)
        val le1_m2 = le_cong_rBL (suc ZeroC, add (pow twoC xF)(pow twoC xF), mult twoC (pow twoC xF)) (oeqsymBL dbl) le1_2y   (* le 1 (mult 2 (pow 2 x)) *)
      in le_cong_rBL (suc ZeroC, mult twoC (pow twoC xF), pow twoC (suc xF)) (oeqsymBL pS) le1_m2 end   (* le 1 (pow 2 (Suc x)) *)
    val stepMeta = Thm.forall_intr (ctermBL xF) (Thm.implies_intr (ctermBL IHp) step)
  in Thm.implies_elim (Thm.implies_elim indThm base) stepMeta end;
fun pow2_pos_BL_at t = beta_norm (Drule.infer_instantiate ctxtBL [((("x_p2p_top",0)), ctermBL t)] (varify pow2_pos_BL));

val () = out ("pow2_pos_BL 0hyp=" ^ Bool.toString (zhBL (varify pow2_pos_BL)) ^ "\n");
val () = out "BL_TR_HELPERS_DEFINED\n";

(* ===========================================================================
   (TR) seb_tail_reduce :
     le (mult (Suc s)(Suc s))(pow 2 b) ==> lt (mult (Suc(Suc s)) b)(mult 2 D)
     ==> lt (pow (mult (Suc s)(Suc s))(Suc(Suc s)))(pow 4 D).
   =========================================================================== *)
fun seb_tail_reduce (sT, bT, DT) hKle hPoly =
  let
    val K = mult (suc sT)(suc sT)        (* (s+1)^2 *)
    val E = suc (suc sT)                  (* s+2 *)
    val twoD = mult twoC DT
    (* 1. le (pow K E)(pow (2^b) E) *)
    val pmono = pow_le_mono_baseBL (K, pow twoC bT, E) hKle   (* le (pow K E)(pow (2^b) E) *)
    (* 2. pow (2^b) E = pow 2 (b*E) *)
    val pp = pow_pow_at (twoC, bT, E)    (* oeq (pow (pow 2 b) E)(pow 2 (mult b E)) *)
    val le_KE_2bE = le_cong_rBL (pow K E, pow (pow twoC bT) E, pow twoC (mult bT E)) pp pmono   (* le (pow K E)(pow 2 (mult b E)) *)
    (* 3. hPoly : lt (mult E b)(2*D) = le (Suc(mult E b))(2*D).  Need lt (mult b E)(2*D) : commute. *)
    val cm = multcommBL_at (E, bT)       (* oeq (mult E b)(mult b E) *)
    (* rewrite : le (Suc(mult E b))(2D) -> le (Suc(mult b E))(2D) via Suc cong on (mult E b -> mult b E) *)
    val hPoly_be2 = le_cong_lBL (suc (mult E bT), suc (mult bT E), twoD) (Suc_congBL OF [cm]) hPoly   (* le (Suc(mult b E))(2D) = lt (mult b E)(2D) *)
    (* 4. lt (pow 2 (mult b E))(pow 2 (2D)) : 2^(b*E) < 2^(Suc(b*E)) <= 2^(2D). *)
    (* 2^(Suc(b*E)) = mult 2 (2^(b*E)) = add (2^(b*E))(2^(b*E)) ; lt (2^(b*E))(add..) needs le 1 (2^(b*E)). *)
    val y = pow twoC (mult bT E)
    val pSy = powSucBL_at (twoC, mult bT E)   (* oeq (pow 2 (Suc(b*E)))(mult 2 y) *)
    val dbly = mult2_is_double_BL y           (* oeq (mult 2 y)(add y y) *)
    val pos_y = pow2_pos_BL_at (mult bT E)    (* le 1 y *)
    (* lt y (add y y) = le (Suc y)(add y y) : Suc y = y + 1 <= y + y [le_add_mono with le 1 y] *)
    val leAdd = le_add_monoBL (suc ZeroC, y, y) pos_y   (* le (add 1 y)(add y y) *)
    val a1y = oeqtransBL OF [addSucBL_at (ZeroC, y), Suc_congBL OF [add0BL_at y]]   (* oeq (add 1 y)(Suc y) *)
    val leSy_yy = le_cong_lBL (add (suc ZeroC) y, suc y, add y y) a1y leAdd   (* le (Suc y)(add y y) *)
    val leSy_m2 = le_cong_rBL (suc y, add y y, mult twoC y) (oeqsymBL dbly) leSy_yy   (* le (Suc y)(mult 2 y) *)
    val lt_y_pS = le_cong_rBL (suc y, mult twoC y, pow twoC (suc (mult bT E))) (oeqsymBL pSy) leSy_m2   (* le (Suc y)(pow 2 (Suc(b*E))) = lt y (pow 2 (Suc(b*E))) *)
    (* 2^(Suc(b*E)) <= 2^(2D) [pow_le_exp from Suc(b*E) <= 2D] *)
    val le_SbE_2D = hPoly_be2   (* le (Suc(mult b E))(2D) *)
    val lt0_2 = lt_evalBL 0 2   (* lt 0 2 = le 1 2 *)
    val pexp = pow_le_expBL (twoC, suc (mult bT E), twoD) lt0_2 le_SbE_2D   (* le (pow 2 (Suc(b*E)))(pow 2 (2D)) *)
    val lt_y_2D = le_transBL_at (suc y, pow twoC (suc (mult bT E)), pow twoC twoD) lt_y_pS pexp   (* le (Suc y)(pow 2 (2D)) = lt y (pow 2 (2D)) *)
    (* 5. pow 2 (2D) = pow 4 D : 2D = D+D *)
    val dblD = mult2_is_double_BL DT          (* oeq (mult 2 D)(add D D) *)
    val p4 = pow4_eq_BL DT                     (* oeq (pow 2 (add D D))(pow 4 D) *)
    val lt_y_padd = le_cong_rBL (suc y, pow twoC twoD, pow twoC (add DT DT)) (pow_cong_eBL (twoC, twoD, add DT DT) dblD) lt_y_2D   (* lt y (pow 2 (add D D)) *)
    val lt_y_4D = le_cong_rBL (suc y, pow twoC (add DT DT), pow fourCBL DT) p4 lt_y_padd   (* lt y (pow 4 D) *)
    (* 6. chain : le (pow K E) y and lt y (pow 4 D) -> lt (pow K E)(pow 4 D). *)
    (* le (Suc(pow K E))(Suc y) [le_suc_mono of le_KE_2bE] ; le (Suc y)(pow 4 D) [lt_y_4D] -> le (Suc(pow K E))(pow 4 D). *)
    val g = le_transBL_at (suc (pow K E), suc y, pow fourCBL DT) (le_suc_monoBL_at (pow K E, y) le_KE_2bE) lt_y_4D
            (* le (Suc(pow K E))(pow 4 D) = lt (pow K E)(pow 4 D) *)
  in g end;

(* TR smoke + gate *)
val seb_tail_reduce_thm =
  (let
     val sF = Free("s_tr", natT) val bF = Free("b_tr", natT) val DF = Free("D_tr", natT)
     val hKle = Thm.assume (ctermBL (jT (le (mult (suc sF)(suc sF))(pow twoC bF))))
     val hPoly = Thm.assume (ctermBL (jT (lt (mult (suc (suc sF)) bF)(mult twoC DF))))
     val th = seb_tail_reduce (sF, bF, DF) hKle hPoly
     val d2 = Thm.implies_intr (ctermBL (jT (lt (mult (suc (suc sF)) bF)(mult twoC DF)))) th
     val d1 = Thm.implies_intr (ctermBL (jT (le (mult (suc sF)(suc sF))(pow twoC bF)))) d2
   in SOME (varify d1) end)
  handle e => (out ("seb_tail_reduce EXN : " ^ General.exnMessage e ^ "\n"); NONE);
val () = (case seb_tail_reduce_thm of
    SOME th => out ("seb_tail_reduce 0hyp=" ^ Bool.toString (zhBL th) ^ " : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of th) ^ "\n")
  | NONE => out "seb_tail_reduce NONE\n");
val tr_ok = (case seb_tail_reduce_thm of SOME th => zhBL th | NONE => false);
val () = if tr_ok then out "SEB_TAIL_REDUCE_OK\n" else out "SEB_TAIL_REDUCE_FAIL\n";
val () = out "W1_CRUDE_TR_DONE\n";

(* ===========================================================================
   (POLY) the polynomial inequality  (s+2)*bitlen((s+1)^2) < 2*rdiv n 3  for s>=S0.
   ----------------------------------------------------------------------------
   STATUS : the genuine analytic WALL, NOT closed.  HONEST report (no fabricated
   axiom / lemma — a smuggled polynomial inequality would be FATAL).

   Tools available + PROVED (all 0-hyp on ctxtBL) :
     bitlen_ub     : lt m (pow 2 (bitlen m))            [BITLEN_OK]
     bitlen_le_of_lt : lt m (pow 2 k) ==> le (bitlen m) k [BITLEN_LE_OK]
     bitlen_sq     : le (bitlen (mult a a))(mult 2 (bitlen a)) [BITLEN_SQ_OK]
     pow_pow       : oeq (pow (pow a m) e)(pow a (mult m e))   [POW_POW_OK]
     seb_tail_reduce : le ((s+1)^2)(2^b) ==> lt ((s+2)*b)(2*D) ==> lt (((s+1)^2)^(s+2))(4^D) [SEB_TAIL_REDUCE_OK]

   The OBSTRUCTION : to bound b = bitlen((s+1)^2) <= 2*bitlen(s+1), and then bound
   bitlen(s+1) by a SUB-LINEAR function of s symbolically (s ranging over [S0,inf)).
   - bitlen_le_of_lt requires a NUMERAL/closed exponent k with (s+1) < 2^k ; the only
     symbolic such k is k = s+1 (since s+1 < 2^(s+1)), giving the LINEAR bound
     bitlen(s+1) <= s+1, hence b <= 2(s+1) and (s+2)*b <= 2(s+1)(s+2) ~ 2 s^2.
   - the RHS 2*rdiv n 3, with s*s <= 2n, lower-bounds only as ~ s^2/3.
   - 2 s^2  <  s^2/3  is FALSE for every s : the LINEAR bitlen bound is too weak,
     and no numeral S0 rescues it.
   The TRUE bound bitlen(s+1) ~ log2(s+1) is correct (the math holds : sub-exp < exp)
   but is NOT extractable as a polynomial term at symbolic s with the discrete toolkit
   (it is exactly the log, obtained only by unrolling the bitlen halving-recursion s/2
   times — not a single kernel inequality).  The standard Isabelle Bertrand proof
   (Eberl/Biehler) uses REAL-VALUED ln estimates precisely here ; a faithful discrete
   analogue needs a "bitlen-grows-like-log" lemma  le (bitlen m)(Suc (bitlen (rdiv m 2)))
   chained against a real/rational logarithm bound — a multi-fleet real-analysis layer,
   beyond this kernel-only fleet.

   We therefore DO NOT close POLY and DO NOT assert it.  S0 is left OPEN for the crude
   route : with only the discrete bitlen toolkit, NO numeral S0 makes POLY provable
   (the log bound is required for all S0).  Piece B's higher-window range [35, S0) is
   thus the ENTIRE tail [35, inf) unless the log layer is added.
   =========================================================================== *)
val () = out "POLY_BLOCKED : (s+2)*bitlen((s+1)^2) < 2*rdiv n 3 needs a SUB-LINEAR (logarithmic) symbolic bound on bitlen(s+1) ; the discrete toolkit gives only the LINEAR bitlen(s+1)<=s+1 (b<=2(s+1), (s+2)*b ~ 2s^2 >> s^2/3 ~ 2*rdiv n 3) ; NO numeral S0 rescues it. The log layer (real ln estimates a la Eberl/Biehler, or a bitlen<=1+bitlen(m/2) unroll) is a separate real-analysis fleet. NOT asserted (no fabricated inequality).\n";
val () = out "POLY_INEQ_FAIL\n";
val () = out "S0_OPEN : no workable numeral S0 with the discrete bitlen toolkit (log bound required for all S0).\n";
val () = out "W1_CRUDE_POLY_DONE\n";

(* ===========================================================================
   (CT) crude_tail : BLOCKED on POLY.  We bank the ASSEMBLY plumbing : GIVEN a
   proof  hPolyHyp : lt (mult (Suc(Suc s)) (bitlen (mult (Suc s)(Suc s))))(mult 2 (rdiv n 3)),
   crude_tail closes (seb_reduce + seb_tail_reduce + bitlen_ub).  This shows POLY is
   the SOLE missing input — the analytic content is fully reduced to it.
   crude_tail_given_poly :
     le S0 s ==> le (mult s s)(add n n) ==> lt (add n n)(mult (Suc s)(Suc s))
       ==> [POLY n s] ==> lt (mult (Suc 2n)(pow 2n (Suc s)))(pow 4 (rdiv n 3)).
   (seb_reduce re-derived on ctxtBL below.)
   =========================================================================== *)
(* seb_reduce re-derived on ctxtBL (pure pow algebra ; from bertrand_w1_appendix). *)
fun seb_reduce (sT, nT) hSsq =   (* hSsq : jT (lt (add n n)(mult (Suc s)(Suc s))) *)
  let
    val twoN = add nT nT
    val K    = mult (suc sT)(suc sT)
    val le_S2n_K = hSsq                       (* le (Suc 2n) K *)
    val le_2n_K  = le_transBL_at (twoN, suc twoN, K) (le_suc_selfBL_at twoN) le_S2n_K   (* le 2n K *)
    val powmono = pow_le_mono_baseBL (twoN, K, suc sT) le_2n_K   (* le (pow 2n (Suc s))(pow K (Suc s)) *)
    val mlm = mult_le_mono2BL (suc twoN, K, pow twoN (suc sT), pow K (suc sT)) le_S2n_K powmono
              (* le (mult (Suc 2n)(pow 2n (Suc s)))(mult K (pow K (Suc s))) *)
    val pSucK = powSucBL_at (K, suc sT)   (* oeq (pow K (Suc(Suc s)))(mult K (pow K (Suc s))) *)
    val g = le_cong_rBL (mult (suc twoN)(pow twoN (suc sT)), mult K (pow K (suc sT)), pow K (suc (suc sT)))
              (oeqsymBL pSucK) mlm
  in g end;

val crude_tail_given_poly =
  (let
     val sF = Free("s_ct", natT) val nF = Free("n_ct", natT)
     val twoN = add nF nF
     val K = mult (suc sF)(suc sF)        (* (s+1)^2 *)
     val b = bitlen K
     val DT = rdiv nF (suc (suc (suc ZeroC)))   (* rdiv n 3 *)
     (* hyps *)
     val hSsq = Thm.assume (ctermBL (jT (lt twoN K)))   (* 2n < (s+1)^2 *)
     val hPoly = Thm.assume (ctermBL (jT (lt (mult (suc (suc sF)) b)(mult twoC DT))))   (* (s+2)*b < 2*(n/3) *)
     (* seb_reduce (lifts from V4) : le ((2n+1)*(2n)^(Suc s)) ((s+1)^2)^(s+2) *)
     val sr = seb_reduce (sF, nF) hSsq
              (* le (mult (Suc 2n)(pow 2n (Suc s)))(pow K (Suc(Suc s))) *)
     (* bitlen_ub at K : lt K (2^b) -> le K (2^b) *)
     val ubK = bitlen_ub_at K    (* lt K (pow 2 b) = le (Suc K)(pow 2 b) *)
     val leK_2b = le_transBL_at (K, suc K, pow twoC b) (le_suc_selfBL_at K) ubK   (* le K (pow 2 b) *)
     (* seb_tail_reduce (s,b,D) leK_2b hPoly : lt (pow K (Suc(Suc s)))(pow 4 D) *)
     val tr = seb_tail_reduce (sF, b, DT) leK_2b hPoly
              (* le (Suc(pow K (Suc(Suc s))))(pow 4 D) = lt (pow K (Suc(Suc s)))(pow 4 D) *)
     (* chain : le (LHS)(pow K (Suc(Suc s))) and lt (pow K (Suc(Suc s)))(pow 4 D) -> lt LHS (pow 4 D). *)
     val LHS = mult (suc twoN)(pow twoN (suc sF))
     val g = le_transBL_at (suc LHS, suc (pow K (suc (suc sF))), pow fourCBL DT)
               (le_suc_monoBL_at (LHS, pow K (suc (suc sF))) sr) tr
             (* le (Suc LHS)(pow 4 D) = lt LHS (pow 4 D) *)
     (* discharge hyps *)
     val d2 = Thm.implies_intr (ctermBL (jT (lt (mult (suc (suc sF)) b)(mult twoC DT)))) g
     val d1 = Thm.implies_intr (ctermBL (jT (lt twoN K))) d2
   in SOME (varify d1) end)
  handle e => (out ("crude_tail_given_poly EXN : " ^ General.exnMessage e ^ "\n"); NONE);
val () = (case crude_tail_given_poly of
    SOME th => out ("crude_tail_given_poly 0hyp=" ^ Bool.toString (zhBL th) ^ " : " ^ Syntax.string_of_term ctxtBL (Thm.prop_of th) ^ "\n")
  | NONE => out "crude_tail_given_poly NONE\n");
val ctgp_ok = (case crude_tail_given_poly of SOME th => zhBL th | NONE => false);
val () = if ctgp_ok then out "CRUDE_TAIL_GIVEN_POLY_OK (crude_tail reduced to POLY as the SOLE residual)\n" else out "CRUDE_TAIL_GIVEN_POLY_FAIL\n";
val () = out "CRUDE_TAIL_FAIL (blocked on POLY ; no fabricated inequality asserted)\n";
val () = out "W1_CRUDE_CT_DONE\n";

(* ===========================================================================
   AXIOM AUDIT : only ex_middle classical + bitlen's two conservative recursion
   eqns (bitlen_Zero, bitlen_Suc).  NO smuggled inequality/crude/bertrand axiom.
   =========================================================================== *)
val () =
  let
    val thy = Proof_Context.theory_of ctxtBL
    val axs = Theory.all_axioms_of thy
    val names = map fst axs
    val hasEM = List.exists (fn s => String.isSubstring "ex_middle" s orelse String.isSubstring "excluded" s) names
    val nClassical = length (List.filter (fn s => String.isSubstring "ex_middle" s orelse String.isSubstring "excluded" s) names)
    val bitlenAx = List.filter (fn s => String.isSubstring "bitlen" s) names
    val suspicious = List.filter (fn s =>
         String.isSubstring "bertrand" s orelse String.isSubstring "prime_exist" s
         orelse String.isSubstring "chebyshev" s orelse String.isSubstring "postulate" s
         orelse String.isSubstring "seb" s orelse String.isSubstring "threshold" s
         orelse String.isSubstring "window" s orelse String.isSubstring "crude" s
         orelse String.isSubstring "poly_ineq" s orelse String.isSubstring "inequality" s) names
  in out ("W1_CRUDE_AXIOM_AUDIT total=" ^ Int.toString (length names)
          ^ " ex_middle_present=" ^ Bool.toString hasEM
          ^ " classical_count=" ^ Int.toString nClassical
          ^ " bitlen_axioms=" ^ Int.toString (length bitlenAx)
          ^ " suspicious_count=" ^ Int.toString (length suspicious) ^ "\n");
     app (fn s => out ("  BITLEN AXIOM: " ^ s ^ "\n")) bitlenAx;
     app (fn s => out ("  SUSPICIOUS AXIOM: " ^ s ^ "\n")) suspicious
  end;

val () = out "W1_CRUDE_DELTA_DONE\n";
