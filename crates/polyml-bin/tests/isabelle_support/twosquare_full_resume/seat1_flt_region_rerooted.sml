val () = out "BINOM_BEGIN\n";

(* ---- the binom theory extension + Pascal recursion axioms (on top of thyP) ---- *)
val thyB0 = Sign.add_consts
  [(Binding.name "binom", natT --> natT --> natT, NoSyn)] thyGR;
val binomC = Const (Sign.full_name thyB0 (Binding.name "binom"), natT --> natT --> natT);
fun binom s t = binomC $ s $ t;

val nBn = Free("n", natT); val kBn = Free("k", natT);
(* binom_n_0 : oeq (binom n Zero) (Suc Zero)              C(n,0) = 1 *)
val ((_,binom_n_0_ax), thyB1) = Thm.add_axiom_global (Binding.name "binom_n_0",
      jT (oeq (binom nBn ZeroC) (suc ZeroC))) thyB0;
(* binom_0_Suc : oeq (binom Zero (Suc k)) Zero            C(0,k+1) = 0 *)
val ((_,binom_0_Suc_ax), thyB2) = Thm.add_axiom_global (Binding.name "binom_0_Suc",
      jT (oeq (binom ZeroC (suc kBn)) ZeroC)) thyB1;
(* binom_Suc_Suc : Pascal *)
val ((_,binom_Suc_Suc_ax), thyB) = Thm.add_axiom_global (Binding.name "binom_Suc_Suc",
      jT (oeq (binom (suc nBn) (suc kBn))
              (add (binom nBn kBn) (binom nBn (suc kBn))))) thyB2;

(* ---- THE ONE FINAL CONTEXT ctxtB / ctermB ---- *)
val ctxtB  = Proof_Context.init_global thyB;
val ctermB = Thm.cterm_of ctxtB;

(* ---- re-varify every reused axiom/lemma onto ctxtB ---- *)
val oeq_refl_vB     = varify oeq_refl;
val oeq_subst_vB    = varify oeq_subst;
val nat_induct_vB   = varify nat_induct;
val add_0_vB        = varify add_0;
val add_Suc_vB      = varify add_Suc;
val add_0_right_vB  = varify add_0_right;
val add_Suc_right_vB= varify add_Suc_right;
val add_comm_vB     = varify add_comm;
val add_assoc_vB    = varify add_assoc;
val mult_0_vB       = varify mult_0;
val mult_Suc_vB     = varify mult_Suc;
val mult_0_right_vB = varify mult_0_right;
val mult_Suc_right_vB = varify mult_Suc_right;
val mult_comm_vB    = varify mult_comm;
val mult_assoc_vB   = varify mult_assoc;
val mult_1_left_vB  = varify mult_1_left;
val mult_1_right_vB = varify mult_1_right;
val left_distrib_vB = varify left_distrib;
val right_distrib_vB= varify right_distrib;
val exI_vB          = varify exI_ax;
val exE_vB          = varify exE_ax;
val disjI1_vB       = varify disjI1_ax;
val disjI2_vB       = varify disjI2_ax;
val disjE_vB        = varify disjE_ax;
val allI_vB         = varify allI_ax;
val allE_vB         = varify allE_ax;
val disj_zero_or_suc_vB = varify disj_zero_or_suc;
val binom_n_0_vB    = varify binom_n_0_ax;
val binom_0_Suc_vB  = varify binom_0_Suc_ax;
val binom_Suc_Suc_vB= varify binom_Suc_Suc_ax;

(* ---- ground instantiators on ctxtB ---- *)
fun oeqreflB_at t      = beta_norm (Drule.infer_instantiate ctxtB [(("a",0), ctermB t)] oeq_refl_vB);
fun mult0B_at t        = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB t)] mult_0_vB);
fun mult0rB_at t       = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB t)] mult_0_right_vB);
fun multSucB_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtB
                            [(("m",0), ctermB mt),(("n",0), ctermB nt)] mult_Suc_vB);
fun multSucrB_at (nt,mt)= beta_norm (Drule.infer_instantiate ctxtB
                            [(("n",0), ctermB nt),(("m",0), ctermB mt)] mult_Suc_right_vB);
fun add0B_at t         = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB t)] add_0_vB);
fun add0rB_at t        = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB t)] add_0_right_vB);
fun addSucB_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtB
                            [(("m",0), ctermB mt),(("n",0), ctermB nt)] add_Suc_vB);
fun addSucrB_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtB
                            [(("m",0), ctermB mt),(("n",0), ctermB nt)] add_Suc_right_vB);
fun addcommB_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtB
                            [(("m",0), ctermB mt),(("n",0), ctermB nt)] add_comm_vB);
fun addassocB_at (mt,nt,kt)= beta_norm (Drule.infer_instantiate ctxtB
                            [(("m",0), ctermB mt),(("n",0), ctermB nt),(("k",0), ctermB kt)] add_assoc_vB);
fun multcommB_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtB
                            [(("m",0), ctermB mt),(("n",0), ctermB nt)] mult_comm_vB);
fun multassocB_at (mt,nt,kt)= beta_norm (Drule.infer_instantiate ctxtB
                            [(("m",0), ctermB mt),(("n",0), ctermB nt),(("k",0), ctermB kt)] mult_assoc_vB);
fun mult1lB_at t       = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB t)] mult_1_left_vB);
fun mult1rB_at t       = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB t)] mult_1_right_vB);
(* left_distrib : oeq (mult x (add m n)) (add (mult x m)(mult x n))   vars x,m,n *)
fun ldistB_at (xt,mt,nt) = beta_norm (Drule.infer_instantiate ctxtB
                            [(("x",0), ctermB xt),(("m",0), ctermB mt),(("n",0), ctermB nt)] left_distrib_vB);
(* right_distrib : oeq (mult (add m n) k)(add (mult m k)(mult n k))   vars m,n,k *)
fun rdistB_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtB
                            [(("m",0), ctermB mt),(("n",0), ctermB nt),(("k",0), ctermB kt)] right_distrib_vB);

(* binom Pascal ground instantiators on ctxtB *)
fun binomN0B_at t       = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB t)] binom_n_0_vB);
fun binom0SB_at t       = beta_norm (Drule.infer_instantiate ctxtB [(("k",0), ctermB t)] binom_0_Suc_vB);
fun binomSSB_at (nt,kt) = beta_norm (Drule.infer_instantiate ctxtB
                            [(("n",0), ctermB nt),(("k",0), ctermB kt)] binom_Suc_Suc_vB);

(* nat_induct ground instance on ctxtB *)
fun nat_induct_atB (Qabs, kT) = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Qabs), (("k",0), ctermB kT)] nat_induct_vB);

(* ---- oeq trans/sym already top-level (oeq_trans/oeq_sym), Suc_cong too ---- *)

(* ---- congruence helpers on ctxtB (LEFT/RIGHT operand of mult / add) ---- *)
fun mult_cong_lB (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Pabs), (("a",0), ctermB pT), (("b",0), ctermB qT)] oeq_subst_vB);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtB [(("a",0), ctermB (mult pT kT))] oeq_refl_vB);
  in inst OF [hpq, refl_pk] end;
fun mult_cong_rB (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Pabs), (("a",0), ctermB pT), (("b",0), ctermB qT)] oeq_subst_vB);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtB [(("a",0), ctermB (mult hT pT))] oeq_refl_vB);
  in inst OF [hpq, refl_hp] end;
fun add_cong_lB (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Pabs), (("a",0), ctermB pT), (("b",0), ctermB qT)] oeq_subst_vB);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtB [(("a",0), ctermB (add pT kT))] oeq_refl_vB);
  in inst OF [hpq, refl_pk] end;
fun add_cong_rB (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Pabs), (("a",0), ctermB pT), (("b",0), ctermB qT)] oeq_subst_vB);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtB [(("a",0), ctermB (add hT pT))] oeq_refl_vB);
  in inst OF [hpq, refl_hp] end;
(* binom-congruence in the SECOND argument (first arg fixed):
   oeq u v ==> oeq (binom aT u) (binom aT v).  (no capture: binom has no binder.) *)
fun binom_cong_arg2B (aT, uT, vT) huv =
  let
    val Pabs = Abs("z", natT, oeq (binom aT uT) (binom aT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Pabs), (("a",0), ctermB uT), (("b",0), ctermB vT)] oeq_subst_vB);
    val refl_pu = beta_norm (Drule.infer_instantiate ctxtB [(("a",0), ctermB (binom aT uT))] oeq_refl_vB);
  in inst OF [huv, refl_pu] end;

(* ---- exE / disjE / allI / allE elimination helpers on ctxtB ---- *)
fun exE_elimB (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm = Thm.assume (ctermB hypTerm);
    val body = bodyFn wF hypThm;
    val minor = Thm.forall_intr (ctermB wF) (Thm.implies_intr (ctermB hypTerm) body);
    val exE_inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Pabs), (("Q",0), ctermB goalC)] exE_vB);
    val partial = Thm.implies_elim exE_inst exThm;
    val res = Thm.implies_elim partial minor;
  in res end;
fun disjE_elimB (At, Bt, Ct) dThm caseA caseB =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("A",0), ctermB At), (("B",0), ctermB Bt), (("C",0), ctermB Ct)] disjE_vB);
    val s1 = Thm.implies_elim inst dThm;
    val s2 = Thm.implies_elim s1 caseA;
  in Thm.implies_elim s2 caseB end;
(* allI : from (!!x. jT (Pabs x)) get jT (Forall Pabs).
   hAll : a thm of meta-form  !!x. jT (Pabs x)  (already forall_intr'd). *)
fun allI_atB Pabs hAll =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtB [(("P",0), ctermB Pabs)] allI_vB);
  in Thm.implies_elim inst hAll end;
fun allE_atB Pabs at hForall =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Pabs), (("a",0), ctermB at)] allE_vB);
  in Thm.implies_elim inst hForall end;
(* disj_zero_or_suc ground instance on ctxtB : Disj (oeq p Zero) (Ex(%q. oeq p (Suc q))) *)
fun dzosB_at t = beta_norm (Drule.infer_instantiate ctxtB [(("p",0), ctermB t)] disj_zero_or_suc_vB);

val () = out "BINOM_HELPERS_READY\n";

(* ---- uniform 0-hyp + aconv validator on ctxtB ---- *)
fun checkB (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtB (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtB intended ^ "\n");
          false)
  end;

(* schematic Vars for intended statements on ctxtB *)
val nVb = Var (("n",0), natT);
val kVb = Var (("k",0), natT);

(* sanity: the three Pascal axioms are usable (ground-instantiate + check 0-hyp).
   binom_n_0_vB / binom_0_Suc_vB / binom_Suc_Suc_vB are schematic; check them. *)
val i_binom_n_0   = jT (oeq (binom nVb ZeroC) (suc ZeroC));
val i_binom_0_Suc = jT (oeq (binom ZeroC (suc kVb)) ZeroC);
val i_binom_SS    = jT (oeq (binom (suc nVb) (suc kVb))
                            (add (binom nVb kVb) (binom nVb (suc kVb))));
val r_binom_n_0   = checkB ("binom_n_0",     binom_n_0_vB,     i_binom_n_0);
val r_binom_0_Suc = checkB ("binom_0_Suc",   binom_0_Suc_vB,   i_binom_0_Suc);
val r_binom_SS    = checkB ("binom_Suc_Suc", binom_Suc_Suc_vB, i_binom_SS);

(* ============================================================================
   ABSORPTION:  oeq (mult (Suc k)(binom (Suc n)(Suc k))) (mult (Suc n)(binom n k))
   ----------------------------------------------------------------------------
   Induction on n; predicate P n := Forall (%k. <stmt at n,k>), k UNIVERSAL.
   Build the predicate CAPTURE-AVOIDING (Term.lambda over a fresh Free), since the
   body has no binder of the bound var (mult/binom of it are fine), but we use
   Term.lambda for safety / uniformity.
   ============================================================================ *)

(* the per-(n,k) body term (n,k as terms) *)
fun absBody nT kT =
  oeq (mult (suc kT) (binom (suc nT) (suc kT))) (mult (suc nT) (binom nT kT));

val absorption_all =
  let
    (* predicate over n, with k universal inside via object Forall *)
    val zN = Free("zn", natT);
    val kInner = Free("kk", natT);
    val innerAbs0 = Term.lambda kInner (absBody zN kInner);   (* %k. body(zn,k) *)
    val Ppred = Term.lambda zN (mkForall innerAbs0);          (* %n. Forall(%k. body(n,k)) *)
    val nFi = Free("n", natT);
    val ind = nat_induct_atB (Ppred, nFi);

    (* =====================  BASE  n = 0  ===================== *)
    (* show  !!k. oeq (mult (Suc k)(binom (Suc 0)(Suc k))) (mult (Suc 0)(binom 0 k))
       by inner case-split on k (Zero / Suc j). *)
    val baseInnerAbs = Term.lambda kInner (absBody ZeroC kInner);  (* %k. body(0,k) *)
    fun base_body kT =
      let
        (* goal: oeq (mult (Suc k)(binom (Suc 0)(Suc k))) (mult (Suc 0)(binom 0 k)) *)
        val dz = dzosB_at kT;                          (* Disj (oeq k 0)(Ex(%q. oeq k (Suc q))) *)
        val goalC = absBody ZeroC kT;
        (* CASE k = 0 *)
        val caseZ =
          let
            val ez = Thm.assume (ctermB (jT (oeq kT ZeroC)));     (* oeq k 0 *)
            val ezs = oeq_sym OF [ez];                            (* oeq 0 k *)
            (* rewrite the WHOLE goalC body : body(0,0) holds, then substitute 0 -> k.
               Easier: prove body(0,0) directly, then transport via oeq 0 k using subst. *)
            (* body(0,0): oeq (mult (Suc 0)(binom (Suc 0)(Suc 0))) (mult (Suc 0)(binom 0 0)) *)
            (* C(1,1) = C(0,0)+C(0,1) = 1 + 0 = 1 ; LHS = 1*1 = 1 ; RHS = 1*C(0,0)=1*1=1 *)
            val p11   = binomSSB_at (ZeroC, ZeroC);               (* C(1,1) = C(0,0)+C(0,1) *)
            val c00   = binomN0B_at ZeroC;                        (* C(0,0) = 1 *)
            val c01   = binom0SB_at ZeroC;                        (* C(0,1) = 0 *)
            (* C(0,0)+C(0,1) = 1 + 0 = 1 *)
            val s1 = add_cong_lB (binom ZeroC ZeroC, suc ZeroC, binom ZeroC (suc ZeroC)) c00;
                                                                 (* C00+C01 = 1+C01 *)
            val s2 = add_cong_rB (suc ZeroC, binom ZeroC (suc ZeroC), ZeroC) c01;
                                                                 (* 1+C01 = 1+0 *)
            val s3 = add0rB_at (suc ZeroC);                       (* 1+0 = 1 *)
            val sumIs1 = oeq_trans OF [oeq_trans OF [s1, s2], s3];(* C00+C01 = 1 *)
            val c11_is1 = oeq_trans OF [p11, sumIs1];             (* C(1,1) = 1 *)
            (* LHS body(0,0) = mult (Suc 0)(C(1,1)) ; rewrite C(1,1)->1, then 1*1=1 *)
            val lhs1 = mult_cong_rB (suc ZeroC, binom (suc ZeroC)(suc ZeroC), suc ZeroC) c11_is1;
                                                                 (* (1)*C(1,1) = (1)*1 *)
            val lhs2 = mult1rB_at (suc ZeroC);                    (* (1)*1 = 1 *)
            val lhs  = oeq_trans OF [lhs1, lhs2];                 (* (1)*C(1,1) = 1 *)
            (* RHS body(0,0) = mult (Suc 0)(C(0,0)) ; C(0,0)->1, 1*1=1 *)
            val rhs1 = mult_cong_rB (suc ZeroC, binom ZeroC ZeroC, suc ZeroC) c00;
                                                                 (* (1)*C(0,0) = (1)*1 *)
            val rhs2 = mult1rB_at (suc ZeroC);                    (* (1)*1 = 1 *)
            val rhs  = oeq_trans OF [rhs1, rhs2];                 (* (1)*C(0,0) = 1 *)
            val rhss = oeq_sym OF [rhs];                          (* 1 = (1)*C(0,0) *)
            val body00 = oeq_trans OF [lhs, rhss];               (* body(0,0): LHS = RHS *)
            (* transport body(0,0) to body(0,k) by substituting 0 -> k (using oeq 0 k).
               predicate %z. body(0,z), capture-avoiding. *)
            val zP = Free("zp0", natT);
            val Pabs = Term.lambda zP (absBody ZeroC zP);
            val inst = beta_norm (Drule.infer_instantiate ctxtB
                  [(("P",0), ctermB Pabs), (("a",0), ctermB ZeroC), (("b",0), ctermB kT)] oeq_subst_vB);
            val g = inst OF [ezs, body00];                       (* body(0,k) *)
          in Thm.implies_intr (ctermB (jT (oeq kT ZeroC))) g end;
        (* CASE k = Suc j *)
        val caseS =
          let
            val PabsQ = Abs("q", natT, oeq kT (suc (Bound 0)));
            val exq = Thm.assume (ctermB (jT (mkEx PabsQ)));
            fun sbody j (hj : thm) =                              (* hj : oeq k (Suc j) *)
              let
                (* prove body(0, Suc j) then transport Suc j -> k. *)
                (* body(0,Suc j): oeq (mult (Suc(Suc j))(binom (Suc 0)(Suc(Suc j))))
                                       (mult (Suc 0)(binom 0 (Suc j)))
                   C(1, Suc(Suc j)) = C(0, Suc j)+C(0,Suc(Suc j)) = 0+0 = 0 ; LHS = _*0 = 0
                   C(0, Suc j) = 0 ; RHS = (1)*0 = 0 *)
                val pSS  = binomSSB_at (ZeroC, suc j);            (* C(1,Suc(Suc j)) = C(0,Suc j)+C(0,Suc(Suc j)) *)
                val c0a  = binom0SB_at j;                         (* C(0,Suc j) = 0 *)
                val c0b  = binom0SB_at (suc j);                   (* C(0,Suc(Suc j)) = 0 *)
                val a1 = add_cong_lB (binom ZeroC (suc j), ZeroC, binom ZeroC (suc (suc j))) c0a;
                                                                 (* C(0,Sj)+C(0,SSj) = 0+C(0,SSj) *)
                val a2 = add_cong_rB (ZeroC, binom ZeroC (suc (suc j)), ZeroC) c0b;
                                                                 (* 0+C(0,SSj) = 0+0 *)
                val a3 = add0B_at ZeroC;                          (* 0+0 = 0 *)
                val sum0 = oeq_trans OF [oeq_trans OF [a1, a2], a3];   (* C(0,Sj)+C(0,SSj) = 0 *)
                val cBig0 = oeq_trans OF [pSS, sum0];            (* C(1,Suc(Suc j)) = 0 *)
                (* LHS = (Suc(Suc j))*C(1,Suc(Suc j)) -> (Suc(Suc j))*0 -> 0 *)
                val lhs1 = mult_cong_rB (suc (suc j), binom (suc ZeroC) (suc (suc j)), ZeroC) cBig0;
                val lhs2 = mult0rB_at (suc (suc j));             (* (Suc(Suc j))*0 = 0 *)
                val lhs  = oeq_trans OF [lhs1, lhs2];            (* LHS = 0 *)
                (* RHS = (Suc 0)*C(0,Suc j) -> (Suc 0)*0 -> 0 *)
                val rhs1 = mult_cong_rB (suc ZeroC, binom ZeroC (suc j), ZeroC) c0a;
                val rhs2 = mult0rB_at (suc ZeroC);              (* (1)*0 = 0 *)
                val rhs  = oeq_trans OF [rhs1, rhs2];            (* RHS = 0 *)
                val rhss = oeq_sym OF [rhs];                     (* 0 = RHS *)
                val bodySj = oeq_trans OF [lhs, rhss];           (* body(0, Suc j) *)
                (* transport Suc j -> k via oeq (Suc j) k *)
                val hjs = oeq_sym OF [hj];                       (* oeq (Suc j) k *)
                val zP = Free("zp1", natT);
                val Pabs = Term.lambda zP (absBody ZeroC zP);
                val inst = beta_norm (Drule.infer_instantiate ctxtB
                      [(("P",0), ctermB Pabs), (("a",0), ctermB (suc j)), (("b",0), ctermB kT)] oeq_subst_vB);
              in inst OF [hjs, bodySj] end;                      (* body(0,k) *)
            val g = exE_elimB (PabsQ, goalC) exq "qb0" sbody;
          in Thm.implies_intr (ctermB (jT (mkEx PabsQ))) g end;
        val PabsW = Abs("q", natT, oeq kT (suc (Bound 0)));
      in disjE_elimB (oeq kT ZeroC, mkEx PabsW, goalC) dz caseZ caseS end;
    (* assemble BASE = Forall(%k. body(0,k)) via allI over a fresh free *)
    val kB0 = Free("kBase", natT);
    val base_meta = Thm.forall_intr (ctermB kB0) (base_body kB0);
    val base = allI_atB baseInnerAbs base_meta;

    (* =====================  STEP  n = Suc x  ===================== *)
    val xF = Free("x", natT);
    val ihInnerAbs = Term.lambda kInner (absBody xF kInner);     (* %k. body(x,k) *)
    val ihprop = jT (mkForall ihInnerAbs);                       (* Forall(%k. body(x,k)) *)
    val IH = Thm.assume (ctermB ihprop);
    (* goal:  !!k. body(Suc x, k)  ->  Forall(%k. body(Suc x,k)) *)
    val stepInnerAbs = Term.lambda kInner (absBody (suc xF) kInner);

    fun step_body kT =
      let
        (* goal: oeq (mult (Suc k)(binom (Suc(Suc x))(Suc k))) (mult (Suc(Suc x))(binom (Suc x) k)) *)
        val goalC = absBody (suc xF) kT;
        val dz = dzosB_at kT;
        (* helper: IH at a term t : oeq (mult (Suc t)(binom (Suc x)(Suc t))) (mult (Suc x)(binom x t)) *)
        fun IH_at t = allE_atB ihInnerAbs t IH;

        (* CASE k = 0 *)
        val caseZ =
          let
            val ez = Thm.assume (ctermB (jT (oeq kT ZeroC)));    (* oeq k 0 *)
            val ezs = oeq_sym OF [ez];                           (* oeq 0 k *)
            (* prove body(Suc x, 0), then transport 0 -> k.
               body(Suc x,0): oeq (mult (Suc 0)(binom (Suc(Suc x))(Suc 0)))
                                  (mult (Suc(Suc x))(binom (Suc x) 0))
               RHS: C(Suc x,0)=1 -> (Suc(Suc x))*1 = Suc(Suc x)
               LHS: (Suc 0)*C(Suc(Suc x),Suc 0) = C(Suc(Suc x),Suc 0)  [mult_1_left]
                    C(Suc(Suc x),Suc 0) Pascal = C(Suc x,0)+C(Suc x,Suc 0) = 1 + C(Suc x,Suc 0)
                    IH at 0 : (Suc 0)*C(Suc x,Suc 0) = (Suc x)*C(x,0) = (Suc x)*1 = Suc x
                              so C(Suc x,Suc 0) = Suc x  [mult_1_left LHS, mult_1_right RHS]
                    => C(Suc(Suc x),Suc 0) = 1 + Suc x = Suc(Suc x)  [add (Suc 0)(Suc x)] *)
            (* derive cSx1 : C(Suc x, Suc 0) = Suc x  from IH at 0 *)
            val ih0  = IH_at ZeroC;     (* (Suc 0)*C(Suc x,Suc 0) = (Suc x)*C(x,0) *)
            val lhsih = mult1lB_at (binom (suc xF) (suc ZeroC));  (* (Suc 0)*C(Suc x,Suc 0) = C(Suc x,Suc 0) *)
            val lhsihs= oeq_sym OF [lhsih];                      (* C(Suc x,Suc 0) = (Suc 0)*C(Suc x,Suc 0) *)
            val cx0  = binomN0B_at xF;                           (* C(x,0) = 1 *)
            val rih1 = mult_cong_rB (suc xF, binom xF ZeroC, suc ZeroC) cx0;  (* (Suc x)*C(x,0) = (Suc x)*1 *)
            val rih2 = mult1rB_at (suc xF);                      (* (Suc x)*1 = Suc x *)
            val rihC = oeq_trans OF [rih1, rih2];                (* (Suc x)*C(x,0) = Suc x *)
            val cSx1 = oeq_trans OF [oeq_trans OF [lhsihs, ih0], rihC];  (* C(Suc x,Suc 0) = Suc x *)
            (* C(Suc(Suc x),Suc 0) = C(Suc x,0)+C(Suc x,Suc 0) *)
            val pBig = binomSSB_at (suc xF, ZeroC);              (* C(Suc(Suc x),Suc 0) = C(Suc x,0)+C(Suc x,Suc 0) *)
            val cSx0 = binomN0B_at (suc xF);                     (* C(Suc x,0) = 1 *)
            val q1 = add_cong_lB (binom (suc xF) ZeroC, suc ZeroC, binom (suc xF) (suc ZeroC)) cSx0;
                                                                (* C(Sx,0)+C(Sx,S0) = 1 + C(Sx,S0) *)
            val q2 = add_cong_rB (suc ZeroC, binom (suc xF) (suc ZeroC), suc xF) cSx1;
                                                                (* 1 + C(Sx,S0) = 1 + (Suc x) *)
            val q3 = add0B_at (suc xF);                          (* add 0 (Suc x) = Suc x *)
            (* 1 + (Suc x) = add (Suc 0)(Suc x) = Suc(add 0 (Suc x)) = Suc(Suc x) *)
            val q4 = addSucB_at (ZeroC, suc xF);                 (* add (Suc 0)(Suc x) = Suc(add 0 (Suc x)) *)
            val q5 = Suc_cong OF [q3];                           (* Suc(add 0 (Suc x)) = Suc(Suc x) *)
            val q45 = oeq_trans OF [q4, q5];                     (* 1 + (Suc x) = Suc(Suc x) *)
            val cBig = oeq_trans OF [oeq_trans OF [oeq_trans OF [pBig, q1], q2], q45];
                                                                (* C(Suc(Suc x),Suc 0) = Suc(Suc x) *)
            (* LHS body = (Suc 0)*C(Suc(Suc x),Suc 0) -> C(...) [mult_1_left] -> Suc(Suc x) *)
            val l1 = mult1lB_at (binom (suc (suc xF)) (suc ZeroC));  (* (1)*C(SSx,S0) = C(SSx,S0) *)
            val lhs = oeq_trans OF [l1, cBig];                  (* LHS = Suc(Suc x) *)
            (* RHS body = (Suc(Suc x))*C(Suc x,0) -> (Suc(Suc x))*1 -> Suc(Suc x) *)
            val r1 = mult_cong_rB (suc (suc xF), binom (suc xF) ZeroC, suc ZeroC) cSx0;
            val r2 = mult1rB_at (suc (suc xF));                 (* (Suc(Suc x))*1 = Suc(Suc x) *)
            val rhs = oeq_trans OF [r1, r2];                    (* RHS = Suc(Suc x) *)
            val rhss = oeq_sym OF [rhs];                        (* Suc(Suc x) = RHS *)
            val bodyS0 = oeq_trans OF [lhs, rhss];              (* body(Suc x, 0) *)
            (* transport 0 -> k *)
            val zP = Free("zps0", natT);
            val Pabs = Term.lambda zP (absBody (suc xF) zP);
            val inst = beta_norm (Drule.infer_instantiate ctxtB
                  [(("P",0), ctermB Pabs), (("a",0), ctermB ZeroC), (("b",0), ctermB kT)] oeq_subst_vB);
            val g = inst OF [ezs, bodyS0];
          in Thm.implies_intr (ctermB (jT (oeq kT ZeroC))) g end;

        (* CASE k = Suc j *)
        val caseS =
          let
            val PabsQ = Abs("q", natT, oeq kT (suc (Bound 0)));
            val exq = Thm.assume (ctermB (jT (mkEx PabsQ)));
            fun sbody j (hj : thm) =                            (* hj : oeq k (Suc j) *)
              let
                (* prove body(Suc x, Suc j), then transport (Suc j) -> k.
                   body(Suc x, Suc j):
                     oeq (mult (Suc(Suc j))(binom (Suc(Suc x))(Suc(Suc j))))
                         (mult (Suc(Suc x))(binom (Suc x)(Suc j)))
                   Let B = C(Suc x, Suc j), c = C(x, Suc j).
                   Pascal:  C(Suc(Suc x),Suc(Suc j)) = C(Suc x,Suc j) + C(Suc x,Suc(Suc j))
                                                     = B + C(Suc x, Suc(Suc j))
                   IH at (Suc j): (Suc(Suc j))*C(Suc x,Suc(Suc j)) = (Suc x)*c
                   IH at j      : (Suc j)*B = (Suc x)*C(x,j)
                   Pascal:  B = C(x,j) + c                              [pBsmall]
                   target identity (after distrib + IH at Suc j):
                     (Suc(Suc j))*B + (Suc x)*c = (Suc(Suc x))*B
                   proof:
                     (Suc(Suc j))*B = B + (Suc j)*B          [mult_Suc]
                                    = B + (Suc x)*C(x,j)      [IH at j]
                     so LHS' = B + (Suc x)*C(x,j) + (Suc x)*c
                             = B + (Suc x)*(C(x,j)+c)         [left_distrib rev]
                             = B + (Suc x)*B                  [pBsmall rev, cong]
                             = (Suc(Suc x))*B                 [mult_Suc rev]
                *)
                val Bt = binom (suc xF) (suc j);                (* B = C(Suc x, Suc j) *)
                val ct = binom xF (suc j);                      (* c = C(x, Suc j) *)
                val cxj= binom xF j;                            (* C(x,j) *)
                val cBig = binom (suc xF) (suc (suc j));        (* C(Suc x, Suc(Suc j)) *)

                (* LHS of body : (Suc(Suc j))*C(Suc(Suc x),Suc(Suc j)) *)
                val pLHS = binomSSB_at (suc xF, suc j);         (* C(SSx,SSj) = B + cBig *)
                val L1 = mult_cong_rB (suc (suc j), binom (suc (suc xF)) (suc (suc j)), add Bt cBig) pLHS;
                                                               (* (SSj)*C(SSx,SSj) = (SSj)*(B+cBig) *)
                val L2 = ldistB_at (suc (suc j), Bt, cBig);    (* (SSj)*(B+cBig) = (SSj)*B + (SSj)*cBig *)
                val Lchain = oeq_trans OF [L1, L2];            (* LHSbody = (SSj)*B + (SSj)*cBig *)
                (* IH at Suc j : (Suc(Suc j))*cBig = (Suc x)*c *)
                val ihSj = IH_at (suc j);                      (* (SSj)*C(Sx,SSj) = (Sx)*C(x,Sj) ; note SSj = Suc(Suc j), cBig=C(Sx,SSj), c=C(x,Sj) *)
                (* fold (SSj)*cBig -> (Sx)*c inside the sum (right summand) *)
                val L3 = add_cong_rB (mult (suc (suc j)) Bt, mult (suc (suc j)) cBig, mult (suc xF) ct) ihSj;
                                                               (* (SSj)*B + (SSj)*cBig = (SSj)*B + (Sx)*c *)
                val LHSbody = oeq_trans OF [Lchain, L3];       (* LHSbody = (SSj)*B + (Sx)*c *)

                (* now transform (SSj)*B + (Sx)*c  ->  (SSx)*B *)
                (* (SSj)*B = B + (Sj)*B  [mult_Suc with m=Suc j, n=B] *)
                val mS = multSucB_at (suc j, Bt);              (* (Suc(Suc j))*B = add B ((Suc j)*B) *)
                (* IH at j : (Suc j)*B = (Suc x)*C(x,j) *)
                val ihj = IH_at j;                             (* (Sj)*C(Sx,Sj) = (Sx)*C(x,j) ; B=C(Sx,Sj), cxj=C(x,j) *)
                val mS2 = add_cong_rB (Bt, mult (suc j) Bt, mult (suc xF) cxj) ihj;
                                                               (* add B ((Sj)*B) = add B ((Sx)*C(x,j)) *)
                val ssjB = oeq_trans OF [mS, mS2];             (* (SSj)*B = add B ((Sx)*C(x,j)) *)
                (* substitute (SSj)*B -> add B ((Sx)*C(x,j)) inside LHSbody's left summand *)
                val L4 = add_cong_lB (mult (suc (suc j)) Bt, add Bt (mult (suc xF) cxj), mult (suc xF) ct) ssjB;
                                                               (* (SSj)*B + (Sx)*c = (add B ((Sx)*C(x,j))) + (Sx)*c *)
                val cur1 = oeq_trans OF [LHSbody, L4];         (* LHSbody = (B + (Sx)*C(x,j)) + (Sx)*c *)
                (* reassoc: (B + (Sx)C(x,j)) + (Sx)c = B + ((Sx)C(x,j) + (Sx)c) *)
                val asc = addassocB_at (Bt, mult (suc xF) cxj, mult (suc xF) ct);
                                                               (* (B + A1) + A2 = B + (A1 + A2) *)
                val cur2 = oeq_trans OF [cur1, asc];           (* LHSbody = B + ((Sx)C(x,j) + (Sx)c) *)
                (* (Sx)*C(x,j) + (Sx)*c = (Sx)*(C(x,j)+c)  [left_distrib reversed] *)
                val ld = ldistB_at (suc xF, cxj, ct);          (* (Sx)*(C(x,j)+c) = (Sx)*C(x,j) + (Sx)*c *)
                val lds= oeq_sym OF [ld];                      (* (Sx)*C(x,j)+(Sx)*c = (Sx)*(C(x,j)+c) *)
                val cur3in = add_cong_rB (Bt, add (mult (suc xF) cxj) (mult (suc xF) ct), mult (suc xF) (add cxj ct)) lds;
                                                               (* B + ((Sx)C(x,j)+(Sx)c) = B + (Sx)*(C(x,j)+c) *)
                val cur3 = oeq_trans OF [cur2, cur3in];        (* LHSbody = B + (Sx)*(C(x,j)+c) *)
                (* Pascal small: B = C(x,j) + c   so  (C(x,j)+c) = B  (sym) *)
                val pBsmall = binomSSB_at (xF, j);             (* C(Sx,Sj) = C(x,j)+C(x,Sj) i.e. B = C(x,j)+c *)
                val pBsmalls = oeq_sym OF [pBsmall];           (* C(x,j)+c = B *)
                val foldB = mult_cong_rB (suc xF, add cxj ct, Bt) pBsmalls;
                                                               (* (Sx)*(C(x,j)+c) = (Sx)*B *)
                val cur4in = add_cong_rB (Bt, mult (suc xF) (add cxj ct), mult (suc xF) Bt) foldB;
                                                               (* B + (Sx)*(C(x,j)+c) = B + (Sx)*B *)
                val cur4 = oeq_trans OF [cur3, cur4in];        (* LHSbody = B + (Sx)*B *)
                (* B + (Sx)*B = (Suc(Suc x))*B  [mult_Suc with m=Suc x, n=B, reversed] *)
                val mSx = multSucB_at (suc xF, Bt);            (* (Suc(Suc x))*B = add B ((Sx)*B) *)
                val mSxs= oeq_sym OF [mSx];                    (* add B ((Sx)*B) = (Suc(Suc x))*B *)
                val cur5 = oeq_trans OF [cur4, mSxs];          (* LHSbody = (Suc(Suc x))*B *)
                (* cur5 : oeq (LHSbody-expr) ((Suc(Suc x))*B).  But LHSbody-expr is the
                   ORIGINAL LHS of body (mult (Suc(Suc j))(binom (Suc(Suc x))(Suc(Suc j)))).
                   The body's RHS is (mult (Suc(Suc x))(binom (Suc x)(Suc j))) = (SSx)*B.
                   So cur5 IS exactly body(Suc x, Suc j). *)
                val bodySj = cur5;
                (* transport (Suc j) -> k via oeq (Suc j) k *)
                val hjs = oeq_sym OF [hj];                     (* oeq (Suc j) k *)
                val zP = Free("zps1", natT);
                val Pabs = Term.lambda zP (absBody (suc xF) zP);
                val inst = beta_norm (Drule.infer_instantiate ctxtB
                      [(("P",0), ctermB Pabs), (("a",0), ctermB (suc j)), (("b",0), ctermB kT)] oeq_subst_vB);
              in inst OF [hjs, bodySj] end;
            val g = exE_elimB (PabsQ, goalC) exq "qbs" sbody;
          in Thm.implies_intr (ctermB (jT (mkEx PabsQ))) g end;

        val PabsW = Abs("q", natT, oeq kT (suc (Bound 0)));
      in disjE_elimB (oeq kT ZeroC, mkEx PabsW, goalC) dz caseZ caseS end;

    (* assemble STEP: from (!!k. body(Suc x,k)) get Forall(%k. body(Suc x,k)),
       then discharge IH and forall_intr x. *)
    val kS0 = Free("kStep", natT);
    val step_meta = Thm.forall_intr (ctermB kS0) (step_body kS0);
    val stepForall = allI_atB stepInnerAbs step_meta;            (* Forall(%k. body(Suc x,k)) *)
    val step1 = Thm.forall_intr (ctermB xF) (Thm.implies_intr (ctermB ihprop) stepForall);

    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;                         (* Forall(%k. body(n,k)) with n Free *)
  in r2 end;

(* absorption_all : Forall(%k. body(n,k))  with n FREE.
   Specialize to a free k, then varify -> both n,k schematic. *)
val absorption =
  let
    val nF = Free("n", natT);
    val kF = Free("k", natT);
    (* absorption_all has n Free; allE at kF gives body(n,k) *)
    val innerAbsN = Term.lambda (Free("kk", natT)) (absBody nF (Free("kk", natT)));
    val spec = allE_atB innerAbsN kF absorption_all;            (* body(n,k) at free n,k *)
  in varify spec end;

val absorption_intended = jT (absBody nVb kVb);
val r_absorption = checkB ("absorption", absorption, absorption_intended);

(* soundness probe: absorption must be NONTRIVIAL (not provable as reflexivity-collapse).
   Confirm the two sides differ syntactically. *)
val b_absorption_nontrivial =
  let val (lhs, rhs) =
        (mult (suc kVb) (binom (suc nVb) (suc kVb)), mult (suc nVb) (binom nVb kVb))
  in not (lhs aconv rhs) end;

val () =
  if r_absorption andalso b_absorption_nontrivial
  then out "ABSORPTION_PROBE_OK nontrivial\n"
  else out "ABSORPTION_PROBE_FAIL\n";

(* ============================================================================
   STAGE B FINAL VALIDATION
   ============================================================================ *)
val () =
  if r_binom_n_0 andalso r_binom_0_Suc andalso r_binom_SS
     andalso r_absorption andalso b_absorption_nontrivial
  then out "BINOM_FOUNDATION_OK\n"
  else out "BINOM_FOUNDATION_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  STAGE B PHASE 2 : p | C(p,k)  for  0 < k < p  ***
   ----------------------------------------------------------------------------
   TARGET p_dvd_binom :
     jT (prime2 p) ==> jT (lt Zero k) ==> jT (lt k p) ==> jT (dvd p (binom p k))
   Everything routed through ctxtB / ctermB (theory thyB with binom).
   ============================================================================ *)

val () = out "PDVD_BEGIN\n";

(* ---- re-varify the order / divisibility / euclid lemmas onto ctxtB ---- *)
val le_trans_vB    = varify le_trans;
val lt_irrefl_vB   = varify lt_irrefl;
val lt_trans_vB    = varify lt_trans;
val lt_suc_vB      = varify lt_suc;
val dvd_le_vB      = varify dvd_le;
val euclid_lemma_vB= varify euclid_lemma;
val conjunct1_vB   = varify conjunct1_ax;
val oFalse_elim_vB = varify oFalse_elim_ax;

(* oFalse_elim on ctxtB at explicit R *)
fun oFalse_elimB_at rT = beta_norm (Drule.infer_instantiate ctxtB
      [(("R",0), ctermB rT)] oFalse_elim_vB);

(* lt_suc on ctxtB : lt n (Suc n) *)
fun lt_suc_atB nt = beta_norm (Drule.infer_instantiate ctxtB
      [(("n",0), ctermB nt)] lt_suc_vB);

(* lt_trans on ctxtB : lt a b -> lt b c -> lt a c *)
fun lt_trans_atB (at, bt, ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB
        [(("a",0), ctermB at), (("b",0), ctermB bt), (("c",0), ctermB ct)] lt_trans_vB)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* le_trans on ctxtB : le m n -> le n k -> le m k *)
fun le_trans_atB (mt, nt, kt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB
        [(("m",0), ctermB mt), (("n",0), ctermB nt), (("k",0), ctermB kt)] le_trans_vB)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* lt_irrefl on ctxtB : lt n n -> oFalse *)
fun lt_irrefl_atB nt h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB
        [(("n",0), ctermB nt)] lt_irrefl_vB)
  in Thm.implies_elim inst h end;

(* dvd_le on ctxtB : dvd d n -> (oeq n Zero ==> oFalse) -> le d n.
   2nd premise is a META implication; discharge with implies_elim of the meta-thm. *)
fun dvd_le_atB (dt, nt) hdvd hnzMeta =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB
        [(("d",0), ctermB dt), (("n",0), ctermB nt)] dvd_le_vB)
  in Thm.implies_elim (Thm.implies_elim inst hdvd) hnzMeta end;

(* euclid_lemma on ctxtB : prime2 p -> dvd p (mult a b) -> Disj (dvd p a)(dvd p b) *)
fun euclid_atB (pt, at, bt) hprime hdvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB
        [(("p",0), ctermB pt), (("a",0), ctermB at), (("b",0), ctermB bt)] euclid_lemma_vB)
  in Thm.implies_elim (Thm.implies_elim inst hprime) hdvd end;

(* conjunct1 on ctxtB : Conj A B -> A *)
fun conjunct1_atB (At, Bt) hConj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB
        [(("A",0), ctermB At), (("B",0), ctermB Bt)] conjunct1_vB)
  in Thm.implies_elim inst hConj end;

(* dvd_intro on ctxtB : from oeq b (mult a w) get jT (dvd a b), witness w. *)
fun dvd_introB (aT, bT, w) hyp =
  let
    val Pabs = Abs ("k", natT, oeq bT (mult aT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Pabs), (("a",0), ctermB w)] exI_vB);
  in inst OF [hyp] end;

(* generic substitution into a predicate on ctxtB :
   substPredB (Pabs, aT, bT) hab hPa : jT (Pabs bT)  from  oeq aT bT  and  jT (Pabs aT). *)
fun substPredB (Pabs, aT, bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB
        [(("P",0), ctermB Pabs), (("a",0), ctermB aT), (("b",0), ctermB bT)] oeq_subst_vB)
  in inst OF [hab, hPa] end;

val () = out "PDVD_HELPERS_READY\n";

(* ============================================================================
   p_dvd_binom
   ============================================================================ *)
val p_dvd_binom =
  let
    val pF = Free("p", natT);
    val kF = Free("k", natT);
    val primeP = jT (prime2 pF);          (* prime2 p *)
    val ltZkP  = jT (lt ZeroC kF);        (* 0 < k     i.e. le (Suc 0) k *)
    val ltkpP  = jT (lt kF pF);           (* k < p     i.e. le (Suc k) p *)
    val hPrime = Thm.assume (ctermB primeP);
    val h0k    = Thm.assume (ctermB ltZkP);
    val hkp    = Thm.assume (ctermB ltkpP);

    val goalBody = dvd pF (binom pF kF);

    (* ---- k != 0  meta-fact : (oeq k Zero ==> oFalse) ---------------------
       from lt Zero k = le (Suc 0) k : if oeq k Zero, transport into the
       2nd arg of le (Suc 0) (.) giving le (Suc 0) Zero = lt Zero Zero,
       then lt_irrefl. *)
    val k_ne_0_meta =
      let
        val ekz = Thm.assume (ctermB (jT (oeq kF ZeroC)));    (* oeq k 0 *)
        (* predicate %z. lt Zero z = le (Suc 0) z, capture-avoiding *)
        val zF   = Free("zk", natT);
        val Pabs = Term.lambda zF (lt ZeroC zF);
        (* h0k : jT (Pabs k);  transport k -> 0 gives jT (Pabs 0) = lt 0 0 *)
        val lt00 = substPredB (Pabs, kF, ZeroC) ekz h0k;      (* jT (lt Zero Zero) *)
        val fls  = lt_irrefl_atB ZeroC lt00;                  (* oFalse *)
      in Thm.implies_intr (ctermB (jT (oeq kF ZeroC))) fls end;

    (* ---- p != 0  meta-fact : (oeq p Zero ==> oFalse) ---------------------
       not strictly needed below (we never call dvd_le on p directly), but
       keep p positive available; derive from prime2 p => lt 1 p => 0<p. *)

    (* ---- absorption at (n := p, k := k0) where k = Suc k0 ----------------
       absorption (schematic) : oeq (mult (Suc K)(binom (Suc N)(Suc K)))
                                    (mult (Suc N)(binom N K))
       We need an instance with Suc K = k and Suc N = p, so we case k and p
       into Suc-form, instantiate absorption at (N:=p0, K:=k0), then rewrite
       Suc k0 -> k and Suc p0 -> p.

       absorption is varified with vars n,k (per absorption_intended: nVb,kVb).
       Instantiate :  n := p0,  k := k0. *)
    fun absorption_at (n0t, k0t) =
      beta_norm (Drule.infer_instantiate ctxtB
        [(("n",0), ctermB n0t), (("k",0), ctermB k0t)] absorption);

    (* core: given p = Suc p0 (via hp_eq : oeq p (Suc p0)) and
                    k = Suc k0 (via hk_eq : oeq k (Suc k0)),
       produce  jT (dvd p (binom p k)). *)
    fun core (p0t, hp_eq) (k0t, hk_eq) =
      let
        (* absorption instance:
             A : oeq (mult (Suc k0)(binom (Suc p0)(Suc k0)))
                     (mult (Suc p0)(binom p0 k0))                         *)
        val A0 = absorption_at (p0t, k0t);
        (* rewrite (Suc k0) -> k and (Suc p0) -> p inside A0 to get
             A : oeq (mult k (binom p k)) (mult p (binom p0 k0))          *)
        (* step 1: replace Suc p0 by p.  predicate over the Suc-p0 occurrences:
             %z. oeq (mult (Suc k0)(binom z (Suc k0))) (mult z (binom p0 k0)) *)
        val hpsym = oeq_sym OF [hp_eq];     (* oeq (Suc p0) p *)
        val hksym = oeq_sym OF [hk_eq];     (* oeq (Suc k0) k *)
        val zP1   = Free("zP1", natT);
        val P1abs = Term.lambda zP1
              (oeq (mult (suc k0t) (binom zP1 (suc k0t)))
                   (mult zP1 (binom p0t k0t)));
        val A1 = substPredB (P1abs, suc p0t, pF) hpsym A0;
        (* A1 : oeq (mult (Suc k0)(binom p (Suc k0))) (mult p (binom p0 k0)) *)
        (* step 2: replace Suc k0 by k.  predicate:
             %z. oeq (mult z (binom p z)) (mult p (binom p0 k0)) *)
        val zP2   = Free("zP2", natT);
        val P2abs = Term.lambda zP2
              (oeq (mult zP2 (binom pF zP2))
                   (mult pF (binom p0t k0t)));
        val A2 = substPredB (P2abs, suc k0t, kF) hksym A1;
        (* A2 : oeq (mult k (binom p k)) (mult p (binom p0 k0))            *)

        (* So  mult k (binom p k) = mult p (binom p0 k0) = p * (witness).
           => dvd p (mult k (binom p k))   with witness (binom p0 k0). *)
        val dvd_p_mkbpk = dvd_introB (pF, mult kF (binom pF kF), binom p0t k0t) A2;
        (* dvd_p_mkbpk : jT (dvd p (mult k (binom p k))) *)

        (* euclid_lemma (prime2 p)(dvd p (mult k (binom p k)))
             => Disj (dvd p k) (dvd p (binom p k)) *)
        val disjD = euclid_atB (pF, kF, binom pF kF) hPrime dvd_p_mkbpk;

        (* disjE : case dvd p k -> IMPOSSIBLE ; case dvd p (binom p k) -> goal *)
        val caseA =   (* dvd p k  ->  goalBody *)
          let
            val hdpk = Thm.assume (ctermB (jT (dvd pF kF)));   (* dvd p k *)
            (* dvd p k + k != 0  => le p k  (dvd_le) *)
            val le_p_k = dvd_le_atB (pF, kF) hdpk k_ne_0_meta; (* le p k *)
            (* lt k p = le (Suc k) p ; le (Suc k) p + le p k => le (Suc k) k = lt k k *)
            val le_Sk_k = le_trans_atB (suc kF, pF, kF) hkp le_p_k;  (* le (Suc k) k = lt k k *)
            (* lt k k = le (Suc k) k ; lt_irrefl => oFalse *)
            val fls = lt_irrefl_atB kF le_Sk_k;                (* oFalse *)
            (* oFalse => goalBody *)
            val g   = (oFalse_elimB_at goalBody) OF [fls];
          in Thm.implies_intr (ctermB (jT (dvd pF kF))) g end;
        val caseB =   (* dvd p (binom p k) -> goalBody (identity) *)
          let
            val hdpb = Thm.assume (ctermB (jT goalBody));
          in Thm.implies_intr (ctermB (jT goalBody)) hdpb end;
        val concl = disjE_elimB (dvd pF kF, goalBody, goalBody) disjD caseA caseB;
      in concl end;

    (* ---- obtain p = Suc p0 (from prime2 p => lt 1 p => p != 0) ----------
       prime2 p = Conj (lt (Suc 0) p) (Forall ...).  conjunct1 -> lt (Suc 0) p
         = le (Suc(Suc 0)) p.  Case p via dzosB_at p; Zero case contradiction. *)
    val lt1p = conjunct1_atB (lt (suc ZeroC) pF, mkForall (ppAbs pF)) hPrime;  (* lt (Suc 0) p *)
    (* p != 0 meta : if oeq p Zero, transport into 2nd arg of le (Suc(Suc 0)) (.)
       -> le (Suc(Suc 0)) Zero = lt (Suc 0) Zero, then... easier: transport
       lt (Suc 0) p to lt (Suc 0) Zero, which is le (Suc(Suc 0)) Zero.
       That alone isn't lt_irrefl-shaped; instead show lt 0 p first then case p. *)

    (* Build the proof by casing p then k. *)
    val dzP = dzosB_at pF;     (* Disj (oeq p Zero) (Ex(%q. oeq p (Suc q))) *)
    val dzK = dzosB_at kF;     (* Disj (oeq k Zero) (Ex(%q. oeq k (Suc q))) *)

    (* For p : Zero case impossible (from lt (Suc 0) p), Suc case -> proceed. *)
    val PpW = Abs("q", natT, oeq pF (suc (Bound 0)));
    val PkW = Abs("q", natT, oeq kF (suc (Bound 0)));

    (* the body once we know p = Suc p0 : case k *)
    fun afterP (p0t, hp_eq) =
      let
        (* case k : Zero impossible (k_ne_0_meta), Suc -> core *)
        val caseKZero =
          let
            val ekz = Thm.assume (ctermB (jT (oeq kF ZeroC)));
            val fls = Thm.implies_elim k_ne_0_meta ekz;       (* oFalse *)
            val g   = (oFalse_elimB_at goalBody) OF [fls];
          in Thm.implies_intr (ctermB (jT (oeq kF ZeroC))) g end;
        val caseKSuc =
          let
            val exk = Thm.assume (ctermB (jT (mkEx PkW)));
            fun kbody k0v (hk0 : thm) =                        (* hk0 : oeq k (Suc k0v) *)
                  core (p0t, hp_eq) (k0v, hk0);
            val g = exE_elimB (PkW, goalBody) exk "k0w" kbody;
          in Thm.implies_intr (ctermB (jT (mkEx PkW))) g end;
      in disjE_elimB (oeq kF ZeroC, mkEx PkW, goalBody) dzK caseKZero caseKSuc end;

    val casePZero =
      let
        (* oeq p Zero ; from lt (Suc 0) p = le (Suc(Suc 0)) p transport to
           le (Suc(Suc 0)) Zero ; that's lt (Suc 0) Zero ; then derive oFalse
           via lt_irrefl?  No: lt (Suc 0) Zero is le (Suc(Suc 0)) Zero, not
           an n<n shape.  Instead: 0 < p (i.e. lt 0 p) holds from lt (Suc 0) p
           by transitivity? simpler: transport lt 0 k won't help for p.
           Use: lt (Suc 0) p ; transport p->0 : lt (Suc 0) 0 = le (Suc(Suc 0)) 0.
           Then lt_trans / lt_irrefl?  Cleanest: lt (Suc 0) Zero contradicts
           via the same trick used for k_ne_0: we need an n<n.  Build it:
             lt (Suc 0) Zero  AND  Zero <= Suc 0  ... messy.
           SIMPLEST robust route: transport lt(Suc 0) p to lt(Suc 0) Zero,
           then note Zero < Suc 0 (lt_suc at... ) and lt_trans gives
           lt (Suc 0)(Suc 0) = lt_irrefl. *)
        val epz = Thm.assume (ctermB (jT (oeq pF ZeroC)));    (* oeq p Zero *)
        val zF   = Free("zp", natT);
        val Pabs = Term.lambda zF (lt (suc ZeroC) zF);        (* %z. lt (Suc 0) z *)
        val lt1_0 = substPredB (Pabs, pF, ZeroC) epz lt1p;    (* lt (Suc 0) Zero *)
        (* Zero < Suc 0 : lt Zero (Suc Zero) = le (Suc Zero)(Suc Zero) ;
           use lt_suc on ctxtB? lt_suc : lt n (Suc n).  varify + inst at n:=0. *)
        val lt0_S0 = lt_suc_atB ZeroC;                        (* lt Zero (Suc Zero) *)
        (* lt_trans : lt 0 (Suc 0) -> lt (Suc 0) 0 -> lt 0 0 *)
        val lt00 = lt_trans_atB (ZeroC, suc ZeroC, ZeroC) lt0_S0 lt1_0;  (* lt 0 0 *)
        val fls  = lt_irrefl_atB ZeroC lt00;
        val g    = (oFalse_elimB_at goalBody) OF [fls];
      in Thm.implies_intr (ctermB (jT (oeq pF ZeroC))) g end;
    val casePSuc =
      let
        val exp = Thm.assume (ctermB (jT (mkEx PpW)));
        fun pbody p0v (hp0 : thm) = afterP (p0v, hp0);        (* hp0 : oeq p (Suc p0v) *)
        val g = exE_elimB (PpW, goalBody) exp "p0w" pbody;
      in Thm.implies_intr (ctermB (jT (mkEx PpW))) g end;

    val concl0 = disjE_elimB (oeq pF ZeroC, mkEx PpW, goalBody) dzP casePZero casePSuc;
    (* concl0 : jT (dvd p (binom p k))  under hyps primeP, ltZkP, ltkpP.
       discharge in reverse: ltkp, lt0k, prime. *)
    val d1 = Thm.implies_intr (ctermB ltkpP) concl0;
    val d2 = Thm.implies_intr (ctermB ltZkP) d1;
    val d3 = Thm.implies_intr (ctermB primeP) d2;
  in varify d3 end;

(* intended statement, schematic on ctxtB *)
val pVb = Var (("p",0), natT);
val kVb2 = Var (("k",0), natT);
val p_dvd_binom_intended =
  Logic.mk_implies (jT (prime2 pVb),
    Logic.mk_implies (jT (lt ZeroC kVb2),
      Logic.mk_implies (jT (lt kVb2 pVb),
        jT (dvd pVb (binom pVb kVb2)))));

val r_p_dvd_binom = checkB ("p_dvd_binom", p_dvd_binom, p_dvd_binom_intended);

(* ---- soundness probe : the kernel must REJECT the false variant that drops
   lt k p.  We do NOT try to PROVE it; we only confirm our proved theorem
   STILL carries the lt k p premise (i.e. it did not collapse to the weaker,
   false statement p | C(p,k) for all 0<k).  p | C(p,p)=1 is false. *)
val false_variant =
  Logic.mk_implies (jT (prime2 pVb),
    Logic.mk_implies (jT (lt ZeroC kVb2),
      jT (dvd pVb (binom pVb kVb2))));
val b_needs_ltkp = not ((Thm.prop_of p_dvd_binom) aconv false_variant);

val () =
  if r_p_dvd_binom andalso b_needs_ltkp
  then out "P_DVD_BINOM_SOUNDPROBE_OK\n"
  else out "P_DVD_BINOM_SOUNDPROBE_FAIL\n";

val () =
  if r_p_dvd_binom andalso b_needs_ltkp
  then out "P_DVD_BINOM_DONE\n"
  else out "P_DVD_BINOM_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  STAGE C1 : TRUNCATED SUBTRACTION (sub) + SUMMATION (sumf)  ***
   ----------------------------------------------------------------------------
   Extend thyB with BOTH new consts in ONE Sign.add_consts:
     sub  : nat=>nat=>nat
     sumf : (nat=>nat)=>nat=>nat      [HIGHER-ORDER: first arg is a function]
   Final context ctxtSub / ctermSub ; check helper checkSub ; route ALL cterms
   through ctermSub.
   ============================================================================ *)

val () = out "SUMSUB_BEGIN\n";

val fnT = natT --> natT;

(* ---- theory extension : SEAT1 re-root.  thyGR already declares `sub`
   (Pure.sub, from the monolith thyW), so add ONLY `sumf` and let `subC` resolve
   to the existing Pure.sub.  The three sub recursion axioms below are re-asserted
   under the spine names (sub_n_0/sub_0_Suc/sub_Suc_Suc); they are the SAME
   truncated-subtraction equations the monolith's sub_0/sub_SS give. ---- *)
val thySub0 = Sign.add_consts
  [(Binding.name "sumf", fnT --> natT --> natT,  NoSyn)] thyB;
val subC  = Const (Sign.full_name thySub0 (Binding.name "sub"),  natT --> natT --> natT);
fun sub s t = subC $ s $ t;
val sumfC = Const (Sign.full_name thySub0 (Binding.name "sumf"), fnT --> natT --> natT);
fun sumf f n = sumfC $ f $ n;

(* ---- axioms ---- *)
val nSu = Free("n", natT); val kSu = Free("k", natT);
val ((_,sub_n_0_ax),    thySub1) = Thm.add_axiom_global (Binding.name "sub_n_0",
      jT (oeq (sub nSu ZeroC) nSu)) thySub0;
val ((_,sub_0_Suc_ax),  thySub2) = Thm.add_axiom_global (Binding.name "sub_0_Suc",
      jT (oeq (sub ZeroC (suc kSu)) ZeroC)) thySub1;
val ((_,sub_Suc_Suc_ax),thySub3) = Thm.add_axiom_global (Binding.name "sub_Suc_Suc",
      jT (oeq (sub (suc nSu) (suc kSu)) (sub nSu kSu))) thySub2;

val fSu = Free("f", fnT);
val ((_,sumf_0_ax),   thySub4) = Thm.add_axiom_global (Binding.name "sumf_0",
      jT (oeq (sumf fSu ZeroC) (fSu $ ZeroC))) thySub3;
val ((_,sumf_Suc_ax), thySub)  = Thm.add_axiom_global (Binding.name "sumf_Suc",
      jT (oeq (sumf fSu (suc nSu)) (add (sumf fSu nSu) (fSu $ (suc nSu))))) thySub4;

(* ---- THE ONE FINAL CONTEXT ctxtSub / ctermSub ---- *)
val ctxtSub  = Proof_Context.init_global thySub;
val ctermSub = Thm.cterm_of ctxtSub;

(* ---- re-varify every reused axiom/lemma onto ctxtSub ---- *)
val oeq_refl_vS2     = varify oeq_refl;
val oeq_subst_vS2    = varify oeq_subst;
val nat_induct_vS2   = varify nat_induct;
val add_0_vS2        = varify add_0;
val add_Suc_vS2      = varify add_Suc;
val add_0_right_vS2  = varify add_0_right;
val add_Suc_right_vS2= varify add_Suc_right;
val exI_vS2          = varify exI_ax;
val exE_vS2          = varify exE_ax;
val le_refl_vS2      = varify le_refl;
val le_trans_vS2     = varify le_trans;
val impI_vS2         = varify impI_ax;
val mp_vS2           = varify mp_ax;
val allI_vS2         = varify allI_ax;
val allE_vS2         = varify allE_ax;

val sub_n_0_vS2      = varify sub_n_0_ax;
val sub_0_Suc_vS2    = varify sub_0_Suc_ax;
val sub_Suc_Suc_vS2  = varify sub_Suc_Suc_ax;
val sumf_0_vS2       = varify sumf_0_ax;
val sumf_Suc_vS2     = varify sumf_Suc_ax;

(* ---- ground instantiators on ctxtSub ---- *)
fun oeqreflS2_at t   = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub t)] oeq_refl_vS2);
fun add0S2_at t      = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] add_0_vS2);
fun addSucS2_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSub
                            [(("m",0), ctermSub mt),(("n",0), ctermSub nt)] add_Suc_vS2);
fun add0rS2_at t     = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] add_0_right_vS2);
fun addSrS2_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtSub
                            [(("m",0), ctermSub mt),(("n",0), ctermSub nt)] add_Suc_right_vS2);

fun subN0S2_at t        = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] sub_n_0_vS2);
fun sub0SS2_at t        = beta_norm (Drule.infer_instantiate ctxtSub [(("k",0), ctermSub t)] sub_0_Suc_vS2);
fun subSSS2_at (nt,kt)  = beta_norm (Drule.infer_instantiate ctxtSub
                            [(("n",0), ctermSub nt),(("k",0), ctermSub kt)] sub_Suc_Suc_vS2);

fun nat_induct_atS2 (Qabs, kT) = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Qabs), (("k",0), ctermSub kT)] nat_induct_vS2);

(* congruence helpers on ctxtSub : left/right operand of add *)
fun add_cong_lS2 (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("a",0), ctermSub pT), (("b",0), ctermSub qT)] oeq_subst_vS2);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub (add pT kT))] oeq_refl_vS2);
  in inst OF [hpq, refl_pk] end;
fun add_cong_rS2 (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("a",0), ctermSub pT), (("b",0), ctermSub qT)] oeq_subst_vS2);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub (add hT pT))] oeq_refl_vS2);
  in inst OF [hpq, refl_hp] end;

(* generic substitution into a predicate on ctxtSub *)
fun substPredS2 (Pabs, aT, bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("P",0), ctermSub Pabs), (("a",0), ctermSub aT), (("b",0), ctermSub bT)] oeq_subst_vS2)
  in inst OF [hab, hPa] end;

(* exE elimination helper on ctxtSub *)
fun exE_elimS2 (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm = Thm.assume (ctermSub hypTerm);
    val body = bodyFn wF hypThm;
    val minor = Thm.forall_intr (ctermSub wF) (Thm.implies_intr (ctermSub hypTerm) body);
    val exE_inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("Q",0), ctermSub goalC)] exE_vS2);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;

(* le_intro on ctxtSub : from oeq nT (add mT w) get jT (le mT nT) *)
fun le_introS2 (mT, nT, w) hyp =
  let
    val Pabs = Abs ("p", natT, oeq nT (add mT (Bound 0)));
    val exI_inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("a",0), ctermSub w)] exI_vS2);
  in exI_inst OF [hyp] end;

fun le_reflS2_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] le_refl_vS2);
fun le_transS2_at (mt, nt, kt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt), (("n",0), ctermSub nt), (("k",0), ctermSub kt)] le_trans_vS2)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* le_suc_self on ctxtSub : le b (Suc b).  witness Suc 0 :  Suc b = b + Suc 0. *)
fun le_suc_selfS2_at bT =
  let
    val asr  = addSrS2_at (bT, ZeroC);            (* oeq (add b (Suc 0)) (Suc (add b 0)) *)
    val a0r  = add0rS2_at bT;                     (* oeq (add b 0) b *)
    val a0rS = Suc_cong OF [a0r];                 (* oeq (Suc (add b 0)) (Suc b) *)
    val chain = oeq_trans OF [asr, a0rS];         (* oeq (add b (Suc 0)) (Suc b) *)
    val chainSym = oeq_sym OF [chain];            (* oeq (Suc b) (add b (Suc 0)) *)
  in le_introS2 (bT, suc bT, suc ZeroC) chainSym end;

(* object Imp / Forall helpers on ctxtSub *)
fun impI_S2 (At, Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("A",0), ctermSub At), (("B",0), ctermSub Bt)] impI_vS2)
  in Thm.implies_elim inst hImpThm end;
fun mp_S2 (At, Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("A",0), ctermSub At), (("B",0), ctermSub Bt)] mp_vS2)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun allI_S2 Pabs hAll =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("P",0), ctermSub Pabs)] allI_vS2)
  in Thm.implies_elim inst hAll end;
fun allE_S2 Pabs at hForall =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("P",0), ctermSub Pabs), (("a",0), ctermSub at)] allE_vS2)
  in Thm.implies_elim inst hForall end;

val () = out "SUMSUB_HELPERS_READY\n";

(* ---- uniform 0-hyp + aconv validator on ctxtSub ---- *)
fun checkSub (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtSub (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtSub intended ^ "\n");
          false)
  end;

(* schematic Vars for intended statements on ctxtSub *)
val nVs = Var (("n",0), natT);
val kVs = Var (("k",0), natT);
val jVs = Var (("j",0), natT);
val pVs = Var (("p",0), natT);
val fVs = Var (("f",0), fnT);
val gVs = Var (("g",0), fnT);

(* sanity: the 5 axioms are usable -> ground-schematic + 0-hyp check via checkSub *)
val i_sub_n_0   = jT (oeq (sub nVs ZeroC) nVs);
val i_sub_0_Suc = jT (oeq (sub ZeroC (suc kVs)) ZeroC);
val i_sub_SS    = jT (oeq (sub (suc nVs) (suc kVs)) (sub nVs kVs));
val r_sub_n_0_ax   = checkSub ("sub_n_0_ax",    sub_n_0_vS2,     i_sub_n_0);
val r_sub_0_Suc_ax = checkSub ("sub_0_Suc_ax",  sub_0_Suc_vS2,   i_sub_0_Suc);
val r_sub_SS_ax    = checkSub ("sub_Suc_Suc_ax",sub_Suc_Suc_vS2, i_sub_SS);
val i_sumf_0   = jT (oeq (sumf fVs ZeroC) (fVs $ ZeroC));
val i_sumf_Suc = jT (oeq (sumf fVs (suc nVs)) (add (sumf fVs nVs) (fVs $ (suc nVs))));
val r_sumf_0_ax   = checkSub ("sumf_0_ax",   sumf_0_vS2,   i_sumf_0);
val r_sumf_Suc_ax = checkSub ("sumf_Suc_ax", sumf_Suc_vS2, i_sumf_Suc);

(* ============================================================================
   1.  sub_self : oeq (sub n n) Zero      (induction on n)
   ============================================================================ *)
val sub_self =
  let
    val Qpred = Abs("z", natT, oeq (sub (Bound 0) (Bound 0)) ZeroC);
    val nF = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nF);
    val base = subN0S2_at ZeroC;                  (* oeq (sub 0 0) 0 *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (sub xF xF) ZeroC);
    val IH = Thm.assume (ctermSub ihprop);
    val ss = subSSS2_at (xF, xF);                 (* oeq (sub (Suc x)(Suc x)) (sub x x) *)
    val stepconcl = oeq_trans OF [ss, IH];
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_sub_self = jT (oeq (sub nVs nVs) ZeroC);
val r_sub_self = checkSub ("sub_self", sub_self, i_sub_self);

(* ============================================================================
   2.  sub_add_l : oeq (sub (add k j) k) j     (induction on k ; j free)
   ============================================================================ *)
val sub_add_l =
  let
    val jF = Free("j", natT);
    val Qpred = Abs("z", natT, oeq (sub (add (Bound 0) jF) (Bound 0)) jF);
    val kF = Free("k", natT);
    val ind = nat_induct_atS2 (Qpred, kF);
    val bn0 = subN0S2_at (add ZeroC jF);          (* oeq (sub (add 0 j) 0) (add 0 j) *)
    val a0  = add0S2_at jF;                        (* oeq (add 0 j) j *)
    val base = oeq_trans OF [bn0, a0];            (* oeq (sub (add 0 j) 0) j *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (sub (add xF jF) xF) jF);
    val IH = Thm.assume (ctermSub ihprop);
    val aS = addSucS2_at (xF, jF);                (* oeq (add (Suc x) j) (Suc (add x j)) *)
    val P1 = Abs("z", natT, oeq (sub (add (suc xF) jF) (suc xF)) (sub (Bound 0) (suc xF)));
    val s1 = substPredS2 (P1, add (suc xF) jF, suc (add xF jF)) aS
                (oeqreflS2_at (sub (add (suc xF) jF) (suc xF)));
    val s2 = subSSS2_at (add xF jF, xF);          (* oeq (sub (Suc (add x j))(Suc x)) (sub (add x j) x) *)
    val s12 = oeq_trans OF [s1, s2];
    val stepconcl = oeq_trans OF [s12, IH];
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_sub_add_l = jT (oeq (sub (add kVs jVs) kVs) jVs);
val r_sub_add_l = checkSub ("sub_add_l", sub_add_l, i_sub_add_l);

(* ============================================================================
   HELPER  sub_Suc_add_l : oeq (sub (Suc (add k p)) k) (Suc p)    (induction on k)
   ============================================================================ *)
val sub_Suc_add_l =
  let
    val pF = Free("p", natT);
    val Qpred = Abs("z", natT, oeq (sub (suc (add (Bound 0) pF)) (Bound 0)) (suc pF));
    val kF = Free("k", natT);
    val ind = nat_induct_atS2 (Qpred, kF);
    val bn0 = subN0S2_at (suc (add ZeroC pF));    (* oeq (sub (Suc (add 0 p)) 0) (Suc (add 0 p)) *)
    val a0  = add0S2_at pF;                        (* oeq (add 0 p) p *)
    val a0S = Suc_cong OF [a0];                    (* oeq (Suc (add 0 p)) (Suc p) *)
    val base = oeq_trans OF [bn0, a0S];
    val xF = Free("x", natT);
    val ihprop = jT (oeq (sub (suc (add xF pF)) xF) (suc pF));
    val IH = Thm.assume (ctermSub ihprop);
    val aS  = addSucS2_at (xF, pF);               (* oeq (add (Suc x) p) (Suc (add x p)) *)
    val aSS = Suc_cong OF [aS];                   (* oeq (Suc (add (Suc x) p)) (Suc (Suc (add x p))) *)
    val P1 = Abs("z", natT, oeq (sub (suc (add (suc xF) pF)) (suc xF)) (sub (Bound 0) (suc xF)));
    val s1 = substPredS2 (P1, suc (add (suc xF) pF), suc (suc (add xF pF))) aSS
                (oeqreflS2_at (sub (suc (add (suc xF) pF)) (suc xF)));
    val s2 = subSSS2_at (suc (add xF pF), xF);    (* oeq (sub (Suc (Suc (add x p)))(Suc x)) (sub (Suc (add x p)) x) *)
    val s12 = oeq_trans OF [s1, s2];
    val stepconcl = oeq_trans OF [s12, IH];
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_sub_Suc_add_l = jT (oeq (sub (suc (add kVs pVs)) kVs) (suc pVs));
val r_sub_Suc_add_l = checkSub ("sub_Suc_add_l", sub_Suc_add_l, i_sub_Suc_add_l);

(* ground instantiators for the two add-cancel laws on ctxtSub *)
val sub_add_l_vS2     = varify sub_add_l;
val sub_Suc_add_l_vS2 = varify sub_Suc_add_l;
fun subAddL_at (kt,jt) = beta_norm (Drule.infer_instantiate ctxtSub
                            [(("k",0), ctermSub kt),(("j",0), ctermSub jt)] sub_add_l_vS2);
fun subSucAddL_at (kt,pt) = beta_norm (Drule.infer_instantiate ctxtSub
                            [(("k",0), ctermSub kt),(("p",0), ctermSub pt)] sub_Suc_add_l_vS2);

(* ============================================================================
   3.  sub_Suc_le : jT (le k n) ==> jT (oeq (sub (Suc n) k) (Suc (sub n k)))
       exE on le k n -> witness w with  oeq n (add k w) ; transport.
   ============================================================================ *)
val sub_Suc_le =
  let
    val kF = Free("k", natT); val nF = Free("n", natT);
    val leHyp = jT (le kF nF);
    val H = Thm.assume (ctermSub leHyp);
    val goalBody = oeq (sub (suc nF) kF) (suc (sub nF kF));
    val lePabs = Abs("p", natT, oeq nF (add kF (Bound 0)));
    fun body wF (hw : thm) =          (* hw : oeq n (add k w) *)
      let
        val lhs = subSucAddL_at (kF, wF);          (* oeq (sub (Suc (add k w)) k) (Suc w) *)
        val sal = subAddL_at (kF, wF);             (* oeq (sub (add k w) k) w *)
        val salS = Suc_cong OF [sal];              (* oeq (Suc (sub (add k w) k)) (Suc w) *)
        val salSsym = oeq_sym OF [salS];           (* oeq (Suc w) (Suc (sub (add k w) k)) *)
        val core = oeq_trans OF [lhs, salSsym];    (* oeq (sub (Suc (add k w)) k)(Suc (sub (add k w) k)) *)
        val hwS = oeq_sym OF [hw];                 (* oeq (add k w) n *)
        val Ptr = Abs("z", natT, oeq (sub (suc (Bound 0)) kF) (suc (sub (Bound 0) kF)));
        val res = substPredS2 (Ptr, add kF wF, nF) hwS core;  (* jT (Ptr n) = goalBody *)
      in res end;
    val concl = exE_elimS2 (lePabs, goalBody) H "w" body;
    val d1 = Thm.implies_intr (ctermSub leHyp) concl;
  in varify d1 end;

val i_sub_Suc_le =
  Logic.mk_implies (jT (le kVs nVs),
    jT (oeq (sub (suc nVs) kVs) (suc (sub nVs kVs))));
val r_sub_Suc_le = checkSub ("sub_Suc_le", sub_Suc_le, i_sub_Suc_le);

val s_subSucle_needs_le =
  not ((Thm.prop_of sub_Suc_le) aconv
        (jT (oeq (sub (suc nVs) kVs) (suc (sub nVs kVs)))));

(* sumf ground instantiators on ctxtSub *)
fun sumf0_at fT       = beta_norm (Drule.infer_instantiate ctxtSub [(("f",0), ctermSub fT)] sumf_0_vS2);
fun sumfSuc_at (fT,nt)= beta_norm (Drule.infer_instantiate ctxtSub
                          [(("f",0), ctermSub fT),(("n",0), ctermSub nt)] sumf_Suc_vS2);

(* ============================================================================
   4.  sum_cong :
        (!!k. jT (le k n) ==> jT (oeq (f k)(g k))) ==> jT (oeq (sumf f n)(sumf g n))
       INDUCTION on n with the hypothesis REFLECTED into the OBJECT predicate so
       it rides along nat_induct :
         hypObj z = Forall (%k. Imp (le k z) (oeq (f k)(g k)))
         P z      = Imp (hypObj z) (oeq (sumf f z)(sumf g z))
       Prove jT (P n) by induction; then convert the meta-hyp -> jT (hypObj n)
       (allI over impI on the meta-implication) and mp.
   ============================================================================ *)
val sum_cong =
  let
    val fF = Free("f", fnT); val gF = Free("g", fnT);
    (* CAPTURE-SAFE construction : `le` is only valid on terms WITHOUT dangling de
       Bruijn indices (it wraps its 1st arg under a fresh Abs("p",..)).  So build
       every abstraction over a Free "k"/"z" and abstract it with Term.lambda. *)
    val kAbsV = Free("k", natT);
    (* the object-Forall hypothesis at z : Forall (%k. Imp (le k z)(f k = g k)) *)
    fun hypObjAbs zt =
      Term.lambda kAbsV (mkImp (le kAbsV zt) (oeq (fF $ kAbsV) (gF $ kAbsV)));
    fun hypObj zt = mkForall (hypObjAbs zt);
    fun concBody zt = oeq (sumf fF zt) (sumf gF zt);

    (* induction predicate P z = Imp (hypObj z)(concBody z), capture-safe *)
    val zAbsV = Free("z", natT);
    val Qpred = Term.lambda zAbsV (mkImp (hypObj zAbsV) (concBody zAbsV));
    val nIndV = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nIndV);

    (* ---- BASE : jT (Imp (hypObj 0)(concBody 0)) ---- *)
    val base =
      let
        val hyp0 = Thm.assume (ctermSub (jT (hypObj ZeroC)));   (* jT (Forall (%k. Imp (le k 0)(f k=g k))) *)
        (* allE @ 0 : jT (Imp (le 0 0)(f 0 = g 0)) *)
        val imp00 = allE_S2 (hypObjAbs ZeroC) ZeroC hyp0;
        val le00 = le_reflS2_at ZeroC;                          (* le 0 0 *)
        val f0g0 = mp_S2 (le ZeroC ZeroC, oeq (fF $ ZeroC) (gF $ ZeroC)) imp00 le00;  (* f 0 = g 0 *)
        val sf0 = sumf0_at fF;                                  (* sumf f 0 = f 0 *)
        val sg0 = sumf0_at gF;                                  (* sumf g 0 = g 0 *)
        val sg0sym = oeq_sym OF [sg0];                          (* g 0 = sumf g 0 *)
        val concl0 = oeq_trans OF [oeq_trans OF [sf0, f0g0], sg0sym];  (* sumf f 0 = sumf g 0 *)
        val dis = Thm.implies_intr (ctermSub (jT (hypObj ZeroC))) concl0;
      in impI_S2 (hypObj ZeroC, concBody ZeroC) dis end;

    (* ---- STEP : assume IH : jT (P x) ; prove jT (P (Suc x)) ---- *)
    val xF = Free("x", natT);
    val ihprop = jT (mkImp (hypObj xF) (concBody xF));
    val IH = Thm.assume (ctermSub ihprop);
    val stepConcl =
      let
        (* assume jT (hypObj (Suc x)) ; derive concBody (Suc x) *)
        val hypSx = Thm.assume (ctermSub (jT (hypObj (suc xF))));
        (* build jT (hypObj x) : allI over (!!k. jT (Imp (le k x)(f k=g k))) *)
        val kk = Free("k", natT);
        (* from hypSx allE @ k : jT (Imp (le k (Suc x))(f k=g k)) *)
        val impSx_k = allE_S2 (hypObjAbs (suc xF)) kk hypSx;
        (* meta-derive jT (Imp (le k x)(f k=g k)) via impI : assume le k x, weaken to le k (Suc x), mp *)
        val le_k_x = Thm.assume (ctermSub (jT (le kk xF)));
        val le_x_Sx = le_suc_selfS2_at xF;                      (* le x (Suc x) *)
        val le_k_Sx = le_transS2_at (kk, xF, suc xF) le_k_x le_x_Sx;  (* le k (Suc x) *)
        val fk_gk = mp_S2 (le kk (suc xF), oeq (fF $ kk) (gF $ kk)) impSx_k le_k_Sx;  (* f k = g k *)
        val impx_k_dis = Thm.implies_intr (ctermSub (jT (le kk xF))) fk_gk;  (* meta : le k x ==> f k = g k *)
        val impx_k = impI_S2 (le kk xF, oeq (fF $ kk) (gF $ kk)) impx_k_dis; (* jT (Imp (le k x)(f k=g k)) *)
        (* allI : !!k. jT (Imp (le k x)(f k=g k)) -> jT (hypObj x) *)
        val allMinor = Thm.forall_intr (ctermSub kk) impx_k;    (* !!k. jT ((hypObjAbs x) k) up to beta *)
        val hypObjx = allI_S2 (hypObjAbs xF) allMinor;          (* jT (hypObj x) *)
        (* mp IH with hypObjx : concBody x = sumf f x = sumf g x *)
        val sumfx_eq = mp_S2 (hypObj xF, concBody xF) IH hypObjx;  (* sumf f x = sumf g x *)
        (* f (Suc x) = g (Suc x) : allE hypSx @ (Suc x), mp with le (Suc x)(Suc x) *)
        val impSx_Sx = allE_S2 (hypObjAbs (suc xF)) (suc xF) hypSx;  (* Imp (le (Sx)(Sx))(f Sx=g Sx) *)
        val le_Sx_Sx = le_reflS2_at (suc xF);
        val fSx_gSx = mp_S2 (le (suc xF) (suc xF), oeq (fF $ (suc xF)) (gF $ (suc xF))) impSx_Sx le_Sx_Sx;
        (* sumf_Suc both sides + add congruence *)
        val sfS = sumfSuc_at (fF, xF);                          (* sumf f (Sx) = add (sumf f x)(f Sx) *)
        val sgS = sumfSuc_at (gF, xF);                          (* sumf g (Sx) = add (sumf g x)(g Sx) *)
        val cL = add_cong_lS2 (sumf fF xF, sumf gF xF, fF $ (suc xF)) sumfx_eq;
        val cR = add_cong_rS2 (sumf gF xF, fF $ (suc xF), gF $ (suc xF)) fSx_gSx;
        val mid = oeq_trans OF [cL, cR];
        val sgS_s = oeq_sym OF [sgS];                           (* add (sumf g x)(g Sx) = sumf g (Sx) *)
        val concl = oeq_trans OF [oeq_trans OF [sfS, mid], sgS_s];  (* sumf f (Sx) = sumf g (Sx) *)
        val dis = Thm.implies_intr (ctermSub (jT (hypObj (suc xF)))) concl;
      in impI_S2 (hypObj (suc xF), concBody (suc xF)) dis end;
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepConcl);

    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;    (* r2 : jT (P n) = jT (Imp (hypObj n)(concBody n)) ; n = nIndV *)

    (* ---- CONVERT meta-hyp -> jT (hypObj n) -> concBody n ; discharge meta-hyp ---- *)
    val kk2 = Free("k", natT);
    val metaHyp = Logic.all kk2 (Logic.mk_implies (jT (le kk2 nIndV), jT (oeq (fF $ kk2) (gF $ kk2))));
    val Hm = Thm.assume (ctermSub metaHyp);                     (* !!k. le k n ==> f k = g k *)
    val Hm_k = Thm.forall_elim (ctermSub kk2) Hm;              (* le k n ==> f k = g k (meta) *)
    val impn_k = impI_S2 (le kk2 nIndV, oeq (fF $ kk2) (gF $ kk2)) Hm_k;  (* jT (Imp (le k n)(f k=g k)) *)
    val allMinor2 = Thm.forall_intr (ctermSub kk2) impn_k;
    val hypObjn = allI_S2 (hypObjAbs nIndV) allMinor2;         (* jT (hypObj n) *)
    val concln = mp_S2 (hypObj nIndV, concBody nIndV) r2 hypObjn;  (* oeq (sumf f n)(sumf g n) *)
    val d1 = Thm.implies_intr (ctermSub metaHyp) concln;
  in varify d1 end;

(* intended statement, schematic on ctxtSub. f,g are function Vars. *)
val i_sum_cong =
  let
    val kk = Free("k", natT)
  in
    Logic.mk_implies (
      Logic.all kk (Logic.mk_implies (jT (le kk nVs), jT (oeq (fVs $ kk) (gVs $ kk)))),
      jT (oeq (sumf fVs nVs) (sumf gVs nVs)))
  end;
val r_sum_cong = checkSub ("sum_cong", sum_cong, i_sum_cong);

val s_sumcong_needs_hyp =
  not ((Thm.prop_of sum_cong) aconv (jT (oeq (sumf fVs nVs) (sumf gVs nVs))));

(* ============================================================================
   STAGE C1 FINAL VALIDATION
   ============================================================================ *)
val () =
  if s_subSucle_needs_le andalso s_sumcong_needs_hyp
  then out "SUMSUB_PROBE_OK conditional laws nontrivial\n"
  else out "SUMSUB_PROBE_FAIL a law collapsed!\n";

val () =
  if r_sub_n_0_ax andalso r_sub_0_Suc_ax andalso r_sub_SS_ax
     andalso r_sumf_0_ax andalso r_sumf_Suc_ax
     andalso r_sub_self andalso r_sub_add_l andalso r_sub_Suc_add_l
     andalso r_sub_Suc_le andalso r_sum_cong
     andalso s_subSucle_needs_le andalso s_sumcong_needs_hyp
  then out "SUMSUB_DONE\n"
  else out "SUMSUB_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  STAGE C2 FOUNDATION : SUM-ALGEBRA LEMMAS for the BINOMIAL THEOREM  ***
   ----------------------------------------------------------------------------
   On the final context ctxtSub / ctermSub (theory thySub : sub + sumf on top of
   thyB which carries binom + pow + the full semiring).  We re-varify the pow,
   binom and semiring axioms onto ctxtSub, build mult-congruence + ground
   instantiators there, then prove:
     sum_mult_l    : oeq (mult c (sumf f n)) (sumf (%k. mult c (f k)) n)
     sum_add       : oeq (add (sumf f n)(sumf g n)) (sumf (%k. add (f k)(g k)) n)
     sum_peel_first: oeq (sumf f (Suc n)) (add (f 0) (sumf (%k. f (Suc k)) n))
     binom_n_n     : oeq (binom n n) (Suc Zero)
   plus helper lemmas binom_lt_0 / binom_n_Suc_n and pow_b_sub_Suc.
   ============================================================================ *)

val () = out "SUMALG_BEGIN\n";

(* ---- re-varify the semiring / pow / binom axioms onto ctxtSub ---- *)
val mult_comm_vS2     = varify mult_comm;       (* oeq (mult m n)(mult n m)             *)
val mult_assoc_vS2    = varify mult_assoc;      (* oeq (mult (mult m n) k)(mult m (mult n k)) *)
val left_distrib_vS2  = varify left_distrib;    (* oeq (mult x (add m n))(add (mult x m)(mult x n)) *)
val right_distrib_vS2 = varify right_distrib;   (* oeq (mult (add m n) k)(add (mult m k)(mult n k)) *)

val pow_Zero_vS2      = varify pow_Zero_ax;     (* oeq (pow a 0)(Suc 0)                 *)
val pow_Suc_vS2       = varify pow_Suc_ax;      (* oeq (pow a (Suc n))(mult a (pow a n)) *)

val binom_n_0_vS2     = varify binom_n_0_ax;    (* oeq (binom n 0)(Suc 0)              *)
val binom_0_Suc_vS2   = varify binom_0_Suc_ax;  (* oeq (binom 0 (Suc k)) 0             *)
val binom_Suc_Suc_vS2 = varify binom_Suc_Suc_ax;(* Pascal                              *)

(* ---- ground instantiators on ctxtSub ---- *)
fun multcommS2_at (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt),(("n",0), ctermSub nt)] mult_comm_vS2);
fun ldistS2_at (xt,mt,nt)  = beta_norm (Drule.infer_instantiate ctxtSub
        [(("x",0), ctermSub xt),(("m",0), ctermSub mt),(("n",0), ctermSub nt)] left_distrib_vS2);

fun powZeroS2_at t         = beta_norm (Drule.infer_instantiate ctxtSub
        [(("a",0), ctermSub t)] pow_Zero_vS2);
fun powSucS2_at (at,nt)    = beta_norm (Drule.infer_instantiate ctxtSub
        [(("a",0), ctermSub at),(("n",0), ctermSub nt)] pow_Suc_vS2);

fun binomN0S2_at t         = beta_norm (Drule.infer_instantiate ctxtSub
        [(("n",0), ctermSub t)] binom_n_0_vS2);
fun binom0SS2_at t         = beta_norm (Drule.infer_instantiate ctxtSub
        [(("k",0), ctermSub t)] binom_0_Suc_vS2);
fun binomSSS2_at (nt,kt)   = beta_norm (Drule.infer_instantiate ctxtSub
        [(("n",0), ctermSub nt),(("k",0), ctermSub kt)] binom_Suc_Suc_vS2);

(* ---- mult congruence on ctxtSub (left/right operand) ---- *)
fun mult_cong_lS2 (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("a",0), ctermSub pT), (("b",0), ctermSub qT)] oeq_subst_vS2);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub (mult pT kT))] oeq_refl_vS2);
  in inst OF [hpq, refl_pk] end;
fun mult_cong_rS2 (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("a",0), ctermSub pT), (("b",0), ctermSub qT)] oeq_subst_vS2);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub (mult hT pT))] oeq_refl_vS2);
  in inst OF [hpq, refl_hp] end;

(* schematic Var for the constant multiplier c (nat) on ctxtSub *)
val cVc = Var (("c",0), natT);

(* ============================================================================
   1.  sum_mult_l : oeq (mult c (sumf f n)) (sumf (%k. mult c (f k)) n)
       induction on n.  summand g = Abs("k", mult c (f k)).
   ============================================================================ *)
val sum_mult_l =
  let
    val cF = Free("c", natT);
    val fF = Free("f", fnT);
    (* canonical summand lambda : %k. mult c (f k) *)
    val gAbs = Abs("k", natT, mult cF (fF $ (Bound 0)));
    fun g_at t = mult cF (fF $ t);              (* beta-reduced application g $ t *)

    val Qpred = Abs("z", natT, oeq (mult cF (sumf fF (Bound 0))) (sumf gAbs (Bound 0)));
    val nF = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nF);

    (* ---- BASE n = 0 ---- *)
    val base =
      let
        val sf0 = sumf0_at fF;                                  (* sumf f 0 = f 0 *)
        val cL  = mult_cong_rS2 (cF, sumf fF ZeroC, fF $ ZeroC) sf0;  (* mult c (sumf f 0) = mult c (f 0) *)
        val sg0 = sumf0_at gAbs;                                (* sumf g 0 = g 0 = mult c (f 0) [beta] *)
        val sg0sym = oeq_sym OF [sg0];                          (* mult c (f 0) = sumf g 0 *)
      in oeq_trans OF [cL, sg0sym] end;

    (* ---- STEP ---- *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (mult cF (sumf fF xF)) (sumf gAbs xF));
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        val sfS = sumfSuc_at (fF, xF);                          (* sumf f (Sx) = add (sumf f x)(f (Sx)) *)
        val cL  = mult_cong_rS2 (cF, sumf fF (suc xF), add (sumf fF xF) (fF $ (suc xF))) sfS;
                  (* mult c (sumf f (Sx)) = mult c (add (sumf f x)(f (Sx))) *)
        val ld  = ldistS2_at (cF, sumf fF xF, fF $ (suc xF));
                  (* mult c (add (sumf f x)(f Sx)) = add (mult c (sumf f x))(mult c (f Sx)) *)
        val lhs = oeq_trans OF [cL, ld];
                  (* mult c (sumf f (Sx)) = add (mult c (sumf f x))(mult c (f Sx)) *)
        (* RHS : sumf g (Sx) = add (sumf g x)(g Sx) = add (mult c (sumf f x))(mult c (f Sx)) *)
        val sgS = sumfSuc_at (gAbs, xF);                        (* sumf g (Sx) = add (sumf g x)(g Sx) [g Sx beta = mult c (f Sx)] *)
        val cIH = add_cong_lS2 (sumf gAbs xF, mult cF (sumf fF xF), g_at (suc xF)) (oeq_sym OF [IH]);
                  (* add (sumf g x)(g Sx) = add (mult c (sumf f x))(g Sx) ; g Sx = mult c (f Sx) *)
        val rhs = oeq_trans OF [sgS, cIH];
                  (* sumf g (Sx) = add (mult c (sumf f x))(mult c (f Sx)) *)
        val rhsSym = oeq_sym OF [rhs];
      in oeq_trans OF [lhs, rhsSym] end;
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_sum_mult_l =
  let val gV = Abs("k", natT, mult cVc (fVs $ (Bound 0)))
  in jT (oeq (mult cVc (sumf fVs nVs)) (sumf gV nVs)) end;
val r_sum_mult_l = checkSub ("sum_mult_l", sum_mult_l, i_sum_mult_l);

(* ============================================================================
   2.  sum_add : oeq (add (sumf f n)(sumf g n)) (sumf (%k. add (f k)(g k)) n)
       induction on n + add4_swap-style reshuffle.
   ============================================================================ *)
(* add4_swap on ctxtSub : reorder (A+B)+(C+D) -> (A+C)+(B+D) *)
fun add4_swapS2 (A,B,C,D) =
  let
    val asbcd = addassocS2_at (A, B, add C D);
    val i1 = addassocS2_at (B, C, D);
    val i1s = oeq_sym OF [i1];
    val icc = addcommS2_at (B, C);
    val i2 = add_cong_lS2 (add B C, add C B, D) icc;
    val i3 = addassocS2_at (C, B, D);
    val inner = oeq_trans OF [oeq_trans OF [i1s, i2], i3];
    val cInner = add_cong_rS2 (A, add B (add C D), add C (add B D)) inner;
    val r1 = oeq_trans OF [asbcd, cInner];
    val r2assoc = addassocS2_at (A, C, add B D);
    val r2assoc_s = oeq_sym OF [r2assoc];
  in oeq_trans OF [r1, r2assoc_s] end

(* need add_comm/add_assoc instantiators on ctxtSub *)
and addcommS2_at (mt,nt)     = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt),(("n",0), ctermSub nt)] (varify add_comm))
and addassocS2_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt),(("n",0), ctermSub nt),(("k",0), ctermSub kt)] (varify add_assoc));

val sum_add =
  let
    val fF = Free("f", fnT); val gF = Free("g", fnT);
    val hAbs = Abs("k", natT, add (fF $ (Bound 0)) (gF $ (Bound 0)));  (* %k. add (f k)(g k) *)
    fun h_at t = add (fF $ t) (gF $ t);

    val Qpred = Abs("z", natT, oeq (add (sumf fF (Bound 0)) (sumf gF (Bound 0))) (sumf hAbs (Bound 0)));
    val nF = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nF);

    (* ---- BASE n = 0 :  add (sumf f 0)(sumf g 0) = add (f 0)(g 0) = sumf h 0 ---- *)
    val base =
      let
        val sf0 = sumf0_at fF;                                  (* sumf f 0 = f 0 *)
        val sg0 = sumf0_at gF;                                  (* sumf g 0 = g 0 *)
        val cL  = add_cong_lS2 (sumf fF ZeroC, fF $ ZeroC, sumf gF ZeroC) sf0;
                  (* add (sumf f 0)(sumf g 0) = add (f 0)(sumf g 0) *)
        val cR  = add_cong_rS2 (fF $ ZeroC, sumf gF ZeroC, gF $ ZeroC) sg0;
                  (* add (f 0)(sumf g 0) = add (f 0)(g 0) *)
        val sh0 = sumf0_at hAbs;                                (* sumf h 0 = h 0 = add (f 0)(g 0) [beta] *)
        val sh0sym = oeq_sym OF [sh0];
      in oeq_trans OF [oeq_trans OF [cL, cR], sh0sym] end;

    (* ---- STEP ---- *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (add (sumf fF xF) (sumf gF xF)) (sumf hAbs xF));
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        val sfS = sumfSuc_at (fF, xF);                          (* sumf f (Sx) = add (sumf f x)(f Sx) *)
        val sgS = sumfSuc_at (gF, xF);                          (* sumf g (Sx) = add (sumf g x)(g Sx) *)
        (* LHS = add (sumf f (Sx))(sumf g (Sx)) = add (add (sumf f x)(f Sx))(add (sumf g x)(g Sx)) *)
        val cL  = add_cong_lS2 (sumf fF (suc xF), add (sumf fF xF) (fF $ (suc xF)), sumf gF (suc xF)) sfS;
        val cR  = add_cong_rS2 (add (sumf fF xF) (fF $ (suc xF)), sumf gF (suc xF), add (sumf gF xF) (gF $ (suc xF))) sgS;
        val lhs1 = oeq_trans OF [cL, cR];
                  (* add (sumf f (Sx))(sumf g (Sx)) = add (add (sumf f x)(f Sx))(add (sumf g x)(g Sx)) *)
        (* reshuffle to add (add (sumf f x)(sumf g x))(add (f Sx)(g Sx)) *)
        val swap = add4_swapS2 (sumf fF xF, fF $ (suc xF), sumf gF xF, gF $ (suc xF));
        val lhs2 = oeq_trans OF [lhs1, swap];
        (* IH on left summand : add (sumf f x)(sumf g x) = sumf h x *)
        val cIH = add_cong_lS2 (add (sumf fF xF) (sumf gF xF), sumf hAbs xF, add (fF $ (suc xF)) (gF $ (suc xF))) IH;
        val lhs3 = oeq_trans OF [lhs2, cIH];
                  (* = add (sumf h x)(add (f Sx)(g Sx)) *)
        (* RHS : sumf h (Sx) = add (sumf h x)(h Sx) ; h Sx beta = add (f Sx)(g Sx) *)
        val shS = sumfSuc_at (hAbs, xF);
        val shSsym = oeq_sym OF [shS];
      in oeq_trans OF [lhs3, shSsym] end;
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_sum_add =
  let val hV = Abs("k", natT, add (fVs $ (Bound 0)) (gVs $ (Bound 0)))
  in jT (oeq (add (sumf fVs nVs) (sumf gVs nVs)) (sumf hV nVs)) end;
val r_sum_add = checkSub ("sum_add", sum_add, i_sum_add);

(* ============================================================================
   3.  sum_peel_first :
        oeq (sumf f (Suc n)) (add (f Zero) (sumf (%k. f (Suc k)) n))
       induction on n.
   ============================================================================ *)
val sum_peel_first =
  let
    val fF = Free("f", fnT);
    val tAbs = Abs("k", natT, fF $ (suc (Bound 0)));   (* %k. f (Suc k) *)
    fun t_at t = fF $ (suc t);

    (* P z = oeq (sumf f (Suc z)) (add (f 0)(sumf tAbs z)) *)
    val Qpred = Abs("z", natT, oeq (sumf fF (suc (Bound 0))) (add (fF $ ZeroC) (sumf tAbs (Bound 0))));
    val nF = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nF);

    (* ---- BASE n = 0 :  sumf f (Suc 0) = add (sumf f 0)(f (Suc 0)) = add (f 0)(f (Suc 0))
                          RHS add (f 0)(sumf tAbs 0) = add (f 0)(t 0) = add (f 0)(f (Suc 0)) ---- *)
    val base =
      let
        val sfS0 = sumfSuc_at (fF, ZeroC);                      (* sumf f (Suc 0) = add (sumf f 0)(f (Suc 0)) *)
        val sf0  = sumf0_at fF;                                 (* sumf f 0 = f 0 *)
        val cL   = add_cong_lS2 (sumf fF ZeroC, fF $ ZeroC, fF $ (suc ZeroC)) sf0;
                   (* add (sumf f 0)(f (Suc 0)) = add (f 0)(f (Suc 0)) *)
        val lhs  = oeq_trans OF [sfS0, cL];                     (* sumf f (Suc 0) = add (f 0)(f (Suc 0)) *)
        val st0  = sumf0_at tAbs;                               (* sumf tAbs 0 = t 0 = f (Suc 0) [beta] *)
        val cR   = add_cong_rS2 (fF $ ZeroC, fF $ (suc ZeroC), sumf tAbs ZeroC) (oeq_sym OF [st0]);
                   (* add (f 0)(f (Suc 0)) = add (f 0)(sumf tAbs 0) *)
      in oeq_trans OF [lhs, cR] end;

    (* ---- STEP : assume sumf f (Sx) = add (f 0)(sumf tAbs x) ; prove for Suc x ---- *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (sumf fF (suc xF)) (add (fF $ ZeroC) (sumf tAbs xF)));
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        (* LHS : sumf f (Suc (Suc x)) = add (sumf f (Suc x))(f (Suc (Suc x))) *)
        val sfSS = sumfSuc_at (fF, suc xF);
        (* rewrite the (sumf f (Suc x)) summand via IH *)
        val cIH = add_cong_lS2 (sumf fF (suc xF), add (fF $ ZeroC) (sumf tAbs xF), fF $ (suc (suc xF))) IH;
        val lhs1 = oeq_trans OF [sfSS, cIH];
                   (* = add (add (f 0)(sumf tAbs x))(f (Suc (Suc x))) *)
        (* re-associate to add (f 0)(add (sumf tAbs x)(f (Suc (Suc x)))) *)
        val reassoc = addassocS2_at (fF $ ZeroC, sumf tAbs xF, fF $ (suc (suc xF)));
        val lhs2 = oeq_trans OF [lhs1, reassoc];
        (* RHS : add (f 0)(sumf tAbs (Suc x)) ; sumf tAbs (Suc x) = add (sumf tAbs x)(t (Suc x))
                 t (Suc x) beta = f (Suc (Suc x)) *)
        val stS = sumfSuc_at (tAbs, xF);                        (* sumf tAbs (Suc x) = add (sumf tAbs x)(f (Suc (Suc x))) *)
        val stSsym = oeq_sym OF [stS];                          (* add (sumf tAbs x)(f (Suc (Suc x))) = sumf tAbs (Suc x) *)
        val cRHS = add_cong_rS2 (fF $ ZeroC, add (sumf tAbs xF) (t_at (suc xF)), sumf tAbs (suc xF)) stSsym;
                   (* add (f 0)(add (sumf tAbs x)(f (SSx))) = add (f 0)(sumf tAbs (Suc x)) *)
      in oeq_trans OF [lhs2, cRHS] end;
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_sum_peel_first =
  let val tV = Abs("k", natT, fVs $ (suc (Bound 0)))
  in jT (oeq (sumf fVs (suc nVs)) (add (fVs $ ZeroC) (sumf tV nVs))) end;
val r_sum_peel_first = checkSub ("sum_peel_first", sum_peel_first, i_sum_peel_first);

(* ============================================================================
   HELPER  binom_lt_0 : jT (lt n k) ==> jT (oeq (binom n k) Zero)
       (n < k  =>  C(n,k) = 0).  Reflect the bound into the object predicate and
       induct on n with k UNIVERSAL (object Forall), inner case-split on k.
       We instead use a direct double-induction-free route:  induction on n with a
       Forall over k inside, using lt n k.

   We take the simplest robust path : prove binom_n_Suc_n directly by induction.
       binom_n_Suc_n : oeq (binom n (Suc n)) Zero        (C(n,n+1) = 0)
       induction on n :
         base : binom 0 (Suc 0) = 0           [binom_0_Suc]
         step : binom (Suc x)(Suc (Suc x)) = binom x (Suc x) + binom x (Suc (Suc x))  [Pascal]
                = 0 + binom x (Suc(Suc x))    [IH on first summand]
                BUT binom x (Suc(Suc x)) is C(x, x+2), need it = 0 too.
       So a single induction on n is NOT enough : we need n<k generally.  Prove
       binom_lt_0 by induction on n with k universally quantified (object Forall).
   ============================================================================ *)
(* lt is defined as : lt m n  ==  le (Suc m) n  (strict order).  Locate it. *)

(* binom right-argument congruence on ctxtSub : oeq u v ==> oeq (binom n u)(binom n v) *)
fun binom_cong_r2 (nT, uT, vT) huv =
  let
    val Pabs = Abs("z", natT, oeq (binom nT uT) (binom nT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("a",0), ctermSub uT), (("b",0), ctermSub vT)] oeq_subst_vS2);
    val refl_nu = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub (binom nT uT))] oeq_refl_vS2);
  in inst OF [huv, refl_nu] end;

(* ============================================================================
   HELPER  binom_diag_zero : (!!j. nothing) — object Forall over j :
        P n  ==  Forall (%j. oeq (binom n (add (Suc n) j)) Zero)
        i.e.  for all j, C(n, n+1+j) = 0.   Induction on n.
   ============================================================================ *)
val binom_diag_zero =
  let
    val jAbsV = Free("j", natT);
    fun bodyAt nt jt = oeq (binom nt (add (suc nt) jt)) ZeroC;
    fun predAbs nt = Term.lambda jAbsV (bodyAt nt jAbsV);   (* %j. binom n (n+1+j) = 0 *)
    fun predForall nt = mkForall (predAbs nt);

    val zAbsV = Free("z", natT);
    val Qpred = Term.lambda zAbsV (predForall zAbsV);
    val nIndV = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nIndV);

    (* ---- BASE n = 0 : forall j. binom 0 (add (Suc 0) j) = 0 ---- *)
    val base =
      let
        val jF = Free("j", natT);
        (* add (Suc 0) j = Suc (add 0 j) = Suc j *)
        val aS = addSucS2_at (ZeroC, jF);                 (* add (Suc 0) j = Suc (add 0 j) *)
        val a0 = add0S2_at jF;                            (* add 0 j = j *)
        val a0S = Suc_cong OF [a0];                       (* Suc (add 0 j) = Suc j *)
        val addEq = oeq_trans OF [aS, a0S];               (* add (Suc 0) j = Suc j *)
        (* binom 0 (add (Suc 0) j) = binom 0 (Suc j) = 0 *)
        val cong = binom_cong_r2 (ZeroC, add (suc ZeroC) jF, suc jF) addEq;  (* binom 0 (n1+j) = binom 0 (Suc j) *)
        val b0Sj = binom0SS2_at jF;                       (* binom 0 (Suc j) = 0 *)
        val body0 = oeq_trans OF [cong, b0Sj];            (* binom 0 (add (Suc 0) j) = 0 *)
        val allMinor = Thm.forall_intr (ctermSub jF) body0;  (* !!j. jT (binom 0 (add (Suc 0) j) = 0) up to beta *)
      in allI_S2 (predAbs ZeroC) allMinor end;            (* jT (Forall (%j. ...)) *)

    (* ---- STEP : assume P x ; prove P (Suc x) ---- *)
    val xF = Free("x", natT);
    val ihprop = jT (predForall xF);
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        val jF = Free("j", natT);
        (* goal body at (Suc x), j : binom (Suc x)(add (Suc(Suc x)) j) = 0 *)
        (* add (Suc(Suc x)) j = Suc (add (Suc x) j)   [add_Suc] *)
        val aS = addSucS2_at (suc xF, jF);                (* add (Suc(Suc x)) j = Suc (add (Suc x) j) *)
        val mTerm = add (suc xF) jF;                      (* m := add (Suc x) j *)
        (* binom (Suc x)(add (Suc(Suc x)) j) = binom (Suc x)(Suc m)  [cong on 2nd arg] *)
        val cong0 = binom_cong_r2 (suc xF, add (suc (suc xF)) jF, suc mTerm) aS;
        (* Pascal : binom (Suc x)(Suc m) = add (binom x m)(binom x (Suc m)) *)
        val pasc = binomSSS2_at (xF, mTerm);
        val lhs1 = oeq_trans OF [cong0, pasc];
                   (* binom (Suc x)(...) = add (binom x m)(binom x (Suc m)) *)
        (* binom x m = binom x (add (Suc x) j) = 0  via IH @ j *)
        val IH_j = allE_S2 (predAbs xF) jF IH;            (* jT (binom x (add (Suc x) j) = 0) *)
        (* binom x (Suc m) : Suc m = Suc (add (Suc x) j) = add (Suc x)(Suc j)  [add_Suc_right sym] *)
        val aSr = addSrS2_at (suc xF, jF);                (* add (Suc x)(Suc j) = Suc (add (Suc x) j) = Suc m *)
        val aSrsym = oeq_sym OF [aSr];                    (* Suc m = add (Suc x)(Suc j) *)
        val congSm = binom_cong_r2 (xF, suc mTerm, add (suc xF) (suc jF)) aSrsym;
                     (* binom x (Suc m) = binom x (add (Suc x)(Suc j)) *)
        val IH_Sj = allE_S2 (predAbs xF) (suc jF) IH;     (* jT (binom x (add (Suc x)(Suc j)) = 0) *)
        val bxSm0 = oeq_trans OF [congSm, IH_Sj];         (* binom x (Suc m) = 0 *)
        (* assemble : add (binom x m)(binom x (Suc m)) = add 0 0 = 0 *)
        val cL = add_cong_lS2 (binom xF mTerm, ZeroC, binom xF (suc mTerm)) IH_j;
                 (* add (binom x m)(binom x (Suc m)) = add 0 (binom x (Suc m)) *)
        val cR = add_cong_rS2 (ZeroC, binom xF (suc mTerm), ZeroC) bxSm0;
                 (* add 0 (binom x (Suc m)) = add 0 0 *)
        val a00 = add0S2_at ZeroC;                        (* add 0 0 = 0 *)
        val rhs = oeq_trans OF [oeq_trans OF [cL, cR], a00];  (* add (..)(..) = 0 *)
        val body = oeq_trans OF [lhs1, rhs];              (* binom (Suc x)(add (Suc(Suc x)) j) = 0 *)
        val allMinor = Thm.forall_intr (ctermSub jF) body;
      in allI_S2 (predAbs (suc xF)) allMinor end;
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;    (* r2 : jT (Forall (%j. binom n (add (Suc n) j) = 0)) ; n = nIndV *)
  in varify r2 end;

(* binom_n_Suc_n : oeq (binom n (Suc n)) Zero
     instantiate binom_diag_zero @ j := 0, then add (Suc n) 0 = Suc n. *)
val binom_diag_zero_vS2 = varify binom_diag_zero;
val binom_n_Suc_n =
  let
    val nF = Free("n", natT);
    (* instantiate the forall (over n) version at n := nF, then allE @ 0 *)
    val diag_n = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub nF)] binom_diag_zero_vS2);
                 (* jT (Forall (%j. binom n (add (Suc n) j) = 0)) *)
    val predAbsN = Abs("j", natT, oeq (binom nF (add (suc nF) (Bound 0))) ZeroC);
    val at0 = allE_S2 predAbsN ZeroC diag_n;              (* jT (binom n (add (Suc n) 0) = 0) *)
    (* add (Suc n) 0 = Suc n *)
    val a0r = add0rS2_at (suc nF);                        (* add (Suc n) 0 = Suc n *)
    val cong = binom_cong_r2 (nF, suc nF, add (suc nF) ZeroC) (oeq_sym OF [a0r]);
               (* binom n (Suc n) = binom n (add (Suc n) 0) *)
    val res = oeq_trans OF [cong, at0];                   (* binom n (Suc n) = 0 *)
  in varify res end;

val i_binom_n_Suc_n = jT (oeq (binom nVs (suc nVs)) ZeroC);
val r_binom_n_Suc_n = checkSub ("binom_n_Suc_n", binom_n_Suc_n, i_binom_n_Suc_n);

(* ground instantiator for binom_n_Suc_n on ctxtSub *)
val binom_n_Suc_n_vS2 = varify binom_n_Suc_n;
fun binomNSn_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] binom_n_Suc_n_vS2);

(* ============================================================================
   4.  binom_n_n : oeq (binom n n) (Suc Zero)        (induction on n)
       base : binom 0 0 = 1            [binom_n_0]
       step : binom (Suc x)(Suc x) = binom x x + binom x (Suc x)  [Pascal]
              = add (Suc 0) 0          [IH + binom_n_Suc_n]
              = Suc 0                  [add_0_right]
   ============================================================================ *)
val binom_n_n =
  let
    val Qpred = Abs("z", natT, oeq (binom (Bound 0) (Bound 0)) (suc ZeroC));
    val nF = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nF);
    val base = binomN0S2_at ZeroC;                        (* binom 0 0 = Suc 0 *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (binom xF xF) (suc ZeroC));
    val IH = Thm.assume (ctermSub ihprop);
    val pasc = binomSSS2_at (xF, xF);                     (* binom (Suc x)(Suc x) = add (binom x x)(binom x (Suc x)) *)
    val cL = add_cong_lS2 (binom xF xF, suc ZeroC, binom xF (suc xF)) IH;
             (* = add (Suc 0)(binom x (Suc x)) *)
    val bnsn = binomNSn_at xF;                            (* binom x (Suc x) = 0 *)
    val cR = add_cong_rS2 (suc ZeroC, binom xF (suc xF), ZeroC) bnsn;
             (* = add (Suc 0) 0 *)
    val a0r = add0rS2_at (suc ZeroC);                     (* add (Suc 0) 0 = Suc 0 *)
    val stepconcl = oeq_trans OF [oeq_trans OF [oeq_trans OF [pasc, cL], cR], a0r];
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_binom_n_n = jT (oeq (binom nVs nVs) (suc ZeroC));
val r_binom_n_n = checkSub ("binom_n_n", binom_n_n, i_binom_n_n);

(* ============================================================================
   HELPER  pow_b_sub_Suc : jT (le k n) ==>
              oeq (mult (pow b (sub n k)) b) (pow b (sub (Suc n) k))
       sub (Suc n) k = Suc (sub n k)   [sub_Suc_le @ le k n]
       pow b (Suc (sub n k)) = mult b (pow b (sub n k))   [pow_Suc]
       mult (pow b (sub n k)) b = mult b (pow b (sub n k))  [mult_comm]
   ============================================================================ *)
val sub_Suc_le_vS2 = varify sub_Suc_le;
fun subSucLe_at (kt,nt) = beta_norm (Drule.infer_instantiate ctxtSub
        [(("k",0), ctermSub kt),(("n",0), ctermSub nt)] sub_Suc_le_vS2);

val pow_b_sub_Suc =
  let
    val bF = Free("b", natT); val kF = Free("k", natT); val nF = Free("n", natT);
    val leHyp = jT (le kF nF);
    val H = Thm.assume (ctermSub leHyp);
    (* sub (Suc n) k = Suc (sub n k) *)
    val ssl = Thm.implies_elim (subSucLe_at (kF, nF)) H;  (* oeq (sub (Suc n) k)(Suc (sub n k)) *)
    (* pow b (Suc (sub n k)) = mult b (pow b (sub n k))  [pow_Suc] *)
    val psuc = powSucS2_at (bF, sub nF kF);              (* pow b (Suc (sub n k)) = mult b (pow b (sub n k)) *)
    (* mult (pow b (sub n k)) b = mult b (pow b (sub n k))  [mult_comm] *)
    val mc = multcommS2_at (pow bF (sub nF kF), bF);     (* mult (pow b (sub n k)) b = mult b (pow b (sub n k)) *)
    (* chain : mult (pow b (sub n k)) b = mult b (pow b (sub n k)) = pow b (Suc (sub n k)) [psuc sym]
              = pow b (sub (Suc n) k)  [cong arg2 with ssl sym] *)
    val psucS = oeq_sym OF [psuc];                       (* mult b (pow b (sub n k)) = pow b (Suc (sub n k)) *)
    val c1 = oeq_trans OF [mc, psucS];                   (* mult (pow b (sub n k)) b = pow b (Suc (sub n k)) *)
    (* pow b (Suc (sub n k)) = pow b (sub (Suc n) k)  via pow arg2 cong with ssl sym *)
    val powcong =
      let
        val Pabs = Abs("z", natT, oeq (pow bF (suc (sub nF kF))) (pow bF (Bound 0)));
        val inst = beta_norm (Drule.infer_instantiate ctxtSub
              [(("P",0), ctermSub Pabs), (("a",0), ctermSub (suc (sub nF kF))), (("b",0), ctermSub (sub (suc nF) kF))] oeq_subst_vS2);
        val refl_bp = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub (pow bF (suc (sub nF kF))))] oeq_refl_vS2);
      in inst OF [oeq_sym OF [ssl], refl_bp] end;        (* pow b (Suc (sub n k)) = pow b (sub (Suc n) k) *)
    val core = oeq_trans OF [c1, powcong];               (* mult (pow b (sub n k)) b = pow b (sub (Suc n) k) *)
    val disch = Thm.implies_intr (ctermSub leHyp) core;
  in varify disch end;

val bVps = Var (("b",0), natT);
val i_pow_b_sub_Suc =
  Logic.mk_implies (jT (le kVs nVs),
    jT (oeq (mult (pow bVps (sub nVs kVs)) bVps) (pow bVps (sub (suc nVs) kVs))));
val r_pow_b_sub_Suc = checkSub ("pow_b_sub_Suc", pow_b_sub_Suc, i_pow_b_sub_Suc);

(* soundness probe : pow_b_sub_Suc must still carry the le k n premise *)
val s_powbsub_needs_le =
  not ((Thm.prop_of pow_b_sub_Suc) aconv
        (jT (oeq (mult (pow bVps (sub nVs kVs)) bVps) (pow bVps (sub (suc nVs) kVs)))));

(* ============================================================================
   STAGE C2 FOUNDATION FINAL VALIDATION
   ============================================================================ *)
val () =
  if r_sum_mult_l andalso r_sum_add andalso r_sum_peel_first
     andalso r_binom_n_n andalso r_binom_n_Suc_n
     andalso r_pow_b_sub_Suc andalso s_powbsub_needs_le
  then out "SUMALG_OK\n"
  else out "SUMALG_FAIL\n";

(* ============================================================================
   ============================================================================
   ***  STAGE C3 : THE BINOMIAL THEOREM  ***
   ----------------------------------------------------------------------------
   binom_theorem :
     oeq (pow (add a b) n)
         (sumf (Abs k. mult (binom n k)(mult (pow a k)(pow b (sub n k)))) n)
   i.e. (a+b)^n = SUM_{k=0}^n  C(n,k) * a^k * b^(n-k).
   Proof by induction on n with a,b FREE.
   ============================================================================ *)

val () = out "BINOM_BEGIN\n";

(* ---- extra ground instantiators on ctxtSub that the foundation did not name ---- *)
fun rdistS2_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt),(("n",0), ctermSub nt),(("k",0), ctermSub kt)] right_distrib_vS2);
fun multassocS2_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt),(("n",0), ctermSub nt),(("k",0), ctermSub kt)] mult_assoc_vS2);

val mult_1_left_vS2  = varify mult_1_left;     (* oeq (mult (Suc 0) n) n *)
fun mult1lS2_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] mult_1_left_vS2);

val subN0S2_at_local = subN0S2_at;             (* alias, already exists : oeq (sub n 0) n *)

(* pow 2nd-argument congruence on ctxtSub :  oeq u v ==> oeq (pow b u)(pow b v) *)
fun pow_cong_a2S2 (bT, uT, vT) huv =
  let
    val Pabs = Abs("z", natT, oeq (pow bT uT) (pow bT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("a",0), ctermSub uT), (("b",0), ctermSub vT)] oeq_subst_vS2);
    val refl_bu = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub (pow bT uT))] oeq_refl_vS2);
  in inst OF [huv, refl_bu] end;

(* pow_Suc instantiator already present as powSucS2_at (at,nt) : pow a (Suc n) = mult a (pow a n) *)
(* pow_Zero instantiator already present as powZeroS2_at t : pow a 0 = Suc 0 *)
(* binom helpers : binomN0S2_at, binom0SS2_at, binomSSS2_at ; sub helpers : subN0S2_at, subSSS2_at *)

(* sum_cong on ctxtSub : (!!k. le k n ==> f k = g k) ==> sumf f n = sumf g n *)
val sum_cong_vS2 = varify sum_cong;
fun sum_cong_at (fAbs, gAbs, nt) congProof =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("f",0), ctermSub fAbs), (("g",0), ctermSub gAbs), (("n",0), ctermSub nt)] sum_cong_vS2)
  in Thm.implies_elim inst congProof end;

(* pow_b_sub_Suc instantiator : le k n ==> mult (pow b (sub n k)) b = pow b (sub (Suc n) k) *)
val pow_b_sub_Suc_vS2 = varify pow_b_sub_Suc;
fun powBsubSuc_at (bt,kt,nt) hle =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("b",0), ctermSub bt),(("k",0), ctermSub kt),(("n",0), ctermSub nt)] pow_b_sub_Suc_vS2)
  in Thm.implies_elim inst hle end;

val () = out "BINOM_HELPERS_READY\n";

(* ============================================================================
   THE MAIN INDUCTION
   ============================================================================ *)
val binom_theorem =
  let
    val aF = Free("a", natT);
    val bF = Free("b", natT);

    (* induction-predicate summand  : %k. C(z,k) * a^k * b^(z-k)  (z = ind var) *)
    fun summandAbs zt = Abs("k", natT,
          mult (binom zt (Bound 0)) (mult (pow aF (Bound 0)) (pow bF (sub zt (Bound 0)))));
    fun summand_at zt t =
          mult (binom zt t) (mult (pow aF t) (pow bF (sub zt t)));     (* beta of (summandAbs zt) $ t *)
    fun pbody zt = oeq (pow (add aF bF) zt) (sumf (summandAbs zt) zt);

    val zV = Free("z", natT);
    val Qpred = Term.lambda zV (pbody zV);
    val nIndV = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nIndV);

    (* ====================================================================
       BASE  n = 0 :  pow (a+b) 0 = 1 ;  sumf (summandAbs 0) 0 = (summandAbs 0) $ 0
                      = C(0,0)*a^0*b^(0-0) = 1*(1*b^0) = 1.
       ==================================================================== *)
    val base =
      let
        val lhs0 = powZeroS2_at (add aF bF);                  (* pow (a+b) 0 = Suc 0 *)
        (* RHS : sumf (summandAbs 0) 0 = summand_at 0 0 [sumf_0, beta] *)
        val sf0  = sumf0_at (summandAbs ZeroC);              (* sumf F0 0 = summand_at 0 0 *)
        (* summand_at 0 0 = C(0,0)*( a^0 *( b^(0-0) ) ) ; reduce to Suc 0 *)
        val b00  = binomN0S2_at ZeroC;                        (* binom 0 0 = Suc 0 *)
        val pa0  = powZeroS2_at aF;                           (* pow a 0 = Suc 0 *)
        val sub00= subN0S2_at ZeroC;                         (* sub 0 0 = 0 *)
        val pb0c = pow_cong_a2S2 (bF, sub ZeroC ZeroC, ZeroC) sub00;  (* pow b (0-0) = pow b 0 *)
        val pb0  = powZeroS2_at bF;                           (* pow b 0 = Suc 0 *)
        val pbsub= oeq_trans OF [pb0c, pb0];                  (* pow b (0-0) = Suc 0 *)
        (* inner = mult (pow a 0)(pow b (0-0)) ; = mult (Suc 0)(Suc 0) ; reduce *)
        val innerL = mult_cong_lS2 (pow aF ZeroC, suc ZeroC, pow bF (sub ZeroC ZeroC)) pa0;
                     (* mult (pow a 0)(pow b (0-0)) = mult (Suc 0)(pow b (0-0)) *)
        val innerR = mult_cong_rS2 (suc ZeroC, pow bF (sub ZeroC ZeroC), suc ZeroC) pbsub;
                     (* mult (Suc 0)(pow b (0-0)) = mult (Suc 0)(Suc 0) *)
        val inner1 = oeq_trans OF [innerL, innerR];           (* inner = mult (Suc 0)(Suc 0) *)
        val m11    = mult1lS2_at (suc ZeroC);                 (* mult (Suc 0)(Suc 0) = Suc 0 *)
        val inner  = oeq_trans OF [inner1, m11];              (* inner = Suc 0 *)
        (* outer = mult (binom 0 0) inner = mult (Suc 0) inner [cong] = inner [m1l] = Suc 0 *)
        val outerL = mult_cong_lS2 (binom ZeroC ZeroC, suc ZeroC, mult (pow aF ZeroC) (pow bF (sub ZeroC ZeroC))) b00;
                     (* outer = mult (Suc 0)(inner-orig) *)
        val outerR = mult_cong_rS2 (suc ZeroC, mult (pow aF ZeroC) (pow bF (sub ZeroC ZeroC)), suc ZeroC) inner;
                     (* mult (Suc 0)(inner-orig) = mult (Suc 0)(Suc 0) *)
        val outer1 = oeq_trans OF [outerL, outerR];           (* outer = mult (Suc 0)(Suc 0) *)
        val m11b   = mult1lS2_at (suc ZeroC);                 (* mult (Suc 0)(Suc 0) = Suc 0 *)
        val outer  = oeq_trans OF [outer1, m11b];             (* summand_at 0 0 = Suc 0 *)
        val rhs0   = oeq_trans OF [sf0, outer];               (* sumf F0 0 = Suc 0 *)
        val rhs0s  = oeq_sym OF [rhs0];                       (* Suc 0 = sumf F0 0 *)
      in oeq_trans OF [lhs0, rhs0s] end;                      (* pow (a+b) 0 = sumf F0 0 *)

    (* ====================================================================
       STEP  n = x -> Suc x.   IH : pow (a+b) x = sumf (summandAbs x) x.
       ==================================================================== *)
    val xF = Free("x", natT);
    val nn = xF;                              (* the IH parameter *)
    val ihprop = jT (pbody xF);              (* oeq (pow (a+b) x) (sumf (summandAbs x) x) *)
    val IH = Thm.assume (ctermSub ihprop);

    val stepconcl =
      let
        val Fn    = summandAbs nn;            (* %k. C(x,k)*a^k*b^(x-k) *)
        val FSucN = summandAbs (suc nn);      (* %k. C(Sx,k)*a^k*b^((Sx)-k) *)

        (* canonical reshaped summand lambdas *)
        val G1 = Abs("k", natT,
              mult (binom nn (Bound 0)) (mult (pow aF (suc (Bound 0))) (pow bF (sub nn (Bound 0)))));
        fun G1_at t = mult (binom nn t) (mult (pow aF (suc t)) (pow bF (sub nn t)));
        val H  = Abs("k", natT,
              mult (binom nn (Bound 0)) (mult (pow aF (Bound 0)) (pow bF (sub (suc nn) (Bound 0)))));
        fun H_at t  = mult (binom nn t) (mult (pow aF t) (pow bF (sub (suc nn) t)));
        val G2 = Abs("k", natT,
              mult (binom nn (suc (Bound 0))) (mult (pow aF (suc (Bound 0))) (pow bF (sub nn (Bound 0)))));
        fun G2_at t = mult (binom nn (suc t)) (mult (pow aF (suc t)) (pow bF (sub nn t)));

        (* ------------------------------------------------------------------
           LHS : pow (a+b)(Suc x) = add (sumf G1 x) (sumf H x)
           ------------------------------------------------------------------ *)
        val pS   = powSucS2_at (add aF bF, nn);             (* pow (a+b)(Sx) = mult (a+b)(pow (a+b) x) *)
        val pIH  = mult_cong_rS2 (add aF bF, pow (add aF bF) nn, sumf Fn nn) IH;
                   (* mult (a+b)(pow (a+b) x) = mult (a+b)(sumf Fn x) *)
        val rd   = rdistS2_at (aF, bF, sumf Fn nn);
                   (* mult (add a b)(sumf Fn x) = add (mult a (sumf Fn x))(mult b (sumf Fn x)) *)
        val lhsAB = oeq_trans OF [oeq_trans OF [pS, pIH], rd];
                   (* pow (a+b)(Sx) = add Sa Sb ; Sa = mult a (sumf Fn x), Sb = mult b (sumf Fn x) *)

        (* Sa = mult a (sumf Fn x) = sumf (%k. mult a (Fn k)) x  [sum_mult_l c:=a] *)
        val aFnAbs = Abs("k", natT, mult aF (summand_at nn (Bound 0)));
        fun aFn_at t = mult aF (summand_at nn t);
        val sml_a = Drule.infer_instantiate ctxtSub
              [(("c",0), ctermSub aF), (("f",0), ctermSub Fn), (("n",0), ctermSub nn)] sum_mult_l;
        val sml_a' = beta_norm sml_a;       (* mult a (sumf Fn x) = sumf aFnAbs x *)
        (* sum_cong : sumf aFnAbs x = sumf G1 x   (pointwise mult a (Fn k) = G1 k, no le) *)
        val congSa =
          let
            val kF = Free("k", natT);
            (* prove : le k x ==> oeq (aFn_at k)(G1_at k) *)
            val hle = Thm.assume (ctermSub (jT (le kF nn)));
            (* mult a (C*(a^k*b^(x-k))) ; pull C out front : a*(C*X) = C*(a*X) *)
            val C   = binom nn kF;
            val X   = mult (pow aF kF) (pow bF (sub nn kF));
            (* a*(C*X) = (a*C)*X [assoc sym]  then (a*C) = (C*a) [comm] then (C*a)*X = C*(a*X) [assoc] *)
            val as1 = multassocS2_at (aF, C, X);            (* (a*C)*X = a*(C*X) *)
            val as1s= oeq_sym OF [as1];                     (* a*(C*X) = (a*C)*X *)
            val cm  = multcommS2_at (aF, C);                (* a*C = C*a *)
            val cmc = mult_cong_lS2 (mult aF C, mult C aF, X) cm;  (* (a*C)*X = (C*a)*X *)
            val as2 = multassocS2_at (C, aF, X);            (* (C*a)*X = C*(a*X) *)
            val pull= oeq_trans OF [oeq_trans OF [as1s, cmc], as2];  (* a*(C*X) = C*(a*X) *)
            (* a*X = a*(a^k * b^(x-k)) = (a*a^k)*b^(x-k) = a^(Sk)*b^(x-k) *)
            val aX_as = multassocS2_at (aF, pow aF kF, pow bF (sub nn kF));   (* (a*a^k)*b = a*(a^k*b) *)
            val aX_ass= oeq_sym OF [aX_as];                 (* a*(a^k*b) = (a*a^k)*b *)
            val pSk = powSucS2_at (aF, kF);                 (* a^(Sk) = mult a (a^k) = a*a^k *)
            val pSks= oeq_sym OF [pSk];                     (* a*a^k = a^(Sk) *)
            val aX_top = mult_cong_lS2 (mult aF (pow aF kF), pow aF (suc kF), pow bF (sub nn kF)) pSks;
                         (* (a*a^k)*b = a^(Sk)*b *)
            val aX = oeq_trans OF [aX_ass, aX_top];         (* a*X = a^(Sk)*b^(x-k) *)
            (* C*(a*X) = C*(a^(Sk)*b^(x-k)) = G1_at k *)
            val cong_inner = mult_cong_rS2 (C, mult aF X, mult (pow aF (suc kF)) (pow bF (sub nn kF))) aX;
            val body = oeq_trans OF [pull, cong_inner];     (* aFn_at k = G1_at k *)
            val dis = Thm.implies_intr (ctermSub (jT (le kF nn))) body;
            val allm = Thm.forall_intr (ctermSub kF) dis;   (* !!k. le k x ==> aFn_at k = G1_at k *)
          in sum_cong_at (aFnAbs, G1, nn) allm end;          (* sumf aFnAbs x = sumf G1 x *)
        val Sa_eq = oeq_trans OF [sml_a', congSa];           (* mult a (sumf Fn x) = sumf G1 x *)

        (* Sb = mult b (sumf Fn x) = sumf (%k. mult b (Fn k)) x  [sum_mult_l c:=b] *)
        val bFnAbs = Abs("k", natT, mult bF (summand_at nn (Bound 0)));
        fun bFn_at t = mult bF (summand_at nn t);
        val sml_b = Drule.infer_instantiate ctxtSub
              [(("c",0), ctermSub bF), (("f",0), ctermSub Fn), (("n",0), ctermSub nn)] sum_mult_l;
        val sml_b' = beta_norm sml_b;       (* mult b (sumf Fn x) = sumf bFnAbs x *)
        (* sum_cong : sumf bFnAbs x = sumf H x  (pointwise for k<=x, needs pow_b_sub_Suc) *)
        val congSb =
          let
            val kF = Free("k", natT);
            val hle = Thm.assume (ctermSub (jT (le kF nn)));   (* le k x *)
            val C   = binom nn kF;
            val pak = pow aF kF;
            val pbx = pow bF (sub nn kF);                      (* b^(x-k) *)
            (* mult b (C*(a^k*b^(x-k))) ; reassociate everything :
               b*(C*(a^k*b^(x-k))) = C*(a^k*(b^(x-k)*b)) = C*(a^k*b^((Sx)-k)) = H_at k *)
            val X    = mult pak pbx;
            (* b*(C*X) = (b*C)*X [assoc sym] = (C*b)*X [comm] = C*(b*X) [assoc] *)
            val as1  = multassocS2_at (bF, C, X);
            val as1s = oeq_sym OF [as1];                       (* b*(C*X) = (b*C)*X *)
            val cm   = multcommS2_at (bF, C);                  (* b*C = C*b *)
            val cmc  = mult_cong_lS2 (mult bF C, mult C bF, X) cm;
            val as2  = multassocS2_at (C, bF, X);              (* (C*b)*X = C*(b*X) *)
            val pull = oeq_trans OF [oeq_trans OF [as1s, cmc], as2];   (* b*(C*X) = C*(b*X) *)
            (* b*X = b*(a^k * b^(x-k)) = (b*a^k)*b^(x-k) = (a^k*b)*b^(x-k) = a^k*(b^(x-k)*b)
               ... cleaner: b*(a^k*b^(x-k)) = a^k * (b * b^(x-k)) ?  do via commute path *)
            (* b*X : X = a^k * b^(x-k).  We want  a^k * (b^(x-k)*b)  then use pow_b_sub_Suc. *)
            (* b*(a^k * b^(x-k)) = (b * a^k) * b^(x-k)   [assoc sym]
                                 = (a^k * b) * b^(x-k)   [comm on b,a^k]
                                 = a^k * (b * b^(x-k))   [assoc]
                                 = a^k * (b^(x-k) * b)   [comm on b, b^(x-k)]
                                 = a^k * b^((Sx)-k)      [pow_b_sub_Suc @ le k x] *)
            val bx_as1  = multassocS2_at (bF, pak, pbx);       (* (b*a^k)*b^ = b*(a^k*b^) *)
            val bx_as1s = oeq_sym OF [bx_as1];                 (* b*(a^k*b^) = (b*a^k)*b^ *)
            val bx_cm   = multcommS2_at (bF, pak);             (* b*a^k = a^k*b *)
            val bx_cmc  = mult_cong_lS2 (mult bF pak, mult pak bF, pbx) bx_cm;  (* (b*a^k)*b^ = (a^k*b)*b^ *)
            val bx_as2  = multassocS2_at (pak, bF, pbx);       (* (a^k*b)*b^ = a^k*(b*b^) *)
            val bx_cm2  = multcommS2_at (bF, pbx);             (* b*b^(x-k) = b^(x-k)*b *)
            val bx_cm2c = mult_cong_rS2 (pak, mult bF pbx, mult pbx bF) bx_cm2;  (* a^k*(b*b^) = a^k*(b^*b) *)
            val pbsuc   = powBsubSuc_at (bF, kF, nn) hle;      (* b^(x-k)*b = b^((Sx)-k) *)
            val bx_top  = mult_cong_rS2 (pak, mult pbx bF, pow bF (sub (suc nn) kF)) pbsuc;
                          (* a^k*(b^(x-k)*b) = a^k*b^((Sx)-k) *)
            val bX = oeq_trans OF [oeq_trans OF [oeq_trans OF [oeq_trans OF [bx_as1s, bx_cmc], bx_as2], bx_cm2c], bx_top];
                     (* b*X = a^k * b^((Sx)-k) *)
            val cong_inner = mult_cong_rS2 (C, mult bF X, mult pak (pow bF (sub (suc nn) kF))) bX;
                             (* C*(b*X) = C*(a^k*b^((Sx)-k)) = H_at k *)
            val body = oeq_trans OF [pull, cong_inner];        (* bFn_at k = H_at k *)
            val dis = Thm.implies_intr (ctermSub (jT (le kF nn))) body;
            val allm = Thm.forall_intr (ctermSub kF) dis;
          in sum_cong_at (bFnAbs, H, nn) allm end;             (* sumf bFnAbs x = sumf H x *)
        val Sb_eq = oeq_trans OF [sml_b', congSb];             (* mult b (sumf Fn x) = sumf H x *)

        (* LHS = add Sa Sb -> add (sumf G1 x)(sumf H x) *)
        val lcL = add_cong_lS2 (mult aF (sumf Fn nn), sumf G1 nn, mult bF (sumf Fn nn)) Sa_eq;
                  (* add Sa Sb = add (sumf G1 x) Sb *)
        val lcR = add_cong_rS2 (sumf G1 nn, mult bF (sumf Fn nn), sumf H nn) Sb_eq;
                  (* add (sumf G1 x) Sb = add (sumf G1 x)(sumf H x) *)
        val LHS = oeq_trans OF [oeq_trans OF [lhsAB, lcL], lcR];
                  (* pow (a+b)(Sx) = add (sumf G1 x)(sumf H x) *)

        (* ------------------------------------------------------------------
           CRUX : sumf H x = add (pow b (Sx)) (sumf G2 x)
           ------------------------------------------------------------------ *)
        (* H $ 0 = pow b (Sx) :
             H_at 0 = C(x,0)*(a^0 * b^((Sx)-0)) = 1*(1 * b^(Sx)) = b^(Sx). *)
        val H0_reduce =
          let
            val bx0  = binomN0S2_at nn;                      (* binom x 0 = Suc 0 *)
            val pa0  = powZeroS2_at aF;                      (* pow a 0 = Suc 0 *)
            val sSx0 = subN0S2_at (suc nn);                  (* sub (Sx) 0 = Sx *)
            val pbc  = pow_cong_a2S2 (bF, sub (suc nn) ZeroC, suc nn) sSx0;  (* pow b ((Sx)-0) = pow b (Sx) *)
            (* inner = mult (pow a 0)(pow b ((Sx)-0)) = mult (Suc 0)(pow b (Sx)) = pow b (Sx) *)
            val innerL = mult_cong_lS2 (pow aF ZeroC, suc ZeroC, pow bF (sub (suc nn) ZeroC)) pa0;
            val innerR = mult_cong_rS2 (suc ZeroC, pow bF (sub (suc nn) ZeroC), pow bF (suc nn)) pbc;
            val inner1 = oeq_trans OF [innerL, innerR];      (* inner = mult (Suc 0)(pow b (Sx)) *)
            val m1l    = mult1lS2_at (pow bF (suc nn));       (* mult (Suc 0)(pow b (Sx)) = pow b (Sx) *)
            val inner  = oeq_trans OF [inner1, m1l];          (* inner = pow b (Sx) *)
            (* outer = mult (binom x 0) inner = mult (Suc 0) inner = inner = pow b (Sx) *)
            val outerL = mult_cong_lS2 (binom nn ZeroC, suc ZeroC, mult (pow aF ZeroC) (pow bF (sub (suc nn) ZeroC))) bx0;
            val outerR = mult_cong_rS2 (suc ZeroC, mult (pow aF ZeroC) (pow bF (sub (suc nn) ZeroC)), pow bF (suc nn)) inner;
            val outer1 = oeq_trans OF [outerL, outerR];       (* outer = mult (Suc 0)(pow b (Sx)) *)
            val m1lb   = mult1lS2_at (pow bF (suc nn));
            val outer  = oeq_trans OF [outer1, m1lb];         (* H_at 0 = pow b (Sx) *)
          in outer end;                                       (* oeq (H_at 0)(pow b (Sx)) *)

        (* sumf G2 x = sumf (%j. H $ (Suc j)) x   [sum_cong : G2 j = H_at (Suc j)] *)
        val HshiftAbs = Abs("j", natT, H_at (suc (Bound 0)));   (* %j. H (Suc j) *)
        fun Hshift_at t = H_at (suc t);
        val congG2 =
          let
            val jF = Free("j", natT);
            val hle = Thm.assume (ctermSub (jT (le jF nn)));  (* le j x  (unused but required shape) *)
            (* G2_at j = C(x, Sj) * a^(Sj) * b^(x-j)
               H_at (Sj) = C(x, Sj) * a^(Sj) * b^((Sx)-(Sj)) ; (Sx)-(Sj) = x-j [sub_Suc_Suc] *)
            val ssub = subSSS2_at (nn, jF);                   (* sub (Sx)(Sj) = sub x j *)
            val ssubS= oeq_sym OF [ssub];                     (* sub x j = sub (Sx)(Sj) *)
            (* G2_at j  ->  H_at (Sj) : rewrite b^(x-j) to b^((Sx)-(Sj)) under the inner mult-right *)
            val pbc  = pow_cong_a2S2 (bF, sub nn jF, sub (suc nn) (suc jF)) ssubS;
                       (* pow b (x-j) = pow b ((Sx)-(Sj)) *)
            val innerC = mult_cong_rS2 (pow aF (suc jF), pow bF (sub nn jF), pow bF (sub (suc nn) (suc jF))) pbc;
                         (* a^(Sj)*b^(x-j) = a^(Sj)*b^((Sx)-(Sj)) *)
            val body = mult_cong_rS2 (binom nn (suc jF), mult (pow aF (suc jF)) (pow bF (sub nn jF)),
                                       mult (pow aF (suc jF)) (pow bF (sub (suc nn) (suc jF)))) innerC;
                       (* G2_at j = H_at (Sj) *)
            val dis = Thm.implies_intr (ctermSub (jT (le jF nn))) body;
            val allm = Thm.forall_intr (ctermSub jF) dis;
          in sum_cong_at (G2, HshiftAbs, nn) allm end;         (* sumf G2 x = sumf HshiftAbs x *)

        (* sum_peel_first @ H, x :  sumf H (Suc x) = add (H $ 0)(sumf (%j. H (Suc j)) x) *)
        val peelH = Drule.infer_instantiate ctxtSub
              [(("f",0), ctermSub H), (("n",0), ctermSub nn)] sum_peel_first;
        val peelH' = beta_norm peelH;     (* sumf H (Sx) = add (H_at 0)(sumf HshiftAbs x) *)

        (* assemble : add (pow b (Sx))(sumf G2 x)
                      = add (H_at 0)(sumf HshiftAbs x)     [H0_reduce sym ; congG2]
                      = sumf H (Sx)                        [peelH' sym]
                      = add (sumf H x)(H_at (Sx))          [sumf_Suc]
                      = add (sumf H x) 0                   [H_at(Sx)=0]
                      = sumf H x                           [add_0_right] *)
        val cP1 = add_cong_lS2 (pow bF (suc nn), H_at ZeroC, sumf G2 nn) (oeq_sym OF [H0_reduce]);
                  (* add (pow b (Sx))(sumf G2 x) = add (H_at 0)(sumf G2 x) *)
        val cP2 = add_cong_rS2 (H_at ZeroC, sumf G2 nn, sumf HshiftAbs nn) congG2;
                  (* add (H_at 0)(sumf G2 x) = add (H_at 0)(sumf HshiftAbs x) *)
        val foldH = oeq_sym OF [peelH'];   (* add (H_at 0)(sumf HshiftAbs x) = sumf H (Sx) *)
        val sumfHS = sumfSuc_at (H, nn);   (* sumf H (Sx) = add (sumf H x)(H_at (Sx)) *)
        (* H_at (Sx) = 0 : C(x, Sx)=0 -> mult 0 (...) = 0 *)
        val HSx0 =
          let
            val bnsn = binomNSn_at nn;                        (* binom x (Sx) = 0 *)
            val cL = mult_cong_lS2 (binom nn (suc nn), ZeroC, mult (pow aF (suc nn)) (pow bF (sub (suc nn) (suc nn)))) bnsn;
                     (* H_at (Sx) = mult 0 (inner) *)
            val m0 = beta_norm (Drule.infer_instantiate ctxtSub
                       [(("n",0), ctermSub (mult (pow aF (suc nn)) (pow bF (sub (suc nn) (suc nn)))))] (varify mult_0));
                     (* mult 0 (inner) = 0 *)
          in oeq_trans OF [cL, m0] end;                        (* H_at (Sx) = 0 *)
        val cAdd0 = add_cong_rS2 (sumf H nn, H_at (suc nn), ZeroC) HSx0;
                    (* add (sumf H x)(H_at (Sx)) = add (sumf H x) 0 *)
        val a0r   = add0rS2_at (sumf H nn);                   (* add (sumf H x) 0 = sumf H x *)
        val crux_rev = oeq_trans OF [oeq_trans OF [oeq_trans OF [oeq_trans OF [oeq_trans OF [cP1, cP2], foldH], sumfHS], cAdd0], a0r];
                       (* add (pow b (Sx))(sumf G2 x) = sumf H x *)
        val crux = oeq_sym OF [crux_rev];   (* sumf H x = add (pow b (Sx))(sumf G2 x) *)

        (* ------------------------------------------------------------------
           RHS : sumf FSucN (Suc x) = add (pow b (Sx)) (add (sumf G1 x)(sumf G2 x))
           ------------------------------------------------------------------ *)
        (* peel first @ FSucN, x : sumf FSucN (Sx) = add (FSucN$0)(sumf (%j. FSucN (Sj)) x) *)
        val peelF = Drule.infer_instantiate ctxtSub
              [(("f",0), ctermSub FSucN), (("n",0), ctermSub nn)] sum_peel_first;
        val peelF' = beta_norm peelF;   (* sumf FSucN (Sx) = add (FSucN_at 0)(sumf FSshiftAbs x) *)
        val FSshiftAbs = Abs("j", natT, summand_at (suc nn) (suc (Bound 0)));   (* %j. FSucN (Suc j) *)
        fun FSshift_at t = summand_at (suc nn) (suc t);

        (* FSucN_at 0 = pow b (Sx)  (SAME shape as H_at 0 but binom (Sx) 0; recompute) *)
        val F0_reduce =
          let
            val bsx0 = binomN0S2_at (suc nn);                (* binom (Sx) 0 = Suc 0 *)
            val pa0  = powZeroS2_at aF;                      (* pow a 0 = Suc 0 *)
            val sSx0 = subN0S2_at (suc nn);                  (* sub (Sx) 0 = Sx *)
            val pbc  = pow_cong_a2S2 (bF, sub (suc nn) ZeroC, suc nn) sSx0;
            val innerL = mult_cong_lS2 (pow aF ZeroC, suc ZeroC, pow bF (sub (suc nn) ZeroC)) pa0;
            val innerR = mult_cong_rS2 (suc ZeroC, pow bF (sub (suc nn) ZeroC), pow bF (suc nn)) pbc;
            val inner1 = oeq_trans OF [innerL, innerR];
            val m1l    = mult1lS2_at (pow bF (suc nn));
            val inner  = oeq_trans OF [inner1, m1l];
            val outerL = mult_cong_lS2 (binom (suc nn) ZeroC, suc ZeroC, mult (pow aF ZeroC) (pow bF (sub (suc nn) ZeroC))) bsx0;
            val outerR = mult_cong_rS2 (suc ZeroC, mult (pow aF ZeroC) (pow bF (sub (suc nn) ZeroC)), pow bF (suc nn)) inner;
            val outer1 = oeq_trans OF [outerL, outerR];
            val m1lb   = mult1lS2_at (pow bF (suc nn));
          in oeq_trans OF [outer1, m1lb] end;               (* FSucN_at 0 = pow b (Sx) *)

        (* sumf FSshiftAbs x = sumf (%j. add (G1 j)(G2 j)) x  [sum_cong : FSucN (Sj) = add (G1 j)(G2 j)] *)
        val GaddAbs = Abs("j", natT, add (G1_at (Bound 0)) (G2_at (Bound 0)));   (* %j. add (G1 j)(G2 j) *)
        val congFS =
          let
            val jF = Free("j", natT);
            val hle = Thm.assume (ctermSub (jT (le jF nn)));
            (* FSucN_at (Sj) = C(Sx, Sj) * (a^(Sj) * b^((Sx)-(Sj)))
               C(Sx,Sj) = C(x,j) + C(x,Sj)   [Pascal]
               (Sx)-(Sj) = x-j               [sub_Suc_Suc]
               -> (C(x,j)+C(x,Sj)) * (a^(Sj)*b^(x-j))
               -> add (C(x,j)*(...))(C(x,Sj)*(...)) [right_distrib]
               = add (G1 j)(G2 j)  ... but G1 j uses binom x j, G2 j uses binom x (Sj). *)
            val MA  = mult (pow aF (suc jF)) (pow bF (sub nn jF));   (* a^(Sj)*b^(x-j) *)
            (* first rewrite the b-exponent in FSucN_at (Sj) : (Sx)-(Sj) -> x-j *)
            val ssub = subSSS2_at (nn, jF);                  (* sub (Sx)(Sj) = sub x j *)
            val pbc  = pow_cong_a2S2 (bF, sub (suc nn) (suc jF), sub nn jF) ssub;
                       (* pow b ((Sx)-(Sj)) = pow b (x-j) *)
            val innerSub = mult_cong_rS2 (pow aF (suc jF), pow bF (sub (suc nn) (suc jF)), pow bF (sub nn jF)) pbc;
                       (* a^(Sj)*b^((Sx)-(Sj)) = a^(Sj)*b^(x-j) = MA *)
            (* now FSucN_at (Sj) = C(Sx,Sj) * (a^(Sj)*b^((Sx)-(Sj)))
                 -> C(Sx,Sj) * MA   [cong on right with innerSub] *)
            val step1 = mult_cong_rS2 (binom (suc nn) (suc jF),
                          mult (pow aF (suc jF)) (pow bF (sub (suc nn) (suc jF))), MA) innerSub;
                        (* FSucN_at (Sj) = C(Sx,Sj) * MA *)
            (* Pascal on the binom : C(Sx,Sj) = add (C(x,j))(C(x,Sj)) *)
            val pasc = binomSSS2_at (nn, jF);                (* binom (Sx)(Sj) = add (binom x j)(binom x (Sj)) *)
            val step2 = mult_cong_lS2 (binom (suc nn) (suc jF), add (binom nn jF) (binom nn (suc jF)), MA) pasc;
                        (* C(Sx,Sj)*MA = (C(x,j)+C(x,Sj))*MA *)
            (* right_distrib : (C1+C2)*MA = add (C1*MA)(C2*MA) *)
            val rdst = rdistS2_at (binom nn jF, binom nn (suc jF), MA);
                       (* add (binom x j)(binom x (Sj)) ... = add (C1*MA)(C2*MA) *)
            (* C1*MA = G1_at j ?  G1_at j = C(x,j)*(a^(Sj)*b^(x-j)) = C1 * MA  YES (aconv).
               C2*MA = G2_at j ?  G2_at j = C(x,Sj)*(a^(Sj)*b^(x-j)) = C2 * MA  YES. *)
            val body = oeq_trans OF [oeq_trans OF [oeq_trans OF [step1, step2], rdst],
                          oeqreflS2_at (add (mult (binom nn jF) MA) (mult (binom nn (suc jF)) MA))];
                       (* FSucN_at (Sj) = add (G1_at j)(G2_at j) *)
            val dis = Thm.implies_intr (ctermSub (jT (le jF nn))) body;
            val allm = Thm.forall_intr (ctermSub jF) dis;
          in sum_cong_at (FSshiftAbs, GaddAbs, nn) allm end;  (* sumf FSshiftAbs x = sumf GaddAbs x *)

        (* sumf GaddAbs x = add (sumf G1 x)(sumf G2 x)  [sum_add backwards] *)
        val sadd = Drule.infer_instantiate ctxtSub
              [(("f",0), ctermSub G1), (("g",0), ctermSub G2), (("n",0), ctermSub nn)] sum_add;
        val sadd' = beta_norm sadd;   (* add (sumf G1 x)(sumf G2 x) = sumf GaddAbs x *)
        val saddS = oeq_sym OF [sadd'];   (* sumf GaddAbs x = add (sumf G1 x)(sumf G2 x) *)

        (* RHS chain : sumf FSucN (Sx)
             = add (FSucN_at 0)(sumf FSshiftAbs x)   [peelF']
             = add (pow b (Sx))(sumf FSshiftAbs x)   [F0_reduce]
             = add (pow b (Sx))(sumf GaddAbs x)      [congFS]
             = add (pow b (Sx))(add (sumf G1 x)(sumf G2 x))   [saddS] *)
        val rc1 = add_cong_lS2 (summand_at (suc nn) ZeroC, pow bF (suc nn), sumf FSshiftAbs nn) F0_reduce;
                  (* add (FSucN_at 0)(sumf FSshiftAbs x) = add (pow b (Sx))(sumf FSshiftAbs x) *)
        val rc2 = add_cong_rS2 (pow bF (suc nn), sumf FSshiftAbs nn, sumf GaddAbs nn) congFS;
                  (* = add (pow b (Sx))(sumf GaddAbs x) *)
        val rc3 = add_cong_rS2 (pow bF (suc nn), sumf GaddAbs nn, add (sumf G1 nn) (sumf G2 nn)) saddS;
                  (* = add (pow b (Sx))(add (sumf G1 x)(sumf G2 x)) *)
        val RHS = oeq_trans OF [oeq_trans OF [oeq_trans OF [peelF', rc1], rc2], rc3];
                  (* sumf FSucN (Sx) = add (pow b (Sx))(add (sumf G1 x)(sumf G2 x)) *)

        (* ------------------------------------------------------------------
           FINAL : LHS = add (sumf G1 x)(sumf H x)
                       = add (sumf G1 x)(add (pow b (Sx))(sumf G2 x))   [crux on right]
                       = add (pow b (Sx))(add (sumf G1 x)(sumf G2 x))   [reshuffle]
                       = sumf FSucN (Sx)                                 [RHS sym]
           ------------------------------------------------------------------ *)
        val A = sumf G1 nn;
        val B = pow bF (suc nn);
        val Cc = sumf G2 nn;
        val applyCrux = add_cong_rS2 (A, sumf H nn, add B Cc) crux;
                        (* add (sumf G1 x)(sumf H x) = add A (add B C) *)
        (* reshuffle add A (add B C) = add B (add A C) *)
        val rs1 = addassocS2_at (A, B, Cc);            (* add (add A B) C = add A (add B C) *)
        val rs1s = oeq_sym OF [rs1];                   (* add A (add B C) = add (add A B) C *)
        val rs2 = addcommS2_at (A, B);                 (* add A B = add B A *)
        val rs2c = add_cong_lS2 (add A B, add B A, Cc) rs2;  (* add (add A B) C = add (add B A) C *)
        val rs3 = addassocS2_at (B, A, Cc);            (* add (add B A) C = add B (add A C) *)
        val reshuffle = oeq_trans OF [oeq_trans OF [rs1s, rs2c], rs3];
                        (* add A (add B C) = add B (add A C) *)
        val RHSs = oeq_sym OF [RHS];   (* add (pow b (Sx))(add (sumf G1 x)(sumf G2 x)) = sumf FSucN (Sx) *)
        val finalEq =
          oeq_trans OF [oeq_trans OF [oeq_trans OF [oeq_trans OF [LHS, applyCrux], reshuffle], RHSs]
                       , oeqreflS2_at (sumf FSucN (suc nn))];
          (* pow (a+b)(Sx) = sumf FSucN (Sx) = sumf (summandAbs (Sx)) (Sx) *)
      in finalEq end;

    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

(* ---- intended statement, schematic on ctxtSub ---- *)
val aVs = Var (("a",0), natT);
val bVs = Var (("b",0), natT);
val i_binom_theorem =
  let
    val summV = Abs("k", natT,
          mult (binom nVs (Bound 0)) (mult (pow aVs (Bound 0)) (pow bVs (sub nVs (Bound 0)))))
  in jT (oeq (pow (add aVs bVs) nVs) (sumf summV nVs)) end;
val r_binom_theorem = checkSub ("binom_theorem", binom_theorem, i_binom_theorem);

val () =
  if r_binom_theorem then out "BINOM_THM_DONE\n"
  else out "BINOM_THM_FAILED\n";

(* ============================================================================
   FLT FOUNDATION HELPERS  (Stage C3/D prep) — divisibility-of-sum + pow helpers
   Final context : ctxtSub / ctermSub.  Check helper : checkSub.
   All four are 0-hyp (0-extra-hyp) + aconv-validated.
   ============================================================================ *)
val () = out "FLT_HELPERS_BEGIN\n";

(* ---- re-varify the divisibility/disjunction/mult-zero axioms onto ctxtSub ---- *)
val mult_0_vS2   = varify mult_0;            (* oeq (mult Zero n) Zero                       *)
val disjI2_vS2   = varify disjI2_ax;         (* jT B ==> jT (Disj A B)                       *)
val dvd_add_vS2  = varify dvd_add;           (* jT(dvd d m) ==> jT(dvd d n) ==> jT(dvd d (add m n)) *)

(* ground instantiators / kernel helpers routed through ctxtSub *)
fun mult0lSub_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] mult_0_vS2);

fun exISub_at Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("P",0), ctermSub Pabs), (("a",0), ctermSub at)] exI_vS2)
  in Thm.implies_elim inst hbody end;

fun exESub_elim (Pabs, goalC) exThm wName bodyFn =
  let
    val wF      = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm  = Thm.assume (ctermSub hypTerm);
    val body    = bodyFn wF hypThm;
    val minor   = Thm.forall_intr (ctermSub wF) (Thm.implies_intr (ctermSub hypTerm) body);
    val exE_inst= beta_norm (Drule.infer_instantiate ctxtSub
                    [(("P",0), ctermSub Pabs), (("Q",0), ctermSub goalC)] exE_vS2);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;

fun disjI2Sub_at (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSub
      [(("A",0), ctermSub At), (("B",0), ctermSub Bt)] disjI2_vS2)) h;

(* dvd as a term constructor is global (mkEx).  dvd_introSub : from
   hyp : oeq b (mult a w)   build   jT (dvd a b)   via exI on the dvd body. *)
fun dvd_introSub (aT, bT, w) hyp =
  let val Pabs = Abs ("k", natT, oeq bT (mult aT (Bound 0)))
  in exISub_at Pabs w hyp end;

(* dvd_addSub (d,m,n) h1 h2 : jT(dvd d (add m n))   [reuse dvd_add; instantiate first,
   then resolve — OF's higher-order unification on the Ex-lambda fails on the bare schematic]. *)
fun dvd_addSub (dT, mT, nT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("d",0), ctermSub dT), (("m",0), ctermSub mT), (("n",0), ctermSub nT)] dvd_add_vS2)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* cong_introRSub : from hyp : oeq a (add b (mult m w))  build jT (cong m a b)
   via exI on the RIGHT (congR) body then disjI2.  (cong/congL/congR are global.) *)
fun cong_introRSub (m, a, b, w) hyp =
  let
    val RAbs  = Abs ("k", natT, oeq a (add b (mult m (Bound 0))));
    val exThm = exISub_at RAbs w hyp;                          (* jT (congR m a b) *)
  in disjI2Sub_at (congL m a b, congR m a b) exThm end;        (* jT (cong m a b)  *)

(* dvd-congruence : substitute equal terms inside dvd p _ via oeq_subst.
   from hab : oeq aT bT   and   hPa : jT (dvd pT aT)   get jT (dvd pT bT). *)
fun dvd_cong_argSub (pT, aT, bT) hab hPa =
  let val zF = Free("zdc", natT);
      val Pabs = Term.lambda zF (dvd pT zF)              (* de Bruijn-safe : %z. dvd p z *)
  in substPredS2 (Pabs, aT, bT) hab hPa end;

(* le helpers routed through ctxtSub : zero_le instance + le_refl already there *)
val zero_le_vS2 = varify zero_le;            (* jT (le Zero n) *)
fun zero_leSub_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] zero_le_vS2);

(* ============================================================================
   sum_all_dvd :
     (!!k. jT (le k n) ==> jT (dvd p (f $ k))) ==> jT (dvd p (sumf f n))
   Induction on n with the OBJECT-conditional predicate
     P m = Imp (Forall (%k. Imp (le k m) (dvd p (f k)))) (dvd p (sumf f m))
   then discharge the meta !!k by building the object Forall from it.
   ============================================================================ *)
val sum_all_dvd =
  let
    val pF = Free("p", natT);
    val fF = Free("f", fnT);
    val nF = Free("n", natT);
    (* object antecedent "all k<=m, p | f k", as a function of the (CLOSED) upper bound.
       Built via Term.lambda over a FREE k so the binder-introducing dvd/le constructors
       never capture a loose Bound (de Bruijn-safe). *)
    val kAbsF = Free("kk", natT);
    fun condAbs mT = Term.lambda kAbsF (mkImp (le kAbsF mT) (dvd pF (fF $ kAbsF)));
    fun condFa  mT = mkForall (condAbs mT);                         (* Forall (%k. Imp (le k m)(dvd p (f k))) *)

    (* the induction predicate over the upper bound z (FREE then abstracted) *)
    val zAbsF = Free("zz", natT);
    val Qpred = Term.lambda zAbsF (mkImp (condFa zAbsF) (dvd pF (sumf fF zAbsF)));
    val ind   = nat_induct_atS2 (Qpred, nF);

    (* ---- BASE  m = 0 :  Imp (condFa 0) (dvd p (sumf f 0)) ---- *)
    val base =
      let
        val Hcond = Thm.assume (ctermSub (jT (condFa ZeroC)));     (* Forall (%k. Imp(le k 0)(dvd p (f k))) *)
        (* get  Imp (le 0 0) (dvd p (f 0))  by allE at k=0 *)
        val imp0  = allE_S2 (condAbs ZeroC) ZeroC Hcond;           (* (condAbs 0) $ 0  -> beta inside helper *)
        val le00  = zero_leSub_at ZeroC;                           (* le 0 0 *)
        val dvdf0 = mp_S2 (le ZeroC ZeroC, dvd pF (fF $ ZeroC)) imp0 le00;  (* dvd p (f 0) *)
        (* dvd p (sumf f 0) : sumf f 0 = f 0  -> sym -> oeq (f 0)(sumf f 0) -> dvd-cong *)
        val sf0   = sumf0_at fF;                                   (* oeq (sumf f 0)(f 0) *)
        val sf0s  = oeq_sym OF [sf0];                              (* oeq (f 0)(sumf f 0) *)
        val dvdS0 = dvd_cong_argSub (pF, fF $ ZeroC, sumf fF ZeroC) sf0s dvdf0;  (* dvd p (sumf f 0) *)
      in impI_S2 (condFa ZeroC, dvd pF (sumf fF ZeroC))
           (Thm.implies_intr (ctermSub (jT (condFa ZeroC))) dvdS0) end;        (* jT (Imp (condFa 0)(dvd p (sumf f 0))) = P 0 *)

    (* ---- STEP  m = Suc x ---- *)
    val xF = Free("x", natT);
    val ihprop = jT (mkImp (condFa xF) (dvd pF (sumf fF xF)));
    val IH = Thm.assume (ctermSub ihprop);                         (* Imp (condFa x)(dvd p (sumf f x)) *)
    val stepconcl =
      let
        val Hcond = Thm.assume (ctermSub (jT (condFa (suc xF))));  (* Forall (%k. Imp(le k (Sx))(dvd p (f k))) *)
        (* (A) build condFa x  from Hcond : for each k, le k x ==> le k (Sx) ==> dvd p (f k) *)
        val condXabs = condAbs xF;
        val condXallProof =
          let
            val kF   = Free("k", natT);
            val hlex = Thm.assume (ctermSub (jT (le kF xF)));       (* le k x *)
            val lexSx= le_suc_selfS2_at xF;                         (* le x (Sx) *)
            val lekSx= le_transS2_at (kF, xF, suc xF) hlex lexSx;   (* le k (Sx) *)
            val impSx= allE_S2 (condAbs (suc xF)) kF Hcond;         (* Imp (le k (Sx))(dvd p (f k)) *)
            val dvdfk= mp_S2 (le kF (suc xF), dvd pF (fF $ kF)) impSx lekSx;  (* dvd p (f k) *)
            (* body : Imp (le k x) (dvd p (f k)) *)
            val body = impI_S2 (le kF xF, dvd pF (fF $ kF))
                          (Thm.implies_intr (ctermSub (jT (le kF xF))) dvdfk);
            (* discharge k : !!k. jT ((condXabs) $ k)   [body has shape (condXabs)$k after beta] *)
          in Thm.forall_intr (ctermSub kF) body end;
        val condXall = allI_S2 condXabs condXallProof;             (* Forall (%k. Imp(le k x)(dvd p (f k))) = condFa x *)
        val dvdSx    = mp_S2 (condFa xF, dvd pF (sumf fF xF)) IH condXall;   (* dvd p (sumf f x) *)
        (* (B) dvd p (f (Sx)) from Hcond at k = Sx with le (Sx)(Sx) *)
        val impSSx   = allE_S2 (condAbs (suc xF)) (suc xF) Hcond;  (* Imp (le (Sx)(Sx))(dvd p (f (Sx))) *)
        val leSSx    = le_reflS2_at (suc xF);                      (* le (Sx)(Sx) *)
        val dvdfSx   = mp_S2 (le (suc xF) (suc xF), dvd pF (fF $ (suc xF))) impSSx leSSx;  (* dvd p (f (Sx)) *)
        (* (C) dvd_add -> dvd p (add (sumf f x)(f (Sx))) *)
        val dvdSum   = dvd_addSub (pF, sumf fF xF, fF $ (suc xF)) dvdSx dvdfSx;  (* dvd p (add (sumf f x)(f (Sx))) *)
        (* (D) sumf f (Sx) = add (sumf f x)(f (Sx))  -> sym -> dvd-cong *)
        val sfS      = sumfSuc_at (fF, xF);                        (* oeq (sumf f (Sx))(add (sumf f x)(f (Sx))) *)
        val dvdSSx   = dvd_cong_argSub (pF, add (sumf fF xF) (fF $ (suc xF)), sumf fF (suc xF))
                          (oeq_sym OF [sfS]) dvdSum;               (* dvd p (sumf f (Sx)) *)
      in impI_S2 (condFa (suc xF), dvd pF (sumf fF (suc xF)))
           (Thm.implies_intr (ctermSub (jT (condFa (suc xF)))) dvdSSx) end;    (* jT (Imp (condFa (Sx))(dvd p (sumf f (Sx)))) = P (Suc x) *)

    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val Pn = Thm.implies_elim r1 step1;                            (* Imp (condFa n)(dvd p (sumf f n)) *)

    (* ---- discharge the META hyp  !!k. jT(le k n) ==> jT(dvd p (f k)) ---- *)
    val kF   = Free("k", natT);
    val mhProp = Logic.all kF (Logic.mk_implies (jT (le kF nF), jT (dvd pF (fF $ kF))));
    val mhThm  = Thm.assume (ctermSub mhProp);
    (* build object  condFa n  from the meta hyp *)
    val condNallProof =
      let
        val hlekn = Thm.assume (ctermSub (jT (le kF nF)));         (* le k n *)
        val mhAt  = Thm.implies_elim (Thm.forall_elim (ctermSub kF) mhThm) hlekn; (* dvd p (f k) *)
        val body  = impI_S2 (le kF nF, dvd pF (fF $ kF))
                       (Thm.implies_intr (ctermSub (jT (le kF nF))) mhAt);
      in Thm.forall_intr (ctermSub kF) body end;
    val condNall = allI_S2 (condAbs nF) condNallProof;             (* condFa n *)
    val dvdSn    = mp_S2 (condFa nF, dvd pF (sumf fF nF)) Pn condNall;  (* dvd p (sumf f n) *)
    val res      = Thm.implies_intr (ctermSub mhProp) dvdSn;
  in varify res end;

(* intended : (!!k. jT(le k ?n) ==> jT(dvd ?p (?f k))) ==> jT(dvd ?p (sumf ?f ?n)) *)
val i_sum_all_dvd =
  let
    val kF = Free("k", natT)
  in Logic.all kF (Logic.mk_implies (jT (le kF nVs), jT (dvd pVs (fVs $ kF)))) end;
val i_sum_all_dvd_full =
  Logic.mk_implies (i_sum_all_dvd, jT (dvd pVs (sumf fVs nVs)));
val r_sum_all_dvd = checkSub ("sum_all_dvd", sum_all_dvd, i_sum_all_dvd_full);

(* ============================================================================
   dvd_imp_cong_zero :  jT (dvd p x) ==> jT (cong p x Zero)
     dvd p x = Ex k. oeq x (mult p k) ;  exE -> w, hw : oeq x (mult p w).
     cong p x Zero RIGHT disjunct (congR p x Zero) = Ex k. oeq x (add Zero (mult p k)).
     add_0 : oeq (add Zero (mult p w)) (mult p w) ; sym ; trans hw -> oeq x (add Zero (mult p w))
     -> cong_introRSub.
   ============================================================================ *)
val dvd_imp_cong_zero =
  let
    val pF = Free("p", natT); val xF = Free("x", natT);
    val hypP = jT (dvd pF xF);
    val hyp  = Thm.assume (ctermSub hypP);
    val Pabs = Abs("k", natT, oeq xF (mult pF (Bound 0)));         (* dvd-body *)
    val goalC = cong pF xF ZeroC;
    fun bodyFn wF hw =                                             (* hw : oeq x (mult p w) *)
      let
        val a0   = add0S2_at (mult pF wF);                         (* oeq (add Zero (mult p w))(mult p w) *)
        val a0s  = oeq_sym OF [a0];                                (* oeq (mult p w)(add Zero (mult p w)) *)
        val chain= oeq_trans OF [hw, a0s];                         (* oeq x (add Zero (mult p w)) *)
      in cong_introRSub (pF, xF, ZeroC, wF) chain end;            (* jT (cong p x Zero) *)
    val concl = exESub_elim (Pabs, goalC) hyp "w0" bodyFn;
    val res   = Thm.implies_intr (ctermSub hypP) concl;
  in varify res end;

val i_dvd_imp_cong_zero =
  Logic.mk_implies (jT (dvd pVs (Var (("x",0), natT))),
                    jT (cong pVs (Var (("x",0), natT)) ZeroC));
val r_dvd_imp_cong_zero = checkSub ("dvd_imp_cong_zero", dvd_imp_cong_zero, i_dvd_imp_cong_zero);

(* ============================================================================
   pow_one_base : oeq (pow (Suc Zero) n) (Suc Zero)        1^n = 1   (induction on n)
     base : pow (Suc 0) 0 = Suc 0                 [pow_Zero]
     step : pow (Suc 0)(Suc x) = mult (Suc 0)(pow (Suc 0) x)   [pow_Suc]
                               = mult (Suc 0)(Suc 0)           [IH, mult_cong_r]
                               = Suc 0                         [mult_1_left]
   ============================================================================ *)
val pow_one_base =
  let
    val one = suc ZeroC;
    val Qpred = Abs("z", natT, oeq (pow one (Bound 0)) one);
    val nF = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nF);
    val base = powZeroS2_at one;                                  (* oeq (pow (Suc 0) 0)(Suc 0) *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (pow one xF) one);
    val IH = Thm.assume (ctermSub ihprop);
    val sS = powSucS2_at (one, xF);                              (* oeq (pow (Suc 0)(Sx))(mult (Suc 0)(pow (Suc 0) x)) *)
    val cr = mult_cong_rS2 (one, pow one xF, one) IH;            (* oeq (mult (Suc 0)(pow (Suc 0) x))(mult (Suc 0)(Suc 0)) *)
    val m1 = mult1lS2_at one;                                    (* oeq (mult (Suc 0)(Suc 0))(Suc 0) *)
    val stepconcl = oeq_trans OF [oeq_trans OF [sS, cr], m1];    (* oeq (pow (Suc 0)(Sx))(Suc 0) *)
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_pow_one_base = jT (oeq (pow (suc ZeroC) nVs) (suc ZeroC));
val r_pow_one_base = checkSub ("pow_one_base", pow_one_base, i_pow_one_base);

(* ============================================================================
   pow_zero_pos : oeq (pow Zero (Suc m)) Zero               0^(m+1) = 0
     pow Zero (Suc m) = mult Zero (pow Zero m)   [pow_Suc]
                      = Zero                      [mult_0]
   ============================================================================ *)
val pow_zero_pos =
  let
    val mF = Free("m", natT);
    val sS = powSucS2_at (ZeroC, mF);                            (* oeq (pow 0 (Suc m))(mult 0 (pow 0 m)) *)
    val m0 = mult0lSub_at (pow ZeroC mF);                       (* oeq (mult 0 (pow 0 m)) 0 *)
  in varify (oeq_trans OF [sS, m0]) end;

val i_pow_zero_pos = jT (oeq (pow ZeroC (suc mVp)) ZeroC);
val r_pow_zero_pos = checkSub ("pow_zero_pos", pow_zero_pos, i_pow_zero_pos);

(* ---- final aggregate ---- *)
val () =
  if r_sum_all_dvd andalso r_dvd_imp_cong_zero
     andalso r_pow_one_base andalso r_pow_zero_pos
  then out "FLT_HELPERS_OK\n"
  else out "FLT_HELPERS_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  STAGE D : FRESHMAN'S DREAM (mod p)  +  FERMAT'S LITTLE THEOREM  ***
   ----------------------------------------------------------------------------
   On the final context ctxtSub / ctermSub.  Validator = checkSub.
   freshman_dream : jT (prime2 p) ==> jT (cong p (pow (add a b) p)(add (pow a p)(pow b p)))
   flt            : jT (prime2 p) ==> jT (cong p (pow a p) a)
   ============================================================================ *)

val () = out "FLT_STAGE_D_BEGIN\n";

(* ---- additional varifications onto ctxtSub for cong / dvd / mult / le ---- *)
val cong_refl_vSub   = varify cong_refl;     (* jT (cong ?m ?a ?a) *)
val cong_add_vSub    = varify cong_add;      (* cong m a a2 ==> cong m b b2 ==> cong m (a+b)(a2+b2) *)
val cong_trans_vSub  = varify cong_trans;    (* cong m a b ==> cong m b c ==> cong m a c *)
val cong_sym_vSub    = varify cong_sym;      (* cong m a b ==> cong m b a *)
val dvd_mult_right_vSub = varify dvd_mult_right; (* dvd a b ==> dvd a (mult b c) *)
val le_suc_mono_vS2  = varify le_suc_mono;   (* le m n ==> le (Suc m)(Suc n) *)
val conjunct1_vSub   = conjunct1_vC;         (* jT (Conj A B) ==> jT A  (global varified) *)
val mult_1_left_vSub = mult_1_left_vS2;      (* oeq (mult (Suc 0) n) n  (already varified) *)
val add_assoc_vSub   = varify add_assoc;     (* oeq (add (add m n) k)(add m (add n k)) *)
val add_comm_vSub    = varify add_comm;      (* oeq (add m n)(add n m) *)

(* ---- ground instantiators / kernel helpers on ctxtSub ---- *)
fun cong_refl_atSub (mt, at) = beta_norm (Drule.infer_instantiate ctxtSub
      [(("m",0), ctermSub mt),(("a",0), ctermSub at)] cong_refl_vSub);

(* cong_add_atSub (m,a,a2,b,b2) h1 h2 : from cong m a a2 and cong m b b2,
   build cong m (a+b)(a2+b2). *)
fun cong_add_atSub (mt,at,a2t,bt,b2t) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt),(("a",0), ctermSub at),(("a2",0), ctermSub a2t),
         (("b",0), ctermSub bt),(("b2",0), ctermSub b2t)] cong_add_vSub)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* cong_trans_atSub (m,a,b,c) h1 h2 : from cong m a b and cong m b c, build cong m a c. *)
fun cong_trans_atSub (mt,at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt),(("a",0), ctermSub at),(("b",0), ctermSub bt),
         (("c",0), ctermSub ct)] cong_trans_vSub)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* cong_sym_atSub (m,a,b) h : from cong m a b, build cong m b a. *)
fun cong_sym_atSub (mt,at,bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt),(("a",0), ctermSub at),(("b",0), ctermSub bt)] cong_sym_vSub)
  in Thm.implies_elim inst h end;

(* dvd_mult_rightSub (a,b,c) h : from dvd a b, build dvd a (mult b c). *)
fun dvd_mult_rightSub (aT,bT,cT) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("a",0), ctermSub aT),(("b",0), ctermSub bT),(("c",0), ctermSub cT)] dvd_mult_right_vSub)
  in Thm.implies_elim inst h end;

fun le_suc_monoSub (mt,nt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt),(("n",0), ctermSub nt)] le_suc_mono_vS2)
  in Thm.implies_elim inst h end;

fun conjunct1_atSub (At, Bt) hConj =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSub
      [(("A",0), ctermSub At), (("B",0), ctermSub Bt)] conjunct1_vSub)) hConj;

fun addassocSub_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtSub
      [(("m",0), ctermSub mt),(("n",0), ctermSub nt),(("k",0), ctermSub kt)] add_assoc_vSub);
fun addcommSub_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSub
      [(("m",0), ctermSub mt),(("n",0), ctermSub nt)] add_comm_vSub);
fun mult1lSub_at t = beta_norm (Drule.infer_instantiate ctxtSub
      [(("n",0), ctermSub t)] mult_1_left_vSub);

val mult_1_right_vSub = varify mult_1_right;   (* oeq (mult n (Suc 0)) n *)
fun mult_1_right_atSub t = beta_norm (Drule.infer_instantiate ctxtSub
      [(("n",0), ctermSub t)] mult_1_right_vSub);
val mult_0_right_vSub = varify mult_0_right;    (* oeq (mult n 0) 0 *)
fun mult0rSub_at t = beta_norm (Drule.infer_instantiate ctxtSub
      [(("n",0), ctermSub t)] mult_0_right_vSub);

(* p_dvd_binom varified onto ctxtSub :
     jT (prime2 ?p) ==> jT (lt 0 ?k) ==> jT (lt ?k ?p) ==> jT (dvd ?p (binom ?p ?k)) *)
val p_dvd_binom_vSub = varify p_dvd_binom;
fun p_dvd_binom_atSub (pt,kt) hPrime hLt0 hLtkp =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("p",0), ctermSub pt),(("k",0), ctermSub kt)] p_dvd_binom_vSub)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hPrime) hLt0) hLtkp end;

(* binom_theorem varified onto ctxtSub : usable via infer_instantiate at a,b,n *)
val binom_theorem_vSub = binom_theorem;   (* already varify'd in its `in varify ... end` *)
fun binom_theorem_at (aT,bT,nT) =
  beta_norm (Drule.infer_instantiate ctxtSub
    [(("a",0), ctermSub aT),(("b",0), ctermSub bT),(("n",0), ctermSub nT)] binom_theorem_vSub);

(* sum_peel_first varified : oeq (sumf ?f (Suc ?n))(add (?f 0)(sumf (%k. ?f(Suc k)) ?n)) *)
val sum_peel_first_vSub = sum_peel_first;
fun sum_peel_first_at (fT,nT) =
  beta_norm (Drule.infer_instantiate ctxtSub
    [(("f",0), ctermSub fT),(("n",0), ctermSub nT)] sum_peel_first_vSub);

(* sum_all_dvd varified : (!!k. jT(le k ?n) ==> jT(dvd ?p (?f k))) ==> jT(dvd ?p (sumf ?f ?n)) *)
val sum_all_dvd_vSub = sum_all_dvd;
fun sum_all_dvd_at (pT,fT,nT) =
  beta_norm (Drule.infer_instantiate ctxtSub
    [(("p",0), ctermSub pT),(("f",0), ctermSub fT),(("n",0), ctermSub nT)] sum_all_dvd_vSub);

(* dvd_imp_cong_zero varified : jT(dvd ?p ?x) ==> jT(cong ?p ?x Zero) *)
val dvd_imp_cong_zero_vSub = dvd_imp_cong_zero;
fun dvd_imp_cong_zero_at (pT,xT) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("p",0), ctermSub pT),(("x",0), ctermSub xT)] dvd_imp_cong_zero_vSub)
  in Thm.implies_elim inst h end;

(* pow_one_base varified : oeq (pow (Suc 0) ?n)(Suc 0) *)
val pow_one_base_vSub = pow_one_base;
fun pow_one_base_at nT = beta_norm (Drule.infer_instantiate ctxtSub
      [(("n",0), ctermSub nT)] pow_one_base_vSub);

(* pow_zero_pos varified : oeq (pow Zero (Suc ?m)) Zero *)
val pow_zero_pos_vSub = pow_zero_pos;
fun pow_zero_pos_at mT = beta_norm (Drule.infer_instantiate ctxtSub
      [(("m",0), ctermSub mT)] pow_zero_pos_vSub);

(* binom_n_n varified : oeq (binom ?n ?n)(Suc 0) *)
val binom_n_n_vSub = binom_n_n;
fun binom_n_n_at nT = beta_norm (Drule.infer_instantiate ctxtSub
      [(("n",0), ctermSub nT)] binom_n_n_vSub);

(* sub_self varified : oeq (sub ?n ?n) Zero *)
val sub_self_vSub = sub_self;
fun sub_self_at nT = beta_norm (Drule.infer_instantiate ctxtSub
      [(("n",0), ctermSub nT)] sub_self_vSub);

(* sub_n_0 already : subN0S2_at t : oeq (sub t 0) t *)

(* generic le_refl / le_trans / zero_le on ctxtSub : le_reflS2_at, le_transS2_at, zero_leSub_at *)

(* ---- abbreviations for the freshman dream summand ----
   TT = %k. mult (binom p k)(mult (pow a k)(pow b (sub p k)))   (a,b,p Free)   *)

val one = suc ZeroC;

(* mult congruence (both args) helpers already: mult_cong_lS2, mult_cong_rS2 *)
(* oeq_sym/oeq_trans global; substPredS2 global; oeqreflS2_at *)

(* ============================================================================
   PHASE 1 : freshman_dream
   ============================================================================ *)

val freshman_dream =
  let
    val aF = Free("a", natT);
    val bF = Free("b", natT);
    val pF = Free("p", natT);

    (* meta hyp : prime2 p *)
    val primeP = jT (prime2 pF);
    val Hprime = Thm.assume (ctermSub primeP);

    (* GOAL term *)
    val goalC = cong pF (pow (add aF bF) pF) (add (pow aF pF) (pow bF pF));

    (* ---- (1) extract p = Suc(Suc q) from prime2 p ----
         prime2 p = Conj (lt 1 p)(Forall ...) ; lt 1 p = le 2 p = Ex w. oeq p (add 2 w). *)
    val lt1p  = lt one pF;                      (* = le (suc one) p = Ex w. oeq p (add (suc one) w) *)
    val forallPart = (case prime2 pF of (_ $ _ $ rhs) => rhs | _ => error "prime2 shape");
    val Hlt1p = conjunct1_atSub (lt1p, forallPart) Hprime;     (* jT (lt 1 p) = jT (Ex w. oeq p (add 2 w)) *)

    (* lt 1 p  unfolds to  le (suc one) p  =  mkEx (Abs("p", oeq p (add (suc one) (Bound 0)))) *)
    val two = suc one;                          (* Suc (Suc Zero) *)
    val exAbs = Abs("w", natT, oeq pF (add two (Bound 0)));    (* le 2 p body, renamed binder *)

    (* The whole proof body, parametric in the witness w and hw : oeq p (add 2 w). *)
    fun mainBody wF (hw : thm) =
      let
        (* p0 := Suc q ; q := add Zero w *)
        val qT  = add ZeroC wF;                 (* q *)
        val p0T = suc qT;                       (* p0 = Suc q *)
        (* hw : oeq p (add 2 w) ; rewrite add 2 w = Suc(Suc(add 0 w)) = Suc p0 *)
        val aS1 = addSucS2_at (one, wF);        (* oeq (add (Suc 1) w)(Suc (add 1 w))  i.e add 2 w = Suc(add 1 w) *)
        val aS2 = addSucS2_at (ZeroC, wF);      (* oeq (add (Suc 0) w)(Suc (add 0 w))  i.e add 1 w = Suc(add 0 w) *)
        (* Suc(add 1 w) = Suc(Suc(add 0 w)) via Suc_cong *)
        val sAS2 = Suc_cong OF [aS2];           (* oeq (Suc(add 1 w))(Suc(Suc(add 0 w))) = oeq (Suc(add 1 w)) (Suc p0) *)
        val add2w_eq = oeq_trans OF [aS1, sAS2];(* oeq (add 2 w)(Suc(Suc(add 0 w))) = oeq (add 2 w)(Suc p0) *)
        val hp0 = oeq_trans OF [hw, add2w_eq];  (* oeq p (Suc p0) *)
        (* hp0 : oeq p (Suc p0).  We rewrite p<->Suc p0 in terms via substPredS2. *)
        val hp0sym = oeq_sym OF [hp0];          (* oeq (Suc p0) p *)
        val () = out "FD step1 (p=Suc p0) ok\n";

        (* ---- (2) binom theorem at n := p :
             oeq (pow (add a b) p)(sumf TT p)   where TT = summandAbs p ---- *)
        fun summandAbs zt = Abs("k", natT,
              mult (binom zt (Bound 0)) (mult (pow aF (Bound 0)) (pow bF (sub zt (Bound 0)))));
        fun summand_at zt t =
              mult (binom zt t) (mult (pow aF t) (pow bF (sub zt t)));

        val TTabs = summandAbs pF;              (* summand uses the upper bound p in binom/sub *)
        val bthm = binom_theorem_at (aF, bF, pF);   (* oeq (pow (add a b) p)(sumf TTabs p) *)
        val () = out "FD bthm ok\n";

        (* ---- (3) rewrite sumf TTabs p  to  sumf TTabs (Suc p0)  using hp0 on the SECOND arg ----
             predicate %z. oeq (sumf TTabs p)(sumf TTabs z) ; subst a:=p b:=Suc p0 on refl. *)
        val sumf_p_to_Sp0 =
          let
            val Pz = Abs("z", natT, oeq (sumf TTabs pF) (sumf TTabs (Bound 0)));
            val refl0 = oeqreflS2_at (sumf TTabs pF);   (* oeq (sumf TTabs p)(sumf TTabs p) *)
          in substPredS2 (Pz, pF, suc p0T) hp0 refl0 end;   (* oeq (sumf TTabs p)(sumf TTabs (Suc p0)) *)

        (* ---- (4) peel first :  sumf TTabs (Suc p0) = add (TTabs$0)(sumf G p0)  where
             G = %j. TTabs$(Suc j). ---- *)
        val peel = sum_peel_first_at (TTabs, p0T);  (* oeq (sumf TTabs (Suc p0))(add (TTabs$0)(sumf Gabs p0)) *)
        val () = out "FD peel ok\n";
        (* G = %k. TTabs (Suc k) : *)
        val Gabs = Abs("k", natT, summand_at pF (suc (Bound 0)));   (* canonical form of (%k. TTabs$(Suc k)) *)

        (* sanity : the peel's RHS uses  Abs("k", TTabs $ (suc (Bound 0))) ; its beta is summand_at p (suc k) ;
           we ensure Gabs is exactly that beta'd shape so later sumf-cong matches.  We will
           NOT rely on definitional equality of Gabs and sum_peel's lambda; instead we rewrite the
           peel RHS's sum into Gabs via a sum_cong if needed.  But sum_peel_first_at already
           beta_norms, producing summand inside as f(Suc k) = TTabs $ (Suc (Bound 0)) which beta's
           to summand_at p (Suc k) under the binder.  Trust the beta_norm to give Gabs shape. *)

        (* ---- (5) TTabs$0 = pow b p ----
             TTabs$0 = mult (binom p 0)(mult (pow a 0)(pow b (sub p 0)))
                     = mult 1 (mult 1 (pow b p))  [binom_n_0, pow_Zero, sub_n_0]
                     = pow b p  [mult_1_left twice] *)
        val t0_term = summand_at pF ZeroC;      (* mult (binom p 0)(mult (pow a 0)(pow b (sub p 0))) *)
        val bn0 = binomN0S2_at pF;              (* oeq (binom p 0)(Suc 0) *)
        val pa0 = powZeroS2_at aF;              (* oeq (pow a 0)(Suc 0) *)
        val sub_p0 = subN0S2_at pF;             (* oeq (sub p 0) p *)
        (* pow b (sub p 0) = pow b p via pow arg2 cong *)
        val powb_sub =
          let
            val Pz = Abs("z", natT, oeq (pow bF (sub pF ZeroC)) (pow bF (Bound 0)));
            val refl0 = oeqreflS2_at (pow bF (sub pF ZeroC));
          in substPredS2 (Pz, sub pF ZeroC, pF) sub_p0 refl0 end;   (* oeq (pow b (sub p 0))(pow b p) *)
        (* inner = mult (pow a 0)(pow b (sub p 0)) -> mult 1 (pow b p) -> pow b p *)
        val inner_cl = mult_cong_lS2 (pow aF ZeroC, one, pow bF (sub pF ZeroC)) pa0;
                       (* oeq (mult (pow a 0)(pow b (sub p 0)))(mult 1 (pow b (sub p 0))) *)
        val inner_cr = mult_cong_rS2 (one, pow bF (sub pF ZeroC), pow bF pF) powb_sub;
                       (* oeq (mult 1 (pow b (sub p 0)))(mult 1 (pow b p)) *)
        val inner_m1 = mult1lSub_at (pow bF pF);   (* oeq (mult 1 (pow b p))(pow b p) *)
        val inner_eq = oeq_trans OF [oeq_trans OF [inner_cl, inner_cr], inner_m1];
                       (* oeq (mult (pow a 0)(pow b (sub p 0)))(pow b p) *)
        (* whole t0 = mult (binom p 0)(inner) -> mult 1 (pow b p) -> pow b p *)
        val t0_cl = mult_cong_lS2 (binom pF ZeroC, one, mult (pow aF ZeroC)(pow bF (sub pF ZeroC))) bn0;
                    (* oeq (t0_term)(mult 1 (mult (pow a 0)(pow b (sub p 0)))) *)
        val t0_cr = mult_cong_rS2 (one, mult (pow aF ZeroC)(pow bF (sub pF ZeroC)), pow bF pF) inner_eq;
                    (* oeq (mult 1 (mult (pow a 0)(pow b (sub p 0))))(mult 1 (pow b p)) *)
        val t0_m1 = mult1lSub_at (pow bF pF);      (* oeq (mult 1 (pow b p))(pow b p) *)
        val t0_eq = oeq_trans OF [oeq_trans OF [t0_cl, t0_cr], t0_m1];
        val () = out "FD t0_eq ok\n";
                    (* oeq (TTabs$0)(pow b p) *)

        (* ---- (6) sumf G p0  with  p0 = Suc q :
               sumf G (Suc q) = add (sumf G q)(G$(Suc q))  [sumf_Suc]
             G$(Suc q) = TTabs$(Suc(Suc q)) = TTabs$(Suc p0) = TTabs$p [via hp0 sym]
                       = mult (binom p p)(mult (pow a p)(pow b (sub p p)))
                       = mult 1 (mult (pow a p) 1)... = pow a p. ---- *)
        val sumfG_Suc = sumfSuc_at (Gabs, qT);     (* oeq (sumf G (Suc q))(add (sumf G q)(G$(Suc q))) *)
        (* G$(Suc q) beta = summand_at p (Suc(Suc q)) = summand_at p (Suc p0) *)
        val GatSq_term = summand_at pF (suc p0T);  (* = summand_at p (Suc(Suc q)) ; note suc p0T = Suc(Suc q) *)

        (* rewrite summand_at p (Suc p0) -> summand_at p p using hp0sym : oeq (Suc p0) p,
           applied inside binom 1st-arg-stays-p but the INDEX (Suc p0) -> p.  The summand_at's
           index appears in: binom p (Suc p0), pow a (Suc p0), sub p (Suc p0).  We substitute
           the INDEX (Suc p0) := p via substPredS2 with predicate over the index. *)
        val GatSq_to_p =
          let
            val Pz = Abs("z", natT,
                       oeq (summand_at pF (suc p0T)) (summand_at pF (Bound 0)));
            val refl0 = oeqreflS2_at (summand_at pF (suc p0T));
          in substPredS2 (Pz, suc p0T, pF) hp0sym refl0 end;
            (* oeq (summand_at p (Suc p0))(summand_at p p) *)

        (* summand_at p p = mult (binom p p)(mult (pow a p)(pow b (sub p p)))
                          = mult 1 (mult (pow a p) 1) [binom_n_n, sub_self->pow b 0->1]
                          = pow a p *)
        val tp_term = summand_at pF pF;
        val bnn = binom_n_n_at pF;               (* oeq (binom p p)(Suc 0) *)
        val subpp = sub_self_at pF;              (* oeq (sub p p) Zero *)
        (* pow b (sub p p) = pow b 0 = Suc 0 *)
        val powb_subpp =
          let
            val Pz = Abs("z", natT, oeq (pow bF (sub pF pF)) (pow bF (Bound 0)));
            val refl0 = oeqreflS2_at (pow bF (sub pF pF));
          in substPredS2 (Pz, sub pF pF, ZeroC) subpp refl0 end;   (* oeq (pow b (sub p p))(pow b 0) *)
        val powb0 = powZeroS2_at bF;             (* oeq (pow b 0)(Suc 0) *)
        val powb_subpp_1 = oeq_trans OF [powb_subpp, powb0];   (* oeq (pow b (sub p p))(Suc 0) *)
        (* inner = mult (pow a p)(pow b (sub p p)) -> mult (pow a p) 1 -> pow a p *)
        val tp_inner_cr = mult_cong_rS2 (pow aF pF, pow bF (sub pF pF), one) powb_subpp_1;
                          (* oeq (mult (pow a p)(pow b (sub p p)))(mult (pow a p) 1) *)
        val tp_inner_m1 = mult_1_right_atSub (pow aF pF);   (* oeq (mult (pow a p) 1)(pow a p) *)
        val tp_inner_eq = oeq_trans OF [tp_inner_cr, tp_inner_m1];
                          (* oeq (mult (pow a p)(pow b (sub p p)))(pow a p) *)
        val tp_cl = mult_cong_lS2 (binom pF pF, one, mult (pow aF pF)(pow bF (sub pF pF))) bnn;
                    (* oeq (tp_term)(mult 1 (mult (pow a p)(pow b (sub p p)))) *)
        val tp_cr = mult_cong_rS2 (one, mult (pow aF pF)(pow bF (sub pF pF)), pow aF pF) tp_inner_eq;
                    (* oeq (mult 1 ...)(mult 1 (pow a p)) *)
        val tp_m1 = mult1lSub_at (pow aF pF);    (* oeq (mult 1 (pow a p))(pow a p) *)
        val tp_eq = oeq_trans OF [oeq_trans OF [tp_cl, tp_cr], tp_m1];
                    (* oeq (summand_at p p)(pow a p) *)
        (* combine : G$(Suc q) = summand_at p (Suc p0) = summand_at p p = pow a p *)
        val GatSq_eq = oeq_trans OF [GatSq_to_p, tp_eq];   (* oeq (G$(Suc q))(pow a p) *)
        val () = out "FD GatSq_eq ok\n";

        (* ---- (7) MIDDLE := sumf G q ; show dvd p MIDDLE via sum_all_dvd ----
             meta hyp for sum_all_dvd : !!k. le k q ==> dvd p (G$k)
             G$k = summand_at p (Suc k) = mult (binom p (Suc k))(...) ;
             need dvd p (binom p (Suc k)) [p_dvd_binom : prime2 p, lt 0 (Suc k), lt (Suc k) p],
             then dvd_mult_right -> dvd p (G$k). *)
        val MIDDLE = sumf Gabs qT;
        (* build the !!k object meta-hyp proof *)
        val kF = Free("kfd", natT);
        val mhProp = Logic.all kF (Logic.mk_implies (jT (le kF qT), jT (dvd pF (Gabs $ kF))));
        (* the actual sum_all_dvd theorem instance, then discharge its meta hyp *)
        val sad_inst = sum_all_dvd_at (pF, Gabs, qT);    (* (!!k. le k q ==> dvd p (G k)) ==> dvd p (sumf G q) *)

        (* prove the meta hyp : assume le k q, derive dvd p (G$k) *)
        val dvdMiddle =
          let
            val hlekq = Thm.assume (ctermSub (jT (le kF qT)));    (* le k q *)
            (* lt 0 (Suc k) = le (suc 0)(Suc k) = le 1 (Suc k).  Prove via le_suc_mono on (le 0 k). *)
            val le0k  = zero_leSub_at kF;                         (* le 0 k *)
            val lt0Sk = le_suc_monoSub (ZeroC, kF) le0k;          (* le (Suc 0)(Suc k) = lt 0 (Suc k) *)
            (* lt (Suc k) p = le (Suc(Suc k)) p.  From le k q :
                 le (Suc k)(Suc q) = le (Suc k) p0      [le_suc_mono]
                 le (Suc(Suc k))(Suc(Suc q)) = le (Suc(Suc k))(Suc p0)  [le_suc_mono again]
               Suc p0 = Suc(Suc q).  And p = Suc p0.  So le (Suc(Suc k))(Suc p0), rewrite Suc p0 -> p. *)
            val leSkSq  = le_suc_monoSub (kF, qT) hlekq;          (* le (Suc k)(Suc q) = le (Suc k) p0 *)
            val leSSkSp0= le_suc_monoSub (suc kF, p0T) leSkSq;    (* le (Suc(Suc k))(Suc p0) *)
            (* rewrite (Suc p0) -> p in  le (Suc(Suc k)) (Suc p0)  using hp0sym : oeq (Suc p0) p *)
            val ltSkp =
              let
                val zF = Free("zlt", natT);
                val Pz = Term.lambda zF (le (suc (suc kF)) zF);   (* de Bruijn-safe : le has an Ex binder inside *)
                (* le (suc(suc k)) (Suc p0) is jT-wrapped; we have leSSkSp0 : jT (le (suc(suc k))(Suc p0)) *)
              in substPredS2 (Pz, suc p0T, pF) hp0sym leSSkSp0 end;   (* jT (le (Suc(Suc k)) p) = jT (lt (Suc k) p) *)
            (* p_dvd_binom at (p, Suc k) *)
            val dvdBinom = p_dvd_binom_atSub (pF, suc kF) Hprime lt0Sk ltSkp;
                           (* jT (dvd p (binom p (Suc k))) *)
            (* G$k = summand_at p (Suc k) = mult (binom p (Suc k))(mult (pow a (Suc k))(pow b (sub p (Suc k)))) *)
            val restTerm = mult (pow aF (suc kF)) (pow bF (sub pF (suc kF)));
            val dvdGk = dvd_mult_rightSub (pF, binom pF (suc kF), restTerm) dvdBinom;
                        (* jT (dvd p (mult (binom p (Suc k)) restTerm)) = jT (dvd p (G$k)) *)
            (* G$k beta : Gabs $ kF = summand_at p (Suc k).  dvdGk's term must aconv jT (dvd p (Gabs$kF)).
               Gabs $ kF beta-reduces to summand_at p (Suc k) = mult (binom p (Suc k)) restTerm. OK. *)
            val body  = Thm.implies_intr (ctermSub (jT (le kF qT))) dvdGk;
          in Thm.forall_intr (ctermSub kF) body end;   (* !!k. le k q ==> dvd p (G k) *)

        val dvdMID = Thm.implies_elim sad_inst dvdMiddle;   (* jT (dvd p (sumf G q)) = jT (dvd p MIDDLE) *)
        val () = out "FD dvdMID ok\n";

        (* ---- (8) assemble the equation :
             pow (add a b) p = sumf TTabs p           [bthm]
                             = sumf TTabs (Suc p0)    [sumf_p_to_Sp0]
                             = add (TTabs$0)(sumf G p0)  [peel]
                             = add (pow b p)(sumf G p0)  [t0_eq, add_cong_l]
             sumf G p0 = sumf G (Suc q) = add (sumf G q)(G$(Suc q))  [sumfG_Suc]
                       = add MIDDLE (pow a p)    [GatSq_eq, add_cong_r]
             so pow (add a b) p = add (pow b p)(add MIDDLE (pow a p)).
             Call RHS_form := add (pow b p)(add MIDDLE (pow a p)). ---- *)
        val eq1 = oeq_trans OF [bthm, sumf_p_to_Sp0];   (* pow(a+b)p = sumf TTabs (Suc p0) *)
        val eq2 = oeq_trans OF [eq1, peel];             (* = add (TTabs$0)(sumf G p0) *)
        (* note: peel RHS is  add (TTabs$0)(sumf Gabs p0) where Gabs is the beta'd %k. TTabs(Suc k). *)
        (* rewrite TTabs$0 -> pow b p *)
        val eq3 =
          let val cl = add_cong_lS2 (summand_at pF ZeroC, pow bF pF, sumf Gabs p0T) t0_eq
                       (* add (TTabs$0)(sumf G p0) = add (pow b p)(sumf G p0) *)
          in oeq_trans OF [eq2, cl] end;                (* pow(a+b)p = add (pow b p)(sumf G p0) *)
        (* expand sumf G p0 = sumf G (Suc q) = add (sumf G q)(G$(Suc q)) ; p0T = suc qT already *)
        val eqMidExpand =
          let val cr = add_cong_rS2 (pow bF pF, sumf Gabs p0T, add MIDDLE GatSq_term) sumfG_Suc
                       (* add (pow b p)(sumf G (Suc q)) = add (pow b p)(add MIDDLE (G$(Suc q))) *)
          in oeq_trans OF [eq3, cr] end;                (* pow(a+b)p = add (pow b p)(add MIDDLE (G$(Suc q))) *)
        (* rewrite G$(Suc q) -> pow a p *)
        val eqFinalForm =
          let val cr2 = add_cong_rS2 (pow bF pF, add MIDDLE GatSq_term, add MIDDLE (pow aF pF))
                          (add_cong_rS2 (MIDDLE, GatSq_term, pow aF pF) GatSq_eq)
                       (* add (pow b p)(add MIDDLE (G$(Suc q))) = add (pow b p)(add MIDDLE (pow a p)) *)
          in oeq_trans OF [eqMidExpand, cr2] end;       (* pow(a+b)p = add (pow b p)(add MIDDLE (pow a p)) *)

        (* ---- (9) now to congruence.  We have :
             E : oeq (pow (add a b) p) (add (pow b p)(add MIDDLE (pow a p)))
           and dvdMID : dvd p MIDDLE -> cong p MIDDLE Zero [dvd_imp_cong_zero].
           Target : cong p (pow(a+b)p)(add (pow a p)(pow b p)).
           Strategy:
             cong p (pow(a+b)p) RHS_form  [from E, via cong over oeq : use cong_introR/refl?]
             Actually use: oeq x y ==> cong p x y.  Build it from E.
           Then show cong p RHS_form (add (pow a p)(pow b p)) :
             RHS_form = add (pow b p)(add MIDDLE (pow a p)).
             cong p MIDDLE Zero, cong_refl elsewhere, cong_add to absorb MIDDLE,
             then oeq-rearrange add (pow b p)(add Zero (pow a p)) = add (pow a p)(pow b p). *)

        (* helper : oeq x y ==> cong p x y  (use cong_introR with witness Zero:
             congR p x y body = oeq x (add y (mult p 0)); need oeq x (add y (mult p 0)).
             from hxy : oeq x y :  y = add y 0 [add_0_right sym]; mult p 0 = 0 [mult_0_right];
             add y (mult p 0) = add y 0 = y ; so oeq x (add y (mult p 0)) by trans(hxy, sym(...)). *)
        fun oeq_to_cong (xT, yT) hxy =
          let
            val m0  = mult0rSub_at pF;                  (* oeq (mult p 0) 0 *)
            val cr  = add_cong_rS2 (yT, mult pF ZeroC, ZeroC) m0;   (* add y (mult p 0) = add y 0 *)
            val a0r = add0rS2_at yT;                    (* add y 0 = y *)
            val rhs_eq = oeq_trans OF [cr, a0r];        (* add y (mult p 0) = y *)
            val rhs_sym= oeq_sym OF [rhs_eq];           (* y = add y (mult p 0) *)
            val chain  = oeq_trans OF [hxy, rhs_sym];   (* oeq x (add y (mult p 0)) *)
          in cong_introRSub (pF, xT, yT, ZeroC) chain end;   (* jT (cong p x y) *)

        (* congE : cong p (pow(a+b)p) RHS_form *)
        val RHS_form = add (pow bF pF) (add MIDDLE (pow aF pF));
        val congE = oeq_to_cong (pow (add aF bF) pF, RHS_form) eqFinalForm;

        (* cong p RHS_form (add (pow a p)(pow b p)) :
             RHS_form = add (pow b p)(add MIDDLE (pow a p))
             Step A: cong p MIDDLE Zero  [dvd_imp_cong_zero]
             Step B: cong p (add MIDDLE (pow a p))(add Zero (pow a p))
                       = cong_add (cong p MIDDLE Zero)(cong_refl p (pow a p))
             Step C: cong p (add (pow b p)(add MIDDLE (pow a p)))(add (pow b p)(add Zero (pow a p)))
                       = cong_add (cong_refl p (pow b p)) (Step B)
             Step D: oeq (add (pow b p)(add Zero (pow a p)))(add (pow a p)(pow b p))   [arith]
                     then cong via oeq_to_cong, and cong_trans C,D.
        *)
        val congMidZero = dvd_imp_cong_zero_at (pF, MIDDLE) dvdMID;   (* cong p MIDDLE Zero *)
        val congReflPa  = cong_refl_atSub (pF, pow aF pF);           (* cong p (pow a p)(pow a p) *)
        val congReflPb  = cong_refl_atSub (pF, pow bF pF);           (* cong p (pow b p)(pow b p) *)
        (* Step B *)
        val congB = cong_add_atSub (pF, MIDDLE, ZeroC, pow aF pF, pow aF pF) congMidZero congReflPa;
                    (* cong p (add MIDDLE (pow a p))(add Zero (pow a p)) *)
        (* Step C *)
        val congC = cong_add_atSub (pF, pow bF pF, pow bF pF, add MIDDLE (pow aF pF), add ZeroC (pow aF pF))
                       congReflPb congB;
                    (* cong p (add (pow b p)(add MIDDLE (pow a p)))(add (pow b p)(add Zero (pow a p)))
                       = cong p RHS_form (add (pow b p)(add Zero (pow a p))) *)
        (* Step D : oeq (add (pow b p)(add Zero (pow a p)))(add (pow a p)(pow b p)) *)
        val congD =
          let
            (* add Zero (pow a p) = pow a p [add_0] *)
            val a0 = add0S2_at (pow aF pF);             (* oeq (add Zero (pow a p))(pow a p) *)
            val cr = add_cong_rS2 (pow bF pF, add ZeroC (pow aF pF), pow aF pF) a0;
                     (* add (pow b p)(add Zero (pow a p)) = add (pow b p)(pow a p) *)
            (* add (pow b p)(pow a p) = add (pow a p)(pow b p) [add_comm] *)
            val comm = addcommSub_at (pow bF pF, pow aF pF);   (* oeq (add (pow b p)(pow a p))(add (pow a p)(pow b p)) *)
            val dEq = oeq_trans OF [cr, comm];          (* oeq (add(pb)(add 0 pa))(add pa pb) *)
          in oeq_to_cong (add (pow bF pF) (add ZeroC (pow aF pF)), add (pow aF pF) (pow bF pF)) dEq end;
            (* cong p (add (pow b p)(add Zero (pow a p)))(add (pow a p)(pow b p)) *)

        (* combine C, D : cong p RHS_form (add (pow a p)(pow b p)) *)
        val congCD = cong_trans_atSub (pF, RHS_form, add (pow bF pF) (add ZeroC (pow aF pF)),
                                        add (pow aF pF) (pow bF pF)) congC congD;
        (* combine E, CD : cong p (pow(a+b)p)(add (pow a p)(pow b p)) *)
        val congFinal = cong_trans_atSub (pF, pow (add aF bF) pF, RHS_form,
                                           add (pow aF pF) (pow bF pF)) congE congCD;
        val () = out "FD assembly ok\n";
      in congFinal end;   (* jT (cong p (pow(a+b)p)(add (pow a p)(pow b p))) = goalC *)

    (* eliminate the existential lt 1 p = Ex w. oeq p (add 2 w) *)
    val concl = exESub_elim (exAbs, goalC) Hlt1p "wfd" mainBody;
    (* discharge prime2 p meta hyp *)
    val res = Thm.implies_intr (ctermSub primeP) concl;
  in varify res end;

(* intended freshman_dream statement *)
val i_freshman_dream =
  Logic.mk_implies (jT (prime2 pVs),
    jT (cong pVs (pow (add aVs bVs) pVs) (add (pow aVs pVs) (pow bVs pVs))));
val r_freshman_dream = checkSub ("freshman_dream", freshman_dream, i_freshman_dream);
val () = if r_freshman_dream then out "FRESHMAN_DREAM_DONE\n" else out "FRESHMAN_DREAM_FAILED\n";

(* ============================================================================
   PHASE 2 : Fermat's little theorem
     flt : jT (prime2 p) ==> jT (cong p (pow a p) a)
   Induction on a (p Free, prime2 p in scope).
   ============================================================================ *)

(* freshman_dream varified : usable at (a, b, p) — but we need prime2 p in scope as the
   premise, so we instantiate and discharge with Hprime. *)
val freshman_dream_vSub = freshman_dream;   (* already varify'd *)
fun freshman_dream_at (aT,bT,pT) hPrime =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("a",0), ctermSub aT),(("b",0), ctermSub bT),(("p",0), ctermSub pT)] freshman_dream_vSub)
  in Thm.implies_elim inst hPrime end;   (* jT (cong p (pow (a+b) p)(add (pow a p)(pow b p))) *)

val flt =
  let
    val pF = Free("p", natT);
    val primeP = jT (prime2 pF);
    val Hprime = Thm.assume (ctermSub primeP);

    (* extract p = Suc p0 from prime2 p (only needed for the base case pow 0 p = 0). *)
    val lt1p  = lt one pF;
    val forallPart = (case prime2 pF of (_ $ _ $ rhs) => rhs | _ => error "prime2 shape");
    val Hlt1p = conjunct1_atSub (lt1p, forallPart) Hprime;
    val two = suc one;
    val exAbs = Abs("w", natT, oeq pF (add two (Bound 0)));

    (* GOAL of the induction : Q a = cong p (pow a p) a *)
    val aIndV = Free("a", natT);
    (* cong contains Ex/Disj binders -> build the induction predicate with a Free + Term.lambda
       (de Bruijn-safe; a bare Abs("z", cong .. (Bound 0) ..) mis-indexes under cong's Ex). *)
    val zQF = Free("zq", natT);
    val Qpred = Term.lambda zQF (cong pF (pow zQF pF) zQF);
    val ind = nat_induct_atS2 (Qpred, aIndV);

    (* BASE a = 0 :  cong p (pow 0 p) 0.
         pow 0 p = pow 0 (Suc p0) = 0  [pow_zero_pos].  Then cong p 0 0 [cong_refl],
         and rewrite pow 0 p back into the cong via oeq (need cong p (pow 0 p) 0). *)
    val base =
      let
        fun baseBody wF (hw : thm) =
          let
            val qT  = add ZeroC wF;
            val p0T = suc qT;
            val aS1 = addSucS2_at (one, wF);
            val aS2 = addSucS2_at (ZeroC, wF);
            val sAS2 = Suc_cong OF [aS2];
            val add2w_eq = oeq_trans OF [aS1, sAS2];
            val hp0 = oeq_trans OF [hw, add2w_eq];     (* oeq p (Suc p0) *)
            (* pow 0 p = pow 0 (Suc p0) [hp0 on 2nd arg] = 0 [pow_zero_pos] *)
            val pow0p_to_Sp0 =
              let
                val Pz = Abs("z", natT, oeq (pow ZeroC pF) (pow ZeroC (Bound 0)));
                val refl0 = oeqreflS2_at (pow ZeroC pF);
              in substPredS2 (Pz, pF, suc p0T) hp0 refl0 end;  (* oeq (pow 0 p)(pow 0 (Suc p0)) *)
            val pzp = pow_zero_pos_at p0T;             (* oeq (pow 0 (Suc p0)) 0 *)
            val pow0p_eq0 = oeq_trans OF [pow0p_to_Sp0, pzp];  (* oeq (pow 0 p) 0 *)
            (* target : cong p (pow 0 p) 0.  We have oeq (pow 0 p) 0 -> use oeq_to_cong. *)
            fun oeq_to_cong (xT, yT) hxy =
              let
                val m0  = mult0rSub_at pF;
                val cr  = add_cong_rS2 (yT, mult pF ZeroC, ZeroC) m0;
                val a0r = add0rS2_at yT;
                val rhs_eq = oeq_trans OF [cr, a0r];
                val rhs_sym= oeq_sym OF [rhs_eq];
                val chain  = oeq_trans OF [hxy, rhs_sym];
              in cong_introRSub (pF, xT, yT, ZeroC) chain end;
          in oeq_to_cong (pow ZeroC pF, ZeroC) pow0p_eq0 end;   (* cong p (pow 0 p) 0 = Q 0 *)
        val concl = exESub_elim (exAbs, cong pF (pow ZeroC pF) ZeroC) Hlt1p "wb" baseBody;
      in concl end;   (* jT (cong p (pow 0 p) 0) = jT (Qpred $ 0) *)
    val () = out "FLT base ok\n";

    (* STEP a -> Suc a :  IH : cong p (pow a p) a ; prove cong p (pow (Suc a) p)(Suc a). *)
    val xF = Free("xa", natT);
    val ihprop = jT (cong pF (pow xF pF) xF);
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        (* Suc a = add a (Suc 0) :  add a (Suc 0) = Suc (add a 0) [add_Suc_right] = Suc a [add_0_right] *)
        val asr  = addSrS2_at (xF, ZeroC);          (* oeq (add a (Suc 0))(Suc (add a 0)) *)
        val a0r  = add0rS2_at xF;                    (* oeq (add a 0) a *)
        val sucA = Suc_cong OF [a0r];                (* oeq (Suc (add a 0))(Suc a) *)
        val Sa_as_add = oeq_trans OF [asr, sucA];    (* oeq (add a (Suc 0))(Suc a) *)
        val Sa_as_add_sym = oeq_sym OF [Sa_as_add];  (* oeq (Suc a)(add a (Suc 0)) *)

        (* freshman_dream at (a, Suc 0) :
             cong p (pow (add a (Suc 0)) p)(add (pow a p)(pow (Suc 0) p)) *)
        val fd = freshman_dream_at (xF, one, pF) Hprime;
                 (* cong p (pow (add a 1) p)(add (pow a p)(pow 1 p)) *)
        val () = out "FLT fd ok\n";

        (* pow (Suc 0) p = Suc 0  [pow_one_base] ; so rewrite RHS add (pow a p)(pow 1 p)
             into add (pow a p)(Suc 0) inside the cong via cong over oeq. *)
        val powOne_p = pow_one_base_at pF;           (* oeq (pow (Suc 0) p)(Suc 0) *)
        (* cong p (add (pow a p)(pow 1 p))(add (pow a p)(Suc 0)) via cong_add(refl)(oeq->cong) *)
        fun oeq_to_cong (xT, yT) hxy =
          let
            val m0  = mult0rSub_at pF;
            val cr  = add_cong_rS2 (yT, mult pF ZeroC, ZeroC) m0;
            val a0rr = add0rS2_at yT;
            val rhs_eq = oeq_trans OF [cr, a0rr];
            val rhs_sym= oeq_sym OF [rhs_eq];
            val chain  = oeq_trans OF [hxy, rhs_sym];
          in cong_introRSub (pF, xT, yT, ZeroC) chain end;

        (* Build: cong p (pow (add a 1) p)(add (pow a p)(Suc 0)) :
             from fd (cong to add(pow a p)(pow 1 p)) and cong (add(pow a p)(pow1p))(add(pow a p)(1)). *)
        val congPow1 =
          let val c = oeq_to_cong (pow one pF, one) powOne_p   (* cong p (pow 1 p)(Suc 0) *)
              val crefl = cong_refl_atSub (pF, pow xF pF)       (* cong p (pow a p)(pow a p) *)
          in cong_add_atSub (pF, pow xF pF, pow xF pF, pow one pF, one) crefl c end;
             (* cong p (add (pow a p)(pow 1 p))(add (pow a p)(Suc 0)) *)
        val fd2 = cong_trans_atSub (pF, pow (add xF one) pF, add (pow xF pF)(pow one pF),
                                     add (pow xF pF) one) fd congPow1;
                  (* cong p (pow (add a 1) p)(add (pow a p)(Suc 0)) *)
        val () = out "FLT fd2 ok\n";

        (* IH : cong p (pow a p) a ; cong_refl p (Suc 0) -> cong_add :
             cong p (add (pow a p)(Suc 0))(add a (Suc 0)) *)
        val crefl1 = cong_refl_atSub (pF, one);      (* cong p (Suc 0)(Suc 0) *)
        val congSum = cong_add_atSub (pF, pow xF pF, xF, one, one) IH crefl1;
                      (* cong p (add (pow a p)(Suc 0))(add a (Suc 0)) *)

        (* cong p (add a (Suc 0))(Suc a)  via oeq Sa_as_add : oeq (add a 1)(Suc a) -> cong *)
        val congSa = oeq_to_cong (add xF one, suc xF) Sa_as_add;   (* cong p (add a 1)(Suc a) *)

        (* chain : cong p (pow (add a 1) p)(Suc a) *)
        val c1 = cong_trans_atSub (pF, pow (add xF one) pF, add (pow xF pF) one, add xF one) fd2 congSum;
                 (* cong p (pow (add a 1) p)(add a (Suc 0)) *)
        val c2 = cong_trans_atSub (pF, pow (add xF one) pF, add xF one, suc xF) c1 congSa;
                 (* cong p (pow (add a 1) p)(Suc a) *)
        val () = out "FLT c2 ok\n";

        (* rewrite pow (add a 1) p -> pow (Suc a) p using Sa_as_add : oeq (add a 1)(Suc a),
           inside the cong's FIRST argument (the base of pow). *)
        val c3 =
          let
            (* predicate %z. cong p (pow z p)(Suc a) ; subst (add a 1) := (Suc a)
               cong contains Ex/Disj binders -> use Free + Term.lambda (de Bruijn-safe). *)
            val zF = Free("zc3", natT);
            val Pz = Term.lambda zF (cong pF (pow zF pF) (suc xF))
          in substPredS2 (Pz, add xF one, suc xF) Sa_as_add c2 end;
            (* cong p (pow (Suc a) p)(Suc a) = Q (Suc a) *)
        val () = out "FLT c3 (stepconcl) ok\n";
      in c3 end;

    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val Qa = Thm.implies_elim r1 step1;     (* !! actually : implies_elim with step1 gives jT (Qpred $ a)?? *)
    (* nat_induct : P 0 ==> (!!x. P x ==> P (Suc x)) ==> P k ; here k := aIndV (Free a).
       So Qa : jT (Qpred $ aIndV) = jT (cong p (pow a p) a). *)
    val () = out "FLT Qa ok\n";
    val res = Thm.implies_intr (ctermSub primeP) Qa;
  in varify res end;

val i_flt =
  Logic.mk_implies (jT (prime2 pVs),
    jT (cong pVs (pow aVs pVs) aVs));
val r_flt = checkSub ("flt", flt, i_flt);
val () = if r_flt then out "OK flt\n" else out "FLT_MAIN_FAILED\n";

(* ---- soundness probe : the kernel must REJECT flt without prime2 p ----
   confirm our proved flt STILL carries the prime2 p premise. *)
val flt_false_variant = jT (cong pVs (pow aVs pVs) aVs);
val flt_needs_prime = not ((Thm.prop_of flt) aconv flt_false_variant);

val () =
  if r_freshman_dream andalso r_flt andalso flt_needs_prime
  then out "FLT_DONE\n"
  else out "FLT_INCOMPLETE\n";
(* ============================================================================
   EULER'S CRITERION — BASE.  Built on flt.sml's final context (ctxtSub: sub +
   sumf on top of pow on top of the euclid/modular base ctxtS2).  flt.sml has
   already given us, all on ctxtSub / ctxtS2:
     flt              : prime2 p ==> cong p (pow a p) a       (Fermat)
     euclid_lemma     : prime2 p ==> dvd p (a*b) ==> dvd p a \/ dvd p b
     pow / pow_Suc_ax / pow_Zero_ax / pow_add / cong_pow / pow_mult_base
     cong + cong_refl/sym/trans/add/mult (on ctxtS2 and ctxtSub)
     sub + sub_n_0_ax/sub_0_Suc_ax/sub_Suc_Suc_ax
     prime2 + destructors, dvd, le, lt machinery.

   We ADD, on ctxtS2 (then varify):
     mod_cancel       : prime2 p ==> ~(p|a) ==> cong p (a*b)(a*c) ==> cong p b c
     lagrange_roots   : prime2 p ==> cong p (a*a) 1 ==> cong p a 1 \/ cong p (Suc a) 0
   (both verbatim from isabelle_mult_group.sml — they are euclid_lemma-based,
    using only helpers flt's embedded ntbase already provides).

   Then we DERIVE Fermat-for-units:
     apm1             : prime2 p ==> ~(p|a) ==> cong p (pow a (sub p 1)) 1
   from flt + mod_cancel:  a^p = a * a^(p-1)  and  a^p == a == a*1, cancel a.
   ============================================================================ *)

val () = out "EULERCRIT_BASE_DELTA_BEGIN\n";

(* ---- bridge helpers the copied mult_group bodies need but flt names elsewhere ---- *)
val oneC = suc ZeroC;

(* ne0_suc_atS : jT (neg (oeq d 0)) ==> jT (Ex m. oeq d (Suc m))  (gcd.sml:844) *)
val ne0_suc_vS   = varify ne0_suc;
fun ne0_suc_atS dt hne =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2 [(("d",0), ctermS2 dt)] ne0_suc_vS)
  in Thm.implies_elim inst hne end;

(* mult_Suc_atS : oeq (mult (Suc m) n) (add n (mult m n))  (gcd.sml:847) *)
val mult_Suc_vS  = varify mult_Suc;
fun mult_Suc_atS (mt, nt) = beta_norm (Drule.infer_instantiate ctxtS2
      [(("m",0), ctermS2 mt), (("n",0), ctermS2 nt)] mult_Suc_vS);

val () = out "EULERCRIT_BRIDGE_READY\n";

(* ============================================================================
   ====================  mod_cancel  (verbatim from mult_group.sml)  ===========
   ============================================================================ *)
val () = out "MOD_CANCEL_BEGIN\n";

(* euclid_lemma on ctxtS2 : jT (prime2 p) ==> jT (dvd p (a*b)) ==> jT (Disj (dvd p a)(dvd p b)) *)
val euclid_lemma_vMC = varify euclid_lemma;
fun euclid_atMC (pT, aT, bT) hPr hDvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("p",0), ctermS2 pT), (("a",0), ctermS2 aT), (("b",0), ctermS2 bT)] euclid_lemma_vMC)
  in Thm.implies_elim (Thm.implies_elim inst hPr) hDvd end;

val mod_cancel =
  let
    val pF = Free("p", natT);
    val aF = Free("a", natT);
    val bF = Free("b", natT);
    val cF = Free("c", natT);

    val hPrimeP = jT (prime2 pF);          val hPrime = Thm.assume (ctermS2 hPrimeP);
    val hNdvdP  = jT (neg (dvd pF aF));     val hNdvd  = Thm.assume (ctermS2 hNdvdP);
    val hCongP  = jT (cong pF (mult aF bF) (mult aF cF));
    val hCong   = Thm.assume (ctermS2 hCongP);

    val goalC = cong pF bF cF;

    (* ---- a <> 0  (else p | 0 = a contradicts ~(p|a)) ---- *)
    val axne0 =
      let
        val ha0 = Thm.assume (ctermS2 (jT (oeq aF ZeroC)));        (* a = 0 *)
        val z_p0 = oeq_sym OF [mult0rS_at pF];                     (* 0 = p*0 *)
        val dvd_p0 = dvd_introS (pF, ZeroC, ZeroC) z_p0;           (* dvd p 0 *)
        val dvd_pa = dvd_cong_rS (pF, ZeroC, aF) (oeq_sym OF [ha0]) dvd_p0;  (* dvd p a *)
        val fls = mp_atS2 (dvd pF aF, oFalseC) hNdvd dvd_pa;       (* oFalse *)
        val metaNe = Thm.implies_intr (ctermS2 (jT (oeq aF ZeroC))) fls;
      in impI_atS2 (oeq aF ZeroC, oFalseC) metaNe end;            (* jT (neg (oeq a 0)) *)
    val aSucEx = ne0_suc_atS aF axne0;                             (* Ex m. oeq a (Suc m) *)

    (* ---- cancel_core : le X Y  ==>  oeq (a*Y) ((a*X) + p*k)  ==>  jT (congL p X Y)
            (Ex j. Y = X + p*j).  No a>0 needed (euclid kills the a-branch). ---- *)
    fun cancel_core (X, Y, kT) hle heqYX =
      let
        val leAbs = Abs("q", natT, oeq Y (add X (Bound 0)));       (* le X Y body *)
        fun body dW (hd : thm) =                                   (* hd : oeq Y (add X dW) *)
          let
            val mcong = mult_cong_rS (aF, Y, add X dW) hd;         (* a*Y = a*(X+d) *)
            val ld    = left_distrib_atS (aF, X, dW);              (* a*(X+d) = a*X + a*d *)
            val aYeq  = oeq_trans OF [mcong, ld];                  (* a*Y = a*X + a*d *)
            val combined = oeq_trans OF [oeq_sym OF [aYeq], heqYX];(* (a*X + a*d) = (a*X + p*k) *)
            val adk   = add_left_cancel_atS (mult aF X, mult aF dW, mult pF kT) combined; (* a*d = p*k *)
            val dvd_p_ad = dvd_introS (pF, mult aF dW, kT) adk;    (* dvd p (a*d) *)
            val eDisj = euclid_atMC (pF, aF, dW) hPrime dvd_p_ad;  (* Disj (dvd p a)(dvd p d) *)
            val goalCL = congL pF X Y;                             (* Ex j. Y = X + p*j *)
            (* case dvd p a : contradiction *)
            val caseA =
              let
                val hda = Thm.assume (ctermS2 (jT (dvd pF aF)));
                val fls = mp_atS2 (dvd pF aF, oFalseC) hNdvd hda; (* oFalse *)
                val any = oFalse_elimS_at goalCL;                  (* jT oFalse ==> jT goalCL *)
              in Thm.implies_intr (ctermS2 (jT (dvd pF aF))) (Thm.implies_elim any fls) end;
            (* case dvd p d : d = p*j -> Y = X + p*j -> congL *)
            val caseD =
              let
                val hdd = Thm.assume (ctermS2 (jT (dvd pF dW)));
                val dvdAbs = Abs("k", natT, oeq dW (mult pF (Bound 0)));   (* dvd p d body *)
                fun jbody jW (hj : thm) =                          (* hj : oeq d (p*j) *)
                  let
                    val ac = add_cong_rS (X, dW, mult pF jW) hj;  (* (X+d) = (X + p*j) *)
                    val Yeq = oeq_trans OF [hd, ac];               (* Y = X + p*j *)
                    val congLabs = Abs("k", natT, oeq Y (add X (mult pF (Bound 0))));
                  in exI_atS2 congLabs jW Yeq end;                 (* jT (congL p X Y) *)
                val res = exE_elimS2 (dvdAbs, goalCL) hdd "j_mc" jbody;
              in Thm.implies_intr (ctermS2 (jT (dvd pF dW))) res end;
            val g = disjE_elimS2 (dvd pF aF, dvd pF dW, goalCL) eDisj caseA caseD;
          in g end;                                               (* jT (congL p X Y) *)
        val res = exE_elimS2 (leAbs, congL pF X Y) hle "d_mc" body;
      in res end;

    (* ---- deg_core : le X Y ==> oeq (a*X) ((a*Y) + p*k) ==> oeq X Y
            (the "wrong direction": smaller X has bigger multiple -> equality).
            Needs a = Suc a0 (passed in via aSuc on a0W). ---- *)
    fun deg_core (X, Y, kT) (a0W, aSuc) hle heqXY =
      let
        val leAbs = Abs("q", natT, oeq Y (add X (Bound 0)));
        fun body dW (hd : thm) =                                  (* hd : oeq Y (add X dW) *)
          let
            val mcong = mult_cong_rS (aF, Y, add X dW) hd;        (* a*Y = a*(X+d) *)
            val ld    = left_distrib_atS (aF, X, dW);             (* a*(X+d) = a*X + a*d *)
            val aYeq  = oeq_trans OF [mcong, ld];                 (* a*Y = a*X + a*d *)
            (* rewrite a*Y inside heqXY's RHS *)
            val rw1 = add_cong_lS (mult aF Y, add (mult aF X) (mult aF dW), mult pF kT) aYeq;
                                                                   (* (a*Y + p*k) = ((a*X+a*d) + p*k) *)
            val eq2 = oeq_trans OF [heqXY, rw1];                  (* a*X = ((a*X+a*d) + p*k) *)
            val assoc = addassocS_at (mult aF X, mult aF dW, mult pF kT);
                                                                   (* ((a*X+a*d)+p*k) = (a*X + (a*d+p*k)) *)
            val eq3 = oeq_trans OF [eq2, assoc];                  (* a*X = a*X + (a*d+p*k) *)
            val W   = add (mult aF dW) (mult pF kT);
            val lhs0 = add0rS_at (mult aF X);                     (* (a*X + 0) = a*X *)
            val eq4 = oeq_trans OF [lhs0, eq3];                   (* (a*X + 0) = (a*X + W) *)
            val zeroW = add_left_cancel_atS (mult aF X, ZeroC, W) eq4;  (* 0 = W *)
            val Weq0 = oeq_sym OF [zeroW];                        (* W = 0 ; i.e. (a*d + p*k) = 0 *)
            val aedW0 = add_eq_zero_left OF [Weq0];               (* a*d = 0 *)
            (* a = Suc a0 : (Suc a0)*d = d + a0*d ; a*d=0 -> d + a0*d = 0 -> d = 0 *)
            val c1 = mult_cong_lS (aF, suc a0W, dW) aSuc;         (* a*d = (Suc a0)*d *)
            val sucdW0 = oeq_trans OF [oeq_sym OF [c1], aedW0];   (* (Suc a0)*d = 0 *)
            val ms = mult_Suc_atS (a0W, dW);                      (* (Suc a0)*d = d + a0*d *)
            val sum0 = oeq_trans OF [oeq_sym OF [ms], sucdW0];    (* (d + a0*d) = 0 *)
            val dW0 = add_eq_zero_left OF [sum0];                 (* d = 0 *)
            (* Y = X + d, d = 0 -> Y = X *)
            val chain1 = oeq_trans OF [add_cong_rS (X, dW, ZeroC) dW0, add0rS_at X]; (* (X+d) = X *)
            val Yeqx = oeq_trans OF [hd, chain1];                 (* Y = X *)
          in oeq_sym OF [Yeqx] end;                               (* oeq X Y *)
        val res = exE_elimS2 (leAbs, oeq X Y) hle "d_dc" body;
      in res end;

    (* ---- cong_of_eq : oeq X Y ==> jT (cong p X Y)  (witness 0 on congL) ---- *)
    fun cong_of_eq (X, Y) hXY =
      let
        val m0 = mult0rS_at pF;                                   (* p*0 = 0 *)
        val acr = add_cong_rS (X, mult pF ZeroC, ZeroC) m0;       (* (X + p*0) = (X + 0) *)
        val a0r = add0rS_at X;                                    (* (X + 0) = X *)
        val xpx = oeq_trans OF [acr, a0r];                        (* (X + p*0) = X *)
        val x_xp0 = oeq_sym OF [xpx];                             (* X = (X + p*0) *)
        val Ybody = oeq_trans OF [oeq_sym OF [hXY], x_xp0];       (* Y = (X + p*0) *)
        val congLabs = Abs("k", natT, oeq Y (add X (mult pF (Bound 0))));
        val exL = exI_atS2 congLabs ZeroC Ybody;                 (* jT (congL p X Y) *)
      in disjI1S2_at (congL pF X Y, congR pF X Y) exL end;        (* jT (cong p X Y) *)

    (* ---- a = Suc a0 in scope, then case split ---- *)
    fun mainWithASuc a0W aSuc =
      let
        (* hypothesis cong p (a*b) (a*c) = Disj (congL ..)(congR ..) *)
        val dL = congL pF (mult aF bF) (mult aF cF);              (* Ex k. a*c = a*b + p*k *)
        val dR = congR pF (mult aF bF) (mult aF cF);              (* Ex k. a*b = a*c + p*k *)

        (* ===== CASE L : a*c = a*b + p*k ===== *)
        val caseL =
          let
            val hL = Thm.assume (ctermS2 (jT dL));
            val lAbs = Abs("k", natT, oeq (mult aF cF) (add (mult aF bF) (mult pF (Bound 0))));
            fun lbody kW (hk : thm) =          (* hk : a*c = a*b + p*k  (a*Y = a*X + p*k ; Y=c,X=b) *)
              let
                val lt = le_total_atS (bF, cF);                  (* Disj (le b c)(le c b) *)
                (* sub : le b c -> cancel_core(b,c) -> congL p b c -> cong via disjI1 *)
                val subBC =
                  let
                    val hbc = Thm.assume (ctermS2 (jT (le bF cF)));
                    val cl = cancel_core (bF, cF, kW) hbc hk;     (* jT (congL p b c) *)
                    val g  = disjI1S2_at (congL pF bF cF, congR pF bF cF) cl;
                  in Thm.implies_intr (ctermS2 (jT (le bF cF))) g end;
                (* sub : le c b -> deg_core(c,b) -> oeq c b -> oeq b c -> cong_of_eq *)
                val subCB =
                  let
                    val hcb = Thm.assume (ctermS2 (jT (le cF bF)));
                    val ecb = deg_core (cF, bF, kW) (a0W, aSuc) hcb hk;  (* oeq c b *)
                    val ebc = oeq_sym OF [ecb];                  (* oeq b c *)
                    val g   = cong_of_eq (bF, cF) ebc;           (* cong p b c *)
                  in Thm.implies_intr (ctermS2 (jT (le cF bF))) g end;
                val g = disjE_elimS2 (le bF cF, le cF bF, goalC) lt subBC subCB;
              in g end;
            val res = exE_elimS2 (lAbs, goalC) hL "kL_mc" lbody;
          in Thm.implies_intr (ctermS2 (jT dL)) res end;

        (* ===== CASE R : a*b = a*c + p*k ===== *)
        val caseR =
          let
            val hR = Thm.assume (ctermS2 (jT dR));
            val rAbs = Abs("k", natT, oeq (mult aF bF) (add (mult aF cF) (mult pF (Bound 0))));
            fun rbody kW (hk : thm) =          (* hk : a*b = a*c + p*k  (a*Y = a*X + p*k ; Y=b,X=c) *)
              let
                val lt = le_total_atS (cF, bF);                  (* Disj (le c b)(le b c) *)
                (* sub : le c b -> cancel_core(c,b) -> congL p c b = congR p b c -> disjI2 *)
                val subCB =
                  let
                    val hcb = Thm.assume (ctermS2 (jT (le cF bF)));
                    val cl = cancel_core (cF, bF, kW) hcb hk;     (* jT (congL p c b) = (Ex j. b = c + p*j) *)
                    val g  = disjI2S2_at (congL pF bF cF, congR pF bF cF) cl;
                  in Thm.implies_intr (ctermS2 (jT (le cF bF))) g end;
                (* sub : le b c -> deg_core(b,c) -> oeq b c -> cong_of_eq *)
                val subBC =
                  let
                    val hbc = Thm.assume (ctermS2 (jT (le bF cF)));
                    val ebc = deg_core (bF, cF, kW) (a0W, aSuc) hbc hk;  (* oeq b c *)
                    val g   = cong_of_eq (bF, cF) ebc;           (* cong p b c *)
                  in Thm.implies_intr (ctermS2 (jT (le bF cF))) g end;
                val g = disjE_elimS2 (le cF bF, le bF cF, goalC) lt subCB subBC;
              in g end;
            val res = exE_elimS2 (rAbs, goalC) hR "kR_mc" rbody;
          in Thm.implies_intr (ctermS2 (jT dR)) res end;

        val g = disjE_elimS2 (dL, dR, goalC) hCong caseL caseR;
      in g end;

    (* exE on a = Suc a0 *)
    val aSucAbs = Abs("m", natT, oeq aF (suc (Bound 0)));
    fun aSucBody a0W (haSuc : thm) = mainWithASuc a0W haSuc;
    val bodyGoal = exE_elimS2 (aSucAbs, goalC) aSucEx "a0_mc" aSucBody;

    (* discharge the three hypotheses *)
    val d1 = Thm.implies_intr (ctermS2 hCongP) bodyGoal;
    val d2 = Thm.implies_intr (ctermS2 hNdvdP) d1;
    val d3 = Thm.implies_intr (ctermS2 hPrimeP) d2;
  in varify d3 end;

val () = out "MOD_CANCEL_PROVED\n";

(* ---- validation : 0-hyp + aconv the TARGET ---- *)
val pVmc = Var (("p",0), natT);
val aVmc = Var (("a",0), natT);
val bVmc = Var (("b",0), natT);
val cVmc = Var (("c",0), natT);
val mod_cancel_intended =
  Logic.mk_implies (jT (prime2 pVmc),
    Logic.mk_implies (jT (neg (dvd pVmc aVmc)),
      Logic.mk_implies (jT (cong pVmc (mult aVmc bVmc) (mult aVmc cVmc)),
        jT (cong pVmc bVmc cVmc))));
val r_mc =
  let
    val nh = length (Thm.hyps_of mod_cancel);
    val ac = (Thm.prop_of mod_cancel) aconv mod_cancel_intended;
  in
    if nh = 0 andalso ac then (out "OK mod_cancel\n"; true)
    else (out ("FAIL mod_cancel (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtS2 (Thm.prop_of mod_cancel) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtS2 mod_cancel_intended ^ "\n");
          false)
  end;

(* ---- soundness probe : dropping ~(p|a) must NOT be provable
        (p=2, a=2 : cong 2 (2*1) (2*0) i.e. cong 2 2 0 holds, but cong 2 1 0 false). *)
val probe_mc_needs_ndvd =
  let
    val bogus = Logic.mk_implies (jT (prime2 pVmc),
                  Logic.mk_implies (jT (cong pVmc (mult aVmc bVmc) (mult aVmc cVmc)),
                    jT (cong pVmc bVmc cVmc)));   (* drops ~(p|a) *)
  in not ((Thm.prop_of mod_cancel) aconv bogus) end;
val probe_mc_nontrivial =
  not ((Thm.prop_of mod_cancel) aconv (jT (cong pVmc bVmc cVmc)));

val () =
  if r_mc andalso probe_mc_needs_ndvd andalso probe_mc_nontrivial
  then out "PROBE_OK mod_cancel is conditional on ~(p|a) / nontrivial\n"
  else out "PROBE_UNSOUND mod_cancel collapsed!\n";

val () =
  if r_mc andalso probe_mc_needs_ndvd andalso probe_mc_nontrivial
  then out "MOD_CANCEL_OK\n"
  else out "MOD_CANCEL_FAILED\n";

(* ============================================================================
   ==============  lagrange_roots  (verbatim from mult_group.sml)  ============
   ============================================================================ *)
val () = out "LAGRANGE_ROOTS_BEGIN\n";

(* ---- extra instantiators on ctxtS2 ---- *)
val Suc_inj_vS2          = varify Suc_inj_ax;            (* oeq (Suc ?a)(Suc ?b) ==> oeq ?a ?b *)
fun Suc_inj_atS (ut, vt) h = Thm.implies_elim
      (beta_norm (Drule.infer_instantiate ctxtS2
        [(("a",0), ctermS2 ut), (("b",0), ctermS2 vt)] Suc_inj_vS2)) h;
val add_eq_zero_left_vS  = varify add_eq_zero_left;      (* oeq (add ?a ?b) Zero ==> oeq ?a Zero *)
fun add_eq_zero_left_atS (at, bt) h = Thm.implies_elim
      (beta_norm (Drule.infer_instantiate ctxtS2
        [(("a",0), ctermS2 at), (("b",0), ctermS2 bt)] add_eq_zero_left_vS)) h;

(* mult left-zero on ctxtS2 : oeq (mult 0 n) 0 *)
val mult_0_vS2 = varify mult_0;
fun mult0lS_at t = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] mult_0_vS2);

(* euclid_lemma on ctxtS2 : prime2 p -> dvd p (mult a b) -> Disj (dvd p a)(dvd p b) *)
val euclid_lemma_vS2 = varify euclid_lemma;
fun euclid_atS (pt, at, bt) hPrime hDvd =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("p",0), ctermS2 pt), (("a",0), ctermS2 at), (("b",0), ctermS2 bt)] euclid_lemma_vS2);
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hDvd end;

(* prime_not_dvd_pos_lt on ctxtS2 : dvd p r -> lt 0 r -> lt r p -> oFalse *)
val prime_not_dvd_pos_lt_vS2 = varify prime_not_dvd_pos_lt;
fun prime_not_dvd_pos_lt_atS (pt, rt) hDvd hPos hLt =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("p",0), ctermS2 pt), (("r",0), ctermS2 rt)] prime_not_dvd_pos_lt_vS2);
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hDvd) hPos) hLt end;

val () = out "LR_HELPERS_READY\n";

val lagrange_roots =
  let
    val pF = Free("p", natT);
    val aF = Free("a", natT);
    val hPrimeP = jT (prime2 pF);
    val hPrime  = Thm.assume (ctermS2 hPrimeP);
    val hCongP  = jT (cong pF (mult aF aF) oneC);
    val hCong   = Thm.assume (ctermS2 hCongP);

    (* the final goal disjunction *)
    val goalC = mkDisj (cong pF aF oneC) (cong pF (suc aF) ZeroC);

    (* num-cases on a : Disj (oeq a 0) (Ex q. oeq a (Suc q)) *)
    val dz = dzosS_at aF;

    (* ===================== CASE a = 0 ===================== *)
    val caseZero =
      let
        val ha0 = Thm.assume (ctermS2 (jT (oeq aF ZeroC)));    (* a = 0 *)
        (* From hCong : Disj (congL p (a*a) 1)(congR p (a*a) 1).  We derive oFalse,
           then oFalse_elim into goalC.  Both disjuncts of cong are contradictory.
           congL : Ex k. 1 = (a*a) + p*k  -> p|1 -> prime contra
           congR : Ex k. (a*a) = 1 + p*k  -> rewrite a*a -> 0 (since a=0); but
                   0 = 1 + p*k = Suc(p*k) -> Suc_neq_Zero contra.  *)
        val aa_0a = mult_cong_lS (aF, ZeroC, aF) ha0;          (* a*a = 0*a *)
        val z0a   = mult0lS_at aF;                             (* 0*a = 0 *)
        val aa0   = oeq_trans OF [aa_0a, z0a];                 (* a*a = 0 *)

        val LcongL = congL pF (mult aF aF) oneC;
        val LcongR = congR pF (mult aF aF) oneC;

        (* congL case : Ex k. oeq 1 (add (a*a) (mult p k)) *)
        val caseL =
          let
            val PabsL = Abs("k", natT, oeq oneC (add (mult aF aF) (mult pF (Bound 0))));
            fun bodyL kW (hk : thm) =                          (* hk : 1 = (a*a) + p*k *)
              let
                (* rewrite a*a -> 0 : (a*a) + p*k = 0 + p*k = p*k *)
                val r1 = add_cong_lS (mult aF aF, ZeroC, mult pF kW) aa0;  (* (a*a + p*k) = (0 + p*k) *)
                val r2 = add0S_at (mult pF kW);                (* (0 + p*k) = p*k *)
                val one_pk = oeq_trans OF [oeq_trans OF [hk, r1], r2];  (* 1 = p*k *)
                (* dvd p 1 : oeq 1 (mult p k) is exactly one_pk *)
                val dvdp1 = dvd_introS (pF, oneC, kW) one_pk;  (* dvd p 1 *)
                (* lt 0 1 = le (Suc 0) 1 = le 1 1 ; witness 0 : oeq 1 (add 1 0) *)
                val lt01 =
                  let val h = oeq_sym OF [add0rS_at oneC]       (* oeq 1 (add 1 0) *)
                  in le_introS (oneC, oneC, ZeroC) h end;       (* le 1 1 = lt 0 1 *)
                val lt1p  = prime2_gt1_atS pF hPrime;           (* lt 1 p *)
                val fls   = prime_not_dvd_pos_lt_atS (pF, oneC) dvdp1 lt01 lt1p;  (* oFalse *)
              in Thm.implies_elim (oFalse_elimS_at goalC) fls end;  (* goalC *)
            val resL = exE_elimS2 (PabsL, goalC) (Thm.assume (ctermS2 (jT LcongL))) "kL_lr" bodyL;
          in Thm.implies_intr (ctermS2 (jT LcongL)) resL end;

        (* congR case : Ex k. oeq (a*a) (add 1 (mult p k)) *)
        val caseR =
          let
            val PabsR = Abs("k", natT, oeq (mult aF aF) (add oneC (mult pF (Bound 0))));
            fun bodyR kW (hk : thm) =                          (* hk : (a*a) = 1 + p*k *)
              let
                (* a*a = 0 (aa0) and a*a = 1 + p*k -> 0 = 1 + p*k *)
                val z_1pk = oeq_trans OF [oeq_sym OF [aa0], hk];   (* 0 = 1 + p*k *)
                (* 1 + p*k = Suc 0 + p*k = Suc(0 + p*k) = Suc(p*k) *)
                val s1 = addSucS_at (ZeroC, mult pF kW);       (* (Suc 0 + p*k) = Suc(0 + p*k) *)
                val s2 = Suc_cong OF [add0S_at (mult pF kW)];  (* Suc(0 + p*k) = Suc(p*k) *)
                val onepk_suc = oeq_trans OF [s1, s2];         (* (1 + p*k) = Suc(p*k) *)
                val z_suc = oeq_trans OF [z_1pk, onepk_suc];   (* 0 = Suc(p*k) *)
                val suc_z = oeq_sym OF [z_suc];                (* Suc(p*k) = 0 *)
                val fls   = (Suc_neq_Zero_atS (mult pF kW)) OF [suc_z];  (* oFalse *)
              in Thm.implies_elim (oFalse_elimS_at goalC) fls end;
            val resR = exE_elimS2 (PabsR, goalC) (Thm.assume (ctermS2 (jT LcongR))) "kR_lr" bodyR;
          in Thm.implies_intr (ctermS2 (jT LcongR)) resR end;

        val res = disjE_elimS2 (LcongL, LcongR, goalC) hCong caseL caseR;
      in Thm.implies_intr (ctermS2 (jT (oeq aF ZeroC))) res end;

    (* ===================== CASE a = Suc a0 ===================== *)
    val PabsSuc = Abs("q", natT, oeq aF (suc (Bound 0)));
    fun caseSucBody a0 (ha : thm) =                            (* ha : a = Suc a0 *)
      let
        val M  = mult a0 aF;                                   (* a0 * a *)
        val T  = add a0 M;                                     (* a0 + a0*a *)
        val xT = mult a0 (suc aF);                             (* a0 * (Suc a) = the witness x *)

        (* ---- key identity : oeq (mult a a) (add xT 1) ---- *)
        (* LHS chain : mult a a -> Suc T *)
        val L1 = mult_cong_lS (aF, suc a0, aF) ha;             (* a*a = (Suc a0)*a *)
        val L2 = mult_Suc_atS (a0, aF);                        (* (Suc a0)*a = add a (a0*a) *)
        val L3 = add_cong_lS (aF, suc a0, M) ha;               (* (a + a0*a) = (Suc a0 + a0*a) *)
        val L4 = addSucS_at (a0, M);                           (* (Suc a0 + a0*a) = Suc(a0 + a0*a) = Suc T *)
        val LHS = oeq_trans OF [oeq_trans OF [oeq_trans OF [L1, L2], L3], L4];  (* a*a = Suc T *)
        (* RHS chain : add xT 1 -> Suc T *)
        val R0 = multSrS_at (a0, aF);                          (* a0*(Suc a) = add a0 (a0*a) = T *)
        val R1 = add_cong_lS (xT, T, oneC) R0;                 (* (xT + 1) = (T + 1) *)
        val R2 = addSrS_at (T, ZeroC);                         (* (T + Suc 0) = Suc(T + 0) *)
        val R3 = Suc_cong OF [add0rS_at T];                    (* Suc(T + 0) = Suc T *)
        val RHS = oeq_trans OF [oeq_trans OF [R1, R2], R3];    (* (xT + 1) = Suc T *)
        val idEq = oeq_trans OF [LHS, oeq_sym OF [RHS]];       (* a*a = add xT 1 *)

        (* ---- derive  dvd p xT  from hCong + idEq ---- *)
        val LcongL = congL pF (mult aF aF) oneC;
        val LcongR = congR pF (mult aF aF) oneC;

        (* congL : Ex k. oeq 1 (add (a*a) (mult p k))  ->  rewrite a*a->xT+1 ->
           1 = (xT+1)+p*k = Suc(xT+p*k) -> Suc_inj -> 0 = xT+p*k -> xT=0 -> dvd p 0 -> dvd p xT *)
        val dvdL =
          let
            val PabsL = Abs("k", natT, oeq oneC (add (mult aF aF) (mult pF (Bound 0))));
            fun bodyL kW (hk : thm) =                          (* hk : 1 = (a*a) + p*k *)
              let
                (* rewrite a*a -> xT+1 in (a*a)+p*k *)
                val rw  = add_cong_lS (mult aF aF, add xT oneC, mult pF kW) idEq;  (* ((a*a)+p*k) = ((xT+1)+p*k) *)
                val one_eq = oeq_trans OF [hk, rw];            (* 1 = (xT+1)+p*k *)
                (* (xT+1)+p*k = Suc(xT) + p*k = Suc(xT + p*k) *)
                val e1 = add_cong_lS (add xT oneC, suc xT, mult pF kW)
                           (let val a1 = addSrS_at (xT, ZeroC)        (* (xT + Suc 0) = Suc(xT+0) *)
                                val a2 = Suc_cong OF [add0rS_at xT]    (* Suc(xT+0) = Suc xT *)
                            in oeq_trans OF [a1, a2] end);     (* (xT+1) = Suc xT *)
                                                               (* ((xT+1)+p*k) = (Suc xT + p*k) *)
                val e2 = addSucS_at (xT, mult pF kW);          (* (Suc xT + p*k) = Suc(xT + p*k) *)
                val one_suc = oeq_trans OF [oeq_trans OF [one_eq, e1], e2];  (* 1 = Suc(xT+p*k) *)
                (* 1 = Suc 0, so Suc 0 = Suc(xT+p*k) -> Suc_inj -> 0 = xT+p*k *)
                val suc_eq = one_suc;                          (* oeq (Suc 0) (Suc (xT+p*k)) *)
                val zero_eq = Suc_inj_atS (ZeroC, add xT (mult pF kW)) suc_eq;  (* 0 = xT+p*k *)
                val sum_zero = oeq_sym OF [zero_eq];           (* (xT+p*k) = 0 *)
                val xT_zero = add_eq_zero_left_atS (xT, mult pF kW) sum_zero;   (* xT = 0 *)
                (* dvd p 0, then rewrite 0->xT : dvd p xT.  dvd_cong_rS needs oeq 0 xT. *)
                val dvdp0 = dvd_zeroS_at pF;                   (* dvd p 0 *)
                val zero_xT = oeq_sym OF [xT_zero];            (* 0 = xT *)
                val dvdpxT = dvd_cong_rS (pF, ZeroC, xT) zero_xT dvdp0;  (* dvd p xT *)
              in dvdpxT end;
            val r = exE_elimS2 (PabsL, dvd pF xT) (Thm.assume (ctermS2 (jT LcongL))) "kL2_lr" bodyL;
          in Thm.implies_intr (ctermS2 (jT LcongL)) r end;

        (* congR : Ex k. oeq (a*a) (add 1 (mult p k)) -> rewrite a*a->xT+1 ->
           (xT+1) = 1 + p*k = Suc(p*k); also xT+1 = Suc xT -> Suc xT = Suc(p*k) -> xT = p*k -> dvd p xT *)
        val dvdR =
          let
            val PabsR = Abs("k", natT, oeq (mult aF aF) (add oneC (mult pF (Bound 0))));
            fun bodyR kW (hk : thm) =                          (* hk : (a*a) = 1 + p*k *)
              let
                val lhs_eq = oeq_trans OF [oeq_sym OF [idEq], hk];   (* (xT+1) = 1 + p*k *)
                (* xT+1 = Suc xT *)
                val xT1_suc = let val a1 = addSrS_at (xT, ZeroC)
                                  val a2 = Suc_cong OF [add0rS_at xT]
                              in oeq_trans OF [a1, a2] end;     (* (xT+1) = Suc xT *)
                (* 1 + p*k = Suc 0 + p*k = Suc(0+p*k) = Suc(p*k) *)
                val rhs_suc = let val b1 = addSucS_at (ZeroC, mult pF kW)
                                  val b2 = Suc_cong OF [add0S_at (mult pF kW)]
                              in oeq_trans OF [b1, b2] end;     (* (1 + p*k) = Suc(p*k) *)
                (* Suc xT = (xT+1) = (1+p*k) = Suc(p*k) *)
                val suc_eq = oeq_trans OF [oeq_trans OF [oeq_sym OF [xT1_suc], lhs_eq], rhs_suc];  (* Suc xT = Suc(p*k) *)
                val xT_pk = Suc_inj_atS (xT, mult pF kW) suc_eq;  (* xT = p*k *)
                val dvdpxT = dvd_introS (pF, xT, kW) xT_pk;     (* dvd p xT *)
              in dvdpxT end;
            val r = exE_elimS2 (PabsR, dvd pF xT) (Thm.assume (ctermS2 (jT LcongR))) "kR2_lr" bodyR;
          in Thm.implies_intr (ctermS2 (jT LcongR)) r end;

        val dvdpxT = disjE_elimS2 (LcongL, LcongR, dvd pF xT) hCong dvdL dvdR;  (* dvd p xT *)

        (* ---- euclid_lemma : dvd p (mult a0 (Suc a)) -> Disj (dvd p a0)(dvd p (Suc a)) ---- *)
        val euDisj = euclid_atS (pF, a0, suc aF) hPrime dvdpxT;   (* Disj (dvd p a0)(dvd p (Suc a)) *)

        (* CASE p|a0 : a0 = p*j -> a = Suc a0 = Suc(p*j) = 1 + p*j -> cong p a 1 (congR) -> disjI1 goalC *)
        val caseDA0 =
          let
            val hda0 = Thm.assume (ctermS2 (jT (dvd pF a0)));    (* dvd p a0 = Ex k. a0 = p*k *)
            val Pdvd = Abs("k", natT, oeq a0 (mult pF (Bound 0)));
            fun body jW (hj : thm) =                             (* hj : a0 = p*j *)
              let
                (* a = Suc a0 = Suc(p*j) ; 1 + p*j = Suc(p*j) ; so a = 1 + p*j *)
                val a_suc_pj = oeq_trans OF [ha, Suc_cong OF [hj]];  (* a = Suc(p*j) *)
                val onepj_suc = let val b1 = addSucS_at (ZeroC, mult pF jW)
                                    val b2 = Suc_cong OF [add0S_at (mult pF jW)]
                                in oeq_trans OF [b1, b2] end;    (* (1 + p*j) = Suc(p*j) *)
                val a_eq = oeq_trans OF [a_suc_pj, oeq_sym OF [onepj_suc]];  (* a = (1 + p*j) *)
                (* congR p a 1 : Ex k. oeq a (add 1 (mult p k)), witness j *)
                val congRabs = Abs("k", natT, oeq aF (add oneC (mult pF (Bound 0))));
                val exC = exI_atS2 congRabs jW a_eq;             (* congR p a 1 *)
                val hcong = disjI2S2_at (congL pF aF oneC, congR pF aF oneC) exC;  (* cong p a 1 *)
              in disjI1S2_at (cong pF aF oneC, cong pF (suc aF) ZeroC) hcong end;  (* goalC *)
            val r = exE_elimS2 (Pdvd, goalC) hda0 "j0_lr" body;
          in Thm.implies_intr (ctermS2 (jT (dvd pF a0))) r end;

        (* CASE p|(Suc a) : Suc a = p*j -> cong p (Suc a) 0 (congR, b:=0) -> disjI2 goalC *)
        val caseDSa =
          let
            val hdSa = Thm.assume (ctermS2 (jT (dvd pF (suc aF))));  (* dvd p (Suc a) = Ex k. Suc a = p*k *)
            val Pdvd = Abs("k", natT, oeq (suc aF) (mult pF (Bound 0)));
            fun body jW (hj : thm) =                             (* hj : Suc a = p*j *)
              let
                (* Suc a = p*j ; 0 + p*j = p*j ; so Suc a = 0 + p*j *)
                val z_pj = oeq_sym OF [add0S_at (mult pF jW)];   (* p*j = 0 + p*j *)
                val Sa_eq = oeq_trans OF [hj, z_pj];             (* Suc a = 0 + p*j *)
                (* congR p (Suc a) 0 : Ex k. oeq (Suc a) (add 0 (mult p k)), witness j *)
                val congRabs = Abs("k", natT, oeq (suc aF) (add ZeroC (mult pF (Bound 0))));
                val exC = exI_atS2 congRabs jW Sa_eq;            (* congR p (Suc a) 0 *)
                val hcong = disjI2S2_at (congL pF (suc aF) ZeroC, congR pF (suc aF) ZeroC) exC;  (* cong p (Suc a) 0 *)
              in disjI2S2_at (cong pF aF oneC, cong pF (suc aF) ZeroC) hcong end;  (* goalC *)
            val r = exE_elimS2 (Pdvd, goalC) hdSa "jS_lr" body;
          in Thm.implies_intr (ctermS2 (jT (dvd pF (suc aF)))) r end;

        val res = disjE_elimS2 (dvd pF a0, dvd pF (suc aF), goalC) euDisj caseDA0 caseDSa;
      in res end;
    val caseSuc =
      let
        val r = exE_elimS2 (PabsSuc, goalC) (Thm.assume (ctermS2 (jT (mkEx PabsSuc)))) "a0_lr" caseSucBody;
      in Thm.implies_intr (ctermS2 (jT (mkEx PabsSuc))) r end;

    val concl = disjE_elimS2 (oeq aF ZeroC, mkEx PabsSuc, goalC) dz caseZero caseSuc;  (* goalC *)
    val disch1 = Thm.implies_intr (ctermS2 hCongP) concl;
    val disch2 = Thm.implies_intr (ctermS2 hPrimeP) disch1;
  in varify disch2 end;

val () = out "LAGRANGE_ROOTS_PROVED\n";

(* ---- validation ---- *)
val pVlr = Var (("p",0), natT);
val aVlr = Var (("a",0), natT);
val lagrange_roots_intended =
  Logic.mk_implies (jT (prime2 pVlr),
    Logic.mk_implies (jT (cong pVlr (mult aVlr aVlr) oneC),
      jT (mkDisj (cong pVlr aVlr oneC) (cong pVlr (suc aVlr) ZeroC))));
val r_lr = checkS2 ("lagrange_roots", lagrange_roots, lagrange_roots_intended);
val () = if r_lr then out "OK lagrange_roots\n" else out "FAIL lagrange_roots\n";

(* ---- soundness probes ---- *)
(* (1) dropping prime2 p must NOT be provable (kernel must still need it) *)
val probe_drop_prime =
  let val bogus = Logic.mk_implies (jT (cong pVlr (mult aVlr aVlr) oneC),
                    jT (mkDisj (cong pVlr aVlr oneC) (cong pVlr (suc aVlr) ZeroC)))
  in not ((Thm.prop_of lagrange_roots) aconv bogus) end;
(* (2) dropping one disjunct (keeping only x==1) must NOT match *)
val probe_drop_disj =
  let val bogus = Logic.mk_implies (jT (prime2 pVlr),
                    Logic.mk_implies (jT (cong pVlr (mult aVlr aVlr) oneC),
                      jT (cong pVlr aVlr oneC)))
  in not ((Thm.prop_of lagrange_roots) aconv bogus) end;

val () =
  if probe_drop_prime andalso probe_drop_disj
  then out "PROBE_OK lagrange_roots conditional on prime / two-sided\n"
  else out "PROBE_UNSOUND lagrange_roots collapsed!\n";

val () =
  if r_lr andalso probe_drop_prime andalso probe_drop_disj
  then out "LAGRANGE_ROOTS_OK\n"
  else out "LAGRANGE_ROOTS_FAILED\n";


(* ============================================================================
   ====================  apm1 : FERMAT FOR UNITS  =============================
     apm1 : prime2 p ==> ~(p|a) ==> cong p (pow a (sub p 1)) 1
   Derivation (on ctxtSub):
     flt           : cong p (pow a p) a
     p = Suc p0    (prime2 => p>1 => p<>0)
     sub p 1 = p0  [subSSS2_at, subN0S2_at]
     pow a p = pow a (Suc p0) = mult a (pow a p0) = mult a (pow a (sub p 1))   [pow_Suc]
     => cong p (mult a (pow a (sub p 1))) a
     a = mult a 1  [mult_1_right sym]  => cong p (mult a (pow a (sub p 1))) (mult a 1)
     mod_cancel    : cancel the (unit) a  => cong p (pow a (sub p 1)) 1
   ============================================================================ *)

val () = out "APM1_BEGIN\n";

(* flt / mod_cancel re-varified for use on ctxtSub *)
val flt_vSub        = varify flt;
val mod_cancel_vSub = varify mod_cancel;

(* flt at (p,a) on ctxtSub : prime2 p ==> jT (cong p (pow a p) a) *)
fun flt_atSub (pT, aT) hPrime =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("p",0), ctermSub pT), (("a",0), ctermSub aT)] flt_vSub)
  in Thm.implies_elim inst hPrime end;

(* mod_cancel at (p,a,b,c) on ctxtSub :
     prime2 p ==> ~(p|a) ==> cong p (a*b)(a*c) ==> cong p b c *)
fun mod_cancel_atSub (pT, aT, bT, cT) hPrime hNdvd hCong =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("p",0), ctermSub pT), (("a",0), ctermSub aT),
         (("b",0), ctermSub bT), (("c",0), ctermSub cT)] mod_cancel_vSub)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hPrime) hNdvd) hCong end;

(* oeq -> cong on ctxtSub : oeq X Y ==> jT (cong p X Y)
   via cong_refl p X then substPredS2 rewriting the SECOND cong argument X->Y. *)
fun oeq_to_congSub (pT, X, Y) hXY =
  let
    val crefl = cong_refl_atSub (pT, X);                       (* cong p X X *)
    val zF = Free("z_otc", natT);
    val Pz = Term.lambda zF (cong pT X zF);                    (* %z. cong p X z *)
  in substPredS2 (Pz, X, Y) hXY crefl end;                    (* cong p X Y *)

(* ctxtSub versions of oFalse_elim / disjE for goals that mention pow/sub
   (the nt_helpers oFalse_elimS_at / disjE_elimS2 certify on ctxtS2, which does
    NOT know pow/sub -> "Unknown constant pow"; rebuild them on ctxtSub). *)
fun oFalse_elimSub_at rT = beta_norm (Drule.infer_instantiate ctxtSub
      [(("R",0), ctermSub rT)] (varify oFalse_elim_ax));
fun disjE_elimSub (At, Bt, Ct) dThm caseA caseB =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("A",0), ctermSub At), (("B",0), ctermSub Bt), (("C",0), ctermSub Ct)]
          (varify disjE_ax));
    val s1 = Thm.implies_elim inst dThm;
    val s2 = Thm.implies_elim s1 caseA;
  in Thm.implies_elim s2 caseB end;

val apm1 =
  let
    val pF = Free("p", natT);
    val aF = Free("a", natT);
    val hPrimeP = jT (prime2 pF);          val hPrime = Thm.assume (ctermSub hPrimeP);
    val hNdvdP  = jT (neg (dvd pF aF));     val hNdvd  = Thm.assume (ctermSub hNdvdP);

    val goalC = cong pF (pow aF (sub pF oneC)) oneC;           (* cong p (pow a (sub p 1)) 1 *)

    (* ---- p <> 0 from prime2 (1 < p) : p = Suc p0 ---- *)
    val gt1 = prime2_gt1_atS pF hPrime;                        (* lt (Suc 0) p = le (Suc(Suc 0)) p *)
    (* num-cases on p; the p=0 branch contradicts gt1 *)
    val dz = dzosS_at pF;                                      (* Disj (oeq p 0)(Ex q. oeq p (Suc q)) *)

    val caseZero =
      let
        val hp0 = Thm.assume (ctermSub (jT (oeq pF ZeroC)));   (* p = 0 *)
        (* gt1 : le (Suc(Suc 0)) p ; rewrite p->0 : le (Suc(Suc 0)) 0 = Ex x. 0 = (Suc(Suc 0)) + x *)
        val twoT = suc (suc ZeroC);
        val leAbs = Abs("x", natT, oeq ZeroC (add twoT (Bound 0)));
        (* rewrite gt1's bound p to 0 : substPred on %z. le (Suc(Suc 0)) z *)
        val zF = Free("z_le", natT);
        val Pz = Term.lambda zF (le twoT zF);                  (* %z. le 2 z *)
        val gt1_0 = substPredS2 (Pz, pF, ZeroC) hp0 gt1;       (* le 2 0 = Ex x. 0 = 2 + x *)
        fun body xW (hx : thm) =                               (* hx : 0 = 2 + x *)
          let
            (* 2 + x = Suc(1 + x) = Suc(Suc(0+x)) -> Suc(...) ; 0 = Suc(...) contra *)
            val s1 = addSucS_at (suc ZeroC, xW);               (* (Suc 1 + x) = Suc(1 + x) ; (Suc(Suc 0))+x = Suc((Suc 0)+x) *)
            val z_suc = oeq_trans OF [hx, s1];                 (* 0 = Suc((Suc 0) + x) *)
            val suc_z = oeq_sym OF [z_suc];                    (* Suc((Suc 0)+x) = 0 *)
            val fls = (Suc_neq_Zero_atS (add (suc ZeroC) xW)) OF [suc_z];  (* oFalse *)
          in Thm.implies_elim (oFalse_elimSub_at goalC) fls end;
        val res = exE_elimS2 (leAbs, goalC) gt1_0 "x_p0" body;
      in Thm.implies_intr (ctermSub (jT (oeq pF ZeroC))) res end;

    (* ---- main case : p = Suc p0 ---- *)
    val PabsSuc = Abs("q", natT, oeq pF (suc (Bound 0)));
    fun caseSucBody p0 (hp : thm) =                            (* hp : p = Suc p0 *)
      let
        (* sub p 1 = sub (Suc p0)(Suc 0) = sub p0 0 = p0 *)
        (* first rewrite sub p 1 -> sub (Suc p0) 1 via hp *)
        val e_sub1 =
          let
            val zF = Free("z_s1", natT);
            val Pz = Term.lambda zF (oeq (sub zF oneC) (sub (suc p0) oneC))
          in (* build oeq (sub p 1)(sub (Suc p0) 1) by subst p->Suc p0 into reflexivity *)
            substPredS2 (Pz, suc p0, pF) (oeq_sym OF [hp]) (oeqreflS2_at (sub (suc p0) oneC))
          end;                                                 (* oeq (sub p 1)(sub (Suc p0) 1) *)
        val e_ss  = subSSS2_at (p0, ZeroC);                    (* oeq (sub (Suc p0)(Suc 0))(sub p0 0) *)
        val e_n0  = subN0S2_at p0;                             (* oeq (sub p0 0) p0 *)
        val sub_p1_p0 = oeq_trans OF [oeq_trans OF [e_sub1, e_ss], e_n0];  (* oeq (sub p 1) p0 *)

        (* pow a p = pow a (Suc p0) [hp] = mult a (pow a p0) [pow_Suc] *)
        (* rewrite pow a p -> pow a (Suc p0) via hp on %z. oeq (pow a z)(mult a (pow a (sub p 1))) ?
           build directly: oeq (pow a p)(mult a (pow a (sub p 1))) *)
        val pow_p_eq =
          let
            (* pow a p = pow a (Suc p0) *)
            val zF = Free("z_pp", natT);
            val Pz1 = Term.lambda zF (oeq (pow aF pF) (pow aF zF))
            val powp_powSp0 = substPredS2 (Pz1, pF, suc p0) hp (oeqreflS2_at (pow aF pF));
                                                               (* oeq (pow a p)(pow a (Suc p0)) *)
            val psuc = powSucS2_at (aF, p0);                   (* oeq (pow a (Suc p0))(mult a (pow a p0)) *)
            (* mult a (pow a p0) = mult a (pow a (sub p 1))  [rewrite p0 <- sub p 1] *)
            val zF2 = Free("z_mp", natT);
            val Pz2 = Term.lambda zF2 (oeq (mult aF (pow aF p0)) (mult aF (pow aF zF2)))
            val mp_eq = substPredS2 (Pz2, p0, sub pF oneC) (oeq_sym OF [sub_p1_p0])
                          (oeqreflS2_at (mult aF (pow aF p0)));
                                                               (* oeq (mult a (pow a p0))(mult a (pow a (sub p 1))) *)
          in oeq_trans OF [oeq_trans OF [powp_powSp0, psuc], mp_eq] end;
                                                               (* oeq (pow a p)(mult a (pow a (sub p 1))) *)

        (* flt : cong p (pow a p) a ; rewrite first arg pow a p -> mult a (pow a (sub p 1)) *)
        val flt0 = flt_atSub (pF, aF) hPrime;                  (* cong p (pow a p) a *)
        val cong_left =                                        (* cong p (mult a (pow a (sub p 1))) a *)
          let
            val zF = Free("z_cl", natT);
            val Pz = Term.lambda zF (cong pF zF aF);           (* %z. cong p z a *)
          in substPredS2 (Pz, pow aF pF, mult aF (pow aF (sub pF oneC))) pow_p_eq flt0 end;

        (* a = mult a 1 : oeq a (mult a (Suc 0)) ; rewrite RHS a -> mult a 1 *)
        val a_eq_a1 = oeq_sym OF [mult_1_right_atSub aF];      (* oeq a (mult a (Suc 0)) *)
        val cong_both =                                        (* cong p (mult a (pow a (sub p 1)))(mult a 1) *)
          let
            val zF = Free("z_cb", natT);
            val Pz = Term.lambda zF (cong pF (mult aF (pow aF (sub pF oneC))) zF);  (* %z. cong p (a*b) z *)
          in substPredS2 (Pz, aF, mult aF oneC) a_eq_a1 cong_left end;

        (* mod_cancel : cong p (a*b)(a*1) ==> cong p b 1  (b = pow a (sub p 1), c = 1) *)
        val res = mod_cancel_atSub (pF, aF, pow aF (sub pF oneC), oneC) hPrime hNdvd cong_both;
                                                               (* cong p (pow a (sub p 1)) 1 *)
      in res end;

    val caseSuc =
      let
        val r = exE_elimS2 (PabsSuc, goalC) (Thm.assume (ctermSub (jT (mkEx PabsSuc)))) "p0_apm1" caseSucBody;
      in Thm.implies_intr (ctermSub (jT (mkEx PabsSuc))) r end;

    val concl = disjE_elimSub (oeq pF ZeroC, mkEx PabsSuc, goalC) dz caseZero caseSuc;  (* goalC *)
    val d1 = Thm.implies_intr (ctermSub hNdvdP) concl;
    val d2 = Thm.implies_intr (ctermSub hPrimeP) d1;
  in varify d2 end;

val () = out "APM1_PROVED\n";

(* ---- validation : 0-hyp + aconv intended ---- *)
val pVa = Var (("p",0), natT);
val aVa = Var (("a",0), natT);
val apm1_intended =
  Logic.mk_implies (jT (prime2 pVa),
    Logic.mk_implies (jT (neg (dvd pVa aVa)),
      jT (cong pVa (pow aVa (sub pVa oneC)) oneC)));
val r_apm1 =
  let
    val nh = length (Thm.hyps_of apm1);
    val ac = (Thm.prop_of apm1) aconv apm1_intended;
  in
    if nh = 0 andalso ac then (out "OK apm1\n"; true)
    else (out ("FAIL apm1 (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtSub (Thm.prop_of apm1) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtSub apm1_intended ^ "\n");
          false)
  end;

(* soundness probes : apm1 must keep BOTH premises *)
val probe_apm1_needs_prime =
  not ((Thm.prop_of apm1) aconv
       (Logic.mk_implies (jT (neg (dvd pVa aVa)),
          jT (cong pVa (pow aVa (sub pVa oneC)) oneC))));
val probe_apm1_needs_ndvd =
  not ((Thm.prop_of apm1) aconv
       (Logic.mk_implies (jT (prime2 pVa),
          jT (cong pVa (pow aVa (sub pVa oneC)) oneC))));
val () =
  if r_apm1 andalso probe_apm1_needs_prime andalso probe_apm1_needs_ndvd
  then out "APM1_OK\n" else out "APM1_FAILED\n";

(* ============================================================================
   BASE READY : apm1 (Fermat-for-units) + lagrange_roots + mod_cancel together,
   all over ctxtSub, with pow/cong/sub algebra in scope.
   ============================================================================ *)
val () =
  if r_apm1 andalso r_lr andalso r_mc
     andalso probe_apm1_needs_prime andalso probe_apm1_needs_ndvd
  then out "BASE_OK\n"
  else out "BASE_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  EULER'S CRITERION  ***
   For an ODD prime p = 2m+1 and a with NOT(p|a):
     a^m == 1 (mod p)  if a is a QR mod p,  == -1 (mod p) otherwise,
   where m = (p-1)/2.  We carry the oddness as the hypothesis
     oeq (sub p 1) (add m m)     [i.e. p-1 = 2m]
   so the exponent m is exact (no division).  -1 mod p is the lagrange form
     cong p (Suc (pow a m)) 0    [ Suc y == 0, i.e. y == p-1 == -1 ].
   Everything is built on ctxtSub (the FINAL context: knows pow + sub + cong).
   ============================================================================ *)
val () = out "EULERCRIT_DELTA_BEGIN\n";

(* ---------------------------------------------------------------------------
   Extra accessors on ctxtSub for the pow algebra we reuse here.
   pow_add / pow_mult_base / cong_pow were varified context-free (pow_add_vP
   etc.); thySub extends thyP so we can infer_instantiate them on ctxtSub.
   --------------------------------------------------------------------------- *)
(* pow_add at (a,m,n) on ctxtSub : oeq (pow a (add m n)) (mult (pow a m)(pow a n)) *)
fun pow_add_atSub (aT, mT, nT) =
  beta_norm (Drule.infer_instantiate ctxtSub
    [(("a",0), ctermSub aT), (("m",0), ctermSub mT), (("n",0), ctermSub nT)] pow_add_vP);

(* pow_mult_base at (a,b,n) on ctxtSub : oeq (pow (mult a b) n)(mult (pow a n)(pow b n)) *)
fun pow_mult_base_atSub (aT, bT, nT) =
  beta_norm (Drule.infer_instantiate ctxtSub
    [(("a",0), ctermSub aT), (("b",0), ctermSub bT), (("n",0), ctermSub nT)] pow_mult_base_vP);

(* cong_pow at (m,a,b,n) on ctxtSub : cong m a b ==> cong m (pow a n)(pow b n) *)
fun cong_pow_atSub (mT, aT, bT, nT) hcong =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mT), (("a",0), ctermSub aT),
         (("b",0), ctermSub bT), (("n",0), ctermSub nT)] cong_pow_vP)
  in Thm.implies_elim inst hcong end;

(* apm1 re-varified for instantiation on ctxtSub at (p,a) *)
val apm1_vSub = varify apm1;
fun apm1_atSub (pT, aT) hPrime hNdvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("p",0), ctermSub pT), (("a",0), ctermSub aT)] apm1_vSub)
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hNdvd end;

(* lagrange_roots varified onto ctxtSub at (p,a) :
     prime2 p ==> cong p (mult a a) 1 ==> Disj (cong p a 1)(cong p (Suc a) 0) *)
val lagrange_roots_vSub = varify lagrange_roots;
fun lagrange_roots_atSub (pT, aT) hPrime hCong =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("p",0), ctermSub pT), (("a",0), ctermSub aT)] lagrange_roots_vSub)
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hCong end;

val () = out "EC_ACCESSORS_READY\n";

(* ============================================================================
   ==========================  THE DICHOTOMY  =================================
   dichotomy :
     prime2 p ==> ~(p|a) ==> oeq (sub p 1) (add m m)
       ==> Disj (cong p (pow a m) 1) (cong p (Suc (pow a m)) 0)
   0-hyp.  m is a free parameter (the half of p-1).
   ============================================================================ *)
val () = out "DICHOTOMY_BEGIN\n";

val dichotomy =
  let
    val pF = Free("p", natT);
    val aF = Free("a", natT);
    val mF = Free("m", natT);

    val hPrimeP = jT (prime2 pF);             val hPrime = Thm.assume (ctermSub hPrimeP);
    val hNdvdP  = jT (neg (dvd pF aF));        val hNdvd  = Thm.assume (ctermSub hNdvdP);
    val hOddP   = jT (oeq (sub pF oneC) (add mF mF));  (* p-1 = 2m *)
    val hOdd    = Thm.assume (ctermSub hOddP);

    val yT      = pow aF mF;                   (* y = pow a m *)
    val goalC   = mkDisj (cong pF yT oneC) (cong pF (suc yT) ZeroC);

    (* (1) pow_add at (a,m,m) : oeq (pow a (add m m)) (mult (pow a m)(pow a m)) *)
    val pa_add  = pow_add_atSub (aF, mF, mF);  (* oeq (pow a (m+m)) (mult y y) *)

    (* (2) rewrite pow a (m+m) -> pow a (sub p 1).  hOdd : (sub p 1) = (m+m),
           so oeq (add m m)(sub p 1) by sym ; substitute into the LHS of pa_add via
           predicate %z. oeq (pow a z) (mult y y). *)
    val hOddSym = oeq_sym OF [hOdd];           (* oeq (add m m) (sub p 1) *)
    val zF1 = Free("z_ec1", natT);
    val Pz1 = Term.lambda zF1 (oeq (pow aF zF1) (mult yT yT));
    val pa_sub  = substPredS2 (Pz1, add mF mF, sub pF oneC) hOddSym pa_add;
                                                (* oeq (pow a (sub p 1)) (mult y y) *)

    (* (3) apm1 : cong p (pow a (sub p 1)) 1 *)
    val ap = apm1_atSub (pF, aF) hPrime hNdvd; (* cong p (pow a (sub p 1)) 1 *)

    (* (4) oeq (mult y y) (pow a (sub p 1)) -> cong p (mult y y) (pow a (sub p 1)) *)
    val pa_sub_sym = oeq_sym OF [pa_sub];      (* oeq (mult y y) (pow a (sub p 1)) *)
    val cong_yy_pa = oeq_to_congSub (pF, mult yT yT, pow aF (sub pF oneC)) pa_sub_sym;
                                                (* cong p (mult y y) (pow a (sub p 1)) *)

    (* (5) chain : cong p (mult y y) 1 *)
    val cong_yy_1 = cong_trans_atSub (pF, mult yT yT, pow aF (sub pF oneC), oneC) cong_yy_pa ap;
                                                (* cong p (mult y y) 1 *)

    (* (6) lagrange_roots at (p, y) : Disj (cong p y 1)(cong p (Suc y) 0) *)
    val res = lagrange_roots_atSub (pF, yT) hPrime cong_yy_1;   (* = goalC *)

    val d1 = Thm.implies_intr (ctermSub hOddP) res;
    val d2 = Thm.implies_intr (ctermSub hNdvdP) d1;
    val d3 = Thm.implies_intr (ctermSub hPrimeP) d2;
  in varify d3 end;

val () = out "DICHOTOMY_PROVED\n";

(* ---- validate : 0-hyp + aconv intended ---- *)
val pVe = Var (("p",0), natT);
val aVe = Var (("a",0), natT);
val mVe = Var (("m",0), natT);
val dichotomy_intended =
  Logic.mk_implies (jT (prime2 pVe),
    Logic.mk_implies (jT (neg (dvd pVe aVe)),
      Logic.mk_implies (jT (oeq (sub pVe oneC) (add mVe mVe)),
        jT (mkDisj (cong pVe (pow aVe mVe) oneC) (cong pVe (suc (pow aVe mVe)) ZeroC)))));
val r_dich = checkSub ("dichotomy", dichotomy, dichotomy_intended);

(* ---- soundness probes ---- *)
val probe_dich_needs_prime =
  let val bogus = Logic.mk_implies (jT (neg (dvd pVe aVe)),
                    Logic.mk_implies (jT (oeq (sub pVe oneC) (add mVe mVe)),
                      jT (mkDisj (cong pVe (pow aVe mVe) oneC) (cong pVe (suc (pow aVe mVe)) ZeroC))))
  in not ((Thm.prop_of dichotomy) aconv bogus) end;
val probe_dich_needs_ndvd =
  let val bogus = Logic.mk_implies (jT (prime2 pVe),
                    Logic.mk_implies (jT (oeq (sub pVe oneC) (add mVe mVe)),
                      jT (mkDisj (cong pVe (pow aVe mVe) oneC) (cong pVe (suc (pow aVe mVe)) ZeroC))))
  in not ((Thm.prop_of dichotomy) aconv bogus) end;
val probe_dich_two_sided =
  let val bogus = Logic.mk_implies (jT (prime2 pVe),
                    Logic.mk_implies (jT (neg (dvd pVe aVe)),
                      Logic.mk_implies (jT (oeq (sub pVe oneC) (add mVe mVe)),
                        jT (cong pVe (pow aVe mVe) oneC))))
  in not ((Thm.prop_of dichotomy) aconv bogus) end;

val () =
  if r_dich andalso probe_dich_needs_prime andalso probe_dich_needs_ndvd andalso probe_dich_two_sided
  then out "PROBE_OK dichotomy conditional / two-sided\n"
  else out "PROBE_UNSOUND dichotomy collapsed!\n";

val () =
  if r_dich andalso probe_dich_needs_prime andalso probe_dich_needs_ndvd andalso probe_dich_two_sided
  then out "EC_DICHOTOMY_OK\n"
  else out "EC_DICHOTOMY_FAILED\n";

(* ============================================================================
   ===================  cong_dvd_transfer (helper for QR-fwd)  ================
   cong_dvd_transfer : cong p X a ==> dvd p X ==> dvd p a.
   (used to derive ~(p|x) from ~(p|a) and cong p (x*x) a)
   cong p X a = Disj (congL p X a)(congR p X a)
     congL p X a = Ex k. a = X + p*k
     congR p X a = Ex k. X = a + p*k
   With dvd p X (so X = p*j):
     Case L : a = X + p*k -> X=p*j -> a=p*(j+k) -> dvd p a
     Case R : X = a + p*k -> dvd p (a + p*k)=dvd p X ; commute -> dvd p (p*k + a) ;
              dvd p (p*k) ; dvd_diff(p, p*k, a) -> dvd p a.
   All on mult/add/dvd terms -> certify on ctxtS2 (subset of thySub).
   ============================================================================ *)
val () = out "CONG_DVD_TRANSFER_BEGIN\n";

fun cong_dvd_transfer (pT, XT, aT) hCong hDvdX =
  let
    val dL = congL pT XT aT;    (* Ex k. a = X + p*k *)
    val dR = congR pT XT aT;    (* Ex k. X = a + p*k *)
    val goalC = dvd pT aT;

    val dvdXabs = Abs("k", natT, oeq XT (mult pT (Bound 0)));   (* dvd p X body *)
    fun withJ jW (hj : thm) =     (* hj : oeq X (mult p j) *)
      let
        (* ---- CASE L : a = X + p*k ---- *)
        val caseL =
          let
            val hL = Thm.assume (ctermSub (jT dL));
            val lAbs = Abs("k", natT, oeq aT (add XT (mult pT (Bound 0))));
            fun lbody kW (hk : thm) =      (* hk : a = X + p*k *)
              let
                val rwX = add_cong_lS (XT, mult pT jW, mult pT kW) hj;  (* (X + p*k) = ((p*j)+(p*k)) *)
                val a_eq = oeq_trans OF [hk, rwX];                     (* a = (p*j)+(p*k) *)
                val ld   = left_distrib_atS (pT, jW, kW);              (* p*(j+k) = (p*j)+(p*k) *)
                val a_eq2= oeq_trans OF [a_eq, oeq_sym OF [ld]];        (* a = p*(j+k) *)
              in dvd_introS (pT, aT, add jW kW) a_eq2 end;            (* dvd p a *)
            val r = exE_elimS2 (lAbs, goalC) hL "kL_cdt" lbody;
          in Thm.implies_intr (ctermSub (jT dL)) r end;

        (* ---- CASE R : X = a + p*k ---- *)
        val caseR =
          let
            val hR = Thm.assume (ctermSub (jT dR));
            val rAbs = Abs("k", natT, oeq XT (add aT (mult pT (Bound 0))));
            fun rbody kW (hk : thm) =      (* hk : X = a + p*k *)
              let
                val dvd_apk = dvd_cong_rS (pT, XT, add aT (mult pT kW)) hk hDvdX;  (* dvd p (a + p*k) *)
                val comm    = addcommS_at (aT, mult pT kW);             (* (a + p*k) = (p*k + a) *)
                val dvd_pka = dvd_cong_rS (pT, add aT (mult pT kW), add (mult pT kW) aT) comm dvd_apk;
                                                                       (* dvd p (p*k + a) *)
                val dvd_pk  = dvd_mult_right_atS (pT, pT, kW) (dvd_refl_atS2 pT);  (* dvd p (p*k) *)
                val res     = dvd_diff_atS (pT, mult pT kW, aT) dvd_pk dvd_pka;    (* dvd p a *)
              in res end;
            val r = exE_elimS2 (rAbs, goalC) hR "kR_cdt" rbody;
          in Thm.implies_intr (ctermSub (jT dR)) r end;

        val g = disjE_elimS2 (dL, dR, goalC) hCong caseL caseR;
      in g end;
    val res = exE_elimS2 (dvdXabs, goalC) hDvdX "j_cdt" withJ;
  in res end;

val () = out "CONG_DVD_TRANSFER_READY\n";

(* ============================================================================
   ==========================  QR-FORWARD  ===================================
   qr_forward :
     prime2 p ==> ~(p|a) ==> oeq (sub p 1) (add m m)
       ==> (Ex x. cong p (mult x x) a) ==> cong p (pow a m) 1
   0-hyp.
   ============================================================================ *)
val () = out "QRFWD_BEGIN\n";

val qr_forward =
  let
    val pF = Free("p", natT);
    val aF = Free("a", natT);
    val mF = Free("m", natT);

    val hPrimeP = jT (prime2 pF);             val hPrime = Thm.assume (ctermSub hPrimeP);
    val hNdvdP  = jT (neg (dvd pF aF));        val hNdvd  = Thm.assume (ctermSub hNdvdP);
    val hOddP   = jT (oeq (sub pF oneC) (add mF mF));  val hOdd = Thm.assume (ctermSub hOddP);
    val hOddSym = oeq_sym OF [hOdd];           (* oeq (add m m)(sub p 1) *)

    val goalC   = cong pF (pow aF mF) oneC;

    (* existential over x : Ex x. cong p (mult x x) a.
       Build CAPTURE-AVOIDING with Term.lambda over a fresh Free — `cong` injects
       inner Ex/Abs("k",..) binders, so a raw `Bound 0` for x would be captured by
       those k-binders.  Term.lambda computes the de Bruijn lift correctly. *)
    val xFresh  = Free("x_qrEx", natT);
    val exAbs   = Term.lambda xFresh (cong pF (mult xFresh xFresh) aF);
    val hExP    = jT (mkEx exAbs);
    val hEx     = Thm.assume (ctermSub hExP);

    fun body xW (hcong_xx_a : thm) =     (* hcong_xx_a : cong p (mult x x) a *)
      let
        val xxT = mult xW xW;

        (* (i) ~(p|x) : assume dvd p x, derive oFalse *)
        val ndvd_x =
          let
            val hdvdx = Thm.assume (ctermSub (jT (dvd pF xW)));         (* dvd p x *)
            val dvd_xx = dvd_mult_right_atS (pF, xW, xW) hdvdx;          (* dvd p (x*x) *)
            val dvd_a  = cong_dvd_transfer (pF, xxT, aF) hcong_xx_a dvd_xx;  (* dvd p a *)
            val fls    = mp_atS2 (dvd pF aF, oFalseC) hNdvd dvd_a;       (* oFalse *)
            val metaNe = Thm.implies_intr (ctermSub (jT (dvd pF xW))) fls;
          in impI_atS2 (dvd pF xW, oFalseC) metaNe end;                 (* jT (neg (dvd p x)) *)

        (* (ii) cong p a (x*x) *)
        val cong_a_xx = cong_sym_atSub (pF, xxT, aF) hcong_xx_a;        (* cong p a (x*x) *)

        (* (iii) cong_pow at n=m : cong p (pow a m)(pow (x*x) m) *)
        val cong_powa_powxx = cong_pow_atSub (pF, aF, xxT, mF) cong_a_xx;
                                                       (* cong p (pow a m)(pow (x*x) m) *)

        (* (iv) pow (x*x) m = pow x (sub p 1) *)
        val pmb = pow_mult_base_atSub (xW, xW, mF);    (* oeq (pow (x*x) m)(mult (pow x m)(pow x m)) *)
        val padd= pow_add_atSub (xW, mF, mF);          (* oeq (pow x (m+m))(mult (pow x m)(pow x m)) *)
        val padd_sym = oeq_sym OF [padd];              (* oeq (mult (pow x m)(pow x m))(pow x (m+m)) *)
        val zF = Free("z_qr", natT);
        val Pz = Term.lambda zF (oeq (mult (pow xW mF) (pow xW mF)) (pow xW zF));
        val padd_sub = substPredS2 (Pz, add mF mF, sub pF oneC) hOddSym padd_sym;
                                                       (* oeq (mult (pow x m)(pow x m))(pow x (sub p 1)) *)
        val powxx_eq = oeq_trans OF [pmb, padd_sub];   (* oeq (pow (x*x) m)(pow x (sub p 1)) *)

        (* (v) apm1 at x : cong p (pow x (sub p 1)) 1 *)
        val ap_x = apm1_atSub (pF, xW) hPrime ndvd_x;  (* cong p (pow x (sub p 1)) 1 *)

        (* (vi) rewrite 2nd arg of (iii) : pow (x*x) m -> pow x (sub p 1) via powxx_eq.
                predicate %z. cong p (pow a m) z  (capture-avoiding). *)
        val zF2 = Free("z_qr2", natT);
        val Pz2 = Term.lambda zF2 (cong pF (pow aF mF) zF2);
        val cong_powa_powxsub = substPredS2 (Pz2, pow xxT mF, pow xW (sub pF oneC)) powxx_eq cong_powa_powxx;
                                                       (* cong p (pow a m)(pow x (sub p 1)) *)

        (* (vii) cong_trans : cong p (pow a m) 1 *)
        val res = cong_trans_atSub (pF, pow aF mF, pow xW (sub pF oneC), oneC) cong_powa_powxsub ap_x;
      in res end;

    val concl = exE_elimS2 (exAbs, goalC) hEx "x_qr" body;

    val d1 = Thm.implies_intr (ctermSub hExP) concl;
    val d2 = Thm.implies_intr (ctermSub hOddP) d1;
    val d3 = Thm.implies_intr (ctermSub hNdvdP) d2;
    val d4 = Thm.implies_intr (ctermSub hPrimeP) d3;
  in varify d4 end;

val () = out "QRFWD_PROVED\n";

(* ---- validate : 0-hyp + aconv intended ----
   The intended existential must be built with the SAME capture-avoiding lambda
   as the proof (Term.lambda over a fresh Free), else aconv fails on the inner
   k-binders of cong. *)
val qr_exFresh = Free("x_qrEx", natT);   (* gets abstracted -> Bound; Free/Var irrelevant after lambda *)
val qr_exAbs = Term.lambda qr_exFresh (cong pVe (mult qr_exFresh qr_exFresh) aVe);
val qr_forward_intended =
  Logic.mk_implies (jT (prime2 pVe),
    Logic.mk_implies (jT (neg (dvd pVe aVe)),
      Logic.mk_implies (jT (oeq (sub pVe oneC) (add mVe mVe)),
        Logic.mk_implies (jT (mkEx qr_exAbs),
          jT (cong pVe (pow aVe mVe) oneC)))));
val r_qr = checkSub ("qr_forward", qr_forward, qr_forward_intended);

(* ---- soundness probes ---- *)
val probe_qr_needs_square =
  let val bogus = Logic.mk_implies (jT (prime2 pVe),
                    Logic.mk_implies (jT (neg (dvd pVe aVe)),
                      Logic.mk_implies (jT (oeq (sub pVe oneC) (add mVe mVe)),
                        jT (cong pVe (pow aVe mVe) oneC))))
  in not ((Thm.prop_of qr_forward) aconv bogus) end;
val probe_qr_needs_ndvd =
  let val bogus = Logic.mk_implies (jT (prime2 pVe),
                    Logic.mk_implies (jT (oeq (sub pVe oneC) (add mVe mVe)),
                      Logic.mk_implies (jT (mkEx qr_exAbs),
                        jT (cong pVe (pow aVe mVe) oneC))))
  in not ((Thm.prop_of qr_forward) aconv bogus) end;
val probe_qr_nontrivial =
  not ((Thm.prop_of qr_forward) aconv (jT (cong pVe (pow aVe mVe) oneC)));

val () =
  if r_qr andalso probe_qr_needs_square andalso probe_qr_needs_ndvd andalso probe_qr_nontrivial
  then out "PROBE_OK qr_forward conditional / nontrivial\n"
  else out "PROBE_UNSOUND qr_forward collapsed!\n";

val () =
  if r_qr andalso probe_qr_needs_square andalso probe_qr_needs_ndvd andalso probe_qr_nontrivial
  then out "EC_QRFWD_OK\n"
  else out "EC_QRFWD_FAILED\n";

(* ============================================================================
   ============================  ALL DONE  ===================================
   ============================================================================ *)
val () =
  if r_dich andalso probe_dich_needs_prime andalso probe_dich_needs_ndvd
     andalso probe_dich_two_sided
     andalso r_qr andalso probe_qr_needs_square andalso probe_qr_needs_ndvd
     andalso probe_qr_nontrivial
  then out "EC_ALL_OK\n"
  else out "EC_ALL_FAILED\n";
(* ============================================================================
   KEY LEMMA toward "INFINITELY MANY PRIMES == 1 (mod 4)".
   The First-Supplement converse:  for an ODD prime q with q | x failing,
     x^2 == -1 (mod q)   ==>   q == 1 (mod 4)   (i.e. ?t. q = 4t + 1).
   Proved on the FLT base (this driver = euler_criterion = the flt base + apm1
   (Fermat for units) + lagrange_roots + mod_cancel, all on ctxtSub).
   ============================================================================ *)
val () = out "P1M4_DELTA_BEGIN\n";

(* ---- small numerals on natT ---- *)
val twoC  = suc (suc ZeroC);
val threeC= suc twoC;
val fourC = suc threeC;

(* ---- lift the global disjunction / excluded-middle / cong_mult axioms onto ctxtSub ---- *)
val disjI1_vSub = varify disjI1_ax;
fun disjI1Sub_at (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSub
      [(("A",0), ctermSub At), (("B",0), ctermSub Bt)] disjI1_vSub)) h;

val ex_middle_vSub = varify ex_middle_ax;
fun ex_middle_atSub At = beta_norm (Drule.infer_instantiate ctxtSub
      [(("A",0), ctermSub At)] ex_middle_vSub);

val cong_mult_vSub = varify cong_mult;
fun cong_mult_atSub (mt, at, a2t, bt, b2t) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt),(("a",0), ctermSub at),(("a2",0), ctermSub a2t),
         (("b",0), ctermSub bt),(("b2",0), ctermSub b2t)] cong_mult_vSub)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* mult congruence both ways on ctxtSub (mult_cong_lS2/rS2 already exist) *)
(* pow congruence in the EXPONENT on ctxtSub : oeq u v ==> oeq (pow a u)(pow a v) *)
fun pow_cong_argSub (aT, uT, vT) huv =
  let val zF = Free("z_pca", natT)
      val Pz = Term.lambda zF (oeq (pow aT uT) (pow aT zF))
  in substPredS2 (Pz, uT, vT) huv (oeqreflS2_at (pow aT uT)) end;

(* powZero on ctxtSub : oeq (pow a 0)(Suc 0) *)
val pow_Zero_vSub = pow_Zero_vP;   (* schematic ; thySub extends thyP *)
fun powZeroS2_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub t)] pow_Zero_vSub);

(* ============================================================================
   PARITY : |- !n. (?k. n = k + k) \/ (?k. n = Suc (k + k))   (every n even or odd)
   by nat induction on n.
   ============================================================================ *)
val () = out "PARITY_BEGIN\n";

val parity =
  let
    val nIndV = Free("n", natT);
    (* Q n := (?k. n = k+k) \/ (?k. n = Suc(k+k)) *)
    fun evenEx t = mkEx (Abs("k", natT, oeq t (add (Bound 0) (Bound 0))));
    fun oddEx  t = mkEx (Abs("k", natT, oeq t (suc (add (Bound 0) (Bound 0)))));
    val zF = Free("zpar", natT);
    val Qpred = Term.lambda zF (mkDisj (evenEx zF) (oddEx zF));
    val ind = nat_induct_atS2 (Qpred, nIndV);

    (* BASE n=0 :  0 = 0 + 0  -> evenEx 0  -> disjI1. *)
    val base =
      let
        val a00 = add0S2_at ZeroC;                 (* oeq (add 0 0) 0 *)
        val z_eq = oeq_sym OF [a00];               (* oeq 0 (add 0 0) *)
        val evAbs = Abs("k", natT, oeq ZeroC (add (Bound 0) (Bound 0)));
        val ev = exISub_at evAbs ZeroC z_eq;       (* evenEx 0 *)
      in disjI1Sub_at (evenEx ZeroC, oddEx ZeroC) ev end;

    (* STEP : IH : Q x ; prove Q (Suc x).  Case on IH:
         even x (x = k+k) -> Suc x = Suc(k+k) -> oddEx (Suc x) -> disjI2.
         odd  x (x = Suc(k+k)) -> Suc x = Suc(Suc(k+k)) = (Suc k)+(Suc k) -> evenEx -> disjI1. *)
    val xF = Free("xpar", natT);
    val ihprop = jT (mkDisj (evenEx xF) (oddEx xF));
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        val goalC = mkDisj (evenEx (suc xF)) (oddEx (suc xF));
        (* case EVEN : witness k with x = k+k *)
        val caseEven =
          let
            val evHypAbs = Abs("k", natT, oeq xF (add (Bound 0) (Bound 0)));
            fun body kW (hk : thm) =        (* hk : x = k + k *)
              let
                val sx = Suc_cong OF [hk];             (* Suc x = Suc (k+k) *)
                val oddAbs = Abs("k", natT, oeq (suc xF) (suc (add (Bound 0) (Bound 0))));
                val od = exISub_at oddAbs kW sx;       (* oddEx (Suc x) *)
              in disjI2Sub_at (evenEx (suc xF), oddEx (suc xF)) od end;
          in exESub_elim (evHypAbs, goalC) (Thm.assume (ctermSub (jT (evenEx xF)))) "ke" body end;
        val caseEvenImp = Thm.implies_intr (ctermSub (jT (evenEx xF))) caseEven;
        (* case ODD : witness k with x = Suc(k+k) *)
        val caseOdd =
          let
            val odHypAbs = Abs("k", natT, oeq xF (suc (add (Bound 0) (Bound 0))));
            fun body kW (hk : thm) =        (* hk : x = Suc (k + k) *)
              let
                val sx = Suc_cong OF [hk];             (* Suc x = Suc (Suc (k+k)) *)
                (* Suc (Suc (k+k)) = (Suc k) + (Suc k) :
                   (Suc k)+(Suc k) = Suc(k + Suc k) [add_Suc] = Suc(Suc(k+k)) [add_Suc_right under Suc_cong] *)
                val aS  = addSucS2_at (kW, suc kW);    (* (Suc k)+(Suc k) = Suc (k + Suc k) *)
                val aSr = addSrS2_at (kW, kW);         (* k + Suc k = Suc (k + k) *)
                val inner = Suc_cong OF [aSr];         (* Suc(k + Suc k) = Suc(Suc(k+k)) *)
                val sk_sk = oeq_trans OF [aS, inner];  (* (Suc k)+(Suc k) = Suc(Suc(k+k)) *)
                val sk_sk_sym = oeq_sym OF [sk_sk];    (* Suc(Suc(k+k)) = (Suc k)+(Suc k) *)
                val sx2 = oeq_trans OF [sx, sk_sk_sym];(* Suc x = (Suc k)+(Suc k) *)
                val evAbs = Abs("k", natT, oeq (suc xF) (add (Bound 0) (Bound 0)));
                val ev = exISub_at evAbs (suc kW) sx2; (* evenEx (Suc x) *)
              in disjI1Sub_at (evenEx (suc xF), oddEx (suc xF)) ev end;
          in exESub_elim (odHypAbs, goalC) (Thm.assume (ctermSub (jT (oddEx xF)))) "ko" body end;
        val caseOddImp = Thm.implies_intr (ctermSub (jT (oddEx xF))) caseOdd;
      in disjE_elimSub (evenEx xF, oddEx xF, goalC) IH caseEvenImp caseOddImp end;

    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val Qn = Thm.implies_elim r1 step1;          (* Q n  for the Free n *)
  in varify Qn end;

(* parity instantiated at a term t : Disj (evenEx t)(oddEx t) *)
fun evenExT t = mkEx (Abs("k", natT, oeq t (add (Bound 0) (Bound 0))));
fun oddExT  t = mkEx (Abs("k", natT, oeq t (suc (add (Bound 0) (Bound 0)))));
val parity_vSub = parity;   (* already varified *)
fun parity_at t = beta_norm (Drule.infer_instantiate ctxtSub
      [(("n",0), ctermSub t)] parity_vSub);

val () = out "PARITY_OK\n";

(* ============================================================================
   x2j : (cong q (mult x x)(sub q 1))  ==>  !j. cong q (pow x (j+j))(pow (sub q 1) j)
   x^(2j) == d^j   where d = sub q 1.  Induction on j; uses x^2 == d (HYP).
   ============================================================================ *)
val () = out "X2J_BEGIN\n";

val x2j =
  let
    val qF = Free("q", natT);
    val xF = Free("x", natT);
    val dT = sub qF oneC;                            (* d = q - 1 *)
    val hsqP = jT (cong qF (mult xF xF) dT);         (* x^2 == d *)
    val Hsq  = Thm.assume (ctermSub hsqP);

    val jIndV = Free("j", natT);
    val zF = Free("zx2j", natT);
    (* Q j := cong q (pow x (j+j))(pow d j) *)
    val Qpred = Term.lambda zF (cong qF (pow xF (add zF zF)) (pow dT zF));
    val ind = nat_induct_atS2 (Qpred, jIndV);

    (* BASE j=0 : pow x (0+0) = pow x 0 = 1 ; pow d 0 = 1.  cong q 1 1 [cong_refl],
       then rewrite endpoints back. *)
    val base =
      let
        val a00 = add0S2_at ZeroC;                   (* 0+0 = 0 *)
        val pe  = pow_cong_argSub (xF, add ZeroC ZeroC, ZeroC) a00; (* pow x (0+0) = pow x 0 *)
        val px0 = powZeroS2_at xF;                   (* pow x 0 = 1 *)
        val lhs = oeq_trans OF [pe, px0];            (* pow x (0+0) = 1 *)
        val pd0 = powZeroS2_at dT;                   (* pow d 0 = 1 *)
        (* goal : cong q (pow x (0+0))(pow d 0).  Build cong q 1 1, then rewrite. *)
        val c11 = cong_refl_atSub (qF, oneC);        (* cong q 1 1 *)
        (* rewrite 2nd arg 1 -> pow d 0 (via pd0 sym) *)
        val zc = Free("zb1", natT);
        val P2 = Term.lambda zc (cong qF oneC zc);
        val c1d = substPredS2 (P2, oneC, pow dT ZeroC) (oeq_sym OF [pd0]) c11;  (* cong q 1 (pow d 0) *)
        (* rewrite 1st arg 1 -> pow x (0+0) (via lhs sym) *)
        val zc2 = Free("zb2", natT);
        val P1 = Term.lambda zc2 (cong qF zc2 (pow dT ZeroC));
        val res = substPredS2 (P1, oneC, pow xF (add ZeroC ZeroC)) (oeq_sym OF [lhs]) c1d;
      in res end;     (* cong q (pow x (0+0))(pow d 0) *)

    (* STEP : IH cong q (pow x (j+j))(pow d j) ; prove cong q (pow x (Sj+Sj))(pow d (Sj)). *)
    val jF = Free("jx2j", natT);
    val ihprop = jT (cong qF (pow xF (add jF jF)) (pow dT jF));
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        (* Sj + Sj = Suc(Suc(j+j)) :  (Suc j)+(Suc j) = Suc(j + Suc j) = Suc(Suc(j+j)). *)
        val aS  = addSucS2_at (jF, suc jF);          (* (Suc j)+(Suc j) = Suc(j + Suc j) *)
        val aSr = addSrS2_at (jF, jF);               (* j + Suc j = Suc(j+j) *)
        val innr= Suc_cong OF [aSr];                 (* Suc(j+Suc j) = Suc(Suc(j+j)) *)
        val SjSj_eq = oeq_trans OF [aS, innr];       (* (Suc j)+(Suc j) = Suc(Suc(j+j)) *)

        (* pow x (Sj+Sj) = pow x (Suc(Suc(j+j))) [SjSj_eq] = mult x (pow x (Suc(j+j)))
                          = mult x (mult x (pow x (j+j)))  [pow_Suc twice] *)
        val pe1 = pow_cong_argSub (xF, add (suc jF)(suc jF), suc (suc (add jF jF))) SjSj_eq;
                  (* pow x (Sj+Sj) = pow x (Suc(Suc(j+j))) *)
        val ps1 = powSucS2_at (xF, suc (add jF jF));     (* pow x (Suc(Suc(j+j))) = mult x (pow x (Suc(j+j))) *)
        val ps2 = powSucS2_at (xF, add jF jF);           (* pow x (Suc(j+j)) = mult x (pow x (j+j)) *)
        val ps2c= mult_cong_rS2 (xF, pow xF (suc (add jF jF)), mult xF (pow xF (add jF jF))) ps2;
                  (* mult x (pow x (Suc(j+j))) = mult x (mult x (pow x (j+j))) *)
        val powxSS = oeq_trans OF [oeq_trans OF [pe1, ps1], ps2c];
                  (* pow x (Sj+Sj) = mult x (mult x (pow x (j+j))) *)

        (* pow d (Suc j) = mult d (pow d j)  [pow_Suc] *)
        val pdS = powSucS2_at (dT, jF);                  (* pow d (Suc j) = mult d (pow d j) *)

        (* cong chain :
             cong q (mult x (mult x (pow x (j+j)))) (mult d (pow d j))
           Build from Hsq (x^2 == d) and IH (pow x (j+j) == pow d j) via cong_mult,
           but note mult x (mult x A) = mult (mult x x) A by mult_assoc.  We compute
           cong q (mult (mult x x)(pow x (j+j)))(mult d (pow d j))
             = cong_mult q (mult x x) d (pow x (j+j)) (pow d j)  [Hsq, IH]. *)
        val cmul = cong_mult_atSub (qF, mult xF xF, dT, pow xF (add jF jF), pow dT jF) Hsq IH;
                  (* cong q (mult (mult x x)(pow x (j+j)))(mult d (pow d j)) *)

        (* mult (mult x x)(pow x (j+j)) = mult x (mult x (pow x (j+j)))  [mult_assoc] *)
        val massoc = multassocS2_at (xF, xF, pow xF (add jF jF));
                  (* (x*x)*(pow x (j+j)) = x*(x*(pow x (j+j))) *)
        (* rewrite cmul's 1st arg  (x*x)*A -> x*(x*A) via massoc *)
        val zc = Free("zm1", natT);
        val Pm = Term.lambda zc (cong qF zc (mult dT (pow dT jF)));
        val cmul2 = substPredS2 (Pm, mult (mult xF xF)(pow xF (add jF jF)),
                                 mult xF (mult xF (pow xF (add jF jF)))) massoc cmul;
                  (* cong q (x*(x*A))(d*(pow d j)) *)

        (* now rewrite 1st arg  x*(x*A) -> pow x (Sj+Sj)  via powxSS (sym) *)
        val zc2 = Free("zm2", natT);
        val Pm2 = Term.lambda zc2 (cong qF zc2 (mult dT (pow dT jF)));
        val cmul3 = substPredS2 (Pm2, mult xF (mult xF (pow xF (add jF jF))),
                                 pow xF (add (suc jF)(suc jF))) (oeq_sym OF [powxSS]) cmul2;
                  (* cong q (pow x (Sj+Sj))(d*(pow d j)) *)

        (* rewrite 2nd arg  d*(pow d j) -> pow d (Suc j)  via pdS (sym) *)
        val zc3 = Free("zm3", natT);
        val Pm3 = Term.lambda zc3 (cong qF (pow xF (add (suc jF)(suc jF))) zc3);
        val res = substPredS2 (Pm3, mult dT (pow dT jF), pow dT (suc jF)) (oeq_sym OF [pdS]) cmul3;
                  (* cong q (pow x (Sj+Sj))(pow d (Suc j)) *)
      in res end;

    val step1 = Thm.forall_intr (ctermSub jF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val Qj = Thm.implies_elim r1 step1;          (* Q jIndV  (Free j) *)
    (* schematic over q, x, AND j (jIndV is a Free, varify makes it a Var). *)
    val res = Thm.implies_intr (ctermSub hsqP) Qj;
  in varify res end;

val () = out "X2J_OK\n";

(* x2j application : from  h : cong q (mult x x)(sub q 1),  produce
   cong q (pow x (j+j))(pow (sub q 1) j)  at the given j term. *)
val x2j_vSub = x2j;
fun x2j_at (qT, xT, jT_) hsq =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("q",0), ctermSub qT), (("x",0), ctermSub xT), (("j",0), ctermSub jT_)] x2j_vSub)
  in Thm.implies_elim inst hsq end;

(* ============================================================================
   neg1_sq :  (oeq q (Suc (Suc q1)))  ==>  cong q (mult (sub q 1)(sub q 1)) 1
   d^2 == 1 (mod q)  where d = sub q 1 = -1.  Witness q1 :  d*d = 1 + q*q1.
   (Pure nat arithmetic — no pow — so ctxtS2 semiring helpers are safe.)
   We prove it for q = Suc(Suc q1) directly (d = Suc q1, q1 the witness).
   ============================================================================ *)
val () = out "NEG1SQ_BEGIN\n";

(* d = sub q 1.  Given q = Suc(Suc q1), oeq (sub q 1)(Suc q1). *)
fun neg1_sq_at (qT, q1T) hq =       (* hq : oeq q (Suc(Suc q1)) ; returns cong q (mult (sub q 1)(sub q 1)) 1 *)
  let
    val dT  = sub qT oneC;
    val SqT = suc q1T;              (* Suc q1 = d (when q = Suc(Suc q1)) *)
    (* (1) oeq (sub q 1)(Suc q1) :  sub q 1 = sub (Suc(Suc q1)) (Suc 0) = sub (Suc q1) 0 = Suc q1. *)
    val e_sub1 =
      let val zF = Free("zns1", natT)
          val Pz = Term.lambda zF (oeq (sub zF oneC)(sub (suc (suc q1T)) oneC))
      in substPredS2 (Pz, suc (suc q1T), qT) (oeq_sym OF [hq]) (oeqreflS2_at (sub (suc (suc q1T)) oneC)) end;
                                        (* oeq (sub q 1)(sub (Suc(Suc q1)) 1) *)
    val e_ss = subSSS2_at (suc q1T, ZeroC);    (* sub (Suc(Suc q1))(Suc 0) = sub (Suc q1) 0 *)
    val e_n0 = subN0S2_at (suc q1T);           (* sub (Suc q1) 0 = Suc q1 *)
    val d_eq = oeq_trans OF [oeq_trans OF [e_sub1, e_ss], e_n0];   (* oeq (sub q 1)(Suc q1) *)

    (* (2) The polynomial identity (no pow) :
            oeq (mult (Suc q1)(Suc q1)) (add (Suc 0)(mult q q1)).
       LHS = (Suc q1) + (Suc q1)*q1                     [mult_Suc_right]
           = (Suc q1) + (q1 + q1*q1)                    [comm + mult_Suc_right]
       RHS = 1 + q*q1 = 1 + (Suc(Suc q1))*q1
           = 1 + (q1 + (Suc q1)*q1)?? -> compute via comm+multSr too.
       Easiest: reduce BOTH to  add (Suc 0)(add (add q1 q1)(mult q1 q1))  and trans. *)
    val sd = SqT;     (* Suc q1 *)
    (* LHS path *)
    val L1 = multSrS_at (sd, q1T);             (* (Suc q1)*(Suc q1) = (Suc q1) + (Suc q1)*q1 *)
    val cmL = multcommS2_at (sd, q1T);         (* (Suc q1)*q1 = q1*(Suc q1) *)
    val msrL= multSrS_at (q1T, q1T);           (* q1*(Suc q1) = q1 + q1*q1 *)
    val inL = oeq_trans OF [cmL, msrL];        (* (Suc q1)*q1 = q1 + q1*q1 *)
    val L2 = oeq_trans OF [L1, add_cong_rS2 (sd, mult sd q1T, add q1T (mult q1T q1T)) inL];
                                               (* (Suc q1)*(Suc q1) = (Suc q1) + (q1 + q1*q1) *)
    (* (Suc q1) + (q1 + q1*q1) : Suc q1 = add (Suc 0) q1 ; so = add (add (Suc 0) q1)(q1+q1*q1)?  No -- keep as is.
       Normalize LHS to  add (Suc 0)(add (add q1 q1)(mult q1 q1)) :
         (Suc q1) + (q1 + q1*q1)
           = Suc (q1 + (q1 + q1*q1))            [add_Suc]
           = Suc ((q1 + q1) + q1*q1)            [add_assoc sym]
           = add (Suc 0)((q1+q1)+q1*q1)         [Suc t = add 1 t]  *)
    val aS = addSucS_at (q1T, add q1T (mult q1T q1T));   (* add (Suc q1)(q1+q1*q1) = Suc(q1 + (q1+q1*q1)) *)
    val aA = addassocS_at (q1T, q1T, mult q1T q1T);      (* (q1+q1)+q1*q1 = q1+(q1+q1*q1) *)
    val aAs= oeq_sym OF [aA];                            (* q1+(q1+q1*q1) = (q1+q1)+q1*q1 *)
    val Sc = Suc_cong OF [aAs];                          (* Suc(q1+(q1+q1*q1)) = Suc((q1+q1)+q1*q1) *)
    (* Suc t = add (Suc 0) t :  add (Suc 0) t = Suc(add 0 t) = Suc t *)
    fun suc_as_add1 t =
      let val a1 = addSucS_at (ZeroC, t)        (* add (Suc 0) t = Suc(add 0 t) *)
          val a0 = add0S_at t                   (* add 0 t = t *)
          val s0 = Suc_cong OF [a0]             (* Suc(add 0 t) = Suc t *)
      in oeq_sym OF [oeq_trans OF [a1, s0]] end;  (* oeq (Suc t)(add (Suc 0) t) *)
    val Lnorm0 = oeq_trans OF [aS, Sc];          (* (Suc q1)+(q1+q1*q1) = Suc((q1+q1)+q1*q1) *)
    val L_to_1 = suc_as_add1 (add (add q1T q1T)(mult q1T q1T));  (* Suc(..) = add 1 (..) *)
    val L3 = oeq_trans OF [L2, oeq_trans OF [Lnorm0, L_to_1]];
                                                 (* (Suc q1)*(Suc q1) = add 1 ((q1+q1)+q1*q1) *)
    (* RHS path : add 1 (mult q q1) , q = Suc(Suc q1).
         mult q q1 = mult (Suc(Suc q1)) q1 = q1*(Suc(Suc q1))  [comm]
                   = q1 + q1*(Suc q1)                          [multSr]
                   = q1 + (q1 + q1*q1)                          [multSr inside]
       so add 1 (mult q q1) = add 1 (q1 + (q1 + q1*q1)).
       Normalize to add 1 ((q1+q1)+q1*q1) via add_assoc inside the second arg. *)
    (* first rewrite mult q q1 -> mult (Suc(Suc q1)) q1 using hq *)
    val mqq1_eq =
      let val zF = Free("zmq", natT)
          val Pz = Term.lambda zF (oeq (mult qT q1T)(mult zF q1T))
      in substPredS2 (Pz, qT, suc (suc q1T)) hq (oeqreflS2_at (mult qT q1T)) end;  (* mult q q1 = mult (Suc(Suc q1)) q1 *)
    val cmR = multcommS2_at (suc (suc q1T), q1T);   (* (Suc(Suc q1))*q1 = q1*(Suc(Suc q1)) *)
    val msr1= multSrS_at (q1T, suc q1T);            (* q1*(Suc(Suc q1)) = q1 + q1*(Suc q1) *)
    val msr2= multSrS_at (q1T, q1T);                (* q1*(Suc q1) = q1 + q1*q1 *)
    val msr2c = add_cong_rS2 (q1T, mult q1T (suc q1T), add q1T (mult q1T q1T)) msr2;
                                                    (* q1 + q1*(Suc q1) = q1 + (q1 + q1*q1) *)
    val mqq1_full = oeq_trans OF [mqq1_eq, oeq_trans OF [cmR, oeq_trans OF [msr1, msr2c]]];
                                                    (* mult q q1 = q1 + (q1 + q1*q1) *)
    (* add 1 (mult q q1) = add 1 (q1 + (q1+q1*q1)) = add 1 ((q1+q1)+q1*q1) *)
    val R1 = add_cong_rS2 (oneC, mult qT q1T, add q1T (add q1T (mult q1T q1T))) mqq1_full;
                                                    (* add 1 (mult q q1) = add 1 (q1+(q1+q1*q1)) *)
    val aA2 = addassocS_at (q1T, q1T, mult q1T q1T);  (* (q1+q1)+q1*q1 = q1+(q1+q1*q1) *)
    val R2 = oeq_trans OF [R1, add_cong_rS2 (oneC, add q1T (add q1T (mult q1T q1T)),
                                add (add q1T q1T)(mult q1T q1T)) (oeq_sym OF [aA2])];
                                                    (* add 1 (mult q q1) = add 1 ((q1+q1)+q1*q1) *)
    (* combine : (Suc q1)*(Suc q1) = add 1 ((q1+q1)+q1*q1) = add 1 (mult q q1) *)
    val poly = oeq_trans OF [L3, oeq_sym OF [R2]];  (* oeq (mult (Suc q1)(Suc q1))(add 1 (mult q q1)) *)

    (* (3) rewrite (Suc q1) -> (sub q 1) = d on BOTH factors of LHS, using d_eq (sym). *)
    val dsym = oeq_sym OF [d_eq];                   (* oeq (Suc q1)(sub q 1) *)
    (* mult (Suc q1)(Suc q1) -> mult d (Suc q1) -> mult d d *)
    val ml = mult_cong_lS2 (sd, dT, sd) dsym;       (* mult (Suc q1)(Suc q1) = mult d (Suc q1) *)
    val mr = mult_cong_rS2 (dT, sd, dT) dsym;       (* mult d (Suc q1) = mult d d *)
    val mlr= oeq_trans OF [ml, mr];                 (* mult (Suc q1)(Suc q1) = mult d d *)
    val poly2 = oeq_trans OF [oeq_sym OF [mlr], poly];  (* oeq (mult d d)(add 1 (mult q q1)) *)

    (* (4) cong_introRSub : oeq a (add b (mult q w)) ==> cong q a b.  a=mult d d, b=1, w=q1. *)
    val res = cong_introRSub (qT, mult dT dT, oneC, q1T) poly2;  (* cong q (mult d d) 1 *)
  in res end;

val () = out "NEG1SQ_OK\n";

(* ============================================================================
   dpow_even / dpow_odd :  given  hd2 : cong q (mult d d) 1  (d == -1, d^2 == 1) :
     dpow_even : cong q (pow d (k+k)) 1            (d^(2k) == 1)
     dpow_odd  : cong q (pow d (Suc(k+k))) d       (d^(2k+1) == d)
   Built once with internal Frees q, d, k and varified; q/d/k all become schematic
   (d is a GENERIC term ad-hoc d == -1, NOT tied to sub q 1 — instantiated later).
   ============================================================================ *)
val () = out "DPOW_BEGIN\n";

val dpow_even =
  let
    val qF = Free("q", natT);
    val dF = Free("d", natT);
    val dT = dF;
    val hd2P = jT (cong qF (mult dT dT) oneC);
    val Hd2  = Thm.assume (ctermSub hd2P);
    val kIndV = Free("k", natT);
    val zF = Free("zde", natT);
    val Qpred = Term.lambda zF (cong qF (pow dT (add zF zF)) oneC);
    val ind = nat_induct_atS2 (Qpred, kIndV);

    (* BASE k=0 : pow d (0+0) = pow d 0 = 1.  cong q 1 1 -> rewrite. *)
    val base =
      let
        val a00 = add0S2_at ZeroC;                       (* 0+0=0 *)
        val pe  = pow_cong_argSub (dT, add ZeroC ZeroC, ZeroC) a00;  (* pow d (0+0)=pow d 0 *)
        val pd0 = powZeroS2_at dT;                        (* pow d 0 = 1 *)
        val lhs = oeq_trans OF [pe, pd0];                 (* pow d (0+0) = 1 *)
        val c11 = cong_refl_atSub (qF, oneC);            (* cong q 1 1 *)
        val zc  = Free("zde0", natT);
        val P1  = Term.lambda zc (cong qF zc oneC);
        val res = substPredS2 (P1, oneC, pow dT (add ZeroC ZeroC)) (oeq_sym OF [lhs]) c11;
      in res end;     (* cong q (pow d (0+0)) 1 *)

    (* STEP : IH cong q (pow d (k+k)) 1 ; prove cong q (pow d (Sk+Sk)) 1.
         pow d (Sk+Sk) = pow d (Suc(Suc(k+k))) = mult d (mult d (pow d (k+k))).
         cong : mult (mult d d)(pow d (k+k)) == mult 1 1 == 1  [hd2, IH, mult_assoc]. *)
    val kF = Free("kde", natT);
    val ihprop = jT (cong qF (pow dT (add kF kF)) oneC);
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        val aS  = addSucS2_at (kF, suc kF);              (* (Sk)+(Sk) = Suc(k + Sk) *)
        val aSr = addSrS2_at (kF, kF);                   (* k + Sk = Suc(k+k) *)
        val innr= Suc_cong OF [aSr];                     (* Suc(k+Sk)=Suc(Suc(k+k)) *)
        val SkSk_eq = oeq_trans OF [aS, innr];           (* (Sk)+(Sk) = Suc(Suc(k+k)) *)
        val pe1 = pow_cong_argSub (dT, add (suc kF)(suc kF), suc (suc (add kF kF))) SkSk_eq;
        val ps1 = powSucS2_at (dT, suc (add kF kF));     (* pow d (Suc(Suc(k+k))) = mult d (pow d (Suc(k+k))) *)
        val ps2 = powSucS2_at (dT, add kF kF);           (* pow d (Suc(k+k)) = mult d (pow d (k+k)) *)
        val ps2c= mult_cong_rS2 (dT, pow dT (suc (add kF kF)), mult dT (pow dT (add kF kF))) ps2;
        val powdSS = oeq_trans OF [oeq_trans OF [pe1, ps1], ps2c];
                   (* pow d (Sk+Sk) = mult d (mult d (pow d (k+k))) *)

        (* cong : mult (mult d d)(pow d (k+k)) == mult 1 1  [hd2, IH] *)
        val cmul = cong_mult_atSub (qF, mult dT dT, oneC, pow dT (add kF kF), oneC) Hd2 IH;
                   (* cong q (mult (mult d d)(pow d (k+k)))(mult 1 1) *)
        (* mult (mult d d)(pow d (k+k)) = mult d (mult d (pow d (k+k)))  [mult_assoc] *)
        val massoc = multassocS2_at (dT, dT, pow dT (add kF kF));
        val zc = Free("zde1", natT);
        val Pm = Term.lambda zc (cong qF zc (mult oneC oneC));
        val cmul2 = substPredS2 (Pm, mult (mult dT dT)(pow dT (add kF kF)),
                                 mult dT (mult dT (pow dT (add kF kF)))) massoc cmul;
                   (* cong q (mult d (mult d (pow d (k+k))))(mult 1 1) *)
        (* rewrite 1st arg -> pow d (Sk+Sk) via powdSS sym *)
        val zc2 = Free("zde2", natT);
        val Pm2 = Term.lambda zc2 (cong qF zc2 (mult oneC oneC));
        val cmul3 = substPredS2 (Pm2, mult dT (mult dT (pow dT (add kF kF))),
                                 pow dT (add (suc kF)(suc kF))) (oeq_sym OF [powdSS]) cmul2;
                   (* cong q (pow d (Sk+Sk))(mult 1 1) *)
        (* mult 1 1 = 1  [mult_1_left] ; rewrite 2nd arg *)
        val m11 = mult1lSub_at oneC;                      (* mult 1 1 = 1 *)
        val zc3 = Free("zde3", natT);
        val Pm3 = Term.lambda zc3 (cong qF (pow dT (add (suc kF)(suc kF))) zc3);
        val res = substPredS2 (Pm3, mult oneC oneC, oneC) m11 cmul3;
                   (* cong q (pow d (Sk+Sk)) 1 *)
      in res end;

    val step1 = Thm.forall_intr (ctermSub kF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val Qk = Thm.implies_elim r1 step1;            (* cong q (pow d (k+k)) 1, k = kIndV Free *)
    val res = Thm.implies_intr (ctermSub hd2P) Qk;
  in varify res end;
(* dpow_even : |- cong ?q (mult ?d ?d) 1 ==> cong ?q (pow ?d (?k + ?k)) 1 *)

(* dpow_even applicator : from hd2 : cong q (mult d d) 1, get cong q (pow d (k+k)) 1. *)
val dpow_even_vSub = dpow_even;
fun dpow_even_at (qT, dT, kT) hd2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("q",0), ctermSub qT),(("d",0), ctermSub dT),(("k",0), ctermSub kT)] dpow_even_vSub)
  in Thm.implies_elim inst hd2 end;

val () = out "DPOW_EVEN_OK\n";

(* dpow_odd : cong q (mult d d) 1 ==> cong q (pow d (Suc(k+k))) d.
   pow d (Suc(k+k)) = mult d (pow d (k+k))  [pow_Suc] ; cong d (pow d (k+k)) == cong d 1
   via cong_mult(refl d)(dpow_even) ; mult d 1 == d. *)
val dpow_odd =
  let
    val qF = Free("q", natT);
    val dF = Free("d", natT);
    val dT = dF;
    val kF = Free("k", natT);
    val hd2P = jT (cong qF (mult dT dT) oneC);
    val Hd2  = Thm.assume (ctermSub hd2P);

    val even_k = dpow_even_at (qF, dT, kF) Hd2;        (* cong q (pow d (k+k)) 1 *)
    (* cong q (mult d (pow d (k+k)))(mult d 1)  via cong_mult (cong_refl d)(even_k) *)
    val crefl_d = cong_refl_atSub (qF, dT);            (* cong q d d *)
    val cmul = cong_mult_atSub (qF, dT, dT, pow dT (add kF kF), oneC) crefl_d even_k;
               (* cong q (mult d (pow d (k+k)))(mult d 1) *)
    (* mult d 1 = d  [mult_1_right] ; rewrite 2nd arg -> d *)
    val md1 = mult_1_right_atSub dT;                   (* mult d 1 = d *)
    val zc = Free("zdo1", natT);
    val P1 = Term.lambda zc (cong qF (mult dT (pow dT (add kF kF))) zc);
    val cmul1 = substPredS2 (P1, mult dT oneC, dT) md1 cmul;  (* cong q (mult d (pow d (k+k))) d *)
    (* pow d (Suc(k+k)) = mult d (pow d (k+k))  [pow_Suc] ; rewrite 1st arg back *)
    val pds = powSucS2_at (dT, add kF kF);             (* pow d (Suc(k+k)) = mult d (pow d (k+k)) *)
    val zc2 = Free("zdo2", natT);
    val P2 = Term.lambda zc2 (cong qF zc2 dT);
    val res0 = substPredS2 (P2, mult dT (pow dT (add kF kF)), pow dT (suc (add kF kF))) (oeq_sym OF [pds]) cmul1;
               (* cong q (pow d (Suc(k+k))) d *)
    val res = Thm.implies_intr (ctermSub hd2P) res0;
  in varify res end;
(* dpow_odd : |- cong ?q (mult ?d ?d) 1 ==> cong ?q (pow ?d (Suc(?k + ?k))) ?d *)

val dpow_odd_vSub = dpow_odd;
fun dpow_odd_at (qT, dT, kT) hd2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("q",0), ctermSub qT),(("d",0), ctermSub dT),(("k",0), ctermSub kT)] dpow_odd_vSub)
  in Thm.implies_elim inst hd2 end;

val () = out "DPOW_OK\n";

(* ============================================================================
   CONTRADICTION HELPERS
     cong2_0_false : le 3 q ==> cong q 2 0 ==> oFalse
     cong_d1_false : le 3 q ==> cong q (sub q 1) 1 ==> oFalse
   (3 = Suc(Suc(Suc 0)).)
   ============================================================================ *)
val () = out "CONTRA_BEGIN\n";

(* Suc_inj / Suc_neq_Zero on ctxtSub *)
val Suc_inj_vSub = varify Suc_inj_ax;
fun Suc_inj_atSub (uT, vT) = beta_norm (Drule.infer_instantiate ctxtSub
      [(("a",0), ctermSub uT),(("b",0), ctermSub vT)] Suc_inj_vSub);
val Suc_neq_Zero_vSub = varify Suc_neq_Zero_ax;
fun Suc_neq_Zero_atSub t = beta_norm (Drule.infer_instantiate ctxtSub
      [(("n",0), ctermSub t)] Suc_neq_Zero_vSub);

(* mult helpers (no pow) on ctxtSub for the q*k expansions *)
fun mult0rSub_local t = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] mult_0_right_vSub);

(* cong2_0_false : le 3 q (= Ex p. q = 3 + p) and cong q 2 0  ==>  oFalse. *)
fun cong2_0_false qT hle3 hc20 =
  let
    (* extract q = 3 + p ; reduce to q = Suc(Suc(Suc p)) *)
    val threeT = suc (suc (suc ZeroC));
    val leAbs  = Abs("p", natT, oeq qT (add threeT (Bound 0)));
    fun afterP pW (hqp : thm) =     (* hqp : q = 3 + p *)
      let
        (* 3 + p = Suc(Suc(Suc p)) *)
        val e1 = addSucS2_at (suc (suc ZeroC), pW);   (* add 3 p = Suc(add 2 p) *)
        val e2 = addSucS2_at (suc ZeroC, pW);         (* add 2 p = Suc(add 1 p) *)
        val e3 = addSucS2_at (ZeroC, pW);             (* add 1 p = Suc(add 0 p) *)
        val e4 = add0S2_at pW;                        (* add 0 p = p *)
        val add1p = oeq_trans OF [e3, Suc_cong OF [e4]];      (* add 1 p = Suc p *)
        val add2p = oeq_trans OF [e2, Suc_cong OF [add1p]];    (* add 2 p = Suc(Suc p) *)
        val step  = oeq_trans OF [e1, Suc_cong OF [add2p]];    (* add 3 p = Suc(Suc(Suc p)) *)
        val q_eq = oeq_trans OF [hqp, step];          (* q = Suc(Suc(Suc p)) *)

        (* cong q 2 0  unfolds to  (Ex k. 0 = 2 + q*k) \/ (Ex k. 2 = 0 + q*k). *)
        val twoT = suc (suc ZeroC);
        val cLabs = Abs("k", natT, oeq ZeroC (add twoT (mult qT (Bound 0))));
        val cRabs = Abs("k", natT, oeq twoT (add ZeroC (mult qT (Bound 0))));
        (* case congL : 0 = 2 + q*k = Suc(Suc(q*k)).  Suc_neq_Zero. *)
        val caseL =
          let
            fun body kW (hk : thm) =     (* hk : 0 = 2 + q*k *)
              let
                val es = addSucS2_at (suc ZeroC, mult qT kW);  (* (Suc(Suc 0))+q*k = Suc((Suc 0)+q*k) *)
                val z_suc = oeq_trans OF [hk, es];             (* 0 = Suc((Suc 0)+q*k) *)
                val suc_z = oeq_sym OF [z_suc];                (* Suc(..) = 0 *)
              in (Suc_neq_Zero_atSub (add (suc ZeroC)(mult qT kW))) OF [suc_z] end;
          in exESub_elim (cLabs, oFalseC) (Thm.assume (ctermSub (jT (mkEx cLabs)))) "kL" body end;
        val caseLImp = Thm.implies_intr (ctermSub (jT (mkEx cLabs))) caseL;
        (* case congR : 2 = 0 + q*k = q*k.  rewrite q -> Suc(Suc(Suc p)) ; case on k. *)
        val caseR =
          let
            fun body kW (hk : thm) =     (* hk : 2 = 0 + q*k *)
              let
                val a0 = add0S2_at (mult qT kW);   (* 0 + q*k = q*k *)
                val two_qk = oeq_trans OF [hk, a0]; (* 2 = q*k *)
                (* case on k : dzosS_at k *)
                val dz = dzosS_at kW;               (* Disj (oeq k 0)(Ex q'. oeq k (Suc q')) *)
                val caseK0 =
                  let
                    val hk0 = Thm.assume (ctermSub (jT (oeq kW ZeroC)));   (* k = 0 *)
                    (* q*k = q*0 = 0 ; so 2 = 0.  rewrite k->0 in two_qk via subst, then mult0r. *)
                    val zF = Free("zk0", natT)
                    val Pz = Term.lambda zF (oeq twoT (mult qT zF))
                    val two_q0 = substPredS2 (Pz, kW, ZeroC) hk0 two_qk;   (* 2 = q*0 *)
                    val mq0 = mult0rSub_local qT;                          (* q*0 = 0 *)
                    val two_0 = oeq_trans OF [two_q0, mq0];                (* 2 = 0 *)
                    (* 2 = Suc(Suc 0) ; 0 ; Suc(Suc 0) = 0 contra *)
                    val two_0_sym = oeq_sym OF [two_0];                    (* 0 = 2 = Suc(Suc 0) *)
                    val zsuc = oeq_sym OF [two_0_sym];                     (* Suc(Suc 0) = 0 *)
                  in (Suc_neq_Zero_atSub (suc ZeroC)) OF [zsuc] end;
                val caseK0Imp = Thm.implies_intr (ctermSub (jT (oeq kW ZeroC))) caseK0;
                val ksAbs = Abs("q'", natT, oeq kW (suc (Bound 0)));
                fun ksBody k'W (hks : thm) =   (* hks : k = Suc k' *)
                      let
                        (* q*k = q*(Suc k') = q + q*k'  [mult_Suc_right]
                           rewrite k -> Suc k' in two_qk first. *)
                        val zF = Free("zks", natT)
                        val Pz = Term.lambda zF (oeq twoT (mult qT zF))
                        val two_qSk = substPredS2 (Pz, kW, suc k'W) hks two_qk;  (* 2 = q*(Suc k') *)
                        val mqs = multSrS_at (qT, k'W);                          (* q*(Suc k') = q + q*k' *)
                        val two_qqk = oeq_trans OF [two_qSk, mqs];               (* 2 = q + q*k' *)
                        (* rewrite q -> Suc(Suc(Suc p)) *)
                        val zF2 = Free("zks2", natT)
                        val Pz2 = Term.lambda zF2 (oeq twoT (add zF2 (mult qT k'W)))
                        val two_3pk = substPredS2 (Pz2, qT, suc (suc (suc pW))) q_eq two_qqk;
                                       (* 2 = Suc(Suc(Suc p)) + q*k' *)
                        (* Suc(Suc(Suc p)) + q*k' = Suc(Suc(Suc(p + q*k'))) *)
                        val s1 = addSucS2_at (suc (suc pW), mult qT k'W);  (* (Suc(Suc(Suc p)))+Z = Suc((Suc(Suc p))+Z) *)
                        val s2 = addSucS2_at (suc pW, mult qT k'W);        (* (Suc(Suc p))+Z = Suc((Suc p)+Z) *)
                        val s3 = addSucS2_at (pW, mult qT k'W);            (* (Suc p)+Z = Suc(p+Z) *)
                        val rhs_norm = oeq_trans OF [s1, Suc_cong OF [oeq_trans OF [s2, Suc_cong OF [s3]]]];
                                       (* (Suc(Suc(Suc p)))+Z = Suc(Suc(Suc(p+Z))) *)
                        val two_norm = oeq_trans OF [two_3pk, rhs_norm];  (* 2 = Suc(Suc(Suc(p+Z))) *)
                        (* 2 = Suc(Suc 0) ; so Suc(Suc 0) = Suc(Suc(Suc(p+Z))) -> 0 = Suc(p+Z) -> contra. *)
                        val two_norm_sym = oeq_sym OF [two_norm];          (* Suc(Suc(Suc(p+Z))) = Suc(Suc 0) *)
                        (* 2 is the term suc(suc ZeroC) = Suc(Suc 0).  two_norm : Suc(Suc 0) = Suc(Suc(Suc(p+Z))).
                           Apply Suc_inj twice : 0 = Suc(p+Z). *)
                        val inj1 = Suc_inj_atSub (suc ZeroC, suc (suc (add pW (mult qT k'W)))) OF [two_norm];
                                       (* Suc 0 = Suc(Suc(p+Z)) *)
                        val inj2 = Suc_inj_atSub (ZeroC, suc (add pW (mult qT k'W))) OF [inj1];
                                       (* 0 = Suc(p+Z) *)
                        val zsuc = oeq_sym OF [inj2];   (* Suc(p+Z) = 0 *)
                      in (Suc_neq_Zero_atSub (add pW (mult qT k'W))) OF [zsuc] end;
                val ksEx = mkEx ksAbs;   (* Ex q'. k = Suc q' *)
                val caseKSImp =
                  Thm.implies_intr (ctermSub (jT ksEx))
                    (exESub_elim (ksAbs, oFalseC) (Thm.assume (ctermSub (jT ksEx))) "kk" ksBody);
              in disjE_elimSub (oeq kW ZeroC, ksEx, oFalseC)
                   dz caseK0Imp caseKSImp
              end;
          in exESub_elim (cRabs, oFalseC) (Thm.assume (ctermSub (jT (mkEx cRabs)))) "kR" body end;
        val caseRImp = Thm.implies_intr (ctermSub (jT (mkEx cRabs))) caseR;
      in disjE_elimSub (mkEx cLabs, mkEx cRabs, oFalseC) hc20 caseLImp caseRImp end;
    val res = exESub_elim (leAbs, oFalseC) hle3 "pq" afterP;
  in res end;

val () = out "CONTRA_PARTIAL\n";

(* cong_d1_false : le 3 q ==> cong q (sub q 1) 1 ==> oFalse.
   Reduce to cong q 2 0 then apply cong2_0_false. *)
fun cong_d1_false qT hle3 hd1 =
  let
    val twoT = suc (suc ZeroC);
    val dT = sub qT oneC;
    (* extract q = 3 + p -> q = Suc(Suc(Suc p)), sub q 1 = Suc(Suc p) *)
    val threeT = suc (suc (suc ZeroC));
    val leAbs  = Abs("p", natT, oeq qT (add threeT (Bound 0)));
    fun afterP pW (hqp : thm) =
      let
        (* q = Suc(Suc(Suc p)) *)
        val e1 = addSucS2_at (suc (suc ZeroC), pW);
        val e2 = addSucS2_at (suc ZeroC, pW);
        val e3 = addSucS2_at (ZeroC, pW);
        val e4 = add0S2_at pW;
        val add1p = oeq_trans OF [e3, Suc_cong OF [e4]];
        val add2p = oeq_trans OF [e2, Suc_cong OF [add1p]];
        val step  = oeq_trans OF [e1, Suc_cong OF [add2p]];
        val q_eq = oeq_trans OF [hqp, step];          (* q = Suc(Suc(Suc p)) *)

        (* sub q 1 = Suc(Suc p) :  sub (Suc(Suc(Suc p)))(Suc 0) = sub (Suc(Suc p)) 0 = Suc(Suc p). *)
        val d_eq =
          let
            val zF = Free("zd", natT)
            val Pz = Term.lambda zF (oeq (sub zF oneC)(sub (suc (suc (suc pW))) oneC))
            val sub_rw = substPredS2 (Pz, suc (suc (suc pW)), qT) (oeq_sym OF [q_eq])
                           (oeqreflS2_at (sub (suc (suc (suc pW))) oneC));  (* sub q 1 = sub (Suc(Suc(Suc p))) 1 *)
            val ss = subSSS2_at (suc (suc pW), ZeroC);   (* sub (Suc(Suc(Suc p)))(Suc 0) = sub (Suc(Suc p)) 0 *)
            val n0 = subN0S2_at (suc (suc pW));          (* sub (Suc(Suc p)) 0 = Suc(Suc p) *)
          in oeq_trans OF [oeq_trans OF [sub_rw, ss], n0] end;  (* oeq (sub q 1)(Suc(Suc p)) *)

        (* step 1 : cong q (add (sub q 1) 1)(add 1 1)  via cong_add hd1 (cong_refl 1) *)
        val crefl1 = cong_refl_atSub (qT, oneC);
        val cadd = cong_add_atSub (qT, dT, oneC, oneC, oneC) hd1 crefl1;
                   (* cong q (add (sub q 1) 1)(add 1 1) *)
        (* add 1 1 = Suc(Suc 0) = 2 :  add (Suc 0)(Suc 0) = Suc(add 0 (Suc 0)) = Suc(Suc 0). *)
        val a11 =
          let val s = addSucS2_at (ZeroC, oneC)        (* add (Suc 0)(Suc 0) = Suc(add 0 (Suc 0)) *)
              val z = add0S2_at oneC                   (* add 0 (Suc 0) = Suc 0 *)
          in oeq_trans OF [s, Suc_cong OF [z]] end;    (* add 1 1 = Suc(Suc 0) *)
        (* rewrite 2nd arg add 1 1 -> 2 *)
        val zc = Free("zc2", natT)
        val P2 = Term.lambda zc (cong qT (add dT oneC) zc)
        val cadd2 = substPredS2 (P2, add oneC oneC, twoT) a11 cadd;  (* cong q (add (sub q 1) 1) 2 *)

        (* add (sub q 1) 1 :  rewrite sub q 1 -> Suc(Suc p), then add (Suc(Suc p))(Suc 0) = Suc(Suc(Suc p)) = q *)
        val add_lhs_eq =
          let
            (* add (sub q 1) 1 = add (Suc(Suc p)) 1   [d_eq on 1st arg of add] *)
            val zF = Free("zal", natT)
            val Pz = Term.lambda zF (oeq (add dT oneC)(add zF oneC))
            val r1 = substPredS2 (Pz, dT, suc (suc pW)) d_eq (oeqreflS2_at (add dT oneC));
                     (* add (sub q 1) 1 = add (Suc(Suc p)) 1 *)
            (* add (Suc(Suc p))(Suc 0) = Suc(add (Suc(Suc p)) 0) = Suc(Suc(Suc p)) *)
            val sr = addSrS2_at (suc (suc pW), ZeroC);     (* add (Suc(Suc p))(Suc 0) = Suc(add (Suc(Suc p)) 0) *)
            val a0 = add0rS2_at (suc (suc pW));            (* add (Suc(Suc p)) 0 = Suc(Suc p) *)
            val r2 = oeq_trans OF [sr, Suc_cong OF [a0]];  (* add (Suc(Suc p))(Suc 0) = Suc(Suc(Suc p)) *)
            val r3 = oeq_trans OF [r2, oeq_sym OF [q_eq]]; (* add (Suc(Suc p))(Suc 0) = q *)
          in oeq_trans OF [r1, r3] end;                    (* add (sub q 1) 1 = q *)

        (* rewrite 1st arg of cadd2 :  add (sub q 1) 1 -> q  ->  cong q q 2 *)
        val zc2 = Free("zc3", natT)
        val P3 = Term.lambda zc2 (cong qT zc2 twoT)
        val cqq2 = substPredS2 (P3, add dT oneC, qT) add_lhs_eq cadd2;  (* cong q q 2 *)
        val c2q  = cong_sym_atSub (qT, qT, twoT) cqq2;                  (* cong q 2 q *)

        (* cong q q 0 :  congR witness 1 :  oeq q (add 0 (mult q 1)). *)
        val cq0 =
          let
            val mq1 = mult_1_right_atSub qT;          (* mult q 1 = q *)
            val a0  = add0S2_at (mult qT oneC);       (* add 0 (mult q 1) = mult q 1 *)
            val chain = oeq_trans OF [a0, mq1];       (* add 0 (mult q 1) = q *)
            val qeqadd = oeq_sym OF [chain];          (* q = add 0 (mult q 1) *)
          in cong_introRSub (qT, qT, ZeroC, oneC) qeqadd end;   (* cong q q 0 *)

        (* trans : cong q 2 q , cong q q 0 -> cong q 2 0 *)
        val c20 = cong_trans_atSub (qT, twoT, qT, ZeroC) c2q cq0;  (* cong q 2 0 *)
        (* le 3 q : rebuild from hqp (q = 3 + p) via le_intro? We have hle3 already in scope. *)
      in cong2_0_false qT hle3 c20 end;
    val res = exESub_elim (leAbs, oFalseC) hle3 "pd" afterP;
  in res end;

val () = out "CONGD1_OK\n";

(* ============================================================================
   q_is_odd : prime2 q ==> lt 2 q ==> (?m. oeq (sub q 1)(add m m))
   (an odd prime q>2 has q-1 even).  parity on (sub q 1):
     even (sub q 1) = (?m. sub q 1 = m+m) -> done.
     odd  (sub q 1) = (?m. sub q 1 = Suc(m+m)) -> q = Suc(sub q 1)?? not directly;
       instead: q-1 odd means q even.  Build dvd 2 q and contradict prime + 2<q.
   We avoid the q-from-(q-1) reconstruction by working from q = Suc(Suc(Suc p))
   (2<q) and parity of (sub q 1) = Suc(Suc p):  if (Suc(Suc p)) = Suc(m+m) then
   Suc p = m + m, and q = Suc(Suc(Suc p)) = Suc(Suc(Suc(m+m))).  Then
   q = (Suc(Suc 0)) * (Suc(Suc...))? messy.  Cleanest: q = Suc(q-1); if q-1 odd
   (= Suc(m+m)) then q = Suc(Suc(m+m)) = (Suc m)+(Suc m) -> dvd 2 q witness ... *)
val () = out "QODD_BEGIN\n";

(* mult_Suc on ctxtSub : (Suc m)*n = n + m*n *)
val mult_Suc_vSub = varify mult_Suc;
fun multSucS2_at (mt, nt) = beta_norm (Drule.infer_instantiate ctxtSub
      [(("m",0), ctermSub mt),(("n",0), ctermSub nt)] mult_Suc_vSub);

(* oeq (mult 2 m)(add m m) :  2*m = m + 1*m = m + m. *)
fun two_mult_m m =
  let
    val ms = multSucS2_at (suc ZeroC, m);     (* (Suc(Suc 0))*m = m + (Suc 0)*m *)
    val m1 = mult1lS2_at m;                    (* (Suc 0)*m = m *)
    val cr = add_cong_rS2 (m, mult (suc ZeroC) m, m) m1;  (* m + (Suc 0)*m = m + m *)
  in oeq_trans OF [ms, cr] end;               (* (Suc(Suc 0))*m = m + m *)

(* le 3 q  (= lt 2 q) is given as hle3.  prime2_div_atS, etc. on ctxtS2. *)
fun q_is_odd qT hPrime hle3 =
  let
    val dT = sub qT oneC;
    val em = parity_at dT;     (* Disj (evenEx dT)(oddEx dT) *)
    val goalEx = mkEx (Abs("m", natT, oeq dT (add (Bound 0) (Bound 0))));
    (* even case : directly the goal. *)
    val caseEven = Thm.implies_intr (ctermSub (jT (evenExT dT))) (Thm.assume (ctermSub (jT (evenExT dT))));
    (* odd case : sub q 1 = Suc(m+m).  Need q = Suc(Suc(Suc p)) (from hle3) to relate.
       From q = Suc(Suc(Suc p)) we get sub q 1 = Suc(Suc p), so Suc(Suc p) = Suc(m+m) -> Suc p = m+m.
       Then q = Suc(Suc(Suc p)) = Suc(Suc(Suc(m+m))) = (Suc(Suc 0))*(Suc m)?? Let's just build
       q = (Suc m)+(Suc m)+? No: q = Suc(Suc(Suc(m+m))).  Hmm q is ODD-q-1 => q even:
       q = Suc(sub q 1) ? We don't have a clean Suc(sub q 1)=q.  Use: q = Suc(Suc(Suc p)),
       and sub q 1 = Suc(Suc p) odd => Suc(Suc p) = Suc(m+m) => Suc p = m+m =>
       q = Suc(Suc(Suc p)) = Suc(Suc(Suc(m+m))).
       (Suc m)+(Suc m) = Suc(Suc(m+m)), so q = Suc((Suc m)+(Suc m)) -- that's odd, NOT 2*(..).
       So q ODD when q-1 EVEN, q EVEN when q-1 ODD.  q-1 odd => q even => 2|q.  q = Suc(Suc(Suc(m+m))).
       2 | q :  q = (Suc(Suc 0)) * k.  q = Suc(Suc(Suc(m+m)))... is this 2*(?): 
       Suc(Suc(Suc(m+m))) = (m+m)+3, even iff 3 even -- NO.  Wait recompute:
       q-1 = Suc(m+m) (odd).  q = q-1 + 1 = Suc(m+m)+1 = Suc(Suc(m+m)) = (Suc m)+(Suc m) = 2*(Suc m)/...
       (Suc m)+(Suc m) IS 2*(Suc m): two_mult_m (Suc m) : 2*(Suc m) = (Suc m)+(Suc m).
       And (Suc m)+(Suc m) = Suc(Suc(m+m)) = Suc(q-1) = q.  GOOD : q = 2*(Suc m). *)
    val caseOddBody =
      let
        val odAbs = Abs("m", natT, oeq dT (suc (add (Bound 0) (Bound 0))));
        fun body mW (hodd : thm) =     (* hodd : sub q 1 = Suc(m + m) *)
          let
            (* q = Suc(sub q 1) :  need oeq q (Suc (sub q 1)).  From q = Suc(Suc(Suc p)),
               sub q 1 = Suc(Suc p), Suc(sub q 1) = Suc(Suc(Suc p)) = q.
               We get this via hle3 -> q=Suc(Suc(Suc p)); sub q 1 = Suc(Suc p) [d_eq]. *)
            val threeT = suc (suc (suc ZeroC));
            val leAbs2 = Abs("p", natT, oeq qT (add threeT (Bound 0)));
            fun innerP pW (hqp : thm) =
              let
                val e1 = addSucS2_at (suc (suc ZeroC), pW);
                val e2 = addSucS2_at (suc ZeroC, pW);
                val e3 = addSucS2_at (ZeroC, pW);
                val e4 = add0S2_at pW;
                val add1p = oeq_trans OF [e3, Suc_cong OF [e4]];
                val add2p = oeq_trans OF [e2, Suc_cong OF [add1p]];
                val step  = oeq_trans OF [e1, Suc_cong OF [add2p]];
                val q_eq = oeq_trans OF [hqp, step];          (* q = Suc(Suc(Suc p)) *)
                val d_eq =
                  let
                    val zF = Free("zqo", natT)
                    val Pz = Term.lambda zF (oeq (sub zF oneC)(sub (suc (suc (suc pW))) oneC))
                    val sub_rw = substPredS2 (Pz, suc (suc (suc pW)), qT) (oeq_sym OF [q_eq])
                                   (oeqreflS2_at (sub (suc (suc (suc pW))) oneC));
                    val ss = subSSS2_at (suc (suc pW), ZeroC);
                    val n0 = subN0S2_at (suc (suc pW));
                  in oeq_trans OF [oeq_trans OF [sub_rw, ss], n0] end;  (* sub q 1 = Suc(Suc p) *)
                (* Suc(sub q 1) = q :  Suc(Suc(Suc p)) = q. *)
                val Sd_q = oeq_trans OF [Suc_cong OF [d_eq], oeq_sym OF [q_eq]];  (* Suc(sub q 1) = q *)
                (* hodd : sub q 1 = Suc(m+m) ; so Suc(sub q 1) = Suc(Suc(m+m)) = (Suc m)+(Suc m). *)
                val Sd = Suc_cong OF [hodd];               (* Suc(sub q 1) = Suc(Suc(m+m)) *)
                (* (Suc m)+(Suc m) = Suc(Suc(m+m)) : addSuc + addSr *)
                val aS  = addSucS2_at (mW, suc mW);        (* (Suc m)+(Suc m) = Suc(m + Suc m) *)
                val aSr = addSrS2_at (mW, mW);             (* m + Suc m = Suc(m+m) *)
                val SmSm = oeq_trans OF [aS, Suc_cong OF [aSr]];  (* (Suc m)+(Suc m) = Suc(Suc(m+m)) *)
                (* q = Suc(sub q 1) = Suc(Suc(m+m)) = (Suc m)+(Suc m) *)
                val q_SmSm = oeq_trans OF [oeq_sym OF [Sd_q], oeq_trans OF [Sd, oeq_sym OF [SmSm]]];
                            (* q = (Suc m)+(Suc m) *)
                (* 2*(Suc m) = (Suc m)+(Suc m) ; so q = 2*(Suc m) -> dvd 2 q witness (Suc m). *)
                val tm = two_mult_m (suc mW);              (* (Suc(Suc 0))*(Suc m) = (Suc m)+(Suc m) *)
                val q_2Sm = oeq_trans OF [q_SmSm, oeq_sym OF [tm]];  (* q = (Suc(Suc 0))*(Suc m) *)
                val dvd2q = dvd_introSub (suc (suc ZeroC), qT, suc mW) q_2Sm;  (* dvd 2 q *)
                (* prime2 q : 2 | q -> 2=1 \/ 2=q.  Both impossible. *)
                val disj = prime2_div_atS (qT, suc (suc ZeroC)) hPrime dvd2q;  (* Disj (oeq 2 1)(oeq 2 q) *)
                val case21 =     (* oeq 2 1 -> Suc(Suc 0)=Suc 0 -> Suc 0 = 0 -> False *)
                  let
                    val h = Thm.assume (ctermSub (jT (oeq (suc (suc ZeroC)) (suc ZeroC))));
                    val inj = Suc_inj_atSub (suc ZeroC, ZeroC) OF [h];   (* Suc 0 = 0 *)
                  in Thm.implies_intr (ctermSub (jT (oeq (suc (suc ZeroC)) (suc ZeroC))))
                       ((Suc_neq_Zero_atSub ZeroC) OF [inj]) end;
                val case2q =     (* oeq 2 q -> q = Suc(Suc(Suc p)) -> Suc(Suc 0)=Suc(Suc(Suc p)) -> 0=Suc p -> False *)
                  let
                    val h = Thm.assume (ctermSub (jT (oeq (suc (suc ZeroC)) qT)));
                    val h2 = oeq_trans OF [h, q_eq];   (* Suc(Suc 0) = Suc(Suc(Suc p)) *)
                    val i1 = Suc_inj_atSub (suc ZeroC, suc (suc pW)) OF [h2];  (* Suc 0 = Suc(Suc p) *)
                    val i2 = Suc_inj_atSub (ZeroC, suc pW) OF [i1];           (* 0 = Suc p *)
                  in Thm.implies_intr (ctermSub (jT (oeq (suc (suc ZeroC)) qT)))
                       ((Suc_neq_Zero_atSub pW) OF [oeq_sym OF [i2]]) end;
                val fls = disjE_elimSub (oeq (suc (suc ZeroC))(suc ZeroC), oeq (suc (suc ZeroC)) qT, oFalseC)
                            disj case21 case2q;   (* oFalse *)
              in Thm.implies_elim (oFalse_elimSub_at goalEx) fls end;   (* goalEx (ex falso) *)
            val r = exESub_elim (leAbs2, goalEx) hle3 "pp2" innerP;
          in r end;
      in exESub_elim (odAbs, goalEx) (Thm.assume (ctermSub (jT (oddExT dT)))) "modd" body end;
    val caseOddImp = Thm.implies_intr (ctermSub (jT (oddExT dT))) caseOddBody;
  in disjE_elimSub (evenExT dT, oddExT dT, goalEx) em caseEven caseOddImp end;

val () = out "QODD_OK\n";

(* ============================================================================
   THE KEY LEMMA  (First Supplement, hard/converse direction) :
     p1m4_key : prime2 q ==> lt 2 q ==> ~(dvd q x) ==> cong q (mult x x)(sub q 1)
                  ==> (?t. oeq q (add (mult 4 t) 1))
   q is an odd prime, x^2 == -1 mod q  ==>  q == 1 (mod 4).
   ============================================================================ *)
val () = out "KEY_BEGIN\n";

(* helper : oeq (mult 4 t)(add (add t t)(add t t))   (4t = 2t + 2t) *)
fun four_t t =
  let
    (* mult 4 t = t + mult 3 t = t + (t + mult 2 t) = t + (t + (t + mult 1 t)) = t+(t+(t+(t+mult 0 t)))
       Build via repeated mult_Suc. *)
    val m4 = multSucS2_at (suc (suc (suc ZeroC)), t);  (* (Suc 3)*t = t + 3*t  (4*t) *)
    val m3 = multSucS2_at (suc (suc ZeroC), t);        (* 3*t = t + 2*t *)
    val m2 = multSucS2_at (suc ZeroC, t);              (* 2*t = t + 1*t *)
    val m1 = multSucS2_at (ZeroC, t);                  (* 1*t = t + 0*t *)
    val m0 = mult0lSub_at t handle _ => (beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] (varify mult_0)));
                                                       (* 0*t = 0 *)
    (* 1*t = t + 0 = t *)
    val one_t = oeq_trans OF [m1, oeq_trans OF [add_cong_rS2 (t, mult ZeroC t, ZeroC) m0, add0rS2_at t]];
                                                       (* 1*t = t *)
    (* 2*t = t + 1*t = t + t *)
    val two_t = oeq_trans OF [m2, add_cong_rS2 (t, mult (suc ZeroC) t, t) one_t]; (* 2*t = t + t *)
    (* 3*t = t + 2*t = t + (t+t) *)
    val three_t = oeq_trans OF [m3, add_cong_rS2 (t, mult (suc (suc ZeroC)) t, add t t) two_t];
                                                       (* 3*t = t + (t+t) *)
    (* 4*t = t + 3*t = t + (t + (t+t)) *)
    val four_t0 = oeq_trans OF [m4, add_cong_rS2 (t, mult (suc (suc (suc ZeroC))) t, add t (add t t)) three_t];
                                                       (* 4*t = t + (t + (t+t)) *)
    (* t + (t + (t+t)) = (t+t)+(t+t)  via add_assoc sym *)
    val reassoc = addassocS2_at (t, t, add t t);       (* (t+t)+(t+t) = t+(t+(t+t)) *)
  in oeq_trans OF [four_t0, oeq_sym OF [reassoc]] end; (* 4*t = (t+t)+(t+t) *)

val p1m4_key =
  let
    val qF = Free("q", natT);
    val xF = Free("x", natT);
    val HprimeP = jT (prime2 qF);                       val Hprime = Thm.assume (ctermSub HprimeP);
    val Hle3P   = jT (lt (suc (suc ZeroC)) qF);          val Hle3   = Thm.assume (ctermSub Hle3P);
    val HndvdP  = jT (neg (dvd qF xF));                  val Hndvd  = Thm.assume (ctermSub HndvdP);
    val HsqP    = jT (cong qF (mult xF xF)(sub qF oneC));val Hsq    = Thm.assume (ctermSub HsqP);
    val dT = sub qF oneC;
    val goalEx = mkEx (Abs("t", natT, oeq qF (add (mult fourC (Bound 0)) oneC)));

    (* (A) q = Suc(Suc(Suc p))  and  sub q 1 = Suc(Suc p)  and  Suc(sub q 1) = q   from Hle3. *)
    val threeT = suc (suc (suc ZeroC));
    val leAbsTop = Abs("p", natT, oeq qF (add threeT (Bound 0)));
    fun mainAfterP pW (hqp : thm) =
      let
        (* add 3 p = Suc(Suc(Suc p)) :  e1 : add 3 p = Suc(add 2 p) ;
           add 2 p = Suc(Suc p) [e2/e3/e4] ; Suc_cong lifts ; trans. *)
        val e1 = addSucS2_at (suc (suc ZeroC), pW);   (* add 3 p = Suc(add 2 p) *)
        val e2 = addSucS2_at (suc ZeroC, pW);         (* add 2 p = Suc(add 1 p) *)
        val e3 = addSucS2_at (ZeroC, pW);             (* add 1 p = Suc(add 0 p) *)
        val e4 = add0S2_at pW;                        (* add 0 p = p *)
        val add1p = oeq_trans OF [e3, Suc_cong OF [e4]];          (* add 1 p = Suc p *)
        val add2p = oeq_trans OF [e2, Suc_cong OF [add1p]];        (* add 2 p = Suc(Suc p) *)
        val stp   = oeq_trans OF [e1, Suc_cong OF [add2p]];        (* add 3 p = Suc(Suc(Suc p)) *)
        val q_eq = oeq_trans OF [hqp, stp];               (* q = Suc(Suc(Suc p)) *)
        val d_eq =
          let
            val zF = Free("zk", natT)
            val Pz = Term.lambda zF (oeq (sub zF oneC)(sub (suc (suc (suc pW))) oneC))
            val sub_rw = substPredS2 (Pz, suc (suc (suc pW)), qF) (oeq_sym OF [q_eq])
                           (oeqreflS2_at (sub (suc (suc (suc pW))) oneC));
            val ss = subSSS2_at (suc (suc pW), ZeroC);
            val n0 = subN0S2_at (suc (suc pW));
          in oeq_trans OF [oeq_trans OF [sub_rw, ss], n0] end;  (* sub q 1 = Suc(Suc p) *)
        val Sd_q = oeq_trans OF [Suc_cong OF [d_eq], oeq_sym OF [q_eq]];  (* Suc(sub q 1) = q *)

        (* (B) hd2 : cong q (mult d d) 1  via neg1_sq at q1 = Suc p. *)
        val hd2 = neg1_sq_at (qF, suc pW) q_eq;       (* cong q (mult (sub q 1)(sub q 1)) 1 *)

        (* (C) q odd : ?m. sub q 1 = m+m. *)
        val odd_ex = q_is_odd qF Hprime Hle3;          (* Ex m. oeq (sub q 1)(add m m) *)
        val mAbs = Abs("m", natT, oeq dT (add (Bound 0)(Bound 0)));
        fun afterM mW (hm : thm) =                     (* hm : sub q 1 = m + m *)
          let
            (* parity of m *)
            val emM = parity_at mW;                    (* Disj (evenEx m)(oddEx m) *)
            (* even m -> goal *)
            val caseEvenBody =
              let
                val evAbs = Abs("t", natT, oeq mW (add (Bound 0)(Bound 0)));
                fun evBody tW (ht : thm) =             (* ht : m = t + t *)
                  let
                    (* sub q 1 = m+m = (t+t)+(t+t) *)
                    val zF = Free("zev", natT)
                    val Pz = Term.lambda zF (oeq dT (add zF zF))
                    val d_tt = substPredS2 (Pz, mW, add tW tW) ht hm;   (* sub q 1 = (t+t)+(t+t) *)
                    (* q = Suc(sub q 1) = Suc((t+t)+(t+t)) *)
                    val q_S = oeq_sym OF [Sd_q];        (* q = Suc(sub q 1) *)
                    val q_Stt = oeq_trans OF [q_S, Suc_cong OF [d_tt]];  (* q = Suc((t+t)+(t+t)) *)
                    (* add (mult 4 t) 1 = Suc(mult 4 t) = Suc((t+t)+(t+t)) *)
                    val ft = four_t tW;                 (* mult 4 t = (t+t)+(t+t) *)
                    val a1 = addSrS2_at (mult fourC tW, ZeroC);  (* add (mult 4 t)(Suc 0) = Suc(add (mult 4 t) 0) *)
                    val a0 = add0rS2_at (mult fourC tW);         (* add (mult 4 t) 0 = mult 4 t *)
                    val add4t1 = oeq_trans OF [a1, Suc_cong OF [a0]];   (* add (mult 4 t) 1 = Suc(mult 4 t) *)
                    val add4t1_tt = oeq_trans OF [add4t1, Suc_cong OF [ft]];  (* add (mult 4 t) 1 = Suc((t+t)+(t+t)) *)
                    (* q = add (mult 4 t) 1 :  q = Suc((t+t)+(t+t)) = add (mult 4 t) 1 *)
                    val q_eq_goal = oeq_trans OF [q_Stt, oeq_sym OF [add4t1_tt]];  (* q = add (mult 4 t) 1 *)
                    val gAbs = Abs("t", natT, oeq qF (add (mult fourC (Bound 0)) oneC));
                  in exISub_at gAbs tW q_eq_goal end;  (* goalEx *)
              in exESub_elim (evAbs, goalEx) (Thm.assume (ctermSub (jT (evenExT mW)))) "te" evBody end;
            val caseEvenImp = Thm.implies_intr (ctermSub (jT (evenExT mW))) caseEvenBody;
            (* odd m -> contradiction -> ex falso -> goal *)
            val caseOddBody =
              let
                val odAbs = Abs("k", natT, oeq mW (suc (add (Bound 0)(Bound 0))));
                fun odBody kW (hk : thm) =             (* hk : m = Suc(k+k) *)
                  let
                    (* x2j at j=m : cong q (pow x (m+m))(pow (sub q 1) m) *)
                    val xm = x2j_at (qF, xF, mW) Hsq;  (* cong q (pow x (m+m))(pow d m) *)
                    (* apm1 : cong q (pow x (sub q 1)) 1 ; rewrite sub q 1 -> m+m (hm) so pow x (m+m). *)
                    val ap = apm1_atSub (qF, xF) Hprime Hndvd;  (* cong q (pow x (sub q 1)) 1 *)
                    (* pow x (sub q 1) = pow x (m+m) via hm *)
                    val px_eq = pow_cong_argSub (xF, dT, add mW mW) hm;  (* pow x (sub q 1) = pow x (m+m) *)
                    val zF = Free("zap", natT)
                    val Pz = Term.lambda zF (cong qF zF oneC)
                    val ap2 = substPredS2 (Pz, pow xF dT, pow xF (add mW mW)) px_eq ap;  (* cong q (pow x (m+m)) 1 *)
                    (* chain : cong q (pow d m) 1   [xm sym ; ap2] *)
                    val xm_sym = cong_sym_atSub (qF, pow xF (add mW mW), pow dT mW) xm;  (* cong q (pow d m)(pow x (m+m)) *)
                    val pdm_1 = cong_trans_atSub (qF, pow dT mW, pow xF (add mW mW), oneC) xm_sym ap2;
                                (* cong q (pow d m) 1 *)
                    (* dpow_odd at (q, d, k) : cong q (pow d (Suc(k+k))) d ; rewrite Suc(k+k) <- m (hk). *)
                    val dodd = dpow_odd_at (qF, dT, kW) hd2;   (* cong q (pow d (Suc(k+k))) d *)
                    val zF2 = Free("zdo", natT)
                    val Pz2 = Term.lambda zF2 (cong qF (pow dT zF2) dT)
                    val dodd_m = substPredS2 (Pz2, suc (add kW kW), mW) (oeq_sym OF [hk]) dodd;
                                (* cong q (pow d m) d *)
                    (* cong q d (pow d m) [sym] ; cong q (pow d m) 1  -> cong q d 1 *)
                    val dm_sym = cong_sym_atSub (qF, pow dT mW, dT) dodd_m;   (* cong q d (pow d m) *)
                    val d_1 = cong_trans_atSub (qF, dT, pow dT mW, oneC) dm_sym pdm_1;  (* cong q d 1 *)
                    (* contradiction *)
                    val fls = cong_d1_false qF Hle3 d_1;   (* oFalse *)
                  in Thm.implies_elim (oFalse_elimSub_at goalEx) fls end;
              in exESub_elim (odAbs, goalEx) (Thm.assume (ctermSub (jT (oddExT mW)))) "ko" odBody end;
            val caseOddImp = Thm.implies_intr (ctermSub (jT (oddExT mW))) caseOddBody;
          in disjE_elimSub (evenExT mW, oddExT mW, goalEx) emM caseEvenImp caseOddImp end;
        val viaM = exESub_elim (mAbs, goalEx) odd_ex "mO" afterM;
      in viaM end;
    val core = exESub_elim (leAbsTop, goalEx) Hle3 "pTop" mainAfterP;

    val d1 = Thm.implies_intr (ctermSub HsqP) core;
    val d2 = Thm.implies_intr (ctermSub HndvdP) d1;
    val d3 = Thm.implies_intr (ctermSub Hle3P) d2;
    val d4 = Thm.implies_intr (ctermSub HprimeP) d3;
  in varify d4 end;

val () = out "KEY_PROVED\n";

(* ---- validation : 0-hyp + aconv intended + soundness probes ---- *)
val qVk = Var (("q",0), natT);
val xVk = Var (("x",0), natT);
val p1m4_key_intended =
  Logic.mk_implies (jT (prime2 qVk),
    Logic.mk_implies (jT (lt (suc (suc ZeroC)) qVk),
      Logic.mk_implies (jT (neg (dvd qVk xVk)),
        Logic.mk_implies (jT (cong qVk (mult xVk xVk)(sub qVk oneC)),
          jT (mkEx (Abs("t", natT, oeq qVk (add (mult fourC (Bound 0)) oneC))))))));
val key_nhyp = length (Thm.hyps_of p1m4_key);
val key_aconv = (Thm.prop_of p1m4_key) aconv p1m4_key_intended;
val () = out ("KEY hyps=" ^ Int.toString key_nhyp ^ " aconv=" ^ Bool.toString key_aconv ^ "\n");

(* soundness probe 1 : needs the square hypothesis (cong q (x*x)(sub q 1)) *)
val probe_needs_sq =
  not ((Thm.prop_of p1m4_key) aconv
       Logic.mk_implies (jT (prime2 qVk),
         Logic.mk_implies (jT (lt (suc (suc ZeroC)) qVk),
           Logic.mk_implies (jT (neg (dvd qVk xVk)),
             jT (mkEx (Abs("t", natT, oeq qVk (add (mult fourC (Bound 0)) oneC))))))));
(* soundness probe 2 : conclusion is genuinely "?t. q = 4t+1", not "?t. q = 4t" *)
val probe_nontrivial =
  not ((Thm.prop_of p1m4_key) aconv
       Logic.mk_implies (jT (prime2 qVk),
         Logic.mk_implies (jT (lt (suc (suc ZeroC)) qVk),
           Logic.mk_implies (jT (neg (dvd qVk xVk)),
             Logic.mk_implies (jT (cong qVk (mult xVk xVk)(sub qVk oneC)),
               jT (mkEx (Abs("t", natT, oeq qVk (mult fourC (Bound 0))))))))));

val () =
  if key_nhyp = 0 andalso key_aconv andalso probe_needs_sq andalso probe_nontrivial
  then out "P1M4_KEY_OK\n"
  else out ("P1M4_KEY_FAILED nhyp=" ^ Int.toString key_nhyp
            ^ " aconv=" ^ Bool.toString key_aconv
            ^ " psq=" ^ Bool.toString probe_needs_sq
            ^ " pnt=" ^ Bool.toString probe_nontrivial ^ "\n");

val () = out "PREFIX_DONE\n";

(* ============================================================================
   ndvd helpers : ~(p|1) and ~(p|b^n) from prime2 p + ~(p|b), then ~(p|x).
   These run on POW-CONTAINING dvd terms, so we need ctxtSub variants of
   euclid_lemma / dvd_le / lt_irrefl / dvd_cong_r / prime2_gt1 (the foundation
   named only ctxtS2 versions, which reject `pow`).
   ============================================================================ *)
val () = out "NDVD_HELPERS_BEGIN\n";

(* euclid_lemma on ctxtSub : prime2 p -> dvd p (a*b) -> Disj (dvd p a)(dvd p b) *)
fun euclid_atSub (pt, at, bt) hPrime hDvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("p",0), ctermSub pt), (("a",0), ctermSub at), (("b",0), ctermSub bt)] euclid_lemma_vS2)
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hDvd end;

(* dvd_cong_r on ctxtSub (pow-safe) : oeq x y -> dvd p x -> dvd p y *)
fun dvd_cong_rSub (pT, xT, yT) hxy hdvd =
  let
    val zF   = Free("z_dcS", natT);
    val Pabs = Term.lambda zF (dvd pT zF);
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("a",0), ctermSub xT), (("b",0), ctermSub yT)] oeq_subst_vS2);
  in (inst OF [hxy]) OF [hdvd] end;

(* dvd_le on ctxtSub : dvd d n -> (oeq n 0 ==> oFalse) -> le d n *)
fun dvd_le_atSub (dT, nT) hdvd hnzMeta =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("d",0), ctermSub dT), (("n",0), ctermSub nT)] dvd_le_vS)
  in Thm.implies_elim (Thm.implies_elim inst hdvd) hnzMeta end;

(* lt_irrefl on ctxtSub *)
fun lt_irrefl_atSub nT h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub nT)] lt_irrefl_vS)
  in Thm.implies_elim inst h end;

(* prime2_gt1 on ctxtSub *)
fun prime2_gt1_atSub p hPrime =
  conjunct1_atSub (lt (suc ZeroC) p, mkForall (ppAbs p)) hPrime;

(* ndvd_one : prime2 p ==> ~(p | 1).   p|1 -> le p 1 [dvd_le] ; lt 1 p -> le 2 p ;
   le_trans 2 p 1 -> le 2 1 = lt 1 1 -> lt_irrefl. *)
fun ndvd_one (pF) Hprime =
  let
    val one1 = suc ZeroC;
    val hdvd1 = Thm.assume (ctermSub (jT (dvd pF one1)));     (* dvd p 1 *)
    (* 1 != 0 (meta) *)
    val nz1 = Thm.implies_intr (ctermSub (jT (oeq one1 ZeroC)))
                ((Suc_neq_Zero_atSub ZeroC) OF [Thm.assume (ctermSub (jT (oeq one1 ZeroC)))]);
    val le_p_1 = dvd_le_atS (pF, one1) hdvd1 nz1;            (* le p 1 *)
    val lt1p = prime2_gt1_atS pF Hprime;                     (* lt 1 p = le 2 p *)
    (* le 2 1 via le_trans 2 p 1 *)
    val le_2_1 = le_transS2_at (suc (suc ZeroC), pF, one1) lt1p le_p_1;  (* le 2 1 = lt 1 1 *)
    val fls = lt_irrefl_atS one1 le_2_1;                     (* oFalse  (le 2 1 = lt 1 1) *)
    val metaNe = Thm.implies_intr (ctermSub (jT (dvd pF one1))) fls;
  in impI_S2 (dvd pF one1, oFalseC) metaNe end;             (* ~(p|1) *)

(* ndvd_pow : prime2 p ==> ~(p|b) ==> !n. ~(p | b^n).  induction on n. *)
fun ndvd_pow_at (pF, bF, nT) Hprime Hndvd_b =
  let
    val zF = Free("zndp", natT);
    val Qpred = Term.lambda zF (neg (dvd pF (pow bF zF)));    (* %n. ~(p | b^n) *)
    val nInd = Free("n_ndp", natT);
    val ind = nat_induct_atS2 (Qpred, nT);
    (* base n=0 : b^0 = 1 ; ~(p|1) -> rewrite to ~(p|b^0) *)
    val base =
      let
        val pb0 = powZeroS2_at bF;                (* b^0 = 1 *)
        val nd1 = ndvd_one pF Hprime;             (* ~(p|1) *)
        val zc = Free("zb0", natT)
        val Pz = Term.lambda zc (neg (dvd pF zc))
      in substPredS2 (Pz, oneC, pow bF ZeroC) (oeq_sym OF [pb0]) nd1 end;  (* ~(p|b^0) *)
    (* step : ~(p|b^n) -> ~(p|b^(Sn)).  b^(Sn) = b*b^n.  p|b*b^n -> euclid -> p|b (contra Hndvd_b)
       or p|b^n (contra IH). *)
    val nF = Free("nstep_ndp", natT);
    val ihprop = jT (neg (dvd pF (pow bF nF)));
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        val hdvdSn = Thm.assume (ctermSub (jT (dvd pF (pow bF (suc nF)))));   (* p | b^(Sn) *)
        val pSn = powSucS2_at (bF, nF);           (* b^(Sn) = b*b^n *)
        val hdvd_bbn = dvd_cong_rSub (pF, pow bF (suc nF), mult bF (pow bF nF)) pSn hdvdSn;  (* p | b*b^n *)
        val disj = euclid_atSub (pF, bF, pow bF nF) Hprime hdvd_bbn;   (* Disj (p|b)(p|b^n) *)
        val caseB  = Thm.implies_intr (ctermSub (jT (dvd pF bF)))
                       (mp_S2 (dvd pF bF, oFalseC) Hndvd_b (Thm.assume (ctermSub (jT (dvd pF bF)))));
        val caseBn = Thm.implies_intr (ctermSub (jT (dvd pF (pow bF nF))))
                       (mp_S2 (dvd pF (pow bF nF), oFalseC) IH (Thm.assume (ctermSub (jT (dvd pF (pow bF nF))))));
        val fls = disjE_elimSub (dvd pF bF, dvd pF (pow bF nF), oFalseC) disj caseB caseBn;
        val metaNe = Thm.implies_intr (ctermSub (jT (dvd pF (pow bF (suc nF))))) fls;
      in impI_S2 (dvd pF (pow bF (suc nF)), oFalseC) metaNe end;     (* ~(p|b^(Sn)) *)
    val step1 = Thm.forall_intr (ctermSub nF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
  in Thm.implies_elim r1 step1 end;       (* ~(p | b^n)  at n = nT *)

(* ndvd_x : prime2 p ==> ~(p|a) ==> ~(p|b) ==> ~(p | a * b^(k+k)).
   euclid on a * b^(k+k) : p|a (contra) or p|b^(k+k) (ndvd_pow contra). *)
fun ndvd_x (pF, aF, bF, kkT) Hprime Hndvd_a Hndvd_b =
  let
    val xT = mult aF (pow bF kkT);
    val hdvdx = Thm.assume (ctermSub (jT (dvd pF xT)));      (* p | a*b^(k+k) *)
    val disj = euclid_atSub (pF, aF, pow bF kkT) Hprime hdvdx; (* Disj (p|a)(p|b^(k+k)) *)
    val ndvd_bk = ndvd_pow_at (pF, bF, kkT) Hprime Hndvd_b;  (* ~(p|b^(k+k)) *)
    val caseA  = Thm.implies_intr (ctermSub (jT (dvd pF aF)))
                   (mp_S2 (dvd pF aF, oFalseC) Hndvd_a (Thm.assume (ctermSub (jT (dvd pF aF)))));
    val caseBk = Thm.implies_intr (ctermSub (jT (dvd pF (pow bF kkT))))
                   (mp_S2 (dvd pF (pow bF kkT), oFalseC) ndvd_bk (Thm.assume (ctermSub (jT (dvd pF (pow bF kkT))))));
    val fls = disjE_elimSub (dvd pF aF, dvd pF (pow bF kkT), oFalseC) disj caseA caseBk;
    val metaNe = Thm.implies_intr (ctermSub (jT (dvd pF xT))) fls;
  in impI_S2 (dvd pF xT, oFalseC) metaNe end;                (* ~(p | a*b^(k+k)) *)

val () = out "NDVD_HELPERS_OK\n";
fun cong_add_rcancel (pT, U, V, W) hcong =
  let
    val goalC = cong pT U V;
    val dL = congL pT (add U W)(add V W);   (* Ex k. (V+W) = (U+W) + p*k *)
    val dR = congR pT (add U W)(add V W);   (* Ex k. (U+W) = (V+W) + p*k *)
    val caseL =
      let
        val hL = Thm.assume (ctermSub (jT dL));
        val lAbs = Abs("k", natT, oeq (add V W)(add (add U W)(mult pT (Bound 0))));
        val r = exESub_elim (lAbs, goalC) hL "kLc"
                  (fn kW => fn hk =>     (* hk : (V+W) = (U+W)+p*k *)
                     let
                       val cUW = addcommSub_at (U, W);                          (* U+W = W+U *)
                       val rw1 = add_cong_lS (add U W, add W U, mult pT kW) cUW; (* (U+W)+p*k = (W+U)+p*k *)
                       val asc = addassocSub_at (W, U, mult pT kW);             (* (W+U)+p*k = W+(U+p*k) *)
                       val rhs_eq = oeq_trans OF [rw1, asc];                    (* (U+W)+p*k = W+(U+p*k) *)
                       val cVW = addcommSub_at (V, W);                          (* V+W = W+V *)
                       val chain = oeq_trans OF [oeq_sym OF [cVW], oeq_trans OF [hk, rhs_eq]];  (* W+V = W+(U+p*k) *)
                       val canc  = add_left_cancel_atS (W, V, add U (mult pT kW)) chain;        (* V = U+p*k *)
                       val congLthm = exISub_at (Abs("k", natT, oeq V (add U (mult pT (Bound 0))))) kW canc;
                     in disjI1Sub_at (congL pT U V, congR pT U V) congLthm end)
      in Thm.implies_intr (ctermSub (jT dL)) r end;
    val caseR =
      let
        val hR = Thm.assume (ctermSub (jT dR));
        val rAbs = Abs("k", natT, oeq (add U W)(add (add V W)(mult pT (Bound 0))));
        val r = exESub_elim (rAbs, goalC) hR "kRc"
                  (fn kW => fn hk =>     (* hk : (U+W) = (V+W)+p*k *)
                     let
                       val cVW = addcommSub_at (V, W);
                       val rw1 = add_cong_lS (add V W, add W V, mult pT kW) cVW;
                       val asc = addassocSub_at (W, V, mult pT kW);
                       val rhs_eq = oeq_trans OF [rw1, asc];
                       val cUW = addcommSub_at (U, W);
                       val chain = oeq_trans OF [oeq_sym OF [cUW], oeq_trans OF [hk, rhs_eq]];
                       val canc  = add_left_cancel_atS (W, U, add V (mult pT kW)) chain;  (* U = V+p*k *)
                       val congRthm = exISub_at (Abs("k", natT, oeq U (add V (mult pT (Bound 0))))) kW canc;
                     in disjI2Sub_at (congL pT U V, congR pT U V) congRthm end)
      in Thm.implies_intr (ctermSub (jT dR)) r end;
  in disjE_elimSub (dL, dR, goalC) hcong caseL caseR end;
fun neg1_not_qr_body (pF, xF) Hprime Hle3 Hndvd Hsq kW (hpk : thm) =
  (* hpk : oeq p (add (add (add (add k k) k) k) 3)  =  p = ((((k+k)+k)+k)+3)
     Hndvd : ~(p | x)   (x the QR-witness base)
     Hsq   : cong p (mult x x)(sub p 1)
     RESULT : oFalse  ("x^2 == -1 mod p" is impossible for p == 3 (mod 4)). *)
  let
    val dT = sub pF oneC;
    val mT = suc (add kW kW);                 (* m = Suc(k+k) *)
    val fourkT = add (add (add kW kW) kW) kW; (* ((k+k)+k)+k  = 4k *)

    (* (A) p = Suc(Suc(Suc(4k)))  from hpk. *)
    val e1 = addSucS2_at (suc (suc ZeroC), fourkT);
    val e2 = addSucS2_at (suc ZeroC, fourkT);
    val e3 = addSucS2_at (ZeroC, fourkT);
    val e4 = add0S2_at fourkT;
    val add1 = oeq_trans OF [e3, Suc_cong OF [e4]];
    val add2 = oeq_trans OF [e2, Suc_cong OF [add1]];
    val add3 = oeq_trans OF [e1, Suc_cong OF [add2]];           (* add 3 4k = Suc(Suc(Suc 4k)) *)
    val acomm = addcommS_at (fourkT, suc (suc (suc ZeroC)));    (* add 4k 3 = add 3 4k *)
    val p_4k3 = oeq_trans OF [hpk, acomm];                      (* p = add 3 4k *)
    val q_eq  = oeq_trans OF [p_4k3, add3];                     (* p = Suc(Suc(Suc 4k)) *)

    (* (B) hd2 : cong p (d*d) 1  via neg1_sq at q1 = Suc 4k. *)
    val q1T = suc fourkT;                       (* q1 = Suc 4k *)
    val hd2 = neg1_sq_at (pF, q1T) q_eq;        (* cong p (mult d d) 1 *)

    (* (C) sub p 1 = Suc(Suc 4k) (d_eq) ; Suc(sub p 1) = p (Sd_q) ; sub p 1 = m+m (subp1_mm). *)
    val d_eq =
      let
        val zF = Free("znq", natT)
        val Pz = Term.lambda zF (oeq (sub zF oneC)(sub (suc (suc (suc fourkT))) oneC))
        val sub_rw = substPredS2 (Pz, suc (suc (suc fourkT)), pF) (oeq_sym OF [q_eq])
                       (oeqreflS2_at (sub (suc (suc (suc fourkT))) oneC));
        val ss = subSSS2_at (suc (suc fourkT), ZeroC);
        val n0 = subN0S2_at (suc (suc fourkT));
      in oeq_trans OF [oeq_trans OF [sub_rw, ss], n0] end;      (* sub p 1 = Suc(Suc 4k) *)
    val Sd_q = oeq_trans OF [Suc_cong OF [d_eq], oeq_sym OF [q_eq]];  (* Suc(sub p 1) = p *)
    val mm_S =
      let
        val aS  = addSucS2_at (add kW kW, suc (add kW kW));
        val aSr = addSrS2_at (add kW kW, add kW kW);
        val innr= Suc_cong OF [aSr];
      in oeq_trans OF [aS, innr] end;                           (* m+m = Suc(Suc((k+k)+(k+k))) *)
    val reassoc = addassocS_at (add kW kW, kW, kW);             (* ((k+k)+k)+k = (k+k)+(k+k) *)
    val kk_4k   = oeq_sym OF [reassoc];                         (* (k+k)+(k+k) = 4k *)
    val mm_4k   = oeq_trans OF [mm_S, Suc_cong OF [Suc_cong OF [kk_4k]]];  (* m+m = Suc(Suc 4k) *)
    val subp1_mm = oeq_trans OF [d_eq, oeq_sym OF [mm_4k]];     (* sub p 1 = m+m *)

    (* (D) cong p (pow d m) d   via dpow_odd at (p, d, k). *)
    val dodd = dpow_odd_at (pF, dT, kW) hd2;            (* cong p (pow d (Suc(k+k))) d = cong p (pow d m) d *)

    (* (E) cong p (pow x (m+m))(pow d m)   via x2j at j = m. *)
    val xm = x2j_at (pF, xF, mT) Hsq;                   (* cong p (pow x (m+m))(pow d m) *)

    (* (F) apm1 : cong p (pow x (sub p 1)) 1 ; rewrite sub p 1 -> m+m. *)
    val ap = apm1_atSub (pF, xF) Hprime Hndvd;          (* cong p (pow x (sub p 1)) 1 *)
    val zF = Free("zap_nq", natT)
    val Pz = Term.lambda zF (cong pF (pow xF zF) oneC)
    val ap2 = substPredS2 (Pz, sub pF oneC, add mT mT) subp1_mm ap;  (* cong p (pow x (m+m)) 1 *)

    (* (G) chain : cong p (pow d m) 1 *)
    val xm_sym = cong_sym_atSub (pF, pow xF (add mT mT), pow dT mT) xm;
    val pdm_1  = cong_trans_atSub (pF, pow dT mT, pow xF (add mT mT), oneC) xm_sym ap2;

    (* (H) cong p d 1 *)
    val dm_sym = cong_sym_atSub (pF, pow dT mT, dT) dodd;
    val d_1    = cong_trans_atSub (pF, dT, pow dT mT, oneC) dm_sym pdm_1;  (* cong p d 1 *)

    (* (I) contradiction *)
    val fls = cong_d1_false pF Hle3 d_1;   (* oFalse *)
  in fls end;

(* ============================================================================
   ***  THE KEY ONLY-IF LEMMA  ***
   key_onlyif : prime2 p ==> (Ex k. p = (k+k+k+k)+3) ==> dvd p (mult a a + mult b b)
                  ==> Conj (dvd p a)(dvd p b)
   ============================================================================ *)
val () = out "KEYMAIN_BEGIN\n";

(* ndvd of product b*b from ndvd b via euclid *)
fun ndvd_sq (pF, bF) Hprime Hndvd_b =
  let
    val hdvd = Thm.assume (ctermSub (jT (dvd pF (mult bF bF))));
    val disj = euclid_atS (pF, bF, bF) Hprime hdvd;
    val caseB = Thm.implies_intr (ctermSub (jT (dvd pF bF)))
                  (mp_atS2 (dvd pF bF, oFalseC) Hndvd_b (Thm.assume (ctermSub (jT (dvd pF bF)))));
    val fls = disjE_elimSub (dvd pF bF, dvd pF bF, oFalseC) disj caseB caseB;
    val metaNe = Thm.implies_intr (ctermSub (jT (dvd pF (mult bF bF)))) fls;
  in impI_atS2 (dvd pF (mult bF bF), oFalseC) metaNe end;

val key_onlyif =
  let
    val pF = Free("p", natT); val aF = Free("a", natT); val bF = Free("b", natT);
    val aaT = mult aF aF; val bbT = mult bF bF; val dT = sub pF oneC;
    val NT = add aaT bbT;   (* a^2 + b^2 *)

    val HprimeP = jT (prime2 pF);   val Hprime = Thm.assume (ctermSub HprimeP);
    val H4k3body = Abs("k", natT, oeq pF (add (add (add (add (Bound 0)(Bound 0))(Bound 0))(Bound 0)) (suc (suc (suc ZeroC)))));
    val H4k3P  = jT (mkEx H4k3body);  val H4k3 = Thm.assume (ctermSub H4k3P);
    val HdvdNP = jT (dvd pF NT);    val HdvdN = Thm.assume (ctermSub HdvdNP);

    val goalConj = mkConj (dvd pF aF)(dvd pF bF);

    (* cong p (a^2+b^2) 0 from dvd *)
    val Hcong0 = dvd_imp_cong_zero_at (pF, NT) HdvdN;   (* cong p (a^2+b^2) 0 *)

    (* exE over (Ex k. p = 4k+3) : inside, kW + hpk : p = ((((k+k)+k)+k)+3) *)
    fun afterK kW (hpk : thm) =
      let
        val kkT = add kW kW;                       (* k+k *)
        val mT  = suc kkT;                         (* m = Suc(k+k) *)
        val ddT = suc (suc kkT);                   (* Suc(Suc(kk)) -- NB this is NOT Suc(Suc(kk+kk)); fix below *)
        val fourkT = add (add (add kW kW) kW) kW;  (* ((k+k)+k)+k = 4k *)

        (* p = Suc(Suc(Suc 4k)) (q_eq) *)
        val e1 = addSucS2_at (suc (suc ZeroC), fourkT);
        val e2 = addSucS2_at (suc ZeroC, fourkT);
        val e3 = addSucS2_at (ZeroC, fourkT);
        val e4 = add0S2_at fourkT;
        val ad1 = oeq_trans OF [e3, Suc_cong OF [e4]];
        val ad2 = oeq_trans OF [e2, Suc_cong OF [ad1]];
        val ad3 = oeq_trans OF [e1, Suc_cong OF [ad2]];      (* add 3 4k = Suc(Suc(Suc 4k)) *)
        val acomm = addcommS_at (fourkT, suc (suc (suc ZeroC)));   (* add 4k 3 = add 3 4k *)
        val p_4k3 = oeq_trans OF [hpk, acomm];                (* p = add 3 4k *)
        val q_eq  = oeq_trans OF [p_4k3, ad3];                (* p = Suc(Suc(Suc 4k)) *)

        (* 4k = kk+kk  (reassoc) ; p_eq : p = Suc(Suc(Suc(kk+kk))) *)
        val reassoc = addassocS_at (kkT, kW, kW);            (* ((k+k)+k)+k = (k+k)+(k+k) *)
        val q_eq_kk = oeq_trans OF [q_eq, Suc_cong OF [Suc_cong OF [Suc_cong OF [reassoc]]]];
                       (* p = Suc(Suc(Suc(kk+kk))) *)

        (* sub p 1 = m+m  (subp1_mm), m = Suc(k+k) ; using q_eq -> sub p 1 = Suc(Suc 4k) -> = m+m *)
        val d_eq =
          let
            val zF = Free("zkm", natT)
            val Pz = Term.lambda zF (oeq (sub zF oneC)(sub (suc (suc (suc fourkT))) oneC))
            val sub_rw = substPredS2 (Pz, suc (suc (suc fourkT)), pF) (oeq_sym OF [q_eq])
                           (oeqreflS2_at (sub (suc (suc (suc fourkT))) oneC));
            val ss = subSSS2_at (suc (suc fourkT), ZeroC);
            val n0 = subN0S2_at (suc (suc fourkT));
          in oeq_trans OF [oeq_trans OF [sub_rw, ss], n0] end;  (* sub p 1 = Suc(Suc 4k) *)
        val mm_S =
          let val aS = addSucS2_at (kkT, suc kkT)
              val aSr= addSrS2_at (kkT, kkT)
          in oeq_trans OF [aS, Suc_cong OF [aSr]] end;        (* m+m = Suc(Suc(kk+kk)) *)
        val ssfourk_eq = Suc_cong OF [Suc_cong OF [reassoc]]; (* Suc(Suc 4k) = Suc(Suc(kk+kk)) *)
        val subp1_mm = oeq_trans OF [oeq_trans OF [d_eq, ssfourk_eq], oeq_sym OF [mm_S]];
                       (* sub p 1 = m+m *)

        (* lt 2 p (= le 3 p) :  p = 3 + 4k  -> witness 4k *)
        val le3p = le_introS2 (suc (suc (suc ZeroC)), pF, fourkT) p_4k3;   (* le 3 p = lt 2 p *)
        val Hle3 = le3p;
        val () = out "KM_SETUP_OK\n";

        (* ============ prove dvd p a by contradiction ============ *)
        val dvd_pa =
          let
            val em = ex_middle_atSub (dvd pF aF);   (* Disj (dvd p a)(neg (dvd p a)) *)
            val caseYes = Thm.implies_intr (ctermSub (jT (dvd pF aF))) (Thm.assume (ctermSub (jT (dvd pF aF))));
            val caseNo =
              let
                val Hndvd_a = Thm.assume (ctermSub (jT (neg (dvd pF aF))));   (* Imp (dvd p a) oFalse *)
                (* derive ~(p|b) *)
                val Hndvd_b =
                  let
                    val hdvdb = Thm.assume (ctermSub (jT (dvd pF bF)));        (* dvd p b *)
                    val dvd_bb = dvd_mult_rightSub (pF, bF, bF) hdvdb;         (* dvd p (b*b) *)
                    (* commute a^2+b^2 -> b^2+a^2 *)
                    val comm = addcommSub_at (aaT, bbT);                       (* a^2+b^2 = b^2+a^2 *)
                    val dvd_baN = dvd_cong_rS (pF, NT, add bbT aaT) comm HdvdN; (* dvd p (b^2+a^2) *)
                    val dvd_aa = dvd_diff_atS (pF, bbT, aaT) dvd_bb dvd_baN;   (* dvd p (a*a) *)
                    val disj = euclid_atS (pF, aF, aF) Hprime dvd_aa;          (* Disj (dvd p a)(dvd p a) *)
                    val caseA = Thm.implies_intr (ctermSub (jT (dvd pF aF)))
                                  (mp_atS2 (dvd pF aF, oFalseC) Hndvd_a (Thm.assume (ctermSub (jT (dvd pF aF)))));
                    val fls = disjE_elimSub (dvd pF aF, dvd pF aF, oFalseC) disj caseA caseA;  (* oFalse *)
                    val metaNe = Thm.implies_intr (ctermSub (jT (dvd pF bF))) fls;
                  in impI_atS2 (dvd pF bF, oFalseC) metaNe end;               (* ~(p|b) *)

                (* build the QR witness : cong p (x*x)(sub p 1), x = a * b^(k+k) *)
                val xT  = mult aF (pow bF kkT);
                val pbk = pow bF kkT; val ZT = pow bF (add kkT kkT);
                val ddSF = suc (suc (add kkT kkT));   (* sub-free dd = Suc(Suc(kk+kk)) *)
                val Hsq =
                  let
                    (* ---- (i) bb*(x*x) = aa * b^(sub p 1) ---- *)
                    val s1 = multassocS2_at (aF, pbk, mult aF pbk);
                    val s2 = multassocS2_at (pbk, aF, pbk);
                    val s2s= oeq_sym OF [s2];
                    val cm = multcommS2_at (pbk, aF);
                    val s3 = mult_cong_lS2 (mult pbk aF, mult aF pbk, pbk) cm;
                    val s4 = multassocS2_at (aF, pbk, pbk);
                    val inner = oeq_trans OF [s2s, oeq_trans OF [s3, s4]];
                    val s5 = mult_cong_rS2 (aF, mult pbk (mult aF pbk), mult aF (mult pbk pbk)) inner;
                    val s6 = multassocS2_at (aF, aF, mult pbk pbk);
                    val xx_eq = oeq_trans OF [s1, oeq_trans OF [s5, oeq_sym OF [s6]]];
                    val padd = pow_add_atSub (bF, kkT, kkT);
                    val pbkpbk = oeq_sym OF [padd];
                    val xx_eq2 = oeq_trans OF [xx_eq, mult_cong_rS2 (aaT, mult pbk pbk, ZT) pbkpbk];
                    val bbxx = mult_cong_rS2 (bbT, mult xT xT, mult aaT ZT) xx_eq2;
                    val r1 = multassocS2_at (bbT, aaT, ZT);
                    val cmba = multcommS2_at (bbT, aaT);
                    val r2 = mult_cong_lS2 (mult bbT aaT, mult aaT bbT, ZT) cmba;
                    val r3 = multassocS2_at (aaT, bbT, ZT);
                    val bbaaZ = oeq_trans OF [oeq_sym OF [r1], oeq_trans OF [r2, r3]];
                    val pS1 = powSucS2_at (bF, add kkT kkT);
                    val pS1s= oeq_sym OF [pS1];
                    val pS2 = powSucS2_at (bF, suc (add kkT kkT));
                    val bbZ_a = mult_cong_rS2 (bF, mult bF ZT, pow bF (suc (add kkT kkT))) pS1s;
                    val bbZ_b = oeq_trans OF [bbZ_a, oeq_sym OF [pS2]];
                    val bbZ_assoc = multassocS2_at (bF, bF, ZT);
                    val bbZ_eq = oeq_trans OF [bbZ_assoc, bbZ_b];
                    val mm_SS =
                      let val aS = addSucS2_at (kkT, suc kkT)
                          val aSr= addSrS2_at (kkT, kkT)
                      in oeq_trans OF [aS, Suc_cong OF [aSr]] end;
                    val subp1_SS = oeq_trans OF [subp1_mm, mm_SS];   (* sub p 1 = Suc(Suc(kk+kk)) *)
                    val powb_eq = pow_cong_argSub (bF, suc (suc (add kkT kkT)), dT) (oeq_sym OF [subp1_SS]);
                    val bbZ_powd = oeq_trans OF [bbZ_eq, powb_eq];
                    val aabbZ = mult_cong_rS2 (aaT, mult bbT ZT, pow bF dT) bbZ_powd;
                    val full_i = oeq_trans OF [bbxx, oeq_trans OF [bbaaZ, aabbZ]];

                    (* ---- (ii) cong p (bb*xx) aa ---- *)
                    val apb = apm1_atSub (pF, bF) Hprime Hndvd_b;
                    val cong_aa = cong_mult_atSub (pF, aaT, aaT, pow bF dT, oneC) (cong_refl_atSub (pF, aaT)) apb;
                    val aa1 = mult_1_right_atSub aaT;
                    val zc = Free("zbw1", natT)
                    val Pc = Term.lambda zc (cong pF (mult aaT (pow bF dT)) zc)
                    val cong_aa2 = substPredS2 (Pc, mult aaT oneC, aaT) aa1 cong_aa;
                    val cong_bbxx_aabd = oeq_to_congSub (pF, mult bbT (mult xT xT), mult aaT (pow bF dT)) full_i;
                    val cong_bbxx_aa = cong_trans_atSub (pF, mult bbT (mult xT xT), mult aaT (pow bF dT), aaT)
                                         cong_bbxx_aabd cong_aa2;

                    (* ---- (iii) cong p aa (bb*dd) (sub-free dd) ---- *)
                    val ddT2 = ddSF;
                    val d1_eq =
                      let
                        val sr = addSrS2_at (ddT2, ZeroC);
                        val a0 = add0rS2_at ddT2;
                        val dS = oeq_trans OF [sr, Suc_cong OF [a0]];   (* dd+1 = Suc dd = Suc(Suc(Suc(kk+kk))) *)
                      in oeq_trans OF [dS, oeq_sym OF [q_eq_kk]] end;   (* dd+1 = p *)
                    val onebb = mult1lS2_at bbT;
                    val step_a = add_cong_rS2 (mult ddT2 bbT, bbT, mult oneC bbT) (oeq_sym OF [onebb]);
                    val rdist  = rdistS2_at (ddT2, oneC, bbT);
                    val step_b = oeq_trans OF [step_a, oeq_sym OF [rdist]];
                    val step_c = mult_cong_lS2 (add ddT2 oneC, pF, bbT) d1_eq;
                    val dbbbb_pbb = oeq_trans OF [step_b, step_c];
                    val dvd_pbb = dvd_introSub (pF, mult pF bbT, bbT) (oeqreflS2_at (mult pF bbT));
                    val cong_pbb0 = dvd_imp_cong_zero_at (pF, mult pF bbT) dvd_pbb;
                    val cong_dbbbb_pbb = oeq_to_congSub (pF, add (mult ddT2 bbT) bbT, mult pF bbT) dbbbb_pbb;
                    val cong_dbbbb_0 = cong_trans_atSub (pF, add (mult ddT2 bbT) bbT, mult pF bbT, ZeroC) cong_dbbbb_pbb cong_pbb0;
                    val cong_aabb_dbbbb = cong_trans_atSub (pF, add aaT bbT, ZeroC, add (mult ddT2 bbT) bbT)
                                            Hcong0 (cong_sym_atSub (pF, add (mult ddT2 bbT) bbT, ZeroC) cong_dbbbb_0);
                    val cong_aa_dbb = cong_add_rcancel (pF, aaT, mult ddT2 bbT, bbT) cong_aabb_dbbbb;
                    val cmdbb = multcommS2_at (ddT2, bbT);
                    val zc2 = Free("zbw2", natT)
                    val Pc2 = Term.lambda zc2 (cong pF aaT zc2)
                    val cong_aa_bbd = substPredS2 (Pc2, mult ddT2 bbT, mult bbT ddT2) cmdbb cong_aa_dbb;

                    (* ---- (iv) chain ---- *)
                    val cong_bbxx_bbd = cong_trans_atSub (pF, mult bbT (mult xT xT), aaT, mult bbT ddT2)
                                          cong_bbxx_aa cong_aa_bbd;

                    (* ---- (v) mod_cancel by bb -> cong p (xx) dd ; rewrite dd -> sub p 1 ---- *)
                    val ndvd_bb = ndvd_sq (pF, bF) Hprime Hndvd_b;
                    val cong_xx_dd = mod_cancel_atSub (pF, bbT, mult xT xT, ddT2) Hprime ndvd_bb cong_bbxx_bbd;
                    val zc3 = Free("zbw3", natT)
                    val Pc3 = Term.lambda zc3 (cong pF (mult xT xT) zc3)
                    val cong_xx_d = substPredS2 (Pc3, ddT2, dT) (oeq_sym OF [subp1_SS]) cong_xx_dd;
                  in cong_xx_d end;     (* cong p (x*x)(sub p 1) *)
                val () = out "KM_HSQ_OK\n";

                (* ~(p | x) , x = a*b^(k+k) , from ~p|a + ~p|b via euclid + ndvd_pow *)
                val Hndvd_x = ndvd_x (pF, aF, bF, kkT) Hprime Hndvd_a Hndvd_b;   (* ~(p | a*b^(k+k)) *)
                val () = out "KM_NDVDX_OK\n";
                (* feed neg1_not_qr_body : oFalse *)
                val fls = neg1_not_qr_body (pF, xT) Hprime Hle3 Hndvd_x Hsq kW hpk;
                val () = out "KM_NEG1_OK\n";
                (* turn oFalse into dvd p a (ex falso) *)
                val g = Thm.implies_elim (oFalse_elimSub_at (dvd pF aF)) fls;
              in Thm.implies_intr (ctermSub (jT (neg (dvd pF aF)))) g end;
          in disjE_elimSub (dvd pF aF, neg (dvd pF aF), dvd pF aF) em caseYes caseNo end;

        (* ============ prove dvd p b from dvd p a ============ *)
        val dvd_pb =
          let
            val dvd_aa = dvd_mult_rightSub (pF, aF, aF) dvd_pa;        (* dvd p (a*a) *)
            val dvd_bb = dvd_diff_atS (pF, aaT, bbT) dvd_aa HdvdN;     (* dvd p (b*b) *)
            val disj = euclid_atS (pF, bF, bF) Hprime dvd_bb;          (* Disj (dvd p b)(dvd p b) *)
            val caseB = Thm.implies_intr (ctermSub (jT (dvd pF bF))) (Thm.assume (ctermSub (jT (dvd pF bF))));
          in disjE_elimSub (dvd pF bF, dvd pF bF, dvd pF bF) disj caseB caseB end;

        val conj = conjI_atS2 (dvd pF aF, dvd pF bF) dvd_pa dvd_pb;    (* Conj (dvd p a)(dvd p b) *)
      in conj end;

    val core = exESub_elim (H4k3body, goalConj) H4k3 "k_ko" afterK;

    val d1 = Thm.implies_intr (ctermSub HdvdNP) core;
    val d2 = Thm.implies_intr (ctermSub H4k3P) d1;
    val d3 = Thm.implies_intr (ctermSub HprimeP) d2;
  in varify d3 end;

val () = out "KEYMAIN_PROVED\n";

(* ============================================================================
   VALIDATION : 0-hyp + aconv intended + soundness probes.
   ============================================================================ *)
val pVk = Var (("p",0), natT);
val aVk = Var (("a",0), natT);
val bVk = Var (("b",0), natT);
val key_4k3_body =
  Abs("k", natT, oeq pVk (add (add (add (add (Bound 0)(Bound 0))(Bound 0))(Bound 0)) (suc (suc (suc ZeroC)))));
(* the +1 (mod 4) body : p = (k+k+k+k) + 1  -- the FALSE companion direction *)
val key_4k1_body =
  Abs("k", natT, oeq pVk (add (add (add (add (Bound 0)(Bound 0))(Bound 0))(Bound 0)) (suc ZeroC)));

val key_onlyif_intended =
  Logic.mk_implies (jT (prime2 pVk),
    Logic.mk_implies (jT (mkEx key_4k3_body),
      Logic.mk_implies (jT (dvd pVk (add (mult aVk aVk)(mult bVk bVk))),
        jT (mkConj (dvd pVk aVk)(dvd pVk bVk)))));
val key_nhyp  = length (Thm.hyps_of key_onlyif);
val key_aconv = (Thm.prop_of key_onlyif) aconv key_onlyif_intended;
val () = out ("KEY hyps=" ^ Int.toString key_nhyp ^ " aconv=" ^ Bool.toString key_aconv ^ "\n");

(* probe 1 : the lemma genuinely USES p == 3 (mod 4) -- NOT the variant with the
   mod-4 premise dropped (FALSE: 5 | 1^2+2^2 but 5 does not divide 1). *)
val probe_needs_mod4 =
  not ((Thm.prop_of key_onlyif) aconv
       Logic.mk_implies (jT (prime2 pVk),
         Logic.mk_implies (jT (dvd pVk (add (mult aVk aVk)(mult bVk bVk))),
           jT (mkConj (dvd pVk aVk)(dvd pVk bVk)))));

(* probe 2 : the lemma genuinely USES the divisibility premise. *)
val probe_needs_dvd =
  not ((Thm.prop_of key_onlyif) aconv
       Logic.mk_implies (jT (prime2 pVk),
         Logic.mk_implies (jT (mkEx key_4k3_body),
           jT (mkConj (dvd pVk aVk)(dvd pVk bVk)))));

(* probe 3 : the conclusion is the CONJUNCTION (both p|a and p|b), not just p|a. *)
val probe_conj =
  not ((Thm.prop_of key_onlyif) aconv
       Logic.mk_implies (jT (prime2 pVk),
         Logic.mk_implies (jT (mkEx key_4k3_body),
           Logic.mk_implies (jT (dvd pVk (add (mult aVk aVk)(mult bVk bVk))),
             jT (dvd pVk aVk)))));

(* probe 4 : the proved statement is the p==3mod4 one and NOT the p==1mod4 one
   (the +1 variant is FALSE: 5 = 4*1+1 and 5 | 1^2+2^2 yet 5 does not divide 1).
   This pins that the lemma is specifically about 3 mod 4, the essential case. *)
val key_onlyif_1mod4 =
  Logic.mk_implies (jT (prime2 pVk),
    Logic.mk_implies (jT (mkEx key_4k1_body),
      Logic.mk_implies (jT (dvd pVk (add (mult aVk aVk)(mult bVk bVk))),
        jT (mkConj (dvd pVk aVk)(dvd pVk bVk)))));
val probe_not_1mod4 = not ((Thm.prop_of key_onlyif) aconv key_onlyif_1mod4);

val () =
  if key_nhyp = 0 andalso key_aconv andalso probe_needs_mod4 andalso probe_needs_dvd
     andalso probe_conj andalso probe_not_1mod4
  then out "PROBE_OK key_onlyif conditional / conjunction / mod4-essential / not-1mod4\n"
  else out "PROBE_UNSOUND key_onlyif collapsed!\n";

val () =
  if key_nhyp = 0 andalso key_aconv andalso probe_needs_mod4 andalso probe_needs_dvd
     andalso probe_conj andalso probe_not_1mod4
  then out "KEY_ONLYIF_OK\n"
  else out ("KEY_ONLYIF_FAILED nhyp=" ^ Int.toString key_nhyp
            ^ " aconv=" ^ Bool.toString key_aconv
            ^ " pm4=" ^ Bool.toString probe_needs_mod4
            ^ " pdvd=" ^ Bool.toString probe_needs_dvd
            ^ " pcj=" ^ Bool.toString probe_conj
            ^ " p1m4=" ^ Bool.toString probe_not_1mod4 ^ "\n");
