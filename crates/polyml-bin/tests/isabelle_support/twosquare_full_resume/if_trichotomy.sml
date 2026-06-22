(* ============================================================================
   MOD-4 TRICHOTOMY for primes, on the twosquare monolith final context ctxtGR.

   GOAL:
     mod4_trichotomy : prime2 p ==>
        Disj (oeq p 2)
             (Disj (Ex k. oeq p (add (mult 4 k) 1))
                   (Ex k. oeq p (add (mult 4 k) 3)))

   PROOF: div_mod_exists at b=4 gives p = 4q + r with r<4.  Peel r<4 by
   repeated lt_suc_cases into r in {0,1,2,3}.
     - r=1 -> middle disjunct, witness q.
     - r=3 -> right  disjunct, witness q.
     - r=0 -> p = 4q = 2*(2q), so 2|p, prime2 forces 2=p -> oeq p 2 (left).
     - r=2 -> p = 4q+2 = 2*(Suc(2q)), so 2|p, prime2 forces 2=p -> oeq p 2.
   0-hyp, aconv-intended, soundness-probed.  NO new axioms / consts / types.

   This file is appended AFTER isabelle_twosquare.sml (final context ctxtGR).
   It re-derives only the small _gr helpers it needs (self-contained: does NOT
   depend on if_toolkit.sml).
   ============================================================================ *)

val () = out "TSF_TRICHOTOMY_BEGIN\n";

(* ---- numerals ---- *)
val n0 = ZeroC;
val n1 = suc ZeroC;
val n2 = suc (suc ZeroC);
val n3 = suc (suc (suc ZeroC));
val n4 = suc (suc (suc (suc ZeroC)));

(* ---- varify base lemmas/axioms onto ctxtGR (suffix _t) ---- *)
val oeq_refl_t   = varify oeq_refl;
val add_0_t      = varify add_0;
val add_Suc_t    = varify add_Suc;
val add_0_right_t   = varify add_0_right;
val add_Suc_right_t = varify add_Suc_right;
val mult_0_t     = varify mult_0;
val mult_Suc_t   = varify mult_Suc;
val mult_0_right_t   = varify mult_0_right;
val mult_Suc_right_t = varify mult_Suc_right;
val mult_assoc_t = varify mult_assoc;
val add_comm_t   = varify add_comm;
val oeq_subst_t  = varify oeq_subst;
val exI_t        = varify exI_ax;
val exE_t        = varify exE_ax;
val disjI1_t     = varify disjI1_ax;
val disjI2_t     = varify disjI2_ax;
val disjE_t      = varify disjE_ax;
val mp_t         = varify mp_ax;
val allE_t       = varify allE_ax;
val conjunct1_t  = varify conjunct1_ax;
val conjunct2_t  = varify conjunct2_ax;
val Suc_inj_t    = varify Suc_inj_ax;
val Suc_neq_Zero_t = varify Suc_neq_Zero_ax;
val oFalse_elim_t  = varify oFalse_elim_ax;
val lt_suc_cases_t = varify lt_suc_cases;
val div_mod_t      = varify div_mod_exists;

(* ---- ground instantiators on ctxtGR ---- *)
fun oeqRefl_t t = beta_norm (Drule.infer_instantiate ctxtGR [(("a",0), ctermGR t)] oeq_refl_t);
fun add0_t t    = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] add_0_t);
fun addSuc_t (mt,nt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt)] add_Suc_t);
fun add0r_t t   = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] add_0_right_t);
fun addSr_t (mt,nt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt)] add_Suc_right_t);
fun mult0_t t   = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] mult_0_t);
fun multSuc_t (mt,nt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt)] mult_Suc_t);
fun mult0r_t t  = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] mult_0_right_t);
fun multSr_t (nt,mt) = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR nt),(("m",0), ctermGR mt)] mult_Suc_right_t);
fun multassoc_t (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt),(("k",0), ctermGR kt)] mult_assoc_t);
fun addcomm_t (mt,nt) = beta_norm (Drule.infer_instantiate ctxtGR [(("m",0), ctermGR mt),(("n",0), ctermGR nt)] add_comm_t);
fun Suc_inj_t_at (uT,vT) = beta_norm (Drule.infer_instantiate ctxtGR [(("a",0), ctermGR uT),(("b",0), ctermGR vT)] Suc_inj_t);
fun Suc_neq_Zero_t_at t  = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] Suc_neq_Zero_t);
fun oFalse_elim_t_at rT  = beta_norm (Drule.infer_instantiate ctxtGR [(("R",0), ctermGR rT)] oFalse_elim_t);

(* oeq-subst rewrite on ctxtGR : oeq a b -> P a -> P b *)
fun oeq_rw_t (Pabs, aT, bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("P",0), ctermGR Pabs), (("a",0), ctermGR aT), (("b",0), ctermGR bT)] oeq_subst_t)
  in (inst OF [hab]) OF [hPa] end;

(* multiplicative / additive congruence (capture-safe via Free-lambda) *)
fun mult_cong_l_t (pT, qT, kT) hpq =
  let val zF = Free("z_mcl", natT)
  in oeq_rw_t (Term.lambda zF (oeq (mult pT kT) (mult zF kT)), pT, qT) hpq (oeqRefl_t (mult pT kT)) end;
fun mult_cong_r_t (hT, pT, qT) hpq =
  let val zF = Free("z_mcr", natT)
  in oeq_rw_t (Term.lambda zF (oeq (mult hT pT) (mult hT zF)), pT, qT) hpq (oeqRefl_t (mult hT pT)) end;
fun add_cong_l_t (pT, qT, kT) hpq =
  let val zF = Free("z_acl", natT)
  in oeq_rw_t (Term.lambda zF (oeq (add pT kT) (add zF kT)), pT, qT) hpq (oeqRefl_t (add pT kT)) end;
fun add_cong_r_t (hT, pT, qT) hpq =
  let val zF = Free("z_acr", natT)
  in oeq_rw_t (Term.lambda zF (oeq (add hT pT) (add hT zF)), pT, qT) hpq (oeqRefl_t (add hT pT)) end;

(* exI / exE / disjE / disjI / mp / allE on ctxtGR *)
fun exI_t_at Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("P",0), ctermGR Pabs), (("a",0), ctermGR at)] exI_t)
  in Thm.implies_elim inst hbody end;
fun exE_t_elim (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm  = Thm.assume (ctermGR hypTerm);
    val body    = bodyFn wF hypThm;
    val minor   = Thm.forall_intr (ctermGR wF) (Thm.implies_intr (ctermGR hypTerm) body);
    val exE_inst= beta_norm (Drule.infer_instantiate ctxtGR
                    [(("P",0), ctermGR Pabs), (("Q",0), ctermGR goalC)] exE_t);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;
fun disjE_t_elim (At, Bt, Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("A",0), ctermGR At),(("B",0), ctermGR Bt),(("C",0), ctermGR Ct)] disjE_t)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB end;
fun disjI1_t_at (At,Bt) h = (beta_norm (Drule.infer_instantiate ctxtGR
      [(("A",0), ctermGR At), (("B",0), ctermGR Bt)] disjI1_t)) OF [h];
fun disjI2_t_at (At,Bt) h = (beta_norm (Drule.infer_instantiate ctxtGR
      [(("A",0), ctermGR At), (("B",0), ctermGR Bt)] disjI2_t)) OF [h];
fun mp_t_at (At, Bt) hImp hA =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] mp_t)) hImp) hA;
fun allE_t_at Pabs at hForall =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("P",0), ctermGR Pabs), (("a",0), ctermGR at)] allE_t)) hForall;
fun conjunct1_t_at (At,Bt) hC =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] conjunct1_t)) hC;
fun conjunct2_t_at (At,Bt) hC =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] conjunct2_t)) hC;

(* lt_suc_cases on ctxtGR : lt m (Suc n) -> Disj (lt m n)(oeq m n) *)
fun lt_suc_cases_t_at (mt,nt) hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("m",0), ctermGR mt),(("n",0), ctermGR nt)] lt_suc_cases_t)) hlt;

(* div_mod_exists on ctxtGR : (lt 0 b) -> Ex q. Ex r. Conj (oeq a (add (mult b q) r)) (lt r b) *)
fun div_mod_t_at (atDividend, btDivisor) hpos =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("a",0), ctermGR atDividend), (("b",0), ctermGR btDivisor)] div_mod_t)) hpos;

(* lt_zero_elim on ctxtGR : lt m 0 -> goal *)
fun lt_zero_elim_t mT goalC hlt =
  let
    val zF = Free("w_lz0", natT);
    val PabsR = Term.lambda zF (oeq ZeroC (add (suc mT) zF));
    fun body w (hw : thm) =                   (* hw : oeq Zero (add (Suc m) w) *)
      let
        val aS  = addSuc_t (mT, w);           (* (Suc m + w) = Suc(m + w) *)
        val z_S = oeq_trans OF [hw, aS];      (* 0 = Suc(m + w) *)
        val S_z = oeq_sym OF [z_S];           (* Suc(m+w) = 0 *)
        val fls = (Suc_neq_Zero_t_at (add mT w)) OF [S_z];   (* oFalse *)
      in (oFalse_elim_t_at goalC) OF [fls] end;
  in exE_t_elim (PabsR, goalC) hlt "w_lz" body end;

val () = out "TSF_TRI_HELPERS_OK\n";

(* ---- prime2 destructors on ctxtGR ---- *)
fun prime2_div_t (pT, dT) hPrime hDvdDP =      (* prime2 p -> dvd d p -> Disj (oeq d 1)(oeq d p) *)
  let
    val faThm = conjunct2_t_at (lt (suc ZeroC) pT, mkForall (ppAbs pT)) hPrime;  (* Forall (ppAbs p) *)
    val impAt = allE_t_at (ppAbs pT) dT faThm;  (* jT (Imp (dvd d p)(Disj (oeq d 1)(oeq d p))) *)
  in mp_t_at (dvd dT pT, mkDisj (oeq dT (suc ZeroC)) (oeq dT pT)) impAt hDvdDP end;

(* ---- four_eq : oeq 4 (mult 2 2) ---- *)
(* mult 2 2 = mult (Suc(Suc 0)) 2 = add 2 (mult (Suc 0) 2)         [mult_Suc]
            = add 2 (add 2 (mult 0 2))                              [mult_Suc]
            = add 2 (add 2 0)                                       [mult_0]
            = add 2 2                                               [add_0_right]
            = 4 .  Then sym. *)
val four_eq =
  let
    val m1 = multSuc_t (suc ZeroC, n2);                 (* mult 2 2 = add 2 (mult (Suc 0) 2) *)
    val m2 = multSuc_t (ZeroC, n2);                     (* mult (Suc 0) 2 = add 2 (mult 0 2) *)
    val m3 = mult0_t n2;                                (* mult 0 2 = 0 *)
    (* add 2 (mult 0 2) = add 2 0 *)
    val m3c = add_cong_r_t (n2, mult ZeroC n2, ZeroC) m3;  (* add 2 (mult 0 2) = add 2 0 *)
    val m2c = oeq_trans OF [m2, m3c];                   (* mult (Suc 0) 2 = add 2 0 *)
    (* add 2 (mult(Suc 0) 2) = add 2 (add 2 0) *)
    val m1b = add_cong_r_t (n2, mult (suc ZeroC) n2, add n2 ZeroC) m2c; (* add 2 (mult (Suc 0)2) = add 2 (add 2 0) *)
    val chain1 = oeq_trans OF [m1, m1b];               (* mult 2 2 = add 2 (add 2 0) *)
    (* add 2 0 = 2 *)
    val a20 = add0r_t n2;                               (* add 2 0 = 2 *)
    val a20c = add_cong_r_t (n2, add n2 ZeroC, n2) a20; (* add 2 (add 2 0) = add 2 2 *)
    val chain2 = oeq_trans OF [chain1, a20c];          (* mult 2 2 = add 2 2 *)
    (* add 2 2 = 4 : add (Suc(Suc 0))(Suc(Suc 0)) = Suc(add (Suc 0)(Suc(Suc 0))) = Suc(Suc(add 0 (Suc(Suc 0)))) = Suc(Suc(Suc(Suc 0))) *)
    val s1 = addSuc_t (suc ZeroC, n2);                 (* add (Suc(Suc 0))(Suc(Suc 0)) = Suc(add (Suc 0)(Suc(Suc 0))) *)
    val s2 = addSuc_t (ZeroC, n2);                     (* add (Suc 0)(Suc(Suc 0)) = Suc(add 0 (Suc(Suc 0))) *)
    val s2c = Suc_cong OF [s2];                        (* Suc(add(Suc 0)..) = Suc(Suc(add 0 ..)) *)
    val s3 = add0_t n2;                                (* add 0 (Suc(Suc 0)) = Suc(Suc 0) *)
    val s3c = Suc_cong OF [Suc_cong OF [s3]];          (* Suc(Suc(add 0 ..)) = Suc(Suc(Suc(Suc 0))) *)
    val add22 = oeq_trans OF [s1, oeq_trans OF [s2c, s3c]]; (* add 2 2 = 4 *)
    val chain3 = oeq_trans OF [chain2, add22];         (* mult 2 2 = 4 *)
  in oeq_sym OF [chain3] end;                          (* 4 = mult 2 2 *)

(* mult4q_2_2q : oeq (mult 4 q)(mult 2 (mult 2 q))
     mult 4 q = mult (mult 2 2) q          [four_eq cong on left]
              = mult 2 (mult 2 q)          [mult_assoc] *)
fun mult4q_2_2q qT =
  let
    val c1 = mult_cong_l_t (n4, mult n2 n2, qT) four_eq;     (* mult 4 q = mult (mult 2 2) q *)
    val asc = multassoc_t (n2, n2, qT);                      (* (mult 2 2)*q = 2*(2*q) *)
  in oeq_trans OF [c1, asc] end;                             (* mult 4 q = 2*(2*q) *)

val () = out "TSF_TRI_four_eq_OK\n";

(* ---- helper: from (oeq p X) and (oeq X (mult 2 W)) -> oeq p (mult 2 W) -> dvd 2 p ---- *)
fun dvd2_from (pT, wT) hp_eq =       (* hp_eq : oeq p (mult 2 w) -> jT (dvd 2 p) *)
  (* dvd 2 p = Ex k. oeq p (mult 2 k).  witness k = w. *)
  let
    val Pabs = Term.lambda (Free("k_d2", natT)) (oeq pT (mult n2 (Free("k_d2", natT))))
    (* dvd a b = mkEx (Abs("k", natT, oeq b (mult a (Bound 0)))) : check this matches ppAbs/dvd. *)
  in exI_t_at Pabs wT hp_eq end;

(* ---- from (dvd 2 p) and prime2 p -> oeq p 2 ----
     prime2_div : Disj (oeq 2 1)(oeq 2 p).  oeq 2 1 = oeq (Suc 1)(Suc 0) -> Suc_inj -> oeq 1 0 = oeq (Suc 0) 0 -> Suc_neq_Zero -> oFalse.
     so disjE: caseA(oeq 2 1)->oFalse_elim; caseB(oeq 2 p)->sym->oeq p 2. *)
fun oeq_p_2_from_dvd2 (pT, hPrime, hDvd2p) =
  let
    val disjD = prime2_div_t (pT, n2) hPrime hDvd2p;     (* Disj (oeq 2 1)(oeq 2 p) *)
    val goalC = oeq pT n2;
    val caseA =
      let
        val h21 = Thm.assume (ctermGR (jT (oeq n2 n1)));   (* oeq (Suc(Suc 0))(Suc 0) *)
        val inj = (Suc_inj_t_at (suc ZeroC, ZeroC)) OF [h21];  (* oeq (Suc 0) 0 *)
        val fls = (Suc_neq_Zero_t_at ZeroC) OF [inj];      (* oFalse *)
        val g   = (oFalse_elim_t_at goalC) OF [fls];
      in Thm.implies_intr (ctermGR (jT (oeq n2 n1))) g end;
    val caseB =
      let
        val h2p = Thm.assume (ctermGR (jT (oeq n2 pT)));   (* oeq 2 p *)
        val g   = oeq_sym OF [h2p];                        (* oeq p 2 *)
      in Thm.implies_intr (ctermGR (jT (oeq n2 pT))) g end;
  in disjE_t_elim (oeq n2 n1, oeq n2 pT, goalC) disjD caseA caseB end;

val () = out "TSF_TRI_dvd2_OK\n";

(* ============================================================================
   THE TRICHOTOMY
   ============================================================================ *)
val mod4_trichotomy =
  let
    val pF = Free("p_tri", natT);
    val hPrime = Thm.assume (ctermGR (jT (prime2 pF)));

    (* the three disjunct bodies *)
    val Aterm = oeq pF n2;                                          (* p = 2 *)
    fun kBody1 k = oeq pF (add (mult n4 k) n1);                     (* p = 4k+1 *)
    fun kBody3 k = oeq pF (add (mult n4 k) n3);                     (* p = 4k+3 *)
    val midEx   = mkEx (Term.lambda (Free("k_m", natT)) (kBody1 (Free("k_m", natT))));
    val rightEx = mkEx (Term.lambda (Free("k_r", natT)) (kBody3 (Free("k_r", natT))));
    val innerDisj = mkDisj midEx rightEx;
    val GOAL = mkDisj Aterm innerDisj;                             (* the full trichotomy disjunction *)

    (* lt 0 4 : le (Suc 0) 4.  4 = add (Suc 0) 3 ? le_intro needs oeq 4 (add (Suc 0) w).
       add (Suc 0) 3 = Suc(add 0 3) = Suc 3 = 4.  witness w = 3. *)
    val lt04 =
      let
        val a1 = addSuc_t (ZeroC, n3);          (* add (Suc 0) 3 = Suc(add 0 3) *)
        val a0 = add0_t n3;                      (* add 0 3 = 3 *)
        val a0S= Suc_cong OF [a0];               (* Suc(add 0 3) = Suc 3 = 4 *)
        val chain = oeq_trans OF [a1, a0S];      (* add (Suc 0) 3 = 4 *)
        val chS = oeq_sym OF [chain];            (* 4 = add (Suc 0) 3 *)
        (* le (Suc 0) 4 = Ex p. oeq 4 (add (Suc 0) p), witness 3 *)
        val Pabs = Term.lambda (Free("w_le", natT)) (oeq n4 (add (suc ZeroC) (Free("w_le", natT))))
      in exI_t_at Pabs n3 chS end;              (* lt 0 4 *)

    (* div_mod at a=p, b=4 *)
    val dm = div_mod_t_at (pF, n4) lt04;    (* Ex q. Ex r. Conj (oeq p (add (mult 4 q) r))(lt r 4) *)

    (* exE over q *)
    val qBodyAbs = Term.lambda (Free("q_e", natT))
        (mkEx (Term.lambda (Free("r_e", natT))
           (mkConj (oeq pF (add (mult n4 (Free("q_e", natT))) (Free("r_e", natT)))) (lt (Free("r_e", natT)) n4))));
    fun afterQ qT (hq : thm) =     (* hq : Ex r. Conj (oeq p (add (mult 4 q) r))(lt r 4) *)
      let
        val rBodyAbs = Term.lambda (Free("r_e2", natT))
            (mkConj (oeq pF (add (mult n4 qT) (Free("r_e2", natT)))) (lt (Free("r_e2", natT)) n4));
        fun afterR rT (hr : thm) =   (* hr : Conj (oeq p (add (mult 4 q) r))(lt r 4) *)
          let
            val hEq = conjunct1_t_at (oeq pF (add (mult n4 qT) rT), lt rT n4) hr;  (* oeq p (add (mult 4 q) r) *)
            val hLt = conjunct2_t_at (oeq pF (add (mult n4 qT) rT), lt rT n4) hr;  (* lt r 4 *)

            (* ===== case r = 3 : right disjunct, witness q ===== *)
            fun mkRight (hR3 : thm) =   (* hR3 : oeq r 3 *)
              let
                (* rewrite (add (mult 4 q) r) -> (add (mult 4 q) 3) via hR3 *)
                val cong = add_cong_r_t (mult n4 qT, rT, n3) hR3;   (* oeq (add (mult4q) r)(add (mult4q) 3) *)
                val pEq  = oeq_trans OF [hEq, cong];                (* oeq p (add (mult 4 q) 3) *)
                val ex   = exI_t_at (Term.lambda (Free("k_r", natT)) (kBody3 (Free("k_r", natT)))) qT pEq;  (* rightEx *)
              in disjI2_t_at (Aterm, innerDisj) (disjI2_t_at (midEx, rightEx) ex) end;

            (* ===== case r = 1 : middle disjunct, witness q ===== *)
            fun mkMid (hR1 : thm) =     (* hR1 : oeq r 1 *)
              let
                val cong = add_cong_r_t (mult n4 qT, rT, n1) hR1;   (* oeq (add (mult4q) r)(add (mult4q) 1) *)
                val pEq  = oeq_trans OF [hEq, cong];                (* oeq p (add (mult 4 q) 1) *)
                val ex   = exI_t_at (Term.lambda (Free("k_m", natT)) (kBody1 (Free("k_m", natT)))) qT pEq;  (* midEx *)
              in disjI2_t_at (Aterm, innerDisj) (disjI1_t_at (midEx, rightEx) ex) end;

            (* ===== case r = 0 : 2|p -> oeq p 2 (left) =====
               p = add (mult 4 q) 0 = mult 4 q = mult 2 (mult 2 q).  witness for dvd 2 p = mult 2 q. *)
            fun mkZero (hR0 : thm) =    (* hR0 : oeq r 0 *)
              let
                val cong = add_cong_r_t (mult n4 qT, rT, ZeroC) hR0;  (* oeq (add (mult4q) r)(add (mult4q) 0) *)
                val a0r  = add0r_t (mult n4 qT);                      (* add (mult4q) 0 = mult4q *)
                val pMul4= oeq_trans OF [hEq, oeq_trans OF [cong, a0r]];  (* oeq p (mult 4 q) *)
                val m422 = mult4q_2_2q qT;                            (* oeq (mult 4 q)(mult 2 (mult 2 q)) *)
                val pEq  = oeq_trans OF [pMul4, m422];                (* oeq p (mult 2 (mult 2 q)) *)
                val hDvd = dvd2_from (pF, mult n2 qT) pEq;            (* dvd 2 p *)
                val pis2 = oeq_p_2_from_dvd2 (pF, hPrime, hDvd);      (* oeq p 2 *)
              in disjI1_t_at (Aterm, innerDisj) pis2 end;

            (* ===== case r = 2 : 2|p -> oeq p 2 (left) =====
               p = add (mult 4 q) 2 = mult 2 (Suc (mult 2 q)).  Derive:
                 mult 2 (Suc (mult 2 q)) = add 2 (mult 2 (mult 2 q))   [mult_Suc_right]
                                         = add 2 (mult 4 q)            [sym mult4q_2_2q]
               and  p = add (mult 4 q) 2 = add 2 (mult 4 q)            [add_comm].
               witness for dvd 2 p = Suc (mult 2 q). *)
            fun mkTwo (hR2 : thm) =     (* hR2 : oeq r 2 *)
              let
                val cong = add_cong_r_t (mult n4 qT, rT, n2) hR2;    (* oeq (add (mult4q) r)(add (mult4q) 2) *)
                val pEq1 = oeq_trans OF [hEq, cong];                 (* oeq p (add (mult 4 q) 2) *)
                (* add (mult 4 q) 2 = add 2 (mult 4 q) [comm] *)
                val comm = addcomm_t (mult n4 qT, n2);              (* oeq (add (mult4q) 2)(add 2 (mult4q)) *)
                val pEq2 = oeq_trans OF [pEq1, comm];               (* oeq p (add 2 (mult 4 q)) *)
                (* mult 2 (Suc (mult 2 q)) = add 2 (mult 2 (mult 2 q))   [mult_Suc_right with n=2, m=mult2q] *)
                val W = mult n2 qT;
                val msr  = multSr_t (n2, W);                        (* oeq (mult 2 (Suc W))(add 2 (mult 2 W)) *)
                (* mult 2 W = mult 2 (mult 2 q) = mult 4 q [sym mult4q_2_2q]; so add 2 (mult 2 W) = add 2 (mult 4 q) *)
                val m422S= oeq_sym OF [mult4q_2_2q qT];             (* oeq (mult 2 (mult 2 q))(mult 4 q) *)
                val cong2= add_cong_r_t (n2, mult n2 W, mult n4 qT) m422S;  (* add 2 (mult 2 W) = add 2 (mult 4 q) *)
                val msr2 = oeq_trans OF [msr, cong2];              (* mult 2 (Suc W) = add 2 (mult 4 q) *)
                (* so p = add 2 (mult 4 q) = mult 2 (Suc W) : oeq p (mult 2 (Suc W)) *)
                val pEq3 = oeq_trans OF [pEq2, oeq_sym OF [msr2]]; (* oeq p (mult 2 (Suc W)) *)
                val hDvd = dvd2_from (pF, suc W) pEq3;             (* dvd 2 p, witness Suc(mult 2 q) *)
                val pis2 = oeq_p_2_from_dvd2 (pF, hPrime, hDvd);  (* oeq p 2 *)
              in disjI1_t_at (Aterm, innerDisj) pis2 end;

            (* ===== peel lt r 4 down to r in {0,1,2,3} ===== *)
            (* lt r 4 = lt r (Suc 3) -> Disj (lt r 3)(oeq r 3) *)
            val d3 = lt_suc_cases_t_at (rT, n3) hLt;
            val caseEq3 =
              let val h = Thm.assume (ctermGR (jT (oeq rT n3)))
              in Thm.implies_intr (ctermGR (jT (oeq rT n3))) (mkRight h) end;
            val caseLt3 =
              let
                val hL3 = Thm.assume (ctermGR (jT (lt rT n3)));    (* lt r 3 = lt r (Suc 2) *)
                val d2  = lt_suc_cases_t_at (rT, n2) hL3;          (* Disj (lt r 2)(oeq r 2) *)
                val caseEq2 =
                  let val h = Thm.assume (ctermGR (jT (oeq rT n2)))
                  in Thm.implies_intr (ctermGR (jT (oeq rT n2))) (mkTwo h) end;
                val caseLt2 =
                  let
                    val hL2 = Thm.assume (ctermGR (jT (lt rT n2)));  (* lt r 2 = lt r (Suc 1) *)
                    val d1  = lt_suc_cases_t_at (rT, n1) hL2;        (* Disj (lt r 1)(oeq r 1) *)
                    val caseEq1 =
                      let val h = Thm.assume (ctermGR (jT (oeq rT n1)))
                      in Thm.implies_intr (ctermGR (jT (oeq rT n1))) (mkMid h) end;
                    val caseLt1 =
                      let
                        val hL1 = Thm.assume (ctermGR (jT (lt rT n1)));  (* lt r 1 = lt r (Suc 0) *)
                        val d0  = lt_suc_cases_t_at (rT, ZeroC) hL1;     (* Disj (lt r 0)(oeq r 0) *)
                        val caseEq0 =
                          let val h = Thm.assume (ctermGR (jT (oeq rT ZeroC)))
                          in Thm.implies_intr (ctermGR (jT (oeq rT ZeroC))) (mkZero h) end;
                        val caseLt0 =
                          let
                            val h = Thm.assume (ctermGR (jT (lt rT ZeroC)))  (* lt r 0 : impossible *)
                            val g = lt_zero_elim_t rT GOAL h
                          in Thm.implies_intr (ctermGR (jT (lt rT ZeroC))) g end;
                        (* discharge hL1 : the disjE result carries jT(lt r 1) as a hyp *)
                        val r1res = disjE_t_elim (lt rT ZeroC, oeq rT ZeroC, GOAL) d0 caseLt0 caseEq0;
                      in Thm.implies_intr (ctermGR (jT (lt rT n1))) r1res end;
                    val r2res = disjE_t_elim (lt rT n1, oeq rT n1, GOAL) d1 caseLt1 caseEq1;
                  in Thm.implies_intr (ctermGR (jT (lt rT n2))) r2res end;
                val r3res = disjE_t_elim (lt rT n2, oeq rT n2, GOAL) d2 caseLt2 caseEq2;
              in Thm.implies_intr (ctermGR (jT (lt rT n3))) r3res end;
          in disjE_t_elim (lt rT n3, oeq rT n3, GOAL) d3 caseLt3 caseEq3 end;
      in exE_t_elim (rBodyAbs, GOAL) hq "r_w" afterR end;
    val afterAll = exE_t_elim (qBodyAbs, GOAL) dm "q_w" afterQ;
    val disch = Thm.implies_intr (ctermGR (jT (prime2 pF))) afterAll;
  in varify disch end;

val () = out "TSF_TRICHOTOMY_PROVED\n";

(* ============================================================================
   VALIDATION : 0-hyp + aconv-intended + soundness probes
   ============================================================================ *)
val tri_hyps = Thm.hyps_of mod4_trichotomy;
val () = if null tri_hyps
         then out "TRI_ZERO_HYP_OK\n"
         else out ("TRI_HAS_HYPS!! n=" ^ Int.toString (length tri_hyps) ^ "\n");

(* intended statement, built with the SCHEMATIC Var that varify produces from
   the proof's Free("p_tri", natT) -> Var(("p_tri",0), natT). *)
val pVtri = Var (("p_tri",0), natT);
val tri_intended =
  let
    val midEx   = mkEx (Term.lambda (Free("k_m", natT)) (oeq pVtri (add (mult n4 (Free("k_m", natT))) n1)));
    val rightEx = mkEx (Term.lambda (Free("k_r", natT)) (oeq pVtri (add (mult n4 (Free("k_r", natT))) n3)));
  in Logic.mk_implies (jT (prime2 pVtri),
        jT (mkDisj (oeq pVtri n2) (mkDisj midEx rightEx))) end;

val () =
  if (Thm.prop_of mod4_trichotomy) aconv tri_intended
  then out "TRI_ACONV_OK\n"
  else (out "TRI_ACONV_MISMATCH!!\n";
        out ("  GOT : " ^ Syntax.string_of_term ctxtGR (Thm.prop_of mod4_trichotomy) ^ "\n");
        out ("  WANT: " ^ Syntax.string_of_term ctxtGR tri_intended ^ "\n"));

(* soundness probe 1 : the theorem genuinely needs prime2 (drop it -> not aconv) *)
val () =
  let
    val midEx   = mkEx (Term.lambda (Free("k_m", natT)) (oeq pVtri (add (mult n4 (Free("k_m", natT))) n1)));
    val rightEx = mkEx (Term.lambda (Free("k_r", natT)) (oeq pVtri (add (mult n4 (Free("k_r", natT))) n3)));
    val bogus = jT (mkDisj (oeq pVtri n2) (mkDisj midEx rightEx));  (* WITHOUT the prime2 premise *)
  in if not ((Thm.prop_of mod4_trichotomy) aconv bogus)
     then out "PROBE_OK tri keeps the prime2 premise\n"
     else out "PROBE_UNSOUND tri dropped the prime2 premise!\n" end;

(* soundness probe 2 : not the false "+2" residue variant (right disjunct +2 not +3) *)
val () =
  let
    val midEx   = mkEx (Term.lambda (Free("k_m", natT)) (oeq pVtri (add (mult n4 (Free("k_m", natT))) n1)));
    val bogusEx = mkEx (Term.lambda (Free("k_r", natT)) (oeq pVtri (add (mult n4 (Free("k_r", natT))) n2)));  (* +2 not +3 *)
    val bogus = Logic.mk_implies (jT (prime2 pVtri),
                  jT (mkDisj (oeq pVtri n2) (mkDisj midEx bogusEx)));
  in if not ((Thm.prop_of mod4_trichotomy) aconv bogus)
     then out "PROBE_OK tri residues are 1 and 3 (not a garbled +2)\n"
     else out "PROBE_UNSOUND tri residue garbled!\n" end;

val () = out "TSF_TRICHOTOMY_DONE\n";
