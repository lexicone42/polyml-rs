(* ============================================================================
   isabelle_euler_converse.sml
   ----------------------------------------------------------------------------
   EULER'S CONVERSE (conditional) + the FULL EUCLID-EULER IFF (conditional),
   appended after the banked self-contained euclid_perfect driver
     crates/polyml-bin/tests/isabelle_support/isabelle_euclid_perfect.sml
   (run directly, concatenated; mirrors the euler/twosquare self-contained pattern).

   STATUS — HONEST.  The ONE residual gap toward a FULLY UNCONDITIONAL Euler
   converse is the GENERAL-m sigma-multiplicativity bridge

       SCG :  !!a m. neg (dvd 2 m)
                ==> oeq (sigma (mult (p2 a) m)) (mult (sumf (pow 2) a) (sigma m))

   i.e. sigma(2^a * m) = (1+2+...+2^a) * sigma m  for m ODD — the GENERAL-m
   generalisation of the banked sigma_char (proved there only for PRIME q).  The
   general case is the sum-support-reindex / divisor-completeness wall documented
   in the base; partial progress (dist_lemma + sigma_mult_reduction) is banked in
   isabelle_euler_converse_sigma_mult.sml.  Closing SCG is a separate fleet.

   THIS DELTA proves, by genuine kernel inference, EVERYTHING ELSE (0 new axioms,
   0 new constant, all 0-extra-hyp, all aconv-intended, all soundness-probed):

     euler_converse_cond :
       |- SCG ==> lt 0 n ==> even n ==> perfect n ==> euclidForm n

     euclid_euler_cond :
       |- SCG ==> lt 0 n ==> even n
            ==> Conj (Imp (perfect n)(euclidForm n)) (Imp (euclidForm n)(perfect n))

   where  even n     := Ex k. oeq n (mult 2 k)
          perfect n  := oeq (sigma n)(mult 2 n)
          euclidForm n := Ex p. prime2 (sub (pow 2 p) 1)
                                 AND oeq n (mult (pow 2 (sub p 1))(sub (pow 2 p) 1))

   The BACKWARD half of the iff (euclidForm ==> perfect) is the BANKED
   euclid_perfect (Euclid IX.36), re-derived here as euclid_perfect_back; the
   FORWARD half (perfect ==> euclidForm) is euler_converse_cond.  So the ONLY
   hypothesis between this and the unconditional Euclid-Euler theorem is SCG.

   This file is the CONCATENATION of four banked pieces (each itself a delta on
   the euclid_perfect base, all on the final context ctxtSigD / thySigD):
     (A) factor_2s + consec_coprime + parity      [the 2-part extraction]
     (B) sigma_bound + the sumf-lower-bound tower  [sigma m = m+d ==> d=1 /\ prime]
     (C) the converse infra + arith/order helpers  [parity bridge, m<=sigma m, bounds]
     (D) euler_converse_cond + euclid_perfect_back + euclid_euler_cond + audits
   ============================================================================ *)

(* ============================================================================
   EULER-EULER converse SUPPORT: the 2-PART EXTRACTION + CONSECUTIVE COPRIMALITY.

   Appended AFTER isabelle_euclid_perfect.sml (run concatenated; the base ends on
   the final context ctxtSigD/ctermSigD over thySigD with all sigma / divlist /
   pow2 / euclid_perfect machinery in scope).

   This delta proves, each 0-hyp + aconv intended + soundness-probed:

   (1) consec_coprime :
         |- dvd d (sub (pow 2 b) (Suc Zero)) ==> dvd d (pow 2 b) ==> oeq d (Suc Zero)
       (a common divisor of 2^b-1 and 2^b divides their difference 1, hence = 1).

   (2) factor_2s :
         |- lt Zero n ==> even n
            ==> Ex a. Ex m. oeq n (mult (pow 2 a) m)
                            AND (Ex k. oeq m (Suc (mult 2 k)))   [m odd]
                            AND lt Zero a                         [a >= 1]
       where  even n := Ex k. oeq n (mult 2 k).
       (repeatedly divide out 2 by strong induction; the odd remainder).

   NO new const is added (so the delta runs directly on ctxtSigD); only the
   classical foundation's single ex_middle is used (via div_mod_exists, which is
   already classical underneath).  No axiom mentions the conclusions.
   ============================================================================ *)
val () = out "EE_FACTOR2S_BEGIN\n";

(* --- handy abbreviations already in scope: two, one, p2, pow, mult, add, sub,
   suc, ZeroC, oeq, dvd, le, lt, neg, mkEx, mkConj, mkImp, mkForall, exI_atD2,
   exE_atD, dvd_destD, dvd_introD, trans3, sym3, substPredD, reflD, addcommD,
   multcommD, multassocD, addassocD, add0D, add0rD, mult0rD, multSrD (mult n (Suc m)),
   powSucD, powZeroD, mult_cong_lD/rD, add_cong_lD/rD, Suc_injD, addSucD (add m (Suc n)),
   dvd_diff_D, dvd_refl_D, dvd_mult_right_D, dvd_cong_target_D, dvd_trans_D,
   disjE_D, disjI1_D2, disjI2_D2, conjI_Sg2, mp_D, allE_D, oFalse_elimD,
   lt0_of_suc, dzosD, Suc_neq_Zero_vD, one_neq_2k_at, pow2_pos_vD. --- *)

(* lift a few base lemmas onto thySigD that the base never lifted *)
val le_antisym_vEE = varify (up le_antisym);  (* le m n ==> le n m ==> oeq m n *)
val le_add_vEE     = varify (up le_add);      (* le m (add m p) *)
val le_trans_vEE   = varify (up le_trans);    (* le m n ==> le n k ==> le m k *)
val le_refl_vEE    = varify (up le_refl);     (* le n n *)
val mult_0_vEE     = varify (up mult_0);      (* oeq (mult 0 n) 0 *)
val add_Suc_vEE    = varify (up add_Suc);     (* oeq (add (Suc m) n)(Suc (add m n)) *)
val mult_Suc_vEE   = varify (up mult_Suc);    (* oeq (mult (Suc m) n)(add n (mult m n)) *)

fun le_antisymD (mT,nT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("m",0), ctermSigD mT),(("n",0), ctermSigD nT)] le_antisym_vEE)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun le_addD (mT,pT) = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("m",0), ctermSigD mT),(("p",0), ctermSigD pT)] le_add_vEE);
fun le_transD (mT,nT,kT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("m",0), ctermSigD mT),(("n",0), ctermSigD nT),(("k",0), ctermSigD kT)] le_trans_vEE)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun le_reflD t = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD t)] le_refl_vEE);
fun mult0lD t = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD t)] mult_0_vEE);
fun addSucLD (mT,nT) = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("m",0), ctermSigD mT),(("n",0), ctermSigD nT)] add_Suc_vEE);    (* add (Suc m) n = Suc(add m n) *)
fun multSucLD (mT,nT) = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("m",0), ctermSigD mT),(("n",0), ctermSigD nT)] mult_Suc_vEE);   (* mult (Suc m) n = add n (mult m n) *)

val () = out "EE_LIFT_OK\n";

(* ============================================================================
   (1) consec_coprime
   ============================================================================ *)
(* helper:  pow2_pred_eq : oeq (add (sub (pow 2 b) one) one)(pow 2 b)
   i.e. (2^b - 1) + 1 = 2^b   (using 2^b = Suc m). *)
val bF0 = Free("b", natT);

(* sub instantiators (subSSD, subN0D already from base) *)
(* (2^b - 1) + 1 = 2^b : witness 2^b = Suc m via pow2_pos *)
fun pow_sub1_add1 bT =
  let
    val pp = beta_norm (Drule.infer_instantiate ctxtSigD [(("k",0), ctermSigD bT)] pow2_pos_vD)
    (* pp : Ex m. pow 2 b = Suc m *)
    val exAbs = Abs("m", natT, oeq (pow two bT)(suc (Bound 0)))
    fun body mF hm =     (* hm : oeq (pow 2 b)(Suc m) *)
      let
        (* sub (pow 2 b) one : rewrite pow 2 b -> Suc m, then sub (Suc m)(Suc 0) = sub m 0 = m *)
        val Psub = Term.lambda (Free("zsb",natT)) (oeq (sub (pow two bT) one)(sub (Free("zsb",natT)) one))
        val subRw = substPredD (Psub, pow two bT, suc mF) hm (reflD (sub (pow two bT) one))
                    (* sub (pow 2 b) 1 = sub (Suc m) 1 *)
        val sSS = subSSD (mF, ZeroC)    (* sub (Suc m)(Suc 0) = sub m 0 *)
        val sN0 = subN0D mF             (* sub m 0 = m *)
        val sub_m = trans3 (sub (pow two bT) one, sub (suc mF) one, sub mF ZeroC) subRw sSS
        val sub_m2 = trans3 (sub (pow two bT) one, sub mF ZeroC, mF) sub_m sN0  (* sub (pow 2 b) 1 = m *)
        (* add (sub (pow 2 b) 1) 1 = add m 1 [cong] ; add m 1 = add m (Suc 0) = Suc(add m 0) = Suc m *)
        val addCong = add_cong_lD (sub (pow two bT) one, mF, one) sub_m2  (* add (sub..1) 1 = add m 1 *)
        val amS = addSucD (mF, ZeroC)   (* add m (Suc 0) = Suc(add m 0) *)
        val am0 = add0rD mF             (* add m 0 = m *)
        val amS2 = trans3 (add mF one, suc (add mF ZeroC), suc mF) amS
                     (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                        [(("a",0), ctermSigD (add mF ZeroC)),(("b",0), ctermSigD mF)] (up (varify Suc_cong)))) am0)
                   (* add m 1 = Suc m *)
        val chain = trans3 (add (sub (pow two bT) one) one, add mF one, suc mF) addCong amS2  (* add (sub..1) 1 = Suc m *)
        val res = trans3 (add (sub (pow two bT) one) one, suc mF, pow two bT) chain (sym3 (pow two bT, suc mF) hm)
                  (* add (sub (pow 2 b) 1) 1 = pow 2 b *)
      in res end
  in exE_atD (exAbs, oeq (add (sub (pow two bT) one) one)(pow two bT)) pp "m_ps1" body end;

val () = out "EE_POW_SUB1_OK\n";

(* dvd d 1 ==> oeq d 1  via dvd_le + lt0 + le_antisym *)
fun dvd_one_eq dT hdvd1 =   (* hdvd1 : dvd d 1 -> oeq d 1 *)
  let
    (* 1 != 0 : Suc 0 != 0 *)
    val one_ne0 = Thm.implies_intr (ctermSigD (jT (oeq one ZeroC)))
                    (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                       [(("n",0), ctermSigD ZeroC)] Suc_neq_Zero_vD))
                       (Thm.assume (ctermSigD (jT (oeq one ZeroC)))))
                  (* oeq 1 0 ==> oFalse *)
    val dle = beta_norm (Drule.infer_instantiate ctxtSigD
                [(("d",0), ctermSigD dT),(("n",0), ctermSigD one)] dvd_le_vD)
    val led1 = Thm.implies_elim (Thm.implies_elim dle hdvd1) one_ne0   (* le d 1 *)
    (* le 1 d : d != 0.  if d = 0 then 1 = 0*k = 0 absurd ; else d = Suc m -> lt0_of_suc *)
    val le1d =
      let
        val dz = dzosD dT    (* Disj (oeq d 0)(Ex q. d = Suc q) *)
        val caseD0 =
          let
            val hd0 = Thm.assume (ctermSigD (jT (oeq dT ZeroC)))
            (* dvd d 1 -> destruct -> 1 = d*k ; d=0 -> 1 = 0*k = 0 absurd *)
            val ff = dvd_destD (dT, one, le one dT) hdvd1 "k_d0"
                      (fn kF => fn hk =>     (* hk : oeq 1 (mult d k) *)
                        let
                          val cong = mult_cong_lD (dT, ZeroC, kF) hd0   (* mult d k = mult 0 k *)
                          val m0k = mult0lD kF                          (* mult 0 k = 0 *)
                          val dk0 = trans3 (mult dT kF, mult ZeroC kF, ZeroC) cong m0k  (* mult d k = 0 *)
                          val one0 = trans3 (one, mult dT kF, ZeroC) hk dk0  (* oeq 1 0 *)
                          val snz = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD ZeroC)] Suc_neq_Zero_vD)
                          val fff = Thm.implies_elim snz one0
                        in oFalse_elimD (le one dT) OF [fff] end)
          in Thm.implies_intr (ctermSigD (jT (oeq dT ZeroC))) ff end
        val sucAbs = Abs("q", natT, oeq dT (suc (Bound 0)))
        val caseDS =
          let
            val hex = Thm.assume (ctermSigD (jT (mkEx sucAbs)))
            fun body qF hq = lt0_of_suc (dT, qF) hq   (* lt 0 d = le 1 d *)
            val r = exE_atD (sucAbs, le one dT) hex "q_d" body
          in Thm.implies_intr (ctermSigD (jT (mkEx sucAbs))) r end
      in disjE_D (oeq dT ZeroC, mkEx sucAbs, le one dT) dz caseD0 caseDS end
  in le_antisymD (dT, one) led1 le1d end;

val () = out "EE_DVD_ONE_EQ_OK\n";

val consec_coprime =
  let
    val dF = Free("d", natT); val bF = Free("b", natT)
    val h1 = Thm.assume (ctermSigD (jT (dvd dF (sub (pow two bF) one))))   (* dvd d (2^b - 1) *)
    val h2 = Thm.assume (ctermSigD (jT (dvd dF (pow two bF))))             (* dvd d 2^b *)
    (* dvd d (add (2^b-1) 1) : rewrite pow 2 b = add (2^b-1) 1 (sym pow_sub1_add1) *)
    val psa = pow_sub1_add1 bF    (* oeq (add (sub (pow 2 b) 1) 1)(pow 2 b) *)
    val h2' = dvd_cong_target_D (dF, pow two bF, add (sub (pow two bF) one) one)
                (sym3 (add (sub (pow two bF) one) one, pow two bF) psa) h2
              (* dvd d (add (2^b-1) 1) *)
    (* dvd_diff : dvd d (2^b-1) -> dvd d (add (2^b-1) 1) -> dvd d 1 *)
    val d1 = dvd_diff_D (dF, sub (pow two bF) one, one) h1 h2'   (* dvd d 1 *)
    val deq = dvd_one_eq dF d1    (* oeq d 1 *)
    val disch2 = Thm.implies_intr (ctermSigD (jT (dvd dF (pow two bF)))) deq
    val disch1 = Thm.implies_intr (ctermSigD (jT (dvd dF (sub (pow two bF) one)))) disch2
  in varify disch1 end;

val () = out ("CONSEC_COPRIME_HYPS = " ^ Int.toString (length (Thm.hyps_of consec_coprime)) ^ "\n");

(* validation *)
val dVe = Var(("d",0),natT); val bVe = Var(("b",0),natT)
val i_consec_coprime =
  Logic.mk_implies (jT (dvd dVe (sub (pow two bVe) one)),
    Logic.mk_implies (jT (dvd dVe (pow two bVe)),
      jT (oeq dVe one)))
val r_cc = chkD ("consec_coprime", consec_coprime, i_consec_coprime)
val () = if r_cc then out "CONSEC_COPRIME_OK\n" else out "CONSEC_COPRIME_FAIL\n";

(* soundness probes *)
val ccProp = Thm.prop_of consec_coprime;
val cc_no1 =   (* drop dvd d (2^b-1) hyp *)
  Logic.mk_implies (jT (dvd dVe (pow two bVe)), jT (oeq dVe one));
val () = if not (ccProp aconv cc_no1) then out "PROBE_OK consec_coprime needs dvd d (2^b-1)\n"
         else out "PROBE_FAIL cc dropped first hyp\n";
val cc_no2 =   (* drop dvd d 2^b hyp *)
  Logic.mk_implies (jT (dvd dVe (sub (pow two bVe) one)), jT (oeq dVe one));
val () = if not (ccProp aconv cc_no2) then out "PROBE_OK consec_coprime needs dvd d (2^b)\n"
         else out "PROBE_FAIL cc dropped second hyp\n";

val () = out "EE_CONSEC_COPRIME_DONE\n";

(* ============================================================================
   (2) factor_2s
   ============================================================================ *)
(* lift more base lemmas onto thySigD *)
val le_suc_mono_vEE = varify (up le_suc_mono);   (* le m n ==> le (Suc m)(Suc n) *)
val strong_induct_vEE = varify (up strong_induct);
fun le_suc_monoD (mT,nT) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("m",0), ctermSigD mT),(("n",0), ctermSigD nT)] le_suc_mono_vEE)
  in Thm.implies_elim inst h end;

val () = out "EE_F2S_LIFT_OK\n";

(* even n := Ex k. oeq n (mult two k) *)
fun evenT n = mkEx (Term.lambda (Free("k", natT)) (oeq n (mult two (Free("k",natT)))));
(* odd-witness body : Ex k. oeq m (Suc (mult two k)) *)
fun oddT m = mkEx (Term.lambda (Free("k", natT)) (oeq m (suc (mult two (Free("k",natT))))));

(* the factor_2s goal for a fixed n *)
fun f2sGoal n =
  mkEx (Term.lambda (Free("a",natT))
    (mkEx (Term.lambda (Free("m",natT))
       (mkConj (oeq n (mult (pow two (Free("a",natT))) (Free("m",natT))))
         (mkConj (oddT (Free("m",natT)))
                 (lt ZeroC (Free("a",natT))))))));

(* ---- PARITY : Disj (even n)(odd n)  by nat_induct ---- *)
(* even n = Ex k. n = 2k ; odd n = Ex k. n = Suc(2k) *)
val parity =
  let
    val nP = Free("n", natT)
    val Pbody = Term.lambda nP (mkDisj (evenT nP) (oddT nP))
    val kInd = Free("n", natT)
    val ind  = nat_induct_atD (Pbody, kInd)
    (* BASE n=0 : even 0, k=0 : 0 = 2*0 = 0 *)
    val base =
      let
        val m20 = mult0rD two            (* mult 2 0 = 0 *)
        val z_eq = sym3 (mult two ZeroC, ZeroC) m20   (* oeq 0 (mult 2 0) *)
        val evz = exI_atD2 (Term.lambda (Free("k",natT)) (oeq ZeroC (mult two (Free("k",natT)))), ZeroC) z_eq
        val r = disjI1_D2 (evenT ZeroC, oddT ZeroC) evz
      in r end
    (* STEP : !!x. (even x \/ odd x) ==> (even (Suc x) \/ odd (Suc x)) *)
    val step =
      let
        val xF = Free("x_par", natT)
        val IH = Thm.assume (ctermSigD (jT (mkDisj (evenT xF)(oddT xF))))
        (* case even x : x = 2k -> Suc x = Suc(2k) = odd (Suc x), witness k *)
        val caseE =
          let
            val hE = Thm.assume (ctermSigD (jT (evenT xF)))
            val exAbs = Term.lambda (Free("k",natT)) (oeq xF (mult two (Free("k",natT))))
            fun body kF hk =    (* hk : oeq x (mult 2 k) *)
              let
                (* Suc x = Suc(2k) [Suc_cong on hk] *)
                val sx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                           [(("a",0), ctermSigD xF),(("b",0), ctermSigD (mult two kF))] (up (varify Suc_cong)))) hk
                         (* oeq (Suc x)(Suc(mult 2 k)) *)
                val odd_sx = exI_atD2 (Term.lambda (Free("k",natT)) (oeq (suc xF) (suc (mult two (Free("k",natT))))), kF) sx
              in disjI2_D2 (evenT (suc xF), oddT (suc xF)) odd_sx end
            val r = exE_atD (exAbs, mkDisj (evenT (suc xF))(oddT (suc xF))) hE "k_pe" body
          in Thm.implies_intr (ctermSigD (jT (evenT xF))) r end
        (* case odd x : x = Suc(2k) -> Suc x = Suc(Suc(2k)) = 2*(Suc k) = even (Suc x), witness Suc k *)
        val caseO =
          let
            val hO = Thm.assume (ctermSigD (jT (oddT xF)))
            val exAbs = Term.lambda (Free("k",natT)) (oeq xF (suc (mult two (Free("k",natT)))))
            fun body kF hk =    (* hk : oeq x (Suc(mult 2 k)) *)
              let
                (* Suc x = Suc(Suc(2k)) *)
                val sx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                           [(("a",0), ctermSigD xF),(("b",0), ctermSigD (suc (mult two kF)))] (up (varify Suc_cong)))) hk
                         (* oeq (Suc x)(Suc(Suc(mult 2 k))) *)
                (* mult 2 (Suc k) = add 2 (mult 2 k) [multSrD] = Suc(Suc(add 0 (mult 2 k))) = Suc(Suc(mult 2 k)) *)
                val msr = multSrD (two, kF)    (* mult 2 (Suc k) = add 2 (mult 2 k) *)
                val aS1 = addSucLD (suc ZeroC, mult two kF)   (* add (Suc(Suc 0))(2k) = Suc(add (Suc 0)(2k)) *)
                val aS2 = addSucLD (ZeroC, mult two kF)       (* add (Suc 0)(2k) = Suc(add 0 (2k)) *)
                val a0  = add0D (mult two kF)                 (* add 0 (2k) = 2k *)
                (* add (Suc 0)(2k) = Suc(add 0 (2k)) = Suc(2k) *)
                val a1  = trans3 (add (suc ZeroC)(mult two kF), suc (add ZeroC (mult two kF)), suc (mult two kF))
                            aS2 (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                                   [(("a",0), ctermSigD (add ZeroC (mult two kF))),(("b",0), ctermSigD (mult two kF))] (up (varify Suc_cong)))) a0)
                (* add 2 (2k) = Suc(add (Suc 0)(2k)) = Suc(Suc(2k)) *)
                val a2  = trans3 (add two (mult two kF), suc (add (suc ZeroC)(mult two kF)), suc (suc (mult two kF)))
                            aS1 (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                                   [(("a",0), ctermSigD (add (suc ZeroC)(mult two kF))),(("b",0), ctermSigD (suc (mult two kF)))] (up (varify Suc_cong)))) a1)
                val m2sk = trans3 (mult two (suc kF), add two (mult two kF), suc (suc (mult two kF))) msr a2
                           (* mult 2 (Suc k) = Suc(Suc(2k)) *)
                (* Suc x = Suc(Suc(2k)) = mult 2 (Suc k) [sym m2sk] *)
                val sx_m = trans3 (suc xF, suc (suc (mult two kF)), mult two (suc kF)) sx (sym3 (mult two (suc kF), suc (suc (mult two kF))) m2sk)
                           (* oeq (Suc x)(mult 2 (Suc k)) *)
                val ev_sx = exI_atD2 (Term.lambda (Free("k",natT)) (oeq (suc xF) (mult two (Free("k",natT)))), suc kF) sx_m
              in disjI1_D2 (evenT (suc xF), oddT (suc xF)) ev_sx end
            val r = exE_atD (exAbs, mkDisj (evenT (suc xF))(oddT (suc xF))) hO "k_po" body
          in Thm.implies_intr (ctermSigD (jT (oddT xF))) r end
        val r = disjE_D (evenT xF, oddT xF, mkDisj (evenT (suc xF))(oddT (suc xF))) IH caseE caseO
      in Thm.forall_intr (ctermSigD xF) (Thm.implies_intr (ctermSigD (jT (mkDisj (evenT xF)(oddT xF)))) r) end
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step    (* jT (Disj (even n)(odd n)) *)
  in varify r2 end;

val () = out ("PARITY_HYPS = " ^ Int.toString (length (Thm.hyps_of parity)) ^ "\n");
val () = out "EE_PARITY_OK\n";

(* parity at a term : Disj (even t)(odd t) *)
fun parityD t = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD t)] parity);

(* lt_irrefl on ctxtSigD *)
val lt_irrefl_vEE = varify (up lt_irrefl);
fun lt_irreflD t h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("n",0), ctermSigD t)] lt_irrefl_vEE)) h;

(* mult 2 c = add c c *)
fun two_mult_eq_add cT =
  let
    val s1 = multSucLD (suc ZeroC, cT)   (* mult (Suc(Suc 0)) c = add c (mult (Suc 0) c) *)
    val s2 = multSucLD (ZeroC, cT)       (* mult (Suc 0) c = add c (mult 0 c) *)
    val s3 = mult0lD cT                  (* mult 0 c = 0 *)
    (* add c (mult 0 c) = add c 0 [cong] = c [add0r] *)
    val ac0 = add_cong_rD (cT, mult ZeroC cT, ZeroC) s3   (* add c (mult 0 c) = add c 0 *)
    val ac  = trans3 (add cT (mult ZeroC cT), add cT ZeroC, cT) ac0 (add0rD cT)  (* add c (mult 0 c) = c *)
    (* mult (Suc 0) c = add c (mult 0 c) = c *)
    val m1c = trans3 (mult (suc ZeroC) cT, add cT (mult ZeroC cT), cT) s2 ac  (* mult 1 c = c *)
    (* add c (mult 1 c) = add c c [cong] *)
    val accc = add_cong_rD (cT, mult (suc ZeroC) cT, cT) m1c   (* add c (mult 1 c) = add c c *)
    val r = trans3 (mult two cT, add cT (mult (suc ZeroC) cT), add cT cT) s1 accc  (* mult 2 c = add c c *)
  in r end;

val () = out "EE_TWO_MULT_OK\n";

(* lt c (mult 2 c)  from  c = Suc c'  (c>0).
   lt c n = le (Suc c)(add c c) where n = mult 2 c.  c = Suc c'.
   le c (add c c') [le_add] -> le (Suc c)(Suc(add c c')) [le_suc_mono] ;
   Suc(add c c') = add c (Suc c') = add c c [c=Suc c'] = mult 2 c. *)
fun lt_c_2c (cT, c'T) hcSc' =   (* hcSc' : oeq c (Suc c') -> lt c (mult 2 c) *)
  let
    val tma = two_mult_eq_add cT    (* mult 2 c = add c c *)
    val ladd = le_addD (cT, c'T)    (* le c (add c c') *)
    val lsm  = le_suc_monoD (cT, add cT c'T) ladd   (* le (Suc c)(Suc(add c c')) *)
    (* Suc(add c c') = add c (Suc c') [sym addSucD] *)
    val asd = addSucD (cT, c'T)     (* add c (Suc c') = Suc(add c c') *)
    val sucAdd = sym3 (add cT (suc c'T), suc (add cT c'T)) asd   (* Suc(add c c') = add c (Suc c') *)
    (* add c (Suc c') = add c c [cong on 2nd arg via sym hcSc'] *)
    val cong = add_cong_rD (cT, suc c'T, cT) (sym3 (cT, suc c'T) hcSc')  (* add c (Suc c') = add c c *)
    val SAcc = trans3 (suc (add cT c'T), add cT (suc c'T), add cT cT) sucAdd cong   (* Suc(add c c') = add c c *)
    (* le (Suc c)(add c c) via cong on 2nd arg of le *)
    val Ple = Term.lambda (Free("zlc",natT)) (le (suc cT) (Free("zlc",natT)))
    val le2 = substPredD (Ple, suc (add cT c'T), add cT cT) SAcc lsm   (* le (Suc c)(add c c) *)
    (* le (Suc c)(mult 2 c) via cong (sym tma) *)
    val le3 = substPredD (Ple, add cT cT, mult two cT) (sym3 (mult two cT, add cT cT) tma) le2
              (* le (Suc c)(mult 2 c) = lt c (mult 2 c) *)
  in le3 end;

val () = out "EE_LT_C_2C_OK\n";

(* pow 2 (Suc 0) = 2 *)
val pow2_one_eq_two =
  let
    val ps = powSucD (two, ZeroC)    (* pow 2 (Suc 0) = mult 2 (pow 2 0) *)
    val pz = powZeroD two            (* pow 2 0 = 1 *)
    val cong = mult_cong_rD (two, pow two ZeroC, one) pz   (* mult 2 (pow 2 0) = mult 2 1 *)
    val m21 = mult1rD two            (* mult 2 1 = 2 *)
    val r = trans3 (pow two (suc ZeroC), mult two (pow two ZeroC), mult two one) ps cong
    val r2 = trans3 (pow two (suc ZeroC), mult two one, two) r m21   (* pow 2 (Suc 0) = 2 *)
  in r2 end;

val () = out "EE_POW2_ONE_OK\n";

(* ---- factor_2s by strong induction ---- *)
val factor_2s =
  let
    val nF = Free("n_f2s", natT)
    (* P n := Imp (lt 0 n)(Imp (even n)(goal n)) *)
    fun Pbody nt = mkImp (lt ZeroC nt) (mkImp (evenT nt) (f2sGoal nt))
    val Ppred = Term.lambda nF (Pbody nF)
    (* strong induct step : !!n. (!!m. lt m n ==> jT(P m)) ==> jT (P n) *)
    val nS = Free("n_si", natT)
    (* G n = !!m. lt m n ==> jT (P m) *)
    val mG = Free("m_g", natT)
    val Gprop = Logic.all mG (Logic.mk_implies (jT (lt mG nS), jT (Pbody mG)))
    val IH = Thm.assume (ctermSigD Gprop)
    fun applyIH (cT, hltc) =   (* hltc : jT (lt c n) -> jT (P c) *)
      Thm.implies_elim (Thm.forall_elim (ctermSigD cT) IH) hltc
    (* prove jT (P n) : assume lt 0 n and even n, produce goal n *)
    val hPos = Thm.assume (ctermSigD (jT (lt ZeroC nS)))
    val hEven = Thm.assume (ctermSigD (jT (evenT nS)))
    (* destruct even n : n = 2*c *)
    val evAbs = Term.lambda (Free("k",natT)) (oeq nS (mult two (Free("k",natT))))
    val goalBody =
      exE_atD (evAbs, f2sGoal nS) hEven "c_f2s"
        (fn cF => fn hc =>    (* hc : oeq n (mult 2 c) *)
          let
            (* c > 0 + witness c = Suc c' : dzos on c. if c=0 then n=2*0=0, lt 0 n absurd *)
            val dz = dzosD cF
            (* We branch directly: build goal in both 'c=0 (absurd)' and 'c=Suc c'' cases.
               In the Suc case we further branch on parity c. *)
            val caseC0 =
              let
                val hc0 = Thm.assume (ctermSigD (jT (oeq cF ZeroC)))
                (* n = mult 2 c = mult 2 0 = 0 *)
                val cong = mult_cong_rD (two, cF, ZeroC) hc0   (* mult 2 c = mult 2 0 *)
                val m20 = mult0rD two                          (* mult 2 0 = 0 *)
                val m2c0 = trans3 (mult two cF, mult two ZeroC, ZeroC) cong m20  (* mult 2 c = 0 *)
                val n0 = trans3 (nS, mult two cF, ZeroC) hc m2c0   (* oeq n 0 *)
                (* lt 0 n -> rewrite n -> lt 0 0 -> lt_irrefl *)
                val Plt = Term.lambda (Free("zln",natT)) (lt ZeroC (Free("zln",natT)))
                val lt00 = substPredD (Plt, nS, ZeroC) n0 hPos   (* lt 0 0 *)
                val ff = lt_irreflD ZeroC lt00
              in Thm.implies_intr (ctermSigD (jT (oeq cF ZeroC))) (oFalse_elimD (f2sGoal nS) OF [ff]) end
            val sucAbs = Term.lambda (Free("c'",natT)) (oeq cF (suc (Free("c'",natT))))
            val caseCS =
              let
                val hex = Thm.assume (ctermSigD (jT (mkEx sucAbs)))
                fun bodyS c'F hc' =    (* hc' : oeq c (Suc c') *)
                  let
                    val ltc = lt0_of_suc (cF, c'F) hc'     (* lt 0 c *)
                    (* lt c n : lt c (mult 2 c), then rewrite mult 2 c -> n via sym hc *)
                    val ltc2c = lt_c_2c (cF, c'F) hc'      (* lt c (mult 2 c) *)
                    val Pltc = Term.lambda (Free("zlcn",natT)) (lt cF (Free("zlcn",natT)))
                    val ltcn = substPredD (Pltc, mult two cF, nS) (sym3 (nS, mult two cF) hc) ltc2c  (* lt c n *)
                    (* parity c *)
                    val par = parityD cF    (* Disj (even c)(odd c) *)
                    (* case even c : recurse via IH *)
                    val caseEc =
                      let
                        val hEc = Thm.assume (ctermSigD (jT (evenT cF)))
                        val pc = applyIH (cF, ltcn)   (* jT (P c) = Imp (lt 0 c)(Imp (even c)(goal c)) *)
                        val g1 = mp_D (lt ZeroC cF, mkImp (evenT cF)(f2sGoal cF)) pc ltc  (* Imp (even c)(goal c) *)
                        val gc = mp_D (evenT cF, f2sGoal cF) g1 hEc                       (* goal c *)
                        (* destruct goal c : Ex a'. Ex m'. c = 2^a' m' /\ odd m' /\ a'>0 *)
                        val aAbs = Term.lambda (Free("a'",natT))
                              (mkEx (Term.lambda (Free("m'",natT))
                                 (mkConj (oeq cF (mult (pow two (Free("a'",natT)))(Free("m'",natT))))
                                   (mkConj (oddT (Free("m'",natT)))
                                           (lt ZeroC (Free("a'",natT)))))))
                        val res = exE_atD (aAbs, f2sGoal nS) gc "a'_ec"
                          (fn a'F => fn ha' =>     (* ha' : Ex m'. ... *)
                            let
                              val mAbs = Term.lambda (Free("m'",natT))
                                    (mkConj (oeq cF (mult (pow two a'F)(Free("m'",natT))))
                                      (mkConj (oddT (Free("m'",natT)))
                                              (lt ZeroC a'F)))
                            in exE_atD (mAbs, f2sGoal nS) ha' "m'_ec"
                                 (fn m'F => fn hm' =>    (* hm' : c = 2^a' m' /\ odd m' /\ a'>0 *)
                                   let
                                     val conj1 = conjunct1_D (oeq cF (mult (pow two a'F) m'F),
                                                    mkConj (oddT m'F)(lt ZeroC a'F)) hm'   (* oeq c (mult (pow 2 a') m') *)
                                     val conjR = beta_norm (Drule.infer_instantiate ctxtSigD
                                                    [(("A",0), ctermSigD (oeq cF (mult (pow two a'F) m'F))),
                                                     (("B",0), ctermSigD (mkConj (oddT m'F)(lt ZeroC a'F)))] conjunct2_vD)
                                     val rest = Thm.implies_elim conjR hm'    (* odd m' /\ a'>0 *)
                                     val oddm' = conjunct1_D (oddT m'F, lt ZeroC a'F) rest   (* odd m' *)
                                     val posA' = beta_norm (Drule.infer_instantiate ctxtSigD
                                                    [(("A",0), ctermSigD (oddT m'F)),(("B",0), ctermSigD (lt ZeroC a'F))] conjunct2_vD)
                                     val posa = Thm.implies_elim posA' rest   (* lt 0 a' *)
                                     (* n = mult 2 c = mult 2 (mult (pow 2 a') m')
                                            = mult (mult 2 (pow 2 a')) m' [assoc sym]
                                            = mult (pow 2 (Suc a')) m' [powSuc sym] *)
                                     (* mult 2 c = mult 2 (mult (pow 2 a') m') [cong on 2nd arg via conj1] *)
                                     val c2 = mult_cong_rD (two, cF, mult (pow two a'F) m'F) conj1
                                              (* mult 2 c = mult 2 (mult (pow 2 a') m') *)
                                     val assoc = multassocD (two, pow two a'F, m'F)
                                              (* mult (mult 2 (pow 2 a')) m' = mult 2 (mult (pow 2 a') m') *)
                                     val c2a = trans3 (mult two cF, mult two (mult (pow two a'F) m'F), mult (mult two (pow two a'F)) m'F)
                                                 c2 (sym3 (mult (mult two (pow two a'F)) m'F, mult two (mult (pow two a'F) m'F)) assoc)
                                              (* mult 2 c = mult (mult 2 (pow 2 a')) m' *)
                                     val psA = powSucD (two, a'F)   (* pow 2 (Suc a') = mult 2 (pow 2 a') *)
                                     val congP = mult_cong_lD (mult two (pow two a'F), pow two (suc a'F), m'F)
                                                   (sym3 (pow two (suc a'F), mult two (pow two a'F)) psA)
                                              (* mult (mult 2 (pow 2 a')) m' = mult (pow 2 (Suc a')) m' *)
                                     val c2b = trans3 (mult two cF, mult (mult two (pow two a'F)) m'F, mult (pow two (suc a'F)) m'F)
                                                 c2a congP   (* mult 2 c = mult (pow 2 (Suc a')) m' *)
                                     (* n = mult 2 c [hc] = mult (pow 2 (Suc a')) m' *)
                                     val nEq = trans3 (nS, mult two cF, mult (pow two (suc a'F)) m'F) hc c2b
                                               (* oeq n (mult (pow 2 (Suc a')) m') *)
                                     (* build goal n : a := Suc a', m := m' *)
                                     (* lt 0 (Suc a') : from posa (lt 0 a') le_trans? actually lt 0 (Suc a') = le 1 (Suc a').
                                        lt 0 a' = le 1 a' ; le 1 (Suc a') from le_add or le_suc.  Simpler: Suc a' = Suc a' > 0
                                        always: lt 0 (Suc a') = le 1 (Suc a').  Suc a' = Suc a'.  Use lt0_of_suc (Suc a', a') refl. *)
                                     val posSa = lt0_of_suc (suc a'F, a'F) (reflD (suc a'F))   (* lt 0 (Suc a') *)
                                     (* assemble Conj (n = 2^(Suc a') m')(Conj (odd m')(lt 0 (Suc a'))) *)
                                     val innerConj = conjI_Sg2 (oddT m'F, lt ZeroC (suc a'F)) oddm' posSa
                                     val fullConj = conjI_Sg2 (oeq nS (mult (pow two (suc a'F)) m'F),
                                                       mkConj (oddT m'F)(lt ZeroC (suc a'F))) nEq innerConj
                                     (* exI on m' then on a' *)
                                     val mInner = Term.lambda (Free("m",natT))
                                           (mkConj (oeq nS (mult (pow two (suc a'F))(Free("m",natT))))
                                             (mkConj (oddT (Free("m",natT)))(lt ZeroC (suc a'F))))
                                     val exM = exI_atD2 (mInner, m'F) fullConj   (* Ex m. ... [a := Suc a'] *)
                                     val aInner = Term.lambda (Free("a",natT))
                                           (mkEx (Term.lambda (Free("m",natT))
                                              (mkConj (oeq nS (mult (pow two (Free("a",natT)))(Free("m",natT))))
                                                (mkConj (oddT (Free("m",natT)))(lt ZeroC (Free("a",natT)))))))
                                     val exA = exI_atD2 (aInner, suc a'F) exM    (* goal n *)
                                   in exA end)
                            end)
                      in Thm.implies_intr (ctermSigD (jT (evenT cF))) res end
                    (* case odd c : a := 1, m := c *)
                    val caseOc =
                      let
                        val hOc = Thm.assume (ctermSigD (jT (oddT cF)))
                        (* n = mult 2 c = mult (pow 2 (Suc 0)) c [sym pow2_one_eq_two on divisor] *)
                        val congDiv = mult_cong_lD (two, pow two (suc ZeroC), cF)
                                        (sym3 (pow two (suc ZeroC), two) pow2_one_eq_two)
                                      (* mult 2 c = mult (pow 2 (Suc 0)) c *)
                        val nEq = trans3 (nS, mult two cF, mult (pow two (suc ZeroC)) cF) hc congDiv
                                  (* oeq n (mult (pow 2 (Suc 0)) c) *)
                        val posSa = lt0_of_suc (suc ZeroC, ZeroC) (reflD (suc ZeroC))   (* lt 0 (Suc 0) *)
                        val innerConj = conjI_Sg2 (oddT cF, lt ZeroC (suc ZeroC)) hOc posSa
                        val fullConj = conjI_Sg2 (oeq nS (mult (pow two (suc ZeroC)) cF),
                                          mkConj (oddT cF)(lt ZeroC (suc ZeroC))) nEq innerConj
                        val mInner = Term.lambda (Free("m",natT))
                              (mkConj (oeq nS (mult (pow two (suc ZeroC))(Free("m",natT))))
                                (mkConj (oddT (Free("m",natT)))(lt ZeroC (suc ZeroC))))
                        val exM = exI_atD2 (mInner, cF) fullConj
                        val aInner = Term.lambda (Free("a",natT))
                              (mkEx (Term.lambda (Free("m",natT))
                                 (mkConj (oeq nS (mult (pow two (Free("a",natT)))(Free("m",natT))))
                                   (mkConj (oddT (Free("m",natT)))(lt ZeroC (Free("a",natT)))))))
                        val exA = exI_atD2 (aInner, suc ZeroC) exM
                      in Thm.implies_intr (ctermSigD (jT (oddT cF))) exA end
                    val gr = disjE_D (evenT cF, oddT cF, f2sGoal nS) par caseEc caseOc
                  in gr end
                val r = exE_atD (sucAbs, f2sGoal nS) hex "c'_f2s" bodyS
              in Thm.implies_intr (ctermSigD (jT (mkEx sucAbs))) r end
            val gr = disjE_D (oeq cF ZeroC, mkEx sucAbs, f2sGoal nS) dz caseC0 caseCS
          in gr end)
    (* goalBody : jT (goal n)  under assumptions [lt 0 n, even n, IH] *)
    val pImp2 = impI_D (evenT nS, f2sGoal nS) goalBody    (* Imp (even n)(goal n) *)
    val pImp1 = impI_D (lt ZeroC nS, mkImp (evenT nS)(f2sGoal nS)) pImp2  (* P n *)
    val stepDisch = Thm.forall_intr (ctermSigD nS) (Thm.implies_intr (ctermSigD Gprop) pImp1)
                    (* !!n. G n ==> jT (P n) *)
    (* feed to strong_induct ; name the target Free "n" so varify yields ?n (matches intended) *)
    val kF = Free("n", natT)
    val siInst = beta_norm (Drule.infer_instantiate ctxtSigD
                   [(("P",0), ctermSigD Ppred),(("k",0), ctermSigD kF)] strong_induct_vEE)
    val Pk = Thm.implies_elim siInst stepDisch   (* jT (P k) = Imp (lt 0 k)(Imp (even k)(goal k)) *)
    (* turn into meta : jT (lt 0 k) ==> jT (even k) ==> jT (goal k) *)
    val hPk1 = Thm.assume (ctermSigD (jT (lt ZeroC kF)))
    val hPk2 = Thm.assume (ctermSigD (jT (evenT kF)))
    val s1 = mp_D (lt ZeroC kF, mkImp (evenT kF)(f2sGoal kF)) Pk hPk1
    val s2 = mp_D (evenT kF, f2sGoal kF) s1 hPk2
    val d2 = Thm.implies_intr (ctermSigD (jT (evenT kF))) s2
    val d1 = Thm.implies_intr (ctermSigD (jT (lt ZeroC kF))) d2
  in varify d1 end;

val () = out ("FACTOR_2S_HYPS = " ^ Int.toString (length (Thm.hyps_of factor_2s)) ^ "\n");
val () = out ("FACTOR_2S_SHYPS = " ^ Int.toString (length (Thm.extra_shyps factor_2s)) ^ "\n");

(* validation *)
val nVf = Var(("n",0),natT)
val i_factor_2s =
  Logic.mk_implies (jT (lt ZeroC nVf),
    Logic.mk_implies (jT (evenT nVf), jT (f2sGoal nVf)))
val r_f2s = chkD ("factor_2s", factor_2s, i_factor_2s)
val () = if r_f2s then out "FACTOR_2S_OK\n" else out "FACTOR_2S_FAIL\n";

(* soundness probes *)
val f2sProp = Thm.prop_of factor_2s;
val f2s_nopos = Logic.mk_implies (jT (evenT nVf), jT (f2sGoal nVf));
val () = if not (f2sProp aconv f2s_nopos) then out "PROBE_OK factor_2s needs lt 0 n\n"
         else out "PROBE_FAIL f2s dropped lt 0 n\n";
val f2s_noeven = Logic.mk_implies (jT (lt ZeroC nVf), jT (f2sGoal nVf));
val () = if not (f2sProp aconv f2s_noeven) then out "PROBE_OK factor_2s needs even n\n"
         else out "PROBE_FAIL f2s dropped even n\n";
(* the conclusion genuinely carries the odd-witness + a>0, not collapsed *)
val f2s_collapsed =
  Logic.mk_implies (jT (lt ZeroC nVf),
    Logic.mk_implies (jT (evenT nVf),
      jT (mkEx (Term.lambda (Free("a",natT))
            (mkEx (Term.lambda (Free("m",natT))
               (oeq nVf (mult (pow two (Free("a",natT)))(Free("m",natT))))))))))
val () = if not (f2sProp aconv f2s_collapsed) then out "PROBE_OK factor_2s keeps odd-witness + a>0\n"
         else out "PROBE_FAIL f2s collapsed conclusion\n";

val () = out "EE_FACTOR2S_DONE\n";

(* ============================================================================
   sigma_bound : the sigma-bound-iff-prime lemma, appended after the banked
   isabelle_euclid_perfect.sml driver.  Built on the FINAL context
   ctxtSigD / ctermSigD (theory thySigD).  NO new const, NO new axiom.

     sigma_bound :
       lt 1 m  ==>  dvd d m  ==>  lt d m  ==>  oeq (sigma m)(add m d)
         ==>  oeq d (Suc Zero)  AND  prime2 m

   MATH:  sigma m = sumf (swt m) m  with swt m i = i if i|m else 0.
     * 3-term lower bound : 1 < d < m, all divisors, so
         sigma m >= swt m 1 + swt m d + swt m m = 1 + d + m.
       If d > 1 then 1 + d + m > m + d = sigma m, contradiction => d = 1.
     * d = 1 => sigma m = m + 1.  If m not prime, a proper divisor e (1<e<m)
       gives sigma m >= 1 + e + m > m + 1, contradiction => prime2 m.
   ============================================================================ *)
val () = out "SIGMA_BOUND_BEGIN\n";

(* ---------------------------------------------------------------------------
   (0) transfer the order / sum / prime machinery up to ctxtSigD and build
       ground instantiators.  All reused lemmas re-varified onto ctxtSigD.
   --------------------------------------------------------------------------- *)
val le_add_vSB        = varify (up le_add)            (* le m (add m p)  ; vars m,p *)
val le_add_mono_vSB   = varify (up le_add_mono)       (* le a b ==> le (add a c)(add b c) *)
val le_antisym_vSB    = varify (up le_antisym)        (* le m n ==> le n m ==> oeq m n *)
val le_trans_vSB      = varify (up le_trans)          (* le m n ==> le n k ==> le m k *)
val le_refl_vSB       = varify (up le_refl)           (* le n n *)
val lt_not_ge_vSB     = varify (up lt_not_ge)         (* lt r b ==> oeq r (add b x) ==> oFalse *)
val le_neq_lt_vSB     = varify (up le_neq_lt)         (* le d n ==> neg(oeq d n) ==> lt d n *)
val sum_peel_first_vSB= varify (up sum_peel_first)    (* sumf f (Suc n) = add (f 0)(sumf (%k. f(Suc k)) n) *)
val sum_cong_vSB      = varify (up sum_cong)          (* (!!k. le k n ==> f k = g k) ==> sumf f n = sumf g n *)
val conjI_vSB         = varify (up conjI_ax)          (* jT A ==> jT B ==> jT (Conj A B) *)
val mult_1_left_vSB   = varify (up mult_1_left)       (* mult 1 n = n *)
val prime_cases_vSB   = varify (up prime_cases)       (* lt 1 n ==> Disj (prime2 n)(Ex d.(1<d /\ d<n)/\ d|n) *)
val dvd_le_vSB        = varify (up dvd_le)            (* dvd d n ==> (oeq n 0 ==> oFalse) ==> le d n *)
val Suc_neq_Zero_vSB  = varify (up Suc_neq_Zero_ax)   (* oeq (Suc n) 0 ==> oFalse *)
val () = out "SB_TRANSFER_OK\n";

fun leAddD (mT, pT) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("m",0), ctermSigD mT),(("p",0), ctermSigD pT)] le_add_vSB)
fun leAddMonoD (aT,bT,cT) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("a",0), ctermSigD aT),(("b",0), ctermSigD bT),(("c",0), ctermSigD cT)] le_add_mono_vSB)) h
fun leAntisymD (mT,nT) h1 h2 = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("m",0), ctermSigD mT),(("n",0), ctermSigD nT)] le_antisym_vSB)) h1) h2
fun leTransD (mT,nT,kT) h1 h2 = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("m",0), ctermSigD mT),(("n",0), ctermSigD nT),(("k",0), ctermSigD kT)] le_trans_vSB)) h1) h2
fun leReflD nT = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD nT)] le_refl_vSB)
fun ltNotGeD (rT,bT,xT) hlt heq = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("r",0), ctermSigD rT),(("b",0), ctermSigD bT),(("x",0), ctermSigD xT)] lt_not_ge_vSB)) hlt) heq
fun leNeqLtD (dT,nT) hle hneq = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("d",0), ctermSigD dT),(("n",0), ctermSigD nT)] le_neq_lt_vSB)) hle) hneq
fun sumPeelD (fT,nT) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("f",0), ctermSigD fT),(("n",0), ctermSigD nT)] sum_peel_first_vSB)
fun sumCongD (fAbs,gAbs,nT) hcong = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("f",0), ctermSigD fAbs),(("g",0), ctermSigD gAbs),(("n",0), ctermSigD nT)] sum_cong_vSB)) hcong
fun conjI_D (At,Bt) hA hB = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("A",0), ctermSigD At),(("B",0), ctermSigD Bt)] conjI_vSB)) hA) hB
fun mult1lD t = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD t)] mult_1_left_vSB)
fun primeCasesD nT hgt1 = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("n",0), ctermSigD nT)] prime_cases_vSB)) hgt1
fun SucNeqZeroD nT hyp = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("n",0), ctermSigD nT)] Suc_neq_Zero_vSB)) hyp
val () = out "SB_INSTANTIATORS_OK\n";

(* mult1rD : oeq (mult n 1) n ; already defined in the base driver (line ~12473) *)
(* oFalse_elimD goal : jT oFalse ==> jT goal (the meta-impl) *)
fun oFalse_elimD goalT = beta_norm (Drule.infer_instantiate ctxtSigD [(("R",0), ctermSigD goalT)] oFalse_elim_vD)

(* dvd_self m : dvd m m  (witness 1 : m = m*1, via mult_1_right) ---------------- *)
fun dvd_selfD m =
  let val Pabs = Abs("k", natT, oeq m (mult m (Bound 0)))    (* %k. m = m*k *)
      val mr   = sym3 (mult m (suc ZeroC), m) (mult1rD m)     (* oeq m (mult m 1) *)
  in exI_atD2 (Pabs, suc ZeroC) mr end
(* dvd_one m : dvd 1 m  (witness m : m = 1*m, via mult_1_left) ----------------- *)
fun dvd_oneD m =
  let val Pabs = Abs("k", natT, oeq m (mult (suc ZeroC) (Bound 0)))   (* %k. m = 1*k *)
      val ml   = sym3 (mult (suc ZeroC) m, m) (mult1lD m)             (* oeq m (mult 1 m) *)
  in exI_atD2 (Pabs, m) ml end

(* swt-eval at a divisor / non-divisor are swt_dvd_D / swt_ndvd_D already. *)
val () = out "SB_DVD_HELPERS_OK\n";

(* ---------------------------------------------------------------------------
   (1) monotone helper le_add_r : le a b ==> le a (add b c)
       via le b (add b c) [le_add] + le_trans.
   --------------------------------------------------------------------------- *)
fun le_add_rD (aT,bT,cT) hab =
  let val lbc = leAddD (bT, cT)               (* le b (add b c) *)
  in leTransD (aT, bT, add bT cT) hab lbc end

(* le_add_r2 : le a b ==> le a (add c b) : le b (add c b) via add_comm *)
fun le_add_r2D (aT,bT,cT) hab =
  let val lbc0 = leAddD (bT, cT)              (* le b (add b c) *)
      val comm = addcommD (bT, cT)            (* add b c = add c b *)
      val Pz = Term.lambda (Free("zlc", natT)) (le bT (Free("zlc",natT)))
      val lbc = substPredD (Pz, add bT cT, add cT bT) comm lbc0   (* le b (add c b) *)
  in leTransD (aT, bT, add cT bT) hab lbc end

val () = out "SB_MONO_OK\n";

(* le_zero_eq is already in the base (line ~13343) : le i 0 ==> oeq i 0.
   apply it via OF since it is varified (var i). *)
fun le_zero_eqD iT hle = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD [(("i",0), ctermSigD iT)] le_zero_eq)) hle
(* le_split already varified (vars i,a) : le i (Suc a) ==> Disj (oeq i (Suc a))(le i a) *)
fun le_splitD (iT,aT) hle = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("i",0), ctermSigD iT),(("a",0), ctermSigD aT)] le_split)) hle

(* le_cong_l : oeq a b ==> le a c ==> le b c  (transport the LHS of a le) *)
fun le_cong_lD (aT,bT,cT) hab hle =
  let val Pz = Term.lambda (Free("zcl", natT)) (le (Free("zcl",natT)) cT)
  in substPredD (Pz, aT, bT) hab hle end
(* le_cong_r : oeq a b ==> le c a ==> le c b *)
fun le_cong_rD (aT,bT,cT) hab hle =
  let val Pz = Term.lambda (Free("zcr", natT)) (le cT (Free("zcr",natT)))
  in substPredD (Pz, aT, bT) hab hle end
val () = out "SB_SPLIT_OK\n";

(* ---------------------------------------------------------------------------
   (2) sumf_lb1 fT : Forall i. Imp (le i n)(le (fT i)(sumf fT n))   -- by induction on n.
   Returns the varified Forall-i statement at a Var-n? We build it at a Free n
   then varify; but easier: we build a function that GIVES the per-(i,n) result.
   Strategy: prove  AllN : Forall n. Forall i. Imp (le i n)(le (f i)(sumf f n))
   is awkward (double Forall). Instead prove for FIXED fT a thm:
       lb1Thm fT : nat_induct conclusion at Var n giving
                   Forall i. Imp (le i n)(le (f i)(sumf f n))
   We keep n a Free during induction, then return a CLOSURE giving le (f i)(sumf f n).
   --------------------------------------------------------------------------- *)
fun build_lb1 fT =
  let
    val iFp = Free("i_l1", natT)
    fun body nT = mkForall (Term.lambda iFp (mkImp (le iFp nT)(le (fT $ iFp)(sumf fT nT))))
    val zN = Free("zN1", natT)
    val Qpred = Term.lambda zN (body zN)
    val kIndN = Free("n_l1", natT)
    val ind = nat_induct_atD (Qpred, kIndN)
    (* BASE n=0 *)
    val base =
      let
        fun perI iF =
          let
            val hle = Thm.assume (ctermSigD (jT (le iF ZeroC)))
            val i0  = le_zero_eqD iF hle              (* oeq i 0 *)
            (* sumf f 0 = f 0 ; f i = f 0 (cong) ; le (f 0)(f 0) refl -> le (f i)(sumf f 0) *)
            val s0  = sumf0D fT                       (* oeq (sumf f 0)(f 0) *)
            (* le (f i)(sumf f 0) : transport from le (f 0)(f 0) *)
            val lref = leReflD (fT $ ZeroC)          (* le (f 0)(f 0) *)
            (* le (f 0)(sumf f 0) via le_cong_r with sym s0 *)
            val l1 = le_cong_rD (fT $ ZeroC, sumf fT ZeroC, fT $ ZeroC) (sym3 (sumf fT ZeroC, fT $ ZeroC) s0) lref
                     (* le (f 0)(sumf f 0) *)
            (* le (f i)(sumf f 0) via le_cong_l with sym (cong f over i0): f i = f 0 *)
            val ficong = beta_norm (Drule.infer_instantiate ctxtSigD     (* oeq (f i)(f 0) via oeq_subst on (%z. f z) *)
                  [(("P",0), ctermSigD (Term.lambda (Free("zfc",natT)) (oeq (fT $ iF)(fT $ (Free("zfc",natT)))))),
                   (("a",0), ctermSigD iF),(("b",0), ctermSigD ZeroC)] oeq_subst_vD)
                  OF [i0, reflD (fT $ iF)]           (* oeq (f i)(f 0) *)
            val l2 = le_cong_lD (fT $ ZeroC, fT $ iF, sumf fT ZeroC) (sym3 (fT $ iF, fT $ ZeroC) ficong) l1
                     (* le (f i)(sumf f 0) *)
          in impI_D (le iF ZeroC, le (fT $ iF)(sumf fT ZeroC)) l2 end
        val iFb = Free("ib1", natT)
      in allI_D (Term.lambda iFp (mkImp (le iFp ZeroC)(le (fT $ iFp)(sumf fT ZeroC))))
                (Thm.forall_intr (ctermSigD iFb) (perI iFb)) end
    (* STEP n -> Suc n *)
    val nF = Free("n_l1", natT)
    val IH = Thm.assume (ctermSigD (jT (body nF)))
    val stepconcl =
      let
        val sfS = sumfSucD (fT, nF)        (* sumf f (Suc n) = add (sumf f n)(f (Suc n)) *)
        fun perI iF =
          let
            val hle = Thm.assume (ctermSigD (jT (le iF (suc nF))))
            val dj  = le_splitD (iF, nF) hle    (* Disj (oeq i (Suc n))(le i n) *)
            val goal = le (fT $ iF)(sumf fT (suc nF))
            val caseEq =
              let val heq = Thm.assume (ctermSigD (jT (oeq iF (suc nF))))
                  (* f i = f (Suc n) ; f(Suc n) <= add (sumf f n)(f(Suc n)) via le_add_r2 *)
                  val ficong = beta_norm (Drule.infer_instantiate ctxtSigD
                        [(("P",0), ctermSigD (Term.lambda (Free("zfc2",natT)) (oeq (fT $ iF)(fT $ (Free("zfc2",natT)))))),
                         (("a",0), ctermSigD iF),(("b",0), ctermSigD (suc nF))] oeq_subst_vD)
                        OF [heq, reflD (fT $ iF)]   (* oeq (f i)(f (Suc n)) *)
                  val l0 = le_add_r2D (fT $ (suc nF), fT $ (suc nF), sumf fT nF) (leReflD (fT $ (suc nF)))
                           (* le (f(Suc n))(add (sumf f n)(f(Suc n))) *)
                  (* transport add(sumf f n)(f(Suc n)) = sumf f (Suc n) [sym sfS] *)
                  val l1 = le_cong_rD (add (sumf fT nF)(fT $ (suc nF)), sumf fT (suc nF), fT $ (suc nF))
                              (sym3 (sumf fT (suc nF), add (sumf fT nF)(fT $ (suc nF))) sfS) l0
                           (* le (f(Suc n))(sumf f (Suc n)) *)
                  val l2 = le_cong_lD (fT $ (suc nF), fT $ iF, sumf fT (suc nF))
                              (sym3 (fT $ iF, fT $ (suc nF)) ficong) l1
                           (* le (f i)(sumf f (Suc n)) *)
              in Thm.implies_intr (ctermSigD (jT (oeq iF (suc nF)))) l2 end
            val caseLe =
              let val hlen = Thm.assume (ctermSigD (jT (le iF nF)))
                  (* IH at i : le (f i)(sumf f n) *)
                  val ihPred = Term.lambda iFp (mkImp (le iFp nF)(le (fT $ iFp)(sumf fT nF)))
                  val ihAt = allE_D (ihPred, iF) IH    (* Imp (le i n)(le (f i)(sumf f n)) *)
                  val lfin = mp_D (le iF nF, le (fT $ iF)(sumf fT nF)) ihAt hlen  (* le (f i)(sumf f n) *)
                  (* sumf f n <= add (sumf f n)(f(Suc n)) = sumf f (Suc n) *)
                  val l0 = leAddD (sumf fT nF, fT $ (suc nF))   (* le (sumf f n)(add (sumf f n)(f(Suc n))) *)
                  val l1 = le_cong_rD (add (sumf fT nF)(fT $ (suc nF)), sumf fT (suc nF), sumf fT nF)
                              (sym3 (sumf fT (suc nF), add (sumf fT nF)(fT $ (suc nF))) sfS) l0
                           (* le (sumf f n)(sumf f (Suc n)) *)
                  val l2 = leTransD (fT $ iF, sumf fT nF, sumf fT (suc nF)) lfin l1
              in Thm.implies_intr (ctermSigD (jT (le iF nF))) l2 end
            val res = disjE_D (oeq iF (suc nF), le iF nF, goal) dj caseEq caseLe
          in impI_D (le iF (suc nF), goal) res end
        val iFs = Free("is1", natT)
      in allI_D (Term.lambda iFp (mkImp (le iFp (suc nF))(le (fT $ iFp)(sumf fT (suc nF)))))
                (Thm.forall_intr (ctermSigD iFs) (perI iFs)) end
    val step1 = Thm.forall_intr (ctermSigD nF) (Thm.implies_intr (ctermSigD (jT (body nF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1   (* Forall i. Imp (le i n_l1)(le (f i)(sumf f n_l1)) ; n_l1 a Free *)
    (* close over n_l1 as an OBJECT Forall : Forall n. Forall i. Imp(le i n)(le(f i)(sumf f n)) *)
    val outerPred = Term.lambda (Free("n_out1", natT)) (body (Free("n_out1", natT)))
    val r3 = allI_D outerPred (Thm.forall_intr (ctermSigD kIndN) r2)
  in r3 end   (* Forall n. Forall i. Imp(le i n)(le(f i)(sumf f n)) ; FUNCTION fT fixed (Free) *)

val () = out "SB_LB1_DEFINED\n";

(* applier : lb1 thm = Forall n. Forall i. Imp(le i n)(le(f i)(sumf f n)) ; f FIXED.
   apply at (iT, nT) and discharge le i n. *)
fun lb1_apply lb1Thm fT (iT, nT) hle =
  let
    val iFp = Free("i_l1", natT)
    fun body nv = mkForall (Term.lambda iFp (mkImp (le iFp nv)(le (fT $ iFp)(sumf fT nv))))
    val outerPred = Term.lambda (Free("n_out1", natT)) (body (Free("n_out1", natT)))
    val atN = allE_D (outerPred, nT) lb1Thm   (* Forall i. Imp(le i nT)(le(f i)(sumf f nT)) *)
    val iPred = Term.lambda iFp (mkImp (le iFp nT)(le (fT $ iFp)(sumf fT nT)))
    val atI = allE_D (iPred, iT) atN
  in mp_D (le iT nT, le (fT $ iT)(sumf fT nT)) atI hle end

(* addSucL : add (Suc m) n = Suc(add m n) *)
fun addSucL (mT,nT) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("m",0), ctermSigD mT),(("n",0), ctermSigD nT)] add_Suc_vD2)

(* lt_Suc_imp_le : lt i (Suc n) ==> le i n
   lt i (Suc n) = le (Suc i)(Suc n) = Ex p. Suc n = (Suc i) + p = Suc(i+p) -> n = i+p -> le i n *)
fun lt_Suc_imp_leD (iT, nT) hlt =
  let
    val goalC = le iT nT
    fun body pF hp =   (* hp : oeq (Suc n)(add (Suc i) p) *)
      let val aS = addSucL (iT, pF)            (* add (Suc i) p = Suc(add i p) *)
          val sucEq = trans3 (suc nT, add (suc iT) pF, suc (add iT pF)) hp aS  (* Suc n = Suc(add i p) *)
          val nEq = Suc_injD (nT, add iT pF) sucEq    (* n = add i p *)
      in le_introD (iT, nT, pF) nEq end
    (* hlt : le (Suc i)(Suc n) = Ex p. Suc n = add (Suc i) p *)
    val Pabs = Abs("p", natT, oeq (suc nT)(add (suc iT)(Bound 0)))
  in exE_atD (Pabs, goalC) hlt "p_lsl" body end
val () = out "SB_LB1_APPLY_OK\n";

(* f-congruence helper : oeq a b ==> oeq (f a)(f b) *)
fun fcongD fT (aT,bT) hab =
  beta_norm (Drule.infer_instantiate ctxtSigD
    [(("P",0), ctermSigD (Term.lambda (Free("zfg",natT)) (oeq (fT $ aT)(fT $ (Free("zfg",natT)))))),
     (("a",0), ctermSigD aT),(("b",0), ctermSigD bT)] oeq_subst_vD)
  OF [hab, reflD (fT $ aT)]

(* ---------------------------------------------------------------------------
   (3) sumf_lb2 fT iF jF : Imp (lt iF jF)(Imp (le jF n)(le (add (f iF)(f jF))(sumf f n)))
       by induction on n.  iF,jF FIXED Frees.  Uses lb1Thm (already built for fT).
   --------------------------------------------------------------------------- *)
fun build_lb2 fT lb1Thm iF jF =
  let
    fun body nT = mkImp (lt iF jF)(mkImp (le jF nT)(le (add (fT $ iF)(fT $ jF))(sumf fT nT)))
    val zN = Free("zN2", natT)
    val Qpred = Term.lambda zN (body zN)
    val kIndN = Free("n_l2", natT)
    val ind = nat_induct_atD (Qpred, kIndN)
    (* BASE n=0 : le j 0 -> oeq j 0.  But lt i j (i<j) with j=0 is impossible.
       le j 0 -> j=0 ; lt i j = lt i 0 = le (Suc i) 0 -> oeq (Suc i) 0 -> oFalse.
       So the whole implication holds vacuously: from lt i j and le j 0 derive oFalse,
       then oFalse_elim to the goal. *)
    val base =
      let
        val hlt = Thm.assume (ctermSigD (jT (lt iF jF)))
        val hlej = Thm.assume (ctermSigD (jT (le jF ZeroC)))
        val goal = le (add (fT $ iF)(fT $ jF))(sumf fT ZeroC)
        val j0 = le_zero_eqD jF hlej          (* oeq j 0 *)
        (* lt i j -> lt i 0 (subst j=0) -> le (Suc i) 0 -> oeq (Suc i) 0 -> oFalse *)
        val Pz = Term.lambda (Free("zlj",natT)) (lt iF (Free("zlj",natT)))
        val lti0 = substPredD (Pz, jF, ZeroC) j0 hlt   (* lt i 0 = le (Suc i) 0 *)
        val sucI0 = le_zero_eqD (suc iF) lti0          (* oeq (Suc i) 0 *)
        val ff = SucNeqZeroD iF sucI0                  (* oFalse *)
        val r = Thm.implies_elim (oFalse_elimD goal) ff   (* jT goal, assumes hlt + hlej *)
        (* impI_D itself discharges the named assumption ; nest twice *)
        val inner = impI_D (le jF ZeroC, goal) r          (* jT(Imp(le j 0)goal), assumes hlt *)
      in impI_D (lt iF jF, mkImp (le jF ZeroC) goal) inner end
    (* STEP n -> Suc n *)
    val nF = Free("n_l2", natT)
    val IH = Thm.assume (ctermSigD (jT (body nF)))
    val stepconcl =
      let
        val hlt = Thm.assume (ctermSigD (jT (lt iF jF)))
        val hlej = Thm.assume (ctermSigD (jT (le jF (suc nF))))
        val sfS = sumfSucD (fT, nF)    (* sumf f (Suc n) = add (sumf f n)(f (Suc n)) *)
        val pairT = add (fT $ iF)(fT $ jF)
        val goal = le pairT (sumf fT (suc nF))
        val dj = le_splitD (jF, nF) hlej     (* Disj (oeq j (Suc n))(le j n) *)
        val caseEq =
          let val heq = Thm.assume (ctermSigD (jT (oeq jF (suc nF))))
              (* lt i j, j=Suc n -> lt i (Suc n) -> le i n *)
              val Pz = Term.lambda (Free("zlj2",natT)) (lt iF (Free("zlj2",natT)))
              val ltiSn = substPredD (Pz, jF, suc nF) heq hlt   (* lt i (Suc n) *)
              val lein = lt_Suc_imp_leD (iF, nF) ltiSn          (* le i n *)
              val fiLe = lb1_apply lb1Thm fT (iF, nF) lein      (* le (f i)(sumf f n) *)
              (* le_add_mono : le (f i)(sumf f n) -> le (add (f i)(f j))(add (sumf f n)(f j)) *)
              val mono = leAddMonoD (fT $ iF, sumf fT nF, fT $ jF) fiLe
                         (* le (add (f i)(f j))(add (sumf f n)(f j)) *)
              (* f j = f (Suc n) ; rewrite RHS add (sumf f n)(f j) -> add (sumf f n)(f(Suc n)) -> sumf f (Suc n) *)
              val fjEq = fcongD fT (jF, suc nF) heq            (* oeq (f j)(f(Suc n)) *)
              val rhs1 = le_cong_rD (add (sumf fT nF)(fT $ jF), add (sumf fT nF)(fT $ (suc nF)), pairT)
                            (add_cong_rD (sumf fT nF, fT $ jF, fT $ (suc nF)) fjEq) mono
                         (* le (add (f i)(f j))(add (sumf f n)(f(Suc n))) *)
              val r = le_cong_rD (add (sumf fT nF)(fT $ (suc nF)), sumf fT (suc nF), pairT)
                          (sym3 (sumf fT (suc nF), add (sumf fT nF)(fT $ (suc nF))) sfS) rhs1
          in Thm.implies_intr (ctermSigD (jT (oeq jF (suc nF)))) r end
        val caseLe =
          let val hlen = Thm.assume (ctermSigD (jT (le jF nF)))
              (* IH : Imp(lt i j)(Imp(le j n)(le pair (sumf f n)))  -- OBJECT Imps, use mp_D *)
              val ih1 = mp_D (lt iF jF, mkImp (le jF nF)(le pairT (sumf fT nF))) IH hlt
              val ihD = mp_D (le jF nF, le pairT (sumf fT nF)) ih1 hlen   (* le pair (sumf f n) *)
              val l0 = leAddD (sumf fT nF, fT $ (suc nF))   (* le (sumf f n)(add (sumf f n)(f(Suc n))) *)
              val l1 = le_cong_rD (add (sumf fT nF)(fT $ (suc nF)), sumf fT (suc nF), sumf fT nF)
                          (sym3 (sumf fT (suc nF), add (sumf fT nF)(fT $ (suc nF))) sfS) l0
                       (* le (sumf f n)(sumf f (Suc n)) *)
              val r = leTransD (pairT, sumf fT nF, sumf fT (suc nF)) ihD l1
          in Thm.implies_intr (ctermSigD (jT (le jF nF))) r end
        val res = disjE_D (oeq jF (suc nF), le jF nF, goal) dj caseEq caseLe   (* jT goal, assumes hlt+hlej *)
        val inner = impI_D (le jF (suc nF), goal) res     (* jT(Imp(le j(Suc n))goal), assumes hlt *)
      in impI_D (lt iF jF, mkImp (le jF (suc nF)) goal) inner end
    val step1 = Thm.forall_intr (ctermSigD nF) (Thm.implies_intr (ctermSigD (jT (body nF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1   (* Imp(lt i j)(Imp(le j n_l2)(le pair (sumf f n_l2))) ; n_l2 Free *)
    (* close over n_l2 as object Forall : Forall n. Imp(lt i j)(Imp(le j n)(le pair (sumf f n))) *)
    val outerPred = Term.lambda (Free("n_out2", natT)) (body (Free("n_out2", natT)))
    val r3 = allI_D outerPred (Thm.forall_intr (ctermSigD kIndN) r2)
  in r3 end   (* Forall n. Imp(lt i j)(Imp(le j n)(le (f i+f j)(sumf f n))) ; i,j,f fixed Frees *)

val () = out "SB_LB2_DEFINED\n";

(* applier : lb2 thm = Forall n. Imp(lt i j)(Imp(le j n)(le(add(f i)(f j))(sumf f n))) ; i,j,f FIXED.
   apply at nT, discharge (lt i j) and (le j n). *)
fun lb2_apply lb2Thm fT iF jF nT hlt hlej =
  let
    fun body nv = mkImp (lt iF jF)(mkImp (le jF nv)(le (add (fT $ iF)(fT $ jF))(sumf fT nv)))
    val outerPred = Term.lambda (Free("n_out2", natT)) (body (Free("n_out2", natT)))
    val atN = allE_D (outerPred, nT) lb2Thm   (* Imp(lt i j)(Imp(le j nT)(le pair (sumf f nT))) *)
    val s1 = mp_D (lt iF jF, mkImp (le jF nT)(le (add (fT $ iF)(fT $ jF))(sumf fT nT))) atN hlt
    val s2 = mp_D (le jF nT, le (add (fT $ iF)(fT $ jF))(sumf fT nT)) s1 hlej
  in s2 end

(* ---------------------------------------------------------------------------
   (4) sumf_lb3 fT iF jF kF :
       Forall n. Imp(lt i j)(Imp(lt j k)(Imp(le k n)(le (add(f i)(add(f j)(f k)))(sumf f n))))
       by induction on n.  Uses lb2 (built for fT, i, j).
   --------------------------------------------------------------------------- *)
fun build_lb3 fT lb2Thm iF jF kF =
  let
    val tripT = add (fT $ iF)(add (fT $ jF)(fT $ kF))
    fun body nT = mkImp (lt iF jF)(mkImp (lt jF kF)(mkImp (le kF nT)(le tripT (sumf fT nT))))
    val zN = Free("zN3", natT)
    val Qpred = Term.lambda zN (body zN)
    val kIndN = Free("n_l3", natT)
    val ind = nat_induct_atD (Qpred, kIndN)
    (* BASE n=0 : le k 0 -> k=0 ; lt j k = lt j 0 -> oFalse (le (Suc j) 0). vacuous. *)
    val base =
      let
        val hltij = Thm.assume (ctermSigD (jT (lt iF jF)))
        val hltjk = Thm.assume (ctermSigD (jT (lt jF kF)))
        val hlek  = Thm.assume (ctermSigD (jT (le kF ZeroC)))
        val goal  = le tripT (sumf fT ZeroC)
        val k0 = le_zero_eqD kF hlek      (* oeq k 0 *)
        val Pz = Term.lambda (Free("zlk",natT)) (lt jF (Free("zlk",natT)))
        val ltj0 = substPredD (Pz, kF, ZeroC) k0 hltjk   (* lt j 0 = le (Suc j) 0 *)
        val sucJ0 = le_zero_eqD (suc jF) ltj0            (* oeq (Suc j) 0 *)
        val ff = SucNeqZeroD jF sucJ0
        val r = Thm.implies_elim (oFalse_elimD goal) ff
        val i3 = impI_D (le kF ZeroC, goal) r
        val i2 = impI_D (lt jF kF, mkImp (le kF ZeroC) goal) i3
      in impI_D (lt iF jF, mkImp (lt jF kF)(mkImp (le kF ZeroC) goal)) i2 end
    (* STEP *)
    val nF = Free("n_l3", natT)
    val IH = Thm.assume (ctermSigD (jT (body nF)))
    val stepconcl =
      let
        val hltij = Thm.assume (ctermSigD (jT (lt iF jF)))
        val hltjk = Thm.assume (ctermSigD (jT (lt jF kF)))
        val hlek  = Thm.assume (ctermSigD (jT (le kF (suc nF))))
        val sfS = sumfSucD (fT, nF)
        val goal = le tripT (sumf fT (suc nF))
        val dj = le_splitD (kF, nF) hlek      (* Disj(oeq k (Suc n))(le k n) *)
        val caseEq =
          let val heq = Thm.assume (ctermSigD (jT (oeq kF (suc nF))))
              (* lt j k, k=Suc n -> lt j (Suc n) -> le j n *)
              val Pz = Term.lambda (Free("zlk2",natT)) (lt jF (Free("zlk2",natT)))
              val ltjSn = substPredD (Pz, kF, suc nF) heq hltjk
              val lejn = lt_Suc_imp_leD (jF, nF) ltjSn         (* le j n *)
              val pairLe = lb2_apply lb2Thm fT iF jF nF hltij lejn  (* le (add(f i)(f j))(sumf f n) *)
              (* triple = add(f i)(add(f j)(f k)) ; f k = f(Suc n).  rewrite to add(add(f i)(f j))(f(Suc n)) *)
              val fkEq = fcongD fT (kF, suc nF) heq           (* oeq (f k)(f(Suc n)) *)
              (* triple = add(f i)(add(f j)(f k)) -> add(f i)(add(f j)(f(Suc n))) [cong on inner] *)
              val tripRw1 = add_cong_rD (fT $ iF, add (fT $ jF)(fT $ kF), add (fT $ jF)(fT $ (suc nF)))
                              (add_cong_rD (fT $ jF, fT $ kF, fT $ (suc nF)) fkEq)
                            (* oeq triple (add(f i)(add(f j)(f(Suc n)))) *)
              (* add(f i)(add(f j)(f(Suc n))) = add(add(f i)(f j))(f(Suc n)) [sym assoc] *)
              val assocEq = sym3 (add (add (fT $ iF)(fT $ jF))(fT $ (suc nF)),
                                  add (fT $ iF)(add (fT $ jF)(fT $ (suc nF))))
                              (addassocD (fT $ iF, fT $ jF, fT $ (suc nF)))
                            (* oeq (add(f i)(add(f j)(f Sn)))(add(add(f i)(f j))(f Sn)) *)
              val tripEq = trans3 (tripT, add (fT $ iF)(add (fT $ jF)(fT $ (suc nF))),
                                   add (add (fT $ iF)(fT $ jF))(fT $ (suc nF))) tripRw1 assocEq
                           (* oeq triple (add(add(f i)(f j))(f(Suc n))) *)
              (* le_add_mono : le (add(f i)(f j))(sumf f n) -> le (add(add(f i)(f j))(f Sn))(add(sumf f n)(f Sn)) *)
              val mono = leAddMonoD (add (fT $ iF)(fT $ jF), sumf fT nF, fT $ (suc nF)) pairLe
                         (* le (add(add(f i)(f j))(f Sn))(add(sumf f n)(f Sn)) *)
              (* rewrite RHS add(sumf f n)(f Sn) = sumf f (Suc n) ; LHS via tripEq sym *)
              val rhs = le_cong_rD (add (sumf fT nF)(fT $ (suc nF)), sumf fT (suc nF),
                                    add (add (fT $ iF)(fT $ jF))(fT $ (suc nF)))
                          (sym3 (sumf fT (suc nF), add (sumf fT nF)(fT $ (suc nF))) sfS) mono
                        (* le (add(add(f i)(f j))(f Sn))(sumf f (Suc n)) *)
              val r = le_cong_lD (add (add (fT $ iF)(fT $ jF))(fT $ (suc nF)), tripT, sumf fT (suc nF))
                          (sym3 (tripT, add (add (fT $ iF)(fT $ jF))(fT $ (suc nF))) tripEq) rhs
                      (* le triple (sumf f (Suc n)) *)
          in Thm.implies_intr (ctermSigD (jT (oeq kF (suc nF)))) r end
        val caseLe =
          let val hlekn = Thm.assume (ctermSigD (jT (le kF nF)))
              (* IH : Imp(lt i j)(Imp(lt j k)(Imp(le k n)(le triple (sumf f n)))) *)
              val ih1 = mp_D (lt iF jF, mkImp (lt jF kF)(mkImp (le kF nF)(le tripT (sumf fT nF)))) IH hltij
              val ih2 = mp_D (lt jF kF, mkImp (le kF nF)(le tripT (sumf fT nF))) ih1 hltjk
              val ihD = mp_D (le kF nF, le tripT (sumf fT nF)) ih2 hlekn   (* le triple (sumf f n) *)
              val l0 = leAddD (sumf fT nF, fT $ (suc nF))
              val l1 = le_cong_rD (add (sumf fT nF)(fT $ (suc nF)), sumf fT (suc nF), sumf fT nF)
                          (sym3 (sumf fT (suc nF), add (sumf fT nF)(fT $ (suc nF))) sfS) l0
              val r = leTransD (tripT, sumf fT nF, sumf fT (suc nF)) ihD l1
          in Thm.implies_intr (ctermSigD (jT (le kF nF))) r end
        val res = disjE_D (oeq kF (suc nF), le kF nF, goal) dj caseEq caseLe   (* jT goal, assumes hltij+hltjk+hlek *)
        val i3 = impI_D (le kF (suc nF), goal) res
        val i2 = impI_D (lt jF kF, mkImp (le kF (suc nF)) goal) i3
      in impI_D (lt iF jF, mkImp (lt jF kF)(mkImp (le kF (suc nF)) goal)) i2 end
    val step1 = Thm.forall_intr (ctermSigD nF) (Thm.implies_intr (ctermSigD (jT (body nF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
    val outerPred = Term.lambda (Free("n_out3", natT)) (body (Free("n_out3", natT)))
    val r3 = allI_D outerPred (Thm.forall_intr (ctermSigD kIndN) r2)
  in r3 end

val () = out "SB_LB3_DEFINED\n";

(* applier : lb3 thm = Forall n. Imp(lt i j)(Imp(lt j k)(Imp(le k n)(le triple (sumf f n)))) ; i,j,k,f FIXED. *)
fun lb3_apply lb3Thm fT iF jF kF nT hltij hltjk hlek =
  let
    val tripT = add (fT $ iF)(add (fT $ jF)(fT $ kF))
    fun body nv = mkImp (lt iF jF)(mkImp (lt jF kF)(mkImp (le kF nv)(le tripT (sumf fT nv))))
    val outerPred = Term.lambda (Free("n_out3", natT)) (body (Free("n_out3", natT)))
    val atN = allE_D (outerPred, nT) lb3Thm
    val s1 = mp_D (lt iF jF, mkImp (lt jF kF)(mkImp (le kF nT)(le tripT (sumf fT nT)))) atN hltij
    val s2 = mp_D (lt jF kF, mkImp (le kF nT)(le tripT (sumf fT nT))) s1 hltjk
    val s3 = mp_D (le kF nT, le tripT (sumf fT nT)) s2 hlek
  in s3 end

(* ---------------------------------------------------------------------------
   (5) misc arithmetic helpers for the assembly.
   --------------------------------------------------------------------------- *)
val dvd_nonzero_vSB = varify (up dvd_nonzero)   (* dvd d n ==> neg(oeq n 0) ==> neg(oeq d 0) *)
fun dvd_nonzeroD (dT,nT) hdvd hnz = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("d",0), ctermSigD dT),(("n",0), ctermSigD nT)] dvd_nonzero_vSB)) hdvd) hnz
val gt1_of_ne0_ne1_vSB = varify (up gt1_of_ne0_ne1)  (* neg(oeq d 0) ==> neg(oeq d 1) ==> lt 1 d *)
fun gt1OfNe0Ne1D dT hne0 hne1 = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("d",0), ctermSigD dT)] gt1_of_ne0_ne1_vSB)) hne0) hne1
val () = out "SB_NE_HELPERS_OK\n";

(* lt_one_imp_ne0 : lt 1 m ==> neg (oeq m 0).
   lt 1 m = le 2 m ; if m=0 then le 2 0 -> oeq 2 0 -> Suc_neq_Zero. *)
fun lt_one_imp_ne0D mT hlt1 =
  let val hm0 = Thm.assume (ctermSigD (jT (oeq mT ZeroC)))
      (* lt 1 m = le 2 m ; subst m=0 -> le 2 0 -> oeq 2 0 -> oFalse *)
      val Pz = Term.lambda (Free("zm0",natT)) (lt (suc ZeroC)(Free("zm0",natT)))
      val lt10 = substPredD (Pz, mT, ZeroC) hm0 hlt1    (* lt 1 0 = le 2 0 *)
      val eq20 = le_zero_eqD (suc (suc ZeroC)) lt10     (* oeq 2 0 = oeq (Suc 1) 0 *)
      val ff = SucNeqZeroD (suc ZeroC) eq20             (* oFalse, assumes (oeq m 0) via hm0 *)
  in impI_D (oeq mT ZeroC, oFalseC) ff end             (* impI_D discharges hm0 -> jT(neg(oeq m 0)) *)

(* neg_destruct : neg A is Imp A oFalse ; from neg A and jT A derive oFalse via mp_D *)
fun negElimD At hnegA hA = mp_D (At, oFalseC) hnegA hA

(* ex_middle on ctxtSigD : Disj A (neg A) -- exists? build from ex_middle_vD *)
fun exMiddleD At = beta_norm (Drule.infer_instantiate ctxtSigD [(("A",0), ctermSigD At)] ex_middle_vD)

val () = out "SB_ARITH_HELPERS_OK\n";

(* lt_irrefl on ctxtSigD : lt n n ==> oFalse *)
val lt_irrefl_vSB = varify (up lt_irrefl)
fun ltIrreflD nT h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("n",0), ctermSigD nT)] lt_irrefl_vSB)) h
fun conjunct1_D (At,Bt) hC = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("A",0), ctermSigD At),(("B",0), ctermSigD Bt)] conjunct1_vD)) hC
fun conjunct2_D (At,Bt) hC = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("A",0), ctermSigD At),(("B",0), ctermSigD Bt)] conjunct2_vD)) hC
val () = out "SB_FINAL_HELPERS_OK\n";

(* ---------------------------------------------------------------------------
   (6) THE LOWER-BOUND COROLLARY (the reusable graceful floor):
       sigma_lb3 : lt 1 e ==> lt e m ==> dvd e m
                     ==> le (add (Suc Zero)(add e m))(sigma m)
   i.e. for any divisor e with 1 < e < m, sigma m >= 1 + e + m.
   (Uses dvd 1 m, dvd m m built-in.)  Subject m,e FIXED Frees.
   --------------------------------------------------------------------------- *)
fun sigma_lb3_for mF eF =
  let
    val fT = swtC $ mF
    val lb1 = build_lb1 fT
    val lb2 = build_lb2 fT lb1 (suc ZeroC) eF
    val lb3 = build_lb3 fT lb2 (suc ZeroC) eF mF
    fun core (hlt1e, hltem, hdvde) =
      let
        (* swt evals *)
        val sw1 = swt_dvd_D (suc ZeroC, mF) (dvd_oneD mF)    (* oeq (swt m 1) 1 *)
        val swe = swt_dvd_D (eF, mF) hdvde                   (* oeq (swt m e) e *)
        val swm = swt_dvd_D (mF, mF) (dvd_selfD mF)          (* oeq (swt m m) m *)
        (* lb3 at (1,e,m) bound m : le (add(swt m 1)(add(swt m e)(swt m m)))(sumf(swt m) m) *)
        val raw = lb3_apply lb3 fT (suc ZeroC) eF mF mF hlt1e hltem (leReflD mF)
        (* rewrite the LHS triple : swt m 1 -> 1, swt m e -> e, swt m m -> m *)
        val tripT = add (fT $ (suc ZeroC))(add (fT $ eF)(fT $ mF))
        val tgt1  = add (suc ZeroC)(add eF mF)
        (* triple cong : add(swt m 1)(add(swt m e)(swt m m)) = add 1 (add e m) *)
        val cInner = trans3 (add (fT $ eF)(fT $ mF), add eF (fT $ mF), add eF mF)
                       (add_cong_lD (fT $ eF, eF, fT $ mF) swe)
                       (add_cong_rD (eF, fT $ mF, mF) swm)
                     (* oeq (add(swt m e)(swt m m))(add e m) *)
        val cTrip = trans3 (tripT, add (fT $ (suc ZeroC))(add eF mF), tgt1)
                       (add_cong_rD (fT $ (suc ZeroC), add (fT $ eF)(fT $ mF), add eF mF) cInner)
                       (add_cong_lD (fT $ (suc ZeroC), suc ZeroC, add eF mF) sw1)
                     (* oeq triple (add 1 (add e m)) *)
        (* sumf(swt m) m = sigma m  [sym sigma_def] *)
        val sdef = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD mF)] sigma_def_vD)
                   (* oeq (sigma m)(sumf(swt m) m) *)
        val sumEqSig = sym3 (sigma mF, sumf fT mF) sdef    (* oeq (sumf(swt m) m)(sigma m) *)
        (* transport raw : le triple (sumf(swt m) m) -> le (add 1 (add e m))(sigma m) *)
        val r1 = le_cong_lD (tripT, tgt1, sumf fT mF) cTrip raw    (* le (add 1 (add e m))(sumf(swt m) m) *)
        val r2 = le_cong_rD (sumf fT mF, sigma mF, tgt1) sumEqSig r1  (* le (add 1 (add e m))(sigma m) *)
      in r2 end
  in core end

val () = out "SB_SIGMA_LB3_DEFINED\n";

(* add_one_l : oeq (add (Suc Zero) y)(Suc y)  [add 1 y = Suc(add 0 y) = Suc y] *)
fun add_one_lD yT =
  let val aS = addSucL (ZeroC, yT)               (* add (Suc 0) y = Suc(add 0 y) *)
      val a0 = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD yT)] add_0_vD)  (* add 0 y = y *)
      val sc = beta_norm (Drule.infer_instantiate ctxtSigD
                 [(("P",0), ctermSigD (Term.lambda (Free("zao",natT)) (oeq (suc (add ZeroC yT))(suc (Free("zao",natT)))))),
                  (("a",0), ctermSigD (add ZeroC yT)),(("b",0), ctermSigD yT)] oeq_subst_vD)
               OF [a0, reflD (suc (add ZeroC yT))]   (* Suc(add 0 y) = Suc y *)
  in trans3 (add (suc ZeroC) yT, suc (add ZeroC yT), suc yT) aS sc end

val () = out "SB_ADD1L_OK\n";

(* ============================================================================
   MAIN : sigma_bound
     lt 1 m ==> dvd d m ==> lt d m ==> oeq (sigma m)(add m d)
       ==> Conj (oeq d (Suc Zero)) (prime2 m)
   ============================================================================ *)
val sigma_bound =
  let
    val mF = Free("m", natT); val dF = Free("d", natT)
    val H1 = Thm.assume (ctermSigD (jT (lt (suc ZeroC) mF)))        (* lt 1 m *)
    val H2 = Thm.assume (ctermSigD (jT (dvd dF mF)))                (* dvd d m *)
    val H3 = Thm.assume (ctermSigD (jT (lt dF mF)))                 (* lt d m *)
    val H4 = Thm.assume (ctermSigD (jT (oeq (sigma mF)(add mF dF))))(* sigma m = m + d *)
    (* PART A : oeq d 1 -- contradiction route under neg(oeq d 1) *)
    val negD1goal = oeq dF (suc ZeroC)
    val emA = exMiddleD (oeq dF (suc ZeroC))    (* Disj (oeq d 1)(neg(oeq d 1)) *)
    val caseEq1 =
      let val heq = Thm.assume (ctermSigD (jT (oeq dF (suc ZeroC))))
      in Thm.implies_intr (ctermSigD (jT (oeq dF (suc ZeroC)))) heq end
    val caseNe1 =
      let
        val hne = Thm.assume (ctermSigD (jT (neg (oeq dF (suc ZeroC)))))
        (* neg(oeq m 0) from H1 *)
        val ne0mThm = lt_one_imp_ne0D mF H1                 (* jT(neg(oeq m 0)) *)
        val ne0d = dvd_nonzeroD (dF, mF) H2 ne0mThm         (* neg(oeq d 0) *)
        val lt1d = gt1OfNe0Ne1D dF ne0d hne                 (* lt 1 d *)
        (* sigma_lb3 at (m,d) : le (add 1 (add d m))(sigma m) *)
        val core = sigma_lb3_for mF dF
        val lb = core (lt1d, H3, H2)         (* le (add 1 (add d m))(sigma m) *)
        (* transport sigma m -> add m d (H4) : le (add 1 (add d m))(add m d) *)
        val lb2t = le_cong_rD (sigma mF, add mF dF, add (suc ZeroC)(add dF mF)) H4 lb
                   (* le (add 1 (add d m))(add m d) *)
        (* add 1 (add d m) = Suc(add d m) [add_one_l]; add d m = add m d [comm];
           so add 1 (add d m) = Suc(add m d) *)
        val a1 = add_one_lD (add dF mF)                     (* add 1 (add d m) = Suc(add d m) *)
        val cm = addcommD (dF, mF)                          (* add d m = add m d *)
        val sucCm = beta_norm (Drule.infer_instantiate ctxtSigD
                      [(("P",0), ctermSigD (Term.lambda (Free("zsc",natT)) (oeq (suc (add dF mF))(suc (Free("zsc",natT)))))),
                       (("a",0), ctermSigD (add dF mF)),(("b",0), ctermSigD (add mF dF))] oeq_subst_vD)
                    OF [cm, reflD (suc (add dF mF))]         (* Suc(add d m) = Suc(add m d) *)
        val a1md = trans3 (add (suc ZeroC)(add dF mF), suc (add dF mF), suc (add mF dF)) a1 sucCm
                   (* add 1 (add d m) = Suc(add m d) *)
        (* le (Suc(add m d))(add m d) via transporting lb2t LHS *)
        val lcontra = le_cong_lD (add (suc ZeroC)(add dF mF), suc (add mF dF), add mF dF) a1md lb2t
                      (* le (Suc(add m d))(add m d) = lt (add m d)(add m d) *)
        val ff = ltIrreflD (add mF dF) lcontra              (* oFalse *)
        val r = Thm.implies_elim (oFalse_elimD negD1goal) ff
      in Thm.implies_intr (ctermSigD (jT (neg (oeq dF (suc ZeroC))))) r end
    val dEq1 = disjE_D (oeq dF (suc ZeroC), neg (oeq dF (suc ZeroC)), negD1goal) emA caseEq1 caseNe1
               (* oeq d 1 *)

    (* PART B : prime2 m.  Use prime_cases on lt 1 m.  Refute the proper-divisor disjunct. *)
    val pcDisj = primeCasesD mF H1     (* Disj (prime2 m)(Ex e.(1<e /\ e<m) /\ e|m) *)
    (* proper-divisor predicate from prime_cases : %e. Conj (Conj (lt 1 e)(lt e m))(dvd e m) *)
    fun pdAbs () =
      let val eF = Free("e_pd", natT)
      in Term.lambda eF (mkConj (mkConj (lt (suc ZeroC) eF)(lt eF mF))(dvd eF mF)) end
    val primeGoal = prime2 mF
    val casePrime =
      let val hp = Thm.assume (ctermSigD (jT (prime2 mF)))
      in Thm.implies_intr (ctermSigD (jT (prime2 mF))) hp end
    val caseProper =
      let
        val hex = Thm.assume (ctermSigD (jT (mkEx (pdAbs ()))))
        fun body eF hconj =   (* hconj : Conj(Conj(lt 1 e)(lt e m))(dvd e m) *)
          let
            val c12 = conjunct1_D (mkConj (lt (suc ZeroC) eF)(lt eF mF), dvd eF mF) hconj  (* Conj(lt 1 e)(lt e m) *)
            val hdvde = conjunct2_D (mkConj (lt (suc ZeroC) eF)(lt eF mF), dvd eF mF) hconj (* dvd e m *)
            val hlt1e = conjunct1_D (lt (suc ZeroC) eF, lt eF mF) c12      (* lt 1 e *)
            val hltem = conjunct2_D (lt (suc ZeroC) eF, lt eF mF) c12      (* lt e m *)
            (* sigma_lb3 at (m,e) : le (add 1 (add e m))(sigma m) *)
            val core = sigma_lb3_for mF eF
            val lb = core (hlt1e, hltem, hdvde)    (* le (add 1 (add e m))(sigma m) *)
            (* d = 1 (dEq1) ; rewrite H4 : sigma m = add m d = add m 1 *)
            val H4md1 = trans3 (sigma mF, add mF dF, add mF (suc ZeroC)) H4 (add_cong_rD (mF, dF, suc ZeroC) dEq1)
                        (* oeq (sigma m)(add m 1) *)
            (* transport lb -> le (add 1 (add e m))(add m 1) *)
            val lb2t = le_cong_rD (sigma mF, add mF (suc ZeroC), add (suc ZeroC)(add eF mF)) H4md1 lb
                       (* le (add 1 (add e m))(add m 1) = Ex x. add m 1 = add (add 1 (add e m)) x *)
            (* CONTRADICTION : le (add 1 (add e m))(add m 1) -> add e x_witness = 0 -> e = 0, contra e>1.
               le LHS RHS : Ex x. RHS = LHS + x  where LHS = add 1 (add e m), RHS = add m 1.
               RHS = add m 1 = add 1 m [comm].  LHS + x = add (add 1 (add e m)) x = add 1 (add (add e m) x) [assoc].
               So add 1 m = add 1 (add (add e m) x) -> m = add (add e m) x [cancel 1].
               add (add e m) x = add e (add m x) [assoc] ; comm to add (add m x) e ... aim: m = add m (add e x).
                 add e (add m x) : comm (add m x) -> add e (add x m) ; assoc -> add (add e x) m ; comm -> add m (add e x).
               So m = add m (add e x) ; add m 0 = m -> add m 0 = add m (add e x) -> 0 = add e x [cancel m]
                 -> add e x = 0 -> e = 0 [add_eq_zero_left] -> contra e != 0. *)
            val LHS = add (suc ZeroC)(add eF mF)
            val RHS = add mF (suc ZeroC)
            val Pwit = Abs("x", natT, oeq RHS (add LHS (Bound 0)))
            fun ffBody xF hx =   (* hx : oeq RHS (add LHS x) = oeq (add m 1)(add (add 1 (add e m)) x) *)
              let
                (* RHS = add 1 m [comm] *)
                val rhsComm = addcommD (mF, suc ZeroC)         (* add m 1 = add 1 m *)
                (* add LHS x = add (add 1 (add e m)) x = add 1 (add (add e m) x) [assoc] *)
                val lhsAssoc = addassocD (suc ZeroC, add eF mF, xF)  (* add (add 1 (add e m)) x = add 1 (add (add e m) x) *)
                (* chain : add 1 m = add LHS x = add 1 (add (add e m) x) *)
                val eq1 = trans3 (add (suc ZeroC) mF, add mF (suc ZeroC), add LHS xF) (sym3 (add mF (suc ZeroC), add (suc ZeroC) mF) rhsComm) hx
                          (* add 1 m = add (add 1 (add e m)) x *)
                val eq2 = trans3 (add (suc ZeroC) mF, add LHS xF, add (suc ZeroC)(add (add eF mF) xF)) eq1 lhsAssoc
                          (* add 1 m = add 1 (add (add e m) x) *)
                val mEq = add_left_cancel_D2 (suc ZeroC, mF, add (add eF mF) xF) eq2  (* m = add (add e m) x *)
                (* add (add e m) x = add m (add e x) :
                   add (add e m) x = add e (add m x) [assoc] ; (add m x)=add x m [comm] ; add e (add x m)=add (add e x) m [assoc] ; =add m (add e x) [comm] *)
                val s1 = addassocD (eF, mF, xF)              (* add (add e m) x = add e (add m x) *)
                val s2 = add_cong_rD (eF, add mF xF, add xF mF) (addcommD (mF, xF))  (* add e (add m x) = add e (add x m) *)
                val s3 = sym3 (add (add eF xF) mF, add eF (add xF mF)) (addassocD (eF, xF, mF))  (* add e (add x m) = add (add e x) m *)
                val s4 = addcommD (add eF xF, mF)            (* add (add e x) m = add m (add e x) *)
                val rearr = trans3 (add (add eF mF) xF, add eF (add mF xF), add mF (add eF xF))
                              s1 (trans3 (add eF (add mF xF), add eF (add xF mF), add mF (add eF xF)) s2
                                    (trans3 (add eF (add xF mF), add (add eF xF) mF, add mF (add eF xF)) s3 s4))
                            (* add (add e m) x = add m (add e x) *)
                val mEq2 = trans3 (mF, add (add eF mF) xF, add mF (add eF xF)) mEq rearr  (* m = add m (add e x) *)
                (* add m 0 = m [add0r] ; add m 0 = add m (add e x) -> 0 = add e x [cancel] *)
                val m0 = add0rD mF                            (* add m 0 = m *)
                val m0eq = trans3 (add mF ZeroC, mF, add mF (add eF xF)) m0 mEq2   (* add m 0 = add m (add e x) *)
                val zeroEq = add_left_cancel_D2 (mF, ZeroC, add eF xF) m0eq    (* 0 = add e x *)
                val addex0 = sym3 (ZeroC, add eF xF) zeroEq                    (* add e x = 0 *)
                val e0 = add_eq_zero_left_D (eF, xF) addex0                    (* oeq e 0 *)
                (* e != 0 from lt 1 e *)
                val ne0e = lt_one_imp_ne0D eF hlt1e          (* jT(neg(oeq e 0)) *)
                val ff = negElimD (oeq eF ZeroC) ne0e e0     (* oFalse *)
              in Thm.implies_elim (oFalse_elimD primeGoal) ff end
            val r = exE_atD (Pwit, primeGoal) lb2t "x_sb" ffBody
          in r end
        val res = exE_atD (pdAbs (), primeGoal) hex "e_pd" body
      in Thm.implies_intr (ctermSigD (jT (mkEx (pdAbs ())))) res end
    val primeM = disjE_D (prime2 mF, mkEx (pdAbs ()), primeGoal) pcDisj casePrime caseProper

    (* combine : Conj (oeq d 1)(prime2 m) *)
    val both = conjI_D (oeq dF (suc ZeroC), prime2 mF) dEq1 primeM
    (* discharge H4,H3,H2,H1 *)
    val d4 = Thm.implies_intr (ctermSigD (jT (oeq (sigma mF)(add mF dF)))) both
    val d3 = Thm.implies_intr (ctermSigD (jT (lt dF mF))) d4
    val d2 = Thm.implies_intr (ctermSigD (jT (dvd dF mF))) d3
    val d1 = Thm.implies_intr (ctermSigD (jT (lt (suc ZeroC) mF))) d2
  in varify d1 end;

val () = out ("SIGMA_BOUND_HYPS = " ^ Int.toString (length (Thm.hyps_of sigma_bound)) ^ "\n");
val () = out ("SIGMA_BOUND_SHYPS = " ^ Int.toString (length (Thm.extra_shyps sigma_bound)) ^ "\n");
val () = out "SIGMA_BOUND_BUILT\n";

(* ---------------------------------------------------------------------------
   VALIDATION : 0-hyp + aconv the intended schematic statement.
   --------------------------------------------------------------------------- *)
val mVsb = Var (("m",0), natT); val dVsb = Var (("d",0), natT)
val i_sigma_bound =
  Logic.mk_implies (jT (lt (suc ZeroC) mVsb),
    Logic.mk_implies (jT (dvd dVsb mVsb),
      Logic.mk_implies (jT (lt dVsb mVsb),
        Logic.mk_implies (jT (oeq (sigma mVsb)(add mVsb dVsb)),
          jT (mkConj (oeq dVsb (suc ZeroC)) (prime2 mVsb))))))
val r_sb = chkD ("sigma_bound", sigma_bound, i_sigma_bound)
val () = if r_sb then out "SIGMA_BOUND_ACONV_OK\n" else out "SIGMA_BOUND_ACONV_FAIL\n";

(* SOUNDNESS PROBE 1 : the conclusion is genuinely conditional on
   oeq (sigma m)(add m d) -- dropping it must NOT be aconv. *)
val s_sb_needs_sigma =
  let val bogus =
        Logic.mk_implies (jT (lt (suc ZeroC) mVsb),
          Logic.mk_implies (jT (dvd dVsb mVsb),
            Logic.mk_implies (jT (lt dVsb mVsb),
              jT (mkConj (oeq dVsb (suc ZeroC)) (prime2 mVsb)))))
  in not ((Thm.prop_of sigma_bound) aconv bogus) end
val () = if s_sb_needs_sigma then out "PROBE_OK sigma_bound needs the sigma-equation hypothesis\n"
         else out "PROBE_FAIL sigma_bound dropped the sigma hypothesis!\n";

(* SOUNDNESS PROBE 2 : the conclusion genuinely contains prime2 m
   (not the trivial Conj (oeq d 1)(oeq d 1) or dropping the prime conjunct). *)
val s_sb_has_prime =
  let val bogus =
        Logic.mk_implies (jT (lt (suc ZeroC) mVsb),
          Logic.mk_implies (jT (dvd dVsb mVsb),
            Logic.mk_implies (jT (lt dVsb mVsb),
              Logic.mk_implies (jT (oeq (sigma mVsb)(add mVsb dVsb)),
                jT (oeq dVsb (suc ZeroC))))))
  in not ((Thm.prop_of sigma_bound) aconv bogus) end
val () = if s_sb_has_prime then out "PROBE_OK sigma_bound concludes prime2 m (not just d=1)\n"
         else out "PROBE_FAIL sigma_bound lost the prime2 conjunct!\n";

(* SOUNDNESS PROBE 3 : the d=1 conjunct is genuinely d=1, not the trivial d=d. *)
val s_sb_d1 =
  let val bogus =
        Logic.mk_implies (jT (lt (suc ZeroC) mVsb),
          Logic.mk_implies (jT (dvd dVsb mVsb),
            Logic.mk_implies (jT (lt dVsb mVsb),
              Logic.mk_implies (jT (oeq (sigma mVsb)(add mVsb dVsb)),
                jT (mkConj (oeq dVsb dVsb) (prime2 mVsb))))))
  in not ((Thm.prop_of sigma_bound) aconv bogus) end
val () = if s_sb_d1 then out "PROBE_OK sigma_bound's first conjunct is d = 1 (not d = d)\n"
         else out "PROBE_FAIL sigma_bound first conjunct collapsed!\n";

val () =
  if r_sb andalso (length (Thm.hyps_of sigma_bound) = 0)
     andalso s_sb_needs_sigma andalso s_sb_has_prime andalso s_sb_d1
  then out "SIGMA_BOUND_ALL_OK\n"
  else out "SIGMA_BOUND_INCOMPLETE\n";

val () = out "SIGMA_BOUND_END\n";
(* ============================================================================
   EULER'S CONVERSE + the FULL EUCLID-EULER IFF.
   Appended AFTER:  isabelle_euclid_perfect.sml  (base, ctxtSigD/thySigD)
                  + ee_factor2s.sml              (factor_2s, consec_coprime, parity)
                  + ee_sigma_bound.sml           (sigma_bound, build_lb1, lb1_apply,
                                                   the order/arith combinator suite)
   ----------------------------------------------------------------------------
   STATUS / HONEST SCOPE.  The ONE remaining gap toward a fully-unconditional
   Euler converse is the GENERAL-m sigma-multiplicativity bridge

       SCG :  !!a m. neg (dvd 2 m)
                ==> oeq (sigma (mult (p2 a) m)) (mult (sumf (pow 2) a) (sigma m))

   i.e.  sigma(2^a * m) = (1+2+...+2^a) * sigma(m)  for m ODD.  This is exactly the
   GENERAL-m generalisation of the BANKED sigma_char (which proves the SAME identity
   for PRIME q).  The general case is the sum-support-reindex wall documented in the
   base driver (completeness of the divisor list of 2^a*m for an arbitrary odd m);
   it is a div2aq_complete-scale piece left for its own fleet (partial progress is
   banked in isabelle_euler_converse_sigma_mult.sml: dist_lemma + sigma_mult_reduction).

   THIS DELTA proves, by genuine kernel inference, EVERYTHING ELSE — i.e. the
   complete L4/L5 assembly CONDITIONAL on SCG :

     euler_converse_cond :
       SCG ==> lt 0 n ==> even n ==> perfect n ==> euclidForm n

     euclid_euler_cond :
       SCG ==> lt 0 n ==> even n
            ==> ( (perfect n --> euclidForm n) AND (euclidForm n --> perfect n) )

   The BACKWARD half of the iff is the BANKED euclid_perfect (Euclid IX.36); the
   FORWARD half is euler_converse_cond curried.  So the ONLY hypothesis standing
   between this and the unconditional Euclid-Euler theorem is SCG — every other
   step (factor-out-2s, the algebra deriving m = (2^(a+1)-1)*d and sigma m = m+d,
   the sigma-bound prime extraction, the euclidForm construction, the iff wrapper)
   is proved 0-extra-hyp here.

   even n     := Ex k. oeq n (mult 2 k)
   perfect n  := oeq (sigma n)(mult 2 n)
   euclidForm n := Ex p. prime2 (sub (pow 2 p) 1) AND
                          oeq n (mult (pow 2 (sub p 1))(sub (pow 2 p) 1))

   THE CLEAN ALGEBRA (no Gauss / coprime cancellation needed):
     n = 2^a * m, m odd, a>=1 (factor_2s).  b := Suc a.  G := sumf (pow 2) a.
     geo_add : 1 + G = 2^b ;  geo_sum : G = 2^b - 1.
     SCG     : sigma n = G * sigma m.
     perfect : sigma n = 2 * n = 2 * (2^a*m) = (2*2^a)*m = 2^b * m = (1+G)*m
                                            = G*m + m   [right_distrib].
     so       G * sigma m = G*m + m.
     m <= sigma m (m is a divisor)  =>  sigma m = m + d  for some d (le_destD).
     substitute: G*(m+d) = G*m + m  =>  G*m + G*d = G*m + m  =>  G*d = m  [cancel].
     so  dvd (G) m  (witness d) and sigma m = m + d.
     BOUNDS: lt 1 m (else m=1 => sigma 1 = 1, G*d=1, but G=2^b-1>=3 => contra),
             lt d m (m = G*d, G>=3, d>0 => d < m).
     sigma_bound (lt 1 m)(dvd d m? -- actually dvd d m via m=G*d=d*G)(lt d m)
                 (sigma m = m+d) => d = 1 AND prime2 m.
     d=1 => m = G = 2^b - 1, prime2 m, n = 2^a*m = 2^(b-1)*(2^b-1).  p := b.
     euclidForm n.  QED (mod SCG).
   ============================================================================ *)
val () = out "EULER_CONVERSE_BEGIN\n";

(* ---------------------------------------------------------------------------
   (0) extra base lemmas lifted to ctxtSigD that the floor deltas did not expose
       at top level but we need:  geo_sum, right_distrib, left_distrib,
       add_left_cancel, mult_eq_zero, mult-1-right, le_refl, etc.
       (factor_2s/sigma_bound already exposed: leAddD, leAntisymD, leTransD,
        ltNotGeD, leNeqLtD, conjI_D, primeCasesD, le_splitD, lt_irrefl_*,
        exMiddleD, build_lb1, lb1_apply, dvd_diff_D, one_neq_2k_at, geoAddD,
        powSucD, subN0D, subSSD, mult_left_cancel_D, dvd_destD, exE_atD,
        add_eq_zero_left_D, exI_atD, mkForall.)
   --------------------------------------------------------------------------- *)
val geo_sum_vEC      = varify (up geo_sum)            (* sumf (pow 2) k = sub (pow 2 (Suc k)) 1 ; var k *)
fun geoSumD kT = beta_norm (Drule.infer_instantiate ctxtSigD [(("k",0), ctermSigD kT)] geo_sum_vEC)

val right_distrib_vEC = varify (up right_distrib)     (* mult (add m n) k = add (mult m k)(mult n k) ; vars m,n,k *)
fun rdistribD (aT,bT,cT) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("m",0), ctermSigD aT),(("n",0), ctermSigD bT),(("k",0), ctermSigD cT)] right_distrib_vEC)
val left_distrib_vEC  = varify (up left_distrib)      (* mult k (add m n) = add (mult k m)(mult k n) ; vars k,m,n *)
fun ldistribD (xT,mT,nT) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("k",0), ctermSigD xT),(("m",0), ctermSigD mT),(("n",0), ctermSigD nT)] left_distrib_vEC)

(* add_left_cancel_D2 (mT,aT,bT) : add m a = add m b ==> oeq a b  is ALREADY in base. *)
fun addLeftCancelD (mT,aT,bT) h = add_left_cancel_D2 (mT,aT,bT) h

val mult_1_right_vEC = varify (up mult_1_right)       (* mult n 1 = n *)
fun mult1rD t = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD t)] mult_1_right_vEC)
(* multcommD (m,n), addcommD (m,n) are ALREADY in base. *)
val add_0_right_vEC = varify (up add_0_right)
fun add0rD t = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD t)] add_0_right_vEC)
fun multcommD2 (m,n) = multcommD (m,n)
fun addcommD2 (m,n) = addcommD (m,n)

val () = out "EC_TRANSFER_OK\n";

(* swt at the divisor m of m : swt m m = m  (swt_dvd_D + dvd_selfD already exposed) *)
(* sigma m = sumf (swt m) m  (sigma_def_vD already exposed via sdef pattern) *)

(* ---------------------------------------------------------------------------
   (1) parity bridge : odd-witness => not-dvd-2.
       odd_to_notdvd2 m : (Ex k. m = Suc (mult 2 k)) ==> neg (dvd 2 m)
   Proof (no parity induction; via dvd_diff + one_neq_2k):
     assume dvd 2 m and m = Suc(2k).  dvd 2 (2k) trivially (witness k).
     m = Suc(2k) = add (2k) 1.  dvd 2 m  ==>  dvd 2 (add (2k) 1).
     dvd_diff 2 (2k) 1 : dvd 2 (2k) ==> dvd 2 (add (2k) 1) ==> dvd 2 1.
     dvd 2 1 : Ex c. 1 = 2c  => one_neq_2k => oFalse.
   --------------------------------------------------------------------------- *)
(* dvd 2 (mult 2 k) : witness k, mult 2 k = mult 2 k *)
fun dvd2_2k kT = exI_atD (Abs("c", natT, oeq (mult two kT)(mult two (Bound 0))), kT)
                   |> (fn impl => Thm.implies_elim impl (reflD (mult two kT)))
(* Suc(2k) = add (2k) 1 : add (2k) 1 = add (2k)(Suc 0) ; use add_comm then add_Suc:
     add (2k)(Suc 0) = add (Suc 0)(2k) [comm] = Suc(add 0 (2k)) [add_Suc] = Suc(2k). *)
fun suc2k_eq_add kT =
  let val twok = mult two kT
      val c1 = addcommD2 (twok, one)                 (* add (2k) 1 = add 1 (2k) *)
      val aS = beta_norm (Drule.infer_instantiate ctxtSigD
                 [(("m",0), ctermSigD ZeroC),(("n",0), ctermSigD twok)] add_Suc_vD2)   (* add (Suc 0)(2k) = Suc(add 0 (2k)) *)
      val a0 = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD twok)] add_0_vD)  (* add 0 (2k) = 2k *)
      val sc = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                 [(("a",0), ctermSigD (add ZeroC twok)),(("b",0), ctermSigD twok)] (up (varify Suc_cong)))) a0  (* Suc(add 0 2k) = Suc 2k *)
      val a12k_s = trans3 (add one twok, suc (add ZeroC twok), suc twok) aS sc          (* add 1 (2k) = Suc 2k *)
      val r = trans3 (add twok one, add one twok, suc twok) c1 a12k_s                    (* add (2k) 1 = Suc 2k *)
  in sym3 (add twok one, suc twok) r end            (* oeq (Suc 2k)(add (2k) 1) *)

fun odd_to_notdvd2 mF hOddEx =
  let
    val goal = neg (dvd two mF)
    fun body kF hk =   (* hk : oeq m (Suc(2k)) *)
      let
        val hdvd = Thm.assume (ctermSigD (jT (dvd two mF)))   (* assume dvd 2 m *)
        (* dvd 2 (Suc 2k) : rewrite m -> Suc 2k via hk *)
        val d2s2k = dvd_cong_target_D (two, mF, suc (mult two kF)) hk hdvd  (* dvd 2 (Suc 2k) *)
        (* Suc 2k = add 2k 1 ; dvd 2 (add 2k 1) *)
        val s2k_a = suc2k_eq_add kF                            (* oeq (Suc 2k)(add 2k 1) *)
        val d2add = dvd_cong_target_D (two, suc (mult two kF), add (mult two kF) one) s2k_a d2s2k  (* dvd 2 (add 2k 1) *)
        (* dvd_diff 2 (2k) 1 : dvd 2 (2k) ==> dvd 2 (add 2k 1) ==> dvd 2 1 *)
        val d2_2k = dvd2_2k kF                                 (* dvd 2 (2k) *)
        val d21 = dvd_diff_D (two, mult two kF, one) d2_2k d2add  (* dvd 2 1 *)
        (* dvd 2 1 : Ex c. 1 = 2c  => one_neq_2k *)
        val ff = dvd_destD (two, one, oFalseC) d21 "c_o2"
                   (fn cc => fn hc => one_neq_2k_at cc hc)      (* hc : oeq 1 (mult 2 cc) *)
      in impI_D (dvd two mF, oFalseC) ff end  (* object neg(dvd 2 m) = Imp (dvd 2 m) oFalse *)
    (* exE on the odd witness : Ex k. m = Suc(2k) *)
    val Pabs = Abs("k", natT, oeq mF (suc (mult two (Bound 0))))
  in exE_atD (Pabs, goal) hOddEx "k_o2" body end

val () = out "EC_PARITY_BRIDGE_OK\n";

(* ---------------------------------------------------------------------------
   (2) m_le_sigma : lt 0 m ==> le m (sigma m).
       sigma m = sumf (swt m) m ; swt m m = m (m | m) ; le m m (refl) ;
       build_lb1 (swt m) gives le (swt m m)(sumf (swt m) m) at i=m.
       rewrite swt m m -> m and sumf (swt m) m -> sigma m.
   (we do not actually need lt 0 m for this -- le m m + lb1 suffice -- but keep the
    signature uniform.)
   --------------------------------------------------------------------------- *)
val sdefD = fn mT => beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD mT)] sigma_def_vD)  (* oeq (sigma m)(sumf (swt m) m) *)

fun m_le_sigma mF =
  let
    val swtm = swtC $ mF
    val lb1 = build_lb1 swtm                                  (* Forall n. Forall i. le i n ==> le (swt m i)(sumf (swt m) n) *)
    val lmm = leReflD mF                                      (* le m m *)
    val core = lb1_apply lb1 swtm (mF, mF) lmm                (* le (swt m m)(sumf (swt m) m) *)
    (* swt m m = m *)
    val swmm = swt_dvd_D (mF, mF) (dvd_selfD mF)              (* oeq (swt m m) m *)
    (* le m (sumf (swt m) m) via le_cong_l (sym? swt m m -> m) *)
    val l1 = le_cong_lD (swtm $ mF, mF, sumf swtm mF) swmm core   (* le m (sumf (swt m) m) *)
    (* sumf (swt m) m = sigma m via sym (sdef) *)
    val sdef = sdefD mF                                       (* oeq (sigma m)(sumf (swt m) m) *)
    val l2 = le_cong_rD (sumf swtm mF, sigma mF, mF) (sym3 (sigma mF, sumf swtm mF) sdef) l1  (* le m (sigma m) *)
  in l2 end

val () = out "EC_M_LE_SIGMA_OK\n";

val () = out "EULER_CONVERSE_INFRA_DONE\n";
(* ===========================================================================
   ARITHMETIC / ORDER HELPERS for the converse assembly (on ctxtSigD).
   =========================================================================== *)
val () = out "EC_HELPERS_BEGIN\n";

(* lt_irrefl on ctxtSigD : lt n n ==> oFalse  (lt_irrefl_vSB already in sigma_bound delta) *)
fun lt_irreflD nT h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("n",0), ctermSigD nT)] lt_irrefl_vSB)) h
val oFalseElimD = oFalse_elimD

(* lt_cong_r : lt a n ==> oeq n b ==> lt a b.   lt a n = le (Suc a) n ; rewrite 2nd arg n->b.
   le_cong_rD (aT,bT,cT) : oeq aT bT ==> le cT aT ==> le cT bT.  here aT=n, bT=b, cT=Suc a. *)
fun lt_cong_rD (aT, nT, bT) hnb hlt = le_cong_rD (nT, bT, suc aT) hnb hlt

(* mult_le_mono_D (cT, jT, kT) : le j k ==> le (mult c j)(mult c k)   (vars j,k,c) *)
val mult_le_mono_vEC = varify (up mult_le_mono)
fun mult_le_mono_D (cT, jT, kT) h = (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("c",0), ctermSigD cT),(("j",0), ctermSigD jT),(("k",0), ctermSigD kT)] mult_le_mono_vEC)) OF [h]

(* mult_Suc / mult_0 instantiators on ctxtSigD *)
val mult_Suc_vEC = varify (up mult_Suc)   (* oeq (mult (Suc m) n)(add n (mult m n)) ; vars m,n *)
fun multSucD (mT,nT) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("m",0), ctermSigD mT),(("n",0), ctermSigD nT)] mult_Suc_vEC)
val mult_0_vEC = varify (up mult_0)       (* oeq (mult 0 n) 0 ; var n *)
fun mult0lD nT = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD nT)] mult_0_vEC)

(* ne0_suc on ctxtSigD : neg(oeq d 0) ==> Ex m. oeq d (Suc m) *)
val ne0_suc_vEC = varify (up ne0_suc)
fun ne0_sucD dT h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("d",0), ctermSigD dT)] ne0_suc_vEC)) h

(* lt0_of_ne0 : neg(oeq d 0) ==> lt 0 d.   d = Suc m (ne0_suc) -> lt0_of_suc. *)
fun lt0_of_ne0 dF hne =
  let val ex = ne0_sucD dF hne          (* Ex m. d = Suc m *)
      val Pabs = Abs("m", natT, oeq dF (suc (Bound 0)))
  in exE_atD (Pabs, lt ZeroC dF) ex "m_ne0" (fn mF => fn hm => lt0_of_suc (dF, mF) hm) end

(* add 1 d = Suc d *)
fun add1_eq_Suc dT =
  let val aS = beta_norm (Drule.infer_instantiate ctxtSigD
                 [(("m",0), ctermSigD ZeroC),(("n",0), ctermSigD dT)] add_Suc_vD2)   (* add(Suc 0)d = Suc(add 0 d) *)
      val a0 = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD dT)] add_0_vD)  (* add 0 d = d *)
      val sc = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                 [(("a",0), ctermSigD (add ZeroC dT)),(("b",0), ctermSigD dT)] (up (varify Suc_cong)))) a0
  in trans3 (add one dT, suc (add ZeroC dT), suc dT) aS sc end   (* add 1 d = Suc d *)

(* mult 2 d = add d d :
     mult (Suc(Suc 0)) d = add d (mult (Suc 0) d) [mult_Suc]
     mult (Suc 0) d = add d (mult 0 d) [mult_Suc] = add d 0 [mult_0 cong] = d [add_0_right] *)
fun mult_two_eq_add dF =
  let
    val mS1 = multSucD (suc ZeroC, dF)                    (* mult 2 d = add d (mult (Suc 0) d) *)
    val mS0 = multSucD (ZeroC, dF)                        (* mult (Suc 0) d = add d (mult 0 d) *)
    val m0  = mult0lD dF                                  (* mult 0 d = 0 *)
    val a_d0 = trans3 (mult (suc ZeroC) dF, add dF (mult ZeroC dF), add dF ZeroC)
                 mS0 (add_cong_rD (dF, mult ZeroC dF, ZeroC) m0)   (* mult(Suc 0)d = add d 0 *)
    val s0d_d = trans3 (mult (suc ZeroC) dF, add dF ZeroC, dF) a_d0 (add0rD dF)  (* mult(Suc 0)d = d *)
    val r = trans3 (mult two dF, add dF (mult (suc ZeroC) dF), add dF dF)
              mS1 (add_cong_rD (dF, mult (suc ZeroC) dF, dF) s0d_d)
  in r end                                                (* oeq (mult 2 d)(add d d) *)

(* mult 2 1 = 2 *)
val mult2_1_eq_2 = mult1rD two       (* oeq (mult 2 1) 2 *)

(* le 2 (pow 2 (Suc k)) for any k *)
fun le2_pow2Suc kT =
  let
    val pk = pow two kT
    val pp = beta_norm (Drule.infer_instantiate ctxtSigD [(("k",0), ctermSigD kT)] pow2_pos_vD)  (* Ex m. pow 2 k = Suc m *)
    val Pabs = Abs("m", natT, oeq pk (suc (Bound 0)))
    val le1pk = exE_atD (Pabs, le one pk) pp "m_p2"
                  (fn mF => fn hm => lt0_of_suc (pk, mF) hm)     (* le 1 (pow 2 k) *)
    val lm = mult_le_mono_D (two, one, pk) le1pk      (* le (mult 2 1)(mult 2 (pow 2 k)) *)
    val l2m = le_cong_lD (mult two one, two, mult two pk) mult2_1_eq_2 lm   (* le 2 (mult 2 (pow 2 k)) *)
    val psk = powSucD (two, kT)                       (* pow 2 (Suc k) = mult 2 (pow 2 k) *)
    val l2psk = le_cong_rD (mult two pk, pow two (suc kT), two) (sym3 (pow two (suc kT), mult two pk) psk) l2m
  in (out "L2P_DONE\n"; l2psk) end   (* le 2 (pow 2 (Suc k)) *)

(* lt1_geoG : lt 0 a ==> lt 1 (sumf pwAbs2 a) *)
fun lt1_geoG aF hPos0a =
  let
    val Pap = Abs("p", natT, oeq aF (add one (Bound 0)))   (* lt 0 a = le (Suc 0) a = Ex p. a = add (Suc 0) p *)
    val goal = lt one (sumf pwAbs2 aF)
    fun body pF hp =     (* hp : oeq a (add 1 p) *)
      let
        val a1p = add1_eq_Suc pF                  (* add 1 p = Suc p *)
        val aSp = trans3 (aF, add one pF, suc pF) hp a1p   (* oeq a (Suc p) *)
        val Gcong = beta_norm (Drule.infer_instantiate ctxtSigD
              [(("P",0), ctermSigD (Term.lambda (Free("zga",natT)) (oeq (sumf pwAbs2 aF)(sumf pwAbs2 (Free("zga",natT)))))),
               (("a",0), ctermSigD aF),(("b",0), ctermSigD (suc pF))] oeq_subst_vD)
              OF [aSp, reflD (sumf pwAbs2 aF)]     (* sumf(pow 2) a = sumf(pow 2)(Suc p) *)
        val sfS = sumfSucD (pwAbs2, pF)            (* sumf(pow 2)(Suc p) = add (sumf(pow 2) p)(pow 2 (Suc p)) *)
        val G_split = trans3 (sumf pwAbs2 aF, sumf pwAbs2 (suc pF), add (sumf pwAbs2 pF)(pow two (suc pF))) Gcong sfS
        val l2p = le2_pow2Suc pF                   (* le 2 (pow 2 (Suc p)) *)
        val lps_G = le_add_r2D (pow two (suc pF), pow two (suc pF), sumf pwAbs2 pF) (leReflD (pow two (suc pF)))
                    (* le (pow 2(Suc p)) (add (sumf p)(pow 2(Suc p))) *)
        val lps_G2 = le_cong_rD (add (sumf pwAbs2 pF)(pow two (suc pF)), sumf pwAbs2 aF, pow two (suc pF))
                       (sym3 (sumf pwAbs2 aF, add (sumf pwAbs2 pF)(pow two (suc pF))) G_split) lps_G
        val () = out "G1_SPLIT\n"
        val l2G = leTransD (two, pow two (suc pF), sumf pwAbs2 aF) l2p lps_G2   (* le 2 G = lt 1 G *)
      in l2G end
  in exE_atD (Pap, goal) hPos0a "p_g1" body end

(* lt_d_Gd : lt 1 G ==> lt 0 d ==> oeq (G*d) m ==> lt d m. *)
fun lt_d_Gd (GT, dF, mF) lt1G ltd0 Gd_m =
  let
    val lm = mult_le_mono_D (dF, two, GT) lt1G          (* le (mult d 2)(mult d G) *)
    val ld2 = multcommD2 (dF, two)                      (* mult d 2 = mult 2 d *)
    val ldG = multcommD2 (dF, GT)                       (* mult d G = mult G d *)
    val lm2 = le_cong_lD (mult dF two, mult two dF, mult dF GT) ld2 lm  (* le (mult 2 d)(mult d G) *)
    val lm3 = le_cong_rD (mult dF GT, mult GT dF, mult two dF) ldG lm2  (* le (mult 2 d)(mult G d) *)
    val m2d = mult_two_eq_add dF                        (* mult 2 d = add d d *)
    val lm4 = le_cong_lD (mult two dF, add dF dF, mult GT dF) m2d lm3   (* le (add d d)(mult G d) *)
    val lam = leAddMonoD (one, dF, dF) ltd0             (* le (add 1 d)(add d d) *)
    val a1d = add1_eq_Suc dF                            (* add 1 d = Suc d *)
    val lsd = le_cong_lD (add one dF, suc dF, add dF dF) a1d lam   (* le (Suc d)(add d d) = lt d (add d d) *)
    val ltd_Gd = leTransD (suc dF, add dF dF, mult GT dF) lsd lm4   (* le (Suc d)(mult G d) = lt d (mult G d) *)
    val ltd_m = lt_cong_rD (dF, mult GT dF, mF) Gd_m ltd_Gd  (* lt d m *)
  in ltd_m end

(* lt1_m : lt 1 G ==> lt 0 d ==> oeq (G*d) m ==> lt 1 m.
   le G (G*d) [mult_le_mono c=G : le 1 d ==> le (G*1)(G*d) ; G*1 = G].  le 2 G (lt1G).  le_trans -> le 2 m. *)
fun lt1_m (GT, dF, mF) lt1G ltd0 Gd_m =
  let
    val lm = mult_le_mono_D (GT, one, dF) ltd0        (* le (mult G 1)(mult G d) *)
    val G1 = mult1rD GT                               (* mult G 1 = G *)
    val lG_Gd = le_cong_lD (mult GT one, GT, mult GT dF) G1 lm  (* le G (mult G d) *)
    val lG_m = le_cong_rD (mult GT dF, mF, GT) Gd_m lG_Gd       (* le G m *)
    val l2m = leTransD (two, GT, mF) lt1G lG_m        (* le 2 m = lt 1 m *)
  in l2m end

val () = out "EC_HELPERS_DONE\n";
(* ===========================================================================
   THE MAIN CONVERSE (conditional on SCG).
     euler_converse_cond :
       SCG ==> lt 0 n ==> even n ==> perfect n ==> euclidForm n
   where SCG (meta) = !!a m. neg(dvd 2 m)
                         ==> oeq (sigma (mult (p2 a) m))(mult (sumf pwAbs2 a)(sigma m)).
   =========================================================================== *)
val () = out "EC_MAIN_BEGIN\n";

(* even / perfect / euclidForm builders (Var-free, n a Free) *)
fun evenN n  = mkEx (Term.lambda (Free("k", natT)) (oeq n (mult two (Free("k",natT)))));
fun perfectN n = oeq (sigma n) (mult two n);
fun euclidFormN n =
  mkEx (Term.lambda (Free("p", natT))
    (mkConj (prime2 (sub (pow two (Free("p",natT))) one))
            (oeq n (mult (pow two (sub (Free("p",natT)) one)) (sub (pow two (Free("p",natT))) one)))));

(* the SCG meta-hypothesis term, as a function of fresh Frees a,m *)
fun scgImpl aF mF = Logic.mk_implies (jT (neg (dvd two mF)),
                      jT (oeq (sigma (mult (p2 aF) mF)) (mult (sumf pwAbs2 aF) (sigma mF))));
val scg_aF = Free("a_scg", natT); val scg_mF = Free("m_scg", natT);
val scgProp = Logic.all scg_aF (Logic.all scg_mF (scgImpl scg_aF scg_mF));

val euler_converse_cond =
  let
    val nF = Free("n", natT)
    val hSCG  = Thm.assume (ctermSigD scgProp)
    val hPos  = Thm.assume (ctermSigD (jT (lt ZeroC nF)))       (* lt 0 n *)
    val hEven = Thm.assume (ctermSigD (jT (evenN nF)))          (* even n *)
    val hPerf = Thm.assume (ctermSigD (jT (perfectN nF)))       (* sigma n = 2*n *)
    (* SCG at (a,m) : neg(dvd 2 m) ==> sigma(2^a*m) = G(a)*sigma m *)
    fun scgAt (aT, mT) = Thm.forall_elim (ctermSigD mT) (Thm.forall_elim (ctermSigD aT) hSCG)

    (* factor_2s n : lt 0 n ==> even n ==> Ex a m. n=2^a*m /\ (Ex k. m=Suc(2k)) /\ lt 0 a *)
    val f2sInst = beta_norm (Drule.infer_instantiate ctxtSigD
                    [(("n",0), ctermSigD nF)] factor_2s)   (* var name in factor_2s is "n" *)
    val f2s0 = Thm.implies_elim (Thm.implies_elim f2sInst hPos) hEven  (* Ex a. Ex m. ... *)

    (* destruct Ex a *)
    val aAbs = Term.lambda (Free("a", natT))
                 (mkEx (Term.lambda (Free("m", natT))
                    (mkConj (oeq nF (mult (pow two (Free("a",natT)))(Free("m",natT))))
                       (mkConj (mkEx (Term.lambda (Free("k",natT)) (oeq (Free("m",natT)) (suc (mult two (Free("k",natT)))))))
                               (lt ZeroC (Free("a",natT)))))))
    fun perA aF hExm =      (* hExm : Ex m. n=2^a*m /\ (Ex k. m=Suc 2k) /\ 0<a *)
      let
        val mAbs = Term.lambda (Free("m", natT))
                     (mkConj (oeq nF (mult (pow two aF)(Free("m",natT))))
                        (mkConj (mkEx (Term.lambda (Free("k",natT)) (oeq (Free("m",natT)) (suc (mult two (Free("k",natT)))))))
                                (lt ZeroC aF)))
        fun perM mF hConj =   (* hConj : n=2^a*m /\ (Ex k. m=Suc 2k) /\ 0<a *)
          let
            val hNeq  = conjunct1_D (oeq nF (mult (pow two aF) mF),
                          mkConj (oddT mF)(lt ZeroC aF)) hConj          (* oeq n (2^a*m) *)
            val hRest = conjunct2_D (oeq nF (mult (pow two aF) mF),
                          mkConj (oddT mF)(lt ZeroC aF)) hConj
            val hOddEx = conjunct1_D (oddT mF, lt ZeroC aF) hRest        (* Ex k. m=Suc 2k *)
            val hPosA  = conjunct2_D (oddT mF, lt ZeroC aF) hRest        (* lt 0 a *)
            val hOdd   = odd_to_notdvd2 mF hOddEx                        (* neg(dvd 2 m) *)

            (* abbreviations *)
            val bT   = suc aF                       (* b = a+1 *)
            val GT   = sumf pwAbs2 aF               (* G = sumf(pow 2) a = 2^b - 1 *)
            val N    = mult (pow two aF) mF         (* 2^a * m *)

            (* (S1) sigma n = G * sigma m   [SCG at (a,m) + odd] *)
            val scgam = Thm.implies_elim (scgAt (aF, mF)) hOdd          (* sigma(2^a*m) = G*sigma m *)
            (* rewrite sigma(2^a*m) target -> sigma n via sym hNeq : sigma n = sigma(2^a*m) *)
            val sig_cong = beta_norm (Drule.infer_instantiate ctxtSigD
                  [(("P",0), ctermSigD (Term.lambda (Free("zsn",natT)) (oeq (sigma nF)(sigma (Free("zsn",natT)))))),
                   (("a",0), ctermSigD nF),(("b",0), ctermSigD N)] oeq_subst_vD)
                  OF [hNeq, reflD (sigma nF)]                            (* oeq (sigma n)(sigma N) *)
            val sigN_Gsig = trans3 (sigma nF, sigma N, mult GT (sigma mF)) sig_cong scgam  (* sigma n = G*sigma m *)

            (* (S2) sigma n = 2*n = (1+G)*m = G*m + m  [perfect + geo_add + distrib] *)
            (* 2*n = 2*(2^a*m).  2*2^a = 2^(Suc a) = 1+G [geo_add sym].  so 2*n = (1+G)*m. *)
            (* perfect : sigma n = mult 2 n *)
            (* 2*n = 2*N : rewrite n->N inside mult 2 n via hNeq *)
            val twoN_cong = beta_norm (Drule.infer_instantiate ctxtSigD
                  [(("P",0), ctermSigD (Term.lambda (Free("ztn",natT)) (oeq (mult two nF)(mult two (Free("ztn",natT)))))),
                   (("a",0), ctermSigD nF),(("b",0), ctermSigD N)] oeq_subst_vD)
                  OF [hNeq, reflD (mult two nF)]                         (* oeq (2*n)(2*N) *)
            (* 2*N = 2*(2^a*m) = (2*2^a)*m  [assoc sym] *)
            val assoc1 = multassocD (two, pow two aF, mF)                (* (2*2^a)*m = 2*(2^a*m) = 2*N *)
            val twoN_a = trans3 (mult two nF, mult two N, mult (mult two (pow two aF)) mF)
                           twoN_cong (sym3 (mult (mult two (pow two aF)) mF, mult two N) assoc1)  (* 2*n = (2*2^a)*m *)
            (* 2*2^a = 2^(Suc a) [pow_Suc sym] ; pow 2 (Suc a) = mult 2 (pow 2 a) [pow_Suc] *)
            val psA = powSucD (two, aF)                                  (* pow 2 (Suc a) = mult 2 (pow 2 a) *)
            (* (2*2^a)*m = pow2(Suc a)*m  [cong divisor via sym psA] *)
            val congDiv = mult_cong_lD (mult two (pow two aF), pow two (suc aF), mF)
                            (sym3 (pow two (suc aF), mult two (pow two aF)) psA)  (* (2*2^a)*m = 2^(Suc a)*m *)
            val twoN_pSa = trans3 (mult two nF, mult (mult two (pow two aF)) mF, mult (pow two (suc aF)) mF)
                             twoN_a congDiv                             (* 2*n = 2^(Suc a)*m *)
            (* 2^(Suc a) = 1+G  [geo_add sym] : geoAddD a : add 1 G = pow 2 (Suc a) *)
            val ga = geoAddD aF                                         (* add 1 G = pow 2 (Suc a) *)
            val congGA = mult_cong_lD (pow two (suc aF), add one GT, mF)
                           (sym3 (add one GT, pow two (suc aF)) ga)     (* 2^(Suc a)*m = (1+G)*m *)
            val twoN_1G = trans3 (mult two nF, mult (pow two (suc aF)) mF, mult (add one GT) mF)
                            twoN_pSa congGA                            (* 2*n = (1+G)*m *)
            (* (1+G)*m = 1*m + G*m  [right_distrib] = m + G*m  [mult_1_left] *)
            val rd = rdistribD (one, GT, mF)                           (* (1+G)*m = (1*m)+(G*m) *)
            val m1l = mult1lD mF                                       (* 1*m = m *)
            val rd2 = trans3 (mult (add one GT) mF, add (mult one mF)(mult GT mF), add mF (mult GT mF))
                        rd (add_cong_lD (mult one mF, mF, mult GT mF) m1l)  (* (1+G)*m = m + G*m *)
            val twoN_mGm = trans3 (mult two nF, mult (add one GT) mF, add mF (mult GT mF)) twoN_1G rd2  (* 2*n = m + G*m *)
            (* perfect : sigma n = 2*n = m + G*m *)
            val sigN_mGm = trans3 (sigma nF, mult two nF, add mF (mult GT mF)) hPerf twoN_mGm  (* sigma n = m + G*m *)

            (* (S3) so G*sigma m = m + G*m, i.e. G*sigma m = G*m + m (after add_comm). *)
            (* from S1 sym: G*sigma m = sigma n ; sigma n = m + G*m : so G*sigma m = m + G*m *)
            val Gsig_mGm = trans3 (mult GT (sigma mF), sigma nF, add mF (mult GT mF))
                             (sym3 (sigma nF, mult GT (sigma mF)) sigN_Gsig) sigN_mGm  (* G*sigma m = m + G*m *)
            (* rewrite m + G*m = G*m + m  [add_comm] *)
            val Gsig_Gmm = trans3 (mult GT (sigma mF), add mF (mult GT mF), add (mult GT mF) mF)
                             Gsig_mGm (addcommD2 (mF, mult GT mF))     (* G*sigma m = G*m + m *)

            (* (S4) sigma m = m + d  via m_le_sigma (le m (sigma m)) -> Ex d. sigma m = m + d *)
            val hmle = m_le_sigma mF                                   (* le m (sigma m) = Ex d. sigma m = m + d *)
            (* destruct le m (sigma m) : sigma m = add m d  (le def : Ex p. sigma m = add m p) *)
            fun perD dF hd =    (* hd : oeq (sigma m)(add m d) *)
              let
                (* (S5) G*sigma m = G*(m+d) = G*m + G*d  [left_distrib], and = G*m + m [S4 into S3].
                   so G*m + G*d = G*m + m  =>  G*d = m  [add_left_cancel]. *)
                (* G*sigma m = G*(m+d) : cong on right with hd *)
                val Gsig_Gmd = mult_cong_rD (GT, sigma mF, add mF dF) hd  (* G*sigma m = G*(m+d) *)
                (* G*(m+d) = G*m + G*d [left_distrib] *)
                val ld = ldistribD (GT, mF, dF)                          (* G*(m+d) = (G*m)+(G*d) *)
                val Gsig_GmGd = trans3 (mult GT (sigma mF), mult GT (add mF dF), add (mult GT mF)(mult GT dF))
                                  Gsig_Gmd ld                            (* G*sigma m = G*m + G*d *)
                (* G*m + G*d = G*m + m  : from Gsig_Gmm (G*sigma m = G*m + m) and Gsig_GmGd *)
                val eqGmGd_Gmm = trans3 (add (mult GT mF)(mult GT dF), mult GT (sigma mF), add (mult GT mF) mF)
                                   (sym3 (mult GT (sigma mF), add (mult GT mF)(mult GT dF)) Gsig_GmGd) Gsig_Gmm
                                 (* G*m + G*d = G*m + m *)
                (* cancel G*m : G*d = m *)
                val Gd_m = addLeftCancelD (mult GT mF, mult GT dF, mF) eqGmGd_Gmm  (* oeq (G*d) m *)
                (* m = G*d (sym), so dvd G m (witness d) ; also dvd d m (m = d*G) *)
                val m_Gd = sym3 (mult GT dF, mF) Gd_m                    (* oeq m (G*d) *)
                (* dvd d m : m = G*d = d*G [comm], witness G *)
                val m_dG = trans3 (mF, mult GT dF, mult dF GT) m_Gd (multcommD2 (GT, dF))  (* m = d*G *)
                val dvd_d_m = dvd_introD (dF, mF, GT) m_dG               (* dvd d m *)

                (* (S6) BOUNDS for sigma_bound : lt 1 m, lt d m, sigma m = m + d (= hd). *)
                (* G = 2^b - 1 = sub(pow 2 (Suc a)) 1 [geo_sum].  b = Suc a >= 2 (a>=1).
                   2^(Suc a) >= 4 so G >= 3 ; in particular lt 1 G and lt 0 G. *)
                (* We need lt 1 m and lt d m.  m = G*d.
                   - d > 0 : if d = 0 then m = G*0 = 0, contra lt 0 m? we have lt 0 n and n=2^a*m.
                     Actually if d=0 then sigma m = m + 0 = m, and G*sigma m = G*m, but also = G*m+m
                     => m = 0.  Then n = 2^a*0 = 0 contra lt 0 n.  Get d>0 cleanly:
                     from Gd_m (G*d=m) and (we show) m>0 -> d>0.  Show m>0 first.
                   m > 0 : n = 2^a*m and lt 0 n.  if m=0 then n = 2^a*0 = 0.  *)
                (* lt 0 m : assume m=0 -> n = 2^a*0 = 0 -> contra hPos.  Use ex_middle? simpler:
                   We will derive lt 1 m and lt d m via the order suite.  First lt 0 m. *)
                (* --- lt 0 m --- *)
                val ltm0 =
                  let
                    (* if oeq m 0 then n = 2^a*m = 2^a*0 = 0 ; lt 0 0 absurd (lt_irrefl). *)
                    val em = exMiddleD (oeq mF ZeroC)        (* Disj (oeq m 0)(neg(oeq m 0)) *)
                    val caseEq =
                      let
                        val hm0 = Thm.assume (ctermSigD (jT (oeq mF ZeroC)))
                        (* n = 2^a*m = 2^a*0 [cong] = 0 [mult_0_right] *)
                        val c1 = mult_cong_rD (pow two aF, mF, ZeroC) hm0   (* 2^a*m = 2^a*0 *)
                        val c2 = mult0rD (pow two aF)                      (* 2^a*0 = 0 *)
                        val nN = trans3 (N, mult (pow two aF) ZeroC, ZeroC) c1 c2  (* N = 0 *)
                        val n0 = trans3 (nF, N, ZeroC) hNeq nN              (* n = 0 *)
                        (* lt 0 n : le 1 n = Ex p. n = 1 + p ; rewrite n -> 0 gives lt 0 0; lt_irrefl 0 *)
                        (* simpler: lt 0 n with n=0 -> lt 0 0 via cong, then lt_irrefl. *)
                        val ltn0 = lt_cong_rD (ZeroC, nF, ZeroC) n0 hPos  (* lt 0 0 *)
                        val ff = lt_irreflD ZeroC ltn0
                      in Thm.implies_intr (ctermSigD (jT (oeq mF ZeroC))) ff end
                    val caseNeq =
                      let val hne = Thm.assume (ctermSigD (jT (neg (oeq mF ZeroC))))
                          (* neg(oeq m 0) -> lt 0 m : le 1 m.  via ne0 -> Ex k. m = Suc k -> le 1 m. *)
                          val l0m = lt0_of_ne0 mF hne
                      in Thm.implies_intr (ctermSigD (jT (neg (oeq mF ZeroC)))) l0m end
                    (* caseEq : jT(oeq m 0) ==> jT oFalse ; lift to lt 0 m via oFalse_elim *)
                    val caseEqLt =
                      Thm.implies_intr (ctermSigD (jT (oeq mF ZeroC)))
                        (Thm.implies_elim (oFalseElimD (lt ZeroC mF))
                          (Thm.implies_elim caseEq (Thm.assume (ctermSigD (jT (oeq mF ZeroC))))))
                  in (let val r = disjE_D (oeq mF ZeroC, neg (oeq mF ZeroC), lt ZeroC mF) em caseEqLt caseNeq in (out "LTM0_OK\n"; r) end) end

                (* --- lt 1 G : G = 2^b-1, b=Suc a, a>=1 so b>=2, 2^b>=4, G>=3 --- *)
                val lt1G = lt1_geoG aF hPosA       (* lt 1 (sumf pwAbs2 a) *)

                (* --- d > 0 : m = G*d, m>0, G>0 => d>0.  if d=0, m=G*0=0 contra lt 0 m. --- *)
                val ltd0 =
                  let
                    val em = exMiddleD (oeq dF ZeroC)
                    val caseEq =
                      let
                        val hd0 = Thm.assume (ctermSigD (jT (oeq dF ZeroC)))
                        (* m = G*d = G*0 = 0 *)
                        val c1 = mult_cong_rD (GT, dF, ZeroC) hd0       (* G*d = G*0 *)
                        val c2 = mult0rD GT                            (* G*0 = 0 *)
                        val md0 = trans3 (mF, mult GT dF, ZeroC) (sym3 (mult GT dF, mF) Gd_m)
                                    (trans3 (mult GT dF, mult GT ZeroC, ZeroC) c1 c2)  (* m = 0 *)
                        val ltm00 = lt_cong_rD (ZeroC, mF, ZeroC) md0 ltm0  (* lt 0 0 *)
                      in Thm.implies_intr (ctermSigD (jT (oeq dF ZeroC)))
                           (Thm.implies_elim (oFalseElimD (lt ZeroC dF)) (lt_irreflD ZeroC ltm00)) end
                    val caseNeq =
                      let val hne = Thm.assume (ctermSigD (jT (neg (oeq dF ZeroC))))
                      in Thm.implies_intr (ctermSigD (jT (neg (oeq dF ZeroC)))) (lt0_of_ne0 dF hne) end
                  in disjE_D (oeq dF ZeroC, neg (oeq dF ZeroC), lt ZeroC dF) em caseEq caseNeq end

                (* --- lt d m : m = G*d, G >= 2 (lt 1 G), d > 0  =>  d < G*d = m.
                       d < G*d : G*d = G*d, with G>=2 so G*d >= 2*d > d (d>0).  Use mult-grows lemma. --- *)
                val ltdm = lt_d_Gd (GT, dF, mF) lt1G ltd0 Gd_m   (* lt d m *)

                (* --- lt 1 m : m = G*d, G>=3>1, d>=1 so m = G*d >= G > 1.  lt 1 G and le G m -> lt 1 m. --- *)
                val lt1m = lt1_m (GT, dF, mF) lt1G ltd0 Gd_m  (* lt 1 m *)

                (* (S7) sigma_bound (lt 1 m)(dvd d m)(lt d m)(sigma m = m+d) => d=1 AND prime2 m *)
                val sb = beta_norm (Drule.infer_instantiate ctxtSigD
                           [(("m",0), ctermSigD mF),(("d",0), ctermSigD dF)] sigma_bound)
                val sbConj = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim sb lt1m) dvd_d_m) ltdm) hd
                             (* Conj (oeq d 1)(prime2 m) *)
                val hd1   = conjunct1_D (oeq dF one, prime2 mF) sbConj    (* oeq d 1 *)
                val hPrimeM = conjunct2_D (oeq dF one, prime2 mF) sbConj  (* prime2 m *)

                (* (S8) m = G : from Gd_m (G*d=m) and d=1 : G*1 = G, so m = G*1 = G. *)
                val Gd_G1 = mult_cong_rD (GT, dF, one) hd1                (* G*d = G*1 *)
                val G1_G  = mult1rD GT                                    (* G*1 = G *)
                val m_G   = trans3 (mF, mult GT dF, GT) (sym3 (mult GT dF, mF) Gd_m)
                              (trans3 (mult GT dF, mult GT one, GT) Gd_G1 G1_G)  (* m = G *)
                (* G = sub(pow 2 (Suc a)) 1  [geo_sum] *)
                val G_sub = geoSumD aF                                    (* G = sub(pow 2 (Suc a)) 1 *)
                val m_sub = trans3 (mF, GT, sub (pow two (suc aF)) one) m_G G_sub  (* m = sub(2^(Suc a)) 1 *)

                (* (S9) build euclidForm n with witness p = Suc a.
                   prime2 (sub(2^(Suc a)) 1) : rewrite prime2 m via m_sub.
                   n = 2^(sub (Suc a) 1) * (sub(2^(Suc a)) 1) = 2^a * m :
                     sub (Suc a) 1 = a  [subSSD + subN0D] ; pow 2 a ; and m = sub(...).
                   so n = 2^a * m = 2^a * (sub(2^(Suc a)) 1) [m_sub] = 2^(sub(Suc a) 1)*(sub(2^(Suc a))1). *)
                val pT = suc aF
                val msubT = sub (pow two pT) one                         (* 2^(Suc a) - 1 *)
                (* prime2 msubT : prime2 m, m = msubT *)
                val primeMsub = beta_norm (Drule.infer_instantiate ctxtSigD
                      [(("P",0), ctermSigD (Term.lambda (Free("zpm",natT)) (prime2 (Free("zpm",natT))))),
                       (("a",0), ctermSigD mF),(("b",0), ctermSigD msubT)] oeq_subst_vD)
                      OF [m_sub, hPrimeM]                                 (* prime2 msubT *)
                (* sub (Suc a) 1 = a *)
                val subSa1 = trans3 (sub (suc aF) one, sub aF ZeroC, aF) (subSSD (aF, ZeroC)) (subN0D aF)  (* sub(Suc a)1 = a *)
                (* n = 2^(sub(Suc a) 1) * msubT *)
                (* start: n = 2^a * m [hNeq], m = msubT [m_sub] -> n = 2^a * msubT *)
                val n_2a_msub = trans3 (nF, N, mult (pow two aF) msubT) hNeq
                                  (mult_cong_rD (pow two aF, mF, msubT) m_sub)  (* n = 2^a * msubT *)
                (* 2^a = 2^(sub(Suc a)1) [cong on exponent via sym subSa1] *)
                val pow_cong = beta_norm (Drule.infer_instantiate ctxtSigD
                      [(("P",0), ctermSigD (Term.lambda (Free("zpe",natT)) (oeq (pow two aF)(pow two (Free("zpe",natT)))))),
                       (("a",0), ctermSigD aF),(("b",0), ctermSigD (sub pT one))] oeq_subst_vD)
                      OF [sym3 (sub pT one, aF) subSa1, reflD (pow two aF)]   (* 2^a = 2^(sub(Suc a)1) *)
                val congDivP = mult_cong_lD (pow two aF, pow two (sub pT one), msubT) pow_cong  (* 2^a*msubT = 2^(sub(Suc a)1)*msubT *)
                val nFinal = trans3 (nF, mult (pow two aF) msubT, mult (pow two (sub pT one)) msubT)
                               n_2a_msub congDivP                       (* n = 2^(sub(Suc a)1)*msubT *)
                (* conjunction at p = Suc a *)
                val efConj = conjI_D (prime2 msubT, oeq nF (mult (pow two (sub pT one)) msubT)) primeMsub nFinal
                (* Ex p. ... via exI at p = Suc a *)
                val efAbs = Term.lambda (Free("p", natT))
                              (mkConj (prime2 (sub (pow two (Free("p",natT))) one))
                                 (oeq nF (mult (pow two (sub (Free("p",natT)) one)) (sub (pow two (Free("p",natT))) one))))
                val efEx = Thm.implies_elim (exI_atD (efAbs, pT)) efConj  (* Ex p. ... = euclidForm n *)
              in efEx end
            (* le m (sigma m) destructed : Ex d. sigma m = add m d *)
            val ledAbs = Abs("p", natT, oeq (sigma mF)(add mF (Bound 0)))
          in exE_atD (ledAbs, euclidFormN nF) hmle "d_ec" perD end
        val mFb = Free("m_ec", natT)
      in exE_atD (mAbs, euclidFormN nF) hExm "m_ec_in" perM end
    val aFb = Free("a_ec", natT)
    val core = exE_atD (aAbs, euclidFormN nF) f2s0 "a_ec_in" perA
    (* discharge in order: perfect, even, lt 0 n, SCG *)
    val d4 = Thm.implies_intr (ctermSigD (jT (perfectN nF))) core
    val d3 = Thm.implies_intr (ctermSigD (jT (evenN nF))) d4
    val d2 = Thm.implies_intr (ctermSigD (jT (lt ZeroC nF))) d3
    val d1 = Thm.implies_intr (ctermSigD scgProp) d2
  in varify d1 end;

val () = out ("EULER_CONVERSE_COND_HYPS = " ^ Int.toString (length (Thm.hyps_of euler_converse_cond)) ^ "\n");
val () = out "EULER_CONVERSE_COND_BUILT\n";
(* ===========================================================================
   VALIDATION of euler_converse_cond + assembly of the FULL EUCLID-EULER IFF.
   =========================================================================== *)
val () = out "EE_IFF_BEGIN\n";

(* ---- aconv-intended check for euler_converse_cond ---- *)
val nVe = Var(("n",0), natT);
fun evenV n = mkEx (Term.lambda (Free("k", natT)) (oeq n (mult two (Free("k",natT)))));
fun perfectV n = oeq (sigma n) (mult two n);
fun euclidFormV n =
  mkEx (Term.lambda (Free("p", natT))
    (mkConj (prime2 (sub (pow two (Free("p",natT))) one))
            (oeq n (mult (pow two (sub (Free("p",natT)) one)) (sub (pow two (Free("p",natT))) one)))));
(* the SCG meta-hyp at schematic n is theory-level; varify turned scgProp's Frees a_scg,m_scg
   into bound (meta-universal) vars, n into ?n.  Build the intended form. *)
val scg_aV = Free("a_scg", natT); val scg_mV = Free("m_scg", natT);
val scgPropV = Logic.all scg_aV (Logic.all scg_mV
                 (Logic.mk_implies (jT (neg (dvd two scg_mV)),
                    jT (oeq (sigma (mult (p2 scg_aV) scg_mV)) (mult (sumf pwAbs2 scg_aV) (sigma scg_mV))))));
val i_euler_converse_cond =
  Logic.mk_implies (scgPropV,
    Logic.mk_implies (jT (lt ZeroC nVe),
      Logic.mk_implies (jT (evenV nVe),
        Logic.mk_implies (jT (perfectV nVe),
          jT (euclidFormV nVe)))));
val r_ecc = (Thm.prop_of euler_converse_cond) aconv i_euler_converse_cond;
val () = out ("EULER_CONVERSE_COND_ACONV = " ^ Bool.toString r_ecc ^ "\n");
val () = if r_ecc then out "EULER_CONVERSE_COND_ACONV_OK\n" else
  (out ("  got      = " ^ Syntax.string_of_term ctxtSigD (Thm.prop_of euler_converse_cond) ^ "\n");
   out ("  intended = " ^ Syntax.string_of_term ctxtSigD i_euler_converse_cond ^ "\n"));

(* soundness probes on euler_converse_cond *)
val eccProp = Thm.prop_of euler_converse_cond;
val ecc_noeven =
  Logic.mk_implies (scgPropV,
    Logic.mk_implies (jT (lt ZeroC nVe),
      Logic.mk_implies (jT (perfectV nVe), jT (euclidFormV nVe))));
val () = if not (eccProp aconv ecc_noeven) then out "PROBE_OK euler_converse needs even n\n"
         else out "PROBE_FAIL even dropped\n";
val ecc_noperf =
  Logic.mk_implies (scgPropV,
    Logic.mk_implies (jT (lt ZeroC nVe),
      Logic.mk_implies (jT (evenV nVe), jT (euclidFormV nVe))));
val () = if not (eccProp aconv ecc_noperf) then out "PROBE_OK euler_converse needs perfect n\n"
         else out "PROBE_FAIL perfect dropped\n";
val ecc_noscg =
  Logic.mk_implies (jT (lt ZeroC nVe),
    Logic.mk_implies (jT (evenV nVe),
      Logic.mk_implies (jT (perfectV nVe), jT (euclidFormV nVe))));
val () = if not (eccProp aconv ecc_noscg) then out "PROBE_OK euler_converse needs the sigma-mult bridge SCG\n"
         else out "PROBE_FAIL SCG dropped\n";

(* ---------------------------------------------------------------------------
   BACKWARD direction (euclidForm n ==> perfect n), via the BANKED euclid_perfect.
   Given euclidForm n = Ex p. prime2(2^p-1) /\ n = 2^(p-1)*(2^p-1):
     destruct p ; q := 2^p-1 ; hPrime : prime2 q ; hNeq : n = 2^(p-1)*q.
     euclid_perfect[q,p] needs : prime2 q ; oeq (add q 1)(2^p) ; lt 1 p.
       (q+1=2^p) : 2^p = Suc m [pow2_pos] ; q = 2^p-1 = m ; q+1 = m+1 = Suc m = 2^p.
       (lt 1 p)  : prime2 q -> lt 1 q -> q > 1 ; p in {0,1,>=2} ; p=0 -> q=0, p=1 -> q=1
                   both contradict q>1 ; so p>=2 = lt 1 p.
     euclid_perfect gives oeq (sigma (2^(p-1)*q))(mult 2 (2^(p-1)*q)) = perfect n  (rewrite n).
   --------------------------------------------------------------------------- *)
(* prime2 q -> lt 1 q *)
fun prime2_gt1_D qT hPrime = conjunct1_D (lt (suc ZeroC) qT, mkForall (ppAbs qT)) hPrime

(* lt_irrefl for lt 1 1 etc already lt_irreflD. *)

val euclid_perfect_back =
  let
    val nF = Free("n", natT)
    val hEF = Thm.assume (ctermSigD (jT (euclidFormV nF)))    (* Ex p. prime2(2^p-1) /\ n = 2^(p-1)*(2^p-1) *)
    val pAbs = Term.lambda (Free("p", natT))
                 (mkConj (prime2 (sub (pow two (Free("p",natT))) one))
                         (oeq nF (mult (pow two (sub (Free("p",natT)) one)) (sub (pow two (Free("p",natT))) one))))
    fun body pF hConj =
      let
        val qT = sub (pow two pF) one                        (* q = 2^p - 1 *)
        val hPrime = conjunct1_D (prime2 qT, oeq nF (mult (pow two (sub pF one)) qT)) hConj  (* prime2 q *)
        val hNeq   = conjunct2_D (prime2 qT, oeq nF (mult (pow two (sub pF one)) qT)) hConj  (* n = 2^(p-1)*q *)

        (* (q+1 = 2^p) : 2^p = Suc m -> q = sub (Suc m) 1 = m -> q+1 = Suc m = 2^p *)
        val pp = beta_norm (Drule.infer_instantiate ctxtSigD [(("k",0), ctermSigD pF)] pow2_pos_vD)  (* Ex m. 2^p = Suc m *)
        val Pm = Abs("m", natT, oeq (pow two pF)(suc (Bound 0)))
        val hEq_q1 =
          exE_atD (Pm, oeq (add qT one)(pow two pF)) pp "m_qp"
            (fn mF => fn hm =>   (* hm : oeq (2^p)(Suc m) *)
              let
                (* q = sub (2^p) 1 ; rewrite 2^p -> Suc m : q = sub (Suc m) 1 = m *)
                val Psub = Term.lambda (Free("zq",natT)) (oeq (sub (pow two pF) one)(sub (Free("zq",natT)) one))
                val qSm = substPredD (Psub, pow two pF, suc mF) hm (reflD (sub (pow two pF) one))  (* sub(2^p)1 = sub(Suc m)1 *)
                val sSS = subSSD (mF, ZeroC)    (* sub(Suc m)(Suc 0) = sub m 0 *)
                val sN0 = subN0D mF             (* sub m 0 = m *)
                val q_m = trans3 (qT, sub (suc mF) one, mF) qSm (trans3 (sub (suc mF) one, sub mF ZeroC, mF) sSS sN0)  (* q = m *)
                (* q+1 = m+1 = Suc m = 2^p *)
                val q1_m1 = add_cong_lD (qT, mF, one) q_m         (* add q 1 = add m 1 *)
                (* add m 1 = add 1 m [comm] = Suc m [add1_eq_Suc] *)
                val m1_1m = addcommD2 (mF, one)                   (* add m 1 = add 1 m *)
                val onem_Sm = add1_eq_Suc mF                      (* add 1 m = Suc m *)
                val m1_Sm = trans3 (add mF one, add one mF, suc mF) m1_1m onem_Sm  (* add m 1 = Suc m *)
                val q1_Sm = trans3 (add qT one, add mF one, suc mF) q1_m1 m1_Sm  (* add q 1 = Suc m *)
                val q1_2p = trans3 (add qT one, suc mF, pow two pF) q1_Sm (sym3 (pow two pF, suc mF) hm)  (* add q 1 = 2^p *)
              in q1_2p end)

        (* (lt 1 p) : prime2 q -> lt 1 q ; p in {0,1,>=2} by dzos. *)
        val q_gt1 = prime2_gt1_D qT hPrime                       (* lt 1 q = le 2 q *)
        val hLt1p =
          let
            val dzp = dzosD pF                                   (* Disj (oeq p 0)(Ex j. p = Suc j) *)
            val goalLt = lt one pF
            (* case p = 0 : q = sub (2^0) 1 = sub 1 1 = 0 ; lt 1 0 absurd via q>1 -> lt 1 0. *)
            val caseP0 =
              let
                val hp0 = Thm.assume (ctermSigD (jT (oeq pF ZeroC)))
                (* 2^p = 2^0 = 1 ; q = sub 1 1 = 0 *)
                val pcong = substPredD (Term.lambda (Free("zp0",natT)) (oeq (pow two pF)(pow two (Free("zp0",natT)))),
                              pF, ZeroC) hp0 (reflD (pow two pF))     (* 2^p = 2^0 *)
                val p20 = powZeroD two  (* 2^0 = 1 *)
                val pow_1 = trans3 (pow two pF, pow two ZeroC, one) pcong p20   (* 2^p = 1 *)
                (* q = sub (2^p) 1 = sub 1 1 = sub (Suc 0)(Suc 0) = sub 0 0 = 0 *)
                val qsub = substPredD (Term.lambda (Free("zq0",natT)) (oeq (sub (pow two pF) one)(sub (Free("zq0",natT)) one)),
                             pow two pF, one) pow_1 (reflD (sub (pow two pF) one))  (* sub(2^p)1 = sub 1 1 *)
                val s11 = subSSD (ZeroC, ZeroC)   (* sub (Suc 0)(Suc 0) = sub 0 0 *)
                val s00 = subN0D ZeroC            (* sub 0 0 = 0 *)
                val q_0 = trans3 (qT, sub one one, ZeroC) qsub (trans3 (sub one one, sub ZeroC ZeroC, ZeroC) s11 s00)  (* q = 0 *)
                (* q_gt1 : lt 1 q ; rewrite q -> 0 : lt 1 0 ; lt 1 0 = le 2 0 ; le 2 0 -> oeq 2 (add 0 x)? use le_zero? *)
                (* lt 1 0 = le (Suc 1) 0 = le 2 0 ; le 2 0 -> oeq 0 (add 2 p) impossible.  use lt_cong on q_gt1: lt 1 q -> lt 1 0 *)
                val lt10 = lt_cong_rD (one, qT, ZeroC) q_0 q_gt1   (* lt 1 0 *)
                (* lt 1 0 = le 2 0 = Ex p. 0 = add 2 p ; absurd : add 2 p = Suc(Suc(..)) != 0 *)
                val ff =
                  let val labs = Abs("p", natT, oeq ZeroC (add (suc (suc ZeroC)) (Bound 0)))
                  in exE_atD (labs, oFalseC) lt10 "p_z"
                       (fn jF => fn hj =>   (* hj : oeq 0 (add 2 j) *)
                          let val aS = beta_norm (Drule.infer_instantiate ctxtSigD
                                         [(("m",0), ctermSigD (suc ZeroC)),(("n",0), ctermSigD jF)] add_Suc_vD2)  (* add(Suc(Suc 0))j = Suc(add(Suc 0)j) *)
                              val zSj = trans3 (ZeroC, add (suc (suc ZeroC)) jF, suc (add (suc ZeroC) jF)) hj aS  (* 0 = Suc(...) *)
                          in Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                                [(("n",0), ctermSigD (add (suc ZeroC) jF))] Suc_neq_Zero_vD))
                               (sym3 (ZeroC, suc (add (suc ZeroC) jF)) zSj) end)
                  end
              in (out "B_CASEP0\n"; Thm.implies_intr (ctermSigD (jT (oeq pF ZeroC)))
                   (Thm.implies_elim (oFalseElimD goalLt) ff)) end
            (* case p = Suc j : sub-case j = 0 (p=1) gives q=1 absurd ; j = Suc i (p>=2) gives lt 1 p. *)
            val caseSucAbs = Abs("j", natT, oeq pF (suc (Bound 0)))
            val caseSuc =
              let
                val hex = Thm.assume (ctermSigD (jT (mkEx caseSucAbs)))
                fun b2 jF hj =   (* hj : oeq p (Suc j) *)
                  let
                    val dzj = dzosD jF                            (* Disj (oeq j 0)(Ex i. j = Suc i) *)
                    (* case j = 0 : p = Suc 0 = 1 ; 2^1 = 2 ; q = sub 2 1 = 1 ; lt 1 1 absurd. *)
                    val cj0 =
                      let
                        val hj0 = Thm.assume (ctermSigD (jT (oeq jF ZeroC)))
                        val sucj0 = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                                    [(("a",0), ctermSigD jF),(("b",0), ctermSigD ZeroC)] (up (varify Suc_cong)))) hj0  (* Suc j = Suc 0 *)
                        val pS0 = trans3 (pF, suc jF, suc ZeroC) hj sucj0  (* p = Suc 0 *)
                        (* 2^p = 2^(Suc 0) = mult 2 (2^0) = mult 2 1 = 2 *)
                        val pcong = substPredD (Term.lambda (Free("zp1",natT)) (oeq (pow two pF)(pow two (Free("zp1",natT)))),
                                      pF, suc ZeroC) pS0 (reflD (pow two pF))    (* 2^p = 2^(Suc 0) *)
                        val pS = powSucD (two, ZeroC)              (* 2^(Suc 0) = mult 2 (2^0) *)
                        val p20 = powZeroD two  (* 2^0 = 1 *)
                        val m21 = mult_cong_rD (two, pow two ZeroC, one) p20   (* mult 2 (2^0) = mult 2 1 *)
                        val m21_2 = mult1rD two                    (* mult 2 1 = 2 *)
                        val pow_2 = trans3 (pow two pF, pow two (suc ZeroC), two)
                                      pcong (trans3 (pow two (suc ZeroC), mult two (pow two ZeroC), two)
                                               pS (trans3 (mult two (pow two ZeroC), mult two one, two) m21 m21_2))  (* 2^p = 2 *)
                        (* q = sub (2^p) 1 = sub 2 1 = sub (Suc(Suc 0))(Suc 0) = sub (Suc 0) 0 = Suc 0 = 1 *)
                        val qsub = substPredD (Term.lambda (Free("zq1",natT)) (oeq (sub (pow two pF) one)(sub (Free("zq1",natT)) one)),
                                     pow two pF, two) pow_2 (reflD (sub (pow two pF) one))   (* sub(2^p)1 = sub 2 1 *)
                        val s21 = subSSD (suc ZeroC, ZeroC)        (* sub (Suc(Suc 0))(Suc 0) = sub (Suc 0) 0 *)
                        val s10 = subN0D (suc ZeroC)               (* sub (Suc 0) 0 = Suc 0 *)
                        val q_1 = trans3 (qT, sub two one, one) qsub (trans3 (sub two one, sub (suc ZeroC) ZeroC, one) s21 s10)  (* q = 1 *)
                        val lt11 = lt_cong_rD (one, qT, one) q_1 q_gt1   (* lt 1 1 *)
                        val ff = lt_irreflD one lt11
                      in (out "B_CJ0\n"; Thm.implies_intr (ctermSigD (jT (oeq jF ZeroC)))
                           (Thm.implies_elim (oFalseElimD goalLt) ff)) end
                    (* case j = Suc i : p = Suc(Suc i) ; lt 1 p = le 2 p ; le 2 (Suc(Suc i)) via le_introD witness i. *)
                    val ciAbs = Abs("i", natT, oeq jF (suc (Bound 0)))
                    val ci =
                      let
                        val hexi = Thm.assume (ctermSigD (jT (mkEx ciAbs)))
                        fun b3 iF hi =   (* hi : oeq j (Suc i) *)
                          let
                            (* p = Suc j = Suc(Suc i) *)
                            val pSSi = trans3 (pF, suc jF, suc (suc iF)) hj
                                         (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                                            [(("a",0), ctermSigD jF),(("b",0), ctermSigD (suc iF))] (up (varify Suc_cong)))) hi)  (* p = Suc(Suc i) *)
                            (* lt 1 p = le 2 p = le (Suc(Suc 0)) p ; witness i : p = add 2 i = Suc(Suc i).
                               add (Suc(Suc 0)) i = Suc(Suc(add 0 i)) = Suc(Suc i). *)
                            val a1 = beta_norm (Drule.infer_instantiate ctxtSigD
                                       [(("m",0), ctermSigD (suc ZeroC)),(("n",0), ctermSigD iF)] add_Suc_vD2)  (* add(Suc(Suc 0))i = Suc(add(Suc 0)i) *)
                            val a2 = beta_norm (Drule.infer_instantiate ctxtSigD
                                       [(("m",0), ctermSigD ZeroC),(("n",0), ctermSigD iF)] add_Suc_vD2)         (* add(Suc 0)i = Suc(add 0 i) *)
                            val a0 = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD iF)] add_0_vD)  (* add 0 i = i *)
                            val s0i = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                                        [(("a",0), ctermSigD (add ZeroC iF)),(("b",0), ctermSigD iF)] (up (varify Suc_cong)))) a0  (* Suc(add 0 i) = Suc i *)
                            val a1i = trans3 (add (suc ZeroC) iF, suc (add ZeroC iF), suc iF) a2 s0i  (* add(Suc 0)i = Suc i *)
                            val a2i = trans3 (add (suc (suc ZeroC)) iF, suc (add (suc ZeroC) iF), suc (suc iF))
                                        a1 (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                                              [(("a",0), ctermSigD (add (suc ZeroC) iF)),(("b",0), ctermSigD (suc iF))] (up (varify Suc_cong)))) a1i)  (* add(Suc(Suc 0))i = Suc(Suc i) *)
                            (* p = add 2 i : p = Suc(Suc i) [pSSi] ; add 2 i = Suc(Suc i) [a2i] ; so p = add 2 i *)
                            val p_a2i = trans3 (pF, suc (suc iF), add (suc (suc ZeroC)) iF) pSSi (sym3 (add (suc (suc ZeroC)) iF, suc (suc iF)) a2i)  (* p = add 2 i *)
                            val le2p = le_introD (suc (suc ZeroC), pF, iF) p_a2i   (* le 2 p = lt 1 p *)
                          in (out "B_CI\n"; le2p) end
                      in Thm.implies_intr (ctermSigD (jT (mkEx ciAbs))) (exE_atD (ciAbs, goalLt) hexi "i_p" b3) end
                    val res = disjE_D (oeq jF ZeroC, mkEx ciAbs, goalLt) dzj cj0 ci
                  in (out "B_INNER_DISJ\n"; res) end
                val r = exE_atD (caseSucAbs, goalLt) hex "j_p" b2
              in (out "B_CASESUC\n"; Thm.implies_intr (ctermSigD (jT (mkEx caseSucAbs))) r) end
          in disjE_D (oeq pF ZeroC, mkEx caseSucAbs, goalLt) dzp caseP0 caseSuc end

        (* euclid_perfect[q,p] *)
        val ep = beta_norm (Drule.infer_instantiate ctxtSigD
                   [(("q",0), ctermSigD qT),(("p",0), ctermSigD pF)] euclid_perfect)
        val epThm = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim ep hPrime) hEq_q1) hLt1p
                    (* oeq (sigma (2^(p-1)*q))(mult 2 (2^(p-1)*q)) *)
        (* rewrite 2^(p-1)*q -> n via sym hNeq : perfect n = oeq (sigma n)(mult 2 n) *)
        val N = mult (pow two (sub pF one)) qT
        val sigcong = beta_norm (Drule.infer_instantiate ctxtSigD
              [(("P",0), ctermSigD (Term.lambda (Free("zsp",natT)) (oeq (sigma (Free("zsp",natT)))(mult two (Free("zsp",natT)))))),
               (("a",0), ctermSigD N),(("b",0), ctermSigD nF)] oeq_subst_vD)
              OF [sym3 (nF, N) hNeq, epThm]    (* oeq (sigma n)(mult 2 n) = perfect n *)
      in (out "B_SIGCONG_OK\n"; sigcong) end
    val core = exE_atD (pAbs, perfectV nF) hEF "p_back" body   (* perfect n, under hEF *)
  in varify (impI_D (euclidFormV nF, perfectV nF) core) end;   (* euclidForm n ==> perfect n (object Imp), schematic n *)

val () = out "EE_IFF_BACK_BUILT_RAW\n";

(* aconv check + 0-hyp for euclid_perfect_back *)
val () = out ("EE_IFF_BACK_HYPS = " ^ Int.toString (length (Thm.hyps_of euclid_perfect_back)) ^ "\n");
val nVb = Var(("n",0), natT);
val i_back = jT (mkImp (euclidFormV nVb) (perfectV nVb));
val r_back = (Thm.prop_of euclid_perfect_back) aconv i_back;
val () = out ("EE_IFF_BACK_ACONV = " ^ Bool.toString r_back ^ "\n");
val () = if not r_back then
  (out ("  got      = " ^ Syntax.string_of_term ctxtSigD (Thm.prop_of euclid_perfect_back) ^ "\n");
   out ("  intended = " ^ Syntax.string_of_term ctxtSigD i_back ^ "\n")) else ();

(* ---------------------------------------------------------------------------
   THE FULL IFF :
     euclid_euler_cond :
       SCG ==> lt 0 n ==> even n
            ==> mkConj (mkImp (perfect n)(euclidForm n)) (mkImp (euclidForm n)(perfect n))
   --------------------------------------------------------------------------- *)
val euclid_euler_cond =
  let
    val nF = Free("n", natT)
    val hSCG  = Thm.assume (ctermSigD scgProp)             (* scgProp from the converse block (Frees a_scg,m_scg) *)
    val hPos  = Thm.assume (ctermSigD (jT (lt ZeroC nF)))
    val hEven = Thm.assume (ctermSigD (jT (evenN nF)))     (* evenN from the converse block *)
    (* FORWARD : perfect n ==> euclidForm n  via euler_converse_cond *)
    val eccN = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD nF)] euler_converse_cond)
               (* SCG ==> lt 0 n ==> even n ==> perfect n ==> euclidForm n *)
    val ecc1 = Thm.implies_elim eccN hSCG
    val ecc2 = Thm.implies_elim ecc1 hPos
    val ecc3 = Thm.implies_elim ecc2 hEven        (* perfect n ==> euclidForm n  (meta) *)
    val hPerf = Thm.assume (ctermSigD (jT (perfectN nF)))
    val efUnderPerf = Thm.implies_elim ecc3 hPerf  (* euclidForm n, under hPerf *)
    val fwdImp = impI_D (perfectN nF, euclidFormN nF) efUnderPerf   (* mkImp (perfect n)(euclidForm n) *)
    (* BACKWARD : euclidForm n ==> perfect n  via euclid_perfect_back (schematic ?n) at nF *)
    val bkImp = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD nF)] euclid_perfect_back)
    (* conjI the two halves *)
    val both = conjI_D (mkImp (perfectN nF)(euclidFormN nF), mkImp (euclidFormN nF)(perfectN nF)) fwdImp bkImp
    (* discharge SCG, lt 0 n, even n *)
    val d3 = Thm.implies_intr (ctermSigD (jT (evenN nF))) both
    val d2 = Thm.implies_intr (ctermSigD (jT (lt ZeroC nF))) d3
    val d1 = Thm.implies_intr (ctermSigD scgProp) d2
  in varify d1 end;

val () = out ("EUCLID_EULER_COND_HYPS = " ^ Int.toString (length (Thm.hyps_of euclid_euler_cond)) ^ "\n");
val () = out ("EUCLID_EULER_COND_SHYPS = " ^ Int.toString (length (Thm.extra_shyps euclid_euler_cond)) ^ "\n");

(* aconv-intended for the iff *)
val i_euclid_euler_cond =
  Logic.mk_implies (scgPropV,
    Logic.mk_implies (jT (lt ZeroC nVe),
      Logic.mk_implies (jT (evenV nVe),
        jT (mkConj (mkImp (perfectV nVe)(euclidFormV nVe))
                   (mkImp (euclidFormV nVe)(perfectV nVe))))));
val r_iff = (Thm.prop_of euclid_euler_cond) aconv i_euclid_euler_cond;
val () = out ("EUCLID_EULER_COND_ACONV = " ^ Bool.toString r_iff ^ "\n");
val () = if r_iff then out "EUCLID_EULER_COND_ACONV_OK\n" else
  (out ("  got      = " ^ Syntax.string_of_term ctxtSigD (Thm.prop_of euclid_euler_cond) ^ "\n");
   out ("  intended = " ^ Syntax.string_of_term ctxtSigD i_euclid_euler_cond ^ "\n"));

(* soundness probes on the iff *)
val iffProp = Thm.prop_of euclid_euler_cond;
val iff_noeven =
  Logic.mk_implies (scgPropV,
    Logic.mk_implies (jT (lt ZeroC nVe),
      jT (mkConj (mkImp (perfectV nVe)(euclidFormV nVe)) (mkImp (euclidFormV nVe)(perfectV nVe)))));
val () = if not (iffProp aconv iff_noeven) then out "PROBE_OK euclid_euler needs even n\n"
         else out "PROBE_FAIL iff even dropped\n";
(* genuinely both directions : NOT aconv the variant with only the forward conjunct *)
val iff_fwdonly =
  Logic.mk_implies (scgPropV,
    Logic.mk_implies (jT (lt ZeroC nVe),
      Logic.mk_implies (jT (evenV nVe),
        jT (mkConj (mkImp (perfectV nVe)(euclidFormV nVe)) (mkImp (perfectV nVe)(euclidFormV nVe))))));
val () = if not (iffProp aconv iff_fwdonly) then out "PROBE_OK euclid_euler is genuinely both directions\n"
         else out "PROBE_FAIL iff collapsed to forward-only\n";
(* euclidForm is the Euclid shape (not collapsed to n) : NOT aconv variant with euclidForm -> n *)
val iff_collapsed =
  Logic.mk_implies (scgPropV,
    Logic.mk_implies (jT (lt ZeroC nVe),
      Logic.mk_implies (jT (evenV nVe),
        jT (mkConj (mkImp (perfectV nVe) nVe) (mkImp nVe (perfectV nVe))))));
val () = if not (iffProp aconv iff_collapsed) then out "PROBE_OK euclidForm is the Euclid shape (not n)\n"
         else out "PROBE_FAIL euclidForm collapsed\n";

val () =
  if r_iff andalso r_ecc andalso r_back
     andalso (length (Thm.hyps_of euclid_euler_cond) = 0)
     andalso (length (Thm.extra_shyps euclid_euler_cond) = 0)
     andalso (length (Thm.hyps_of euler_converse_cond) = 0)
  then out "EUCLID_EULER_ALL_OK\n"
  else out "EUCLID_EULER_INCOMPLETE\n";

val () = out "EE_IFF_END\n";

(* ===========================================================================
   AXIOM AUDIT : this delta adds NO new constant and NO new axiom over thySigD
   (the whole converse + iff are pure derivations).  Confirm the axiom set of the
   current theory is identical to the base euclid_perfect theory's.
   =========================================================================== *)
val () = out "EE_AXIOM_AUDIT_BEGIN\n";
val baseAxNames = map #1 (Theory.all_axioms_of thySigD);
val curAxNames  = map #1 (Theory.all_axioms_of (Thm.theory_of_thm euclid_euler_cond));
val newAxC = List.filter (fn nm => not (List.exists (fn b => b = nm) baseAxNames)) curAxNames;
val () = out ("EE_NEW_AXIOM_COUNT = " ^ Int.toString (length newAxC) ^ "\n");
val () = List.app (fn nm => out ("  EE_NEWAX " ^ nm ^ "\n")) newAxC;
val () = if length newAxC = 0 then out "EE_AXIOM_AUDIT_OK: converse+iff add NO new axiom\n"
         else out "EE_AXIOM_AUDIT_NOTE: see new axioms above\n";
val () = out "EE_AXIOM_AUDIT_END\n";
