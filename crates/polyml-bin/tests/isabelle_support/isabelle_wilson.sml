(* ============================================================================
   WILSON'S THEOREM in Isabelle/Pure on the polyml-rs interpreter.
   (test: isabelle_wilson.rs)
   ----------------------------------------------------------------------------
        wilson : prime p ==> cong p (lprod (upto (p-1))) (p-1)
   i.e.  (p-1)! == p-1 == -1  (mod p)  for every prime p.

   A 0-hypothesis theorem by genuine LCF kernel inference, the classical
   companion to Fermat's little theorem. `prime` here is `prime2`, the GENUINE
   structural prime (1 < p AND for all d, d | p ==> d = 1 \/ d = p), used
   consistently by the whole keystone chain (euclid_lemma, mod_inverse,
   lagrange_roots all take prime2; the legacy `prime`/primePredAbs with its
   de-Bruijn capture bug is dead code, unused downstream). Three soundness probes
   on the result pass: it genuinely needs the prime hypothesis, the residue is
   p-1 (= -1) and NOT 0, and it is NOT the false unconditional `(p-1)! == 1`.

   THE PROOF, assembled from the pieces proved in the prior layers:
     - finv_one / finv_pm1: the endpoints 1 and p-1 are their own inverses
       (sq_pm1: (p-1)^2 == 1, + inverse uniqueness);
     - L2 = [2..p-2] (= the residue range with 1 and p-1 removed) is closed under
       the modular inverse finv (finv x lands in [1..p-1] by finv_mem, and is
       neither 1 nor p-1 by the involution + endpoint facts), fixed-point free
       (finv_neq via lagrange_roots), and an involution (finv_invol);
     - so by the INVOLUTION-PAIRING LEMMA, lprod L2 == 1 (mod p);
     - decompose (p-1)! = (p-1) * 1 * lprod L2 (extract the elements p-1 and 1),
       hence (p-1)! == (p-1) * 1 == p-1 == -1 (mod p).

   Built on the full Wilson development (pairing lemma + modular-inverse function
   + residue range + keystones) via common::with_wilson_inverse. Proved by a
   3-seat ultracode assembly fleet (wf_39658abf-b42), the capstone of a multi-run
   campaign; re-verified end-to-end by hand. The same pairing_lemma + finv
   machinery reaches EULER'S THEOREM next (product over the reduced residues).
   ============================================================================ *)

(* ============================================================================
   WILSON'S THEOREM (seat wa0) -- STEP 1 first: endpoint inverse facts.
   On ctxtW.  prime2 is THE structural prime (prime = phase-1 captured/buggy).
   ============================================================================ *)
val () = out "WA_STEP0_BEGIN\n";

val oneN = suc ZeroC;
val twoN = suc oneN;

(* ---- extra combinators on ctxtW ---- *)
fun allI_W Pabs hAll = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("P",0), ctermW Pabs)] allI_vW)) hAll;
fun multSuc_W (mt,nt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt)] mult_Suc_vW);
fun multSucr_W (nt,mt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("n",0), ctermW nt),(("m",0), ctermW mt)] mult_Suc_right_vW);
fun mult1l_W' t = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] mult_1_left_vW);
fun mult1r_W' t = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] mult_1_right_vW);

(* ---- varify list lemmas onto ctxtW ---- *)
val extract_vW       = varify extract;
val nodup_remove_vW  = varify nodup_remove;
val mem_remove_fwd_vW= varify mem_remove_fwd;
val mem_remove_bwd_vW= varify mem_remove_bwd;
val llen_remove_vW   = varify llen_remove;
val lprod_nil_vW2    = varify lprod_nil_ax;
val lprod_cons_vW2   = varify lprod_cons_ax;
val lremove_nil_vW2  = varify lremove_nil_ax;
val lremove_cons_eq_vW2  = varify lremove_cons_eq_ax;
val lremove_cons_neq_vW2 = varify lremove_cons_neq_ax;
val pairing_lemma_vW = varify pairing_lemma;

fun extract_W (xt,Lt) hmem = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("x",0), ctermW xt),(("L",0), ctermW Lt)] extract_vW)) hmem;
fun nodup_remove_W (xt,Lt) hnd = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("x",0), ctermW xt),(("L",0), ctermW Lt)] nodup_remove_vW)) hnd;
fun lprodCons_W (ht,tt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("x",0), ctermW ht),(("t",0), ctermW tt)] lprod_cons_vW2);
fun lremoveConsNeq_W (xt,yt,tt) hneq = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("x",0), ctermW xt),(("y",0), ctermW yt),(("t",0), ctermW tt)] lremove_cons_neq_vW2)) hneq;
(* lprod-cong via leq_subst *)
fun lprod_cong_W (aT,bT) hab =
  let val Pabs = Abs("z", natlistT, oeq (lprod aT) (lprod (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtW
            [(("P",0), ctermW Pabs),(("a",0), ctermW aT),(("b",0), ctermW bT)] leq_subst_vW)
      val refl0 = oeqRefl_W (lprod aT)
  in inst OF [hab, refl0] end;

val () = out "WA_STEP0_COMBINATORS_OK\n";

(* lnodup_upto_W : lnodup (uptoF n) *)
fun lnodup_upto_W nt = beta_norm (Drule.infer_instantiate ctxtW [(("k_nd",0), ctermW nt)] lnodup_upto_vW);

(* ============================================================================
   ARITH : sq_identity (schematic in r) :
     oeq (mult (Suc r)(Suc r)) (add 1 (mult (Suc(Suc r)) r))
   both sides reduce to Suc (add r (add r (mult r r))).
   ============================================================================ *)
val sq_identity =
  let
    val rF = Free("r", natT)
    val sr = suc rF; val ssr = suc sr
    val l1 = multSuc_W (rF, sr)
    val l2 = multSucr_W (rF, rF)
    val l2c = add_cong_r_W (sr, mult rF sr, add rF (mult rF rF)) l2
    val lhs = oeq_trans_vW OF [l1, l2c]
    val Xt = add rF (mult rF rF)
    val lhsS = addSuc_W (rF, Xt)
    val lhs2 = oeq_trans_vW OF [lhs, lhsS]
    val r1 = multSuc_W (sr, rF)
    val r2 = multSuc_W (rF, rF)
    val r2c = add_cong_r_W (rF, mult sr rF, add rF (mult rF rF)) r2
    val rmid = oeq_trans_vW OF [r1, r2c]
    val rcong = add_cong_r_W (oneN, mult ssr rF, add rF Xt) rmid
    val rS = addSuc_W (ZeroC, add rF Xt)
    val r0 = add0_W (add rF Xt)
    val r0s = Suc_cong_vW OF [r0]
    val rhs1 = oeq_trans_vW OF [rcong, rS]
    val rhs2 = oeq_trans_vW OF [rhs1, r0s]
    val rhs2s = oeq_sym_vW OF [rhs2]
    val res = oeq_trans_vW OF [lhs2, rhs2s]
  in varify res end;
val () = if length (Thm.hyps_of sq_identity) = 0 then out "OK sq_identity\n" else out "FAIL sq_identity\n";
fun sq_identity_W rt = beta_norm (Drule.infer_instantiate ctxtW [(("r",0), ctermW rt)] sq_identity);

val () = out "WA_STEP1_ARITH_OK\n";
(* ============================================================================
   STEP 1b : range-membership helpers + sub_p1_pos / pred2
   ============================================================================ *)
val () = out "WA_STEP1B_BEGIN\n";

(* sub_p1_pos : lt 1 p ==> lt 0 (sub p 1)   (i.e. le 1 (sub p 1)) *)
val sub_p1_pos =
  let
    val pF = Free("p", natT)
    val hp1P = jT (lt oneN pF); val hp1 = Thm.assume (ctermW hp1P)
    val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pF)] pos_pred)) hp1
    val goalC = lt ZeroC (sub pF oneN)
    fun body q (hq:thm) =
      let
        val ssq_inst = beta_norm (Drule.infer_instantiate ctxtW [(("q",0), ctermW q)] (varify sub_suc_one))
        val hq_s = oeq_sym_vW OF [hq]
        val Psub = Term.lambda (Free("z_sb",natT)) (oeq (sub (Free("z_sb",natT)) oneN) q)
        val subPq = oeq_rw_W (Psub, suc q, pF) hq_s ssq_inst
        val Plt1 = Term.lambda (Free("z_l1",natT)) (lt oneN (Free("z_l1",natT)))
        val lt1Sq = oeq_rw_W (Plt1, pF, suc q) hq hp1
        val Pd = Abs("d", natT, oeq (suc q) (add twoN (Bound 0)))
        fun body2 d (hd:thm) =
          let
            val aS = addSuc_W (oneN, d)
            val Sq_S = oeq_trans_vW OF [hd, aS]
            val q_1d = Suc_inj_W (q, add oneN d) Sq_S
            val Pe = Abs("e", natT, oeq q (add oneN (Bound 0)))
            val ex = exI_W Pe d q_1d
          in ex end
        val lt0q = exE_W (Pd, lt ZeroC q) lt1Sq "d_sp" body2
        val subPq_s = oeq_sym_vW OF [subPq]
        val Plt0 = Term.lambda (Free("z_l0",natT)) (lt ZeroC (Free("z_l0",natT)))
        val res = oeq_rw_W (Plt0, q, sub pF oneN) subPq_s lt0q
      in res end
    val res = exE_W (Abs("q", natT, oeq pF (suc (Bound 0))), goalC) predEx "q_sp" body
  in varify (Thm.implies_intr (ctermW hp1P) res) end;
val () = if length (Thm.hyps_of sub_p1_pos) = 0 then out "OK sub_p1_pos\n" else out "FAIL sub_p1_pos\n";
fun sub_p1_pos_W pt hp1 = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt)] sub_p1_pos)) hp1;

(* lmem_one_rng : lt 1 p ==> lmem 1 (uptoF (sub p 1)) *)
fun lmem_one_rng_W pt hp1 =
  let val lt01 = le_refl_W oneN
      val ltpos = sub_p1_pos_W pt hp1
      val cj = conjI_W (lt ZeroC oneN, le oneN (sub pt oneN)) lt01 ltpos
  in lmem_upto_bwd_W (oneN, sub pt oneN) cj end;

(* lmem_pm1_rng : lt 1 p ==> lmem (sub p 1) (uptoF (sub p 1)) *)
fun lmem_pm1_rng_W pt hp1 =
  let val ltpos = sub_p1_pos_W pt hp1
      val leRefl = le_refl_W (sub pt oneN)
      val cj = conjI_W (lt ZeroC (sub pt oneN), le (sub pt oneN)(sub pt oneN)) ltpos leRefl
  in lmem_upto_bwd_W (sub pt oneN, sub pt oneN) cj end;

val () = out "WA_STEP1B_RANGE_OK\n";

(* pred2 : lt 1 p ==> Ex r. Conj (oeq p (Suc(Suc r))) (Conj (oeq (sub p 1)(Suc r)) (oeq (sub p 2) r)) *)
fun mkConj3 a b c = mkConj a (mkConj b c);
val pred2 =
  let
    val pF = Free("p", natT)
    val hp1P = jT (lt oneN pF); val hp1 = Thm.assume (ctermW hp1P)
    val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pF)] pos_pred)) hp1
    val goalC = mkEx (Term.lambda (Free("r_g",natT))
                  (mkConj3 (oeq pF (suc (suc (Free("r_g",natT)))))
                           (oeq (sub pF oneN) (suc (Free("r_g",natT))))
                           (oeq (sub pF twoN) (Free("r_g",natT)))))
    fun body q (hq:thm) =
      let
        val Plt1 = Term.lambda (Free("z_l1b",natT)) (lt oneN (Free("z_l1b",natT)))
        val lt1Sq = oeq_rw_W (Plt1, pF, suc q) hq hp1
        val Pd = Abs("d", natT, oeq (suc q) (add twoN (Bound 0)))
        fun body2 d (hd:thm) =
          let
            val aS = addSuc_W (oneN, d)
            val Sq_S = oeq_trans_vW OF [hd, aS]
            val q_1d = Suc_inj_W (q, add oneN d) Sq_S
            val a1d = addSuc_W (ZeroC, d)
            val a0d = add0_W d
            val a0ds= Suc_cong_vW OF [a0d]
            val q_Sd = oeq_trans_vW OF [oeq_trans_vW OF [q_1d, a1d], a0ds]
            val Sq_SSd = Suc_cong_vW OF [q_Sd]
            val p_SSd = oeq_trans_vW OF [hq, Sq_SSd]
            val sso1 = beta_norm (Drule.infer_instantiate ctxtW [(("q",0), ctermW (suc d))] (varify sub_suc_one))
            val p_SSd_s = oeq_sym_vW OF [p_SSd]
            val Psub1 = Term.lambda (Free("z_s1b",natT)) (oeq (sub (Free("z_s1b",natT)) oneN) (suc d))
            val subp1_Sd = oeq_rw_W (Psub1, suc(suc d), pF) p_SSd_s sso1
            val e1 = subSS_W (suc d, suc ZeroC)
            val e2 = subSS_W (d, ZeroC)
            val e3 = sub0_W d
            val subSSd_d = oeq_trans_vW OF [oeq_trans_vW OF [e1, e2], e3]
            val Psub2 = Term.lambda (Free("z_s2b",natT)) (oeq (sub (Free("z_s2b",natT)) twoN) d)
            val subp2_d = oeq_rw_W (Psub2, suc(suc d), pF) p_SSd_s subSSd_d
            val cj = conjI_W (oeq pF (suc(suc d)), mkConj (oeq (sub pF oneN)(suc d)) (oeq (sub pF twoN) d))
                       p_SSd (conjI_W (oeq (sub pF oneN)(suc d), oeq (sub pF twoN) d) subp1_Sd subp2_d)
            val Pex = Term.lambda (Free("r_g",natT))
                  (mkConj3 (oeq pF (suc (suc (Free("r_g",natT)))))
                           (oeq (sub pF oneN) (suc (Free("r_g",natT))))
                           (oeq (sub pF twoN) (Free("r_g",natT))))
          in exI_W Pex d cj end
        val res = exE_W (Pd, goalC) lt1Sq "d_p2" body2
      in res end
    val res = exE_W (Abs("q", natT, oeq pF (suc (Bound 0))), goalC) predEx "q_p2" body
  in varify (Thm.implies_intr (ctermW hp1P) res) end;
val () = if length (Thm.hyps_of pred2) = 0 then out "OK pred2\n" else out "FAIL pred2\n";

val () = out "WA_STEP1B_PRED2_OK\n";
(* ============================================================================
   STEP 1c : finv_one and finv_pm1
   ============================================================================ *)
val () = out "WA_STEP1C_BEGIN\n";

(* finv_one : prime2 p ==> oeq (finv p 1) 1 *)
val finv_one =
  let
    val pF = Free("p", natT)
    val hPrimeP = jT (prime2 pF); val hPrime = Thm.assume (ctermW hPrimeP)
    val hp1 = prime2_gt1_W pF hPrime
    val mem1 = lmem_one_rng_W pF hp1
    val cong_1fi = finv_inv_W (pF, oneN) hPrime mem1
    val m1l = mult1l_W (finv pF oneN)
    val Pc = Term.lambda (Free("z_o1",natT)) (cong pF (Free("z_o1",natT)) oneN)
    val cong_fi_1 = oeq_rw_W (Pc, mult oneN (finv pF oneN), finv pF oneN) m1l cong_1fi
    val memFi = finv_mem_W (pF, oneN) hPrime mem1
    val lt_fi = lmem_range_lt_W (pF, finv pF oneN) hp1 memFi
    val res = cong_range_unique_W (pF, finv pF oneN, oneN) hp1 lt_fi hp1 cong_fi_1
  in varify (Thm.implies_intr (ctermW hPrimeP) res) end;
val () = if length (Thm.hyps_of finv_one) = 0 then out "OK finv_one\n" else out "FAIL finv_one\n";
fun finv_one_W pt hPrime = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt)] finv_one)) hPrime;

(* sq_pm1_cong : prime2 p ==> cong p (mult (sub p 1)(sub p 1)) 1 *)
val sq_pm1_cong =
  let
    val pF = Free("p", natT)
    val hPrimeP = jT (prime2 pF); val hPrime = Thm.assume (ctermW hPrimeP)
    val hp1 = prime2_gt1_W pF hPrime
    val pm1 = sub pF oneN; val pm2 = sub pF twoN
    val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pF)] pred2)) hp1
    val goalC = cong pF (mult pm1 pm1) oneN
    val Pex = Term.lambda (Free("r_g",natT))
                  (mkConj3 (oeq pF (suc (suc (Free("r_g",natT)))))
                           (oeq (sub pF oneN) (suc (Free("r_g",natT))))
                           (oeq (sub pF twoN) (Free("r_g",natT))))
    fun body r (hc:thm) =
      let
        val hp_SSr  = conjunct1_W (oeq pF (suc(suc r)), mkConj (oeq pm1 (suc r))(oeq pm2 r)) hc
        val hrest   = conjunct2_W (oeq pF (suc(suc r)), mkConj (oeq pm1 (suc r))(oeq pm2 r)) hc
        val hpm1_Sr = conjunct1_W (oeq pm1 (suc r), oeq pm2 r) hrest
        val hpm2_r  = conjunct2_W (oeq pm1 (suc r), oeq pm2 r) hrest
        val si = sq_identity_W r
        val hpm1_Sr_s = oeq_sym_vW OF [hpm1_Sr]
        val hp_SSr_s  = oeq_sym_vW OF [hp_SSr]
        val hpm2_r_s  = oeq_sym_vW OF [hpm2_r]
        val a1 = mult_cong_l_W (suc r, pm1, suc r) hpm1_Sr_s
        val a2 = mult_cong_r_W (pm1, suc r, pm1) hpm1_Sr_s
        val lhsEq = oeq_trans_vW OF [a1, a2]
        val b1 = mult_cong_l_W (suc(suc r), pF, r) hp_SSr_s
        val b2 = mult_cong_r_W (pF, r, pm2) hpm2_r_s
        val bmid = oeq_trans_vW OF [b1, b2]
        val bb = add_cong_r_W (oneN, mult (suc(suc r)) r, mult pF pm2) bmid
        val lhsEq_s = oeq_sym_vW OF [lhsEq]
        val chain = oeq_trans_vW OF [oeq_trans_vW OF [lhsEq_s, si], bb]
        val congL_one = cong_introL_W (pF, oneN, mult pm1 pm1, pm2) chain
        val res = cong_sym_W (pF, oneN, mult pm1 pm1) congL_one
      in res end
    val res = exE_W (Pex, goalC) predEx "r_sq" body
  in varify (Thm.implies_intr (ctermW hPrimeP) res) end;
val () = if length (Thm.hyps_of sq_pm1_cong) = 0 then out "OK sq_pm1_cong\n" else out "FAIL sq_pm1_cong\n";
fun sq_pm1_cong_W pt hPrime = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt)] sq_pm1_cong)) hPrime;

(* finv_pm1 : prime2 p ==> oeq (finv p (sub p 1)) (sub p 1) *)
val finv_pm1 =
  let
    val pF = Free("p", natT)
    val hPrimeP = jT (prime2 pF); val hPrime = Thm.assume (ctermW hPrimeP)
    val hp1 = prime2_gt1_W pF hPrime
    val pm1 = sub pF oneN
    val memPm1 = lmem_pm1_rng_W pF hp1
    val cong_pm1_fi = finv_inv_W (pF, pm1) hPrime memPm1
    val cong_pm1_pm1 = sq_pm1_cong_W pF hPrime
    val cong_fi_pm1 = inverse_unique_W (pF, pm1, finv pF pm1, pm1) cong_pm1_fi cong_pm1_pm1
    val memFi = finv_mem_W (pF, pm1) hPrime memPm1
    val lt_fi = lmem_range_lt_W (pF, finv pF pm1) hp1 memFi
    val lt_pm1 = lmem_range_lt_W (pF, pm1) hp1 memPm1
    val res = cong_range_unique_W (pF, finv pF pm1, pm1) hp1 lt_fi lt_pm1 cong_fi_pm1
  in varify (Thm.implies_intr (ctermW hPrimeP) res) end;
val () = if length (Thm.hyps_of finv_pm1) = 0 then out "OK finv_pm1\n" else out "FAIL finv_pm1\n";
fun finv_pm1_W pt hPrime = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt)] finv_pm1)) hPrime;

val () = out "WA_STEP1_DONE\n";
(* ============================================================================
   STEP 2 : helpers for L2 = lremove 1 (upto (sub p 2)).
   ============================================================================ *)
val () = out "WA_STEP2_BEGIN\n";

val mem_remove_neq_vW = varify mem_remove_neq;
val le_neq_lt_vW      = varify le_neq_lt;
val mem_remove_fwd_vW2 = varify mem_remove_fwd;

fun mem_remove_neq_W (yt,xt,Lt) hnd hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("y",0), ctermW yt),(("x",0), ctermW xt),(("L",0), ctermW Lt)] mem_remove_neq_vW)
  in Thm.implies_elim (Thm.implies_elim inst hnd) hmem end;
fun mem_remove_fwd_W (yt,xt,Lt) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("y",0), ctermW yt),(("x",0), ctermW xt),(("L",0), ctermW Lt)] mem_remove_fwd_vW2)
  in Thm.implies_elim inst hmem end;
fun le_neq_lt_W (dt,nt) hle hneq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("d",0), ctermW dt),(("n",0), ctermW nt)] le_neq_lt_vW)
  in Thm.implies_elim (Thm.implies_elim inst hle) hneq end;
fun mem_remove_bwd_W (yt,xt,Lt) hconj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("y",0), ctermW yt),(("x",0), ctermW xt),(("L",0), ctermW Lt)] mem_remove_bwd_vW)
  in Thm.implies_elim inst hconj end;

(* pm1_eq_Suc_pm2 : lt 1 p ==> oeq (sub p 1)(Suc (sub p 2)) *)
val pm1_eq_Suc_pm2 =
  let
    val pF = Free("p", natT)
    val hp1P = jT (lt oneN pF); val hp1 = Thm.assume (ctermW hp1P)
    val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pF)] pred2)) hp1
    val goalC = oeq (sub pF oneN) (suc (sub pF twoN))
    val Pex = Term.lambda (Free("r_g",natT))
                  (mkConj3 (oeq pF (suc (suc (Free("r_g",natT)))))
                           (oeq (sub pF oneN) (suc (Free("r_g",natT))))
                           (oeq (sub pF twoN) (Free("r_g",natT))))
    fun body r (hc:thm) =
      let
        val hrest   = conjunct2_W (oeq pF (suc(suc r)), mkConj (oeq (sub pF oneN) (suc r))(oeq (sub pF twoN) r)) hc
        val hpm1_Sr = conjunct1_W (oeq (sub pF oneN) (suc r), oeq (sub pF twoN) r) hrest
        val hpm2_r  = conjunct2_W (oeq (sub pF oneN) (suc r), oeq (sub pF twoN) r) hrest
        val hpm2_r_s= oeq_sym_vW OF [hpm2_r]
        val Sr_Spm2 = Suc_cong_vW OF [hpm2_r_s]
        val res = oeq_trans_vW OF [hpm1_Sr, Sr_Spm2]
      in res end
    val res = exE_W (Pex, goalC) predEx "r_eq" body
  in varify (Thm.implies_intr (ctermW hp1P) res) end;
val () = if length (Thm.hyps_of pm1_eq_Suc_pm2) = 0 then out "OK pm1_eq_Suc_pm2\n" else out "FAIL pm1_eq_Suc_pm2\n";
fun pm1_eq_Suc_pm2_W pt hp1 = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt)] pm1_eq_Suc_pm2)) hp1;

val () = out "WA_STEP2_HELPERS_OK\n";

(* le_pm2_pm1 : lt 1 p ==> le (sub p 2)(sub p 1) *)
fun le_pm2_pm1_W pt hp1 =
  let val e = pm1_eq_Suc_pm2_W pt hp1
      val lesuc = le_self_suc_W (sub pt twoN)
      val e_s = oeq_sym_vW OF [e]
      val Ple = Term.lambda (Free("z_lp2",natT)) (le (sub pt twoN) (Free("z_lp2",natT)))
  in oeq_rw_W (Ple, suc (sub pt twoN), sub pt oneN) e_s lesuc end;

(* mem_pm1_neq_imp_pm2 : lt 1 p ==> lmem y (uptoF (sub p 1)) ==> neg (oeq y (sub p 1)) ==> lmem y (uptoF (sub p 2)) *)
fun mem_pm1_neq_imp_pm2_W pt y hp1 hmem hneq =
  let
    val cj = lmem_upto_fwd_W (y, sub pt oneN) hmem
    val ypos = conjunct1_W (lt ZeroC y, le y (sub pt oneN)) cj
    val yle  = conjunct2_W (lt ZeroC y, le y (sub pt oneN)) cj
    val ylt  = le_neq_lt_W (y, sub pt oneN) yle hneq
    val e    = pm1_eq_Suc_pm2_W pt hp1
    val Plt  = Term.lambda (Free("z_yl",natT)) (lt y (Free("z_yl",natT)))
    val ylt2 = oeq_rw_W (Plt, sub pt oneN, suc (sub pt twoN)) e ylt
    val yle2 = lt_suc_imp_le_W (y, sub pt twoN) ylt2
    val cj2  = conjI_W (lt ZeroC y, le y (sub pt twoN)) ypos yle2
  in lmem_upto_bwd_W (y, sub pt twoN) cj2 end;

(* mem_pm2_imp_pm1 : lt 1 p ==> lmem y (uptoF (sub p 2)) ==> lmem y (uptoF (sub p 1)) *)
fun mem_pm2_imp_pm1_W pt y hp1 hmem =
  let
    val cj = lmem_upto_fwd_W (y, sub pt twoN) hmem
    val ypos = conjunct1_W (lt ZeroC y, le y (sub pt twoN)) cj
    val yle  = conjunct2_W (lt ZeroC y, le y (sub pt twoN)) cj
    val lepp = le_pm2_pm1_W pt hp1
    val yle1 = le_trans_W (y, sub pt twoN, sub pt oneN) yle lepp
    val cj2  = conjI_W (lt ZeroC y, le y (sub pt oneN)) ypos yle1
  in lmem_upto_bwd_W (y, sub pt oneN) cj2 end;

val () = out "WA_STEP2_MEMBRIDGE_OK\n";
(* ============================================================================
   STEP 2 core helpers
   ============================================================================ *)
val () = out "WA_STEP2CORE_BEGIN\n";

fun finv_invol_W (pt,xt) hPrime hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pt),(("x",0), ctermW xt)] finv_invol)
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hmem end;
fun finv_neq_W (pt,xt) hPrime hmem hne1 hnepm1 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pt),(("x",0), ctermW xt)] finv_neq)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hPrime) hmem) hne1) hnepm1 end;

(* y_neq_pm1 : lt 1 p ==> lmem y (uptoF (sub p 2)) ==> neg (oeq y (sub p 1)) *)
fun y_neq_pm1_W pt y hp1 hmem2 =
  let
    val cj = lmem_upto_fwd_W (y, sub pt twoN) hmem2
    val yle = conjunct2_W (lt ZeroC y, le y (sub pt twoN)) cj
    val Pd = Abs("d", natT, oeq (sub pt twoN)(add y (Bound 0)))
    fun body d (hd:thm) =
      let
        val e = pm1_eq_Suc_pm2_W pt hp1
        val Sd = Suc_cong_vW OF [hd]
        val aS = addSuc_W (y, d)
        val aS_s = oeq_sym_vW OF [aS]
        val Sd2 = oeq_trans_vW OF [Sd, aS_s]
        val e2 = oeq_trans_vW OF [e, Sd2]
        val lty = le_intro_W (suc y, sub pt oneN, d) e2
      in lty end
    val ltypm1 = exE_W (Pd, lt y (sub pt oneN)) yle "d_ynp" body
    val hassume = Thm.assume (ctermW (jT (oeq y (sub pt oneN))))
    val Plt = Term.lambda (Free("z_yi",natT)) (lt (Free("z_yi",natT)) (sub pt oneN))
    val ltpp = oeq_rw_W (Plt, y, sub pt oneN) hassume ltypm1
    val fls = lt_irrefl_W (sub pt oneN) ltpp
    val metaImp = Thm.implies_intr (ctermW (jT (oeq y (sub pt oneN)))) fls
  in impI_W (oeq y (sub pt oneN), oFalseC) metaImp end;

val () = out "WA_STEP2CORE_HELPERS_OK\n";
(* ============================================================================
   STEP 2 : the four pairing hypotheses for L2 + lnodup L2, then apply pairing_lemma.
   ============================================================================ *)
val () = out "WA_STEP2HYP_BEGIN\n";

(* pairing_lemma is an OBJECT-Imp chain: Imp (lnodup L)(Imp H2 (Imp H3 (Imp H4 (Imp H5 cong)))).
   Apply via object modus ponens mp_W at each layer. *)
fun pairing_apply (invAbs, pt, Lt, ndT, h2T, h3T, h4T, h5T, congT) hnd h2 h3 h4 h5 =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("inv",0), ctermW invAbs),(("p",0), ctermW pt),(("L_fin",0), ctermW Lt)] pairing_lemma_vW)
    val rest5 = mkImp h5T congT
    val rest4 = mkImp h4T rest5
    val rest3 = mkImp h3T rest4
    val rest2 = mkImp h2T rest3
    val s1 = mp_W (ndT, rest2) inst hnd
    val s2 = mp_W (h2T, rest3) s1 h2
    val s3 = mp_W (h3T, rest4) s2 h3
    val s4 = mp_W (h4T, rest5) s3 h4
    val s5 = mp_W (h5T, congT) s4 h5
  in s5 end;

(* cong_L2_one : prime2 p ==> cong p (lprod (lremove 1 (upto (sub p 2)))) 1 *)
val cong_L2_one =
  let
    val pF = Free("p", natT)
    val hPrimeP = jT (prime2 pF); val hPrime = Thm.assume (ctermW hPrimeP)
    val hp1 = prime2_gt1_W pF hPrime
    val rngInner = uptoF (sub pF twoN)
    val L2 = lremove oneN rngInner
    val invAbs = Term.lambda (Free("xinv", natT)) (finv pF (Free("xinv", natT)))
    val ndInner = lnodup_upto_W (sub pF twoN)

    fun mem_inner y hyR = mem_remove_fwd_W (y, oneN, rngInner) hyR
    fun y_neq_1 y hyR = mem_remove_neq_W (y, oneN, rngInner) ndInner hyR
    fun mem_full y hyR = mem_pm2_imp_pm1_W pF y hp1 (mem_inner y hyR)
    fun y_neq_pm1 y hyR = y_neq_pm1_W pF y hp1 (mem_inner y hyR)

    val h3 =
      let val yf = Free("xh3", natT)
          val Pabs = Term.lambda yf (mkImp (lmem yf L2) (cong pF (mult yf (finv pF yf)) oneN))
          val hyR = Thm.assume (ctermW (jT (lmem yf L2)))
          val res = finv_inv_W (pF, yf) hPrime (mem_full yf hyR)
          val imp = impI_W (lmem yf L2, cong pF (mult yf (finv pF yf)) oneN)
                      (Thm.implies_intr (ctermW (jT (lmem yf L2))) res)
      in allI_W Pabs (Thm.forall_intr (ctermW yf) imp) end

    val h4 =
      let val yf = Free("xh4", natT)
          val Pabs = Term.lambda yf (mkImp (lmem yf L2) (neg (oeq (finv pF yf) yf)))
          val hyR = Thm.assume (ctermW (jT (lmem yf L2)))
          val res = finv_neq_W (pF, yf) hPrime (mem_full yf hyR) (y_neq_1 yf hyR) (y_neq_pm1 yf hyR)
          val imp = impI_W (lmem yf L2, neg (oeq (finv pF yf) yf))
                      (Thm.implies_intr (ctermW (jT (lmem yf L2))) res)
      in allI_W Pabs (Thm.forall_intr (ctermW yf) imp) end

    val h5 =
      let val yf = Free("xh5", natT)
          val Pabs = Term.lambda yf (mkImp (lmem yf L2) (oeq (finv pF (finv pF yf)) yf))
          val hyR = Thm.assume (ctermW (jT (lmem yf L2)))
          val res = finv_invol_W (pF, yf) hPrime (mem_full yf hyR)
          val imp = impI_W (lmem yf L2, oeq (finv pF (finv pF yf)) yf)
                      (Thm.implies_intr (ctermW (jT (lmem yf L2))) res)
      in allI_W Pabs (Thm.forall_intr (ctermW yf) imp) end

    val h2 =
      let val yf = Free("xh2", natT)
          val fy = finv pF yf
          val Pabs = Term.lambda yf (mkImp (lmem yf L2) (lmem (finv pF yf) L2))
          val hyR = Thm.assume (ctermW (jT (lmem yf L2)))
          val memFi_full = finv_mem_W (pF, yf) hPrime (mem_full yf hyR)
          val hyNe1 = y_neq_1 yf hyR
          val hyNepm1 = y_neq_pm1 yf hyR
          val fy_neq_1 =
            let val hassume = Thm.assume (ctermW (jT (oeq fy oneN)))
                val invol = finv_invol_W (pF, yf) hPrime (mem_full yf hyR)
                val Pr = Term.lambda (Free("z_f1",natT)) (oeq (finv pF (Free("z_f1",natT))) yf)
                val finv1_y = oeq_rw_W (Pr, fy, oneN) hassume invol
                val finv1_1 = finv_one_W pF hPrime
                val finv1_1_s = oeq_sym_vW OF [finv1_1]
                val one_y = oeq_trans_vW OF [finv1_1_s, finv1_y]
                val y_one = oeq_sym_vW OF [one_y]
                val fls = mp_W (oeq yf oneN, oFalseC) hyNe1 y_one
            in impI_W (oeq fy oneN, oFalseC) (Thm.implies_intr (ctermW (jT (oeq fy oneN))) fls) end
          val fy_neq_pm1 =
            let val hassume = Thm.assume (ctermW (jT (oeq fy (sub pF oneN))))
                val invol = finv_invol_W (pF, yf) hPrime (mem_full yf hyR)
                val Pr = Term.lambda (Free("z_fp",natT)) (oeq (finv pF (Free("z_fp",natT))) yf)
                val finvpm1_y = oeq_rw_W (Pr, fy, sub pF oneN) hassume invol
                val finvpm1_pm1 = finv_pm1_W pF hPrime
                val finvpm1_pm1_s = oeq_sym_vW OF [finvpm1_pm1]
                val pm1_y = oeq_trans_vW OF [finvpm1_pm1_s, finvpm1_y]
                val y_pm1 = oeq_sym_vW OF [pm1_y]
                val fls = mp_W (oeq yf (sub pF oneN), oFalseC) hyNepm1 y_pm1
            in impI_W (oeq fy (sub pF oneN), oFalseC) (Thm.implies_intr (ctermW (jT (oeq fy (sub pF oneN)))) fls) end
          val memFi_inner = mem_pm1_neq_imp_pm2_W pF fy hp1 memFi_full fy_neq_pm1
          val cjBwd = conjI_W (lmem fy rngInner, neg (oeq fy oneN)) memFi_inner fy_neq_1
          val memFi_L2 = mem_remove_bwd_W (fy, oneN, rngInner) cjBwd
          val imp = impI_W (lmem yf L2, lmem (finv pF yf) L2)
                      (Thm.implies_intr (ctermW (jT (lmem yf L2))) memFi_L2)
      in allI_W Pabs (Thm.forall_intr (ctermW yf) imp) end

    val ndL2 = nodup_remove_W (oneN, rngInner) ndInner

    val ndT  = lnodup L2
    val h2T  = mkForall (Term.lambda (Free("xh2",natT)) (mkImp (lmem (Free("xh2",natT)) L2) (lmem (finv pF (Free("xh2",natT))) L2)))
    val h3T  = mkForall (Term.lambda (Free("xh3",natT)) (mkImp (lmem (Free("xh3",natT)) L2) (cong pF (mult (Free("xh3",natT)) (finv pF (Free("xh3",natT)))) oneN)))
    val h4T  = mkForall (Term.lambda (Free("xh4",natT)) (mkImp (lmem (Free("xh4",natT)) L2) (neg (oeq (finv pF (Free("xh4",natT))) (Free("xh4",natT))))))
    val h5T  = mkForall (Term.lambda (Free("xh5",natT)) (mkImp (lmem (Free("xh5",natT)) L2) (oeq (finv pF (finv pF (Free("xh5",natT)))) (Free("xh5",natT)))))
    val congT = cong pF (lprod L2) oneN

    val congL2 = pairing_apply (invAbs, pF, L2, ndT, h2T, h3T, h4T, h5T, congT) ndL2 h2 h3 h4 h5
  in varify (Thm.implies_intr (ctermW hPrimeP) congL2) end;
val () = if length (Thm.hyps_of cong_L2_one) = 0 then out "OK cong_L2_one\n" else out "FAIL cong_L2_one\n";

val () = out "WA_STEP2_DONE\n";
(* ============================================================================
   STEP 3 : factorial decomposition + conclusion (WILSON).
   ============================================================================ *)
val () = out "WA_STEP3_BEGIN\n";

val leq_sym_vW   = varify leq_sym;
val leq_refl_vW2 = varify leq_refl_ax;
fun leq_sym_W h = leq_sym_vW OF [h];
fun leqRefl_W t = beta_norm (Drule.infer_instantiate ctxtW [(("a",0), ctermW t)] leq_refl_vW2);
fun upto_suc_W nt = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW nt)] upto_suc_vW);
val lremoveNil_vW = varify lremove_nil_ax;
fun lremoveNil_W xt = beta_norm (Drule.infer_instantiate ctxtW [(("x",0), ctermW xt)] lremoveNil_vW);

(* lprod_inner_eq_L2 : prime2 p ==> oeq (lprod (upto(sub p 2)))(lprod (lremove 1 (upto(sub p 2)))) *)
val lprod_inner_eq_L2 =
  let
    val pF = Free("p", natT)
    val hPrimeP = jT (prime2 pF); val hPrime = Thm.assume (ctermW hPrimeP)
    val hp1 = prime2_gt1_W pF hPrime
    val rngInner = uptoF (sub pF twoN)
    val L2 = lremove oneN rngInner
    val goalC = oeq (lprod rngInner) (lprod L2)
    val dj = dzos_W (sub pF twoN)
    val caseZ =
      let
        val hz = Thm.assume (ctermW (jT (oeq (sub pF twoN) ZeroC)))
        val hz_s = oeq_sym_vW OF [hz]
        val Pup = Term.lambda (Free("z_uz",natT)) (leq (uptoF (Free("z_uz",natT))) lnilC)
        val u0 = uptoZero_W
        val rngLnil = oeq_rw_W (Pup, ZeroC, sub pF twoN) hz_s u0
        val lp_inner_nil = lprod_cong_W (rngInner, lnilC) rngLnil
        val rmnil = lremoveNil_W oneN
        val P_lnil = lprod_cong_W (lremove oneN lnilC, lnilC) rmnil
        val leq_lnil_inner = leq_sym_W rngLnil
        val Pp = Term.lambda (Free("z_pl",natlistT)) (oeq (lprod (lremove oneN (Free("z_pl",natlistT)))) (lprod lnilC))
        val inst = beta_norm (Drule.infer_instantiate ctxtW
              [(("P",0), ctermW Pp),(("a",0), ctermW lnilC),(("b",0), ctermW rngInner)] leq_subst_vW)
        val P_inner = inst OF [leq_lnil_inner, P_lnil]
        val P_inner_s = oeq_sym_vW OF [P_inner]
        val res = oeq_trans_vW OF [lp_inner_nil, P_inner_s]
      in Thm.implies_intr (ctermW (jT (oeq (sub pF twoN) ZeroC))) res end
    val caseS =
      let
        val hsP = jT (mkExSuc_W (sub pF twoN))
        val hs  = Thm.assume (ctermW hsP)
        val Pq  = Abs("q", natT, oeq (sub pF twoN) (suc (Bound 0)))
        fun body q (hq:thm) =
          let
            val lt01 = le_refl_W oneN
            val a1q = addSuc_W (ZeroC, q)
            val a0q = add0_W q
            val a0qs= Suc_cong_vW OF [a0q]
            val one_q_Sq = oeq_trans_vW OF [a1q, a0qs]
            val one_q_sub = oeq_trans_vW OF [one_q_Sq, oeq_sym_vW OF [hq]]
            val sub_1q = oeq_sym_vW OF [one_q_sub]
            val le1sub = le_intro_W (oneN, sub pF twoN, q) sub_1q
            val cj = conjI_W (lt ZeroC oneN, le oneN (sub pF twoN)) lt01 le1sub
            val mem1 = lmem_upto_bwd_W (oneN, sub pF twoN) cj
            val ex = extract_W (oneN, rngInner) mem1
            val m1l = mult1l_W (lprod L2)
            val res = oeq_trans_vW OF [ex, m1l]
          in res end
        val res = exE_W (Pq, goalC) hs "q_s3" body
      in Thm.implies_intr (ctermW hsP) res end
    val res = disjE_W (oeq (sub pF twoN) ZeroC, mkExSuc_W (sub pF twoN), goalC) dj caseZ caseS
  in varify (Thm.implies_intr (ctermW hPrimeP) res) end;
val () = if length (Thm.hyps_of lprod_inner_eq_L2) = 0 then out "OK lprod_inner_eq_L2\n" else out "FAIL lprod_inner_eq_L2\n";
fun lprod_inner_eq_L2_W pt hPrime = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt)] lprod_inner_eq_L2)) hPrime;

val () = out "WA_STEP3_INNER_OK\n";
(* ============================================================================
   STEP 3 final : lprod rngFull = pm1 * lprod L2 ; then WILSON.
   ============================================================================ *)
val () = out "WA_STEP3FINAL_BEGIN\n";

fun cong_L2_one_W pt hPrime = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt)] cong_L2_one)) hPrime;

(* lprod_full_decomp : prime2 p ==> oeq (lprod (upto(sub p 1))) (mult (sub p 1)(lprod (lremove 1 (upto(sub p 2))))) *)
val lprod_full_decomp =
  let
    val pF = Free("p", natT)
    val hPrimeP = jT (prime2 pF); val hPrime = Thm.assume (ctermW hPrimeP)
    val hp1 = prime2_gt1_W pF hPrime
    val pm1 = sub pF oneN
    val rngFull = uptoF pm1
    val rngInner = uptoF (sub pF twoN)
    val L2 = lremove oneN rngInner
    val us = upto_suc_W (sub pF twoN)
    val eqpm1 = pm1_eq_Suc_pm2_W pF hp1
    val eqpm1_s = oeq_sym_vW OF [eqpm1]
    val Pus = Term.lambda (Free("z_us",natT))
                (leq (uptoF (Free("z_us",natT))) (lcons (Free("z_us",natT)) rngInner))
    val usRw = oeq_rw_W (Pus, suc (sub pF twoN), pm1) eqpm1_s us
    val lp_full = lprod_cong_W (rngFull, lcons pm1 rngInner) usRw
    val lp_cons = lprodCons_W (pm1, rngInner)
    val lp_full2 = oeq_trans_vW OF [lp_full, lp_cons]
    val innerEq = lprod_inner_eq_L2_W pF hPrime
    val rcong = mult_cong_r_W (pm1, lprod rngInner, lprod L2) innerEq
    val res = oeq_trans_vW OF [lp_full2, rcong]
  in varify (Thm.implies_intr (ctermW hPrimeP) res) end;
val () = if length (Thm.hyps_of lprod_full_decomp) = 0 then out "OK lprod_full_decomp\n" else out "FAIL lprod_full_decomp\n";
fun lprod_full_decomp_W pt hPrime = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt)] lprod_full_decomp)) hPrime;

val () = out "WA_STEP3FINAL_DECOMP_OK\n";

(* ============================================================================
   WILSON : prime2 p ==> cong p (lprod (upto (sub p 1))) (sub p 1)
   ============================================================================ *)
val wilson =
  let
    val pF = Free("p", natT)
    val hPrimeP = jT (prime2 pF); val hPrime = Thm.assume (ctermW hPrimeP)
    val pm1 = sub pF oneN
    val rngFull = uptoF pm1
    val rngInner = uptoF (sub pF twoN)
    val L2 = lremove oneN rngInner
    val congL2 = cong_L2_one_W pF hPrime
    val creflPm1 = cong_refl_W (pF, pm1)
    val congMult = cong_mult_W (pF, pm1, pm1, lprod L2, oneN) creflPm1 congL2
    val m1r = mult1r_W pm1
    val Pc = Term.lambda (Free("z_w",natT)) (cong pF (mult pm1 (lprod L2)) (Free("z_w",natT)))
    val congMult2 = oeq_rw_W (Pc, mult pm1 oneN, pm1) m1r congMult
    val decomp = lprod_full_decomp_W pF hPrime
    val congDecomp = cong_of_eq_W (pF, lprod rngFull, mult pm1 (lprod L2)) decomp
    val res = cong_trans_W (pF, lprod rngFull, mult pm1 (lprod L2), pm1) congDecomp congMult2
  in varify (Thm.implies_intr (ctermW hPrimeP) res) end;
val () = if length (Thm.hyps_of wilson) = 0 then out "OK wilson\n" else out "FAIL wilson\n";

val () = out "WA_WILSON_PROVED\n";
(* ============================================================================
   WILSON : validation (0-hyp + aconv intended) + soundness probes.
   prime2 is THE structural prime; `prime` (phase-1) is the variable-captured
   broken predicate (prime aconv prime2 = false), so we state with prime2.
   ============================================================================ *)
val () = out "WA_VALIDATE_BEGIN\n";

val pVw = Var(("p",0), natT);
val oneVw = suc ZeroC;
val pm1Vw = sub pVw oneVw;
val rngVw = uptoF pm1Vw;

val wilson_intended =
  Logic.mk_implies (jT (prime2 pVw),
    jT (cong pVw (lprod rngVw) pm1Vw));

val r_wilson = (length (Thm.hyps_of wilson) = 0) andalso ((Thm.prop_of wilson) aconv wilson_intended);
val () = if r_wilson then out "OK wilson aconv intended (0-hyp): prime p ==> cong p ((p-1)!) (p-1)\n"
         else (out ("FAIL wilson aconv\n  got      = "^Syntax.string_of_term ctxtW (Thm.prop_of wilson)^"\n"
                    ^"  intended = "^Syntax.string_of_term ctxtW wilson_intended^"\n"));

val wilson_BOGUS1 =
  Logic.mk_implies (jT (prime2 pVw), jT (cong pVw (lprod rngVw) oneVw));
val probe1 = not ((Thm.prop_of wilson) aconv wilson_BOGUS1);
val () = if probe1 then out "PROBE_OK wilson is NOT cong p ((p-1)!) 1 (that is false for odd primes)\n"
         else out "PROBE_FAIL wilson collapsed to cong p ((p-1)!) 1\n";

val wilson_BOGUS2 = jT (cong pVw (lprod rngVw) pm1Vw);
val probe2 = not ((Thm.prop_of wilson) aconv wilson_BOGUS2);
val () = if probe2 then out "PROBE_OK wilson genuinely needs the prime hypothesis\n"
         else out "PROBE_FAIL wilson dropped the prime hypothesis\n";

val wilson_BOGUS3 =
  Logic.mk_implies (jT (prime2 pVw), jT (cong pVw (lprod rngVw) ZeroC));
val probe3 = not ((Thm.prop_of wilson) aconv wilson_BOGUS3);
val () = if probe3 then out "PROBE_OK wilson residue is (p-1)=-1, not 0\n"
         else out "PROBE_FAIL wilson residue collapsed to 0\n";

val () =
  if r_wilson andalso probe1 andalso probe2 andalso probe3
  then out "WILSON_OK\n"
  else out "WILSON_FAILED\n";
