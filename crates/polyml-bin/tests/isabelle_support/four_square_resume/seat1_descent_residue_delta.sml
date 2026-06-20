(* ============================================================================
   DESCENT SEAT 1 (direct / explicit-witness route).
   TARGET descent_step :
     prime2 p ==> 1<m ==> m<p ==> four_sq (m*p)
        ==> EX m2. 0<m2 AND m2<m AND four_sq (m2*p)
   Built on the assembled four_square base (ctxtGR / ctermGR / thyGR).

   ACHIEVED (this delta), 0-hyp + aconv + 2 soundness probes:
     descent_residue :
       prime2 p ==> 1<m ==> m<p ==> four_sq (m*p)
          ==> EX r. (0<r) AND (r<=m) AND four_sq (m*r)
   This is the descent SETUP: it PROVES (a) the SIGNED four_residue_sum (thread
   the per-coordinate a'== +/- a (mod m) through all four coords), (b) the r=0
   EXCLUSION (a'=..=d'=0 => m|a,b,c,d => m^2|m*p => m|p, contradicting 1<m<p
   prime), and (c) the bound r<=m (the AM bound: 4*(sum) <= 4*m^2).

   NOT in descent_residue (the open remainder of the full step, see SEAT SUMMARY):
     - upgrading r<=m to the STRICT r<m (the r=m exclusion: forces all 2x'=m,
       m even, x'=m/2 -> m|2a..2d -> m|4p; needs Euclid's lemma);
     - (d) the Euler divide-by-m^2 (apply the four-square identity to (m*p)(m*r),
       show m|w,x,y,z, divide).  Both are multi-lemma efforts; (d) in particular
       needs a SIGNED-bilinear Euler identity over N (the banked proveStarFor uses
       absdiff-massaged witnesses, so its w,x,y,z are not the clean bilinear forms
       whose divisibility-by-m the divide requires).

   descent_residue does NOT use four_sq_mult / proveStarFor, so it is genuinely
   0-hyp independent of the partA star (verified on the REAL base).
   ============================================================================ *)
val () = out "L4_SEAT1_BEGIN\n";

(* ---------- small GR-level glue ---------- *)
fun sq x = mult x x;

(* GR alias of the schematic cong_radd_cancel (cong m (a+w)(b+w) ==> cong m a b) *)
fun cong_radd_cancel_r (m,a,b,w) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("m_cc",0), ctermGR m),(("a_cc",0), ctermGR a),
       (("b_cc",0), ctermGR b),(("w_cc",0), ctermGR w)] cong_radd_cancel)) h;

(* cong_of_oeq_r (m,X,Y) : oeq X Y ==> cong m X Y    (witness 0 on congR-form a=b+m*0) *)
fun cong_of_oeq_r (mT,X,Y) hXY =
  let
    (* need  oeq X (add Y (mult m 0))  to feed cong_introR_r (m,X,Y,0) *)
    val m0  = mult0r_d mT                      (* m*0 = 0 *)
    val yp0 = oeqTrans_r2 (add_cong_r_d (Y, mult mT ZeroC, ZeroC) m0, add0r_d Y) (* Y + m*0 = Y *)
    val ypY = oeqSym_r2 yp0                     (* Y = Y + m*0 *)
    val hXp = oeqTrans_r2 (hXY, ypY)            (* X = Y + m*0 *)
  in cong_introR_r (mT, X, Y, ZeroC) hXp end;

(* x * 0 rewrite to 0, as a cong:  cong m (x*0) 0 *)
(* (not needed directly; we use mult0r_d) *)

val () = out "L4_SEAT1_GLUE_OK\n";

(* ----------------------------------------------------------------------------
   sq_cong_from_signed (m, x', x) hsign :
     hsign : Disj (cong m x' x) (cong m (x'+x) 0)
     ==> cong m (x'*x') (x*x)
   LEFT branch: cong_sq_r.
   RIGHT branch (x' == -x): via the N-identity  x'^2 + x*(x'+x) = x^2 + x'*(x'+x)
     and cong m (x*(x'+x)) 0, cong m (x'*(x'+x)) 0.
   ---------------------------------------------------------------------------- *)
fun sq_cong_from_signed (mT, apT, aT) hsign =
  let
    val goalC = cong mT (sq apT) (sq aT)
    val caseL =
      let
        val hP = jT (cong mT apT aT)
        val h  = Thm.assume (ctermGR hP)
        val r  = cong_sq_r (mT, apT, aT) h     (* cong m (a'*a')(a*a) *)
      in Thm.implies_intr (ctermGR hP) r end
    val caseR =
      let
        val sT = add apT aT
        val hP = jT (cong mT sT ZeroC)
        val h  = Thm.assume (ctermGR hP)        (* cong m (a'+a) 0 *)
        (* cong m (a*(a'+a)) 0  and  cong m (a'*(a'+a)) 0 *)
        val cas  = cong_mult_r (mT, aT, aT, sT, ZeroC) (cong_refl_g (mT, aT)) h   (* cong m (a*s)(a*0) *)
        val a0   = mult0r_d aT                                                    (* a*0 = 0 *)
        val cas0 = cong_trans_g (mT, mult aT sT, mult aT ZeroC, ZeroC) cas (cong_of_oeq_r (mT, mult aT ZeroC, ZeroC) a0)  (* cong m (a*s) 0 *)
        val cps  = cong_mult_r (mT, apT, apT, sT, ZeroC) (cong_refl_g (mT, apT)) h
        val ap0  = mult0r_d apT
        val cps0 = cong_trans_g (mT, mult apT sT, mult apT ZeroC, ZeroC) cps (cong_of_oeq_r (mT, mult apT ZeroC, ZeroC) ap0)  (* cong m (a'*s) 0 *)
        (* the N-identity : oeq (a'^2 + a*s) (a^2 + a'*s) *)
        val idI = proveIdentityG (add (sq apT) (mult aT sT)) (add (sq aT) (mult apT sT))
        val cId = cong_of_oeq_r (mT, add (sq apT) (mult aT sT), add (sq aT) (mult apT sT)) idI
                  (* cong m (a'^2 + a*s)(a^2 + a'*s) *)
        (* cong m (a'^2 + a*s)(a'^2 + 0)  via cong_add(refl a'^2, cas0) ; then -> a'^2 *)
        val cL1 = cong_add_g (mT, sq apT, sq apT, mult aT sT, ZeroC) (cong_refl_g (mT, sq apT)) cas0
                  (* cong m (a'^2 + a*s)(a'^2 + 0) *)
        val rwL = oeqTrans_r2 (add_cong_r_d (sq apT, ZeroC, ZeroC) (oeqRefl_g ZeroC), add0r_d (sq apT)) (* (a'^2+0)=a'^2 ; trivial via add0r *)
        (* simpler: a'^2 + 0 = a'^2 *)
        val cL  = cong_trans_g (mT, add (sq apT) (mult aT sT), add (sq apT) ZeroC, sq apT)
                    cL1 (cong_of_oeq_r (mT, add (sq apT) ZeroC, sq apT) (add0r_d (sq apT)))
                  (* cong m (a'^2 + a*s) (a'^2) *)
        val cR1 = cong_add_g (mT, sq aT, sq aT, mult apT sT, ZeroC) (cong_refl_g (mT, sq aT)) cps0
                  (* cong m (a^2 + a'*s)(a^2 + 0) *)
        val cR  = cong_trans_g (mT, add (sq aT) (mult apT sT), add (sq aT) ZeroC, sq aT)
                    cR1 (cong_of_oeq_r (mT, add (sq aT) ZeroC, sq aT) (add0r_d (sq aT)))
                  (* cong m (a^2 + a'*s) (a^2) *)
        (* chain: a'^2 == a'^2+a*s == a^2+a'*s == a^2 *)
        val step1 = cong_sym_g (mT, add (sq apT) (mult aT sT), sq apT) cL   (* cong m (a'^2)(a'^2+a*s) *)
        val step2 = cong_trans_g (mT, sq apT, add (sq apT) (mult aT sT), add (sq aT) (mult apT sT)) step1 cId
        val res   = cong_trans_g (mT, sq apT, add (sq aT) (mult apT sT), sq aT) step2 cR
      in Thm.implies_intr (ctermGR hP) res end
  in disjE_r (cong mT apT aT, cong mT (add apT aT) ZeroC, goalC) hsign caseL caseR end;
val () = out "L4_SQ_CONG_FROM_SIGNED_DEFINED\n";

(* smoke *)
val () =
  let
    val mF = Free("m_t", natT); val apF = Free("ap_t", natT); val aF = Free("a_t", natT)
    val hs = Thm.assume (ctermGR (jT (mkDisj (cong mF apF aF) (cong mF (add apF aF) ZeroC))))
    val r  = sq_cong_from_signed (mF, apF, aF) hs
  in out ("SMOKE sq_cong_from_signed hyps="^Int.toString(length(Thm.hyps_of r))
          ^" prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)^"\n") end
  handle e => out ("SMOKE sq_cong_from_signed FAIL "^exnMessage e^"\n");
val () = out "L4_SEAT1_SMOKE_SQCONG_DONE\n";

val () = out "L4_SEAT1_PHASE_A0_DONE\n";

(* ----------------------------------------------------------------------------
   (a) SIGNED four_residue_sum.
   sym_residue_signed (m,x) hm : EX x'. (cong m x' x OR cong m (x'+x) 0) /\ le (x'+x') m.
   For each coordinate we unpack -> (x', signDisj, bound), and DERIVE squared cong.
   Output existential carries: sum=m*r, the FOUR sign disjuncts, the FOUR bounds.
   ---------------------------------------------------------------------------- *)
val sym_signed_v = varify sym_residue_signed_thm;   (* schematic m_srs, a_srs *)
fun sym_signed_app (mT, aT) hm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("m_srs",0), ctermGR mT),(("a_srs",0), ctermGR aT)] sym_signed_v)
  in Thm.implies_elim inst hm end;

(* sign disjunction term for (x', x) *)
fun signD (mT, xpT, xT) = mkDisj (cong mT xpT xT) (cong mT (add xpT xT) ZeroC);

(* unpack one signed residue existential. wnm distinct per call.
   k : term(x') -> thm(signD) -> thm(bound) -> thm(goalC).  goalC must not mention x'. *)
fun with_signed wnm (mT, xT) hm (k : term -> thm -> thm -> thm) goalC =
  let
    val ex = sym_signed_app (mT, xT) hm
    val wF = Free(wnm, natT)
    val P  = Term.lambda wF (mkConj (signD (mT, wF, xT)) (le (add wF wF) mT))
    fun bd xp (hconj:thm) =
      let val hsg = conjunct1_r (signD (mT, xp, xT), le (add xp xp) mT) hconj
          val hbd = conjunct2_r (signD (mT, xp, xT), le (add xp xp) mT) hconj
      in k xp hsg hbd end
  in exE_r (P, goalC) ex wnm natT bd end;

val () = out "L4_SEAT1_WITH_SIGNED_OK\n";

(* The output body of signed_four_residue_sum (parameterised on m,a,b,c,d, with
   bound vars a4 b4 c4 d4 r4).  We build it via nested mkEx + mkConj. *)
fun srsBody mT aT bT cT dT a4 b4 c4 d4 r4 =
  mkConj
    (oeq (add (add (sq a4)(sq b4)) (add (sq c4)(sq d4))) (mult mT r4))
    (mkConj (signD (mT, a4, aT))
      (mkConj (signD (mT, b4, bT))
        (mkConj (signD (mT, c4, cT))
          (mkConj (signD (mT, d4, dT))
            (mkConj (le (add a4 a4) mT)
              (mkConj (le (add b4 b4) mT)
                (mkConj (le (add c4 c4) mT)
                        (le (add d4 d4) mT))))))));

(* signed_four_residue_sum (m,a,b,c,d,N) hm hbody hN0 :
     hm : lt 0 m ; hbody : oeq N (a^2+b^2+c^2+d^2) ; hN0 : cong m N 0
     ==> EX a' b' c' d' r. srsBody (with the sign disjuncts + bounds). *)
fun signed_four_residue_sum (mT, aT, bT, cT, dT, nT) hm hbody hN0 =
  let
    val A4=Free("a4s",natT); val B4=Free("b4s",natT); val C4=Free("c4s",natT)
    val D4=Free("d4s",natT); val R4=Free("r4s",natT)
    val goalP_r = fn a' => fn b' => fn c' => fn d' =>
                    Term.lambda R4 (srsBody mT aT bT cT dT a' b' c' d' R4)
    val goalP_d = fn a' => fn b' => fn c' =>
                    Term.lambda D4 (mkEx (Term.lambda R4 (srsBody mT aT bT cT dT a' b' c' D4 R4)))
    val goalP_c = fn a' => fn b' =>
                    Term.lambda C4 (mkEx (Term.lambda D4 (mkEx (Term.lambda R4 (srsBody mT aT bT cT dT a' b' C4 D4 R4)))))
    val goalP_b = fn a' =>
                    Term.lambda B4 (mkEx (Term.lambda C4 (mkEx (Term.lambda D4 (mkEx (Term.lambda R4 (srsBody mT aT bT cT dT a' B4 C4 D4 R4)))))))
    val goalP_a = Term.lambda A4 (mkEx (Term.lambda B4 (mkEx (Term.lambda C4 (mkEx (Term.lambda D4 (mkEx (Term.lambda R4 (srsBody mT aT bT cT dT A4 B4 C4 D4 R4)))))))))
    val goalC = mkEx goalP_a
    fun finish a' hsa hba b' hsb hbb c' hsc hbc d' hsd hbd =
      let
        (* squared congs *)
        val sqa = sq_cong_from_signed (mT, a', aT) hsa   (* cong m (a'^2)(a^2) *)
        val sqb = sq_cong_from_signed (mT, b', bT) hsb
        val sqc = sq_cong_from_signed (mT, c', cT) hsc
        val sqd = sq_cong_from_signed (mT, d', dT) hsd
        (* cong m (a'^2+b'^2)(a^2+b^2), (c'^2+d'^2)(c^2+d^2), sum *)
        val cab = cong_add_g (mT, sq a', sq aT, sq b', sq bT) sqa sqb
        val ccd = cong_add_g (mT, sq c', sq cT, sq d', sq dT) sqc sqd
        val sumLHS = add (add (sq a')(sq b'))(add (sq c')(sq d'))
        val sumRHSab = add (sq aT)(sq bT)
        val sumRHScd = add (sq cT)(sq dT)
        val csum = cong_add_g (mT, add (sq a')(sq b'), sumRHSab, add (sq c')(sq d'), sumRHScd) cab ccd
        (* (a^2+b^2)+(c^2+d^2) = N (via hbody) *)
        val hbodyS = oeqSym_r2 hbody
        val cN = oeq_rw_r (Term.lambda (Free("zsfr",natT)) (cong mT sumLHS (Free("zsfr",natT))),
                           add sumRHSab sumRHScd, nT) hbodyS csum   (* cong m sumLHS N *)
        val csum0 = cong_trans_g (mT, sumLHS, nT, ZeroC) cN hN0      (* cong m sumLHS 0 *)
        val exMult = cong_zero_imp_mult (mT, sumLHS) csum0           (* EX r. sumLHS = m*r *)
        val Pr = Term.lambda (Free("rcm",natT)) (oeq sumLHS (mult mT (Free("rcm",natT))))
        fun bdr r (hr:thm) =
          let
            (* build the big conjunction: sum=m*r, signD a', signD b', signD c', signD d', 4 bounds *)
            val sgD = signD (mT, d', dT)
            val sgC = signD (mT, c', cT)
            val sgB = signD (mT, b', bT)
            val sgA = signD (mT, a', aT)
            val lA = le (add a' a') mT
            val lB = le (add b' b') mT
            val lC = le (add c' c') mT
            val lD = le (add d' d') mT
            val bounds = mkConj lA (mkConj lB (mkConj lC lD))
            val conjBounds = conjI_r (lA, mkConj lB (mkConj lC lD)) hba
                               (conjI_r (lB, mkConj lC lD) hbb
                                  (conjI_r (lC, lD) hbc hbd))
            val rest_after_d = mkConj sgD bounds
            val conj_d = conjI_r (sgD, bounds) hsd conjBounds
            val rest_after_c = mkConj sgC rest_after_d
            val conj_c = conjI_r (sgC, rest_after_d) hsc conj_d
            val rest_after_b = mkConj sgB rest_after_c
            val conj_b = conjI_r (sgB, rest_after_c) hsb conj_c
            val rest_after_a = mkConj sgA rest_after_b
            val conj_a = conjI_r (sgA, rest_after_b) hsa conj_b
            val sumEq = oeq sumLHS (mult mT r)
            val bigConj = conjI_r (sumEq, rest_after_a) hr conj_a
            (* nested exI : r, d', c', b', a' *)
            val e1 = exI_r (goalP_r a' b' c' d') r bigConj
            val e2 = exI_r (goalP_d a' b' c') d' e1
            val e3 = exI_r (goalP_c a' b') c' e2
            val e4 = exI_r (goalP_b a') b' e3
            val e5 = exI_r goalP_a a' e4
          in e5 end
      in exE_r (Pr, goalC) exMult "r_sfr" natT bdr end
  in
    with_signed "asig" (mT, aT) hm (fn a' => fn hsa => fn hba =>
      with_signed "bsig" (mT, bT) hm (fn b' => fn hsb => fn hbb =>
        with_signed "csig" (mT, cT) hm (fn c' => fn hsc => fn hbc =>
          with_signed "dsig" (mT, dT) hm (fn d' => fn hsd => fn hbd =>
            finish a' hsa hba b' hsb hbb c' hsc hbc d' hsd hbd) goalC) goalC) goalC) goalC
  end;
val () = out "L4_SIGNED_FOUR_RESIDUE_SUM_DEFINED\n";

(* smoke : build a 0-hyp discharged version and check hyps *)
val signed_four_residue_sum_thm =
  let
    val mF=Free("m_sf",natT); val aF=Free("a_sf",natT); val bF=Free("b_sf",natT)
    val cF=Free("c_sf",natT); val dF=Free("d_sf",natT); val nF=Free("N_sf",natT)
    val hmP = jT (lt ZeroC mF); val hm = Thm.assume (ctermGR hmP)
    val hbodyP = jT (oeq nF (add (add (mult aF aF)(mult bF bF))(add (mult cF cF)(mult dF dF))))
    val hbody = Thm.assume (ctermGR hbodyP)
    val hN0P = jT (cong mF nF ZeroC); val hN0 = Thm.assume (ctermGR hN0P)
    val r = signed_four_residue_sum (mF,aF,bF,cF,dF,nF) hm hbody hN0
  in Thm.implies_intr (ctermGR hmP) (Thm.implies_intr (ctermGR hbodyP) (Thm.implies_intr (ctermGR hN0P) r)) end;
val () = out ("signed_four_residue_sum hyps="^Int.toString(length(Thm.hyps_of signed_four_residue_sum_thm))^"\n");
val () = out ("signed_FRS prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of signed_four_residue_sum_thm)^"\n");
val () = out "L4_SEAT1_PHASE_A_DONE\n";

(* ---------- GR dvd helpers ---------- *)
fun dvd_intro_r (aT, bT, w) hyp =   (* hyp : oeq b (mult a w) ==> dvd a b *)
  exI_r (Abs("k", natT, oeq bT (mult aT (Bound 0)))) w hyp;
val dvd_add_vGR  = varify dvd_add;
val dvd_trans_vGR= varify dvd_trans;
fun dvd_add_r (dT, mT, nT) h1 h2 =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("d",0), ctermGR dT),(("m",0), ctermGR mT),(("n",0), ctermGR nT)] dvd_add_vGR)) h1) h2;
fun dvd_trans_r (aT, bT, cT) h1 h2 =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("a",0), ctermGR aT),(("b",0), ctermGR bT),(("c",0), ctermGR cT)] dvd_trans_vGR)) h1) h2;
fun Suc_neq_Zero_r nt heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("n",0), ctermGR nt)] Suc_neq_Zero_vR2)) heq;
val () = out "L4_SEAT1_DVD_HELPERS_OK\n";

(* sq_eq_zero_r (x) : oeq (x*x) 0 ==> oeq x 0
   num-cases on x: x=0 done; x=Suc k -> (Suc k)*(Suc k)=Suc(...)=0 absurd. *)
fun sq_eq_zero_r xT hsq =     (* hsq : oeq (x*x) 0 *)
  let
    val dz = dzos_d xT     (* Disj (oeq x 0)(Ex k. x = Suc k) *)
    val goalC = oeq xT ZeroC
    val caseZ =
      let val hP = jT (oeq xT ZeroC)
          val h  = Thm.assume (ctermGR hP)
      in Thm.implies_intr (ctermGR hP) h end
    val caseS =
      let
        val Pk = Abs("k", natT, oeq xT (suc (Bound 0)))
        val hP = jT (mkEx Pk)
        val h  = Thm.assume (ctermGR hP)
        fun bd k (hk:thm) =   (* hk : oeq x (Suc k) *)
          let
            (* x*x = (Suc k)*(Suc k) = Suc(k + k*(Suc k)) ; = 0 absurd *)
            val c1 = mult_cong_l_g (xT, suc k, xT) hk      (* x*x = (Suc k)*x *)
            val c2 = mult_cong_r_g (suc k, xT, suc k) hk    (* (Suc k)*x = (Suc k)*(Suc k) *)
            val xxSS = oeqTrans_r2 (c1, c2)                 (* x*x = (Suc k)*(Suc k) *)
            val ms   = multSuc_d (k, suc k)                 (* (Suc k)*(Suc k) = (Suc k) + k*(Suc k) *)
            val xxe  = oeqTrans_r2 (xxSS, ms)               (* x*x = (Suc k) + k*(Suc k) *)
            val addS = addSuc_d (k, mult k (suc k))         (* (Suc k) + k*(Suc k) = Suc(k + k*(Suc k)) *)
            val xxS  = oeqTrans_r2 (xxe, addS)              (* x*x = Suc(k + k*(Suc k)) *)
            val Seq0 = oeqTrans_r2 (oeqSym_r2 xxS, hsq)     (* Suc(...) = 0 *)
            val fls  = Suc_neq_Zero_r (add k (mult k (suc k))) Seq0
          in Thm.implies_elim (oFalse_elim_r goalC) fls end
      in Thm.implies_intr (ctermGR hP) (exE_r (Pk, goalC) h "kszr" natT bd) end
  in disjE_r (oeq xT ZeroC, mkEx (Abs("k",natT, oeq xT (suc (Bound 0)))), goalC) dz caseZ caseS end;
val () = out "L4_SEAT1_SQ_EQ_ZERO_OK\n";

(* dvd_m_of_signed_zero (m, x) hsign hx0 :
     hsign : signD m x' x  with x' the witness ; hx0 : oeq x' 0
     ==> dvd m x
   We pass the SIGN as (cong m x' x OR cong m (x'+x) 0) and x'=0 separately.
   After x'=0: LEFT -> cong m 0 x -> sym -> cong m x 0 ; RIGHT -> cong m (0+x) 0 -> rewrite -> cong m x 0.
   Then cong m x 0 -> cong_zero_imp_mult -> EX r. x = m*r -> dvd m x. *)
fun dvd_of_cong_zero (mT, xT) hcong =    (* hcong : cong m x 0 ==> dvd m x *)
  let
    val exm = cong_zero_imp_mult (mT, xT) hcong   (* EX r. oeq x (mult m r) *)
    (* that existential IS dvd m x (same body) *)
  in exm end;
val () = out "L4_SEAT1_DVD_OF_CONGZERO_OK\n";

(* dvd_msq_of_dvd_m (m, x) hdvd : dvd m x ==> dvd (m*m) (x*x)
   hdvd : EX u. x = m*u.  x*x = (m*u)*(m*u) = (m*m)*(u*u). witness u*u. *)
fun dvd_msq_of_dvd_m (mT, xT) hdvd =
  let
    val goalC = dvd (mult mT mT) (mult xT xT)
    val P = Abs("u", natT, oeq xT (mult mT (Bound 0)))
    fun bd u (hu:thm) =   (* hu : oeq x (m*u) *)
      let
        val c1 = mult_cong_l_g (xT, mult mT u, xT) hu       (* x*x = (m*u)*x *)
        val c2 = mult_cong_r_g (mult mT u, xT, mult mT u) hu (* (m*u)*x = (m*u)*(m*u) *)
        val xx = oeqTrans_r2 (c1, c2)                        (* x*x = (m*u)*(m*u) *)
        val idP = proveIdentityG (mult (mult mT u)(mult mT u)) (mult (mult mT mT)(mult u u))
        val xxe = oeqTrans_r2 (xx, idP)                      (* x*x = (m*m)*(u*u) *)
      in dvd_intro_r (mult mT mT, mult xT xT, mult u u) xxe end
  in exE_r (P, goalC) hdvd "u_dvdsq" natT bd end;
val () = out "L4_SEAT1_DVD_MSQ_OK\n";

val () = out "L4_SEAT1_PHASE_B_HELPERS_DONE\n";

(* ---------- ordering helpers for step (c) ---------- *)
val nlt_le_vGR = varify nlt_le;
fun nlt_le_r (dt,ct) hneg =      (* neg(lt d c) ==> le c d *)
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("d",0), ctermGR dt),(("c",0), ctermGR ct)] nlt_le_vGR)) hneg;

(* nle_lt_r (a,b) : neg(le a b) ==> lt b a *)
fun nle_lt_r (aT,bT) hnle =
  let
    val goalC = lt bT aT
    val em = em_r (lt bT aT)        (* Disj (lt b a)(neg(lt b a)) *)
    val cA = let val hP = jT (lt bT aT); val h = Thm.assume (ctermGR hP)
             in Thm.implies_intr (ctermGR hP) h end
    val cB = let val hP = jT (neg (lt bT aT)); val h = Thm.assume (ctermGR hP)
                 val leab = nlt_le_r (bT, aT) h            (* le a b *)
                 val fls  = mp_r (le aT bT, oFalseC) hnle leab   (* oFalse *)
             in Thm.implies_intr (ctermGR hP) (Thm.implies_elim (oFalse_elim_r goalC) fls) end
  in disjE_r (lt bT aT, neg (lt bT aT), goalC) em cA cB end;

(* 0<m as Suc form : from lt 0 m, get (m0, oeq m (Suc m0)) via dzos *)
(* mult_lt_mono_l (m) hm_pos (a,b) hlt : 0<m, lt a b ==> lt (m*a)(m*b) *)
fun mult_lt_mono_l mT hmPos (aT,bT) hlt =
  let
    (* hlt : le (Suc a) b ; mult_le_mono_g (m, Suc a, b) : le (m*(Suc a))(m*b) *)
    val lmm = mult_le_mono_g (mT, suc aT, bT) hlt        (* le (m*(Suc a))(m*b) *)
    (* mult_Suc_right : m*(Suc a) = m + m*a *)
    val msr = multSucr_d (mT, aT)                          (* m*(Suc a) = m + m*a *)
    val dzm = dzos_d mT
    val goalLe = le (suc (mult mT aT)) (mult mT (suc aT))
    val Pk = Abs("k", natT, oeq mT (suc (Bound 0)))
    val leStep =
      let
        val hP = jT (mkEx Pk); val h = Thm.assume (ctermGR hP)
        fun bd m0 (hm0:thm) =   (* hm0 : oeq m (Suc m0) *)
          let
            (* m + m*a = Suc m0 + m*a = Suc(m0 + m*a) *)
            val c1 = add_cong_l_d (mT, suc m0, mult mT aT) hm0     (* m + m*a = Suc m0 + m*a *)
            val aS = addSuc_d (m0, mult mT aT)                    (* Suc m0 + m*a = Suc(m0 + m*a) *)
            val mSa = oeqTrans_r2 (msr, oeqTrans_r2 (c1, aS))      (* m*(Suc a) = Suc(m0 + m*a) *)
            (* le (Suc(m*a))(Suc(m0+m*a)) : Suc(m0+m*a) = Suc(m*a) + m0
                 Suc(m*a) + m0 = Suc(m*a + m0) [addSuc] ; m*a+m0 = m0+m*a [comm] ;
                 so Suc(m*a)+m0 = Suc(m0+m*a). witness m0. *)
            val addsuc = addSuc_d (mult mT aT, m0)                 (* Suc(m*a) + m0 = Suc(m*a+m0) *)
            val commin = Suc_cong OF [addcomm_d (mult mT aT, m0)]  (* Suc(m*a+m0) = Suc(m0+m*a) *)
            val sumeq  = oeqTrans_r2 (addsuc, commin)              (* Suc(m*a)+m0 = Suc(m0+m*a) *)
            val leW = le_intro_d (suc (mult mT aT), suc (add m0 (mult mT aT)), m0)
                        (oeqSym_r2 sumeq)                           (* le (Suc(m*a))(Suc(m0+m*a)) *)
            val leW2 = oeq_rw_r (Term.lambda (Free("zml",natT)) (le (suc (mult mT aT)) (Free("zml",natT))),
                                 suc (add m0 (mult mT aT)), mult mT (suc aT)) (oeqSym_r2 mSa) leW
          in leW2 end
      in disjE_r (oeq mT ZeroC, mkEx Pk, goalLe)
           dzm
           (let val hP=jT (oeq mT ZeroC); val h=Thm.assume (ctermGR hP)
                (* m=0 contradicts 0<m *)
                val ltmm = oeq_rw_r (Term.lambda (Free("zz",natT)) (lt ZeroC (Free("zz",natT))), mT, ZeroC) h hmPos
                val fls = lt_irrefl_r ZeroC ltmm
            in Thm.implies_intr (ctermGR hP) (Thm.implies_elim (oFalse_elim_r goalLe) fls) end)
           (Thm.implies_intr (ctermGR (jT (mkEx Pk))) (exE_r (Pk, goalLe) h "m0mlm" natT bd))
      end
  in le_trans_d (suc (mult mT aT), mult mT (suc aT), mult mT bT) leStep lmm end
  (* result : le (Suc(m*a))(m*b) = lt (m*a)(m*b) *)
  ;
val () = out "L4_SEAT1_MULTLT_DEFINED\n";

(* mult_le_cancel_l mT hmPos (aT,bT) hle : 0<m, le(m*a)(m*b) ==> le a b *)
fun mult_le_cancel_l mT hmPos (aT,bT) hle =
  let
    val goalC = le aT bT
    val em = em_r (le aT bT)
    val cA = let val hP=jT (le aT bT); val h=Thm.assume (ctermGR hP)
             in Thm.implies_intr (ctermGR hP) h end
    val cB = let val hP=jT (neg (le aT bT)); val h=Thm.assume (ctermGR hP)
                 val ltba = nle_lt_r (aT,bT) h           (* lt b a *)
                 val ltmba = mult_lt_mono_l mT hmPos (bT,aT) ltba   (* lt (m*b)(m*a) *)
                 (* le(m*a)(m*b) and lt(m*b)(m*a) -> lt(m*b)(m*b) -> False *)
                 val ltmm = le_lt_trans (mult mT aT, mult mT bT, mult mT aT) hle ltmba (* lt(m*a)(m*a)? *)
                 (* careful: le(m*a)(m*b) then lt(m*b)(m*a): le_lt_trans (m*a)(m*b)(m*a) -> lt(m*a)(m*a) *)
                 val fls = lt_irrefl_r (mult mT aT) ltmm
             in Thm.implies_intr (ctermGR hP) (Thm.implies_elim (oFalse_elim_r goalC) fls) end
  in disjE_r (le aT bT, neg (le aT bT), goalC) em cA cB end;
val () = out "L4_SEAT1_MULTLECANCEL_DEFINED\n";

(* smokes *)
val () =
  let val mF=Free("m_sm",natT); val aF=Free("a_sm",natT); val bF=Free("b_sm",natT)
      val hpos = Thm.assume (ctermGR (jT (lt ZeroC mF)))
      val hlt  = Thm.assume (ctermGR (jT (lt aF bF)))
      val r = mult_lt_mono_l mF hpos (aF,bF) hlt
  in out ("SMOKE mult_lt_mono_l hyps="^Int.toString(length(Thm.hyps_of r))
          ^" prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)^"\n") end
  handle e => out ("SMOKE mult_lt_mono_l FAIL "^exnMessage e^"\n");
val () =
  let val mF=Free("m_sm2",natT); val aF=Free("a_sm2",natT); val bF=Free("b_sm2",natT)
      val hpos = Thm.assume (ctermGR (jT (lt ZeroC mF)))
      val hle  = Thm.assume (ctermGR (jT (le (mult mF aF)(mult mF bF))))
      val r = mult_le_cancel_l mF hpos (aF,bF) hle
  in out ("SMOKE mult_le_cancel_l hyps="^Int.toString(length(Thm.hyps_of r))
          ^" prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)^"\n") end
  handle e => out ("SMOKE mult_le_cancel_l FAIL "^exnMessage e^"\n");

val () = out "L4_SEAT1_PHASE_C_HELPERS_DONE\n";

(* ============================================================================
   (b) r=0 EXCLUSION machinery.
   ============================================================================ *)
(* prime2 destructor on GR : prime2 p -> dvd d p -> Disj(oeq d 1)(oeq d p) *)
fun prime2_div_r (p, d) hPrime hDvdDP =
  let
    val faThm = conjunct2_r (lt (suc ZeroC) p, mkForall (ppAbs p)) hPrime
    val impAt = allE_r (ppAbs p) d faThm
  in mp_r (dvd d p, mkDisj (oeq d (suc ZeroC)) (oeq d p)) impAt hDvdDP end;
val () = out "L4_SEAT1_PRIME2DIV_OK\n";

(* m_dvd_p_contra : dvd m p -> prime2 p -> lt 1 m -> lt m p -> oFalse
     dvd m p -> m=1 or m=p ; m=1 contradicts 1<m ; m=p contradicts m<p. *)
fun m_dvd_p_contra (mT, pT) hdvd hPrime h1m hmp =
  let
    val dj = prime2_div_r (pT, mT) hPrime hdvd       (* Disj(oeq m 1)(oeq m p) *)
    val goalC = oFalseC
    val cA =
      let val hP = jT (oeq mT (suc ZeroC)); val h = Thm.assume (ctermGR hP)
          (* m=1, 1<m=lt 1 m -> lt 1 1 -> irrefl ; rewrite m->1 in (lt 1 m) *)
          val lt11 = oeq_rw_r (Term.lambda (Free("zc1",natT)) (lt (suc ZeroC) (Free("zc1",natT))), mT, suc ZeroC) h h1m
          val fls  = lt_irrefl_r (suc ZeroC) lt11
      in Thm.implies_intr (ctermGR hP) fls end
    val cB =
      let val hP = jT (oeq mT pT); val h = Thm.assume (ctermGR hP)
          (* m=p, m<p -> p<p -> irrefl ; rewrite m->p in (lt m p) *)
          val ltpp = oeq_rw_r (Term.lambda (Free("zc2",natT)) (lt (Free("zc2",natT)) pT), mT, pT) h hmp
          val fls  = lt_irrefl_r pT ltpp
      in Thm.implies_intr (ctermGR hP) fls end
  in disjE_r (oeq mT (suc ZeroC), oeq mT pT, goalC) dj cA cB end;
val () = out "L4_SEAT1_MDVDP_CONTRA_OK\n";

(* dvd_m_x_from_signed (m, x', x) hsign hx'0 : signD(m,x',x), oeq x' 0  -> dvd m x *)
fun dvd_m_x_from_signed (mT, xpT, xT) hsign hx0 =
  let
    val goalC = dvd mT xT
    (* rewrite x' -> 0 in the disjunction *)
    val P = Term.lambda (Free("zsg",natT)) (mkDisj (cong mT (Free("zsg",natT)) xT) (cong mT (add (Free("zsg",natT)) xT) ZeroC))
    val sign0 = oeq_rw_r (P, xpT, ZeroC) hx0 hsign   (* Disj(cong m 0 x)(cong m (0+x) 0) *)
    val cL =
      let val hP = jT (cong mT ZeroC xT); val h = Thm.assume (ctermGR hP)
          val cx0 = cong_sym_g (mT, ZeroC, xT) h       (* cong m x 0 *)
          val dvdmx = dvd_of_cong_zero (mT, xT) cx0     (* dvd m x *)
      in Thm.implies_intr (ctermGR hP) dvdmx end
    val cR =
      let val hP = jT (cong mT (add ZeroC xT) ZeroC); val h = Thm.assume (ctermGR hP)
          (* rewrite 0+x -> x *)
          val zx = add0_d xT                              (* 0+x = x *)
          val cx0 = oeq_rw_r (Term.lambda (Free("zsg2",natT)) (cong mT (Free("zsg2",natT)) ZeroC), add ZeroC xT, xT) zx h
          val dvdmx = dvd_of_cong_zero (mT, xT) cx0
      in Thm.implies_intr (ctermGR hP) dvdmx end
  in disjE_r (cong mT ZeroC xT, cong mT (add ZeroC xT) ZeroC, goalC) sign0 cL cR end;
val () = out "L4_SEAT1_DVD_FROM_SIGNED_OK\n";

val () = out "L4_SEAT1_PHASE_B2_HELPERS_DONE\n";

(* oeq_imp_le_r (a,b) : oeq a b ==> le a b   (witness 0 : b = a + 0) *)
fun oeq_imp_le_r (aT,bT) heq =
  let val b_a0 = oeqTrans_r2 (oeqSym_r2 heq, oeqSym_r2 (add0r_d aT))  (* b = a = a+0 *)
  in le_intro_d (aT, bT, ZeroC) b_a0 end;

(* le_antisym at GR *)
val le_antisym_vGR = varify le_antisym;
fun le_antisym_r (mT,nT) h1 h2 =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("m",0), ctermGR mT),(("n",0), ctermGR nT)] le_antisym_vGR)) h1) h2;

(* mult_left_cancel_r m hmPos (a,b) : oeq (m*a)(m*b) ==> oeq a b *)
fun mult_left_cancel_r mT hmPos (aT,bT) heq =
  let
    val leAB = mult_le_cancel_l mT hmPos (aT,bT) (oeq_imp_le_r (mult mT aT, mult mT bT) heq)
    val leBA = mult_le_cancel_l mT hmPos (bT,aT) (oeq_imp_le_r (mult mT bT, mult mT aT) (oeqSym_r2 heq))
  in le_antisym_r (aT,bT) leAB leBA end;
val () = out "L4_SEAT1_MULTLCANCEL_OK\n";

(* dvd_msq_cancel m hmPos (p) hdvd : dvd (m*m)(m*p) ==> dvd m p
   hdvd : EX k. m*p = (m*m)*k.  (m*m)*k = m*(m*k) [assoc]. cancel m -> p = m*k. *)
fun dvd_msq_cancel mT hmPos pT hdvd =
  let
    val goalC = dvd mT pT
    val P = Abs("k", natT, oeq (mult mT pT) (mult (mult mT mT) (Bound 0)))
    fun bd k (hk:thm) =   (* hk : oeq (m*p) ((m*m)*k) *)
      let
        val assoc = multassoc_g (mT, mT, k)            (* (m*m)*k = m*(m*k) *)
        val mp_eq = oeqTrans_r2 (hk, assoc)             (* m*p = m*(m*k) *)
        val p_eq  = mult_left_cancel_r mT hmPos (pT, mult mT k) mp_eq  (* p = m*k *)
      in dvd_intro_r (mT, pT, k) p_eq end
  in exE_r (P, goalC) hdvd "k_msqc" natT bd end;
val () = out "L4_SEAT1_DVD_MSQ_CANCEL_OK\n";

val () = out "L4_SEAT1_PHASE_B3_HELPERS_DONE\n";

(* ============================================================================
   r0_excl : assuming r=0, derive oFalse.
   Inputs (all on ctxtGR):
     mT,pT,rT, a,b,c,d (orig coords), ap,bp,cp,dp (residue witnesses)
     hsum  : oeq (ap^2+bp^2+cp^2+dp^2) (m*r)
     hsa..hsd : signD m ap a , ... (sign disjunctions)
     hbodyP : oeq (m*p) (a^2+b^2+c^2+d^2)
     hPrime : prime2 p ; h1m : lt 1 m ; hmp : lt m p ; hmPos : lt 0 m
     hr0 : oeq r 0
   ============================================================================ *)
fun r0_excl (mT,pT,rT, a,b,c,d, ap,bp,cp,dp)
            hsum hsa hsb hsc hsd hbodyP hPrime h1m hmp hmPos hr0 =
  let
    (* sumLHS = m*r = m*0 = 0 *)
    val sumLHS = add (add (sq ap)(sq bp)) (add (sq cp)(sq dp))
    val mr0 = mult_cong_r_d (mT, rT, ZeroC) hr0      (* m*r = m*0 *)
    val m0z = mult0r_d mT                              (* m*0 = 0 *)
    val sum0 = oeqTrans_r2 (hsum, oeqTrans_r2 (mr0, m0z))   (* sumLHS = 0 *)
    (* (ap^2+bp^2)+(cp^2+dp^2) = 0 -> ap^2+bp^2 = 0  (add_eq_zero_left) *)
    val ab0 = add_eq_zero_left_d (add (sq ap)(sq bp), add (sq cp)(sq dp)) sum0  (* ap^2+bp^2 = 0 *)
    (* need cp^2+dp^2 = 0 too : sum0 sym + addcomm then add_eq_zero_left *)
    val sumComm = oeqTrans_r2 (addcomm_d (add (sq cp)(sq dp), add (sq ap)(sq bp)), sum0)
                  (* (cp^2+dp^2)+(ap^2+bp^2) = 0 *)
    val cd0 = add_eq_zero_left_d (add (sq cp)(sq dp), add (sq ap)(sq bp)) sumComm  (* cp^2+dp^2 = 0 *)
    val ap2_0 = add_eq_zero_left_d (sq ap, sq bp) ab0     (* ap^2 = 0 *)
    val bp2_0 = add_eq_zero_left_d (sq bp, sq ap) (oeqTrans_r2 (addcomm_d (sq bp, sq ap), ab0))  (* bp^2=0 *)
    val cp2_0 = add_eq_zero_left_d (sq cp, sq dp) cd0     (* cp^2=0 *)
    val dp2_0 = add_eq_zero_left_d (sq dp, sq cp) (oeqTrans_r2 (addcomm_d (sq dp, sq cp), cd0))  (* dp^2=0 *)
    val ap0 = sq_eq_zero_r ap ap2_0   (* ap=0 *)
    val bp0 = sq_eq_zero_r bp bp2_0
    val cp0 = sq_eq_zero_r cp cp2_0
    val dp0 = sq_eq_zero_r dp dp2_0
    (* dvd m a,b,c,d *)
    val dma = dvd_m_x_from_signed (mT, ap, a) hsa ap0
    val dmb = dvd_m_x_from_signed (mT, bp, b) hsb bp0
    val dmc = dvd_m_x_from_signed (mT, cp, c) hsc cp0
    val dmd = dvd_m_x_from_signed (mT, dp, d) hsd dp0
    (* dvd (m*m)(x^2) *)
    val dma2 = dvd_msq_of_dvd_m (mT, a) dma
    val dmb2 = dvd_msq_of_dvd_m (mT, b) dmb
    val dmc2 = dvd_msq_of_dvd_m (mT, c) dmc
    val dmd2 = dvd_msq_of_dvd_m (mT, d) dmd
    (* dvd (m*m)(a^2+b^2+c^2+d^2) via dvd_add *)
    val dmab = dvd_add_r (mult mT mT, sq a, sq b) dma2 dmb2     (* dvd m^2 (a^2+b^2) *)
    val dmcd = dvd_add_r (mult mT mT, sq c, sq d) dmc2 dmd2     (* dvd m^2 (c^2+d^2) *)
    val dmAll = dvd_add_r (mult mT mT, add (sq a)(sq b), add (sq c)(sq d)) dmab dmcd
                (* dvd m^2 ((a^2+b^2)+(c^2+d^2)) *)
    (* (a^2+b^2)+(c^2+d^2) = m*p (hbodyP sym) -> dvd m^2 (m*p) *)
    val bodyMP = add (add (sq a)(sq b))(add (sq c)(sq d))
    val dmMP = oeq_rw_r (Term.lambda (Free("zdv",natT)) (dvd (mult mT mT) (Free("zdv",natT))),
                         bodyMP, mult mT pT) (oeqSym_r2 hbodyP) dmAll   (* dvd m^2 (m*p) *)
    val dmP = dvd_msq_cancel mT hmPos pT dmMP        (* dvd m p *)
  in m_dvd_p_contra (mT, pT) dmP hPrime h1m hmp end;
val () = out "L4_SEAT1_R0_EXCL_DEFINED\n";

(* smoke r0_excl : assume all hyps, build oFalse *)
val () =
  let
    val mF=Free("mE",natT); val pF=Free("pE",natT); val rF=Free("rE",natT)
    val aF=Free("aE",natT); val bF=Free("bE",natT); val cF=Free("cE",natT); val dF=Free("dE",natT)
    val apF=Free("apE",natT); val bpF=Free("bpE",natT); val cpF=Free("cpE",natT); val dpF=Free("dpE",natT)
    val sumLHS = add (add (sq apF)(sq bpF)) (add (sq cpF)(sq dpF))
    val hsum = Thm.assume (ctermGR (jT (oeq sumLHS (mult mF rF))))
    val hsa = Thm.assume (ctermGR (jT (signD (mF, apF, aF))))
    val hsb = Thm.assume (ctermGR (jT (signD (mF, bpF, bF))))
    val hsc = Thm.assume (ctermGR (jT (signD (mF, cpF, cF))))
    val hsd = Thm.assume (ctermGR (jT (signD (mF, dpF, dF))))
    val hbodyP = Thm.assume (ctermGR (jT (oeq (mult mF pF) (add (add (sq aF)(sq bF))(add (sq cF)(sq dF))))))
    val hPrime = Thm.assume (ctermGR (jT (prime2 pF)))
    val h1m = Thm.assume (ctermGR (jT (lt (suc ZeroC) mF)))
    val hmp = Thm.assume (ctermGR (jT (lt mF pF)))
    val hmPos = Thm.assume (ctermGR (jT (lt ZeroC mF)))
    val hr0 = Thm.assume (ctermGR (jT (oeq rF ZeroC)))
    val r = r0_excl (mF,pF,rF, aF,bF,cF,dF, apF,bpF,cpF,dpF)
              hsum hsa hsb hsc hsd hbodyP hPrime h1m hmp hmPos hr0
  in out ("SMOKE r0_excl prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)
          ^" hyps="^Int.toString(length(Thm.hyps_of r))^"\n") end
  handle e => out ("SMOKE r0_excl FAIL "^exnMessage e^"\n");
val () = out "L4_SEAT1_PHASE_B_DONE\n";

(* ============================================================================
   (c) r <= m  (the AM bound).
   ============================================================================ *)
(* add_lt_le_mono (a,b,c,d) : lt a b ==> le c d ==> lt (a+c)(b+d) *)
fun add_lt_le_mono (aT,bT,cT,dT) hlt hle =
  let
    val lm = add_le_mono (suc aT, bT, cT, dT) hlt hle    (* le (Suc a + c)(b+d) *)
    val asuc = addSuc_d (aT, cT)                          (* Suc a + c = Suc(a+c) *)
    val lm2 = oeq_rw_r (Term.lambda (Free("zalm",natT)) (le (Free("zalm",natT)) (add bT dT)), add (suc aT) cT, suc (add aT cT)) asuc lm
  in lm2 end;  (* le (Suc(a+c))(b+d) = lt (a+c)(b+d) *)

fun quadT X = add X (add X (add X X));

(* add4_lt_mono (a,b) : lt a b ==> lt (quad a)(quad b) *)
fun add4_lt_mono (aT,bT) hlt =
  let
    val laeb = lt_imp_le_r (aT,bT) hlt
    val l2 = le_addsame (aT,bT) laeb                       (* le (a+a)(b+b) *)
    val l3 = add_lt_le_mono (aT,bT, add aT aT, add bT bT) hlt l2   (* lt (a+(a+a))(b+(b+b)) *)
    val l3le = lt_imp_le_r (add aT (add aT aT), add bT (add bT bT)) l3
    val l4 = add_lt_le_mono (aT,bT, add aT (add aT aT), add bT (add bT bT)) hlt l3le
  in l4 end;   (* lt (quad a)(quad b) *)

(* add4_le_cancel (a,b) : le (quad a)(quad b) ==> le a b *)
fun add4_le_cancel (aT,bT) hle =
  let
    val goalC = le aT bT
    val em = em_r (le aT bT)
    val cA = let val hP=jT (le aT bT); val h=Thm.assume (ctermGR hP) in Thm.implies_intr (ctermGR hP) h end
    val cB = let val hP=jT (neg (le aT bT)); val h=Thm.assume (ctermGR hP)
                 val ltba = nle_lt_r (aT,bT) h                 (* lt b a *)
                 val ltq  = add4_lt_mono (bT,aT) ltba          (* lt (quad b)(quad a) *)
                 val ltqq = le_lt_trans (quadT aT, quadT bT, quadT aT) hle ltq  (* lt(quad a)(quad a) *)
                 val fls = lt_irrefl_r (quadT aT) ltqq
             in Thm.implies_intr (ctermGR hP) (Thm.implies_elim (oFalse_elim_r goalC) fls) end
  in disjE_r (le aT bT, neg (le aT bT), goalC) em cA cB end;
val () = out "L4_SEAT1_ADD4_HELPERS_OK\n";

(* r_le_m : from hsum : oeq sumLHS (m*r) and 4 bounds le(2x')m, 0<m  ==> le r m *)
fun r_le_m (mT,rT, ap,bp,cp,dp) hsum hba hbb hbc hbd hmPos =
  let
    val sumLHS = add (add (sq ap)(sq bp)) (add (sq cp)(sq dp))
    (* each (x'+x')^2 <= m^2 *)
    val sa = sq_le (add ap ap, mT) hba    (* le ((ap+ap)^2)(m*m) *)
    val sb = sq_le (add bp bp, mT) hbb
    val sc = sq_le (add cp cp, mT) hbc
    val sd = sq_le (add dp dp, mT) hbd
    (* sum the four squares-bounds via add_le_mono : le (Sab) (m^2+m^2) etc. *)
    val sab = add_le_mono (sq (add ap ap), mult mT mT, sq (add bp bp), mult mT mT) sa sb
              (* le ((ap+ap)^2 + (bp+bp)^2)(m^2 + m^2) *)
    val scd = add_le_mono (sq (add cp cp), mult mT mT, sq (add dp dp), mult mT mT) sc sd
    val ssum = add_le_mono (add (sq (add ap ap))(sq (add bp bp)), add (mult mT mT)(mult mT mT),
                            add (sq (add cp cp))(sq (add dp dp)), add (mult mT mT)(mult mT mT)) sab scd
               (* le (Lsum)(quad-ish m^2) where RHS = (m^2+m^2)+(m^2+m^2) *)
    val Lsum = add (add (sq (add ap ap))(sq (add bp bp))) (add (sq (add cp cp))(sq (add dp dp)))
    val Rsum = add (add (mult mT mT)(mult mT mT)) (add (mult mT mT)(mult mT mT))
    (* identity : Lsum = quad sumLHS  (each (x+x)^2 = 4 x^2 ; sum = 4 sumLHS = quad sumLHS) *)
    val idL = proveIdentityG Lsum (quadT sumLHS)        (* oeq Lsum (quad sumLHS) *)
    val idR = proveIdentityG Rsum (quadT (mult mT mT))  (* oeq Rsum (quad (m*m)) *)
    (* rewrite ssum LHS and RHS *)
    val ss1 = oeq_rw_r (Term.lambda (Free("zrl1",natT)) (le (Free("zrl1",natT)) Rsum), Lsum, quadT sumLHS) idL ssum
    val ss2 = oeq_rw_r (Term.lambda (Free("zrl2",natT)) (le (quadT sumLHS) (Free("zrl2",natT))), Rsum, quadT (mult mT mT)) idR ss1
              (* le (quad sumLHS)(quad (m*m)) *)
    val canc4 = add4_le_cancel (sumLHS, mult mT mT) ss2     (* le sumLHS (m*m) *)
    (* rewrite sumLHS = m*r *)
    val canc4b = oeq_rw_r (Term.lambda (Free("zrl3",natT)) (le (Free("zrl3",natT)) (mult mT mT)), sumLHS, mult mT rT) hsum canc4
                 (* le (m*r)(m*m) *)
    val le_rm = mult_le_cancel_l mT hmPos (rT, mT) canc4b  (* le r m *)
  in le_rm end;
val () = out "L4_SEAT1_R_LE_M_DEFINED\n";

(* smoke r_le_m *)
val () =
  let
    val mF=Free("mL",natT); val rF=Free("rL",natT)
    val apF=Free("apL",natT); val bpF=Free("bpL",natT); val cpF=Free("cpL",natT); val dpF=Free("dpL",natT)
    val sumLHS = add (add (sq apF)(sq bpF)) (add (sq cpF)(sq dpF))
    val hsum = Thm.assume (ctermGR (jT (oeq sumLHS (mult mF rF))))
    val hba = Thm.assume (ctermGR (jT (le (add apF apF) mF)))
    val hbb = Thm.assume (ctermGR (jT (le (add bpF bpF) mF)))
    val hbc = Thm.assume (ctermGR (jT (le (add cpF cpF) mF)))
    val hbd = Thm.assume (ctermGR (jT (le (add dpF dpF) mF)))
    val hmPos = Thm.assume (ctermGR (jT (lt ZeroC mF)))
    val r = r_le_m (mF,rF, apF,bpF,cpF,dpF) hsum hba hbb hbc hbd hmPos
  in out ("SMOKE r_le_m prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)^" hyps="^Int.toString(length(Thm.hyps_of r))^"\n") end
  handle e => out ("SMOKE r_le_m FAIL "^exnMessage e^"\n");
val () = out "L4_SEAT1_PHASE_C_DONE\n";

(* lt_0_suc_r r0 : lt 0 (Suc r0) *)
fun lt_0_suc_r r0 =
  let
    (* Suc r0 = (Suc 0) + r0 :  (Suc 0)+r0 = Suc(0+r0) = Suc r0 *)
    val aS = addSuc_d (ZeroC, r0)             (* (Suc 0)+r0 = Suc(0+r0) *)
    val z0 = Suc_cong OF [add0_d r0]          (* Suc(0+r0) = Suc r0 *)
    val chain = oeqTrans_r2 (aS, z0)          (* (Suc 0)+r0 = Suc r0 *)
  in le_intro_d (suc ZeroC, suc r0, r0) (oeqSym_r2 chain) end;  (* le (Suc 0)(Suc r0) = lt 0 (Suc r0) *)

(* cong m (m*p) 0 : m | m*p, witness p :  m*p = 0 + m*p *)
fun cong_mp_zero (mT, pT) =
  let val z = add0_d (mult mT pT)             (* 0 + m*p = m*p *)
  in cong_introR_r (mT, mult mT pT, ZeroC, pT) (oeqSym_r2 z) end;  (* cong m (m*p) 0 *)
val () = out "L4_SEAT1_LT0SUC_CONGMP_OK\n";

(* elim_signed_sum (m,a,b,c,d) ex goalC k :
   ex : EX a' b' c' d' r. srsBody m a b c d a' b' c' d' r
   k (ap,bp,cp,dp,r) hsum hsa hsb hsc hsd hba hbb hbc hbd -> thm(goalC).
   goalC must not mention the witnesses. *)
fun elim_signed_sum (mT,aT,bT,cT,dT) ex goalC k =
  let
    (* predicate builders mirror signed_four_residue_sum's goalP_* *)
    val Rv=Free("r4e",natT); val Dv=Free("d4e",natT); val Cv=Free("c4e",natT)
    val Bv=Free("b4e",natT); val Av=Free("a4e",natT)
    fun pR a' b' c' d' = Term.lambda Rv (srsBody mT aT bT cT dT a' b' c' d' Rv)
    fun pD a' b' c' = Term.lambda Dv (mkEx (Term.lambda Rv (srsBody mT aT bT cT dT a' b' c' Dv Rv)))
    fun pC a' b' = Term.lambda Cv (mkEx (Term.lambda Dv (mkEx (Term.lambda Rv (srsBody mT aT bT cT dT a' b' Cv Dv Rv)))))
    fun pB a' = Term.lambda Bv (mkEx (Term.lambda Cv (mkEx (Term.lambda Dv (mkEx (Term.lambda Rv (srsBody mT aT bT cT dT a' Bv Cv Dv Rv)))))))
    val pA = Term.lambda Av (mkEx (Term.lambda Bv (mkEx (Term.lambda Cv (mkEx (Term.lambda Dv (mkEx (Term.lambda Rv (srsBody mT aT bT cT dT Av Bv Cv Dv Rv)))))))))
  in
    exE_r (pA, goalC) ex "ap_es" natT (fn ap => fn hA =>
      exE_r (pB ap, goalC) hA "bp_es" natT (fn bp => fn hB =>
        exE_r (pC ap bp, goalC) hB "cp_es" natT (fn cp => fn hC =>
          exE_r (pD ap bp cp, goalC) hC "dp_es" natT (fn dp => fn hD =>
            exE_r (pR ap bp cp dp, goalC) hD "r_es" natT (fn r => fn hbig =>
              let
                val sumEq = oeq (add (add (sq ap)(sq bp)) (add (sq cp)(sq dp))) (mult mT r)
                val sgA = signD (mT, ap, aT); val sgB = signD (mT, bp, bT)
                val sgC = signD (mT, cp, cT); val sgD = signD (mT, dp, dT)
                val lA = le (add ap ap) mT; val lB = le (add bp bp) mT
                val lC = le (add cp cp) mT; val lD = le (add dp dp) mT
                val rest1 = mkConj sgA (mkConj sgB (mkConj sgC (mkConj sgD (mkConj lA (mkConj lB (mkConj lC lD))))))
                val hsum = conjunct1_r (sumEq, rest1) hbig
                val r1   = conjunct2_r (sumEq, rest1) hbig
                val rest2 = mkConj sgB (mkConj sgC (mkConj sgD (mkConj lA (mkConj lB (mkConj lC lD)))))
                val hsa = conjunct1_r (sgA, rest2) r1
                val r2  = conjunct2_r (sgA, rest2) r1
                val rest3 = mkConj sgC (mkConj sgD (mkConj lA (mkConj lB (mkConj lC lD))))
                val hsb = conjunct1_r (sgB, rest3) r2
                val r3  = conjunct2_r (sgB, rest3) r2
                val rest4 = mkConj sgD (mkConj lA (mkConj lB (mkConj lC lD)))
                val hsc = conjunct1_r (sgC, rest4) r3
                val r4  = conjunct2_r (sgC, rest4) r3
                val rest5 = mkConj lA (mkConj lB (mkConj lC lD))
                val hsd = conjunct1_r (sgD, rest5) r4
                val r5  = conjunct2_r (sgD, rest5) r4
                val rest6 = mkConj lB (mkConj lC lD)
                val hba = conjunct1_r (lA, rest6) r5
                val r6  = conjunct2_r (lA, rest6) r5
                val rest7 = mkConj lC lD
                val hbb = conjunct1_r (lB, rest7) r6
                val r7  = conjunct2_r (lB, rest7) r6
                val hbc = conjunct1_r (lC, lD) r7
                val hbd = conjunct2_r (lC, lD) r7
              in k (ap,bp,cp,dp,r) hsum hsa hsb hsc hsd hba hbb hbc hbd end)))))
  end;
val () = out "L4_SEAT1_ELIM_SIGNED_SUM_OK\n";

(* ============================================================================
   descent_residue : prime2 p ==> 1<m ==> m<p ==> four_sq (m*p)
       ==> EX r. (lt 0 r) AND (le r m) AND four_sq (mult m r)
   (the descent SETUP : the smaller multiple r, 0<r<=m, m*r a sum of four squares.
    The STRICT r<m (r=m exclusion) and the divide-by-m^2 are NOT in this lemma.)
   ============================================================================ *)
val descent_residue =
  let
    val pF = Free("p_dr", natT); val mF = Free("m_dr", natT)
    val hPrP = jT (prime2 pF); val hPr = Thm.assume (ctermGR hPrP)
    val h1mP = jT (lt (suc ZeroC) mF); val h1m = Thm.assume (ctermGR h1mP)
    val hmpP = jT (lt mF pF); val hmp = Thm.assume (ctermGR hmpP)
    val hfsP = jT (four_sq (mult mF pF)); val hfs = Thm.assume (ctermGR hfsP)
    (* 0<m from 1<m : lt 0 m via le 1 m; lt 1 m = le 2 m; le 1 2 then trans? simpler:
       lt 1 m = le (Suc 1) m ; le (Suc 0)(Suc 1) trivial ; trans -> le (Suc 0) m = lt 0 m *)
    val le12 = lt_0_suc_r (suc ZeroC)         (* lt 0 (Suc(Suc 0)) = le 1 2 *)
    val hmPos = le_trans_d (suc ZeroC, suc (suc ZeroC), mF) le12 h1m   (* le 1 m = lt 0 m *)
    (* result existential predicate over r *)
    val rF0 = Free("r_dres", natT)
    val goalP = Term.lambda rF0 (mkConj (lt ZeroC rF0) (mkConj (le rF0 mF) (four_sq (mult mF rF0))))
    val goalC = mkEx goalP
    val cmp0 = cong_mp_zero (mF, pF)           (* cong m (m*p) 0 *)
    val core =
      elim_four_sq "dr" hfs (mult mF pF) goalC (fn (a,b,c,d) => fn hbody =>
        (* hbody : oeq (m*p)(a^2+b^2+c^2+d^2) *)
        let
          val ex = signed_four_residue_sum (mF, a, b, c, d, mult mF pF) hmPos hbody cmp0
        in elim_signed_sum (mF, a, b, c, d) ex goalC (fn (ap,bp,cp,dp,r) =>
             fn hsum => fn hsa => fn hsb => fn hsc => fn hsd => fn hba => fn hbb => fn hbc => fn hbd =>
             let
               (* four_sq(m*r) from hsum *)
               val fsmr = four_sq_witness (mult mF r, ap, bp, cp, dp) (oeqSym_r2 hsum)
               (* 0<r : case r=0 (contra via r0_excl) ; r=Suc r0 (lt_0_suc) *)
               val dzr = dzos_d r
               val pos_r =
                 disjE_r (oeq r ZeroC, mkEx (Abs("k",natT, oeq r (suc (Bound 0)))), lt ZeroC r)
                   dzr
                   (let val hP=jT (oeq r ZeroC); val h=Thm.assume (ctermGR hP)
                        val fls = r0_excl (mF,pF,r, a,b,c,d, ap,bp,cp,dp)
                                    hsum hsa hsb hsc hsd hbody hPr h1m hmp hmPos h
                    in Thm.implies_intr (ctermGR hP) (Thm.implies_elim (oFalse_elim_r (lt ZeroC r)) fls) end)
                   (let val Pk=Abs("k",natT, oeq r (suc (Bound 0)))
                        val hP=jT (mkEx Pk); val h=Thm.assume (ctermGR hP)
                        fun bd r0 (hr0:thm) =
                          let val ltp = lt_0_suc_r r0
                              val ltpr = oeq_rw_r (Term.lambda (Free("zpr",natT)) (lt ZeroC (Free("zpr",natT))), suc r0, r) (oeqSym_r2 hr0) ltp
                          in ltpr end
                    in Thm.implies_intr (ctermGR hP) (exE_r (Pk, lt ZeroC r) h "r0pos" natT bd) end)
               (* r<=m *)
               val le_rm = r_le_m (mF, r, ap,bp,cp,dp) hsum hba hbb hbc hbd hmPos
               (* assemble conjunction + exI r *)
               val conj = conjI_r (lt ZeroC r, mkConj (le r mF)(four_sq (mult mF r))) pos_r
                            (conjI_r (le r mF, four_sq (mult mF r)) le_rm fsmr)
               val exr = exI_r goalP r conj
             in exr end)
        end)
  in Thm.implies_intr (ctermGR hPrP) (Thm.implies_intr (ctermGR h1mP)
       (Thm.implies_intr (ctermGR hmpP) (Thm.implies_intr (ctermGR hfsP) core))) end;
val () = out ("descent_residue hyps="^Int.toString(length(Thm.hyps_of descent_residue))^"\n");
val () = out ("descent_residue prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of descent_residue)^"\n");

(* ---- aconv against intended ---- *)
val descent_residue_intended =
  let
    val pV = Free("p_dr", natT); val mV = Free("m_dr", natT)
    val rV = Free("r_dres", natT)
    val concl = mkEx (Term.lambda rV
                  (mkConj (lt ZeroC rV) (mkConj (le rV mV) (four_sq (mult mV rV)))))
  in Logic.mk_implies (jT (prime2 pV),
       Logic.mk_implies (jT (lt (suc ZeroC) mV),
         Logic.mk_implies (jT (lt mV pV),
           Logic.mk_implies (jT (four_sq (mult mV pV)), jT concl))))
  end;
val dr_aconv = ((Thm.prop_of descent_residue) aconv descent_residue_intended);
val dr_0hyp  = (length (Thm.hyps_of descent_residue) = 0);
val () = out ("L4_SEAT1_DR_VALIDATE aconv="^Bool.toString dr_aconv^" zero_hyp="^Bool.toString dr_0hyp^"\n");

(* SOUNDNESS PROBE 1 : genuinely conditional (drop four_sq(m*p) -> NOT aconv).
   A version missing the four_sq(m*p) premise would be unsound (no four-sq multiple given). *)
val dr_probe_needs_fs =
  let
    val pV = Free("p_dr", natT); val mV = Free("m_dr", natT); val rV = Free("r_dres", natT)
    val concl = mkEx (Term.lambda rV (mkConj (lt ZeroC rV) (mkConj (le rV mV) (four_sq (mult mV rV)))))
    val wrong = Logic.mk_implies (jT (prime2 pV),
                  Logic.mk_implies (jT (lt (suc ZeroC) mV),
                    Logic.mk_implies (jT (lt mV pV), jT concl)))
  in not ((Thm.prop_of descent_residue) aconv wrong) end;
val () = out ("L4_SEAT1_DR_PROBE_NEEDS_FS "^Bool.toString dr_probe_needs_fs^"\n");

(* SOUNDNESS PROBE 2 : conclusion genuinely asserts 0<r (not the trivial true). *)
val dr_probe_pos =
  let
    val pV = Free("p_dr", natT); val mV = Free("m_dr", natT); val rV = Free("r_dres", natT)
    (* a version that DROPS 0<r from the conjunction *)
    val conclW = mkEx (Term.lambda rV (mkConj (le rV mV) (four_sq (mult mV rV))))
    val wrong = Logic.mk_implies (jT (prime2 pV),
                  Logic.mk_implies (jT (lt (suc ZeroC) mV),
                    Logic.mk_implies (jT (lt mV pV),
                      Logic.mk_implies (jT (four_sq (mult mV pV)), jT conclW))))
  in not ((Thm.prop_of descent_residue) aconv wrong) end;
val () = out ("L4_SEAT1_DR_PROBE_POS "^Bool.toString dr_probe_pos^"\n");

val () = if dr_aconv andalso dr_0hyp andalso dr_probe_needs_fs andalso dr_probe_pos
         then out "L4_SEAT1_DESCENT_RESIDUE_OK\n" else out "L4_SEAT1_DESCENT_RESIDUE_VALIDATE_FAILED\n";
val () = out "L4_SEAT1_DESCENT_RESIDUE_DONE\n";

(* ============================================================================
   SEAT 1 SUMMARY (honest).
   PROVED (0-hyp, aconv-checked, 2 soundness probes) — the descent SETUP:
     descent_residue : prime2 p ==> 1<m ==> m<p ==> four_sq (m*p)
                          ==> EX r. (0<r) /\ (r<=m) /\ four_sq (m*r)
   Sub-results proved 0-hyp en route (all bankable):
     signed_four_residue_sum : the SIGNED four-residue decomposition (sum=m*r +
       per-coordinate (cong m a' a OR cong m (a'+a) 0) + bounds 2x'<=m) — the
       piece the resume material LACKED (it only had the squared/unsigned form).
     r0_excl                 : the r=0 EXCLUSION  (=> oFalse).
     r_le_m                  : the r<=m AM bound.
     mult_left_cancel_r      : m>0 ==> m*a=m*b ==> a=b  (the base had NO such lemma).
   NOT proved (the open remainder toward the FULL descent_step):
     (1) STRICT r<m : the r=m exclusion (all 2x'=m -> m even, x'=m/2 -> m|2a..2d
         -> m|4p ; needs Euclid's lemma) — a multi-lemma effort.
     (2) the EULER DIVIDE-by-m^2 : (m*p)(m*r)=W^2+X^2+Y^2+Z^2 with m|W,X,Y,Z, then
         divide -> four_sq(r*p).  The banked proveStarFor proves the identity with
         ABSDIFF-massaged witnesses (sx=|Px-Qx| etc.), whose divisibility-by-m is
         NOT directly available — (d) needs a SIGNED-bilinear Euler identity over N
         (W=aa'+bb'+cc'+dd', X=ab'-ba'+cd'-dc', ...) with absdiff, tracking m|W..Z
         from the signed residues.  That is the genuinely large open piece.
   ============================================================================ *)
val () = out "L4_SEAT1_SUMMARY_DONE\n";
val () = out "SMOKE_ALL_DONE\n";
