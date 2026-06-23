(* ============================================================================
   FERMAT TWO-SQUARE FULL IFF — BRIDGE SEAT 2 : the UNCONDITIONAL full iff.

   Appended AFTER the full merged base (isabelle_twosquare.sml + the if-direction
   deltas + seat1_flt_region_rerooted + oi_arith/oi_descent/oi_casea_seat2 +
   seat1_iff_assembly).  In scope:
     - ctxtGR / ctermGR + the full _gr/_r/_g/_d toolkit, pow_*, le_total_gr_at,
       vpredBody / evenBody / fourk3 / hpBody / innerAllE / hpInnerBody,
       val_coprime_self / prime_not_dvd_pow / padic_split, pow_pos / pow_pos_at,
       le1_of_le2, powAdd_gr / add0r_gr, mult_cong_*_gr, multassoc_gr, ...
     - if_direction : 0<n ==> hpBody n ==> sumsq n      (on ctxtGR, 0-hyp)
     - ctxtSub / ctermSub (extends thyGR) + the S2 toolkit (mp_S2/allI_S2/allE_S2/
       impI_S2/exISub_at/exESub_elim/conjI_atSub/conjunct{1,2}_atSub/disjE_elimSub/
       ex_middle_atSub/oeq_subst_vS2) and `only_if` :
         prime2 p ==> (Ex k. p=4k+3) ==> (Conj (lt 0 n)(sumsqBody n))
           ==> Ex v m. n=pow p v*m /\ ~(p|m) /\ (Ex j. v=j+j)

   THE GAP THIS SEAT CLOSES:  only_if gives a PER-PRIME EXISTENTIAL even
   valuation; hpBody's inner is UNIVERSAL (!e. vpred p n e ==> even e).  The
   bridge = VALUATION UNIQUENESS.  This seat proves valuation_unique by
   mult_left_cancel (built here, via le_total + a from-scratch mult_eq_zero),
   then assembles the unconditional

     twosquare_full : 0<n ==> Conj (Imp (sumsq n)(hpBody n)) (Imp (hpBody n)(sumsq n))

   0 new axioms / consts / types over the merged base.  Only classical = ex_middle.
   ============================================================================ *)
val () = out "TSF_BRIDGE_SEAT2_BEGIN\n";

(* ---- a couple of base lemmas onto ctxtGR not already supplied ---- *)
val mult_eq_zero_disjI1_gr = disjI1_gr_at;   (* alias for clarity *)
val mult_eq_zero_disjI2_gr = disjI2_gr_at;

(* ===========================================================================
   mult_eq_zero (ctxtGR) :  oeq (mult a b) 0 ==> Disj (oeq a 0)(oeq b 0)
   (mirror isabelle_pyth.sml; multSuc_gr is the LEFT-recursion form
    (Suc m)*n = n + m*n, and add_eq_zero_left_d : add x y = 0 ==> x = 0.)
   =========================================================================== *)
val mult_eq_zero =
  let
    val aF = Free("a_mez", natT); val bF = Free("b_mez", natT);
    val hyp = Thm.assume (ctermGR (jT (oeq (mult aF bF) ZeroC)));
    val goalC = mkDisj (oeq aF ZeroC) (oeq bF ZeroC);
    val dz = dzos_gr aF;                       (* Disj (oeq a 0)(Ex q. oeq a (Suc q)) *)
    val caseZ =
      let val hZ = Thm.assume (ctermGR (jT (oeq aF ZeroC)))
      in Thm.implies_intr (ctermGR (jT (oeq aF ZeroC)))
           (disjI1_gr_at (oeq aF ZeroC, oeq bF ZeroC) hZ) end;
    val sucAbs = Abs("q", natT, oeq aF (suc (Bound 0)));
    val caseS =
      let val hEx = Thm.assume (ctermGR (jT (mkEx sucAbs)))
          val res = exE_r (sucAbs, goalC) hEx "q_mez" natT (fn qF => fn hq =>
            let
              (* a*b = (Suc q)*b = b + q*b *)
              val abq  = mult_cong_l_gr (aF, suc qF, bF) hq;     (* oeq (a*b) ((Suc q)*b) *)
              val sqb  = multSuc_gr (qF, bF);                     (* oeq ((Suc q)*b) (add b (q*b)) *)
              val ab_e = oeqTrans_r2 (oeqSym_r2 (oeqTrans_r2 (abq, sqb)), hyp);  (* oeq (add b (q*b)) 0 *)
              val bz   = add_eq_zero_left_d (bF, mult qF bF) ab_e;               (* oeq b 0 *)
            in disjI2_gr_at (oeq aF ZeroC, oeq bF ZeroC) bz end);
      in Thm.implies_intr (ctermGR (jT (mkEx sucAbs))) res end;
    val body = disjE_r (oeq aF ZeroC, mkEx sucAbs, goalC) dz caseZ caseS;
  in varify (Thm.implies_intr (ctermGR (jT (oeq (mult aF bF) ZeroC))) body) end;
val mult_eq_zero_v = varify mult_eq_zero;
fun mult_eq_zero_at (aT,bT) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
    [(("a_mez",0), ctermGR aT),(("b_mez",0), ctermGR bT)] mult_eq_zero_v)) h;
val () = out ("MULT_EQ_ZERO hyps="^Int.toString(length(Thm.hyps_of mult_eq_zero))^"\n");

(* ===========================================================================
   mult_left_cancel (ctxtGR) :  lt 0 p ==> oeq (mult p a)(mult p b) ==> oeq a b
   (mirror isabelle_pyth.sml mult_left_cancel via le_total + left_distrib +
    add_left_cancel + mult_eq_zero.)
   =========================================================================== *)
val mult_left_cancel =
  let
    val pF = Free("p_mlc", natT); val aF = Free("a_mlc", natT); val bF = Free("b_mlc", natT);
    val hPos = Thm.assume (ctermGR (jT (lt ZeroC pF)));
    val hEq  = Thm.assume (ctermGR (jT (oeq (mult pF aF) (mult pF bF))));
    val goalC = oeq aF bF;
    val tot  = le_total_gr_at (aF, bF);    (* Disj (le a b)(le b a) *)
    (* contraP : (oeq p 0) ==> goal  (p=0 contradicts lt 0 p) *)
    fun contraP goal =
      let val hpz = Thm.assume (ctermGR (jT (oeq pF ZeroC)))
          val zV  = Free("z_mlc0", natT); val Psub = Term.lambda zV (lt ZeroC zV)
          val lt00 = oeq_rw_r (Psub, pF, ZeroC) hpz hPos     (* lt 0 0 *)
          val fls  = lt_irrefl_g ZeroC lt00
      in Thm.implies_intr (ctermGR (jT (oeq pF ZeroC))) (Thm.implies_elim (oFalse_elim_r goal) fls) end;
    (* case le a b : Ex d. b = a + d *)
    val leAbsAB = Abs("k", natT, oeq bF (add aF (Bound 0)));
    val caseAB =
      let val hLe = Thm.assume (ctermGR (jT (le aF bF)))
          val r = exE_r (leAbsAB, goalC) hLe "d_ab" natT (fn dF => fn hd =>
            let
              val pb1 = mult_cong_r_gr (pF, bF, add aF dF) hd;       (* p*b = p*(a+d) *)
              val ld  = leftdistrib_gr (pF, aF, dF);                  (* p*(a+d) = p*a + p*d *)
              val pb2 = oeqTrans_r2 (pb1, ld);                        (* p*b = p*a + p*d *)
              val pa_e= oeqTrans_r2 (hEq, pb2);                       (* p*a = p*a + p*d *)
              (* p*a = (p*a)+0  -> add_left_cancel : 0 = p*d *)
              val pa0 = oeqSym_r2 (add0r_gr (mult pF aF));            (* (p*a)+0 = p*a, sym -> p*a = (p*a)+0 *)
              val both= oeqTrans_r2 (oeqSym_r2 pa0, pa_e);            (* (p*a)+0 = (p*a)+(p*d) *)
              val zpd = add_left_cancel_gr OF [both];                 (* 0 = p*d *)
              val pdz = oeqSym_r2 zpd;                                (* p*d = 0 *)
              val disj= mult_eq_zero_at (pF, dF) pdz;                 (* Disj (p=0)(d=0) *)
              val cZp = contraP goalC;
              val cZd =
                let val hdz = Thm.assume (ctermGR (jT (oeq dF ZeroC)))
                    (* b = a+d = a+0 = a, sym -> a = b *)
                    val ba0 = oeqTrans_r2 (hd, add_cong_r_gr (aF, dF, ZeroC) hdz)  (* b = a+0 *)
                    val ba  = oeqTrans_r2 (ba0, add0r_gr aF)                       (* b = a *)
                    val ab  = oeqSym_r2 ba                                          (* a = b *)
                in Thm.implies_intr (ctermGR (jT (oeq dF ZeroC))) ab end;
            in disjE_r (oeq pF ZeroC, oeq dF ZeroC, goalC) disj cZp cZd end);
      in Thm.implies_intr (ctermGR (jT (le aF bF))) r end;
    val leAbsBA = Abs("k", natT, oeq aF (add bF (Bound 0)));
    val caseBA =
      let val hLe = Thm.assume (ctermGR (jT (le bF aF)))
          val r = exE_r (leAbsBA, goalC) hLe "d_ba" natT (fn dF => fn hd =>
            let
              val pa1 = mult_cong_r_gr (pF, aF, add bF dF) hd;       (* p*a = p*(b+d) *)
              val ld  = leftdistrib_gr (pF, bF, dF);                  (* p*(b+d) = p*b + p*d *)
              val pa2 = oeqTrans_r2 (pa1, ld);                        (* p*a = p*b + p*d *)
              val pb_e= oeqTrans_r2 (oeqSym_r2 hEq, pa2);             (* p*b = p*b + p*d *)
              val pb0 = oeqSym_r2 (add0r_gr (mult pF bF));            (* p*b = (p*b)+0 *)
              val both= oeqTrans_r2 (oeqSym_r2 pb0, pb_e);            (* (p*b)+0 = (p*b)+(p*d) *)
              val zpd = add_left_cancel_gr OF [both];                 (* 0 = p*d *)
              val pdz = oeqSym_r2 zpd;                                (* p*d = 0 *)
              val disj= mult_eq_zero_at (pF, dF) pdz;
              val cZp = contraP goalC;
              val cZd =
                let val hdz = Thm.assume (ctermGR (jT (oeq dF ZeroC)))
                    val ab0 = oeqTrans_r2 (hd, add_cong_r_gr (bF, dF, ZeroC) hdz)  (* a = b+0 *)
                    val ab  = oeqTrans_r2 (ab0, add0r_gr bF)                       (* a = b *)
                in Thm.implies_intr (ctermGR (jT (oeq dF ZeroC))) ab end;
            in disjE_r (oeq pF ZeroC, oeq dF ZeroC, goalC) disj cZp cZd end);
      in Thm.implies_intr (ctermGR (jT (le bF aF))) r end;
    val body = disjE_r (le aF bF, le bF aF, goalC) tot caseAB caseBA;
    val d1 = Thm.implies_intr (ctermGR (jT (oeq (mult pF aF) (mult pF bF)))) body;
    val d2 = Thm.implies_intr (ctermGR (jT (lt ZeroC pF))) d1;
  in varify d2 end;
val mult_left_cancel_v = varify mult_left_cancel;
fun mult_left_cancel_at (pT,aT,bT) hpos heq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("p_mlc",0), ctermGR pT),(("a_mlc",0), ctermGR aT),(("b_mlc",0), ctermGR bT)] mult_left_cancel_v)
  in (inst OF [hpos]) OF [heq] end;
val () = out ("MULT_LEFT_CANCEL hyps="^Int.toString(length(Thm.hyps_of mult_left_cancel))^"\n");

(* self-test mult_left_cancel aconv *)
local
  val pp = Free("p", natT); val aa = Free("a", natT); val bb = Free("b", natT);
  val mlc_intended = Logic.mk_implies (jT (lt ZeroC pp),
        Logic.mk_implies (jT (oeq (mult pp aa)(mult pp bb)), jT (oeq aa bb)));
  val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("p_mlc",0), ctermGR pp),(("a_mlc",0), ctermGR aa),(("b_mlc",0), ctermGR bb)] mult_left_cancel_v);
in
  val () = out ("MLC aconv="^Bool.toString ((Thm.prop_of inst) aconv mlc_intended)^"\n");
end;

val () = out "TSF_BRIDGE_CANCEL_OK\n";

(* ===========================================================================
   valuation_unique (ctxtGR) :
     prime2 p ==> lt 0 n ==> vpredBody(p,n,e1) ==> vpredBody(p,n,e2) ==> oeq e1 e2
   Proof: le_total e1 e2.  WLOG le ea eb (Ex d. eb = ea+d).  From
     n = p^ea*ma (~p|ma) and n = p^eb*mb (~p|mb), and
     p^eb = p^(ea+d) = p^ea * p^d  [pow_add], get
     p^ea*ma = p^ea*(p^d*mb)  [assoc] ; mult_left_cancel (p^ea>0) -> ma = p^d*mb.
     dzos on d: d=Suc d0 -> p^d = p*p^d0 -> ma = p*(p^d0*mb) -> p|ma, contra ~p|ma.
     So d=0 -> eb = ea+0 = ea -> oeq ea eb.
   =========================================================================== *)
val valuation_unique =
  let
    val pF = Free("p", natT); val nF = Free("n", natT);
    val e1F = Free("e1", natT); val e2F = Free("e2", natT);
    val hPrP = jT (prime2 pF);          val hPr  = Thm.assume (ctermGR hPrP);
    val hPosP= jT (lt ZeroC nF);        val hPos = Thm.assume (ctermGR hPosP);
    val hV1P = jT (vpredBody (pF, nF, e1F)); val hV1 = Thm.assume (ctermGR hV1P);
    val hV2P = jT (vpredBody (pF, nF, e2F)); val hV2 = Thm.assume (ctermGR hV2P);
    val goalC = oeq e1F e2F;

    (* le 1 p, then pow_pos : lt 0 (pow p ea) for ANY exponent *)
    val hLe2P = prime2_gt1_r pF hPr;        (* le 2 p = lt 1 p *)
    val hLe1P = le1_of_le2 pF hLe2P;        (* le 1 p = lt 0 p *)

    (* descend (eaT,ebT, hVa, hVb) : given le eaT ebT, returns oeq eaT ebT.
       hVa : vpredBody (p,n,ea) ; hVb : vpredBody (p,n,eb). *)
    fun descend (eaT, ebT, hVa, hVb) hLe =
      let
        val leAbs = Abs("k", natT, oeq ebT (add eaT (Bound 0)));
        val gC = oeq eaT ebT;
      in exE_r (leAbs, gC) hLe "d_vu" natT (fn dF => fn hd =>   (* hd : oeq eb (ea+d) *)
        let
          (* extract ma : n = p^ea*ma /\ ~p|ma *)
          val PaM = Term.lambda mFrV (mkConj (oeq nF (mult (pow pF eaT) mFrV)) (neg (dvd pF mFrV)));
          val r = exE_r (PaM, gC) hVa "ma_vu" natT (fn maF => fn hCa =>
            let
              val hNa = conjunct1_gr_at (oeq nF (mult (pow pF eaT) maF), neg (dvd pF maF)) hCa; (* n = p^ea*ma *)
              val hNdma = conjunct2_gr_at (oeq nF (mult (pow pF eaT) maF), neg (dvd pF maF)) hCa; (* ~p|ma *)
              val PbM = Term.lambda mFrV (mkConj (oeq nF (mult (pow pF ebT) mFrV)) (neg (dvd pF mFrV)));
            in exE_r (PbM, gC) hVb "mb_vu" natT (fn mbF => fn hCb =>
              let
                val hNb = conjunct1_gr_at (oeq nF (mult (pow pF ebT) mbF), neg (dvd pF mbF)) hCb; (* n = p^eb*mb *)
                (* p^eb = p^(ea+d) = p^ea * p^d  : rewrite eb -> ea+d then pow_add *)
                val zE = Free("zpe_vu", natT); val PpE = Term.lambda zE (oeq (pow pF ebT)(pow pF zE));
                val pebCong = oeq_rw_r (PpE, ebT, add eaT dF) hd (oeqRefl_r2 (pow pF ebT)); (* p^eb = p^(ea+d) *)
                val padd = powAdd_gr (pF, eaT, dF);                  (* p^(ea+d) = p^ea * p^d *)
                val pebEq = oeqTrans_r2 (pebCong, padd);             (* p^eb = p^ea * p^d *)
                (* n = p^eb*mb = (p^ea*p^d)*mb = p^ea*(p^d*mb) *)
                val s1 = mult_cong_l_gr (pow pF ebT, mult (pow pF eaT)(pow pF dF), mbF) pebEq; (* p^eb*mb = (p^ea*p^d)*mb *)
                val s2 = multassoc_gr (pow pF eaT, pow pF dF, mbF);  (* (p^ea*p^d)*mb = p^ea*(p^d*mb) *)
                val nEqB = oeqTrans_r2 (hNb, oeqTrans_r2 (s1, s2));  (* n = p^ea*(p^d*mb) *)
                (* p^ea*ma = p^ea*(p^d*mb) *)
                val cancelEq = oeqTrans_r2 (oeqSym_r2 hNa, nEqB);    (* p^ea*ma = p^ea*(p^d*mb) *)
                val hPosPea = pow_pos_at (pF, eaT) hLe1P;            (* lt 0 (pow p ea) *)
                val maEq = mult_left_cancel_at (pow pF eaT, maF, mult (pow pF dF) mbF) hPosPea cancelEq; (* ma = p^d*mb *)
                (* dzos d *)
                val dzD = dzos_gr dF;
                val caseDz =
                  let val hz = Thm.assume (ctermGR (jT (oeq dF ZeroC)))
                      (* eb = ea+d = ea+0 = ea -> oeq ea eb *)
                      val be0 = oeqTrans_r2 (hd, add_cong_r_gr (eaT, dF, ZeroC) hz)  (* eb = ea+0 *)
                      val beA = oeqTrans_r2 (be0, add0r_gr eaT)                      (* eb = ea *)
                      val res = oeqSym_r2 beA                                         (* ea = eb *)
                  in Thm.implies_intr (ctermGR (jT (oeq dF ZeroC))) res end;
                val caseDs =
                  let val hsP = jT (mkExSuc dF); val hs = Thm.assume (ctermGR hsP)
                      val inner = exE_r (Abs("q", natT, oeq dF (suc (Bound 0))), gC) hs "dq_vu" natT (fn d0F => fn hdq =>
                        let
                          (* p^d = p^(Suc d0) = p*p^d0 *)
                          val pdCong = let val Pp = Term.lambda (Free("zpd_vu",natT)) (oeq (pow pF dF)(pow pF (Free("zpd_vu",natT))))
                                       in oeq_rw_r (Pp, dF, suc d0F) hdq (oeqRefl_r2 (pow pF dF)) end; (* p^d = p^(Suc d0) *)
                          val pdSuc = powSuc_gr (pF, d0F);                  (* p^(Suc d0) = p*p^d0 *)
                          val pdEq  = oeqTrans_r2 (pdCong, pdSuc);          (* p^d = p*p^d0 *)
                          (* ma = p^d*mb = (p*p^d0)*mb = p*(p^d0*mb) *)
                          val c1 = mult_cong_l_gr (pow pF dF, mult pF (pow pF d0F), mbF) pdEq; (* p^d*mb = (p*p^d0)*mb *)
                          val c2 = multassoc_gr (pF, pow pF d0F, mbF);      (* (p*p^d0)*mb = p*(p^d0*mb) *)
                          val maP = oeqTrans_r2 (maEq, oeqTrans_r2 (c1, c2)); (* ma = p*(p^d0*mb) *)
                          (* p | ma *)
                          val hdvd = dvdIntro_gr (pF, maF, mult (pow pF d0F) mbF) maP; (* dvd p ma *)
                          val fls  = mp_r (dvd pF maF, oFalseC) hNdma hdvd;  (* oFalse *)
                        in Thm.implies_elim (oFalse_elim_r gC) fls end)
                  in Thm.implies_intr (ctermGR hsP) inner end;
              in disjE_r (oeq dF ZeroC, mkExSuc dF, gC) dzD caseDz caseDs end) end);
        in r end) end;

    (* le_total e1 e2 *)
    val tot = le_total_gr_at (e1F, e2F);
    val caseAB =
      let val hLe = Thm.assume (ctermGR (jT (le e1F e2F)))
          val r = descend (e1F, e2F, hV1, hV2) hLe                 (* oeq e1 e2 *)
      in Thm.implies_intr (ctermGR (jT (le e1F e2F))) r end;
    val caseBA =
      let val hLe = Thm.assume (ctermGR (jT (le e2F e1F)))
          val r0 = descend (e2F, e1F, hV2, hV1) hLe                (* oeq e2 e1 *)
          val r  = oeqSym_r2 r0                                     (* oeq e1 e2 *)
      in Thm.implies_intr (ctermGR (jT (le e2F e1F))) r end;
    val body = disjE_r (le e1F e2F, le e2F e1F, goalC) tot caseAB caseBA;
    val t = Thm.implies_intr (ctermGR hPrP)
              (Thm.implies_intr (ctermGR hPosP)
                (Thm.implies_intr (ctermGR hV1P)
                  (Thm.implies_intr (ctermGR hV2P) body)));
  in varify t end;
val () = out ("VALUATION_UNIQUE hyps="^Int.toString(length(Thm.hyps_of valuation_unique))^"\n");

local
  val pF = Free("p", natT); val nF = Free("n", natT);
  val e1F = Free("e1", natT); val e2F = Free("e2", natT);
  val vu_intended = Logic.mk_implies (jT (prime2 pF),
        Logic.mk_implies (jT (lt ZeroC nF),
          Logic.mk_implies (jT (vpredBody (pF, nF, e1F)),
            Logic.mk_implies (jT (vpredBody (pF, nF, e2F)), jT (oeq e1F e2F)))));
  val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("p",0), ctermGR pF),(("n",0), ctermGR nF),(("e1",0), ctermGR e1F),(("e2",0), ctermGR e2F)] (varify valuation_unique));
in
  val () = out ("VALUATION_UNIQUE aconv="^Bool.toString ((Thm.prop_of inst) aconv vu_intended)^"\n");
  (* soundness probe : drops the prime2 hypothesis -> must NOT be aconv (valuation
     uniqueness genuinely needs primality, e.g. for a composite base the two
     decompositions need not have the same exponent). *)
  val vu_drop_prime = Logic.mk_implies (jT (lt ZeroC nF),
        Logic.mk_implies (jT (vpredBody (pF, nF, e1F)),
          Logic.mk_implies (jT (vpredBody (pF, nF, e2F)), jT (oeq e1F e2F))));
  val () = if not ((Thm.prop_of inst) aconv vu_drop_prime)
           then out "PROBE_OK valuation_unique keeps prime2 p\n"
           else out "PROBE_FAIL valuation_unique dropped prime2 p\n";
  (* soundness probe 2 : concludes oeq e1 e2, not the trivial oeq e1 e1 *)
  val vu_trivial = Logic.mk_implies (jT (prime2 pF),
        Logic.mk_implies (jT (lt ZeroC nF),
          Logic.mk_implies (jT (vpredBody (pF, nF, e1F)),
            Logic.mk_implies (jT (vpredBody (pF, nF, e2F)), jT (oeq e1F e1F)))));
  val () = if not ((Thm.prop_of inst) aconv vu_trivial)
           then out "PROBE_OK valuation_unique concludes oeq e1 e2 (not e1 e1)\n"
           else out "PROBE_FAIL valuation_unique conclusion trivial\n";
end;
val () = out "TSF_BRIDGE_VALUNIQUE_OK\n";

(* ===========================================================================
   RE-VARIFY valuation_unique onto ctxtSub (which EXTENDS thyGR) for the bridge
   assembly that also touches `only_if` (on ctxtSub).
   =========================================================================== *)
val valuation_unique_vS = varify valuation_unique;
fun valuation_unique_atS (pT,nT,e1T,e2T) hPr hPos hV1 hV2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("p",0), ctermSub pT),(("n",0), ctermSub nT),(("e1",0), ctermSub e1T),(("e2",0), ctermSub e2T)] valuation_unique_vS)
  in (((inst OF [hPr]) OF [hPos]) OF [hV1]) OF [hV2] end;

(* oeq-rewrite on ctxtSub *)
fun oeq_rw_S2 (Pabs, aT, bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("P",0), ctermSub Pabs),(("a",0), ctermSub aT),(("b",0), ctermSub bT)] oeq_subst_vS2)
  in (inst OF [hab]) OF [hPa] end;

(* ===========================================================================
   THE BRIDGE : oiH : 0<n ==> Imp (sumsqBody n)(hpBody n)   (a THEOREM on ctxtSub)

   sumsqBody / hpBody / vpredBody / evenBody / fourk3 are the if-direction
   builders (valid cterms on ctxtSub since ctxtSub extends thyGR).
   only_if (on ctxtSub) gives the per-prime EXISTENTIAL even valuation; we feed
   it (under hpBody's per-prime premises + 0<n + sumsqBody n), exE its (v,m),
   rebuild vpred p n v, apply valuation_unique to (v, the universal e) to get
   oeq e v, transfer the even-ness, allI over e and p -> hpBody n.
   =========================================================================== *)
val () = out "TSF_BRIDGE_OIH_BEGIN\n";

(* only_if instantiator on ctxtSub : prime2 p ==> (Ex k. p=4k+3) ==> (0<n /\ sumsq n)
                                       ==> conclBody n.
   only_if's antecedents are OBJECT implications (built with impI_S2), so apply
   with mp_S2 (NOT OF / implies_elim, which resolve on META ==>). *)
val only_if_vS = varify only_if;
(* the only_if conclBody (oi_descent form) as a term-fn of (pT,nT) *)
fun oi_conclBody (pT,nT) =
  let val vF = Free("vcb_oi", natT); val mF = Free("mcb_oi", natT);
      fun cb (vT,mT) = mkConj (oeq nT (mult (pow pT vT) mT))
                              (mkConj (neg (dvd pT mT))
                                      (mkEx (Abs("j", natT, oeq vT (add (Bound 0)(Bound 0))))));
  in mkEx (Term.lambda vF (mkEx (Term.lambda mF (cb (vF, mF))))) end;
fun oi_4k3 pT = mkEx (Abs("k", natT,
      oeq pT (add (add (add (add (Bound 0)(Bound 0))(Bound 0))(Bound 0)) (suc (suc (suc ZeroC))))));
fun only_if_atS (pT,nT) hPr h4k3 hPre =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("p",0), ctermSub pT),(("n",0), ctermSub nT)] only_if_vS)
    val concl = oi_conclBody (pT,nT);
    val pre   = mkConj (lt ZeroC nT) (sumsqBody nT);
    val k3    = oi_4k3 pT;
    val s1 = mp_S2 (prime2 pT, mkImp k3 (mkImp pre concl)) inst hPr;
    val s2 = mp_S2 (k3, mkImp pre concl) s1 h4k3;
    val s3 = mp_S2 (pre, concl) s2 hPre;
  in s3 end;

val oiH_thm =
  let
    val nF = Free("n_oih", natT);
    val hPosP = jT (lt ZeroC nF); val hPos = Thm.assume (ctermSub hPosP);
    val hSSP  = jT (sumsqBody nF); val hSS  = Thm.assume (ctermSub hSSP);
    (* build hpBody nF : Forall(%p. hpInnerBody nF p) *)
    val pBodyAbs = Term.lambda pFrH (hpInnerBody nF pFrH);
    val pFr = Free("p_oih", natT);
    val perP =
      let
        val hPpP = jT (prime2 pFr); val hPp = Thm.assume (ctermSub hPpP);
        val hF3P = jT (fourk3 pFr); val hF3 = Thm.assume (ctermSub hF3P);
        val eFr = Free("e_oih", natT);
        val eBodyAbs = Term.lambda eFr (mkImp (vpredBody (pFr, nF, eFr)) (evenBody eFr));
        val perE =
          let
            val hVeP = jT (vpredBody (pFr, nF, eFr)); val hVe = Thm.assume (ctermSub hVeP);
            (* only_if at (p,n) : need (0<n /\ sumsq n) and (Ex k. p=4k+3).
               hF3 : jT (fourk3 p) is EXACTLY only_if's h4k3Term (same 4k+3 form). *)
            val hPre = conjI_atSub (lt ZeroC nF, sumsqBody nF) hPos hSS;  (* 0<n /\ sumsq n *)
            val concl = only_if_atS (pFr, nF) hPp hF3 hPre;               (* conclBody n (only_if form) *)
            (* conclBody n = Ex v. Ex m. Conj (n=p^v*m)(Conj (~p|m)(Ex j. v=j+j)).
               exE v, exE m. *)
            (* the only_if conclBody uses fresh Frees vFr0/mFr0 (from oi_descent), with
               cbInner n (v,m) = Conj (oeq n (pow p v * m)) (Conj (neg(dvd p m)) (Ex j. oeq v (j+j))).
               Rebuild the predicate abstractions to drive exESub_elim. *)
            fun cbInnerOi (vT, mT) =
                  mkConj (oeq nF (mult (pow pFr vT) mT))
                         (mkConj (neg (dvd pFr mT))
                                 (mkEx (Abs("j", natT, oeq vT (add (Bound 0)(Bound 0))))));
            val cbVAbs = Term.lambda vFr0 (mkEx (Term.lambda mFr0 (cbInnerOi (vFr0, mFr0))));
            val res = exESub_elim (cbVAbs, evenBody eFr) concl "v_oih" (fn vF => fn hExM =>
              let
                val cbMAbs = Term.lambda mFr0 (cbInnerOi (vF, mFr0));
              in exESub_elim (cbMAbs, evenBody eFr) hExM "m_oih" (fn mF => fn hCb =>
                let
                  val innerRest = mkConj (neg (dvd pFr mF)) (mkEx (Abs("j",natT, oeq vF (add (Bound 0)(Bound 0)))));
                  val hNv  = conjunct1_atSub (oeq nF (mult (pow pFr vF) mF), innerRest) hCb;  (* n = p^v*m *)
                  val hRest= conjunct2_atSub (oeq nF (mult (pow pFr vF) mF), innerRest) hCb;
                  val hNdm = conjunct1_atSub (neg (dvd pFr mF), mkEx (Abs("j",natT, oeq vF (add (Bound 0)(Bound 0))))) hRest; (* ~p|m *)
                  val hEvenV = conjunct2_atSub (neg (dvd pFr mF), mkEx (Abs("j",natT, oeq vF (add (Bound 0)(Bound 0))))) hRest; (* Ex j. v=j+j *)
                  (* rebuild vpredBody (p,n,v) = Ex m'. (n=p^v*m' /\ ~p|m') *)
                  val vpConj = conjI_atSub (oeq nF (mult (pow pFr vF) mF), neg (dvd pFr mF)) hNv hNdm;
                  val vpPred = Term.lambda mFrV (mkConj (oeq nF (mult (pow pFr vF) mFrV)) (neg (dvd pFr mFrV)));
                  val hVpv = exISub_at vpPred mF vpConj;     (* jT (vpredBody (p,n,v)) *)
                  (* valuation_unique at (p,n,e,v) : oeq e v  (needs prime2 p, 0<n, vpred p n e, vpred p n v) *)
                  val hEqEv = valuation_unique_atS (pFr, nF, eFr, vF) hPp hPos hVe hVpv;  (* oeq e v *)
                  (* transfer even v -> even e : rewrite v -> e via oeq v e (sym of oeq e v) inside evenBody *)
                  val zRW = Free("z_ev_oih", natT); val Pev = Term.lambda zRW (evenBody zRW);
                  val hEqVe = oeq_sym OF [hEqEv];            (* oeq v e *)
                  val hEvenE = oeq_rw_S2 (Pev, vF, eFr) hEqVe hEvenV;   (* evenBody e *)
                in hEvenE end) end);
            val perEimp = impI_S2 (vpredBody (pFr, nF, eFr), evenBody eFr)
                            (Thm.implies_intr (ctermSub hVeP) res);   (* Imp(vpred p n e)(even e) *)
          in perEimp end;
        val innerForall = allI_S2 eBodyAbs (Thm.forall_intr (ctermSub eFr) perE);  (* Forall(%e. Imp(vpred p n e)(even e)) *)
        val d1 = impI_S2 (fourk3 pFr, innerAllE nF pFr) (Thm.implies_intr (ctermSub hF3P) innerForall);
        val d2 = impI_S2 (prime2 pFr, mkImp (fourk3 pFr) (innerAllE nF pFr)) (Thm.implies_intr (ctermSub hPpP) d1);
      in d2 end;   (* jT (hpInnerBody n p) *)
    val hpAll = allI_S2 pBodyAbs (Thm.forall_intr (ctermSub pFr) perP);  (* jT (hpBody n) *)
    (* Imp (sumsqBody n)(hpBody n) *)
    val ssImp = impI_S2 (sumsqBody nF, hpBody nF) (Thm.implies_intr (ctermSub hSSP) hpAll);
    (* 0<n ==> Imp (sumsqBody n)(hpBody n) *)
    val full = Thm.implies_intr (ctermSub hPosP) ssImp;
  in varify full end;
val () = out ("OIH_THM hyps="^Int.toString(length(Thm.hyps_of oiH_thm))^"\n");

local
  val nV = Free("n_oih", natT);
  val oih_intended = Logic.mk_implies (jT (lt ZeroC nV), jT (mkImp (sumsqBody nV)(hpBody nV)));
  val inst = beta_norm (Drule.infer_instantiate ctxtSub [(("n_oih",0), ctermSub nV)] (varify oiH_thm));
in
  val () = out ("OIH_THM aconv="^Bool.toString ((Thm.prop_of inst) aconv oih_intended)^"\n");
end;
val () = out "TSF_BRIDGE_OIH_OK\n";

(* ===========================================================================
   FINAL : twosquare_full (UNCONDITIONAL) on ctxtSub
     0<n ==> Conj (Imp (sumsqBody n)(hpBody n)) (Imp (hpBody n)(sumsqBody n))
   second conjunct = the PROVED if_direction ; first = the PROVED bridge oiH.
   (mirrors seat1_iff_assembly's mkConj, but oiH is now a THEOREM not a hyp.)
   =========================================================================== *)
val () = out "TSF_BRIDGE_FINAL_BEGIN\n";

(* if_direction instantiator on ctxtSub *)
val if_direction_vS = varify if_direction;
fun if_direction_atS nT =
  beta_norm (Drule.infer_instantiate ctxtSub [(("n_if",0), ctermSub nT)] if_direction_vS);

(* conjI on ctxtSub already: conjI_atSub *)
val twosquare_full =
  let
    val nF = Free("n_tsf", natT);
    val L  = sumsqBody nF;     (* sum of two squares *)
    val R  = hpBody nF;        (* universal per-prime even valuation *)
    val hPosP = jT (lt ZeroC nF); val hPos = Thm.assume (ctermSub hPosP);
    (* first conjunct : Imp L R  via the bridge oiH at n, mp'd with 0<n *)
    val oihAt = beta_norm (Drule.infer_instantiate ctxtSub [(("n_oih",0), ctermSub nF)] (varify oiH_thm));
    val onlyifObj = Thm.implies_elim oihAt hPos;   (* jT (Imp L R) -- only_if half, PROVED *)
    (* second conjunct : Imp R L via if_direction at n, mp'd with 0<n *)
    val ifAt = if_direction_atS nF;                (* jT (Imp (lt 0 n)(Imp R L)) *)
    val ifObj = mp_S2 (lt ZeroC nF, mkImp (hpBody nF) (sumsqBody nF)) ifAt hPos;  (* jT (Imp R L) *)
    val iffConj = conjI_atSub (mkImp L R, mkImp R L) onlyifObj ifObj;
    val body = Thm.implies_intr (ctermSub hPosP) iffConj;
  in varify body end;
val () = out ("TWOSQUARE_FULL hyps="^Int.toString(length(Thm.hyps_of twosquare_full))^"\n");

(* validation : 0-hyp + aconv the intended full biconditional *)
val twosquare_full_intended =
  let val nV = Var(("n_tsf",0), natT)
      val L = sumsqBody nV; val R = hpBody nV
  in Logic.mk_implies (jT (lt ZeroC nV), jT (mkConj (mkImp L R) (mkImp R L))) end;
val tsf_hyps = length (Thm.hyps_of twosquare_full);
val tsf_aconv = (Thm.prop_of twosquare_full) aconv twosquare_full_intended;
val () = out ("TWOSQUARE_FULL hyps="^Int.toString tsf_hyps^" aconv="^Bool.toString tsf_aconv^"\n");

(* soundness probe 1 : the SCG/oiH-style hypothesis is GONE -- the full thm is NOT
   aconv the seat1 modulo-bridge form (which had Imp L R as a SEPARATE hypothesis). *)
val tsf_modulo_bogus =
  let val nV = Var(("n_tsf",0), natT)
      val L = sumsqBody nV; val R = hpBody nV
  in Logic.mk_implies (jT (lt ZeroC nV),
       Logic.mk_implies (jT (mkImp L R),
         jT (mkConj (mkImp L R) (mkImp R L)))) end;
val tsf_probe_unconditional = not ((Thm.prop_of twosquare_full) aconv tsf_modulo_bogus);
val () = if tsf_probe_unconditional
         then out "PROBE_OK twosquare_full is UNCONDITIONAL (no Imp L R hypothesis)\n"
         else out "PROBE_FAIL twosquare_full still has the oiH hypothesis\n";
(* soundness probe 2 : second conjunct is genuinely R==>L, not a copy of L==>R *)
val tsf_collapse_bogus =
  let val nV = Var(("n_tsf",0), natT)
      val L = sumsqBody nV; val R = hpBody nV
  in Logic.mk_implies (jT (lt ZeroC nV), jT (mkConj (mkImp L R) (mkImp L R))) end;
val tsf_probe_iff = not ((Thm.prop_of twosquare_full) aconv tsf_collapse_bogus);
val () = if tsf_probe_iff then out "PROBE_OK twosquare_full second conjunct is R==>L (genuine iff)\n"
         else out "PROBE_FAIL twosquare_full second conjunct collapsed\n";
(* soundness probe 3 : keeps 0<n *)
val tsf_drop0_bogus =
  let val nV = Var(("n_tsf",0), natT)
      val L = sumsqBody nV; val R = hpBody nV
  in jT (mkConj (mkImp L R) (mkImp R L)) end;
val tsf_probe_pos = not ((Thm.prop_of twosquare_full) aconv tsf_drop0_bogus);
val () = if tsf_probe_pos then out "PROBE_OK twosquare_full keeps 0<n\n" else out "PROBE_FAIL twosquare_full dropped 0<n\n";

val () = if tsf_hyps = 0 andalso tsf_aconv andalso tsf_probe_unconditional andalso tsf_probe_iff andalso tsf_probe_pos
         then out "TWOSQUARE_FULL_OK\n" else out "TWOSQUARE_FULL_FAILED\n";

(* dump the final statement for the record *)
val () = out ("TWOSQUARE_FULL_PROP:\n" ^ Syntax.string_of_term ctxtSub (Thm.prop_of twosquare_full) ^ "\n");
val () = out "TSF_BRIDGE_SEAT2_DONE\n";
