(* ============================================================================
   FERMAT TWO-SQUARE FULL IFF — THE VALUATION TRANSFER (the if-direction crux)
   ----------------------------------------------------------------------------
   Appended AFTER  isabelle_twosquare.sml  +  if_direction.sml  (final context
   ctxtGR / ctermGR ; the full _gr / _r / _d / _g toolkit + euclid_lemma + pow
   + strong_induct + the natlist library are all in scope).

   GOAL.  The if-direction reduces (via the banked `prod_all_sumsq`) to: factor n
   into prime powers, classify each prime mod 4, and show every prime-power factor
   is a sum of two squares.  The non-trivial hypothesis is the per-prime relational
   even-valuation hypothesis H:

       H_pred n  ==  !p. prime2 p ==> (Ex k. p = 4k+3)
                          ==> !e. vpred p n e ==> Ex j. e = j+j

   where the RELATIONAL p-adic valuation predicate is

       vpred p n e  ==  Ex m. n = p^e * m  AND  ~(p | m)         (e is "the" valuation)

   The strong-induction if-direction peels a prime q's full power off n
   (n = q^v * m, ~(q|m)) and recurses on m.  For the IH it needs H to SURVIVE on
   the cofactor m.  THAT is the valuation transfer, proved here END-TO-END from
   euclid_lemma — WITHOUT any appeal to FTA (the key de-risking insight: the
   RELATIONAL valuation needs no FTA factorization function, only euclid).

   The deliverable:
     L1  val_mult_coprime : ~(p|a) ==> vpred p m e ==> vpred p (a*m) e    [THE transfer]
     L2  val_coprime_self : vpred p m e ==> ~(p|m) ==> e = 0              [self-coprime]
     L3  padic_split      : prime2 p ==> 0<n ==> Ex e m. n=p^e*m /\ ~p|m  [existence]
     L4  prime_div_eq     : prime2 p ==> prime2 q ==> p|q ==> p=q
     L5  prime_not_dvd_pow: prime2 p ==> prime2 q ==> ~(p=q) ==> ~(p|q^v)
     L6  val_transfer (THE CRUX) :
           prime2 q ==> ~(q|m) ==> n = q^v*m ==> H_pred n ==> H_pred m
         "dividing n by a coprime-free prime power preserves the per-prime
          even-valuation hypothesis on the cofactor."

   0 new axioms / consts / types over the monolith.  Only classical = ex_middle.
   ============================================================================ *)
val () = out "TSF_VALUATION_BEGIN\n";

(* ---------------------------------------------------------------------------
   base lemmas onto ctxtGR not already supplied by the if-direction toolkit
   --------------------------------------------------------------------------- *)
val euclid_lemma_gr = varify euclid_lemma;
fun euclid_at (pT,aT,bT) hPr hDvd =
  ((beta_norm (Drule.infer_instantiate ctxtGR
     [(("p",0), ctermGR pT),(("a",0), ctermGR aT),(("b",0), ctermGR bT)] euclid_lemma_gr)) OF [hPr]) OF [hDvd];

val dvd_le_gr = varify dvd_le;
fun dvd_le_at (dt,nt) hdvd hnz =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
     [(("d",0), ctermGR dt),(("n",0), ctermGR nt)] dvd_le_gr)) hdvd) hnz;

val Suc_neq_Zero_gr = varify Suc_neq_Zero_ax;
fun Suc_neq_Zero_at t = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR t)] Suc_neq_Zero_gr);

val ex_middle_gr = varify ex_middle_ax;
fun em_gr t = beta_norm (Drule.infer_instantiate ctxtGR [(("A",0), ctermGR t)] ex_middle_gr);

val disj_zos_gr = varify disj_zero_or_suc;
fun dzos_gr t = beta_norm (Drule.infer_instantiate ctxtGR [(("p",0), ctermGR t)] disj_zos_gr);
fun mkExSuc t = mkEx (Abs ("q", natT, oeq t (suc (Bound 0))));

val pow_Suc_gr2 = varify pow_Suc_ax;
fun powSuc_gr2 (at,nt) = beta_norm (Drule.infer_instantiate ctxtGR
     [(("a",0), ctermGR at),(("n",0), ctermGR nt)] pow_Suc_gr2);
val pow_Zero_gr2 = varify pow_Zero_ax;
fun powZero_gr2 t = beta_norm (Drule.infer_instantiate ctxtGR [(("a",0), ctermGR t)] pow_Zero_gr2);

val strong_induct_gr = varify strong_induct;
fun prime2_div_GR pt hpr = conjunct2_r (lt (suc ZeroC) pt, mkForall (ppAbs pt)) hpr;  (* Forall (ppAbs p) *)

fun dvdIntro_gr (pT, nT, w) hyp =
  let val Pabs = Abs("k", natT, oeq nT (mult pT (Bound 0))) in exI_r Pabs w hyp end;

(* ---------------------------------------------------------------------------
   vpred  (RELATIONAL p-adic valuation).  Capture-safe builders.
     dvd p m  inserts an inner Abs("k") ; build the m-existential with a fresh
     Free via Term.lambda so its Bound 0 cannot be captured by the inner k.
   --------------------------------------------------------------------------- *)
val mFrV = Free("m_vp", natT);
val eFrV = Free("e_vp", natT);
fun vpredBody (pT, nT, eT) =
   mkEx (Term.lambda mFrV (mkConj (oeq nT (mult (pow pT eT) mFrV)) (neg (dvd pT mFrV))));
fun vpredEBody pT nT = mkEx (Term.lambda eFrV (vpredBody (pT, nT, eFrV)));   (* Ex e m. ... *)
fun evenBody eT = mkEx (Abs("j", natT, oeq eT (add (Bound 0)(Bound 0))));    (* Ex j. e=j+j *)

val () = out "TSF_VAL_TERMS_OK\n";

(* ===========================================================================
   L1  val_mult_coprime  (THE forward transfer)
     prime2 p ==> ~(p|a) ==> vpred p m e ==> vpred p (a*m) e
   =========================================================================== *)
val val_mult_coprime =
  let
    val pT0 = Free("p", natT); val aT0 = Free("a", natT);
    val mT0 = Free("m", natT); val eT0 = Free("e", natT);
    val hPrP  = jT (prime2 pT0);                 val hPr  = Thm.assume (ctermGR hPrP);
    val hNaP  = jT (neg (dvd pT0 aT0));            val hNa  = Thm.assume (ctermGR hNaP);
    val hVmP  = jT (vpredBody (pT0, mT0, eT0));     val hVm  = Thm.assume (ctermGR hVmP);
    val goalC = vpredBody (pT0, mult aT0 mT0, eT0);
    val PabsM = Term.lambda mFrV (mkConj (oeq mT0 (mult (pow pT0 eT0) mFrV)) (neg (dvd pT0 mFrV)));
    val body = exE_r (PabsM, goalC) hVm "mw_vmc" natT (fn mwF => fn hConj =>
      let
        val hEq  = conjunct1_gr_at (oeq mT0 (mult (pow pT0 eT0) mwF), neg (dvd pT0 mwF)) hConj;
        val hNmw = conjunct2_gr_at (oeq mT0 (mult (pow pT0 eT0) mwF), neg (dvd pT0 mwF)) hConj;
        (* a*m = a*(p^e*mw) = (a*p^e)*mw = (p^e*a)*mw = p^e*(a*mw) *)
        val s1 = mult_cong_r_gr (aT0, mT0, mult (pow pT0 eT0) mwF) hEq;
        val s2 = oeqSym_r2 (multassoc_gr (aT0, pow pT0 eT0, mwF));
        val s3 = mult_cong_l_gr (mult aT0 (pow pT0 eT0), mult (pow pT0 eT0) aT0, mwF) (multcomm_gr (aT0, pow pT0 eT0));
        val s4 = multassoc_gr (pow pT0 eT0, aT0, mwF);
        val eqChain = oeqTrans_r2 (s1, oeqTrans_r2 (s2, oeqTrans_r2 (s3, s4)));   (* a*m = p^e*(a*mw) *)
        (* ~(p | a*mw) : euclid + ~p|a + ~p|mw *)
        val hDvdAmw = Thm.assume (ctermGR (jT (dvd pT0 (mult aT0 mwF))));
        val disj = euclid_at (pT0, aT0, mwF) hPr hDvdAmw;
        val caseA = let val hda = Thm.assume (ctermGR (jT (dvd pT0 aT0)))
                        val fls = mp_r (dvd pT0 aT0, oFalseC) hNa hda
                    in Thm.implies_intr (ctermGR (jT (dvd pT0 aT0))) fls end;
        val caseB = let val hdm = Thm.assume (ctermGR (jT (dvd pT0 mwF)))
                        val fls = mp_r (dvd pT0 mwF, oFalseC) hNmw hdm
                    in Thm.implies_intr (ctermGR (jT (dvd pT0 mwF))) fls end;
        val flsAmw = disjE_r (dvd pT0 aT0, dvd pT0 mwF, oFalseC) disj caseA caseB;
        val hNamwMeta = Thm.implies_intr (ctermGR (jT (dvd pT0 (mult aT0 mwF)))) flsAmw;
        val hNamw = impI_r (dvd pT0 (mult aT0 mwF), oFalseC) hNamwMeta;   (* OBJECT neg *)
        val conjG = conjI_gr_at (oeq (mult aT0 mT0) (mult (pow pT0 eT0) (mult aT0 mwF)),
                                 neg (dvd pT0 (mult aT0 mwF))) eqChain hNamw;
        val PabsG = Term.lambda mFrV (mkConj (oeq (mult aT0 mT0) (mult (pow pT0 eT0) mFrV)) (neg (dvd pT0 mFrV)));
      in exI_r PabsG (mult aT0 mwF) conjG end);
    val t3 = Thm.implies_intr (ctermGR hPrP) (Thm.implies_intr (ctermGR hNaP) (Thm.implies_intr (ctermGR hVmP) body));
  in varify t3 end;

local
  val pT0 = Free("p", natT); val aT0 = Free("a", natT);
  val mT0 = Free("m", natT); val eT0 = Free("e", natT);
  val vmc_intended = Logic.mk_implies (jT (prime2 pT0),
        Logic.mk_implies (jT (neg (dvd pT0 aT0)),
          Logic.mk_implies (jT (vpredBody (pT0, mT0, eT0)), jT (vpredBody (pT0, mult aT0 mT0, eT0)))));
  val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("p",0), ctermGR pT0),(("a",0), ctermGR aT0),(("m",0), ctermGR mT0),(("e",0), ctermGR eT0)] val_mult_coprime);
in
  val () = out ("VAL_MULT_COPRIME hyps="^Int.toString(length(Thm.hyps_of val_mult_coprime))
                ^" aconv="^Bool.toString((Thm.prop_of inst) aconv vmc_intended)^"\n");
  (* SOUNDNESS PROBE : the ~(p|a) coprimality hypothesis is genuinely load-bearing
     (dropping it gives a FALSE statement: vpred p m e ==> vpred p (a*m) e is wrong
      when p|a, e.g. a=p shifts the valuation up).  So the thm must NOT be aconv the
      hypothesis-dropped variant. *)
  val vmc_dropped = Logic.mk_implies (jT (prime2 pT0),
          Logic.mk_implies (jT (vpredBody (pT0, mT0, eT0)), jT (vpredBody (pT0, mult aT0 mT0, eT0))));
  val () = if not ((Thm.prop_of inst) aconv vmc_dropped)
           then out "PROBE_OK val_mult_coprime keeps the ~(p|a) hypothesis\n"
           else out "PROBE_FAIL val_mult_coprime dropped ~(p|a)\n";
end;

(* ===========================================================================
   L2  val_coprime_self
     vpred p m e ==> ~(p|m) ==> e = 0
   (if p does not divide m then m's p-adic valuation is 0)
   =========================================================================== *)
val val_coprime_self =
  let
    val pT0 = Free("p", natT); val mT0 = Free("m", natT); val eT0 = Free("e", natT);
    val hVmP = jT (vpredBody (pT0, mT0, eT0));   val hVm = Thm.assume (ctermGR hVmP);
    val hNmP = jT (neg (dvd pT0 mT0));            val hNm = Thm.assume (ctermGR hNmP);
    val goalC = oeq eT0 ZeroC;
    val PabsM = Term.lambda mFrV (mkConj (oeq mT0 (mult (pow pT0 eT0) mFrV)) (neg (dvd pT0 mFrV)));
    val body = exE_r (PabsM, goalC) hVm "mw_vcs" natT (fn mwF => fn hConj =>
      let
        val hEq = conjunct1_gr_at (oeq mT0 (mult (pow pT0 eT0) mwF), neg (dvd pT0 mwF)) hConj;
        val dz = dzos_gr eT0;
        val caseZ = let val hz = Thm.assume (ctermGR (jT (oeq eT0 ZeroC)))
                    in Thm.implies_intr (ctermGR (jT (oeq eT0 ZeroC))) hz end;
        val caseS = let val hsP = jT (mkExSuc eT0); val hs = Thm.assume (ctermGR hsP)
                        val inner = exE_r (Abs("q", natT, oeq eT0 (suc (Bound 0))), oeq eT0 ZeroC) hs "eq_vcs" natT (fn qF => fn hq =>
                          let
                            (* e = Suc q.  p^e = p*p^q.  m = p^e*mw = p*(p^q*mw) -> p|m -> contra ~p|m *)
                            val powCong = let val Pp = Abs("z", natT, oeq (pow pT0 eT0) (pow pT0 (Bound 0)))
                                          in oeq_rw_r (Pp, eT0, suc qF) hq (oeqRefl_r2 (pow pT0 eT0)) end;
                            val powSuc = powSuc_gr2 (pT0, qF);
                            val powE = oeqTrans_r2 (powCong, powSuc);     (* p^e = p*p^q *)
                            val e1 = mult_cong_l_gr (pow pT0 eT0, mult pT0 (pow pT0 qF), mwF) powE;
                            val e2 = multassoc_gr (pT0, pow pT0 qF, mwF);
                            val mEqP = oeqTrans_r2 (hEq, oeqTrans_r2 (e1, e2));   (* m = p*(p^q*mw) *)
                            val hdvd = dvdIntro_gr (pT0, mT0, mult (pow pT0 qF) mwF) mEqP;
                            val fls = mp_r (dvd pT0 mT0, oFalseC) hNm hdvd;
                          in oFalse_elim_r (oeq eT0 ZeroC) OF [fls] end)
                    in Thm.implies_intr (ctermGR hsP) inner end;
      in disjE_r (oeq eT0 ZeroC, mkExSuc eT0, oeq eT0 ZeroC) dz caseZ caseS end);
    val t2 = Thm.implies_intr (ctermGR hVmP) (Thm.implies_intr (ctermGR hNmP) body);
  in varify t2 end;

local
  val pT0 = Free("p", natT); val mT0 = Free("m", natT); val eT0 = Free("e", natT);
  val vcs_intended = Logic.mk_implies (jT (vpredBody (pT0, mT0, eT0)),
        Logic.mk_implies (jT (neg (dvd pT0 mT0)), jT (oeq eT0 ZeroC)));
  val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("p",0), ctermGR pT0),(("m",0), ctermGR mT0),(("e",0), ctermGR eT0)] val_coprime_self);
in
  val () = out ("VAL_COPRIME_SELF hyps="^Int.toString(length(Thm.hyps_of val_coprime_self))
                ^" aconv="^Bool.toString((Thm.prop_of inst) aconv vcs_intended)^"\n");
end;

(* ===========================================================================
   L4  prime_div_eq : prime2 p ==> prime2 q ==> p|q ==> p=q
   =========================================================================== *)
val prime_div_eq =
  let
    val pp = Free("p", natT); val qq = Free("q", natT);
    val hPrP = jT (prime2 pp); val hPr = Thm.assume (ctermGR hPrP);
    val hQrP = jT (prime2 qq); val hQr = Thm.assume (ctermGR hQrP);
    val hDpqP= jT (dvd pp qq);  val hDpq= Thm.assume (ctermGR hDpqP);
    val faQ  = prime2_div_GR qq hQr;
    val impAt= allE_r (ppAbs qq) pp faQ;
    val disj = mp_r (dvd pp qq, mkDisj (oeq pp (suc ZeroC)) (oeq pp qq)) impAt hDpq;
    val le2p = prime2_gt1_r pp hPr;
    val caseP1 = let val h1 = Thm.assume (ctermGR (jT (oeq pp (suc ZeroC))))
                     val z = Free("zpe1", natT); val Plt = Term.lambda z (lt (suc ZeroC) z)
                     val lt11 = oeq_rw_r (Plt, pp, suc ZeroC) h1 le2p
                     val fls = lt_irrefl_g (suc ZeroC) lt11
                 in Thm.implies_intr (ctermGR (jT (oeq pp (suc ZeroC)))) (Thm.implies_elim (oFalse_elim_r (oeq pp qq)) fls) end;
    val casePq = let val hq = Thm.assume (ctermGR (jT (oeq pp qq))) in Thm.implies_intr (ctermGR (jT (oeq pp qq))) hq end;
    val res = disjE_r (oeq pp (suc ZeroC), oeq pp qq, oeq pp qq) disj caseP1 casePq;
  in varify (Thm.implies_intr (ctermGR hPrP) (Thm.implies_intr (ctermGR hQrP) (Thm.implies_intr (ctermGR hDpqP) res))) end;

local
  val pp = Free("p", natT); val qq = Free("q", natT);
  val pde_intended = Logic.mk_implies (jT (prime2 pp),
        Logic.mk_implies (jT (prime2 qq), Logic.mk_implies (jT (dvd pp qq), jT (oeq pp qq))));
  val inst = beta_norm (Drule.infer_instantiate ctxtGR [(("p",0), ctermGR pp),(("q",0), ctermGR qq)] prime_div_eq);
in
  val () = out ("PRIME_DIV_EQ hyps="^Int.toString(length(Thm.hyps_of prime_div_eq))
                ^" aconv="^Bool.toString((Thm.prop_of inst) aconv pde_intended)^"\n");
end;

(* ===========================================================================
   L5  prime_not_dvd_pow : prime2 p ==> prime2 q ==> ~(p=q) ==> ~(p|q^v)
       (induction on v ; uses euclid_lemma + prime_div_eq)
   =========================================================================== *)
val prime_not_dvd_pow =
  let
    val pp = Free("p", natT); val qq = Free("q", natT);
    val hPrP = jT (prime2 pp); val hPr = Thm.assume (ctermGR hPrP);
    val hQrP = jT (prime2 qq); val hQr = Thm.assume (ctermGR hQrP);
    val hNeqP= jT (neg (oeq pp qq)); val hNeq = Thm.assume (ctermGR hNeqP);
    val vF = Free("v_pn", natT);
    val Rabs = Term.lambda vF (neg (dvd pp (pow qq vF)));
    (* base : ~(p | q^0) = ~(p|1) *)
    val base =
      let val hd1mP = jT (dvd pp (pow qq ZeroC)); val hd1m = Thm.assume (ctermGR hd1mP)
          val pz = powZero_gr2 qq
          val z = Free("zpn0", natT); val Pd = Term.lambda z (dvd pp z)
          val hdp1 = oeq_rw_r (Pd, pow qq ZeroC, suc ZeroC) pz hd1m   (* dvd p 1 *)
          val nz = let val he = Thm.assume (ctermGR (jT (oeq (suc ZeroC) ZeroC)))
                       val f = Suc_neq_Zero_at ZeroC OF [he]
                   in Thm.implies_intr (ctermGR (jT (oeq (suc ZeroC) ZeroC))) f end  (* META 1<>0 *)
          val lep1 = dvd_le_at (pp, suc ZeroC) hdp1 nz   (* le p 1 *)
          val le2p = prime2_gt1_r pp hPr                 (* le 2 p = lt 1 p *)
          val le21 = le_trans_d (suc (suc ZeroC), pp, suc ZeroC) le2p lep1  (* le 2 1 = lt 1 1 *)
          val fls = lt_irrefl_g (suc ZeroC) le21
          val negMeta = Thm.implies_intr (ctermGR hd1mP) fls
      in impI_r (dvd pp (pow qq ZeroC), oFalseC) negMeta end;
    (* step : !!x. ~(p|q^x) ==> ~(p|q^(Suc x)) *)
    val step =
      let val xF = Free("x_pn", natT)
          val hRxP = jT (neg (dvd pp (pow qq xF))); val hRx = Thm.assume (ctermGR hRxP)
          val hdsP = jT (dvd pp (pow qq (suc xF))); val hds = Thm.assume (ctermGR hdsP)
          val ps = powSuc_gr2 (qq, xF)
          val z = Free("zpns", natT); val Pd = Term.lambda z (dvd pp z)
          val hdqq = oeq_rw_r (Pd, pow qq (suc xF), mult qq (pow qq xF)) ps hds  (* p | q*q^x *)
          val disj = euclid_at (pp, qq, pow qq xF) hPr hdqq                       (* p|q \/ p|q^x *)
          val caseQ = let val hdq = Thm.assume (ctermGR (jT (dvd pp qq)))
                          val peq = (prime_div_eq OF [hPr]) OF [hQr] OF [hdq]      (* p=q *)
                          val fls = mp_r (oeq pp qq, oFalseC) hNeq peq
                      in Thm.implies_intr (ctermGR (jT (dvd pp qq))) fls end
          val caseQx= let val hdqx = Thm.assume (ctermGR (jT (dvd pp (pow qq xF))))
                          val fls = mp_r (dvd pp (pow qq xF), oFalseC) hRx hdqx
                      in Thm.implies_intr (ctermGR (jT (dvd pp (pow qq xF)))) fls end
          val flsS = disjE_r (dvd pp qq, dvd pp (pow qq xF), oFalseC) disj caseQ caseQx
          val rSuc = impI_r (dvd pp (pow qq (suc xF)), oFalseC) (Thm.implies_intr (ctermGR hdsP) flsS)
      in Thm.forall_intr (ctermGR xF) (Thm.implies_intr (ctermGR hRxP) rSuc) end;
    val vK = Free("vK_pn", natT);
    val indThm = nat_induct_r Rabs vK base step;   (* jT (neg (dvd p (pow q vK))) *)
  in varify (Thm.implies_intr (ctermGR hPrP) (Thm.implies_intr (ctermGR hQrP) (Thm.implies_intr (ctermGR hNeqP) indThm))) end;

local
  val pp = Free("p", natT); val qq = Free("q", natT); val vv = Free("v", natT);
  val pnp_intended = Logic.mk_implies (jT (prime2 pp),
        Logic.mk_implies (jT (prime2 qq),
          Logic.mk_implies (jT (neg (oeq pp qq)), jT (neg (dvd pp (pow qq vv))))));
  val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("p",0), ctermGR pp),(("q",0), ctermGR qq),(("vK_pn",0), ctermGR vv)] prime_not_dvd_pow);
in
  val () = out ("PRIME_NOT_DVD_POW hyps="^Int.toString(length(Thm.hyps_of prime_not_dvd_pow))
                ^" aconv="^Bool.toString((Thm.prop_of inst) aconv pnp_intended)^"\n");
end;

(* ===========================================================================
   L3  padic_split : prime2 p ==> 0<n ==> Ex e m. n = p^e*m /\ ~(p|m)
       (existence of the p-adic decomposition, by strong induction on n)
   =========================================================================== *)
val padic_split =
  let
    val pp = Free("p", natT);
    val hPrimeP = jT (prime2 pp); val hPrime = Thm.assume (ctermGR hPrimeP);
    fun predBody nT = mkImp (lt ZeroC nT) (vpredEBody pp nT);
    val nStep = Free("n_ps", natT);
    val GpropMeta = Logic.all (Free("m_g",natT))
          (Logic.mk_implies (jT (lt (Free("m_g",natT)) nStep), jT (predBody (Free("m_g",natT)))));
    val IHbox = Thm.assume (ctermGR GpropMeta);
    fun applyIH mT (ltThm:thm) = Thm.implies_elim (Thm.forall_elim (ctermGR mT) IHbox) ltThm;
    val hPosP = jT (lt ZeroC nStep);  val hPos = Thm.assume (ctermGR hPosP);
    val em = em_gr (dvd pp nStep);
    val goalC = vpredEBody pp nStep;
    (* CASE B : ~(p|n) -> e=0,m=n *)
    val caseB =
      let val hNdP = jT (neg (dvd pp nStep));  val hNd = Thm.assume (ctermGR hNdP)
          val pz = powZero_gr2 pp;
          val cz = mult_cong_l_gr (pow pp ZeroC, suc ZeroC, nStep) pz;
          val m1 = mult1l_gr nStep;
          val eqn = oeqSym_r2 (oeqTrans_r2 (cz, m1));
          val conjB = conjI_gr_at (oeq nStep (mult (pow pp ZeroC) nStep), neg (dvd pp nStep)) eqn hNd;
          val PabsM = Term.lambda mFrV (mkConj (oeq nStep (mult (pow pp ZeroC) mFrV)) (neg (dvd pp mFrV)));
          val exM = exI_r PabsM nStep conjB;
          val PabsE = Term.lambda eFrV (vpredBody (pp, nStep, eFrV));
          val exE0 = exI_r PabsE ZeroC exM;
      in Thm.implies_intr (ctermGR hNdP) exE0 end;
    (* CASE A : p|n -> n=p*n', n'<n, n'>=1, IH *)
    val caseA =
      let val hDP = jT (dvd pp nStep);  val hD = Thm.assume (ctermGR hDP)
          val PabsW = Abs("k", natT, oeq nStep (mult pp (Bound 0)))
          val inner = exE_r (PabsW, goalC) hD "np_ps" natT (fn npF => fn hnpEq =>
            let
              val dzNp = dzos_gr npF
              val posNp =
                let val caseZnp = let val hz = Thm.assume (ctermGR (jT (oeq npF ZeroC)))
                                      val cpz = mult_cong_r_gr (pp, npF, ZeroC) hz
                                      val p0  = mult0r_g pp
                                      val nEq0 = oeqTrans_r2 (hnpEq, oeqTrans_r2 (cpz, p0))
                                      val z = Free("z0np", natT); val Plt = Term.lambda z (lt ZeroC z)
                                      val lt00 = oeq_rw_r (Plt, nStep, ZeroC) nEq0 hPos
                                      val fls = lt_irrefl_g ZeroC lt00
                                  in Thm.implies_intr (ctermGR (jT (oeq npF ZeroC))) (Thm.implies_elim (oFalse_elim_r (lt ZeroC npF)) fls) end
                    val caseSnp = let val hsP = jT (mkExSuc npF); val hs = Thm.assume (ctermGR hsP)
                                      val b = exE_r (Abs("q",natT,oeq npF (suc (Bound 0))), lt ZeroC npF) hs "qnp" natT (fn qF => fn hq =>
                                                let val l0sq = lt_zero_suc_g qF
                                                    val z = Free("zsnp", natT); val Plt = Term.lambda z (lt ZeroC z)
                                                in oeq_rw_r (Plt, suc qF, npF) (oeqSym_r2 hq) l0sq end)
                                  in Thm.implies_intr (ctermGR hsP) b end
                in disjE_r (oeq npF ZeroC, mkExSuc npF, lt ZeroC npF) dzNp caseZnp caseSnp end
              (* n' < n : n' < n'+n' <= p*n' = n *)
              val ltNp2 = lt_p_2p npF posNp
              val le2p = prime2_gt1_r pp hPrime
              val lmm = mult_le_mono_g (npF, suc (suc ZeroC), pp) le2p
              val np2 = oeqTrans_r2 (multcomm_g (npF, suc (suc ZeroC)), two_p_eq_d npF)
              val npp = multcomm_g (npF, pp)
              val z1 = Free("zlm1", natT); val Pl1 = Term.lambda z1 (le z1 (mult npF pp))
              val lmm1 = oeq_rw_r (Pl1, mult npF (suc (suc ZeroC)), add npF npF) np2 lmm
              val z2 = Free("zlm2", natT); val Pl2 = Term.lambda z2 (le (add npF npF) z2)
              val lmm2 = oeq_rw_r (Pl2, mult npF pp, mult pp npF) npp lmm1
              val ltNpPn = le_trans_d (suc npF, add npF npF, mult pp npF) ltNp2 lmm2
              val z3 = Free("zlt3", natT); val Pl3 = Term.lambda z3 (lt npF z3)
              val ltNpN = oeq_rw_r (Pl3, mult pp npF, nStep) (oeqSym_r2 hnpEq) ltNpPn   (* lt n' n *)
              val predNp = applyIH npF ltNpN
              val vpE_np = mp_r (lt ZeroC npF, vpredEBody pp npF) predNp posNp   (* vpredE p n' *)
              val PabsEnp = Term.lambda eFrV (vpredBody (pp, npF, eFrV))
              val resA = exE_r (PabsEnp, goalC) vpE_np "ep_ps" natT (fn epF => fn hVe =>
                let
                  val PabsMnp = Term.lambda mFrV (mkConj (oeq npF (mult (pow pp epF) mFrV)) (neg (dvd pp mFrV)))
                in exE_r (PabsMnp, goalC) hVe "mp_ps" natT (fn mpF => fn hConj =>
                    let
                      val hNpEq2 = conjunct1_gr_at (oeq npF (mult (pow pp epF) mpF), neg (dvd pp mpF)) hConj
                      val hNmp   = conjunct2_gr_at (oeq npF (mult (pow pp epF) mpF), neg (dvd pp mpF)) hConj
                      val s1 = mult_cong_r_gr (pp, npF, mult (pow pp epF) mpF) hNpEq2
                      val s2 = oeqSym_r2 (multassoc_gr (pp, pow pp epF, mpF))
                      val pSuc = oeqSym_r2 (powSuc_gr2 (pp, epF))
                      val s3 = mult_cong_l_gr (mult pp (pow pp epF), pow pp (suc epF), mpF) pSuc
                      val nEq = oeqTrans_r2 (hnpEq, oeqTrans_r2 (s1, oeqTrans_r2 (s2, s3)))   (* n = p^(Suc e')*m' *)
                      val conjG = conjI_gr_at (oeq nStep (mult (pow pp (suc epF)) mpF), neg (dvd pp mpF)) nEq hNmp
                      val PabsMg = Term.lambda mFrV (mkConj (oeq nStep (mult (pow pp (suc epF)) mFrV)) (neg (dvd pp mFrV)))
                      val exMg = exI_r PabsMg mpF conjG
                      val PabsEg = Term.lambda eFrV (vpredBody (pp, nStep, eFrV))
                    in exI_r PabsEg (suc epF) exMg end) end)
            in resA end)
      in Thm.implies_intr (ctermGR hDP) inner end;
    val vpE = disjE_r (dvd pp nStep, neg (dvd pp nStep), goalC) em caseA caseB;
    val predN = impI_r (lt ZeroC nStep, vpredEBody pp nStep) (Thm.implies_intr (ctermGR hPosP) vpE);
    val stepAll = Thm.forall_intr (ctermGR nStep) (Thm.implies_intr (ctermGR GpropMeta) predN);
    val predAbs = Term.lambda nStep (predBody nStep);
    val si_inst = beta_norm (Drule.infer_instantiate ctxtGR [(("P",0), ctermGR predAbs),(("k",0), ctermGR nStep)] strong_induct_gr);
    val predNStep = Thm.implies_elim si_inst stepAll;          (* jT (predBody n), hyp = {hPrimeP} *)
    (* object-ify : prime2 p ==> 0<n ==> vpredE p n  (the relational existence statement) *)
    val obj = impI_r (prime2 pp, mkImp (lt ZeroC nStep) (vpredEBody pp nStep))
                (Thm.implies_intr (ctermGR hPrimeP) predNStep);
  in varify obj end;

local
  val pp = Free("p", natT); val nn = Free("n", natT);
  val ps_intended = jT (mkImp (prime2 pp) (mkImp (lt ZeroC nn) (vpredEBody pp nn)));
  val inst = beta_norm (Drule.infer_instantiate ctxtGR [(("p",0), ctermGR pp),(("n_ps",0), ctermGR nn)] padic_split);
in
  val () = out ("PADIC_SPLIT hyps="^Int.toString(length(Thm.hyps_of padic_split))
                ^" aconv="^Bool.toString((Thm.prop_of inst) aconv ps_intended)^"\n");
  (* PROBE : the ~(p|m) conjunct in the conclusion is genuinely present (not the
     trivially-true Ex e m. n = p^e*m which holds with e=0,m=n unconditionally). *)
  val ps_collapsed = jT (mkImp (prime2 pp) (mkImp (lt ZeroC nn)
        (mkEx (Term.lambda eFrV (mkEx (Term.lambda mFrV (oeq nn (mult (pow pp eFrV) mFrV))))))));
  val () = if not ((Thm.prop_of inst) aconv ps_collapsed)
           then out "PROBE_OK padic_split keeps the ~(p|m) maximality conjunct\n"
           else out "PROBE_FAIL padic_split dropped ~(p|m)\n";
end;

(* ===========================================================================
   L6  val_transfer  (THE CRUX — the valuation transfer for the if-direction)

     H_pred n  ==  Forall(%p. Imp (prime2 p)
                        (Imp (Ex k. p=4k+3)
                             (Forall(%e. Imp (vpred p n e) (Ex j. e=j+j)))))

     val_transfer : prime2 q ==> ~(q|m) ==> n = q^v*m ==> H_pred n ==> H_pred m

   i.e. dividing n by the prime power q^v (q coprime to the cofactor m) PRESERVES
   the per-prime even-valuation hypothesis on m.

   PROOF of H_pred m from H_pred n :  take any prime p, p=4k+3, and any e with
   vpred p m e ; show e even.  EM on (p=q):
     p=q : vpred q m e + ~(q|m)  --L2-->  e=0 = 0+0  (even).
     p<>q: ~(p|q^v) [L5] ; vpred p m e  --L1-->  vpred p (q^v*m) e
           ; rewrite q^v*m = n  ->  vpred p n e ; H_pred n at p,e  ->  e even.
   =========================================================================== *)
(* 4k+3 body as in oi_descent : %k. p = (((k+k)+k)+k) + Suc(Suc(Suc 0)) *)
fun fourk3Body pT = Abs("k", natT,
      oeq pT (add (add (add (add (Bound 0)(Bound 0))(Bound 0))(Bound 0)) (suc (suc (suc ZeroC)))));
fun fourk3 pT = mkEx (fourk3Body pT);

(* the per-prime even-valuation predicate over a fixed argument N (a nat term):
   %p. Imp (prime2 p) (Imp (fourk3 p) (Forall(%e. Imp (vpred p N e) (evenBody e)))) *)
val pFrH = Free("p_hp", natT);
val eFrH = Free("e_hp", natT);
fun innerAllE NT pT = mkForall (Term.lambda eFrH (mkImp (vpredBody (pT, NT, eFrH)) (evenBody eFrH)));
fun hpInnerBody NT pT = mkImp (prime2 pT) (mkImp (fourk3 pT) (innerAllE NT pT));
fun hpBody NT = mkForall (Term.lambda pFrH (hpInnerBody NT pFrH));

val val_transfer =
  let
    val qq = Free("q", natT); val mm = Free("m", natT);
    val vv = Free("v", natT); val nn = Free("n", natT);
    val hQrP  = jT (prime2 qq);                  val hQr  = Thm.assume (ctermGR hQrP);
    val hNqmP = jT (neg (dvd qq mm));             val hNqm = Thm.assume (ctermGR hNqmP);
    val hEqP  = jT (oeq nn (mult (pow qq vv) mm)); val hEq  = Thm.assume (ctermGR hEqP);
    val hHnP  = jT (hpBody nn);                    val hHn  = Thm.assume (ctermGR hHnP);
    (* goal : H_pred m = Forall(%p. ...) ; prove by allI_r over a fresh p *)
    val goalAll = hpBody mm;
    val pBody = Term.lambda pFrH (hpInnerBody mm pFrH);   (* the predicate abstraction *)
    (* per-p proof : jT (hpInnerBody m pFr) for fresh pFr *)
    val pFr = Free("p_vt", natT);
    val perP =
      let
        val hPpP = jT (prime2 pFr); val hPp = Thm.assume (ctermGR hPpP);
        val hF3P = jT (fourk3 pFr); val hF3 = Thm.assume (ctermGR hF3P);
        (* inner Forall(%e. Imp (vpred p m e)(even e)) : allI_r over fresh e *)
        val eFr = Free("e_vt", natT);
        val eBody = Term.lambda eFr (mkImp (vpredBody (pFr, mm, eFr)) (evenBody eFr));
        val perE =
          let
            val hVpmP = jT (vpredBody (pFr, mm, eFr)); val hVpm = Thm.assume (ctermGR hVpmP);
            (* EM on p=q *)
            val em = em_gr (oeq pFr qq);   (* Disj (p=q)(~p=q) *)
            (* case p=q : vpred q m e (rewrite p->q) + ~q|m -> e=0 -> even *)
            val caseEq =
              let val hpq = Thm.assume (ctermGR (jT (oeq pFr qq)))
                  (* rewrite vpred p m e -> vpred q m e via p->q *)
                  val zv = Free("zvpq", natT); val Pv = Term.lambda zv (vpredBody (zv, mm, eFr))
                  val hVqm = oeq_rw_r (Pv, pFr, qq) hpq hVpm   (* vpred q m e *)
                  (* val_coprime_self at q,m,e *)
                  val vcsAt = beta_norm (Drule.infer_instantiate ctxtGR
                                [(("p",0), ctermGR qq),(("m",0), ctermGR mm),(("e",0), ctermGR eFr)] val_coprime_self)
                  val e0 = Thm.implies_elim (Thm.implies_elim vcsAt hVqm) hNqm  (* oeq e 0 *)
                  (* even : Ex j. e = j+j with j=0 : e=0=0+0 *)
                  val a00 = add0_gr ZeroC   (* 0+0 = 0 *)
                  val ev0 = oeqTrans_r2 (e0, oeqSym_r2 a00)   (* e = 0+0 *)
                  val evEx = exI_r (Abs("j", natT, oeq eFr (add (Bound 0)(Bound 0)))) ZeroC ev0
              in Thm.implies_intr (ctermGR (jT (oeq pFr qq))) evEx end
            (* case p<>q : ~p|q^v ; vpred p m e -L1-> vpred p (q^v*m) e ; = vpred p n e ; H_pred n -> even *)
            val caseNeq =
              let val hnpq = Thm.assume (ctermGR (jT (neg (oeq pFr qq))))
                  (* ~(p | q^v) *)
                  val pnpAt = beta_norm (Drule.infer_instantiate ctxtGR
                                [(("p",0), ctermGR pFr),(("q",0), ctermGR qq),(("vK_pn",0), ctermGR vv)] prime_not_dvd_pow)
                  val hNpqv = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim pnpAt hPp) hQr) hnpq   (* ~p|q^v *)
                  (* val_mult_coprime at p, a=q^v, m, e : vpred p m e -> vpred p (q^v*m) e *)
                  val vmcAt = beta_norm (Drule.infer_instantiate ctxtGR
                                [(("p",0), ctermGR pFr),(("a",0), ctermGR (pow qq vv)),
                                 (("m",0), ctermGR mm),(("e",0), ctermGR eFr)] val_mult_coprime)
                  val hVpqvm = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim vmcAt hPp) hNpqv) hVpm  (* vpred p (q^v*m) e *)
                  (* rewrite q^v*m -> n via hEq sym : vpred p n e *)
                  val zn = Free("zvtn", natT); val Pn = Term.lambda zn (vpredBody (pFr, zn, eFr))
                  val hVpn = oeq_rw_r (Pn, mult (pow qq vv) mm, nn) (oeqSym_r2 hEq) hVpqvm  (* vpred p n e *)
                  (* apply H_pred n at p : Forall(%p. ...) -> Imp(prime2 p)(Imp(fourk3 p)(Forall(%e...))) *)
                  val hHnAtP = allE_r (Term.lambda pFrH (hpInnerBody nn pFrH)) pFr hHn   (* hpInnerBody n p *)
                  val step1  = mp_r (prime2 pFr, mkImp (fourk3 pFr) (innerAllE nn pFr)) hHnAtP hPp
                  val step2  = mp_r (fourk3 pFr, innerAllE nn pFr) step1 hF3            (* Forall(%e. Imp(vpred p n e)(even e)) *)
                  val hAtE   = allE_r (Term.lambda eFrH (mkImp (vpredBody (pFr, nn, eFrH)) (evenBody eFrH))) eFr step2  (* Imp(vpred p n e)(even e) *)
                  val evn    = mp_r (vpredBody (pFr, nn, eFr), evenBody eFr) hAtE hVpn   (* even e *)
              in Thm.implies_intr (ctermGR (jT (neg (oeq pFr qq)))) evn end
            val evE = disjE_r (oeq pFr qq, neg (oeq pFr qq), evenBody eFr) em caseEq caseNeq  (* even e *)
            val perEimp = impI_r (vpredBody (pFr, mm, eFr), evenBody eFr) (Thm.implies_intr (ctermGR hVpmP) evE)  (* Imp(vpred p m e)(even e) *)
          in perEimp end;
        (* generalise e -> inner Forall *)
        val innerForall = allI_r eBody (Thm.forall_intr (ctermGR eFr) perE)   (* Forall(%e. Imp(vpred p m e)(even e)) *)
        (* discharge fourk3 p and prime2 p as object Imps *)
        val d1 = impI_r (fourk3 pFr, innerAllE mm pFr) (Thm.implies_intr (ctermGR hF3P) innerForall)
        val d2 = impI_r (prime2 pFr, mkImp (fourk3 pFr) (innerAllE mm pFr)) (Thm.implies_intr (ctermGR hPpP) d1)
      in d2 end;   (* jT (hpInnerBody m p) *)
    val allM = allI_r pBody (Thm.forall_intr (ctermGR pFr) perP)   (* jT (H_pred m) *)
    val t = Thm.implies_intr (ctermGR hQrP)
              (Thm.implies_intr (ctermGR hNqmP)
                (Thm.implies_intr (ctermGR hEqP)
                  (Thm.implies_intr (ctermGR hHnP) allM)))
  in varify t end;

local
  val qq = Free("q", natT); val mm = Free("m", natT); val vv = Free("v", natT); val nn = Free("n", natT);
  val vt_intended = Logic.mk_implies (jT (prime2 qq),
        Logic.mk_implies (jT (neg (dvd qq mm)),
          Logic.mk_implies (jT (oeq nn (mult (pow qq vv) mm)),
            Logic.mk_implies (jT (hpBody nn), jT (hpBody mm)))));
  val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("q",0), ctermGR qq),(("m",0), ctermGR mm),(("v",0), ctermGR vv),(("n",0), ctermGR nn)] val_transfer);
  val nh = length (Thm.hyps_of val_transfer);
  val ac = (Thm.prop_of inst) aconv vt_intended;
in
  val () = out ("VAL_TRANSFER hyps="^Int.toString nh^" aconv="^Bool.toString ac^"\n");
  (* SOUNDNESS PROBE 1 : the coprimality hypothesis ~(q|m) is genuinely load-bearing
     (without it the cofactor's q-valuation need not be 0 / the transfer is false). *)
  val vt_drop_coprime = Logic.mk_implies (jT (prime2 qq),
        Logic.mk_implies (jT (oeq nn (mult (pow qq vv) mm)),
          Logic.mk_implies (jT (hpBody nn), jT (hpBody mm))));
  val () = if not ((Thm.prop_of inst) aconv vt_drop_coprime)
           then out "PROBE_OK val_transfer keeps the ~(q|m) coprimality hyp\n"
           else out "PROBE_FAIL val_transfer dropped ~(q|m)\n";
  (* SOUNDNESS PROBE 2 : the conclusion is H_pred m, NOT the trivially-derivable
     H_pred n again (the transfer genuinely moves the hypothesis to the cofactor). *)
  val vt_trivial = Logic.mk_implies (jT (prime2 qq),
        Logic.mk_implies (jT (neg (dvd qq mm)),
          Logic.mk_implies (jT (oeq nn (mult (pow qq vv) mm)),
            Logic.mk_implies (jT (hpBody nn), jT (hpBody nn)))));
  val () = if not ((Thm.prop_of inst) aconv vt_trivial)
           then out "PROBE_OK val_transfer concludes H_pred m (the cofactor), not H_pred n\n"
           else out "PROBE_FAIL val_transfer conclusion collapsed to H_pred n\n";
  (* SOUNDNESS PROBE 3 : the per-prime EVEN-valuation content (Ex j. e=j+j) is
     genuinely present in BOTH the hypothesis and conclusion (not collapsed to a
     vacuous predicate).  Build the variant H'_pred whose inner conjunct is the
     TRIVIALLY-TRUE (Ex j. oeq j j) instead of (Ex j. e = j+j) ; the proved thm
     must NOT be aconv the H'-transfer (which would mean the even content is dead). *)
  fun evenTriv eT = mkEx (Abs("j", natT, oeq (Bound 0) (Bound 0)));   (* Ex j. j=j  (always true) *)
  fun innerAllE' NT pT = mkForall (Term.lambda eFrH (mkImp (vpredBody (pT, NT, eFrH)) (evenTriv eFrH)));
  fun hpInnerBody' NT pT = mkImp (prime2 pT) (mkImp (fourk3 pT) (innerAllE' NT pT));
  fun hpBody' NT = mkForall (Term.lambda pFrH (hpInnerBody' NT pFrH));
  val vt_triv_even = Logic.mk_implies (jT (prime2 qq),
        Logic.mk_implies (jT (neg (dvd qq mm)),
          Logic.mk_implies (jT (oeq nn (mult (pow qq vv) mm)),
            Logic.mk_implies (jT (hpBody' nn), jT (hpBody' mm)))));
  val () = if not ((Thm.prop_of inst) aconv vt_triv_even)
           then out "PROBE_OK val_transfer carries the even-valuation content (Ex j. e=j+j)\n"
           else out "PROBE_FAIL val_transfer even content is vacuous\n";
  val () = if nh = 0 andalso ac then out "VAL_TRANSFER_CLOSED\n"
           else out ("VAL_TRANSFER_FAILED hyps="^Int.toString nh^" aconv="^Bool.toString ac^"\n");
end;

val () = out "TSF_VALUATION_DONE\n";
