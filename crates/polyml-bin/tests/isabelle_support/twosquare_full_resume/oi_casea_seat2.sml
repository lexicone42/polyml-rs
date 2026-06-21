(* ============================================================================
   FERMAT TWO-SQUARE FULL IFF — ONLY-IF direction, SEAT 2
   Route: rebuild caseA closely mirroring the WORKING caseB structure, then
   assemble only_if via strong_induct.

   This file is APPENDED after:  ts_key_lemma.sml ; oi_arith.sml ; oi_descent.sml
   (which define the spine + all 11 arith helpers + caseB_arm + Pred/conclBody/
    sumsqBody/predBody + applyIH + build_concl + dzosSub_at etc.)

   It RE-DEFINES caseA from scratch (does NOT load oi_casea.sml — that one has
   the meta/object disjE-combine bug).  caseB_meta mirrors caseB_arm but kept as
   a META implication for the EM-on-(dvd p n) split.
   ============================================================================ *)
val () = out "OI_SEAT2_BEGIN\n";

(* dzos on Sub : Disj (oeq t 0)(Ex q. oeq t (Suc q)) *)
val disj_zero_or_suc_vSub = varify disj_zero_or_suc;
fun dzosSub_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("p",0), ctermSub t)] disj_zero_or_suc_vSub);

(* ----------------------------------------------------------------------------
   caseA as a META implication :  jT (dvd p n) ==> jT (conclBody n)
   (the p|n descent case).  Built by mirroring caseB_arm's internal structure:
   assume the hyp, build conclBody n, discharge with Thm.implies_intr.
   ---------------------------------------------------------------------------- *)
val caseA_meta =
  let
    val hDnP = jT (dvd pp_free nStep);
    val hDn  = Thm.assume (ctermSub hDnP);
    val ppT  = mult pp_free pp_free;   (* pp = p*p *)

    (* exE a, exE b from hSS : jT (sumsqBody n) *)
    val ssAbsA = Abs("a", natT, mkEx (Abs("b", natT,
                   oeq nStep (add (mult (Bound 1)(Bound 1)) (mult (Bound 0)(Bound 0))))));
    fun afterA aT (hExB : thm) =
      let
        val ssAbsB = Abs("b", natT, oeq nStep (add (mult aT aT) (mult (Bound 0)(Bound 0))));
        fun afterB bT (hN : thm) =     (* hN : jT (oeq n (a*a + b*b)) *)
          let
            val () = out "OI_S2_afterB\n";
            (* dvd p (a*a+b*b) from dvd p n + hN *)
            val hDab = dvd_cong_argSub (pp_free, nStep, add (mult aT aT)(mult bT bT)) hN hDn;
            val conj = key_onlyif_at (pp_free, aT, bT) hPrime h4k3 hDab;  (* conj(p|a)(p|b) *)
            val hPa  = conjunct1_atSub (dvd pp_free aT, dvd pp_free bT) conj;
            val hPb  = conjunct2_atSub (dvd pp_free aT, dvd pp_free bT) conj;
            val () = out "OI_S2_keyonlyif\n";
            (* extract a', b' *)
            fun afterAp apT (hAeq : thm) =   (* hAeq : oeq a (mult p a') *)
              let
                fun afterBp bpT (hBeq : thm) =  (* hBeq : oeq b (mult p b') *)
                  let
                    val () = out "OI_S2_afterBp\n";
                    val a2  = mult aT aT;  val b2 = mult bT bT;
                    val x2  = mult apT apT; val y2 = mult bpT bpT;
                    val nprime = add x2 y2;          (* n' = a'^2 + b'^2 *)
                    val hA2 = sq_factor_at (aT, pp_free, apT, hAeq);  (* oeq (a^2)(pp * a'^2) *)
                    val hB2 = sq_factor_at (bT, pp_free, bpT, hBeq);  (* oeq (b^2)(pp * b'^2) *)
                    val hNfac = factor_n_at (nStep, a2, b2, ppT, x2, y2, hN, hA2, hB2); (* oeq n (pp * n') *)
                    val () = out "OI_S2_factor_n\n";
                    val dz = dzosSub_at nprime;     (* Disj (oeq n' 0)(Ex q. oeq n' (Suc q)) *)
                    val goalC = conclBody nStep;
                    (* ---- case n'=0 : contra (META arm) ---- *)
                    val caseZ =
                      let
                        val hz = Thm.assume (ctermSub (jT (oeq nprime ZeroC)));   (* oeq n' 0 *)
                        val cpp0 = mult_cong_rS2 (ppT, nprime, ZeroC) hz;          (* oeq (pp*n')(pp*0) *)
                        val pp0  = mult0r_atSub ppT;                               (* oeq (pp*0) 0 *)
                        val nEq0 = oeq_trans OF [hNfac, oeq_trans OF [cpp0, pp0]]; (* oeq n 0 *)
                        fun posBody wT (hw : thm) =  (* hw : oeq n (add (Suc 0) w) *)
                          let
                            val hw0 = oeq_trans OF [oeq_sym OF [nEq0], hw];  (* oeq 0 (add (Suc 0) w) *)
                            val aS  = addSucS2_at (ZeroC, wT);              (* add (Suc 0) w = Suc(add 0 w) *)
                            val o0w = oeq_trans OF [hw0, aS];               (* oeq 0 (Suc(add 0 w)) *)
                            val o0wS= oeq_sym OF [o0w];                     (* oeq (Suc(add 0 w)) 0 *)
                            val fls = (Suc_neq_Zero_atSub (add ZeroC wT)) OF [o0wS]; (* oFalse *)
                          in Thm.implies_elim (oFalse_elimSub_at goalC) fls end;
                        val posWAbs = Abs("w", natT, oeq nStep (add (suc ZeroC)(Bound 0)));
                        val fromPos = exESub_elim (posWAbs, goalC) hPos "wpos" posBody;
                      in Thm.implies_intr (ctermSub (jT (oeq nprime ZeroC))) fromPos end;
                    val () = out "OI_S2_caseZ_OK\n";
                    (* ---- case n'=Suc q : the real descent (META arm) ---- *)
                    val caseSq =
                      let
                        val qsAbs = Abs("q", natT, oeq nprime (suc (Bound 0)));  (* Ex q. n' = Suc q *)
                        fun sqBody qT (hq : thm) =   (* hq : oeq n' (Suc q) *)
                          let
                            val hPosNp = lt0_suc_at qT;   (* lt 0 (Suc q) *)
                            val hqS = oeq_sym OF [hq];    (* oeq (Suc q) n' *)
                            val zLt0 = Free("zlt0", natT);
                            val PabsLt = Term.lambda zLt0 (lt ZeroC zLt0);   (* capture-safe *)
                            val hPosNprime = beta_norm (Drule.infer_instantiate ctxtSub
                                  [(("P",0), ctermSub PabsLt), (("a",0), ctermSub (suc qT)),
                                   (("b",0), ctermSub nprime)] oeq_subst_vS2) OF [hqS, hPosNp];  (* lt 0 n' *)
                            (* extract p = Suc(Suc t) *)
                            val ltp = prime2_gt1_atSub pp_free hPrime;  (* lt 1 p = Ex t. oeq p (add 2 t) *)
                            fun ptBody tT (ht2 : thm) =  (* ht2 : oeq p (add (Suc(Suc 0)) t) *)
                              let
                                val a1 = addSucS2_at (suc ZeroC, tT);   (* add (Suc(Suc 0)) t = Suc(add (Suc 0) t) *)
                                val a2x= addSucS2_at (ZeroC, tT);       (* add (Suc 0) t = Suc(add 0 t) *)
                                val a0 = add0S2_at tT;                  (* add 0 t = t *)
                                val a2S= Suc_cong OF [oeq_trans OF [a2x, Suc_cong OF [a0]]]; (* Suc(add (Suc 0) t) = Suc(Suc t) *)
                                val pSS = oeq_trans OF [ht2, oeq_trans OF [a1, a2S]];  (* oeq p (Suc(Suc t)) *)
                                val hPP = pp_suc2_at (pp_free, tT, pSS);  (* oeq (p*p)(Suc(Suc S)) *)
                                val sS  = add tT (mult (suc tT) pp_free);
                                val ltSelf = lt_self_mult_at (ppT, nprime, sS, qT, hPP, hq);  (* lt n' (pp*n') *)
                                val hNfacS = oeq_sym OF [hNfac];   (* oeq (pp*n') n *)
                                val zLt2 = Free("zlt2", natT);
                                val PabsLt2 = Term.lambda zLt2 (lt nprime zLt2);   (* capture-safe *)
                                val ltNpN = beta_norm (Drule.infer_instantiate ctxtSub
                                      [(("P",0), ctermSub PabsLt2), (("a",0), ctermSub (mult ppT nprime)),
                                       (("b",0), ctermSub nStep)] oeq_subst_vS2) OF [hNfacS, ltSelf]; (* lt n' n *)
                                val () = out "OI_S2_ltNpN\n";
                                (* applyIH n' (lt n' n) -> predBody n' = Imp(Hpre n')(conclBody n') *)
                                val predNp = applyIH nprime ltNpN;     (* jT (predBody n') *)
                                (* build Hpre n' = Conj(lt 0 n')(sumsqBody n') *)
                                val nprimeReflSS = oeqreflS2_at nprime;  (* oeq n' n' *)
                                val ssInnerB = Abs("b", natT, oeq nprime (add (mult apT apT)(mult (Bound 0)(Bound 0))));
                                val exBnp = exISub_at ssInnerB bpT nprimeReflSS;  (* Ex b. oeq n' (a'^2 + b^2) *)
                                val ssInnerA = Abs("a", natT, mkEx (Abs("b", natT,
                                                  oeq nprime (add (mult (Bound 1)(Bound 1))(mult (Bound 0)(Bound 0))))));
                                val exAnp = exISub_at ssInnerA apT exBnp;        (* sumsqBody n' *)
                                val hpreNp = conjI_atSub (lt ZeroC nprime, sumsqBody nprime) hPosNprime exAnp;
                                (* mp predNp hpreNp -> conclBody n' *)
                                val conclNp = mp_S2 (mkConj (lt ZeroC nprime)(sumsqBody nprime), conclBody nprime) predNp hpreNp;
                                val () = out "OI_S2_conclNp\n";
                                (* exE v', exE m' from conclNp *)
                                fun afterV vpT (hExM : thm) =   (* hExM : Ex m. cbInner n' (v', m) *)
                                  let
                                    fun afterM mpT (hCb : thm) =  (* hCb : cbInner n' (v', m') *)
                                      let
                                        val () = out "OI_S2_afterM\n";
                                        val hEqNp = conjunct1_atSub (oeq nprime (mult (pow pp_free vpT) mpT),
                                                       mkConj (neg (dvd pp_free mpT))(mkEx (Abs("j",natT, oeq vpT (add (Bound 0)(Bound 0)))))) hCb;
                                        val hRest = conjunct2_atSub (oeq nprime (mult (pow pp_free vpT) mpT),
                                                       mkConj (neg (dvd pp_free mpT))(mkEx (Abs("j",natT, oeq vpT (add (Bound 0)(Bound 0)))))) hCb;
                                        val hNdvdMp = conjunct1_atSub (neg (dvd pp_free mpT),
                                                        mkEx (Abs("j",natT, oeq vpT (add (Bound 0)(Bound 0))))) hRest;
                                        val hEvenVp = conjunct2_atSub (neg (dvd pp_free mpT),
                                                        mkEx (Abs("j",natT, oeq vpT (add (Bound 0)(Bound 0))))) hRest; (* Ex j. oeq v' (j+j) *)
                                        val () = out "OI_S2_projections_OK\n";
                                        (* build conclBody n with v = Suc(Suc v'), m = m' *)
                                        val vNew = suc (suc vpT);
                                        val e1 = mult_cong_rS2 (ppT, nprime, mult (pow pp_free vpT) mpT) hEqNp; (* pp*n' = pp*(pow p v' * m') *)
                                        val nEq1 = oeq_trans OF [hNfac, e1];   (* oeq n (pp*(pow p v' * m')) *)
                                        val assoc = multassocS2_at (ppT, pow pp_free vpT, mpT); (* (pp*pow p v')*m' = pp*(pow p v' * m') *)
                                        val assocS = oeq_sym OF [assoc];       (* pp*(pow p v' * m') = (pp*pow p v')*m' *)
                                        val nEq2 = oeq_trans OF [nEq1, assocS]; (* oeq n ((pp*pow p v')*m') *)
                                        val pstep = pow_step_at (pp_free, vpT); (* pow p (SSv') = pp*pow p v' *)
                                        val pstepS= oeq_sym OF [pstep];        (* pp*pow p v' = pow p (SSv') *)
                                        val congM = mult_cong_lS2 (mult ppT (pow pp_free vpT), pow pp_free vNew, mpT) pstepS; (* (pp*pow p v')*m' = pow p (SSv') * m' *)
                                        val hEqnNew = oeq_trans OF [nEq2, congM];  (* oeq n (pow p (SSv') * m') *)
                                        val () = out "OI_S2_hEqnNew\n";
                                        (* Ex j. oeq (SSv') (j+j) : exE j' from hEvenVp, even_step, exI (Suc j') *)
                                        fun afterJ jpT (hVeven : thm) =  (* hVeven : oeq v' (add j' j') *)
                                          let
                                            val hSSeven = even_step_at (vpT, jpT, hVeven);  (* oeq (SSv')(add (Suc j')(Suc j')) *)
                                            val evNewAbs = Abs("j", natT, oeq vNew (add (Bound 0)(Bound 0)));
                                            val exJnew = exISub_at evNewAbs (suc jpT) hSSeven;  (* Ex j. oeq (SSv')(j+j) *)
                                            val res = build_concl (vNew, mpT, hEqnNew, hNdvdMp, exJnew);
                                            val () = out "OI_S2_build_concl_OK\n";
                                          in res end;
                                        val evJpAbs = Abs("j", natT, oeq vpT (add (Bound 0)(Bound 0)));
                                      in exESub_elim (evJpAbs, goalC) hEvenVp "jp" afterJ end;
                                    val cbMAbs = Term.lambda mFr0 (cbInner nprime (vpT, mFr0));
                                  in exESub_elim (cbMAbs, goalC) hExM "mp" afterM end;
                                val cbVAbs = Term.lambda vFr0 (mkEx (Term.lambda mFr0 (cbInner nprime (vFr0, mFr0))));
                              in exESub_elim (cbVAbs, goalC) conclNp "vp" afterV end;
                          in exESub_elim (Abs("t", natT, oeq pp_free (add (suc(suc ZeroC))(Bound 0))), goalC) ltp "tp" ptBody end;
                        val ig = exESub_elim (qsAbs, goalC) (Thm.assume (ctermSub (jT (mkEx qsAbs)))) "qd" sqBody;
                      in Thm.implies_intr (ctermSub (jT (mkEx qsAbs))) ig end;
                    val () = out "OI_S2_caseSq_OK\n";
                    (* combine via disjE_elimSub : feed the META arms caseZ / caseSq DIRECTLY
                       (the bug in oi_casea.sml was wrapping them in impI_S2 first). *)
                    val combined = disjE_elimSub
                                     (oeq nprime ZeroC, mkEx (Abs("q",natT, oeq nprime (suc (Bound 0)))), conclBody nStep)
                                     dz caseZ caseSq;
                    val () = out "OI_S2_disjE_OK\n";
                  in combined end;
                val bpAbs = Abs("k", natT, oeq bT (mult pp_free (Bound 0)));
              in exESub_elim (bpAbs, conclBody nStep) hPb "bp" afterBp end;
            val apAbs = Abs("k", natT, oeq aT (mult pp_free (Bound 0)));
          in exESub_elim (apAbs, conclBody nStep) hPa "ap" afterAp end;
      in exESub_elim (ssAbsB, conclBody nStep) hExB "bb" afterB end;
    val resA = exESub_elim (ssAbsA, conclBody nStep) hSS "aa" afterA;
  in Thm.implies_intr (ctermSub hDnP) resA end;   (* META : jT(dvd p n) ==> jT(conclBody n) *)

val () = out "OI_CASEA_META_BUILT\n";

(* sanity : wrap to OBJECT and aconv-check (same shape caseB_arm advertises) *)
val caseA_arm = impI_S2 (dvd pp_free nStep, conclBody nStep) caseA_meta;
val () = out ("OI_CASEA_OK aconv-impl="^
  Bool.toString ((Thm.prop_of caseA_arm) aconv (jT (mkImp (dvd pp_free nStep) (conclBody nStep))))^"\n");

(* ----------------------------------------------------------------------------
   caseB as a META implication too (mirror caseB_arm but stop before impI_S2).
   caseB_arm in oi_descent.sml ends in impI_S2; rebuild the META form here.
   ---------------------------------------------------------------------------- *)
val caseB_meta =
  let
    val hNdP = jT (neg (dvd pp_free nStep));
    val hNd  = Thm.assume (ctermSub hNdP);
    val pz   = powZeroS2_at pp_free;
    val cz   = mult_cong_lS2 (pow pp_free ZeroC, suc ZeroC, nStep) pz;
    val m1   = mult1lSub_at nStep;
    val eqn  = oeq_sym OF [oeq_trans OF [cz, m1]];          (* oeq n (mult (pow p 0) n) *)
    val a00  = add0S2_at ZeroC;
    val ev0  = oeq_sym OF [a00];                            (* oeq 0 (add 0 0) *)
    val evJabs = Abs("j", natT, oeq ZeroC (add (Bound 0)(Bound 0)));
    val evEx = exISub_at evJabs ZeroC ev0;                  (* jT (Ex j. oeq 0 (add j j)) *)
    val exV  = build_concl (ZeroC, nStep, eqn, hNd, evEx);  (* jT (conclBody n) *)
  in Thm.implies_intr (ctermSub hNdP) exV end;             (* META : jT(neg(dvd p n)) ==> jT(conclBody n) *)

val () = out "OI_CASEB_META_BUILT\n";

(* ----------------------------------------------------------------------------
   COMBINE caseA + caseB via EM on (dvd p n) -> conclBody n (under Hpre).
   Then discharge Hpre -> predBody n = Imp Hpre (conclBody n)  via impI_S2.
   ---------------------------------------------------------------------------- *)
val emDvd = ex_middle_atSub (dvd pp_free nStep);   (* Disj (dvd p n)(neg (dvd p n)) *)
val conclN = disjE_elimSub (dvd pp_free nStep, neg (dvd pp_free nStep), conclBody nStep)
               emDvd caseA_meta caseB_meta;          (* jT (conclBody n)  -- under Hpre + the fixed-p assumptions *)
val () = out "OI_CONCLN_OK\n";

(* predBody n = Imp Hpre (conclBody n).  Hpre is the assumed Conj(lt0 n)(sumsqBody n)=HpreT;
   discharge it (Hpre = Thm.assume HpreT lives in oi_descent.sml). *)
val stepBodyMeta = Thm.implies_intr (ctermSub (jT HpreT)) conclN;   (* META : jT Hpre ==> jT(conclBody n) *)
val predN = impI_S2 (HpreT, conclBody nStep) stepBodyMeta;          (* jT (predBody n) *)
val () = out ("OI_PREDN aconv="^
  Bool.toString ((Thm.prop_of predN) aconv (jT (predBody nStep)))^"\n");

(* ----------------------------------------------------------------------------
   FEED strong_induct.  The step we must supply :
     (!!n. (!!m. lt m n ==> predBody m) ==> predBody n)
   We have predN under the assumptions:  GpropMeta (the IH = IHbox) + the fixed-p
   assumptions hPrimeP/h4k3P.  Discharge the IH meta-hyp + forall_intr n.
   ---------------------------------------------------------------------------- *)
val stepDischIH = Thm.implies_intr (ctermSub GpropMeta) predN;      (* (IH n) ==> predBody n , still under hPrime/h4k3 *)
val stepAll     = Thm.forall_intr (ctermSub nStep) stepDischIH;     (* !!n. (IH n) ==> predBody n *)
val () = out "OI_STEP_ALL_BUILT\n";

(* strong_induct : (!!n.(!!m. lt m n ==> P m)==>P n) ==> P k , P,k schematic.
   instantiate P := predBody-abbrev, k := nStep ; the major premise = stepAll. *)
val predAbs = Term.lambda nStep (predBody nStep);   (* %n. predBody n  (capture-safe : fresh? nStep is a Free) *)
val si_inst = beta_norm (Drule.infer_instantiate ctxtSub
                [(("P",0), ctermSub predAbs), (("k",0), ctermSub nStep)] (varify strong_induct));
val predNStep = Thm.implies_elim si_inst stepAll;   (* jT (predBody nStep) , under hPrime/h4k3 only *)
val () = out ("OI_SI aconv-predNStep="^
  Bool.toString ((Thm.prop_of predNStep) aconv (jT (predBody nStep)))^"\n");
val () = out ("OI_SI hyps="^Int.toString (length (Thm.hyps_of predNStep))^"\n");

(* ----------------------------------------------------------------------------
   FINAL only_if : discharge the fixed-p assumptions to META, then build the
   object-implication statement :
     only_if : 0<n ==> (Ex a b. n=a^2+b^2) ==> for the fixed prime2 p with
               p=4k+3, the relational even-exponent conclusion.
   Statement shape (object-meta mix, matching predBody but with the p-conditions
   as object Imps so the final thm is the closed only_if):
     jT ( Imp (prime2 p)
              (Imp (Ex k. p=4k+3)
                   (Imp (Conj (lt 0 n)(sumsqBody n)) (conclBody n)) ) )
   ---------------------------------------------------------------------------- *)
(* predNStep : jT (predBody nStep), hyps = { hPrimeP, h4k3P } (the fixed-p assumes). *)
val d1 = Thm.implies_intr (ctermSub h4k3P)  predNStep;   (* (Ex k. p=4k+3) ==> predBody n *)
val d2 = Thm.implies_intr (ctermSub hPrimeP) d1;          (* prime2 p ==> (Ex k...) ==> predBody n *)
val () = out ("OI_DISCHARGED hyps="^Int.toString (length (Thm.hyps_of d2))^"\n");

(* wrap to a fully-object statement via impI_S2 (innermost first) *)
val h4k3Term = mkEx h4k3body;     (* Ex k. p = 4k+3 *)
val obj_inner = predN;            (* jT (Imp Hpre (conclBody n)) = jT (predBody n) -- but under hyps; rebuild from predNStep instead *)

(* Build the object-form only_if : need predNStep (= jT (predBody n)) discharged
   into object Imps for the p-conditions.  predBody n is ALREADY an object Imp.
   So compose:  prime2 p --o--> (Ex k. p=4k+3) --o--> predBody n   as OBJECT Imps. *)
val onlyif_meta = d2;   (* META : prime2 p ==> (Ex k...) ==> jT(predBody n), 0-hyp *)
(* object-ify the two outer p-conditions *)
val oi_inner = impI_S2 (h4k3Term, predBody nStep)
                 (Thm.implies_intr (ctermSub h4k3P)
                    (Thm.implies_elim (Thm.implies_elim onlyif_meta (Thm.assume (ctermSub hPrimeP)))
                                      (Thm.assume (ctermSub h4k3P))));
(* oi_inner : jT (Imp (Ex k...) (predBody n)) , hyp = { hPrimeP } *)
val only_if = impI_S2 (prime2 pp_free, mkImp h4k3Term (predBody nStep))
                 (Thm.implies_intr (ctermSub hPrimeP) oi_inner);
val () = out "OI_ONLYIF_BUILT\n";

(* intended statement *)
val only_if_intended =
  jT (mkImp (prime2 pp_free)
       (mkImp h4k3Term
          (mkImp (mkConj (lt ZeroC nStep) (sumsqBody nStep)) (conclBody nStep))));

val oi_hyps  = length (Thm.hyps_of only_if);
val oi_aconv = (Thm.prop_of only_if) aconv only_if_intended;
val () = out ("ONLY_IF hyps="^Int.toString oi_hyps^" aconv="^Bool.toString oi_aconv^"\n");

(* SOUNDNESS PROBE : the false variant dropping the prime2 hypothesis must NOT be aconv. *)
val false_variant =
  jT (mkImp h4k3Term
        (mkImp (mkConj (lt ZeroC nStep) (sumsqBody nStep)) (conclBody nStep)));
val probe_needs_prime = not ((Thm.prop_of only_if) aconv false_variant);
(* PROBE 2 : the relational even-exponent conclusion is genuinely present (not collapsed
   to the trivially-true (Ex v m. oeq n (pow p v * m)) with no even/ndvd). *)
val collapsed_concl =
  jT (mkImp (prime2 pp_free)
       (mkImp h4k3Term
          (mkImp (mkConj (lt ZeroC nStep) (sumsqBody nStep))
                 (mkEx (Term.lambda vFr0 (mkEx (Term.lambda mFr0
                    (oeq nStep (mult (pow pp_free vFr0) mFr0)))))))));
val probe_concl = not ((Thm.prop_of only_if) aconv collapsed_concl);

val () =
  if oi_hyps = 0 andalso oi_aconv andalso probe_needs_prime andalso probe_concl
  then out "ONLY_IF_CLOSED\n"
  else out ("ONLY_IF_FAILED hyps="^Int.toString oi_hyps^" aconv="^Bool.toString oi_aconv
            ^" pprime="^Bool.toString probe_needs_prime^" pconcl="^Bool.toString probe_concl^"\n");
