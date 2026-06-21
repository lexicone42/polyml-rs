(* ============ CASE A : p|n -> descent ============ *)
val () = out "OI_CASEA_BEGIN\n";

(* dzos on Sub *)
val disj_zero_or_suc_vSub = varify disj_zero_or_suc;
fun dzosSub_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("p",0), ctermSub t)] disj_zero_or_suc_vSub);

(* mult0r on Sub already: mult0r_atSub. *)
(* prime2_gt1_atSub p hPrime : jT (lt 1 p) = jT (le 2 p) = jT (Ex t. oeq p (add 2 t)). *)

val caseA_arm =
  let
    val hDnP = jT (dvd pp_free nStep);
    val hDn  = Thm.assume (ctermSub hDnP);
    val ppT  = mult pp_free pp_free;   (* pp = p*p *)
    (* goal : conclBody n.  exE a, exE b from hSS. *)
    val aAbs = Abs("a", natT, sumsqBody nStep);  (* not used; sumsqBody = Ex a. Ex b. ... *)
    (* exE a *)
    val ssAbsA = Abs("a", natT, mkEx (Abs("b", natT,
                   oeq nStep (add (mult (Bound 1)(Bound 1)) (mult (Bound 0)(Bound 0))))));
    fun afterA aT (hExB : thm) =     (* hExB : jT (Ex b. oeq n (a*a + b*b)) *)
      let
        val ssAbsB = Abs("b", natT, oeq nStep (add (mult aT aT) (mult (Bound 0)(Bound 0))));
        fun afterB bT (hN : thm) =   (* hN : jT (oeq n (a*a + b*b)) *)
          let
            (* dvd p (a*a+b*b) from dvd p n + hN *)
            val hDab = dvd_cong_argSub (pp_free, nStep, add (mult aT aT)(mult bT bT)) hN hDn;
            val conj = key_onlyif_at (pp_free, aT, bT) hPrime h4k3 hDab;  (* conj(p|a)(p|b) *)
            val hPa  = conjunct1_atSub (dvd pp_free aT, dvd pp_free bT) conj;
            val hPb  = conjunct2_atSub (dvd pp_free aT, dvd pp_free bT) conj;
            (* extract a', b' *)
            fun afterAp apT (hAeq : thm) =   (* hAeq : oeq a (mult p a') *)
              let
                fun afterBp bpT (hBeq : thm) =  (* hBeq : oeq b (mult p b') *)
                  let
                    val a2  = mult aT aT;  val b2 = mult bT bT;
                    val x2  = mult apT apT; val y2 = mult bpT bpT;
                    val nprime = add x2 y2;          (* n' = a'^2 + b'^2 *)
                    val hA2 = sq_factor_at (aT, pp_free, apT, hAeq);  (* oeq (a^2)(pp * a'^2) *)
                    val hB2 = sq_factor_at (bT, pp_free, bpT, hBeq);  (* oeq (b^2)(pp * b'^2) *)
                    val hNfac = factor_n_at (nStep, a2, b2, ppT, x2, y2, hN, hA2, hB2); (* oeq n (pp * n') *)
                    (* positivity + descent inside n' = Suc q branch *)
                    val dz = dzosSub_at nprime;     (* Disj (oeq n' 0)(Ex q. oeq n' (Suc q)) *)
                    val goalC = conclBody nStep;
                    (* case n'=0 : contra *)
                    val caseZ =
                      let
                        val hz = Thm.assume (ctermSub (jT (oeq nprime ZeroC)));   (* oeq n' 0 *)
                        (* n = pp*n' = pp*0 = 0 ; but 0<n.  derive oFalse, then ex falso. *)
                        val cpp0 = mult_cong_rS2 (ppT, nprime, ZeroC) hz;          (* oeq (pp*n')(pp*0) *)
                        val pp0  = mult0r_atSub ppT;                               (* oeq (pp*0) 0 *)
                        val nEq0 = oeq_trans OF [hNfac, oeq_trans OF [cpp0, pp0]]; (* oeq n 0 *)
                        (* hPos : jT (lt 0 n) = jT (le (Suc 0) n) = Ex w. oeq n (add (Suc 0) w).
                           with n=0 : oeq 0 (add (Suc 0) w) -> Suc(..) = 0 contra Suc_neq_Zero. *)
                        fun posBody wT (hw : thm) =  (* hw : oeq n (add (Suc 0) w) *)
                          let
                            (* oeq 0 (add (Suc 0) w) : rewrite n->0 in hw *)
                            val hw0 = oeq_trans OF [oeq_sym OF [nEq0], hw];  (* oeq 0 (add (Suc 0) w) *)
                            val aS  = addSucS2_at (ZeroC, wT);              (* add (Suc 0) w = Suc(add 0 w) *)
                            val o0w = oeq_trans OF [hw0, aS];               (* oeq 0 (Suc(add 0 w)) *)
                            val o0wS= oeq_sym OF [o0w];                     (* oeq (Suc(add 0 w)) 0 *)
                            val fls = (Suc_neq_Zero_atSub (add ZeroC wT)) OF [o0wS]; (* oFalse *)
                          in Thm.implies_elim (oFalse_elimSub_at goalC) fls end;
                        val posWAbs = Abs("w", natT, oeq nStep (add (suc ZeroC)(Bound 0)));
                        val fromPos = exESub_elim (posWAbs, goalC) hPos "wpos" posBody;
                      in Thm.implies_intr (ctermSub (jT (oeq nprime ZeroC))) fromPos end;
                    (* case n'=Suc q : the real descent *)
                    val caseSq =
                      let
                        val qsAbs = Abs("q", natT, oeq nprime (suc (Bound 0)));  (* Ex q. n' = Suc q *)
                        fun sqBody qT (hq : thm) =   (* hq : oeq n' (Suc q) *)
                          let
                            val hPosNp = lt0_suc_at qT;   (* lt 0 (Suc q) *)
                            (* lift to lt 0 n' via hq : need lt 0 n'.  rewrite Suc q -> n'. *)
                            val hqS = oeq_sym OF [hq];    (* oeq (Suc q) n' *)
                            val zLt0 = Free("zlt0", natT);
                            val PabsLt = Term.lambda zLt0 (lt ZeroC zLt0);   (* capture-safe : lt has an inner Ex *)
                            val hPosNprime = beta_norm (Drule.infer_instantiate ctxtSub
                                  [(("P",0), ctermSub PabsLt), (("a",0), ctermSub (suc qT)),
                                   (("b",0), ctermSub nprime)] oeq_subst_vS2) OF [hqS, hPosNp];  (* lt 0 n' *)
                            (* lt n' n : lt_self_mult (pp=Suc(Suc s), n'=Suc q) -> lt n' (pp*n'), rewrite pp*n' -> n via hNfac sym *)
                            (* extract p = Suc(Suc t) *)
                            val ltp = prime2_gt1_atSub pp_free hPrime;  (* lt 1 p = Ex t. oeq p (add 2 t) *)
                            fun ptBody tT (ht2 : thm) =  (* ht2 : oeq p (add (Suc(Suc 0)) t) *)
                              let
                                (* oeq p (Suc(Suc t)) : add (Suc(Suc 0)) t = Suc(add (Suc 0) t) = Suc(Suc(add 0 t)) = Suc(Suc t) *)
                                val a1 = addSucS2_at (suc ZeroC, tT);   (* add (Suc(Suc 0)) t = Suc(add (Suc 0) t) *)
                                val a2x= addSucS2_at (ZeroC, tT);       (* add (Suc 0) t = Suc(add 0 t) *)
                                val a0 = add0S2_at tT;                  (* add 0 t = t *)
                                val a2S= Suc_cong OF [oeq_trans OF [a2x, Suc_cong OF [a0]]]; (* Suc(add (Suc 0) t) = Suc(Suc t) *)
                                val pSS = oeq_trans OF [ht2, oeq_trans OF [a1, a2S]];  (* oeq p (Suc(Suc t)) *)
                                val hPP = pp_suc2_at (pp_free, tT, pSS);  (* oeq (p*p)(Suc(Suc S)), S = add t (mult(Suc t) p) *)
                                val sS  = add tT (mult (suc tT) pp_free);
                                val ltSelf = lt_self_mult_at (ppT, nprime, sS, qT, hPP, hq);  (* lt n' (pp*n') *)
                                (* rewrite pp*n' -> n via hNfac : oeq n (pp*n') ; sym -> oeq (pp*n') n *)
                                val hNfacS = oeq_sym OF [hNfac];   (* oeq (pp*n') n *)
                                val zLt2 = Free("zlt2", natT);
                                val PabsLt2 = Term.lambda zLt2 (lt nprime zLt2);   (* capture-safe *)
                                val ltNpN = beta_norm (Drule.infer_instantiate ctxtSub
                                      [(("P",0), ctermSub PabsLt2), (("a",0), ctermSub (mult ppT nprime)),
                                       (("b",0), ctermSub nStep)] oeq_subst_vS2) OF [hNfacS, ltSelf]; (* lt n' n *)
                                (* applyIH n' (lt n' n) -> predBody n' = Imp(Hpre n')(conclBody n') *)
                                val predNp = applyIH nprime ltNpN;     (* jT (predBody n') *)
                                (* build Hpre n' = Conj(lt 0 n')(sumsqBody n') *)
                                (* sumsqBody n' : Ex a. Ex b. oeq n' (a*a+b*b), witness a',b' : oeq n' (a'^2+b'^2) refl *)
                                val nprimeReflSS = oeqreflS2_at nprime;  (* oeq n' n' ; n' IS add x2 y2 = a'^2+b'^2 *)
                                (* sumsqBody n' inner body at a',b' : oeq n' (add (a'*a')(b'*b')) = oeq n' n' (defeq) *)
                                val ssInnerB = Abs("b", natT, oeq nprime (add (mult apT apT)(mult (Bound 0)(Bound 0))));
                                val exBnp = exISub_at ssInnerB bpT nprimeReflSS;  (* Ex b. oeq n' (a'^2 + b^2) *)
                                val ssInnerA = Abs("a", natT, mkEx (Abs("b", natT,
                                                  oeq nprime (add (mult (Bound 1)(Bound 1))(mult (Bound 0)(Bound 0))))));
                                val exAnp = exISub_at ssInnerA apT exBnp;        (* sumsqBody n' *)
                                val hpreNp = conjI_atSub (lt ZeroC nprime, sumsqBody nprime) hPosNprime exAnp;
                                (* mp predNp hpreNp -> conclBody n' *)
                                val conclNp = mp_S2 (mkConj (lt ZeroC nprime)(sumsqBody nprime), conclBody nprime) predNp hpreNp;
                                (* exE v', exE m' from conclNp *)
                                fun afterV vpT (hExM : thm) =   (* hExM : Ex m. cbInner n' (v', m) *)
                                  let
                                    fun afterM mpT (hCb : thm) =  (* hCb : cbInner n' (v', m') *)
                                      let
                                        val hEqNp = conjunct1_atSub (oeq nprime (mult (pow pp_free vpT) mpT),
                                                       mkConj (neg (dvd pp_free mpT))(mkEx (Abs("j",natT, oeq vpT (add (Bound 0)(Bound 0)))))) hCb;
                                        val hRest = conjunct2_atSub (oeq nprime (mult (pow pp_free vpT) mpT),
                                                       mkConj (neg (dvd pp_free mpT))(mkEx (Abs("j",natT, oeq vpT (add (Bound 0)(Bound 0)))))) hCb;
                                        val hNdvdMp = conjunct1_atSub (neg (dvd pp_free mpT),
                                                        mkEx (Abs("j",natT, oeq vpT (add (Bound 0)(Bound 0))))) hRest;
                                        val hEvenVp = conjunct2_atSub (neg (dvd pp_free mpT),
                                                        mkEx (Abs("j",natT, oeq vpT (add (Bound 0)(Bound 0))))) hRest; (* Ex j. oeq v' (j+j) *)
                                        (* build conclBody n with v = Suc(Suc v'), m = m' *)
                                        val vNew = suc (suc vpT);
                                        (* n = pow p (SSv') * m' :  n = pp*n' [hNfac] ; n' = pow p v' * m' [hEqNp]
                                             -> pp*(pow p v' * m') ; = (pp*pow p v')*m' [assoc] ; pp*pow p v' = pow p (SSv') [pow_step sym] *)
                                        val e1 = mult_cong_rS2 (ppT, nprime, mult (pow pp_free vpT) mpT) hEqNp; (* pp*n' = pp*(pow p v' * m') *)
                                        val nEq1 = oeq_trans OF [hNfac, e1];   (* oeq n (pp*(pow p v' * m')) *)
                                        val assoc = multassocS2_at (ppT, pow pp_free vpT, mpT); (* (pp*pow p v')*m' = pp*(pow p v' * m') *)
                                        val assocS = oeq_sym OF [assoc];       (* pp*(pow p v' * m') = (pp*pow p v')*m' *)
                                        val nEq2 = oeq_trans OF [nEq1, assocS]; (* oeq n ((pp*pow p v')*m') *)
                                        val pstep = pow_step_at (pp_free, vpT); (* pow p (SSv') = (p*p)*pow p v' = pp*pow p v' *)
                                        val pstepS= oeq_sym OF [pstep];        (* pp*pow p v' = pow p (SSv') *)
                                        val congM = mult_cong_lS2 (mult ppT (pow pp_free vpT), pow pp_free vNew, mpT) pstepS; (* (pp*pow p v')*m' = pow p (SSv') * m' *)
                                        val hEqnNew = oeq_trans OF [nEq2, congM];  (* oeq n (pow p (SSv') * m') *)
                                        (* Ex j. oeq (SSv') (j+j) : exE j' from hEvenVp, even_step, exI (Suc j') *)
                                        fun afterJ jpT (hVeven : thm) =  (* hVeven : oeq v' (add j' j') *)
                                          let
                                            val hSSeven = even_step_at (vpT, jpT, hVeven);  (* oeq (SSv')(add (Suc j')(Suc j')) *)
                                            val evNewAbs = Abs("j", natT, oeq vNew (add (Bound 0)(Bound 0)));
                                            val exJnew = exISub_at evNewAbs (suc jpT) hSSeven;  (* Ex j. oeq (SSv')(j+j) *)
                                          in build_concl (vNew, mpT, hEqnNew, hNdvdMp, exJnew) end;
                                        val evJpAbs = Abs("j", natT, oeq vpT (add (Bound 0)(Bound 0)));
                                      in exESub_elim (evJpAbs, goalC) hEvenVp "jp" afterJ end;
                                    val cbMAbs = Term.lambda mFr0 (cbInner nprime (vpT, mFr0));
                                  in exESub_elim (cbMAbs, goalC) hExM "mp" afterM end;
                                val cbVAbs = Term.lambda vFr0 (mkEx (Term.lambda mFr0 (cbInner nprime (vFr0, mFr0))));
                              in exESub_elim (cbVAbs, goalC) conclNp "vp" afterV end;
                          in exESub_elim (Abs("t", natT, oeq pp_free (add (suc(suc ZeroC))(Bound 0))), goalC) ltp "tp" ptBody end;
                        val ig = exESub_elim (qsAbs, goalC) (Thm.assume (ctermSub (jT (mkEx qsAbs)))) "qd" sqBody;
                      in Thm.implies_intr (ctermSub (jT (mkEx qsAbs))) ig end;
                    (* combine via disjE_elimSub *)
                    val combined = disjE_elimSub (oeq nprime ZeroC, mkEx (Abs("q",natT, oeq nprime (suc (Bound 0)))), conclBody nStep)
                                     dz
                                     (impI_S2 (oeq nprime ZeroC, conclBody nStep) caseZ)
                                     (impI_S2 (mkEx (Abs("q",natT, oeq nprime (suc (Bound 0)))), conclBody nStep) caseSq);
                  in combined end;
                val bpAbs = Abs("k", natT, oeq bT (mult pp_free (Bound 0)));
              in exESub_elim (bpAbs, conclBody nStep) hPb "bp" afterBp end;
            val apAbs = Abs("k", natT, oeq aT (mult pp_free (Bound 0)));
          in exESub_elim (apAbs, conclBody nStep) hPa "ap" afterAp end;
        val () = ();
      in exESub_elim (ssAbsB, conclBody nStep) hExB "bb" afterB end;
    val resA = exESub_elim (ssAbsA, conclBody nStep) hSS "aa" afterA;
    val metaImpA = Thm.implies_intr (ctermSub hDnP) resA;
  in impI_S2 (dvd pp_free nStep, conclBody nStep) metaImpA end;

val () = out ("OI_CASEA_OK aconv-impl="^
  Bool.toString ((Thm.prop_of caseA_arm) aconv (jT (mkImp (dvd pp_free nStep) (conclBody nStep))))^"\n");
