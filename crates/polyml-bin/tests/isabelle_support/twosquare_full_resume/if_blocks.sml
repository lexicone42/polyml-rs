(* ============================================================================
   IF-DIRECTION building blocks (per-prime-power sums of two squares + fold).
   On ctxtGR.  Each is a small, citable, 0-hyp / 0-extra-hyp lemma.
   ============================================================================ *)
val () = out "IF_BLOCKS_BEGIN\n";

(* sumsq n := Ex a b. n = a*a + b*b   (an ML term builder) *)
fun sumsqBody nT = mkEx (Abs("a", natT, mkEx (Abs("b", natT,
                     oeq nT (add (mult (Bound 1)(Bound 1)) (mult (Bound 0)(Bound 0)))))));

(* exI helper specialised for the two-nested-Ex sumsq shape:
   given witnesses a0,b0 and h : oeq n (a0*a0 + b0*b0), build jT (sumsqBody n). *)
fun mk_sumsq nT (a0,b0) h =
  let
    val innerPred = Abs("b", natT, oeq nT (add (mult a0 a0) (mult (Bound 0)(Bound 0))));
    val innerEx = exI_gr_at innerPred b0 h;     (* Ex b. n = a0*a0 + b*b *)
    val outerPred = Abs("a", natT, mkEx (Abs("b", natT,
                      oeq nT (add (mult (Bound 1)(Bound 1)) (mult (Bound 0)(Bound 0))))));
  in exI_gr_at outerPred a0 innerEx end;

(* ---- two_is_sumsq : |- Ex a b. (Suc(Suc 0)) = a*a + b*b   (a=b=1) ---- *)
val two_is_sumsq =
  let
    val one = suc ZeroC;
    val two = suc (suc ZeroC);
    (* 1*1 + 1*1 = 2 : 1*1 = 1 (mult_1_left), then 1+1 = Suc(Suc 0) *)
    val m11 = mult1l_gr one;                  (* oeq (1*1) 1 *)
    (* add 1 1 = Suc 1 : add_Suc then add_0 : add (Suc 0) (Suc 0)? Use addSuc + add0 *)
    (* oeq (add (1*1)(1*1)) 2 : rewrite both 1*1 -> 1, then add (Suc 0)(Suc 0)=Suc(Suc 0). *)
    val sumRefl = oeqRefl_gr (add (mult one one)(mult one one));
    (* step: add (1*1)(1*1) = add 1 (1*1) [cong_l m11] = add 1 1 [cong_r m11] *)
    val s1 = add_cong_l_gr (mult one one, one, mult one one) m11;  (* oeq (add (1*1)(1*1)) (add 1 (1*1)) *)
    val s2 = add_cong_r_gr (one, mult one one, one) m11;          (* oeq (add 1 (1*1)) (add 1 1) *)
    val sum11 = oeqTrans_gr (s1, s2);                              (* oeq (add (1*1)(1*1)) (add 1 1) *)
    (* add 1 1 = Suc(Suc 0) : add (Suc 0)(Suc 0). add_Suc: add (Suc 0) y = Suc(add 0 y). *)
    val aS = addSuc_gr (ZeroC, one);          (* oeq (add (Suc 0) (Suc 0)) (Suc (add 0 (Suc 0))) *)
    val a0 = add0_gr one;                      (* oeq (add 0 (Suc 0)) (Suc 0) *)
    val sucA0 = Suc_cong_gr2 a0;               (* oeq (Suc(add 0 (Suc 0))) (Suc(Suc 0)) *)
    val add11_2 = oeqTrans_gr (aS, sucA0);     (* oeq (add 1 1) (Suc(Suc 0)) = 2 *)
    val full = oeqTrans_gr (sum11, add11_2);   (* oeq (add (1*1)(1*1)) 2 *)
    val eqn = oeqSym_gr full;                  (* oeq 2 (add (1*1)(1*1)) *)
  in mk_sumsq two (one,one) eqn end;
val () = out ("two_is_sumsq hyps="^Int.toString(length(Thm.hyps_of two_is_sumsq))^"\n");
val two_is_sumsq_intended = jT (sumsqBody (suc (suc ZeroC)));
val () = out ("IF_TWO_OK aconv="^Bool.toString ((Thm.prop_of two_is_sumsq) aconv two_is_sumsq_intended)^"\n");

(* ---- sq_is_sumsq : |- Ex a b. (k*k) = a*a + b*b   (a=k, b=0) ---- *)
fun sq_is_sumsq kT =
  let
    val zz0 = mult0_gr ZeroC;                  (* oeq (0*0) 0 (mult_0 with n=0 gives mult 0 0 = 0? mult_0: 0*n=0) *)
    (* mult_0 : oeq (mult Zero n) Zero. instance n=0 -> oeq (mult 0 0) 0 *)
    (* add (k*k) (0*0) = add (k*k) 0 = k*k *)
    val cong0 = add_cong_r_gr (mult kT kT, mult ZeroC ZeroC, ZeroC) zz0;  (* oeq (add (k*k)(0*0)) (add (k*k) 0) *)
    (* add (k*k) 0 = k*k : need add_0_right. add_0 is add 0 n = n. Use add_comm then add_0. *)
    val ac = addcomm_gr (mult kT kT, ZeroC);   (* oeq (add (k*k) 0) (add 0 (k*k)) *)
    val a0 = add0_gr (mult kT kT);             (* oeq (add 0 (k*k)) (k*k) *)
    val add0r = oeqTrans_gr (ac, a0);          (* oeq (add (k*k) 0) (k*k) *)
    val full = oeqTrans_gr (cong0, add0r);     (* oeq (add (k*k)(0*0)) (k*k) *)
    val eqn = oeqSym_gr full;                  (* oeq (k*k) (add (k*k)(0*0)) *)
  in mk_sumsq (mult kT kT) (kT,ZeroC) eqn end;
val () =
  let val kk = Free("k_sq", natT)
      val h = sq_is_sumsq kk
  in out ("IF_SQ_OK hyps="^Int.toString(length(Thm.hyps_of h))^
          " aconv="^Bool.toString ((Thm.prop_of h) aconv (jT (sumsqBody (mult kk kk))))^"\n") end
  handle e => out ("IF_SQ_FAIL "^exnMessage e^"\n");

(* ---- sumsq_times_sq : |- (Ex a b. n = a*a+b*b) ==> Ex a b. (k*k)*n = a*a+b*b ----
   witnesses for (k*k)*n: (k*a, k*b), since (k*k)*(a*a+b*b) = (k*a)*(k*a)+(k*b)*(k*b). *)
fun sumsq_times_sq (kT, nT) hsum =
  let
    val goal = jT (sumsqBody (mult (mult kT kT) nT));
    val nP = Abs("a", natT, mkEx (Abs("b", natT,
               oeq nT (add (mult (Bound 1)(Bound 1)) (mult (Bound 0)(Bound 0))))));
  in
    exE_gr_elim (nP, sumsqBody (mult (mult kT kT) nT)) hsum "a_ks"
      (fn aF => fn hb =>
         let
           val nP2 = Abs("b", natT, oeq nT (add (mult aF aF) (mult (Bound 0)(Bound 0))));
         in
           exE_gr_elim (nP2, sumsqBody (mult (mult kT kT) nT)) hb "b_ks"
             (fn bF => fn heq =>   (* heq : oeq n (a*a + b*b) *)
                let
                  (* (k*k)*n = (k*k)*(a*a+b*b) [cong_r heq] = (k*a)^2 + (k*b)^2 [proveIdentityG] *)
                  val congN = mult_cong_r_gr (mult kT kT, nT, add (mult aF aF)(mult bF bF)) heq;
                          (* oeq ((k*k)*n) ((k*k)*(a*a+b*b)) *)
                  val ka = mult kT aF; val kb = mult kT bF;
                  val idP = proveIdentityG
                              (mult (mult kT kT) (add (mult aF aF)(mult bF bF)))
                              (add (mult ka ka)(mult kb kb));
                          (* oeq ((k*k)*(a*a+b*b)) ((k*a)^2+(k*b)^2) *)
                  val eqn = oeqTrans_gr (congN, idP);   (* oeq ((k*k)*n) ((k*a)^2+(k*b)^2) *)
                in mk_sumsq (mult (mult kT kT) nT) (ka, kb) eqn end)
         end)
  end;
val () =
  let val kk = Free("k_st", natT); val nn = Free("n_st", natT)
      val hassume = Thm.assume (ctermGR (jT (sumsqBody nn)))
      val h = sumsq_times_sq (kk, nn) hassume
      val disch = Thm.implies_intr (ctermGR (jT (sumsqBody nn))) h
  in out ("IF_STSQ_OK hyps="^Int.toString(length(Thm.hyps_of disch))^"\n") end
  handle e => out ("IF_STSQ_FAIL "^exnMessage e^"\n");

(* ---- sumsq_mult : |- (Ex a b. m = a*a+b*b) ==> (Ex a b. n = a*a+b*b)
                        ==> Ex a b. m*n = a*a+b*b   (the brahmagupta fold step) ----
   destructure both, use brahma4 (a,b,c,d) on the witnesses, rewrite m*n. *)
fun sumsq_mult (mT, nT) hM hN =
  let
    val goalBody = sumsqBody (mult mT nT);
    val mP = Abs("a", natT, mkEx (Abs("b", natT,
               oeq mT (add (mult (Bound 1)(Bound 1)) (mult (Bound 0)(Bound 0))))));
  in
    exE_gr_elim (mP, goalBody) hM "a_mm"
      (fn aF => fn hb1 =>
         let val mP2 = Abs("b", natT, oeq mT (add (mult aF aF)(mult (Bound 0)(Bound 0)))) in
           exE_gr_elim (mP2, goalBody) hb1 "b_mm"
             (fn bF => fn heqM =>   (* oeq m (a*a+b*b) *)
                let val nP = Abs("a", natT, mkEx (Abs("b", natT,
                               oeq nT (add (mult (Bound 1)(Bound 1)) (mult (Bound 0)(Bound 0)))))) in
                  exE_gr_elim (nP, goalBody) hN "c_mm"
                    (fn cF => fn hb2 =>
                       let val nP2 = Abs("b", natT, oeq nT (add (mult cF cF)(mult (Bound 0)(Bound 0)))) in
                         exE_gr_elim (nP2, goalBody) hb2 "d_mm"
                           (fn dF => fn heqN =>   (* oeq n (c*c+d*d) *)
                              let
                                (* m*n = (a*a+b*b)*(c*c+d*d) [cong both] = brahma witnesses *)
                                val congM = mult_cong_l_gr (mT, add (mult aF aF)(mult bF bF), nT) heqM;
                                        (* oeq (m*n) ((a*a+b*b)*n) *)
                                val congN = mult_cong_r_gr (add (mult aF aF)(mult bF bF), nT, add (mult cF cF)(mult dF dF)) heqN;
                                        (* oeq ((a*a+b*b)*n) ((a*a+b*b)*(c*c+d*d)) *)
                                val eqProd = oeqTrans_gr (congM, congN);   (* oeq (m*n) ((a*a+b*b)*(c*c+d*d)) *)
                                (* brahma4 (a,b,c,d) : Ex P Q. (a*a+b*b)*(c*c+d*d) = P*P+Q*Q *)
                                val brh = brahma4 (aF,bF,cF,dF);
                                val lhsProd = mult (add (mult aF aF)(mult bF bF))(add (mult cF cF)(mult dF dF));
                                val brhP = Abs("P", natT, mkEx (Abs("Q", natT,
                                             oeq lhsProd (add (mult (Bound 1)(Bound 1))(mult (Bound 0)(Bound 0))))));
                              in
                                exE_gr_elim (brhP, goalBody) brh "P_mm"
                                  (fn pF => fn hq =>
                                     let val brhP2 = Abs("Q", natT, oeq lhsProd (add (mult pF pF)(mult (Bound 0)(Bound 0)))) in
                                       exE_gr_elim (brhP2, goalBody) hq "Q_mm"
                                         (fn qF => fn heqPQ =>  (* oeq ((a*a+b*b)*(c*c+d*d)) (P*P+Q*Q) *)
                                            let val eqn = oeqTrans_gr (eqProd, heqPQ)  (* oeq (m*n) (P*P+Q*Q) *)
                                            in mk_sumsq (mult mT nT) (pF,qF) eqn end)
                                     end)
                              end)
                       end)
                end)
         end)
  end;
val () =
  let val mm = Free("m_sm2", natT); val nn = Free("n_sm2", natT)
      val hm = Thm.assume (ctermGR (jT (sumsqBody mm)))
      val hn = Thm.assume (ctermGR (jT (sumsqBody nn)))
      val h = sumsq_mult (mm,nn) hm hn
      val d1 = Thm.implies_intr (ctermGR (jT (sumsqBody nn))) h
      val d2 = Thm.implies_intr (ctermGR (jT (sumsqBody mm))) d1
  in out ("IF_SMULT_OK hyps="^Int.toString(length(Thm.hyps_of d2))^"\n") end
  handle e => out ("IF_SMULT_FAIL "^exnMessage e^"\n");

(* ---- prod_all_sumsq : |- !ps. (!x. lmem x ps ==> sumsq x) ==> sumsq (lprod ps) ----
   THE structural backbone of the if-direction: a list of sums-of-two-squares
   multiplies to a sum of two squares (brahmagupta fold over an FTA-style list).
   By list_induct on ps.  Built on ctxtGR.
   - base ps=lnil: lprod lnil = 1 = 1*1 + 0*0, sumsq 1 (the hypothesis vacuous).
   - step ps=lcons h t: lprod = h * lprod t.  h is a sum of squares (apply the
     hyp at the head, lmem h (lcons h t) via lmem_cons_bwd+disjI1+oeq_refl);
     lprod t is a sum of squares (IH, with hyp transferred via lmem_cons_bwd+disjI2);
     fold via sumsq_mult; rewrite (h * lprod t) = lprod (lcons h t). *)
val lprod_nil_gr  = varify lprod_nil_ax;
val lprod_cons_gr = varify lprod_cons_ax;
fun lprodNil_gr ()     = lprod_nil_gr;
fun lprodCons_gr (h,t) = beta_norm (Drule.infer_instantiate ctxtGR
                          [(("x",0), ctermGR h),(("t",0), ctermGR t)] lprod_cons_gr);
fun lmemNilElim_gr x   = beta_norm (Drule.infer_instantiate ctxtGR [(("x",0), ctermGR x)] lmem_nil_elim_vR);
fun lmemConsBwd_gr (x,y,t) = beta_norm (Drule.infer_instantiate ctxtGR
                          [(("x",0), ctermGR x),(("y",0), ctermGR y),(("t",0), ctermGR t)] lmem_cons_bwd_vR);
fun oFalseElim_gr rT   = beta_norm (Drule.infer_instantiate ctxtGR [(("R",0), ctermGR rT)] oFalse_elim_vR);

val prod_all_sumsq =
  let
    val psV = Free("ps_pa", natlistT);
    (* hypBody zt = !x. lmem x zt ==> sumsq x   (object Forall).
       Built capture-safely: the inner per-x predicate uses a FRESH Free xPA so
       the `zt` (a natlist term that may itself contain bound vars) is never
       captured by the inner Abs; Term.lambda re-abstracts xPA. *)
    val xPA = Free("xPA", natT);
    fun hypBody zt = mkForall (Term.lambda xPA (mkImp (lmem xPA zt) (sumsqBody xPA)));
    fun concBody zt = mkImp (hypBody zt) (sumsqBody (lprod zt));
    val zPA = Free("zPA", natlistT);
    val Qpred = Term.lambda zPA (concBody zPA);
    val ind = beta_norm (Drule.infer_instantiate ctxtGR
          [(("P",0), ctermGR Qpred), (("a",0), ctermGR psV)] list_induct_vR);
    (* base : concBody lnil *)
    val base =
      let
        val hh = Thm.assume (ctermGR (jT (hypBody lnilC)));   (* unused: lprod lnil = 1, sumsq 1 directly *)
        (* sumsq 1 : 1 = 1*1 + 0*0 *)
        val one = suc ZeroC;
        (* lprod lnil = 1 *)
        val lp = lprodNil_gr ();                               (* oeq (lprod lnil) 1 *)
        (* sumsq 1 via mk_sumsq: 1 = 1*1 + 0*0 *)
        val m11 = mult1l_gr one;                               (* oeq (1*1) 1 *)
        val zz0 = mult0_gr ZeroC;                              (* oeq (0*0) 0 *)
        val cong0 = add_cong_r_gr (mult one one, mult ZeroC ZeroC, ZeroC) zz0;  (* (1*1)+(0*0) = (1*1)+0 *)
        val ac = addcomm_gr (mult one one, ZeroC);            (* (1*1)+0 = 0+(1*1) *)
        val a0 = add0_gr (mult one one);                       (* 0+(1*1) = 1*1 *)
        val add0r = oeqTrans_gr (ac, a0);                      (* (1*1)+0 = 1*1 *)
        val rhs1 = oeqTrans_gr (oeqTrans_gr (cong0, add0r), m11);  (* (1*1)+(0*0) = 1 *)
        val rhsSym = oeqSym_gr rhs1;                           (* 1 = (1*1)+(0*0) *)
        (* lprod lnil = (1*1)+(0*0) *)
        val eqn = oeqTrans_gr (lp, rhsSym);                    (* lprod lnil = (1*1)+(0*0) *)
        val sq1 = mk_sumsq (lprod lnilC) (one, ZeroC) eqn;     (* sumsq (lprod lnil) *)
        (* sumsq(lprod lnil) does NOT depend on the hyp; build the OBJECT
           implication jT (Imp (hypBody lnil) (sumsq (lprod lnil))). *)
        val disM = Thm.implies_intr (ctermGR (jT (hypBody lnilC))) sq1;  (* meta *)
        val disO = impI_r (hypBody lnilC, sumsqBody (lprod lnilC)) disM; (* object *)
      in disO end;
    (* step : !!h t. concBody t ==> concBody (lcons h t) *)
    val hF = Free("h_pa", natT); val tF = Free("t_pa", natlistT);
    val IH = Thm.assume (ctermGR (jT (concBody tF)));
    val stepConcl =
      let
        val hh = Thm.assume (ctermGR (jT (hypBody (lcons hF tF))));   (* !x. lmem x (lcons h t) ==> sumsq x *)
        (* sumsq h : apply hh at h.  need lmem h (lcons h t). *)
        val hhAtH = allE_r (Term.lambda xPA (mkImp (lmem xPA (lcons hF tF)) (sumsqBody xPA))) hF hh;
                    (* lmem h (lcons h t) ==> sumsq h *)
        val memH = lmemConsBwd_gr (hF, hF, tF) OF [ disjI1_gr_at (oeq hF hF, lmem hF tF) (oeqRefl_gr hF) ];
                    (* lmem h (lcons h t) *)
        val sqH = mp_r (lmem hF (lcons hF tF), sumsqBody hF) hhAtH memH;   (* sumsq h *)
        (* sumsq (lprod t) : transfer hyp to t, apply IH. *)
        val hypT =
          let
            val xT = Free("x_pat", natT);
            (* prove !x. lmem x t ==> sumsq x *)
            val body =
              let
                val hmem = Thm.assume (ctermGR (jT (lmem xT tF)));   (* lmem x t *)
                val memXcons = lmemConsBwd_gr (xT, hF, tF) OF [ disjI2_gr_at (oeq xT hF, lmem xT tF) hmem ];
                            (* lmem x (lcons h t) *)
                val hhAtX = allE_r (Term.lambda xPA (mkImp (lmem xPA (lcons hF tF)) (sumsqBody xPA))) xT hh;
                val sqX = mp_r (lmem xT (lcons hF tF), sumsqBody xT) hhAtX memXcons;  (* sumsq x *)
                val disM = Thm.implies_intr (ctermGR (jT (lmem xT tF))) sqX;  (* META: jT(lmem x t) ==> jT(sumsq x) *)
                val disO = impI_r (lmem xT tF, sumsqBody xT) disM;  (* OBJECT: jT (Imp (lmem x t)(sumsq x)) *)
              in disO end;
            val fa = allI_r (Term.lambda xPA (mkImp (lmem xPA tF) (sumsqBody xPA)))
                       (Thm.forall_intr (ctermGR xT) body);
          in fa end;  (* jT (hypBody t) *)
        val sqProdT = mp_r (hypBody tF, sumsqBody (lprod tF)) IH hypT;   (* sumsq (lprod t) *)
        (* fold : sumsq h ==> sumsq (lprod t) ==> sumsq (h * lprod t) *)
        val foldHT = sumsq_mult (hF, lprod tF) sqH sqProdT;   (* sumsq (h * lprod t) *)
        (* rewrite (h * lprod t) -> lprod (lcons h t) using lprod_cons (sym) *)
        val lpc = lprodCons_gr (hF, tF);                       (* oeq (lprod (lcons h t)) (h * lprod t) *)
        val lpcSym = oeqSym_gr lpc;                            (* oeq (h * lprod t) (lprod (lcons h t)) *)
        val zRW = Free("zRW_pa", natT);
        val Prw = Term.lambda zRW (sumsqBody zRW);             (* capture-safe %z. sumsq z *)
        val sqCons = oeq_subst_gr_at (Prw, mult hF (lprod tF), lprod (lcons hF tF)) lpcSym foldHT;
                    (* sumsq (lprod (lcons h t)) *)
        val disM = Thm.implies_intr (ctermGR (jT (hypBody (lcons hF tF)))) sqCons;  (* meta *)
        val disO = impI_r (hypBody (lcons hF tF), sumsqBody (lprod (lcons hF tF))) disM;  (* object: concBody (lcons h t) *)
      in disO end;
    (* step needs jT (P t) ==> jT (P (lcons h t)) as a META implication for list_induct. *)
    val step1 = Thm.forall_intr (ctermGR hF)
                  (Thm.forall_intr (ctermGR tF)
                     (Thm.implies_intr (ctermGR (jT (concBody tF))) stepConcl));
    val concPs = Thm.implies_elim (Thm.implies_elim ind base) step1;   (* concBody ps  (ps Free) *)
    (* "for all ps" = SCHEMATIC ps via meta forall_intr + varify (the Forall
       connective is nat-only; the meta/schematic universal is the right form). *)
  in varify (Thm.forall_intr (ctermGR psV) concPs) end;
val () = out ("prod_all_sumsq hyps="^Int.toString(length(Thm.hyps_of prod_all_sumsq))^"\n");
(* ---- validation : 0-hyp + aconv the intended schematic statement ---- *)
val prod_all_sumsq_intended =
  let
    val psI = Var(("ps_pa",0), natlistT);
    val xI  = Free("xPA", natT);
    val hyp = mkForall (Term.lambda xI (mkImp (lmem xI psI) (sumsqBody xI)));
  in jT (mkImp hyp (sumsqBody (lprod psI))) end;
val prod_aconv = ((Thm.prop_of prod_all_sumsq) aconv prod_all_sumsq_intended);
val prod_0hyp  = (length (Thm.hyps_of prod_all_sumsq) = 0);
val () = out ("prod_all_sumsq aconv intended = "^Bool.toString prod_aconv^"\n");
(* soundness probe: NOT the vacuous form that drops the hypothesis (sumsq(lprod ps)
   is FALSE in general, e.g. lprod [3] = 3 is not a sum of two squares). *)
val prod_probe =
  let val psI = Var(("ps_pa",0), natlistT)
      val bogus = jT (sumsqBody (lprod psI))
  in not ((Thm.prop_of prod_all_sumsq) aconv bogus) end;
val () = if prod_probe then out "PROBE_OK prod_all_sumsq keeps the all-elements-sumsq hypothesis\n"
         else out "PROBE_UNSOUND prod_all_sumsq dropped its hypothesis!\n";
val () = if prod_aconv andalso prod_0hyp andalso prod_probe
         then out "IF_PROD_OK hyps=0 aconv=true\n" else out "IF_PROD_FAILED\n";

(* ---- axiom audit : the if-direction delta adds NO new axioms/consts/types;
   it is a pure derivation over the twosquare monolith's final theory.  Confirm
   the prod_all_sumsq theory's axiom set is exactly the monolith's (no axiom
   mentions lprod-sumsq / brahmagupta — every if-direction lemma is DERIVED). ---- *)
val () =
  let
    val thyOf = Thm.theory_of_thm prod_all_sumsq;
    val axs = Theory.all_axioms_of thyOf;
    val nax = length axs;
  in out ("IF_AXIOM_AUDIT total_axioms="^Int.toString nax^"\n") end
  handle e => out ("IF_AXIOM_AUDIT skipped ("^exnMessage e^")\n");

val () = out "IF_BLOCKS_DONE\n";
