(* ============================================================================
   DESCENT SEAT 3 (lemma-factored route).
   Appended after the FULL assembled four-square base (/tmp/four_square_base.sml).
   Final context: ctxtGR / ctermGR on thyGR.  No new const -> no new context.

   Goal: the FULL descent step
     descent_step : prime2 p ==> 1<m ==> m<p ==> four_sq (m*p)
                      ==> EX m2. lt 0 m2 /\ lt m2 m /\ four_sq (m2*p)
   built by first proving each of
     (a) signed four_residue_sum  [cheap]
     (b) r=0 exclusion            [cheap]
     (c) r<m                      [cheap]
     (d) Euler divide-by-m^2      [ONE proveStarFor, ~13 min]
   as SEPARATE named 0-hyp lemmas, then composing.  Each cheap lemma is on its
   own top-level binding so a later failure cannot un-bind the earlier ones.
   ============================================================================ *)
val () = out "SEAT3_DESCENT_BEGIN\n";

fun sq3 x = mult x x;

(* ----------------------------------------------------------------------------
   varify the dvd / mult-monotone lemmas onto ctxtGR (reused below).
   ---------------------------------------------------------------------------- *)
val dvd_diff_vGR3       = varify dvd_diff;        (* dvd p x ==> dvd p (x+y) ==> dvd p y *)
val dvd_trans_vGR3      = varify dvd_trans;
val dvd_mult_right_vGR3 = varify dvd_mult_right;  (* dvd a b ==> dvd a (b*c) *)
val dvd_mult_cong_vGR3  = varify dvd_mult_cong;   (* dvd a b ==> dvd (a*c)(b*c) *)
val dvd_add_vGR3        = varify dvd_add;         (* dvd d m ==> dvd d n ==> dvd d (m+n) *)
val dvd_le_vGR3         = varify dvd_le;          (* dvd d n ==> (oeq n 0 ==> oFalse) ==> le d n *)
val mult_le_mono_vGR3   = varify mult_le_mono;    (* le j k ==> le (c*j)(c*k) *)

fun dvd_diff_r (pT,xT,yT) h1 h2 =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
    [(("p",0), ctermGR pT),(("x",0), ctermGR xT),(("y",0), ctermGR yT)] dvd_diff_vGR3)) h1) h2;
fun dvd_trans_r (aT,bT,cT) h1 h2 =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
    [(("a",0), ctermGR aT),(("b",0), ctermGR bT),(("c",0), ctermGR cT)] dvd_trans_vGR3)) h1) h2;
fun dvd_mult_right_r (aT,bT,cT) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
    [(("a",0), ctermGR aT),(("b",0), ctermGR bT),(("c",0), ctermGR cT)] dvd_mult_right_vGR3)) h;
fun dvd_mult_cong_r (aT,bT,cT) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
    [(("a",0), ctermGR aT),(("b",0), ctermGR bT),(("c",0), ctermGR cT)] dvd_mult_cong_vGR3)) h;
fun dvd_add_r (dT,mT,nT) h1 h2 =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
    [(("d",0), ctermGR dT),(("m",0), ctermGR mT),(("n",0), ctermGR nT)] dvd_add_vGR3)) h1) h2;
fun dvd_le_r (dT,nT) hdvd hnz =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
    [(("d",0), ctermGR dT),(("n",0), ctermGR nT)] dvd_le_vGR3)) hdvd) hnz;
fun mult_le_mono_r (cT,jT_,kT) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
    [(("c",0), ctermGR cT),(("j",0), ctermGR jT_),(("k",0), ctermGR kT)] mult_le_mono_vGR3)) h;
val () = out "SEAT3_VARIFY_OK\n";

(* ----------------------------------------------------------------------------
   sqcong_of_signed (m,x') (xT) hsig :
     hsig : Trueprop (Disj (cong m x' x)(cong m (add x' x) 0))
     ==>  cong m (x'*x')(x*x)
   LEFT  (cong m x' x)        : cong_sq_r.
   RIGHT (cong m (x'+x) 0)    : derive cong m (x'*x')(x*x) from x'+x ≡ 0.
     mul hsigR by (cong_refl x') :  cong m ((x'+x)*x')(0*x') -> cong m (x'^2 + x*x') 0.
     mul hsigR by (cong_refl x)  :  cong m ((x'+x)*x)(0*x)  -> cong m (x'*x + x*x) 0.
     so  cong m (x'^2 + x*x') 0  and  cong m (x'*x + x*x) 0 ; note x*x' = x'*x (comm),
     so the two zero-congruent sums share the middle term x'*x.  Then:
        cong m (x'^2 + x'*x)(x'*x + x*x)   [trans: A≡0, 0≡B via sym]
        cancel the common x'*x additively inside the cong via cong_radd-style:
        write both as (x'*x) + (..) using comm/assoc and cancel.
   To avoid heavy cancellation, use the cleaner route:
     from cong m (x'+x) 0 : cong m ((x'+x)*(x'-?))... no.  Use the identity-free path:
     cong m (x'+x) 0  =>  cong m ((x'+x)*(x'+x)) 0          [cong_sq_r on hsigR? no, sq of (x'+x)]
        actually cong_sq_r (m, x'+x, 0) hsigR : cong m ((x'+x)^2)(0*0)=cong m ((x'+x)^2) 0
     (x'+x)^2 = x'^2 + (2*x'*x + x^2).  And we want x'^2 ≡ x^2.
     Hmm that mixes a 2*x'*x term.  The additive-cancel route is cleanest; do it.
   ---------------------------------------------------------------------------- *)
fun sqcong_of_signed (mT, xpT) xT hsig =
  let
    val goalC = cong mT (sq3 xpT) (sq3 xT)
    val Lprop = cong mT xpT xT
    val Rprop = cong mT (add xpT xT) ZeroC
    (* LEFT *)
    val caseL =
      let val h = Thm.assume (ctermGR (jT Lprop))
      in Thm.implies_intr (ctermGR (jT Lprop)) (cong_sq_r (mT, xpT, xT) h) end
    (* RIGHT : cong m (x'+x) 0 *)
    val caseR =
      let
        val h = Thm.assume (ctermGR (jT Rprop))     (* cong m (x'+x) 0 *)
        (* A : cong m ((x'+x)*x') 0 *)
        val cA1 = cong_mult_r (mT, add xpT xT, ZeroC, xpT, xpT) h (cong_refl_g (mT, xpT))
                  (* cong m ((x'+x)*x')(0*x') *)
        val z0a = mult0_d xpT                         (* 0*x' = 0 *)
        val PzA = Term.lambda (Free("zsA",natT)) (cong mT (mult (add xpT xT) xpT) (Free("zsA",natT)))
        val cA = oeq_rw_r (PzA, mult ZeroC xpT, ZeroC) z0a cA1  (* cong m ((x'+x)*x') 0 *)
        (* (x'+x)*x' = x'*x' + x*x'  [right_distrib] *)
        val dA = rightdistrib_g (xpT, xT, xpT)        (* (x'+x)*x' = x'*x' + x*x' *)
        val PdA = Term.lambda (Free("zdA",natT)) (cong mT (Free("zdA",natT)) ZeroC)
        val cA2 = oeq_rw_r (PdA, mult (add xpT xT) xpT, add (mult xpT xpT)(mult xT xpT)) dA cA
                  (* cong m (x'*x' + x*x') 0 *)
        (* B : cong m ((x'+x)*x) 0 *)
        val cB1 = cong_mult_r (mT, add xpT xT, ZeroC, xT, xT) h (cong_refl_g (mT, xT))
        val z0b = mult0_d xT
        val PzB = Term.lambda (Free("zsB",natT)) (cong mT (mult (add xpT xT) xT) (Free("zsB",natT)))
        val cB = oeq_rw_r (PzB, mult ZeroC xT, ZeroC) z0b cB1   (* cong m ((x'+x)*x) 0 *)
        val dB = rightdistrib_g (xpT, xT, xT)         (* (x'+x)*x = x'*x + x*x *)
        val PdB = Term.lambda (Free("zdB",natT)) (cong mT (Free("zdB",natT)) ZeroC)
        val cB2 = oeq_rw_r (PdB, mult (add xpT xT) xT, add (mult xpT xT)(mult xT xT)) dB cB
                  (* cong m (x'*x + x*x) 0 *)
        (* now: cA2 : cong m (x'*x' + x*x') 0 ; rewrite x*x' -> x'*x [comm] *)
        val cxx = multcomm_g (xT, xpT)                (* x*x' = x'*x *)
        val PcA = Term.lambda (Free("zcA",natT)) (cong mT (add (mult xpT xpT) (Free("zcA",natT))) ZeroC)
        val cA3 = oeq_rw_r (PcA, mult xT xpT, mult xpT xT) cxx cA2
                  (* cong m (x'*x' + x'*x) 0 *)
        (* cong m (x'*x' + x'*x)(x'*x + x*x) : trans A3 with sym(B2) *)
        val cAB = cong_trans_g (mT, add (mult xpT xpT)(mult xpT xT), ZeroC, add (mult xpT xT)(mult xT xT))
                    cA3 (cong_sym_g (mT, add (mult xpT xT)(mult xT xT), ZeroC) cB2)
                  (* cong m (x'*x' + x'*x)(x'*x + x*x) *)
        (* rewrite LHS (x'*x' + x'*x) -> (x'*x) + x'*x'  [comm] ; RHS already (x'*x)+x*x *)
        val lcomm = addcomm_g (mult xpT xpT, mult xpT xT)   (* x'*x'+x'*x = x'*x + x'*x' *)
        val Pl = Term.lambda (Free("zl3",natT)) (cong mT (Free("zl3",natT)) (add (mult xpT xT)(mult xT xT)))
        val cAB2 = oeq_rw_r (Pl, add (mult xpT xpT)(mult xpT xT), add (mult xpT xT)(mult xpT xpT)) lcomm cAB
                  (* cong m (x'*x + x'*x')(x'*x + x*x) *)
        (* cancel the left summand (x'*x) : cong_ladd_cancel.  Use cong_radd_cancel by
           first commuting both sides to put x'*x on the RIGHT. *)
        val rcL = addcomm_g (mult xpT xT, mult xpT xpT)   (* x'*x + x'*x' = x'*x' + x'*x *)
        val rcR = addcomm_g (mult xpT xT, mult xT xT)     (* x'*x + x*x  = x*x + x'*x *)
        val zb = Free("zbb3", natT)
        val Pb1 = Term.lambda zb (cong mT zb (add (mult xpT xT)(mult xT xT)))
        val cAB3 = oeq_rw_r (Pb1, add (mult xpT xT)(mult xpT xpT), add (mult xpT xpT)(mult xpT xT)) rcL cAB2
                  (* cong m (x'*x' + x'*x)(x'*x + x*x) *)
        val Pb2 = Term.lambda zb (cong mT (add (mult xpT xpT)(mult xpT xT)) zb)
        val cAB4 = oeq_rw_r (Pb2, add (mult xpT xT)(mult xT xT), add (mult xT xT)(mult xpT xT)) rcR cAB3
                  (* cong m (x'*x' + x'*x)(x*x + x'*x) *)
        val canc = cong_radd_cancel_g (mT, mult xpT xpT, mult xT xT, mult xpT xT) cAB4
                  (* cong m (x'*x')(x*x) *)
      in Thm.implies_intr (ctermGR (jT Rprop)) canc end
  in disjE_r (Lprop, Rprop, goalC) hsig caseL caseR end;
val () = out "SEAT3_SQCONG_OF_SIGNED_DEFINED\n";

(* smoke (cheap) : exercise sqcong_of_signed on fresh frees from an assumed disjunction *)
val () =
  let
    val mF = Free("m_ss",natT); val xpF = Free("xp_ss",natT); val xF = Free("x_ss",natT)
    val hsig = Thm.assume (ctermGR (jT (mkDisj (cong mF xpF xF)(cong mF (add xpF xF) ZeroC))))
    val r = sqcong_of_signed (mF, xpF) xF hsig
  in out ("SMOKE sqcong_of_signed hyps="^Int.toString(length(Thm.hyps_of r))
          ^" prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)^"\n") end
  handle e => out ("SMOKE sqcong_of_signed FAIL "^exnMessage e^"\n");
val () = out "SEAT3_SQCONG_SMOKE_DONE\n";

(* ============================================================================
   STEP (a) — SIGNED four_residue_sum.
   Inputs (on assumptions):
     hm    : lt 0 m
     hbody : oeq N (a*a + b*b + c*c + d*d)
     hN0   : cong m N 0
   Output:
     EX a' b' c' d' r.
        oeq (a'*a'+b'*b'+c'*c'+d'*d')(m*r)
      /\ (cong m a' a OR cong m (a'+a) 0)
      /\ (cong m b' b OR cong m (b'+b) 0)
      /\ (cong m c' c OR cong m (c'+c) 0)
      /\ (cong m d' d OR cong m (d'+d) 0)
      /\ le (a'+a') m /\ le (b'+b') m /\ le (c'+c') m /\ le (d'+d') m
   ============================================================================ *)

(* sign disjunct + bound shape for one coordinate *)
fun sigDj mT xpT xT = mkDisj (cong mT xpT xT)(cong mT (add xpT xT) ZeroC);

(* unpack one sym_residue_signed existential for coordinate (m,a) with hm. *)
fun with_signed wnm (mT, aT) hm (k : term -> thm -> thm -> thm) goalC =
  let
    val ex = sym_residue_signed (mT, aT) hm    (* EX a'. (sigDj) /\ le (a'+a') m *)
    val wF = Free(wnm, natT)
    val P = Term.lambda wF (mkConj (sigDj mT wF aT) (le (add wF wF) mT))
    fun bd ap (hconj:thm) =
      let val hsig = conjunct1_r (sigDj mT ap aT, le (add ap ap) mT) hconj
          val hle  = conjunct2_r (sigDj mT ap aT, le (add ap ap) mT) hconj
      in k ap hsig hle end
  in exE_r (P, goalC) ex wnm natT bd end;

fun signed_four_residue_sum (mT, aT, bT, cT, dT, nT) hm hbody hN0 =
  let
    (* the nested existential predicate over a',b',c',d',r *)
    val a4=Free("a4s",natT); val b4=Free("b4s",natT); val c4=Free("c4s",natT)
    val d4=Free("d4s",natT); val r4=Free("r4s",natT)
    fun bodyTerm (ap,bp,cp,dp,rr) =
      mkConj (oeq (add (add (sq3 ap)(sq3 bp))(add (sq3 cp)(sq3 dp))) (mult mT rr))
        (mkConj (sigDj mT ap aT)
          (mkConj (sigDj mT bp bT)
            (mkConj (sigDj mT cp cT)
              (mkConj (sigDj mT dp dT)
                (mkConj (le (add ap ap) mT)
                  (mkConj (le (add bp bp) mT)
                    (mkConj (le (add cp cp) mT) (le (add dp dp) mT))))))))
    val predR = Term.lambda r4 (bodyTerm (a4,b4,c4,d4,r4))
    val predD = Term.lambda d4 (mkEx (Term.lambda r4 (bodyTerm (a4,b4,c4,d4,r4))))
    val predC = Term.lambda c4 (mkEx (Term.lambda d4 (mkEx (Term.lambda r4 (bodyTerm (a4,b4,c4,d4,r4))))))
    val predB = Term.lambda b4 (mkEx (Term.lambda c4 (mkEx (Term.lambda d4 (mkEx (Term.lambda r4 (bodyTerm (a4,b4,c4,d4,r4))))))))
    val goalP = Term.lambda a4 (mkEx predB)
    val goalC = mkEx goalP

    fun finish ap hsa hla bp hsb hlb cp hsc hlc dp hsd hld =
      let
        (* squared congs from the signed disjuncts *)
        val hca = sqcong_of_signed (mT, ap) aT hsa     (* cong m (ap^2)(a^2) *)
        val hcb = sqcong_of_signed (mT, bp) bT hsb
        val hcc = sqcong_of_signed (mT, cp) cT hsc
        val hcd = sqcong_of_signed (mT, dp) dT hsd
        (* cong m (ap^2+bp^2)(a^2+b^2) etc. *)
        val cab = cong_add_g (mT, sq3 ap, sq3 aT, sq3 bp, sq3 bT) hca hcb
        val ccd = cong_add_g (mT, sq3 cp, sq3 cT, sq3 dp, sq3 dT) hcc hcd
        val sumLHS = add (add (sq3 ap)(sq3 bp))(add (sq3 cp)(sq3 dp))
        val sumRHSab = add (sq3 aT)(sq3 bT)
        val sumRHScd = add (sq3 cT)(sq3 dT)
        val csum = cong_add_g (mT, add (sq3 ap)(sq3 bp), sumRHSab, add (sq3 cp)(sq3 dp), sumRHScd) cab ccd
                   (* cong m sumLHS ((a^2+b^2)+(c^2+d^2)) *)
        val hbodyS = oeqSym_r2 hbody    (* oeq ((a^2+b^2)+(c^2+d^2)) N *)
        val cN = oeq_rw_r (Term.lambda (Free("zfrs",natT)) (cong mT sumLHS (Free("zfrs",natT))),
                           add sumRHSab sumRHScd, nT) hbodyS csum   (* cong m sumLHS N *)
        val csum0 = cong_trans_g (mT, sumLHS, nT, ZeroC) cN hN0     (* cong m sumLHS 0 *)
        val exMult = cong_zero_imp_mult (mT, sumLHS) csum0          (* EX r. sumLHS = m*r *)
        val Pr = Term.lambda (Free("rcm",natT)) (oeq sumLHS (mult mT (Free("rcm",natT))))
        fun bdr rr (hr:thm) =   (* hr : oeq sumLHS (m*r) *)
          let
            (* build the big conjunction at (ap,bp,cp,dp,rr) *)
            val cBnd = mkConj (le (add ap ap) mT)
                         (mkConj (le (add bp bp) mT)
                           (mkConj (le (add cp cp) mT) (le (add dp dp) mT)))
            val cBndThm = conjI_r (le (add ap ap) mT, mkConj (le (add bp bp) mT)(mkConj (le (add cp cp) mT)(le (add dp dp) mT)))
                            hla (conjI_r (le (add bp bp) mT, mkConj (le (add cp cp) mT)(le (add dp dp) mT))
                                   hlb (conjI_r (le (add cp cp) mT, le (add dp dp) mT) hlc hld))
            val cSigD = mkConj (sigDj mT dp dT) cBnd
            val cSigDThm = conjI_r (sigDj mT dp dT, cBnd) hsd cBndThm
            val cSigC = mkConj (sigDj mT cp cT) cSigD
            val cSigCThm = conjI_r (sigDj mT cp cT, cSigD) hsc cSigDThm
            val cSigB = mkConj (sigDj mT bp bT) cSigC
            val cSigBThm = conjI_r (sigDj mT bp bT, cSigC) hsb cSigCThm
            val cSigA = mkConj (sigDj mT ap aT) cSigB
            val cSigAThm = conjI_r (sigDj mT ap aT, cSigB) hsa cSigBThm
            val eqPart = oeq sumLHS (mult mT rr)
            val bigConj = conjI_r (eqPart, cSigA) hr cSigAThm
            (* nested exI : r, then d, c, b, a *)
            (* nested exI, inside-out : r, d, c, b, a.  At each level the ALREADY-
               chosen (inner) witnesses are concrete; the level's own var + outer
               vars are bound.  So eB's predicate uses ap CONCRETE (NOT the global
               predB, which keeps a4 free for the a-level). *)
            val eR = exI_r (Term.lambda r4 (bodyTerm (ap,bp,cp,dp,r4))) rr bigConj
            val eD = exI_r (Term.lambda d4 (mkEx (Term.lambda r4 (bodyTerm (ap,bp,cp,d4,r4))))) dp eR
            val eC = exI_r (Term.lambda c4 (mkEx (Term.lambda d4 (mkEx (Term.lambda r4 (bodyTerm (ap,bp,c4,d4,r4))))))) cp eD
            val eB = exI_r (Term.lambda b4 (mkEx (Term.lambda c4 (mkEx (Term.lambda d4 (mkEx (Term.lambda r4 (bodyTerm (ap,b4,c4,d4,r4))))))))) bp eC
            val eA = exI_r goalP ap eB
          in eA end
      in exE_r (Pr, goalC) exMult "rs_frs" natT bdr end
  in
    with_signed "ares" (mT, aT) hm (fn ap => fn hsa => fn hla =>
      with_signed "bres" (mT, bT) hm (fn bp => fn hsb => fn hlb =>
        with_signed "cres" (mT, cT) hm (fn cp => fn hsc => fn hlc =>
          with_signed "dres" (mT, dT) hm (fn dp => fn hsd => fn hld =>
            finish ap hsa hla bp hsb hlb cp hsc hlc dp hsd hld) goalC) goalC) goalC) goalC
  end;
val () = out "SEAT3_SIGNED_FRS_DEFINED\n";

(* signed_four_residue_sum_thm : 0-hyp discharged lemma. *)
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
val () = out ("signed_four_residue_sum prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of signed_four_residue_sum_thm)^"\n");

(* aconv against intended *)
val signed_frs_intended =
  let
    val mF=Free("m_sf",natT); val aF=Free("a_sf",natT); val bF=Free("b_sf",natT)
    val cF=Free("c_sf",natT); val dF=Free("d_sf",natT); val nF=Free("N_sf",natT)
    val a4=Free("a4s",natT); val b4=Free("b4s",natT); val c4=Free("c4s",natT)
    val d4=Free("d4s",natT); val r4=Free("r4s",natT)
    fun sq x = mult x x
    fun sigD xp x = mkDisj (cong mF xp x)(cong mF (add xp x) ZeroC)
    val body = mkConj (oeq (add (add (sq a4)(sq b4))(add (sq c4)(sq d4)))(mult mF r4))
                 (mkConj (sigD a4 aF)(mkConj (sigD b4 bF)(mkConj (sigD c4 cF)(mkConj (sigD d4 dF)
                   (mkConj (le (add a4 a4) mF)(mkConj (le (add b4 b4) mF)(mkConj (le (add c4 c4) mF)(le (add d4 d4) mF))))))))
    val concl = mkEx (Term.lambda a4 (mkEx (Term.lambda b4 (mkEx (Term.lambda c4 (mkEx (Term.lambda d4 (mkEx (Term.lambda r4 body)))))))))
    val prem2 = oeq nF (add (add (mult aF aF)(mult bF bF))(add (mult cF cF)(mult dF dF)))
  in Logic.mk_implies (jT (lt ZeroC mF),
       Logic.mk_implies (jT prem2,
         Logic.mk_implies (jT (cong mF nF ZeroC), jT concl))) end;
val sfrs_aconv = ((Thm.prop_of signed_four_residue_sum_thm) aconv signed_frs_intended);
val sfrs_0hyp = (length (Thm.hyps_of signed_four_residue_sum_thm) = 0);
val () = out ("SEAT3_SIGNED_FRS_VALIDATE aconv="^Bool.toString sfrs_aconv^" zero_hyp="^Bool.toString sfrs_0hyp^"\n");
(* SOUNDNESS PROBE (a): the lemma genuinely carries the SIGNED per-coordinate
   disjunction, NOT merely the squared cong (a4*a4 == a*a) of the banked
   four_residue_sum_thm.  The kernel result must NOT be aconv the squared-only form. *)
val sfrs_probe_signed =
  let
    val mF=Free("m_sf",natT); val aF=Free("a_sf",natT); val bF=Free("b_sf",natT)
    val cF=Free("c_sf",natT); val dF=Free("d_sf",natT); val nF=Free("N_sf",natT)
    val a4=Free("a4s",natT); val b4=Free("b4s",natT); val c4=Free("c4s",natT)
    val d4=Free("d4s",natT); val r4=Free("r4s",natT)
    fun sq x = mult x x
    val bodySq = mkConj (oeq (add (add (sq a4)(sq b4))(add (sq c4)(sq d4)))(mult mF r4))
                 (mkConj (cong mF (sq a4)(sq aF))(mkConj (cong mF (sq b4)(sq bF))(mkConj (cong mF (sq c4)(sq cF))(mkConj (cong mF (sq d4)(sq dF))
                   (mkConj (le (add a4 a4) mF)(mkConj (le (add b4 b4) mF)(mkConj (le (add c4 c4) mF)(le (add d4 d4) mF))))))))
    val conclSq = mkEx (Term.lambda a4 (mkEx (Term.lambda b4 (mkEx (Term.lambda c4 (mkEx (Term.lambda d4 (mkEx (Term.lambda r4 bodySq)))))))))
    val prem2 = oeq nF (add (add (mult aF aF)(mult bF bF))(add (mult cF cF)(mult dF dF)))
    val squaredOnly = Logic.mk_implies (jT (lt ZeroC mF),
       Logic.mk_implies (jT prem2, Logic.mk_implies (jT (cong mF nF ZeroC), jT conclSq)))
  in not ((Thm.prop_of signed_four_residue_sum_thm) aconv squaredOnly) end;
val () = out ("SEAT3_STEP_A_PROBE_SIGNED "^Bool.toString sfrs_probe_signed^"\n");
val () = if sfrs_aconv andalso sfrs_0hyp andalso sfrs_probe_signed then out "SEAT3_STEP_A_OK\n" else out "SEAT3_STEP_A_FAILED\n";

(* ============================================================================
   Banked reusable helpers (GR-ported): mult_eq_zero, mult_left_cancel, dvd_sq.
   ============================================================================ *)

(* mult_eq_zero : oeq (mult a b) 0 ==> Disj (oeq a 0)(oeq b 0)   (cases on a) *)
val mult_eq_zero_GR =
  let
    val aF = Free("a_mez3", natT); val bF = Free("b_mez3", natT)
    val hypP = jT (oeq (mult aF bF) ZeroC)
    val hyp  = Thm.assume (ctermGR hypP)
    val goalC = mkDisj (oeq aF ZeroC)(oeq bF ZeroC)
    val dz = dzos_d aF                                  (* Disj (oeq a 0)(Ex q. oeq a (Suc q)) *)
    val caseZ =
      let val hZ = Thm.assume (ctermGR (jT (oeq aF ZeroC)))
      in Thm.implies_intr (ctermGR (jT (oeq aF ZeroC)))
           (disjI1_r (oeq aF ZeroC, oeq bF ZeroC) hZ) end
    val sucAbs = Abs("q", natT, oeq aF (suc (Bound 0)))
    val caseS =
      let val hEx = Thm.assume (ctermGR (jT (mkEx sucAbs)))
          fun body q (hq:thm) =          (* hq : oeq a (Suc q) *)
            let val abq = mult_cong_l_g (aF, suc q, bF) hq      (* a*b = (Suc q)*b *)
                val sqb = multSuc_d (q, bF)                      (* (Suc q)*b = b + q*b *)
                val ab_e = oeqTrans_r2 (oeqSym_r2 (oeqTrans_r2 (abq, sqb)), hyp)
                           (* (b + q*b) = 0 *)
                val bz = add_eq_zero_left_d (bF, mult q bF) ab_e (* b = 0 *)
            in disjI2_r (oeq aF ZeroC, oeq bF ZeroC) bz end
          val res = exE_r (sucAbs, goalC) hEx "q_mez3" natT body
      in Thm.implies_intr (ctermGR (jT (mkEx sucAbs))) res end
  in Thm.implies_intr (ctermGR hypP) (disjE_r (oeq aF ZeroC, mkEx sucAbs, goalC) dz caseZ caseS) end;
val mult_eq_zero_vGR = varify mult_eq_zero_GR;
fun mult_eq_zero_r (aT,bT) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
    [(("a_mez3",0), ctermGR aT),(("b_mez3",0), ctermGR bT)] mult_eq_zero_vGR)) h;
val () = out ("mult_eq_zero_GR hyps="^Int.toString(length(Thm.hyps_of mult_eq_zero_GR))^"\n");

(* mult_left_cancel : lt 0 p ==> oeq (mult p a)(mult p b) ==> oeq a b *)
val mult_left_cancel_GR =
  let
    val pF = Free("p_mlc3", natT); val aF = Free("a_mlc3", natT); val bF = Free("b_mlc3", natT)
    val hPos = Thm.assume (ctermGR (jT (lt ZeroC pF)))
    val hEq  = Thm.assume (ctermGR (jT (oeq (mult pF aF)(mult pF bF))))
    val goalC = oeq aF bF
    val tot = le_total_d (aF, bF)
    fun contraP goal =
      let val hpz = Thm.assume (ctermGR (jT (oeq pF ZeroC)))
          val Psub = Term.lambda (Free("zmlc",natT)) (lt ZeroC (Free("zmlc",natT)))
          val lt00 = oeq_rw_r (Psub, pF, ZeroC) hpz hPos     (* lt 0 0 *)
          val fls  = lt_irrefl_r ZeroC lt00
          val g    = Thm.implies_elim (oFalse_elim_r goal) fls
      in Thm.implies_intr (ctermGR (jT (oeq pF ZeroC))) g end
    val leAbsAB = Abs("k", natT, oeq bF (add aF (Bound 0)))
    val caseAB =
      let val hLe = Thm.assume (ctermGR (jT (le aF bF)))
          fun body d (hd:thm) =        (* hd : oeq b (add a d) *)
            let val pb1 = mult_cong_r_d (pF, bF, add aF d) hd      (* p*b = p*(a+d) *)
                val ld  = leftdistrib_g (pF, aF, d)                 (* p*(a+d) = p*a + p*d *)
                val pb2 = oeqTrans_r2 (pb1, ld)                     (* p*b = p*a + p*d *)
                val pa_e = oeqTrans_r2 (hEq, pb2)                   (* p*a = p*a + p*d *)
                val pa0 = oeqSym_r2 (add0r_d (mult pF aF))          (* p*a = (p*a)+0 ; sym -> (p*a)+0 = p*a *)
                val both = oeqTrans_r2 (oeqSym_r2 pa0, pa_e)        (* (p*a)+0 = (p*a)+(p*d) *)
                val zpd = add_left_cancel_g (mult pF aF, ZeroC, mult pF d) both  (* 0 = p*d *)
                val pdz = oeqSym_r2 zpd                              (* p*d = 0 *)
                val disj = mult_eq_zero_r (pF, d) pdz               (* p=0 \/ d=0 *)
                val cZp = contraP goalC
                val cZd =
                  let val hdz = Thm.assume (ctermGR (jT (oeq d ZeroC)))
                      val ba0 = oeqTrans_r2 (hd, add_cong_r_d (aF, d, ZeroC) hdz)  (* b = a+0 *)
                      val ba  = oeqTrans_r2 (ba0, add0r_d aF)                       (* b = a *)
                      val ab  = oeqSym_r2 ba                                        (* a = b *)
                  in Thm.implies_intr (ctermGR (jT (oeq d ZeroC))) ab end
            in disjE_r (oeq pF ZeroC, oeq d ZeroC, goalC) disj cZp cZd end
          val r = exE_r (leAbsAB, goalC) hLe "d_ab3" natT body
      in Thm.implies_intr (ctermGR (jT (le aF bF))) r end
    val leAbsBA = Abs("k", natT, oeq aF (add bF (Bound 0)))
    val caseBA =
      let val hLe = Thm.assume (ctermGR (jT (le bF aF)))
          fun body d (hd:thm) =        (* hd : oeq a (add b d) *)
            let val pa1 = mult_cong_r_d (pF, aF, add bF d) hd
                val ld  = leftdistrib_g (pF, bF, d)
                val pa2 = oeqTrans_r2 (pa1, ld)
                val pb_e = oeqTrans_r2 (oeqSym_r2 hEq, pa2)         (* p*b = p*b + p*d *)
                val pb0 = oeqSym_r2 (add0r_d (mult pF bF))
                val both = oeqTrans_r2 (oeqSym_r2 pb0, pb_e)
                val zpd = add_left_cancel_g (mult pF bF, ZeroC, mult pF d) both
                val pdz = oeqSym_r2 zpd
                val disj = mult_eq_zero_r (pF, d) pdz
                val cZp = contraP goalC
                val cZd =
                  let val hdz = Thm.assume (ctermGR (jT (oeq d ZeroC)))
                      val ab0 = oeqTrans_r2 (hd, add_cong_r_d (bF, d, ZeroC) hdz)
                      val ab  = oeqTrans_r2 (ab0, add0r_d bF)        (* a = b *)
                  in Thm.implies_intr (ctermGR (jT (oeq d ZeroC))) ab end
            in disjE_r (oeq pF ZeroC, oeq d ZeroC, goalC) disj cZp cZd end
          val r = exE_r (leAbsBA, goalC) hLe "d_ba3" natT body
      in Thm.implies_intr (ctermGR (jT (le bF aF))) r end
    val body = disjE_r (le aF bF, le bF aF, goalC) tot caseAB caseBA
  in Thm.implies_intr (ctermGR (jT (lt ZeroC pF)))
       (Thm.implies_intr (ctermGR (jT (oeq (mult pF aF)(mult pF bF)))) body) end;
val mult_left_cancel_vGR = varify mult_left_cancel_GR;
fun mult_left_cancel_r (pT,aT,bT) hpos heq =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
    [(("p_mlc3",0), ctermGR pT),(("a_mlc3",0), ctermGR aT),(("b_mlc3",0), ctermGR bT)] mult_left_cancel_vGR)) hpos) heq;
val () = out ("mult_left_cancel_GR hyps="^Int.toString(length(Thm.hyps_of mult_left_cancel_GR))^"\n");
val () = out "SEAT3_CANCEL_HELPERS_OK\n";

(* ============================================================================
   STEP (b) — r=0 EXCLUSION.
   Two pieces:
     (b1) signed_zero_imp_dvd : (cong m x' x OR cong m (x'+x) 0) ==> oeq x' 0 ==> dvd m x
     (b2) divides_all_imp_false :
            prime2 p ==> lt 1 m ==> lt m p ==> dvd m a ==> dvd m b ==> dvd m c ==> dvd m d
              ==> oeq (m*p)(a*a+b*b+c*c+d*d) ==> oFalse
   ============================================================================ *)

(* lt 0 m from lt 1 m *)
fun lt0_of_lt1 mT hlt1 = le_trans_d (suc ZeroC, suc (suc ZeroC), mT) le_1_2 hlt1;  (* le 1 m = lt 0 m *)

(* dvd m x from oeq x (mult m w) *)
fun dvd_witness (mT, xT, w) hyp =
  exI_r (Abs("k", natT, oeq xT (mult mT (Bound 0)))) w hyp;

(* signed_zero_imp_dvd : on assumptions hsig + hx0 -> dvd m x *)
fun signed_zero_imp_dvd (mT, xpT, xT) hsig hx0 =   (* hsig:Disj(..); hx0:oeq x' 0 *)
  let
    val goalC = dvd mT xT
    val Lprop = cong mT xpT xT
    val Rprop = cong mT (add xpT xT) ZeroC
    (* in both branches: substitute x'=0 then derive cong m x 0, then dvd m x. *)
    val caseL =
      let val h = Thm.assume (ctermGR (jT Lprop))     (* cong m x' x *)
          (* rewrite x'->0 : cong m 0 x *)
          val Pz = Term.lambda (Free("zszL",natT)) (cong mT (Free("zszL",natT)) xT)
          val c0x = oeq_rw_r (Pz, xpT, ZeroC) hx0 h    (* cong m 0 x *)
          val cx0 = cong_sym_g (mT, ZeroC, xT) c0x      (* cong m x 0 *)
          (* dvd m x : from cong m x 0 use cong_zero_imp_mult (gives EX r. x = m*r) then exI->dvd *)
          val exm = cong_zero_imp_mult (mT, xT) cx0     (* EX r. oeq x (mult m r) *)
          (* this IS dvd m x (same shape) ; but rebuild to match dvd exactly *)
          val Pr = Term.lambda (Free("rcm",natT)) (oeq xT (mult mT (Free("rcm",natT))))
          fun bd r (hr:thm) = dvd_witness (mT, xT, r) hr
      in Thm.implies_intr (ctermGR (jT Lprop)) (exE_r (Pr, goalC) exm "rL_sz" natT bd) end
    val caseR =
      let val h = Thm.assume (ctermGR (jT Rprop))     (* cong m (x'+x) 0 *)
          (* x'+x = 0+x = x via x'=0 *)
          val P1 = Term.lambda (Free("zszR",natT)) (cong mT (add (Free("zszR",natT)) xT) ZeroC)
          val c1 = oeq_rw_r (P1, xpT, ZeroC) hx0 h      (* cong m (0+x) 0 *)
          val a0 = add0_d xT                             (* 0+x = x *)
          val P2 = Term.lambda (Free("zszR2",natT)) (cong mT (Free("zszR2",natT)) ZeroC)
          val cx0 = oeq_rw_r (P2, add ZeroC xT, xT) a0 c1   (* cong m x 0 *)
          val exm = cong_zero_imp_mult (mT, xT) cx0
          val Pr = Term.lambda (Free("rcm",natT)) (oeq xT (mult mT (Free("rcm",natT))))
          fun bd r (hr:thm) = dvd_witness (mT, xT, r) hr
      in Thm.implies_intr (ctermGR (jT Rprop)) (exE_r (Pr, goalC) exm "rR_sz" natT bd) end
  in disjE_r (Lprop, Rprop, goalC) hsig caseL caseR end;
val () = out "SEAT3_SIGNED_ZERO_DVD_DEFINED\n";

(* dvd_sq : dvd m a ==> dvd (m*m)(a*a)   [witness k*k where a = m*k] *)
fun dvd_sq (mT, aT) hdvd =     (* hdvd : dvd m a = EX k. oeq a (mult m k) *)
  let
    val goalC = dvd (mult mT mT)(mult aT aT)
    val Pk = Abs("k", natT, oeq aT (mult mT (Bound 0)))
    fun bd k (hk:thm) =   (* hk : oeq a (mult m k) *)
      let
        (* a*a = (m*k)*(m*k) = (m*m)*(k*k)  via proveIdentityG *)
        val aaEq = let val l1 = mult_cong_l_g (aT, mult mT k, aT) hk    (* a*a = (m*k)*a *)
                       val l2 = mult_cong_r_g (mult mT k, aT, mult mT k) hk (* (m*k)*a = (m*k)*(m*k) *)
                       val idP = proveIdentityG (mult (mult mT k)(mult mT k)) (mult (mult mT mT)(mult k k))
                                 (* (m*k)*(m*k) = (m*m)*(k*k) *)
                   in oeqTrans_g (oeqTrans_g (l1, l2), idP) end   (* a*a = (m*m)*(k*k) *)
        val w = mult k k
      in dvd_witness (mult mT mT, mult aT aT, w) aaEq end
  in exE_r (Pk, goalC) hdvd "k_dsq" natT bd end;
val () = out "SEAT3_DVD_SQ_DEFINED\n";

fun divides_all_imp_false (pT, mT, aT, bT, cT, dT) hPrime hlt1m hltmp hda hdb hdc hdd hbody =
  let
    (* hbody : oeq (m*p)(a*a+b*b+c*c+d*d) *)
    val hpos = lt0_of_lt1 mT hlt1m                      (* lt 0 m *)
    val dma = dvd_sq (mT, aT) hda                       (* dvd (m*m)(a*a) *)
    val dmb = dvd_sq (mT, bT) hdb
    val dmc = dvd_sq (mT, cT) hdc
    val dmd = dvd_sq (mT, dT) hdd
    val mm = mult mT mT
    val dab = dvd_add_r (mm, mult aT aT, mult bT bT) dma dmb   (* m^2 | a^2+b^2 *)
    val dcd = dvd_add_r (mm, mult cT cT, mult dT dT) dmc dmd   (* m^2 | c^2+d^2 *)
    val dsum = dvd_add_r (mm, add (mult aT aT)(mult bT bT), add (mult cT cT)(mult dT dT)) dab dcd
               (* m^2 | (a^2+b^2)+(c^2+d^2) *)
    (* rewrite sum -> m*p directly via sym hbody *)
    val Pdv = Term.lambda (Free("zdv",natT)) (dvd mm (Free("zdv",natT)))
    val dmp2 = oeq_rw_r (Pdv, add (add (mult aT aT)(mult bT bT))(add (mult cT cT)(mult dT dT)), mult mT pT)
                (oeqSym_r2 hbody) dsum
              (* m^2 | (m*p) *)
    (* m^2 | m*p  -> EX t. m*p = (m*m)*t ; (m*m)*t = m*(m*t) ; cancel m -> p = m*t -> dvd m p *)
    val dvdMp = dmp2
    val Pt = Abs("t", natT, oeq (mult mT pT)(mult mm (Bound 0)))
    val dvdmp_to_dvdmp =
      let
        val goalC = dvd mT pT
        fun bd t (ht:thm) =    (* ht : oeq (m*p)((m*m)*t) *)
          let
            val assoc = multassoc_g (mT, mT, t)         (* (m*m)*t = m*(m*t) *)
            val mpmt = oeqTrans_r2 (ht, assoc)          (* m*p = m*(m*t) *)
            val pEq = mult_left_cancel_r (mT, pT, mult mT t) hpos mpmt  (* oeq p (mult m t) *)
          in dvd_witness (mT, pT, t) pEq end   (* dvd m p, witness t (NOT m*t) *)
      in exE_r (Pt, goalC) dvdMp "t_dmp" natT bd end
    val dvdmp = dvdmp_to_dvdmp                          (* dvd m p *)
    (* prime2_div : dvd m p -> Disj (oeq m 1)(oeq m p) *)
    val faThm = prime2_div_r pT hPrime                  (* Forall (ppAbs p) *)
    val faM   = allE_r (ppAbs pT) mT faThm              (* Imp (dvd m p)(Disj (oeq m 1)(oeq m p)) *)
    val disj  = mp_r (dvd mT pT, mkDisj (oeq mT (suc ZeroC))(oeq mT pT)) faM dvdmp
    val goalC = oFalseC
    val caseM1 =
      let val hm1 = Thm.assume (ctermGR (jT (oeq mT (suc ZeroC))))   (* m = 1 *)
          (* lt 1 m, rewrite m->1 : lt 1 1 -> irrefl *)
          val Plt = Term.lambda (Free("zm1",natT)) (lt (suc ZeroC)(Free("zm1",natT)))
          val lt11 = oeq_rw_r (Plt, mT, suc ZeroC) hm1 hlt1m         (* lt 1 1 *)
          val fls = lt_irrefl_r (suc ZeroC) lt11
      in Thm.implies_intr (ctermGR (jT (oeq mT (suc ZeroC)))) fls end
    val caseMp =
      let val hmp = Thm.assume (ctermGR (jT (oeq mT pT)))            (* m = p *)
          (* lt m p, rewrite m->p : lt p p -> irrefl *)
          val Plt = Term.lambda (Free("zmp",natT)) (lt (Free("zmp",natT)) pT)
          val ltpp = oeq_rw_r (Plt, mT, pT) hmp hltmp                (* lt p p *)
          val fls = lt_irrefl_r pT ltpp
      in Thm.implies_intr (ctermGR (jT (oeq mT pT))) fls end
  in disjE_r (oeq mT (suc ZeroC), oeq mT pT, goalC) disj caseM1 caseMp end;
val () = out "SEAT3_DIVIDES_ALL_FALSE_DEFINED\n";

(* 0-hyp discharged step (b) lemma *)
val r0_excl_thm =
  let
    val pF=Free("p_r0",natT); val mF=Free("m_r0",natT)
    val aF=Free("a_r0",natT); val bF=Free("b_r0",natT); val cF=Free("c_r0",natT); val dF=Free("d_r0",natT)
    val hPrP=jT(prime2 pF); val hPr=Thm.assume(ctermGR hPrP)
    val h1P=jT(lt (suc ZeroC) mF); val h1=Thm.assume(ctermGR h1P)
    val hmpP=jT(lt mF pF); val hmp=Thm.assume(ctermGR hmpP)
    val daP=jT(dvd mF aF); val da=Thm.assume(ctermGR daP)
    val dbP=jT(dvd mF bF); val db=Thm.assume(ctermGR dbP)
    val dcP=jT(dvd mF cF); val dc=Thm.assume(ctermGR dcP)
    val ddP=jT(dvd mF dF); val dd=Thm.assume(ctermGR ddP)
    val hbP=jT(oeq (mult mF pF)(add (add (mult aF aF)(mult bF bF))(add (mult cF cF)(mult dF dF))))
    val hb=Thm.assume(ctermGR hbP)
    val r = divides_all_imp_false (pF,mF,aF,bF,cF,dF) hPr h1 hmp da db dc dd hb
  in Thm.implies_intr (ctermGR hPrP)(Thm.implies_intr (ctermGR h1P)(Thm.implies_intr (ctermGR hmpP)
       (Thm.implies_intr (ctermGR daP)(Thm.implies_intr (ctermGR dbP)(Thm.implies_intr (ctermGR dcP)
         (Thm.implies_intr (ctermGR ddP)(Thm.implies_intr (ctermGR hbP) r))))))) end;
val () = out ("r0_excl hyps="^Int.toString(length(Thm.hyps_of r0_excl_thm))^"\n");
val () = out ("r0_excl prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of r0_excl_thm)^"\n");
val r0_0hyp = (length (Thm.hyps_of r0_excl_thm) = 0);
(* aconv against intended *)
val r0_excl_intended =
  let
    val pF=Free("p_r0",natT); val mF=Free("m_r0",natT)
    val aF=Free("a_r0",natT); val bF=Free("b_r0",natT); val cF=Free("c_r0",natT); val dF=Free("d_r0",natT)
    val body = oeq (mult mF pF)(add (add (mult aF aF)(mult bF bF))(add (mult cF cF)(mult dF dF)))
  in Logic.mk_implies (jT (prime2 pF),
       Logic.mk_implies (jT (lt (suc ZeroC) mF),
         Logic.mk_implies (jT (lt mF pF),
           Logic.mk_implies (jT (dvd mF aF),
             Logic.mk_implies (jT (dvd mF bF),
               Logic.mk_implies (jT (dvd mF cF),
                 Logic.mk_implies (jT (dvd mF dF),
                   Logic.mk_implies (jT body, jT oFalseC)))))))) end;
val r0_aconv = ((Thm.prop_of r0_excl_thm) aconv r0_excl_intended);
(* SOUNDNESS PROBE (b): genuinely uses primality -- dropping prime2 p makes it
   non-aconv (the unconditional "m|a,b,c,d /\ m*p=sum ==> False" is FALSE, e.g.
   m=2,p=2 with a=b=c=d gives a sum-of-4-squares multiple of 4 with 2|all). *)
val r0_probe_cond = not ((Thm.prop_of r0_excl_thm) aconv
  (let
    val pF=Free("p_r0",natT); val mF=Free("m_r0",natT)
    val aF=Free("a_r0",natT); val bF=Free("b_r0",natT); val cF=Free("c_r0",natT); val dF=Free("d_r0",natT)
    val body = oeq (mult mF pF)(add (add (mult aF aF)(mult bF bF))(add (mult cF cF)(mult dF dF)))
   in Logic.mk_implies (jT (lt (suc ZeroC) mF),
        Logic.mk_implies (jT (lt mF pF),
          Logic.mk_implies (jT (dvd mF aF),
            Logic.mk_implies (jT (dvd mF bF),
              Logic.mk_implies (jT (dvd mF cF),
                Logic.mk_implies (jT (dvd mF dF),
                  Logic.mk_implies (jT body, jT oFalseC))))))) end));
val () = out ("SEAT3_STEP_B_VALIDATE aconv="^Bool.toString r0_aconv^" zero_hyp="^Bool.toString r0_0hyp
              ^" probe_cond="^Bool.toString r0_probe_cond^"\n");
val () = if r0_0hyp andalso r0_aconv andalso r0_probe_cond then out "SEAT3_STEP_B_OK\n" else out "SEAT3_STEP_B_FAILED\n";

(* ============================================================================
   SEAT 3 SUMMARY (lemma-factored route).
   Banked this run (each 0-hyp, aconv-checked where applicable):
     (a) signed_four_residue_sum_thm  -- the SIGNED m*r decomposition carrying the
         per-coordinate (cong m x' x OR cong m (x'+x) 0) disjuncts + 2x'<=m bounds.
         THE keystone-dependent piece the resume material lacked.
     (b) r0_excl_thm  -- divides_all_imp_false : prime2 p, 1<m<p, m|a,b,c,d,
         m*p = a^2+..+d^2 ==> oFalse.  The r=0 exclusion (uses the SIGNED relation
         via signed_zero_imp_dvd).
     reusable GR helpers: sqcong_of_signed, signed_zero_imp_dvd, dvd_sq,
       mult_eq_zero_GR, mult_left_cancel_GR + the dvd _r toolkit.
   NOT attempted this run (the expensive / fiddly remainder, scoped for a follow-up):
     (c) r<m  (the r=m / m-even sub-case is the documented fiddly step), and
     (d) the Euler divide-by-m^2 (ONE proveStarFor, ~13 min) + the full
         descent_step composition.
   ============================================================================ *)
val () = out ("SEAT3_FINAL signed_frs_0hyp="^Bool.toString sfrs_0hyp
              ^" signed_frs_aconv="^Bool.toString sfrs_aconv
              ^" r0_excl_0hyp="^Bool.toString r0_0hyp^"\n");
val () = out "SEAT3_SMOKE_ALL_DONE\n";
