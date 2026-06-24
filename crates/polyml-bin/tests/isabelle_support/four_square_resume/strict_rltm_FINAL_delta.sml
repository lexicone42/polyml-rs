(* ============================================================================
   DESCENT — STRICT r<m (the r=m exclusion), FULL.
   Builds descent_strict : prime2 p ==> 1<m ==> m<p ==> four_sq(m*p)
                             ==> EX r. (0<r) AND (r<m) AND four_sq(m*r).
   Re-runs descent_residue's SETUP internals (elim_four_sq + signed_four_residue_sum
   + elim_signed_sum) so the per-coordinate sign-disjuncts + bounds are in scope,
   then EXCLUDES r=m (tightness -> FACT R -> per-coord cong(m^2)(a^2)(x'^2) ->
   dvd m^2 (m*p) -> dvd m p -> m_dvd_p_contra), upgrading r<=m to r<m.
   Run on /tmp/l4_foursq_star (warm checkpoint with seat1 internals live).
   ============================================================================ *)
val () = restore_l4_context ();
val () = out "STRICT_BEGIN\n";
fun sq x = mult x x;
fun dbl t = add t t;
fun quad X = add X (add X (add X X));

(* ============================ order/tightness glue ============================ *)
val le_eq_or_lt_vGR = varify le_eq_or_lt;
fun le_eq_or_lt_d (aT,bT) hle =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("a",0), ctermGR aT),(("b",0), ctermGR bT)] le_eq_or_lt_vGR)) hle;
fun lt_imp_0lt_r2 (aT,bT) hlt =
  let val aS = addSuc_d (ZeroC, aT)
      val z0 = Suc_cong OF [add0_d aT]
      val chain = oeqTrans_r2 (aS, z0)
      val le1Sa = le_intro_d (suc ZeroC, suc aT, aT) (oeqSym_r2 chain)
  in le_trans_d (suc ZeroC, suc aT, bT) le1Sa hlt end;
fun sq_strict_mono (aT,bT) hlt =
  let val h0b  = lt_imp_0lt_r2 (aT,bT) hlt
      val leab = lt_imp_le_r (aT,bT) hlt
      val laa_ab = mult_le_mono_g (aT, aT, bT) leab
      val comm = multcomm_g (aT, bT)
      val laa_ba = oeq_rw_r (Term.lambda (Free("zssm",natT)) (le (mult aT aT) (Free("zssm",natT))), mult aT bT, mult bT aT) comm laa_ab
      val lba_bb = mult_lt_mono_l bT h0b (aT,bT) hlt
  in le_lt_trans (mult aT aT, mult bT aT, mult bT bT) laa_ba lba_bb end;
fun sq_eq_imp_eq (aT,bT) hsq =
  let val goalC = oeq aT bT
      val tot = le_total_d (aT, bT)
      val caseAB =
        let val hP = jT (le aT bT); val h = Thm.assume (ctermGR hP)
            val djlt = le_eq_or_lt_d (aT,bT) h
            val sub = disjE_r (oeq aT bT, lt aT bT, goalC) djlt
                (let val hQ=jT (oeq aT bT); val q=Thm.assume (ctermGR hQ) in Thm.implies_intr (ctermGR hQ) q end)
                (let val hQ=jT (lt aT bT); val q=Thm.assume (ctermGR hQ)
                     val ltsq = sq_strict_mono (aT,bT) q
                     val ltbb = oeq_rw_r (Term.lambda (Free("zse",natT)) (lt (Free("zse",natT)) (mult bT bT)), mult aT aT, mult bT bT) hsq ltsq
                     val fls = lt_irrefl_r (mult bT bT) ltbb
                 in Thm.implies_intr (ctermGR hQ) (Thm.implies_elim (oFalse_elim_r goalC) fls) end)
        in Thm.implies_intr (ctermGR hP) sub end
      val caseBA =
        let val hP = jT (le bT aT); val h = Thm.assume (ctermGR hP)
            val djlt = le_eq_or_lt_d (bT,aT) h
            val sub = disjE_r (oeq bT aT, lt bT aT, goalC) djlt
                (let val hQ=jT (oeq bT aT); val q=Thm.assume (ctermGR hQ) in Thm.implies_intr (ctermGR hQ) (oeqSym_r2 q) end)
                (let val hQ=jT (lt bT aT); val q=Thm.assume (ctermGR hQ)
                     val ltsq = sq_strict_mono (bT,aT) q
                     val hsqS = oeqSym_r2 hsq
                     val ltaa = oeq_rw_r (Term.lambda (Free("zse2",natT)) (lt (Free("zse2",natT)) (mult aT aT)), mult bT bT, mult aT aT) hsqS ltsq
                     val fls = lt_irrefl_r (mult aT aT) ltaa
                 in Thm.implies_intr (ctermGR hQ) (Thm.implies_elim (oFalse_elim_r goalC) fls) end)
        in Thm.implies_intr (ctermGR hP) sub end
  in disjE_r (le aT bT, le bT aT, goalC) tot caseAB caseBA end;

(* le_radd_cancel2 via le_witness (base le_radd_cancel has an orientation bug on complex z) *)
val add_left_cancel_vGR = varify add_left_cancel;
fun add_left_cancel_d (mT,aT,bT) heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("m",0), ctermGR mT),(("a",0), ctermGR aT),(("b",0), ctermGR bT)] add_left_cancel_vGR)) heq;
fun add_right_cancel_d (aT,bT,cT) heq =
  let val ca = addcomm_d (aT, cT); val cb = addcomm_d (bT, cT)
      val e1 = oeqTrans_r2 (oeqSym_r2 ca, oeqTrans_r2 (heq, cb))
  in add_left_cancel_d (cT, aT, bT) e1 end;
fun le_radd_cancel2 (aT,bT,cT) hle =
  let val goalC = le aT bT
      fun bd w (hw:thm) =
        let val s1 = addassoc_d (aT, cT, w)
            val s2 = add_cong_r_d (aT, add cT w, add w cT) (addcomm_d (cT, w))
            val s3 = oeqSym_r2 (addassoc_d (aT, w, cT))
            val chain = oeqTrans_r2 (s1, oeqTrans_r2 (s2, s3))
            val bc_eq = oeqTrans_r2 (hw, chain)
            val b_eq = add_right_cancel_d (bT, add aT w, cT) bc_eq
        in le_intro_d (aT, bT, w) b_eq end
  in le_witness (add aT cT, add bT cT, goalC) hle bd end;
fun tightA (A,B,C,D,M2) hA hB hC hD hsum =
  let val rl1 = addassoc_d (A, B, add C D)
      val sumA = oeqTrans_r2 (oeqSym_r2 rl1, hsum)
      val lcd = add_le_mono (C, M2, D, M2) hC hD
      val lcomp = add_le_mono (B, M2, add C D, add M2 M2) hB lcd
      val l_A_comp = add_le_mono (A, A, add B (add C D), add M2 (add M2 M2)) (oeq_imp_le_r (A,A) (oeqRefl_r2 A)) lcomp
      val l_quad_A3 = oeq_rw_r (Term.lambda (Free("ztq",natT)) (le (Free("ztq",natT)) (add A (add M2 (add M2 M2)))),
                                add A (add B (add C D)), quad M2) sumA l_A_comp
      val Xc = add M2 (add M2 M2)
      val leM2A = le_radd_cancel2 (M2, A, Xc) l_quad_A3
  in le_antisym_r (A, M2) hA leM2A end;
fun quad_cong (U,V) hUV =
  oeq_rw_r (Term.lambda (Free("zqc",natT)) (oeq (quad U)(quad (Free("zqc",natT)))), U, V) hUV (oeqRefl_r2 (quad U));
fun tightOne (twoX, A',B',C',D', mT) hA' hB' hC' hD' hsumQ =
  let val M2 = mult mT mT
      val eqA = tightA (A',B',C',D',M2) hA' hB' hC' hD' hsumQ
  in sq_eq_imp_eq (twoX, mT) eqA end;
fun perm_BACD (A,B,C,D) = add_cong_l_d (add A B, add B A, add C D) (addcomm_d (A,B));
fun perm_CDAB (A,B,C,D) = addcomm_d (add A B, add C D);
fun perm_DCAB (A,B,C,D) =
  let val s1 = addcomm_d (add A B, add C D)
      val s2 = add_cong_l_d (add C D, add D C, add A B) (addcomm_d (C,D))
  in oeqTrans_r2 (s1, s2) end;
(* tightAll : 4 bounds le(2x'_i)m, hsum: oeq sumLHS (m*r), hr_m: oeq r m -> (te_a..te_d) oeq (2x'_i) m.
   ONE proveIdentityG (the quad) + cheap addcomm reorders. *)
fun tightAll (rT, ap,bp,cp,dp,mT) hba hbb hbc hbd hsum hr_m =
  let
    val M2 = mult mT mT
    val sumLHS = add (add (sq ap)(sq bp)) (add (sq cp)(sq dp))
    val s_mm = oeqTrans_r2 (hsum, mult_cong_r_d (mT, rT, mT) hr_m)
    val qcong = quad_cong (sumLHS, M2) s_mm
    val A = sq (dbl ap); val B = sq (dbl bp); val C = sq (dbl cp); val D = sq (dbl dp)
    val lA = sq_le (dbl ap, mT) hba; val lB = sq_le (dbl bp, mT) hbb
    val lC = sq_le (dbl cp, mT) hbc; val lD = sq_le (dbl dp, mT) hbd
    val LHS4 = add (add A B)(add C D)
    val idQ = proveIdentityG LHS4 (quad sumLHS)
    val hsum4 = oeqTrans_r2 (idQ, qcong)
    val te_a = tightOne (dbl ap, A,B,C,D, mT) lA lB lC lD hsum4
    val hsumB = oeqTrans_r2 (oeqSym_r2 (perm_BACD (A,B,C,D)), hsum4)
    val te_b = tightOne (dbl bp, B,A,C,D, mT) lB lA lC lD hsumB
    val hsumC = oeqTrans_r2 (oeqSym_r2 (perm_CDAB (A,B,C,D)), hsum4)
    val te_c = tightOne (dbl cp, C,D,A,B, mT) lC lD lA lB hsumC
    val hsumD = oeqTrans_r2 (oeqSym_r2 (perm_DCAB (A,B,C,D)), hsum4)
    val te_d = tightOne (dbl dp, D,C,A,B, mT) lD lC lA lB hsumD
  in (te_a, te_b, te_c, te_d) end;
val () = out "STRICT_TIGHTALL_OK\n";

(* ============================ FACT R + per-coord cong ============================ *)
fun cong_of_oeq_M (MT, X, Y) hXY =
  let val m0  = mult0r_d MT
      val yp0 = oeqTrans_r2 (add_cong_r_d (Y, mult MT ZeroC, ZeroC) m0, add0r_d Y)
      val hXp = oeqTrans_r2 (hXY, oeqSym_r2 yp0)
  in cong_introR_r (MT, X, Y, ZeroC) hXp end;
fun cong_M_mult_zero (MT, kT) =
  let val z = add0_d (mult MT kT) in cong_introR_r (MT, mult MT kT, ZeroC, kT) (oeqSym_r2 z) end;
(* mult1r_dGR : oeq (m * 1) m   via multSucr_d (m,0) : m*(Suc 0) = m + m*0, then m*0=0, m+0=m *)
fun mult1r_dGR mT =
  let val ms = multSucr_d (mT, ZeroC)          (* m*(Suc 0) = m + m*0 *)
      val m0 = mult0r_d mT                       (* m*0 = 0 *)
      val mp0 = oeqTrans_r2 (add_cong_r_d (mT, mult mT ZeroC, ZeroC) m0, add0r_d mT)  (* m + m*0 = m *)
  in oeqTrans_r2 (ms, mp0) end;                  (* m*(Suc 0) = m *)

(* factR (m,a,x') hsign te : cong m (a+x') 0   from signD(m,x',a) + te:oeq(x'+x')m *)
fun factR (mT, aT, xpT) hsign te =
  let
    val goalC = cong mT (add aT xpT) ZeroC
    val cMM0 = (let val one = suc ZeroC
                    val m1 = mult1r_dGR mT                    (* m*1 = m *)
                    val zm1 = oeqTrans_r2 (add0_d (mult mT one), m1)  (* 0 + m*1 = m *)
                in cong_introR_r (mT, mT, ZeroC, one) (oeqSym_r2 zm1) end)  (* cong m m 0 *)
    val caseL =
      let val hP = jT (cong mT xpT aT); val h = Thm.assume (ctermGR hP)
          val cax = cong_sym_g (mT, xpT, aT) h                  (* cong m a x' *)
          val cadd = cong_add_g (mT, aT, xpT, xpT, xpT) cax (cong_refl_g (mT, xpT))  (* cong m (a+x')(x'+x') *)
          (* (x'+x') = m [te] -> cong m (a+x') m *)
          val caddm = oeq_rw_r (Term.lambda (Free("zfl",natT)) (cong mT (add aT xpT) (Free("zfl",natT))), add xpT xpT, mT) te cadd
          val res = cong_trans_g (mT, add aT xpT, mT, ZeroC) caddm cMM0   (* cong m (a+x') 0 *)
      in Thm.implies_intr (ctermGR hP) res end
    val caseR =
      let val hP = jT (cong mT (add xpT aT) ZeroC); val h = Thm.assume (ctermGR hP)
          val comm = addcomm_g (xpT, aT)                        (* x'+a = a+x' *)
          val res = oeq_rw_r (Term.lambda (Free("zfr",natT)) (cong mT (Free("zfr",natT)) ZeroC), add xpT aT, add aT xpT) comm h
      in Thm.implies_intr (ctermGR hP) res end
  in disjE_r (cong mT xpT aT, cong mT (add xpT aT) ZeroC, goalC) hsign caseL caseR end;
val () = out "STRICT_FACTR_OK\n";

fun coord_cong_msq (mT, aT, xpT, vT) hfactR te =
  let
    val M2 = mult mT mT
    val sqV = sq vT; val mv = mult mT vT
    val xa = mult xpT aT; val xx = mult xpT xpT
    val e1 = multassoc_g (mT, mT, vT)
    val e2 = mult_cong_r_g (mT, mv, add aT xpT) (oeqSym_r2 hfactR)
    val e3 = leftdistrib_g (mT, aT, xpT)
    val teS = oeqSym_r2 te
    val ma1 = mult_cong_l_g (mT, add xpT xpT, aT) teS
    val ma2 = rightdistrib_g (xpT, xpT, aT)
    val ma  = oeqTrans_r2 (ma1, ma2)
    val mx1 = mult_cong_l_g (mT, add xpT xpT, xpT) teS
    val mx2 = rightdistrib_g (xpT, xpT, xpT)
    val mx  = oeqTrans_r2 (mx1, mx2)
    val e4 = oeqTrans_r2 (e3, oeqTrans_r2 (add_cong_l_d (mult mT aT, add xa xa, mult mT xpT) ma,
                                           add_cong_r_d (add xa xa, mult mT xpT, add xx xx) mx))
    val m2v_eq = oeqTrans_r2 (e1, oeqTrans_r2 (e2, e4))
    val d1 = leftdistrib_g (add aT xpT, aT, xpT)
    val d2 = rightdistrib_g (aT, xpT, aT)
    val d3 = rightdistrib_g (aT, xpT, xpT)
    val L_aa_xa = add (mult aT aT)(mult xpT aT)
    val L_ax_xx = add (mult aT xpT)(mult xpT xpT)
    val cL = add_cong_l_d (mult (add aT xpT) aT, L_aa_xa, mult (add aT xpT) xpT) d2
    val cR = add_cong_r_d (L_aa_xa, mult (add aT xpT) xpT, L_ax_xx) d3
    val expand = oeqTrans_r2 (d1, oeqTrans_r2 (cL, cR))
    val c1 = mult_cong_l_g (add aT xpT, mv, add aT xpT) hfactR
    val c2 = mult_cong_r_g (mv, add aT xpT, mv) hfactR
    val sqFR = oeqTrans_r2 (c1, c2)
    val aa1 = multassoc_g (mT, vT, mv)
    val aa2 = mult_cong_r_g (mT, mult vT mv, mult (mult vT mT) vT) (oeqSym_r2 (multassoc_g (vT, mT, vT)))
    val aa3 = mult_cong_r_g (mT, mult (mult vT mT) vT, mult (mult mT vT) vT)
               (mult_cong_l_g (mult vT mT, mult mT vT, vT) (multcomm_g (vT, mT)))
    val aa4 = mult_cong_r_g (mT, mult (mult mT vT) vT, mult mT (mult vT vT)) (multassoc_g (mT, vT, vT))
    val aa5 = oeqSym_r2 (multassoc_g (mT, mT, mult vT vT))
    val mvSq = oeqTrans_r2 (aa1, oeqTrans_r2 (aa2, oeqTrans_r2 (aa3, oeqTrans_r2 (aa4, aa5))))
    val sqFR2 = oeqTrans_r2 (sqFR, mvSq)
    val m2v2_eq = oeqSym_r2 sqFR2
    val P = mult aT aT; val Q = mult xpT aT; val R = mult aT xpT; val S = mult xpT xpT
    val niLHS = add P (mult M2 vT)
    val LHS_exp = add P (add (add Q Q)(add S S))
    val lhs_eq = add_cong_r_d (P, mult M2 vT, add (add Q Q)(add S S)) m2v_eq
    val niRHS = add (mult M2 sqV) S
    val rhs1 = add_cong_l_d (mult M2 sqV, sq (add aT xpT), S) m2v2_eq
    val rhs2 = add_cong_l_d (sq (add aT xpT), add (add P Q)(add R S), S) expand
    val rhs_eq = oeqTrans_r2 (rhs1, rhs2)
    val RtoQ = multcomm_g (aT, xpT)
    val RHS_exp0 = add (add (add P Q)(add R S)) S
    val RHS_exp  = add (add (add P Q)(add Q S)) S
    val rhs_RQ = oeq_rw_r (Term.lambda (Free("zrq",natT)) (oeq RHS_exp0 (add (add (add P Q)(add (Free("zrq",natT)) S)) S)), R, Q) RtoQ (oeqRefl_r2 RHS_exp0)
    val rhs_eq2 = oeqTrans_r2 (rhs_eq, rhs_RQ)
    val addId = proveAddIdentity noLeaf LHS_exp RHS_exp
    val niEq = oeqTrans_r2 (lhs_eq, oeqTrans_r2 (addId, oeqSym_r2 rhs_eq2))
    val cMv0 = cong_M_mult_zero (M2, vT)
    val cLref = cong_refl_g (M2, P)
    val cLadd = cong_add_g (M2, P, P, mult M2 vT, ZeroC) cLref cMv0
    val a2p0 = add0r_d P
    val cL_a2 = cong_trans_g (M2, niLHS, add P ZeroC, P) cLadd (cong_of_oeq_M (M2, add P ZeroC, P) a2p0)
    val cMv2_0 = cong_M_mult_zero (M2, sqV)
    val cRref = cong_refl_g (M2, S)
    val cRadd = cong_add_g (M2, mult M2 sqV, ZeroC, S, S) cMv2_0 cRref
    val z0s = add0_d S
    val cR_x2 = cong_trans_g (M2, niRHS, add ZeroC S, S) cRadd (cong_of_oeq_M (M2, add ZeroC S, S) z0s)
    val cNi = cong_of_oeq_M (M2, niLHS, niRHS) niEq
    val s1 = cong_sym_g (M2, niLHS, P) cL_a2
    val s2 = cong_trans_g (M2, P, niLHS, niRHS) s1 cNi
    val res = cong_trans_g (M2, P, niRHS, S) s2 cR_x2
  in res end;
val () = out "STRICT_COORD_OK\n";

(* per-coord wrapper: from signD + tightness, eliminate v (FACT R existential), produce cong M2 (a^2)(x'^2).
   vname must be DISTINCT per coordinate (the exE eigenvariable must not collide across nesting). *)
fun coord_msq_from_sign vname (mT, aT, xpT) hsign te goalC k =
  let
    val cFR0 = factR (mT, aT, xpT) hsign te          (* cong m (a+x') 0 *)
    val exV  = cong_zero_imp_mult (mT, add aT xpT) cFR0   (* EX v. (a+x') = m*v *)
    val Pv = Term.lambda (Free(vname, natT)) (oeq (add aT xpT) (mult mT (Free(vname,natT))))
    fun bd v (hv:thm) = k (coord_cong_msq (mT, aT, xpT, v) hv te)
  in exE_r (Pv, goalC) exV vname natT bd end;
val () = out "STRICT_COORDWRAP_OK\n";

(* smoke factR *)
val () =
  let val mF=Free("m_f",natT); val aF=Free("a_f",natT); val xpF=Free("xp_f",natT)
      val hsign = Thm.assume (ctermGR (jT (mkDisj (cong mF xpF aF)(cong mF (add xpF aF) ZeroC))))
      val te = Thm.assume (ctermGR (jT (oeq (add xpF xpF) mF)))
      val r = factR (mF,aF,xpF) hsign te
  in out ("SMOKE factR prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)^" hyps="^Int.toString(length(Thm.hyps_of r))^"\n") end
  handle e => out ("SMOKE factR FAIL "^exnMessage e^"\n");

(* smoke coord_msq_from_sign *)
val () =
  let val mF=Free("m_c",natT); val aF=Free("a_c",natT); val xpF=Free("xp_c",natT)
      val hsign = Thm.assume (ctermGR (jT (mkDisj (cong mF xpF aF)(cong mF (add xpF aF) ZeroC))))
      val te = Thm.assume (ctermGR (jT (oeq (add xpF xpF) mF)))
      val rThm = coord_msq_from_sign "vsm" (mF,aF,xpF) hsign te (oeq (mult mF mF)(mult mF mF)) (fn cc =>
                 (out ("SMOKE coord_msq cong="^Syntax.string_of_term ctxtGR (Thm.prop_of cc)^" hyps="^Int.toString(length(Thm.hyps_of cc))^"\n");
                  oeqRefl_r2 (mult mF mF)))
  in out ("SMOKE coord_msq_from_sign returned hyps="^Int.toString(length(Thm.hyps_of rThm))^"\n") end
  handle e => out ("SMOKE coord_msq FAIL "^exnMessage e^"\n");

val () = out "STRICT_PHASE1_DONE\n";

(* ============================ rm_excl : r=m -> oFalse ============================
   Inputs (all ctxtGR):
     mT,pT,rT, a,b,c,d (orig coords), ap,bp,cp,dp (residue witnesses)
     hsum   : oeq (ap^2+bp^2+cp^2+dp^2) (m*r)   [sumLHS shape ((ap^2+bp^2)+(cp^2+dp^2))]
     hsa..hsd : signD m ap a , ...               [Disj (cong m ap a)(cong m (ap+a) 0)]
     hba..hbd : le (2x'_i) m
     hbodyP : oeq (m*p) ((a^2+b^2)+(c^2+d^2))
     hPrime : prime2 p ; h1m : lt 1 m ; hmp : lt m p ; hmPos : lt 0 m ; hr_m : oeq r m
   ================================================================================ *)
fun rm_excl (mT,pT,rT, a,b,c,d, ap,bp,cp,dp)
            hsum hsa hsb hsc hsd hba hbb hbc hbd hbodyP hPrime h1m hmp hmPos hr_m =
  let
    val M2 = mult mT mT
    val goalC = oFalseC
    (* tightness for all 4 *)
    val (te_a, te_b, te_c, te_d) = tightAll (rT, ap,bp,cp,dp, mT) hba hbb hbc hbd hsum hr_m
    val () = out "STRICT_RM_TIGHT_OK\n"
    (* nested per-coord cong M2 (x^2)(x'^2), then assemble *)
  in
    coord_msq_from_sign "vca" (mT, a, ap) hsa te_a goalC (fn ca =>
    coord_msq_from_sign "vcb" (mT, b, bp) hsb te_b goalC (fn cb =>
    coord_msq_from_sign "vcc" (mT, c, cp) hsc te_c goalC (fn cc =>
    coord_msq_from_sign "vcd" (mT, d, dp) hsd te_d goalC (fn cd =>
      let
        (* ca : cong M2 (a^2)(ap^2), ... *)
        val cab = cong_add_g (M2, sq a, sq ap, sq b, sq bp) ca cb   (* cong M2 (a^2+b^2)(ap^2+bp^2) *)
        val ccd = cong_add_g (M2, sq c, sq cp, sq d, sq dp) cc cd   (* cong M2 (c^2+d^2)(cp^2+dp^2) *)
        val bodyA = add (add (sq a)(sq b))(add (sq c)(sq d))        (* (a^2+b^2)+(c^2+d^2) *)
        val bodyAp= add (add (sq ap)(sq bp))(add (sq cp)(sq dp))    (* sumLHS *)
        val csum = cong_add_g (M2, add (sq a)(sq b), add (sq ap)(sq bp), add (sq c)(sq d), add (sq cp)(sq dp)) cab ccd
                   (* cong M2 bodyA bodyAp *)
        (* bodyA = m*p [hbodyP sym] ; bodyAp = m*r [hsum] = m*m [r=m] *)
        val c1 = oeq_rw_r (Term.lambda (Free("zb1",natT)) (cong M2 (Free("zb1",natT)) bodyAp), bodyA, mult mT pT)
                   (oeqSym_r2 hbodyP) csum    (* cong M2 (m*p) bodyAp *)
        (* bodyAp = m*r = m*m *)
        val ap_mr = hsum                                    (* bodyAp = m*r *)
        val mr_mm = mult_cong_r_d (mT, rT, mT) hr_m         (* m*r = m*m *)
        val ap_mm = oeqTrans_r2 (ap_mr, mr_mm)              (* bodyAp = m*m *)
        val c2 = oeq_rw_r (Term.lambda (Free("zb2",natT)) (cong M2 (mult mT pT) (Free("zb2",natT))), bodyAp, M2)
                   ap_mm c1    (* cong M2 (m*p) (m*m) *)
        (* cong M2 (m*m) 0 : m*m = M2*1 ; use cong_M_mult_zero (M2,1) + rewrite M2*1 -> m*m *)
        val cMM0 = (let val one = suc ZeroC
                        val m21 = mult1r_dGR M2          (* (m*m)*1 = (m*m) *)
                        val z = oeqTrans_r2 (add0_d (mult M2 one), m21)   (* 0 + (m*m)*1 = (m*m) *)
                    in cong_introR_r (M2, M2, ZeroC, one) (oeqSym_r2 z) end)   (* cong M2 (m*m) 0 *)
        val c_mp_0 = cong_trans_g (M2, mult mT pT, M2, ZeroC) c2 cMM0   (* cong M2 (m*p) 0 *)
        val () = out "STRICT_RM_CONGMP0_OK\n"
        (* dvd M2 (m*p) -> dvd m p -> contra *)
        val exMP = cong_zero_imp_mult (M2, mult mT pT) c_mp_0   (* EX k. m*p = M2*k = dvd M2 (m*p) *)
        val dvdMP = dvd_msq_cancel mT hmPos pT exMP            (* dvd m p *)
        val () = out "STRICT_RM_DVDMP_OK\n"
        val fls = m_dvd_p_contra (mT, pT) dvdMP hPrime h1m hmp  (* oFalse *)
      in fls end))))
  end;
val () = out "STRICT_RM_EXCL_DEFINED\n";

(* smoke rm_excl : assume all hyps, build oFalse *)
val () =
  let
    val mF=Free("mE",natT); val pF=Free("pE",natT); val rF=Free("rE",natT)
    val aF=Free("aE",natT); val bF=Free("bE",natT); val cF=Free("cE",natT); val dF=Free("dE",natT)
    val apF=Free("apE",natT); val bpF=Free("bpE",natT); val cpF=Free("cpE",natT); val dpF=Free("dpE",natT)
    val sumLHS = add (add (sq apF)(sq bpF)) (add (sq cpF)(sq dpF))
    val hsum = Thm.assume (ctermGR (jT (oeq sumLHS (mult mF rF))))
    val hsa = Thm.assume (ctermGR (jT (mkDisj (cong mF apF aF)(cong mF (add apF aF) ZeroC))))
    val hsb = Thm.assume (ctermGR (jT (mkDisj (cong mF bpF bF)(cong mF (add bpF bF) ZeroC))))
    val hsc = Thm.assume (ctermGR (jT (mkDisj (cong mF cpF cF)(cong mF (add cpF cF) ZeroC))))
    val hsd = Thm.assume (ctermGR (jT (mkDisj (cong mF dpF dF)(cong mF (add dpF dF) ZeroC))))
    val hba = Thm.assume (ctermGR (jT (le (add apF apF) mF)))
    val hbb = Thm.assume (ctermGR (jT (le (add bpF bpF) mF)))
    val hbc = Thm.assume (ctermGR (jT (le (add cpF cpF) mF)))
    val hbd = Thm.assume (ctermGR (jT (le (add dpF dpF) mF)))
    val hbodyP = Thm.assume (ctermGR (jT (oeq (mult mF pF) (add (add (sq aF)(sq bF))(add (sq cF)(sq dF))))))
    val hPrime = Thm.assume (ctermGR (jT (prime2 pF)))
    val h1m = Thm.assume (ctermGR (jT (lt (suc ZeroC) mF)))
    val hmp = Thm.assume (ctermGR (jT (lt mF pF)))
    val hmPos = Thm.assume (ctermGR (jT (lt ZeroC mF)))
    val hr_m = Thm.assume (ctermGR (jT (oeq rF mF)))
    val r = rm_excl (mF,pF,rF, aF,bF,cF,dF, apF,bpF,cpF,dpF)
              hsum hsa hsb hsc hsd hba hbb hbc hbd hbodyP hPrime h1m hmp hmPos hr_m
  in out ("SMOKE rm_excl prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)
          ^" hyps="^Int.toString(length(Thm.hyps_of r))^"\n") end
  handle e => out ("SMOKE rm_excl FAIL "^exnMessage e^"\n");
val () = out "STRICT_PHASE2_DONE\n";

(* ============================================================================
   descent_strict : prime2 p ==> 1<m ==> m<p ==> four_sq (m*p)
       ==> EX r. (lt 0 r) AND (lt r m) AND four_sq (mult m r)
   = descent_residue with r<=m UPGRADED to STRICT r<m via rm_excl.
   ============================================================================ *)
val descent_strict =
  let
    val pF = Free("p_dr", natT); val mF = Free("m_dr", natT)
    val hPrP = jT (prime2 pF); val hPr = Thm.assume (ctermGR hPrP)
    val h1mP = jT (lt (suc ZeroC) mF); val h1m = Thm.assume (ctermGR h1mP)
    val hmpP = jT (lt mF pF); val hmp = Thm.assume (ctermGR hmpP)
    val hfsP = jT (four_sq (mult mF pF)); val hfs = Thm.assume (ctermGR hfsP)
    val le12 = lt_0_suc_r (suc ZeroC)
    val hmPos = le_trans_d (suc ZeroC, suc (suc ZeroC), mF) le12 h1m
    val rF0 = Free("r_dres", natT)
    val goalP = Term.lambda rF0 (mkConj (lt ZeroC rF0) (mkConj (lt rF0 mF) (four_sq (mult mF rF0))))
    val goalC = mkEx goalP
    val cmp0 = cong_mp_zero (mF, pF)
    val core =
      elim_four_sq "ds" hfs (mult mF pF) goalC (fn (a,b,c,d) => fn hbody =>
        let
          val ex = signed_four_residue_sum (mF, a, b, c, d, mult mF pF) hmPos hbody cmp0
        in elim_signed_sum (mF, a, b, c, d) ex goalC (fn (ap,bp,cp,dp,r) =>
             fn hsum => fn hsa => fn hsb => fn hsc => fn hsd => fn hba => fn hbb => fn hbc => fn hbd =>
             let
               val fsmr = four_sq_witness (mult mF r, ap, bp, cp, dp) (oeqSym_r2 hsum)
               (* 0<r *)
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
               (* STRICT r<m : r<=m -> (r=m OR r<m) ; r=m closes via rm_excl *)
               val djrm = le_eq_or_lt_d (r, mF) le_rm    (* Disj (oeq r m)(lt r m) *)
               val lt_rm =
                 disjE_r (oeq r mF, lt r mF, lt r mF) djrm
                   (let val hP=jT (oeq r mF); val h=Thm.assume (ctermGR hP)
                        val fls = rm_excl (mF,pF,r, a,b,c,d, ap,bp,cp,dp)
                                    hsum hsa hsb hsc hsd hba hbb hbc hbd hbody hPr h1m hmp hmPos h
                    in Thm.implies_intr (ctermGR hP) (Thm.implies_elim (oFalse_elim_r (lt r mF)) fls) end)
                   (let val hP=jT (lt r mF); val h=Thm.assume (ctermGR hP)
                    in Thm.implies_intr (ctermGR hP) h end)
               (* assemble : 0<r AND r<m AND four_sq(m*r) *)
               val conj = conjI_r (lt ZeroC r, mkConj (lt r mF)(four_sq (mult mF r))) pos_r
                            (conjI_r (lt r mF, four_sq (mult mF r)) lt_rm fsmr)
               val exr = exI_r goalP r conj
             in exr end)
        end)
  in Thm.implies_intr (ctermGR hPrP) (Thm.implies_intr (ctermGR h1mP)
       (Thm.implies_intr (ctermGR hmpP) (Thm.implies_intr (ctermGR hfsP) core))) end;
val () = out ("descent_strict hyps="^Int.toString(length(Thm.hyps_of descent_strict))^"\n");
val () = out ("descent_strict prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of descent_strict)^"\n");

(* ---- aconv against intended ---- *)
val descent_strict_intended =
  let
    val pV = Free("p_dr", natT); val mV = Free("m_dr", natT); val rV = Free("r_dres", natT)
    val concl = mkEx (Term.lambda rV
                  (mkConj (lt ZeroC rV) (mkConj (lt rV mV) (four_sq (mult mV rV)))))
  in Logic.mk_implies (jT (prime2 pV),
       Logic.mk_implies (jT (lt (suc ZeroC) mV),
         Logic.mk_implies (jT (lt mV pV),
           Logic.mk_implies (jT (four_sq (mult mV pV)), jT concl))))
  end;
val ds_aconv = ((Thm.prop_of descent_strict) aconv descent_strict_intended);
val ds_0hyp  = (length (Thm.hyps_of descent_strict) = 0);
val () = out ("STRICT_DS_VALIDATE aconv="^Bool.toString ds_aconv^" zero_hyp="^Bool.toString ds_0hyp^"\n");

(* SOUNDNESS PROBE 1 : drop four_sq(m*p) -> NOT aconv (genuinely needs the four-sq multiple) *)
val ds_probe_needs_fs =
  let
    val pV = Free("p_dr", natT); val mV = Free("m_dr", natT); val rV = Free("r_dres", natT)
    val concl = mkEx (Term.lambda rV (mkConj (lt ZeroC rV) (mkConj (lt rV mV) (four_sq (mult mV rV)))))
    val wrong = Logic.mk_implies (jT (prime2 pV),
                  Logic.mk_implies (jT (lt (suc ZeroC) mV),
                    Logic.mk_implies (jT (lt mV pV), jT concl)))
  in not ((Thm.prop_of descent_strict) aconv wrong) end;
val () = out ("STRICT_DS_PROBE_NEEDS_FS "^Bool.toString ds_probe_needs_fs^"\n");

(* SOUNDNESS PROBE 2 : the bound is STRICT lt r m, NOT the weak le r m (would be the un-strengthened residue) *)
val ds_probe_strict =
  let
    val pV = Free("p_dr", natT); val mV = Free("m_dr", natT); val rV = Free("r_dres", natT)
    val conclWeak = mkEx (Term.lambda rV (mkConj (lt ZeroC rV) (mkConj (le rV mV) (four_sq (mult mV rV)))))
    val wrong = Logic.mk_implies (jT (prime2 pV),
                  Logic.mk_implies (jT (lt (suc ZeroC) mV),
                    Logic.mk_implies (jT (lt mV pV),
                      Logic.mk_implies (jT (four_sq (mult mV pV)), jT conclWeak))))
  in not ((Thm.prop_of descent_strict) aconv wrong) end;
val () = out ("STRICT_DS_PROBE_STRICT "^Bool.toString ds_probe_strict^"\n");

(* SOUNDNESS PROBE 3 : conclusion genuinely asserts 0<r (not the trivial true) *)
val ds_probe_pos =
  let
    val pV = Free("p_dr", natT); val mV = Free("m_dr", natT); val rV = Free("r_dres", natT)
    val conclW = mkEx (Term.lambda rV (mkConj (lt rV mV) (four_sq (mult mV rV))))
    val wrong = Logic.mk_implies (jT (prime2 pV),
                  Logic.mk_implies (jT (lt (suc ZeroC) mV),
                    Logic.mk_implies (jT (lt mV pV),
                      Logic.mk_implies (jT (four_sq (mult mV pV)), jT conclW))))
  in not ((Thm.prop_of descent_strict) aconv wrong) end;
val () = out ("STRICT_DS_PROBE_POS "^Bool.toString ds_probe_pos^"\n");

val () = if ds_aconv andalso ds_0hyp andalso ds_probe_needs_fs andalso ds_probe_strict andalso ds_probe_pos
         then out "STRICT_DESCENT_STRICT_OK\n" else out "STRICT_DESCENT_STRICT_VALIDATE_FAILED\n";
val () = out "STRICT_ALL_DONE\n";

(* ============================================================================
   SUMMARY (verified 2026-06-23 on /tmp/l4_foursq_star, Tagged(0)):

   PROVED, 0-hyp, aconv-checked, 3 soundness probes, 0 add_axiom_global:
     descent_strict :
       prime2 p ==> 1<m ==> m<p ==> four_sq (m*p)
          ==> EX r. (lt 0 r) AND (lt r m) AND four_sq (mult m r)
   = the banked descent_residue (r<=m) with the bound UPGRADED to STRICT r<m.

   THE r=m EXCLUSION (rm_excl, the new piece), fully additive over N (NO truncated
   subtraction, NO m/2 literal, only ONE proveIdentityG = the tightness quad):
     - tightAll : from r=m + sum=m*r + bounds 2x'_i<=m, derive 2x'_i = m for all i
       (the AM-equality is TIGHT: sum (2x'_i)^2 = 4*sum x'^2 = 4*m^2 = quad(m^2) with
        each (2x'_i)^2 <= m^2 forces each (2x'_i)^2 = m^2, then sq_eq_imp_eq).
     - factR : 2x'_i=m + signD => cong m (a_i + x'_i) 0  (FACT R, both sign branches
       collapse since 2x'_i = m makes a_i = -x'_i = x'_i mod m).
     - coord_cong_msq : FACT R (a_i+x'_i = m*v_i) + tightness => cong (m*m)(a_i^2)(x'_i^2)
       via the N-identity  a^2 + (m*m)*v = (m*m)*v^2 + x'^2  (Ni'), built purely from
       distrib + addcomm + addassoc (proveAddIdentity on opaque atoms) — NO proveIdentityG.
       The cross term 2 a x' = m^2 v - 2 x'^2 is divisible by m^2, which is why the
       m | (sum a_i) snag of the naive square route is avoided.
     - assemble : sum the four cong(m^2)(a_i^2)(x'_i^2) => cong(m^2)(m*p)(m*m)
       => cong(m^2)(m*p) 0 => dvd m^2 (m*p) => dvd_msq_cancel => dvd m p
       => m_dvd_p_contra (1<m<p prime) => oFalse.   r=m NEVER occurs for prime p.

   Composes into the descent step: with the 16->8 disjE divide tree (divide_leaf_*),
   descent_strict gives the STRICT bound the strong-induction iteration needs.
   ============================================================================ *)
