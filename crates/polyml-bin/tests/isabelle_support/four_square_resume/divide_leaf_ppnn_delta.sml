(* ============================================================================
   FULL (PPNN) DIVIDE LEAF, end-to-end on /tmp/l4_foursq_star.  *** PROVEN ***
   (2026-06-23: DIVNN_SMOKE hyps=7, prop = four_sq (mult p r), Result Tagged(0),
    145,722,934,612 bytecode steps, ~19 min wall on the warm star checkpoint.)

   THE THIRD fully-proven divide leaf (after ++++ and PPPN).

   Pattern PPNN: a,b LEFT (cong m e a / f b), c,d RIGHT
                 (cong m (g+c) 0 / cong m (h+d) 0).

   The PPNN star (l4_build_8stars_v2.sml starL_3/starR_3) is the
   "one-component-dropped" shape: Pz = 0, so it has THREE cross-pairs
   (wP/wQ, Px/Qx, Py/Qy) PLUS a LONE square Qz (no Pz partner, no Qz cross
   term).  This is structurally distinct from ++++ (one lone w + 3 pairs)
   and PPPN (4 full pairs):  here the divide uses THREE sq_diff_dvd pairs +
   ONE direct cong-zero square (Qz).

   PPNN witnesses (true-signed = all-positive groupings, c,d are the negative
   coordinates so their residue products are folded into wQ / the Qx,Qy
   negative groups; verified offline /tmp/check_ppnn.py):
     wP = a*e + b*f          wQ = c*g + d*h
     Px = a*f + g*d          Qx = e*b + c*h
     Py = b*h + f*d          Qy = a*g + e*c
     Pz = 0                  Qz = ((a*h + e*d) + b*g) + f*c

   Residue reductions (e=a, f=b, g=-c, h=-d mod m):
     wP ≡ a^2+b^2 , wQ ≡ -(c^2+d^2)  -> cong m wP wQ via +correction (c^2+d^2)
     Px ≡ a*b-c*d , Qx ≡ a*b-c*d     -> cong m Px Qx via +correction (c*d)
     Py ≡ 0 , Qy ≡ 0                 -> cong m Py 0 and cong m Qy 0
     Qz ≡ 0                          -> cong m Qz 0 directly

   The divide pipeline (3 sq_diff_dvd pairs -> assemble mn = SS where
   SS = (sw^2+sx^2)+(sy^2+Qz^2) LEFT-PAIRED -> dvd m sw,sx,sy,Qz ->
   divide-by-m^2 via withQuot+proveIdentityG+mult_left_cancel_r ->
   four_sq_witness) is otherwise identical to ++++ / PPPN.

   RE-RUN (warm star checkpoint, BIG step budget):
     POLYML_HEAP_BYTES=8000000000 POLYML_GC_THRESHOLD=88 \
       ./target/release/poly run --max-steps 1000000000000 /tmp/l4_foursq_star \
       < divide_leaf_ppnn_delta.sml
   Output: four_sq (mult p r), hyps = the 7 disclosed divide-leaf premises only.
   ============================================================================ *)
val () = restore_l4_context ();
val () = out "DIVNN_BEGIN\n";
fun sq x = mult x x;
fun dbl t = add t t;

(* ---- sq_diff_dvd : cong m P Q ==> EX s. (s^2+2PQ = P^2+Q^2) AND cong m s 0 ---- *)
fun sqDiffDvdPred (mT,P,Q) =
  let val sF = Free("s_sdd", natT)
  in Term.lambda sF (mkConj (oeq (add (sq sF) (dbl (mult P Q))) (add (sq P)(sq Q)))
                            (cong mT sF ZeroC)) end;
fun sq_diff_dvd (mT, P, Q) hPQ =
  let
    val Cgoal = mkEx (sqDiffDvdPred (mT,P,Q))
    val tot = le_total_d (Q, P)
    val caseA =
      let val hP = jT (le Q P); val h = Thm.assume (ctermGR hP)
          val sT = subv P Q
          val rec0 = sub_recover_g (P, Q) h
          val idPoly = proveIdentityG (add (sq sT) (dbl (mult (add sT Q) Q))) (add (sq (add sT Q)) (sq Q))
          val zF = Free("zsd",natT)
          val rwPred = Term.lambda zF (oeq (add (sq sT) (dbl (mult zF Q))) (add (sq zF)(sq Q)))
          val bodyEq = oeq_rw_g (rwPred, add sT Q, P) rec0 idPoly
          val congSQ = oeq_rw_r (Term.lambda (Free("zc",natT)) (cong mT (Free("zc",natT)) Q), P, add sT Q) (oeqSym_r2 rec0) hPQ
          val q0q = oeqSym_r2 (add0_d Q)
          val congSQ0 = oeq_rw_r (Term.lambda (Free("zc2",natT)) (cong mT (add sT Q) (Free("zc2",natT))), Q, add ZeroC Q) q0q congSQ
          val congS0 = cong_radd_cancel_r (mT, sT, ZeroC, Q) congSQ0
          val body = conjI_r (oeq (add (sq sT)(dbl (mult P Q))) (add (sq P)(sq Q)), cong mT sT ZeroC) bodyEq congS0
          val ex = exI_r (sqDiffDvdPred (mT,P,Q)) sT body
      in Thm.implies_intr (ctermGR hP) ex end
    val caseB =
      let val hP = jT (le P Q); val h = Thm.assume (ctermGR hP)
          val sT = subv Q P
          val rec0 = sub_recover_g (Q, P) h
          val idPoly = proveIdentityG (add (sq sT) (dbl (mult P (add sT P)))) (add (sq P) (sq (add sT P)))
          val zF = Free("zsd",natT)
          val rwPred = Term.lambda zF (oeq (add (sq sT) (dbl (mult P zF))) (add (sq P)(sq zF)))
          val bodyEq = oeq_rw_g (rwPred, add sT P, Q) rec0 idPoly
          val hQP = cong_sym_g (mT, P, Q) hPQ
          val congSP = oeq_rw_r (Term.lambda (Free("zc",natT)) (cong mT (Free("zc",natT)) P), Q, add sT P) (oeqSym_r2 rec0) hQP
          val p0p = oeqSym_r2 (add0_d P)
          val congSP0 = oeq_rw_r (Term.lambda (Free("zc2",natT)) (cong mT (add sT P) (Free("zc2",natT))), P, add ZeroC P) p0p congSP
          val congS0 = cong_radd_cancel_r (mT, sT, ZeroC, P) congSP0
          val body = conjI_r (oeq (add (sq sT)(dbl (mult P Q))) (add (sq P)(sq Q)), cong mT sT ZeroC) bodyEq congS0
          val ex = exI_r (sqDiffDvdPred (mT,P,Q)) sT body
      in Thm.implies_intr (ctermGR hP) ex end
  in disjE_r (le Q P, le P Q, Cgoal) tot caseA caseB end;
val () = out "DIVNN_SQDIFF_OK\n";

(* cong helper: from cong m x' x, get cong m (k*x')(k*x) *)
fun cong_kmult (mT, k, xp, x) hflag = cong_mult_r (mT, k, k, xp, x) (cong_refl_g (mT, k)) hflag;

(* ---- THE PPNN LEAF ---- *)
fun divide_leaf_ppnn (mT,pT,rT, a,b,c,d, e,f,g,h)
        hbodyP hsum hca hcb hccR hcdR hmPos =
  (* hca: cong m e a ; hcb: cong m f b ; hccR: cong m (g+c) 0 ; hcdR: cong m (h+d) 0 *)
  let
    val mp = mult mT pT  val mr = mult mT rT
    val sumA = add (add (sq a)(sq b))(add (sq c)(sq d))
    val Mabcd = add (add (sq a)(sq b))(add (sq c)(sq d))
    val Mefgh = add (add (sq e)(sq f))(add (sq g)(sq h))
    val mn = mult Mabcd Mefgh
    (* witnesses (match starL_3/starR_3 exactly) *)
    val wP = add (mult a e)(mult b f)                   val wQ = add (mult c g)(mult d h)
    val Px = add (mult a f)(mult g d)                   val Qx = add (mult e b)(mult c h)
    val Py = add (mult b h)(mult f d)                   val Qy = add (mult a g)(mult e c)
    val Qz = add (add (add (mult a h)(mult e d))(mult b g))(mult f c)
    (* Dcross = 2*(wP*wQ + Px*Qx + Py*Qy)  [left-folded as ((wP*wQ + Px*Qx) + Py*Qy)] *)
    val Dcross = dbl (add (add (mult wP wQ)(mult Px Qx)) (mult Py Qy))
    val PPsum  = add (add (add (add (add (add (sq wP)(sq wQ))(sq Px))(sq Qx))(sq Py))(sq Qy))(sq Qz)
    val starL_i = add mn Dcross
    val starR_i = PPsum
    val star_i = proveIdentityG starL_i starR_i
    val () = if (Thm.prop_of star_i) aconv (jT (oeq starL_i starR_i)) then out "DIVNN_STAR_SHAPE_OK\n"
             else raise Fail "star shape"

    (* ============ THE FOUR DIVISIBILITY FACTS ============ *)

    (* (1) cong m wP wQ : wP=a*e+b*f (LEFT) ; wQ=c*g+d*h (RIGHT pair).
       correction = c^2+d^2.
         wP + (c^2+d^2) ≡ (a^2+b^2)+(c^2+d^2) = m*p ≡ 0
         wQ + (c^2+d^2) = (c*g+c^2)+(d*h+d^2) = c*(g+c)+d*(h+d) ≡ 0 *)
    val corrW = add (sq c)(sq d)
    val c_ae = cong_kmult (mT, a, e, a) hca   (* cong m (a*e)(a*a) *)
    val c_bf = cong_kmult (mT, b, f, b) hcb   (* cong m (b*f)(b*b) *)
    val c_wp = cong_add_g (mT, mult a e, sq a, mult b f, sq b) c_ae c_bf  (* cong m wP (a^2+b^2) *)
    val c_wPcorr = cong_add_g (mT, wP, add (sq a)(sq b), corrW, corrW) c_wp (cong_refl_g (mT, corrW))
                   (* cong m (wP+corr) ((a^2+b^2)+(c^2+d^2)) *)
    val reA = proveIdentityG (add (add (sq a)(sq b)) corrW) sumA  (* (a^2+b^2)+(c^2+d^2) = sumA *)
    val c_to_sumA = cong_trans_g (mT, add wP corrW, add (add (sq a)(sq b)) corrW, sumA)
                      c_wPcorr (cong_of_oeq_r (mT, add (add (sq a)(sq b)) corrW, sumA) reA)
    val c_wPcorr_mp = oeq_rw_r (Term.lambda (Free("zq",natT)) (cong mT (add wP corrW) (Free("zq",natT))), sumA, mp)
                        (oeqSym_r2 hbodyP) c_to_sumA   (* cong m (wP+corr)(m*p) *)
    val c_mp0 = (let val z = add0_d mp in cong_introR_r (mT, mp, ZeroC, pT) (oeqSym_r2 z) end)
    val c_wPcorr0 = cong_trans_g (mT, add wP corrW, mp, ZeroC) c_wPcorr_mp c_mp0   (* cong m (wP+corr) 0 *)
    (* wQ + corr = (c*g + d*h) + (c^2 + d^2) ; reassoc to (c*g+c^2) + (d*h+d^2) = c*(g+c) + d*(h+d). *)
    val c_cgc = cong_kmult (mT, c, add g c, ZeroC) hccR     (* cong m (c*(g+c))(c*0) *)
    val cc0 = mult0r_d c
    val c_cgc0 = cong_trans_g (mT, mult c (add g c), mult c ZeroC, ZeroC) c_cgc (cong_of_oeq_r (mT, mult c ZeroC, ZeroC) cc0) (* cong m (c*(g+c)) 0 *)
    val c_dhd = cong_kmult (mT, d, add h d, ZeroC) hcdR     (* cong m (d*(h+d))(d*0) *)
    val dd0 = mult0r_d d
    val c_dhd0 = cong_trans_g (mT, mult d (add h d), mult d ZeroC, ZeroC) c_dhd (cong_of_oeq_r (mT, mult d ZeroC, ZeroC) dd0) (* cong m (d*(h+d)) 0 *)
    val c_negsum = cong_add_g (mT, mult c (add g c), ZeroC, mult d (add h d), ZeroC) c_cgc0 c_dhd0
                   (* cong m (c*(g+c)+d*(h+d)) (0+0) *)
    val re00 = add0_d ZeroC   (* 0+0 = 0 *)
    val c_negsum0 = cong_trans_g (mT, add (mult c (add g c))(mult d (add h d)), add ZeroC ZeroC, ZeroC)
                      c_negsum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) re00)
                    (* cong m (c*(g+c)+d*(h+d)) 0 *)
    val reWQcorr = proveIdentityG (add wQ corrW) (add (mult c (add g c))(mult d (add h d)))
                   (* (c*g+d*h)+(c^2+d^2) = c*(g+c)+d*(h+d) *)
    val c_wQcorr0 = cong_trans_g (mT, add wQ corrW, add (mult c (add g c))(mult d (add h d)), ZeroC)
                      (cong_of_oeq_r (mT, add wQ corrW, add (mult c (add g c))(mult d (add h d))) reWQcorr) c_negsum0
                    (* cong m (wQ+corr) 0 *)
    val c_both_w = cong_trans_g (mT, add wP corrW, ZeroC, add wQ corrW) c_wPcorr0 (cong_sym_g (mT, add wQ corrW, ZeroC) c_wQcorr0)
                   (* cong m (wP+corr)(wQ+corr) *)
    val c_wPwQ = cong_radd_cancel_r (mT, wP, wQ, corrW) c_both_w   (* cong m wP wQ *)
    val () = out "DIVNN_CONG_W_OK\n";

    (* (2) cong m Px Qx : Px=a*f+g*d ; Qx=e*b+c*h.  Both ≡ a*b - c*d.
       correction = c*d.
         Px + c*d = a*f + (g*d + c*d) = a*f + (g+c)*d ; a*f≡a*b, (g+c)*d≡0 (need d*(g+c)) -> ≡ a*b
         Qx + c*d = e*b + (c*h + c*d) = e*b + c*(h+d) ; e*b≡a*b, c*(h+d)≡0 -> ≡ a*b *)
    val corrX = mult c d
    (* Px + c*d ≡ a*b *)
    val cPx_af_ab = cong_kmult (mT, a, f, b) hcb            (* cong m (a*f)(a*b) *)
    (* g*d + c*d ≡ 0 : g*d≡? use g RIGHT.  g*d + c*d = (g*d + c*d); show cong m (g*d+c*d) 0.
       d*(g+c) route: cong m (g*d)(? ) is awkward; instead rewrite g*d+c*d = d*(g+c) and use cong m (d*(g+c)) 0. *)
    val reGD = proveIdentityG (add (mult g d)(mult c d)) (mult d (add g c))   (* g*d+c*d = d*(g+c) *)
    val c_dgc = cong_kmult (mT, d, add g c, ZeroC) hccR     (* cong m (d*(g+c))(d*0) *)
    val dgc0 = mult0r_d d
    val c_dgc0 = cong_trans_g (mT, mult d (add g c), mult d ZeroC, ZeroC) c_dgc (cong_of_oeq_r (mT, mult d ZeroC, ZeroC) dgc0)
    val c_gdcd0 = cong_trans_g (mT, add (mult g d)(mult c d), mult d (add g c), ZeroC)
                    (cong_of_oeq_r (mT, add (mult g d)(mult c d), mult d (add g c)) reGD) c_dgc0
                  (* cong m (g*d+c*d) 0 *)
    (* Px + c*d = (a*f + g*d) + c*d ; reassoc to a*f + (g*d + c*d). cong m (Px+c*d)(a*b+0)=a*b *)
    val rePxC = proveIdentityG (add Px corrX) (add (mult a f)(add (mult g d)(mult c d)))  (* (a*f+g*d)+c*d = a*f+(g*d+c*d) *)
    val c_PxC_re = cong_of_oeq_r (mT, add Px corrX, add (mult a f)(add (mult g d)(mult c d))) rePxC
    val c_PxC_sum = cong_add_g (mT, mult a f, mult a b, add (mult g d)(mult c d), ZeroC) cPx_af_ab c_gdcd0
                    (* cong m (a*f+(g*d+c*d))(a*b+0) *)
    val reAB0 = add0r_d (mult a b)   (* a*b+0 = a*b *)
    val c_PxC_ab = cong_trans_g (mT, add Px corrX, add (mult a f)(add (mult g d)(mult c d)), mult a b)
                     c_PxC_re (cong_trans_g (mT, add (mult a f)(add (mult g d)(mult c d)), add (mult a b) ZeroC, mult a b)
                                 c_PxC_sum (cong_of_oeq_r (mT, add (mult a b) ZeroC, mult a b) reAB0))
                   (* cong m (Px+c*d)(a*b) *)
    (* Qx + c*d ≡ a*b *)
    val c_eb_ab = cong_mult_r (mT, e, a, b, b) hca (cong_refl_g (mT, b))   (* cong m (e*b)(a*b) *)
    val reCH = proveIdentityG (add (mult c h)(mult c d)) (mult c (add h d))   (* c*h+c*d = c*(h+d) *)
    val c_chd = cong_kmult (mT, c, add h d, ZeroC) hcdR    (* cong m (c*(h+d))(c*0) *)
    val cch0 = mult0r_d c
    val c_chd0 = cong_trans_g (mT, mult c (add h d), mult c ZeroC, ZeroC) c_chd (cong_of_oeq_r (mT, mult c ZeroC, ZeroC) cch0)
    val c_chcd0 = cong_trans_g (mT, add (mult c h)(mult c d), mult c (add h d), ZeroC)
                    (cong_of_oeq_r (mT, add (mult c h)(mult c d), mult c (add h d)) reCH) c_chd0
                  (* cong m (c*h+c*d) 0 *)
    val reQxC = proveIdentityG (add Qx corrX) (add (mult e b)(add (mult c h)(mult c d)))  (* (e*b+c*h)+c*d = e*b+(c*h+c*d) *)
    val c_QxC_re = cong_of_oeq_r (mT, add Qx corrX, add (mult e b)(add (mult c h)(mult c d))) reQxC
    val c_QxC_sum = cong_add_g (mT, mult e b, mult a b, add (mult c h)(mult c d), ZeroC) c_eb_ab c_chcd0
                    (* cong m (e*b+(c*h+c*d))(a*b+0) *)
    val reAB0b = add0r_d (mult a b)
    val c_QxC_ab = cong_trans_g (mT, add Qx corrX, add (mult e b)(add (mult c h)(mult c d)), mult a b)
                     c_QxC_re (cong_trans_g (mT, add (mult e b)(add (mult c h)(mult c d)), add (mult a b) ZeroC, mult a b)
                                 c_QxC_sum (cong_of_oeq_r (mT, add (mult a b) ZeroC, mult a b) reAB0b))
                   (* cong m (Qx+c*d)(a*b) *)
    val c_both_x = cong_trans_g (mT, add Px corrX, mult a b, add Qx corrX) c_PxC_ab (cong_sym_g (mT, add Qx corrX, mult a b) c_QxC_ab)
                   (* cong m (Px+c*d)(Qx+c*d) *)
    val c_PxQx = cong_radd_cancel_r (mT, Px, Qx, corrX) c_both_x   (* cong m Px Qx *)
    val () = out "DIVNN_CONG_X_OK\n";

    (* (3) cong m Py Qy : Py=b*h+f*d ; Qy=a*g+e*c.  Both ≡ 0.
       Py: b*h≡-b*d (h RIGHT), f*d≡b*d (f≡b) -> b*h+f*d ≡ 0.
           b*h + b*d = b*(h+d) ≡ 0 ; f*d≡b*d.  So cong m Py 0.
       Qy: a*g≡-a*c (g RIGHT), e*c≡a*c (e≡a) -> a*g+e*c ≡ 0.
           a*g + a*c = a*(g+c) ≡ 0 ; e*c≡a*c.  So cong m Qy 0. *)
    (* cong m Py 0 *)
    val c_fd_bd = cong_mult_r (mT, f, b, d, d) hcb (cong_refl_g (mT, d))   (* cong m (f*d)(b*d) *)
    val c_Py_to = cong_add_g (mT, mult b h, mult b h, mult f d, mult b d) (cong_refl_g (mT, mult b h)) c_fd_bd
                  (* cong m (b*h+f*d)(b*h+b*d) *)
    val reBH = proveIdentityG (add (mult b h)(mult b d)) (mult b (add h d))   (* b*h+b*d = b*(h+d) *)
    val c_bhd = cong_kmult (mT, b, add h d, ZeroC) hcdR    (* cong m (b*(h+d))(b*0) *)
    val cbh0 = mult0r_d b
    val c_bhd0 = cong_trans_g (mT, mult b (add h d), mult b ZeroC, ZeroC) c_bhd (cong_of_oeq_r (mT, mult b ZeroC, ZeroC) cbh0)
    val c_bhbd0 = cong_trans_g (mT, add (mult b h)(mult b d), mult b (add h d), ZeroC)
                    (cong_of_oeq_r (mT, add (mult b h)(mult b d), mult b (add h d)) reBH) c_bhd0
                  (* cong m (b*h+b*d) 0 *)
    val c_Py0 = cong_trans_g (mT, Py, add (mult b h)(mult b d), ZeroC) c_Py_to c_bhbd0   (* cong m Py 0 *)
    (* cong m Qy 0 *)
    val c_ec_ac = cong_mult_r (mT, e, a, c, c) hca (cong_refl_g (mT, c))   (* cong m (e*c)(a*c) *)
    val c_Qy_to = cong_add_g (mT, mult a g, mult a g, mult e c, mult a c) (cong_refl_g (mT, mult a g)) c_ec_ac
                  (* cong m (a*g+e*c)(a*g+a*c) *)
    val reAG = proveIdentityG (add (mult a g)(mult a c)) (mult a (add g c))   (* a*g+a*c = a*(g+c) *)
    val c_agc = cong_kmult (mT, a, add g c, ZeroC) hccR    (* cong m (a*(g+c))(a*0) *)
    val cag0 = mult0r_d a
    val c_agc0 = cong_trans_g (mT, mult a (add g c), mult a ZeroC, ZeroC) c_agc (cong_of_oeq_r (mT, mult a ZeroC, ZeroC) cag0)
    val c_agac0 = cong_trans_g (mT, add (mult a g)(mult a c), mult a (add g c), ZeroC)
                    (cong_of_oeq_r (mT, add (mult a g)(mult a c), mult a (add g c)) reAG) c_agc0
                  (* cong m (a*g+a*c) 0 *)
    val c_Qy0 = cong_trans_g (mT, Qy, add (mult a g)(mult a c), ZeroC) c_Qy_to c_agac0   (* cong m Qy 0 *)
    val c_PyQy = cong_trans_g (mT, Py, ZeroC, Qy) c_Py0 (cong_sym_g (mT, Qy, ZeroC) c_Qy0)   (* cong m Py Qy *)
    val () = out "DIVNN_CONG_Y_OK\n";

    (* (4) cong m Qz 0 : Qz=((a*h+e*d)+b*g)+f*c.  ≡0.
       a*h≡-a*d (h RIGHT), e*d≡a*d (e≡a) -> a*h+e*d ≡ 0
       b*g≡-b*c (g RIGHT), f*c≡b*c (f≡b) -> b*g+f*c ≡ 0
       Qz = ((a*h+e*d)+b*g)+f*c ; reassoc to (a*h+e*d)+(b*g+f*c) ≡ 0+0 = 0 *)
    (* a*h+e*d ≡ 0 *)
    val c_ed_ad = cong_mult_r (mT, e, a, d, d) hca (cong_refl_g (mT, d))   (* cong m (e*d)(a*d) *)
    val c_ahed_to = cong_add_g (mT, mult a h, mult a h, mult e d, mult a d) (cong_refl_g (mT, mult a h)) c_ed_ad
                    (* cong m (a*h+e*d)(a*h+a*d) *)
    val reAH = proveIdentityG (add (mult a h)(mult a d)) (mult a (add h d))   (* a*h+a*d = a*(h+d) *)
    val c_ahd = cong_kmult (mT, a, add h d, ZeroC) hcdR    (* cong m (a*(h+d))(a*0) *)
    val cah0 = mult0r_d a
    val c_ahd0 = cong_trans_g (mT, mult a (add h d), mult a ZeroC, ZeroC) c_ahd (cong_of_oeq_r (mT, mult a ZeroC, ZeroC) cah0)
    val c_ahad0 = cong_trans_g (mT, add (mult a h)(mult a d), mult a (add h d), ZeroC)
                    (cong_of_oeq_r (mT, add (mult a h)(mult a d), mult a (add h d)) reAH) c_ahd0
    val c_ahed0 = cong_trans_g (mT, add (mult a h)(mult e d), add (mult a h)(mult a d), ZeroC) c_ahed_to c_ahad0
                  (* cong m (a*h+e*d) 0 *)
    (* b*g+f*c ≡ 0 *)
    val c_fc_bc = cong_mult_r (mT, f, b, c, c) hcb (cong_refl_g (mT, c))   (* cong m (f*c)(b*c) *)
    val c_bgfc_to = cong_add_g (mT, mult b g, mult b g, mult f c, mult b c) (cong_refl_g (mT, mult b g)) c_fc_bc
                    (* cong m (b*g+f*c)(b*g+b*c) *)
    val reBG = proveIdentityG (add (mult b g)(mult b c)) (mult b (add g c))   (* b*g+b*c = b*(g+c) *)
    val c_bgc = cong_kmult (mT, b, add g c, ZeroC) hccR    (* cong m (b*(g+c))(b*0) *)
    val cbg0 = mult0r_d b
    val c_bgc0 = cong_trans_g (mT, mult b (add g c), mult b ZeroC, ZeroC) c_bgc (cong_of_oeq_r (mT, mult b ZeroC, ZeroC) cbg0)
    val c_bgbc0 = cong_trans_g (mT, add (mult b g)(mult b c), mult b (add g c), ZeroC)
                    (cong_of_oeq_r (mT, add (mult b g)(mult b c), mult b (add g c)) reBG) c_bgc0
    val c_bgfc0 = cong_trans_g (mT, add (mult b g)(mult f c), add (mult b g)(mult b c), ZeroC) c_bgfc_to c_bgbc0
                  (* cong m (b*g+f*c) 0 *)
    (* Qz = ((a*h+e*d)+b*g)+f*c ; reassoc to (a*h+e*d)+(b*g+f*c) *)
    val reQz = proveIdentityG Qz (add (add (mult a h)(mult e d)) (add (mult b g)(mult f c)))
    val c_Qz_re = cong_of_oeq_r (mT, Qz, add (add (mult a h)(mult e d)) (add (mult b g)(mult f c))) reQz
    val c_Qz_sum = cong_add_g (mT, add (mult a h)(mult e d), ZeroC, add (mult b g)(mult f c), ZeroC) c_ahed0 c_bgfc0
                   (* cong m ((a*h+e*d)+(b*g+f*c))(0+0) *)
    val re00z = add0_d ZeroC
    val c_Qz_0sum = cong_trans_g (mT, add (add (mult a h)(mult e d))(add (mult b g)(mult f c)), add ZeroC ZeroC, ZeroC)
                      c_Qz_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) re00z)
    val c_Qz0 = cong_trans_g (mT, Qz, add (add (mult a h)(mult e d))(add (mult b g)(mult f c)), ZeroC) c_Qz_re c_Qz_0sum
                (* cong m Qz 0 *)
    val () = out "DIVNN_CONG_Z_OK\n";

    (* ============ THE DIVIDE (3 pairs + lone Qz) ============ *)
    val goalC = four_sq (mult pT rT)
    val exW = sq_diff_dvd (mT, wP, wQ) c_wPwQ
    val exX = sq_diff_dvd (mT, Px, Qx) c_PxQx
    val exY = sq_diff_dvd (mT, Py, Qy) c_PyQy
    fun elimSD (P,Q) ex nm k =
      let val Pp = sqDiffDvdPred (mT,P,Q)
          fun bd s (hbody:thm) =
            let val hEq = conjunct1_r (oeq (add (sq s)(dbl (mult P Q))) (add (sq P)(sq Q)), cong mT s ZeroC) hbody
                val hDv = conjunct2_r (oeq (add (sq s)(dbl (mult P Q))) (add (sq P)(sq Q)), cong mT s ZeroC) hbody
            in k s hEq hDv end
      in exE_r (Pp, goalC) ex nm natT bd end

    val res =
      elimSD (wP,wQ) exW "sw_d" (fn sw => fn hwEq => fn hwDv =>
       elimSD (Px,Qx) exX "sx_d" (fn sx => fn hxEq => fn hxDv =>
        elimSD (Py,Qy) exY "sy_d" (fn sy => fn hyEq => fn hyDv =>
          let
            (* L_i = s_i^2 + 2 P_i Q_i ; R_i = P_i^2 + Q_i^2 ; for the lone Qz it stays as Qz^2 *)
            val Lw = add (sq sw) (add (mult wP wQ)(mult wP wQ))   val Rw = add (sq wP)(sq wQ)
            val Lx = add (sq sx) (add (mult Px Qx)(mult Px Qx))   val Rx = add (sq Px)(sq Qx)
            val Ly = add (sq sy) (add (mult Py Qy)(mult Py Qy))   val Ry = add (sq Py)(sq Qy)
            (* sumL = Lw + (Lx + (Ly + Qz^2)) ; the corresponding R-shape =
               Rw + (Rx + (Ry + Qz^2)) ; sumL=this via the three hEq + refl on Qz^2 *)
            val Qz2 = sq Qz
            val sumL = add Lw (add Lx (add Ly Qz2))
            val cong_yz  = add_cong_l_g (Ly, Ry, Qz2) hyEq             (* (Ly+Qz^2)=(Ry+Qz^2) *)
            val cong_x   = add_cong_l_g (Lx, Rx, add Ly Qz2) hxEq
            val cong_xyz = oeqTrans_g (cong_x, add_cong_r_g (Rx, add Ly Qz2, add Ry Qz2) cong_yz)
                           (* (Lx+(Ly+Qz^2))=(Rx+(Ry+Qz^2)) *)
            val cong_w   = add_cong_l_g (Lw, Rw, add Lx (add Ly Qz2)) hwEq
            val hsumLR = oeqTrans_g (cong_w, add_cong_r_g (Rw, add Lx (add Ly Qz2), add Rx (add Ry Qz2)) cong_xyz)
                         (* sumL = Rw + (Rx + (Ry + Qz^2)) *)
            (* SS = (sw^2 + sx^2) + (sy^2 + Qz^2)  (LEFT-PAIRED to match fourSqBody) ;
               target = SS + Dcross ; sumL = target (proveAddIdentity) *)
            val SS = add (add (sq sw)(sq sx)) (add (sq sy) Qz2)
            val target = add SS Dcross
            val rearr = proveAddIdentity noLeaf sumL target
            (* sumRshape = Rw + (Rx + (Ry + Qz^2)) ; PPsum = left-folded.  Relate via proveAddIdentity *)
            val sumRshape = add Rw (add Rx (add Ry Qz2))
            val ppRel = proveAddIdentity noLeaf sumRshape PPsum    (* sumRshape = PPsum *)
            val tEqSumR = oeqTrans_g (oeqSym_g rearr, hsumLR)       (* target = sumRshape *)
            val tEqPP   = oeqTrans_g (tEqSumR, ppRel)               (* target = PPsum *)
            (* star_i : oeq (mn + Dcross) PPsum.  So mn+Dcross = SS+Dcross => mn = SS. *)
            val starEqTarget = oeqTrans_g (star_i, oeqSym_g tEqPP)  (* (mn+Dcross) = (SS+Dcross) *)
            val commL = addcomm_g (mn, Dcross)      (* mn+Dcross = Dcross+mn *)
            val commR = addcomm_g (SS, Dcross)      (* SS+Dcross = Dcross+SS *)
            val flip  = oeqTrans_g (oeqTrans_g (oeqSym_g commL, starEqTarget), commR)  (* Dcross+mn = Dcross+SS *)
            val mnEqSS = alc_g (Dcross, mn, SS) flip   (* mn = SS *)
            val () = out "DIVNN_ASSEMBLE_OK\n"

            (* mn = (m*p)*(m*r) = m^2*(p*r) *)
            val Mabcd_mp = oeqSym_r2 hbodyP
            val Mefgh_mr = hsum
            val mn_eq1 = mult_cong_l_g (Mabcd, mp, Mefgh) Mabcd_mp
            val mn_eq2 = mult_cong_r_g (mp, Mefgh, mr) Mefgh_mr
            val mn_mpmr = oeqTrans_g (mn_eq1, mn_eq2)
            val mpmr_id = proveIdentityG (mult mp mr) (mult (mult mT mT) (mult pT rT))
            val mn_msq = oeqTrans_g (mn_mpmr, mpmr_id)       (* mn = m^2*(p*r) *)

            (* dvd m sw,sx,sy,Qz *)
            val dvW = dvd_of_cong_zero (mT, sw) hwDv
            val dvX = dvd_of_cong_zero (mT, sx) hxDv
            val dvY = dvd_of_cong_zero (mT, sy) hyDv
            val dvZ = dvd_of_cong_zero (mT, Qz) c_Qz0   (* the lone Qz *)
            val () = out "DIVNN_DVD_OK\n";

            (* extract quotients and build divided sum *)
            fun withQuot (xT, dvx) nm k2 =
              let val Pq = Abs("q", natT, oeq xT (mult mT (Bound 0)))
                  fun bd q (hq:thm) = k2 q hq
              in exE_r (Pq, goalC) dvx nm natT bd end
            val res2 =
              withQuot (sw, dvW) "w0q" (fn w0 => fn hw0 =>
              withQuot (sx, dvX) "sx0q" (fn sx0 => fn hsx0 =>
              withQuot (sy, dvY) "sy0q" (fn sy0 => fn hsy0 =>
              withQuot (Qz, dvZ) "sz0q" (fn sz0 => fn hsz0 =>
                let
                  fun sqQuot (xT, x0, hx0) =
                    let val c1 = mult_cong_l_g (xT, mult mT x0, xT) hx0
                        val c2 = mult_cong_r_g (mult mT x0, xT, mult mT x0) hx0
                        val xx = oeqTrans_g (c1, c2)
                        val idP = proveIdentityG (mult (mult mT x0)(mult mT x0)) (mult (mult mT mT)(mult x0 x0))
                    in oeqTrans_g (xx, idP) end
                  val w2e  = sqQuot (sw, w0, hw0)     (* sw^2 = m^2*w0^2 *)
                  val sx2e = sqQuot (sx, sx0, hsx0)
                  val sy2e = sqQuot (sy, sy0, hsy0)
                  val sz2e = sqQuot (Qz, sz0, hsz0)   (* Qz^2 = m^2*sz0^2 *)
                  val msq = mult mT mT
                  (* SS = (sw^2 + sx^2) + (sy^2 + Qz^2)  (LEFT-PAIRED) ; rewrite each to m^2*(..) *)
                  val sWX = add_cong_l_g (sq sw, mult msq (sq w0), sq sx) w2e
                  val sWX2 = oeqTrans_g (sWX, add_cong_r_g (mult msq (sq w0), sq sx, mult msq (sq sx0)) sx2e)
                  val sYZ = add_cong_l_g (sq sy, mult msq (sq sy0), Qz2) sy2e
                  val sYZ2 = oeqTrans_g (sYZ, add_cong_r_g (mult msq (sq sy0), Qz2, mult msq (sq sz0)) sz2e)
                  val sAll = oeqTrans_g (add_cong_l_g (add (sq sw)(sq sx), add (mult msq (sq w0))(mult msq (sq sx0)), add (sq sy) Qz2) sWX2,
                                         add_cong_r_g (add (mult msq (sq w0))(mult msq (sq sx0)), add (sq sy) Qz2, add (mult msq (sq sy0))(mult msq (sq sz0))) sYZ2)
                  (* SS = (m^2*w0^2 + m^2*sx0^2) + (m^2*sy0^2 + m^2*sz0^2) =: distShape *)
                  val divSum = add (add (sq w0)(sq sx0)) (add (sq sy0)(sq sz0))
                  val distShape = add (add (mult msq (sq w0))(mult msq (sq sx0))) (add (mult msq (sq sy0))(mult msq (sq sz0)))
                  val factId = proveIdentityG distShape (mult msq divSum)
                  (* chain: m^2*(p*r) = mn [mn_msq sym] = SS [mnEqSS] = distShape [sAll] = m^2*divSum [factId] *)
                  val e1 = oeqTrans_r2 (oeqSym_r2 mn_msq, mnEqSS)    (* m^2*(p*r) = SS *)
                  val e2 = oeqTrans_r2 (e1, sAll)                    (* m^2*(p*r) = distShape *)
                  val e3 = oeqTrans_r2 (e2, factId)                  (* m^2*(p*r) = m^2*divSum *)
                  val ltm0mm = mult_lt_mono_l mT hmPos (ZeroC, mT) hmPos
                  val msqPos = oeq_rw_r (Term.lambda (Free("zmp",natT)) (lt (Free("zmp",natT)) (mult mT mT)),
                                         mult mT ZeroC, ZeroC) (mult0r_d mT) ltm0mm
                  val pr_eq = mult_left_cancel_r msq msqPos (mult pT rT, divSum) e3   (* p*r = divSum *)
                  val fsBody = oeqTrans_r2 (pr_eq, oeqRefl_r2 divSum)
                in four_sq_witness (mult pT rT, w0, sx0, sy0, sz0) fsBody end)))
              )
          in res2 end)))
  in res end;
val () = out "DIVNN_LEAF_DEFINED\n";

(* smoke: run on Frees with assumed hyps (a,b LEFT, c,d RIGHT) *)
val () =
  let
    val mF=Free("m_n",natT); val pF=Free("p_n",natT); val rF=Free("r_n",natT);
    val aF=Free("a_n",natT); val bF=Free("b_n",natT); val cF=Free("c_n",natT); val dF=Free("d_n",natT);
    val eF=Free("e_n",natT); val fF=Free("f_n",natT); val gF=Free("g_n",natT); val hF=Free("h_n",natT);
    val hbodyP = Thm.assume (ctermGR (jT (oeq (mult mF pF) (add (add (sq aF)(sq bF))(add (sq cF)(sq dF))))));
    val hsum   = Thm.assume (ctermGR (jT (oeq (add (add (sq eF)(sq fF))(add (sq gF)(sq hF))) (mult mF rF))));
    val hca = Thm.assume (ctermGR (jT (cong mF eF aF)));
    val hcb = Thm.assume (ctermGR (jT (cong mF fF bF)));
    val hccR = Thm.assume (ctermGR (jT (cong mF (add gF cF) ZeroC)));
    val hcdR = Thm.assume (ctermGR (jT (cong mF (add hF dF) ZeroC)));
    val hmPos = Thm.assume (ctermGR (jT (lt ZeroC mF)));
    val r = divide_leaf_ppnn (mF,pF,rF, aF,bF,cF,dF, eF,fF,gF,hF) hbodyP hsum hca hcb hccR hcdR hmPos
  in out ("DIVNN_SMOKE hyps="^Int.toString(length(Thm.hyps_of r))
          ^" prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)^"\n") end
  handle e => out ("DIVNN_SMOKE FAIL "^exnMessage e^"\n");

val () = out "DIVNN_ALL_DONE\n";
