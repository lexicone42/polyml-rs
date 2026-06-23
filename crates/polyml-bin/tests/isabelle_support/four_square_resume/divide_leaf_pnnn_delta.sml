(* ============================================================================
   FULL (PNNN) DIVIDE LEAF, end-to-end on /tmp/l4_foursq_star.
   Pattern PNNN: a LEFT (cong m e a), b,c,d RIGHT
                 (cong m (f+b) 0 / cong m (g+c) 0 / cong m (h+d) 0).

   The fourth+ fully-proven divide leaf (after ++++, PPPN, PPNP, PPNN, PNPP,
   PNPN).  PNNN is the all-but-one-negative pattern (only a is positive); it is
   the global-negation twin of PPPP under (a,b,c,d)->(a,-b,-c,-d).

   PNNN star (l4_build_8stars_v2.sml starL_7/starR_7), 8-square order:
     W0 = a*e                  W1 = (b*f + c*g) + d*h
     W2 = g*d                  W3 = (a*f + e*b) + c*h
     W4 = b*h                  W5 = (a*g + e*c) + f*d
     W6 = f*c                  W7 = (a*h + e*d) + b*g
   cross pairs: (W0,W1),(W2,W3),(W4,W5),(W6,W7) -- the FULL symmetric 4-pair
   shape (like PPPN/PNPP), so the divide uses FOUR sq_diff_dvd pairs.

   Residue reductions (e=a, f=-b, g=-c, h=-d mod m):
     wP=W0 ≡ a^2          wQ=W1 ≡ -(b^2+c^2+d^2)  -> +correction (b^2+c^2+d^2)
     Px=W2 ≡ -c*d         Qx=W3 ≡ -c*d            -> +correction (c*d)
     Py=W4 ≡ -b*d         Qy=W5 ≡ -b*d            -> +correction (b*d)
     Pz=W6 ≡ -b*c         Qz=W7 ≡ -b*c            -> +correction (b*c)
   Unlike PNPP (where only one side of each pair needs correction), here BOTH
   sides of EVERY pair reduce to 0 after the correction (only a is positive),
   so each cong m P Q is proved by cong m (P+corr) 0 AND cong m (Q+corr) 0,
   then cong_radd_cancel.  Verified offline (/tmp/verify_pnnn.py): the star
   identity holds and all 8 corrected reductions are correct.

   The star is built CHEAPLY via proveIdentityG starL_i starR_i (NO 13-min
   proveStarFor, NO starV_i checkpoint).  The divide pipeline (sq_diff_dvd x4
   -> assemble mn=SS -> dvd m s_i -> divide-by-m^2 via withQuot +
   proveIdentityG + mult_left_cancel_r -> four_sq_witness) is identical to
   PNPP / PPPN.

   IMPORTANT divSum/SS shape: four_sq_witness needs the LEFT-PAIRED RHS
   (sw^2+sx^2)+(sy^2+sz^2) (fourSqBody in _assembled_base.sml).

   RE-RUN (warm star checkpoint, needs a BIG step budget -- the 4-pair
   symmetric divide is heavy; 200e9 is NOT enough):
     POLYML_HEAP_BYTES=8000000000 POLYML_GC_THRESHOLD=88 \
       ./target/release/poly run --max-steps 1000000000000 /tmp/l4_foursq_star \
       < divide_leaf_pnnn_delta.sml
   Output: four_sq (mult p r), hyps = the 7 disclosed divide-leaf premises only.
   ============================================================================ *)
val () = restore_l4_context ();
val () = out "DIVPNNN_BEGIN\n";
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
val () = out "DIVPNNN_SQDIFF_OK\n";

(* cong helper: from cong m x' x, get cong m (k*x')(k*x) *)
fun cong_kmult (mT, k, xp, x) hflag = cong_mult_r (mT, k, k, xp, x) (cong_refl_g (mT, k)) hflag;

(* ---- reusable building blocks for the all-RIGHT corrections ----

   rightZero (mT, k, residPlusOrig, hflagR) : from hflagR : cong m residPlusOrig 0,
     produce  cong m (k * residPlusOrig) 0.   [= k*(r+o) ≡ k*0 = 0]              *)
fun rightZero (mT, k, ro, hflagR) =
  let val c1 = cong_kmult (mT, k, ro, ZeroC) hflagR        (* cong m (k*ro)(k*0) *)
      val z  = mult0r_d k                                   (* k*0 = 0 *)
  in cong_trans_g (mT, mult k ro, mult k ZeroC, ZeroC) c1 (cong_of_oeq_r (mT, mult k ZeroC, ZeroC) z) end;

(* ---- THE PNNN LEAF ---- *)
fun divide_leaf_pnnn (mT,pT,rT, a,b,c,d, e,f,g,h)
        hbodyP hsum hca hcbR hccR hcdR hmPos =
  (* hca: cong m e a ; hcbR: cong m (f+b) 0 ; hccR: cong m (g+c) 0 ; hcdR: cong m (h+d) 0 *)
  let
    val mp = mult mT pT  val mr = mult mT rT
    val sumA = add (add (sq a)(sq b))(add (sq c)(sq d))
    val Mabcd = add (add (sq a)(sq b))(add (sq c)(sq d))
    val Mefgh = add (add (sq e)(sq f))(add (sq g)(sq h))
    val mn = mult Mabcd Mefgh
    (* witnesses (match starL_7/starR_7 exactly) *)
    val wP = mult a e                                    val wQ = add (add (mult b f)(mult c g))(mult d h)
    val Px = mult g d                                    val Qx = add (add (mult a f)(mult e b))(mult c h)
    val Py = mult b h                                    val Qy = add (add (mult a g)(mult e c))(mult f d)
    val Pz = mult f c                                    val Qz = add (add (mult a h)(mult e d))(mult b g)
    val Dcross = dbl (add (add (add (mult wP wQ) (mult Px Qx)) (mult Py Qy)) (mult Pz Qz))
    val PPsum  = add (add (add (add (add (add (add (sq wP)(sq wQ))(sq Px))(sq Qx))(sq Py))(sq Qy))(sq Pz))(sq Qz)
    val starL_i = add mn Dcross
    val starR_i = PPsum
    (* build the star via proveIdentityG (cheap) *)
    val star_i = proveIdentityG starL_i starR_i
    val () = if (Thm.prop_of star_i) aconv (jT (oeq starL_i starR_i)) then out "DIVPNNN_STAR_SHAPE_OK\n"
             else raise Fail "star shape"

    val c_mp0 = (let val z = add0_d mp in cong_introR_r (mT, mp, ZeroC, pT) (oeqSym_r2 z) end)

    (* ============ PAIR W : cong m wP wQ ============
       wP = a*e (a LEFT) ; wQ = (b*f+c*g)+d*h (all RIGHT).
       corrW = (b^2+c^2)+d^2.
         wP + corrW ≡ a^2 + (b^2+c^2+d^2) = sumA = m*p ≡ 0
         wQ + corrW = (b*f+c*g+d*h)+(b^2+c^2+d^2) = b*(f+b)+c*(g+c)+d*(h+d) ≡ 0 *)
    val corrW = add (add (sq b)(sq c))(sq d)
    (* LHS: cong m (wP+corrW) 0 *)
    val c_ae = cong_kmult (mT, a, e, a) hca                       (* cong m (a*e)(a*a) *)
    val c_wPcorr = cong_add_g (mT, wP, sq a, corrW, corrW) c_ae (cong_refl_g (mT, corrW))
                   (* cong m (wP+corrW)(a^2+corrW) *)
    val reA = proveIdentityG (add (sq a) corrW) sumA             (* a^2+(b^2+c^2+d^2) = sumA *)
    val c_to_sumA = cong_trans_g (mT, add wP corrW, add (sq a) corrW, sumA)
                      c_wPcorr (cong_of_oeq_r (mT, add (sq a) corrW, sumA) reA)
    val c_wPcorr_mp = oeq_rw_r (Term.lambda (Free("zq",natT)) (cong mT (add wP corrW) (Free("zq",natT))), sumA, mp)
                        (oeqSym_r2 hbodyP) c_to_sumA              (* cong m (wP+corrW)(m*p) *)
    val c_wPcorr0 = cong_trans_g (mT, add wP corrW, mp, ZeroC) c_wPcorr_mp c_mp0   (* cong m (wP+corrW) 0 *)
    (* RHS: cong m (wQ+corrW) 0.  wQ+corrW = b*(f+b)+c*(g+c)+d*(h+d) *)
    val c_bfb0 = rightZero (mT, b, add f b, hcbR)               (* cong m (b*(f+b)) 0 *)
    val c_cgc0 = rightZero (mT, c, add g c, hccR)               (* cong m (c*(g+c)) 0 *)
    val c_dhd0 = rightZero (mT, d, add h d, hcdR)               (* cong m (d*(h+d)) 0 *)
    val c_bc_sum = cong_add_g (mT, mult b (add f b), ZeroC, mult c (add g c), ZeroC) c_bfb0 c_cgc0
                   (* cong m (b*(f+b)+c*(g+c)) (0+0) *)
    val re00w = add0_d ZeroC
    val c_bc_sum0 = cong_trans_g (mT, add (mult b (add f b))(mult c (add g c)), add ZeroC ZeroC, ZeroC)
                      c_bc_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) re00w)  (* cong m (b*(f+b)+c*(g+c)) 0 *)
    val c_bcd_sum = cong_add_g (mT, add (mult b (add f b))(mult c (add g c)), ZeroC, mult d (add h d), ZeroC) c_bc_sum0 c_dhd0
                    (* cong m ((b*(f+b)+c*(g+c))+d*(h+d)) (0+0) *)
    val re00w2 = add0_d ZeroC
    val c_bcd_sum0 = cong_trans_g (mT, add (add (mult b (add f b))(mult c (add g c)))(mult d (add h d)), add ZeroC ZeroC, ZeroC)
                       c_bcd_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) re00w2)
                     (* cong m ((b*(f+b)+c*(g+c))+d*(h+d)) 0 *)
    val reWQ = proveIdentityG (add wQ corrW) (add (add (mult b (add f b))(mult c (add g c)))(mult d (add h d)))
               (* (b*f+c*g+d*h)+(b^2+c^2+d^2) = (b*(f+b)+c*(g+c))+d*(h+d) *)
    val c_wQcorr0 = cong_trans_g (mT, add wQ corrW, add (add (mult b (add f b))(mult c (add g c)))(mult d (add h d)), ZeroC)
                      (cong_of_oeq_r (mT, add wQ corrW, add (add (mult b (add f b))(mult c (add g c)))(mult d (add h d))) reWQ) c_bcd_sum0
                    (* cong m (wQ+corrW) 0 *)
    val c_both_w = cong_trans_g (mT, add wP corrW, ZeroC, add wQ corrW) c_wPcorr0 (cong_sym_g (mT, add wQ corrW, ZeroC) c_wQcorr0)
    val c_wPwQ = cong_radd_cancel_r (mT, wP, wQ, corrW) c_both_w   (* cong m wP wQ *)
    val () = out "DIVPNNN_CONG_W_OK\n";

    (* ============ PAIR X : cong m Px Qx ============
       Px = g*d (g RIGHT) ; Qx = (a*f+e*b)+c*h ; corrX = c*d.
         Px + c*d = g*d+c*d = d*(g+c) ≡ 0
         Qx + c*d = (a*f+e*b) + (c*h+c*d) = (a*f+e*b) + c*(h+d) ; a*f+e*b≡0, c*(h+d)≡0 *)
    val corrX = mult c d
    (* cong m (Px+corrX) 0 *)
    val c_dgc0 = rightZero (mT, d, add g c, hccR)               (* cong m (d*(g+c)) 0 *)
    val reGD = proveIdentityG (add Px corrX) (mult d (add g c)) (* g*d+c*d = d*(g+c) *)
    val c_PxX0 = cong_trans_g (mT, add Px corrX, mult d (add g c), ZeroC)
                   (cong_of_oeq_r (mT, add Px corrX, mult d (add g c)) reGD) c_dgc0  (* cong m (Px+corrX) 0 *)
    (* cong m (Qx+corrX) 0 *)
    (* a*f+e*b ≡ 0 : a*f+a*b = a*(f+b)≡0, e*b≡a*b *)
    val c_eb = cong_mult_r (mT, e, a, b, b) hca (cong_refl_g (mT, b))  (* cong m (e*b)(a*b) *)
    val c_afeb1 = cong_add_g (mT, mult a f, mult a f, mult e b, mult a b) (cong_refl_g (mT, mult a f)) c_eb
                  (* cong m (a*f+e*b)(a*f+a*b) *)
    val reAF = proveIdentityG (add (mult a f)(mult a b)) (mult a (add f b))  (* a*f+a*b = a*(f+b) *)
    val c_afb0 = rightZero (mT, a, add f b, hcbR)              (* cong m (a*(f+b)) 0 *)
    val c_afab0 = cong_trans_g (mT, add (mult a f)(mult a b), mult a (add f b), ZeroC)
                    (cong_of_oeq_r (mT, add (mult a f)(mult a b), mult a (add f b)) reAF) c_afb0
    val c_afeb0 = cong_trans_g (mT, add (mult a f)(mult e b), add (mult a f)(mult a b), ZeroC) c_afeb1 c_afab0
                  (* cong m (a*f+e*b) 0 *)
    (* c*h+c*d = c*(h+d) ≡ 0 *)
    val c_chd0 = rightZero (mT, c, add h d, hcdR)             (* cong m (c*(h+d)) 0 *)
    val reCH = proveIdentityG (add (mult c h)(mult c d)) (mult c (add h d))  (* c*h+c*d = c*(h+d) *)
    val c_chcd0 = cong_trans_g (mT, add (mult c h)(mult c d), mult c (add h d), ZeroC)
                    (cong_of_oeq_r (mT, add (mult c h)(mult c d), mult c (add h d)) reCH) c_chd0
                  (* cong m (c*h+c*d) 0 *)
    (* Qx+corrX = ((a*f+e*b)+c*h)+c*d ; regroup to (a*f+e*b)+(c*h+c*d) *)
    val reQxC = proveIdentityG (add Qx corrX) (add (add (mult a f)(mult e b)) (add (mult c h)(mult c d)))
    val c_QxC_re = cong_of_oeq_r (mT, add Qx corrX, add (add (mult a f)(mult e b))(add (mult c h)(mult c d))) reQxC
    val c_QxC_sum = cong_add_g (mT, add (mult a f)(mult e b), ZeroC, add (mult c h)(mult c d), ZeroC) c_afeb0 c_chcd0
                    (* cong m ((a*f+e*b)+(c*h+c*d))(0+0) *)
    val re00x = add0_d ZeroC
    val c_QxC0 = cong_trans_g (mT, add Qx corrX, add (add (mult a f)(mult e b))(add (mult c h)(mult c d)), ZeroC)
                   c_QxC_re (cong_trans_g (mT, add (add (mult a f)(mult e b))(add (mult c h)(mult c d)), add ZeroC ZeroC, ZeroC)
                              c_QxC_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) re00x))
                 (* cong m (Qx+corrX) 0 *)
    val c_both_x = cong_trans_g (mT, add Px corrX, ZeroC, add Qx corrX) c_PxX0 (cong_sym_g (mT, add Qx corrX, ZeroC) c_QxC0)
    val c_PxQx = cong_radd_cancel_r (mT, Px, Qx, corrX) c_both_x   (* cong m Px Qx *)
    val () = out "DIVPNNN_CONG_X_OK\n";

    (* ============ PAIR Y : cong m Py Qy ============
       Py = b*h (h RIGHT) ; Qy = (a*g+e*c)+f*d ; corrY = b*d.
         Py + b*d = b*h+b*d = b*(h+d) ≡ 0
         Qy + b*d = (a*g+e*c) + (f*d+b*d) = (a*g+e*c) + d*(f+b) ; a*g+e*c≡0, d*(f+b)≡0 *)
    val corrY = mult b d
    (* cong m (Py+corrY) 0 *)
    val c_bhd0 = rightZero (mT, b, add h d, hcdR)              (* cong m (b*(h+d)) 0 *)
    val reBH = proveIdentityG (add Py corrY) (mult b (add h d))  (* b*h+b*d = b*(h+d) *)
    val c_PyY0 = cong_trans_g (mT, add Py corrY, mult b (add h d), ZeroC)
                   (cong_of_oeq_r (mT, add Py corrY, mult b (add h d)) reBH) c_bhd0  (* cong m (Py+corrY) 0 *)
    (* cong m (Qy+corrY) 0 *)
    (* a*g+e*c ≡ 0 : a*g+a*c=a*(g+c)≡0, e*c≡a*c *)
    val c_ec = cong_mult_r (mT, e, a, c, c) hca (cong_refl_g (mT, c))  (* cong m (e*c)(a*c) *)
    val c_agec1 = cong_add_g (mT, mult a g, mult a g, mult e c, mult a c) (cong_refl_g (mT, mult a g)) c_ec
                  (* cong m (a*g+e*c)(a*g+a*c) *)
    val reAG = proveIdentityG (add (mult a g)(mult a c)) (mult a (add g c))  (* a*g+a*c = a*(g+c) *)
    val c_agc0 = rightZero (mT, a, add g c, hccR)             (* cong m (a*(g+c)) 0 *)
    val c_agac0 = cong_trans_g (mT, add (mult a g)(mult a c), mult a (add g c), ZeroC)
                    (cong_of_oeq_r (mT, add (mult a g)(mult a c), mult a (add g c)) reAG) c_agc0
    val c_agec0 = cong_trans_g (mT, add (mult a g)(mult e c), add (mult a g)(mult a c), ZeroC) c_agec1 c_agac0
                  (* cong m (a*g+e*c) 0 *)
    (* f*d+b*d = d*(f+b) ≡ 0 *)
    val c_dfb0 = rightZero (mT, d, add f b, hcbR)            (* cong m (d*(f+b)) 0 *)
    val reFD = proveIdentityG (add (mult f d)(mult b d)) (mult d (add f b))  (* f*d+b*d = d*(f+b) *)
    val c_fdbd0 = cong_trans_g (mT, add (mult f d)(mult b d), mult d (add f b), ZeroC)
                    (cong_of_oeq_r (mT, add (mult f d)(mult b d), mult d (add f b)) reFD) c_dfb0
                  (* cong m (f*d+b*d) 0 *)
    (* Qy+corrY = ((a*g+e*c)+f*d)+b*d ; regroup to (a*g+e*c)+(f*d+b*d) *)
    val reQyC = proveIdentityG (add Qy corrY) (add (add (mult a g)(mult e c)) (add (mult f d)(mult b d)))
    val c_QyC_re = cong_of_oeq_r (mT, add Qy corrY, add (add (mult a g)(mult e c))(add (mult f d)(mult b d))) reQyC
    val c_QyC_sum = cong_add_g (mT, add (mult a g)(mult e c), ZeroC, add (mult f d)(mult b d), ZeroC) c_agec0 c_fdbd0
    val re00y = add0_d ZeroC
    val c_QyC0 = cong_trans_g (mT, add Qy corrY, add (add (mult a g)(mult e c))(add (mult f d)(mult b d)), ZeroC)
                   c_QyC_re (cong_trans_g (mT, add (add (mult a g)(mult e c))(add (mult f d)(mult b d)), add ZeroC ZeroC, ZeroC)
                              c_QyC_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) re00y))
                 (* cong m (Qy+corrY) 0 *)
    val c_both_y = cong_trans_g (mT, add Py corrY, ZeroC, add Qy corrY) c_PyY0 (cong_sym_g (mT, add Qy corrY, ZeroC) c_QyC0)
    val c_PyQy = cong_radd_cancel_r (mT, Py, Qy, corrY) c_both_y   (* cong m Py Qy *)
    val () = out "DIVPNNN_CONG_Y_OK\n";

    (* ============ PAIR Z : cong m Pz Qz ============
       Pz = f*c (f RIGHT) ; Qz = (a*h+e*d)+b*g ; corrZ = b*c.
         Pz + b*c = f*c+b*c = c*(f+b) ≡ 0
         Qz + b*c = (a*h+e*d) + (b*g+b*c) = (a*h+e*d) + b*(g+c) ; a*h+e*d≡0, b*(g+c)≡0 *)
    val corrZ = mult b c
    (* cong m (Pz+corrZ) 0 *)
    val c_cfb0 = rightZero (mT, c, add f b, hcbR)            (* cong m (c*(f+b)) 0 *)
    val reFC = proveIdentityG (add Pz corrZ) (mult c (add f b))  (* f*c+b*c = c*(f+b) *)
    val c_PzZ0 = cong_trans_g (mT, add Pz corrZ, mult c (add f b), ZeroC)
                   (cong_of_oeq_r (mT, add Pz corrZ, mult c (add f b)) reFC) c_cfb0  (* cong m (Pz+corrZ) 0 *)
    (* cong m (Qz+corrZ) 0 *)
    (* a*h+e*d ≡ 0 : a*h+a*d=a*(h+d)≡0, e*d≡a*d *)
    val c_ed = cong_mult_r (mT, e, a, d, d) hca (cong_refl_g (mT, d))  (* cong m (e*d)(a*d) *)
    val c_ahed1 = cong_add_g (mT, mult a h, mult a h, mult e d, mult a d) (cong_refl_g (mT, mult a h)) c_ed
                  (* cong m (a*h+e*d)(a*h+a*d) *)
    val reAH = proveIdentityG (add (mult a h)(mult a d)) (mult a (add h d))  (* a*h+a*d = a*(h+d) *)
    val c_ahd0 = rightZero (mT, a, add h d, hcdR)           (* cong m (a*(h+d)) 0 *)
    val c_ahad0 = cong_trans_g (mT, add (mult a h)(mult a d), mult a (add h d), ZeroC)
                    (cong_of_oeq_r (mT, add (mult a h)(mult a d), mult a (add h d)) reAH) c_ahd0
    val c_ahed0 = cong_trans_g (mT, add (mult a h)(mult e d), add (mult a h)(mult a d), ZeroC) c_ahed1 c_ahad0
                  (* cong m (a*h+e*d) 0 *)
    (* b*g+b*c = b*(g+c) ≡ 0 *)
    val c_bgc0 = rightZero (mT, b, add g c, hccR)           (* cong m (b*(g+c)) 0 *)
    val reBG = proveIdentityG (add (mult b g)(mult b c)) (mult b (add g c))  (* b*g+b*c = b*(g+c) *)
    val c_bgbc0 = cong_trans_g (mT, add (mult b g)(mult b c), mult b (add g c), ZeroC)
                    (cong_of_oeq_r (mT, add (mult b g)(mult b c), mult b (add g c)) reBG) c_bgc0
                  (* cong m (b*g+b*c) 0 *)
    (* Qz+corrZ = ((a*h+e*d)+b*g)+b*c ; regroup to (a*h+e*d)+(b*g+b*c) *)
    val reQzC = proveIdentityG (add Qz corrZ) (add (add (mult a h)(mult e d)) (add (mult b g)(mult b c)))
    val c_QzC_re = cong_of_oeq_r (mT, add Qz corrZ, add (add (mult a h)(mult e d))(add (mult b g)(mult b c))) reQzC
    val c_QzC_sum = cong_add_g (mT, add (mult a h)(mult e d), ZeroC, add (mult b g)(mult b c), ZeroC) c_ahed0 c_bgbc0
    val re00z = add0_d ZeroC
    val c_QzC0 = cong_trans_g (mT, add Qz corrZ, add (add (mult a h)(mult e d))(add (mult b g)(mult b c)), ZeroC)
                   c_QzC_re (cong_trans_g (mT, add (add (mult a h)(mult e d))(add (mult b g)(mult b c)), add ZeroC ZeroC, ZeroC)
                              c_QzC_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) re00z))
                 (* cong m (Qz+corrZ) 0 *)
    val c_both_z = cong_trans_g (mT, add Pz corrZ, ZeroC, add Qz corrZ) c_PzZ0 (cong_sym_g (mT, add Qz corrZ, ZeroC) c_QzC0)
    val c_PzQz = cong_radd_cancel_r (mT, Pz, Qz, corrZ) c_both_z   (* cong m Pz Qz *)
    val () = out "DIVPNNN_CONG_Z_OK\n";

    (* ============ THE DIVIDE (4-pair symmetric) ============ *)
    val goalC = four_sq (mult pT rT)
    val exW = sq_diff_dvd (mT, wP, wQ) c_wPwQ
    val exX = sq_diff_dvd (mT, Px, Qx) c_PxQx
    val exY = sq_diff_dvd (mT, Py, Qy) c_PyQy
    val exZ = sq_diff_dvd (mT, Pz, Qz) c_PzQz
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
         elimSD (Pz,Qz) exZ "sz_d" (fn sz => fn hzEq => fn hzDv =>
          let
            (* L_i = s_i^2 + 2 P_i Q_i ; R_i = P_i^2 + Q_i^2 *)
            val Lw = add (sq sw) (add (mult wP wQ)(mult wP wQ))   val Rw = add (sq wP)(sq wQ)
            val Lx = add (sq sx) (add (mult Px Qx)(mult Px Qx))   val Rx = add (sq Px)(sq Qx)
            val Ly = add (sq sy) (add (mult Py Qy)(mult Py Qy))   val Ry = add (sq Py)(sq Qy)
            val Lz = add (sq sz) (add (mult Pz Qz)(mult Pz Qz))   val Rz = add (sq Pz)(sq Qz)
            val sumL = add Lw (add Lx (add Ly Lz))
            val cong_yz  = add_cong_l_g (Ly, Ry, Lz) hyEq
            val cong_yz2 = oeqTrans_g (cong_yz, add_cong_r_g (Ry, Lz, Rz) hzEq)            (* (Ly+Lz)=(Ry+Rz) *)
            val cong_x   = add_cong_l_g (Lx, Rx, add Ly Lz) hxEq
            val cong_xyz = oeqTrans_g (cong_x, add_cong_r_g (Rx, add Ly Lz, add Ry Rz) cong_yz2) (* (Lx+(Ly+Lz))=(Rx+(Ry+Rz)) *)
            val cong_w   = add_cong_l_g (Lw, Rw, add Lx (add Ly Lz)) hwEq
            val hsumLR = oeqTrans_g (cong_w, add_cong_r_g (Rw, add Lx (add Ly Lz), add Rx (add Ry Rz)) cong_xyz)
                         (* sumL = Rw + (Rx + (Ry + Rz)) *)
            val SS = add (add (sq sw)(sq sx)) (add (sq sy)(sq sz))
            val target = add SS Dcross
            val rearr = proveAddIdentity noLeaf sumL target
            val sumRshape = add Rw (add Rx (add Ry Rz))
            val ppRel = proveAddIdentity noLeaf sumRshape PPsum    (* (Rw+(Rx+(Ry+Rz))) = PPsum *)
            val tEqSumR = oeqTrans_g (oeqSym_g rearr, hsumLR)       (* target = sumRshape *)
            val tEqPP   = oeqTrans_g (tEqSumR, ppRel)               (* target = PPsum *)
            val starEqTarget = oeqTrans_g (star_i, oeqSym_g tEqPP)  (* (mn+Dcross) = (SS+Dcross) *)
            val commL = addcomm_g (mn, Dcross)      (* mn+Dcross = Dcross+mn *)
            val commR = addcomm_g (SS, Dcross)      (* SS+Dcross = Dcross+SS *)
            val flip  = oeqTrans_g (oeqTrans_g (oeqSym_g commL, starEqTarget), commR)  (* Dcross+mn = Dcross+SS *)
            val mnEqSS = alc_g (Dcross, mn, SS) flip   (* mn = SS *)
            val () = out "DIVPNNN_ASSEMBLE_OK\n"

            (* mn = (m*p)*(m*r) = m^2*(p*r) *)
            val Mabcd_mp = oeqSym_r2 hbodyP
            val Mefgh_mr = hsum
            val mn_eq1 = mult_cong_l_g (Mabcd, mp, Mefgh) Mabcd_mp
            val mn_eq2 = mult_cong_r_g (mp, Mefgh, mr) Mefgh_mr
            val mn_mpmr = oeqTrans_g (mn_eq1, mn_eq2)
            val mpmr_id = proveIdentityG (mult mp mr) (mult (mult mT mT) (mult pT rT))
            val mn_msq = oeqTrans_g (mn_mpmr, mpmr_id)       (* mn = m^2*(p*r) *)

            (* dvd m sw,sx,sy,sz *)
            val dvW = dvd_of_cong_zero (mT, sw) hwDv
            val dvX = dvd_of_cong_zero (mT, sx) hxDv
            val dvY = dvd_of_cong_zero (mT, sy) hyDv
            val dvZ = dvd_of_cong_zero (mT, sz) hzDv
            val () = out "DIVPNNN_DVD_OK\n";

            (* extract quotients and build divided sum, mirroring PPPP/PNPP *)
            fun withQuot (xT, dvx) nm k2 =
              let val Pq = Abs("q", natT, oeq xT (mult mT (Bound 0)))
                  fun bd q (hq:thm) = k2 q hq
              in exE_r (Pq, goalC) dvx nm natT bd end
            val res2 =
              withQuot (sw, dvW) "w0q" (fn w0 => fn hw0 =>
              withQuot (sx, dvX) "sx0q" (fn sx0 => fn hsx0 =>
              withQuot (sy, dvY) "sy0q" (fn sy0 => fn hsy0 =>
              withQuot (sz, dvZ) "sz0q" (fn sz0 => fn hsz0 =>
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
                  val sz2e = sqQuot (sz, sz0, hsz0)
                  val msq = mult mT mT
                  val sWX = add_cong_l_g (sq sw, mult msq (sq w0), sq sx) w2e
                  val sWX2 = oeqTrans_g (sWX, add_cong_r_g (mult msq (sq w0), sq sx, mult msq (sq sx0)) sx2e)
                  val sYZ = add_cong_l_g (sq sy, mult msq (sq sy0), sq sz) sy2e
                  val sYZ2 = oeqTrans_g (sYZ, add_cong_r_g (mult msq (sq sy0), sq sz, mult msq (sq sz0)) sz2e)
                  val sAll = oeqTrans_g (add_cong_l_g (add (sq sw)(sq sx), add (mult msq (sq w0))(mult msq (sq sx0)), add (sq sy)(sq sz)) sWX2,
                                         add_cong_r_g (add (mult msq (sq w0))(mult msq (sq sx0)), add (sq sy)(sq sz), add (mult msq (sq sy0))(mult msq (sq sz0))) sYZ2)
                  val divSum = add (add (sq w0)(sq sx0)) (add (sq sy0)(sq sz0))
                  val distShape = add (add (mult msq (sq w0))(mult msq (sq sx0))) (add (mult msq (sq sy0))(mult msq (sq sz0)))
                  val factId = proveIdentityG distShape (mult msq divSum)
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
          in res2 end))))
  in res end;
val () = out "DIVPNNN_LEAF_DEFINED\n";

(* smoke: run on Frees with assumed hyps (a LEFT, b,c,d RIGHT) *)
val () =
  let
    val mF=Free("m_n",natT); val pF=Free("p_n",natT); val rF=Free("r_n",natT);
    val aF=Free("a_n",natT); val bF=Free("b_n",natT); val cF=Free("c_n",natT); val dF=Free("d_n",natT);
    val eF=Free("e_n",natT); val fF=Free("f_n",natT); val gF=Free("g_n",natT); val hF=Free("h_n",natT);
    val hbodyP = Thm.assume (ctermGR (jT (oeq (mult mF pF) (add (add (sq aF)(sq bF))(add (sq cF)(sq dF))))));
    val hsum   = Thm.assume (ctermGR (jT (oeq (add (add (sq eF)(sq fF))(add (sq gF)(sq hF))) (mult mF rF))));
    val hca = Thm.assume (ctermGR (jT (cong mF eF aF)));
    val hcbR = Thm.assume (ctermGR (jT (cong mF (add fF bF) ZeroC)));
    val hccR = Thm.assume (ctermGR (jT (cong mF (add gF cF) ZeroC)));
    val hcdR = Thm.assume (ctermGR (jT (cong mF (add hF dF) ZeroC)));
    val hmPos = Thm.assume (ctermGR (jT (lt ZeroC mF)));
    val r = divide_leaf_pnnn (mF,pF,rF, aF,bF,cF,dF, eF,fF,gF,hF) hbodyP hsum hca hcbR hccR hcdR hmPos
  in out ("DIVPNNN_SMOKE hyps="^Int.toString(length(Thm.hyps_of r))
          ^" prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)^"\n") end
  handle e => out ("DIVPNNN_SMOKE FAIL "^exnMessage e^"\n");

val () = out "DIVPNNN_ALL_DONE\n";
