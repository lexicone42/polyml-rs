(* ============================================================================
   FULL (NNNN) DIVIDE LEAF — the 9th leaf, the global-negation of PPPP.
   All FOUR coordinates RIGHT:  cong m (e+a) 0, cong m (f+b) 0, cong m (g+c) 0,
   cong m (h+d) 0.  Needed for the RRRR sign-branch of descent_step (the only
   branch the 8 a-LEFT leaves + coordinate permutation cannot reach).

   Witnesses (LEFT-FOLDED, from the NNNN star = global-neg of PPPP):
     wP = 0                          wQ = ((a*e + b*f) + c*g) + d*h
     Px = b*e + d*g                  Qx = a*f + c*h
     Py = b*h + c*e                  Qy = a*g + d*f
     Pz = c*f + d*e                  Qz = a*h + b*g
   (verified star identity: mn + 2*(wP*wQ + Px*Qx + Py*Qy + Pz*Qz) = ΣP²+ΣQ², /tmp gen.)

   All four divisibility congruences via the "+correction" trick (rightZero), as in
   the pnnn leaf; the only new wrinkle is the W-pair has wP=0 (so cong m wP wQ is
   cong m 0 wQ).  Otherwise the divide pipeline is identical to pnnn.

   Run on /tmp/l4_foursq_star (or any checkpoint with the GR helpers + proveIdentityG).
     POLYML_HEAP_BYTES=8000000000 POLYML_GC_THRESHOLD=88 \
       ./target/release/poly run --max-steps 1000000000000 <ckpt> < this.sml
   ============================================================================ *)
val () = restore_l4_context ();
val () = out "DIVNNNN_BEGIN\n";
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
val () = out "DIVNNNN_SQDIFF_OK\n";

fun cong_kmult (mT, k, xp, x) hflag = cong_mult_r (mT, k, k, xp, x) (cong_refl_g (mT, k)) hflag;
(* rightZero (m,k,ro,hflagR) : hflagR : cong m ro 0  ->  cong m (k*ro) 0
   used as: ro = (resid+coord), hflagR : cong m (resid+coord) 0 *)
fun rightZero (mT, k, ro, hflagR) =
  let val c1 = cong_kmult (mT, k, ro, ZeroC) hflagR        (* cong m (k*ro)(k*0) *)
      val z  = mult0r_d k                                   (* k*0 = 0 *)
  in cong_trans_g (mT, mult k ro, mult k ZeroC, ZeroC) c1 (cong_of_oeq_r (mT, mult k ZeroC, ZeroC) z) end;

(* ---- THE NNNN LEAF ---- *)
fun divide_leaf_nnnn (mT,pT,rT, a,b,c,d, e,f,g,h)
        hbodyP hsum hcaR hcbR hccR hcdR hmPos =
  (* hcaR: cong m (e+a) 0 ; hcbR: cong m (f+b) 0 ; hccR: cong m (g+c) 0 ; hcdR: cong m (h+d) 0 *)
  let
    val mp = mult mT pT  val mr = mult mT rT
    val sumA = add (add (sq a)(sq b))(add (sq c)(sq d))
    val Mabcd = add (add (sq a)(sq b))(add (sq c)(sq d))
    val Mefgh = add (add (sq e)(sq f))(add (sq g)(sq h))
    val mn = mult Mabcd Mefgh
    (* witnesses (LEFT-FOLDED, NNNN star = global-neg of PPPP).
       wP=0 dropped from star/Dcross/PPsum (proveIdentityG does NOT reduce mult Zero x);
       w is a SINGLE divisible value wQ (cong m wQ 0), handled directly (sw:=wQ). *)
    val wQ = add (add (add (mult a e)(mult b f))(mult c g))(mult d h)
    val Px = add (mult b e)(mult d g)                   val Qx = add (mult a f)(mult c h)
    val Py = add (mult b h)(mult c e)                   val Qy = add (mult a g)(mult d f)
    val Pz = add (mult c f)(mult d e)                   val Qz = add (mult a h)(mult b g)
    (* Dcross drops wP*wQ ; PPsum keeps wQ^2 but drops wP^2=0 *)
    val Dcross = dbl (add (mult Px Qx) (add (mult Py Qy) (mult Pz Qz)))
    val PPsum  = add (sq wQ) (add (add (sq Px)(sq Qx)) (add (add (sq Py)(sq Qy)) (add (sq Pz)(sq Qz))))
    val starL_i = add mn Dcross
    val starR_i = PPsum
    val star_i = proveIdentityG starL_i starR_i
    val () = if (Thm.prop_of star_i) aconv (jT (oeq starL_i starR_i)) then out "DIVNNNN_STAR_SHAPE_OK\n"
             else raise Fail "star shape"

    val c_mp0 = (let val z = add0_d mp in cong_introR_r (mT, mp, ZeroC, pT) (oeqSym_r2 z) end)

    (* ============ PAIR W : cong m wP wQ = cong m 0 wQ ============
       wQ = a*e+b*f+c*g+d*h.  wQ + sumA = a*(e+a)+b*(f+b)+c*(g+c)+d*(h+d) ≡ 0,
       and sumA = m*p ≡ 0, so wQ ≡ 0; then cong m 0 wQ = sym. *)
    val c_aea0 = rightZero (mT, a, add e a, hcaR)              (* cong m (a*(e+a)) 0 *)
    val c_bfb0 = rightZero (mT, b, add f b, hcbR)
    val c_cgc0 = rightZero (mT, c, add g c, hccR)
    val c_dhd0 = rightZero (mT, d, add h d, hcdR)
    val c_ab_sum = cong_add_g (mT, mult a (add e a), ZeroC, mult b (add f b), ZeroC) c_aea0 c_bfb0
    val re00ab = add0_d ZeroC
    val c_ab_sum0 = cong_trans_g (mT, add (mult a (add e a))(mult b (add f b)), add ZeroC ZeroC, ZeroC)
                      c_ab_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) re00ab)
    val c_abc_sum = cong_add_g (mT, add (mult a (add e a))(mult b (add f b)), ZeroC, mult c (add g c), ZeroC) c_ab_sum0 c_cgc0
    val c_abc_sum0 = cong_trans_g (mT, add (add (mult a (add e a))(mult b (add f b)))(mult c (add g c)), add ZeroC ZeroC, ZeroC)
                       c_abc_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) (add0_d ZeroC))
    val c_abcd_sum = cong_add_g (mT, add (add (mult a (add e a))(mult b (add f b)))(mult c (add g c)), ZeroC, mult d (add h d), ZeroC) c_abc_sum0 c_dhd0
    val rhsRT = add (add (add (mult a (add e a))(mult b (add f b)))(mult c (add g c)))(mult d (add h d))
    val c_abcd_sum0 = cong_trans_g (mT, rhsRT, add ZeroC ZeroC, ZeroC)
                       c_abcd_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) (add0_d ZeroC))
                     (* cong m (a*(e+a)+...) 0 *)
    val reWQ = proveIdentityG (add wQ sumA) rhsRT          (* wQ + sumA = a*(e+a)+...  *)
    val c_wQsumA0 = cong_trans_g (mT, add wQ sumA, rhsRT, ZeroC)
                      (cong_of_oeq_r (mT, add wQ sumA, rhsRT) reWQ) c_abcd_sum0   (* cong m (wQ+sumA) 0 *)
    (* sumA = m*p ≡ 0 *)
    val c_sumA_mp = cong_of_oeq_r (mT, sumA, mp) (oeqSym_r2 hbodyP)   (* cong m sumA (m*p) *)
    val c_sumA0 = cong_trans_g (mT, sumA, mp, ZeroC) c_sumA_mp c_mp0  (* cong m sumA 0 *)
    (* cong m wQ 0 : wQ+sumA ≡ 0, sumA ≡ 0 ; cong m (wQ+sumA)(wQ+0) via cong_add(refl wQ, c_sumA0 sym)?
       simpler: cong m (wQ+sumA) 0 and we want cong m wQ 0.  Use:
         cong m (wQ+0)(wQ+sumA)  [cong_add refl wQ, (cong m 0 sumA = sym c_sumA0)]
         cong m (wQ+0) 0          [trans with c_wQsumA0]
         cong m wQ 0              [wQ+0=wQ rewrite] *)
    val c_0sumA = cong_sym_g (mT, sumA, ZeroC) c_sumA0          (* cong m 0 sumA *)
    val c_wQ0_wQsumA = cong_add_g (mT, wQ, wQ, ZeroC, sumA) (cong_refl_g (mT, wQ)) c_0sumA  (* cong m (wQ+0)(wQ+sumA) *)
    val c_wQ0_0 = cong_trans_g (mT, add wQ ZeroC, add wQ sumA, ZeroC) c_wQ0_wQsumA c_wQsumA0  (* cong m (wQ+0) 0 *)
    val c_wQ_0 = oeq_rw_r (Term.lambda (Free("zwq",natT)) (cong mT (Free("zwq",natT)) ZeroC), add wQ ZeroC, wQ) (add0r_d wQ) c_wQ0_0  (* cong m wQ 0 *)
    val () = out "DIVNNNN_CONG_W_OK\n";

    (* ============ PAIR X : cong m Px Qx ============
       Px=b*e+d*g (b,d RIGHT) ; Qx=a*f+c*h (a,c RIGHT).  corrX = a*b+c*d.
         Px + corrX = (b*e+a*b)+(d*g+c*d) = b*(e+a)+d*(g+c) ≡ 0
         Qx + corrX = (a*f+a*b)+(c*h+c*d) = a*(f+b)+c*(h+d) ≡ 0 *)
    val corrX = add (mult a b)(mult c d)
    (* Px + corrX = (b*e + a*b) + (d*g + c*d) ; b*e+a*b = b*(e+a) [b*a=a*b], d*g+c*d=d*(g+c) [c*d=d*c] *)
    val c_bea0 = rightZero (mT, b, add e a, hcaR)             (* cong m (b*(e+a)) 0 *)
    val reBE = proveIdentityG (add (mult b e)(mult a b)) (mult b (add e a))   (* b*e+a*b = b*(e+a) *)
    val c_beab0 = cong_trans_g (mT, add (mult b e)(mult a b), mult b (add e a), ZeroC)
                    (cong_of_oeq_r (mT, add (mult b e)(mult a b), mult b (add e a)) reBE) c_bea0  (* cong m (b*e+a*b) 0 *)
    val c_dgc0 = rightZero (mT, d, add g c, hccR)             (* cong m (d*(g+c)) 0 *)
    val reDG = proveIdentityG (add (mult d g)(mult c d)) (mult d (add g c))   (* d*g+c*d = d*(g+c) *)
    val c_dgcd0 = cong_trans_g (mT, add (mult d g)(mult c d), mult d (add g c), ZeroC)
                    (cong_of_oeq_r (mT, add (mult d g)(mult c d), mult d (add g c)) reDG) c_dgc0  (* cong m (d*g+c*d) 0 *)
    val rePxC = proveIdentityG (add Px corrX) (add (add (mult b e)(mult a b)) (add (mult d g)(mult c d)))
    val c_PxC_sum = cong_add_g (mT, add (mult b e)(mult a b), ZeroC, add (mult d g)(mult c d), ZeroC) c_beab0 c_dgcd0
    val c_PxC0 = cong_trans_g (mT, add Px corrX, add (add (mult b e)(mult a b))(add (mult d g)(mult c d)), ZeroC)
                   (cong_of_oeq_r (mT, add Px corrX, add (add (mult b e)(mult a b))(add (mult d g)(mult c d))) rePxC)
                   (cong_trans_g (mT, add (add (mult b e)(mult a b))(add (mult d g)(mult c d)), add ZeroC ZeroC, ZeroC)
                      c_PxC_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) (add0_d ZeroC)))  (* cong m (Px+corrX) 0 *)
    (* Qx + corrX = (a*f + a*b) + (c*h + c*d) = a*(f+b) + c*(h+d) ≡ 0 *)
    val c_afb0 = rightZero (mT, a, add f b, hcbR)
    val reAF = proveIdentityG (add (mult a f)(mult a b)) (mult a (add f b))
    val c_afab0 = cong_trans_g (mT, add (mult a f)(mult a b), mult a (add f b), ZeroC)
                    (cong_of_oeq_r (mT, add (mult a f)(mult a b), mult a (add f b)) reAF) c_afb0
    val c_chd0 = rightZero (mT, c, add h d, hcdR)
    val reCH = proveIdentityG (add (mult c h)(mult c d)) (mult c (add h d))
    val c_chcd0 = cong_trans_g (mT, add (mult c h)(mult c d), mult c (add h d), ZeroC)
                    (cong_of_oeq_r (mT, add (mult c h)(mult c d), mult c (add h d)) reCH) c_chd0
    val reQxC = proveIdentityG (add Qx corrX) (add (add (mult a f)(mult a b)) (add (mult c h)(mult c d)))
    val c_QxC_sum = cong_add_g (mT, add (mult a f)(mult a b), ZeroC, add (mult c h)(mult c d), ZeroC) c_afab0 c_chcd0
    val c_QxC0 = cong_trans_g (mT, add Qx corrX, add (add (mult a f)(mult a b))(add (mult c h)(mult c d)), ZeroC)
                   (cong_of_oeq_r (mT, add Qx corrX, add (add (mult a f)(mult a b))(add (mult c h)(mult c d))) reQxC)
                   (cong_trans_g (mT, add (add (mult a f)(mult a b))(add (mult c h)(mult c d)), add ZeroC ZeroC, ZeroC)
                      c_QxC_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) (add0_d ZeroC)))  (* cong m (Qx+corrX) 0 *)
    val c_both_x = cong_trans_g (mT, add Px corrX, ZeroC, add Qx corrX) c_PxC0 (cong_sym_g (mT, add Qx corrX, ZeroC) c_QxC0)
    val c_PxQx = cong_radd_cancel_r (mT, Px, Qx, corrX) c_both_x   (* cong m Px Qx *)
    val () = out "DIVNNNN_CONG_X_OK\n";

    (* ============ PAIR Y : cong m Py Qy ============
       Py=b*h+c*e ; Qy=a*g+d*f.  corrY = a*c+b*d.
         Py + corrY = (b*h+b*d)+(c*e+a*c) = b*(h+d)+c*(e+a) ≡ 0
         Qy + corrY = (a*g+a*c)+(d*f+b*d) = a*(g+c)+d*(f+b) ≡ 0 *)
    val corrY = add (mult a c)(mult b d)
    val c_bhd0 = rightZero (mT, b, add h d, hcdR)
    val reBH = proveIdentityG (add (mult b h)(mult b d)) (mult b (add h d))
    val c_bhbd0 = cong_trans_g (mT, add (mult b h)(mult b d), mult b (add h d), ZeroC)
                    (cong_of_oeq_r (mT, add (mult b h)(mult b d), mult b (add h d)) reBH) c_bhd0
    val c_cea0 = rightZero (mT, c, add e a, hcaR)
    val reCE = proveIdentityG (add (mult c e)(mult a c)) (mult c (add e a))
    val c_ceac0 = cong_trans_g (mT, add (mult c e)(mult a c), mult c (add e a), ZeroC)
                    (cong_of_oeq_r (mT, add (mult c e)(mult a c), mult c (add e a)) reCE) c_cea0
    val rePyC = proveIdentityG (add Py corrY) (add (add (mult b h)(mult b d)) (add (mult c e)(mult a c)))
    val c_PyC_sum = cong_add_g (mT, add (mult b h)(mult b d), ZeroC, add (mult c e)(mult a c), ZeroC) c_bhbd0 c_ceac0
    val c_PyC0 = cong_trans_g (mT, add Py corrY, add (add (mult b h)(mult b d))(add (mult c e)(mult a c)), ZeroC)
                   (cong_of_oeq_r (mT, add Py corrY, add (add (mult b h)(mult b d))(add (mult c e)(mult a c))) rePyC)
                   (cong_trans_g (mT, add (add (mult b h)(mult b d))(add (mult c e)(mult a c)), add ZeroC ZeroC, ZeroC)
                      c_PyC_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) (add0_d ZeroC)))
    val c_agc0 = rightZero (mT, a, add g c, hccR)
    val reAG = proveIdentityG (add (mult a g)(mult a c)) (mult a (add g c))
    val c_agac0 = cong_trans_g (mT, add (mult a g)(mult a c), mult a (add g c), ZeroC)
                    (cong_of_oeq_r (mT, add (mult a g)(mult a c), mult a (add g c)) reAG) c_agc0
    val c_dfb0 = rightZero (mT, d, add f b, hcbR)
    val reDF = proveIdentityG (add (mult d f)(mult b d)) (mult d (add f b))
    val c_dfbd0 = cong_trans_g (mT, add (mult d f)(mult b d), mult d (add f b), ZeroC)
                    (cong_of_oeq_r (mT, add (mult d f)(mult b d), mult d (add f b)) reDF) c_dfb0
    val reQyC = proveIdentityG (add Qy corrY) (add (add (mult a g)(mult a c)) (add (mult d f)(mult b d)))
    val c_QyC_sum = cong_add_g (mT, add (mult a g)(mult a c), ZeroC, add (mult d f)(mult b d), ZeroC) c_agac0 c_dfbd0
    val c_QyC0 = cong_trans_g (mT, add Qy corrY, add (add (mult a g)(mult a c))(add (mult d f)(mult b d)), ZeroC)
                   (cong_of_oeq_r (mT, add Qy corrY, add (add (mult a g)(mult a c))(add (mult d f)(mult b d))) reQyC)
                   (cong_trans_g (mT, add (add (mult a g)(mult a c))(add (mult d f)(mult b d)), add ZeroC ZeroC, ZeroC)
                      c_QyC_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) (add0_d ZeroC)))
    val c_both_y = cong_trans_g (mT, add Py corrY, ZeroC, add Qy corrY) c_PyC0 (cong_sym_g (mT, add Qy corrY, ZeroC) c_QyC0)
    val c_PyQy = cong_radd_cancel_r (mT, Py, Qy, corrY) c_both_y
    val () = out "DIVNNNN_CONG_Y_OK\n";

    (* ============ PAIR Z : cong m Pz Qz ============
       Pz=c*f+d*e ; Qz=a*h+b*g.  corrZ = a*d+b*c.
         Pz + corrZ = (c*f+b*c)+(d*e+a*d) = c*(f+b)+d*(e+a) ≡ 0
         Qz + corrZ = (a*h+a*d)+(b*g+b*c) = a*(h+d)+b*(g+c) ≡ 0 *)
    val corrZ = add (mult a d)(mult b c)
    val c_cfb0 = rightZero (mT, c, add f b, hcbR)
    val reCF = proveIdentityG (add (mult c f)(mult b c)) (mult c (add f b))
    val c_cfbc0 = cong_trans_g (mT, add (mult c f)(mult b c), mult c (add f b), ZeroC)
                    (cong_of_oeq_r (mT, add (mult c f)(mult b c), mult c (add f b)) reCF) c_cfb0
    val c_dea0 = rightZero (mT, d, add e a, hcaR)
    val reDE = proveIdentityG (add (mult d e)(mult a d)) (mult d (add e a))
    val c_dead0 = cong_trans_g (mT, add (mult d e)(mult a d), mult d (add e a), ZeroC)
                    (cong_of_oeq_r (mT, add (mult d e)(mult a d), mult d (add e a)) reDE) c_dea0
    val rePzC = proveIdentityG (add Pz corrZ) (add (add (mult c f)(mult b c)) (add (mult d e)(mult a d)))
    val c_PzC_sum = cong_add_g (mT, add (mult c f)(mult b c), ZeroC, add (mult d e)(mult a d), ZeroC) c_cfbc0 c_dead0
    val c_PzC0 = cong_trans_g (mT, add Pz corrZ, add (add (mult c f)(mult b c))(add (mult d e)(mult a d)), ZeroC)
                   (cong_of_oeq_r (mT, add Pz corrZ, add (add (mult c f)(mult b c))(add (mult d e)(mult a d))) rePzC)
                   (cong_trans_g (mT, add (add (mult c f)(mult b c))(add (mult d e)(mult a d)), add ZeroC ZeroC, ZeroC)
                      c_PzC_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) (add0_d ZeroC)))
    val c_ahd0 = rightZero (mT, a, add h d, hcdR)
    val reAH = proveIdentityG (add (mult a h)(mult a d)) (mult a (add h d))
    val c_ahad0 = cong_trans_g (mT, add (mult a h)(mult a d), mult a (add h d), ZeroC)
                    (cong_of_oeq_r (mT, add (mult a h)(mult a d), mult a (add h d)) reAH) c_ahd0
    val c_bgc0 = rightZero (mT, b, add g c, hccR)
    val reBG = proveIdentityG (add (mult b g)(mult b c)) (mult b (add g c))
    val c_bgbc0 = cong_trans_g (mT, add (mult b g)(mult b c), mult b (add g c), ZeroC)
                    (cong_of_oeq_r (mT, add (mult b g)(mult b c), mult b (add g c)) reBG) c_bgc0
    val reQzC = proveIdentityG (add Qz corrZ) (add (add (mult a h)(mult a d)) (add (mult b g)(mult b c)))
    val c_QzC_sum = cong_add_g (mT, add (mult a h)(mult a d), ZeroC, add (mult b g)(mult b c), ZeroC) c_ahad0 c_bgbc0
    val c_QzC0 = cong_trans_g (mT, add Qz corrZ, add (add (mult a h)(mult a d))(add (mult b g)(mult b c)), ZeroC)
                   (cong_of_oeq_r (mT, add Qz corrZ, add (add (mult a h)(mult a d))(add (mult b g)(mult b c))) reQzC)
                   (cong_trans_g (mT, add (add (mult a h)(mult a d))(add (mult b g)(mult b c)), add ZeroC ZeroC, ZeroC)
                      c_QzC_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) (add0_d ZeroC)))
    val c_both_z = cong_trans_g (mT, add Pz corrZ, ZeroC, add Qz corrZ) c_PzC0 (cong_sym_g (mT, add Qz corrZ, ZeroC) c_QzC0)
    val c_PzQz = cong_radd_cancel_r (mT, Pz, Qz, corrZ) c_both_z
    val () = out "DIVNNNN_CONG_Z_OK\n";

    (* ============ THE DIVIDE: w is a SINGLE divisible value (sw:=wQ, no cross);
       x,y,z are 3 sq_diff_dvd pairs (wP=0 dropped). ============ *)
    val goalC = four_sq (mult pT rT)
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
      let val sw = wQ                       (* w handled directly: sw = wQ, cong m wQ 0 *)
          val hwDv = c_wQ_0                  (* dvd via dvd_of_cong_zero below *)
      in
       elimSD (Px,Qx) exX "sx_d" (fn sx => fn hxEq => fn hxDv =>
        elimSD (Py,Qy) exY "sy_d" (fn sy => fn hyEq => fn hyDv =>
         elimSD (Pz,Qz) exZ "sz_d" (fn sz => fn hzEq => fn hzDv =>
          let
            val Lx = add (sq sx) (add (mult Px Qx)(mult Px Qx))   val Rx = add (sq Px)(sq Qx)
            val Ly = add (sq sy) (add (mult Py Qy)(mult Py Qy))   val Ry = add (sq Py)(sq Qy)
            val Lz = add (sq sz) (add (mult Pz Qz)(mult Pz Qz))   val Rz = add (sq Pz)(sq Qz)
            (* sumL = sq wQ + (Lx + (Ly + Lz)) ; sumRshape = sq wQ + (Rx + (Ry + Rz)) *)
            val sumL = add (sq wQ) (add Lx (add Ly Lz))
            val cong_yz  = add_cong_l_g (Ly, Ry, Lz) hyEq
            val cong_yz2 = oeqTrans_g (cong_yz, add_cong_r_g (Ry, Lz, Rz) hzEq)
            val cong_x   = add_cong_l_g (Lx, Rx, add Ly Lz) hxEq
            val cong_xyz = oeqTrans_g (cong_x, add_cong_r_g (Rx, add Ly Lz, add Ry Rz) cong_yz2)
            val cong_w   = add_cong_l_g (sq wQ, sq wQ, add Lx (add Ly Lz)) (oeqRefl_g (sq wQ))
            val hsumLR = oeqTrans_g (cong_w, add_cong_r_g (sq wQ, add Lx (add Ly Lz), add Rx (add Ry Rz)) cong_xyz)
            val SS = add (add (sq sw)(sq sx)) (add (sq sy)(sq sz))
            val target = add SS Dcross
            val rearr = proveAddIdentity noLeaf sumL target
            val sumRshape = add (sq wQ) (add Rx (add Ry Rz))
            val ppRel = proveAddIdentity noLeaf sumRshape PPsum
            val tEqSumR = oeqTrans_g (oeqSym_g rearr, hsumLR)
            val tEqPP   = oeqTrans_g (tEqSumR, ppRel)
            val starEqTarget = oeqTrans_g (star_i, oeqSym_g tEqPP)
            val commL = addcomm_g (mn, Dcross)
            val commR = addcomm_g (SS, Dcross)
            val flip  = oeqTrans_g (oeqTrans_g (oeqSym_g commL, starEqTarget), commR)
            val mnEqSS = alc_g (Dcross, mn, SS) flip
            val () = out "DIVNNNN_ASSEMBLE_OK\n"

            val Mabcd_mp = oeqSym_r2 hbodyP
            val Mefgh_mr = hsum
            val mn_eq1 = mult_cong_l_g (Mabcd, mp, Mefgh) Mabcd_mp
            val mn_eq2 = mult_cong_r_g (mp, Mefgh, mr) Mefgh_mr
            val mn_mpmr = oeqTrans_g (mn_eq1, mn_eq2)
            val mpmr_id = proveIdentityG (mult mp mr) (mult (mult mT mT) (mult pT rT))
            val mn_msq = oeqTrans_g (mn_mpmr, mpmr_id)

            val dvW = dvd_of_cong_zero (mT, sw) hwDv
            val dvX = dvd_of_cong_zero (mT, sx) hxDv
            val dvY = dvd_of_cong_zero (mT, sy) hyDv
            val dvZ = dvd_of_cong_zero (mT, sz) hzDv
            val () = out "DIVNNNN_DVD_OK\n";

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
                  val w2e  = sqQuot (sw, w0, hw0)
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
                  val e1 = oeqTrans_r2 (oeqSym_r2 mn_msq, mnEqSS)
                  val e2 = oeqTrans_r2 (e1, sAll)
                  val e3 = oeqTrans_r2 (e2, factId)
                  val ltm0mm = mult_lt_mono_l mT hmPos (ZeroC, mT) hmPos
                  val msqPos = oeq_rw_r (Term.lambda (Free("zmp",natT)) (lt (Free("zmp",natT)) (mult mT mT)),
                                         mult mT ZeroC, ZeroC) (mult0r_d mT) ltm0mm
                  val pr_eq = mult_left_cancel_r msq msqPos (mult pT rT, divSum) e3
                  val fsBody = oeqTrans_r2 (pr_eq, oeqRefl_r2 divSum)
                in four_sq_witness (mult pT rT, w0, sx0, sy0, sz0) fsBody end)))
              )
          in res2 end)))
      end
  in res end;
val () = out "DIVNNNN_LEAF_DEFINED\n";

(* smoke: run on Frees with all-RIGHT hyps *)
val () =
  let
    val mF=Free("m_q",natT); val pF=Free("p_q",natT); val rF=Free("r_q",natT);
    val aF=Free("a_q",natT); val bF=Free("b_q",natT); val cF=Free("c_q",natT); val dF=Free("d_q",natT);
    val eF=Free("e_q",natT); val fF=Free("f_q",natT); val gF=Free("g_q",natT); val hF=Free("h_q",natT);
    val hbodyP = Thm.assume (ctermGR (jT (oeq (mult mF pF) (add (add (sq aF)(sq bF))(add (sq cF)(sq dF))))));
    val hsum   = Thm.assume (ctermGR (jT (oeq (add (add (sq eF)(sq fF))(add (sq gF)(sq hF))) (mult mF rF))));
    val hcaR = Thm.assume (ctermGR (jT (cong mF (add eF aF) ZeroC)));
    val hcbR = Thm.assume (ctermGR (jT (cong mF (add fF bF) ZeroC)));
    val hccR = Thm.assume (ctermGR (jT (cong mF (add gF cF) ZeroC)));
    val hcdR = Thm.assume (ctermGR (jT (cong mF (add hF dF) ZeroC)));
    val hmPos = Thm.assume (ctermGR (jT (lt ZeroC mF)));
    val r = divide_leaf_nnnn (mF,pF,rF, aF,bF,cF,dF, eF,fF,gF,hF) hbodyP hsum hcaR hcbR hccR hcdR hmPos
  in out ("DIVNNNN_SMOKE hyps="^Int.toString(length(Thm.hyps_of r))
          ^" prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)^"\n") end
  handle e => out ("DIVNNNN_SMOKE FAIL "^exnMessage e^"\n");
val () = out "DIVNNNN_ALL_DONE\n";
