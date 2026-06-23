(* ============================================================================
   FULL (PNNP) DIVIDE LEAF, end-to-end on /tmp/l4_foursq_star.

   Pattern PNNP: a,d LEFT (cong m e a / cong m h d),
                 b,c RIGHT (cong m (f+b) 0 / cong m (g+c) 0).

   The PNNP star (gen_8stars_v2.py s=(1,-1,-1,1)) is the
   "one-component-dropped" shape: Py = 0, so it has THREE cross-pairs
   (wP/wQ, Px/Qx, Pz/Qz) PLUS a LONE square Qy (no Py partner, no Py cross
   term).  This is the SAME structure as the proven PPNN leaf (Pz=0, lone Qz),
   only with the dropped component at the y position instead of z; the divide
   uses THREE sq_diff_dvd pairs + ONE direct cong-zero square (Qy).

   PNNP witnesses (LEFT-FOLDED, from /tmp/gen_8stars_v2.py / pnnp_star_shape.py,
   residue names ap=e, bp=f, cp=g, dp=h):
     wP = a*e + d*h          wQ = b*f + c*g
     Px = c*h + g*d          Qx = a*f + e*b
     Py = 0                  Qy = ((a*g + e*c) + b*h) + f*d
     Pz = a*h + f*c          Qz = e*d + b*g

   Residue reductions (e=a, f=-b, g=-c, h=d mod m):
     wP ≡ a^2+d^2 , wQ ≡ -(b^2+c^2)  -> cong m wP wQ via +correction (b^2+c^2)
     Px ≡ 0 , Qx ≡ 0                 -> cong m Px 0 and cong m Qx 0
     Qy ≡ 0                          -> cong m Qy 0 directly (lone square)
     Pz ≡ a*d-b*c , Qz ≡ a*d-b*c     -> cong m Pz Qz via +correction (b*c)

   The star is built CHEAPLY via proveIdentityG starL_i starR_i (NO 13-min
   proveStarFor, NO starV_i checkpoint).  The divide pipeline (3 sq_diff_dvd
   pairs + 1 direct cong-zero square -> assemble mn = SS where
   SS = (sw^2+sx^2)+(Qy^2+sz^2) LEFT-PAIRED -> dvd m sw,sx,Qy,sz ->
   divide-by-m^2 via withQuot+proveIdentityG+mult_left_cancel_r ->
   four_sq_witness) is otherwise identical to PPNN / ++++ / PPPN.

   RE-RUN (warm star checkpoint, BIG step budget):
     POLYML_HEAP_BYTES=8000000000 POLYML_GC_THRESHOLD=88 \
       ./target/release/poly run --max-steps 1000000000000 /tmp/l4_foursq_star \
       < divide_leaf_pnnp_delta.sml
   Output: four_sq (mult p r), hyps = the 7 disclosed divide-leaf premises only
   [hbodyP hsum hca hcbR hccR hcd hmPos].
   ============================================================================ *)
val () = restore_l4_context ();
val () = out "DIVPNNP_BEGIN\n";
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
val () = out "DIVPNNP_SQDIFF_OK\n";

(* cong helper: from cong m x' x, get cong m (k*x')(k*x) *)
fun cong_kmult (mT, k, xp, x) hflag = cong_mult_r (mT, k, k, xp, x) (cong_refl_g (mT, k)) hflag;

(* ---- THE PNNP LEAF ---- *)
fun divide_leaf_pnnp (mT,pT,rT, a,b,c,d, e,f,g,h)
        hbodyP hsum hca hcbR hccR hcd hmPos =
  (* hca: cong m e a ; hcbR: cong m (f+b) 0 ; hccR: cong m (g+c) 0 ; hcd: cong m h d *)
  let
    val mp = mult mT pT  val mr = mult mT rT
    val sumA = add (add (sq a)(sq b))(add (sq c)(sq d))
    val Mabcd = add (add (sq a)(sq b))(add (sq c)(sq d))
    val Mefgh = add (add (sq e)(sq f))(add (sq g)(sq h))
    val mn = mult Mabcd Mefgh
    (* witnesses (match starL/starR exactly) *)
    val wP = add (mult a e)(mult d h)                   val wQ = add (mult b f)(mult c g)
    val Px = add (mult c h)(mult g d)                   val Qx = add (mult a f)(mult e b)
    val Qy = add (add (add (mult a g)(mult e c))(mult b h))(mult f d)
    val Pz = add (mult a h)(mult f c)                   val Qz = add (mult e d)(mult b g)
    (* Dcross = 2*(wP*wQ + Px*Qx + Pz*Qz)  [left-folded as ((wP*wQ + Px*Qx) + Pz*Qz)] *)
    val Dcross = dbl (add (add (mult wP wQ)(mult Px Qx)) (mult Pz Qz))
    val PPsum  = add (add (add (add (add (add (sq wP)(sq wQ))(sq Px))(sq Qx))(sq Qy))(sq Pz))(sq Qz)
    val starL_i = add mn Dcross
    val starR_i = PPsum
    val star_i = proveIdentityG starL_i starR_i
    val () = if (Thm.prop_of star_i) aconv (jT (oeq starL_i starR_i)) then out "DIVPNNP_STAR_SHAPE_OK\n"
             else raise Fail "star shape"

    (* ============ THE FOUR DIVISIBILITY FACTS ============ *)

    (* (1) cong m wP wQ : wP=a*e+d*h (LEFT) ; wQ=b*f+c*g (RIGHT pair).
       correction = b^2+c^2.
         wP + (b^2+c^2) ≡ (a^2+d^2)+(b^2+c^2) = m*p ≡ 0
         wQ + (b^2+c^2) = (b*f+b^2)+(c*g+c^2) = b*(f+b)+c*(g+c) ≡ 0 *)
    val corrW = add (sq b)(sq c)
    val c_ae = cong_kmult (mT, a, e, a) hca   (* cong m (a*e)(a*a) *)
    val c_dh = cong_kmult (mT, d, h, d) hcd   (* cong m (d*h)(d*d) *)
    val c_wp = cong_add_g (mT, mult a e, sq a, mult d h, sq d) c_ae c_dh  (* cong m wP (a^2+d^2) *)
    val c_wPcorr = cong_add_g (mT, wP, add (sq a)(sq d), corrW, corrW) c_wp (cong_refl_g (mT, corrW))
                   (* cong m (wP+corr) ((a^2+d^2)+(b^2+c^2)) *)
    val reA = proveIdentityG (add (add (sq a)(sq d)) corrW) sumA  (* (a^2+d^2)+(b^2+c^2) = sumA *)
    val c_to_sumA = cong_trans_g (mT, add wP corrW, add (add (sq a)(sq d)) corrW, sumA)
                      c_wPcorr (cong_of_oeq_r (mT, add (add (sq a)(sq d)) corrW, sumA) reA)
    val c_wPcorr_mp = oeq_rw_r (Term.lambda (Free("zq",natT)) (cong mT (add wP corrW) (Free("zq",natT))), sumA, mp)
                        (oeqSym_r2 hbodyP) c_to_sumA   (* cong m (wP+corr)(m*p) *)
    val c_mp0 = (let val z = add0_d mp in cong_introR_r (mT, mp, ZeroC, pT) (oeqSym_r2 z) end)
    val c_wPcorr0 = cong_trans_g (mT, add wP corrW, mp, ZeroC) c_wPcorr_mp c_mp0   (* cong m (wP+corr) 0 *)
    (* wQ + corr = (b*f + c*g) + (b^2 + c^2) ; reassoc to (b*f+b^2) + (c*g+c^2) = b*(f+b) + c*(g+c). *)
    val c_bfb = cong_kmult (mT, b, add f b, ZeroC) hcbR     (* cong m (b*(f+b))(b*0) *)
    val cb0 = mult0r_d b
    val c_bfb0 = cong_trans_g (mT, mult b (add f b), mult b ZeroC, ZeroC) c_bfb (cong_of_oeq_r (mT, mult b ZeroC, ZeroC) cb0) (* cong m (b*(f+b)) 0 *)
    val c_cgc = cong_kmult (mT, c, add g c, ZeroC) hccR     (* cong m (c*(g+c))(c*0) *)
    val cc0 = mult0r_d c
    val c_cgc0 = cong_trans_g (mT, mult c (add g c), mult c ZeroC, ZeroC) c_cgc (cong_of_oeq_r (mT, mult c ZeroC, ZeroC) cc0) (* cong m (c*(g+c)) 0 *)
    val c_negsum = cong_add_g (mT, mult b (add f b), ZeroC, mult c (add g c), ZeroC) c_bfb0 c_cgc0
                   (* cong m (b*(f+b)+c*(g+c)) (0+0) *)
    val re00 = add0_d ZeroC   (* 0+0 = 0 *)
    val c_negsum0 = cong_trans_g (mT, add (mult b (add f b))(mult c (add g c)), add ZeroC ZeroC, ZeroC)
                      c_negsum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) re00)
                    (* cong m (b*(f+b)+c*(g+c)) 0 *)
    val reWQcorr = proveIdentityG (add wQ corrW) (add (mult b (add f b))(mult c (add g c)))
                   (* (b*f+c*g)+(b^2+c^2) = b*(f+b)+c*(g+c) *)
    val c_wQcorr0 = cong_trans_g (mT, add wQ corrW, add (mult b (add f b))(mult c (add g c)), ZeroC)
                      (cong_of_oeq_r (mT, add wQ corrW, add (mult b (add f b))(mult c (add g c))) reWQcorr) c_negsum0
                    (* cong m (wQ+corr) 0 *)
    val c_both_w = cong_trans_g (mT, add wP corrW, ZeroC, add wQ corrW) c_wPcorr0 (cong_sym_g (mT, add wQ corrW, ZeroC) c_wQcorr0)
                   (* cong m (wP+corr)(wQ+corr) *)
    val c_wPwQ = cong_radd_cancel_r (mT, wP, wQ, corrW) c_both_w   (* cong m wP wQ *)
    val () = out "DIVPNNP_CONG_W_OK\n";

    (* (2) cong m Px Qx : Px=c*h+g*d ; Qx=a*f+e*b.  Both ≡ 0 (route through 0).
       Px: c*h≡c*d (h≡d) ; g*d+c*d = d*(g+c)≡0.  So Px = c*h+g*d ≡ c*d+g*d ... use
           cong m (c*h)(c*d) then c*d+g*d = d*(c+g)? flag is g+c.  Use d*(g+c).
           Route: cong m (c*h+g*d)(c*d+g*d) [c*h≡c*d], and (c*d+g*d) via reorder
           = (g*d+c*d) = d*(g+c) ≡ 0.
       Qx: e*b≡a*b (e≡a) ; a*f+a*b = a*(f+b)≡0.  Route: cong m (e*b)(a*b) then
           a*f+a*b = a*(f+b) ≡ 0. *)
    (* cong m Px 0 *)
    val c_ch_cd = cong_kmult (mT, c, h, d) hcd            (* cong m (c*h)(c*d) *)
    val c_Px_to = cong_add_g (mT, mult c h, mult c d, mult g d, mult g d) c_ch_cd (cong_refl_g (mT, mult g d))
                  (* cong m (c*h+g*d)(c*d+g*d) *)
    val reCG = proveIdentityG (add (mult c d)(mult g d)) (mult d (add g c))   (* c*d+g*d = d*(g+c) *)
    val c_dgc = cong_kmult (mT, d, add g c, ZeroC) hccR    (* cong m (d*(g+c))(d*0) *)
    val cd0 = mult0r_d d
    val c_dgc0 = cong_trans_g (mT, mult d (add g c), mult d ZeroC, ZeroC) c_dgc (cong_of_oeq_r (mT, mult d ZeroC, ZeroC) cd0)
    val c_cdgd0 = cong_trans_g (mT, add (mult c d)(mult g d), mult d (add g c), ZeroC)
                    (cong_of_oeq_r (mT, add (mult c d)(mult g d), mult d (add g c)) reCG) c_dgc0
                  (* cong m (c*d+g*d) 0 *)
    val c_Px0 = cong_trans_g (mT, Px, add (mult c d)(mult g d), ZeroC) c_Px_to c_cdgd0   (* cong m Px 0 *)
    (* cong m Qx 0 *)
    val c_eb_ab = cong_mult_r (mT, e, a, b, b) hca (cong_refl_g (mT, b))   (* cong m (e*b)(a*b) *)
    val c_Qx_to = cong_add_g (mT, mult a f, mult a f, mult e b, mult a b) (cong_refl_g (mT, mult a f)) c_eb_ab
                  (* cong m (a*f+e*b)(a*f+a*b) *)
    val reAF = proveIdentityG (add (mult a f)(mult a b)) (mult a (add f b))   (* a*f+a*b = a*(f+b) *)
    val c_afb = cong_kmult (mT, a, add f b, ZeroC) hcbR    (* cong m (a*(f+b))(a*0) *)
    val ca0 = mult0r_d a
    val c_afb0 = cong_trans_g (mT, mult a (add f b), mult a ZeroC, ZeroC) c_afb (cong_of_oeq_r (mT, mult a ZeroC, ZeroC) ca0)
    val c_afab0 = cong_trans_g (mT, add (mult a f)(mult a b), mult a (add f b), ZeroC)
                    (cong_of_oeq_r (mT, add (mult a f)(mult a b), mult a (add f b)) reAF) c_afb0
                  (* cong m (a*f+a*b) 0 *)
    val c_Qx0 = cong_trans_g (mT, Qx, add (mult a f)(mult a b), ZeroC) c_Qx_to c_afab0   (* cong m Qx 0 *)
    val c_PxQx = cong_trans_g (mT, Px, ZeroC, Qx) c_Px0 (cong_sym_g (mT, Qx, ZeroC) c_Qx0)   (* cong m Px Qx *)
    val () = out "DIVPNNP_CONG_X_OK\n";

    (* (3) cong m Qy 0 : Qy=((a*g+e*c)+b*h)+f*d.  ≡0  (lone square).
       a*g≡-a*c (g RIGHT), e*c≡a*c (e≡a) -> a*g+e*c ≡ 0  via a*(g+c)
       b*h≡b*d (h≡d), f*d≡-b*d (f RIGHT) -> b*h+f*d ≡ 0  via d*(f+b)
       Qy = ((a*g+e*c)+b*h)+f*d ; reassoc to (a*g+e*c)+(b*h+f*d) ≡ 0+0 = 0 *)
    (* a*g+e*c ≡ 0 *)
    val c_ec_ac = cong_mult_r (mT, e, a, c, c) hca (cong_refl_g (mT, c))   (* cong m (e*c)(a*c) *)
    val c_agec_to = cong_add_g (mT, mult a g, mult a g, mult e c, mult a c) (cong_refl_g (mT, mult a g)) c_ec_ac
                    (* cong m (a*g+e*c)(a*g+a*c) *)
    val reAG = proveIdentityG (add (mult a g)(mult a c)) (mult a (add g c))   (* a*g+a*c = a*(g+c) *)
    val c_agc = cong_kmult (mT, a, add g c, ZeroC) hccR    (* cong m (a*(g+c))(a*0) *)
    val cag0 = mult0r_d a
    val c_agc0 = cong_trans_g (mT, mult a (add g c), mult a ZeroC, ZeroC) c_agc (cong_of_oeq_r (mT, mult a ZeroC, ZeroC) cag0)
    val c_agac0 = cong_trans_g (mT, add (mult a g)(mult a c), mult a (add g c), ZeroC)
                    (cong_of_oeq_r (mT, add (mult a g)(mult a c), mult a (add g c)) reAG) c_agc0
    val c_agec0 = cong_trans_g (mT, add (mult a g)(mult e c), add (mult a g)(mult a c), ZeroC) c_agec_to c_agac0
                  (* cong m (a*g+e*c) 0 *)
    (* b*h+f*d ≡ 0 *)
    val c_bh_bd = cong_mult_r (mT, b, b, h, d) (cong_refl_g (mT, b)) hcd   (* cong m (b*h)(b*d) *)
    val c_bhfd_to = cong_add_g (mT, mult b h, mult b d, mult f d, mult f d) c_bh_bd (cong_refl_g (mT, mult f d))
                    (* cong m (b*h+f*d)(b*d+f*d) *)
    val reFD = proveIdentityG (add (mult b d)(mult f d)) (mult d (add f b))   (* b*d+f*d = d*(f+b) *)
    val c_dfb = cong_kmult (mT, d, add f b, ZeroC) hcbR    (* cong m (d*(f+b))(d*0) *)
    val cdf0 = mult0r_d d
    val c_dfb0 = cong_trans_g (mT, mult d (add f b), mult d ZeroC, ZeroC) c_dfb (cong_of_oeq_r (mT, mult d ZeroC, ZeroC) cdf0)
    val c_bdfd0 = cong_trans_g (mT, add (mult b d)(mult f d), mult d (add f b), ZeroC)
                    (cong_of_oeq_r (mT, add (mult b d)(mult f d), mult d (add f b)) reFD) c_dfb0
    val c_bhfd0 = cong_trans_g (mT, add (mult b h)(mult f d), add (mult b d)(mult f d), ZeroC) c_bhfd_to c_bdfd0
                  (* cong m (b*h+f*d) 0 *)
    (* Qy = ((a*g+e*c)+b*h)+f*d ; reassoc to (a*g+e*c)+(b*h+f*d) *)
    val reQy = proveIdentityG Qy (add (add (mult a g)(mult e c)) (add (mult b h)(mult f d)))
    val c_Qy_re = cong_of_oeq_r (mT, Qy, add (add (mult a g)(mult e c)) (add (mult b h)(mult f d))) reQy
    val c_Qy_sum = cong_add_g (mT, add (mult a g)(mult e c), ZeroC, add (mult b h)(mult f d), ZeroC) c_agec0 c_bhfd0
                   (* cong m ((a*g+e*c)+(b*h+f*d))(0+0) *)
    val re00y = add0_d ZeroC
    val c_Qy_0sum = cong_trans_g (mT, add (add (mult a g)(mult e c))(add (mult b h)(mult f d)), add ZeroC ZeroC, ZeroC)
                      c_Qy_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) re00y)
    val c_Qy0 = cong_trans_g (mT, Qy, add (add (mult a g)(mult e c))(add (mult b h)(mult f d)), ZeroC) c_Qy_re c_Qy_0sum
                (* cong m Qy 0 *)
    val () = out "DIVPNNP_CONG_Y_OK\n";

    (* (4) cong m Pz Qz : Pz=a*h+f*c ; Qz=e*d+b*g.  Both ≡ a*d - b*c.
       correction = b*c.
         Pz + b*c = a*h + (f*c + b*c) = a*h + (f+b)*c ; a*h≡a*d, (f+b)*c≡0 -> ≡ a*d
         Qz + b*c = e*d + (b*g + b*c) = e*d + b*(g+c) ; e*d≡a*d, b*(g+c)≡0 -> ≡ a*d *)
    val corrZ = mult b c
    (* Pz + b*c ≡ a*d *)
    val c_ah_ad = cong_kmult (mT, a, h, d) hcd            (* cong m (a*h)(a*d) *)
    (* f*c + b*c ≡ 0 : f*c+b*c = c*(f+b) = ? flag is f+b ; use c*(f+b) ≡ 0 *)
    val reFC = proveIdentityG (add (mult f c)(mult b c)) (mult c (add f b))   (* f*c+b*c = c*(f+b) *)
    val c_cfb = cong_kmult (mT, c, add f b, ZeroC) hcbR     (* cong m (c*(f+b))(c*0) *)
    val ccz0 = mult0r_d c
    val c_cfb0 = cong_trans_g (mT, mult c (add f b), mult c ZeroC, ZeroC) c_cfb (cong_of_oeq_r (mT, mult c ZeroC, ZeroC) ccz0)
    val c_fcbc0 = cong_trans_g (mT, add (mult f c)(mult b c), mult c (add f b), ZeroC)
                    (cong_of_oeq_r (mT, add (mult f c)(mult b c), mult c (add f b)) reFC) c_cfb0
                  (* cong m (f*c+b*c) 0 *)
    (* Pz + b*c = (a*h + f*c) + b*c ; reassoc to a*h + (f*c + b*c). cong m (Pz+b*c)(a*d+0)=a*d *)
    val rePzC = proveIdentityG (add Pz corrZ) (add (mult a h)(add (mult f c)(mult b c)))  (* (a*h+f*c)+b*c = a*h+(f*c+b*c) *)
    val c_PzC_re = cong_of_oeq_r (mT, add Pz corrZ, add (mult a h)(add (mult f c)(mult b c))) rePzC
    val c_PzC_sum = cong_add_g (mT, mult a h, mult a d, add (mult f c)(mult b c), ZeroC) c_ah_ad c_fcbc0
                    (* cong m (a*h+(f*c+b*c))(a*d+0) *)
    val reAD0 = add0r_d (mult a d)   (* a*d+0 = a*d *)
    val c_PzC_ad = cong_trans_g (mT, add Pz corrZ, add (mult a h)(add (mult f c)(mult b c)), mult a d)
                     c_PzC_re (cong_trans_g (mT, add (mult a h)(add (mult f c)(mult b c)), add (mult a d) ZeroC, mult a d)
                                 c_PzC_sum (cong_of_oeq_r (mT, add (mult a d) ZeroC, mult a d) reAD0))
                   (* cong m (Pz+b*c)(a*d) *)
    (* Qz + b*c ≡ a*d *)
    val c_ed_ad = cong_mult_r (mT, e, a, d, d) hca (cong_refl_g (mT, d))   (* cong m (e*d)(a*d) *)
    val reBG = proveIdentityG (add (mult b g)(mult b c)) (mult b (add g c))   (* b*g+b*c = b*(g+c) *)
    val c_bgc = cong_kmult (mT, b, add g c, ZeroC) hccR    (* cong m (b*(g+c))(b*0) *)
    val cbz0 = mult0r_d b
    val c_bgc0 = cong_trans_g (mT, mult b (add g c), mult b ZeroC, ZeroC) c_bgc (cong_of_oeq_r (mT, mult b ZeroC, ZeroC) cbz0)
    val c_bgbc0 = cong_trans_g (mT, add (mult b g)(mult b c), mult b (add g c), ZeroC)
                    (cong_of_oeq_r (mT, add (mult b g)(mult b c), mult b (add g c)) reBG) c_bgc0
                  (* cong m (b*g+b*c) 0 *)
    val reQzC = proveIdentityG (add Qz corrZ) (add (mult e d)(add (mult b g)(mult b c)))  (* (e*d+b*g)+b*c = e*d+(b*g+b*c) *)
    val c_QzC_re = cong_of_oeq_r (mT, add Qz corrZ, add (mult e d)(add (mult b g)(mult b c))) reQzC
    val c_QzC_sum = cong_add_g (mT, mult e d, mult a d, add (mult b g)(mult b c), ZeroC) c_ed_ad c_bgbc0
                    (* cong m (e*d+(b*g+b*c))(a*d+0) *)
    val reAD0b = add0r_d (mult a d)
    val c_QzC_ad = cong_trans_g (mT, add Qz corrZ, add (mult e d)(add (mult b g)(mult b c)), mult a d)
                     c_QzC_re (cong_trans_g (mT, add (mult e d)(add (mult b g)(mult b c)), add (mult a d) ZeroC, mult a d)
                                 c_QzC_sum (cong_of_oeq_r (mT, add (mult a d) ZeroC, mult a d) reAD0b))
                   (* cong m (Qz+b*c)(a*d) *)
    val c_both_z = cong_trans_g (mT, add Pz corrZ, mult a d, add Qz corrZ) c_PzC_ad (cong_sym_g (mT, add Qz corrZ, mult a d) c_QzC_ad)
                   (* cong m (Pz+b*c)(Qz+b*c) *)
    val c_PzQz = cong_radd_cancel_r (mT, Pz, Qz, corrZ) c_both_z   (* cong m Pz Qz *)
    val () = out "DIVPNNP_CONG_Z_OK\n";

    (* ============ THE DIVIDE (3 pairs + lone Qy) ============ *)
    val goalC = four_sq (mult pT rT)
    val exW = sq_diff_dvd (mT, wP, wQ) c_wPwQ
    val exX = sq_diff_dvd (mT, Px, Qx) c_PxQx
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
        elimSD (Pz,Qz) exZ "sz_d" (fn sz => fn hzEq => fn hzDv =>
          let
            (* L_i = s_i^2 + 2 P_i Q_i ; R_i = P_i^2 + Q_i^2 ; for the lone Qy it stays as Qy^2.
               Pair ORDER in the star fold is (w, x, z) with the lone Qy^2 living
               at the y position of PPsum.  We assemble sumL = Lw + (Lx + (Qy^2 + Lz))
               so the running R-shape Rw + (Rx + (Qy^2 + Rz)) matches PPsum's fold
               (...+ Qx^2 + Qy^2 + Pz^2 + Qz^2). *)
            val Lw = add (sq sw) (add (mult wP wQ)(mult wP wQ))   val Rw = add (sq wP)(sq wQ)
            val Lx = add (sq sx) (add (mult Px Qx)(mult Px Qx))   val Rx = add (sq Px)(sq Qx)
            val Lz = add (sq sz) (add (mult Pz Qz)(mult Pz Qz))   val Rz = add (sq Pz)(sq Qz)
            val Qy2 = sq Qy
            val sumL = add Lw (add Lx (add Qy2 Lz))
            val cong_yz  = add_cong_r_g (Qy2, Lz, Rz) hzEq             (* (Qy^2+Lz)=(Qy^2+Rz) *)
            val cong_x   = add_cong_l_g (Lx, Rx, add Qy2 Lz) hxEq
            val cong_xyz = oeqTrans_g (cong_x, add_cong_r_g (Rx, add Qy2 Lz, add Qy2 Rz) cong_yz)
                           (* (Lx+(Qy^2+Lz))=(Rx+(Qy^2+Rz)) *)
            val cong_w   = add_cong_l_g (Lw, Rw, add Lx (add Qy2 Lz)) hwEq
            val hsumLR = oeqTrans_g (cong_w, add_cong_r_g (Rw, add Lx (add Qy2 Lz), add Rx (add Qy2 Rz)) cong_xyz)
                         (* sumL = Rw + (Rx + (Qy^2 + Rz)) *)
            (* SS = (sw^2 + sx^2) + (Qy^2 + sz^2)  (LEFT-PAIRED to match fourSqBody) ;
               target = SS + Dcross ; sumL = target (proveAddIdentity) *)
            val SS = add (add (sq sw)(sq sx)) (add Qy2 (sq sz))
            val target = add SS Dcross
            val rearr = proveAddIdentity noLeaf sumL target
            (* sumRshape = Rw + (Rx + (Qy^2 + Rz)) ; PPsum = left-folded.  Relate via proveAddIdentity *)
            val sumRshape = add Rw (add Rx (add Qy2 Rz))
            val ppRel = proveAddIdentity noLeaf sumRshape PPsum    (* sumRshape = PPsum *)
            val tEqSumR = oeqTrans_g (oeqSym_g rearr, hsumLR)       (* target = sumRshape *)
            val tEqPP   = oeqTrans_g (tEqSumR, ppRel)               (* target = PPsum *)
            (* star_i : oeq (mn + Dcross) PPsum.  So mn+Dcross = SS+Dcross => mn = SS. *)
            val starEqTarget = oeqTrans_g (star_i, oeqSym_g tEqPP)  (* (mn+Dcross) = (SS+Dcross) *)
            val commL = addcomm_g (mn, Dcross)      (* mn+Dcross = Dcross+mn *)
            val commR = addcomm_g (SS, Dcross)      (* SS+Dcross = Dcross+SS *)
            val flip  = oeqTrans_g (oeqTrans_g (oeqSym_g commL, starEqTarget), commR)  (* Dcross+mn = Dcross+SS *)
            val mnEqSS = alc_g (Dcross, mn, SS) flip   (* mn = SS *)
            val () = out "DIVPNNP_ASSEMBLE_OK\n"

            (* mn = (m*p)*(m*r) = m^2*(p*r) *)
            val Mabcd_mp = oeqSym_r2 hbodyP
            val Mefgh_mr = hsum
            val mn_eq1 = mult_cong_l_g (Mabcd, mp, Mefgh) Mabcd_mp
            val mn_eq2 = mult_cong_r_g (mp, Mefgh, mr) Mefgh_mr
            val mn_mpmr = oeqTrans_g (mn_eq1, mn_eq2)
            val mpmr_id = proveIdentityG (mult mp mr) (mult (mult mT mT) (mult pT rT))
            val mn_msq = oeqTrans_g (mn_mpmr, mpmr_id)       (* mn = m^2*(p*r) *)

            (* dvd m sw,sx,Qy,sz *)
            val dvW = dvd_of_cong_zero (mT, sw) hwDv
            val dvX = dvd_of_cong_zero (mT, sx) hxDv
            val dvY = dvd_of_cong_zero (mT, Qy) c_Qy0   (* the lone Qy *)
            val dvZ = dvd_of_cong_zero (mT, sz) hzDv
            val () = out "DIVPNNP_DVD_OK\n";

            (* extract quotients and build divided sum *)
            fun withQuot (xT, dvx) nm k2 =
              let val Pq = Abs("q", natT, oeq xT (mult mT (Bound 0)))
                  fun bd q (hq:thm) = k2 q hq
              in exE_r (Pq, goalC) dvx nm natT bd end
            val res2 =
              withQuot (sw, dvW) "w0q" (fn w0 => fn hw0 =>
              withQuot (sx, dvX) "sx0q" (fn sx0 => fn hsx0 =>
              withQuot (Qy, dvY) "sy0q" (fn sy0 => fn hsy0 =>
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
                  val sy2e = sqQuot (Qy, sy0, hsy0)   (* Qy^2 = m^2*sy0^2 *)
                  val sz2e = sqQuot (sz, sz0, hsz0)
                  val msq = mult mT mT
                  (* SS = (sw^2 + sx^2) + (Qy^2 + sz^2)  (LEFT-PAIRED) ; rewrite each to m^2*(..) *)
                  val sWX = add_cong_l_g (sq sw, mult msq (sq w0), sq sx) w2e
                  val sWX2 = oeqTrans_g (sWX, add_cong_r_g (mult msq (sq w0), sq sx, mult msq (sq sx0)) sx2e)
                  val sYZ = add_cong_l_g (Qy2, mult msq (sq sy0), sq sz) sy2e
                  val sYZ2 = oeqTrans_g (sYZ, add_cong_r_g (mult msq (sq sy0), sq sz, mult msq (sq sz0)) sz2e)
                  val sAll = oeqTrans_g (add_cong_l_g (add (sq sw)(sq sx), add (mult msq (sq w0))(mult msq (sq sx0)), add Qy2 (sq sz)) sWX2,
                                         add_cong_r_g (add (mult msq (sq w0))(mult msq (sq sx0)), add Qy2 (sq sz), add (mult msq (sq sy0))(mult msq (sq sz0))) sYZ2)
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
val () = out "DIVPNNP_LEAF_DEFINED\n";

(* smoke: run on Frees with assumed hyps (a,d LEFT, b,c RIGHT) *)
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
    val hcd = Thm.assume (ctermGR (jT (cong mF hF dF)));
    val hmPos = Thm.assume (ctermGR (jT (lt ZeroC mF)));
    val r = divide_leaf_pnnp (mF,pF,rF, aF,bF,cF,dF, eF,fF,gF,hF) hbodyP hsum hca hcbR hccR hcd hmPos
  in out ("DIVPNNP_SMOKE hyps="^Int.toString(length(Thm.hyps_of r))
          ^" prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)^"\n") end
  handle e => out ("DIVPNNP_SMOKE FAIL "^exnMessage e^"\n");

val () = out "DIVPNNP_ALL_DONE\n";
