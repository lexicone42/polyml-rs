(* ============================================================================
   FULL (PNPN) DIVIDE LEAF, end-to-end on /tmp/l4_foursq_star.  *** PROVEN ***
   (2026-06-23: DIVPN_SMOKE hyps=7, prop = four_sq (mult p r), Result Tagged(0),
    150,889,327,538 bytecode steps, ~20 min wall on the warm star checkpoint.)

   THE FOURTH fully-proven divide leaf (after ++++, PPPN, PPNN).

   Pattern PNPN: a,c LEFT (cong m e a / g c), b,d RIGHT
                 (cong m (f+b) 0 / cong m (h+d) 0).

   The PNPN star (l4_build_8stars_v2.sml starL_5/starR_5) is a
   "one-component-dropped" shape: Px = 0, so it has THREE cross-pairs
   (wP/wQ, Py/Qy, Pz/Qz) PLUS a LONE square Qx (no Px partner, no Px cross
   term).  Structurally the SAME family as PPNN (which dropped Pz), but here
   the dropped coordinate is X (Px=0) and the lone square is Qx.  The divide
   uses THREE sq_diff_dvd pairs + ONE direct cong-zero square (Qx).

   PNPN witnesses (true-signed = all-positive groupings, b,d are the negative
   coordinates so their residue products fold into wQ / the Py,Qy negative
   groups; verified offline /tmp/check_pnpn_final.py):
     wP = a*e + c*g          wQ = b*f + d*h
     Px = 0                  Qx = ((a*f + e*b) + c*h) + g*d
     Py = a*g + b*h          Qy = e*c + f*d
     Pz = b*g + f*c          Qz = a*h + e*d

   Residue reductions (e=a, f=-b, g=c, h=-d mod m):
     wP ≡ a^2+c^2 , wQ ≡ -(b^2+d^2)  -> cong m wP wQ via +correction (b^2+d^2)
     Qx ≡ 0                          -> cong m Qx 0 directly (the lone square)
     Py ≡ a*c-b*d , Qy ≡ a*c-b*d     -> cong m Py Qy via +correction (b*d)
     Pz ≡ 0 , Qz ≡ 0                 -> cong m Pz 0 and cong m Qz 0

   The divide pipeline (3 sq_diff_dvd pairs -> assemble mn = SS where
   SS = (sw^2+Qx^2)+(sy^2+sz^2) LEFT-PAIRED -> dvd m sw,Qx,sy,sz ->
   divide-by-m^2 via withQuot+proveIdentityG+mult_left_cancel_r ->
   four_sq_witness) is otherwise identical to ++++ / PPPN / PPNN.

   RE-RUN (warm star checkpoint, BIG step budget):
     POLYML_HEAP_BYTES=8000000000 POLYML_GC_THRESHOLD=88 \
       ./target/release/poly run --max-steps 1000000000000 /tmp/l4_foursq_star \
       < divide_leaf_pnpn_delta.sml
   Output: four_sq (mult p r), hyps = the 7 disclosed divide-leaf premises only.
   ============================================================================ *)
val () = restore_l4_context ();
val () = out "DIVPN_BEGIN\n";
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
val () = out "DIVPN_SQDIFF_OK\n";

(* cong helper: from cong m x' x, get cong m (k*x')(k*x) *)
fun cong_kmult (mT, k, xp, x) hflag = cong_mult_r (mT, k, k, xp, x) (cong_refl_g (mT, k)) hflag;

(* ---- THE PNPN LEAF ---- *)
fun divide_leaf_pnpn (mT,pT,rT, a,b,c,d, e,f,g,h)
        hbodyP hsum hca hcbR hcc hcdR hmPos =
  (* hca: cong m e a ; hcbR: cong m (f+b) 0 ; hcc: cong m g c ; hcdR: cong m (h+d) 0 *)
  let
    val mp = mult mT pT  val mr = mult mT rT
    val sumA = add (add (sq a)(sq b))(add (sq c)(sq d))
    val Mabcd = add (add (sq a)(sq b))(add (sq c)(sq d))
    val Mefgh = add (add (sq e)(sq f))(add (sq g)(sq h))
    val mn = mult Mabcd Mefgh
    (* witnesses (3 pairs + lone Qx ; Px = 0) *)
    val wP = add (mult a e)(mult c g)                   val wQ = add (mult b f)(mult d h)
    val Qx = add (add (add (mult a f)(mult e b))(mult c h))(mult g d)   (* the lone square *)
    val Py = add (mult a g)(mult b h)                   val Qy = add (mult e c)(mult f d)
    val Pz = add (mult b g)(mult f c)                   val Qz = add (mult a h)(mult e d)
    (* Dcross = 2*(wP*wQ + Py*Qy + Pz*Qz)  [left-folded as ((wP*wQ + Py*Qy) + Pz*Qz)] *)
    val Dcross = dbl (add (add (mult wP wQ)(mult Py Qy)) (mult Pz Qz))
    val PPsum  = add (add (add (add (add (add (sq wP)(sq wQ))(sq Qx))(sq Py))(sq Qy))(sq Pz))(sq Qz)
    val starL_i = add mn Dcross
    val starR_i = PPsum
    val star_i = proveIdentityG starL_i starR_i
    val () = if (Thm.prop_of star_i) aconv (jT (oeq starL_i starR_i)) then out "DIVPN_STAR_SHAPE_OK\n"
             else raise Fail "star shape"

    (* ============ THE FOUR DIVISIBILITY FACTS ============ *)

    (* (1) cong m wP wQ : wP=a*e+c*g (LEFT) ; wQ=b*f+d*h (RIGHT pair).
       correction = b^2+d^2.
         wP + (b^2+d^2) ≡ (a^2+c^2)+(b^2+d^2) = m*p ≡ 0
         wQ + (b^2+d^2) = (b*f+b^2)+(d*h+d^2) = b*(f+b)+d*(h+d) ≡ 0 *)
    val corrW = add (sq b)(sq d)
    val c_ae = cong_kmult (mT, a, e, a) hca   (* cong m (a*e)(a*a) *)
    val c_cg = cong_kmult (mT, c, g, c) hcc   (* cong m (c*g)(c*c) *)
    val c_wp = cong_add_g (mT, mult a e, sq a, mult c g, sq c) c_ae c_cg  (* cong m wP (a^2+c^2) *)
    val c_wPcorr = cong_add_g (mT, wP, add (sq a)(sq c), corrW, corrW) c_wp (cong_refl_g (mT, corrW))
                   (* cong m (wP+corr) ((a^2+c^2)+(b^2+d^2)) *)
    val reA = proveIdentityG (add (add (sq a)(sq c)) corrW) sumA  (* (a^2+c^2)+(b^2+d^2) = sumA *)
    val c_to_sumA = cong_trans_g (mT, add wP corrW, add (add (sq a)(sq c)) corrW, sumA)
                      c_wPcorr (cong_of_oeq_r (mT, add (add (sq a)(sq c)) corrW, sumA) reA)
    val c_wPcorr_mp = oeq_rw_r (Term.lambda (Free("zq",natT)) (cong mT (add wP corrW) (Free("zq",natT))), sumA, mp)
                        (oeqSym_r2 hbodyP) c_to_sumA   (* cong m (wP+corr)(m*p) *)
    val c_mp0 = (let val z = add0_d mp in cong_introR_r (mT, mp, ZeroC, pT) (oeqSym_r2 z) end)
    val c_wPcorr0 = cong_trans_g (mT, add wP corrW, mp, ZeroC) c_wPcorr_mp c_mp0   (* cong m (wP+corr) 0 *)
    (* wQ + corr = (b*f + d*h) + (b^2 + d^2) ; reassoc to (b*f+b^2) + (d*h+d^2) = b*(f+b) + d*(h+d). *)
    val c_bfb = cong_kmult (mT, b, add f b, ZeroC) hcbR     (* cong m (b*(f+b))(b*0) *)
    val cb0 = mult0r_d b
    val c_bfb0 = cong_trans_g (mT, mult b (add f b), mult b ZeroC, ZeroC) c_bfb (cong_of_oeq_r (mT, mult b ZeroC, ZeroC) cb0) (* cong m (b*(f+b)) 0 *)
    val c_dhd = cong_kmult (mT, d, add h d, ZeroC) hcdR     (* cong m (d*(h+d))(d*0) *)
    val dd0 = mult0r_d d
    val c_dhd0 = cong_trans_g (mT, mult d (add h d), mult d ZeroC, ZeroC) c_dhd (cong_of_oeq_r (mT, mult d ZeroC, ZeroC) dd0) (* cong m (d*(h+d)) 0 *)
    val c_negsum = cong_add_g (mT, mult b (add f b), ZeroC, mult d (add h d), ZeroC) c_bfb0 c_dhd0
                   (* cong m (b*(f+b)+d*(h+d)) (0+0) *)
    val re00 = add0_d ZeroC   (* 0+0 = 0 *)
    val c_negsum0 = cong_trans_g (mT, add (mult b (add f b))(mult d (add h d)), add ZeroC ZeroC, ZeroC)
                      c_negsum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) re00)
                    (* cong m (b*(f+b)+d*(h+d)) 0 *)
    val reWQcorr = proveIdentityG (add wQ corrW) (add (mult b (add f b))(mult d (add h d)))
                   (* (b*f+d*h)+(b^2+d^2) = b*(f+b)+d*(h+d) *)
    val c_wQcorr0 = cong_trans_g (mT, add wQ corrW, add (mult b (add f b))(mult d (add h d)), ZeroC)
                      (cong_of_oeq_r (mT, add wQ corrW, add (mult b (add f b))(mult d (add h d))) reWQcorr) c_negsum0
                    (* cong m (wQ+corr) 0 *)
    val c_both_w = cong_trans_g (mT, add wP corrW, ZeroC, add wQ corrW) c_wPcorr0 (cong_sym_g (mT, add wQ corrW, ZeroC) c_wQcorr0)
                   (* cong m (wP+corr)(wQ+corr) *)
    val c_wPwQ = cong_radd_cancel_r (mT, wP, wQ, corrW) c_both_w   (* cong m wP wQ *)
    val () = out "DIVPN_CONG_W_OK\n";

    (* (2) cong m Qx 0 : Qx=((a*f+e*b)+c*h)+g*d.  ≡0.   (the lone square)
       a*f≡-a*b (f RIGHT), e*b≡a*b (e≡a) -> a*f+e*b ≡ 0
            a*f + a*b = a*(f+b) ≡ 0 ; e*b≡a*b
       c*h≡-c*d (h RIGHT), g*d≡c*d (g≡c) -> c*h+g*d ≡ 0
            c*h + c*d = c*(h+d) ≡ 0 ; g*d≡c*d
       Qx = ((a*f+e*b)+c*h)+g*d ; reassoc to (a*f+e*b)+(c*h+g*d) ≡ 0+0 = 0 *)
    (* a*f+e*b ≡ 0 *)
    val c_eb_ab = cong_mult_r (mT, e, a, b, b) hca (cong_refl_g (mT, b))   (* cong m (e*b)(a*b) *)
    val c_afeb_to = cong_add_g (mT, mult a f, mult a f, mult e b, mult a b) (cong_refl_g (mT, mult a f)) c_eb_ab
                    (* cong m (a*f+e*b)(a*f+a*b) *)
    val reAF = proveIdentityG (add (mult a f)(mult a b)) (mult a (add f b))   (* a*f+a*b = a*(f+b) *)
    val c_afb = cong_kmult (mT, a, add f b, ZeroC) hcbR    (* cong m (a*(f+b))(a*0) *)
    val caf0 = mult0r_d a
    val c_afb0 = cong_trans_g (mT, mult a (add f b), mult a ZeroC, ZeroC) c_afb (cong_of_oeq_r (mT, mult a ZeroC, ZeroC) caf0)
    val c_afab0 = cong_trans_g (mT, add (mult a f)(mult a b), mult a (add f b), ZeroC)
                    (cong_of_oeq_r (mT, add (mult a f)(mult a b), mult a (add f b)) reAF) c_afb0
                  (* cong m (a*f+a*b) 0 *)
    val c_afeb0 = cong_trans_g (mT, add (mult a f)(mult e b), add (mult a f)(mult a b), ZeroC) c_afeb_to c_afab0
                  (* cong m (a*f+e*b) 0 *)
    (* c*h+g*d ≡ 0 *)
    val c_gd_cd = cong_mult_r (mT, g, c, d, d) hcc (cong_refl_g (mT, d))   (* cong m (g*d)(c*d) *)
    val c_chgd_to = cong_add_g (mT, mult c h, mult c h, mult g d, mult c d) (cong_refl_g (mT, mult c h)) c_gd_cd
                    (* cong m (c*h+g*d)(c*h+c*d) *)
    val reCH = proveIdentityG (add (mult c h)(mult c d)) (mult c (add h d))   (* c*h+c*d = c*(h+d) *)
    val c_chd = cong_kmult (mT, c, add h d, ZeroC) hcdR    (* cong m (c*(h+d))(c*0) *)
    val cch0 = mult0r_d c
    val c_chd0 = cong_trans_g (mT, mult c (add h d), mult c ZeroC, ZeroC) c_chd (cong_of_oeq_r (mT, mult c ZeroC, ZeroC) cch0)
    val c_chcd0 = cong_trans_g (mT, add (mult c h)(mult c d), mult c (add h d), ZeroC)
                    (cong_of_oeq_r (mT, add (mult c h)(mult c d), mult c (add h d)) reCH) c_chd0
                  (* cong m (c*h+c*d) 0 *)
    val c_chgd0 = cong_trans_g (mT, add (mult c h)(mult g d), add (mult c h)(mult c d), ZeroC) c_chgd_to c_chcd0
                  (* cong m (c*h+g*d) 0 *)
    (* Qx = ((a*f+e*b)+c*h)+g*d ; reassoc to (a*f+e*b)+(c*h+g*d) *)
    val reQx = proveIdentityG Qx (add (add (mult a f)(mult e b)) (add (mult c h)(mult g d)))
    val c_Qx_re = cong_of_oeq_r (mT, Qx, add (add (mult a f)(mult e b)) (add (mult c h)(mult g d))) reQx
    val c_Qx_sum = cong_add_g (mT, add (mult a f)(mult e b), ZeroC, add (mult c h)(mult g d), ZeroC) c_afeb0 c_chgd0
                   (* cong m ((a*f+e*b)+(c*h+g*d))(0+0) *)
    val re00x = add0_d ZeroC
    val c_Qx_0sum = cong_trans_g (mT, add (add (mult a f)(mult e b))(add (mult c h)(mult g d)), add ZeroC ZeroC, ZeroC)
                      c_Qx_sum (cong_of_oeq_r (mT, add ZeroC ZeroC, ZeroC) re00x)
    val c_Qx0 = cong_trans_g (mT, Qx, add (add (mult a f)(mult e b))(add (mult c h)(mult g d)), ZeroC) c_Qx_re c_Qx_0sum
                (* cong m Qx 0 *)
    val () = out "DIVPN_CONG_X_OK\n";

    (* (3) cong m Py Qy : Py=a*g+b*h ; Qy=e*c+f*d.  Both ≡ a*c - b*d.
       correction = b*d.
         Py + b*d = a*g + (b*h + b*d) = a*g + b*(h+d) ; a*g≡a*c, b*(h+d)≡0 -> ≡ a*c
         Qy + b*d = e*c + (f*d + b*d) = e*c + d*(f+b) ; e*c≡a*c, d*(f+b)≡0 -> ≡ a*c *)
    val corrY = mult b d
    (* Py + b*d ≡ a*c *)
    val c_ag_ac = cong_kmult (mT, a, g, c) hcc            (* cong m (a*g)(a*c) *)
    (* b*h + b*d = b*(h+d) ≡ 0 *)
    val reBH = proveIdentityG (add (mult b h)(mult b d)) (mult b (add h d))   (* b*h+b*d = b*(h+d) *)
    val c_bhd = cong_kmult (mT, b, add h d, ZeroC) hcdR    (* cong m (b*(h+d))(b*0) *)
    val cbh0 = mult0r_d b
    val c_bhd0 = cong_trans_g (mT, mult b (add h d), mult b ZeroC, ZeroC) c_bhd (cong_of_oeq_r (mT, mult b ZeroC, ZeroC) cbh0)
    val c_bhbd0 = cong_trans_g (mT, add (mult b h)(mult b d), mult b (add h d), ZeroC)
                    (cong_of_oeq_r (mT, add (mult b h)(mult b d), mult b (add h d)) reBH) c_bhd0
                  (* cong m (b*h+b*d) 0 *)
    (* Py + b*d = (a*g + b*h) + b*d ; reassoc to a*g + (b*h + b*d). cong m (Py+b*d)(a*c+0)=a*c *)
    val rePyC = proveIdentityG (add Py corrY) (add (mult a g)(add (mult b h)(mult b d)))  (* (a*g+b*h)+b*d = a*g+(b*h+b*d) *)
    val c_PyC_re = cong_of_oeq_r (mT, add Py corrY, add (mult a g)(add (mult b h)(mult b d))) rePyC
    val c_PyC_sum = cong_add_g (mT, mult a g, mult a c, add (mult b h)(mult b d), ZeroC) c_ag_ac c_bhbd0
                    (* cong m (a*g+(b*h+b*d))(a*c+0) *)
    val reAC0 = add0r_d (mult a c)   (* a*c+0 = a*c *)
    val c_PyC_ac = cong_trans_g (mT, add Py corrY, add (mult a g)(add (mult b h)(mult b d)), mult a c)
                     c_PyC_re (cong_trans_g (mT, add (mult a g)(add (mult b h)(mult b d)), add (mult a c) ZeroC, mult a c)
                                 c_PyC_sum (cong_of_oeq_r (mT, add (mult a c) ZeroC, mult a c) reAC0))
                   (* cong m (Py+b*d)(a*c) *)
    (* Qy + b*d ≡ a*c *)
    val c_ec_ac = cong_mult_r (mT, e, a, c, c) hca (cong_refl_g (mT, c))   (* cong m (e*c)(a*c) *)
    val reFD = proveIdentityG (add (mult f d)(mult b d)) (mult d (add f b))   (* f*d+b*d = d*(f+b) *)
    val c_dfb = cong_kmult (mT, d, add f b, ZeroC) hcbR    (* cong m (d*(f+b))(d*0) *)
    val cdf0 = mult0r_d d
    val c_dfb0 = cong_trans_g (mT, mult d (add f b), mult d ZeroC, ZeroC) c_dfb (cong_of_oeq_r (mT, mult d ZeroC, ZeroC) cdf0)
    val c_fdbd0 = cong_trans_g (mT, add (mult f d)(mult b d), mult d (add f b), ZeroC)
                    (cong_of_oeq_r (mT, add (mult f d)(mult b d), mult d (add f b)) reFD) c_dfb0
                  (* cong m (f*d+b*d) 0 *)
    val reQyC = proveIdentityG (add Qy corrY) (add (mult e c)(add (mult f d)(mult b d)))  (* (e*c+f*d)+b*d = e*c+(f*d+b*d) *)
    val c_QyC_re = cong_of_oeq_r (mT, add Qy corrY, add (mult e c)(add (mult f d)(mult b d))) reQyC
    val c_QyC_sum = cong_add_g (mT, mult e c, mult a c, add (mult f d)(mult b d), ZeroC) c_ec_ac c_fdbd0
                    (* cong m (e*c+(f*d+b*d))(a*c+0) *)
    val reAC0b = add0r_d (mult a c)
    val c_QyC_ac = cong_trans_g (mT, add Qy corrY, add (mult e c)(add (mult f d)(mult b d)), mult a c)
                     c_QyC_re (cong_trans_g (mT, add (mult e c)(add (mult f d)(mult b d)), add (mult a c) ZeroC, mult a c)
                                 c_QyC_sum (cong_of_oeq_r (mT, add (mult a c) ZeroC, mult a c) reAC0b))
                   (* cong m (Qy+b*d)(a*c) *)
    val c_both_y = cong_trans_g (mT, add Py corrY, mult a c, add Qy corrY) c_PyC_ac (cong_sym_g (mT, add Qy corrY, mult a c) c_QyC_ac)
                   (* cong m (Py+b*d)(Qy+b*d) *)
    val c_PyQy = cong_radd_cancel_r (mT, Py, Qy, corrY) c_both_y   (* cong m Py Qy *)
    val () = out "DIVPN_CONG_Y_OK\n";

    (* (4) cong m Pz Qz : Pz=b*g+f*c ; Qz=a*h+e*d.  Both ≡ 0.
       Pz: b*g≡b*c (g LEFT), f*c≡-b*c (f RIGHT) -> b*g+f*c ≡ 0.
           b*c + f*c = c*(b+f) ≡ 0 ; b*g≡b*c.  So cong m Pz 0.
       Qz: a*h≡-a*d (h RIGHT), e*d≡a*d (e LEFT) -> a*h+e*d ≡ 0.
           a*h + a*d = a*(h+d) ≡ 0 ; e*d≡a*d.  So cong m Qz 0. *)
    (* cong m Pz 0 : route b*g≡b*c, then b*c+f*c = c*(f+b) ≡ 0  (use f+b to match hcbR) *)
    val c_bg_bc = cong_kmult (mT, b, g, c) hcc            (* cong m (b*g)(b*c) *)
    val c_Pz_to = cong_add_g (mT, mult b g, mult b c, mult f c, mult f c) c_bg_bc (cong_refl_g (mT, mult f c))
                  (* cong m (b*g+f*c)(b*c+f*c) *)
    val reBC = proveIdentityG (add (mult b c)(mult f c)) (mult c (add f b))   (* b*c+f*c = c*(f+b) *)
    val c_cfb = cong_kmult (mT, c, add f b, ZeroC) hcbR    (* cong m (c*(f+b))(c*0) *)
    val ccf0 = mult0r_d c
    val c_cfb0 = cong_trans_g (mT, mult c (add f b), mult c ZeroC, ZeroC) c_cfb (cong_of_oeq_r (mT, mult c ZeroC, ZeroC) ccf0)
    val c_bcfc0 = cong_trans_g (mT, add (mult b c)(mult f c), mult c (add f b), ZeroC)
                    (cong_of_oeq_r (mT, add (mult b c)(mult f c), mult c (add f b)) reBC) c_cfb0
                  (* cong m (b*c+f*c) 0 *)
    val c_Pz0 = cong_trans_g (mT, Pz, add (mult b c)(mult f c), ZeroC) c_Pz_to c_bcfc0   (* cong m Pz 0 *)
    (* cong m Qz 0 : route e*d≡a*d, then a*h+a*d = a*(h+d) ≡ 0 *)
    val c_ed_ad = cong_mult_r (mT, e, a, d, d) hca (cong_refl_g (mT, d))   (* cong m (e*d)(a*d) *)
    val c_Qz_to = cong_add_g (mT, mult a h, mult a h, mult e d, mult a d) (cong_refl_g (mT, mult a h)) c_ed_ad
                  (* cong m (a*h+e*d)(a*h+a*d) *)
    val reAH = proveIdentityG (add (mult a h)(mult a d)) (mult a (add h d))   (* a*h+a*d = a*(h+d) *)
    val c_ahd = cong_kmult (mT, a, add h d, ZeroC) hcdR    (* cong m (a*(h+d))(a*0) *)
    val cah0 = mult0r_d a
    val c_ahd0 = cong_trans_g (mT, mult a (add h d), mult a ZeroC, ZeroC) c_ahd (cong_of_oeq_r (mT, mult a ZeroC, ZeroC) cah0)
    val c_ahad0 = cong_trans_g (mT, add (mult a h)(mult a d), mult a (add h d), ZeroC)
                    (cong_of_oeq_r (mT, add (mult a h)(mult a d), mult a (add h d)) reAH) c_ahd0
                  (* cong m (a*h+a*d) 0 *)
    val c_Qz0 = cong_trans_g (mT, Qz, add (mult a h)(mult a d), ZeroC) c_Qz_to c_ahad0   (* cong m Qz 0 *)
    val c_PzQz = cong_trans_g (mT, Pz, ZeroC, Qz) c_Pz0 (cong_sym_g (mT, Qz, ZeroC) c_Qz0)   (* cong m Pz Qz *)
    val () = out "DIVPN_CONG_Z_OK\n";

    (* ============ THE DIVIDE (3 pairs + lone Qx) ============ *)
    val goalC = four_sq (mult pT rT)
    val exW = sq_diff_dvd (mT, wP, wQ) c_wPwQ
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
       elimSD (Py,Qy) exY "sy_d" (fn sy => fn hyEq => fn hyDv =>
        elimSD (Pz,Qz) exZ "sz_d" (fn sz => fn hzEq => fn hzDv =>
          let
            (* L_i = s_i^2 + 2 P_i Q_i ; R_i = P_i^2 + Q_i^2 ; for the lone Qx it stays as Qx^2.
               ORDER chosen to match SS = (sw^2+Qx^2)+(sy^2+sz^2) LEFT-PAIRED. *)
            val Lw = add (sq sw) (add (mult wP wQ)(mult wP wQ))   val Rw = add (sq wP)(sq wQ)
            val Ly = add (sq sy) (add (mult Py Qy)(mult Py Qy))   val Ry = add (sq Py)(sq Qy)
            val Lz = add (sq sz) (add (mult Pz Qz)(mult Pz Qz))   val Rz = add (sq Pz)(sq Qz)
            val Qx2 = sq Qx
            (* sumL = Lw + (Qx^2 + (Ly + Lz)) ; the corresponding R-shape =
               Rw + (Qx^2 + (Ry + Rz)) ; sumL=this via the three hEq + refl on Qx^2 *)
            val sumL = add Lw (add Qx2 (add Ly Lz))
            val cong_yz  = add_cong_l_g (Ly, Ry, Lz) hyEq                          (* (Ly+Lz)=(Ry+Lz) *)
            val cong_yz2 = oeqTrans_g (cong_yz, add_cong_r_g (Ry, Lz, Rz) hzEq)    (* (Ly+Lz)=(Ry+Rz) *)
            val cong_qx  = add_cong_r_g (Qx2, add Ly Lz, add Ry Rz) cong_yz2        (* (Qx^2+(Ly+Lz))=(Qx^2+(Ry+Rz)) *)
            val cong_w   = add_cong_l_g (Lw, Rw, add Qx2 (add Ly Lz)) hwEq
            val hsumLR = oeqTrans_g (cong_w, add_cong_r_g (Rw, add Qx2 (add Ly Lz), add Qx2 (add Ry Rz)) cong_qx)
                         (* sumL = Rw + (Qx^2 + (Ry + Rz)) *)
            (* SS = (sw^2 + Qx^2) + (sy^2 + sz^2)  (LEFT-PAIRED to match fourSqBody) ;
               target = SS + Dcross ; sumL = target (proveAddIdentity) *)
            val SS = add (add (sq sw) Qx2) (add (sq sy)(sq sz))
            val target = add SS Dcross
            val rearr = proveAddIdentity noLeaf sumL target
            (* sumRshape = Rw + (Qx^2 + (Ry + Rz)) ; PPsum = left-folded.  Relate via proveAddIdentity *)
            val sumRshape = add Rw (add Qx2 (add Ry Rz))
            val ppRel = proveAddIdentity noLeaf sumRshape PPsum    (* sumRshape = PPsum *)
            val tEqSumR = oeqTrans_g (oeqSym_g rearr, hsumLR)       (* target = sumRshape *)
            val tEqPP   = oeqTrans_g (tEqSumR, ppRel)               (* target = PPsum *)
            (* star_i : oeq (mn + Dcross) PPsum.  So mn+Dcross = SS+Dcross => mn = SS. *)
            val starEqTarget = oeqTrans_g (star_i, oeqSym_g tEqPP)  (* (mn+Dcross) = (SS+Dcross) *)
            val commL = addcomm_g (mn, Dcross)      (* mn+Dcross = Dcross+mn *)
            val commR = addcomm_g (SS, Dcross)      (* SS+Dcross = Dcross+SS *)
            val flip  = oeqTrans_g (oeqTrans_g (oeqSym_g commL, starEqTarget), commR)  (* Dcross+mn = Dcross+SS *)
            val mnEqSS = alc_g (Dcross, mn, SS) flip   (* mn = SS *)
            val () = out "DIVPN_ASSEMBLE_OK\n"

            (* mn = (m*p)*(m*r) = m^2*(p*r) *)
            val Mabcd_mp = oeqSym_r2 hbodyP
            val Mefgh_mr = hsum
            val mn_eq1 = mult_cong_l_g (Mabcd, mp, Mefgh) Mabcd_mp
            val mn_eq2 = mult_cong_r_g (mp, Mefgh, mr) Mefgh_mr
            val mn_mpmr = oeqTrans_g (mn_eq1, mn_eq2)
            val mpmr_id = proveIdentityG (mult mp mr) (mult (mult mT mT) (mult pT rT))
            val mn_msq = oeqTrans_g (mn_mpmr, mpmr_id)       (* mn = m^2*(p*r) *)

            (* dvd m sw,Qx,sy,sz *)
            val dvW = dvd_of_cong_zero (mT, sw) hwDv
            val dvX = dvd_of_cong_zero (mT, Qx) c_Qx0   (* the lone Qx *)
            val dvY = dvd_of_cong_zero (mT, sy) hyDv
            val dvZ = dvd_of_cong_zero (mT, sz) hzDv
            val () = out "DIVPN_DVD_OK\n";

            (* extract quotients and build divided sum *)
            fun withQuot (xT, dvx) nm k2 =
              let val Pq = Abs("q", natT, oeq xT (mult mT (Bound 0)))
                  fun bd q (hq:thm) = k2 q hq
              in exE_r (Pq, goalC) dvx nm natT bd end
            val res2 =
              withQuot (sw, dvW) "w0q" (fn w0 => fn hw0 =>
              withQuot (Qx, dvX) "sx0q" (fn sx0 => fn hsx0 =>
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
                  val sx2e = sqQuot (Qx, sx0, hsx0)   (* Qx^2 = m^2*sx0^2 *)
                  val sy2e = sqQuot (sy, sy0, hsy0)
                  val sz2e = sqQuot (sz, sz0, hsz0)
                  val msq = mult mT mT
                  (* SS = (sw^2 + Qx^2) + (sy^2 + sz^2)  (LEFT-PAIRED) ; rewrite each to m^2*(..) *)
                  val sWX = add_cong_l_g (sq sw, mult msq (sq w0), Qx2) w2e
                  val sWX2 = oeqTrans_g (sWX, add_cong_r_g (mult msq (sq w0), Qx2, mult msq (sq sx0)) sx2e)
                  val sYZ = add_cong_l_g (sq sy, mult msq (sq sy0), sq sz) sy2e
                  val sYZ2 = oeqTrans_g (sYZ, add_cong_r_g (mult msq (sq sy0), sq sz, mult msq (sq sz0)) sz2e)
                  val sAll = oeqTrans_g (add_cong_l_g (add (sq sw) Qx2, add (mult msq (sq w0))(mult msq (sq sx0)), add (sq sy)(sq sz)) sWX2,
                                         add_cong_r_g (add (mult msq (sq w0))(mult msq (sq sx0)), add (sq sy)(sq sz), add (mult msq (sq sy0))(mult msq (sq sz0))) sYZ2)
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
val () = out "DIVPN_LEAF_DEFINED\n";

(* smoke: run on Frees with assumed hyps (a,c LEFT, b,d RIGHT) *)
val () =
  let
    val mF=Free("m_n",natT); val pF=Free("p_n",natT); val rF=Free("r_n",natT);
    val aF=Free("a_n",natT); val bF=Free("b_n",natT); val cF=Free("c_n",natT); val dF=Free("d_n",natT);
    val eF=Free("e_n",natT); val fF=Free("f_n",natT); val gF=Free("g_n",natT); val hF=Free("h_n",natT);
    val hbodyP = Thm.assume (ctermGR (jT (oeq (mult mF pF) (add (add (sq aF)(sq bF))(add (sq cF)(sq dF))))));
    val hsum   = Thm.assume (ctermGR (jT (oeq (add (add (sq eF)(sq fF))(add (sq gF)(sq hF))) (mult mF rF))));
    val hca = Thm.assume (ctermGR (jT (cong mF eF aF)));
    val hcbR = Thm.assume (ctermGR (jT (cong mF (add fF bF) ZeroC)));
    val hcc = Thm.assume (ctermGR (jT (cong mF gF cF)));
    val hcdR = Thm.assume (ctermGR (jT (cong mF (add hF dF) ZeroC)));
    val hmPos = Thm.assume (ctermGR (jT (lt ZeroC mF)));
    val r = divide_leaf_pnpn (mF,pF,rF, aF,bF,cF,dF, eF,fF,gF,hF) hbodyP hsum hca hcbR hcc hcdR hmPos
  in out ("DIVPN_SMOKE hyps="^Int.toString(length(Thm.hyps_of r))
          ^" prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)^"\n") end
  handle e => out ("DIVPN_SMOKE FAIL "^exnMessage e^"\n");

val () = out "DIVPN_ALL_DONE\n";
