(* ============================================================================
   FULL (PNPP) DIVIDE LEAF, end-to-end on /tmp/l4_foursq_star.
   A fully-proven divide leaf (after ++++ in divide_leaf_pppp_delta.sml,
   PPPN in divide_leaf_pppn_delta.sml, PPNP in divide_leaf_ppnp_delta.sml).
   Confirms the mixed-sign generalization with the single RIGHT coordinate at
   position b (second), residue f, flag cong m (f+b) 0.

   Pattern PNPP: a,c,d LEFT (cong m e a / g c / h d), b RIGHT (cong m (f+b) 0).
   PNPP witnesses (LEFT-FOLDED, from /tmp/emit_stars.py PNPP s=(1,-1,1,1),
   residue names ap=e, bp=f, cp=g, dp=h):
     wP = (a*e + c*g) + d*h        wQ = b*f
     Px = c*h                      Qx = (a*f + e*b) + g*d
     Py = a*g                      Qy = (e*c + b*h) + f*d
     Pz = (a*h + b*g) + f*c        Qz = e*d

   The RIGHT coordinate is b (residue f, flag cong m (f+b) 0); the correction
   term is b^2 (= bb).  Per-witness mid-values (verified mod m):
     wP/wQ -> m*p   (correction trick: wP+b^2 ≡ m*p ≡ 0 ≡ wQ+b^2)
     Px/Qx -> c*d   (Qx reassoc (a*f+e*b) + g*d; a*f+e*b ≡ 0 via a*(f+b); g*d≡c*d)
     Py/Qy -> a*c   (Qy reassoc e*c + (b*h+f*d); b*h+f*d ≡ 0 via d*(f+b); e*c≡a*c)
     Pz/Qz -> a*d   (Pz reassoc a*h + (b*g+f*c); b*g+f*c ≡ 0 via c*(f+b); a*h≡a*d)

   The star is built CHEAPLY via proveIdentityG starL_i starR_i (NO 13-min
   proveStarFor, NO starV_i checkpoint).  The divide pipeline (sq_diff_dvd x4
   -> assemble mn=SS -> dvd m s_i -> divide-by-m^2 via withQuot +
   proveIdentityG + mult_left_cancel_r -> four_sq_witness) is identical to PPNP.

   IMPORTANT divSum/SS shape: four_sq_witness needs the LEFT-PAIRED RHS
   (sw^2+sx^2)+(sy^2+sz^2) (fourSqBody in _assembled_base.sml).

   RE-RUN (warm star checkpoint, needs a BIG step budget -- the 4-pair
   symmetric divide is heavy; 200e9 is NOT enough):
     POLYML_HEAP_BYTES=8000000000 POLYML_GC_THRESHOLD=88 \
       ./target/release/poly run --max-steps 1000000000000 /tmp/l4_foursq_star \
       < divide_leaf_pnpp_delta.sml
   Output: four_sq (mult p r), hyps = the 7 disclosed divide-leaf premises only.
   ============================================================================ *)
val () = restore_l4_context ();
val () = out "DIVPNPP_BEGIN\n";
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
val () = out "DIVPNPP_SQDIFF_OK\n";

(* cong helper: cong_kmult (m,k,x',x) : from cong m x' x, get cong m (k*x')(k*x) *)
fun cong_kmult (mT, k, xp, x) hflag = cong_mult_r (mT, k, k, xp, x) (cong_refl_g (mT, k)) hflag;

(* ---- THE PNPP LEAF ---- *)
fun divide_leaf_pnpp (mT,pT,rT, a,b,c,d, e,f,g,h)
        hbodyP hsum hca hcbR hcc hcd hmPos =
  (* hca: cong m e a ; hcbR: cong m (f+b) 0 ; hcc: cong m g c ; hcd: cong m h d *)
  let
    val mp = mult mT pT  val mr = mult mT rT
    val sumA = add (add (sq a)(sq b))(add (sq c)(sq d))
    val Mabcd = add (add (sq a)(sq b))(add (sq c)(sq d))
    val Mefgh = add (add (sq e)(sq f))(add (sq g)(sq h))
    val mn = mult Mabcd Mefgh
    (* witnesses (LEFT-FOLDED) *)
    val wP = add (add (mult a e)(mult c g))(mult d h)    val wQ = mult b f
    val Px = mult c h                                     val Qx = add (add (mult a f)(mult e b))(mult g d)
    val Py = mult a g                                     val Qy = add (add (mult e c)(mult b h))(mult f d)
    val Pz = add (add (mult a h)(mult b g))(mult f c)     val Qz = mult e d
    val Dcross = dbl (add (add (add (mult wP wQ) (mult Px Qx)) (mult Py Qy)) (mult Pz Qz))
    val PPsum  = add (add (add (add (add (add (add (sq wP)(sq wQ))(sq Px))(sq Qx))(sq Py))(sq Qy))(sq Pz))(sq Qz)
    val starL_i = add mn Dcross
    val starR_i = PPsum
    (* build the star via proveIdentityG (cheap) *)
    val star_i = proveIdentityG starL_i starR_i
    val () = if (Thm.prop_of star_i) aconv (jT (oeq starL_i starR_i)) then out "DIVPNPP_STAR_SHAPE_OK\n"
             else raise Fail "star shape"

    (* ============ THE FOUR DIVISIBILITY CONGRUENCES ============ *)
    (* cong m wP wQ : wP=(a*e+c*g)+d*h (LEFT) ; wQ=b*f (RIGHT).
       Route: cong m (wP + b^2)(wQ + b^2), cancel b^2.
         wP + b^2 ≡ (a^2+c^2+d^2) + b^2 = m*p
         wQ + b^2 = b*f + b*b = b*(f+b) ≡ b*0 = 0 ≡ m*p  (RIGHT flag) *)
    val bb = sq b
    val c_ae = cong_kmult (mT, a, e, a) hca   (* cong m (a*e)(a*a) *)
    val c_cg = cong_kmult (mT, c, g, c) hcc
    val c_dh = cong_kmult (mT, d, h, d) hcd
    val c_wp1 = cong_add_g (mT, mult a e, sq a, mult c g, sq c) c_ae c_cg
    val c_wp2 = cong_add_g (mT, add (mult a e)(mult c g), add (sq a)(sq c), mult d h, sq d) c_wp1 c_dh
                (* cong m wP ((a^2+c^2)+d^2) *)
    val c_wPbb = cong_add_g (mT, wP, add (add (sq a)(sq c))(sq d), bb, bb) c_wp2 (cong_refl_g (mT, bb))
                 (* cong m (wP+b^2) (((a^2+c^2)+d^2)+b^2) *)
    val reA = proveIdentityG (add (add (add (sq a)(sq c))(sq d)) bb) sumA  (* ((a^2+c^2)+d^2)+b^2 = sumA *)
    val c_to_sumA = cong_trans_g (mT, add wP bb, add (add (add (sq a)(sq c))(sq d)) bb, sumA)
                      c_wPbb (cong_of_oeq_r (mT, add (add (add (sq a)(sq c))(sq d)) bb, sumA) reA)
    val c_wPbb_mp = oeq_rw_r (Term.lambda (Free("zq",natT)) (cong mT (add wP bb) (Free("zq",natT))), sumA, mp)
                      (oeqSym_r2 hbodyP) c_to_sumA   (* cong m (wP+b^2)(m*p) *)
    (* RHS: wQ + b^2 = b*f + b*b = b*(f+b) ; cong m (b*(f+b)) 0 from RIGHT flag *)
    val c_bfb = cong_kmult (mT, b, add f b, ZeroC) hcbR     (* cong m (b*(f+b))(b*0) *)
    val b0 = mult0r_d b                                      (* b*0 = 0 *)
    val c_bfb0 = cong_trans_g (mT, mult b (add f b), mult b ZeroC, ZeroC) c_bfb (cong_of_oeq_r (mT, mult b ZeroC, ZeroC) b0)
                 (* cong m (b*(f+b)) 0 *)
    val reQ = proveIdentityG (add wQ bb) (mult b (add f b))  (* b*f+b^2 = b*(f+b) *)
    val c_wQbb0 = cong_trans_g (mT, add wQ bb, mult b (add f b), ZeroC) (cong_of_oeq_r (mT, add wQ bb, mult b (add f b)) reQ) c_bfb0  (* cong m (wQ+b^2) 0 *)
    val c_mp0 = (let val z = add0_d mp in cong_introR_r (mT, mp, ZeroC, pT) (oeqSym_r2 z) end)
    val c_wPbb0 = cong_trans_g (mT, add wP bb, mp, ZeroC) c_wPbb_mp c_mp0   (* cong m (wP+b^2) 0 *)
    val c_both = cong_trans_g (mT, add wP bb, ZeroC, add wQ bb) c_wPbb0 (cong_sym_g (mT, add wQ bb, ZeroC) c_wQbb0)
                 (* cong m (wP+b^2)(wQ+b^2) *)
    val c_wPwQ = cong_radd_cancel_r (mT, wP, wQ, bb) c_both   (* cong m wP wQ *)
    val () = out "DIVPNPP_CONG_W_OK\n";

    (* cong m Px Qx : Px=c*h ; Qx=(a*f+e*b)+g*d.  Both ≡ c*d.
       Px=c*h ≡ c*d [h≡d].
       Qx mod m: a*f: f RIGHT (f≡-b) -> a*f≡-a*b ; e*b≡a*b [e≡a] ; g*d≡c*d [g≡c].
         a*f+e*b ≡ -a*b+a*b = 0.  Qx ≡ c*d. *)
    val cPx_cd = cong_kmult (mT, c, h, d) hcd            (* cong m (c*h)(c*d) *)
    (* a*f + e*b ≡ 0 : a*f+a*b = a*(f+b)≡0, and e*b≡a*b [e≡a] *)
    val c_eb = cong_mult_r (mT, e, a, b, b) hca (cong_refl_g (mT, b))   (* cong m (e*b)(a*b) *)
    val c_afeb1 = cong_add_g (mT, mult a f, mult a f, mult e b, mult a b) (cong_refl_g (mT, mult a f)) c_eb
                  (* cong m (a*f+e*b)(a*f+a*b) *)
    val reAF = proveIdentityG (add (mult a f)(mult a b)) (mult a (add f b))  (* a*f+a*b = a*(f+b) *)
    val c_afb = cong_kmult (mT, a, add f b, ZeroC) hcbR
    val a0 = mult0r_d a
    val c_afb0 = cong_trans_g (mT, mult a (add f b), mult a ZeroC, ZeroC) c_afb (cong_of_oeq_r (mT, mult a ZeroC, ZeroC) a0)
    val c_afab0 = cong_trans_g (mT, add (mult a f)(mult a b), mult a (add f b), ZeroC) (cong_of_oeq_r (mT, add (mult a f)(mult a b), mult a (add f b)) reAF) c_afb0
    val c_afeb0 = cong_trans_g (mT, add (mult a f)(mult e b), add (mult a f)(mult a b), ZeroC) c_afeb1 c_afab0
                  (* cong m (a*f+e*b) 0 *)
    val c_gd = cong_mult_r (mT, g, c, d, d) hcc (cong_refl_g (mT, d))    (* cong m (g*d)(c*d) *)
    (* Qx = (a*f + e*b) + g*d.  cong m Qx (0 + c*d).  *)
    val c_Qxsum = cong_add_g (mT, add (mult a f)(mult e b), ZeroC, mult g d, mult c d) c_afeb0 c_gd
                  (* cong m Qx (0 + c*d) *)
    val re0CD = add0_d (mult c d)   (* 0 + c*d = c*d *)
    val c_Qx_cd = cong_trans_g (mT, Qx, add ZeroC (mult c d), mult c d) c_Qxsum (cong_of_oeq_r (mT, add ZeroC (mult c d), mult c d) re0CD)
    val c_PxQx = cong_trans_g (mT, Px, mult c d, Qx) cPx_cd (cong_sym_g (mT, Qx, mult c d) c_Qx_cd)
    val () = out "DIVPNPP_CONG_X_OK\n";

    (* cong m Py Qy : Py=a*g ; Qy=(e*c+b*h)+f*d.  Both ≡ a*c.
       Py=a*g ≡ a*c [g≡c].
       Qy mod m: e*c≡a*c [e≡a] ; b*h≡b*d [h≡d] ; f*d: f RIGHT -> f*d≡-b*d.
         b*h+f*d ≡ b*d - b*d = 0.  Qy ≡ a*c. *)
    val cPy_ac = cong_kmult (mT, a, g, c) hcc            (* cong m (a*g)(a*c) *)
    val c_ec = cong_mult_r (mT, e, a, c, c) hca (cong_refl_g (mT, c))     (* cong m (e*c)(a*c) *)
    (* b*h + f*d ≡ 0 : b*h≡b*d [h≡d], and f*d+b*d = (f+b)*d = d*(f+b)≡0 *)
    val c_bh = cong_mult_r (mT, b, b, h, d) (cong_refl_g (mT, b)) hcd   (* cong m (b*h)(b*d) *)
    val c_bhfd1 = cong_add_g (mT, mult b h, mult b d, mult f d, mult f d) c_bh (cong_refl_g (mT, mult f d))
                  (* cong m (b*h+f*d)(b*d+f*d) *)
    val c_dfb = cong_kmult (mT, d, add f b, ZeroC) hcbR    (* cong m (d*(f+b))(d*0) *)
    val d0 = mult0r_d d
    val c_dfb0 = cong_trans_g (mT, mult d (add f b), mult d ZeroC, ZeroC) c_dfb (cong_of_oeq_r (mT, mult d ZeroC, ZeroC) d0)
    val reFD = proveIdentityG (add (mult b d)(mult f d)) (mult d (add f b))  (* b*d+f*d = d*(f+b) *)
    val c_bdfd0 = cong_trans_g (mT, add (mult b d)(mult f d), mult d (add f b), ZeroC) (cong_of_oeq_r (mT, add (mult b d)(mult f d), mult d (add f b)) reFD) c_dfb0
                  (* cong m (b*d+f*d) 0 *)
    val c_bhfd0 = cong_trans_g (mT, add (mult b h)(mult f d), add (mult b d)(mult f d), ZeroC) c_bhfd1 c_bdfd0
                  (* cong m (b*h+f*d) 0 *)
    (* Qy = (e*c + b*h) + f*d.  reassoc to e*c + (b*h+f*d).  cong m Qy (a*c+0)=a*c. *)
    val reQy = proveIdentityG Qy (add (mult e c) (add (mult b h)(mult f d)))
    val c_Qy_re = cong_of_oeq_r (mT, Qy, add (mult e c)(add (mult b h)(mult f d))) reQy
    val c_Qysum = cong_add_g (mT, mult e c, mult a c, add (mult b h)(mult f d), ZeroC) c_ec c_bhfd0
                  (* cong m (e*c+(b*h+f*d))(a*c+0) *)
    val reAC0 = add0r_d (mult a c)   (* (a*c)+0 = a*c *)
    val c_Qy_ac = cong_trans_g (mT, Qy, add (mult e c)(add (mult b h)(mult f d)), mult a c)
                    c_Qy_re (cong_trans_g (mT, add (mult e c)(add (mult b h)(mult f d)), add (mult a c) ZeroC, mult a c)
                              c_Qysum (cong_of_oeq_r (mT, add (mult a c) ZeroC, mult a c) reAC0))
    val c_PyQy = cong_trans_g (mT, Py, mult a c, Qy) cPy_ac (cong_sym_g (mT, Qy, mult a c) c_Qy_ac)
    val () = out "DIVPNPP_CONG_Y_OK\n";

    (* cong m Pz Qz : Pz=(a*h+b*g)+f*c ; Qz=e*d.  Both ≡ a*d.
       Qz=e*d ≡ a*d [e≡a].
       Pz mod m: a*h≡a*d [h≡d] ; b*g≡b*c [g≡c] ; f*c: f RIGHT -> f*c≡-b*c.
         b*g+f*c ≡ b*c - b*c = 0.  Pz ≡ a*d. *)
    val cQz_ad = cong_mult_r (mT, e, a, d, d) hca (cong_refl_g (mT, d))   (* cong m (e*d)(a*d) *)
    val c_ah = cong_kmult (mT, a, h, d) hcd             (* cong m (a*h)(a*d) *)
    (* b*g + f*c ≡ 0 : b*g≡b*c [g≡c], and f*c+b*c = (f+b)*c = c*(f+b)≡0 *)
    val c_bg = cong_mult_r (mT, b, b, g, c) (cong_refl_g (mT, b)) hcc   (* cong m (b*g)(b*c) *)
    val c_bgfc1 = cong_add_g (mT, mult b g, mult b c, mult f c, mult f c) c_bg (cong_refl_g (mT, mult f c))
                  (* cong m (b*g+f*c)(b*c+f*c) *)
    val c_cfb = cong_kmult (mT, c, add f b, ZeroC) hcbR    (* cong m (c*(f+b))(c*0) *)
    val c0 = mult0r_d c
    val c_cfb0 = cong_trans_g (mT, mult c (add f b), mult c ZeroC, ZeroC) c_cfb (cong_of_oeq_r (mT, mult c ZeroC, ZeroC) c0)
    val reFC = proveIdentityG (add (mult b c)(mult f c)) (mult c (add f b))  (* b*c+f*c = c*(f+b) *)
    val c_bcfc0 = cong_trans_g (mT, add (mult b c)(mult f c), mult c (add f b), ZeroC) (cong_of_oeq_r (mT, add (mult b c)(mult f c), mult c (add f b)) reFC) c_cfb0
                  (* cong m (b*c+f*c) 0 *)
    val c_bgfc0 = cong_trans_g (mT, add (mult b g)(mult f c), add (mult b c)(mult f c), ZeroC) c_bgfc1 c_bcfc0
                  (* cong m (b*g+f*c) 0 *)
    (* Pz = (a*h + b*g) + f*c.  reassoc to a*h + (b*g+f*c).  cong m Pz (a*d+0)=a*d. *)
    val rePz = proveIdentityG Pz (add (mult a h) (add (mult b g)(mult f c)))
    val c_Pz_re = cong_of_oeq_r (mT, Pz, add (mult a h)(add (mult b g)(mult f c))) rePz
    val c_Pzsum = cong_add_g (mT, mult a h, mult a d, add (mult b g)(mult f c), ZeroC) c_ah c_bgfc0
                  (* cong m (a*h+(b*g+f*c))(a*d+0) *)
    val reAD0 = add0r_d (mult a d)   (* (a*d)+0 = a*d *)
    val c_Pz_ad = cong_trans_g (mT, Pz, add (mult a h)(add (mult b g)(mult f c)), mult a d)
                    c_Pz_re (cong_trans_g (mT, add (mult a h)(add (mult b g)(mult f c)), add (mult a d) ZeroC, mult a d)
                              c_Pzsum (cong_of_oeq_r (mT, add (mult a d) ZeroC, mult a d) reAD0))
    val c_PzQz = cong_trans_g (mT, Pz, mult a d, Qz) c_Pz_ad (cong_sym_g (mT, Qz, mult a d) cQz_ad)
    val () = out "DIVPNPP_CONG_Z_OK\n";

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
            val () = out "DIVPNPP_ASSEMBLE_OK\n"

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
            val () = out "DIVPNPP_DVD_OK\n";

            (* extract quotients and build divided sum, mirroring PPPP/PPPN/PPNP *)
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
val () = out "DIVPNPP_LEAF_DEFINED\n";

(* smoke: run on Frees with assumed hyps (a,c,d LEFT, b RIGHT) *)
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
    val hcd = Thm.assume (ctermGR (jT (cong mF hF dF)));
    val hmPos = Thm.assume (ctermGR (jT (lt ZeroC mF)));
    val r = divide_leaf_pnpp (mF,pF,rF, aF,bF,cF,dF, eF,fF,gF,hF) hbodyP hsum hca hcbR hcc hcd hmPos
  in out ("DIVPNPP_SMOKE hyps="^Int.toString(length(Thm.hyps_of r))
          ^" prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)^"\n") end
  handle e => out ("DIVPNPP_SMOKE FAIL "^exnMessage e^"\n");

val () = out "DIVPNPP_ALL_DONE\n";
