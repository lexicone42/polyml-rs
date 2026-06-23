(* ============================================================================
   FULL (PPPN) DIVIDE LEAF, end-to-end on /tmp/l4_foursq_star.  *** PROVEN ***
   (2026-06-23: DIVN_SMOKE hyps=7, prop = four_sq (mult p r), Result Tagged(0),
    ~227e9 bytecode steps, ~31 min wall on the warm star checkpoint.)

   THE SECOND fully-proven divide leaf (after the ++++ leaf in
   divide_leaf_pppp_delta.sml).  Confirms the mixed-sign generalization: a leaf
   is a parameterization of the ++++ leaf, differing ONLY in (a) the witness
   groupings (a per-pattern all-positive star, built CHEAPLY here via
   `proveIdentityG starL_1 starR_1` -- NO 13-min proveStarFor, NO need for the
   separate starV_i checkpoints) and (b) the RIGHT-branch flag handling for each
   N coordinate (cong m (x'+x) 0 instead of cong m x' x).

   Pattern PPPN: a,b,c LEFT (cong m e a / f b / g c), d RIGHT (cong m (h+d) 0).
   The PPPN star is FULLY SYMMETRIC (4 sq_diff_dvd pairs, including wP/wQ) --
   structurally CLEANER than ++++ (whose w is a single `cong m w 0`).
   PPPN witnesses (LEFT-FOLDED, match l4_build_8stars_v2.sml starL_1/starR_1):
     wP = (a*e + b*f) + c*g          wQ = d*h
     Px = a*f                        Qx = (e*b + c*h) + g*d
     Py = (a*g + b*h) + f*d          Qy = e*c
     Pz = b*g                        Qz = (a*h + e*d) + f*c

   RIGHT-coordinate congruences use the "+correction" trick: e.g. cong m wP wQ
   via cong m (wP+d^2)(wQ+d^2) then cong_radd_cancel (wP+d^2=(a^2+b^2+c^2)+d^2=
   m*p=0; wQ+d^2=d*(h+d)=0 via the RIGHT flag).  The divide pipeline
   (sq_diff_dvd x4 -> assemble mn=SS -> dvd m s_i -> divide-by-m^2 via
   withQuot+proveIdentityG+mult_left_cancel_r -> four_sq_witness) is otherwise
   identical to ++++.

   IMPORTANT divSum/SS shape: four_sq_witness needs the LEFT-PAIRED RHS
   (a^2+b^2)+(c^2+d^2) (fourSqBody in _assembled_base.sml), so SS and divSum are
   built LEFT-PAIRED (sw^2+sx^2)+(sy^2+sz^2) -- not right-folded.

   RE-RUN (warm star checkpoint, needs a BIG step budget -- the 4-pair symmetric
   divide is heavier than ++++; 200e9 is NOT enough, it cuts off mid-divide):
     POLYML_HEAP_BYTES=8000000000 POLYML_GC_THRESHOLD=88 \
       ./target/release/poly run --max-steps 1000000000000 /tmp/l4_foursq_star \
       < divide_leaf_pppn_delta.sml
   Output: four_sq (mult p r), hyps = the 7 disclosed divide-leaf premises only.
   ============================================================================ *)
val () = restore_l4_context ();
val () = out "DIVN_BEGIN\n";
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
val () = out "DIVN_SQDIFF_OK\n";

(* cong helper: cong_kmult (m,k,x',x) : from cong m x' x, get cong m (k*x')(k*x) *)
fun cong_kmult (mT, k, xp, x) hflag = cong_mult_r (mT, k, k, xp, x) (cong_refl_g (mT, k)) hflag;

(* ---- THE PPPN LEAF ---- *)
fun divide_leaf_pppn (mT,pT,rT, a,b,c,d, e,f,g,h)
        hbodyP hsum hca hcb hcc hcdR hmPos =
  (* hca: cong m e a ; hcb: cong m f b ; hcc: cong m g c ; hcdR: cong m (h+d) 0 *)
  let
    val mp = mult mT pT  val mr = mult mT rT
    val sumA = add (add (sq a)(sq b))(add (sq c)(sq d))
    val Mabcd = add (add (sq a)(sq b))(add (sq c)(sq d))
    val Mefgh = add (add (sq e)(sq f))(add (sq g)(sq h))
    val mn = mult Mabcd Mefgh
    (* witnesses (LEFT-FOLDED, exactly matching starL_1/starR_1) *)
    val wP = add (add (mult a e)(mult b f))(mult c g)   val wQ = mult d h
    val Px = mult a f                                    val Qx = add (add (mult e b)(mult c h))(mult g d)
    val Py = add (add (mult a g)(mult b h))(mult f d)    val Qy = mult e c
    val Pz = mult b g                                    val Qz = add (add (mult a h)(mult e d))(mult f c)
    val Dcross = dbl (add (add (add (mult wP wQ) (mult Px Qx)) (mult Py Qy)) (mult Pz Qz))
    val PPsum  = add (add (add (add (add (add (add (sq wP)(sq wQ))(sq Px))(sq Qx))(sq Py))(sq Qy))(sq Pz))(sq Qz)
    val starL_i = add mn Dcross
    val starR_i = PPsum
    (* build the star via proveIdentityG (cheap) *)
    val star_i = proveIdentityG starL_i starR_i
    val () = if (Thm.prop_of star_i) aconv (jT (oeq starL_i starR_i)) then out "DIVN_STAR_SHAPE_OK\n"
             else raise Fail "star shape"

    (* ============ THE FOUR DIVISIBILITY CONGRUENCES ============ *)
    (* cong m wP wQ : wP=a*e+b*f+c*g (LEFT) ; wQ=d*h (RIGHT).
       Route: cong m (wP + d^2)(wQ + d^2), cancel d^2. *)
    val dd = sq d
    val c_ae = cong_kmult (mT, a, e, a) hca
    val c_bf = cong_kmult (mT, b, f, b) hcb
    val c_cg = cong_kmult (mT, c, g, c) hcc
    val c_wp1 = cong_add_g (mT, mult a e, sq a, mult b f, sq b) c_ae c_bf
    val c_wp2 = cong_add_g (mT, add (mult a e)(mult b f), add (sq a)(sq b), mult c g, sq c) c_wp1 c_cg
    val c_wPdd = cong_add_g (mT, wP, add (add (sq a)(sq b))(sq c), dd, dd) c_wp2 (cong_refl_g (mT, dd))
    val reA = proveIdentityG (add (add (add (sq a)(sq b))(sq c)) dd) sumA
    val c_to_sumA = cong_trans_g (mT, add wP dd, add (add (add (sq a)(sq b))(sq c)) dd, sumA)
                      c_wPdd (cong_of_oeq_r (mT, add (add (add (sq a)(sq b))(sq c)) dd, sumA) reA)
    val c_wPdd_mp = oeq_rw_r (Term.lambda (Free("zq",natT)) (cong mT (add wP dd) (Free("zq",natT))), sumA, mp)
                      (oeqSym_r2 hbodyP) c_to_sumA
    val c_dhd = cong_kmult (mT, d, add h d, ZeroC) hcdR
    val d0 = mult0r_d d
    val c_dhd0 = cong_trans_g (mT, mult d (add h d), mult d ZeroC, ZeroC) c_dhd (cong_of_oeq_r (mT, mult d ZeroC, ZeroC) d0)
    val reQ = proveIdentityG (add wQ dd) (mult d (add h d))
    val c_wQdd0 = cong_trans_g (mT, add wQ dd, mult d (add h d), ZeroC) (cong_of_oeq_r (mT, add wQ dd, mult d (add h d)) reQ) c_dhd0
    val c_mp0 = (let val z = add0_d mp in cong_introR_r (mT, mp, ZeroC, pT) (oeqSym_r2 z) end)
    val c_wPdd0 = cong_trans_g (mT, add wP dd, mp, ZeroC) c_wPdd_mp c_mp0
    val c_both = cong_trans_g (mT, add wP dd, ZeroC, add wQ dd) c_wPdd0 (cong_sym_g (mT, add wQ dd, ZeroC) c_wQdd0)
    val c_wPwQ = cong_radd_cancel_r (mT, wP, wQ, dd) c_both
    val () = out "DIVN_CONG_W_OK\n";

    (* cong m Px Qx : Px=a*f ; Qx=(e*b+c*h)+g*d.  Both ≡ a*b. *)
    val cPx_ab = cong_kmult (mT, a, f, b) hcb            (* cong m (a*f)(a*b) *)
    val c_eb' = cong_mult_r (mT, e, a, b, b) hca (cong_refl_g (mT, b))  (* cong m (e*b)(a*b) *)
    val c_gd  = cong_mult_r (mT, g, c, d, d) hcc (cong_refl_g (mT, d))  (* cong m (g*d)(c*d) *)
    val c_chgd1 = cong_add_g (mT, mult c h, mult c h, mult g d, mult c d) (cong_refl_g (mT, mult c h)) c_gd
    val reCH = proveIdentityG (add (mult c h)(mult c d)) (mult c (add h d))
    val c_chd = cong_kmult (mT, c, add h d, ZeroC) hcdR
    val c0 = mult0r_d c
    val c_chd0 = cong_trans_g (mT, mult c (add h d), mult c ZeroC, ZeroC) c_chd (cong_of_oeq_r (mT, mult c ZeroC, ZeroC) c0)
    val c_chcd0 = cong_trans_g (mT, add (mult c h)(mult c d), mult c (add h d), ZeroC) (cong_of_oeq_r (mT, add (mult c h)(mult c d), mult c (add h d)) reCH) c_chd0
    val c_chgd0 = cong_trans_g (mT, add (mult c h)(mult g d), add (mult c h)(mult c d), ZeroC) c_chgd1 c_chcd0
    val reQx = proveIdentityG Qx (add (mult e b) (add (mult c h)(mult g d)))
    val c_Qx_re = cong_of_oeq_r (mT, Qx, add (mult e b)(add (mult c h)(mult g d))) reQx
    val c_Qxsum = cong_add_g (mT, mult e b, mult a b, add (mult c h)(mult g d), ZeroC) c_eb' c_chgd0
    val reAB0 = add0r_d (mult a b)
    val c_Qx_ab = cong_trans_g (mT, Qx, add (mult e b)(add (mult c h)(mult g d)), mult a b)
                    c_Qx_re (cong_trans_g (mT, add (mult e b)(add (mult c h)(mult g d)), add (mult a b) ZeroC, mult a b)
                              c_Qxsum (cong_of_oeq_r (mT, add (mult a b) ZeroC, mult a b) reAB0))
    val c_PxQx = cong_trans_g (mT, Px, mult a b, Qx) cPx_ab (cong_sym_g (mT, Qx, mult a b) c_Qx_ab)
    val () = out "DIVN_CONG_X_OK\n";

    (* cong m Py Qy : Py=(a*g+b*h)+f*d ; Qy=e*c.  Both ≡ a*c.
       Py mod m: a*g≡a*c [g≡c], b*h: h RIGHT -> b*h≡-b*d, f*d: f≡b -> f*d≡b*d.
         so b*h+f*d ≡ -b*d+b*d = 0.  Py ≡ a*c.
       Qy=e*c ≡ a*c [e≡a]. *)
    val c_ag = cong_mult_r (mT, a, a, g, c) (cong_refl_g (mT, a)) hcc   (* cong m (a*g)(a*c) *)
    (* b*h + f*d ≡ 0 : b*h+b*d = b*(h+d)≡0, and f*d≡b*d [f≡b] *)
    val c_fd = cong_mult_r (mT, f, b, d, d) hcb (cong_refl_g (mT, d))   (* cong m (f*d)(b*d) *)
    val c_bhfd1 = cong_add_g (mT, mult b h, mult b h, mult f d, mult b d) (cong_refl_g (mT, mult b h)) c_fd
                  (* cong m (b*h+f*d)(b*h+b*d) *)
    val reBH = proveIdentityG (add (mult b h)(mult b d)) (mult b (add h d))
    val c_bhd = cong_kmult (mT, b, add h d, ZeroC) hcdR
    val b0 = mult0r_d b
    val c_bhd0 = cong_trans_g (mT, mult b (add h d), mult b ZeroC, ZeroC) c_bhd (cong_of_oeq_r (mT, mult b ZeroC, ZeroC) b0)
    val c_bhbd0 = cong_trans_g (mT, add (mult b h)(mult b d), mult b (add h d), ZeroC) (cong_of_oeq_r (mT, add (mult b h)(mult b d), mult b (add h d)) reBH) c_bhd0
    val c_bhfd0 = cong_trans_g (mT, add (mult b h)(mult f d), add (mult b h)(mult b d), ZeroC) c_bhfd1 c_bhbd0
                  (* cong m (b*h+f*d) 0 *)
    (* Py = (a*g + b*h) + f*d.  reassoc to a*g + (b*h+f*d). cong m Py (a*c+0)=a*c. *)
    val rePy = proveIdentityG Py (add (mult a g)(add (mult b h)(mult f d)))
    val c_Py_re = cong_of_oeq_r (mT, Py, add (mult a g)(add (mult b h)(mult f d))) rePy
    val c_Pysum = cong_add_g (mT, mult a g, mult a c, add (mult b h)(mult f d), ZeroC) c_ag c_bhfd0
                  (* cong m (a*g+(b*h+f*d))(a*c+0) *)
    val reAC0 = add0r_d (mult a c)
    val c_Py_ac = cong_trans_g (mT, Py, add (mult a g)(add (mult b h)(mult f d)), mult a c)
                    c_Py_re (cong_trans_g (mT, add (mult a g)(add (mult b h)(mult f d)), add (mult a c) ZeroC, mult a c)
                              c_Pysum (cong_of_oeq_r (mT, add (mult a c) ZeroC, mult a c) reAC0))
    val cQy_ac = cong_mult_r (mT, e, a, c, c) hca (cong_refl_g (mT, c))   (* cong m (e*c)(a*c) *)
    val c_PyQy = cong_trans_g (mT, Py, mult a c, Qy) c_Py_ac (cong_sym_g (mT, Qy, mult a c) cQy_ac)
    val () = out "DIVN_CONG_Y_OK\n";

    (* cong m Pz Qz : Pz=b*g ; Qz=(a*h+e*d)+f*c.  Both ≡ b*c.
       Pz=b*g ≡ b*c [g≡c].
       Qz mod m: a*h: h RIGHT -> a*h≡-a*d ; e*d: e≡a -> e*d≡a*d ; f*c: f≡b -> f*c≡b*c.
         a*h+e*d ≡ -a*d+a*d = 0.  Qz ≡ b*c. *)
    val cPz_bc = cong_mult_r (mT, b, b, g, c) (cong_refl_g (mT, b)) hcc   (* cong m (b*g)(b*c) *)
    (* a*h + e*d ≡ 0 : a*h+a*d=a*(h+d)≡0, and e*d≡a*d [e≡a] *)
    val c_ed = cong_mult_r (mT, e, a, d, d) hca (cong_refl_g (mT, d))     (* cong m (e*d)(a*d) *)
    val c_ahed1 = cong_add_g (mT, mult a h, mult a h, mult e d, mult a d) (cong_refl_g (mT, mult a h)) c_ed
                  (* cong m (a*h+e*d)(a*h+a*d) *)
    val reAH = proveIdentityG (add (mult a h)(mult a d)) (mult a (add h d))
    val c_ahd = cong_kmult (mT, a, add h d, ZeroC) hcdR
    val a0 = mult0r_d a
    val c_ahd0 = cong_trans_g (mT, mult a (add h d), mult a ZeroC, ZeroC) c_ahd (cong_of_oeq_r (mT, mult a ZeroC, ZeroC) a0)
    val c_ahad0 = cong_trans_g (mT, add (mult a h)(mult a d), mult a (add h d), ZeroC) (cong_of_oeq_r (mT, add (mult a h)(mult a d), mult a (add h d)) reAH) c_ahd0
    val c_ahed0 = cong_trans_g (mT, add (mult a h)(mult e d), add (mult a h)(mult a d), ZeroC) c_ahed1 c_ahad0
                  (* cong m (a*h+e*d) 0 *)
    (* Qz = (a*h + e*d) + f*c.  cong m Qz ((a*h+e*d) + f*c).  f*c≡b*c. *)
    val c_fc = cong_mult_r (mT, f, b, c, c) hcb (cong_refl_g (mT, c))    (* cong m (f*c)(b*c) *)
    val c_Qzsum = cong_add_g (mT, add (mult a h)(mult e d), ZeroC, mult f c, mult b c) c_ahed0 c_fc
                  (* cong m Qz (0 + b*c) *)
    val re0BC = add0_d (mult b c)   (* 0 + b*c = b*c *)
    val c_Qz_bc = cong_trans_g (mT, Qz, add ZeroC (mult b c), mult b c) c_Qzsum (cong_of_oeq_r (mT, add ZeroC (mult b c), mult b c) re0BC)
    val c_PzQz = cong_trans_g (mT, Pz, mult b c, Qz) cPz_bc (cong_sym_g (mT, Qz, mult b c) c_Qz_bc)
    val () = out "DIVN_CONG_Z_OK\n";

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
            (* sumL = Lw + (Lx + (Ly + Lz)) ; sumR = Rw + (Rx + (Ry + Rz)) ; sumL=sumR (each hEq) *)
            val sumL = add Lw (add Lx (add Ly Lz))
            (* chain congruences pairing each L_i->R_i *)
            val cong_yz  = add_cong_l_g (Ly, Ry, Lz) hyEq
            val cong_yz2 = oeqTrans_g (cong_yz, add_cong_r_g (Ry, Lz, Rz) hzEq)            (* (Ly+Lz)=(Ry+Rz) *)
            val cong_x   = add_cong_l_g (Lx, Rx, add Ly Lz) hxEq
            val cong_xyz = oeqTrans_g (cong_x, add_cong_r_g (Rx, add Ly Lz, add Ry Rz) cong_yz2) (* (Lx+(Ly+Lz))=(Rx+(Ry+Rz)) *)
            val cong_w   = add_cong_l_g (Lw, Rw, add Lx (add Ly Lz)) hwEq
            val hsumLR = oeqTrans_g (cong_w, add_cong_r_g (Rw, add Lx (add Ly Lz), add Rx (add Ry Rz)) cong_xyz)
                         (* sumL = Rw + (Rx + (Ry + Rz)) *)
            (* SS = (sw^2 + sx^2) + (sy^2 + sz^2)  (LEFT-PAIRED to match fourSqBody) ;
               target = SS + Dcross ; sumL = target (proveAddIdentity) *)
            val SS = add (add (sq sw)(sq sx)) (add (sq sy)(sq sz))
            val target = add SS Dcross
            val rearr = proveAddIdentity noLeaf sumL target
            (* sumR shape = Rw + (Rx + (Ry + Rz)) ; PPsum is the left-folded sum.  Relate via proveAddIdentity *)
            val sumRshape = add Rw (add Rx (add Ry Rz))
            val ppRel = proveAddIdentity noLeaf sumRshape PPsum    (* (Rw+(Rx+(Ry+Rz))) = PPsum *)
            (* hSS : SS + Dcross = PPsum  i.e.  target = PPsum *)
            val tEqSumR = oeqTrans_g (oeqSym_g rearr, hsumLR)       (* target = sumRshape *)
            val tEqPP   = oeqTrans_g (tEqSumR, ppRel)               (* target = PPsum *)
            (* star_i : oeq (mn + Dcross) PPsum.  So mn + Dcross = SS + Dcross => mn = SS. *)
            val starEqTarget = oeqTrans_g (star_i, oeqSym_g tEqPP)  (* (mn+Dcross) = (SS+Dcross) *)
            (* cancel Dcross on the right: addcomm then alc_g *)
            val commL = addcomm_g (mn, Dcross)      (* mn+Dcross = Dcross+mn *)
            val commR = addcomm_g (SS, Dcross)      (* SS+Dcross = Dcross+SS *)
            val flip  = oeqTrans_g (oeqTrans_g (oeqSym_g commL, starEqTarget), commR)  (* Dcross+mn = Dcross+SS *)
            val mnEqSS = alc_g (Dcross, mn, SS) flip   (* mn = SS *)
            val () = out "DIVN_ASSEMBLE_OK\n"

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
            val () = out "DIVN_DVD_OK\n";

            (* extract quotients and build divided sum, mirroring PPPP *)
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
                  (* SS = (sw^2 + sx^2) + (sy^2 + sz^2)  (LEFT-PAIRED) ; rewrite each to m^2*(..) *)
                  val sWX = add_cong_l_g (sq sw, mult msq (sq w0), sq sx) w2e
                  val sWX2 = oeqTrans_g (sWX, add_cong_r_g (mult msq (sq w0), sq sx, mult msq (sq sx0)) sx2e)
                  val sYZ = add_cong_l_g (sq sy, mult msq (sq sy0), sq sz) sy2e
                  val sYZ2 = oeqTrans_g (sYZ, add_cong_r_g (mult msq (sq sy0), sq sz, mult msq (sq sz0)) sz2e)
                  val sAll = oeqTrans_g (add_cong_l_g (add (sq sw)(sq sx), add (mult msq (sq w0))(mult msq (sq sx0)), add (sq sy)(sq sz)) sWX2,
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
          in res2 end))))
  in res end;
val () = out "DIVN_LEAF_DEFINED\n";

(* smoke: run on Frees with assumed hyps (a,b,c LEFT, d RIGHT) *)
val () =
  let
    val mF=Free("m_n",natT); val pF=Free("p_n",natT); val rF=Free("r_n",natT);
    val aF=Free("a_n",natT); val bF=Free("b_n",natT); val cF=Free("c_n",natT); val dF=Free("d_n",natT);
    val eF=Free("e_n",natT); val fF=Free("f_n",natT); val gF=Free("g_n",natT); val hF=Free("h_n",natT);
    val hbodyP = Thm.assume (ctermGR (jT (oeq (mult mF pF) (add (add (sq aF)(sq bF))(add (sq cF)(sq dF))))));
    val hsum   = Thm.assume (ctermGR (jT (oeq (add (add (sq eF)(sq fF))(add (sq gF)(sq hF))) (mult mF rF))));
    val hca = Thm.assume (ctermGR (jT (cong mF eF aF)));
    val hcb = Thm.assume (ctermGR (jT (cong mF fF bF)));
    val hcc = Thm.assume (ctermGR (jT (cong mF gF cF)));
    val hcdR = Thm.assume (ctermGR (jT (cong mF (add hF dF) ZeroC)));
    val hmPos = Thm.assume (ctermGR (jT (lt ZeroC mF)));
    val r = divide_leaf_pppn (mF,pF,rF, aF,bF,cF,dF, eF,fF,gF,hF) hbodyP hsum hca hcb hcc hcdR hmPos
  in out ("DIVN_SMOKE hyps="^Int.toString(length(Thm.hyps_of r))
          ^" prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)^"\n") end
  handle e => out ("DIVN_SMOKE FAIL "^exnMessage e^"\n");

val () = out "DIVN_ALL_DONE\n";
