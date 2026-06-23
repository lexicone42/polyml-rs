(* ============================================================================
   FULL (++++) DIVIDE LEAF, end-to-end on the star checkpoint.
   Inputs (uniform LEFT orientation):
     a,b,c,d (orig rep coords), e,f,g,h (residues = a',b',c',d'), p, r
     hbodyP : oeq (m*p) (a^2+b^2+c^2+d^2)
     hsum   : oeq (e^2+f^2+g^2+h^2) (m*r)
     hca: cong m e a, hcb: cong m f b, hcc: cong m g c, hcd: cong m h d
     hmPos  : lt 0 m
   Output: four_sq (mult p r).
   ============================================================================ *)
val () = restore_l4_context ();
val () = out "DIVF_BEGIN\n";
fun sq x = mult x x;
fun dbl t = add t t;

(* ---- starFast (reuse banked star_v) ---- *)
fun starFast (a,b,c,d,e,f,g,h) =
  beta_norm (Drule.infer_instantiate ctxtGR
    [(("sa_v",0),ctermGR a),(("sb_v",0),ctermGR b),(("sc_v",0),ctermGR c),(("sd_v",0),ctermGR d),
     (("se_v",0),ctermGR e),(("sf_v",0),ctermGR f),(("sg_v",0),ctermGR g),(("sh_v",0),ctermGR h)] star_v);

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
val () = out "DIVF_HELPERS_OK\n";

(* witness builders *)
fun mkMt (a,b,c,d) = add (add (mult a a)(mult b b)) (add (mult c c)(mult d d));
fun mkWt (a,b,c,d,e,f,g,h) = add (add (mult a e)(mult b f)) (add (mult c g)(mult d h));
fun mkPxt (a,b,c,d,e,f,g,h) = add (mult a f)(mult c h);  fun mkQxt (a,b,c,d,e,f,g,h) = add (mult b e)(mult d g);
fun mkPyt (a,b,c,d,e,f,g,h) = add (mult a g)(mult d f);  fun mkQyt (a,b,c,d,e,f,g,h) = add (mult b h)(mult c e);
fun mkPzt (a,b,c,d,e,f,g,h) = add (mult a h)(mult b g);  fun mkQzt (a,b,c,d,e,f,g,h) = add (mult c f)(mult d e);

(* dvd-from-cong-zero + square + cancel helpers (reuse seat1) *)
(* dvd_of_cong_zero (m,x) : cong m x 0 ==> dvd m x  [= EX k. x=m*k] *)
(* m | x  AND  m | y ... we want x^2+y^2+... = m^2 * (...). Use dvd_msq_of_dvd_m + sum + cancel. *)

(* sum-of-4-squares divide:
   given dvd m w, dvd m sx, dvd m sy, dvd m sz, and
     hMN : oeq mn (w^2+sx^2+sy^2+sz^2)   [mn = (m*p)*(m*r)]
   and  mn = m^2*(p*r)   (proveIdentityG on (m*p)*(m*r) = (m*m)*(p*r))
   produce four_sq (p*r). *)
val () = out "DIVF_PHASE_SETUP_OK\n";

(* ---- THE LEAF (parameterised; called on Frees for the template proof) ---- *)
fun divide_leaf_pppp (mT,pT,rT, a,b,c,d, e,f,g,h)
        hbodyP hsum hca hcb hcc hcd hmPos =
  let
    val mp = mult mT pT
    val mr = mult mT rT
    val sumA = add (add (sq a)(sq b))(add (sq c)(sq d))   (* a^2+b^2+c^2+d^2 = m*p *)
    val sumE = add (add (sq e)(sq f))(add (sq g)(sq h))   (* e^2+f^2+g^2+h^2 = m*r *)
    val Mabcd = mkMt (a,b,c,d)   (* = sumA *)
    val Mefgh = mkMt (e,f,g,h)   (* = sumE *)
    val wT  = mkWt (a,b,c,d,e,f,g,h)
    val Px = mkPxt (a,b,c,d,e,f,g,h)  val Qx = mkQxt (a,b,c,d,e,f,g,h)
    val Py = mkPyt (a,b,c,d,e,f,g,h)  val Qy = mkQyt (a,b,c,d,e,f,g,h)
    val Pz = mkPzt (a,b,c,d,e,f,g,h)  val Qz = mkQzt (a,b,c,d,e,f,g,h)
    val mn = mult Mabcd Mefgh
    val XCross = add (mult Px Qx) (add (mult Py Qy) (mult Pz Qz))
    val Dcross = add XCross XCross
    val PPsum  = add (add (sq Px)(sq Qx)) (add (add (sq Py)(sq Qy)) (add (sq Pz)(sq Qz)))
    val starL_i = add mn Dcross
    val starR_i = add (sq wT) PPsum
    val star_i = starFast (a,b,c,d,e,f,g,h)
    val () = if (Thm.prop_of star_i) aconv (jT (oeq starL_i starR_i)) then out "DIVF_STAR_SHAPE_OK\n"
             else (out ("DIVF_STAR GOT  "^Syntax.string_of_term ctxtGR (Thm.prop_of star_i)^"\n");
                   out ("DIVF_STAR WANT "^Syntax.string_of_term ctxtGR (jT (oeq starL_i starR_i))^"\n");
                   raise Fail "star shape")

    (* cong m w 0 *)
    val c_ae = cong_mult_r (mT, a, a, e, a) (cong_refl_g (mT, a)) hca
    val c_bf = cong_mult_r (mT, b, b, f, b) (cong_refl_g (mT, b)) hcb
    val c_cg = cong_mult_r (mT, c, c, g, c) (cong_refl_g (mT, c)) hcc
    val c_dh = cong_mult_r (mT, d, d, h, d) (cong_refl_g (mT, d)) hcd
    val c_ab = cong_add_g (mT, mult a e, sq a, mult b f, sq b) c_ae c_bf
    val c_cd = cong_add_g (mT, mult c g, sq c, mult d h, sq d) c_cg c_dh
    val c_w_sum = cong_add_g (mT, add (mult a e)(mult b f), add (sq a)(sq b),
                                  add (mult c g)(mult d h), add (sq c)(sq d)) c_ab c_cd  (* cong m w sumA *)
    val c_w_mp = oeq_rw_r (Term.lambda (Free("zwm",natT)) (cong mT wT (Free("zwm",natT))), sumA, mp)
                   (oeqSym_r2 hbodyP) c_w_sum         (* cong m w (m*p) *)
    val c_mp0 = (let val z = add0_d mp in cong_introR_r (mT, mp, ZeroC, pT) (oeqSym_r2 z) end)
    val c_w0 = cong_trans_g (mT, wT, mp, ZeroC) c_w_mp c_mp0   (* cong m w 0 *)

    (* cong m Px Qx (and Py Qy, Pz Qz) *)
    fun congPQ (P,Q,pterm1a,pterm1b,pterm2a,pterm2b, ca,cb, midL,midR) =
      (* generic: cong m P midL, cong m Q midR, oeq midL midR -> cong m P Q *)
      let val cId = cong_of_oeq_r (mT, midL, midR) (proveIdentityG midL midR)
          val cP = ca  (* cong m P midL *)
          val s1 = cong_trans_g (mT, P, midL, midR) cP cId
      in cong_trans_g (mT, P, midR, Q) s1 (cong_sym_g (mT, Q, midR) cb) end
    (* Px=a*f+c*h ≡ a*b+c*d ; Qx=b*e+d*g ≡ b*a+d*c *)
    val c_af = cong_mult_r (mT, a, a, f, b) (cong_refl_g (mT, a)) hcb
    val c_ch = cong_mult_r (mT, c, c, h, d) (cong_refl_g (mT, c)) hcd
    val cPx_mid = cong_add_g (mT, mult a f, mult a b, mult c h, mult c d) c_af c_ch  (* cong m Px (ab+cd) *)
    val c_be = cong_mult_r (mT, b, b, e, a) (cong_refl_g (mT, b)) hca
    val c_dg = cong_mult_r (mT, d, d, g, c) (cong_refl_g (mT, d)) hcc
    val cQx_mid = cong_add_g (mT, mult b e, mult b a, mult d g, mult d c) c_be c_dg  (* cong m Qx (ba+dc) *)
    val c_PxQx = congPQ (Px,Qx,a,f,c,h, cPx_mid, cQx_mid, add (mult a b)(mult c d), add (mult b a)(mult d c))
    (* Py=a*g+d*f ≡ a*c+d*b ; Qy=b*h+c*e ≡ b*d+c*a *)
    val c_ag = cong_mult_r (mT, a, a, g, c) (cong_refl_g (mT, a)) hcc
    val c_df = cong_mult_r (mT, d, d, f, b) (cong_refl_g (mT, d)) hcb
    val cPy_mid = cong_add_g (mT, mult a g, mult a c, mult d f, mult d b) c_ag c_df
    val c_bh = cong_mult_r (mT, b, b, h, d) (cong_refl_g (mT, b)) hcd
    val c_ce = cong_mult_r (mT, c, c, e, a) (cong_refl_g (mT, c)) hca
    val cQy_mid = cong_add_g (mT, mult b h, mult b d, mult c e, mult c a) c_bh c_ce
    val c_PyQy = congPQ (Py,Qy,a,g,d,f, cPy_mid, cQy_mid, add (mult a c)(mult d b), add (mult b d)(mult c a))
    (* Pz=a*h+b*g ≡ a*d+b*c ; Qz=c*f+d*e ≡ c*b+d*a *)
    val c_ah = cong_mult_r (mT, a, a, h, d) (cong_refl_g (mT, a)) hcd
    val c_bg = cong_mult_r (mT, b, b, g, c) (cong_refl_g (mT, b)) hcc
    val cPz_mid = cong_add_g (mT, mult a h, mult a d, mult b g, mult b c) c_ah c_bg
    val c_cf = cong_mult_r (mT, c, c, f, b) (cong_refl_g (mT, c)) hcb
    val c_de = cong_mult_r (mT, d, d, e, a) (cong_refl_g (mT, d)) hca
    val cQz_mid = cong_add_g (mT, mult c f, mult c b, mult d e, mult d a) c_cf c_de
    val c_PzQz = congPQ (Pz,Qz,a,h,b,g, cPz_mid, cQz_mid, add (mult a d)(mult b c), add (mult c b)(mult d a))
    val () = out "DIVF_CONGS_OK\n";

    (* sq_diff_dvd for x,y,z : eliminate to get sx,sy,sz with both facts *)
    val goalC = four_sq (mult pT rT)
    val exX = sq_diff_dvd (mT, Px, Qx) c_PxQx
    val exY = sq_diff_dvd (mT, Py, Qy) c_PyQy
    val exZ = sq_diff_dvd (mT, Pz, Qz) c_PzQz
    fun elimSD (P,Q) ex nm goalC k =
      let val Pp = sqDiffDvdPred (mT,P,Q)
          fun bd s (hbody:thm) =
            let val hEq = conjunct1_r (oeq (add (sq s)(dbl (mult P Q))) (add (sq P)(sq Q)), cong mT s ZeroC) hbody
                val hDv = conjunct2_r (oeq (add (sq s)(dbl (mult P Q))) (add (sq P)(sq Q)), cong mT s ZeroC) hbody
            in k s hEq hDv end
      in exE_r (Pp, goalC) ex nm natT bd end

    val res =
      elimSD (Px,Qx) exX "sx_d" goalC (fn sx => fn hxEq => fn hxDv =>
        elimSD (Py,Qy) exY "sy_d" goalC (fn sy => fn hyEq => fn hyDv =>
          elimSD (Pz,Qz) exZ "sz_d" goalC (fn sz => fn hzEq => fn hzDv =>
            let
              (* assemble mn = w^2 + sx^2 + sy^2 + sz^2  (mirror multiplicativityBody.assemble) *)
              val Lx = add (sq sx) (add (mult Px Qx)(mult Px Qx))   val Rx = add (sq Px)(sq Qx)
              val Ly = add (sq sy) (add (mult Py Qy)(mult Py Qy))   val Ry = add (sq Py)(sq Qy)
              val Lz = add (sq sz) (add (mult Pz Qz)(mult Pz Qz))   val Rz = add (sq Pz)(sq Qz)
              (* hxEq : oeq (sx^2 + 2*Px*Qx)(Px^2+Qx^2)  but my dbl is add t t = Px*Qx+Px*Qx; Lx uses that *)
              val sumL = add Lx (add Ly Lz)
              val cong_yz  = add_cong_l_g (Ly, Ry, Lz) hyEq
              val cong_yz2 = oeqTrans_g (cong_yz, add_cong_r_g (Ry, Lz, Rz) hzEq)
              val cong_x   = add_cong_l_g (Lx, Rx, add Ly Lz) hxEq
              val hsum2 = oeqTrans_g (cong_x, add_cong_r_g (Rx, add Ly Lz, add Ry Rz) cong_yz2)
              val SS = add (sq sx) (add (sq sy)(sq sz))
              val target = add SS Dcross
              val rearr = proveAddIdentity noLeaf sumL target
              val hSS = oeqTrans_g (oeqSym_g rearr, hsum2)
              val starRrew = add_cong_r_g (sq wT, PPsum, add SS Dcross) (oeqSym_g hSS)
              val chain1 = oeqTrans_g (star_i, starRrew)
              val assocBk = oeqSym_g (addassoc_g (sq wT, SS, Dcross))
              val chain2 = oeqTrans_g (chain1, assocBk)
              val wSS = add (sq wT) SS
              val commL = addcomm_g (mn, Dcross)
              val commR = addcomm_g (wSS, Dcross)
              val flip  = oeqTrans_g (oeqTrans_g (oeqSym_g commL, chain2), commR)
              val canc  = alc_g (Dcross, mn, wSS) flip       (* oeq mn (w^2+SS) *)
              val fsShape = add (add (sq wT)(sq sx)) (add (sq sy)(sq sz))
              val reshape = proveAddIdentity noLeaf wSS fsShape
              val bodyEq = oeqTrans_g (canc, reshape)         (* oeq mn (w^2+sx^2+sy^2+sz^2) *)
              val () = out "DIVF_ASSEMBLE_OK\n"

              (* mn = (m*p)*(m*r) : Mabcd=sumA=m*p (hbodyP sym), Mefgh=sumE; sumE=m*r (hsum) *)
              (* Mabcd = m*p : hbodyP : m*p = sumA = Mabcd ; so Mabcd = m*p (sym) *)
              val Mabcd_mp = oeqSym_r2 hbodyP                 (* Mabcd(=sumA) = m*p *)
              val Mefgh_mr = hsum                              (* Mefgh(=sumE) = m*r *)
              val mn_eq1 = mult_cong_l_g (Mabcd, mp, Mefgh) Mabcd_mp   (* mn = (m*p)*Mefgh *)
              val mn_eq2 = mult_cong_r_g (mp, Mefgh, mr) Mefgh_mr      (* (m*p)*Mefgh = (m*p)*(m*r) *)
              val mn_mpmr = oeqTrans_g (mn_eq1, mn_eq2)        (* mn = (m*p)*(m*r) *)
              (* (m*p)*(m*r) = (m*m)*(p*r) *)
              val mpmr_id = proveIdentityG (mult mp mr) (mult (mult mT mT) (mult pT rT))
              val mn_msq = oeqTrans_g (mn_mpmr, mpmr_id)       (* mn = m^2*(p*r) *)

              (* dvd m w, sx, sy, sz *)
              val dvW  = dvd_of_cong_zero (mT, wT) c_w0    (* dvd m w *)
              val dvX  = dvd_of_cong_zero (mT, sx) hxDv
              val dvY  = dvd_of_cong_zero (mT, sy) hyDv
              val dvZ  = dvd_of_cong_zero (mT, sz) hzDv
              (* dvd m^2 (w^2) etc *)
              val dvW2 = dvd_msq_of_dvd_m (mT, wT) dvW
              val dvX2 = dvd_msq_of_dvd_m (mT, sx) dvX
              val dvY2 = dvd_msq_of_dvd_m (mT, sy) dvY
              val dvZ2 = dvd_msq_of_dvd_m (mT, sz) dvZ
              (* dvd m^2 (w^2+sx^2+sy^2+sz^2) *)
              val dvWX = dvd_add_r (mult mT mT, sq wT, sq sx) dvW2 dvX2
              val dvYZ = dvd_add_r (mult mT mT, sq sy, sq sz) dvY2 dvZ2
              (* the sum shape from bodyEq RHS is ((w^2+sx^2)+(sy^2+sz^2)) *)
              val rhsShape = add (add (sq wT)(sq sx)) (add (sq sy)(sq sz))
              val dvRHS = dvd_add_r (mult mT mT, add (sq wT)(sq sx), add (sq sy)(sq sz)) dvWX dvYZ
              (* dvd m^2 mn  (rewrite RHS shape back to mn via bodyEq sym) *)
              val dv_mn = oeq_rw_r (Term.lambda (Free("zdv",natT)) (dvd (mult mT mT) (Free("zdv",natT))),
                                    rhsShape, mn) (oeqSym_r2 bodyEq) dvRHS  (* dvd m^2 mn *)
              (* mn = m^2*(p*r), so dvd m^2 (m^2*(p*r)) -- trivially. We want four_sq(p*r).
                 Strategy: divide bodyEq by m^2.  Use dvW etc to write w=m*w0, then
                 w^2+sx^2+sy^2+sz^2 = m^2*(w0^2+sx0^2+sy0^2+sz0^2) and mn=m^2*(p*r),
                 cancel m^2 -> p*r = w0^2+... *)
              val () = out "DIVF_DVD_OK\n";

              (* extract quotients w0,sx0,sy0,sz0 and build the divided sum *)
              (* dvW : EX k. w = m*k.  elim to w0. *)
              fun withQuot (xT, dvx) nm k2 =
                let val Pq = Abs("q", natT, oeq xT (mult mT (Bound 0)))
                    fun bd q (hq:thm) = k2 q hq
                in exE_r (Pq, goalC) dvx nm natT bd end
              val res2 =
                withQuot (wT, dvW) "w0q" (fn w0 => fn hw0 =>
                withQuot (sx, dvX) "sx0q" (fn sx0 => fn hsx0 =>
                withQuot (sy, dvY) "sy0q" (fn sy0 => fn hsy0 =>
                withQuot (sz, dvZ) "sz0q" (fn sz0 => fn hsz0 =>
                  let
                    (* w^2 = m^2 * w0^2 *)
                    fun sqQuot (xT, x0, hx0) =
                      let val c1 = mult_cong_l_g (xT, mult mT x0, xT) hx0      (* x*x = (m*x0)*x *)
                          val c2 = mult_cong_r_g (mult mT x0, xT, mult mT x0) hx0 (* (m*x0)*x = (m*x0)*(m*x0) *)
                          val xx = oeqTrans_g (c1, c2)
                          val idP = proveIdentityG (mult (mult mT x0)(mult mT x0)) (mult (mult mT mT)(mult x0 x0))
                      in oeqTrans_g (xx, idP) end   (* x^2 = m^2 * x0^2 *)
                    val w2e  = sqQuot (wT, w0, hw0)     (* w^2 = m^2*w0^2 *)
                    val sx2e = sqQuot (sx, sx0, hsx0)
                    val sy2e = sqQuot (sy, sy0, hsy0)
                    val sz2e = sqQuot (sz, sz0, hsz0)
                    (* sum: (w^2+sx^2)+(sy^2+sz^2) = (m^2*w0^2+m^2*sx0^2)+(m^2*sy0^2+m^2*sz0^2) *)
                    val msq = mult mT mT
                    val sWX = add_cong_l_g (sq wT, mult msq (sq w0), sq sx) w2e
                    val sWX2 = oeqTrans_g (sWX, add_cong_r_g (mult msq (sq w0), sq sx, mult msq (sq sx0)) sx2e)
                    val sYZ = add_cong_l_g (sq sy, mult msq (sq sy0), sq sz) sy2e
                    val sYZ2 = oeqTrans_g (sYZ, add_cong_r_g (mult msq (sq sy0), sq sz, mult msq (sq sz0)) sz2e)
                    val sAll = oeqTrans_g (add_cong_l_g (add (sq wT)(sq sx), add (mult msq (sq w0))(mult msq (sq sx0)), add (sq sy)(sq sz)) sWX2,
                                           add_cong_r_g (add (mult msq (sq w0))(mult msq (sq sx0)), add (sq sy)(sq sz), add (mult msq (sq sy0))(mult msq (sq sz0))) sYZ2)
                    (* rhsShape = m^2*w0^2 + m^2*sx0^2 + ... ; factor m^2: = m^2*(w0^2+sx0^2+sy0^2+sz0^2) *)
                    val divSum = add (add (sq w0) (sq sx0)) (add (sq sy0) (sq sz0))
                    (* rhsShape(distributed) = m^2*divSum  via proveIdentityG *)
                    val distShape = add (add (mult msq (sq w0))(mult msq (sq sx0))) (add (mult msq (sq sy0))(mult msq (sq sz0)))
                    val factId = proveIdentityG distShape (mult msq divSum)  (* distributed = m^2*divSum *)
                    (* chain: mn = m^2*(p*r) [mn_msq] ; mn = rhsShape [bodyEq] ; rhsShape = distShape [sAll] ; distShape = m^2*divSum [factId]
                       => m^2*(p*r) = m^2*divSum *)
                    val e1 = oeqTrans_r2 (oeqSym_r2 mn_msq, bodyEq)         (* m^2*(p*r) = rhsShape *)
                    val e2 = oeqTrans_r2 (e1, sAll)                         (* m^2*(p*r) = distShape *)
                    val e3 = oeqTrans_r2 (e2, factId)                       (* m^2*(p*r) = m^2*divSum *)
                    (* cancel m^2 (m^2>0 since m>0): lt (m*0)(m*m) then m*0=0 *)
                    val ltm0mm = mult_lt_mono_l mT hmPos (ZeroC, mT) hmPos   (* lt (m*0)(m*m) *)
                    val msqPos = oeq_rw_r (Term.lambda (Free("zmp",natT)) (lt (Free("zmp",natT)) (mult mT mT)),
                                           mult mT ZeroC, ZeroC) (mult0r_d mT) ltm0mm   (* lt 0 (m*m) *)
                    val pr_eq = mult_left_cancel_r msq msqPos (mult pT rT, divSum) e3   (* p*r = divSum *)
                    (* four_sq (p*r) witness w0,sx0,sy0,sz0 *)
                    val fsBody = oeqTrans_r2 (pr_eq, oeqRefl_r2 divSum)   (* p*r = w0^2+sx0^2+sy0^2+sz0^2 *)
                  in four_sq_witness (mult pT rT, w0, sx0, sy0, sz0) fsBody end)))
              )
            in res2 end)))
  in res end;
val () = out "DIVF_LEAF_DEFINED\n";

(* smoke: run the leaf on Frees with assumed hypotheses *)
val () =
  let
    val mF=Free("m_l",natT); val pF=Free("p_l",natT); val rF=Free("r_l",natT);
    val aF=Free("a_l",natT); val bF=Free("b_l",natT); val cF=Free("c_l",natT); val dF=Free("d_l",natT);
    val eF=Free("e_l",natT); val fF=Free("f_l",natT); val gF=Free("g_l",natT); val hF=Free("h_l",natT);
    val hbodyP = Thm.assume (ctermGR (jT (oeq (mult mF pF) (add (add (sq aF)(sq bF))(add (sq cF)(sq dF))))));
    val hsum   = Thm.assume (ctermGR (jT (oeq (add (add (sq eF)(sq fF))(add (sq gF)(sq hF))) (mult mF rF))));
    val hca = Thm.assume (ctermGR (jT (cong mF eF aF)));
    val hcb = Thm.assume (ctermGR (jT (cong mF fF bF)));
    val hcc = Thm.assume (ctermGR (jT (cong mF gF cF)));
    val hcd = Thm.assume (ctermGR (jT (cong mF hF dF)));
    val hmPos = Thm.assume (ctermGR (jT (lt ZeroC mF)));
    val r = divide_leaf_pppp (mF,pF,rF, aF,bF,cF,dF, eF,fF,gF,hF) hbodyP hsum hca hcb hcc hcd hmPos
  in out ("DIVF_SMOKE hyps="^Int.toString(length(Thm.hyps_of r))
          ^" prop="^Syntax.string_of_term ctxtGR (Thm.prop_of r)^"\n") end
  handle e => out ("DIVF_SMOKE FAIL "^exnMessage e^"\n");

val () = out "DIVF_ALL_DONE\n";
