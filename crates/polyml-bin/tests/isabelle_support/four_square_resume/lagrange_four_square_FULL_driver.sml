val () = (Proofterm.proofs := 0; out "MEGA_PROOFS0\n");
val () = restore_l4_context ();
val () = out "MEGA_BEGIN\n";
fun sqMega x = mult x x;
(* ===== leaf def: pppp ===== *)
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
(* ===== leaf def: pppn ===== *)
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
(* ===== leaf def: ppnp ===== *)
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

(* cong helper: cong_kmult (m,k,x',x) : from cong m x' x, get cong m (k*x')(k*x) *)
fun cong_kmult (mT, k, xp, x) hflag = cong_mult_r (mT, k, k, xp, x) (cong_refl_g (mT, k)) hflag;

(* ---- THE PPNP LEAF ---- *)
fun divide_leaf_ppnp (mT,pT,rT, a,b,c,d, e,f,g,h)
        hbodyP hsum hca hcb hccR hcd hmPos =
  (* hca: cong m e a ; hcb: cong m f b ; hccR: cong m (g+c) 0 ; hcd: cong m h d *)
  let
    val mp = mult mT pT  val mr = mult mT rT
    val sumA = add (add (sq a)(sq b))(add (sq c)(sq d))
    val Mabcd = add (add (sq a)(sq b))(add (sq c)(sq d))
    val Mefgh = add (add (sq e)(sq f))(add (sq g)(sq h))
    val mn = mult Mabcd Mefgh
    (* witnesses (LEFT-FOLDED) *)
    val wP = add (add (mult a e)(mult b f))(mult d h)    val wQ = mult c g
    val Px = add (add (mult a f)(mult c h))(mult g d)     val Qx = mult e b
    val Py = mult f d                                     val Qy = add (add (mult a g)(mult e c))(mult b h)
    val Pz = mult a h                                     val Qz = add (add (mult e d)(mult b g))(mult f c)
    val Dcross = dbl (add (add (add (mult wP wQ) (mult Px Qx)) (mult Py Qy)) (mult Pz Qz))
    val PPsum  = add (add (add (add (add (add (add (sq wP)(sq wQ))(sq Px))(sq Qx))(sq Py))(sq Qy))(sq Pz))(sq Qz)
    val starL_i = add mn Dcross
    val starR_i = PPsum
    (* build the star via proveIdentityG (cheap) *)
    val star_i = proveIdentityG starL_i starR_i
    val () = if (Thm.prop_of star_i) aconv (jT (oeq starL_i starR_i)) then out "DIVPN_STAR_SHAPE_OK\n"
             else raise Fail "star shape"

    (* ============ THE FOUR DIVISIBILITY CONGRUENCES ============ *)
    (* cong m wP wQ : wP=(a*e+b*f)+d*h (LEFT) ; wQ=c*g (RIGHT).
       Route: cong m (wP + c^2)(wQ + c^2), cancel c^2.
         wP + c^2 ≡ (a^2+b^2+d^2) + c^2 = m*p
         wQ + c^2 = c*g + c*c = c*(g+c) ≡ c*0 = 0 ≡ m*p  (RIGHT flag) *)
    val cc = sq c
    val c_ae = cong_kmult (mT, a, e, a) hca   (* cong m (a*e)(a*a) *)
    val c_bf = cong_kmult (mT, b, f, b) hcb
    val c_dh = cong_kmult (mT, d, h, d) hcd
    val c_wp1 = cong_add_g (mT, mult a e, sq a, mult b f, sq b) c_ae c_bf
    val c_wp2 = cong_add_g (mT, add (mult a e)(mult b f), add (sq a)(sq b), mult d h, sq d) c_wp1 c_dh
                (* cong m wP ((a^2+b^2)+d^2) *)
    val c_wPcc = cong_add_g (mT, wP, add (add (sq a)(sq b))(sq d), cc, cc) c_wp2 (cong_refl_g (mT, cc))
                 (* cong m (wP+c^2) (((a^2+b^2)+d^2)+c^2) *)
    val reA = proveIdentityG (add (add (add (sq a)(sq b))(sq d)) cc) sumA  (* ((a^2+b^2)+d^2)+c^2 = sumA *)
    val c_to_sumA = cong_trans_g (mT, add wP cc, add (add (add (sq a)(sq b))(sq d)) cc, sumA)
                      c_wPcc (cong_of_oeq_r (mT, add (add (add (sq a)(sq b))(sq d)) cc, sumA) reA)
    val c_wPcc_mp = oeq_rw_r (Term.lambda (Free("zq",natT)) (cong mT (add wP cc) (Free("zq",natT))), sumA, mp)
                      (oeqSym_r2 hbodyP) c_to_sumA   (* cong m (wP+c^2)(m*p) *)
    (* RHS: wQ + c^2 = c*g + c*c = c*(g+c) ; cong m (c*(g+c)) 0 from RIGHT flag *)
    val c_cgc = cong_kmult (mT, c, add g c, ZeroC) hccR     (* cong m (c*(g+c))(c*0) *)
    val c0 = mult0r_d c                                      (* c*0 = 0 *)
    val c_cgc0 = cong_trans_g (mT, mult c (add g c), mult c ZeroC, ZeroC) c_cgc (cong_of_oeq_r (mT, mult c ZeroC, ZeroC) c0)
                 (* cong m (c*(g+c)) 0 *)
    val reQ = proveIdentityG (add wQ cc) (mult c (add g c))  (* c*g+c^2 = c*(g+c) *)
    val c_wQcc0 = cong_trans_g (mT, add wQ cc, mult c (add g c), ZeroC) (cong_of_oeq_r (mT, add wQ cc, mult c (add g c)) reQ) c_cgc0  (* cong m (wQ+c^2) 0 *)
    val c_mp0 = (let val z = add0_d mp in cong_introR_r (mT, mp, ZeroC, pT) (oeqSym_r2 z) end)
    val c_wPcc0 = cong_trans_g (mT, add wP cc, mp, ZeroC) c_wPcc_mp c_mp0   (* cong m (wP+c^2) 0 *)
    val c_both = cong_trans_g (mT, add wP cc, ZeroC, add wQ cc) c_wPcc0 (cong_sym_g (mT, add wQ cc, ZeroC) c_wQcc0)
                 (* cong m (wP+c^2)(wQ+c^2) *)
    val c_wPwQ = cong_radd_cancel_r (mT, wP, wQ, cc) c_both   (* cong m wP wQ *)
    val () = out "DIVPN_CONG_W_OK\n";

    (* cong m Px Qx : Px=(a*f+c*h)+g*d ; Qx=e*b.  Both ≡ a*b.
       Px mod m: a*f≡a*b [f≡b], c*h≡c*d [h≡d], g*d: g RIGHT (g≡-c) -> g*d≡-c*d.
         so c*h+g*d ≡ c*d - c*d = 0.  Px ≡ a*b.
       Qx=e*b ≡ a*b [e≡a]. *)
    val c_af = cong_kmult (mT, a, f, b) hcb            (* cong m (a*f)(a*b) *)
    (* c*h + g*d ≡ 0 : c*h≡c*d [h≡d], and g*d+c*d = (g+c)*d = d*(g+c)≡0 *)
    val c_ch = cong_mult_r (mT, c, c, h, d) (cong_refl_g (mT, c)) hcd   (* cong m (c*h)(c*d) *)
    val c_chgd1 = cong_add_g (mT, mult c h, mult c d, mult g d, mult g d) c_ch (cong_refl_g (mT, mult g d))
                  (* cong m (c*h+g*d)(c*d+g*d) *)
    val c_dgc = cong_kmult (mT, d, add g c, ZeroC) hccR    (* cong m (d*(g+c))(d*0) *)
    val d0 = mult0r_d d
    val c_dgc0 = cong_trans_g (mT, mult d (add g c), mult d ZeroC, ZeroC) c_dgc (cong_of_oeq_r (mT, mult d ZeroC, ZeroC) d0)
    val reGD = proveIdentityG (add (mult c d)(mult g d)) (mult d (add g c))  (* c*d+g*d = d*(g+c) *)
    val c_cdgd0 = cong_trans_g (mT, add (mult c d)(mult g d), mult d (add g c), ZeroC) (cong_of_oeq_r (mT, add (mult c d)(mult g d), mult d (add g c)) reGD) c_dgc0
                  (* cong m (c*d+g*d) 0 *)
    val c_chgd0 = cong_trans_g (mT, add (mult c h)(mult g d), add (mult c d)(mult g d), ZeroC) c_chgd1 c_cdgd0
                  (* cong m (c*h+g*d) 0 *)
    (* Px = (a*f + c*h) + g*d.  reassoc to a*f + (c*h+g*d).  cong m Px (a*b+0)=a*b. *)
    val rePx = proveIdentityG Px (add (mult a f) (add (mult c h)(mult g d)))
    val c_Px_re = cong_of_oeq_r (mT, Px, add (mult a f)(add (mult c h)(mult g d))) rePx
    val c_Pxsum = cong_add_g (mT, mult a f, mult a b, add (mult c h)(mult g d), ZeroC) c_af c_chgd0
                  (* cong m (a*f+(c*h+g*d))(a*b+0) *)
    val reAB0 = add0r_d (mult a b)   (* (a*b)+0 = a*b *)
    val c_Px_ab = cong_trans_g (mT, Px, add (mult a f)(add (mult c h)(mult g d)), mult a b)
                    c_Px_re (cong_trans_g (mT, add (mult a f)(add (mult c h)(mult g d)), add (mult a b) ZeroC, mult a b)
                              c_Pxsum (cong_of_oeq_r (mT, add (mult a b) ZeroC, mult a b) reAB0))
    val cQx_ab = cong_mult_r (mT, e, a, b, b) hca (cong_refl_g (mT, b))   (* cong m (e*b)(a*b) *)
    val c_PxQx = cong_trans_g (mT, Px, mult a b, Qx) c_Px_ab (cong_sym_g (mT, Qx, mult a b) cQx_ab)
    val () = out "DIVPN_CONG_X_OK\n";

    (* cong m Py Qy : Py=f*d ; Qy=(a*g+e*c)+b*h.  Both ≡ b*d.
       Py=f*d ≡ b*d [f≡b].
       Qy mod m: a*g: g RIGHT -> a*g≡-a*c ; e*c≡a*c [e≡a] ; b*h≡b*d [h≡d].
         a*g+e*c ≡ -a*c+a*c = 0.  Qy ≡ b*d. *)
    val cPy_bd = cong_mult_r (mT, f, b, d, d) hcb (cong_refl_g (mT, d))   (* cong m (f*d)(b*d) *)
    (* a*g + e*c ≡ 0 : a*g+a*c = a*(g+c)≡0, and e*c≡a*c [e≡a] *)
    val c_ec = cong_mult_r (mT, e, a, c, c) hca (cong_refl_g (mT, c))     (* cong m (e*c)(a*c) *)
    val c_agec1 = cong_add_g (mT, mult a g, mult a g, mult e c, mult a c) (cong_refl_g (mT, mult a g)) c_ec
                  (* cong m (a*g+e*c)(a*g+a*c) *)
    val reAG = proveIdentityG (add (mult a g)(mult a c)) (mult a (add g c))  (* a*g+a*c = a*(g+c) *)
    val c_agc = cong_kmult (mT, a, add g c, ZeroC) hccR
    val a0 = mult0r_d a
    val c_agc0 = cong_trans_g (mT, mult a (add g c), mult a ZeroC, ZeroC) c_agc (cong_of_oeq_r (mT, mult a ZeroC, ZeroC) a0)
    val c_agac0 = cong_trans_g (mT, add (mult a g)(mult a c), mult a (add g c), ZeroC) (cong_of_oeq_r (mT, add (mult a g)(mult a c), mult a (add g c)) reAG) c_agc0
    val c_agec0 = cong_trans_g (mT, add (mult a g)(mult e c), add (mult a g)(mult a c), ZeroC) c_agec1 c_agac0
                  (* cong m (a*g+e*c) 0 *)
    val c_bh = cong_kmult (mT, b, h, d) hcd            (* cong m (b*h)(b*d) *)
    (* Qy = (a*g + e*c) + b*h.  cong m Qy (0 + b*d).  *)
    val c_Qysum = cong_add_g (mT, add (mult a g)(mult e c), ZeroC, mult b h, mult b d) c_agec0 c_bh
                  (* cong m Qy (0 + b*d) *)
    val re0BD = add0_d (mult b d)   (* 0 + b*d = b*d *)
    val c_Qy_bd = cong_trans_g (mT, Qy, add ZeroC (mult b d), mult b d) c_Qysum (cong_of_oeq_r (mT, add ZeroC (mult b d), mult b d) re0BD)
    val c_PyQy = cong_trans_g (mT, Py, mult b d, Qy) cPy_bd (cong_sym_g (mT, Qy, mult b d) c_Qy_bd)
    val () = out "DIVPN_CONG_Y_OK\n";

    (* cong m Pz Qz : Pz=a*h ; Qz=(e*d+b*g)+f*c.  Both ≡ a*d.
       Pz=a*h ≡ a*d [h≡d].
       Qz mod m: e*d≡a*d [e≡a] ; b*g: g RIGHT -> b*g≡-b*c ; f*c≡b*c [f≡b].
         b*g+f*c ≡ -b*c+b*c = 0.  Qz ≡ a*d. *)
    val cPz_ad = cong_kmult (mT, a, h, d) hcd            (* cong m (a*h)(a*d) *)
    val c_ed = cong_mult_r (mT, e, a, d, d) hca (cong_refl_g (mT, d))     (* cong m (e*d)(a*d) *)
    (* b*g + f*c ≡ 0 : b*g+b*c = b*(g+c)≡0, and f*c≡b*c [f≡b] *)
    val c_fc = cong_mult_r (mT, f, b, c, c) hcb (cong_refl_g (mT, c))    (* cong m (f*c)(b*c) *)
    val c_bgfc1 = cong_add_g (mT, mult b g, mult b g, mult f c, mult b c) (cong_refl_g (mT, mult b g)) c_fc
                  (* cong m (b*g+f*c)(b*g+b*c) *)
    val reBG = proveIdentityG (add (mult b g)(mult b c)) (mult b (add g c))  (* b*g+b*c = b*(g+c) *)
    val c_bgc = cong_kmult (mT, b, add g c, ZeroC) hccR
    val b0 = mult0r_d b
    val c_bgc0 = cong_trans_g (mT, mult b (add g c), mult b ZeroC, ZeroC) c_bgc (cong_of_oeq_r (mT, mult b ZeroC, ZeroC) b0)
    val c_bgbc0 = cong_trans_g (mT, add (mult b g)(mult b c), mult b (add g c), ZeroC) (cong_of_oeq_r (mT, add (mult b g)(mult b c), mult b (add g c)) reBG) c_bgc0
    val c_bgfc0 = cong_trans_g (mT, add (mult b g)(mult f c), add (mult b g)(mult b c), ZeroC) c_bgfc1 c_bgbc0
                  (* cong m (b*g+f*c) 0 *)
    (* Qz = (e*d + b*g) + f*c.  reassoc to e*d + (b*g+f*c).  cong m Qz (a*d+0)=a*d. *)
    val reQz = proveIdentityG Qz (add (mult e d) (add (mult b g)(mult f c)))
    val c_Qz_re = cong_of_oeq_r (mT, Qz, add (mult e d)(add (mult b g)(mult f c))) reQz
    val c_Qzsum = cong_add_g (mT, mult e d, mult a d, add (mult b g)(mult f c), ZeroC) c_ed c_bgfc0
                  (* cong m (e*d+(b*g+f*c))(a*d+0) *)
    val reAD0 = add0r_d (mult a d)   (* (a*d)+0 = a*d *)
    val c_Qz_ad = cong_trans_g (mT, Qz, add (mult e d)(add (mult b g)(mult f c)), mult a d)
                    c_Qz_re (cong_trans_g (mT, add (mult e d)(add (mult b g)(mult f c)), add (mult a d) ZeroC, mult a d)
                              c_Qzsum (cong_of_oeq_r (mT, add (mult a d) ZeroC, mult a d) reAD0))
    val c_PzQz = cong_trans_g (mT, Pz, mult a d, Qz) cPz_ad (cong_sym_g (mT, Qz, mult a d) c_Qz_ad)
    val () = out "DIVPN_CONG_Z_OK\n";

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
            val () = out "DIVPN_ASSEMBLE_OK\n"

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
            val () = out "DIVPN_DVD_OK\n";

            (* extract quotients and build divided sum, mirroring PPPP/PPPN *)
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
val () = out "DIVPN_LEAF_DEFINED\n";
(* ===== leaf def: ppnn ===== *)
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
(* ===== leaf def: pnpp ===== *)
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
(* ===== leaf def: pnpn ===== *)
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
(* ===== leaf def: pnnp ===== *)
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
(* ===== leaf def: pnnn ===== *)
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
(* ===== leaf def: nnnn ===== *)
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
(* ===== prove all 9 leaf theorems (GC between each) ===== *)
fun mkLF () = (Free("m_L",natT),Free("p_L",natT),Free("r_L",natT),Free("a_L",natT),Free("b_L",natT),Free("c_L",natT),Free("d_L",natT),Free("e_L",natT),Free("f_L",natT),Free("g_L",natT),Free("h_L",natT));
val leaf_pppp_thm =
  let val (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) = mkLF ()
      val hbP=jT(oeq(mult mF pF)(add(add(sqMega aF)(sqMega bF))(add(sqMega cF)(sqMega dF))))
      val hsP=jT(oeq(add(add(sqMega eF)(sqMega fF))(add(sqMega gF)(sqMega hF)))(mult mF rF))
      val haP=jT(cong mF eF aF) val hbbP=jT(cong mF fF bF) val hccP=jT(cong mF gF cF) val hddP=jT(cong mF hF dF) val hmP=jT(lt ZeroC mF)
      val r=divide_leaf_pppp (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) (Thm.assume(ctermGR hbP))(Thm.assume(ctermGR hsP))(Thm.assume(ctermGR haP))(Thm.assume(ctermGR hbbP))(Thm.assume(ctermGR hccP))(Thm.assume(ctermGR hddP))(Thm.assume(ctermGR hmP))
  in varify(Thm.implies_intr(ctermGR hbP)(Thm.implies_intr(ctermGR hsP)(Thm.implies_intr(ctermGR haP)(Thm.implies_intr(ctermGR hbbP)(Thm.implies_intr(ctermGR hccP)(Thm.implies_intr(ctermGR hddP)(Thm.implies_intr(ctermGR hmP) r))))))) end;
val () = out ("MEGA leaf_pppp hyps="^Int.toString(length(Thm.hyps_of leaf_pppp_thm))^"\n");
val () = (PolyML.fullGC(); ());
val leaf_pppn_thm =
  let val (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) = mkLF ()
      val hbP=jT(oeq(mult mF pF)(add(add(sqMega aF)(sqMega bF))(add(sqMega cF)(sqMega dF))))
      val hsP=jT(oeq(add(add(sqMega eF)(sqMega fF))(add(sqMega gF)(sqMega hF)))(mult mF rF))
      val haP=jT(cong mF eF aF) val hbbP=jT(cong mF fF bF) val hccP=jT(cong mF gF cF) val hddP=jT(cong mF (add hF dF) ZeroC) val hmP=jT(lt ZeroC mF)
      val r=divide_leaf_pppn (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) (Thm.assume(ctermGR hbP))(Thm.assume(ctermGR hsP))(Thm.assume(ctermGR haP))(Thm.assume(ctermGR hbbP))(Thm.assume(ctermGR hccP))(Thm.assume(ctermGR hddP))(Thm.assume(ctermGR hmP))
  in varify(Thm.implies_intr(ctermGR hbP)(Thm.implies_intr(ctermGR hsP)(Thm.implies_intr(ctermGR haP)(Thm.implies_intr(ctermGR hbbP)(Thm.implies_intr(ctermGR hccP)(Thm.implies_intr(ctermGR hddP)(Thm.implies_intr(ctermGR hmP) r))))))) end;
val () = out ("MEGA leaf_pppn hyps="^Int.toString(length(Thm.hyps_of leaf_pppn_thm))^"\n");
val () = (PolyML.fullGC(); ());
val leaf_ppnp_thm =
  let val (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) = mkLF ()
      val hbP=jT(oeq(mult mF pF)(add(add(sqMega aF)(sqMega bF))(add(sqMega cF)(sqMega dF))))
      val hsP=jT(oeq(add(add(sqMega eF)(sqMega fF))(add(sqMega gF)(sqMega hF)))(mult mF rF))
      val haP=jT(cong mF eF aF) val hbbP=jT(cong mF fF bF) val hccP=jT(cong mF (add gF cF) ZeroC) val hddP=jT(cong mF hF dF) val hmP=jT(lt ZeroC mF)
      val r=divide_leaf_ppnp (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) (Thm.assume(ctermGR hbP))(Thm.assume(ctermGR hsP))(Thm.assume(ctermGR haP))(Thm.assume(ctermGR hbbP))(Thm.assume(ctermGR hccP))(Thm.assume(ctermGR hddP))(Thm.assume(ctermGR hmP))
  in varify(Thm.implies_intr(ctermGR hbP)(Thm.implies_intr(ctermGR hsP)(Thm.implies_intr(ctermGR haP)(Thm.implies_intr(ctermGR hbbP)(Thm.implies_intr(ctermGR hccP)(Thm.implies_intr(ctermGR hddP)(Thm.implies_intr(ctermGR hmP) r))))))) end;
val () = out ("MEGA leaf_ppnp hyps="^Int.toString(length(Thm.hyps_of leaf_ppnp_thm))^"\n");
val () = (PolyML.fullGC(); ());
val leaf_ppnn_thm =
  let val (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) = mkLF ()
      val hbP=jT(oeq(mult mF pF)(add(add(sqMega aF)(sqMega bF))(add(sqMega cF)(sqMega dF))))
      val hsP=jT(oeq(add(add(sqMega eF)(sqMega fF))(add(sqMega gF)(sqMega hF)))(mult mF rF))
      val haP=jT(cong mF eF aF) val hbbP=jT(cong mF fF bF) val hccP=jT(cong mF (add gF cF) ZeroC) val hddP=jT(cong mF (add hF dF) ZeroC) val hmP=jT(lt ZeroC mF)
      val r=divide_leaf_ppnn (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) (Thm.assume(ctermGR hbP))(Thm.assume(ctermGR hsP))(Thm.assume(ctermGR haP))(Thm.assume(ctermGR hbbP))(Thm.assume(ctermGR hccP))(Thm.assume(ctermGR hddP))(Thm.assume(ctermGR hmP))
  in varify(Thm.implies_intr(ctermGR hbP)(Thm.implies_intr(ctermGR hsP)(Thm.implies_intr(ctermGR haP)(Thm.implies_intr(ctermGR hbbP)(Thm.implies_intr(ctermGR hccP)(Thm.implies_intr(ctermGR hddP)(Thm.implies_intr(ctermGR hmP) r))))))) end;
val () = out ("MEGA leaf_ppnn hyps="^Int.toString(length(Thm.hyps_of leaf_ppnn_thm))^"\n");
val () = (PolyML.fullGC(); ());
val leaf_pnpp_thm =
  let val (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) = mkLF ()
      val hbP=jT(oeq(mult mF pF)(add(add(sqMega aF)(sqMega bF))(add(sqMega cF)(sqMega dF))))
      val hsP=jT(oeq(add(add(sqMega eF)(sqMega fF))(add(sqMega gF)(sqMega hF)))(mult mF rF))
      val haP=jT(cong mF eF aF) val hbbP=jT(cong mF (add fF bF) ZeroC) val hccP=jT(cong mF gF cF) val hddP=jT(cong mF hF dF) val hmP=jT(lt ZeroC mF)
      val r=divide_leaf_pnpp (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) (Thm.assume(ctermGR hbP))(Thm.assume(ctermGR hsP))(Thm.assume(ctermGR haP))(Thm.assume(ctermGR hbbP))(Thm.assume(ctermGR hccP))(Thm.assume(ctermGR hddP))(Thm.assume(ctermGR hmP))
  in varify(Thm.implies_intr(ctermGR hbP)(Thm.implies_intr(ctermGR hsP)(Thm.implies_intr(ctermGR haP)(Thm.implies_intr(ctermGR hbbP)(Thm.implies_intr(ctermGR hccP)(Thm.implies_intr(ctermGR hddP)(Thm.implies_intr(ctermGR hmP) r))))))) end;
val () = out ("MEGA leaf_pnpp hyps="^Int.toString(length(Thm.hyps_of leaf_pnpp_thm))^"\n");
val () = (PolyML.fullGC(); ());
val leaf_pnpn_thm =
  let val (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) = mkLF ()
      val hbP=jT(oeq(mult mF pF)(add(add(sqMega aF)(sqMega bF))(add(sqMega cF)(sqMega dF))))
      val hsP=jT(oeq(add(add(sqMega eF)(sqMega fF))(add(sqMega gF)(sqMega hF)))(mult mF rF))
      val haP=jT(cong mF eF aF) val hbbP=jT(cong mF (add fF bF) ZeroC) val hccP=jT(cong mF gF cF) val hddP=jT(cong mF (add hF dF) ZeroC) val hmP=jT(lt ZeroC mF)
      val r=divide_leaf_pnpn (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) (Thm.assume(ctermGR hbP))(Thm.assume(ctermGR hsP))(Thm.assume(ctermGR haP))(Thm.assume(ctermGR hbbP))(Thm.assume(ctermGR hccP))(Thm.assume(ctermGR hddP))(Thm.assume(ctermGR hmP))
  in varify(Thm.implies_intr(ctermGR hbP)(Thm.implies_intr(ctermGR hsP)(Thm.implies_intr(ctermGR haP)(Thm.implies_intr(ctermGR hbbP)(Thm.implies_intr(ctermGR hccP)(Thm.implies_intr(ctermGR hddP)(Thm.implies_intr(ctermGR hmP) r))))))) end;
val () = out ("MEGA leaf_pnpn hyps="^Int.toString(length(Thm.hyps_of leaf_pnpn_thm))^"\n");
val () = (PolyML.fullGC(); ());
val leaf_pnnp_thm =
  let val (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) = mkLF ()
      val hbP=jT(oeq(mult mF pF)(add(add(sqMega aF)(sqMega bF))(add(sqMega cF)(sqMega dF))))
      val hsP=jT(oeq(add(add(sqMega eF)(sqMega fF))(add(sqMega gF)(sqMega hF)))(mult mF rF))
      val haP=jT(cong mF eF aF) val hbbP=jT(cong mF (add fF bF) ZeroC) val hccP=jT(cong mF (add gF cF) ZeroC) val hddP=jT(cong mF hF dF) val hmP=jT(lt ZeroC mF)
      val r=divide_leaf_pnnp (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) (Thm.assume(ctermGR hbP))(Thm.assume(ctermGR hsP))(Thm.assume(ctermGR haP))(Thm.assume(ctermGR hbbP))(Thm.assume(ctermGR hccP))(Thm.assume(ctermGR hddP))(Thm.assume(ctermGR hmP))
  in varify(Thm.implies_intr(ctermGR hbP)(Thm.implies_intr(ctermGR hsP)(Thm.implies_intr(ctermGR haP)(Thm.implies_intr(ctermGR hbbP)(Thm.implies_intr(ctermGR hccP)(Thm.implies_intr(ctermGR hddP)(Thm.implies_intr(ctermGR hmP) r))))))) end;
val () = out ("MEGA leaf_pnnp hyps="^Int.toString(length(Thm.hyps_of leaf_pnnp_thm))^"\n");
val () = (PolyML.fullGC(); ());
val leaf_pnnn_thm =
  let val (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) = mkLF ()
      val hbP=jT(oeq(mult mF pF)(add(add(sqMega aF)(sqMega bF))(add(sqMega cF)(sqMega dF))))
      val hsP=jT(oeq(add(add(sqMega eF)(sqMega fF))(add(sqMega gF)(sqMega hF)))(mult mF rF))
      val haP=jT(cong mF eF aF) val hbbP=jT(cong mF (add fF bF) ZeroC) val hccP=jT(cong mF (add gF cF) ZeroC) val hddP=jT(cong mF (add hF dF) ZeroC) val hmP=jT(lt ZeroC mF)
      val r=divide_leaf_pnnn (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) (Thm.assume(ctermGR hbP))(Thm.assume(ctermGR hsP))(Thm.assume(ctermGR haP))(Thm.assume(ctermGR hbbP))(Thm.assume(ctermGR hccP))(Thm.assume(ctermGR hddP))(Thm.assume(ctermGR hmP))
  in varify(Thm.implies_intr(ctermGR hbP)(Thm.implies_intr(ctermGR hsP)(Thm.implies_intr(ctermGR haP)(Thm.implies_intr(ctermGR hbbP)(Thm.implies_intr(ctermGR hccP)(Thm.implies_intr(ctermGR hddP)(Thm.implies_intr(ctermGR hmP) r))))))) end;
val () = out ("MEGA leaf_pnnn hyps="^Int.toString(length(Thm.hyps_of leaf_pnnn_thm))^"\n");
val () = (PolyML.fullGC(); ());
val leaf_nnnn_thm =
  let val (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) = mkLF ()
      val hbP=jT(oeq(mult mF pF)(add(add(sqMega aF)(sqMega bF))(add(sqMega cF)(sqMega dF))))
      val hsP=jT(oeq(add(add(sqMega eF)(sqMega fF))(add(sqMega gF)(sqMega hF)))(mult mF rF))
      val haP=jT(cong mF (add eF aF) ZeroC) val hbbP=jT(cong mF (add fF bF) ZeroC) val hccP=jT(cong mF (add gF cF) ZeroC) val hddP=jT(cong mF (add hF dF) ZeroC) val hmP=jT(lt ZeroC mF)
      val r=divide_leaf_nnnn (mF,pF,rF,aF,bF,cF,dF,eF,fF,gF,hF) (Thm.assume(ctermGR hbP))(Thm.assume(ctermGR hsP))(Thm.assume(ctermGR haP))(Thm.assume(ctermGR hbbP))(Thm.assume(ctermGR hccP))(Thm.assume(ctermGR hddP))(Thm.assume(ctermGR hmP))
  in varify(Thm.implies_intr(ctermGR hbP)(Thm.implies_intr(ctermGR hsP)(Thm.implies_intr(ctermGR haP)(Thm.implies_intr(ctermGR hbbP)(Thm.implies_intr(ctermGR hccP)(Thm.implies_intr(ctermGR hddP)(Thm.implies_intr(ctermGR hmP) r))))))) end;
val () = out ("MEGA leaf_nnnn hyps="^Int.toString(length(Thm.hyps_of leaf_nnnn_thm))^"\n");
val () = (PolyML.fullGC(); ());
val () = out "MEGA_ALL_LEAVES_DONE\n";
(* ===== strict helpers (rm_excl etc.) ===== *)
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
(* ===== descent_step assembly (no export) ===== *)
val () = out "DSTEP_BEGIN\n";

(* ---- assembly helpers (apply_leaf, fsq_commute) ---- *)
fun sqh x = mult x x;
fun apply_leaf leafThm (mT,pT,rT) (cA,cB,cC,cD) (rA,rB,rC,rD) hbodyP' hsum' hc1 hc2 hc3 hc4 hmPos =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtGR
      [(("m_L",0),ctermGR mT),(("p_L",0),ctermGR pT),(("r_L",0),ctermGR rT),
       (("a_L",0),ctermGR cA),(("b_L",0),ctermGR cB),(("c_L",0),ctermGR cC),(("d_L",0),ctermGR cD),
       (("e_L",0),ctermGR rA),(("f_L",0),ctermGR rB),(("g_L",0),ctermGR rC),(("h_L",0),ctermGR rD)] leafThm)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim
       (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hbodyP') hsum') hc1) hc2) hc3) hc4) hmPos
  end;
fun fsq_commute (pT,rT) hfs =
  let val comm = multcomm_g (pT, rT)
      val Pf = Term.lambda (Free("zfc",natT)) (four_sq (Free("zfc",natT)))
  in oeq_rw_r (Pf, mult pT rT, mult rT pT) comm hfs end;
(* permuted hbodyP : from oeq (m*p)(a^2+b^2+c^2+d^2) build oeq(m*p)(cA^2+cB^2+cC^2+cD^2)
   where (cA,cB,cC,cD) is a permutation of (a,b,c,d).  via proveIdentityG on the RHS. *)
fun permBody (mT,pT) (a,b,c,d) (cA,cB,cC,cD) hbody =
  let val origRHS = add (add (sqh a)(sqh b))(add (sqh c)(sqh d))
      val permRHS = add (add (sqh cA)(sqh cB))(add (sqh cC)(sqh cD))
      val id = proveIdentityG origRHS permRHS    (* a^2+b^2+c^2+d^2 = cA^2+cB^2+cC^2+cD^2 *)
  in oeqTrans_r2 (hbody, id) end;   (* oeq (m*p) permRHS *)
fun permSum (mT,rT) (ap,bp,cp,dp) (rA,rB,rC,rD) hsum =
  let val origLHS = add (add (sqh ap)(sqh bp))(add (sqh cp)(sqh dp))
      val permLHS = add (add (sqh rA)(sqh rB))(add (sqh rC)(sqh rD))
      val id = proveIdentityG permLHS origLHS    (* permLHS = origLHS *)
  in oeqTrans_r2 (id, hsum) end;   (* oeq permLHS (m*r) *)
val () = out "DSTEP_HELPERS_OK\n";

(* ============================================================================
   route : given the 4 resolved congruences (each L or R, tagged) for coords
   (a,b,c,d) with residues (ap,bp,cp,dp), route to the matching leaf via the
   permutation that brings a LEFT coord to position 1.  Returns four_sq(r*p).

   The sign tuple is (sA,sB,sC,sD) : bool list (true=LEFT, false=RIGHT).
   cgA..cgD : the concrete cong thms (cong m resid coord for LEFT,
              cong m (resid+coord) 0 for RIGHT).
   coords (a,b,c,d), residues (ap,bp,cp,dp), m,p,r, hbody, hsum, hmPos.
   ============================================================================ *)
fun route (sA,sB,sC,sD) (a,b,c,d) (ap,bp,cp,dp) (mT,pT,rT) hbody hsum hmPos cgA cgB cgC cgD =
  let
    (* leaf-pos order produced by a permutation pi=[i0,i1,i2,i3] (orig indices) *)
    (* coords/residues/congs reordered; leaf pattern derived from signs at pi positions *)
    val coordsV = Vector.fromList [a,b,c,d]
    val residsV = Vector.fromList [ap,bp,cp,dp]
    val congsV  = Vector.fromList [cgA,cgB,cgC,cgD]
    val signsV  = Vector.fromList [sA,sB,sC,sD]
    fun pick pi =
      let val [i0,i1,i2,i3] = pi
          val cA=Vector.sub(coordsV,i0) val cB=Vector.sub(coordsV,i1) val cC=Vector.sub(coordsV,i2) val cD=Vector.sub(coordsV,i3)
          val rA=Vector.sub(residsV,i0) val rB=Vector.sub(residsV,i1) val rC=Vector.sub(residsV,i2) val rD=Vector.sub(residsV,i3)
          val g1=Vector.sub(congsV,i0) val g2=Vector.sub(congsV,i1) val g3=Vector.sub(congsV,i2) val g4=Vector.sub(congsV,i3)
          val hbodyP' = permBody (mT,pT) (a,b,c,d) (cA,cB,cC,cD) hbody
          val hsum'   = permSum (mT,rT) (ap,bp,cp,dp) (rA,rB,rC,rD) hsum
      in (cA,cB,cC,cD, rA,rB,rC,rD, g1,g2,g3,g4, hbodyP', hsum') end
    (* choose leaf + perm based on sign tuple. patIs returns the leaf thm for a-LEFT pattern (sb,sc,sd at positions) *)
    fun leafFor (s1,s2,s3) =  (* positions 2,3,4 signs (pos1 always LEFT); true=LEFT=P false=RIGHT=N *)
      case (s1,s2,s3) of
        (true,true,true)    => leaf_pppp_thm
      | (true,true,false)   => leaf_pppn_thm
      | (true,false,true)   => leaf_ppnp_thm
      | (true,false,false)  => leaf_ppnn_thm
      | (false,true,true)   => leaf_pnpp_thm
      | (false,true,false)  => leaf_pnpn_thm
      | (false,false,true)  => leaf_pnnp_thm
      | (false,false,false) => leaf_pnnn_thm
    val hfs_pr =
      if sA then
        (* a-LEFT: identity perm, leaf from (sB,sC,sD) *)
        let val (cA,cB,cC,cD, rA,rB,rC,rD, g1,g2,g3,g4, hbP, hsm) = pick [0,1,2,3]
            val lf = leafFor (sB,sC,sD)
        in apply_leaf lf (mT,pT,rT) (cA,cB,cC,cD) (rA,rB,rC,rD) hbP hsm g1 g2 g3 g4 hmPos end
      else if sB then
        (* a-RIGHT, b-LEFT: perm [1,0,2,3] -> positions (b=L, a=R, c, d), pattern (R-at-2, sC, sD) *)
        let val (cA,cB,cC,cD, rA,rB,rC,rD, g1,g2,g3,g4, hbP, hsm) = pick [1,0,2,3]
            val lf = leafFor (false,sC,sD)   (* pos2 = a = RIGHT=false *)
        in apply_leaf lf (mT,pT,rT) (cA,cB,cC,cD) (rA,rB,rC,rD) hbP hsm g1 g2 g3 g4 hmPos end
      else if sC then
        (* a,b RIGHT, c LEFT: perm [2,1,0,3] -> positions (c=L, b=R, a=R, d), pattern (false,false,sD) *)
        let val (cA,cB,cC,cD, rA,rB,rC,rD, g1,g2,g3,g4, hbP, hsm) = pick [2,1,0,3]
            val lf = leafFor (false,false,sD)
        in apply_leaf lf (mT,pT,rT) (cA,cB,cC,cD) (rA,rB,rC,rD) hbP hsm g1 g2 g3 g4 hmPos end
      else if sD then
        (* a,b,c RIGHT, d LEFT: perm [3,1,2,0] -> positions (d=L, b=R, c=R, a=R), pattern (false,false,false) *)
        let val (cA,cB,cC,cD, rA,rB,rC,rD, g1,g2,g3,g4, hbP, hsm) = pick [3,1,2,0]
            val lf = leafFor (false,false,false)   (* pnnn *)
        in apply_leaf lf (mT,pT,rT) (cA,cB,cC,cD) (rA,rB,rC,rD) hbP hsm g1 g2 g3 g4 hmPos end
      else
        (* RRRR: leaf_nnnn, identity perm, all-RIGHT congs *)
        let val (cA,cB,cC,cD, rA,rB,rC,rD, g1,g2,g3,g4, hbP, hsm) = pick [0,1,2,3]
            val inst = beta_norm (Drule.infer_instantiate ctxtGR
              [(("m_L",0),ctermGR mT),(("p_L",0),ctermGR pT),(("r_L",0),ctermGR rT),
               (("a_L",0),ctermGR cA),(("b_L",0),ctermGR cB),(("c_L",0),ctermGR cC),(("d_L",0),ctermGR cD),
               (("e_L",0),ctermGR rA),(("f_L",0),ctermGR rB),(("g_L",0),ctermGR rC),(("h_L",0),ctermGR rD)] leaf_nnnn_thm)
        in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim
             (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hbP) hsm) g1) g2) g3) g4) hmPos end
  in fsq_commute (pT,rT) hfs_pr end;
val () = out "DSTEP_ROUTE_OK\n";

(* ============================================================================
   THE 16-BRANCH disjE on the 4 sign flags, producing four_sq(mult r p).
   hsa..hsd : signD m ap a , ...  (each = Disj (cong m ap a)(cong m (ap+a) 0))
   ============================================================================ *)
fun divide_all (a,b,c,d) (ap,bp,cp,dp) (mT,pT,rT) hbody hsum hmPos hsa hsb hsc hsd =
  let
    val goalC = four_sq (mult rT pT)
    fun branchD sA sB sC cgA cgB cgC =
      (* split hsd *)
      let val hdL = jT (cong mT dp d)
          val hdR = jT (cong mT (add dp d) ZeroC)
          val cL = let val h=Thm.assume (ctermGR hdL)
                   in Thm.implies_intr (ctermGR hdL) (route (sA,sB,sC,true) (a,b,c,d) (ap,bp,cp,dp) (mT,pT,rT) hbody hsum hmPos cgA cgB cgC h) end
          val cR = let val h=Thm.assume (ctermGR hdR)
                   in Thm.implies_intr (ctermGR hdR) (route (sA,sB,sC,false) (a,b,c,d) (ap,bp,cp,dp) (mT,pT,rT) hbody hsum hmPos cgA cgB cgC h) end
      in disjE_r (cong mT dp d, cong mT (add dp d) ZeroC, goalC) hsd cL cR end
    fun branchC sA sB cgA cgB =
      let val hcL = jT (cong mT cp c)
          val hcR = jT (cong mT (add cp c) ZeroC)
          val cL = let val h=Thm.assume (ctermGR hcL)
                   in Thm.implies_intr (ctermGR hcL) (branchD sA sB true cgA cgB h) end
          val cR = let val h=Thm.assume (ctermGR hcR)
                   in Thm.implies_intr (ctermGR hcR) (branchD sA sB false cgA cgB h) end
      in disjE_r (cong mT cp c, cong mT (add cp c) ZeroC, goalC) hsc cL cR end
    fun branchB sA cgA =
      let val hbL = jT (cong mT bp b)
          val hbR = jT (cong mT (add bp b) ZeroC)
          val cL = let val h=Thm.assume (ctermGR hbL)
                   in Thm.implies_intr (ctermGR hbL) (branchC sA true cgA h) end
          val cR = let val h=Thm.assume (ctermGR hbR)
                   in Thm.implies_intr (ctermGR hbR) (branchC sA false cgA h) end
      in disjE_r (cong mT bp b, cong mT (add bp b) ZeroC, goalC) hsb cL cR end
    val haL = jT (cong mT ap a)
    val haR = jT (cong mT (add ap a) ZeroC)
    val cAL = let val h=Thm.assume (ctermGR haL) in Thm.implies_intr (ctermGR haL) (branchB true h) end
    val cAR = let val h=Thm.assume (ctermGR haR) in Thm.implies_intr (ctermGR haR) (branchB false h) end
  in disjE_r (cong mT ap a, cong mT (add ap a) ZeroC, goalC) hsa cAL cAR end;
val () = out "DSTEP_DIVIDE_ALL_OK\n";

(* ============================================================================
   descent_step : !!p m. prime2 p ==> 1<m ==> m<p ==> four_sq(m*p)
                    ==> Ex r. (0<r) AND (r<m) AND four_sq(mult r p)
   Mirrors descent_strict but ADDS the divide (four_sq(m*r) -> four_sq(r*p)).
   ============================================================================ *)
val descent_step =
  let
    val pF = Free("p_ds2", natT); val mF = Free("m_ds2", natT)
    val hPrP = jT (prime2 pF); val hPr = Thm.assume (ctermGR hPrP)
    val h1mP = jT (lt (suc ZeroC) mF); val h1m = Thm.assume (ctermGR h1mP)
    val hmpP = jT (lt mF pF); val hmp = Thm.assume (ctermGR hmpP)
    val hfsP = jT (four_sq (mult mF pF)); val hfs = Thm.assume (ctermGR hfsP)
    val le12 = lt_0_suc_r (suc ZeroC)
    val hmPos = le_trans_d (suc ZeroC, suc (suc ZeroC), mF) le12 h1m
    val rF0 = Free("r_ds2v", natT)
    val goalP = Term.lambda rF0 (mkConj (lt ZeroC rF0) (mkConj (lt rF0 mF) (four_sq (mult rF0 pF))))
    val goalC = mkEx goalP
    val cmp0 = cong_mp_zero (mF, pF)
    val core =
      elim_four_sq "ds2" hfs (mult mF pF) goalC (fn (a,b,c,d) => fn hbody =>
        let
          val ex = signed_four_residue_sum (mF, a, b, c, d, mult mF pF) hmPos hbody cmp0
        in elim_signed_sum (mF, a, b, c, d) ex goalC (fn (ap,bp,cp,dp,r) =>
             fn hsum => fn hsa => fn hsb => fn hsc => fn hsd => fn hba => fn hbb => fn hbc => fn hbd =>
             let
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
               (* r<=m -> r<m strict via rm_excl *)
               val le_rm = r_le_m (mF, r, ap,bp,cp,dp) hsum hba hbb hbc hbd hmPos
               val djrm = le_eq_or_lt_d (r, mF) le_rm
               val lt_rm =
                 disjE_r (oeq r mF, lt r mF, lt r mF) djrm
                   (let val hP=jT (oeq r mF); val h=Thm.assume (ctermGR hP)
                        val fls = rm_excl (mF,pF,r, a,b,c,d, ap,bp,cp,dp)
                                    hsum hsa hsb hsc hsd hba hbb hbc hbd hbody hPr h1m hmp hmPos h
                    in Thm.implies_intr (ctermGR hP) (Thm.implies_elim (oFalse_elim_r (lt r mF)) fls) end)
                   (let val hP=jT (lt r mF); val h=Thm.assume (ctermGR hP)
                    in Thm.implies_intr (ctermGR hP) h end)
               (* THE DIVIDE : four_sq(mult r p) via the 16-branch disjE *)
               val fsq_rp = divide_all (a,b,c,d) (ap,bp,cp,dp) (mF,pF,r) hbody hsum hmPos hsa hsb hsc hsd
               (* assemble : 0<r AND r<m AND four_sq(r*p) *)
               val conj = conjI_r (lt ZeroC r, mkConj (lt r mF)(four_sq (mult r pF))) pos_r
                            (conjI_r (lt r mF, four_sq (mult r pF)) lt_rm fsq_rp)
               val exr = exI_r goalP r conj
             in exr end)
        end)
    val body4 = Thm.implies_intr (ctermGR hPrP) (Thm.implies_intr (ctermGR h1mP)
                 (Thm.implies_intr (ctermGR hmpP) (Thm.implies_intr (ctermGR hfsP) core)))
  in Thm.forall_intr (ctermGR pF) (Thm.forall_intr (ctermGR mF) body4) end;
val () = out ("descent_step hyps="^Int.toString(length(Thm.hyps_of descent_step))^"\n");
val () = out ("descent_step prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of descent_step)^"\n");
val () = out "DSTEP_PROVED\n";

(* ============================================================================
   VALIDATION : aconv against the intended descent_step (the antecedent of the
   banked iterate_discharge) + soundness probes.
   ============================================================================ *)
val descent_step_intended =
  let
    val pDS = Free("p_ds2", natT); val mDS = Free("m_ds2", natT)
    fun descConcl p m =
      mkEx (Term.lambda (Free("r_ds2v",natT))
        (mkConj (lt ZeroC (Free("r_ds2v",natT)))
           (mkConj (lt (Free("r_ds2v",natT)) m) (four_sq (mult (Free("r_ds2v",natT)) p)))));
  in Logic.all pDS (Logic.all mDS
       (Logic.mk_implies (jT (prime2 pDS),
        Logic.mk_implies (jT (lt (suc ZeroC) mDS),
        Logic.mk_implies (jT (lt mDS pDS),
        Logic.mk_implies (jT (four_sq (mult mDS pDS)),
          jT (descConcl pDS mDS)))))))
  end;
val ds_aconv = ((Thm.prop_of descent_step) aconv descent_step_intended);
val ds_0hyp  = (length (Thm.hyps_of descent_step) = 0);
val () = out ("DSTEP_VALIDATE aconv="^Bool.toString ds_aconv^" zero_hyp="^Bool.toString ds_0hyp^"\n");

(* PROBE 1: genuinely needs four_sq(m*p) *)
val ds_probe_needs_fs =
  let
    val pV = Free("p_ds2", natT); val mV = Free("m_ds2", natT)
    val concl = mkEx (Term.lambda (Free("r_ds2v",natT)) (mkConj (lt ZeroC (Free("r_ds2v",natT))) (mkConj (lt (Free("r_ds2v",natT)) mV) (four_sq (mult (Free("r_ds2v",natT)) pV)))))
    val wrong = Logic.all pV (Logic.all mV (Logic.mk_implies (jT (prime2 pV), Logic.mk_implies (jT (lt (suc ZeroC) mV), Logic.mk_implies (jT (lt mV pV), jT concl)))))
  in not ((Thm.prop_of descent_step) aconv wrong) end;
val () = out ("DSTEP_PROBE_NEEDS_FS "^Bool.toString ds_probe_needs_fs^"\n");
(* PROBE 2: conclusion subject is four_sq(r*p) (DIVIDED), not four_sq(m*r) *)
val ds_probe_divided =
  let
    val pV = Free("p_ds2", natT); val mV = Free("m_ds2", natT)
    val conclMR = mkEx (Term.lambda (Free("r_ds2v",natT)) (mkConj (lt ZeroC (Free("r_ds2v",natT))) (mkConj (lt (Free("r_ds2v",natT)) mV) (four_sq (mult mV (Free("r_ds2v",natT)))))))
    val wrong = Logic.all pV (Logic.all mV (Logic.mk_implies (jT (prime2 pV), Logic.mk_implies (jT (lt (suc ZeroC) mV), Logic.mk_implies (jT (lt mV pV), Logic.mk_implies (jT (four_sq (mult mV pV)), jT conclMR))))))
  in not ((Thm.prop_of descent_step) aconv wrong) end;
val () = out ("DSTEP_PROBE_DIVIDED "^Bool.toString ds_probe_divided^"\n");
(* PROBE 3: bound is STRICT r<m, not r<=m *)
val ds_probe_strict =
  let
    val pV = Free("p_ds2", natT); val mV = Free("m_ds2", natT)
    val conclLe = mkEx (Term.lambda (Free("r_ds2v",natT)) (mkConj (lt ZeroC (Free("r_ds2v",natT))) (mkConj (le (Free("r_ds2v",natT)) mV) (four_sq (mult (Free("r_ds2v",natT)) pV)))))
    val wrong = Logic.all pV (Logic.all mV (Logic.mk_implies (jT (prime2 pV), Logic.mk_implies (jT (lt (suc ZeroC) mV), Logic.mk_implies (jT (lt mV pV), Logic.mk_implies (jT (four_sq (mult mV pV)), jT conclLe))))))
  in not ((Thm.prop_of descent_step) aconv wrong) end;
val () = out ("DSTEP_PROBE_STRICT "^Bool.toString ds_probe_strict^"\n");

val () = if ds_aconv andalso ds_0hyp andalso ds_probe_needs_fs andalso ds_probe_divided andalso ds_probe_strict
         then out "DSTEP_ALL_OK\n" else out "DSTEP_VALIDATE_FAILED\n";

(* ===== export a checkpoint banking descent_step ===== *)
val () = out "DSTEP_DRIVER_DONE\n";
(* ===== iterate_discharge ===== *)
val () = out "RESTORE_OK\n";

(* ===================== GR object impI / mp ===================== *)
fun mp_r (At,Bt) hImp hA =
  Thm.implies_elim (Thm.implies_elim
    (beta_norm (Drule.infer_instantiate ctxtGR [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] mp_vR)) hImp) hA;
fun impI_r (At,Bt) himp =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR [(("A",0), ctermGR At),(("B",0), ctermGR Bt)] impI_vR)) himp;
val oneT = suc ZeroC;
val twoT = suc (suc ZeroC);
fun mult1l_d n = beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR n)] mult_1_left_vR);
val () = out "L4_HELPERS_OK\n";

(* ===================== n_parity ===================== *)
fun evenBody n = mkEx (Term.lambda (Free("ke",natT)) (oeq n (add (Free("ke",natT))(Free("ke",natT)))));
fun oddBody  n = mkEx (Term.lambda (Free("ko",natT)) (oeq n (suc (add (Free("ko",natT))(Free("ko",natT))))));
fun parityGoal n = jT (mkDisj (evenBody n)(oddBody n));
val n_parity =
  let
    val nPhi = Free("n_phi_par", natT);
    val PhiAbs = Term.lambda nPhi (parityGoal nPhi);
    val base =
      let val a00 = add0_d ZeroC
          val body0 = oeqSym_r2 a00
          val Pe = Term.lambda (Free("ke",natT)) (oeq ZeroC (add (Free("ke",natT))(Free("ke",natT))))
          val ev0 = exI_r Pe ZeroC body0
      in disjI1_r (evenBody ZeroC, oddBody ZeroC) ev0 end;
    val step =
      let
        val xF = Free("x_par", natT);
        val hIH = Thm.assume (ctermGR (parityGoal xF));
        val caseE =
          let val Pe = Term.lambda (Free("ke",natT)) (oeq xF (add (Free("ke",natT))(Free("ke",natT))))
              fun bodyE k (hk:thm) =
                let val sx = Suc_cong_r hk
                    val Po = Term.lambda (Free("ko",natT)) (oeq (suc xF)(suc (add (Free("ko",natT))(Free("ko",natT)))))
                    val od = exI_r Po k sx
                in disjI2_r (evenBody (suc xF), oddBody (suc xF)) od end
              val hE = Thm.assume (ctermGR (jT (evenBody xF)))
              val g = exE_r (Pe, mkDisj (evenBody (suc xF))(oddBody (suc xF))) hE "ke_w" natT bodyE
          in Thm.implies_intr (ctermGR (jT (evenBody xF))) g end;
        val caseO =
          let val Po = Term.lambda (Free("ko",natT)) (oeq xF (suc (add (Free("ko",natT))(Free("ko",natT)))))
              fun bodyO k (hk:thm) =
                let val sx = Suc_cong_r hk
                    val a1 = addSuc_d (k, suc k)
                    val a2 = addSucr_d (k, k)
                    val a2s= Suc_cong_r a2
                    val aEq= oeqTrans_r2 (a1, a2s)
                    val body = oeqTrans_r2 (sx, oeqSym_r2 aEq)
                    val Pe = Term.lambda (Free("ke",natT)) (oeq (suc xF)(add (Free("ke",natT))(Free("ke",natT))))
                    val ev = exI_r Pe (suc k) body
                in disjI1_r (evenBody (suc xF), oddBody (suc xF)) ev end
              val hO = Thm.assume (ctermGR (jT (oddBody xF)))
              val g = exE_r (Po, mkDisj (evenBody (suc xF))(oddBody (suc xF))) hO "ko_w" natT bodyO
          in Thm.implies_intr (ctermGR (jT (oddBody xF))) g end;
        val concl = disjE_r (evenBody xF, oddBody xF, mkDisj (evenBody (suc xF))(oddBody (suc xF))) hIH caseE caseO
      in Thm.forall_intr (ctermGR xF) (Thm.implies_intr (ctermGR (parityGoal xF)) concl) end;
    val nF = Free("n_par", natT);
    val indInst = beta_norm (Drule.infer_instantiate ctxtGR
                    [(("Phi",0), ctermGR PhiAbs),(("k",0), ctermGR nF)] meta_nat_induct_v2)
    val r1 = Thm.implies_elim indInst base
    val r2 = Thm.implies_elim r1 step
  in Thm.forall_intr (ctermGR nF) r2 end;
fun parity_at n = Thm.forall_elim (ctermGR n) n_parity;   (* Disj(evenBody n)(oddBody n) *)
val () = out ("L4_NPARITY hyps="^Int.toString(length(Thm.hyps_of n_parity))^"\n");

(* ===================== even_prime_is_two ===================== *)
fun two_mult_eq k =
  let val m1 = multSuc_d (suc ZeroC, k)
      val m2 = multSuc_d (ZeroC, k)
      val m3 = mult0_d k
      val m2b= oeqTrans_r2 (m2, add_cong_r_d (k, mult ZeroC k, ZeroC) m3)
      val m2c= oeqTrans_r2 (m2b, add0r_d k)
      val r  = oeqTrans_r2 (m1, add_cong_r_d (k, mult (suc ZeroC) k, k) m2c)
  in r end;
fun two_neq_one h21 =
  let val h10 = Suc_inj_g (suc ZeroC, ZeroC) h21
  in Suc_neq_Zero_g ZeroC h10 end;
fun prime_div_at p hPrime d =
  let val hForall = conjunct2_r (lt (suc ZeroC) p, mkForall (ppAbs p)) hPrime
  in allE_r (ppAbs p) d hForall end;
fun even_prime_is_two p hPrime hEven =
  let
    val Pe = Term.lambda (Free("ke",natT)) (oeq p (add (Free("ke",natT))(Free("ke",natT))))
    fun bodyE k (hk:thm) =
      let
        val tme = two_mult_eq k
        val pEqMult = oeqTrans_r2 (hk, oeqSym_r2 tme)
        val Pdvd = Term.lambda (Free("kd",natT)) (oeq p (mult twoT (Free("kd",natT))))
        val hDvd = exI_r Pdvd k pEqMult
        val himp = prime_div_at p hPrime twoT
        val hdisj= mp_r (dvd twoT p, mkDisj (oeq twoT oneT)(oeq twoT p)) himp hDvd
        val case1 =
          let val h21 = Thm.assume (ctermGR (jT (oeq twoT oneT)))
              val fls = two_neq_one h21
          in Thm.implies_intr (ctermGR (jT (oeq twoT oneT)))
               (Thm.implies_elim (oFalse_elim_r (oeq p twoT)) fls) end
        val case2 =
          let val h2p = Thm.assume (ctermGR (jT (oeq twoT p)))
          in Thm.implies_intr (ctermGR (jT (oeq twoT p))) (oeqSym_r2 h2p) end
      in disjE_r (oeq twoT oneT, oeq twoT p, oeq p twoT) hdisj case1 case2 end
  in exE_r (Pe, oeq p twoT) hEven "kep_w" natT bodyE end;
val () = out "L4_EVEN2_OK\n";

(* ===================== four_sq 2 (witness 1,1,0,0) ===================== *)
val fsq2 =
  let
    fun sqA x = mult x x;
    val ms  = multSuc_d (ZeroC, oneT)            (* mult 1 1 = add 1 (mult 0 1) *)
    val mc  = multcomm_g (ZeroC, oneT)            (* mult 0 1 = mult 1 0 *)
    val m10 = mult0r_d oneT                        (* mult 1 0 = 0 *)
    val m0_1= oeqTrans_r2 (mc, m10)               (* mult 0 1 = 0 *)
    val ac  = add_cong_r_d (oneT, mult ZeroC oneT, ZeroC) m0_1
    val a10 = add0r_d oneT
    val sq1eq = oeqTrans_r2 (oeqTrans_r2 (ms, ac), a10)   (* mult 1 1 = 1 *)
    val z00 = mult0r_d ZeroC                       (* 0*0 = 0 *)
    val l1 = add_cong_l_d (sqA oneT, oneT, sqA oneT) sq1eq
    val l2 = add_cong_r_d (oneT, sqA oneT, oneT) sq1eq
    val leftEq = oeqTrans_r2 (l1, l2)              (* (1*1+1*1)=add 1 1 *)
    val rr1 = add_cong_l_d (sqA ZeroC, ZeroC, sqA ZeroC) z00
    val rr2 = add_cong_r_d (ZeroC, sqA ZeroC, ZeroC) z00
    val rr3 = add0_d ZeroC
    val rightEq = oeqTrans_r2 (oeqTrans_r2 (rr1, rr2), rr3)  (* (0*0+0*0)=0 *)
    val f1 = add_cong_l_d (add (sqA oneT)(sqA oneT), add oneT oneT, add (sqA ZeroC)(sqA ZeroC)) leftEq
    val f2 = add_cong_r_d (add oneT oneT, add (sqA ZeroC)(sqA ZeroC), ZeroC) rightEq
    val f3 = add0r_d (add oneT oneT)
    val rhsEq = oeqTrans_r2 (oeqTrans_r2 (f1, f2), f3)      (* rhs = add 1 1 *)
    val a11 = addSuc_d (ZeroC, oneT)              (* add 1 1 = Suc(add 0 1) *)
    val a01 = add0_d oneT
    val a11s= oeqTrans_r2 (a11, Suc_cong_r a01)   (* add 1 1 = Suc 1 = 2 *)
    val twoEqAdd = oeqSym_r2 a11s                  (* 2 = add 1 1 *)
    val body = oeqTrans_r2 (twoEqAdd, oeqSym_r2 rhsEq)
  in four_sq_witness (twoT, oneT, oneT, ZeroC, ZeroC) body end;
val () = out ("L4_FSQ2 hyps="^Int.toString(length(Thm.hyps_of fsq2))^"\n");
val () = out "HEAD_DONE\n";

(* ============================================================================
   DESCENT_STEP (the assumed hypothesis) and the ITERATE + DISCHARGE.
   ============================================================================ *)
val () = out "DESC_BEGIN\n";

(* descent_step term : !!p m. prime2 p ==> 1<m ==> m<p ==> four_sq(m*p)
                        ==> Ex r. (0<r) AND (r<m) AND four_sq(r*p) *)
val pDS = Free("p_ds", natT);
val mDS = Free("m_ds", natT);
fun descConcl p m =
  mkEx (Term.lambda (Free("r_ds",natT))
    (mkConj (lt ZeroC (Free("r_ds",natT)))
       (mkConj (lt (Free("r_ds",natT)) m) (four_sq (mult (Free("r_ds",natT)) p)))));
val descent_step_prop =
  Logic.all pDS (Logic.all mDS
    (Logic.mk_implies (jT (prime2 pDS),
     Logic.mk_implies (jT (lt (suc ZeroC) mDS),
     Logic.mk_implies (jT (lt mDS pDS),
     Logic.mk_implies (jT (four_sq (mult mDS pDS)),
       jT (descConcl pDS mDS)))))));
val hDescStep = Thm.assume (ctermGR descent_step_prop);
(* primemult_thm is keyed on FREE vars p_B/m_B -> varify to schematic before instantiating *)
val primemult_v = varify primemult_thm;
(* instantiate descent_step at (p,m), apply 4 premises -> Ex r. ... *)
fun descent_at (p,m) hPr h1ltm hmltp hfsq =
  let val i0 = Thm.forall_elim (ctermGR m) (Thm.forall_elim (ctermGR p) hDescStep)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim i0 hPr) h1ltm) hmltp) hfsq end;
val () = out "DESC_STEP_ASSUMED\n";

(* ============================================================================
   descent_to_one : given prime2 pPrime, prove (via strong induct)
     P k := Imp (0<k) (Imp (k<p) (Imp (four_sq(k*p)) (four_sq p)))   for all k.
   ============================================================================ *)
fun build_prime_is_fsq pPrime hPrime =
  let
    val P = pPrime
    fun PdescBody m =
      mkImp (lt ZeroC m) (mkImp (lt m P) (mkImp (four_sq (mult m P)) (four_sq P)));
    val PdescAbs = Term.lambda (Free("m_dsc",natT)) (PdescBody (Free("m_dsc",natT)));   (* nat=>o *)
    (* --- strong induction step : !!n. (!!m. m<n ==> Pdesc m) ==> Pdesc n --- *)
    val stepThm =
      let
        val nStep = Free("n_dsc", natT);
        (* IH : !!m_g. lt m_g nStep ==> Trueprop (PdescBody m_g) *)
        val mIH = Free("m_g", natT);
        val Gprop = Logic.all mIH (Logic.mk_implies (jT (lt mIH nStep), jT (PdescBody mIH)));
        val Hthm  = Thm.assume (ctermGR Gprop);
        fun applyIH dt h_lt = Thm.implies_elim (Thm.forall_elim (ctermGR dt) Hthm) h_lt;  (* PdescBody dt *)
        (* build Trueprop (PdescBody nStep) via impI_r x3 *)
        val inner =     (* a meta-impl: Trueprop(0<n) ==> Trueprop( Imp (n<p)(Imp (fsq(n*p))(fsq p)) ) *)
          let
            val h0lt = Thm.assume (ctermGR (jT (lt ZeroC nStep)))   (* 0<n *)
            val mid =   (* meta-impl: Trueprop(n<p) ==> Trueprop( Imp(fsq(n*p))(fsq p) ) *)
              let
                val hltp = Thm.assume (ctermGR (jT (lt nStep P)))   (* n<p *)
                val inn = (* meta-impl: Trueprop(fsq(n*p)) ==> Trueprop(fsq p) *)
                  let
                    val hfsq = Thm.assume (ctermGR (jT (four_sq (mult nStep P))))   (* fsq(n*p) *)
                    (* === core: prove four_sq P === *)
                    (* expose nStep = Suc w from 0<n *)
                    val PwAbs = Term.lambda (Free("w0",natT)) (oeq nStep (add (suc ZeroC)(Free("w0",natT))))
                    fun afterW w hw =     (* hw : oeq n (add (Suc 0) w) *)
                      let
                        (* n = Suc w : add (Suc 0) w = Suc(add 0 w) = Suc w *)
                        val a1 = addSuc_d (ZeroC, w)
                        val a2 = add0_d w
                        val nEqSw = oeqTrans_r2 (hw, oeqTrans_r2 (a1, Suc_cong_r a2))   (* n = Suc w *)
                        (* dzos w : w=0 (n=1) or w=Suc w1 (1<n) *)
                        val dzw = dzos_d w
                        val caseW0 =
                          let val hw0 = Thm.assume (ctermGR (jT (oeq w ZeroC)))   (* w=0 *)
                              (* n = Suc 0 = 1 *)
                              val nEq1 = oeqTrans_r2 (nEqSw, Suc_cong_r hw0)        (* n = Suc 0 = 1 *)
                              (* mult n P = mult 1 P = P : rewrite fsq(n*p).  mult 1 P = P (mult1l) *)
                              (* first rewrite n -> 1 in fsq(mult n P) : fsq(mult 1 P) *)
                              val zfs = Free("zfs1", natT)
                              val Pfs1 = Term.lambda zfs (four_sq (mult zfs P))
                              val hfsq1 = oeq_rw_r (Pfs1, nStep, oneT) nEq1 hfsq   (* fsq(mult 1 P) *)
                              (* mult 1 P = P *)
                              val m1eq = mult1l_d P                                (* oeq (mult 1 P) P *)
                              val zfs2 = Free("zfs2", natT)
                              val Pfs2 = Term.lambda zfs2 (four_sq zfs2)
                              val r = oeq_rw_r (Pfs2, mult oneT P, P) m1eq hfsq1   (* fsq P *)
                          in Thm.implies_intr (ctermGR (jT (oeq w ZeroC))) r end
                        val Pw1 = Term.lambda (Free("w1",natT)) (oeq w (suc (Free("w1",natT))))
                        val caseWS =
                          let val hws = Thm.assume (ctermGR (jT (mkEx Pw1)))
                              fun afterW1 w1 hw1 =     (* hw1 : oeq w (Suc w1) *)
                                let
                                  (* n = Suc w = Suc(Suc w1) so 1<n.
                                     1<n = le (Suc(Suc 0)) n = Ex p. oeq n (add (Suc(Suc 0)) p), witness w1:
                                       add (Suc(Suc 0)) w1 = Suc(Suc w1) = Suc w = n. *)
                                  val nEqSSw1 = oeqTrans_r2 (nEqSw, Suc_cong_r hw1)   (* n = Suc(Suc w1) *)
                                  val t1 = addSuc_d (suc ZeroC, w1)     (* add (Suc(Suc 0)) w1 = Suc(add (Suc 0) w1) *)
                                  val t2 = addSuc_d (ZeroC, w1)         (* add (Suc 0) w1 = Suc(add 0 w1) *)
                                  val t3 = add0_d w1
                                  val t2s= oeqTrans_r2 (t2, Suc_cong_r t3)  (* add (Suc 0) w1 = Suc w1 *)
                                  val t1s= oeqTrans_r2 (t1, Suc_cong_r t2s) (* add (Suc(Suc 0)) w1 = Suc(Suc w1) *)
                                  val nAdd = oeqTrans_r2 (nEqSSw1, oeqSym_r2 t1s)  (* n = add (Suc(Suc 0)) w1 *)
                                  val h1ltn = le_intro_d (suc (suc ZeroC), nStep, w1) nAdd  (* le 2 n = lt 1 n *)
                                  (* apply descent_step at (P, nStep) *)
                                  val hex = descent_at (P, nStep) hPrime h1ltn hltp hfsq  (* Ex r. 0<r /\ r<n /\ fsq(r*p) *)
                                  val PrAbs = Term.lambda (Free("r_ds",natT))
                                                (mkConj (lt ZeroC (Free("r_ds",natT)))
                                                   (mkConj (lt (Free("r_ds",natT)) nStep) (four_sq (mult (Free("r_ds",natT)) P))))
                                  fun afterR r hConj =   (* hConj : 0<r /\ r<n /\ fsq(r*p) *)
                                    let
                                      val c1 = lt ZeroC r
                                      val rest = mkConj (lt r nStep) (four_sq (mult r P))
                                      val h0r = conjunct1_r (c1, rest) hConj                 (* 0<r *)
                                      val hrest = conjunct2_r (c1, rest) hConj
                                      val hrltn = conjunct1_r (lt r nStep, four_sq (mult r P)) hrest  (* r<n *)
                                      val hfrp  = conjunct2_r (lt r nStep, four_sq (mult r P)) hrest  (* fsq(r*p) *)
                                      val hrltp = lt_trans_r (r, nStep, P) hrltn hltp        (* r<p *)
                                      (* apply IH at r : Pdesc r, then mp x3 *)
                                      val pdr = applyIH r hrltn                                (* PdescBody r *)
                                      val s1 = mp_r (lt ZeroC r,
                                                 mkImp (lt r P)(mkImp (four_sq (mult r P))(four_sq P))) pdr h0r
                                      val s2 = mp_r (lt r P, mkImp (four_sq (mult r P))(four_sq P)) s1 hrltp
                                      val s3 = mp_r (four_sq (mult r P), four_sq P) s2 hfrp     (* fsq P *)
                                    in s3 end
                                in exE_r (PrAbs, four_sq P) hex "r_ds" natT afterR end
                          in Thm.implies_intr (ctermGR (jT (mkEx Pw1)))
                               (exE_r (Pw1, four_sq P) hws "w1_ds" natT afterW1) end
                      in disjE_r (oeq w ZeroC, mkEx Pw1, four_sq P) dzw caseW0 caseWS end
                    val coreFsqP = exE_r (PwAbs, four_sq P) h0lt "w0_ds" natT afterW   (* four_sq P *)
                  in Thm.implies_intr (ctermGR (jT (four_sq (mult nStep P)))) coreFsqP end
                (* inn : Trueprop(fsq(n*p)) ==> Trueprop(fsq p);  wrap to object Imp *)
                val objInn = impI_r (four_sq (mult nStep P), four_sq P) inn
              in Thm.implies_intr (ctermGR (jT (lt nStep P))) objInn end
            val objMid = impI_r (lt nStep P, mkImp (four_sq (mult nStep P))(four_sq P)) mid
          in Thm.implies_intr (ctermGR (jT (lt ZeroC nStep))) objMid end
        val objInner = impI_r (lt ZeroC nStep, mkImp (lt nStep P)(mkImp (four_sq (mult nStep P))(four_sq P))) inner
          (* objInner : Trueprop (PdescBody nStep) *)
      in Thm.forall_intr (ctermGR nStep) (Thm.implies_intr (ctermGR Gprop) objInner) end;
    (* apply strong_induct at P := PdescAbs, k := kFin -> PdescBody kFin -> !!k. PdescBody k *)
    val kFin = Free("k_dsc", natT);
    val siInst = beta_norm (Drule.infer_instantiate ctxtGR
                   [(("P",0), ctermGR PdescAbs),(("k",0), ctermGR kFin)] strong_induct)
    val pdK = Thm.implies_elim siInst stepThm                       (* PdescBody kFin *)
    val descAll = Thm.forall_intr (ctermGR kFin) pdK;              (* !!k. PdescBody k *)
    fun Pdesc_at m = Thm.forall_elim (ctermGR m) descAll;         (* PdescBody m *)

    (* ---- now case on parity of P to get four_sq P ---- *)
    val par = parity_at P;                                         (* Disj(evenBody P)(oddBody P) *)
    (* EVEN case : P = 2 -> four_sq 2 -> rewrite to four_sq P *)
    val caseEven =
      let val hEv = Thm.assume (ctermGR (jT (evenBody P)))
          val pEq2 = even_prime_is_two P hPrime hEv               (* oeq P 2 *)
          val zf = Free("zfp2", natT)
          val Pf = Term.lambda zf (four_sq zf)
          val r = oeq_rw_r (Pf, twoT, P) (oeqSym_r2 pEq2) fsq2     (* four_sq P *)
      in Thm.implies_intr (ctermGR (jT (evenBody P))) r end;
    (* ODD case : P = Suc(k+k) -> primemult_thm gives m', 0<m', m'<p, fsq(m'*p) -> Pdesc m' *)
    val caseOdd =
      let
        val Po = Term.lambda (Free("ko",natT)) (oeq P (suc (add (Free("ko",natT))(Free("ko",natT)))))
        fun afterK k hk =     (* hk : oeq P (Suc(add k k)) *)
          let
            (* primemult_thm at p_B:=P, m_B:=k.  premises: prime2 P, oeq P (Suc(k+k)). *)
            (* primemult_thm lives on thyB (extends thyGR); instantiate on ctxtB.
               ctxtGR-built hyps compose up to thyB automatically. *)
            val pmInst = beta_norm (Drule.infer_instantiate ctxtB
                           [(("p_B",0), ctermB P),(("m_B",0), ctermB k)] primemult_v)
            val pmEx = Thm.implies_elim (Thm.implies_elim pmInst hPrime) hk
                       (* Ex m_pf. 0<m_pf /\ m_pf<P /\ fsq(m_pf*P) *)
            val PmAbs = Term.lambda (Free("m_pf",natT))
                          (mkConj (lt ZeroC (Free("m_pf",natT)))
                             (mkConj (lt (Free("m_pf",natT)) P) (four_sq (mult (Free("m_pf",natT)) P))))
            fun afterM m hConj =
              let
                val c1 = lt ZeroC m
                val rest = mkConj (lt m P) (four_sq (mult m P))
                val h0m = conjunct1_r (c1, rest) hConj             (* 0<m *)
                val hr2 = conjunct2_r (c1, rest) hConj
                val hmltp = conjunct1_r (lt m P, four_sq (mult m P)) hr2   (* m<P *)
                val hfmp  = conjunct2_r (lt m P, four_sq (mult m P)) hr2   (* fsq(m*P) *)
                val pdm = Pdesc_at m                               (* PdescBody m *)
                val s1 = mp_r (lt ZeroC m, mkImp (lt m P)(mkImp (four_sq (mult m P))(four_sq P))) pdm h0m
                val s2 = mp_r (lt m P, mkImp (four_sq (mult m P))(four_sq P)) s1 hmltp
                val s3 = mp_r (four_sq (mult m P), four_sq P) s2 hfmp   (* four_sq P *)
              in s3 end
          in exE_r (PmAbs, four_sq P) pmEx "m_pf" natT afterM end
        val hOd = Thm.assume (ctermGR (jT (oddBody P)))
        val g = exE_r (Po, four_sq P) hOd "ko_w" natT afterK
      in Thm.implies_intr (ctermGR (jT (oddBody P))) g end;
    val fsqP = disjE_r (evenBody P, oddBody P, four_sq P) par caseEven caseOdd  (* four_sq P *)
  in fsqP end;
val () = out "DESC_TO_ONE_FN_READY\n";

(* ============================================================================
   prime_is_fsq : !!p. prime2 p ==> four_sq p
   ============================================================================ *)
val prime_is_fsq =
  let
    val pF = Free("p_pif", natT);
    val hPr = Thm.assume (ctermGR (jT (prime2 pF)));
    val fsqp = build_prime_is_fsq pF hPr;            (* four_sq p *)
    val disch = Thm.implies_intr (ctermGR (jT (prime2 pF))) fsqp;
  in Thm.forall_intr (ctermGR pF) disch end;          (* !!p. prime2 p ==> four_sq p *)
val () = out ("L4_PRIME_IS_FSQ hyps="^Int.toString(length(Thm.hyps_of prime_is_fsq))^"\n");
val () = out ("L4_PRIME_IS_FSQ prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of prime_is_fsq)^"\n");

(* ============================================================================
   DISCHARGE : chain lagrange_assembly -> !!n. four_sq n ; then implies_intr descent_step.
   ============================================================================ *)
val allFsq = Thm.implies_elim lagrange_assembly prime_is_fsq;   (* !!n. four_sq n   (open hyp: descent_step) *)
val () = out ("L4_ALLFSQ hyps="^Int.toString(length(Thm.hyps_of allFsq))^"\n");
val iterate_discharge = Thm.implies_intr (ctermGR descent_step_prop) allFsq;
val () = out ("L4_ITER_DISCHARGE hyps="^Int.toString(length(Thm.hyps_of iterate_discharge))^"\n");
val () = out ("L4_ITER_DISCHARGE prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of iterate_discharge)^"\n");
val () = out "DESC_DONE\n";

(* ============================================================================
   VALIDATION : aconv against the intended statement + soundness probes.
   ============================================================================ *)
fun clean s = String.translate (fn c => if c = #"\n" then " " else String.str c) s;
val () = out ("ITER_FULL_PROP = "^clean(Syntax.string_of_term ctxtGR (Thm.prop_of iterate_discharge))^" ::END\n");

(* intended : descent_step_prop ==> (!!n. four_sq n) *)
val nFin = Free("n_fin", natT);
val iter_intended = Logic.mk_implies (descent_step_prop, Logic.all nFin (jT (four_sq nFin)));
val iter_aconv = ((Thm.prop_of iterate_discharge) aconv iter_intended);
val iter_0hyp  = (length (Thm.hyps_of iterate_discharge) = 0);
val () = out ("L4_ITER_VALIDATE aconv="^Bool.toString iter_aconv^" zero_hyp="^Bool.toString iter_0hyp^"\n");

(* SOUNDNESS PROBE 1 : iterate_discharge must NOT be the unconditional !!n. four_sq n
   (it must keep the descent_step antecedent). *)
val probe1 = not ((Thm.prop_of iterate_discharge) aconv (Logic.all nFin (jT (four_sq nFin))));
(* SOUNDNESS PROBE 2 : the antecedent is genuinely the descent step (mentions the
   strict r<m + four_sq(m*p) premise + the divided conclusion four_sq(r*p)).
   Check by aconv: the LHS of the implication equals descent_step_prop. *)
val probe2 =
  let val (lhs, _) = Logic.dest_implies (Thm.prop_of iterate_discharge)
  in lhs aconv descent_step_prop end;
(* SOUNDNESS PROBE 3 : dropping the four_sq(m*p) premise from the antecedent gives a
   DIFFERENT (weaker-antecedent) theorem the kernel did NOT prove (i.e. our thm really
   used that premise's PRESENCE in the antecedent). *)
val descent_step_noFsq =
  Logic.all pDS (Logic.all mDS
    (Logic.mk_implies (jT (prime2 pDS),
     Logic.mk_implies (jT (lt (suc ZeroC) mDS),
     Logic.mk_implies (jT (lt mDS pDS),
       jT (descConcl pDS mDS))))));
val iter_intended_weak = Logic.mk_implies (descent_step_noFsq, Logic.all nFin (jT (four_sq nFin)));
val probe3 = not ((Thm.prop_of iterate_discharge) aconv iter_intended_weak);
(* SOUNDNESS PROBE 4 : weakening r<m (STRICT) to r<=m in the antecedent gives a different
   antecedent (we used the strict descent, not the non-strict descent_residue). *)
val descConcl_nonstrict =
  fn (p,m) => mkEx (Term.lambda (Free("r_ds",natT))
    (mkConj (lt ZeroC (Free("r_ds",natT)))
       (mkConj (le (Free("r_ds",natT)) m) (four_sq (mult (Free("r_ds",natT)) p)))));
val descent_step_nonstrict =
  Logic.all pDS (Logic.all mDS
    (Logic.mk_implies (jT (prime2 pDS),
     Logic.mk_implies (jT (lt (suc ZeroC) mDS),
     Logic.mk_implies (jT (lt mDS pDS),
     Logic.mk_implies (jT (four_sq (mult mDS pDS)),
       jT (descConcl_nonstrict (pDS,mDS))))))));
val iter_intended_nonstrict = Logic.mk_implies (descent_step_nonstrict, Logic.all nFin (jT (four_sq nFin)));
val probe4 = not ((Thm.prop_of iterate_discharge) aconv iter_intended_nonstrict);

val () = out ("L4_ITER_PROBE noUncond="^Bool.toString probe1
              ^" antecedentIsDescentStep="^Bool.toString probe2
              ^" needsFsqPremise="^Bool.toString probe3
              ^" needsStrict="^Bool.toString probe4^"\n");

(* axiom audit : the delta added NO new axiom (no add_axiom_global). The thm's only
   classical assumption is whatever the base carries; we add none. *)
val () = if iter_aconv andalso iter_0hyp andalso probe1 andalso probe2 andalso probe3 andalso probe4
         then out "L4_ITER_ALL_OK\n" else out "L4_ITER_PROBES_FAILED\n";

(* also surface prime_is_fsq's single hyp = the descent_step (for the report) *)
val () = out ("PIF_HYP = "^(case Thm.hyps_of prime_is_fsq of
                 [h] => clean(Syntax.string_of_term ctxtGR h)
               | _ => "??")^" ::END\n");
val pif_hyp_is_descstep = (case Thm.hyps_of prime_is_fsq of [h] => h aconv descent_step_prop | _ => false);
val () = out ("L4_PIF_HYP_IS_DESCSTEP "^Bool.toString pif_hyp_is_descstep^"\n");
val () = out "VALIDATE_DONE\n";

(* ===== FINAL CLOSURE ===== *)
val () = out "MEGA_CLOSURE_BEGIN\n";
val ds_matches = ((Thm.prop_of descent_step) aconv descent_step_prop);
val () = out ("MEGA_DSMATCH "^Bool.toString ds_matches^"\n");
val lagrange_four_square = Thm.implies_elim iterate_discharge descent_step;
val () = out ("MEGA lagrange_four_square hyps="^Int.toString(length(Thm.hyps_of lagrange_four_square))^"\n");
val () = out ("MEGA_LFS_PROP "^Syntax.string_of_term ctxtGR (Thm.prop_of lagrange_four_square)^"\n");
val nHd = Free("n_head", natT);
val fsqN = Thm.forall_elim (ctermGR nHd) lagrange_four_square;
val () = out ("MEGA_FSQN_PROP "^Syntax.string_of_term ctxtGR (Thm.prop_of fsqN)^"\n");
val lfs_0hyp = (length (Thm.hyps_of lagrange_four_square) = 0);
val lfs_intended = Logic.all (Free("n_l4",natT)) (jT (four_sq (Free("n_l4",natT))));
val lfs_aconv = ((Thm.prop_of lagrange_four_square) aconv lfs_intended);
val () = out ("MEGA_VALIDATE aconv="^Bool.toString lfs_aconv^" zero_hyp="^Bool.toString lfs_0hyp^"\n");
val () = if ds_matches andalso lfs_aconv andalso lfs_0hyp
         then out "MEGA_LAGRANGE_FOUR_SQUARE_PROVED\n" else out "MEGA_LAGRANGE_FAILED\n";
val () = out "MEGA_DONE\n";
