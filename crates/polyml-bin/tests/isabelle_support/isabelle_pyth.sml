(* ============================================================================
   THE KEY LEMMA for Pythagorean triples:
     coprime u v  ==>  u*v = w*w  ==>  EX s t. u = s*s  AND  v = t*t.
   (A product of coprime naturals is a perfect square only if each factor is.)

   coprime u v  is the with_gcd PREDICATE form:  Forall (%d. d|u ==> d|v ==> d=1).

   ROUTE B : strong induction on w, via Euclid's lemma + mult_left_cancel.
     P(w) := !u v. coprime u v -> u*v = w*w
                   -> (EX s. u = s*s) AND (EX t. v = t*t).
   Step at w (strong IH at all w' < w):  fix u, v ; assume coprime, u*v = w*w.
     * u = 1 : v = u*v = w*w, so u = 1*1 and v = w*w.  (s:=1, t:=w)
     * u = 0 : w*w = 0 -> w = 0 ; coprime u v with v|0,v|v forces v = 1.  (s:=0, t:=1)
     * u >= 2 : prime_divisor_exists gives a prime p | u.  p | u*v = w*w, Euclid -> p|w.
         p does NOT divide v (else p|u,p|v,coprime -> p=1 contra 1<p).
         w = p*w' ; u*v = p^2*w'^2 ; p|u*v, p~|v, Euclid -> p|u ; u = p*u1 ;
         cancel one p : u1*v = p*w'^2 ; p|u1*v, p~|v, Euclid -> p|u1 ; u1 = p*u' ;
         cancel one p : u'*v = w'^2 ; u = p^2*u'.
         coprime u' v (divisors of u' divide u) ; w' < w (p>=2, w!=0 in this branch).
         IH(w') at (u',v) -> u' = s'^2, v = t^2 -> u = (p*s')^2, v = t^2.
   ============================================================================ *)
val () = out "KEY_DELTA_BEGIN\n";

(* ---------------------------------------------------------------------------
   Local helper lemmas on ctxtS2 (mult_eq_zero, mult_left_cancel) + instantiators
   --------------------------------------------------------------------------- *)
val add_eq_zero_left_vS = varify add_eq_zero_left;   (* oeq (add a b) 0 ==> oeq a 0 *)
val mult_0_vS_l   = varify mult_0;                   (* oeq (mult 0 n) 0 *)
val mult_Suc_vS_l = varify mult_Suc;                 (* oeq (mult (Suc m) n) (add n (mult m n)) *)
fun mult0lS_at t = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] mult_0_vS_l);
fun multSuclS_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtS2
       [(("m",0), ctermS2 mt),(("n",0), ctermS2 nt)] mult_Suc_vS_l);

(* euclid_lemma instantiator on ctxtS2 *)
val euclid_lemma_vS2 = varify euclid_lemma;          (* prime2 p ==> p|(a*b) ==> p|a \/ p|b *)
fun euclid_lemma_atS (pT,aT,bT) hpr hdvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("p",0), ctermS2 pT), (("a",0), ctermS2 aT), (("b",0), ctermS2 bT)] euclid_lemma_vS2)
  in (inst OF [hpr]) OF [hdvd] end;

(* prime_divisor_exists instantiator on ctxtS2 : le 2 n ==> Ex p. prime2 p /\ p|n *)
val prime_divisor_exists_vS2 = varify prime_divisor_exists;
fun prime_divisor_exists_atS nt hle2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 nt)] prime_divisor_exists_vS2)
  in Thm.implies_elim inst hle2 end;
fun pde_bodyAbs nt =                                  (* %p. Conj (prime2 p)(dvd p n) *)
  let val pF = Free("p_pde", natT) in Term.lambda pF (mkConj (prime2 pF) (dvd pF nt)) end;

(* prime2 destructors on ctxtS2 (capture-avoiding ppAbs) *)
fun prime2_gt1S pt hprime = conjunct1_atS2 (lt (suc ZeroC) pt, mkForall (ppAbs pt)) hprime;  (* lt 1 p *)
fun prime2_divS pt hprime = conjunct2_atS2 (lt (suc ZeroC) pt, mkForall (ppAbs pt)) hprime;  (* Forall (ppAbs p) *)

(* Suc_inj on ctxtS2 : oeq (Suc a)(Suc b) ==> oeq a b *)
val Suc_inj_vS = varify Suc_inj_ax;
fun Suc_inj_atS (aT,bT) = beta_norm (Drule.infer_instantiate ctxtS2
      [(("a",0), ctermS2 aT),(("b",0), ctermS2 bT)] Suc_inj_vS);

(* ---- mult_eq_zero ---- *)
val mult_eq_zero =
  let
    val aF = Free("a_mez", natT);  val bF = Free("b_mez", natT);
    val hyp = Thm.assume (ctermS2 (jT (oeq (mult aF bF) ZeroC)));
    val goalC = mkDisj (oeq aF ZeroC) (oeq bF ZeroC);
    val dz = dzosS_at aF;
    val caseZ =
      let val hZ = Thm.assume (ctermS2 (jT (oeq aF ZeroC)))
      in Thm.implies_intr (ctermS2 (jT (oeq aF ZeroC)))
           (disjI1S2_at (oeq aF ZeroC, oeq bF ZeroC) hZ) end;
    val sucAbs = Abs("q", natT, oeq aF (suc (Bound 0)));
    val caseS =
      let
        val hEx = Thm.assume (ctermS2 (jT (mkEx sucAbs)))
        fun body q (hq : thm) =
          let
            val abq  = mult_cong_lS (aF, suc q, bF) hq;
            val sqb  = multSuclS_at (q, bF);
            val ab_e = oeq_trans OF [oeq_sym OF [oeq_trans OF [abq, sqb]], hyp];
            val bz   = add_eq_zero_left_vS OF [ab_e];
          in disjI2S2_at (oeq aF ZeroC, oeq bF ZeroC) bz end;
        val res = exE_elimS2 (sucAbs, goalC) hEx "q_mez" body;
      in Thm.implies_intr (ctermS2 (jT (mkEx sucAbs))) res end;
    val body = disjE_elimS2 (oeq aF ZeroC, mkEx sucAbs, goalC) dz caseZ caseS;
  in varify (Thm.implies_intr (ctermS2 (jT (oeq (mult aF bF) ZeroC))) body) end;
val mult_eq_zero_vS2 = varify mult_eq_zero;
fun mult_eq_zero_atS (aT,bT) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("a_mez",0), ctermS2 aT), (("b_mez",0), ctermS2 bT)] mult_eq_zero_vS2)
  in Thm.implies_elim inst h end;

(* ---- mult_left_cancel : lt 0 p ==> p*a = p*b ==> a = b ---- *)
val mult_left_cancel =
  let
    val pF = Free("p_mlc", natT); val aF = Free("a_mlc", natT); val bF = Free("b_mlc", natT);
    val hPos = Thm.assume (ctermS2 (jT (lt ZeroC pF)));
    val hEq  = Thm.assume (ctermS2 (jT (oeq (mult pF aF) (mult pF bF))));
    val goalC = oeq aF bF;
    val tot = le_total_atS (aF, bF);
    fun contraP goal =
      let val hpz = Thm.assume (ctermS2 (jT (oeq pF ZeroC)))
          val zV   = Free("z_subst", natT)
          val Psub = Term.lambda zV (lt ZeroC zV)
          val sub  = beta_norm (Drule.infer_instantiate ctxtS2
                       [(("P",0), ctermS2 Psub),(("a",0), ctermS2 pF),(("b",0), ctermS2 ZeroC)] oeq_subst_vS)
          val lt00 = (sub OF [hpz]) OF [hPos]
          val fls  = lt_irrefl_atS ZeroC lt00
          val g    = Thm.implies_elim (oFalse_elimS_at goal) fls
      in Thm.implies_intr (ctermS2 (jT (oeq pF ZeroC))) g end;
    val leAbsAB = Abs("k", natT, oeq bF (add aF (Bound 0)));
    val caseAB =
      let
        val hLe = Thm.assume (ctermS2 (jT (le aF bF)))
        fun body d (hd : thm) =
          let
            val pb1 = mult_cong_rS (pF, bF, add aF d) hd;
            val ld  = left_distrib_atS (pF, aF, d);
            val pb2 = oeq_trans OF [pb1, ld];
            val pa_e = oeq_trans OF [hEq, pb2];
            val pa0  = oeq_sym OF [add0rS_at (mult pF aF)];
            val both = oeq_trans OF [oeq_sym OF [pa0], pa_e];
            val zpd  = add_left_cancel_atS (mult pF aF, ZeroC, mult pF d) both;
            val pdz  = oeq_sym OF [zpd];
            val disj = mult_eq_zero_atS (pF, d) pdz;
            val cZp  = contraP goalC;
            val cZd =
              let val hdz = Thm.assume (ctermS2 (jT (oeq d ZeroC)))
                  val ba0 = oeq_trans OF [hd, add_cong_rS (aF, d, ZeroC) hdz]
                  val ba  = oeq_trans OF [ba0, add0rS_at aF]
                  val ab  = oeq_sym OF [ba]
              in Thm.implies_intr (ctermS2 (jT (oeq d ZeroC))) ab end;
          in disjE_elimS2 (oeq pF ZeroC, oeq d ZeroC, goalC) disj cZp cZd end;
        val r = exE_elimS2 (leAbsAB, goalC) hLe "d_ab" body;
      in Thm.implies_intr (ctermS2 (jT (le aF bF))) r end;
    val leAbsBA = Abs("k", natT, oeq aF (add bF (Bound 0)));
    val caseBA =
      let
        val hLe = Thm.assume (ctermS2 (jT (le bF aF)))
        fun body d (hd : thm) =
          let
            val pa1 = mult_cong_rS (pF, aF, add bF d) hd;
            val ld  = left_distrib_atS (pF, bF, d);
            val pa2 = oeq_trans OF [pa1, ld];
            val pb_e = oeq_trans OF [oeq_sym OF [hEq], pa2];
            val pb0  = oeq_sym OF [add0rS_at (mult pF bF)];
            val both = oeq_trans OF [oeq_sym OF [pb0], pb_e];
            val zpd  = add_left_cancel_atS (mult pF bF, ZeroC, mult pF d) both;
            val pdz  = oeq_sym OF [zpd];
            val disj = mult_eq_zero_atS (pF, d) pdz;
            val cZp  = contraP goalC;
            val cZd =
              let val hdz = Thm.assume (ctermS2 (jT (oeq d ZeroC)))
                  val ab0 = oeq_trans OF [hd, add_cong_rS (bF, d, ZeroC) hdz]
                  val ab  = oeq_trans OF [ab0, add0rS_at bF]
              in Thm.implies_intr (ctermS2 (jT (oeq d ZeroC))) ab end;
          in disjE_elimS2 (oeq pF ZeroC, oeq d ZeroC, goalC) disj cZp cZd end;
        val r = exE_elimS2 (leAbsBA, goalC) hLe "d_ba" body;
      in Thm.implies_intr (ctermS2 (jT (le bF aF))) r end;
    val body = disjE_elimS2 (le aF bF, le bF aF, goalC) tot caseAB caseBA;
    val d1 = Thm.implies_intr (ctermS2 (jT (oeq (mult pF aF) (mult pF bF)))) body;
    val d2 = Thm.implies_intr (ctermS2 (jT (lt ZeroC pF))) d1;
  in varify d2 end;
val mult_left_cancel_vS2 = varify mult_left_cancel;
fun mult_left_cancel_atS (pT,aT,bT) hpos heq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("p_mlc",0), ctermS2 pT),(("a_mlc",0), ctermS2 aT),(("b_mlc",0), ctermS2 bT)] mult_left_cancel_vS2)
  in (inst OF [hpos]) OF [heq] end;

(* ---- lt_self_mult : lt 1 c ==> lt 0 n ==> lt n (mult c n) ---- *)
val oneC = suc ZeroC;
val lt_self_mult =
  let
    val cF = Free("c_lsm", natT);  val nF = Free("n_lsm", natT);
    val hC = Thm.assume (ctermS2 (jT (lt oneC cF)));
    val hN = Thm.assume (ctermS2 (jT (lt ZeroC nF)));
    val goalC = lt nF (mult cF nF);
    val cAbs = Abs("j", natT, oeq cF (add (suc (suc ZeroC)) (Bound 0)));
    val nAbs = Abs("k", natT, oeq nF (add oneC (Bound 0)));
    fun cBody j (hj : thm) =
      let
        val s1 = addSucS_at (suc ZeroC, j)
        val s2 = addSucS_at (ZeroC, j)
        val s3 = add0S_at j
        val inner = oeq_trans OF [s2, Suc_cong OF [s3]]
        val c_SSj = oeq_trans OF [hj, oeq_trans OF [s1, Suc_cong OF [inner]]]
        fun nBody npp (hnpp : thm) =
          let
            val n1 = addSucS_at (ZeroC, npp)
            val n2 = add0S_at npp
            val n_Snpp = oeq_trans OF [hnpp, oeq_trans OF [n1, Suc_cong OF [n2]]]
            val cn1 = mult_cong_lS (cF, suc (suc j), nF) c_SSj
            val cn2 = multSuclS_at (suc j, nF)
            val cn3 = multSuclS_at (j, nF)
            val cn3b= add_cong_rS (nF, mult (suc j) nF, add nF (mult j nF)) cn3
            val cn  = oeq_trans OF [cn1, oeq_trans OF [cn2, cn3b]]
            val nin = add_cong_lS (nF, suc npp, mult j nF) n_Snpp
            val cn_b= add_cong_rS (nF, add nF (mult j nF), add (suc npp) (mult j nF)) nin
            val ss  = addSucS_at (npp, mult j nF)
            val cn_c= add_cong_rS (nF, add (suc npp) (mult j nF), suc (add npp (mult j nF))) ss
            val sr  = addSrS_at (nF, add npp (mult j nF))
            val cn_full = oeq_trans OF [cn, oeq_trans OF [cn_b, oeq_trans OF [cn_c, sr]]]
            val kT  = add npp (mult j nF)
            val SnK = addSucS_at (nF, kT)
            val cn_eq = oeq_trans OF [cn_full, oeq_sym OF [SnK]]
          in le_introS (suc nF, mult cF nF, kT) cn_eq end
        val r = exE_elimS2 (nAbs, goalC) hN "npp_lsm" nBody
      in r end
    val body = exE_elimS2 (cAbs, goalC) hC "j_lsm" cBody
  in varify (Thm.implies_intr (ctermS2 (jT (lt oneC cF)))
              (Thm.implies_intr (ctermS2 (jT (lt ZeroC nF))) body)) end;
val lt_self_mult_vS2 = varify lt_self_mult;
fun lt_self_mult_atS (cT,nT) hc hn =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("c_lsm",0), ctermS2 cT),(("n_lsm",0), ctermS2 nT)] lt_self_mult_vS2)
  in (inst OF [hc]) OF [hn] end;

val () = out "KEY_HELPERS_READY\n";

(* ============================================================================
   PREDICATE BUILDERS
   ============================================================================ *)

(* coprime u v = Forall (%d. Imp (dvd d u) (Imp (dvd d v) (oeq d 1))) *)
fun coprimeAbs (uT, vT) =
  let val dF = Free("d_cop", natT)
  in Term.lambda dF (mkImp (dvd dF uT) (mkImp (dvd dF vT) (oeq dF oneC))) end;
fun coprime (uT, vT) = mkForall (coprimeAbs (uT, vT));

(* sqEx x = Ex s. oeq x (mult s s) *)
fun sqAbs xT = let val sF = Free("s_sq", natT) in Term.lambda sF (oeq xT (mult sF sF)) end;
fun sqEx xT = mkEx (sqAbs xT);
(* result u v = Conj (sqEx u) (sqEx v) *)
fun resultC (uT, vT) = mkConj (sqEx uT) (sqEx vT);

(* P body for a fixed w : !u v. coprime u v -> u*v = w*w -> result u v *)
(* inner over v : %v. Imp (coprime u v)(Imp (oeq (u*v)(w*w)) (result u v)) *)
fun innerVAbs (uT, wT) =
  let val vF = Free("v_in", natT)
  in Term.lambda vF (mkImp (coprime (uT, vF)) (mkImp (oeq (mult uT vF) (mult wT wT)) (resultC (uT, vF)))) end;
fun innerU (uT, wT) = mkForall (innerVAbs (uT, wT));     (* !v. ... *)
(* outer over u : %u. !v. ... *)
fun outerUAbs wT =
  let val uF = Free("u_out", natT)
  in Term.lambda uF (innerU (uF, wT)) end;
fun Pterm wT = mkForall (outerUAbs wT);                  (* !u v. ... *)
val Ppred = let val wF = Free("w_P", natT) in Term.lambda wF (Pterm wF) end;  (* %w. P w *)

val () = out "KEY_PRED_READY\n";

(* ============================================================================
   THE STRONG INDUCTION STEP
   ============================================================================ *)
val key_lemma_thm =
  let
    val wStep = Free("w_step", natT);
    val mIH   = Free("m_ih", natT);
    (* IH : !!m. lt m w ==> jT (P m) *)
    val Gprop = Logic.all mIH (Logic.mk_implies (jT (lt mIH wStep), jT (Pterm mIH)));
    val Hthm  = Thm.assume (ctermS2 Gprop);
    fun applyIH wt h_lt =                                 (* lt w' w -> jT (P w') *)
      let val hAt = Thm.forall_elim (ctermS2 wt) Hthm
      in Thm.implies_elim hAt h_lt end;

    (* prove jT (P wStep) = jT (!u v. ...) by allI over u, allI over v *)
    val uF = Free("u_k", natT);
    val vF = Free("v_k", natT);
    val hCop = Thm.assume (ctermS2 (jT (coprime (uF, vF))));         (* coprime u v *)
    val hUV  = Thm.assume (ctermS2 (jT (oeq (mult uF vF) (mult wStep wStep)))); (* u*v = w*w *)
    val goalC = resultC (uF, vF);                                    (* Conj (sqEx u)(sqEx v) *)

    (* coprime applied at a divisor d : d|u -> d|v -> d=1 *)
    fun copApply dT hdu hdv =
      let val hImp = allE_atS2 (coprimeAbs (uF, vF)) dT hCop          (* Imp (d|u)(Imp (d|v)(d=1)) *)
          val s1 = mp_atS2 (dvd dT uF, mkImp (dvd dT vF) (oeq dT oneC)) hImp hdu
          val s2 = mp_atS2 (dvd dT vF, oeq dT oneC) s1 hdv
      in s2 end;

    (* ---- CASE split on u : dzos u ---- *)
    val dzU = dzosS_at uF;   (* Disj (oeq u 0)(Ex q. oeq u (Suc q)) *)

    (* ===== CASE u = 0 =====
       w*w = u*v = 0*v = 0 ; mult_eq_zero -> w=0 (twice) ; v: coprime forces v=1.
       Actually u*v = 0 ; w*w = 0 -> but we need v = 1.  coprime 0 v : v|0, v|v -> v=1.
       u = 0 = 0*0 ; v = 1 = 1*1. *)
    val caseU0 =
      let
        val hU0 = Thm.assume (ctermS2 (jT (oeq uF ZeroC)))
        (* v|0 : dvd v 0 ; v|v : dvd v v ; coprime -> v=1 *)
        val dvd_v_0 = dvd_introS (vF, ZeroC, ZeroC) (oeq_sym OF [mult0rS_at vF]);  (* dvd v 0 : 0 = v*0 *)
        (* but coprime is on (u,v) ; need d|u and d|v ; take d:=v ; v|u since u=0 (dvd v 0 then u=0) *)
        (* dvd v u : u = v*0 since u=0 ; 0 = v*0 -> u = v*0 *)
        val u_v0 = oeq_trans OF [hU0, oeq_sym OF [mult0rS_at vF]];                 (* u = v*0 *)
        val dvd_v_u = dvd_introS (vF, uF, ZeroC) u_v0;                             (* dvd v u *)
        val dvd_v_v = dvd_refl_atS2 vF;                                            (* dvd v v *)
        val v1 = copApply vF dvd_v_u dvd_v_v;                                      (* oeq v 1 *)
        (* sqEx u : u = 0 = 0*0 ; witness s:=0 *)
        val u_00 = oeq_trans OF [hU0, oeq_sym OF [mult0lS_at ZeroC]];              (* u = 0*0 *)
        val exU  = exI_atS2 (sqAbs uF) ZeroC u_00;                                 (* Ex s. u = s*s *)
        (* sqEx v : v = 1 = 1*1 ; witness t:=1 ; 1*1 = 1 via mult_1_left -> mult 1 1 = 1 *)
        val one_one = mult1lS_at oneC;                                             (* (1*1) = 1 *)
        val v_11 = oeq_trans OF [v1, oeq_sym OF [one_one]];                        (* v = 1*1 *)
        val exV  = exI_atS2 (sqAbs vF) oneC v_11;                                  (* Ex t. v = t*t *)
        val conj = conjI_atS2 (sqEx uF, sqEx vF) exU exV;
      in Thm.implies_intr (ctermS2 (jT (oeq uF ZeroC))) conj end;
    val () = out "KEY_CASE_U0_BUILT\n";

    (* ===== CASE u = Suc q : split q = 0 (u=1) vs q = Suc q' (u>=2) ===== *)
    val sucUAbs = Abs("q", natT, oeq uF (suc (Bound 0)));
    val caseUSuc =
      let
        val hExSuc = Thm.assume (ctermS2 (jT (mkEx sucUAbs)))
        fun sucBody q (hq : thm) =      (* hq : oeq u (Suc q) *)
          let
            val dzQ = dzosS_at q   (* Disj (oeq q 0)(Ex q'. oeq q (Suc q')) *)
            (* --- u = 1 (q = 0) --- *)
            val caseU1 =
              let
                val hQ0 = Thm.assume (ctermS2 (jT (oeq q ZeroC)))
                (* u = Suc q = Suc 0 = 1 *)
                val u_1 = oeq_trans OF [hq, Suc_cong OF [hQ0]]   (* u = Suc 0 = 1 *)
                (* v = u*v = 1*v = v ; but we want v = w*w.  u*v = w*w ; u=1 -> 1*v=w*w -> v=w*w *)
                (* u*v = 1*v : mult_cong_l u 1 v ; 1*v = v : mult_1_left *)
                val uv_1v = mult_cong_lS (uF, oneC, vF) u_1                  (* (u*v) = (1*v) *)
                val onev_v = mult1lS_at vF                                   (* (1*v) = v *)
                val uv_v = oeq_trans OF [uv_1v, onev_v]                      (* (u*v) = v *)
                val v_ww = oeq_trans OF [oeq_sym OF [uv_v], hUV]             (* v = w*w *)
                (* sqEx u : u = 1 = 1*1 *)
                val u_11 = oeq_trans OF [u_1, oeq_sym OF [mult1lS_at oneC]]  (* u = 1*1 *)
                val exU  = exI_atS2 (sqAbs uF) oneC u_11
                (* sqEx v : v = w*w *)
                val exV  = exI_atS2 (sqAbs vF) wStep v_ww
                val conj = conjI_atS2 (sqEx uF, sqEx vF) exU exV
              in Thm.implies_intr (ctermS2 (jT (oeq q ZeroC))) conj end
            (* --- u >= 2 (q = Suc q') : the DESCENT --- *)
            val sucQAbs = Abs("qp", natT, oeq q (suc (Bound 0)))
            val caseU2 =
              let
                val hExQ = Thm.assume (ctermS2 (jT (mkEx sucQAbs)))
                fun q2body qp (hqp : thm) =     (* hqp : oeq q (Suc qp) *)
                  let
                    (* u = Suc q = Suc (Suc qp) ; le 2 u : u = 2 + qp *)
                    val u_SSqp = oeq_trans OF [hq, Suc_cong OF [hqp]]   (* u = Suc(Suc qp) *)
                    (* 2 + qp = Suc(Suc(0+qp)) = Suc(Suc qp).  build le 2 u via le_introS (2,u,qp) needs u = 2 + qp *)
                    val twoC = suc (suc ZeroC)
                    (* 2 + qp = Suc(Suc qp) : addSuc twice + add0 *)
                    val t1 = addSucS_at (suc ZeroC, qp)        (* (Suc 0 + qp) = Suc(0 + qp) *)
                    val t2 = addSucS_at (ZeroC, qp)            (* (0 + qp)?  no: (Suc 0 + qp). need (2 + qp) *)
                    (* 2 + qp = Suc 1 + qp ; addSucS (Suc 0, qp) : (Suc(Suc 0) + qp) = Suc(Suc 0 + qp) *)
                    val a1 = addSucS_at (suc ZeroC, qp)        (* (Suc(Suc 0) + qp) = Suc((Suc 0) + qp) *)
                    val a2 = addSucS_at (ZeroC, qp)            (* ((Suc 0) + qp) = Suc(0 + qp) *)
                    val a3 = add0S_at qp                        (* (0 + qp) = qp *)
                    val inner = oeq_trans OF [a2, Suc_cong OF [a3]]   (* (Suc 0 + qp) = Suc qp *)
                    val twoqp = oeq_trans OF [a1, Suc_cong OF [inner]] (* (2 + qp) = Suc(Suc qp) *)
                    val u_2qp = oeq_trans OF [u_SSqp, oeq_sym OF [twoqp]]  (* u = (2 + qp) *)
                    val hLe2u = le_introS (twoC, uF, qp) u_2qp           (* le 2 u *)
                    val () = out "KEY_DESC_LE2U\n"

                    (* STEP 1 : prime divisor p of u *)
                    val pdEx = prime_divisor_exists_atS uF hLe2u   (* Ex p. prime2 p /\ p|u *)
                    val res = exE_elimS2 (pde_bodyAbs uF, goalC) pdEx "p_d"
                      (fn pP => fn (hpP : thm) =>
                        let
                          val hPr    = conjunct1_atS2 (prime2 pP, dvd pP uF) hpP   (* prime2 p *)
                          val hPdvdU = conjunct2_atS2 (prime2 pP, dvd pP uF) hpP   (* dvd p u *)
                          (* lt 1 p and lt 0 p *)
                          val hLt1p = prime2_gt1S pP hPr                    (* lt 1 p = le 2 p *)
                          val le_1_2 = lt_zero_suc_atS oneC                 (* lt 0 1? actually le 1 2 = lt 0 1 *)
                          (* lt 0 p : le 1 p from le_trans (le 1 2)(le 2 p) ; le 1 2 = lt 0 1 = lt_zero_suc 1? *)
                          (* le 1 2 = le (Suc 0)(Suc(Suc 0)) : 2 = 1 + 1 ; use lt_zero_suc_atS oneC = lt 0 (Suc 1) = le 1 (Suc 1) = le 1 2 *)
                          val le12  = lt_zero_suc_atS oneC                  (* lt 0 (Suc 1) = le 1 2 *)
                          val hLt0p = le_trans_atS (oneC, suc (suc ZeroC), pP) le12 hLt1p  (* le 1 p = lt 0 p *)

                          (* STEP 2 : p | u*v  then p|w via euclid_lemma on w*w *)
                          val pdvdUV = dvd_mult_right_atS (pP, uF, vF) hPdvdU     (* dvd p (u*v) *)
                          (* p | (w*w) : rewrite u*v -> w*w *)
                          val zV = Free("z_d", natT)
                          val Psub_uw = Term.lambda zV (dvd pP zV)
                          val subUW = beta_norm (Drule.infer_instantiate ctxtS2
                                        [(("P",0), ctermS2 Psub_uw),(("a",0), ctermS2 (mult uF vF)),(("b",0), ctermS2 (mult wStep wStep))] oeq_subst_vS)
                          val pdvdWW = (subUW OF [hUV]) OF [pdvdUV]               (* dvd p (w*w) *)
                          val eucW = euclid_lemma_atS (pP, wStep, wStep) hPr pdvdWW  (* Disj (p|w)(p|w) *)
                          val pdvdW =
                            let val cA = let val h = Thm.assume (ctermS2 (jT (dvd pP wStep)))
                                         in Thm.implies_intr (ctermS2 (jT (dvd pP wStep))) h end
                            in disjE_elimS2 (dvd pP wStep, dvd pP wStep, dvd pP wStep) eucW cA cA end

                          (* STEP 3 : p does NOT divide v  (notPdvdV : dvd p v ==> oFalse) *)
                          fun notPdvdV hpv =     (* hpv : dvd p v *)
                            let
                              val p1 = allE_atS2 (coprimeAbs (uF, vF)) pP hCop   (* Imp (p|u)(Imp(p|v)(p=1)) *)
                              val p2 = mp_atS2 (dvd pP uF, mkImp (dvd pP vF) (oeq pP oneC)) p1 hPdvdU
                              val p1eq = mp_atS2 (dvd pP vF, oeq pP oneC) p2 hpv   (* oeq p 1 *)
                              (* lt 1 p with p=1 -> lt 1 1 -> lt_irrefl *)
                              val zV2 = Free("z_d2", natT)
                              val Psub_p1 = Term.lambda zV2 (lt oneC zV2)
                              val subp1 = beta_norm (Drule.infer_instantiate ctxtS2
                                            [(("P",0), ctermS2 Psub_p1),(("a",0), ctermS2 pP),(("b",0), ctermS2 oneC)] oeq_subst_vS)
                              val lt11 = (subp1 OF [p1eq]) OF [hLt1p]    (* lt 1 1 *)
                            in lt_irrefl_atS oneC lt11 end                (* oFalse *)

                          (* STEP 4 : w = p*w' *)
                          val wAbs = Abs("wp", natT, oeq wStep (mult pP (Bound 0)))
                          val res2 = exE_elimS2 (wAbs, goalC) pdvdW "wp_d"
                            (fn wp => fn (hW : thm) =>     (* hW : oeq w (p*wp) *)
                              let
                                (* STEP : p | u (already have hPdvdU). u = p*u1 *)
                                val uAbs = Abs("u1", natT, oeq uF (mult pP (Bound 0)))
                                val res3 = exE_elimS2 (uAbs, goalC) hPdvdU "u1_d"
                                  (fn u1 => fn (hU1 : thm) =>    (* hU1 : oeq u (p*u1) *)
                                    let
                                      (* (p*u1)*v = w*w = (p*wp)*(p*wp) ; cancel p :
                                         p*(u1*v) = p*(wp*(p*wp)) ->  u1*v = wp*(p*wp) = p*(wp*wp) *)
                                      (* LHS: u*v -> (p*u1)*v -> p*(u1*v) *)
                                      val luv1 = mult_cong_lS (uF, mult pP u1, vF) hU1   (* (u*v) = ((p*u1)*v) *)
                                      val luv2 = mult_assoc_atS (pP, u1, vF)             (* ((p*u1)*v) = (p*(u1*v)) *)
                                      val luv  = oeq_trans OF [oeq_sym OF [luv1], oeq_trans OF [luv1, luv2]]
                                      (* simpler: (u*v) = (p*(u1*v)) *)
                                      val uv_p_u1v = oeq_trans OF [luv1, luv2]           (* (u*v) = (p*(u1*v)) *)
                                      (* RHS: w*w -> (p*wp)*(p*wp) -> p*(wp*(p*wp)) *)
                                      val rww1 = mult_cong_lS (wStep, mult pP wp, wStep) hW  (* (w*w) = ((p*wp)*w) *)
                                      val rww2 = mult_cong_rS (mult pP wp, wStep, mult pP wp) hW (* ((p*wp)*w) = ((p*wp)*(p*wp)) *)
                                      val rww3 = mult_assoc_atS (pP, wp, mult pP wp)     (* ((p*wp)*(p*wp)) = (p*(wp*(p*wp))) *)
                                      val ww_p = oeq_trans OF [rww1, oeq_trans OF [rww2, rww3]]  (* (w*w) = (p*(wp*(p*wp))) *)
                                      (* p*(u1*v) = p*(wp*(p*wp)) *)
                                      val pEq1 = oeq_trans OF [oeq_sym OF [uv_p_u1v], oeq_trans OF [hUV, ww_p]]  (* (p*(u1*v)) = (p*(wp*(p*wp))) *)
                                      val canc1 = mult_left_cancel_atS (pP, mult u1 vF, mult wp (mult pP wp)) hLt0p pEq1  (* (u1*v) = (wp*(p*wp)) *)
                                      (* wp*(p*wp) = p*(wp*wp) : wp*(p*wp) = (wp*p)*wp [assoc back] = (p*wp)*wp [comm] = p*(wp*wp) [assoc] *)
                                      val a_back = mult_assoc_atS (wp, pP, wp)          (* ((wp*p)*wp) = (wp*(p*wp)) *)
                                      val a_comm = mult_comm_atS (wp, pP)               (* (wp*p) = (p*wp) *)
                                      val a_cl   = mult_cong_lS (mult wp pP, mult pP wp, wp) a_comm  (* ((wp*p)*wp) = ((p*wp)*wp) *)
                                      val a_fwd  = mult_assoc_atS (pP, wp, wp)          (* ((p*wp)*wp) = (p*(wp*wp)) *)
                                      val wppw_p = oeq_trans OF [oeq_sym OF [a_back], oeq_trans OF [a_cl, a_fwd]]  (* (wp*(p*wp)) = (p*(wp*wp)) *)
                                      val u1v_p = oeq_trans OF [canc1, wppw_p]          (* (u1*v) = (p*(wp*wp)) *)

                                      (* p | (u1*v) : (u1*v) = p*(wp*wp) ; dvd_introS witness (wp*wp) *)
                                      val pdvd_u1v = dvd_introS (pP, mult u1 vF, mult wp wp) u1v_p   (* dvd p (u1*v) *)
                                      val euc2 = euclid_lemma_atS (pP, u1, vF) hPr pdvd_u1v          (* Disj (p|u1)(p|v) *)
                                      (* p|v impossible -> so p|u1 *)
                                      val pdvdU1 =
                                        let
                                          val cA = let val h = Thm.assume (ctermS2 (jT (dvd pP u1)))
                                                   in Thm.implies_intr (ctermS2 (jT (dvd pP u1))) h end
                                          val cB = let val h = Thm.assume (ctermS2 (jT (dvd pP vF)))
                                                       val fls = notPdvdV h
                                                       val g = Thm.implies_elim (oFalse_elimS_at (dvd pP u1)) fls
                                                   in Thm.implies_intr (ctermS2 (jT (dvd pP vF))) g end
                                        in disjE_elimS2 (dvd pP u1, dvd pP vF, dvd pP u1) euc2 cA cB end
                                      (* u1 = p*u' *)
                                      val u1Abs = Abs("up", natT, oeq u1 (mult pP (Bound 0)))
                                      val res4 = exE_elimS2 (u1Abs, goalC) pdvdU1 "up_d"
                                        (fn up => fn (hU' : thm) =>    (* hU' : oeq u1 (p*up) *)
                                          let
                                            (* u1*v = p*(wp*wp) ; u1 = p*up ; (p*up)*v = p*(up*v) ; cancel p -> up*v = wp*wp *)
                                            val l1 = mult_cong_lS (u1, mult pP up, vF) hU'   (* (u1*v) = ((p*up)*v) *)
                                            val l2 = mult_assoc_atS (pP, up, vF)             (* ((p*up)*v) = (p*(up*v)) *)
                                            val u1v_pupv = oeq_trans OF [l1, l2]             (* (u1*v) = (p*(up*v)) *)
                                            val pEq2 = oeq_trans OF [oeq_sym OF [u1v_pupv], u1v_p]  (* (p*(up*v)) = (p*(wp*wp)) *)
                                            val canc2 = mult_left_cancel_atS (pP, mult up vF, mult wp wp) hLt0p pEq2  (* (up*v) = (wp*wp) *)

                                            (* coprime up v : any d|up -> d|u1 (u1=p*up) -> d|u (u=p*u1) -> with d|v -> d=1 *)
                                            val copUpV =
                                              let
                                                val dF = Free("d_up", natT)
                                                val cnjP = jT (mkConj (dvd dF up) (dvd dF vF))
                                                (* actually coprime form is curried: Imp(d|up)(Imp(d|v)(d=1)) *)
                                                fun mkImpl () =
                                                  let
                                                    val hdup = Thm.assume (ctermS2 (jT (dvd dF up)))
                                                    val hdv  = Thm.assume (ctermS2 (jT (dvd dF vF)))
                                                    (* d|up -> d|u1 : u1 = p*up, dvd_mult_right gives up | up*c ; need d|up -> d|(p*up).
                                                       d|up and up|(p*up) (since p*up = up*p comm) -> d|(p*up)=d|u1 via dvd_trans *)
                                                    (* up | (p*up) : p*up = up*p [comm], dvd_introS (up,(p*up),p) needs (p*up) = up*p *)
                                                    val pup_upp = mult_comm_atS (pP, up)        (* (p*up) = (up*p) *)
                                                    val up_dvd_pup = dvd_introS (up, mult pP up, pP) pup_upp  (* dvd up (p*up) *)
                                                    val d_dvd_pup = dvd_trans_atS2 (dF, up, mult pP up) hdup up_dvd_pup  (* dvd d (p*up) *)
                                                    (* rewrite p*up -> u1 : u1 = p*up so p*up = u1 (sym) *)
                                                    val zVc = Free("z_dc", natT)
                                                    val Psd = Term.lambda zVc (dvd dF zVc)
                                                    val subc = beta_norm (Drule.infer_instantiate ctxtS2
                                                                 [(("P",0), ctermS2 Psd),(("a",0), ctermS2 (mult pP up)),(("b",0), ctermS2 u1)] oeq_subst_vS)
                                                    val d_dvd_u1 = (subc OF [oeq_sym OF [hU']]) OF [d_dvd_pup]   (* dvd d u1 *)
                                                    (* u1 | u : u = p*u1 = u1*p [comm] ; dvd_introS (u1,u,p) needs u = u1*p *)
                                                    val u_u1p0 = oeq_trans OF [hU1, mult_comm_atS (pP, u1)]   (* u = (u1*p) *)
                                                    val u1_dvd_u = dvd_introS (u1, uF, pP) u_u1p0             (* dvd u1 u *)
                                                    val d_dvd_u  = dvd_trans_atS2 (dF, u1, uF) d_dvd_u1 u1_dvd_u  (* dvd d u *)
                                                    (* coprime u v at d : d|u -> d|v -> d=1 *)
                                                    val cp1 = allE_atS2 (coprimeAbs (uF, vF)) dF hCop
                                                    val cp2 = mp_atS2 (dvd dF uF, mkImp (dvd dF vF) (oeq dF oneC)) cp1 d_dvd_u
                                                    val cp3 = mp_atS2 (dvd dF vF, oeq dF oneC) cp2 hdv     (* oeq d 1 *)
                                                    val i1 = Thm.implies_intr (ctermS2 (jT (dvd dF vF))) cp3
                                                    val i0 = Thm.implies_intr (ctermS2 (jT (dvd dF up))) i1
                                                    val asImp1 = impI_atS2 (dvd dF vF, oeq dF oneC) i1
                                                    val asImp0 = impI_atS2 (dvd dF up, mkImp (dvd dF vF) (oeq dF oneC)) (Thm.implies_intr (ctermS2 (jT (dvd dF up))) asImp1)
                                                  in asImp0 end   (* jT (Imp (d|up)(Imp(d|v)(d=1))) *)
                                                val impThm = mkImpl ()
                                                val minor = Thm.forall_intr (ctermS2 dF) impThm
                                              in allI_atS2 (coprimeAbs (up, vF)) minor end   (* coprime up v *)

                                            (* w' < w : lt wp w.  lt 1 p, lt 0 wp -> lt wp (p*wp) = lt wp w (rewrite) *)
                                            (* need lt 0 wp : wp != 0 because w != 0 (this u>=2 branch) and w=p*wp.
                                               w != 0 : if w=0 then u*v=0 -> v=0 (u>=2) -> coprime forces u=1 contra.
                                               then wp != 0 : w=p*wp=0 -> p=0 or wp=0 ; p!=0 -> wp=0 -> w... circular.
                                               Cleaner: lt 0 wp from lt 0 w and w=p*wp : if wp=0 then w=p*0=0, but lt 0 w. *)
                                            (* First prove lt 0 w. *)
                                            val hLt0w =
                                              let
                                                (* assume w=0 -> derive oFalse, then oFalse_elim ; but we want a proof of lt 0 w.
                                                   Use dzos w : w=0 or w=Suc k. If w=Suc k, lt_zero_suc. If w=0, contradiction. *)
                                                val dzW = dzosS_at wStep
                                                val cZ =
                                                  let
                                                    val hW0 = Thm.assume (ctermS2 (jT (oeq wStep ZeroC)))
                                                    (* w*w = 0 : w=0 -> w*w = 0*w? rewrite both ; w*w = (0)*w via cong then mult0l *)
                                                    val ww0a = mult_cong_lS (wStep, ZeroC, wStep) hW0   (* (w*w) = (0*w) *)
                                                    val ww0  = oeq_trans OF [ww0a, mult0lS_at wStep]    (* (w*w) = 0 *)
                                                    val uv0  = oeq_trans OF [hUV, ww0]                  (* (u*v) = 0 *)
                                                    val duv  = mult_eq_zero_atS (uF, vF) uv0            (* u=0 \/ v=0 *)
                                                    (* u=0 impossible (u = Suc(Suc qp)) ; v=0 -> coprime forces u=1 contra u>=2 *)
                                                    val cU0 =
                                                      let val h = Thm.assume (ctermS2 (jT (oeq uF ZeroC)))
                                                          (* u = Suc(Suc qp) and u=0 -> Suc(..)=0 *)
                                                          val su0 = oeq_trans OF [oeq_sym OF [u_SSqp], h]  (* Suc(Suc qp) = 0 *)
                                                          val fls = Suc_neq_Zero_atS (suc qp) OF [su0]
                                                      in Thm.implies_intr (ctermS2 (jT (oeq uF ZeroC))) (Thm.implies_elim (oFalse_elimS_at (lt ZeroC wStep)) fls) end
                                                    val cV0 =
                                                      let val h = Thm.assume (ctermS2 (jT (oeq vF ZeroC)))
                                                          (* v=0 ; u|0 (dvd u 0), u|u -> coprime(u,v) at d:=u, u|v? need u|v.  v=0 -> u|v=u|0. *)
                                                          val u_dvd_v = let val u_u0 = oeq_trans OF [h, oeq_sym OF [mult0rS_at uF]]  (* v = u*0 *)
                                                                        in dvd_introS (uF, vF, ZeroC) u_u0 end   (* dvd u v *)
                                                          val u_dvd_u = dvd_refl_atS2 uF
                                                          val u1eq = copApply uF u_dvd_u u_dvd_v   (* oeq u 1 *)
                                                          (* u = Suc(Suc qp) and u=1=Suc 0 -> Suc(Suc qp)=Suc 0 -> Suc_inj -> Suc qp = 0 -> contra *)
                                                          val u_1' = oeq_trans OF [oeq_sym OF [u_SSqp], u1eq]   (* Suc(Suc qp) = Suc 0 *)
                                                          val inj  = Suc_inj_atS (suc qp, ZeroC) OF [u_1']      (* Suc qp = 0 *)
                                                          val fls  = Suc_neq_Zero_atS qp OF [inj]
                                                      in Thm.implies_intr (ctermS2 (jT (oeq vF ZeroC))) (Thm.implies_elim (oFalse_elimS_at (lt ZeroC wStep)) fls) end
                                                    val contra = disjE_elimS2 (oeq uF ZeroC, oeq vF ZeroC, lt ZeroC wStep) duv cU0 cV0
                                                  in Thm.implies_intr (ctermS2 (jT (oeq wStep ZeroC))) contra end
                                                val cS =
                                                  let val hExk = Thm.assume (ctermS2 (jT (mkEx (Abs("k", natT, oeq wStep (suc (Bound 0)))))))
                                                  in Thm.implies_intr (ctermS2 (jT (mkEx (Abs("k", natT, oeq wStep (suc (Bound 0)))))))
                                                       (exE_elimS2 (Abs("k", natT, oeq wStep (suc (Bound 0))), lt ZeroC wStep) hExk "kw_d"
                                                         (fn kk => fn (hk : thm) =>
                                                            let val lt0Sk = lt_zero_suc_atS kk        (* lt 0 (Suc kk) *)
                                                                val zVw = Free("z_dw", natT)
                                                                val Psw = Term.lambda zVw (lt ZeroC zVw)
                                                                val subw = beta_norm (Drule.infer_instantiate ctxtS2
                                                                             [(("P",0), ctermS2 Psw),(("a",0), ctermS2 (suc kk)),(("b",0), ctermS2 wStep)] oeq_subst_vS)
                                                            in (subw OF [oeq_sym OF [hk]]) OF [lt0Sk] end)) end
                                              in disjE_elimS2 (oeq wStep ZeroC, mkEx (Abs("k", natT, oeq wStep (suc (Bound 0)))), lt ZeroC wStep) dzW cZ cS end
                                            (* lt 0 wp : if wp=0 then w=p*0=0 contradicting lt 0 w *)
                                            val hLt0wp =
                                              let
                                                val dzWp = dzosS_at wp
                                                val cZ =
                                                  let val h = Thm.assume (ctermS2 (jT (oeq wp ZeroC)))
                                                      (* w = p*wp = p*0 = 0 *)
                                                      val w_p0 = oeq_trans OF [hW, mult_cong_rS (pP, wp, ZeroC) h]  (* w = (p*0) *)
                                                      val w0   = oeq_trans OF [w_p0, mult0rS_at pP]                 (* w = 0 *)
                                                      (* lt 0 w with w=0 -> lt 0 0 *)
                                                      val zVw2 = Free("z_dw2", natT)
                                                      val Psw2 = Term.lambda zVw2 (lt ZeroC zVw2)
                                                      val subw2 = beta_norm (Drule.infer_instantiate ctxtS2
                                                                    [(("P",0), ctermS2 Psw2),(("a",0), ctermS2 wStep),(("b",0), ctermS2 ZeroC)] oeq_subst_vS)
                                                      val lt00w = (subw2 OF [w0]) OF [hLt0w]
                                                      val fls = lt_irrefl_atS ZeroC lt00w
                                                  in Thm.implies_intr (ctermS2 (jT (oeq wp ZeroC))) (Thm.implies_elim (oFalse_elimS_at (lt ZeroC wp)) fls) end
                                                val cS =
                                                  let val hExk = Thm.assume (ctermS2 (jT (mkEx (Abs("k", natT, oeq wp (suc (Bound 0)))))))
                                                  in Thm.implies_intr (ctermS2 (jT (mkEx (Abs("k", natT, oeq wp (suc (Bound 0)))))))
                                                       (exE_elimS2 (Abs("k", natT, oeq wp (suc (Bound 0))), lt ZeroC wp) hExk "kwp_d"
                                                         (fn kk => fn (hk : thm) =>
                                                            let val lt0Sk = lt_zero_suc_atS kk
                                                                val zVw = Free("z_dwp", natT)
                                                                val Psw = Term.lambda zVw (lt ZeroC zVw)
                                                                val subw = beta_norm (Drule.infer_instantiate ctxtS2
                                                                             [(("P",0), ctermS2 Psw),(("a",0), ctermS2 (suc kk)),(("b",0), ctermS2 wp)] oeq_subst_vS)
                                                            in (subw OF [oeq_sym OF [hk]]) OF [lt0Sk] end)) end
                                              in disjE_elimS2 (oeq wp ZeroC, mkEx (Abs("k", natT, oeq wp (suc (Bound 0)))), lt ZeroC wp) dzWp cZ cS end
                                            (* lt wp (p*wp) then rewrite (p*wp) -> w via hW(sym) -> lt wp w *)
                                            val lt_wp_pwp = lt_self_mult_atS (pP, wp) hLt1p hLt0wp   (* lt wp (p*wp) *)
                                            val zVlt = Free("z_dlt", natT)
                                            val Plt  = Term.lambda zVlt (lt wp zVlt)
                                            val sublt = beta_norm (Drule.infer_instantiate ctxtS2
                                                          [(("P",0), ctermS2 Plt),(("a",0), ctermS2 (mult pP wp)),(("b",0), ctermS2 wStep)] oeq_subst_vS)
                                            val lt_wp_w = (sublt OF [oeq_sym OF [hW]]) OF [lt_wp_pwp]   (* lt wp w *)

                                            (* IH at wp : jT (P wp) ; instantiate at up, v ; feed coprime + (up*v = wp*wp) *)
                                            val Pwp = applyIH wp lt_wp_w                  (* jT (P wp) = jT (!u v. ...) *)
                                            val PwpU = allE_atS2 (outerUAbs wp) up Pwp    (* jT (!v. ... at u:=up) *)
                                            val PwpUV = allE_atS2 (innerVAbs (up, wp)) vF PwpU  (* Imp (coprime up v)(Imp(up*v=wp*wp)(result up v)) *)
                                            val step1 = mp_atS2 (coprime (up, vF), mkImp (oeq (mult up vF) (mult wp wp)) (resultC (up, vF))) PwpUV copUpV
                                            val ihRes = mp_atS2 (oeq (mult up vF) (mult wp wp), resultC (up, vF)) step1 canc2  (* Conj (sqEx up)(sqEx v) *)
                                            val ih_sqUp = conjunct1_atS2 (sqEx up, sqEx vF) ihRes   (* Ex s. up = s*s *)
                                            val ih_sqV  = conjunct2_atS2 (sqEx up, sqEx vF) ihRes   (* Ex t. v = t*t *)

                                            (* sqEx u : u = p*u1 = p*(p*up) = (p*p)*up ; up = s'*s' -> u = (p*p)*(s'*s') = (p*s')*(p*s') *)
                                            val sqU =
                                              exE_elimS2 (sqAbs up, sqEx uF) ih_sqUp "sp_d"
                                                (fn sp => fn (hSp : thm) =>     (* hSp : oeq up (sp*sp) *)
                                                  let
                                                    (* u = p*u1 = p*(p*up) ; subst u1 = p*up *)
                                                    val u_ppu = oeq_trans OF [hU1, mult_cong_rS (pP, u1, mult pP up) hU']  (* u = (p*(p*up)) *)
                                                    (* p*(p*up) = (p*p)*up [assoc back] *)
                                                    val assoc_back = mult_assoc_atS (pP, pP, up)   (* ((p*p)*up) = (p*(p*up)) *)
                                                    val u_ppup = oeq_trans OF [u_ppu, oeq_sym OF [assoc_back]]   (* u = ((p*p)*up) *)
                                                    (* up = sp*sp -> u = (p*p)*(sp*sp) *)
                                                    val u_ppss = oeq_trans OF [u_ppup, mult_cong_rS (mult pP pP, up, mult sp sp) hSp]  (* u = ((p*p)*(sp*sp)) *)
                                                    (* (p*p)*(sp*sp) = (p*sp)*(p*sp) : prove via assoc/comm *)
                                                    (* (p*sp)*(p*sp) = p*(sp*(p*sp)) [assoc]
                                                       sp*(p*sp) = (sp*p)*sp [assoc back] = (p*sp)*sp [comm] = p*(sp*sp) [assoc]
                                                       so (p*sp)*(p*sp) = p*(p*(sp*sp)) = (p*p)*(sp*sp) [assoc back] *)
                                                    val e1 = mult_assoc_atS (pP, sp, mult pP sp)   (* ((p*sp)*(p*sp)) = (p*(sp*(p*sp))) *)
                                                    val e2a = mult_assoc_atS (sp, pP, sp)          (* ((sp*p)*sp) = (sp*(p*sp)) *)
                                                    val e2b = mult_comm_atS (sp, pP)               (* (sp*p) = (p*sp) *)
                                                    val e2c = mult_cong_lS (mult sp pP, mult pP sp, sp) e2b  (* ((sp*p)*sp) = ((p*sp)*sp) *)
                                                    val e2d = mult_assoc_atS (pP, sp, sp)          (* ((p*sp)*sp) = (p*(sp*sp)) *)
                                                    val sp_psp = oeq_trans OF [oeq_sym OF [e2a], oeq_trans OF [e2c, e2d]]  (* (sp*(p*sp)) = (p*(sp*sp)) *)
                                                    val e3 = mult_cong_rS (pP, mult sp (mult pP sp), mult pP (mult sp sp)) sp_psp  (* (p*(sp*(p*sp))) = (p*(p*(sp*sp))) *)
                                                    val e4 = mult_assoc_atS (pP, pP, mult sp sp)   (* ((p*p)*(sp*sp)) = (p*(p*(sp*sp))) *)
                                                    val psp_sq = oeq_trans OF [e1, oeq_trans OF [e3, oeq_sym OF [e4]]]  (* ((p*sp)*(p*sp)) = ((p*p)*(sp*sp)) *)
                                                    val u_final = oeq_trans OF [u_ppss, oeq_sym OF [psp_sq]]  (* u = ((p*sp)*(p*sp)) *)
                                                  in exI_atS2 (sqAbs uF) (mult pP sp) u_final end)
                                            val conj = conjI_atS2 (sqEx uF, sqEx vF) sqU ih_sqV
                                          in conj end)
                                    in res4 end)
                                in res3 end)
                          in res2 end)
                  in res end
                val r = exE_elimS2 (sucQAbs, goalC) hExQ "qp_d" q2body
              in Thm.implies_intr (ctermS2 (jT (mkEx sucQAbs))) r end
          in disjE_elimS2 (oeq q ZeroC, mkEx sucQAbs, goalC) dzQ caseU1 caseU2 end
        val r = exE_elimS2 (sucUAbs, goalC) hExSuc "q_u" sucBody
      in Thm.implies_intr (ctermS2 (jT (mkEx sucUAbs))) r end;
    val () = out "KEY_CASE_USUC_BUILT\n";

    val bodyUV = disjE_elimS2 (oeq uF ZeroC, mkEx sucUAbs, goalC) dzU caseU0 caseUSuc;
    (* turn meta-hyps (coprime, u*v=w*w) into OBJECT implications via impI_atS2 *)
    val objInner =
      let
        val inner1 = impI_atS2 (oeq (mult uF vF) (mult wStep wStep), resultC (uF, vF))
                       (Thm.implies_intr (ctermS2 (jT (oeq (mult uF vF) (mult wStep wStep)))) bodyUV)
                     (* jT (Imp (u*v=w*w) (result)) *)
        val inner0 = impI_atS2 (coprime (uF, vF), mkImp (oeq (mult uF vF) (mult wStep wStep)) (resultC (uF, vF)))
                       (Thm.implies_intr (ctermS2 (jT (coprime (uF, vF)))) inner1)
                     (* jT (Imp (coprime u v) (Imp (u*v=w*w) (result))) *)
      in inner0 end;
    (* allI over v then u *)
    val allV = allI_atS2 (innerVAbs (uF, wStep)) (Thm.forall_intr (ctermS2 vF) objInner);
    val allU = allI_atS2 (outerUAbs wStep) (Thm.forall_intr (ctermS2 uF) allV);   (* jT (P w) *)
    val stepThm = Thm.forall_intr (ctermS2 wStep) (Thm.implies_intr (ctermS2 Gprop) allU);
    (* feed to strong_induct *)
    val wK = Free("w_key", natT);
    val siInst = beta_norm (Drule.infer_instantiate ctxtS2
                   [(("P",0), ctermS2 Ppred), (("k",0), ctermS2 wK)] (varify strong_induct));
    val Pw = Thm.implies_elim siInst stepThm;     (* jT (P wK) *)
    (* extract the meta-form : coprime u v ==> u*v = w*w ==> result, schematic in u,v,w *)
    val uK = Free("u_key", natT);
    val vK = Free("v_key", natT);
    val PwU = allE_atS2 (outerUAbs wK) uK Pw;                 (* jT (!v. ... at u:=uK) *)
    val PwUV = allE_atS2 (innerVAbs (uK, wK)) vK PwU;         (* jT (Imp (coprime uK vK)(Imp(uK*vK=wK*wK)(result uK vK))) *)
    val hcop2 = Thm.assume (ctermS2 (jT (coprime (uK, vK))));
    val huv2  = Thm.assume (ctermS2 (jT (oeq (mult uK vK) (mult wK wK))));
    val m1 = mp_atS2 (coprime (uK, vK), mkImp (oeq (mult uK vK) (mult wK wK)) (resultC (uK, vK))) PwUV hcop2;
    val m2 = mp_atS2 (oeq (mult uK vK) (mult wK wK), resultC (uK, vK)) m1 huv2;   (* jT (result uK vK) *)
    val d1 = Thm.implies_intr (ctermS2 (jT (oeq (mult uK vK) (mult wK wK)))) m2;
    val d2 = Thm.implies_intr (ctermS2 (jT (coprime (uK, vK)))) d1;
  in varify d2 end;

val () = out "KEY_STEP_DONE\n";

(* ============================================================================
   VALIDATION : 0-hyp + aconv intended + soundness probe
   ============================================================================ *)
val key_nhyp = length (Thm.hyps_of key_lemma_thm);
val () = out ("key hyps=" ^ Int.toString key_nhyp ^ "\n");
val () = out (Syntax.string_of_term ctxtS2 (Thm.prop_of key_lemma_thm) ^ "\n");

(* intended schematic goal, built the SAME way with Var(u),Var(v),Var(w) *)
val uV = Var (("u_key",0), natT);
val vV = Var (("v_key",0), natT);
val wV = Var (("w_key",0), natT);
val key_intended =
  Logic.mk_implies (jT (coprime (uV, vV)),
    Logic.mk_implies (jT (oeq (mult uV vV) (mult wV wV)), jT (resultC (uV, vV))));
val r_key = checkS2 ("key_lemma", key_lemma_thm, key_intended);

(* soundness probe : dropping the coprime hypothesis must NOT be what we proved
   (it's false: u=2,v=2,w=2 -> 2*2=4=2*2 but 2 is not a square). *)
val probe_key =
  let val bogus = Logic.mk_implies (jT (oeq (mult uV vV) (mult wV wV)), jT (resultC (uV, vV)))
  in not ((Thm.prop_of key_lemma_thm) aconv bogus) end;
val () = if probe_key then out "PROBE_OK key needs coprime\n" else out "PROBE_UNSOUND\n";

val () = if r_key andalso probe_key then out "KEY_OK\n" else out "KEY_FAILED\n";

(* ============================================================================
   ============================================================================
   PYTHAGOREAN CHARACTERIZATION  (the headline ==>):
     every PRIMITIVE Pythagorean triple with b EVEN arises as
       a = m^2 - n^2,  b = 2mn,  c = m^2 + n^2,  for coprime m>n.
   Stated subtraction-free:
       pyth_triple(a,b,c) /\ primitive(a,b) /\ even b
         ==> EX m n. lt n m /\ coprime(m,n) /\ oeq c (m*m + n*n)
                          /\ oeq b (2*m*n) /\ oeq (add a (n*n)) (m*m).
   Built on the KEY LEMMA above (coprime u v /\ uv=w^2 -> u,v squares).
   ============================================================================
   ============================================================================ *)
val () = out "PYTH_CHAR_HELPERS_BEGIN\n";

val twoC  = suc (suc ZeroC);

(* ---- div_mod_exists / div_mod_unique instantiators on ctxtS2 ---- *)
val div_mod_exists_vS2 = varify div_mod_exists;
fun div_mod_exists_atS (nT, bT) hpos =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("a",0), ctermS2 nT),(("b",0), ctermS2 bT)] div_mod_exists_vS2)
  in Thm.implies_elim inst hpos end;
val div_mod_unique_vS2 = varify div_mod_unique;
fun div_mod_unique_atS (bT, q1T, r1T, q2T, r2T) hEq hLt1 hLt2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("b",0), ctermS2 bT),(("q1",0), ctermS2 q1T),(("r1",0), ctermS2 r1T),
         (("q2",0), ctermS2 q2T),(("r2",0), ctermS2 r2T)] div_mod_unique_vS2)
  in ((inst OF [hEq]) OF [hLt1]) OF [hLt2] end;
val lt0_2 = lt_zero_suc_atS oneC;   (* lt 0 2 ; oneC defined in the KEY delta *)

(* le_neq_lt on ctxtS2 *)
val le_neq_lt_vS2 = varify le_neq_lt;
fun le_neq_lt_atS (dT, nT) hle hneq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2 [(("d",0), ctermS2 dT),(("n",0), ctermS2 nT)] le_neq_lt_vS2)
  in (inst OF [hle]) OF [hneq] end;

(* ---- two_mult : (2*x) = (x + x) ---- *)
fun two_mult_atS x =
  let
    val s1 = multSuclS_at (oneC, x)
    val s2 = multSuclS_at (ZeroC, x)
    val s3 = mult0lS_at x
    val one_x = oeq_trans OF [s2, oeq_trans OF [add_cong_rS (x, mult ZeroC x, ZeroC) s3, add0rS_at x]]
  in oeq_trans OF [s1, add_cong_rS (x, mult oneC x, x) one_x] end;

(* ---- parity predicates ---- *)
fun evenAt nT = let val kF = Free("k_ev", natT) in mkEx (Term.lambda kF (oeq nT (mult twoC kF))) end;
fun oddAt  nT = let val kF = Free("k_od", natT) in mkEx (Term.lambda kF (oeq nT (suc (mult twoC kF)))) end;

(* parity : Disj (even n)(odd n) *)
fun parity_atS nT =
  let
    val goalC = mkDisj (evenAt nT) (oddAt nT)
    val dme = div_mod_exists_atS (nT, twoC) lt0_2
    fun rInner qT = let val rF = Free("r_in", natT)
                    in mkEx (Term.lambda rF (mkConj (oeq nT (add (mult twoC qT) rF)) (lt rF twoC))) end
    val qBodyAbs = let val qF = Free("q_in", natT) in Term.lambda qF (rInner qF) end
  in exE_elimS2 (qBodyAbs, goalC) dme "q_par"
      (fn q => fn hq =>
        let
          val rBodyAbs = let val rF = Free("r_in2", natT)
                         in Term.lambda rF (mkConj (oeq nT (add (mult twoC q) rF)) (lt rF twoC)) end
        in exE_elimS2 (rBodyAbs, goalC) hq "r_par"
            (fn r => fn hr =>
              let
                val hEq = conjunct1_atS2 (oeq nT (add (mult twoC q) r), lt r twoC) hr
                val hLt = conjunct2_atS2 (oeq nT (add (mult twoC q) r), lt r twoC) hr
                val dzR = dzosS_at r
                val caseR0 =
                  let
                    val hR0 = Thm.assume (ctermS2 (jT (oeq r ZeroC)))
                    val n2q0 = oeq_trans OF [hEq, add_cong_rS (mult twoC q, r, ZeroC) hR0]
                    val n2q  = oeq_trans OF [n2q0, add0rS_at (mult twoC q)]
                    val evenP = let val kF = Free("k_ev", natT) in Term.lambda kF (oeq nT (mult twoC kF)) end
                    val exE  = exI_atS2 evenP q n2q
                  in Thm.implies_intr (ctermS2 (jT (oeq r ZeroC))) (disjI1S2_at (evenAt nT, oddAt nT) exE) end
                val sucRAbs = let val rpF = Free("rp_in", natT) in Term.lambda rpF (oeq r (suc rpF)) end
                val caseRS =
                  let
                    val hExRp = Thm.assume (ctermS2 (jT (mkEx sucRAbs)))
                  in Thm.implies_intr (ctermS2 (jT (mkEx sucRAbs)))
                      (exE_elimS2 (sucRAbs, goalC) hExRp "rp_par"
                        (fn rp => fn hrp =>
                          let
                            val zV = Free("z_p", natT)
                            val Psub = Term.lambda zV (lt zV twoC)
                            val ltSrp = oeq_rewrite_atS (Psub, r, suc rp) hrp hLt
                            val leAbs = let val wF = Free("w_in", natT)
                                        in Term.lambda wF (oeq twoC (add (suc (suc rp)) wF)) end
                            val rpZero = exE_elimS2 (leAbs, oeq rp ZeroC) ltSrp "w_par"
                              (fn w => fn hw =>
                                let
                                  val a1 = addSucS_at (suc rp, w)
                                  val a2 = addSucS_at (rp, w)
                                  val rhs = oeq_trans OF [a1, Suc_cong OF [a2]]
                                  val eq2 = oeq_trans OF [hw, rhs]
                                  val inj1 = Suc_inj_atS (suc ZeroC, suc (add rp w)) OF [eq2]
                                  val inj2 = Suc_inj_atS (ZeroC, add rp w) OF [inj1]
                                in add_eq_zero_left_vS OF [oeq_sym OF [inj2]] end)
                            val r_1 = oeq_trans OF [hrp, Suc_cong OF [rpZero]]
                            val n2q1 = oeq_trans OF [hEq, add_cong_rS (mult twoC q, r, oneC) r_1]
                            val sr = addSrS_at (mult twoC q, ZeroC)
                            val s0 = add0rS_at (mult twoC q)
                            val n_Suc = oeq_trans OF [n2q1, oeq_trans OF [sr, Suc_cong OF [s0]]]
                            val oddP = let val kF = Free("k_od", natT) in Term.lambda kF (oeq nT (suc (mult twoC kF))) end
                            val exO  = exI_atS2 oddP q n_Suc
                          in disjI2S2_at (evenAt nT, oddAt nT) exO end))
                  end
              in disjE_elimS2 (oeq r ZeroC, mkEx sucRAbs, goalC) dzR caseR0 caseRS end)
        end)
  end;

(* even_sq : oeq n (2k) -> even(n*n) *)
fun even_sq_atS (nT, kT) hEven =
  let
    val l1 = mult_cong_lS (nT, mult twoC kT, nT) hEven
    val l2 = mult_cong_rS (mult twoC kT, nT, mult twoC kT) hEven
    val nn_2k = oeq_trans OF [l1, l2]
    val a1 = mult_assoc_atS (twoC, kT, mult twoC kT)
    val b1 = mult_assoc_atS (kT, twoC, kT)
    val b2 = mult_comm_atS (kT, twoC)
    val b3 = mult_cong_lS (mult kT twoC, mult twoC kT, kT) b2
    val b4 = mult_assoc_atS (twoC, kT, kT)
    val k2k = oeq_trans OF [oeq_sym OF [b1], oeq_trans OF [b3, b4]]
    val a2 = mult_cong_rS (twoC, mult kT (mult twoC kT), mult twoC (mult kT kT)) k2k
    val nn_final = oeq_trans OF [nn_2k, oeq_trans OF [a1, a2]]
    val evenP = let val wF = Free("k_ev", natT) in Term.lambda wF (oeq (mult nT nT) (mult twoC wF)) end
  in exI_atS2 evenP (mult twoC (mult kT kT)) nn_final end;

(* odd_sq : oeq n (Suc(2k)) -> odd(n*n) *)
fun odd_sq_atS (nT, kT) hOdd =
  let
    val m = mult twoC kT
    val l1 = mult_cong_lS (nT, suc m, nT) hOdd
    val l2 = mult_cong_rS (suc m, nT, suc m) hOdd
    val nn = oeq_trans OF [l1, l2]
    val ms = multSuclS_at (m, suc m)
    val mr = multSrS_at (m, m)
    val step1 = add_cong_rS (suc m, mult m (suc m), add m (mult m m)) mr
    val as1 = addSucS_at (m, add m (mult m m))
    val Wt = add (mult twoC kT) (mult m kT)
    val rd = left_distrib_atS (twoC, mult twoC kT, mult m kT)
    val tm2k = two_mult_atS (mult twoC kT)
    val mm_comm = mult_comm_atS (m, twoC)
    val mm_cl = mult_cong_lS (mult m twoC, mult twoC m, kT) mm_comm
    val mm_assoc2 = mult_assoc_atS (twoC, m, kT)
    val mm_to = oeq_sym OF [mult_assoc_atS (m, twoC, kT)]
    val twomk = oeq_trans OF [mm_to, oeq_trans OF [mm_cl, mm_assoc2]]
    val twomk_mm = oeq_sym OF [twomk]
    val rhs1 = oeq_trans OF [rd, add_cong_lS (mult twoC (mult twoC kT), add m m, mult twoC (mult m kT)) tm2k]
    val rhs2 = oeq_trans OF [rhs1, add_cong_rS (add m m, mult twoC (mult m kT), mult m m) twomk_mm]
    val lhs_assoc = oeq_sym OF [addassocS_at (m, m, mult m m)]
    val lhs_eq_2Wt = oeq_trans OF [lhs_assoc, oeq_sym OF [rhs2]]
    val chain1 = oeq_trans OF [ms, step1]
    val chain2 = oeq_trans OF [chain1, as1]
    val chain3 = oeq_trans OF [chain2, Suc_cong OF [lhs_eq_2Wt]]
    val nn_odd = oeq_trans OF [nn, chain3]
    val oddP = let val wF = Free("k_od", natT) in Term.lambda wF (oeq (mult nT nT) (suc (mult twoC wF))) end
  in exI_atS2 oddP Wt nn_odd end;

(* even_odd_absurd : oeq n (2k) -> oeq n (Suc(2j)) -> oFalse *)
fun even_odd_absurd (kT, jT_) hEven hOdd =
  let
    val eq1 = oeq_trans OF [oeq_sym OF [hEven], hOdd]
    val lhs = oeq_sym OF [add0rS_at (mult twoC kT)]
    val r1 = addSrS_at (mult twoC jT_, ZeroC)
    val r2 = Suc_cong OF [add0rS_at (mult twoC jT_)]
    val rhs = oeq_sym OF [oeq_trans OF [r1, r2]]
    val eqForm = oeq_trans OF [oeq_sym OF [lhs], oeq_trans OF [eq1, rhs]]
    val hLt1' = le_introS (twoC, twoC, ZeroC) (oeq_sym OF [add0rS_at twoC])
    val du = div_mod_unique_atS (twoC, kT, ZeroC, jT_, suc ZeroC) eqForm lt0_2 hLt1'
    val r0eq1 = conjunct2_atS2 (oeq kT jT_, oeq ZeroC (suc ZeroC)) du
  in Suc_neq_Zero_atS ZeroC OF [oeq_sym OF [r0eq1]] end;

(* odd_add_odd_even : oeq x (Suc(2i)) -> oeq y (Suc(2j)) -> even(x+y) *)
fun odd_add_odd_even (xT, yT, iT, jT_) hxo hyo =
  let
    val s1 = add_cong_lS (xT, suc (mult twoC iT), yT) hxo
    val s2 = add_cong_rS (suc (mult twoC iT), yT, suc (mult twoC jT_)) hyo
    val s3 = addSucS_at (mult twoC iT, suc (mult twoC jT_))
    val s4inner = addSrS_at (mult twoC iT, mult twoC jT_)
    val s4 = Suc_cong OF [s4inner]
    val ld = left_distrib_atS (twoC, iT, jT_)
    val s5 = Suc_cong OF [Suc_cong OF [oeq_sym OF [ld]]]
    val ij = add iT jT_
    val tm = two_mult_atS ij
    val twoSij = two_mult_atS (suc ij)
    val r1 = addSucS_at (ij, suc ij)
    val r2 = Suc_cong OF [addSrS_at (ij, ij)]
    val rhs_form = oeq_trans OF [twoSij, oeq_trans OF [r1, r2]]
    val mid = Suc_cong OF [Suc_cong OF [tm]]
    val xy_to = oeq_trans OF [s1, oeq_trans OF [s2, oeq_trans OF [s3, oeq_trans OF [s4, s5]]]]
    val xy_2W = oeq_trans OF [xy_to, oeq_trans OF [mid, oeq_sym OF [rhs_form]]]
    val evenP = let val wF = Free("k_ev", natT) in Term.lambda wF (oeq (add xT yT) (mult twoC wF)) end
  in exI_atS2 evenP (suc ij) xy_2W end;

(* sq_mono : le m n -> le (m*m)(n*n) *)
fun sq_mono_atS (mT, nT) hle =
  let
    val s1 = mult_le_mono_atS (mT, mT, nT) hle
    val s2a = mult_le_mono_atS (nT, mT, nT) hle
    val comm = mult_comm_atS (nT, mT)
    val zV = Free("z_sq", natT)
    val Psub = Term.lambda zV (le zV (mult nT nT))
    val s2 = oeq_rewrite_atS (Psub, mult nT mT, mult mT nT) comm s2a
  in le_trans_atS (mult mT mT, mult mT nT, mult nT nT) s1 s2 end;

(* mult_eq_zero_atS, mult_left_cancel_atS, lt_self_mult_atS, euclid_lemma_atS,
   prime_divisor_exists_atS, prime2_gt1S, prime2_divS, Suc_inj_atS, dvd helpers
   are ALL defined in the KEY delta (isabelle_pyth.sml) above. *)

val () = out "PYTH_CHAR_HELPERS_OK\n";
(* Extra helpers for the continuation : add_eq_zero_right, sqrt_unique, lt_sq_rev. *)

(* add_eq_zero_left_vS : oeq (add ?a ?b) 0 ==> oeq ?a 0  (vars a,b).  Build right version. *)
fun add_eq_zero_left_at (aT, bT) h =      (* h : (a+b)=0 -> a=0 *)
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2 [(("a",0), ctermS2 aT),(("b",0), ctermS2 bT)] add_eq_zero_left_vS)
  in inst OF [h] end;
fun add_eq_zero_right_at (aT, bT) h =      (* h : (a+b)=0 -> b=0 *)
  let val ba0 = oeq_trans OF [oeq_sym OF [addcommS_at (aT, bT)], h]   (* (b+a)=0 ... wait addcomm: (a+b)=(b+a); need (b+a) *)
  in add_eq_zero_left_at (bT, aT) ba0 end;
(* check: addcommS_at (a,b) : (a+b)=(b+a).  oeq_sym : (b+a)=(a+b).  trans with h:(a+b)=0 needs (a+b) match
   -> oeq_trans OF [addcommS_at(a,b), h] : (a+b)=0 ... no.  Want (b+a)=0.
   (b+a)=(a+b) [addcomm (b,a)] then =0 [h]. *)
fun add_eq_zero_right_at2 (aT, bT) h =     (* h : (a+b)=0 -> b=0 *)
  let val ba_ab = addcommS_at (bT, aT)              (* (b+a)=(a+b) *)
      val ba0 = oeq_trans OF [ba_ab, h]             (* (b+a)=0 *)
  in add_eq_zero_left_at (bT, aT) ba0 end;

(* sqrt_unique : oeq (mult x x)(mult y y) ==> oeq x y. *)
fun sqrt_unique_atS (xT, yT) hsq =
  let
    val tot = le_total_atS (xT, yT)
    val goalC = oeq xT yT
    (* given (le p q) thm and (p*p = q*q), produce (oeq q p). *)
    fun oneSide (pT, qT) hLe hpq_sq =
      let
        val leAbs = let val eF = Free("e_sq", natT) in Term.lambda eF (oeq qT (add pT eF)) end
      in exE_elimS2 (leAbs, oeq qT pT) hLe "e_sq"
          (fn e => fn he =>
            let
              val qq = oeq_trans OF [mult_cong_lS (qT, add pT e, qT) he, mult_cong_rS (add pT e, qT, add pT e) he]
              val rd1 = rdist_at_S2 (pT, e, add pT e)
              val ld_p = left_distrib_atS (pT, pT, e)
              val ld_e = left_distrib_atS (e, pT, e)
              val exp = oeq_trans OF [rd1, oeq_trans OF [add_cong_lS (mult pT (add pT e), add (mult pT pT) (mult pT e), mult e (add pT e)) ld_p,
                                                        add_cong_rS (add (mult pT pT) (mult pT e), mult e (add pT e), add (mult e pT) (mult e e)) ld_e]]
              val qq_exp = oeq_trans OF [qq, exp]
              val qq_assoc = oeq_trans OF [qq_exp, addassocS_at (mult pT pT, mult pT e, add (mult e pT) (mult e e))]
              val pp_form = oeq_trans OF [hpq_sq, qq_assoc]
              val pp0 = oeq_sym OF [add0rS_at (mult pT pT)]
              val both = oeq_trans OF [oeq_sym OF [pp0], pp_form]
              val sum0 = add_left_cancel_atS (mult pT pT, ZeroC, add (mult pT e) (add (mult e pT) (mult e e))) both  (* 0 = (p*e + (e*p + e*e)) *)
              val sum_zero = oeq_sym OF [sum0]                  (* (p*e + (e*p+e*e)) = 0 *)
              val inner_zero = add_eq_zero_right_at2 (mult pT e, add (mult e pT) (mult e e)) sum_zero  (* (e*p+e*e) = 0 *)
              val ee_zero = add_eq_zero_right_at2 (mult e pT, mult e e) inner_zero   (* e*e = 0 *)
              val e_zero_disj = mult_eq_zero_atS (e, e) ee_zero
              val e_zero = disjE_elimS2 (oeq e ZeroC, oeq e ZeroC, oeq e ZeroC) e_zero_disj
                             (let val h = Thm.assume (ctermS2 (jT (oeq e ZeroC))) in Thm.implies_intr (ctermS2 (jT (oeq e ZeroC))) h end)
                             (let val h = Thm.assume (ctermS2 (jT (oeq e ZeroC))) in Thm.implies_intr (ctermS2 (jT (oeq e ZeroC))) h end)
              val q_p = oeq_trans OF [he, oeq_trans OF [add_cong_rS (pT, e, ZeroC) e_zero, add0rS_at pT]]  (* q = p *)
            in q_p end)
      end
    val cXY = let val h = Thm.assume (ctermS2 (jT (le xT yT)))
                  val q_p = oneSide (xT, yT) h hsq            (* oeq y x *)
              in Thm.implies_intr (ctermS2 (jT (le xT yT))) (oeq_sym OF [q_p]) end  (* x = y *)
    val cYX = let val h = Thm.assume (ctermS2 (jT (le yT xT)))
                  val q_p = oneSide (yT, xT) h (oeq_sym OF [hsq])   (* oeq x y *)
              in Thm.implies_intr (ctermS2 (jT (le yT xT))) q_p end
  in disjE_elimS2 (le xT yT, le yT xT, goalC) tot cXY cYX end;

(* lt_sq_rev : lt (n*n)(m*m) ==> lt n m.   via contrapositive le m n -> le (m*m)(n*n) [sq_mono]
   ; lt (n*n)(m*m) = le (Suc(n*n))(m*m) ; le_total n m. *)
fun lt_sq_rev_atS (nT, mT) hlt =     (* hlt : lt (n*n)(m*m) -> lt n m *)
  let
    val tot = le_total_atS (nT, mT)
    val goalC = lt nT mT
    val cNM =
      let val h = Thm.assume (ctermS2 (jT (le nT mT)))
          (* need lt n m.  but le n m alone isn't lt; need n<>m.  if n=m then n*n=m*m, but lt(n*n)(m*m) -> irrefl.
             so derive n<>m, then le_neq_lt. *)
          val n_ne_m =
            let val heq = Thm.assume (ctermS2 (jT (oeq nT mT)))
                val nn_mm = oeq_trans OF [mult_cong_lS (nT, mT, nT) heq, mult_cong_rS (mT, nT, mT) heq]  (* (n*n)=(m*m) *)
                val zV = Free("z_lsr", natT); val Psub = Term.lambda zV (lt (mult nT nT) zV)
                val lt_nn_nn = oeq_rewrite_atS (Psub, mult mT mT, mult nT nT) (oeq_sym OF [nn_mm]) hlt  (* lt (n*n)(n*n) *)
            in impI_atS2 (oeq nT mT, oFalseC) (Thm.implies_intr (ctermS2 (jT (oeq nT mT))) (lt_irrefl_atS (mult nT nT) lt_nn_nn)) end
      in Thm.implies_intr (ctermS2 (jT (le nT mT))) (le_neq_lt_atS (nT, mT) h n_ne_m) end
    val cMN =
      let val h = Thm.assume (ctermS2 (jT (le mT nT)))
          val sm = sq_mono_atS (mT, nT) h    (* le (m*m)(n*n) *)
          val tr = le_trans_atS (suc (mult nT nT), mult mT mT, mult nT nT) hlt sm  (* le (Suc(n*n))(n*n) = lt (n*n)(n*n) *)
      in Thm.implies_intr (ctermS2 (jT (le mT nT))) (Thm.implies_elim (oFalse_elimS_at goalC) (lt_irrefl_atS (mult nT nT) tr)) end
  in disjE_elimS2 (le nT mT, le mT nT, goalC) tot cNM cMN end;

(* ============================================================================
   THE CHARACTERIZATION THEOREM
   ============================================================================ *)
val () = out "PYTH_CHAR_MAIN_BEGIN\n";

(* REUSE the KEY delta's coprime/coprimeAbs (Free "d_cop") so the conclusion's coprime
   conjunct is LITERALLY the KEY lemma's coprime form (no conversion needed). *)
fun coprimeAbsC (uT,vT) = coprimeAbs (uT,vT);
fun coprimeC (uT,vT) = coprime (uT,vT);
fun pyth_tripleC (aT,bT,cT) = mkConj (lt ZeroC aT) (mkConj (lt ZeroC bT) (oeq (add (mult aT aT) (mult bT bT)) (mult cT cT)));

fun concl_inner (mT, nT, aT, bT, cT) =
  mkConj (lt nT mT)
    (mkConj (coprimeC (mT, nT))
      (mkConj (oeq cT (add (mult mT mT) (mult nT nT)))
        (mkConj (oeq bT (mult twoC (mult mT nT)))
                (oeq (add aT (mult nT nT)) (mult mT mT)))));
fun innerNAbs (mT, aT, bT, cT) = let val nF = Free("n_concl", natT) in Term.lambda nF (concl_inner (mT, nF, aT, bT, cT)) end;
fun outerMAbs (aT, bT, cT) = let val mF = Free("m_concl", natT) in Term.lambda mF (mkEx (innerNAbs (mF, aT, bT, cT))) end;
fun conclEx (aT, bT, cT) = mkEx (outerMAbs (aT, bT, cT));

val () = out "PYTH_CHAR_PREDS_OK\n";

val char_thm =
  let
    val aF = Free("a_ch", natT);
    val bF = Free("b_ch", natT);
    val cF = Free("c_ch", natT);
    val hTriple = Thm.assume (ctermS2 (jT (pyth_tripleC (aF, bF, cF))));
    val hPrim   = Thm.assume (ctermS2 (jT (coprimeC (aF, bF))));
    val hEvenB  = Thm.assume (ctermS2 (jT (evenAt bF)));
    val goalC   = conclEx (aF, bF, cF);

    val hPa = conjunct1_atS2 (lt ZeroC aF, mkConj (lt ZeroC bF) (oeq (add (mult aF aF) (mult bF bF)) (mult cF cF))) hTriple;
    val hBC = conjunct2_atS2 (lt ZeroC aF, mkConj (lt ZeroC bF) (oeq (add (mult aF aF) (mult bF bF)) (mult cF cF))) hTriple;
    val hPb = conjunct1_atS2 (lt ZeroC bF, oeq (add (mult aF aF) (mult bF bF)) (mult cF cF)) hBC;
    val hPy = conjunct2_atS2 (lt ZeroC bF, oeq (add (mult aF aF) (mult bF bF)) (mult cF cF)) hBC;

    fun primApply dT hda hdb =
      let val hImp = allE_atS2 (coprimeAbsC (aF, bF)) dT hPrim
          val s1 = mp_atS2 (dvd dT aF, mkImp (dvd dT bF) (oeq dT oneC)) hImp hda
      in mp_atS2 (dvd dT bF, oeq dT oneC) s1 hdb end;

    val bbAbs = let val bbF = Free("bb_e", natT) in Term.lambda bbF (oeq bF (mult twoC bbF)) end;
    val main = exE_elimS2 (bbAbs, goalC) hEvenB "bb_ch"
      (fn bb => fn hBev =>
       let
        val dvd2b = dvd_introS (twoC, bF, bb) hBev;
        (* ===== PARITY : a odd, c odd ===== *)
        val aOdd =
          let val par = parity_atS aF; val gC = oddAt aF
              val evCase = let val evP = let val kF = Free("k_ev", natT) in Term.lambda kF (oeq aF (mult twoC kF)) end
                               val hEv = Thm.assume (ctermS2 (jT (evenAt aF)))
                           in Thm.implies_intr (ctermS2 (jT (evenAt aF)))
                               (exE_elimS2 (evP, gC) hEv "k_ae"
                                 (fn k => fn hk =>
                                   let val two1 = primApply twoC (dvd_introS (twoC, aF, k) hk) dvd2b
                                       val fls = Suc_neq_Zero_atS ZeroC OF [Suc_inj_atS (suc ZeroC, ZeroC) OF [two1]]
                                   in Thm.implies_elim (oFalse_elimS_at gC) fls end)) end
              val odCase = let val hOd = Thm.assume (ctermS2 (jT (oddAt aF))) in Thm.implies_intr (ctermS2 (jT (oddAt aF))) hOd end
          in disjE_elimS2 (evenAt aF, oddAt aF, gC) par evCase odCase end;
        val a2odd =
          let val aoP = let val kF = Free("k_od", natT) in Term.lambda kF (oeq aF (suc (mult twoC kF))) end
          in exE_elimS2 (aoP, oddAt (mult aF aF)) aOdd "ka_od" (fn ka => fn hka => odd_sq_atS (aF, ka) hka) end;
        val b2even = even_sq_atS (bF, bb) hBev;
        val c2odd =
          let val gC = oddAt (mult cF cF)
              val aoP = let val kF = Free("k_od", natT) in Term.lambda kF (oeq (mult aF aF) (suc (mult twoC kF))) end
          in exE_elimS2 (aoP, gC) a2odd "p_c"
              (fn p => fn hp =>
                let val beP = let val kF = Free("k_ev", natT) in Term.lambda kF (oeq (mult bF bF) (mult twoC kF)) end
                in exE_elimS2 (beP, gC) b2even "q_c"
                    (fn q => fn hq =>
                      let val s1 = add_cong_lS (mult aF aF, suc (mult twoC p), mult bF bF) hp
                          val s2 = add_cong_rS (suc (mult twoC p), mult bF bF, mult twoC q) hq
                          val s3 = addSucS_at (mult twoC p, mult twoC q)
                          val s4 = Suc_cong OF [oeq_sym OF [left_distrib_atS (twoC, p, q)]]
                          val ab_odd = oeq_trans OF [s1, oeq_trans OF [s2, oeq_trans OF [s3, s4]]]
                          val cc_odd = oeq_trans OF [oeq_sym OF [hPy], ab_odd]
                          val oddP = let val kF = Free("k_od", natT) in Term.lambda kF (oeq (mult cF cF) (suc (mult twoC kF))) end
                      in exI_atS2 oddP (add p q) cc_odd end) end) end;
        val cOdd =
          let val par = parity_atS cF; val gC = oddAt cF
              val evCase = let val evP = let val kF = Free("k_ev", natT) in Term.lambda kF (oeq cF (mult twoC kF)) end
                               val hEv = Thm.assume (ctermS2 (jT (evenAt cF)))
                           in Thm.implies_intr (ctermS2 (jT (evenAt cF)))
                               (exE_elimS2 (evP, gC) hEv "k_ce"
                                 (fn k => fn hk =>
                                   let val c2ev = even_sq_atS (cF, k) hk
                                       val evP2 = let val wF = Free("k_ev", natT) in Term.lambda wF (oeq (mult cF cF) (mult twoC wF)) end
                                   in exE_elimS2 (evP2, gC) c2ev "ke_c"
                                       (fn ke => fn hke =>
                                         let val odP = let val wF = Free("k_od", natT) in Term.lambda wF (oeq (mult cF cF) (suc (mult twoC wF))) end
                                         in exE_elimS2 (odP, gC) c2odd "ko_c"
                                             (fn ko => fn hko => Thm.implies_elim (oFalse_elimS_at gC) (even_odd_absurd (ke, ko) hke hko)) end) end)) end
              val odCase = let val hOd = Thm.assume (ctermS2 (jT (oddAt cF))) in Thm.implies_intr (ctermS2 (jT (oddAt cF))) hOd end
          in disjE_elimS2 (evenAt cF, oddAt cF, gC) par evCase odCase end;
        val () = out "MAIN_PARITY_DONE\n";

        (* ===== c > a (d>0, c=a+d) ===== *)
        val b2pos =
          let val gC = lt ZeroC (mult bF bF)
              val leAbs = let val wF = Free("w_b", natT) in Term.lambda wF (oeq bF (add (suc ZeroC) wF)) end
          in exE_elimS2 (leAbs, gC) hPb "w_b"
              (fn w => fn hw =>
                let val b_Sw = oeq_trans OF [hw, oeq_trans OF [addSucS_at (ZeroC, w), Suc_cong OF [add0S_at w]]]
                    val l1 = mult_cong_lS (bF, suc w, bF) b_Sw
                    val l2 = multSuclS_at (w, bF)
                    val l3 = add_cong_lS (bF, suc w, mult w bF) b_Sw
                    val l4 = addSucS_at (w, mult w bF)
                    val bb_S = oeq_trans OF [l1, oeq_trans OF [l2, oeq_trans OF [l3, l4]]]
                    val rhs = oeq_trans OF [addSucS_at (ZeroC, add w (mult w bF)), Suc_cong OF [add0S_at (add w (mult w bF))]]
                    val bb_form = oeq_trans OF [bb_S, oeq_sym OF [rhs]]
                in le_introS (suc ZeroC, mult bF bF, add w (mult w bF)) bb_form end) end;
        val lt_a2_ab =
          let val gC = lt (mult aF aF) (add (mult aF aF) (mult bF bF))
              val leAbs = let val wF = Free("w_b2", natT) in Term.lambda wF (oeq (mult bF bF) (add (suc ZeroC) wF)) end
          in exE_elimS2 (leAbs, gC) b2pos "w_b2"
              (fn w => fn hw =>
                let val s1 = add_cong_rS (mult aF aF, mult bF bF, add (suc ZeroC) w) hw
                    val inner = oeq_trans OF [addSucS_at (ZeroC, w), Suc_cong OF [add0S_at w]]
                    val s2 = add_cong_rS (mult aF aF, add (suc ZeroC) w, suc w) inner
                    val s3 = addSrS_at (mult aF aF, w)
                    val s4 = oeq_sym OF [addSucS_at (mult aF aF, w)]
                    val form = oeq_trans OF [s1, oeq_trans OF [s2, oeq_trans OF [s3, s4]]]
                in le_introS (suc (mult aF aF), add (mult aF aF) (mult bF bF), w) form end) end;
        val lt_a2_c2 = let val zV = Free("z_lt2", natT); val Psub = Term.lambda zV (lt (mult aF aF) zV)
                       in oeq_rewrite_atS (Psub, add (mult aF aF) (mult bF bF), mult cF cF) hPy lt_a2_ab end;
        val a_ne_c =
          let val hac = Thm.assume (ctermS2 (jT (oeq aF cF)))
              val aa_cc = oeq_trans OF [mult_cong_lS (aF, cF, aF) hac, mult_cong_rS (cF, aF, cF) hac]
              val zV = Free("z_ne", natT); val Psub = Term.lambda zV (lt (mult aF aF) zV)
              val lt_aa_aa = oeq_rewrite_atS (Psub, mult cF cF, mult aF aF) (oeq_sym OF [aa_cc]) lt_a2_c2
          in impI_atS2 (oeq aF cF, oFalseC) (Thm.implies_intr (ctermS2 (jT (oeq aF cF))) (lt_irrefl_atS (mult aF aF) lt_aa_aa)) end;
        val le_a_c =
          let val tot = le_total_atS (aF, cF); val gC = le aF cF
              val cAC = let val h = Thm.assume (ctermS2 (jT (le aF cF))) in Thm.implies_intr (ctermS2 (jT (le aF cF))) h end
              val cCA = let val h = Thm.assume (ctermS2 (jT (le cF aF)))
                            val tr = le_trans_atS (suc (mult aF aF), mult cF cF, mult aF aF) lt_a2_c2 (sq_mono_atS (cF, aF) h)
                        in Thm.implies_intr (ctermS2 (jT (le cF aF))) (Thm.implies_elim (oFalse_elimS_at gC) (lt_irrefl_atS (mult aF aF) tr)) end
          in disjE_elimS2 (le aF cF, le cF aF, gC) tot cAC cCA end;
        val lt_a_c = le_neq_lt_atS (aF, cF) le_a_c a_ne_c;
        val () = out "MAIN_LT_A_C_DONE\n";

        val leAbsAC = let val wF = Free("w_ac", natT) in Term.lambda wF (oeq cF (add (suc aF) wF)) end;
       in
        exE_elimS2 (leAbsAC, goalC) lt_a_c "w_ac"
          (fn w => fn hw =>
            let
              val dT = suc w
              val h_c_ad = oeq_trans OF [hw, oeq_trans OF [addSucS_at (aF, w), oeq_sym OF [addSrS_at (aF, w)]]]  (* c = a + d *)
              val hd_pos = lt_zero_suc_atS w   (* 0 < d *)
              val () = out "MAIN_D_UNPACKED\n";

              (* b^2 = d*(2a+d) *)
              val b2_dd =
                let
                  val cc = oeq_trans OF [mult_cong_lS (cF, add aF dT, cF) h_c_ad, mult_cong_rS (add aF dT, cF, add aF dT) h_c_ad]
                  val rd1 = rdist_at_S2 (aF, dT, add aF dT)
                  val ld_a = left_distrib_atS (aF, aF, dT)
                  val ld_d = left_distrib_atS (dT, aF, dT)
                  val exp1 = oeq_trans OF [rd1, add_cong_lS (mult aF (add aF dT), add (mult aF aF) (mult aF dT), mult dT (add aF dT)) ld_a]
                  val exp2 = oeq_trans OF [exp1, add_cong_rS (add (mult aF aF) (mult aF dT), mult dT (add aF dT), add (mult dT aF) (mult dT dT)) ld_d]
                  val cc_exp = oeq_trans OF [cc, exp2]
                  val cc_assoc = oeq_trans OF [cc_exp, addassocS_at (mult aF aF, mult aF dT, add (mult dT aF) (mult dT dT))]
                  val both = oeq_trans OF [hPy, cc_assoc]
                  val b2_form = add_left_cancel_atS (mult aF aF, mult bF bF, add (mult aF dT) (add (mult dT aF) (mult dT dT))) both
                  val lhs1 = add_cong_lS (mult aF dT, mult dT aF, add (mult dT aF) (mult dT dT)) (mult_comm_atS (aF, dT))
                  val lhs2 = oeq_sym OF [addassocS_at (mult dT aF, mult dT aF, mult dT dT)]
                  val b2_canon = oeq_trans OF [b2_form, oeq_trans OF [lhs1, lhs2]]
                  val tgt = oeq_trans OF [left_distrib_atS (dT, add aF aF, dT),
                              add_cong_lS (mult dT (add aF aF), add (mult dT aF) (mult dT aF), mult dT dT) (left_distrib_atS (dT, aF, aF))]
                  val b2_da = oeq_trans OF [b2_canon, oeq_sym OF [tgt]]
                  val zV = Free("z_pr", natT); val Psub = Term.lambda zV (oeq (mult bF bF) (mult dT (add zV dT)))
                in oeq_rewrite_atS (Psub, add aF aF, mult twoC aF) (oeq_sym OF [two_mult_atS aF]) b2_da end;  (* b*b = d*(2a+d) *)
              val () = out "MAIN_B2_DD_DONE\n";
(* ===== continuation : d even -> delta ; c+a=2f ; bb^2=delta*f ; coprime delta f ;
         key lemma -> delta=n^2, f=m^2 ; reassemble.  In scope:
   aF,bF,cF,bb,dT,hBev,hPy,hPa,b2_dd,h_c_ad,hd_pos,aOdd,cOdd,primApply,hPrim,dvd2b,goalC.
   Uses KEY delta's: coprime, coprimeAbs, sqEx, sqAbs, resultC, key_lemma_thm,
                     mult_eq_zero_atS, mult_left_cancel_atS, euclid_lemma_atS,
                     prime_divisor_exists_atS, prime2_gt1S, Suc_inj_atS, oneC.  ===== *)

(* d EVEN *)
val d_even =
  let
    val par = parity_atS dT; val gC = evenAt dT
    val evCase = let val h = Thm.assume (ctermS2 (jT (evenAt dT))) in Thm.implies_intr (ctermS2 (jT (evenAt dT))) h end
    val odCase =
      let val hOd = Thm.assume (ctermS2 (jT (oddAt dT)))
          val dodP = let val kF = Free("k_od", natT) in Term.lambda kF (oeq dT (suc (mult twoC kF))) end
          val body = exE_elimS2 (dodP, gC) hOd "kd_od"
            (fn kd => fn hkd =>
              let val aodP = let val kF = Free("k_od", natT) in Term.lambda kF (oeq aF (suc (mult twoC kF))) end
              in exE_elimS2 (aodP, gC) aOdd "ka_od2"
                  (fn ka => fn hka =>
                    let val ad_even = odd_add_odd_even (aF, dT, ka, kd) hka hkd
                        val zV = Free("z_de", natT); val Psub = Term.lambda zV (evenAt zV)
                        val c_even = oeq_rewrite_atS (Psub, add aF dT, cF) (oeq_sym OF [h_c_ad]) ad_even
                        val evP = let val wF = Free("k_ev", natT) in Term.lambda wF (oeq cF (mult twoC wF)) end
                    in exE_elimS2 (evP, gC) c_even "kce_de"
                        (fn kce => fn hkce =>
                          let val codP = let val wF = Free("k_od", natT) in Term.lambda wF (oeq cF (suc (mult twoC wF))) end
                          in exE_elimS2 (codP, gC) cOdd "kco_de"
                              (fn kco => fn hkco => Thm.implies_elim (oFalse_elimS_at gC) (even_odd_absurd (kce, kco) hkce hkco)) end) end) end)
      in Thm.implies_intr (ctermS2 (jT (oddAt dT))) body end
  in disjE_elimS2 (evenAt dT, oddAt dT, gC) par evCase odCase end;
val () = out "FIN_D_EVEN\n";

val delAbs = let val dF = Free("delta_e", natT) in Term.lambda dF (oeq dT (mult twoC dF)) end;
val finished =
  exE_elimS2 (delAbs, goalC) d_even "delta"
    (fn delta => fn hDel =>
      let
        val fT = add aF delta
        (* bb^2 = delta*f *)
        val twoa_2del = add_cong_rS (mult twoC aF, dT, mult twoC delta) hDel
        val ld_f = oeq_sym OF [left_distrib_atS (twoC, aF, delta)]
        val twoad_2f = oeq_trans OF [twoa_2del, ld_f]
        val dd1 = mult_cong_lS (dT, mult twoC delta, add (mult twoC aF) dT) hDel
        val dd2 = mult_cong_rS (mult twoC delta, add (mult twoC aF) dT, mult twoC fT) twoad_2f
        val b2_4df0 = oeq_trans OF [b2_dd, oeq_trans OF [dd1, dd2]]
        val a1 = mult_assoc_atS (twoC, delta, mult twoC fT)
        val df1 = oeq_sym OF [mult_assoc_atS (delta, twoC, fT)]
        val df2 = mult_cong_lS (mult delta twoC, mult twoC delta, fT) (mult_comm_atS (delta, twoC))
        val df3 = mult_assoc_atS (twoC, delta, fT)
        val del2f = oeq_trans OF [df1, oeq_trans OF [df2, df3]]
        val a2 = mult_cong_rS (twoC, mult delta (mult twoC fT), mult twoC (mult delta fT)) del2f
        val b2_4df = oeq_trans OF [b2_4df0, oeq_trans OF [a1, a2]]   (* (b*b) = (2*(2*(delta*f))) *)
        val bb1 = oeq_trans OF [mult_cong_lS (bF, mult twoC bb, bF) hBev, mult_cong_rS (mult twoC bb, bF, mult twoC bb) hBev]
        val bb_a1 = mult_assoc_atS (twoC, bb, mult twoC bb)
        val bbk1 = oeq_sym OF [mult_assoc_atS (bb, twoC, bb)]
        val bbk2 = mult_cong_lS (mult bb twoC, mult twoC bb, bb) (mult_comm_atS (bb, twoC))
        val bbk3 = mult_assoc_atS (twoC, bb, bb)
        val bbk = oeq_trans OF [bbk1, oeq_trans OF [bbk2, bbk3]]
        val bb_a2 = mult_cong_rS (twoC, mult bb (mult twoC bb), mult twoC (mult bb bb)) bbk
        val bb_4 = oeq_trans OF [bb1, oeq_trans OF [bb_a1, bb_a2]]   (* (b*b) = (2*(2*(bb*bb))) *)
        val eq4 = oeq_trans OF [oeq_sym OF [bb_4], b2_4df]           (* (2*(2*(bb*bb))) = (2*(2*(delta*f))) *)
        val canc1 = mult_left_cancel_atS (twoC, mult twoC (mult bb bb), mult twoC (mult delta fT)) lt0_2 eq4
        val bb2_df = mult_left_cancel_atS (twoC, mult bb bb, mult delta fT) lt0_2 canc1   (* (bb*bb) = (delta*f) *)
        val () = out "FIN_BB2_DF\n";

        (* coprime delta f (KEY's coprime form) *)
        val coprimeDF =
          let
            val gF = Free("d_cop", natT)    (* MATCH KEY's coprimeAbs free name *)
            val hgd = Thm.assume (ctermS2 (jT (dvd gF delta)))
            val hgf = Thm.assume (ctermS2 (jT (dvd gF fT)))
            val zV = Free("z_cf", natT); val Psub = Term.lambda zV (dvd gF zV)
            val hg_da = oeq_rewrite_atS (Psub, fT, add delta aF) (addcommS_at (aF, delta)) hgf
            val hga = dvd_diff_atS (gF, delta, aF) hgd hg_da     (* g|a *)
            val hgdf = dvd_mult_right_atS (gF, delta, fT) hgd     (* g|(delta*f) *)
            val zV2 = Free("z_cf2", natT); val Psub2 = Term.lambda zV2 (dvd gF zV2)
            val hg_bb2 = oeq_rewrite_atS (Psub2, mult delta fT, mult bb bb) (oeq_sym OF [bb2_df]) hgdf  (* g|(bb*bb) *)
            val le_a_f = le_introS (aF, fT, delta) (oeqreflS_at fT)   (* le a f *)
            val lt0_f = le_trans_atS (suc ZeroC, aF, fT) hPa le_a_f   (* lt 0 f *)
            val lt0_g =
              let val gAbs = let val kF = Free("kg", natT) in Term.lambda kF (oeq fT (mult gF kF)) end
              in exE_elimS2 (gAbs, lt ZeroC gF) hgf "kg_w"
                  (fn kg => fn hkg =>
                    let val dzG = dzosS_at gF
                        val cZ = let val hg0 = Thm.assume (ctermS2 (jT (oeq gF ZeroC)))
                                     val f0 = oeq_trans OF [hkg, oeq_trans OF [mult_cong_lS (gF, ZeroC, kg) hg0, mult0lS_at kg]]
                                     val zV3 = Free("z_g0", natT); val Ps3 = Term.lambda zV3 (lt ZeroC zV3)
                                     val lt00 = oeq_rewrite_atS (Ps3, fT, ZeroC) f0 lt0_f
                                 in Thm.implies_intr (ctermS2 (jT (oeq gF ZeroC))) (Thm.implies_elim (oFalse_elimS_at (lt ZeroC gF)) (lt_irrefl_atS ZeroC lt00)) end
                        val sucGAbs = let val gpF = Free("gp", natT) in Term.lambda gpF (oeq gF (suc gpF)) end
                        val cS = let val hEx = Thm.assume (ctermS2 (jT (mkEx sucGAbs)))
                                 in Thm.implies_intr (ctermS2 (jT (mkEx sucGAbs)))
                                     (exE_elimS2 (sucGAbs, lt ZeroC gF) hEx "gp_w"
                                       (fn gp => fn hgp =>
                                          let val lt0Sg = lt_zero_suc_atS gp
                                              val zV4 = Free("z_gs", natT); val Ps4 = Term.lambda zV4 (lt ZeroC zV4)
                                          in oeq_rewrite_atS (Ps4, suc gp, gF) (oeq_sym OF [hgp]) lt0Sg end)) end
                    in disjE_elimS2 (oeq gF ZeroC, mkEx sucGAbs, lt ZeroC gF) dzG cZ cS end)
              end
            val not_lt1g =
              let
                val hlt1g = Thm.assume (ctermS2 (jT (lt oneC gF)))
                val pdEx = prime_divisor_exists_atS gF hlt1g
                val pdbody = let val pF = Free("p_pdc", natT) in Term.lambda pF (mkConj (prime2 pF) (dvd pF gF)) end
                val body = exE_elimS2 (pdbody, oFalseC) pdEx "p_cf"
                  (fn pP => fn hpP =>
                    let
                      val hPr = conjunct1_atS2 (prime2 pP, dvd pP gF) hpP
                      val hPg = conjunct2_atS2 (prime2 pP, dvd pP gF) hpP
                      val hPa' = dvd_trans_atS2 (pP, gF, aF) hPg hga
                      val hPbb2 = dvd_trans_atS2 (pP, gF, mult bb bb) hPg hg_bb2
                      val euc = euclid_lemma_atS (pP, bb, bb) hPr hPbb2
                      val hPbb = disjE_elimS2 (dvd pP bb, dvd pP bb, dvd pP bb) euc
                                   (let val h = Thm.assume (ctermS2 (jT (dvd pP bb))) in Thm.implies_intr (ctermS2 (jT (dvd pP bb))) h end)
                                   (let val h = Thm.assume (ctermS2 (jT (dvd pP bb))) in Thm.implies_intr (ctermS2 (jT (dvd pP bb))) h end)
                      val b_bb2 = oeq_trans OF [hBev, mult_comm_atS (twoC, bb)]
                      val bb_dvd_b = dvd_introS (bb, bF, twoC) b_bb2
                      val hPb' = dvd_trans_atS2 (pP, bb, bF) hPbb bb_dvd_b
                      val p1 = primApply pP hPa' hPb'
                      val hLt1p = prime2_gt1S pP hPr
                      val zV5 = Free("z_p1", natT); val Ps5 = Term.lambda zV5 (lt oneC zV5)
                      val lt11 = oeq_rewrite_atS (Ps5, pP, oneC) p1 hLt1p
                    in lt_irrefl_atS oneC lt11 end)
              in impI_atS2 (lt oneC gF, oFalseC) (Thm.implies_intr (ctermS2 (jT (lt oneC gF))) body) end
            val le_g_1 = nlt_le_atS (oneC, gF) not_lt1g
            val g_eq_1 = le_antisym_atS (gF, oneC) le_g_1 lt0_g
            val impThm = impI_atS2 (dvd gF fT, oeq gF oneC) (Thm.implies_intr (ctermS2 (jT (dvd gF fT))) g_eq_1)
            val impThm2 = impI_atS2 (dvd gF delta, mkImp (dvd gF fT) (oeq gF oneC)) (Thm.implies_intr (ctermS2 (jT (dvd gF delta))) impThm)
            val minor = Thm.forall_intr (ctermS2 gF) impThm2
          in allI_atS2 (coprimeAbs (delta, fT)) minor end;
        val () = out "FIN_COPRIME_DF\n";

        (* KEY LEMMA at (delta, f, bb) *)
        val key_inst = beta_norm (Drule.infer_instantiate ctxtS2
                         [(("u_key",0), ctermS2 delta),(("v_key",0), ctermS2 fT),(("w_key",0), ctermS2 bb)] (varify key_lemma_thm));
        val df_eq = oeq_sym OF [bb2_df]                   (* (delta*f) = (bb*bb) *)
        val keyRes = (key_inst OF [coprimeDF]) OF [df_eq]
        val () = out "FIN_KEY_APPLIED\n";
        val sqDeltaEx = conjunct1_atS2 (sqEx delta, sqEx fT) keyRes
        val sqFEx     = conjunct2_atS2 (sqEx delta, sqEx fT) keyRes
      in
        exE_elimS2 (sqAbs delta, goalC) sqDeltaEx "n_sq"
          (fn nT => fn hn =>     (* delta = n*n *)
            exE_elimS2 (sqAbs fT, goalC) sqFEx "m_sq"
              (fn mT => fn hm =>   (* f = m*m *)
                let
                  (* m*m = f = a + delta = a + n*n.  so a+n*n = m*m (one conjunct). *)
                  val m2_adel = oeq_trans OF [oeq_sym OF [hm], oeqreflS_at fT]   (* m*m = f = (a+delta) ; fT IS add a delta *)
                  (* a + delta = a + n*n [delta = n*n] *)
                  val adel_ann = add_cong_rS (aF, delta, mult nT nT) hn          (* (a+delta) = (a + n*n) *)
                  val m2_ann = oeq_trans OF [m2_adel, adel_ann]                  (* m*m = (a + n*n) *)
                  val a_nn_m2 = oeq_sym OF [m2_ann]                              (* (a + n*n) = m*m  [conjunct 5] *)
                  val () = out "FIN_CONJ5\n";

                  (* c = m*m + n*n.  c = a+d = a+2delta = a+2(n*n).  m*m = a+n*n.  m*m+n*n = (a+n*n)+n*n = a+(n*n+n*n) = a+2(n*n). *)
                  (* c = a + d ; d = 2 delta = 2(n*n) *)
                  val d_2nn = oeq_trans OF [hDel, mult_cong_rS (twoC, delta, mult nT nT) hn]   (* d = 2*(n*n) *)
                  val c_a2nn = oeq_trans OF [h_c_ad, add_cong_rS (aF, dT, mult twoC (mult nT nT)) d_2nn]  (* c = a + 2*(n*n) *)
                  (* m*m + n*n = (a+n*n)+n*n [m2_ann] = a + (n*n + n*n) [assoc] = a + 2*(n*n) [two_mult sym] *)
                  val mn1 = add_cong_lS (mult mT mT, add aF (mult nT nT), mult nT nT) m2_ann   (* (m*m + n*n) = ((a+n*n)+n*n) *)
                  val mn2 = addassocS_at (aF, mult nT nT, mult nT nT)                          (* ((a+n*n)+n*n) = (a + (n*n+n*n)) *)
                  val mn3 = add_cong_rS (aF, add (mult nT nT) (mult nT nT), mult twoC (mult nT nT)) (oeq_sym OF [two_mult_atS (mult nT nT)])  (* (a+(n*n+n*n)) = (a + 2*(n*n)) *)
                  val mn_a2nn = oeq_trans OF [mn1, oeq_trans OF [mn2, mn3]]                     (* (m*m + n*n) = (a + 2*(n*n)) *)
                  val c_mn = oeq_trans OF [c_a2nn, oeq_sym OF [mn_a2nn]]                        (* c = (m*m + n*n)  [conjunct 3] *)
                  val () = out "FIN_CONJ3\n";

                  (* b = 2*(m*n).  bb*bb = delta*f = (n*n)*(m*m).  (n*n)*(m*m) = (m*n)*(m*n) [comm/assoc].
                     sqrt_unique : bb*bb = (m*n)*(m*n) -> bb = m*n.  then b = 2bb = 2(m*n). *)
                  val df_nm = oeq_trans OF [bb2_df, oeq_trans OF [mult_cong_lS (delta, mult nT nT, fT) hn,
                                                                  mult_cong_rS (mult nT nT, fT, mult mT mT) hm]]  (* (bb*bb) = ((n*n)*(m*m)) *)
                  (* (n*n)*(m*m) = (m*n)*(m*n) : (n*n)*(m*m) = n*(n*(m*m)) [assoc] ; messy. do via 4-term swap.
                     (n*n)*(m*m) = (m*n)*(m*n).  Prove both = a canonical product.  Use mult_comm + assoc steps:
                       (n*n)*(m*m) = n*(n*(m*m)) [assoc]
                       n*(m*m) = (n*m)*m [assoc back] = (m*n)*m [comm] = m*(n*m)? ...
                     Simpler: (m*n)*(m*n) = m*(n*(m*n)) [assoc] = m*((n*m)*n) [assoc back] = m*((m*n)*n) [comm]
                       = m*(m*(n*n)) [assoc] = (m*m)*(n*n) [assoc back].  And (n*n)*(m*m) = (m*m)*(n*n) [comm].
                     So both equal (m*m)*(n*n). *)
                  val nnmm_comm = mult_comm_atS (mult nT nT, mult mT mT)         (* ((n*n)*(m*m)) = ((m*m)*(n*n)) *)
                  (* (m*n)*(m*n) = (m*m)*(n*n) : *)
                  val e1 = mult_assoc_atS (mT, nT, mult mT nT)                   (* ((m*n)*(m*n)) = (m*(n*(m*n))) *)
                  val e2 = oeq_sym OF [mult_assoc_atS (nT, mT, nT)]              (* (n*(m*n)) = ((n*m)*n) *)
                  val e3 = mult_cong_lS (mult nT mT, mult mT nT, nT) (mult_comm_atS (nT, mT))  (* ((n*m)*n) = ((m*n)*n) *)
                  val e4 = mult_assoc_atS (mT, nT, nT)                           (* ((m*n)*n) = (m*(n*n)) *)
                  val nmn = oeq_trans OF [e2, oeq_trans OF [e3, e4]]             (* (n*(m*n)) = (m*(n*n)) *)
                  val e5 = mult_cong_rS (mT, mult nT (mult mT nT), mult mT (mult nT nT)) nmn  (* (m*(n*(m*n))) = (m*(m*(n*n))) *)
                  val e6 = oeq_sym OF [mult_assoc_atS (mT, mT, mult nT nT)]      (* (m*(m*(n*n))) = ((m*m)*(n*n)) *)
                  val mnmn_mmnn = oeq_trans OF [e1, oeq_trans OF [e5, e6]]       (* ((m*n)*(m*n)) = ((m*m)*(n*n)) *)
                  val bb2_mnmn = oeq_trans OF [df_nm, oeq_trans OF [nnmm_comm, oeq_sym OF [mnmn_mmnn]]]  (* (bb*bb) = ((m*n)*(m*n)) *)
                  val bb_mn = sqrt_unique_atS (bb, mult mT nT) bb2_mnmn          (* bb = m*n *)
                  val b_2mn = oeq_trans OF [hBev, mult_cong_rS (twoC, bb, mult mT nT) bb_mn]  (* b = 2*(m*n)  [conjunct 4] *)
                  val () = out "FIN_CONJ4\n";

                  (* lt n m : m*m = a+n*n, a>0 -> n*n < m*m -> n<m (lt_sq_rev). *)
                  (* lt (n*n)(a + n*n) : a>0 = le 1 a = Ex w. a = Suc 0 + w = Suc w. a+n*n = Suc w + n*n = Suc(w+n*n) = Suc(n*n + w) = Suc(n*n)+w. *)
                  val ltnm =
                    let
                      val leAbs = let val wF = Free("w_lt", natT) in Term.lambda wF (oeq aF (add (suc ZeroC) wF)) end
                      val lt_nn_ann = exE_elimS2 (leAbs, lt (mult nT nT) (add aF (mult nT nT))) hPa "w_lt"
                        (fn w => fn hw =>     (* a = Suc 0 + w *)
                          let
                            val a_Sw = oeq_trans OF [hw, oeq_trans OF [addSucS_at (ZeroC, w), Suc_cong OF [add0S_at w]]]  (* a = Suc w *)
                            (* a + n*n = Suc w + n*n = Suc(w + n*n) = Suc(n*n + w) = Suc(n*n) + w *)
                            val s1 = add_cong_lS (aF, suc w, mult nT nT) a_Sw      (* (a+n*n) = (Suc w + n*n) *)
                            val s2 = addSucS_at (w, mult nT nT)                    (* (Suc w + n*n) = Suc(w + n*n) *)
                            val s3 = Suc_cong OF [addcommS_at (w, mult nT nT)]      (* Suc(w + n*n) = Suc(n*n + w) *)
                            val s4 = oeq_sym OF [addSucS_at (mult nT nT, w)]        (* Suc(n*n + w) = (Suc(n*n) + w) *)
                            val ann_form = oeq_trans OF [s1, oeq_trans OF [s2, oeq_trans OF [s3, s4]]]  (* (a+n*n) = (Suc(n*n) + w) *)
                          in le_introS (suc (mult nT nT), add aF (mult nT nT), w) ann_form end)
                      (* rewrite a+n*n -> m*m via m2_ann : m*m = a+n*n -> a+n*n = m*m (sym) *)
                      val zV = Free("z_ltnm", natT); val Psub = Term.lambda zV (lt (mult nT nT) zV)
                      val lt_nn_mm = oeq_rewrite_atS (Psub, add aF (mult nT nT), mult mT mT) (oeq_sym OF [m2_ann]) lt_nn_ann  (* lt (n*n)(m*m) *)
                    in lt_sq_rev_atS (nT, mT) lt_nn_mm end   (* lt n m  [conjunct 1] *)
                  val () = out "FIN_CONJ1\n";

                  (* coprime m n : Forall(%g. g|m -> g|n -> g=1).  g|m -> g|m*m=f ; g|n -> g|n*n=delta ;
                     coprimeDF g : g|delta -> g|f -> g=1. *)
                  val coprimeMN =
                    let
                      val gF = Free("d_cop", natT)
                      val hgm = Thm.assume (ctermS2 (jT (dvd gF mT)))
                      val hgn = Thm.assume (ctermS2 (jT (dvd gF nT)))
                      (* g|delta : delta = n*n ; g|n -> g|(n*n) [dvd_mult_right g|n -> g|(n*n)] ; rewrite n*n -> delta *)
                      val g_nn = dvd_mult_right_atS (gF, nT, nT) hgn       (* g|(n*n) *)
                      val zV = Free("z_cmn", natT); val Ps = Term.lambda zV (dvd gF zV)
                      val g_delta = oeq_rewrite_atS (Ps, mult nT nT, delta) (oeq_sym OF [hn]) g_nn  (* g|delta *)
                      val g_mm = dvd_mult_right_atS (gF, mT, mT) hgm        (* g|(m*m) *)
                      val zV2 = Free("z_cmn2", natT); val Ps2 = Term.lambda zV2 (dvd gF zV2)
                      val g_f = oeq_rewrite_atS (Ps2, mult mT mT, fT) (oeq_sym OF [hm]) g_mm     (* g|f *)
                      (* coprimeDF : Forall(%d. d|delta -> d|f -> d=1).  apply at g. *)
                      val hImp = allE_atS2 (coprimeAbs (delta, fT)) gF coprimeDF
                      val s1 = mp_atS2 (dvd gF delta, mkImp (dvd gF fT) (oeq gF oneC)) hImp g_delta
                      val g1 = mp_atS2 (dvd gF fT, oeq gF oneC) s1 g_f       (* g = 1 *)
                      val impA = impI_atS2 (dvd gF nT, oeq gF oneC) (Thm.implies_intr (ctermS2 (jT (dvd gF nT))) g1)
                      val impB = impI_atS2 (dvd gF mT, mkImp (dvd gF nT) (oeq gF oneC)) (Thm.implies_intr (ctermS2 (jT (dvd gF mT))) impA)
                      val minor = Thm.forall_intr (ctermS2 gF) impB
                    in allI_atS2 (coprimeAbs (mT, nT)) minor end;   (* coprime m n  [conjunct 2] *)
                  val () = out "FIN_CONJ2\n";

                  (* assemble the 5-fold conjunction (right-nested) at witnesses m, n *)
                  val conj45 = conjI_atS2 (oeq bF (mult twoC (mult mT nT)), oeq (add aF (mult nT nT)) (mult mT mT)) b_2mn a_nn_m2
                  val conj345 = conjI_atS2 (oeq cF (add (mult mT mT) (mult nT nT)),
                                            mkConj (oeq bF (mult twoC (mult mT nT))) (oeq (add aF (mult nT nT)) (mult mT mT))) c_mn conj45
                  val conj2345 = conjI_atS2 (coprime (mT, nT),
                                             mkConj (oeq cF (add (mult mT mT) (mult nT nT)))
                                               (mkConj (oeq bF (mult twoC (mult mT nT))) (oeq (add aF (mult nT nT)) (mult mT mT)))) coprimeMN conj345
                  val conjAll = conjI_atS2 (lt nT mT,
                                            mkConj (coprime (mT, nT))
                                              (mkConj (oeq cF (add (mult mT mT) (mult nT nT)))
                                                (mkConj (oeq bF (mult twoC (mult mT nT))) (oeq (add aF (mult nT nT)) (mult mT mT))))) ltnm conj2345
                  val () = out "FIN_CONJ_ALL\n";
                  (* exI over n (inner) then m (outer) *)
                  val exN = exI_atS2 (innerNAbs (mT, aF, bF, cF)) nT conjAll   (* Ex n. concl_inner(m,n) *)
                  val exM = exI_atS2 (outerMAbs (aF, bF, cF)) mT exN           (* Ex m. Ex n. ... = goalC *)
                in exM end))
      end);
val () = out "FIN_FINISHED\n";
            in finished end)
       end);
  in main end;
val () = out ("PYTH_CHAR hyps=" ^ Int.toString (length (Thm.hyps_of char_thm)) ^ "\n");
val () = out "PYTH_CHAR_MAIN_DONE\n";

(* ============================================================================
   VALIDATION : 0-hyp (modulo the 3 antecedents) + aconv intended + soundness probes
   The proof `char_thm` was built by ASSUMING the 3 hypotheses (triple, primitive,
   even b) and proving conclEx, so we discharge them into object/meta implications
   and check the schematic statement.
   ============================================================================ *)
val () = out "PYTH_CHAR_VALIDATE_BEGIN\n";

(* discharge the 3 assumptions into a META-implication chain (schematic in a,b,c) *)
val aF = Free("a_ch", natT);
val bF = Free("b_ch", natT);
val cF = Free("c_ch", natT);
val char_meta =
  let
    val d1 = Thm.implies_intr (ctermS2 (jT (evenAt bF))) char_thm
    val d2 = Thm.implies_intr (ctermS2 (jT (coprimeC (aF, bF)))) d1
    val d3 = Thm.implies_intr (ctermS2 (jT (pyth_tripleC (aF, bF, cF)))) d2
  in varify d3 end;
val () = out (Syntax.string_of_term ctxtS2 (Thm.prop_of char_meta) ^ "\n");

val char_nhyp = length (Thm.hyps_of char_meta);
val () = out ("char hyps=" ^ Int.toString char_nhyp ^ "\n");

(* intended schematic statement built with Var(a,b,c) the SAME way *)
val aV = Var (("a_ch",0), natT);
val bV = Var (("b_ch",0), natT);
val cV = Var (("c_ch",0), natT);
val char_intended =
  Logic.mk_implies (jT (pyth_tripleC (aV, bV, cV)),
    Logic.mk_implies (jT (coprimeC (aV, bV)),
      Logic.mk_implies (jT (evenAt bV), jT (conclEx (aV, bV, cV)))));
val r_char = checkS2 ("pyth_char", char_meta, char_intended);

(* SOUNDNESS PROBE : dropping the EVEN-b hypothesis must change the theorem
   (it's false without it : an odd-b primitive triple like (4,3,5) has b odd... well in our
   stated form b is the EVEN leg; without "b even" the m,n decomposition can fail). *)
val probe_needs_even =
  let val bogus = Logic.mk_implies (jT (pyth_tripleC (aV, bV, cV)),
                    Logic.mk_implies (jT (coprimeC (aV, bV)), jT (conclEx (aV, bV, cV))))
  in not ((Thm.prop_of char_meta) aconv bogus) end;
val () = if probe_needs_even then out "PROBE_OK char needs even-b\n" else out "PROBE_UNSOUND_EVEN\n";

(* SOUNDNESS PROBE : dropping the PRIMITIVE hypothesis must change the theorem. *)
val probe_needs_prim =
  let val bogus = Logic.mk_implies (jT (pyth_tripleC (aV, bV, cV)),
                    Logic.mk_implies (jT (evenAt bV), jT (conclEx (aV, bV, cV))))
  in not ((Thm.prop_of char_meta) aconv bogus) end;
val () = if probe_needs_prim then out "PROBE_OK char needs primitive\n" else out "PROBE_UNSOUND_PRIM\n";

val () = if r_char andalso probe_needs_even andalso probe_needs_prim
         then out "PYTH_CHAR_OK\n" else out "PYTH_CHAR_FAILED\n";
