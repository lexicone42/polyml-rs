
(* ============================================================================
   PART B back-end BRIDGE (on ctxtGR / thyGR):
     pm_bridge :
       dvd p N  ==>  lt Zero N  ==>  lt N (mult p p)  ==>  four_sq N
         ==>  EX m. lt Zero m /\ lt m p /\ four_sq (mult m p)
   This packages a four-square representation of a multiple m*p of p with 0<m<p,
   given p | N, 0<N, N<p^2.  It is the reusable "package the multiple" step that
   PART B's pigeonhole front-end and PART C's descent both feed into.
   ============================================================================ *)
val () = out "L4_BRIDGE_BEGIN\n";

(* varify the two extra base lemmas onto GR *)
val mult_le_mono_vGR = varify mult_le_mono;   (* le j k ==> le (mult c j)(mult c k) *)
val nlt_le_vGR       = varify nlt_le;          (* ~(lt d c) ==> le c d *)
val mult_comm_vGR2   = varify mult_comm;
fun mult_le_mono_gr (cT, jT_, kT) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("c",0), ctermGR cT),(("j",0), ctermGR jT_),(("k",0), ctermGR kT)] mult_le_mono_vGR)) h;
fun nlt_le_gr (dT, cT) hneg =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
      [(("d",0), ctermGR dT),(("c",0), ctermGR cT)] nlt_le_vGR)) hneg;
fun mult_comm_gr (mT, nT) = beta_norm (Drule.infer_instantiate ctxtGR
      [(("m",0), ctermGR mT),(("n",0), ctermGR nT)] mult_comm_vGR2);
val () = out "L4_BRIDGE_VARIFY_OK\n";

val pm_bridge =
  let
    val pF = Free("p_pm", natT)
    val nF = Free("N_pm", natT)
    val hdvdP = jT (dvd pF nF);             val hdvd = Thm.assume (ctermGR hdvdP)
    val hposP = jT (lt ZeroC nF);           val hpos = Thm.assume (ctermGR hposP)
    val hltP  = jT (lt nF (mult pF pF));     val hlt  = Thm.assume (ctermGR hltP)
    val hfsqP = jT (four_sq nF);            val hfsq = Thm.assume (ctermGR hfsqP)

    (* goal :  EX m. lt 0 m /\ lt m p /\ four_sq (m*p) *)
    val mF0 = Free("m_pm", natT)
    fun goalPredBody mT = mkConj (lt ZeroC mT) (mkConj (lt mT pF) (four_sq (mult mT pF)))
    val goalPred = Term.lambda mF0 (goalPredBody mF0)
    val goalC    = mkEx goalPred

    (* dvd p N  =  Ex k. oeq N (mult p k).  exE on it. *)
    val dvdBody = Abs("k", natT, oeq nF (mult pF (Bound 0)))
    fun afterK k (hk : thm) =   (* hk : oeq N (mult p k) *)
      let
        (* ---- (1) lt 0 k :  if k=0 then N = p*0 = 0, contra 0<N. ---- *)
        val lt0k =
          let
            val dzk = dzos_d k     (* Disj (oeq k 0)(Ex q. oeq k (Suc q)) *)
            (* goal here: lt 0 k *)
            val caseK0 =
              let val hk0 = Thm.assume (ctermGR (jT (oeq k ZeroC)))
                  val pkEq = mult_cong_r_d (pF, k, ZeroC) hk0   (* p*k = p*0 *)
                  val p0   = mult0r_d pF                         (* p*0 = 0 *)
                  val nZero= oeqTrans_r2 (oeqTrans_r2 (hk, pkEq), p0)  (* N = 0 *)
                  val zN = Free("zlt0k", natT)
                  val Plt = Term.lambda zN (lt ZeroC zN)
                  val hlt0= oeq_rw_r (Plt, nF, ZeroC) nZero hpos      (* lt 0 0 *)
                  val fls = lt_irrefl_g ZeroC hlt0
              in Thm.implies_intr (ctermGR (jT (oeq k ZeroC)))
                   (Thm.implies_elim (oFalse_elim_r (lt ZeroC k)) fls) end
            val PkSuc = Abs("q", natT, oeq k (suc (Bound 0)))
            val caseKS =
              let val hs = Thm.assume (ctermGR (jT (mkEx PkSuc)))
                  fun bodyKS q (hq : thm) =   (* hq : oeq k (Suc q) *)
                    let (* lt 0 (Suc q) = le (Suc 0)(Suc q): witness q, oeq (Suc q)(add (Suc 0) q) *)
                        val a1 = addSuc_d (ZeroC, q)        (* (Suc 0)+q = Suc(0+q) *)
                        val a2 = add0_d q                    (* 0+q = q *)
                        val a2s= Suc_cong_r a2               (* Suc(0+q) = Suc q *)
                        val a1c= oeqTrans_r2 (a1, a2s)       (* (Suc 0)+q = Suc q *)
                        val a1cs=oeqSym_r2 a1c               (* Suc q = (Suc 0)+q *)
                        (* oeq k ((Suc 0)+q) via hq then a1cs *)
                        val keq = oeqTrans_r2 (hq, a1cs)     (* k = (Suc 0)+q *)
                        val le1k= le_intro_d (suc ZeroC, k, q) keq   (* le (Suc 0) k = lt 0 k *)
                    in le1k end
              in Thm.implies_intr (ctermGR (jT (mkEx PkSuc)))
                   (exE_r (PkSuc, lt ZeroC k) hs "q_lt0k" natT bodyKS) end
          in disjE_r (oeq k ZeroC, mkEx PkSuc, lt ZeroC k) dzk caseK0 caseKS end

        (* ---- (2) lt k p :  classical; if ~lt k p then le p k, mult_le_mono gives
                  le (p*p)(p*k)=le (p*p) N (rewrite), contra lt N (p*p). ---- *)
        val ltkp =
          let
            val emkp = em_r (lt k pF)   (* Disj (lt k p)(neg(lt k p)) *)
            val caseYes =
              let val hy = Thm.assume (ctermGR (jT (lt k pF)))
              in Thm.implies_intr (ctermGR (jT (lt k pF))) hy end
            val caseNo =
              let val hn = Thm.assume (ctermGR (jT (neg (lt k pF))))   (* ~(lt k p) *)
                  val lepk = nlt_le_gr (k, pF) hn       (* le p k *)
                  val lemm = mult_le_mono_gr (pF, pF, k) lepk   (* le (p*p)(p*k) *)
                  (* rewrite p*k -> N via hk: oeq N (p*k) => oeq (p*k) N *)
                  val hk_s = oeqSym_r2 hk               (* (p*k) = N *)
                  val zPK = Free("zPK", natT)
                  val Plepp = Term.lambda zPK (le (mult pF pF) zPK)
                  val lePPn = oeq_rw_r (Plepp, mult pF k, nF) hk_s lemm   (* le (p*p) N *)
                  (* lt N (p*p) = le (Suc N)(p*p); le (Suc N)(p*p) and le (p*p) N => le (Suc N) N => lt N N => oFalse *)
                  val leSnN = le_trans_d (suc nF, mult pF pF, nF) hlt lePPn  (* le (Suc N) N = lt N N *)
                  val fls   = lt_irrefl_g nF leSnN
              in Thm.implies_intr (ctermGR (jT (neg (lt k pF))))
                   (Thm.implies_elim (oFalse_elim_r (lt k pF)) fls) end
          in disjE_r (lt k pF, neg (lt k pF), lt k pF) emkp caseYes caseNo end

        (* ---- (3) four_sq (k*p) :  four_sq N, oeq N (mult k p) [comm], rewrite. ---- *)
        val fsqkp =
          let
            val pk_kp = mult_comm_gr (pF, k)    (* oeq (p*k)(k*p) *)
            val nEqkp = oeqTrans_r2 (hk, pk_kp) (* oeq N (k*p) *)
            val zfs = Free("zfs", natT)
            val Pfs = Term.lambda zfs (four_sq zfs)
            val r   = oeq_rw_r (Pfs, nF, mult k pF) nEqkp hfsq   (* four_sq (k*p) *)
          in r end

        (* ---- assemble the conjunction at m := k, then exI ---- *)
        val conj = conjI_r (lt ZeroC k, mkConj (lt k pF) (four_sq (mult k pF)))
                     lt0k
                     (conjI_r (lt k pF, four_sq (mult k pF)) ltkp fsqkp)
        val exC  = exI_r goalPred k conj
      in exC end

    val mainEx = exE_r (dvdBody, goalC) hdvd "k_pm" natT afterK
  in Thm.implies_intr (ctermGR hdvdP)
       (Thm.implies_intr (ctermGR hposP)
         (Thm.implies_intr (ctermGR hltP)
           (Thm.implies_intr (ctermGR hfsqP) mainEx))) end;

val () = out ("pm_bridge hyps="^Int.toString (length (Thm.hyps_of pm_bridge))^"\n");
val () = out ("pm_bridge prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of pm_bridge)^"\n");

(* aconv against intended *)
val pm_bridge_intended =
  let
    val pV = Free("p_pm", natT); val nV = Free("N_pm", natT)
    val mB = Free("m_pm", natT)
    val concl = mkEx (Term.lambda mB
                  (mkConj (lt ZeroC mB) (mkConj (lt mB pV) (four_sq (mult mB pV)))))
  in Logic.mk_implies (jT (dvd pV nV),
       Logic.mk_implies (jT (lt ZeroC nV),
         Logic.mk_implies (jT (lt nV (mult pV pV)),
           Logic.mk_implies (jT (four_sq nV), jT concl))))
  end;
val pm_aconv = ((Thm.prop_of pm_bridge) aconv pm_bridge_intended);
val pm_0hyp  = (length (Thm.hyps_of pm_bridge) = 0);
val () = out ("L4_BRIDGE_VALIDATE aconv="^Bool.toString pm_aconv^" zero_hyp="^Bool.toString pm_0hyp^"\n");
val () = if pm_aconv andalso pm_0hyp then out "L4_BRIDGE_OK\n" else out "L4_BRIDGE_FAILED\n";

(* ============================================================================
   cong_zero_imp_dvd : cong p X 0 ==> lt Zero X ==> dvd p X
     cong p X 0 = Disj (congL p X 0) (congR p X 0).
       congL : Ex k. oeq 0 (add X (p*k))  -> X = 0 (add_eq_zero_left) contra 0<X.
       congR : Ex k. oeq X (add 0 (p*k))  -> X = 0 + p*k = p*k  -> dvd p X (witness k).
   The pigeonhole front-end of PART B yields cong p (a^2+b^2+1) 0; this converts
   it to dvd p (a^2+b^2+1) so pm_bridge can package the multiple.
   ============================================================================ *)
val () = out "L4_CONGDVD_BEGIN\n";

(* dvd intro on ctxtGR : from oeq X (mult p w) build dvd p X (witness w). *)
fun dvd_intro_d (aT, bT, w) hyp =   (* hyp : oeq bT (mult aT w) ; result : dvd aT bT *)
  let val Pabs = Abs("k", natT, oeq bT (mult aT (Bound 0)))
  in exI_r Pabs w hyp end;

val cong_zero_imp_dvd =
  let
    val pF = Free("p_cz", natT)
    val xF = Free("X_cz", natT)
    val hcongP = jT (cong pF xF ZeroC); val hcong = Thm.assume (ctermGR hcongP)
    val hposP  = jT (lt ZeroC xF);      val hpos  = Thm.assume (ctermGR hposP)
    val goalC  = dvd pF xF

    (* congL : Ex k. oeq 0 (add X (p*k)) *)
    val congLbody = Abs("k", natT, oeq ZeroC (add xF (mult pF (Bound 0))))
    val caseL =
      let val hL = Thm.assume (ctermGR (jT (congL pF xF ZeroC)))
          fun bodyL k (hk:thm) =   (* hk : oeq 0 (add X (p*k)) *)
            let val hk_s = oeqSym_r2 hk                          (* add X (p*k) = 0 *)
                val xZero= add_eq_zero_left_d (xF, mult pF k) hk_s  (* X = 0 *)
                val zX = Free("zCZL", natT)
                val Plt= Term.lambda zX (lt ZeroC zX)
                val hlt0=oeq_rw_r (Plt, xF, ZeroC) xZero hpos     (* lt 0 0 *)
                val fls= lt_irrefl_g ZeroC hlt0
            in Thm.implies_elim (oFalse_elim_r goalC) fls end
      in Thm.implies_intr (ctermGR (jT (congL pF xF ZeroC)))
           (exE_r (congLbody, goalC) hL "kL_cz" natT bodyL) end

    (* congR : Ex k. oeq X (add 0 (p*k)) *)
    val congRbody = Abs("k", natT, oeq xF (add ZeroC (mult pF (Bound 0))))
    val caseR =
      let val hR = Thm.assume (ctermGR (jT (congR pF xF ZeroC)))
          fun bodyR k (hk:thm) =   (* hk : oeq X (add 0 (p*k)) *)
            let val a0pk = add0_d (mult pF k)         (* 0 + p*k = p*k *)
                val xEqpk= oeqTrans_r2 (hk, a0pk)     (* X = p*k *)
                val dvdT = dvd_intro_d (pF, xF, k) xEqpk   (* dvd p X *)
            in dvdT end
      in Thm.implies_intr (ctermGR (jT (congR pF xF ZeroC)))
           (exE_r (congRbody, goalC) hR "kR_cz" natT bodyR) end

    val resThm = disjE_r (congL pF xF ZeroC, congR pF xF ZeroC, goalC) hcong caseL caseR
    val disch  = Thm.implies_intr (ctermGR hcongP) (Thm.implies_intr (ctermGR hposP) resThm)
  in disch end;   (* keep Free-form; varify a separate copy below for reuse *)

val cong_zero_imp_dvd_v = varify cong_zero_imp_dvd;   (* schematic copy for instantiation *)

val () = out ("cong_zero_imp_dvd hyps="^Int.toString (length (Thm.hyps_of cong_zero_imp_dvd))^"\n");
val () = out ("cong_zero_imp_dvd prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of cong_zero_imp_dvd)^"\n");

(* aconv intended (compare the Free-form lemma against the Free-form intended) *)
val cong_zero_imp_dvd_intended =
  let val pV = Free("p_cz", natT); val xV = Free("X_cz", natT)
  in Logic.mk_implies (jT (cong pV xV ZeroC),
       Logic.mk_implies (jT (lt ZeroC xV), jT (dvd pV xV))) end;
val cz_aconv = ((Thm.prop_of cong_zero_imp_dvd) aconv cong_zero_imp_dvd_intended);
val cz_0hyp  = (length (Thm.hyps_of cong_zero_imp_dvd) = 0);
val () = out ("L4_CONGDVD_VALIDATE aconv="^Bool.toString cz_aconv^" zero_hyp="^Bool.toString cz_0hyp^"\n");

(* soundness probe : must NOT be the unconditional dvd (drop a premise) *)
val cz_probe = not ((Thm.prop_of cong_zero_imp_dvd) aconv
  (jT (dvd (Free("p_cz",natT)) (Free("X_cz",natT)))));
val () = out ("L4_CONGDVD_PROBE conditional="^Bool.toString cz_probe^"\n");
val () = if cz_aconv andalso cz_0hyp andalso cz_probe then out "L4_CONGDVD_OK\n" else out "L4_CONGDVD_FAILED\n";

(* ============================================================================
   pm_from_cong : compose cong_zero_imp_dvd + pm_bridge.
     cong p N 0 ==> lt Zero N ==> lt N (mult p p) ==> four_sq N
       ==> EX m. lt Zero m /\ lt m p /\ four_sq (mult m p)
   This is the exact "residue collision -> prime multiple package" the PART B
   pigeonhole front-end (cong p (a^2+b^2+1) 0 with 0<a^2+b^2+1<p^2 and a four_sq
   witness a^2+b^2+1^2+0^2) feeds into to conclude PART B's existential.
   ============================================================================ *)
val () = out "L4_COMPOSE_BEGIN\n";

val cong_zero_imp_dvd_vGR = cong_zero_imp_dvd_v;   (* already schematic *)
val pm_bridge_vGR         = varify pm_bridge;

val pm_from_cong =
  let
    val pF = Free("p_pf", natT)
    val nF = Free("N_pf", natT)
    val hcongP = jT (cong pF nF ZeroC); val hcong = Thm.assume (ctermGR hcongP)
    val hposP  = jT (lt ZeroC nF);      val hpos  = Thm.assume (ctermGR hposP)
    val hltP   = jT (lt nF (mult pF pF)); val hlt  = Thm.assume (ctermGR hltP)
    val hfsqP  = jT (four_sq nF);       val hfsq  = Thm.assume (ctermGR hfsqP)

    (* dvd p N *)
    val czInst = beta_norm (Drule.infer_instantiate ctxtGR
                   [(("p_cz",0), ctermGR pF),(("X_cz",0), ctermGR nF)] cong_zero_imp_dvd_vGR)
    val hdvd = Thm.implies_elim (Thm.implies_elim czInst hcong) hpos   (* dvd p N *)

    (* pm_bridge p N *)
    val pmInst = beta_norm (Drule.infer_instantiate ctxtGR
                   [(("p_pm",0), ctermGR pF),(("N_pm",0), ctermGR nF)] pm_bridge_vGR)
    val res = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim
                (Thm.implies_elim pmInst hdvd) hpos) hlt) hfsq
  in Thm.implies_intr (ctermGR hcongP)
       (Thm.implies_intr (ctermGR hposP)
         (Thm.implies_intr (ctermGR hltP)
           (Thm.implies_intr (ctermGR hfsqP) res))) end;

val () = out ("pm_from_cong hyps="^Int.toString (length (Thm.hyps_of pm_from_cong))^"\n");
val () = out ("pm_from_cong prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of pm_from_cong)^"\n");

val pm_from_cong_intended =
  let
    val pV = Free("p_pf", natT); val nV = Free("N_pf", natT); val mB = Free("m_pf", natT)
    val concl = mkEx (Term.lambda mB
                  (mkConj (lt ZeroC mB) (mkConj (lt mB pV) (four_sq (mult mB pV)))))
  in Logic.mk_implies (jT (cong pV nV ZeroC),
       Logic.mk_implies (jT (lt ZeroC nV),
         Logic.mk_implies (jT (lt nV (mult pV pV)),
           Logic.mk_implies (jT (four_sq nV), jT concl)))) end;
val pf_aconv = ((Thm.prop_of pm_from_cong) aconv pm_from_cong_intended);
val pf_0hyp  = (length (Thm.hyps_of pm_from_cong) = 0);
val () = out ("L4_COMPOSE_VALIDATE aconv="^Bool.toString pf_aconv^" zero_hyp="^Bool.toString pf_0hyp^"\n");
val () = if pf_aconv andalso pf_0hyp then out "L4_COMPOSE_OK\n" else out "L4_COMPOSE_FAILED\n";

(* ============================================================================
   PART B SUMMARY (honest):
     PROVEN + VERIFIED (0-hyp, aconv-checked, on ctxtGR/thyGR):
       pm_bridge          : dvd p N ==> 0<N ==> N<p^2 ==> four_sq N
                              ==> EX m. 0<m /\ m<p /\ four_sq (m*p)
       cong_zero_imp_dvd  : cong p X 0 ==> 0<X ==> dvd p X
       pm_from_cong       : cong p N 0 ==> 0<N ==> N<p^2 ==> four_sq N
                              ==> EX m. 0<m /\ m<p /\ four_sq (m*p)
     These are the complete BACK-END + INTERFACE of PART B: they turn the
     pigeonhole's output (a residue collision a^2+b^2+1 = 0 (mod p), with the
     four_sq witness a^2+b^2+1^2+0^2 and bounds 0<a^2+b^2+1<p^2) into PART B's
     existential.  The pigeonhole FRONT-END (producing the collision for an odd
     prime via two residue sets of size (p+1)/2) is NOT yet built here.
   ============================================================================ *)
val () = out "L4_PRIMEMULT_BACKEND_OK\n";
