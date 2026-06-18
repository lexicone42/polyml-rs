(* ============================================================================
   PART B FRONT-END (the residue-set pigeonhole) — delta appended AFTER the
   runnable base (base.sml + partA + assembly + partB + partC, OR the lean
   base.sml + partB_backend_delta.sml which carries pm_from_cong).

   PROVES (each 0-hyp, aconv intended, soundness-probed; markers at the end):
     pigeon_thm    : prime2 p ==> oeq p (Suc(m+m))
                       ==> EX a b. (le a m /\ le b m)
                                /\ cong p (a*a + b*b + Suc Zero) Zero       [L4_PIGEON_OK]
     primemult_thm : prime2 p ==> oeq p (Suc(m+m))
                       ==> EX m'. lt 0 m' /\ lt m' p /\ four_sq (m'*p)       [L4_PRIMEMULT_OK]

   "p = Suc(m+m)" is the ODD-prime encoding (p = 2m+1).  The pigeonhole uses two
   residue sets {a^2 mod p} and {(p-1)-b^2 mod p} of size (p+1)/2 each, total
   p+1 > p, so they collide.  Same-set collisions are excluded by sq_inj_mod
   (squares are injective mod p on [0,m] via Euclid's lemma); the cross collision
   gives a^2+b^2+1 == 0 (mod p).  Compose with the PROVEN pm_from_cong (witness
   four_sq N = a^2+b^2+1^2+0^2, bound N < p^2 from a,b<=m).
   ============================================================================ *)
val () = out "L4_PARTB_DELTA_BEGIN\n";


(* ============================================================================
   PART B FRONT-END (residue-set pigeonhole) -- TEST 1: instantiators + helpers
   on ctxtGR / thyGR (the final context).
   ============================================================================ *)
val () = out "PB_T1_BEGIN\n";

(* ---- varify base lemmas onto GR + build GR instantiators ---- *)
val euclid_lemma_vGR        = varify euclid_lemma;          (* prime2 p ==> dvd p (a*b) ==> dvd p a \/ dvd p b *)
val dvd_diff_vGR            = varify dvd_diff;              (* dvd p x ==> dvd p (x+y) ==> dvd p y *)
val prime_not_dvd_pos_lt_vGR= varify prime_not_dvd_pos_lt; (* dvd p r ==> 0<r ==> r<p ==> oFalse *)
val dvd_le_vGR             = varify dvd_le;                (* dvd d n ==> (n=0 ==> oFalse) ==> le d n *)
val sub_recover_vGR        = varify sub_recover_ax;        (* le j s ==> (s-j)+j = s *)

fun euclid_lemma_gr (pT,aT,bT) hpr hdvd =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
    [(("p",0), ctermGR pT),(("a",0), ctermGR aT),(("b",0), ctermGR bT)] euclid_lemma_vGR)) hpr) hdvd;

fun dvd_diff_gr (pT,xT,yT) hx hxy =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
    [(("p",0), ctermGR pT),(("x",0), ctermGR xT),(("y",0), ctermGR yT)] dvd_diff_vGR)) hx) hxy;

fun prime_not_dvd_pos_lt_gr (pT,rT) hdvd hpos hlt =
  Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
    [(("p",0), ctermGR pT),(("r",0), ctermGR rT)] prime_not_dvd_pos_lt_vGR)) hdvd) hpos) hlt;

(* dvd_le_gr : dvd d n ==> (meta: n=0 ==> oFalse) ==> le d n *)
fun dvd_le_gr (dT,nT) hdvd hnzMeta =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("d",0), ctermGR dT),(("n",0), ctermGR nT)] dvd_le_vGR)
  in Thm.implies_elim (Thm.implies_elim inst hdvd) hnzMeta end;

fun sub_recover_gr (sT,jT_) hle =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtGR
    [(("s_sub",0), ctermGR sT),(("j_sub",0), ctermGR jT_)] sub_recover_vGR)) hle;

val () = out "PB_T1_INSTANTIATORS_OK\n";

(* ---- dvd intro on GR: from oeq b (mult a w) build dvd a b (witness w). ---- *)
fun dvd_intro_gr (aT, bT, w) hyp =
  let val Pabs = Abs("k", natT, oeq bT (mult aT (Bound 0)))
  in exI_r Pabs w hyp end;

(* ---- dvd_elim_gr : dvd a b ==> (meta: !!w. oeq b (mult a w) ==> R) ==> R ---- *)
fun dvd_elim_gr (aT, bT, goalC) hdvd bodyFn =
  let val Pabs = Abs("k", natT, oeq bT (mult aT (Bound 0)))
  in exE_r (Pabs, goalC) hdvd "w_dvd" natT bodyFn end;

val () = out "PB_T1_DVD_HELPERS_OK\n";

(* quick smoke: dvd a (a*0)?  build dvd a 0 via witness 0: oeq 0 (a*0). *)
val () =
  let val aP = Free("a_t1", natT)
      val z0 = mult0r_g aP                              (* oeq (a*0) 0 *)
      val z0s = oeqSym_r2 z0                            (* oeq 0 (a*0) *)
      val d   = dvd_intro_gr (aP, ZeroC, ZeroC) z0s     (* dvd a 0 *)
  in out ("PB_T1_SMOKE dvd_intro hyps="^Int.toString(length(Thm.hyps_of d))^"\n") end
  handle e => out ("PB_T1_SMOKE FAIL "^exnMessage e^"\n");

val () = out "PB_T1_DONE\n";

(* ============================================================================
   PART B TEST 2: cong_eq_sum_imp_dvd + square-sum factoring + prime-small-zero
   + the DISTINCTNESS crux sq_inj_mod.
   Uses ctxtGR helpers (_r / _d / _g) + the test-1 instantiators.
   ============================================================================ *)
val () = out "PB_T2_BEGIN\n";

(* cong p X Y = Disj (Ex k. Y = X + p*k)(Ex k. X = Y + p*k). *)

(* ---- cong_eq_sum_imp_dvd : cong p X Y ==> oeq X (add Y D) ==> dvd p D ----
   right disjunct: X = Y + p*k ; with X = Y + D => Y+D = Y+p*k => D = p*k => dvd p D.
   left  disjunct: Y = X + p*k = (Y+D)+p*k = Y+(D+p*k) => 0 = D + p*k (cancel Y)
                   => D = 0 => dvd p 0 = dvd p D. *)
fun cong_eq_sum_imp_dvd (pT, xT, yT, dT) hcong hXeq =
  let
    val goalC = dvd pT dT
    val LbodyAbs = Abs("k", natT, oeq yT (add xT (mult pT (Bound 0))))   (* congL p X Y *)
    val RbodyAbs = Abs("k", natT, oeq xT (add yT (mult pT (Bound 0))))   (* congR p X Y *)
    val caseL =
      let val hL = Thm.assume (ctermGR (jT (congL pT xT yT)))
          fun bodyL k (hk:thm) =   (* hk : oeq Y (add X (p*k)) *)
            let (* X = Y + D ; Y = X + p*k => Y = (Y+D)+p*k = Y + (D + p*k) *)
                val xsub = oeq_rw_r (Term.lambda (Free("zL",natT)) (oeq yT (add (Free("zL",natT)) (mult pT k))),
                                     xT, add yT dT) hXeq hk    (* Y = (Y+D) + p*k *)
                val reassoc = addassoc_d (yT, dT, mult pT k)   (* (Y+D)+p*k = Y + (D + p*k) *)
                val yEq = oeqTrans_r2 (xsub, reassoc)          (* Y = Y + (D + p*k) *)
                (* Y = Y + 0 ; cancel: 0 = D + p*k => D = 0 *)
                val y0 = add0r_g yT                            (* Y + 0 = Y *)
                val yY0 = oeqSym_r2 y0                         (* Y = Y + 0 *)
                val canEq = oeqTrans_r2 (oeqSym_r2 yY0, yEq)   (* (Y+0) = Y + (D+p*k) *)
                val zeroEq = add_left_cancel_g (yT, ZeroC, add dT (mult pT k)) canEq  (* 0 = D + p*k *)
                val sumZero = oeqSym_r2 zeroEq                 (* D + p*k = 0 *)
                val dZero = add_eq_zero_left_d (dT, mult pT k) sumZero  (* D = 0 *)
                (* dvd p D : dvd p 0 then rewrite 0 -> D *)
                val p0 = mult0r_g pT                           (* p*0 = 0 *)
                val p0s = oeqSym_r2 p0                         (* 0 = p*0 *)
                val dvd0 = dvd_intro_gr (pT, ZeroC, ZeroC) p0s (* dvd p 0 *)
                val dZeroS = oeqSym_r2 dZero                   (* 0 = D *)
                val res = oeq_rw_r (Term.lambda (Free("zD",natT)) (dvd pT (Free("zD",natT))), ZeroC, dT) dZeroS dvd0
            in res end
      in Thm.implies_intr (ctermGR (jT (congL pT xT yT)))
           (exE_r (LbodyAbs, goalC) hL "kL_cs" natT bodyL) end
    val caseR =
      let val hR = Thm.assume (ctermGR (jT (congR pT xT yT)))
          fun bodyR k (hk:thm) =   (* hk : oeq X (add Y (p*k)) *)
            let (* X = Y + D and X = Y + p*k => Y + D = Y + p*k => D = p*k *)
                val mid = oeqTrans_r2 (oeqSym_r2 hXeq, hk)   (* (Y+D) = (Y+p*k) *)
                val dpk = add_left_cancel_g (yT, dT, mult pT k) mid  (* D = p*k *)
                val dvdT = dvd_intro_gr (pT, dT, k) dpk      (* dvd p D *)
            in dvdT end
      in Thm.implies_intr (ctermGR (jT (congR pT xT yT)))
           (exE_r (RbodyAbs, goalC) hR "kR_cs" natT bodyR) end
  in disjE_r (congL pT xT yT, congR pT xT yT, goalC) hcong caseL caseR end;

val () = out "PB_T2_CONGSUMDVD_OK\n";

(* ---- sq_sum_factor : oeq a (add a' e) ==> oeq (mult a a) (add (mult a' a')(mult e (add a a'))).
   With a = a'+e: a*a = (a'+e)*a. RHS = a'^2 + e*(a+a').
   Proof:  a*a = (a'+e)*a [rw left a]
              = a'*a + e*a  [right_distrib? need (a'+e)*a = a'*a + e*a]
         and a+a' : e*(a+a') = e*a + e*a' (left_distrib).
         RHS = a'*a' + (e*a + e*a').
         a'*a = a'*(a'+e) = a'*a' + a'*e (left_distrib).
         So a'*a + e*a = (a'*a'+a'*e) + e*a.
         Want = a'*a' + (e*a + e*a').  Note a'*e = e*a' (comm).
         (a'*a' + e*a') + e*a = a'*a' + (e*a' + e*a) = a'*a' + (e*a + e*a') [comm].  OK. ---- *)
fun sq_sum_factor (aT, a'T, eT) (haeq:thm) =  (* haeq : oeq a (add a' e) *)
  let
    (* a*a = (a'+e)*a *)
    val step1 = mult_cong_l_g (aT, add a'T eT, aT) haeq            (* a*a = (a'+e)*a *)
    (* (a'+e)*a = a'*a + e*a  [right_distrib (m+n)*k = m*k + n*k] *)
    val rd1 = rightdistrib_g (a'T, eT, aT)                          (* (a'+e)*a = a'*a + e*a *)
    val laa = oeqTrans_g (step1, rd1)                              (* a*a = a'*a + e*a *)
    (* a'*a = a'*(a'+e) [rw second a] = a'*a' + a'*e *)
    val aa'eq = mult_cong_r_g (a'T, aT, add a'T eT) haeq           (* a'*a = a'*(a'+e) *)
    val ld_a' = leftdistrib_g (a'T, a'T, eT)                        (* a'*(a'+e) = a'*a' + a'*e *)
    val a'a_eq = oeqTrans_g (aa'eq, ld_a')                          (* a'*a = a'*a' + a'*e *)
    (* substitute a'*a in laa : a*a = (a'*a' + a'*e) + e*a *)
    val laa2 = oeq_rw_g (Term.lambda (Free("zf1",natT)) (oeq (mult aT aT) (add (Free("zf1",natT)) (mult eT aT))),
                          mult a'T aT, add (mult a'T a'T) (mult a'T eT)) a'a_eq laa
                                                                    (* a*a = (a'*a'+a'*e)+e*a *)
    (* reassoc: (a'*a'+a'*e)+e*a = a'*a' + (a'*e + e*a) *)
    val reass = addassoc_g (mult a'T a'T, mult a'T eT, mult eT aT)  (* = a'*a' + (a'*e + e*a) *)
    val laa3 = oeqTrans_g (laa2, reass)                            (* a*a = a'*a' + (a'*e + e*a) *)
    (* target RHS = a'*a' + e*(a+a') ; e*(a+a') = e*a + e*a' (left_distrib) *)
    val ld_e = leftdistrib_g (eT, aT, a'T)                          (* e*(a+a') = e*a + e*a' *)
    (* show (a'*e + e*a) = (e*a + e*a') :
         a'*e = e*a' (comm), so a'*e + e*a = e*a' + e*a = e*a + e*a' (comm). *)
    val ae_comm = multcomm_g (a'T, eT)                             (* a'*e = e*a' *)
    val inner1 = add_cong_l_g (mult a'T eT, mult eT a'T, mult eT aT) ae_comm  (* a'*e + e*a = e*a' + e*a *)
    val inner2 = addcomm_g (mult eT a'T, mult eT aT)               (* e*a' + e*a = e*a + e*a' *)
    val innerEq = oeqTrans_g (inner1, inner2)                      (* a'*e + e*a = e*a + e*a' *)
    val rhs_eq = oeqSym_g (oeqTrans_g (ld_e, oeqSym_g innerEq))    (* (a'*e + e*a) = e*(a+a') *)
    (* a*a = a'*a' + (a'*e + e*a) = a'*a' + e*(a+a') *)
    val laa4 = oeq_rw_g (Term.lambda (Free("zf2",natT)) (oeq (mult aT aT) (add (mult a'T a'T) (Free("zf2",natT)))),
                          add (mult a'T eT) (mult eT aT), mult eT (add aT a'T)) rhs_eq laa3
  in laa4 end;  (* oeq (a*a) (a'*a' + e*(a+a')) *)

val () = out "PB_T2_SQFACTOR_OK\n";

(* smoke sq_sum_factor : a=2,a'=1,e=1 (2 = 1+1) -- structural check only *)
val () =
  let val a' = oneC; val e = oneC; val a = add a' e   (* a = 1+1 *)
      val haeq = oeqRefl_r2 a                          (* oeq (1+1) (1+1) -- a := add a' e literally *)
      val r = sq_sum_factor (a, a', e) haeq
  in out ("PB_T2_SQFACTOR_SMOKE hyps="^Int.toString(length(Thm.hyps_of r))^"\n") end
  handle ex => out ("PB_T2_SQFACTOR_SMOKE FAIL "^exnMessage ex^"\n");

val () = out "PB_T2_DONE\n";

(* ============================================================================
   PART B TEST 3: prime_dvd_lt_imp_zero + the DISTINCTNESS crux sq_inj_mod.
   ============================================================================ *)
val () = out "PB_T3_BEGIN\n";

(* ---- prime_dvd_lt_imp_zero : prime2 p ==> dvd p e ==> lt e p ==> oeq e Zero ---- *)
fun prime_dvd_lt_imp_zero (pT, eT) hpr hdvd hlt =
  let
    val goalC = oeq eT ZeroC
    val dze = dzos_d eT
    val caseZ =
      let val h0 = Thm.assume (ctermGR (jT (oeq eT ZeroC)))
      in Thm.implies_intr (ctermGR (jT (oeq eT ZeroC))) h0 end
    val PqSuc = Abs("q", natT, oeq eT (suc (Bound 0)))
    val caseS =
      let val hs = Thm.assume (ctermGR (jT (mkEx PqSuc)))
          fun bodyS q (hq:thm) =
            let val a1 = addSuc_d (ZeroC, q)
                val a2 = add0_d q
                val a2s= Suc_cong_r a2
                val a1c= oeqTrans_r2 (a1, a2s)
                val keq= oeqTrans_r2 (hq, oeqSym_r2 a1c)
                val pose = le_intro_d (suc ZeroC, eT, q) keq
                val fls = prime_not_dvd_pos_lt_gr (pT, eT) hdvd pose hlt
            in Thm.implies_elim (oFalse_elim_r goalC) fls end
      in Thm.implies_intr (ctermGR (jT (mkEx PqSuc)))
           (exE_r (PqSuc, goalC) hs "q_pdz" natT bodyS) end
  in disjE_r (oeq eT ZeroC, mkEx PqSuc, goalC) dze caseZ caseS end;

val () = out "PB_T3_PDZ_OK\n";

(* ---- sum_zero_imp_eq : oeq (add a a') Zero ==> oeq a a' ---- *)
fun sum_zero_imp_eq (aT, a'T) hsumZero =
  let val aZ  = add_eq_zero_left_d (aT, a'T) hsumZero
      val sumC = oeqTrans_r2 (oeqSym_r2 (addcomm_d (aT, a'T)), hsumZero)
      val a'Z = add_eq_zero_left_d (a'T, aT) sumC
  in oeqTrans_r2 (aZ, oeqSym_r2 a'Z) end;

(* ---- ltp_imp_zero : lt s p ==> dvd p s ==> oeq s Zero (s NOT necessarily prime arg)
   uses dvd p s, lt s p, prime2 p.  Same as prime_dvd_lt_imp_zero. ---- *)

(* ---- sq_inj_mod : prime2 p ==> lt (add a a') p ==> cong p (a*a)(a'*a') ==> oeq a a' ---- *)
fun sq_inj_mod (pT, aT, a'T) hpr hltsum hcong =
  let
    val goalC = oeq aT a'T
    val dlt = le_total_d (aT, a'T)   (* Disj (le a a')(le a' a) *)
    (* CORE: returns oeq HI LO given hle: le LO HI, hcLH: cong p (HI*HI)(LO*LO),
             hHIle: le HI (a+a'), hsumEq: oeq (HI+LO)(a+a'). *)
    fun core (hiT, loT) hle hcLH hHIle hsumEq =
      let
        val leBody = Abs("e", natT, oeq hiT (add loT (Bound 0)))
        fun afterE e (heq:thm) =   (* heq : oeq HI (LO + e) *)
          let
            val fac = sq_sum_factor (hiT, loT, e) heq
            val dvdProd = cong_eq_sum_imp_dvd (pT, mult hiT hiT, mult loT loT, mult e (add hiT loT)) hcLH fac
            val eucl = euclid_lemma_gr (pT, e, add hiT loT) hpr dvdProd
            (* le e HI ; le e (a+a') ; lt e p *)
            val heqc = oeqTrans_r2 (heq, addcomm_d (loT, e))   (* HI = e + LO *)
            val leEHI = le_intro_d (e, hiT, loT) heqc
            val leEsum = le_trans_d (e, hiT, add aT a'T) leEHI hHIle
            val leSeS = le_suc_mono_g (e, add aT a'T) leEsum
            val ltEp  = le_trans_d (suc e, suc (add aT a'T), pT) leSeS hltsum
            (* CASE dvd p e *)
            val caseDE =
              let val hde = Thm.assume (ctermGR (jT (dvd pT e)))
                  val e0 = prime_dvd_lt_imp_zero (pT, e) hpr hde ltEp
                  val rwE = oeq_rw_r (Term.lambda (Free("ze1",natT)) (oeq hiT (add loT (Free("ze1",natT)))),
                                       e, ZeroC) e0 heq
                  val lo0 = add0r_g loT
                  val hiLo= oeqTrans_r2 (rwE, lo0)             (* HI = LO *)
              in Thm.implies_intr (ctermGR (jT (dvd pT e))) hiLo end
            (* CASE dvd p (HI+LO) : rewrite to dvd p (a+a'), lt (a+a') p => a+a'=0 => HI=LO via both 0 *)
            val caseDS =
              let val hds = Thm.assume (ctermGR (jT (dvd pT (add hiT loT))))
                  val hdsum = oeq_rw_r (Term.lambda (Free("zs1",natT)) (dvd pT (Free("zs1",natT))),
                                         add hiT loT, add aT a'T) hsumEq hds   (* dvd p (a+a') *)
                  val sumZ = prime_dvd_lt_imp_zero (pT, add aT a'T) hpr hdsum hltsum   (* a+a' = 0 *)
                  (* a+a'=0 => HI+LO=0 (sumEq sym) => HI=0 /\ LO=0 => HI=LO *)
                  val hilo0 = oeqTrans_r2 (hsumEq, sumZ)        (* HI+LO = 0 *)
                  val hiLo = sum_zero_imp_eq (hiT, loT) hilo0   (* HI = LO *)
              in Thm.implies_intr (ctermGR (jT (dvd pT (add hiT loT)))) hiLo end
          in disjE_r (dvd pT e, dvd pT (add hiT loT), oeq hiT loT) eucl caseDE caseDS end
      in exE_r (leBody, oeq hiT loT) hle "e_sij" natT afterE end
    (* CASE le a a' : HI=a', LO=a.  need cong p (a'*a')(a*a) [sym of hcong];
         le a' (a+a') ; sumEq: (a'+a)=(a+a') [comm].  result oeq a' a -> oeq a a' (sym). *)
    val caseLE1 =
      let val hle = Thm.assume (ctermGR (jT (le aT a'T)))     (* le a a' *)
          val hcLH = cong_sym_g (pT, mult aT aT, mult a'T a'T) hcong   (* cong p (a'*a')(a*a) *)
          val leHI = le_add_g (a'T, aT)                        (* le a' (a'+a) *)
          (* need le a' (a+a') : rewrite (a'+a)->(a+a') in le a' _ *)
          val comm1 = addcomm_d (a'T, aT)                      (* (a'+a) = (a+a') *)
          val leHI2 = oeq_rw_r (Term.lambda (Free("zh1",natT)) (le a'T (Free("zh1",natT))),
                                 add a'T aT, add aT a'T) comm1 leHI   (* le a' (a+a') *)
          val sumEq = addcomm_d (a'T, aT)                      (* (a'+a) = (a+a') *)
          val hiLo = core (a'T, aT) hle hcLH leHI2 sumEq       (* oeq a' a *)
          val res  = oeqSym_r2 hiLo                            (* oeq a a' *)
      in Thm.implies_intr (ctermGR (jT (le aT a'T))) res end
    (* CASE le a' a : HI=a, LO=a'.  hcong already cong p (a*a)(a'*a').
         le a (a+a') ; sumEq: (a+a')=(a+a') refl.  result oeq a a'. *)
    val caseLE2 =
      let val hle = Thm.assume (ctermGR (jT (le a'T aT)))     (* le a' a *)
          val leHI = le_add_g (aT, a'T)                        (* le a (a+a') *)
          val sumEq = oeqRefl_r2 (add aT a'T)                  (* (a+a') = (a+a') *)
          val hiLo = core (aT, a'T) hle hcong leHI sumEq       (* oeq a a' *)
      in Thm.implies_intr (ctermGR (jT (le a'T aT))) hiLo end
  in disjE_r (le aT a'T, le a'T aT, goalC) dlt caseLE1 caseLE2 end;

val () = out "PB_T3_SQINJ_OK\n";

(* smoke: sq_inj_mod is a fn; can't easily 0-hyp test without prime hyp, just confirm it built. *)
val () = out "PB_T3_DONE\n";

(* ============================================================================
   PART B TEST 4: residue-list infrastructure.
   New consts fdec (index->value) + bres (residue list), 2+2 axioms, new context
   ctxtB/ctermB, re-varify the helper set, then prove (mirroring gridres):
     breslen      : oeq (llen (bres n)) n
     bresmem_lt_p : 0<p ==> !e. lmem e (bres n) ==> lt e p
     mem_bres_reflect : !e. lmem e (bres n) ==> ?c. lt c n /\ oeq e (fres c)
     dup_bres     : neg(lnodup (bres n)) ==> ?c1 c2. lt c1 n /\ lt c2 n /\ ~(c1=c2)
                                              /\ oeq (fres c1)(fres c2)
   fres/bres parametric in the value-decode fdec; fdec gets PART-B axioms in T5.
   ============================================================================ *)
val () = out "PB_T4_BEGIN\n";

(* p, m as the fixed Free parameters of PART B *)
val pB = Free("p_B", natT);
val mB = Free("m_B", natT);

(* ---- new consts: fdec : nat->nat (the index decode), bres : nat->natlist ---- *)
val thyBc = Sign.add_consts
  [(Binding.name "fdec", natT --> natT, NoSyn),
   (Binding.name "bres", natT --> natlistT, NoSyn)] thyGR;
fun cnstB nm T = Const (Sign.full_name thyBc (Binding.name nm), T);
val fdecC = cnstB "fdec" (natT --> natT);   fun fdec k = fdecC $ k;
val bresC = cnstB "bres" (natT --> natlistT); fun bres n = bresC $ n;

(* fres k = rmodv (fdec k) p_B *)
fun fres k = rmodv (fdec k) pB;

(* bres recursion axioms (mirror gridres_zero/suc) *)
val nB = Free("n_brc", natT);
val ((_,bres_zero_ax), thyB1) = Thm.add_axiom_global (Binding.name "bres_zero",
      jT (leq (bres ZeroC) lnilC)) thyBc;
val ((_,bres_suc_ax), thyB2) = Thm.add_axiom_global (Binding.name "bres_suc",
      jT (leq (bres (suc nB)) (lcons (fres nB) (bres nB)))) thyB1;

(* ---- fdec PART-B value axioms (conditional, used only in T5):
     fdecA : lt k (Suc m) ==> oeq (fdec k) (mult k k)
     fdecB : le (Suc m) k ==> oeq (fdec k) (subv (mult p p)(Suc (mult (subv k (Suc m))(subv k (Suc m))))) *)
val kB = Free("k_fd", natT);
fun bidx k = subv k (suc mB);
fun bval k = subv (mult pB pB) (suc (mult (bidx k)(bidx k)));
val ((_,fdecA_ax), thyB3) = Thm.add_axiom_global (Binding.name "fdecA",
      Logic.mk_implies (jT (lt kB (suc mB)), jT (oeq (fdec kB) (mult kB kB)))) thyB2;
val ((_,fdecB_ax), thyB) = Thm.add_axiom_global (Binding.name "fdecB",
      Logic.mk_implies (jT (le (suc mB) kB), jT (oeq (fdec kB) (bval kB)))) thyB3;

val ctxtB  = Proof_Context.init_global thyB;
val ctermB = Thm.cterm_of ctxtB;
val () = out "PB_T4_CONTEXT_READY\n";

(* ---- re-varify the helper set onto ctxtB ---- *)
val bres_zero_vB = varify bres_zero_ax;
val bres_suc_vB  = varify bres_suc_ax;
val fdecA_vB     = varify fdecA_ax;
val fdecB_vB     = varify fdecB_ax;
val rmod_lt_vB   = varify rmod_lt_ax;
val leq_subst_vB = varify leq_subst_ax;
val leq_sym_vB   = varify leq_sym;
val leq_refl_vB  = varify leq_refl_ax;
val oeq_refl_vB  = varify oeq_refl;
val oeq_sym_vB   = varify oeq_sym;
val oeq_trans_vB = varify oeq_trans;
val Suc_cong_vB  = varify Suc_cong;
val nat_induct_vB= varify nat_induct;
val llen_nil_vB  = varify llen_nil_ax;
val llen_cons_vB = varify llen_cons_ax;
val lmem_nil_elim_vB = varify lmem_nil_elim_ax;
val lmem_cons_fwd_vB = varify lmem_cons_fwd_ax;
val lmem_cons_bwd_vB = varify lmem_cons_bwd_ax;
val lnodup_cons_bwd_vB = varify lnodup_cons_bwd_ax;
val lnodup_nil_vB = varify lnodup_nil_ax;
val mp_vB        = varify mp_ax;
val impI_vB      = varify impI_ax;
val allI_vB      = varify allI_ax;
val allE_vB      = varify allE_ax;
val disjE_vB     = varify disjE_ax;
val conjI_vB     = varify conjI_ax;
val conjunct1_vB = varify conjunct1_ax;
val conjunct2_vB = varify conjunct2_ax;
val exI_vB       = varify exI_ax;
val exE_vB       = varify exE_ax;
val ex_middle_vB = varify ex_middle_ax;
val oFalse_elim_vB = varify oFalse_elim_ax;
val lt_irrefl_vB = varify lt_irrefl;
val lt_trans_vB  = varify lt_trans;
val lt_suc_vB    = varify lt_suc;

(* ---- helper functions on ctxtB (suffix _b) ---- *)
fun oeqRefl_b x = beta_norm (Drule.infer_instantiate ctxtB [(("a",0), ctermB x)] oeq_refl_vB);
fun oeqSym_b h = oeq_sym_vB OF [h];
fun oeqTrans_b (h1,h2) = oeq_trans_vB OF [h1,h2];
fun Suc_cong_b h = Suc_cong_vB OF [h];
fun leq_sym_b h = leq_sym_vB OF [h];
fun leqRefl_b l = beta_norm (Drule.infer_instantiate ctxtB [(("a",0), ctermB l)] leq_refl_vB);
fun leq_rw_b (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB [(("P",0), ctermB Pabs),(("a",0), ctermB aT),(("b",0), ctermB bT)] leq_subst_vB)
  in inst OF [hab, hPa] end;
val oeq_subst_vB = varify oeq_subst;
fun oeq_rw_b2 (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB [(("P",0), ctermB Pabs),(("a",0), ctermB aT),(("b",0), ctermB bT)] oeq_subst_vB)
  in inst OF [hab, hPa] end;
fun llenNil_b () = llen_nil_vB;
fun llenCons_b (h,t) = beta_norm (Drule.infer_instantiate ctxtB [(("x",0), ctermB h),(("t",0), ctermB t)] llen_cons_vB);
fun lmemNilElim_b x = beta_norm (Drule.infer_instantiate ctxtB [(("x",0), ctermB x)] lmem_nil_elim_vB);
fun lmemConsFwd_b (x,y,t) = beta_norm (Drule.infer_instantiate ctxtB [(("x",0), ctermB x),(("y",0), ctermB y),(("t",0), ctermB t)] lmem_cons_fwd_vB);
fun lmemConsBwd_b (x,y,t) = beta_norm (Drule.infer_instantiate ctxtB [(("x",0), ctermB x),(("y",0), ctermB y),(("t",0), ctermB t)] lmem_cons_bwd_vB);
fun lnodupConsBwd_b (x,t) = beta_norm (Drule.infer_instantiate ctxtB [(("x",0), ctermB x),(("t",0), ctermB t)] lnodup_cons_bwd_vB);
fun mp_b (At,Bt) hImp hA = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("A",0), ctermB At),(("B",0), ctermB Bt)] mp_vB)) hImp) hA;
fun impI_b (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("A",0), ctermB At),(("B",0), ctermB Bt)] impI_vB)) h;
fun allI_b Pabs h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("P",0), ctermB Pabs)] allI_vB)) h;
fun allE_b Pabs at h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("P",0), ctermB Pabs),(("a",0), ctermB at)] allE_vB)) h;
fun disjE_b (At,Bt,Ct) dThm cA cB = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("A",0), ctermB At),(("B",0), ctermB Bt),(("C",0), ctermB Ct)] disjE_vB)) dThm) cA) cB;
fun conjI_b (At,Bt) hA hB = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("A",0), ctermB At),(("B",0), ctermB Bt)] conjI_vB)) hA) hB;
fun conjunct1_b (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("A",0), ctermB At),(("B",0), ctermB Bt)] conjunct1_vB)) h;
fun conjunct2_b (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("A",0), ctermB At),(("B",0), ctermB Bt)] conjunct2_vB)) h;
fun exI_b Pabs at hbody = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("P",0), ctermB Pabs),(("a",0), ctermB at)] exI_vB)) hbody;
fun exE_b (Pabs, goalC) exThm wName wT bodyFn =
  let val wF = Free(wName, wT)
      val hypTerm = jT (Term.betapply (Pabs, wF))
      val hypThm  = Thm.assume (ctermB hypTerm)
      val body    = bodyFn wF hypThm
      val minor   = Thm.forall_intr (ctermB wF) (Thm.implies_intr (ctermB hypTerm) body)
      val exE_inst= beta_norm (Drule.infer_instantiate ctxtB [(("P",0), ctermB Pabs),(("Q",0), ctermB goalC)] exE_vB)
  in Thm.implies_elim (Thm.implies_elim exE_inst exThm) minor end;
fun em_b t = beta_norm (Drule.infer_instantiate ctxtB [(("A",0), ctermB t)] ex_middle_vB);
fun oFalse_elim_b rT = beta_norm (Drule.infer_instantiate ctxtB [(("R",0), ctermB rT)] oFalse_elim_vB);
fun lt_irrefl_b n hlt = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB n)] lt_irrefl_vB)) hlt;
fun lt_trans_b (a,b,c) h1 h2 = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("a",0), ctermB a),(("b",0), ctermB b),(("c",0), ctermB c)] lt_trans_vB)) h1) h2;
fun lt_suc_b n = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB n)] lt_suc_vB);
fun rmod_lt_b (ct,dt) hpos = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("c_dm",0), ctermB ct),(("d_dm",0), ctermB dt)] rmod_lt_vB)) hpos;
fun nat_induct_b Pabs kT baseThm stepThm =
  let val ind = beta_norm (Drule.infer_instantiate ctxtB [(("P",0), ctermB Pabs),(("k",0), ctermB kT)] nat_induct_vB)
  in Thm.implies_elim (Thm.implies_elim ind baseThm) stepThm end;
fun bresZero_b () = bres_zero_vB;
fun bresSuc_b n = beta_norm (Drule.infer_instantiate ctxtB [(("n_brc",0), ctermB n)] bres_suc_vB);
(* lt_imp_neq on ctxtB *)
fun lt_imp_neq_b (cP, nP) hlt =
  let val hca = Thm.assume (ctermB (jT (oeq cP nP)))
      val zl = Free("zinb", natT)
      val Plt = Term.lambda zl (lt zl nP)
      val ltnn = oeq_rw_b2 (Plt, cP, nP) hca hlt
      val fls = lt_irrefl_b nP ltnn
      val metaImp = Thm.implies_intr (ctermB (jT (oeq cP nP))) fls
  in impI_b (oeq cP nP, oFalseC) metaImp end;
val () = out "PB_T4_VARIFY_READY\n";

val () = out "PB_T4_DONE\n";

(* ============================================================================
   PART B TEST 5: the four residue-list lemmas on ctxtB (copied from gridres).
   ============================================================================ *)
val () = out "PB_T5_BEGIN\n";

(* ---- breslen : oeq (llen (bres n)) n   (induction on n) ---- *)
val breslen =
  let
    val Pabs = Term.lambda (Free("n_bl", natT)) (oeq (llen (bres (Free("n_bl",natT)))) (Free("n_bl",natT)))
    val base =
      let val r0 = bresZero_b ()                     (* leq (bres 0) lnil *)
          val llN = llenNil_b ()                      (* oeq (llen lnil) 0 *)
          val r0s = leq_sym_b r0                       (* leq lnil (bres 0) *)
          val zN = Free("zbl0", natlistT)
          val P = Term.lambda zN (oeq (llen zN) ZeroC)
      in leq_rw_b (P, lnilC, bres ZeroC) r0s llN end
    val step =
      let val xF = Free("x_bl", natT)
          val ihP = jT (oeq (llen (bres xF)) xF)
          val hIH = Thm.assume (ctermB ihP)
          val rSuc = bresSuc_b xF                      (* leq (bres (Suc x)) (lcons (fres x)(bres x)) *)
          val gx = fres xF
          val llc = llenCons_b (gx, bres xF)           (* oeq (llen (lcons (fres x)(bres x))) (Suc(llen(bres x))) *)
          val sucIH = Suc_cong_b hIH                    (* Suc(llen(bres x)) = Suc x *)
          val eqCons = oeqTrans_b (llc, sucIH)          (* oeq (llen (lcons ..)) (Suc x) *)
          val zN = Free("zbls", natlistT)
          val P = Term.lambda zN (oeq (llen zN) (suc xF))
          val rSuc_s = leq_sym_b rSuc
      in Thm.forall_intr (ctermB xF) (Thm.implies_intr (ctermB ihP)
           (leq_rw_b (P, lcons gx (bres xF), bres (suc xF)) rSuc_s eqCons)) end
    val kF = Free("k_bl", natT)
  in nat_induct_b Pabs kF base step end;
val () = out ("PB_T5_BRESLEN hyps="^Int.toString(length(Thm.hyps_of breslen))^"\n");

(* ---- bresmem_lt_p : 0<p ==> !e. lmem e (bres n) ==> lt e p  (induction on n) ---- *)
fun bresmem_lt_p_g hpos =
  let
    fun memBody n = let val ef=Free("e_bm",natT)
                    in mkForall (Term.lambda ef (mkImp (lmem ef (bres n)) (lt ef pB))) end
    val Pabs = Term.lambda (Free("n_bm", natT)) (memBody (Free("n_bm",natT)))
    val base =
      let val ef=Free("e_bm",natT)
          val r0 = bresZero_b ()
          val body =
            let val hm = Thm.assume (ctermB (jT (lmem ef (bres ZeroC))))
                val zN=Free("zbm0",natlistT)
                val Pm=Term.lambda zN (lmem ef zN)
                val memNil = leq_rw_b (Pm, bres ZeroC, lnilC) r0 hm
                val fls = Thm.implies_elim (lmemNilElim_b ef) memNil
                val concl = Thm.implies_elim (oFalse_elim_b (lt ef pB)) fls
            in impI_b (lmem ef (bres ZeroC), lt ef pB)
                 (Thm.implies_intr (ctermB (jT (lmem ef (bres ZeroC)))) concl) end
      in allI_b (Term.lambda ef (mkImp (lmem ef (bres ZeroC)) (lt ef pB)))
           (Thm.forall_intr (ctermB ef) body) end
    val step =
      let val xF=Free("x_bm",natT)
          val ihP = jT (memBody xF)
          val hIH = Thm.assume (ctermB ihP)
          val ef=Free("e_bm",natT)
          val gx = fres xF
          val rSuc = bresSuc_b xF
          val body =
            let val hm = Thm.assume (ctermB (jT (lmem ef (bres (suc xF)))))
                val zN=Free("zbms",natlistT)
                val Pm=Term.lambda zN (lmem ef zN)
                val memCons = leq_rw_b (Pm, bres (suc xF), lcons gx (bres xF)) rSuc hm
                val dj = Thm.implies_elim (lmemConsFwd_b (ef, gx, bres xF)) memCons
                val caseEq =
                  let val heq = Thm.assume (ctermB (jT (oeq ef gx)))
                      val ltgx = rmod_lt_b (fdec xF, pB) hpos   (* lt (rmodv (fdec x) p) p = lt (fres x) p *)
                      val heq_s = oeqSym_b heq
                      val zl=Free("zbmlt",natT)
                      val Plt=Term.lambda zl (lt zl pB)
                      val res = oeq_rw_b2 (Plt, gx, ef) heq_s ltgx   (* lt e p *)
                  in Thm.implies_intr (ctermB (jT (oeq ef gx))) res end
                val caseMem =
                  let val hmx = Thm.assume (ctermB (jT (lmem ef (bres xF))))
                      val ihAt = allE_b (Term.lambda ef (mkImp (lmem ef (bres xF)) (lt ef pB))) ef hIH
                      val res = mp_b (lmem ef (bres xF), lt ef pB) ihAt hmx
                  in Thm.implies_intr (ctermB (jT (lmem ef (bres xF)))) res end
                val resThm = disjE_b (oeq ef gx, lmem ef (bres xF), lt ef pB) dj caseEq caseMem
            in impI_b (lmem ef (bres (suc xF)), lt ef pB)
                 (Thm.implies_intr (ctermB (jT (lmem ef (bres (suc xF))))) resThm) end
          val allStep = allI_b (Term.lambda ef (mkImp (lmem ef (bres (suc xF))) (lt ef pB)))
                          (Thm.forall_intr (ctermB ef) body)
      in Thm.forall_intr (ctermB xF) (Thm.implies_intr (ctermB ihP) allStep) end
    val kF = Free("k_bm", natT)
  in (kF, nat_induct_b Pabs kF base step) end;
val () =
  let val hpos = Thm.assume (ctermB (jT (lt ZeroC pB)))
      val (k, th) = bresmem_lt_p_g hpos
  in out ("PB_T5_BRESMEM nhyps="^Int.toString(length(Thm.hyps_of th))^"\n") end;

val () = out "PB_T5_DONE\n";

(* ============================================================================
   PART B TEST 6: mem_bres_reflect + dup_bres (copied from gridres proofs).
   ============================================================================ *)
val () = out "PB_T6_BEGIN\n";

(* extra varify: lt_suc / lt_trans already _vB; need lnodup_nil on B (have lnodup_nil_vB) *)

(* ---- mem_bres_reflect : !e. lmem e (bres n) ==> ?c. lt c n /\ oeq e (fres c)  (induction on n) ---- *)
val mem_bres_reflect =
  let
    fun reflBody n e = mkEx (Term.lambda (Free("c_rb",natT))
                         (mkConj (lt (Free("c_rb",natT)) n) (oeq e (fres (Free("c_rb",natT))))))
    fun allBody n = let val ef=Free("e_rb",natT)
                    in mkForall (Term.lambda ef (mkImp (lmem ef (bres n)) (reflBody n ef))) end
    val Pabs = Term.lambda (Free("n_rb", natT)) (allBody (Free("n_rb",natT)))
    val base =
      let val ef=Free("e_rb",natT)
          val r0 = bresZero_b ()
          val body =
            let val hm = Thm.assume (ctermB (jT (lmem ef (bres ZeroC))))
                val zN=Free("zrb0",natlistT)
                val Pm=Term.lambda zN (lmem ef zN)
                val memNil = leq_rw_b (Pm, bres ZeroC, lnilC) r0 hm
                val fls = Thm.implies_elim (lmemNilElim_b ef) memNil
                val concl = Thm.implies_elim (oFalse_elim_b (reflBody ZeroC ef)) fls
            in impI_b (lmem ef (bres ZeroC), reflBody ZeroC ef)
                 (Thm.implies_intr (ctermB (jT (lmem ef (bres ZeroC)))) concl) end
      in allI_b (Term.lambda ef (mkImp (lmem ef (bres ZeroC)) (reflBody ZeroC ef)))
           (Thm.forall_intr (ctermB ef) body) end
    val step =
      let val xF=Free("x_rb",natT)
          val ihP = jT (allBody xF)
          val hIH = Thm.assume (ctermB ihP)
          val ef=Free("e_rb",natT)
          val gx = fres xF
          val rSuc = bresSuc_b xF
          val body =
            let val hm = Thm.assume (ctermB (jT (lmem ef (bres (suc xF)))))
                val zN=Free("zrbs",natlistT)
                val Pm=Term.lambda zN (lmem ef zN)
                val memCons = leq_rw_b (Pm, bres (suc xF), lcons gx (bres xF)) rSuc hm
                val dj = Thm.implies_elim (lmemConsFwd_b (ef, gx, bres xF)) memCons
                val goalC = reflBody (suc xF) ef
                val caseEq =
                  let val heq = Thm.assume (ctermB (jT (oeq ef gx)))
                      val ltx = lt_suc_b xF
                      val cj = conjI_b (lt xF (suc xF), oeq ef (fres xF)) ltx heq
                      val Pc = Term.lambda (Free("c_rb",natT))
                                 (mkConj (lt (Free("c_rb",natT)) (suc xF)) (oeq ef (fres (Free("c_rb",natT)))))
                      val ex = exI_b Pc xF cj
                  in Thm.implies_intr (ctermB (jT (oeq ef gx))) ex end
                val caseMem =
                  let val hmx = Thm.assume (ctermB (jT (lmem ef (bres xF))))
                      val ihAt = allE_b (Term.lambda ef (mkImp (lmem ef (bres xF)) (reflBody xF ef))) ef hIH
                      val exC = mp_b (lmem ef (bres xF), reflBody xF ef) ihAt hmx
                      val PcX = Term.lambda (Free("c_rb",natT))
                                  (mkConj (lt (Free("c_rb",natT)) xF) (oeq ef (fres (Free("c_rb",natT)))))
                      fun bodyC c (hc:thm) =
                        let val hlt = conjunct1_b (lt c xF, oeq ef (fres c)) hc
                            val heqe = conjunct2_b (lt c xF, oeq ef (fres c)) hc
                            val ltcSx = lt_trans_b (c, xF, suc xF) hlt (lt_suc_b xF)
                            val cj = conjI_b (lt c (suc xF), oeq ef (fres c)) ltcSx heqe
                            val Pc = Term.lambda (Free("c_rb",natT))
                                       (mkConj (lt (Free("c_rb",natT)) (suc xF)) (oeq ef (fres (Free("c_rb",natT)))))
                        in exI_b Pc c cj end
                      val res = exE_b (PcX, goalC) exC "cc_rb" natT bodyC
                  in Thm.implies_intr (ctermB (jT (lmem ef (bres xF)))) res end
                val resThm = disjE_b (oeq ef gx, lmem ef (bres xF), goalC) dj caseEq caseMem
            in impI_b (lmem ef (bres (suc xF)), goalC)
                 (Thm.implies_intr (ctermB (jT (lmem ef (bres (suc xF))))) resThm) end
          val allStep = allI_b (Term.lambda ef (mkImp (lmem ef (bres (suc xF))) (reflBody (suc xF) ef)))
                          (Thm.forall_intr (ctermB ef) body)
      in Thm.forall_intr (ctermB xF) (Thm.implies_intr (ctermB ihP) allStep) end
    val kF = Free("k_rb", natT)
  in (kF, nat_induct_b Pabs kF base step) end;
val () =
  let val (k, th) = mem_bres_reflect
  in out ("PB_T6_REFLECT nhyps="^Int.toString(length(Thm.hyps_of th))^"\n") end;

(* ---- collPair / mkCollExists for fres ---- *)
fun collPairB n =
  let val c1f=Free("c1_db",natT)
  in mkEx (Term.lambda c1f
       (mkEx (Term.lambda (Free("c2_db",natT))
          (mkConj (lt c1f n)
            (mkConj (lt (Free("c2_db",natT)) n)
              (mkConj (neg (oeq c1f (Free("c2_db",natT))))
                      (oeq (fres c1f) (fres (Free("c2_db",natT)))))))))) end;
fun mkCollExistsB n (w1,w2) hconj =
  let
    val Pc2 = Term.lambda (Free("c2_db",natT))
                (mkConj (lt w1 n)
                  (mkConj (lt (Free("c2_db",natT)) n)
                    (mkConj (neg (oeq w1 (Free("c2_db",natT))))
                            (oeq (fres w1) (fres (Free("c2_db",natT)))))))
    val ex2 = exI_b Pc2 w2 hconj
    val Pc1 = Term.lambda (Free("c1_db",natT))
                (mkEx (Term.lambda (Free("c2_db",natT))
                  (mkConj (lt (Free("c1_db",natT)) n)
                    (mkConj (lt (Free("c2_db",natT)) n)
                      (mkConj (neg (oeq (Free("c1_db",natT)) (Free("c2_db",natT))))
                              (oeq (fres (Free("c1_db",natT))) (fres (Free("c2_db",natT)))))))))
  in exI_b Pc1 w1 ex2 end;

(* ---- dup_bres : neg(lnodup (bres n)) ==> collPairB n  (induction on n) ---- *)
val dup_bres =
  let
    val Pabs = Term.lambda (Free("n_db", natT))
                 (mkImp (neg (lnodup (bres (Free("n_db",natT))))) (collPairB (Free("n_db",natT))))
    val base =
      let val r0 = bresZero_b ()
          val hneg = Thm.assume (ctermB (jT (neg (lnodup (bres ZeroC)))))
      in
        let
          val zN=Free("zdb0",natlistT)
          val Pnd=Term.lambda zN (lnodup zN)
          val r0s = leq_sym_b r0
          val ndG = leq_rw_b (Pnd, lnilC, bres ZeroC) r0s lnodup_nil_vB
          val fls = mp_b (lnodup (bres ZeroC), oFalseC) hneg ndG
          val concl = Thm.implies_elim (oFalse_elim_b (collPairB ZeroC)) fls
        in impI_b (neg (lnodup (bres ZeroC)), collPairB ZeroC)
             (Thm.implies_intr (ctermB (jT (neg (lnodup (bres ZeroC))))) concl) end
      end
    val step =
      let val xF=Free("x_db",natT)
          val ihP = jT (mkImp (neg (lnodup (bres xF))) (collPairB xF))
          val hIH = Thm.assume (ctermB ihP)
          val gx = fres xF
          val tailL = bres xF
          val rSuc = bresSuc_b xF
          val goalC = collPairB (suc xF)
          val hnegP = jT (neg (lnodup (bres (suc xF))))
          val hneg = Thm.assume (ctermB hnegP)
          val em = em_b (lmem gx tailL)
          val (kr, refl) = mem_bres_reflect
          val caseA =
            let val hmem = Thm.assume (ctermB (jT (lmem gx tailL)))
                val refl_x = beta_norm (Thm.forall_elim (ctermB xF) (Thm.forall_intr (ctermB kr) refl))
                val ihAt = allE_b (Term.lambda (Free("e_rb",natT))
                              (mkImp (lmem (Free("e_rb",natT)) tailL)
                                 (mkEx (Term.lambda (Free("c_rb",natT))
                                    (mkConj (lt (Free("c_rb",natT)) xF)
                                            (oeq (Free("e_rb",natT)) (fres (Free("c_rb",natT))))))))) gx refl_x
                val exC = mp_b (lmem gx tailL,
                               mkEx (Term.lambda (Free("c_rb",natT))
                                  (mkConj (lt (Free("c_rb",natT)) xF) (oeq gx (fres (Free("c_rb",natT))))))) ihAt hmem
                val PcX = Term.lambda (Free("c_rb",natT))
                            (mkConj (lt (Free("c_rb",natT)) xF) (oeq gx (fres (Free("c_rb",natT)))))
                fun bodyC c (hc:thm) =
                  let val hltc = conjunct1_b (lt c xF, oeq gx (fres c)) hc
                      val heqgx = conjunct2_b (lt c xF, oeq gx (fres c)) hc
                      val ltxSx = lt_suc_b xF
                      val ltcSx = lt_trans_b (c, xF, suc xF) hltc (lt_suc_b xF)
                      val negcx = lt_imp_neq_b (c, xF) hltc       (* neg (oeq c x) *)
                      val negxc =
                        let val hxc = Thm.assume (ctermB (jT (oeq xF c)))
                            val hcx = oeqSym_b hxc
                            val fls = mp_b (oeq c xF, oFalseC) negcx hcx
                            val metaImp = Thm.implies_intr (ctermB (jT (oeq xF c))) fls
                        in impI_b (oeq xF c, oFalseC) metaImp end
                      val gxgc = heqgx
                      val cj = conjI_b (lt xF (suc xF),
                                  mkConj (lt c (suc xF))
                                    (mkConj (neg (oeq xF c)) (oeq (fres xF)(fres c))))
                                  ltxSx
                                  (conjI_b (lt c (suc xF), mkConj (neg (oeq xF c)) (oeq (fres xF)(fres c)))
                                     ltcSx
                                     (conjI_b (neg (oeq xF c), oeq (fres xF)(fres c)) negxc gxgc))
                  in mkCollExistsB (suc xF) (xF, c) cj end
                val res = exE_b (PcX, goalC) exC "cA_db" natT bodyC
            in Thm.implies_intr (ctermB (jT (lmem gx tailL))) res end
          val caseB =
            let val hnotmem = Thm.assume (ctermB (jT (neg (lmem gx tailL))))
                val negNDtail =
                  let val hndtail = Thm.assume (ctermB (jT (lnodup tailL)))
                      val cjND = conjI_b (neg (lmem gx tailL), lnodup tailL) hnotmem hndtail
                      val ndCons = Thm.implies_elim (lnodupConsBwd_b (gx, tailL)) cjND
                      val zN=Free("zdbB",natlistT)
                      val Pnd=Term.lambda zN (lnodup zN)
                      val rSuc_s = leq_sym_b rSuc
                      val ndG = leq_rw_b (Pnd, lcons gx tailL, bres (suc xF)) rSuc_s ndCons
                      val fls = mp_b (lnodup (bres (suc xF)), oFalseC) hneg ndG
                      val metaImp = Thm.implies_intr (ctermB (jT (lnodup tailL))) fls
                  in impI_b (lnodup tailL, oFalseC) metaImp end
                val exC = mp_b (neg (lnodup tailL), collPairB xF) hIH negNDtail
                val Pc1 = Term.lambda (Free("c1_db",natT))
                            (mkEx (Term.lambda (Free("c2_db",natT))
                              (mkConj (lt (Free("c1_db",natT)) xF)
                                (mkConj (lt (Free("c2_db",natT)) xF)
                                  (mkConj (neg (oeq (Free("c1_db",natT)) (Free("c2_db",natT))))
                                          (oeq (fres (Free("c1_db",natT))) (fres (Free("c2_db",natT)))))))))
                fun body1 c1 (h1:thm) =
                  let val Pc2 = Term.lambda (Free("c2_db",natT))
                                  (mkConj (lt c1 xF)
                                    (mkConj (lt (Free("c2_db",natT)) xF)
                                      (mkConj (neg (oeq c1 (Free("c2_db",natT))))
                                              (oeq (fres c1) (fres (Free("c2_db",natT)))))))
                      fun body2 c2 (h2:thm) =
                        let val A = lt c1 xF
                            val B = lt c2 xF
                            val Cc = neg (oeq c1 c2)
                            val D = oeq (fres c1)(fres c2)
                            val hA = conjunct1_b (A, mkConj B (mkConj Cc D)) h2
                            val rest1 = conjunct2_b (A, mkConj B (mkConj Cc D)) h2
                            val hB = conjunct1_b (B, mkConj Cc D) rest1
                            val rest2 = conjunct2_b (B, mkConj Cc D) rest1
                            val hC = conjunct1_b (Cc, D) rest2
                            val hD = conjunct2_b (Cc, D) rest2
                            val ltc1 = lt_trans_b (c1, xF, suc xF) hA (lt_suc_b xF)
                            val ltc2 = lt_trans_b (c2, xF, suc xF) hB (lt_suc_b xF)
                            val cj = conjI_b (lt c1 (suc xF),
                                        mkConj (lt c2 (suc xF))
                                          (mkConj (neg (oeq c1 c2)) (oeq (fres c1)(fres c2))))
                                        ltc1
                                        (conjI_b (lt c2 (suc xF), mkConj (neg (oeq c1 c2)) (oeq (fres c1)(fres c2)))
                                           ltc2
                                           (conjI_b (neg (oeq c1 c2), oeq (fres c1)(fres c2)) hC hD))
                        in mkCollExistsB (suc xF) (c1, c2) cj end
                  in exE_b (Pc2, goalC) h1 "c2_dbB" natT body2 end
                val res = exE_b (Pc1, goalC) exC "c1_dbB" natT body1
            in Thm.implies_intr (ctermB (jT (neg (lmem gx tailL)))) res end
          val resThm = disjE_b (lmem gx tailL, neg (lmem gx tailL), goalC) em caseA caseB
      in Thm.forall_intr (ctermB xF) (Thm.implies_intr (ctermB ihP)
           (impI_b (neg (lnodup (bres (suc xF))), goalC)
              (Thm.implies_intr (ctermB hnegP) resThm))) end
    val kF = Free("k_db", natT)
  in (kF, nat_induct_b Pabs kF base step) end;
val () =
  let val (k, th) = dup_bres
  in out ("PB_T6_DUP nhyps="^Int.toString(length(Thm.hyps_of th))^"\n") end;

val () = out "PB_T6_DONE\n";

(* ============================================================================
   PART B TEST 7: the pigeonhole assembly -> collision -> 4-case decode ->
   cong p (a*a+b*b+1) 0.  Parameters: prime2 p, p = Suc(m+m) (odd).
   We work with the fixed Frees pB, mB declared in T4.
   ============================================================================ *)
val () = out "PB_T7_BEGIN\n";

(* extra ctxtB helpers needed for the assembly arithmetic *)
val add_0_vB        = varify add_0;
val add_0_right_vB  = varify add_0_right;
val add_Suc_vB      = varify add_Suc;
val add_comm_vB     = varify add_comm;
val le_total_vB     = varify le_total;
val le_add_vB       = varify le_add;
val le_trans_vB     = varify le_trans;
val le_suc_mono_vB  = varify le_suc_mono;
val sub_recover_vB  = varify sub_recover_ax;
val disj_zero_or_suc_vB = varify disj_zero_or_suc;
fun add0_b t   = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB t)] add_0_vB);
fun add0r_b t  = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB t)] add_0_right_vB);
fun addSuc_b (m,n) = beta_norm (Drule.infer_instantiate ctxtB [(("m",0), ctermB m),(("n",0), ctermB n)] add_Suc_vB);
fun addcomm_b (m,n) = beta_norm (Drule.infer_instantiate ctxtB [(("m",0), ctermB m),(("n",0), ctermB n)] add_comm_vB);
fun le_total_b (m,n) = beta_norm (Drule.infer_instantiate ctxtB [(("m",0), ctermB m),(("n",0), ctermB n)] le_total_vB);
fun le_add_b (m,p) = beta_norm (Drule.infer_instantiate ctxtB [(("m",0), ctermB m),(("p",0), ctermB p)] le_add_vB);
fun le_trans_b (a,b,c) h1 h2 = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("m",0), ctermB a),(("n",0), ctermB b),(("k",0), ctermB c)] le_trans_vB)) h1) h2;
fun le_suc_mono_b (m,n) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("m",0), ctermB m),(("n",0), ctermB n)] le_suc_mono_vB)) h;
fun le_intro_b (mT,nT,w) hyp =
  let val Pabs = Abs("p", natT, oeq nT (add mT (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtB [(("P",0), ctermB Pabs),(("a",0), ctermB w)] exI_vB)
  in inst OF [hyp] end;
fun dzos_b t = beta_norm (Drule.infer_instantiate ctxtB [(("p",0), ctermB t)] disj_zero_or_suc_vB);
fun fdecA_b k hlt = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("k_fd",0), ctermB k),(("m_B",0), ctermB mB)] fdecA_vB)) hlt;
fun fdecB_b k hle = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("k_fd",0), ctermB k),(("m_B",0), ctermB mB),(("p_B",0), ctermB pB)] fdecB_vB)) hle;
val () = out "PB_T7_HELPERS_OK\n";

(* ---- assume the parameter hypotheses ---- *)
val primeP = jT (prime2 pB);
val hprime = Thm.assume (ctermB primeP);
val oddP   = jT (oeq pB (suc (add mB mB)));   (* p = Suc(m+m) = 2m+1 *)
val hodd   = Thm.assume (ctermB oddP);

(* 0<p : p = Suc(m+m) so p = Suc(..) => lt 0 p = le (Suc 0) p, witness (m+m):
   p = (Suc 0)+(m+m) ? add (Suc 0)(m+m) = Suc(0+(m+m)) = Suc(m+m) = p. *)
val hposB =
  let val a1 = addSuc_b (ZeroC, add mB mB)        (* (Suc 0)+(m+m) = Suc(0+(m+m)) *)
      val a2 = add0_b (add mB mB)                  (* 0+(m+m) = (m+m) *)
      val a2s= Suc_cong_b a2                       (* Suc(0+(m+m)) = Suc(m+m) *)
      val a1c= oeqTrans_b (a1, a2s)                (* (Suc 0)+(m+m) = Suc(m+m) *)
      val pEq= oeqTrans_b (hodd, oeqSym_b a1c)     (* p = (Suc 0)+(m+m) *)
  in le_intro_b (suc ZeroC, pB, add mB mB) pEq end;   (* le (Suc 0) p = lt 0 p *)
val () = out "PB_T7_POS_OK\n";

(* n = Suc p (the list length = p+1).  bound: lt p (llen (bres n)) = lt p (Suc p). *)
val nB7 = suc pB;
(* breslen at n : oeq (llen (bres (Suc p))) (Suc p) -- breslen is a forall-free thm with k_bl;
   specialize via forall_intr/elim. *)
val breslen_n =
  let val kbl = Free("k_bl", natT)   (* the induction var name used in breslen *)
  in beta_norm (Thm.forall_elim (ctermB nB7) (Thm.forall_intr (ctermB kbl) breslen)) end
  handle _ => breslen;  (* if breslen is already closed over k via a different mechanism *)
val () = out ("PB_T7_BRESLEN_N hyps="^Int.toString(length(Thm.hyps_of breslen_n))^"\n");

val () = out "PB_T7_PARTIAL_DONE\n";

(* ============================================================================
   PART B TEST 8: collision extraction + arithmetic helpers + bval_cong.
   ============================================================================ *)
val () = out "PB_T8_BEGIN\n";

(* lt_suc_cases on ctxtB *)
val lt_suc_cases_vB = varify lt_suc_cases;
fun lt_suc_cases_b (m,n) hlt = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB
      [(("m",0), ctermB m),(("n",0), ctermB n)] lt_suc_cases_vB)) hlt;
(* mult_le_mono on ctxtB *)
val mult_le_mono_vB = varify mult_le_mono;
fun mult_le_mono_b (c,j,k) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB
      [(("c",0), ctermB c),(("j",0), ctermB j),(("k",0), ctermB k)] mult_le_mono_vB)) h;
(* mult congruence on ctxtB *)
val mult_comm_vB2 = varify mult_comm;
fun multcomm_b (m,n) = beta_norm (Drule.infer_instantiate ctxtB [(("m",0), ctermB m),(("n",0), ctermB n)] mult_comm_vB2);
val mult_assoc_vB2 = varify mult_assoc;
fun multassoc_b (m,n,k) = beta_norm (Drule.infer_instantiate ctxtB [(("m",0), ctermB m),(("n",0), ctermB n),(("k",0), ctermB k)] mult_assoc_vB2);
val add_assoc_vB2 = varify add_assoc;
fun addassoc_b (m,n,k) = beta_norm (Drule.infer_instantiate ctxtB [(("m",0), ctermB m),(("n",0), ctermB n),(("k",0), ctermB k)] add_assoc_vB2);
val mult_Suc_vB = varify mult_Suc;
val mult_Suc_right_vB = varify mult_Suc_right;
fun multSucr_b (n,m) = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB n),(("m",0), ctermB m)] mult_Suc_right_vB);
fun mult_cong_l_b (p,q,k) hpq = let val P=Term.lambda (Free("zmlb",natT)) (oeq (mult p k)(mult (Free("zmlb",natT)) k)) in oeq_rw_b2 (P,p,q) hpq (oeqRefl_b (mult p k)) end;
fun mult_cong_r_b (h,p,q) hpq = let val P=Term.lambda (Free("zmrb",natT)) (oeq (mult h p)(mult h (Free("zmrb",natT)))) in oeq_rw_b2 (P,p,q) hpq (oeqRefl_b (mult h p)) end;
fun add_cong_l_b (p,q,k) hpq = let val P=Term.lambda (Free("zalb",natT)) (oeq (add p k)(add (Free("zalb",natT)) k)) in oeq_rw_b2 (P,p,q) hpq (oeqRefl_b (add p k)) end;
fun add_cong_r_b (h,p,q) hpq = let val P=Term.lambda (Free("zarb",natT)) (oeq (add h p)(add h (Free("zarb",natT)))) in oeq_rw_b2 (P,p,q) hpq (oeqRefl_b (add h p)) end;
fun sub_recover_b (sT,jT_) hle = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB
      [(("s_sub",0), ctermB sT),(("j_sub",0), ctermB jT_)] sub_recover_vB)) hle;
val () = out "PB_T8_HELPERS2_OK\n";

(* ---- le_from_lt_suc : lt c (Suc m) ==> le c m ---- *)
fun le_from_lt_suc (cT, mT) hlt =   (* hlt : lt c (Suc m) ; result le c m *)
  let val dj = lt_suc_cases_b (cT, mT) hlt   (* Disj (lt c m)(oeq c m) *)
      val caseLt = let val h = Thm.assume (ctermB (jT (lt cT mT)))
                       (* lt c m = le (Suc c) m ; want le c m : le c (Suc c) then trans? simpler:
                          lt c m means le (Suc c) m; le c (Suc c) (le_add: le c (c+1)? ). Use:
                          le c m from le (Suc c) m via le_trans (le c (Suc c))(le (Suc c) m). *)
                       val lecSc = le_add_b (cT, suc ZeroC)   (* le c (c + 1) *)
                       (* c+1 = Suc c : add c (Suc 0) = Suc(c+0)=Suc c *)
                       val a1 = beta_norm (Drule.infer_instantiate ctxtB [(("m",0), ctermB cT),(("n",0), ctermB ZeroC)] (varify add_Suc_right))
                       (* a1 : c + Suc 0 = Suc(c+0) *)
                       val a2 = add0r_b cT      (* c+0 = c *)
                       val a2s= Suc_cong_b a2   (* Suc(c+0) = Suc c *)
                       val cEq= oeqTrans_b (a1, a2s)  (* c + Suc 0 = Suc c *)
                       val lecSc2 = oeq_rw_b2 (Term.lambda (Free("zlfs",natT)) (le cT (Free("zlfs",natT))), add cT (suc ZeroC), suc cT) cEq lecSc  (* le c (Suc c) *)
                       val r = le_trans_b (cT, suc cT, mT) lecSc2 h   (* le c m *)
                   in Thm.implies_intr (ctermB (jT (lt cT mT))) r end
      val caseEq = let val h = Thm.assume (ctermB (jT (oeq cT mT)))
                       (* oeq c m => le c m (refl rewritten) : le m m then rewrite m->c? le c m via witness 0: m = c+0 *)
                       val m0 = oeqSym_b (add0r_b cT)   (* c = c+0 *)
                       (* want oeq m (c + 0): from c=m (h sym) and c=c+0 *)
                       val mEqc = oeqSym_b h            (* m = c *)
                       val mc0 = oeqTrans_b (mEqc, m0)  (* m = c + 0 *)
                       val r = le_intro_b (cT, mT, ZeroC) mc0   (* le c m *)
                   in Thm.implies_intr (ctermB (jT (oeq cT mT))) r end
  in disjE_b (lt cT mT, oeq cT mT, le cT mT) dj caseLt caseEq end;
val () = out "PB_T8_LEFROMLT_OK\n";

(* ---- m_lt_p : lt m p  (p = Suc(m+m), so m < m+m+1) ---- *)
val m_lt_p =
  let (* lt m p = le (Suc m) p ; p = Suc(m+m); le (Suc m)(Suc(m+m)) via le_suc_mono (le m (m+m)) *)
      val lemm = le_add_b (mB, mB)            (* le m (m+m) *)
      val leSmSmm = le_suc_mono_b (mB, add mB mB) lemm   (* le (Suc m)(Suc(m+m)) *)
      (* rewrite Suc(m+m) -> p via hodd sym *)
      val r = oeq_rw_b2 (Term.lambda (Free("zmlp",natT)) (le (suc mB) (Free("zmlp",natT))), suc (add mB mB), pB) (oeqSym_b hodd) leSmSmm
  in r end;   (* lt m p *)
val () = out ("PB_T8_MLTP hyps="^Int.toString(length(Thm.hyps_of m_lt_p))^"\n");

val () = out "PB_T8_DONE\n";

(* ============================================================================
   PART B TEST 9: cong infrastructure on ctxtB + bval_cong + bound.
   ============================================================================ *)
val () = out "PB_T9_BEGIN\n";

(* cong builders on ctxtB (cong = Disj congL congR; congL/congR/cong are SML fns, ctxt-free terms) *)
val disjI1_vB = varify disjI1_ax;
val disjI2_vB = varify disjI2_ax;
fun disjI1_b (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("A",0), ctermB At),(("B",0), ctermB Bt)] disjI1_vB)) h;
fun disjI2_b (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("A",0), ctermB At),(("B",0), ctermB Bt)] disjI2_vB)) h;
(* cong_introL_b : from hyp: oeq b (add a (mult m w)) build cong m a b *)
fun cong_introL_b (m,a,b,w) hyp =
  let val LAbs = Abs("k", natT, oeq b (add a (mult m (Bound 0))))
      val exThm = exI_b LAbs w hyp
  in disjI1_b (congL m a b, congR m a b) exThm end;
fun cong_introR_b (m,a,b,w) hyp =
  let val RAbs = Abs("k", natT, oeq a (add b (mult m (Bound 0))))
      val exThm = exI_b RAbs w hyp
  in disjI2_b (congL m a b, congR m a b) exThm end;
(* cong_radd_cancel_b *)
val cong_radd_cancel_vB = varify cong_radd_cancel;
fun cong_radd_cancel_b (m,a,b,w) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB
      [(("m_cc",0), ctermB m),(("a_cc",0), ctermB a),(("b_cc",0), ctermB b),(("w_cc",0), ctermB w)] cong_radd_cancel_vB)) h;
(* cong_sym_b / cong_trans_b *)
val cong_sym_vB = varify cong_sym;
val cong_trans_vB = varify cong_trans;
fun cong_sym_b (m,a,b) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("m",0), ctermB m),(("a",0), ctermB a),(("b",0), ctermB b)] cong_sym_vB)) h;
fun cong_trans_b (m,a,b,c) h1 h2 = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("m",0), ctermB m),(("a",0), ctermB a),(("b",0), ctermB b),(("c",0), ctermB c)] cong_trans_vB)) h1) h2;
val () = out "PB_T9_CONG_INFRA_OK\n";

(* cong_pp_zero : cong p (mult p p) Zero.   p*p = 0 + p*p (witness p on congL: 0 = (p*p)+? no).
   cong p A 0 = Disj (Ex k. 0 = A + p*k)(Ex k. A = 0 + p*k).  Use RIGHT: A=p*p = 0 + p*p, witness p.
   need oeq (p*p) (add 0 (mult p p)) : 0 + p*p = p*p (add_0) sym. *)
val cong_pp_zero =
  let val a0 = add0_b (mult pB pB)            (* 0 + p*p = p*p *)
      (* congR body at k=p : oeq (p*p) (add 0 (mult p p)) ; but we need add 0 (mult p p), and the
         general congR uses mult m k = mult p p. We want A = p*p, 0 = b, witness p: A = b + p*k => p*p = 0 + p*p. *)
      val rhs = oeqSym_b a0                     (* p*p = 0 + p*p *)
      (* cong_introR (m=p, a=p*p, b=0, w=p): hyp oeq a (add b (mult m w)) = oeq (p*p) (add 0 (mult p p)) *)
  in cong_introR_b (pB, mult pB pB, ZeroC, pB) rhs end;
val () = out ("PB_T9_CONGPP hyps="^Int.toString(length(Thm.hyps_of cong_pp_zero))^"\n");

(* ---- bound : le (Suc m) k ==> le (Suc(mult(bidx k)(bidx k))) (mult p p)  [needs bidx k <= m < p] ----
   bidx k = subv k (Suc m).  We need le (bidx k) m.  From le (Suc m) k and k <= p (k < Suc p):
     k = (Suc m) + bidx k [sub_recover: (k-(Suc m))+(Suc m) = k], so bidx k = k - (Suc m).
     With k <= p = 2m+1 : bidx k <= 2m+1 - (m+1) = m.  We carry hltk : lt k (Suc p) for this.
   Actually we prove a helper bidx_le_m : le (Suc m) k ==> lt k (Suc p) ==> le (bidx k) m. ---- *)
(* bidx_le_m : from k = (Suc m) + (bidx k) [sub_recover] and k < Suc p = Suc(Suc(m+m)),
   so (Suc m)+(bidx k) <= Suc(m+m) (since k <= Suc(m+m)=p ... wait k<Suc p means k<=p=Suc(m+m)).
   (Suc m)+(bidx k) = k <= p = Suc(m+m).  Cancel: le (bidx k) m.
   We have le (Suc m) k (so sub_recover applies), and le k p (from lt k (Suc p) => le k p). *)
(* le_radd_cancel_b : le (add a w)(add b w) ==> le a b *)
val add_Suc_right_vB = varify add_Suc_right;
fun addSucr_b2 (m,n) = beta_norm (Drule.infer_instantiate ctxtB [(("m",0), ctermB m),(("n",0), ctermB n)] add_Suc_right_vB);
val add_left_cancel_vB = varify add_left_cancel;
fun add_left_cancel_b (m,a,b) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB
      [(("m",0), ctermB m),(("a",0), ctermB a),(("b",0), ctermB b)] add_left_cancel_vB)) h;
fun le_radd_cancel_b (aT, bT, wT) hle =   (* le (a+w)(b+w) => le a b *)
  let val leBody = Abs("e", natT, oeq (add bT wT) (add (add aT wT) (Bound 0)))
      fun afterE e (heq:thm) =   (* heq : (b+w) = ((a+w)+e) *)
        let (* (a+w)+e = (a+e)+w : assoc + comm.  (a+w)+e = a+(w+e)=a+(e+w)=(a+e)+w *)
            val e1 = addassoc_b (aT, wT, e)            (* (a+w)+e = a+(w+e) *)
            val e2 = addcomm_b (wT, e)                  (* w+e = e+w *)
            val e3 = add_cong_r_b (aT, add wT e, add e wT) e2  (* a+(w+e) = a+(e+w) *)
            val e4 = addassoc_b (aT, e, wT)             (* (a+e)+w = a+(e+w) *)
            val chain = oeqTrans_b (oeqTrans_b (e1, e3), oeqSym_b e4)  (* (a+w)+e = (a+e)+w *)
            val bw_eq = oeqTrans_b (heq, chain)         (* (b+w) = (a+e)+w *)
            (* commute both: w+b = w+(a+e) ; cancel w => b = a+e => le a b witness e *)
            val cb = addcomm_b (bT, wT)                 (* (b+w) = (w+b) *)
            val ca = addcomm_b (add aT e, wT)            (* ((a+e)+w) = (w+(a+e)) *)
            val wb = oeqTrans_b (oeqTrans_b (oeqSym_b cb, bw_eq), ca)  (* (w+b) = (w+(a+e)) *)
            val beq = add_left_cancel_b (wT, bT, add aT e) wb   (* b = a+e *)
        in le_intro_b (aT, bT, e) beq end
  in exE_b (leBody, le aT bT) hle "e_lrc" natT afterE end;

fun bidx_le_m (kT) hle hltk =   (* hle : le (Suc m) k ; hltk : lt k (Suc p) ; result le (bidx k) m *)
  let
    val bk = bidx kT
    val rec0 = sub_recover_b (kT, suc mB) hle    (* oeq (add bk (Suc m)) k *)
    val lekp = le_from_lt_suc (kT, pB) hltk      (* le k p *)
    val rec0s = oeqSym_b rec0                     (* k = bk + (Suc m) *)
    val leSum = oeq_rw_b2 (Term.lambda (Free("zbk1",natT)) (le (Free("zbk1",natT)) pB), kT, add bk (suc mB)) rec0s lekp
                                                  (* le (bk + (Suc m)) p *)
    val leSum2 = oeq_rw_b2 (Term.lambda (Free("zbk2",natT)) (le (add bk (suc mB)) (Free("zbk2",natT))), pB, suc (add mB mB)) hodd leSum
                                                  (* le (bk+(Suc m)) (Suc(m+m)) *)
    (* Suc(m+m) = m + Suc m : add_Suc_right m m : m + Suc m = Suc(m+m); sym *)
    val msr = addSucr_b2 (mB, mB)                 (* m + Suc m = Suc(m+m) *)
    val leSum3 = oeq_rw_b2 (Term.lambda (Free("zbk3",natT)) (le (add bk (suc mB)) (Free("zbk3",natT))), suc (add mB mB), add mB (suc mB)) (oeqSym_b msr) leSum2
                                                  (* le (bk+(Suc m)) (m + Suc m) *)
    (* le_radd_cancel with w = Suc m : le bk m *)
    val r = le_radd_cancel_b (bk, mB, suc mB) leSum3   (* le bk m *)
  in r end;
val () = out "PB_T9_BIDXLEM_OK\n";

val () = out "PB_T9_PARTIAL_DONE\n";

(* ============================================================================
   PART B TEST 10: the bound + bval_cong.
   ============================================================================ *)
val () = out "PB_T10_BEGIN\n";

val mult_Suc_vB2 = varify mult_Suc;
fun multSuc_b (m,n) = beta_norm (Drule.infer_instantiate ctxtB [(("m",0), ctermB m),(("n",0), ctermB n)] mult_Suc_vB2);
(* mult_Suc : (Suc m)*n = n + m*n ; mult_Suc_right (multSucr_b) : n*(Suc m) = n + n*m *)

(* identity : oeq (mult (suc x)(suc x)) (add (suc (mult x x)) (add x x)) *)
fun sq_suc_identity xT =
  let
    (* (Suc x)*(Suc x) = (Suc x) + x*(Suc x)   [mult_Suc with m:=x, n:=Suc x] *)
    val s1 = multSuc_b (xT, suc xT)             (* (Suc x)*(Suc x) = (Suc x) + x*(Suc x) *)
    (* x*(Suc x) = x + x*x   [mult_Suc_right with n:=x, m:=x] *)
    val s2 = multSucr_b (xT, xT)                (* x*(Suc x) = x + x*x *)
    val s3 = add_cong_r_b (suc xT, mult xT (suc xT), add xT (mult xT xT)) s2   (* (Suc x)+x*(Suc x) = (Suc x)+(x + x*x) *)
    val lhs = oeqTrans_b (s1, s3)               (* (Suc x)*(Suc x) = (Suc x)+(x+x*x) *)
    (* now reshape (Suc x)+(x+x*x) = Suc(x*x) + (x+x) :
         (Suc x)+(x+x*x) = Suc(x+(x+x*x)) [add_Suc] = Suc((x+x)+x*x) [assoc]
         Suc((x+x)+x*x) = Suc(x*x + (x+x)) [comm inside] = (Suc(x*x)) + (x+x) [add_Suc back] *)
    val a1 = addSuc_b (xT, add xT (mult xT xT))  (* (Suc x)+(x+x*x) = Suc(x+(x+x*x)) *)
    val a2 = addassoc_b (xT, xT, mult xT xT)     (* (x+x)+x*x = x+(x+x*x) ; we want x+(x+x*x) = (x+x)+x*x => sym *)
    val a2s= oeqSym_b a2                          (* x+(x+x*x) = (x+x)+x*x *)
    val a2c= Suc_cong_b a2s                       (* Suc(x+(x+x*x)) = Suc((x+x)+x*x) *)
    (* Suc((x+x)+x*x) : reorder to Suc(x*x+(x+x)) [comm] *)
    val cz = addcomm_b (add xT xT, mult xT xT)    (* (x+x)+x*x = x*x+(x+x) *)
    val czc= Suc_cong_b cz                        (* Suc((x+x)+x*x) = Suc(x*x+(x+x)) *)
    (* Suc(x*x+(x+x)) = Suc(x*x) + (x+x)  [add_Suc back: Suc(a+b)=Suc a + b? add_Suc: (Suc a)+b = Suc(a+b), sym] *)
    val a3 = addSuc_b (mult xT xT, add xT xT)     (* (Suc(x*x))+(x+x) = Suc(x*x+(x+x)) *)
    val a3s= oeqSym_b a3                           (* Suc(x*x+(x+x)) = (Suc(x*x))+(x+x) *)
    val rhsChain = oeqTrans_b (oeqTrans_b (oeqTrans_b (a1, a2c), czc), a3s)  (* (Suc x)+(x+x*x) = (Suc(x*x))+(x+x) *)
  in oeqTrans_b (lhs, rhsChain) end;   (* (Suc x)*(Suc x) = (Suc(x*x))+(x+x) *)
val () =
  let val r = sq_suc_identity (Free("xsq",natT))
  in out ("PB_T10_SQSUC hyps="^Int.toString(length(Thm.hyps_of r))^"\n") end;

(* le_Suc_sq : le (Suc(mult x x)) (mult (suc x)(suc x))   [witness x+x via identity] *)
fun le_Suc_sq xT =
  let val idn = sq_suc_identity xT    (* (Suc x)*(Suc x) = Suc(x*x) + (x+x) *)
  in le_intro_b (suc (mult xT xT), mult (suc xT)(suc xT), add xT xT) idn end;

(* sq_le_mono_b : le a b ==> le (a*a)(b*b)  via mult_le_mono twice + comm *)
fun sq_le_mono_b (aT,bT) hle =
  let val l1 = mult_le_mono_b (aT, aT, bT) hle    (* le (a*a)(a*b) *)
      val l2 = mult_le_mono_b (bT, aT, bT) hle    (* le (b*a)(b*b) *)
      (* a*b = b*a ; rewrite le (a*a)(a*b) -> le (a*a)(b*a) *)
      val ab = multcomm_b (aT, bT)                 (* a*b = b*a *)
      val l1' = oeq_rw_b2 (Term.lambda (Free("zsm",natT)) (le (mult aT aT) (Free("zsm",natT))), mult aT bT, mult bT aT) ab l1   (* le (a*a)(b*a) *)
      val r = le_trans_b (mult aT aT, mult bT aT, mult bT bT) l1' l2   (* le (a*a)(b*b) *)
  in r end;

(* the bound : le (Suc m) k ==> lt k (Suc p) ==> le (Suc(mult (bidx k)(bidx k)))(mult p p) *)
fun bval_bound (kT) hle hltk =
  let
    val bk = bidx kT
    val lebm = bidx_le_m kT hle hltk            (* le bk m *)
    (* lt bk p : le bk m, lt m p => le (Suc bk)(Suc m) (le_suc_mono), le (Suc m) p (=lt m p) => le (Suc bk) p *)
    val leSbkSm = le_suc_mono_b (bk, mB) lebm   (* le (Suc bk)(Suc m) *)
    val ltmp = m_lt_p                            (* lt m p = le (Suc m) p, but carries hyp odd *)
    val leSbkp = le_trans_b (suc bk, suc mB, pB) leSbkSm ltmp   (* le (Suc bk) p *)
    (* le (Suc bk)*(Suc bk) <= p*p  [sq_le_mono] *)
    val leSqSq = sq_le_mono_b (suc bk, pB) leSbkp   (* le ((Suc bk)*(Suc bk))(p*p) *)
    (* le (Suc(bk*bk))((Suc bk)*(Suc bk)) [le_Suc_sq] *)
    val leLow = le_Suc_sq bk                     (* le (Suc(bk*bk))((Suc bk)*(Suc bk)) *)
    val r = le_trans_b (suc (mult bk bk), mult (suc bk)(suc bk), mult pB pB) leLow leSqSq
  in r end;   (* le (Suc(bk*bk))(p*p) *)
val () = out "PB_T10_BOUND_READY\n";

(* bval_cong : le (Suc m) k ==> lt k (Suc p) ==>
     cong p (add (fdec k)(Suc(mult (bidx k)(bidx k)))) Zero
   Proof: fdec k = bval k = subv (p*p)(Suc(bk*bk))   [fdecB]
          sub_recover : le (Suc(bk*bk))(p*p) ==> oeq (add (bval k)(Suc(bk*bk))) (p*p)
          rewrite bval k <- fdec k (fdecB sym), then cong p (add (fdec k)(Suc(bk*bk))) (p*p),
          and cong p (p*p) 0 => cong p (...) 0 via oeq + cong_trans. *)
fun bval_cong (kT) hle hltk =
  let
    val bk = bidx kT
    val hfd = fdecB_b kT hle                     (* oeq (fdec k)(bval k) ; bval k = subv (p*p)(Suc(bk*bk)) *)
    val bnd = bval_bound kT hle hltk             (* le (Suc(bk*bk))(p*p) *)
    val rec0 = sub_recover_b (mult pB pB, suc (mult bk bk)) bnd
                                                 (* oeq (add (subv (p*p)(Suc(bk*bk))) (Suc(bk*bk))) (p*p) *)
    (* subv (p*p)(Suc(bk*bk)) is exactly bval k.  rewrite to fdec k via hfd sym in the sum's first slot *)
    val sumEq = oeq_rw_b2 (Term.lambda (Free("zbv1",natT)) (oeq (add (Free("zbv1",natT)) (suc (mult bk bk))) (mult pB pB)),
                            bval kT, fdec kT) (oeqSym_b hfd) rec0
                                                 (* oeq (add (fdec k)(Suc(bk*bk))) (p*p) *)
    (* cong p (add (fdec k)(Suc(bk*bk))) (p*p)  via cong from oeq (witness 0 on congL) then cong_trans with cong p (p*p) 0 *)
    (* cong from oeq : oeq X Y => cong p X Y ; build cong_introL (p, X, Y, 0): need oeq Y (add X (p*0))
       i.e. Y = X + 0 = X.  We have X = Y (sumEq); so Y = X.  cong_introL needs oeq Y (X + p*0). *)
    val X = add (fdec kT)(suc (mult bk bk))
    val Y = mult pB pB
    (* oeq Y (add X (mult p 0)) : add X (p*0) = X + 0 = X = Y(sym sumEq). *)
    val p0 = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB pB)] (varify mult_0_right))  (* p*0 = 0 *)
    val xp0 = add_cong_r_b (X, mult pB ZeroC, ZeroC) p0   (* X + p*0 = X + 0 *)
    val x0  = add0r_b X                                    (* X + 0 = X *)
    val xpX = oeqTrans_b (xp0, x0)                         (* X + p*0 = X *)
    val Yeq = oeqTrans_b (oeqSym_b sumEq, oeqSym_b xpX)    (* Y = X + p*0 *)
    val congXY = cong_introL_b (pB, X, Y, ZeroC) Yeq       (* cong p X Y = cong p (...) (p*p) *)
    val r = cong_trans_b (pB, X, Y, ZeroC) congXY cong_pp_zero   (* cong p X 0 *)
  in r end;
val () = out "PB_T10_DONE\n";

(* ============================================================================
   PART B TEST 11: FINAL ASSEMBLY.  Collision -> 4-case decode ->
   cong p (a*a+b*b+1) 0 -> compose with pm_from_cong -> primemult existential.
   ============================================================================ *)
val () = out "PB_T11_BEGIN\n";

(* ---- cong_add_b, divmod_id_b, cong_of_rmod_b ---- *)
val cong_add_vB = varify cong_add;
fun cong_add_b (m,a,a2,b,b2) h1 h2 = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB
      [(("m",0), ctermB m),(("a",0), ctermB a),(("a2",0), ctermB a2),(("b",0), ctermB b),(("b2",0), ctermB b2)] cong_add_vB)) h1) h2;
val cong_refl_vB = varify cong_refl;
fun cong_refl_b (m,a) = beta_norm (Drule.infer_instantiate ctxtB [(("m",0), ctermB m),(("a",0), ctermB a)] cong_refl_vB);
val divmod_id_vB = varify divmod_id_ax;
fun divmod_id_b (ct,dt) hpos = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB
      [(("c_dm",0), ctermB ct),(("d_dm",0), ctermB dt)] divmod_id_vB)) hpos;
(* cong_x_rmod_b / cong_of_rmod_b *)
fun cong_x_rmod_b (xP, pP) hpos =
  let val did = divmod_id_b (xP, pP) hpos
      val comm = addcomm_b (mult pP (rdivv xP pP), rmodv xP pP)
      val x_eq = oeqTrans_b (did, comm)
      val RAbs = Abs("k", natT, oeq xP (add (rmodv xP pP) (mult pP (Bound 0))))
      val exThm = exI_b RAbs (rdivv xP pP) x_eq
  in disjI2_b (mkEx (Abs("k",natT, oeq (rmodv xP pP) (add xP (mult pP (Bound 0))))),
               mkEx (Abs("k",natT, oeq xP (add (rmodv xP pP) (mult pP (Bound 0)))))) exThm end;
fun cong_of_rmod_b (xP, yP, pP) hpos heq =
  let val cx = cong_x_rmod_b (xP, pP) hpos
      val cy = cong_x_rmod_b (yP, pP) hpos
      val cy_s = cong_sym_b (pP, yP, rmodv yP pP) cy
      val zc = Free("zcrb", natT)
      val P = Term.lambda zc (cong pP xP zc)
      val cx2 = oeq_rw_b2 (P, rmodv xP pP, rmodv yP pP) heq cx
      val res = cong_trans_b (pP, xP, rmodv yP pP, yP) cx2 cy_s
  in res end;
(* sq_inj_mod / pm_from_cong / four_sq_witness are GR-context; their inputs (no fdec) work. *)
val () = out "PB_T11_CONGOFRMOD_OK\n";

(* ---- THE COLLISION ---- *)
val nB7 = suc pB;   (* p+1 *)
(* lt p (Suc p) *)
val ltp_Sp = lt_suc_b pB;   (* lt p (Suc p) *)
(* lt p (llen (bres (Suc p))) via breslen_n sym *)
val ltp_len =
  let val zl = Free("zce_b", natT)
      val Plt = Term.lambda zl (lt pB zl)
  in oeq_rw_b2 (Plt, nB7, llen (bres nB7)) (oeqSym_b breslen_n) ltp_Sp end;
(* bresmem at n = Suc p, with 0<p discharged *)
val (kbm, bresmem) = bresmem_lt_p_g hposB;   (* carries hyp? hposB is from hodd assume; bresmem has hyp on hodd *)
val bresmem_n = beta_norm (Thm.forall_elim (ctermB nB7) (Thm.forall_intr (ctermB kbm) bresmem));
(* list_pigeonhole on ctxtB *)
val list_pigeonhole_vB = varify list_pigeonhole;
fun list_pigeonhole_b (RLt, kt) hbnd hlt =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB
        [(("RL_ph",0), ctermB RLt),(("k_ph",0), ctermB kt)] list_pigeonhole_vB)
      val ef = Free("e_ph", natT)
      val bndT = mkForall (Term.lambda ef (mkImp (lmem ef RLt) (lt ef kt)))
      val s1 = mp_b (bndT, mkImp (lt kt (llen RLt)) (neg (lnodup RLt))) inst hbnd
  in mp_b (lt kt (llen RLt), neg (lnodup RLt)) s1 hlt end;
val collNeg = list_pigeonhole_b (bres nB7, pB) bresmem_n ltp_len;   (* neg (lnodup (bres (Suc p))) *)
(* dup_bres at n = Suc p *)
val (kdb, dupthm) = dup_bres;
val dup_n = beta_norm (Thm.forall_elim (ctermB nB7) (Thm.forall_intr (ctermB kdb) dupthm));
val collExists = mp_b (neg (lnodup (bres nB7)), collPairB nB7) dup_n collNeg;
val () = out "PB_T11_COLLISION_OK\n";

(* ---- the FINAL goal predicate : EX a b. (le a m /\ le b m) /\ cong p (a*a+b*b+1) 0 ---- *)
fun targetCong a b = cong pB (add (add (mult a a)(mult b b)) (suc ZeroC)) ZeroC;
fun targetBody a b = mkConj (mkConj (le a mB)(le b mB)) (targetCong a b);
fun targetEx () =
  mkEx (Term.lambda (Free("a_tg",natT))
    (mkEx (Term.lambda (Free("b_tg",natT))
      (targetBody (Free("a_tg",natT)) (Free("b_tg",natT))))));
fun mkTargetExists (a,b) hleA hleB hcong =
  let val hbody = conjI_b (mkConj (le a mB)(le b mB), targetCong a b) (conjI_b (le a mB, le b mB) hleA hleB) hcong
      val Pb = Term.lambda (Free("b_tg",natT)) (targetBody a (Free("b_tg",natT)))
      val e1 = exI_b Pb b hbody
      val Pa = Term.lambda (Free("a_tg",natT))
                 (mkEx (Term.lambda (Free("b_tg",natT)) (targetBody (Free("a_tg",natT)) (Free("b_tg",natT)))))
  in exI_b Pa a e1 end;
val goalT = jT (targetEx ());

(* ---- helper: cong p (Suc X)(Suc Y) ==> cong p X Y  (Suc = +1, radd_cancel with w = Suc 0
   after rewriting Suc X = X + Suc 0). ---- *)
fun cong_Suc_cancel (xT,yT) hc =   (* hc : cong p (Suc X)(Suc Y) *)
  let (* Suc X = X + Suc 0 : add_Suc_right X 0 : X + Suc 0 = Suc(X+0)=Suc X; sym *)
      val ax = addSucr_b2 (xT, ZeroC)   (* X + Suc 0 = Suc(X+0) *)
      val ax2= Suc_cong_b (add0r_b xT)  (* Suc(X+0) = Suc X *)
      val axc= oeqTrans_b (ax, ax2)     (* X + Suc 0 = Suc X *)
      val ay = addSucr_b2 (yT, ZeroC)
      val ay2= Suc_cong_b (add0r_b yT)
      val ayc= oeqTrans_b (ay, ay2)     (* Y + Suc 0 = Suc Y *)
      (* rewrite Suc X -> X + Suc 0 and Suc Y -> Y + Suc 0 in hc *)
      val hc1 = oeq_rw_b2 (Term.lambda (Free("zcs1",natT)) (cong pB (Free("zcs1",natT)) (suc yT)), suc xT, add xT (suc ZeroC)) (oeqSym_b axc) hc
      val hc2 = oeq_rw_b2 (Term.lambda (Free("zcs2",natT)) (cong pB (add xT (suc ZeroC)) (Free("zcs2",natT))), suc yT, add yT (suc ZeroC)) (oeqSym_b ayc) hc1
      (* cong p (X + Suc 0)(Y + Suc 0) => cong p X Y *)
  in cong_radd_cancel_b (pB, xT, yT, suc ZeroC) hc2 end;

val () = out "PB_T11_TARGET_READY\n";

(* ---- the per-(c1,c2) decode body : given the collision conjuncts, produce goalT.
   hltc1 : lt c1 (Suc p), hltc2 : lt c2 (Suc p), hneq : neg(oeq c1 c2),
   hgreq : oeq (fres c1)(fres c2).  ---- *)
fun decodeBody (c1, c2) hltc1 hltc2 hneq hgreq =
  let
    (* cong p (fdec c1)(fdec c2) *)
    val congFdec = cong_of_rmod_b (fdec c1, fdec c2, pB) hposB hgreq   (* cong p (fdec c1)(fdec c2) *)
    (* em on lt c1 (Suc m), lt c2 (Suc m) *)
    val em1 = em_b (lt c1 (suc mB))
    val em2 = em_b (lt c2 (suc mB))
    (* ===== 4 cases ===== *)
    (* helper to make the AA-style contradiction usable: given oeq c1 c2 -> goalT (via oFalse) *)
    fun fromContra (heqc : thm) =   (* heqc : oeq c1 c2 *)
      let val fls = mp_b (oeq c1 c2, oFalseC) hneq heqc
      in Thm.implies_elim (oFalse_elim_b (targetEx ())) fls end
    (* CASE c1 in A (lt c1 (Suc m)) *)
    val caseA1 =
      let val hA1 = Thm.assume (ctermB (jT (lt c1 (suc mB))))
          val leC1m = le_from_lt_suc (c1, mB) hA1   (* le c1 m *)
          val fdc1  = fdecA_b c1 hA1                 (* oeq (fdec c1)(c1*c1) *)
          (* sub-case c2 *)
          val caseA1A2 =
            let val hA2 = Thm.assume (ctermB (jT (lt c2 (suc mB))))
                val leC2m = le_from_lt_suc (c2, mB) hA2
                val fdc2  = fdecA_b c2 hA2            (* oeq (fdec c2)(c2*c2) *)
                (* cong p (c1*c1)(c2*c2) : rewrite fdec c1->c1*c1, fdec c2->c2*c2 in congFdec *)
                val cg1 = oeq_rw_b2 (Term.lambda (Free("zaa1",natT)) (cong pB (Free("zaa1",natT)) (fdec c2)), fdec c1, mult c1 c1) fdc1 congFdec
                val cg2 = oeq_rw_b2 (Term.lambda (Free("zaa2",natT)) (cong pB (mult c1 c1) (Free("zaa2",natT))), fdec c2, mult c2 c2) fdc2 cg1
                                                     (* cong p (c1*c1)(c2*c2) *)
                (* lt (c1+c2) p : c1,c2 <= m, c1+c2 <= m+m < p.  le (c1+c2)(m+m) then lt (m+m) p.
                   le c1 m, le c2 m => le (c1+c2)(m+m): add monotone.  Then lt (m+m)(Suc(m+m))=lt(m+m)p. *)
                val leSum1 = (* le (c1+c2)(m+c2) via mono on first *)
                  (* le c1 m => le (c1+c2)(m+c2): add_right? use le_intro from witness.  Easier:
                     le c1 m witness e1: m=c1+e1.  m+c2 = (c1+e1)+c2 = (c1+c2)+e1 => le (c1+c2)(m+c2). *)
                  let val leBody = Abs("e",natT, oeq mB (add c1 (Bound 0)))
                      fun aft e (he:thm) =  (* he: m = c1+e *)
                        let val mc2 = add_cong_l_b (mB, add c1 e, c2) he   (* m+c2 = (c1+e)+c2 *)
                            val re  = addassoc_b (c1, e, c2)               (* (c1+e)+c2 = c1+(e+c2) *)
                            val ce  = addcomm_b (e, c2)                     (* e+c2 = c2+e *)
                            val rc  = add_cong_r_b (c1, add e c2, add c2 e) ce  (* c1+(e+c2)=c1+(c2+e) *)
                            val ra  = addassoc_b (c1, c2, e)               (* (c1+c2)+e = c1+(c2+e); sym *)
                            val chain = oeqTrans_b (oeqTrans_b (oeqTrans_b (mc2, re), rc), oeqSym_b ra)
                                                                           (* m+c2 = (c1+c2)+e *)
                        in le_intro_b (add c1 c2, add mB c2, e) chain end
                  in exE_b (leBody, le (add c1 c2)(add mB c2)) leC1m "e_aa1" natT aft end
                val leSum2 = (* le (m+c2)(m+m) via le c2 m *)
                  let val leBody = Abs("e",natT, oeq mB (add c2 (Bound 0)))
                      fun aft e (he:thm) =  (* he: m = c2+e *)
                        let val mm = add_cong_r_b (mB, c2, add c2 e)  (* hmm wrong: want m+m = (m+c2)+e *)
                            (* m+m: rewrite 2nd m = c2+e: m+m = m+(c2+e) [add_cong_r he] = (m+c2)+e [assoc sym] *)
                            val r1 = add_cong_r_b (mB, mB, add c2 e) he   (* m+m = m+(c2+e) *)
                            val r2 = addassoc_b (mB, c2, e)               (* (m+c2)+e = m+(c2+e); sym *)
                            val chain = oeqTrans_b (r1, oeqSym_b r2)      (* m+m = (m+c2)+e *)
                        in le_intro_b (add mB c2, add mB mB, e) chain end
                  in exE_b (leBody, le (add mB c2)(add mB mB)) leC2m "e_aa2" natT aft end
                val leSumMM = le_trans_b (add c1 c2, add mB c2, add mB mB) leSum1 leSum2  (* le (c1+c2)(m+m) *)
                (* lt (m+m) p : p = Suc(m+m) so lt (m+m)(Suc(m+m)) [lt_suc] then rewrite Suc(m+m)->p *)
                val ltmm = lt_suc_b (add mB mB)   (* lt (m+m)(Suc(m+m)) *)
                val ltmmp = oeq_rw_b2 (Term.lambda (Free("zaa3",natT)) (lt (add mB mB) (Free("zaa3",natT))), suc (add mB mB), pB) (oeqSym_b hodd) ltmm  (* lt (m+m) p *)
                (* lt (c1+c2) p : le (c1+c2)(m+m), lt (m+m) p => le (Suc(c1+c2))(Suc(m+m)) then le (Suc(c1+c2)) p *)
                val leS = le_suc_mono_b (add c1 c2, add mB mB) leSumMM  (* le (Suc(c1+c2))(Suc(m+m)) *)
                val ltSumP = le_trans_b (suc (add c1 c2), suc (add mB mB), pB) leS ltmmp  (* le (Suc(c1+c2)) p = lt (c1+c2) p *)
                (* sq_inj_mod : prime2 p ==> lt (c1+c2) p ==> cong p (c1*c1)(c2*c2) ==> oeq c1 c2 *)
                val heqc = sq_inj_mod (pB, c1, c2) hprime ltSumP cg2   (* oeq c1 c2 *)
            in Thm.implies_intr (ctermB (jT (lt c2 (suc mB)))) (fromContra heqc) end
          (* sub-case c2 in B (le (Suc m) c2) : CROSS AB.  a=c1, b=bidx c2. *)
          val caseA1B2 =
            let val hB2 = Thm.assume (ctermB (jT (neg (lt c2 (suc mB)))))
                (* neg (lt c2 (Suc m)) => le (Suc m) c2 *)
                val leSmC2 = nlt_le_d (c2, suc mB) hB2   (* le (Suc m) c2 *)
                val b2 = bidx c2
                val fdc2 = fdecB_b c2 leSmC2          (* oeq (fdec c2)(bval c2) *)
                (* cong p (c1*c1)(bval c2) *)
                val cg1 = oeq_rw_b2 (Term.lambda (Free("zab1",natT)) (cong pB (Free("zab1",natT)) (fdec c2)), fdec c1, mult c1 c1) fdc1 congFdec
                val cg2 = oeq_rw_b2 (Term.lambda (Free("zab2",natT)) (cong pB (mult c1 c1) (Free("zab2",natT))), fdec c2, bval c2) fdc2 cg1
                                                       (* cong p (c1*c1)(bval c2) *)
                (* but fdec c2 = bval c2 only up to the fdecB form; bval c2 = subv (p*p)(Suc(b2*b2)).
                   bval_cong c2 : cong p (add (fdec c2)(Suc(b2*b2))) 0 -- uses fdec c2, NOT bval c2. *)
                val bvc = bval_cong c2 leSmC2 hltc2    (* cong p (add (fdec c2)(Suc(b2*b2))) 0 *)
                (* From cg1 (cong p (c1*c1)(fdec c2)) add (Suc(b2*b2)) both sides:
                   cong p (c1*c1 + Suc(b2*b2))(fdec c2 + Suc(b2*b2)).  Use cg1 NOT cg2. *)
                val addRefl = cong_refl_b (pB, suc (mult b2 b2))   (* cong p (Suc(b2*b2))(Suc(b2*b2)) *)
                val cgAdd = cong_add_b (pB, mult c1 c1, fdec c2, suc (mult b2 b2), suc (mult b2 b2)) cg1 addRefl
                                                       (* cong p (c1*c1 + Suc(b2*b2))(fdec c2 + Suc(b2*b2)) *)
                val cgZero = cong_trans_b (pB, add (mult c1 c1)(suc (mult b2 b2)), add (fdec c2)(suc (mult b2 b2)), ZeroC) cgAdd bvc
                                                       (* cong p (c1*c1 + Suc(b2*b2)) 0 *)
                (* reshape c1*c1 + Suc(b2*b2) = (c1*c1 + b2*b2) + Suc 0 :
                   add_Suc_right (c1*c1)(b2*b2): (c1*c1) + Suc(b2*b2) = Suc((c1*c1)+(b2*b2));
                   (c1*c1+b2*b2) + Suc 0 = Suc((c1*c1+b2*b2)+0)=Suc(c1*c1+b2*b2).  equal. *)
                val r1 = addSucr_b2 (mult c1 c1, mult b2 b2)   (* c1*c1 + Suc(b2*b2) = Suc(c1*c1 + b2*b2) *)
                val r2 = addSucr_b2 (add (mult c1 c1)(mult b2 b2), ZeroC)  (* (c1*c1+b2*b2)+Suc 0 = Suc((c1*c1+b2*b2)+0) *)
                val r3 = Suc_cong_b (add0r_b (add (mult c1 c1)(mult b2 b2)))  (* Suc((c1*c1+b2*b2)+0) = Suc(c1*c1+b2*b2) *)
                val r23= oeqTrans_b (r2, r3)            (* (c1*c1+b2*b2)+Suc 0 = Suc(c1*c1+b2*b2) *)
                val reshape = oeqTrans_b (r1, oeqSym_b r23)  (* c1*c1+Suc(b2*b2) = (c1*c1+b2*b2)+Suc 0 *)
                val cgTarget = oeq_rw_b2 (Term.lambda (Free("zab3",natT)) (cong pB (Free("zab3",natT)) ZeroC),
                                           add (mult c1 c1)(suc (mult b2 b2)), add (add (mult c1 c1)(mult b2 b2))(suc ZeroC)) reshape cgZero
                                                       (* cong p ((c1*c1+b2*b2)+Suc 0) 0 = targetBody c1 b2 *)
                val leB2m = bidx_le_m c2 leSmC2 hltc2   (* le b2 m *)
                val ex = mkTargetExists (c1, b2) leC1m leB2m cgTarget
            in Thm.implies_intr (ctermB (jT (neg (lt c2 (suc mB))))) ex end
      in Thm.implies_intr (ctermB (jT (lt c1 (suc mB))))
           (disjE_b (lt c2 (suc mB), neg (lt c2 (suc mB)), targetEx ()) em2 caseA1A2 caseA1B2) end
    (* CASE c1 in B (neg (lt c1 (Suc m))) *)
    val caseB1 =
      let val hB1 = Thm.assume (ctermB (jT (neg (lt c1 (suc mB)))))
          val leSmC1 = nlt_le_d (c1, suc mB) hB1   (* le (Suc m) c1 *)
          val b1 = bidx c1
          val fdc1 = fdecB_b c1 leSmC1             (* oeq (fdec c1)(bval c1) *)
          val bvc1 = bval_cong c1 leSmC1 hltc1     (* cong p (add (fdec c1)(Suc(b1*b1))) 0 *)
          (* sub-case c2 in A : CROSS BA.  a=c2, b=b1. *)
          val caseB1A2 =
            let val hA2 = Thm.assume (ctermB (jT (lt c2 (suc mB))))
                val leC2m = le_from_lt_suc (c2, mB) hA2
                val fdc2  = fdecA_b c2 hA2           (* oeq (fdec c2)(c2*c2) *)
                (* congFdec : cong p (fdec c1)(fdec c2).  sym -> cong p (fdec c2)(fdec c1). *)
                val cgS = cong_sym_b (pB, fdec c1, fdec c2) congFdec   (* cong p (fdec c2)(fdec c1) *)
                val cg1 = oeq_rw_b2 (Term.lambda (Free("zba1",natT)) (cong pB (Free("zba1",natT)) (fdec c1)), fdec c2, mult c2 c2) fdc2 cgS
                                                    (* cong p (c2*c2)(fdec c1) *)
                val addRefl = cong_refl_b (pB, suc (mult b1 b1))
                val cgAdd = cong_add_b (pB, mult c2 c2, fdec c1, suc (mult b1 b1), suc (mult b1 b1)) cg1 addRefl
                val cgZero = cong_trans_b (pB, add (mult c2 c2)(suc (mult b1 b1)), add (fdec c1)(suc (mult b1 b1)), ZeroC) cgAdd bvc1
                                                    (* cong p (c2*c2 + Suc(b1*b1)) 0 *)
                val r1 = addSucr_b2 (mult c2 c2, mult b1 b1)
                val r2 = addSucr_b2 (add (mult c2 c2)(mult b1 b1), ZeroC)
                val r3 = Suc_cong_b (add0r_b (add (mult c2 c2)(mult b1 b1)))
                val r23= oeqTrans_b (r2, r3)
                val reshape = oeqTrans_b (r1, oeqSym_b r23)
                val cgTarget = oeq_rw_b2 (Term.lambda (Free("zba3",natT)) (cong pB (Free("zba3",natT)) ZeroC),
                                           add (mult c2 c2)(suc (mult b1 b1)), add (add (mult c2 c2)(mult b1 b1))(suc ZeroC)) reshape cgZero
                val leB1m = bidx_le_m c1 leSmC1 hltc1   (* le b1 m *)
                val ex = mkTargetExists (c2, b1) leC2m leB1m cgTarget
            in Thm.implies_intr (ctermB (jT (lt c2 (suc mB)))) ex end
          (* sub-case c2 in B : BB.  reduce to cong p (b1*b1)(b2*b2) -> sq_inj -> b1=b2 -> c1=c2 -> contra *)
          val caseB1B2 =
            let val hB2 = Thm.assume (ctermB (jT (neg (lt c2 (suc mB)))))
                val leSmC2 = nlt_le_d (c2, suc mB) hB2   (* le (Suc m) c2 *)
                val b2 = bidx c2
                val fdc2 = fdecB_b c2 leSmC2             (* oeq (fdec c2)(bval c2) *)
                val bvc2 = bval_cong c2 leSmC2 hltc2     (* cong p (add (fdec c2)(Suc(b2*b2))) 0 *)
                (* cong p (fdec c1)(fdec c2).  Add Suc(b1*b1) and Suc(b2*b2)? We want cong p (b1*b1)(b2*b2).
                   From bvc1: fdec c1 ≡ -(Suc(b1*b1)) ; bvc2: fdec c2 ≡ -(Suc(b2*b2)).
                   congFdec: fdec c1 ≡ fdec c2.  So -(Suc(b1*b1)) ≡ -(Suc(b2*b2)) ; add Suc(b1*b1)+Suc(b2*b2):
                   Suc(b2*b2) ≡ Suc(b1*b1) (cancel via the two bval_cong).  Concretely:
                     cong p (fdec c1 + Suc(b1*b1)) 0     [bvc1]
                     cong p (fdec c2 + Suc(b1*b1)) (fdec c1 + Suc(b1*b1))  [cong_add congFdec(sym) refl]  = ... 0
                   Simpler: a ≡ b (congFdec) and a + s1 ≡ 0 (bvc1) and b + s2 ≡ 0 (bvc2).
                     a + s1 ≡ b + s1 (cong_add congFdec refl).  b+s1 ≡ 0? no.  Let me do:
                     from a≡b add s2: a+s2 ≡ b+s2 ≡ 0 (bvc2).  And a+s1 ≡ 0 (bvc1).
                     so a+s1 ≡ a+s2 (both 0, trans+sym).  cancel a (cong has add? need cong p (a+s1)(a+s2) -> cong p s1 s2).
                     cong (a+s1)(a+s2): a+s1=s1+a, a+s2=s2+a [comm], radd_cancel with w=a... but radd_cancel is on +w RIGHT.
                     comm to s1+a, s2+a then radd_cancel (s1,s2,a). *)
                val s1 = suc (mult b1 b1)
                val s2 = suc (mult b2 b2)
                (* a+s2 ≡ b+s2 : cong_add congFdec(a≡b) refl(s2) *)
                val reflS2 = cong_refl_b (pB, s2)
                val aS2_bS2 = cong_add_b (pB, fdec c1, fdec c2, s2, s2) congFdec reflS2  (* cong p (a+s2)(b+s2) *)
                (* b+s2 ≡ 0 (bvc2 with a=fdec c2=b) *)
                val aS2_zero = cong_trans_b (pB, add (fdec c1) s2, add (fdec c2) s2, ZeroC) aS2_bS2 bvc2  (* cong p (a+s2) 0 *)
                (* a+s1 ≡ 0 (bvc1) *)
                (* a+s1 ≡ a+s2 : trans (a+s1 ≡ 0)(0 ≡ a+s2) *)
                val aS2_z_sym = cong_sym_b (pB, add (fdec c1) s2, ZeroC) aS2_zero  (* cong p 0 (a+s2) *)
                val aS1_aS2 = cong_trans_b (pB, add (fdec c1) s1, ZeroC, add (fdec c1) s2) bvc1 aS2_z_sym  (* cong p (a+s1)(a+s2) *)
                (* comm: a+s1 = s1+a, a+s2 = s2+a *)
                val c_as1 = addcomm_b (fdec c1, s1)   (* a+s1 = s1+a *)
                val c_as2 = addcomm_b (fdec c1, s2)   (* a+s2 = s2+a *)
                val st1 = oeq_rw_b2 (Term.lambda (Free("zbb1",natT)) (cong pB (Free("zbb1",natT)) (add (fdec c1) s2)), add (fdec c1) s1, add s1 (fdec c1)) c_as1 aS1_aS2
                val st2 = oeq_rw_b2 (Term.lambda (Free("zbb2",natT)) (cong pB (add s1 (fdec c1)) (Free("zbb2",natT))), add (fdec c1) s2, add s2 (fdec c1)) c_as2 st1
                                                      (* cong p (s1 + a)(s2 + a) *)
                val congS1S2 = cong_radd_cancel_b (pB, s1, s2, fdec c1) st2   (* cong p s1 s2 = cong p (Suc(b1*b1))(Suc(b2*b2)) *)
                val congB1B2 = cong_Suc_cancel (mult b1 b1, mult b2 b2) congS1S2  (* cong p (b1*b1)(b2*b2) *)
                (* sq_inj_mod : need lt (b1+b2) p.  b1,b2 <= m => b1+b2 <= m+m < p. *)
                val leb1m = bidx_le_m c1 leSmC1 hltc1   (* le b1 m *)
                val leb2m = bidx_le_m c2 leSmC2 hltc2   (* le b2 m *)
                (* le (b1+b2)(m+m) then lt (m+m) p (as in AA) *)
                val leSum1 =
                  let val leBody = Abs("e",natT, oeq mB (add b1 (Bound 0)))
                      fun aft e (he:thm) =
                        let val mc2 = add_cong_l_b (mB, add b1 e, b2) he
                            val re  = addassoc_b (b1, e, b2)
                            val ce  = addcomm_b (e, b2)
                            val rc  = add_cong_r_b (b1, add e b2, add b2 e) ce
                            val ra  = addassoc_b (b1, b2, e)
                            val chain = oeqTrans_b (oeqTrans_b (oeqTrans_b (mc2, re), rc), oeqSym_b ra)
                        in le_intro_b (add b1 b2, add mB b2, e) chain end
                  in exE_b (leBody, le (add b1 b2)(add mB b2)) leb1m "e_bb1" natT aft end
                val leSum2 =
                  let val leBody = Abs("e",natT, oeq mB (add b2 (Bound 0)))
                      fun aft e (he:thm) =
                        let val r1 = add_cong_r_b (mB, mB, add b2 e) he
                            val r2 = addassoc_b (mB, b2, e)
                            val chain = oeqTrans_b (r1, oeqSym_b r2)
                        in le_intro_b (add mB b2, add mB mB, e) chain end
                  in exE_b (leBody, le (add mB b2)(add mB mB)) leb2m "e_bb2" natT aft end
                val leSumMM = le_trans_b (add b1 b2, add mB b2, add mB mB) leSum1 leSum2
                val ltmm = lt_suc_b (add mB mB)
                val ltmmp = oeq_rw_b2 (Term.lambda (Free("zbb3",natT)) (lt (add mB mB) (Free("zbb3",natT))), suc (add mB mB), pB) (oeqSym_b hodd) ltmm
                val leS = le_suc_mono_b (add b1 b2, add mB mB) leSumMM
                val ltSumP = le_trans_b (suc (add b1 b2), suc (add mB mB), pB) leS ltmmp
                val heqb = sq_inj_mod (pB, b1, b2) hprime ltSumP congB1B2   (* oeq b1 b2 *)
                (* b1 = b2 => c1 = c2 : c1 = b1 + Suc m (sub_recover), c2 = b2 + Suc m. *)
                val rec1 = sub_recover_b (c1, suc mB) leSmC1   (* (b1 + Suc m) = c1 *)
                val rec2 = sub_recover_b (c2, suc mB) leSmC2   (* (b2 + Suc m) = c2 *)
                val b1sm_b2sm = add_cong_l_b (b1, b2, suc mB) heqb   (* (b1 + Suc m) = (b2 + Suc m) *)
                val c1c2 = oeqTrans_b (oeqTrans_b (oeqSym_b rec1, b1sm_b2sm), rec2)   (* c1 = c2 *)
            in Thm.implies_intr (ctermB (jT (neg (lt c2 (suc mB))))) (fromContra c1c2) end
      in Thm.implies_intr (ctermB (jT (neg (lt c1 (suc mB)))))
           (disjE_b (lt c2 (suc mB), neg (lt c2 (suc mB)), targetEx ()) em2 caseB1A2 caseB1B2) end
  in disjE_b (lt c1 (suc mB), neg (lt c1 (suc mB)), targetEx ()) em1 caseA1 caseB1 end;

val () = out "PB_T11_DECODEBODY_READY\n";

(* ---- exE on c1, c2 from collExists, apply decodeBody ---- *)
val pigeonThm =
  let
    val Pc1 = Term.lambda (Free("c1_db",natT))
                (mkEx (Term.lambda (Free("c2_db",natT))
                  (mkConj (lt (Free("c1_db",natT)) nB7)
                    (mkConj (lt (Free("c2_db",natT)) nB7)
                      (mkConj (neg (oeq (Free("c1_db",natT)) (Free("c2_db",natT))))
                              (oeq (fres (Free("c1_db",natT))) (fres (Free("c2_db",natT)))))))))
    fun body1 c1 (h1:thm) =
      let val Pc2 = Term.lambda (Free("c2_db",natT))
                      (mkConj (lt c1 nB7)
                        (mkConj (lt (Free("c2_db",natT)) nB7)
                          (mkConj (neg (oeq c1 (Free("c2_db",natT))))
                                  (oeq (fres c1) (fres (Free("c2_db",natT)))))))
          fun body2 c2 (h2:thm) =
            let val A = lt c1 nB7; val B = lt c2 nB7
                val Cc = neg (oeq c1 c2); val D = oeq (fres c1)(fres c2)
                val hA = conjunct1_b (A, mkConj B (mkConj Cc D)) h2
                val r1 = conjunct2_b (A, mkConj B (mkConj Cc D)) h2
                val hB = conjunct1_b (B, mkConj Cc D) r1
                val r2 = conjunct2_b (B, mkConj Cc D) r1
                val hC = conjunct1_b (Cc, D) r2
                val hD = conjunct2_b (Cc, D) r2
            in decodeBody (c1, c2) hA hB hC hD end
      in exE_b (Pc2, targetEx ()) h1 "c2_pf" natT body2 end
  in exE_b (Pc1, targetEx ()) collExists "c1_pf" natT body1 end;
val () = out ("PB_T11_PIGEON hyps="^Int.toString(length(Thm.hyps_of pigeonThm))^"\n");
val () = out "L4_PIGEON_OK\n";

val () = out "PB_T11_DONE\n";

(* ============================================================================
   PART B TEST 12: bound lemma + compose with pm_from_cong -> primemult.
   ============================================================================ *)
val () = out "PB_T12_BEGIN\n";

(* ---- le_one_m : prime2 p ==> p = Suc(m+m) ==> le (Suc 0) m  (m >= 1) ----
   lt 1 p (prime2) => lt 1 (Suc(m+m)) (rewrite) = le 2 (Suc(m+m)) => le 1 (m+m) (Suc-cancel)
   => m+m != 0 => m != 0 => le 1 m.  Simplest: lt 1 (Suc(m+m)) = le (Suc 1)(Suc(m+m))
     => le 1 (m+m) [le from Suc both: le (Suc a)(Suc b) => le a b].
   Then le 1 (m+m): if m=0 then m+m=0, le 1 0 false. So m=Suc q, le 1 (Suc q) trivial... but we want le 1 m.
   Cleaner: dzos m. m=0 => m+m=0 (mult0) => le 1 0 contra. m=Suc q => le 1 (Suc q)=le 1 m. *)
val le_suc_both_vB = varify lt_suc_cases;  (* not directly; build le-from-le-Suc differently *)
(* le_pred : le (Suc a)(Suc b) => le a b.  le (Suc a)(Suc b) = Ex p. Suc b = Suc a + p = Suc(a+p)
   => b = a+p (Suc_inj) => le a b. *)
val Suc_inj_vB = varify Suc_inj_ax;
fun Suc_inj_b (a,b) heq = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtB [(("a",0), ctermB a),(("b",0), ctermB b)] Suc_inj_vB)) heq;
fun le_pred_b (aT,bT) hle =   (* le (Suc a)(Suc b) => le a b *)
  let val leBody = Abs("p", natT, oeq (suc bT) (add (suc aT) (Bound 0)))
      fun aft p (hp:thm) =   (* hp : Suc b = (Suc a)+p = Suc(a+p) *)
        let val aS = addSuc_b (aT, p)         (* (Suc a)+p = Suc(a+p) *)
            val sb = oeqTrans_b (hp, aS)       (* Suc b = Suc(a+p) *)
            val beq= Suc_inj_b (bT, add aT p) sb   (* b = a+p *)
        in le_intro_b (aT, bT, p) beq end
  in exE_b (leBody, le aT bT) hle "p_lp" natT aft end;

val le_one_m =
  let
    val lt1p = conjunct1_b (lt (suc ZeroC) pB, mkForall (ppAbs pB)) hprime   (* lt 1 p *)
    (* rewrite p -> Suc(m+m) : lt 1 (Suc(m+m)) *)
    val lt1S = oeq_rw_b2 (Term.lambda (Free("zlo1",natT)) (lt (suc ZeroC) (Free("zlo1",natT))), pB, suc (add mB mB)) hodd lt1p
                                             (* lt 1 (Suc(m+m)) = le (Suc 1)(Suc(m+m)) *)
    (* le (Suc 1)(Suc(m+m)) => le 1 (m+m) [le_pred] *)
    val le1mm = le_pred_b (suc ZeroC, add mB mB) lt1S   (* le 1 (m+m) *)
    (* dzos m : m=0 => m+m=0 => le 1 0 contra ; m=Suc q => le 1 m *)
    val dz = dzos_b mB
    val caseZ =
      let val h0 = Thm.assume (ctermB (jT (oeq mB ZeroC)))
          (* m+m = 0 : rewrite both m -> 0 then add 0 0 = 0 *)
          val mm1 = add_cong_l_b (mB, ZeroC, mB) h0   (* m+m = 0+m *)
          val mm2 = add_cong_r_b (ZeroC, mB, ZeroC) h0  (* 0+m = 0+0 *)
          val a00 = add0_b ZeroC                        (* 0+0 = 0 *)
          val mmZero = oeqTrans_b (oeqTrans_b (mm1, mm2), a00)   (* m+m = 0 *)
          (* le 1 (m+m) rewrite m+m -> 0 : le 1 0 *)
          val le10 = oeq_rw_b2 (Term.lambda (Free("zlo2",natT)) (le (suc ZeroC) (Free("zlo2",natT))), add mB mB, ZeroC) mmZero le1mm
          (* le 1 0 = le (Suc 0) 0 = Ex p. 0 = Suc 0 + p = Suc(0+p) => Suc_neq_Zero contra *)
          val fls =
            let val leBody = Abs("p", natT, oeq ZeroC (add (suc ZeroC) (Bound 0)))
                fun aft p (hp:thm) =   (* 0 = (Suc 0)+p = Suc(0+p) *)
                  let val aS = addSuc_b (ZeroC, p)        (* (Suc 0)+p = Suc(0+p) *)
                      val z0 = oeqTrans_b (hp, aS)          (* 0 = Suc(0+p) *)
                      val z0s= oeqSym_b z0                  (* Suc(0+p) = 0 *)
                  in Suc_neq_Zero_g (add ZeroC p) z0s end  (* oFalse -- uses GR helper, term fdec-free OK *)
            in exE_b (leBody, oFalseC) le10 "p_lo" natT aft end
      in Thm.implies_intr (ctermB (jT (oeq mB ZeroC))) (Thm.implies_elim (oFalse_elim_b (le (suc ZeroC) mB)) fls) end
    val PqS = Abs("q", natT, oeq mB (suc (Bound 0)))
    val caseS =
      let val hs = Thm.assume (ctermB (jT (mkEx PqS)))
          fun aft q (hq:thm) =   (* m = Suc q ; le 1 m = le (Suc 0)(Suc q) : Ex p. Suc q = Suc 0 + p ;
                                    witness q : Suc 0 + q = Suc(0+q)=Suc q = m.  But need le 1 m, m=Suc q. *)
            let val a1 = addSuc_b (ZeroC, q)     (* (Suc 0)+q = Suc(0+q) *)
                val a2 = Suc_cong_b (add0_b q)    (* Suc(0+q) = Suc q *)
                val a1c= oeqTrans_b (a1, a2)      (* (Suc 0)+q = Suc q *)
                val mq = oeqTrans_b (hq, oeqSym_b a1c)  (* m = (Suc 0)+q *)
            in le_intro_b (suc ZeroC, mB, q) mq end   (* le 1 m *)
      in Thm.implies_intr (ctermB (jT (mkEx PqS))) (exE_b (PqS, le (suc ZeroC) mB) hs "q_lo" natT aft) end
  in disjE_b (oeq mB ZeroC, mkEx PqS, le (suc ZeroC) mB) dz caseZ caseS end;
val () = out "PB_T12_LEONEM_OK\n";

(* ---- the bound : le a m ==> le b m ==> lt (add(add(a*a)(b*b))(Suc 0))(mult p p) ----
   N = a*a+b*b+1 <= m*m+m*m+1 ; and m*m+m*m+1 <= m*p (= 2m^2+m, needs 1<=m) ; m*p < p*p (m<p). *)
fun bound_lemma (aT,bT) hleA hleB =
  let
    (* a*a <= m*m, b*b <= m*m *)
    val saa = sq_le_mono_b (aT, mB) hleA   (* le (a*a)(m*m) *)
    val sbb = sq_le_mono_b (bT, mB) hleB   (* le (b*b)(m*m) *)
    (* le (a*a+b*b)(m*m+m*m) via add monotone (two steps) *)
    val leSum1 =   (* le (a*a+b*b)(m*m+b*b) *)
      let val leBody = Abs("e",natT, oeq (mult mB mB) (add (mult aT aT) (Bound 0)))
          fun aft e (he:thm) =   (* m*m = a*a + e *)
            let val r = add_cong_l_b (mult mB mB, add (mult aT aT) e, mult bT bT) he   (* m*m+b*b = (a*a+e)+b*b *)
                val re= addassoc_b (mult aT aT, e, mult bT bT)   (* (a*a+e)+b*b = a*a+(e+b*b) *)
                val ce= addcomm_b (e, mult bT bT)                 (* e+b*b = b*b+e *)
                val rc= add_cong_r_b (mult aT aT, add e (mult bT bT), add (mult bT bT) e) ce
                val ra= addassoc_b (mult aT aT, mult bT bT, e)    (* (a*a+b*b)+e = a*a+(b*b+e); sym *)
                val chain = oeqTrans_b (oeqTrans_b (oeqTrans_b (r, re), rc), oeqSym_b ra)  (* m*m+b*b = (a*a+b*b)+e *)
            in le_intro_b (add (mult aT aT)(mult bT bT), add (mult mB mB)(mult bT bT), e) chain end
      in exE_b (leBody, le (add (mult aT aT)(mult bT bT)) (add (mult mB mB)(mult bT bT))) saa "e_b1" natT aft end
    val leSum2 =   (* le (m*m+b*b)(m*m+m*m) *)
      let val leBody = Abs("e",natT, oeq (mult mB mB) (add (mult bT bT) (Bound 0)))
          fun aft e (he:thm) =   (* m*m = b*b + e *)
            let (* m*m + m*m : rewrite 2nd m*m = b*b+e: = m*m + (b*b+e) = (m*m+b*b)+e *)
                val rr = add_cong_r_b (mult mB mB, mult mB mB, add (mult bT bT) e) he   (* m*m+m*m = m*m+(b*b+e) *)
                val ra = addassoc_b (mult mB mB, mult bT bT, e)   (* (m*m+b*b)+e = m*m+(b*b+e); sym *)
                val chain = oeqTrans_b (rr, oeqSym_b ra)          (* m*m+m*m = (m*m+b*b)+e *)
            in le_intro_b (add (mult mB mB)(mult bT bT), add (mult mB mB)(mult mB mB), e) chain end
      in exE_b (leBody, le (add (mult mB mB)(mult bT bT)) (add (mult mB mB)(mult mB mB))) sbb "e_b2" natT aft end
    val leSumMM = le_trans_b (add (mult aT aT)(mult bT bT), add (mult mB mB)(mult bT bT), add (mult mB mB)(mult mB mB)) leSum1 leSum2
                                                 (* le (a*a+b*b)(m*m+m*m) *)
    (* le (Suc(a*a+b*b))(Suc(m*m+m*m)) = le N (Suc(m*m+m*m)) [reshaping Suc to +1] *)
    val leSucN = le_suc_mono_b (add (mult aT aT)(mult bT bT), add (mult mB mB)(mult mB mB)) leSumMM
                                                 (* le (Suc(a*a+b*b))(Suc(m*m+m*m)) *)
    (* N = (a*a+b*b)+Suc 0 = Suc(a*a+b*b) ; 2m^2+1 = (m*m+m*m)+Suc 0 = Suc(m*m+m*m). *)
    val Nval = add (add (mult aT aT)(mult bT bT))(suc ZeroC)
    val NeqSuc = let val r = addSucr_b2 (add (mult aT aT)(mult bT bT), ZeroC)  (* (a*a+b*b)+Suc 0 = Suc((a*a+b*b)+0) *)
                     val r2= Suc_cong_b (add0r_b (add (mult aT aT)(mult bT bT)))  (* Suc(...+0)=Suc(...) *)
                 in oeqTrans_b (r, r2) end       (* N = Suc(a*a+b*b) *)
    val TwoM = add (add (mult mB mB)(mult mB mB))(suc ZeroC)   (* 2m^2+1 *)
    val TwoMeqSuc = let val r = addSucr_b2 (add (mult mB mB)(mult mB mB), ZeroC)
                        val r2= Suc_cong_b (add0r_b (add (mult mB mB)(mult mB mB)))
                    in oeqTrans_b (r, r2) end     (* 2m^2+1 = Suc(m*m+m*m) *)
    (* le N (2m^2+1) : rewrite both Suc's *)
    val leN2M = let val l1 = oeq_rw_b2 (Term.lambda (Free("zb1",natT)) (le (Free("zb1",natT)) (suc (add (mult mB mB)(mult mB mB)))), suc (add (mult aT aT)(mult bT bT)), Nval) (oeqSym_b NeqSuc) leSucN
                    val l2 = oeq_rw_b2 (Term.lambda (Free("zb2",natT)) (le Nval (Free("zb2",natT))), suc (add (mult mB mB)(mult mB mB)), TwoM) (oeqSym_b TwoMeqSuc) l1
                in l2 end   (* le N (2m^2+1) *)
    (* m*p = 2m^2+m : oeq (mult m p)(add (add (mult m m)(mult m m)) m).
       m*p = m*(Suc(m+m)) [hodd] = m + m*(m+m) [mult_Suc_right] = m + (m*m + m*m) [left_distrib].
       = (m*m+m*m)+m [comm].  So oeq (m*p)((m*m+m*m)+m). *)
    val mp1 = mult_cong_r_b (mB, pB, suc (add mB mB)) hodd   (* m*p = m*(Suc(m+m)) *)
    val mp2 = multSucr_b (mB, add mB mB)                      (* m*(Suc(m+m)) = m + m*(m+m) *)
    val mp3 = let val ld = beta_norm (Drule.infer_instantiate ctxtB [(("x",0), ctermB mB),(("m",0), ctermB mB),(("n",0), ctermB mB)] (varify left_distrib))
              in ld end   (* m*(m+m) = m*m + m*m *)
    val mp23 = oeqTrans_b (mp2, add_cong_r_b (mB, mult mB (add mB mB), add (mult mB mB)(mult mB mB)) mp3)  (* m*(Suc(m+m)) = m + (m*m+m*m) *)
    val mp_eq0 = oeqTrans_b (mp1, mp23)   (* m*p = m + (m*m+m*m) *)
    val mp_comm = addcomm_b (mB, add (mult mB mB)(mult mB mB))   (* m+(m*m+m*m) = (m*m+m*m)+m *)
    val mp_eq = oeqTrans_b (mp_eq0, mp_comm)   (* m*p = (m*m+m*m)+m *)
    (* le (2m^2+1)(m*p) : 2m^2+1 = (m*m+m*m)+Suc 0 ; m*p = (m*m+m*m)+m ; le 1 m => le ((m*m+m*m)+1)((m*m+m*m)+m). *)
    (* le (Suc 0) m (= le_one_m).  le ((2m^2)+1)((2m^2)+m) via add_left mono on the Suc0<=m. *)
    val le1mAdd = (* le (add S2 (Suc 0))(add S2 m) where S2=m*m+m*m, from le (Suc 0) m *)
      let val S2 = add (mult mB mB)(mult mB mB)
          val leBody = Abs("e",natT, oeq mB (add (suc ZeroC) (Bound 0)))
          fun aft e (he:thm) =   (* m = (Suc 0) + e *)
            let (* S2+m = S2+((Suc 0)+e) = (S2+Suc 0)+e *)
                val r1 = add_cong_r_b (S2, mB, add (suc ZeroC) e) he    (* S2+m = S2+((Suc 0)+e) *)
                val r2 = addassoc_b (S2, suc ZeroC, e)                   (* (S2+Suc 0)+e = S2+((Suc 0)+e); sym *)
                val chain = oeqTrans_b (r1, oeqSym_b r2)                 (* S2+m = (S2+Suc 0)+e *)
            in le_intro_b (add S2 (suc ZeroC), add S2 mB, e) chain end
      in exE_b (leBody, le (add S2 (suc ZeroC))(add S2 mB)) le_one_m "e_b3" natT aft end
    (* le1mAdd : le ((m*m+m*m)+Suc 0)((m*m+m*m)+m) = le (2m^2+1)(...).  rewrite RHS (m*m+m*m)+m -> m*p (mp_eq sym) *)
    val le2M_mp = oeq_rw_b2 (Term.lambda (Free("zb4",natT)) (le TwoM (Free("zb4",natT))), add (add (mult mB mB)(mult mB mB)) mB, mult mB pB) (oeqSym_b mp_eq) le1mAdd
                                                 (* le (2m^2+1)(m*p) *)
    (* lt (m*p)(p*p) : m<p => le (Suc(m*p))(p*p).
       p*(Suc m) = p + p*m [mult_Suc_right] = p + m*p [comm].  le (Suc m) p => le (p*(Suc m))(p*p) [mult_le_mono c=p].
       p*(Suc m) = p+m*p >= Suc(m*p) (p>=1).  So le (Suc(m*p))(p*p). *)
    val ltmp = m_lt_p                            (* lt m p = le (Suc m) p *)
    val lemono = mult_le_mono_b (pB, suc mB, pB) ltmp   (* le (p*(Suc m))(p*p) *)
    val pSm = multSucr_b (pB, mB)                (* p*(Suc m) = p + p*m *)
    val pm_comm = add_cong_r_b (pB, mult pB mB, mult mB pB) (multcomm_b (pB, mB))   (* p + p*m = p + m*p *)
    val pSm2 = oeqTrans_b (pSm, pm_comm)         (* p*(Suc m) = p + m*p *)
    (* p + m*p >= Suc(m*p) : p>=1 so p = Suc(pred)... use le (Suc(m*p))(p + m*p):
       Suc(m*p) = (Suc 0)+(m*p) [addSuc: (Suc 0)+m*p=Suc(0+m*p)=Suc(m*p)]; and le (Suc 0) p (le_one... no, p>=1).
       le (Suc 0) p: from lt 1 p? we have lt 1 p (1<p). lt 1 p = le 2 p => le 1 p (le_trans le 1 2). Simpler:
       p = Suc(m+m) so le (Suc 0) p directly (witness m+m). *)
    val le1p = let val a1 = addSuc_b (ZeroC, add mB mB)
                   val a2 = Suc_cong_b (add0_b (add mB mB))
                   val a1c= oeqTrans_b (a1, a2)            (* (Suc 0)+(m+m) = Suc(m+m) *)
                   val pEq= oeqTrans_b (hodd, oeqSym_b a1c)  (* p = (Suc 0)+(m+m) *)
               in le_intro_b (suc ZeroC, pB, add mB mB) pEq end   (* le (Suc 0) p *)
    (* le (Suc(m*p))(p + m*p) : Suc(m*p) = (Suc 0)+(m*p) ; le (Suc 0) p => le ((Suc 0)+(m*p))(p+(m*p)) [add right mono]. *)
    val SucMp_eq = let val a1 = addSuc_b (ZeroC, mult mB pB)    (* (Suc 0)+(m*p) = Suc(0+m*p) *)
                       val a2 = Suc_cong_b (add0_b (mult mB pB)) (* Suc(0+m*p) = Suc(m*p) *)
                   in oeqTrans_b (a1, a2) end   (* (Suc 0)+(m*p) = Suc(m*p) *)
    val leAddMono = (* le ((Suc 0)+(m*p))(p+(m*p)) from le (Suc 0) p *)
      let val leBody = Abs("e",natT, oeq pB (add (suc ZeroC) (Bound 0)))
          fun aft e (he:thm) =   (* p = (Suc 0)+e *)
            let val r1 = add_cong_l_b (pB, add (suc ZeroC) e, mult mB pB) he   (* p+(m*p) = ((Suc 0)+e)+(m*p) *)
                val r2 = addassoc_b (suc ZeroC, e, mult mB pB)   (* ((Suc 0)+e)+(m*p) = (Suc 0)+(e+(m*p)) *)
                val r3 = addcomm_b (e, mult mB pB)               (* e+(m*p) = (m*p)+e *)
                val r4 = add_cong_r_b (suc ZeroC, add e (mult mB pB), add (mult mB pB) e) r3
                val r5 = addassoc_b (suc ZeroC, mult mB pB, e)   (* ((Suc 0)+(m*p))+e = (Suc 0)+((m*p)+e); sym *)
                val chain = oeqTrans_b (oeqTrans_b (oeqTrans_b (r1, r2), r4), oeqSym_b r5)  (* p+(m*p) = ((Suc 0)+(m*p))+e *)
            in le_intro_b (add (suc ZeroC)(mult mB pB), add pB (mult mB pB), e) chain end
      in exE_b (leBody, le (add (suc ZeroC)(mult mB pB))(add pB (mult mB pB))) le1p "e_b5" natT aft end
    (* rewrite ((Suc 0)+(m*p)) -> Suc(m*p) on LHS *)
    val leSucMp_pmp = oeq_rw_b2 (Term.lambda (Free("zb6",natT)) (le (Free("zb6",natT)) (add pB (mult mB pB))), add (suc ZeroC)(mult mB pB), suc (mult mB pB)) SucMp_eq leAddMono
                                                 (* le (Suc(m*p))(p + m*p) *)
    (* p + m*p = p*(Suc m) [pSm2 sym] ; le (Suc(m*p))(p*(Suc m)) *)
    val leSucMp_pSm = oeq_rw_b2 (Term.lambda (Free("zb7",natT)) (le (suc (mult mB pB)) (Free("zb7",natT))), add pB (mult mB pB), mult pB (suc mB)) (oeqSym_b pSm2) leSucMp_pmp
                                                 (* le (Suc(m*p))(p*(Suc m)) *)
    val lt_mp_pp = le_trans_b (suc (mult mB pB), mult pB (suc mB), mult pB pB) leSucMp_pSm lemono
                                                 (* le (Suc(m*p))(p*p) = lt (m*p)(p*p) *)
    (* combine: le N (2m^2+1) <= le (2m^2+1)(m*p) ; lt (m*p)(p*p).
       le N (m*p) [le_trans] ; then le N (m*p) and lt (m*p)(p*p) => lt N (p*p):
         le (Suc N)(Suc(m*p)) [le_suc_mono] ; le (Suc(m*p))(p*p) [lt_mp_pp] => le (Suc N)(p*p) = lt N (p*p). *)
    val leN_mp = le_trans_b (Nval, TwoM, mult mB pB) leN2M le2M_mp   (* le N (m*p) *)
    val leSucN_Sucmp = le_suc_mono_b (Nval, mult mB pB) leN_mp        (* le (Suc N)(Suc(m*p)) *)
    val ltN = le_trans_b (suc Nval, suc (mult mB pB), mult pB pB) leSucN_Sucmp lt_mp_pp  (* le (Suc N)(p*p) = lt N (p*p) *)
  in ltN end;
val () = out "PB_T12_BOUND_READY\n";

val () = out "PB_T12_DONE\n";

(* ============================================================================
   PART B TEST 13: FINAL composition.  From pigeonThm (EX a b. bounds /\ cong N 0)
   build EX m'. 0<m' /\ m'<p /\ four_sq(m'*p).  Marker L4_PRIMEMULT_OK.
   ============================================================================ *)
val () = out "PB_T13_BEGIN\n";

(* pm_from_cong GR instantiator *)
val pm_from_cong_vGR = varify pm_from_cong;
fun pm_from_cong_gr (pT,nT) hcong hpos hlt hfsq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtGR
        [(("p_pf",0), ctermGR pT),(("N_pf",0), ctermGR nT)] pm_from_cong_vGR)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hcong) hpos) hlt) hfsq end;
val mult_1_left_vB = varify mult_1_left;
fun mult1l_b n = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB n)] mult_1_left_vB);
val () = out "PB_T13_HELPERS_OK\n";

(* the primemult goal predicate (matches pm_from_cong's conclusion shape) *)
fun pmBody m' = mkConj (lt ZeroC m') (mkConj (lt m' pB) (four_sq (mult m' pB)));
val pmGoal = mkEx (Term.lambda (Free("m_pf",natT)) (pmBody (Free("m_pf",natT))));

(* exE on a, b from pigeonThm *)
val primemult =
  let
    val Pa = Term.lambda (Free("a_tg",natT))
               (mkEx (Term.lambda (Free("b_tg",natT)) (targetBody (Free("a_tg",natT)) (Free("b_tg",natT)))))
    fun bodyA a (ha:thm) =   (* ha : Ex b. targetBody a b *)
      let val Pb = Term.lambda (Free("b_tg",natT)) (targetBody a (Free("b_tg",natT)))
          fun bodyB b (hb:thm) =   (* hb : targetBody a b = (le a m /\ le b m) /\ cong N 0 *)
            let
              val N = add (add (mult a a)(mult b b))(suc ZeroC)
              val hbounds = conjunct1_b (mkConj (le a mB)(le b mB), targetCong a b) hb   (* le a m /\ le b m *)
              val hcongN  = conjunct2_b (mkConj (le a mB)(le b mB), targetCong a b) hb   (* cong p N 0 *)
              val hleA = conjunct1_b (le a mB, le b mB) hbounds
              val hleB = conjunct2_b (le a mB, le b mB) hbounds
              (* 0 < N : N = (a*a+b*b)+Suc 0 = (Suc 0)+(a*a+b*b) ; le_intro witness (a*a+b*b) *)
              val s2 = add (mult a a)(mult b b)
              val a1 = addSuc_b (ZeroC, s2)         (* (Suc 0)+s2 = Suc(0+s2) *)
              val a2 = Suc_cong_b (add0_b s2)        (* Suc(0+s2) = Suc s2 *)
              val a1c= oeqTrans_b (a1, a2)           (* (Suc 0)+s2 = Suc s2 *)
              val Nsuc = let val r = addSucr_b2 (s2, ZeroC)    (* s2 + Suc 0 = Suc(s2+0) *)
                             val r2= Suc_cong_b (add0r_b s2)    (* Suc(s2+0) = Suc s2 *)
                         in oeqTrans_b (r, r2) end   (* N = Suc s2 *)
              val NeqSuc0 = oeqTrans_b (Nsuc, oeqSym_b a1c)   (* N = (Suc 0)+s2 *)
              val hposN = le_intro_b (suc ZeroC, N, s2) NeqSuc0   (* le (Suc 0) N = lt 0 N *)
              (* N < p*p : bound_lemma *)
              val hltN = bound_lemma (a, b) hleA hleB   (* lt N (p*p) *)
              (* four_sq N : witness (a,b,1,0).  body oeq N ((a*a+b*b)+(1*1+0*0)).
                 1*1 = Suc 0 (mult1l), 0*0 = 0, (1*1+0*0) = Suc 0 + 0 = Suc 0.
                 So (a*a+b*b)+(1*1+0*0) = (a*a+b*b)+Suc 0 = N. *)
              val m11 = mult1l_b (suc ZeroC)         (* (Suc 0)*(Suc 0) = Suc 0 *)
              val m00 = let val z = mult0_g ZeroC in z end  (* 0*0 = 0 (GR helper, fdec-free) *)
              (* (1*1+0*0) = (Suc 0)+0 [cong] = Suc 0 *)
              val s1 = add_cong_l_b (mult (suc ZeroC)(suc ZeroC), suc ZeroC, mult ZeroC ZeroC) m11   (* (1*1+0*0) = (Suc 0)+(0*0) *)
              val s2b= add_cong_r_b (suc ZeroC, mult ZeroC ZeroC, ZeroC) m00   (* (Suc 0)+(0*0) = (Suc 0)+0 *)
              val s3 = add0r_b (suc ZeroC)            (* (Suc 0)+0 = Suc 0 *)
              val cdEq = oeqTrans_b (oeqTrans_b (s1, s2b), s3)   (* (1*1+0*0) = Suc 0 *)
              (* body : oeq N (add s2 (add (1*1)(0*0))).  N = s2 + Suc 0.  rewrite Suc 0 -> (1*1+0*0). *)
              val NeqBody = oeq_rw_b2 (Term.lambda (Free("zfsw",natT)) (oeq N (add s2 (Free("zfsw",natT)))),
                                        suc ZeroC, add (mult (suc ZeroC)(suc ZeroC))(mult ZeroC ZeroC)) (oeqSym_b cdEq) (oeqRefl_b N)
                                       (* oeq N (s2 + (1*1+0*0)) = body *)
              val hfsq = four_sq_witness (N, a, b, suc ZeroC, ZeroC) NeqBody   (* four_sq N *)
              (* compose pm_from_cong *)
              val res = pm_from_cong_gr (pB, N) hcongN hposN hltN hfsq   (* EX m'. 0<m' /\ m'<p /\ four_sq(m'*p) *)
            in res end
      in exE_b (Pb, pmGoal) ha "b_pm" natT bodyB end
  in exE_b (Pa, pmGoal) pigeonThm "a_pm" natT bodyA end;

val () = out ("PB_T13_PRIMEMULT hyps="^Int.toString(length(Thm.hyps_of primemult))^"\n");
val () = out ("PB_T13_PRIMEMULT prop = "^Syntax.string_of_term ctxtB (Thm.prop_of primemult)^"\n");

(* discharge the two assumptions (prime2 p, p=Suc(m+m)) to get the clean implication *)
val primemult_thm =
  Thm.implies_intr (ctermB primeP) (Thm.implies_intr (ctermB oddP) primemult);
val () = out ("PB_T13_PRIMEMULT_THM hyps="^Int.toString(length(Thm.hyps_of primemult_thm))^"\n");

val () = if length (Thm.hyps_of primemult_thm) = 0 then out "L4_PRIMEMULT_OK\n" else out ("L4_PRIMEMULT_HYPS "^Int.toString(length(Thm.hyps_of primemult_thm))^"\n");
val () = out "PB_T13_DONE\n";

(* ============================================================================
   PART B TEST 14: aconv against intended + soundness probes.
   primemult_thm :
     prime2 p ==> oeq p (Suc(m+m)) ==> EX m'. lt 0 m' /\ lt m' p /\ four_sq (m'*p)
   ============================================================================ *)
val () = out "PB_T14_BEGIN\n";

val primemult_intended =
  let val concl = mkEx (Term.lambda (Free("m_pf",natT))
                    (mkConj (lt ZeroC (Free("m_pf",natT)))
                      (mkConj (lt (Free("m_pf",natT)) pB) (four_sq (mult (Free("m_pf",natT)) pB)))))
  in Logic.mk_implies (jT (prime2 pB),
       Logic.mk_implies (jT (oeq pB (suc (add mB mB))), jT concl)) end;
val pm_aconv = ((Thm.prop_of primemult_thm) aconv primemult_intended);
val pm_0hyp  = (length (Thm.hyps_of primemult_thm) = 0);
val () = out ("L4_PRIMEMULT_VALIDATE aconv="^Bool.toString pm_aconv^" zero_hyp="^Bool.toString pm_0hyp^"\n");

(* soundness probe 1 : must NOT be the unconditional existential (keeps prime hyp) *)
val pm_probe1 = not ((Thm.prop_of primemult_thm) aconv
  (jT (mkEx (Term.lambda (Free("m_pf",natT))
         (mkConj (lt ZeroC (Free("m_pf",natT)))
           (mkConj (lt (Free("m_pf",natT)) pB) (four_sq (mult (Free("m_pf",natT)) pB))))))));
(* soundness probe 2 : the pigeonhole core (cong) genuinely conditional on prime + odd *)
val pigeon_probe = (length (Thm.hyps_of pigeonThm) = 2);

val () = out ("L4_PRIMEMULT_PROBE conditional="^Bool.toString pm_probe1^" pigeon2hyp="^Bool.toString pigeon_probe^"\n");

(* the pigeon (cong) lemma discharged to a clean implication too *)
val pigeon_thm =
  Thm.implies_intr (ctermB primeP) (Thm.implies_intr (ctermB oddP) pigeonThm);
val () = out ("L4_PIGEON_THM hyps="^Int.toString(length(Thm.hyps_of pigeon_thm))^"\n");
val pigeon_intended =
  let val concl = mkEx (Term.lambda (Free("a_tg",natT))
                    (mkEx (Term.lambda (Free("b_tg",natT))
                      (mkConj (mkConj (le (Free("a_tg",natT)) mB)(le (Free("b_tg",natT)) mB))
                              (cong pB (add (add (mult (Free("a_tg",natT))(Free("a_tg",natT)))(mult (Free("b_tg",natT))(Free("b_tg",natT))))(suc ZeroC)) ZeroC)))))
  in Logic.mk_implies (jT (prime2 pB),
       Logic.mk_implies (jT (oeq pB (suc (add mB mB))), jT concl)) end;
val pigeon_aconv = ((Thm.prop_of pigeon_thm) aconv pigeon_intended);
val () = out ("L4_PIGEON_VALIDATE aconv="^Bool.toString pigeon_aconv^" zero_hyp="^Bool.toString (length(Thm.hyps_of pigeon_thm)=0)^"\n");

val () = if pm_aconv andalso pm_0hyp andalso pm_probe1 then out "L4_PARTB_ALL_OK\n" else out "L4_PARTB_VALIDATE_FAILED\n";
val () = out "PB_T14_DONE\n";
