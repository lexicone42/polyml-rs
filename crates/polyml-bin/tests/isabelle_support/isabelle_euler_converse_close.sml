
(* ============================================================================
   BRIDGE ASSEMBLY + SCG DISCHARGE  (the prize: close euclid_euler).
   Uses dl2_complete + dl2_lnodup + the banked dl2_members_dvd + sum_supp_collapse
   to build bridge_m / bridge_N, feed sigma_mult_reduction -> SCG, then discharge
   euclid_euler_cond -> euclid_euler.
   ============================================================================ *)
val () = out "EE_BRIDGE_BEGIN\n";

(* transfer the swt / sum_supp_collapse / sigma_def / lsumf_cong machinery to ctxtEC *)
val sum_supp_collapse_vE = upE sum_supp_collapse_vD;   (* f,L,N : [lnodup L; H1; H2] -> sumf f N = lsumf f L *)
val sigma_def_vE  = upE sigma_def_vD2;                 (* oeq (sigma n)(sumf (swt n) n) ; var n *)
val lsumf_cong_vE = upE lsumf_cong_vD;                 (* (!!d. lmem d L -> f d = g d) -> lsumf f L = lsumf g L *)
val swt_dvd_vE    = upE swt_dvd_vD;                    (* dvd d n -> swt n d = d *)
val swt_ndvd_vE   = upE swt_ndvd_vD;                   (* neg(dvd d n) -> swt n d = 0 *)
val dl2_members_dvd_vE = dl2_members_dvd;              (* already on ctxtEC (partial) *)

fun swtDvdE (dT, nT) hdvd = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtEC
      [(("d",0), ctermEC dT),(("n",0), ctermEC nT)] swt_dvd_vE)) hdvd;
fun swtNdvdE (dT, nT) hndvd = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtEC
      [(("d",0), ctermEC dT),(("n",0), ctermEC nT)] swt_ndvd_vE)) hndvd;
fun sigmaDefE nT = beta_norm (Drule.infer_instantiate ctxtEC [(("n",0), ctermEC nT)] sigma_def_vE);

val swtC_E = swtC;   (* the swt constant term (theory-independent Const) *)
fun swtF nT = swtC_E $ nT;   (* (swt N) as a function term *)

(* ============================================================================
   bridge generic : for a list L that IS the divisor support of K (with the three
   support facts), sigma K = lsumf idw L.
     supportBridge (KT, LT) hLnodup hH1meta hH2meta hMembersDvd
       hH1meta : !!d. le d K ==> Disj(lmem d L)(oeq (swt K d) 0)
       hH2meta : !!d. lmem d L ==> le d K
       hMembersDvd : !!d. lmem d L ==> dvd d K   (so swt K d = d on members)
     returns oeq (sigma K)(lsumf idw L).
   ============================================================================ *)
fun supportBridge (KT, LT) hLnodup hH1meta hH2meta hMembersDvd =
  let
    val ssc = beta_norm (Drule.infer_instantiate ctxtEC
                [(("f",0), ctermEC (swtF KT)),(("L",0), ctermEC LT),(("N",0), ctermEC KT)] sum_supp_collapse_vE)
    val s1 = Thm.implies_elim ssc hLnodup
    val s2 = Thm.implies_elim s1 hH1meta
    val s3 = Thm.implies_elim s2 hH2meta   (* oeq (sumf (swt K) K)(lsumf (swt K) L) *)
    (* sigma K = sumf (swt K) K *)
    val sdef = sigmaDefE KT
    val sig_lsumf = trans2E (sdef, s3)   (* oeq (sigma K)(lsumf (swt K) L) *)
    (* lsumf (swt K) L = lsumf idw L  via lsumf_cong : on members d, swt K d = d = idw d. *)
    (* lsumf_cong expects an OBJECT-Forall premise : Forall(%d. Imp(lmem d L)(oeq (f d)(g d))).
       Build it (NOT a meta !!d. ...), mirroring apply_lsumf_congL. *)
    val congMinor =
      let
        val dF = Free("d_sb", natT)
        val hmem = Thm.assume (ctermEC (jT (lmem dF LT)))
        val hdvd = Thm.implies_elim (Thm.forall_elim (ctermEC dF) hMembersDvd) hmem   (* dvd d K *)
        val swtd = swtDvdE (dF, KT) hdvd   (* oeq (swt K d) d ; note idw d beta = d *)
        (* discharge the membership as OBJECT Imp ; body oeq (swt K d) d *)
        val impd = impI_E (lmem dF LT, oeq (swtF KT $ dF) dF) swtd
      in allI_E (Term.lambda (Free("d",natT))
                   (mkImp (lmem (Free("d",natT)) LT)(oeq (swtF KT $ (Free("d",natT))) (Free("d",natT)))))
                (Thm.forall_intr (ctermEC dF) impd) end
    val congInst = beta_norm (Drule.infer_instantiate ctxtEC
                     [(("f",0), ctermEC (swtF KT)),(("g",0), ctermEC idw),(("L",0), ctermEC LT)] lsumf_cong_vE)
    (* congInst beta-normalises (g d)=(idw d) to d, so its premise is the object Forall built above. *)
    val forallT = mkForall (Term.lambda (Free("d",natT))
                    (mkImp (lmem (Free("d",natT)) LT)(oeq (swtF KT $ (Free("d",natT))) (Free("d",natT)))))
    val congEq = mp_E (forallT, oeq (lsumf (swtF KT) LT)(lsumf idw LT)) congInst congMinor
    val res = trans2E (sig_lsumf, congEq)   (* oeq (sigma K)(lsumf idw L) *)
  in res end;
val () = out "EE_BRIDGE_SUPPORT_OK\n";

(* ============================================================================
   H1 / H2 META builders for sum_supp_collapse, parameterised by a "membership
   prover" memProve : (eF, hPos, hLe, hDvd) -> lmem eF L  (for the divisor case).
   H1 : !!d. le d K ==> Disj(lmem d L)(oeq (swt K d) 0)
   H2 : !!d. lmem d L ==> le d K     (from membersDvd + dvd_le, K != 0)
   ============================================================================ *)
(* K != 0 meta (oeq K 0 ==> oFalse) supplied by caller as hKnz. *)
fun mkH1 (KT, LT) hKnz memProve =
  let
    val dF = Free("d_h1", natT)
    val concl = mkDisj (lmem dF LT)(oeq (swtF KT $ dF) ZeroC)
    val hle = Thm.assume (ctermEC (jT (le dF KT)))
    val em = exMiddleE (dvd dF KT)
    val caseDvd =
      let
        val hdvd = Thm.assume (ctermEC (jT (dvd dF KT)))
        val emp = exMiddleE (lt ZeroC dF)
        val cPos =
          let val hpos = Thm.assume (ctermEC (jT (lt ZeroC dF)))
              val mem = memProve (dF, hpos, hle, hdvd)   (* lmem d L *)
          in Thm.implies_intr (ctermEC (jT (lt ZeroC dF))) (disjI1_E (lmem dF LT, oeq (swtF KT $ dF) ZeroC) mem) end
        val cZero =
          let val hnp = Thm.assume (ctermEC (jT (neg (lt ZeroC dF))))
              (* d = 0 : dzos d, Suc case -> lt 0 d contra ; so d = 0. *)
              val dz = dzosE dF
              val d0 = let val cZ = let val h0 = Thm.assume (ctermEC (jT (oeq dF ZeroC))) in Thm.implies_intr (ctermEC (jT (oeq dF ZeroC))) h0 end
                           val cS = let val Pq = Abs("q",natT, oeq dF (suc (Bound 0)))
                                        val hx = Thm.assume (ctermEC (jT (mkEx Pq)))
                                    in Thm.implies_intr (ctermEC (jT (mkEx Pq)))
                                         (exE_E (Pq, oeq dF ZeroC) hx (fn (qF,hq) =>
                                            let val ltp = ltZeroSucE (dF, qF) hq
                                                val ff = mp_E (lt ZeroC dF, oFalseC) hnp ltp
                                            in Thm.implies_elim (oFalse_elimE (oeq dF ZeroC)) ff end)) end
                       in disjE_E (oeq dF ZeroC, mkEx (Abs("q",natT, oeq dF (suc (Bound 0)))), oeq dF ZeroC) dz cZ cS end
              (* swt K d : d=0, neg(dvd 0 K) since K != 0 ; so swt K 0 = 0 ; rewrite. *)
              (* neg(dvd 0 K) : dvd 0 K = K = 0*k = 0 ; so dvd 0 K -> K = 0 -> contra hKnz. *)
              val ndvd0 = let val hdK = Thm.assume (ctermEC (jT (dvd ZeroC KT)))
                              (* dvd 0 K : Ex k. K = 0*k ; 0*k = 0 ; K = 0 *)
                              val kK0 = dvd_destE (ZeroC, KT, oFalseC) hdK (fn (kF,hk) =>
                                          let val z = trans2E (hk, (* 0*k = 0 *) (let val m0 = trans2E (multcommE (ZeroC,kF), mult0rE kF) in m0 end))  (* K = 0 *)
                                          in Thm.implies_elim hKnz z end)
                          in impI_E (dvd ZeroC KT, oFalseC) kK0 end  (* neg(dvd 0 K) [OBJECT Imp] *)
              (* swt K 0 = 0 : swt_ndvd at d=0 *)
              val swt0at0 = swtNdvdE (ZeroC, KT) ndvd0   (* oeq (swt K 0) 0 *)
              (* swt K d = 0 : rewrite 0 -> d via sym d0 in swt K _ *)
              val Ps = Term.lambda (Free("zs",natT)) (oeq (swtF KT $ (Free("zs",natT))) ZeroC)
              val swt0atd = substPredE (Ps, ZeroC, dF) (symmE d0) swt0at0   (* oeq (swt K d) 0 *)
          in Thm.implies_intr (ctermEC (jT (neg (lt ZeroC dF)))) (disjI2_E (lmem dF LT, oeq (swtF KT $ dF) ZeroC) swt0atd) end
      in Thm.implies_intr (ctermEC (jT (dvd dF KT))) (disjE_E (lt ZeroC dF, neg (lt ZeroC dF), concl) emp cPos cZero) end
    val caseNdvd =
      let val hnd = Thm.assume (ctermEC (jT (neg (dvd dF KT))))
          val swt0 = swtNdvdE (dF, KT) hnd   (* oeq (swt K d) 0 *)
      in Thm.implies_intr (ctermEC (jT (neg (dvd dF KT)))) (disjI2_E (lmem dF LT, oeq (swtF KT $ dF) ZeroC) swt0) end
    val body = disjE_E (dvd dF KT, neg (dvd dF KT), concl) em caseDvd caseNdvd
  in Thm.forall_intr (ctermEC dF) (Thm.implies_intr (ctermEC (jT (le dF KT))) body) end;

(* H2 : !!d. lmem d L ==> le d K  ; from membersDvd (lmem d L -> dvd d K) + dvd_le (K != 0) *)
fun mkH2 (KT, LT) hKnz hMembersDvd =
  let
    val dF = Free("d_h2", natT)
    val hmem = Thm.assume (ctermEC (jT (lmem dF LT)))
    val hdvd = Thm.implies_elim (Thm.forall_elim (ctermEC dF) hMembersDvd) hmem   (* dvd d K *)
    val hle = dvdLeE (dF, KT) hdvd hKnz   (* le d K *)
  in Thm.forall_intr (ctermEC dF) (Thm.implies_intr (ctermEC (jT (lmem dF LT))) hle) end;

val () = out "EE_BRIDGE_H1H2_OK\n";

(* ============================================================================
   sig2a : oeq (sigma (p2 a)) (sumf (pow 2) a)     [ = sigma_pow2, previously
   noted as itself-blocked].  Derived via the dl2 machinery at m = 1, D = [1] :
     sigma(2^a) = sigma(2^a * 1) = lsumf idw (dl2 a [1])  [supportBridge]
                = (sumf(pow 2) a) * (lsumf idw [1])        [dist_lemma]
                = (sumf(pow 2) a) * 1 = sumf(pow 2) a.
   D=[1] is the divisor list of 1 ; its hyps are trivial.
   ============================================================================ *)
val one_list = lcons one lnilC;   (* [1] *)

(* lnodup [1] : neg(lmem 1 [])  /\ lnodup [] *)
val lnodup_one_list =
  let
    val neg1nil = impI_E (lmem one lnilC, oFalseC) (Thm.implies_elim (lmemNilElimE2 one) (Thm.assume (ctermEC (jT (lmem one lnilC)))))
  in lnodupConsBwdE (one, lnilC) (conjI_E (neg (lmem one lnilC), lnodup lnilC) neg1nil lnodup_nil_E) end;

(* membersDvd for [1] w.r.t. m=1 : !!d. lmem d [1] ==> dvd d 1.   member d=1 ; dvd 1 1. *)
val membersDvd_one_list =
  let
    val dF = Free("d_ol", natT)
    val hmem = Thm.assume (ctermEC (jT (lmem dF one_list)))
    val dj = Thm.implies_elim (lmemConsFwdE2 (dF, one, lnilC)) hmem   (* Disj(oeq d 1)(lmem d []) *)
    val goal = dvd dF one
    val cEq = let val heq = Thm.assume (ctermEC (jT (oeq dF one)))   (* d = 1 *)
                  val d11 = dvd_reflE one   (* dvd 1 1 *)
                  val res = dvd_cong_divisorE (one, dF, one) (symmE heq) d11   (* dvd d 1 *)
              in Thm.implies_intr (ctermEC (jT (oeq dF one))) res end
    val cNil = let val hn = Thm.assume (ctermEC (jT (lmem dF lnilC)))
               in Thm.implies_intr (ctermEC (jT (lmem dF lnilC))) (Thm.implies_elim (oFalse_elimE goal) (Thm.implies_elim (lmemNilElimE2 dF) hn)) end
    val res = disjE_E (oeq dF one, lmem dF lnilC, goal) dj cEq cNil
  in Thm.forall_intr (ctermEC dF) (Thm.implies_intr (ctermEC (jT (lmem dF one_list))) res) end;

(* completeness DHcmp for [1] w.r.t. m=1 : !!d. lt 0 d ==> le d 1 ==> dvd d 1 ==> lmem d [1].
   d|1 ==> d=1 ; lmem 1 [1]. *)
val complete_one_list =
  let
    val dF = Free("d_ol2", natT)
    val hpos = Thm.assume (ctermEC (jT (lt ZeroC dF)))
    val hle  = Thm.assume (ctermEC (jT (le dF one)))
    val hdvd = Thm.assume (ctermEC (jT (dvd dF one)))   (* Ex k. 1 = d*k *)
    (* d | 1 ==> d = 1 : 1 = d*k ; d = Suc d' (pos) ; if d>=2 then d*k >= 2 > 1 ... use mult_eq_one style.
       Simpler: 1 = d*k ; so d | 1 ; dvd_le gives le d 1 (already have hle) ; combine lt 0 d (le 1 d) + le d 1 -> le_antisym -> d = 1. *)
    (* le 1 d from lt 0 d : lt 0 d = le 1 d definitionally. *)
    val le1d = hpos   (* lt 0 d = le (Suc 0) d = le 1 d *)
    (* le_antisym : le 1 d ==> le d 1 ==> oeq 1 d   (need le_antisym) *)
    val le_antisym_vE = upE (varify (up le_antisym)) handle _ => upE (varify le_antisym)
    val d_eq_1 = let val inst = beta_norm (Drule.infer_instantiate ctxtEC
                       [(("m",0), ctermEC one),(("n",0), ctermEC dF)] le_antisym_vE)
                 in Thm.implies_elim (Thm.implies_elim inst le1d) hle end   (* oeq 1 d *)
    (* lmem 1 [1] then rewrite 1 -> d *)
    val mem1 = Thm.implies_elim (lmemConsBwdE (one, one, lnilC)) (disjI1_E (oeq one one, lmem one lnilC) (reflE one))   (* lmem 1 [1] *)
    val Pm = Term.lambda (Free("zm",natT)) (lmem (Free("zm",natT)) one_list)
    val memd = substPredE (Pm, one, dF) d_eq_1 mem1   (* lmem d [1] *)
  in Thm.forall_intr (ctermEC dF)
       (Thm.implies_intr (ctermEC (jT (lt ZeroC dF)))
         (Thm.implies_intr (ctermEC (jT (le dF one)))
           (Thm.implies_intr (ctermEC (jT (dvd dF one))) memd))) end;
val () = out "EE_BRIDGE_ONELIST_OK\n";

(* neg(dvd 2 1) : 1 odd. *)
val one_odd =
  let
    val hd = Thm.assume (ctermEC (jT (dvd two one)))   (* Ex k. 1 = 2*k *)
    val ff = dvd_destE (two, one, oFalseC) hd
      (fn (kF, hk) =>   (* hk : oeq 1 (mult 2 k) = oeq (Suc 0)(2*k) *)
         let val dz = dzosE kF
             val cZ = let val h0 = Thm.assume (ctermEC (jT (oeq kF ZeroC)))
                          (* 1 = 2*k = 2*0 = 0 ; Suc 0 = 0 -> Suc_neq *)
                          val k0 = trans2E (mult_cong_rE (two, kF, ZeroC) h0, mult0rE two)   (* 2*k = 0 *)
                          val one0 = trans2E (hk, k0)   (* 1 = 0 i.e. Suc 0 = 0 *)
                      in Thm.implies_intr (ctermEC (jT (oeq kF ZeroC))) (Thm.implies_elim (SneqZE ZeroC) one0) end
             val cS = let val Pq = Abs("q",natT, oeq kF (suc (Bound 0)))
                          val hx = Thm.assume (ctermEC (jT (mkEx Pq)))
                      in Thm.implies_intr (ctermEC (jT (mkEx Pq)))
                           (exE_E (Pq, oFalseC) hx (fn (qF, hq) =>
                              let (* 2*k = 2*(Suc q) = 2 + 2q = Suc(Suc(2q)) ; 1 = Suc(Suc(2q)) ; Suc_inj -> 0 = Suc(2q) -> Suc_neq *)
                                  val m2sq = beta_norm (Drule.infer_instantiate ctxtEC
                                        [(("n",0), ctermEC two),(("m",0), ctermEC qF)] (upE (varify mult_Suc_right)))  (* 2*(Suc q) = 2 + 2*q *)
                                  val k2 = trans2E (mult_cong_rE (two, kF, suc qF) hq, m2sq)   (* 2*k = add 2 (2*q) *)
                                  (* add 2 (2q) = add (Suc(Suc 0))(2q) = Suc(Suc(add 0 (2q)))... = Suc(Suc(2q)) *)
                                  val a2 = addSucE (suc ZeroC, mult two qF)   (* add (Suc(Suc 0))(2q) = Suc(add (Suc 0)(2q)) *)
                                  val a1 = addSucE (ZeroC, mult two qF)       (* add (Suc 0)(2q) = Suc(add 0 (2q)) *)
                                  val a0 = add0E2 (mult two qF)               (* add 0 (2q) = 2q *)
                                  val inner = trans2E (a1, ScongE (add ZeroC (mult two qF), mult two qF) a0)  (* add (Suc 0)(2q) = Suc(2q) *)
                                  val add2 = trans2E (a2, ScongE (add (suc ZeroC)(mult two qF), suc (mult two qF)) inner)  (* add 2 (2q) = Suc(Suc(2q)) *)
                                  val k2b = trans2E (k2, add2)   (* 2*k = Suc(Suc(2q)) *)
                                  val one_eq = trans2E (hk, k2b)   (* Suc 0 = Suc(Suc(2q)) *)
                                  val inj = SinjE (ZeroC, suc (mult two qF)) one_eq   (* 0 = Suc(2q) *)
                              in Thm.implies_elim (SneqZE (mult two qF)) (symmE inj) end)) end
         in disjE_E (oeq kF ZeroC, mkEx (Abs("q",natT, oeq kF (suc (Bound 0)))), oFalseC) dz cZ cS end)
  in impI_E (dvd two one, oFalseC) ff end;   (* neg(dvd 2 1) *)
val () = out "EE_BRIDGE_ONEODD_OK\n";

(* K = 2^a * 1 ; build dl2_complete / dl2_lnodup / dl2_members_dvd instances at m=1, D=[1]. *)
val sig2a =
  let
    val aF = Free("a", natT)
    val Kone = mult (p2 aF) one    (* 2^a * 1 = N at m=1 *)
    (* K != 0 : Kone = 2^a*1 = 2^a ; 2^a = Suc(..) (pow2_pos) ; so Kone = Suc(..). *)
    val K_eq_2a = mult1rE (p2 aF)   (* 2^a*1 = 2^a *)
    val hKnz =
      let val h0 = Thm.assume (ctermEC (jT (oeq Kone ZeroC)))
          val a0 = trans2E (symmE K_eq_2a, h0)   (* 2^a = 0 *)
          (* 2^a = Suc m (pow2_pos) -> Suc m = 0 -> Suc_neq *)
          val pp = beta_norm (Drule.infer_instantiate ctxtEC [(("k",0), ctermEC aF)] pow2_pos_vE)  (* Ex m. 2^a = Suc m *)
          val ff = exE_E (Abs("m",natT, oeq (p2 aF)(suc (Bound 0))), oFalseC) pp
                     (fn (mF, hm) => Thm.implies_elim (SneqZE mF) (trans2E (symmE hm, a0)))
      in Thm.implies_intr (ctermEC (jT (oeq Kone ZeroC))) ff end   (* neg(oeq (2^a*1) 0) *)
    (* dl2_members_dvd at (a, m=1, D=[1]) : members of dl2 a [1] divide 2^a*1 *)
    val mdInst = beta_norm (Drule.infer_instantiate ctxtEC
                   [(("a",0), ctermEC aF),(("m",0), ctermEC one),(("D",0), ctermEC one_list)] dl2_members_dvd)
                 (* (Forall d. lmem d [1] -> dvd d 1) ==> Forall e. lmem e (dl2 a [1]) -> dvd e (2^a*1) *)
    (* dl2_members_dvd's hyp is OBJECT Forall ; build it from membersDvd_one_list (META). *)
    val md_obj_hyp =
      let val dF = Free("d_mdo", natT)
          val perd = Thm.implies_elim (Thm.forall_elim (ctermEC dF) membersDvd_one_list) (Thm.assume (ctermEC (jT (lmem dF one_list))))  (* dvd d 1 *)
          val impd = impI_E (lmem dF one_list, dvd dF one) perd
      in allI_E (Term.lambda (Free("d",natT)) (mkImp (lmem (Free("d",natT)) one_list)(dvd (Free("d",natT)) one)))
                (Thm.forall_intr (ctermEC dF) impd) end
    val membersDvd_dl2 = Thm.implies_elim mdInst md_obj_hyp   (* Forall e. lmem e (dl2 a [1]) -> dvd e (2^a*1) *)
    (* convert to META : !!e. lmem e (dl2 a [1]) ==> dvd e Kone *)
    val membersDvd_meta =
      let val eF = Free("e_md", natT)
          val pred = Term.lambda (Free("e",natT)) (mkImp (lmem (Free("e",natT)) (dl2 aF one_list))(dvd (Free("e",natT)) Kone))
          val at = allE_E (pred, eF) membersDvd_dl2
          val concl = mp_E (lmem eF (dl2 aF one_list), dvd eF Kone) at (Thm.assume (ctermEC (jT (lmem eF (dl2 aF one_list)))))
      in Thm.forall_intr (ctermEC eF) (Thm.implies_intr (ctermEC (jT (lmem eF (dl2 aF one_list)))) concl) end
    (* dl2_lnodup at (a,1,[1]) *)
    val lnodupInst = beta_norm (Drule.infer_instantiate ctxtEC
                       [(("a_ld",0), ctermEC aF),(("m",0), ctermEC one),(("D",0), ctermEC one_list)] dl2_lnodup)
    val md_meta_for_lnodup =   (* dl2_lnodup wants META all : !!d. lmem d [1] ==> dvd d 1 *)
      let val dF = Free("d_lm", natT)
      in Thm.forall_intr (ctermEC dF)
           (Thm.implies_intr (ctermEC (jT (lmem dF one_list)))
             (Thm.implies_elim (Thm.forall_elim (ctermEC dF) membersDvd_one_list) (Thm.assume (ctermEC (jT (lmem dF one_list)))))) end
    val hLnodup = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim lnodupInst one_odd) md_meta_for_lnodup) lnodup_one_list  (* lnodup (dl2 a [1]) *)
    (* dl2_complete at (a,1,[1]) for H1's memProve *)
    val completeInst = beta_norm (Drule.infer_instantiate ctxtEC
                         [(("a",0), ctermEC aF),(("m",0), ctermEC one),(("D",0), ctermEC one_list)] dl2_complete)
    (* completeInst : neg(dvd 2 1) ==> DHcmp[1] ==> !!e. dvd e Kone ==> lt 0 e ==> le e Kone ==> lmem e (dl2 a [1]) *)
    val dhcmp_meta_one =   (* !!d. lt 0 d ==> le d 1 ==> dvd d 1 ==> lmem d [1] *)
      complete_one_list
    val complete_e = Thm.implies_elim (Thm.implies_elim completeInst one_odd) dhcmp_meta_one
                     (* !!e. dvd e Kone ==> lt 0 e ==> le e Kone ==> lmem e (dl2 a [1]) *)
    fun memProve (eF, hpos, hle, hdvd) =
      let val s0 = Thm.forall_elim (ctermEC eF) complete_e
          val s1 = Thm.implies_elim s0 hdvd
          val s2 = Thm.implies_elim s1 hpos
          val s3 = Thm.implies_elim s2 hle
      in s3 end
    (* H1, H2 *)
    val hH1 = mkH1 (Kone, dl2 aF one_list) hKnz memProve
    val hH2 = mkH2 (Kone, dl2 aF one_list) hKnz membersDvd_meta
    (* supportBridge : sigma Kone = lsumf idw (dl2 a [1]) *)
    val sb = supportBridge (Kone, dl2 aF one_list) hLnodup hH1 hH2 membersDvd_meta
    (* dist_lemma at (a, [1]) : lsumf idw (dl2 a [1]) = (sumf(pow 2)a) * (lsumf idw [1]) *)
    val dl = beta_norm (Drule.infer_instantiate ctxtEC
               [(("a",0), ctermEC aF),(("D",0), ctermEC one_list)] dist_lemma)
    (* lsumf idw [1] = idw 1 + lsumf idw [] = 1 + 0 = 1 *)
    val ls1 = lsumfConsE (idw, one, lnilC)   (* lsumf idw [1] = idw 1 + lsumf idw [] *)
    val lsnil = lsumfNilE idw                 (* lsumf idw [] = 0 *)
    (* idw 1 = 1 (beta) *)
    val ls1b = beta_norm (trans2E (ls1, trans2E (add_cong_rE (idw $ one, lsumf idw lnilC, ZeroC) lsnil, add0rE (idw $ one))))  (* lsumf idw [1] = idw 1 = (beta) 1 *)
    (* idw 1 beta-reduces to 1, so lsumf idw [1] = 1.  add0rE gives = idw 1 = (beta) 1. *)
    (* dist with lsumf[1] -> 1 : (sumf(pow2)a)*(lsumf idw [1]) = (sumf(pow2)a)*1 = sumf(pow2)a *)
    val distR = trans2E (dl, mult_cong_rE (sumf pwAbsE aF, lsumf idw one_list, one) ls1b)
                (* sigma side : lsumf idw (dl2 a [1]) = (sumf(pow2)a)*(idw 1)= (sumf(pow2)a)*1 ; note idw 1 beta = 1 *)
    (* (sumf(pow2)a)*1 = sumf(pow2)a *)
    val collapse = mult1rE (sumf pwAbsE aF)   (* (sumf(pow2)a)*1 = sumf(pow2)a *)
    val rhs = trans2E (distR, collapse)        (* lsumf idw (dl2 a [1]) = sumf(pow2)a *)
    val sigKone = trans2E (sb, rhs)            (* sigma Kone = sumf(pow2)a *)
    (* rewrite sigma Kone -> sigma (2^a) via K_eq_2a : Kone = 2^a *)
    val sig_lhs = let val Ps = Term.lambda (Free("zs",natT)) (oeq (sigma (Free("zs",natT))) (sumf pwAbsE aF))
                  in substPredE (Ps, Kone, p2 aF) K_eq_2a sigKone end   (* sigma (2^a) = sumf(pow2)a *)
  in varify sig_lhs end;

val aVs2 = Var(("a",0), natT)
val i_sig2a = jT (oeq (sigma (p2 aVs2)) (sumf pwAbsE aVs2));
val r_sig2a = chkEC ("sig2a", sig2a, i_sig2a);
val () = if r_sig2a then out "SIG2A_OK\n" else out "SIG2A_FAIL\n";
val () = out "EE_BRIDGE_SIG2A_DONE\n";
(* ============================================================================
   CRUX LEMMA 1 : general divisor_list (dvl) of an arbitrary m.

   Construct  dvl m  = the list of exactly the divisors of m in [1..m], and prove
     (i)   completeness :
              lmem d (dvl m) <-> (lt 0 d AND le d m AND dvd d m)
     (ii)  lnodup (dvl m)
     (iii) lsumf id (dvl m) = sigma m
              (the support bridge :  dvl m IS the support of swt m on [0..m]).

   We build on ctxtSigD (the base's sigma/natlist context), extending thySigD with
   a fresh aux collector dvla : nat->nat->natlist and dvl : nat->natlist, defined
   by CONSERVATIVE recursion axioms only (documented below; NONE mentions
   sigma/perfect/the conclusion).

   CONSTRUCTION (recursive collector, descending bound k = m..0):
     dvla 0 m                       = lnil
     dvd (Suc k) m  ==> dvla (Suc k) m = lcons (Suc k) (dvla k m)
     neg(dvd (Suc k) m) ==> dvla (Suc k) m = dvla k m
     dvl m                          = dvla m m
   i.e. dvla k m = the divisors of m in [1..k].  Every member of dvla k m is <= k,
   so lnodup is clean (prepended Suc k is strictly larger than every tail member).
   ============================================================================ *)
val () = out "DIVLIST_M_BEGIN\n";

(* ---------------------------------------------------------------------------
   THEORY EXTENSION : dvla, dvl over thySigD.  Conservative recursion axioms.
   --------------------------------------------------------------------------- *)
val thyDL0 = Sign.add_consts
  [(Binding.name "dvla", natT --> natT --> natlistT, NoSyn),
   (Binding.name "dvl",  natT --> natlistT, NoSyn)] thyEC;
fun cnstDL nm T = Const (Sign.full_name thyDL0 (Binding.name nm), T);
val dvlaC = cnstDL "dvla" (natT --> natT --> natlistT);
fun dvla k m = dvlaC $ k $ m;
val dvlC  = cnstDL "dvl" (natT --> natlistT);
fun dvl m = dvlC $ m;

val kDL = Free("k", natT);
val mDL = Free("m", natT);

(* conditional recursion axioms (returns leq-equations, mirroring lremove's
   conditional form). *)
val ((_,dvla_0_ax), thyDL1) = Thm.add_axiom_global (Binding.name "dvla_0",
      jT (leqL (dvla ZeroC mDL) lnilC)) thyDL0;
val ((_,dvla_dvd_ax), thyDL2) = Thm.add_axiom_global (Binding.name "dvla_dvd",
      Logic.mk_implies (jT (dvd (suc kDL) mDL),
        jT (leqL (dvla (suc kDL) mDL) (lcons (suc kDL) (dvla kDL mDL))))) thyDL1;
val ((_,dvla_ndvd_ax), thyDL3) = Thm.add_axiom_global (Binding.name "dvla_ndvd",
      Logic.mk_implies (jT (neg (dvd (suc kDL) mDL)),
        jT (leqL (dvla (suc kDL) mDL) (dvla kDL mDL)))) thyDL2;
val ((_,dvl_def_ax), thyDL4) = Thm.add_axiom_global (Binding.name "dvl_def",
      jT (leqL (dvl mDL) (dvla mDL mDL))) thyDL3;

val thyDL  = thyDL4;
val ctxtDL = Proof_Context.init_global thyDL;
val ctermDL= Thm.cterm_of ctxtDL;
fun chkDL (nm, th, intended) =
  let val nh = length (Thm.hyps_of th)
      val ac = (Thm.prop_of th) aconv intended
  in if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
     else (out ("CHK_FAIL " ^ nm ^ "  hyps=" ^ Int.toString nh
                ^ "  aconv=" ^ Bool.toString ac ^ "\n"
                ^ "  got      = " ^ Syntax.string_of_term ctxtDL (Thm.prop_of th) ^ "\n"
                ^ "  intended = " ^ Syntax.string_of_term ctxtDL intended ^ "\n"); false)
  end;
val () = out "DIVLIST_M_CONSTS_OK\n";

(* ---------------------------------------------------------------------------
   TRANSFER every reused base/sigma lemma up to thyDL, and re-wrap the *_DL
   combinator family (mirror of the *_D / *_E families).
   --------------------------------------------------------------------------- *)
fun upL th = Thm.transfer thyDL th;

val oeq_refl_vL    = upL oeq_refl_vD;
val oeq_subst_vL   = upL oeq_subst_vD;
val oeq_sym_L      = upL oeq_sym_D;
val oeq_trans_L    = upL oeq_trans_D;
val add_0_vL       = upL add_0_vD;
val add_0_right_vL = upL add_0_right_vD;
val add_comm_vL    = upL add_comm_vD;
val add_assoc_vL   = upL add_assoc_vD;
val nat_induct_vL  = upL nat_induct_vD;
val list_induct_vL = upL list_induct_vD;
val lsumf_nil_vL   = upL lsumf_nil_vD;
val lsumf_cons_vL  = upL lsumf_cons_vD;
val lmem_nil_elim_vL = upL lmem_nil_elim_vD;
val lmem_cons_fwd_vL = upL lmem_cons_fwd_vD;
val lmem_cons_bwd_vL = upL lmem_cons_bwd_vD;
val lnodup_nil_vL  = upL lnodup_nil_vD;
val lnodup_cons_fwd_vL = upL lnodup_cons_fwd_vD;
val lnodup_cons_bwd_vL = upL lnodup_cons_bwd_vD;
val leq_refl_vL    = upL leq_refl_vD;
val leq_subst_vL   = upL leq_subst_vD;
val impI_vL        = upL impI_vD;
val mp_vL          = upL mp_vD;
val allI_vL        = upL allI_vD;
val allE_vL        = upL allE_vD;
val disjE_vL       = upL disjE_vD;
val disjI1_vL      = upL disjI1_vD;
val disjI2_vL      = upL disjI2_vD;
val conjI_vL       = upL conjI_vD;
val conjunct1_vL   = upL conjunct1_vD;
val conjunct2_vL   = upL conjunct2_vD;
val exI_vL         = upL exI_vD;
val exE_vL         = upL exE_vD;
val ex_middle_vL   = upL ex_middle_vD;
val oFalse_elim_vL = upL oFalse_elim_vD;
val dvd_le_vL      = upL dvd_le_vD;
val disj_zero_or_suc_vL = upL disj_zero_or_suc_vD;
val Suc_inj_vL     = upL Suc_inj_vD;
val sigma_def_vL   = upL sigma_def_vD;
val sum_supp_collapse_vL = upL sum_supp_collapse_vD;
val lsumf_cong_vL  = upL lsumf_cong_vD;
(* the new axioms (varify : Free -> schematic) *)
val dvla_0_vL    = varify dvla_0_ax;
val dvla_dvd_vL  = varify dvla_dvd_ax;
val dvla_ndvd_vL = varify dvla_ndvd_ax;
val dvl_def_vL   = varify dvl_def_ax;

(* ---- ground instantiators / combinators on ctxtDL ---- *)
fun reflL t = beta_norm (Drule.infer_instantiate ctxtDL [(("a",0), ctermDL t)] oeq_refl_vL);
fun trans2L (h1,h2) = oeq_trans_L OF [h1,h2];
fun symmL h = oeq_sym_L OF [h];
fun add0L t   = beta_norm (Drule.infer_instantiate ctxtDL [(("n",0), ctermDL t)] add_0_vL);
fun add0rL t  = beta_norm (Drule.infer_instantiate ctxtDL [(("n",0), ctermDL t)] add_0_right_vL);
fun addcommL (m,n) = beta_norm (Drule.infer_instantiate ctxtDL
      [(("m",0), ctermDL m),(("n",0), ctermDL n)] add_comm_vL);
fun add_cong_lL (p,q,k) hpq =
  let val Pabs = Abs("z", natT, oeq (add p k) (add (Bound 0) k))
      val inst = beta_norm (Drule.infer_instantiate ctxtDL
            [(("P",0), ctermDL Pabs),(("a",0), ctermDL p),(("b",0), ctermDL q)] oeq_subst_vL)
  in inst OF [hpq, reflL (add p k)] end;
fun add_cong_rL (h,p,q) hpq =
  let val Pabs = Abs("z", natT, oeq (add h p) (add h (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtDL
            [(("P",0), ctermDL Pabs),(("a",0), ctermDL p),(("b",0), ctermDL q)] oeq_subst_vL)
  in inst OF [hpq, reflL (add h p)] end;
fun substPredL (Pabs, xT, yT) hxy hPx =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("P",0), ctermDL Pabs),(("a",0), ctermDL xT),(("b",0), ctermDL yT)] oeq_subst_vL)
  in Thm.implies_elim (Thm.implies_elim inst hxy) hPx end;

(* FOL on ctxtDL *)
fun impI_L (At, Bt) hImp =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("A",0), ctermDL At),(("B",0), ctermDL Bt)] impI_vL)
  in Thm.implies_elim inst (Thm.implies_intr (ctermDL (jT At)) hImp) end;
fun mp_L (At, Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("A",0), ctermDL At),(("B",0), ctermDL Bt)] mp_vL)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun allI_L Pabs hAll =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL [(("P",0), ctermDL Pabs)] allI_vL)
  in Thm.implies_elim inst hAll end;
fun allE_L (Pabs, at) hForall =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("P",0), ctermDL Pabs),(("a",0), ctermDL at)] allE_vL)
  in Thm.implies_elim inst hForall end;
fun disjE_L (At, Bt, Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("A",0), ctermDL At),(("B",0), ctermDL Bt),(("C",0), ctermDL Ct)] disjE_vL)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB end;
fun disjI1_L (At, Bt) hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("A",0), ctermDL At),(("B",0), ctermDL Bt)] disjI1_vL)
  in Thm.implies_elim inst hA end;
fun disjI2_L (At, Bt) hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("A",0), ctermDL At),(("B",0), ctermDL Bt)] disjI2_vL)
  in Thm.implies_elim inst hB end;
fun conjI_L (At, Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("A",0), ctermDL At),(("B",0), ctermDL Bt)] conjI_vL)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_L (At, Bt) hC =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("A",0), ctermDL At),(("B",0), ctermDL Bt)] conjunct1_vL)
  in Thm.implies_elim inst hC end;
fun conjunct2_L (At, Bt) hC =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("A",0), ctermDL At),(("B",0), ctermDL Bt)] conjunct2_vL)
  in Thm.implies_elim inst hC end;
fun oFalse_elimL rT = beta_norm (Drule.infer_instantiate ctxtDL [(("R",0), ctermDL rT)] oFalse_elim_vL);
fun exMiddleL At = beta_norm (Drule.infer_instantiate ctxtDL [(("A",0), ctermDL At)] ex_middle_vL);
fun dzosL t = beta_norm (Drule.infer_instantiate ctxtDL [(("p",0), ctermDL t)] disj_zero_or_suc_vL);
fun Suc_injL (a,b) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtDL
      [(("a",0), ctermDL a),(("b",0), ctermDL b)] Suc_inj_vL)) h;
val Suc_cong_vL = upL (varify Suc_cong);
fun Suc_congL (a,b) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtDL
      [(("a",0), ctermDL a),(("b",0), ctermDL b)] Suc_cong_vL)) h;   (* oeq a b ==> oeq (Suc a)(Suc b) *)
(* exE_atL : eliminate Ex P with named witness *)
fun exE_atL (Pabs, goalT) hEx wnm body =
  let
    val wF = Free(wnm, natT)
    val hypTerm = jT (Term.betapply (Pabs, wF))
    val hypThm = Thm.assume (ctermDL hypTerm)
    val bodyThm = body wF hypThm
    val minor = Thm.forall_intr (ctermDL wF) (Thm.implies_intr (ctermDL hypTerm) bodyThm)
    val inst = beta_norm (Drule.infer_instantiate ctxtDL
          [(("P",0), ctermDL Pabs),(("Q",0), ctermDL goalT)] exE_vL)
  in Thm.implies_elim (Thm.implies_elim inst hEx) minor end;

(* natlist intro/elim on ctxtDL *)
fun lsumfNilL f = beta_norm (Drule.infer_instantiate ctxtDL [(("f",0), ctermDL f)] lsumf_nil_vL);
fun lsumfConsL (f,h,t) = beta_norm (Drule.infer_instantiate ctxtDL
      [(("f",0), ctermDL f),(("x",0), ctermDL h),(("t",0), ctermDL t)] lsumf_cons_vL);
fun lmemNilElimL x = beta_norm (Drule.infer_instantiate ctxtDL [(("x",0), ctermDL x)] lmem_nil_elim_vL);
fun lmemConsFwdL (x,y,t) = beta_norm (Drule.infer_instantiate ctxtDL
      [(("x",0), ctermDL x),(("y",0), ctermDL y),(("t",0), ctermDL t)] lmem_cons_fwd_vL);
fun lmemConsBwdL (x,y,t) = beta_norm (Drule.infer_instantiate ctxtDL
      [(("x",0), ctermDL x),(("y",0), ctermDL y),(("t",0), ctermDL t)] lmem_cons_bwd_vL);
val lnodupNilL = lnodup_nil_vL;
fun lnodupConsFwdL (x,t) = beta_norm (Drule.infer_instantiate ctxtDL
      [(("x",0), ctermDL x),(("t",0), ctermDL t)] lnodup_cons_fwd_vL);
fun lnodupConsBwdL (x,t) hConj = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtDL
      [(("x",0), ctermDL x),(("t",0), ctermDL t)] lnodup_cons_bwd_vL)) hConj;
fun list_induct_atL (Pabs, kT) = beta_norm (Drule.infer_instantiate ctxtDL
      [(("P",0), ctermDL Pabs),(("L",0), ctermDL kT)] list_induct_vL);
fun nat_induct_atL (Pabs, kT) = beta_norm (Drule.infer_instantiate ctxtDL
      [(("P",0), ctermDL Pabs),(("k",0), ctermDL kT)] nat_induct_vL);

(* leq transport on lists : leq A B ==> P A ==> P B *)
fun leq_transL (Pabs, AT, BT) hleq hPA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("P",0), ctermDL Pabs),(("L",0), ctermDL AT),(("M",0), ctermDL BT)] leq_subst_vL)
  in inst OF [hleq, hPA] end;
fun lmem_leqL (yT, LT, MT) hleq hmem =
  let val Pabs = Term.lambda (Free("zlm", natlistT)) (lmem yT (Free("zlm",natlistT)))
  in leq_transL (Pabs, LT, MT) hleq hmem end;
fun lsumf_leqL (f, LT, MT) hleq =
  let val Pabs = Term.lambda (Free("zLm", natlistT)) (oeq (lsumf f LT) (lsumf f (Free("zLm",natlistT))))
  in leq_transL (Pabs, LT, MT) hleq (reflL (lsumf f LT)) end;
fun lnodup_leqL (AT, BT) hleq hnd =
  let val Pabs = Term.lambda (Free("zN", natlistT)) (lnodup (Free("zN",natlistT)))
  in leq_transL (Pabs, AT, BT) hleq hnd end;
(* leqL symmetry : leq A B ==> leq B A *)
fun leqL_symL (AT, BT) hleq =
  let val Pabs = Term.lambda (Free("zS", natlistT)) (leqL (Free("zS",natlistT)) AT)
      val reflAA = beta_norm (Drule.infer_instantiate ctxtDL [(("L",0), ctermDL AT)] leq_refl_vL)
  in leq_transL (Pabs, AT, BT) hleq reflAA end;
(* add_eq_zero_left + Suc_neq_Zero on ctxtDL *)
val add_eq_zero_left_vL = upL add_eq_zero_left_vD;
val Suc_neq_Zero_vL     = upL Suc_neq_Zero_vD;

(* le on ctxtDL *)
fun le_introL (mT, nT, w) hyp =
  let val Pabs = Abs("p", natT, oeq nT (add mT (Bound 0)))
      val exI_inst = beta_norm (Drule.infer_instantiate ctxtDL
            [(("P",0), ctermDL Pabs),(("a",0), ctermDL w)] exI_vL)
  in Thm.implies_elim exI_inst hyp end;
val le_refl_vL  = upL le_refl_vEE;     (* le n n *)
val le_trans_vL = upL le_trans_vEE;    (* le m n ==> le n k ==> le m k *)
val le_antisym_vL = upL le_antisym_vEE; (* le m n ==> le n m ==> oeq m n *)
fun le_reflL t = beta_norm (Drule.infer_instantiate ctxtDL [(("n",0), ctermDL t)] le_refl_vL);
fun le_transL3 (mt,nt,kt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("m",0), ctermDL mt),(("n",0), ctermDL nt),(("k",0), ctermDL kt)] le_trans_vL)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun le_antisymL (mt,nt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("m",0), ctermDL mt),(("n",0), ctermDL nt)] le_antisym_vL)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
val add_Suc_vL       = upL add_Suc_vEE;       (* add (Suc m) n = Suc(add m n) *)
val add_Suc_right_vL = upL add_Suc_right_vD;  (* add m (Suc n) = Suc(add m n) *)
fun addSucL (m,n) = beta_norm (Drule.infer_instantiate ctxtDL
      [(("m",0), ctermDL m),(("n",0), ctermDL n)] add_Suc_vL);          (* add (Suc m) n = Suc(add m n) *)
fun addSrL (m,n) = beta_norm (Drule.infer_instantiate ctxtDL
      [(("m",0), ctermDL m),(("n",0), ctermDL n)] add_Suc_right_vL);    (* add m (Suc n) = Suc(add m n) *)
(* dvd_le on ctxtDL *)
fun dvd_leL (dT, nT) hdvd hnz =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("d",0), ctermDL dT),(("n",0), ctermDL nT)] dvd_le_vL)
  in Thm.implies_elim (Thm.implies_elim inst hdvd) hnz end;
(* lt0_of_suc on ctxtDL : oeq c (Suc m) ==> lt 0 c  (lt 0 c = le 1 c = ?p. c = 1 + p) *)
fun lt0_of_sucL (cT, mT) hcSm =
  let
    (* c = Suc m ; Suc m = add (Suc 0) m : add (Suc 0) m = Suc(add 0 m) = Suc m. so c = add 1 m. *)
    val aS  = addSucL (ZeroC, mT)         (* add (Suc 0) m = Suc(add 0 m) *)
    val a0  = add0L mT                     (* add 0 m = m *)
    val sCong = Suc_congL (add ZeroC mT, mT) a0   (* Suc(add 0 m) = Suc m *)
    val add1m_Sm = trans2L (aS, sCong)     (* add (Suc 0) m = Suc m *)
    val c_add1m = trans2L (hcSm, symmL add1m_Sm)  (* c = add (Suc 0) m *)
  in le_introL (suc ZeroC, cT, mT) c_add1m end;  (* le 1 c = lt 0 c *)

(* swt eval on ctxtDL : swt_dvd / swt_ndvd transferred *)
val swt_dvd_vL  = upL swt_dvd_vD;
val swt_ndvd_vL = upL swt_ndvd_vD;
fun swt_dvdL (dT, nT) hdvd =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtDL
    [(("d",0), ctermDL dT),(("n",0), ctermDL nT)] swt_dvd_vL)) hdvd;
fun swt_ndvdL (dT, nT) hndvd =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtDL
    [(("d",0), ctermDL dT),(("n",0), ctermDL nT)] swt_ndvd_vL)) hndvd;

(* dvl axioms on ctxtDL *)
fun dvla0L m = beta_norm (Drule.infer_instantiate ctxtDL [(("m",0), ctermDL m)] dvla_0_vL);
fun dvlaDvdL (k,m) hdvd = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtDL
      [(("k",0), ctermDL k),(("m",0), ctermDL m)] dvla_dvd_vL)) hdvd;
fun dvlaNdvdL (k,m) hndvd = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtDL
      [(("k",0), ctermDL k),(("m",0), ctermDL m)] dvla_ndvd_vL)) hndvd;
fun dvlDefL m = beta_norm (Drule.infer_instantiate ctxtDL [(("m",0), ctermDL m)] dvl_def_vL);

val () = out "DIVLIST_M_INFRA_OK\n";

(* ===========================================================================
   le_suc_cases : le d (Suc k) ==> Disj (le d k)(oeq d (Suc k))
     destruct le as ?p. Suc k = d + p ; dzos on p.
   =========================================================================== *)
fun le_suc_casesL (dT, kT) hle =   (* hle : le d (Suc k)  ->  Disj (le d k)(oeq d (Suc k)) *)
  let
    val Pabs = Abs("p", natT, oeq (suc kT) (add dT (Bound 0)))   (* body of le d (Suc k) *)
    val goalC = mkDisj (le dT kT)(oeq dT (suc kT))
    fun body pF hp =     (* hp : oeq (Suc k)(add d p) *)
      let
        val dz = dzosL pF    (* Disj (oeq p 0)(Ex q. p = Suc q) *)
        val caseP0 =
          let
            val hp0 = Thm.assume (ctermDL (jT (oeq pF ZeroC)))
            val cong = add_cong_rL (dT, pF, ZeroC) hp0    (* add d p = add d 0 *)
            val Sk_d0 = trans2L (hp, cong)                (* Suc k = add d 0 *)
            val Sk_d  = trans2L (Sk_d0, add0rL dT)        (* Suc k = d *)
            val d_Sk  = symmL Sk_d                        (* d = Suc k *)
            val g = disjI2_L (le dT kT, oeq dT (suc kT)) d_Sk
          in Thm.implies_intr (ctermDL (jT (oeq pF ZeroC))) g end
        val PabsQ = Abs("q", natT, oeq pF (suc (Bound 0)))
        val caseSuc =
          let
            val hex = Thm.assume (ctermDL (jT (mkEx PabsQ)))
            fun sbody qF hq =    (* hq : oeq p (Suc q) *)
              let
                val cong = add_cong_rL (dT, pF, suc qF) hq    (* add d p = add d (Suc q) *)
                val Sk_dSq = trans2L (hp, cong)               (* Suc k = add d (Suc q) *)
                (* add d (Suc q) = Suc(add d q) *)
                val dSq_S = addSrL (dT, qF)
                val Sk_Sdq = trans2L (Sk_dSq, dSq_S)          (* Suc k = Suc(add d q) *)
                val k_dq = Suc_injL (kT, add dT qF) Sk_Sdq    (* k = add d q *)
                val le_d_k = le_introL (dT, kT, qF) k_dq      (* le d k *)
                val g = disjI1_L (le dT kT, oeq dT (suc kT)) le_d_k
              in g end
            val r = exE_atL (PabsQ, goalC) hex "q_lsc" sbody
          in Thm.implies_intr (ctermDL (jT (mkEx PabsQ))) r end
      in disjE_L (oeq pF ZeroC, mkEx PabsQ, goalC) dz caseP0 caseSuc end
  in exE_atL (Pabs, goalC) hle "p_lsc" body end;
val () = out "DIVLIST_M_LE_SUC_CASES_OK\n";

(* ===========================================================================
   LEMMA A : dvla member properties (induction on k)
     lmem d (dvla k m) ==> Conj (lt 0 d) (Conj (le d k) (dvd d m))
   reflected as object-Forall over d so the predicate is over k:nat.
   =========================================================================== *)
val dvla_member_props =
  let
    val mF = Free("m", natT)
    fun propBody dt kt = mkConj (lt ZeroC dt) (mkConj (le dt kt) (dvd dt mF))
    fun bodyConcl kt = mkForall (Term.lambda (Free("d", natT))
                         (mkImp (lmem (Free("d",natT)) (dvla kt mF)) (propBody (Free("d",natT)) kt)))
    val zV = Free("z", natT)
    val Qpred = Term.lambda zV (bodyConcl zV)
    val kIndA = Free("k", natT)
    val ind = nat_induct_atL (Qpred, kIndA)
    (* base k=0 : dvla 0 m = lnil ; lmem d lnil is absurd. *)
    val base =
      let
        fun perD dF =
          let
            val hmem = Thm.assume (ctermDL (jT (lmem dF (dvla ZeroC mF))))
            (* dvla 0 m = lnil : transport membership to lnil -> absurd *)
            val dleq = dvla0L mF                                   (* leq (dvla 0 m) lnil *)
            val memNil = lmem_leqL (dF, dvla ZeroC mF, lnilC) dleq hmem   (* lmem d lnil *)
            val ff  = Thm.implies_elim (lmemNilElimL dF) memNil          (* oFalse *)
            val res = Thm.implies_elim (oFalse_elimL (propBody dF ZeroC)) ff
          in impI_L (lmem dF (dvla ZeroC mF), propBody dF ZeroC) res end
        val dFb = Free("d_b", natT)
      in allI_L (Term.lambda (Free("d", natT))
                  (mkImp (lmem (Free("d",natT)) (dvla ZeroC mF)) (propBody (Free("d",natT)) ZeroC)))
                (Thm.forall_intr (ctermDL dFb) (perD dFb)) end
    (* step k -> Suc k : split on dvd (Suc k) m via ex_middle. *)
    val xF = Free("x", natT)
    val IH = Thm.assume (ctermDL (jT (bodyConcl xF)))
    val stepconcl =
      let
        val Sx = suc xF
        fun perD dF =
          let
            val hmem = Thm.assume (ctermDL (jT (lmem dF (dvla Sx mF))))
            val goal = propBody dF Sx
            val em = exMiddleL (dvd Sx mF)   (* Disj (dvd (Suc x) m)(neg(dvd (Suc x) m)) *)
            (* CASE dvd (Suc x) m : dvla (Suc x) m = lcons (Suc x)(dvla x m). *)
            val caseDvd =
              let
                val hdvdSx = Thm.assume (ctermDL (jT (dvd Sx mF)))
                val dleq = dvlaDvdL (xF, mF) hdvdSx      (* leq (dvla (Suc x) m)(lcons (Suc x)(dvla x m)) *)
                val memCons = lmem_leqL (dF, dvla Sx mF, lcons Sx (dvla xF mF)) dleq hmem  (* lmem d (lcons (Suc x)(dvla x m)) *)
                (* fwd : Disj (oeq d (Suc x))(lmem d (dvla x m)) *)
                val dj = Thm.implies_elim (lmemConsFwdL (dF, Sx, dvla xF mF)) memCons
                (* subcase d = Suc x : lt 0 (Suc x) [lt0_of_suc with Suc x = Suc x], le (Suc x)(Suc x) [refl], dvd (Suc x) m -> dvd d m. *)
                val caseEq =
                  let
                    val heq = Thm.assume (ctermDL (jT (oeq dF Sx)))   (* d = Suc x *)
                    (* lt 0 d : d = Suc x -> lt 0 d. *)
                    val lt0d = lt0_of_sucL (dF, xF) heq               (* lt 0 d *)
                    (* le d (Suc x) : d = Suc x -> le d (Suc x) via refl + subst. le (Suc x)(Suc x) is le_refl. *)
                    val leSxSx = le_reflL Sx                          (* le (Suc x)(Suc x) *)
                    val Ple = Term.lambda (Free("zle", natT)) (le (Free("zle",natT)) Sx)
                    val led = substPredL (Ple, Sx, dF) (symmL heq) leSxSx   (* le d (Suc x) *)
                    (* dvd d m : d = Suc x, dvd (Suc x) m -> dvd d m via subst on divisor slot. *)
                    val Pdvd = Term.lambda (Free("zdv", natT)) (dvd (Free("zdv",natT)) mF)
                    val dvdd = substPredL (Pdvd, Sx, dF) (symmL heq) hdvdSx  (* dvd d m *)
                    val conj = conjI_L (lt ZeroC dF, mkConj (le dF Sx)(dvd dF mF)) lt0d
                                 (conjI_L (le dF Sx, dvd dF mF) led dvdd)
                  in Thm.implies_intr (ctermDL (jT (oeq dF Sx))) conj end
                (* subcase lmem d (dvla x m) : IH at d -> Conj(lt 0 d)(Conj(le d x)(dvd d m)) ; lift le d x to le d (Suc x). *)
                val caseMem =
                  let
                    val hmemx = Thm.assume (ctermDL (jT (lmem dF (dvla xF mF))))
                    val ihAt = allE_L (Term.lambda (Free("d", natT))
                                 (mkImp (lmem (Free("d",natT)) (dvla xF mF)) (propBody (Free("d",natT)) xF)), dF) IH
                    val props = mp_L (lmem dF (dvla xF mF), propBody dF xF) ihAt hmemx  (* Conj(lt 0 d)(Conj(le d x)(dvd d m)) *)
                    val lt0d = conjunct1_L (lt ZeroC dF, mkConj (le dF xF)(dvd dF mF)) props
                    val rest = conjunct2_L (lt ZeroC dF, mkConj (le dF xF)(dvd dF mF)) props
                    val ledx = conjunct1_L (le dF xF, dvd dF mF) rest   (* le d x *)
                    val dvdd = conjunct2_L (le dF xF, dvd dF mF) rest   (* dvd d m *)
                    (* le d (Suc x) : le d x and le x (Suc x) -> le_trans.  le x (Suc x) witness Suc 0. *)
                    val lex_Sx =
                      let
                        val aS = addSucL (xF, ZeroC)        (* add (Suc 0) x ... wait need add x (Suc 0) *)
                      in le_introL (xF, Sx, suc ZeroC)
                           (let val aSr = addSrL (xF, ZeroC)        (* add x (Suc 0) = Suc(add x 0) *)
                                val a0r = add0rL xF                  (* add x 0 = x *)
                                val sc  = Suc_congL (add xF ZeroC, xF) a0r  (* Suc(add x 0) = Suc x *)
                                val axS1 = trans2L (aSr, sc)         (* add x (Suc 0) = Suc x *)
                            in symmL axS1 end)                       (* Suc x = add x (Suc 0) *)
                      end
                    val led_Sx = le_transL3 (dF, xF, Sx) ledx lex_Sx   (* le d (Suc x) *)
                    val conj = conjI_L (lt ZeroC dF, mkConj (le dF Sx)(dvd dF mF)) lt0d
                                 (conjI_L (le dF Sx, dvd dF mF) led_Sx dvdd)
                  in Thm.implies_intr (ctermDL (jT (lmem dF (dvla xF mF)))) conj end
                val res = disjE_L (oeq dF Sx, lmem dF (dvla xF mF), goal) dj caseEq caseMem
              in Thm.implies_intr (ctermDL (jT (dvd Sx mF))) res end
            (* CASE neg(dvd (Suc x) m) : dvla (Suc x) m = dvla x m. *)
            val caseNdvd =
              let
                val hndvdSx = Thm.assume (ctermDL (jT (neg (dvd Sx mF))))
                val dleq = dvlaNdvdL (xF, mF) hndvdSx     (* leq (dvla (Suc x) m)(dvla x m) *)
                val memx = lmem_leqL (dF, dvla Sx mF, dvla xF mF) dleq hmem  (* lmem d (dvla x m) *)
                val ihAt = allE_L (Term.lambda (Free("d", natT))
                             (mkImp (lmem (Free("d",natT)) (dvla xF mF)) (propBody (Free("d",natT)) xF)), dF) IH
                val props = mp_L (lmem dF (dvla xF mF), propBody dF xF) ihAt memx
                val lt0d = conjunct1_L (lt ZeroC dF, mkConj (le dF xF)(dvd dF mF)) props
                val rest = conjunct2_L (lt ZeroC dF, mkConj (le dF xF)(dvd dF mF)) props
                val ledx = conjunct1_L (le dF xF, dvd dF mF) rest
                val dvdd = conjunct2_L (le dF xF, dvd dF mF) rest
                val lex_Sx = le_introL (xF, Sx, suc ZeroC)
                       (let val aSr = addSrL (xF, ZeroC)
                            val a0r = add0rL xF
                            val sc  = Suc_congL (add xF ZeroC, xF) a0r
                            val axS1 = trans2L (aSr, sc)
                        in symmL axS1 end)
                val led_Sx = le_transL3 (dF, xF, Sx) ledx lex_Sx
                val conj = conjI_L (lt ZeroC dF, mkConj (le dF Sx)(dvd dF mF)) lt0d
                             (conjI_L (le dF Sx, dvd dF mF) led_Sx dvdd)
              in Thm.implies_intr (ctermDL (jT (neg (dvd Sx mF)))) conj end
            val res = disjE_L (dvd Sx mF, neg (dvd Sx mF), goal) em caseDvd caseNdvd
          in impI_L (lmem dF (dvla Sx mF), goal) res end
        val dFb = Free("d_s", natT)
      in allI_L (Term.lambda (Free("d", natT))
                  (mkImp (lmem (Free("d",natT)) (dvla Sx mF)) (propBody (Free("d",natT)) Sx)))
                (Thm.forall_intr (ctermDL dFb) (perD dFb)) end
    val step1 = Thm.forall_intr (ctermDL xF) (Thm.implies_intr (ctermDL (jT (bodyConcl xF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in varify r2 end;
val () = out "DIVLIST_M_LEMMA_A_BUILT\n";

(* ===========================================================================
   LEMMA B : completeness (backward), induction on k
     lt 0 d ==> le d k ==> dvd d m ==> lmem d (dvla k m)
   reflected as object-Forall over d.
   =========================================================================== *)
val dvla_complete_bwd =
  let
    val mF = Free("m", natT)
    fun bodyImp dt kt = mkImp (lt ZeroC dt) (mkImp (le dt kt) (mkImp (dvd dt mF) (lmem dt (dvla kt mF))))
    fun bodyConcl kt = mkForall (Term.lambda (Free("d", natT)) (bodyImp (Free("d",natT)) kt))
    val zV = Free("z", natT)
    val Qpred = Term.lambda zV (bodyConcl zV)
    val kIndA = Free("k", natT)
    val ind = nat_induct_atL (Qpred, kIndA)
    (* base k=0 : le d 0 + lt 0 d is contradictory -> lmem d (dvla 0 m) vacuously. *)
    val base =
      let
        fun perD dF =
          let
            val hlt0 = Thm.assume (ctermDL (jT (lt ZeroC dF)))     (* le (Suc 0) d : ?p. d = 1 + p *)
            val hle0 = Thm.assume (ctermDL (jT (le dF ZeroC)))     (* ?p. 0 = d + p *)
            val hdvd = Thm.assume (ctermDL (jT (dvd dF mF)))
            (* from le d 0 : d = 0. *)
            val PabsLe = Abs("p", natT, oeq ZeroC (add dF (Bound 0)))
            val d_eq_0 =
              let
                fun body pF hp =     (* hp : oeq 0 (add d p) *)
                  let val hps = symmL hp    (* add d p = 0 *)
                      val aez = beta_norm (Drule.infer_instantiate ctxtDL
                            [(("a",0), ctermDL dF),(("b",0), ctermDL pF)] (upL add_eq_zero_left_vL))
                  in Thm.implies_elim aez hps end    (* oeq d 0 *)
              in exE_atL (PabsLe, oeq dF ZeroC) hle0 "p_b0" body end
            (* lt 0 d = le (Suc 0) d : ?p. d = 1 + p ; d = 0 -> 1 + p = 0 -> Suc(0+p)=0 absurd. *)
            val PabsLt = Abs("p", natT, oeq dF (add (suc ZeroC) (Bound 0)))
            val ff =
              let
                fun body pF hp =    (* hp : oeq d (add (Suc 0) p) *)
                  let
                    (* d = 0 -> 0 = add (Suc 0) p ; add (Suc 0) p = Suc(add 0 p) ; so Suc(..)=0 absurd. *)
                    val z_eq_add = trans2L (symmL d_eq_0, hp)   (* 0 = add (Suc 0) p *)
                    val aS = addSucL (ZeroC, pF)                (* add (Suc 0) p = Suc(add 0 p) *)
                    val z_eq_S = trans2L (z_eq_add, aS)         (* 0 = Suc(add 0 p) *)
                    val S_eq_z = symmL z_eq_S                   (* Suc(add 0 p) = 0 *)
                    val snz = beta_norm (Drule.infer_instantiate ctxtDL
                                [(("n",0), ctermDL (add ZeroC pF))] Suc_neq_Zero_vL)  (* Suc(add 0 p)=0 ==> oFalse *)
                  in Thm.implies_elim snz S_eq_z end
              in exE_atL (PabsLt, oFalseC) hlt0 "p_lt0" body end
            val res = Thm.implies_elim (oFalse_elimL (lmem dF (dvla ZeroC mF))) ff
            val i3 = impI_L (dvd dF mF, lmem dF (dvla ZeroC mF)) res
            val i2 = impI_L (le dF ZeroC, mkImp (dvd dF mF)(lmem dF (dvla ZeroC mF))) i3
            val i1 = impI_L (lt ZeroC dF, mkImp (le dF ZeroC)(mkImp (dvd dF mF)(lmem dF (dvla ZeroC mF)))) i2
          in i1 end
        val dFb = Free("d_b", natT)
      in allI_L (Term.lambda (Free("d", natT)) (bodyImp (Free("d",natT)) ZeroC))
                (Thm.forall_intr (ctermDL dFb) (perD dFb)) end
    (* step k -> Suc k *)
    val xF = Free("x", natT)
    val IH = Thm.assume (ctermDL (jT (bodyConcl xF)))
    val stepconcl =
      let
        val Sx = suc xF
        fun perD dF =
          let
            val hlt0 = Thm.assume (ctermDL (jT (lt ZeroC dF)))
            val hleSx= Thm.assume (ctermDL (jT (le dF Sx)))
            val hdvd = Thm.assume (ctermDL (jT (dvd dF mF)))
            val goal = lmem dF (dvla Sx mF)
            val lsc = le_suc_casesL (dF, xF) hleSx   (* Disj (le d x)(oeq d (Suc x)) *)
            (* helper : given lmem d (dvla x m), produce lmem d (dvla (Suc x) m) by split on dvd (Suc x) m. *)
            fun lift_from_x hmemx =
              let
                val em = exMiddleL (dvd Sx mF)
                val caseDvd =
                  let
                    val hd = Thm.assume (ctermDL (jT (dvd Sx mF)))
                    val dleq = dvlaDvdL (xF, mF) hd     (* leq (dvla (Suc x) m)(lcons (Suc x)(dvla x m)) *)
                    val memCons = Thm.implies_elim (lmemConsBwdL (dF, Sx, dvla xF mF))
                                    (disjI2_L (oeq dF Sx, lmem dF (dvla xF mF)) hmemx)  (* lmem d (lcons (Suc x)(dvla x m)) *)
                    val r = lmem_leqL (dF, lcons Sx (dvla xF mF), dvla Sx mF) (leqL_symL (dvla Sx mF, lcons Sx (dvla xF mF)) dleq) memCons
                  in Thm.implies_intr (ctermDL (jT (dvd Sx mF))) r end
                val caseNdvd =
                  let
                    val hn = Thm.assume (ctermDL (jT (neg (dvd Sx mF))))
                    val dleq = dvlaNdvdL (xF, mF) hn    (* leq (dvla (Suc x) m)(dvla x m) *)
                    val r = lmem_leqL (dF, dvla xF mF, dvla Sx mF) (leqL_symL (dvla Sx mF, dvla xF mF) dleq) hmemx
                  in Thm.implies_intr (ctermDL (jT (neg (dvd Sx mF)))) r end
              in disjE_L (dvd Sx mF, neg (dvd Sx mF), goal) em caseDvd caseNdvd end
            (* case le d x : IH at d gives lmem d (dvla x m), then lift. *)
            val caseLe =
              let
                val hle = Thm.assume (ctermDL (jT (le dF xF)))
                val ihAt = allE_L (Term.lambda (Free("d", natT)) (bodyImp (Free("d",natT)) xF), dF) IH
                val s1 = mp_L (lt ZeroC dF, mkImp (le dF xF)(mkImp (dvd dF mF)(lmem dF (dvla xF mF)))) ihAt hlt0
                val s2 = mp_L (le dF xF, mkImp (dvd dF mF)(lmem dF (dvla xF mF))) s1 hle
                val hmemx = mp_L (dvd dF mF, lmem dF (dvla xF mF)) s2 hdvd   (* lmem d (dvla x m) *)
              in Thm.implies_intr (ctermDL (jT (le dF xF))) (lift_from_x hmemx) end
            (* case d = Suc x : dvd d m = dvd (Suc x) m ; dvla (Suc x) m = lcons (Suc x)(dvla x m) ; lmem d via left disj. *)
            val caseEq =
              let
                val heq = Thm.assume (ctermDL (jT (oeq dF Sx)))   (* d = Suc x *)
                (* dvd (Suc x) m from dvd d m + d = Suc x *)
                val Pdvd = Term.lambda (Free("zdv", natT)) (dvd (Free("zdv",natT)) mF)
                val dvdSx = substPredL (Pdvd, dF, Sx) heq hdvd     (* dvd (Suc x) m *)
                val dleq = dvlaDvdL (xF, mF) dvdSx                 (* leq (dvla (Suc x) m)(lcons (Suc x)(dvla x m)) *)
                val memCons = Thm.implies_elim (lmemConsBwdL (dF, Sx, dvla xF mF))
                                (disjI1_L (oeq dF Sx, lmem dF (dvla xF mF)) heq)   (* lmem d (lcons (Suc x)(dvla x m)) *)
                val r = lmem_leqL (dF, lcons Sx (dvla xF mF), dvla Sx mF)
                          (leqL_symL (dvla Sx mF, lcons Sx (dvla xF mF)) dleq) memCons
              in Thm.implies_intr (ctermDL (jT (oeq dF Sx))) r end
            val res = disjE_L (le dF xF, oeq dF Sx, goal) lsc caseLe caseEq
            val i3 = impI_L (dvd dF mF, lmem dF (dvla Sx mF)) res
            val i2 = impI_L (le dF Sx, mkImp (dvd dF mF)(lmem dF (dvla Sx mF))) i3
            val i1 = impI_L (lt ZeroC dF, mkImp (le dF Sx)(mkImp (dvd dF mF)(lmem dF (dvla Sx mF)))) i2
          in i1 end
        val dFb = Free("d_s", natT)
      in allI_L (Term.lambda (Free("d", natT)) (bodyImp (Free("d",natT)) Sx))
                (Thm.forall_intr (ctermDL dFb) (perD dFb)) end
    val step1 = Thm.forall_intr (ctermDL xF) (Thm.implies_intr (ctermDL (jT (bodyConcl xF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in varify r2 end;
val () = out "DIVLIST_M_LEMMA_B_BUILT\n";

(* lt_irrefl on ctxtDL : lt n n ==> oFalse *)
val lt_irrefl_vL = upL lt_irrefl_vEE;
fun lt_irreflL t h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtDL
      [(("n",0), ctermDL t)] lt_irrefl_vL)) h;

(* ===========================================================================
   LEMMA C : lnodup (dvla k m)   (induction on k)
   Step (dvd case) needs : (Suc k) not in (dvla k m), because every member <= k
   < Suc k.  lmem (Suc k)(dvla k m) -> le (Suc k) k [Lemma A] = lt k k -> absurd.
   =========================================================================== *)
val dvla_member_props_vL = dvla_member_props;   (* already varified, vars m,k? : it's Forall over d, vars m and the k slot *)
val dvla_nodup =
  let
    val mF = Free("m", natT)
    fun bodyC kt = lnodup (dvla kt mF)
    val zV = Free("z", natT)
    val Qpred = Term.lambda zV (bodyC zV)
    val kIndA = Free("k", natT)
    val ind = nat_induct_atL (Qpred, kIndA)
    (* base k=0 : dvla 0 m = lnil ; lnodup lnil ; transport. *)
    val base =
      let
        val dleq = dvla0L mF                                   (* leq (dvla 0 m) lnil *)
        val ndNil = lnodupNilL                                 (* lnodup lnil *)
        val r = lnodup_leqL (lnilC, dvla ZeroC mF) (leqL_symL (dvla ZeroC mF, lnilC) dleq) ndNil
      in r end
    (* step k -> Suc k *)
    val xF = Free("x", natT)
    val Sx = suc xF
    val IH = Thm.assume (ctermDL (jT (bodyC xF)))             (* lnodup (dvla x m) *)
    val stepconcl =
      let
        val em = exMiddleL (dvd Sx mF)
        val caseDvd =
          let
            val hd = Thm.assume (ctermDL (jT (dvd Sx mF)))
            val dleq = dvlaDvdL (xF, mF) hd     (* leq (dvla (Suc x) m)(lcons (Suc x)(dvla x m)) *)
            (* neg (lmem (Suc x)(dvla x m)) *)
            val notmem =
              let
                val hmem = Thm.assume (ctermDL (jT (lmem Sx (dvla xF mF))))
                (* Lemma A at (k=x, d=Suc x) : lmem (Suc x)(dvla x m) -> Conj(lt 0 (Suc x))(Conj(le (Suc x) x)(dvd (Suc x) m)) *)
                val maInst = beta_norm (Drule.infer_instantiate ctxtDL
                               [(("m",0), ctermDL mF),(("k",0), ctermDL xF)] dvla_member_props_vL)
                              (* Forall d. lmem d (dvla x m) -> Conj(lt 0 d)(Conj(le d x)(dvd d m)) *)
                val atSx = allE_L (Term.lambda (Free("d", natT))
                             (mkImp (lmem (Free("d",natT)) (dvla xF mF))
                                    (mkConj (lt ZeroC (Free("d",natT))) (mkConj (le (Free("d",natT)) xF) (dvd (Free("d",natT)) mF)))), Sx) maInst
                val props = mp_L (lmem Sx (dvla xF mF),
                              mkConj (lt ZeroC Sx)(mkConj (le Sx xF)(dvd Sx mF))) atSx hmem
                val rest = conjunct2_L (lt ZeroC Sx, mkConj (le Sx xF)(dvd Sx mF)) props
                val leSxx = conjunct1_L (le Sx xF, dvd Sx mF) rest   (* le (Suc x) x = lt x x *)
                val ff = lt_irreflL xF leSxx                         (* oFalse *)
              in impI_L (lmem Sx (dvla xF mF), oFalseC) ff end   (* object neg *)
            val conj = conjI_L (neg (lmem Sx (dvla xF mF)), lnodup (dvla xF mF)) notmem IH
            val ndCons = lnodupConsBwdL (Sx, dvla xF mF) conj    (* lnodup (lcons (Suc x)(dvla x m)) *)
            val r = lnodup_leqL (lcons Sx (dvla xF mF), dvla Sx mF)
                      (leqL_symL (dvla Sx mF, lcons Sx (dvla xF mF)) dleq) ndCons
          in Thm.implies_intr (ctermDL (jT (dvd Sx mF))) r end
        val caseNdvd =
          let
            val hn = Thm.assume (ctermDL (jT (neg (dvd Sx mF))))
            val dleq = dvlaNdvdL (xF, mF) hn    (* leq (dvla (Suc x) m)(dvla x m) *)
            val r = lnodup_leqL (dvla xF mF, dvla Sx mF) (leqL_symL (dvla Sx mF, dvla xF mF) dleq) IH
          in Thm.implies_intr (ctermDL (jT (neg (dvd Sx mF)))) r end
      in disjE_L (dvd Sx mF, neg (dvd Sx mF), bodyC Sx) em caseDvd caseNdvd end
    val step1 = Thm.forall_intr (ctermDL xF) (Thm.implies_intr (ctermDL (jT (bodyC xF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in varify r2 end;
val () = out "DIVLIST_M_LEMMA_C_BUILT\n";

(* ===========================================================================
   ASSEMBLY (i) : COMPLETENESS of dvl m, stated as a Forall of the iff-as-conj
     !!d. (lmem d (dvl m) ==> Conj(lt 0 d)(Conj(le d m)(dvd d m)))
       /\ (Conj(lt 0 d)(Conj(le d m)(dvd d m)) ==> lmem d (dvl m))
   0-hyp, m schematic.
   =========================================================================== *)
val dvl_complete =
  let
    val mF = Free("m", natT)
    fun rhs dt = mkConj (lt ZeroC dt) (mkConj (le dt mF) (dvd dt mF))
    fun iffBody dt = mkConj (mkImp (lmem dt (dvl mF)) (rhs dt))
                            (mkImp (rhs dt) (lmem dt (dvl mF)))
    val ddef = dvlDefL mF                                   (* leq (dvl m)(dvla m m) *)
    fun perD dF =
      let
        (* FORWARD : lmem d (dvl m) -> rhs d *)
        val fwd =
          let
            val hmem = Thm.assume (ctermDL (jT (lmem dF (dvl mF))))
            (* transport to dvla m m *)
            val memDvla = lmem_leqL (dF, dvl mF, dvla mF mF) ddef hmem  (* lmem d (dvla m m) *)
            val maInst = beta_norm (Drule.infer_instantiate ctxtDL
                           [(("m",0), ctermDL mF),(("k",0), ctermDL mF)] dvla_member_props_vL)
            val atd = allE_L (Term.lambda (Free("d", natT))
                        (mkImp (lmem (Free("d",natT)) (dvla mF mF))
                               (mkConj (lt ZeroC (Free("d",natT))) (mkConj (le (Free("d",natT)) mF) (dvd (Free("d",natT)) mF)))), dF) maInst
            val props = mp_L (lmem dF (dvla mF mF), rhs dF) atd memDvla
          in impI_L (lmem dF (dvl mF), rhs dF) props end
        (* BACKWARD : rhs d -> lmem d (dvl m) *)
        val bwd =
          let
            val hrhs = Thm.assume (ctermDL (jT (rhs dF)))
            val lt0d = conjunct1_L (lt ZeroC dF, mkConj (le dF mF)(dvd dF mF)) hrhs
            val rest = conjunct2_L (lt ZeroC dF, mkConj (le dF mF)(dvd dF mF)) hrhs
            val ledm = conjunct1_L (le dF mF, dvd dF mF) rest
            val dvdd = conjunct2_L (le dF mF, dvd dF mF) rest
            (* Lemma B at (k=m) : lt 0 d -> le d m -> dvd d m -> lmem d (dvla m m) *)
            val bInst = beta_norm (Drule.infer_instantiate ctxtDL
                          [(("m",0), ctermDL mF),(("k",0), ctermDL mF)] dvla_complete_bwd)
            val atd = allE_L (Term.lambda (Free("d", natT))
                        (mkImp (lt ZeroC (Free("d",natT))) (mkImp (le (Free("d",natT)) mF) (mkImp (dvd (Free("d",natT)) mF) (lmem (Free("d",natT)) (dvla mF mF))))), dF) bInst
            val s1 = mp_L (lt ZeroC dF, mkImp (le dF mF)(mkImp (dvd dF mF)(lmem dF (dvla mF mF)))) atd lt0d
            val s2 = mp_L (le dF mF, mkImp (dvd dF mF)(lmem dF (dvla mF mF))) s1 ledm
            val memDvla = mp_L (dvd dF mF, lmem dF (dvla mF mF)) s2 dvdd  (* lmem d (dvla m m) *)
            (* transport back to dvl m via sym of dvl_def *)
            val r = lmem_leqL (dF, dvla mF mF, dvl mF) (leqL_symL (dvl mF, dvla mF mF) ddef) memDvla
          in impI_L (rhs dF, lmem dF (dvl mF)) r end
        val conj = conjI_L (mkImp (lmem dF (dvl mF)) (rhs dF), mkImp (rhs dF) (lmem dF (dvl mF))) fwd bwd
      in conj end
    val dFb = Free("d_c", natT)
    val r = allI_L (Term.lambda (Free("d", natT)) (iffBody (Free("d",natT))))
              (Thm.forall_intr (ctermDL dFb) (perD dFb))
  in varify r end;

val mVc = Var(("m",0), natT)
val i_dvl_complete =
  let val dV = Free("d", natT)
      fun rhsV dt = mkConj (lt ZeroC dt) (mkConj (le dt mVc) (dvd dt mVc))
  in jT (mkForall (Term.lambda dV
       (mkConj (mkImp (lmem dV (dvl mVc)) (rhsV dV))
               (mkImp (rhsV dV) (lmem dV (dvl mVc)))))) end;
val r_complete = chkDL ("dvl_complete", dvl_complete, i_dvl_complete);
val () = if r_complete then out "DVL_COMPLETE_OK\n" else out "DVL_COMPLETE_FAIL\n";

(* ===========================================================================
   ASSEMBLY (ii) : lnodup (dvl m)
   =========================================================================== *)
val dvl_nodup =
  let
    val mF = Free("m", natT)
    val ddef = dvlDefL mF                       (* leq (dvl m)(dvla m m) *)
    val ndDvla = beta_norm (Drule.infer_instantiate ctxtDL
                   [(("m",0), ctermDL mF),(("k",0), ctermDL mF)] dvla_nodup)  (* lnodup (dvla m m) *)
    val r = lnodup_leqL (dvla mF mF, dvl mF) (leqL_symL (dvl mF, dvla mF mF) ddef) ndDvla
  in varify r end;
val i_dvl_nodup = jT (lnodup (dvl mVc));
val r_nodup = chkDL ("dvl_nodup", dvl_nodup, i_dvl_nodup);
val () = if r_nodup then out "DVL_NODUP_OK\n" else out "DVL_NODUP_FAIL\n";
val () = out "DIVLIST_M_ASSEMBLY_I_II_DONE\n";

(* ===========================================================================
   ASSEMBLY (iii) : lsumf idw (dvl m) = sigma m   (the support bridge).
     sum_supp_collapse (f = swt m, L = dvl m, N = m) : sumf (swt m) m = lsumf (swt m)(dvl m)
     sigma_def : sigma m = sumf (swt m) m
     lsumf_cong (swt m -> idw on members, since members divide m) :
       lsumf (swt m)(dvl m) = lsumf idw (dvl m)
   ============================================================================ *)
(* lsumf_cong on ctxtDL : (!!d. lmem d L ==> oeq (f d)(g d)) [object Forall] ==> lsumf f L = lsumf g L *)
fun apply_lsumf_congL (fT, gT, LT) perMemThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("f",0), ctermDL fT),(("g",0), ctermDL gT),(("L",0), ctermDL LT)] lsumf_cong_vL)
      val forallT = mkForall (Term.lambda (Free("dd",natT))
              (mkImp (lmem (Free("dd",natT)) LT)(oeq (fT $ (Free("dd",natT)))(gT $ (Free("dd",natT))))))
  in mp_L (forallT, oeq (lsumf fT LT)(lsumf gT LT)) inst perMemThm end;

val dvl_sigma =
  let
    val mF = Free("m", natT)
    val L  = dvl mF
    val swtm = swtC $ mF                      (* swt m : nat=>nat *)
    (* completeness instance (object Forall iff) *)
    val compInst = beta_norm (Drule.infer_instantiate ctxtDL [(("m",0), ctermDL mF)] dvl_complete)
    fun rhsP dt = mkConj (lt ZeroC dt) (mkConj (le dt mF) (dvd dt mF))
    fun iffP dt = mkConj (mkImp (lmem dt L) (rhsP dt)) (mkImp (rhsP dt) (lmem dt L))
    (* nodup *)
    val hnodup = beta_norm (Drule.infer_instantiate ctxtDL [(("m",0), ctermDL mF)] dvl_nodup)  (* lnodup (dvl m) *)
    (* H1 meta : !!d. le d m ==> Disj (lmem d (dvl m))(swt m d = 0) *)
    val h1meta =
      let
        val dF = Free("d_h1", natT)
        val hle = Thm.assume (ctermDL (jT (le dF mF)))
        val goalD = mkDisj (lmem dF L)(oeq (swtm $ dF) ZeroC)
        (* split on dvd d m *)
        val em = exMiddleL (dvd dF mF)
        val caseDvd =
          let
            val hd = Thm.assume (ctermDL (jT (dvd dF mF)))
            (* split d : 0 or Suc *)
            val dz = dzosL dF   (* Disj (oeq d 0)(Ex q. d = Suc q) *)
            val caseD0 =
              let
                val hd0 = Thm.assume (ctermDL (jT (oeq dF ZeroC)))   (* d = 0 *)
                (* swt m d = d (swt_dvd dvd d m) = 0 (d=0).  swt m d -> right disj. *)
                val sw = swt_dvdL (dF, mF) hd      (* oeq (swt m d) d *)
                val sw0 = trans2L (sw, hd0)        (* oeq (swt m d) 0 *)
                (* swtm $ dF beta = swt m d *)
                val g = disjI2_L (lmem dF L, oeq (swtm $ dF) ZeroC) sw0
              in Thm.implies_intr (ctermDL (jT (oeq dF ZeroC))) g end
            val PsucE = Abs("q", natT, oeq dF (suc (Bound 0)))
            val caseDS =
              let
                val hex = Thm.assume (ctermDL (jT (mkEx PsucE)))
                fun sbody qF hq =    (* hq : d = Suc q ; lt 0 d via lt0_of_suc *)
                  let
                    val lt0d = lt0_of_sucL (dF, qF) hq    (* lt 0 d *)
                    (* completeness backward : rhs d -> lmem d (dvl m) *)
                    val bwd = conjunct2_L (mkImp (lmem dF L)(rhsP dF), mkImp (rhsP dF)(lmem dF L))
                                (allE_L (Term.lambda (Free("d",natT)) (iffP (Free("d",natT))), dF) compInst)
                    val rhsThm = conjI_L (lt ZeroC dF, mkConj (le dF mF)(dvd dF mF)) lt0d
                                   (conjI_L (le dF mF, dvd dF mF) hle hd)
                    val memd = mp_L (rhsP dF, lmem dF L) bwd rhsThm   (* lmem d (dvl m) *)
                    val g = disjI1_L (lmem dF L, oeq (swtm $ dF) ZeroC) memd
                  in g end
                val r = exE_atL (PsucE, goalD) hex "q_h1" sbody
              in Thm.implies_intr (ctermDL (jT (mkEx PsucE))) r end
            val resD = disjE_L (oeq dF ZeroC, mkEx PsucE, goalD) dz caseD0 caseDS
          in Thm.implies_intr (ctermDL (jT (dvd dF mF))) resD end
        val caseNdvd =
          let
            val hn = Thm.assume (ctermDL (jT (neg (dvd dF mF))))
            val sw0 = swt_ndvdL (dF, mF) hn       (* oeq (swt m d) 0 *)
            val g = disjI2_L (lmem dF L, oeq (swtm $ dF) ZeroC) sw0
          in Thm.implies_intr (ctermDL (jT (neg (dvd dF mF)))) g end
        val concl = disjE_L (dvd dF mF, neg (dvd dF mF), goalD) em caseDvd caseNdvd
      in Thm.forall_intr (ctermDL dF) (Thm.implies_intr (ctermDL (jT (le dF mF))) concl) end
    (* H2 meta : !!d. lmem d (dvl m) ==> le d m *)
    val h2meta =
      let
        val dF = Free("d_h2", natT)
        val hmem = Thm.assume (ctermDL (jT (lmem dF L)))
        val fwd = conjunct1_L (mkImp (lmem dF L)(rhsP dF), mkImp (rhsP dF)(lmem dF L))
                    (allE_L (Term.lambda (Free("d",natT)) (iffP (Free("d",natT))), dF) compInst)
        val rhsThm = mp_L (lmem dF L, rhsP dF) fwd hmem   (* Conj(lt 0 d)(Conj(le d m)(dvd d m)) *)
        val rest = conjunct2_L (lt ZeroC dF, mkConj (le dF mF)(dvd dF mF)) rhsThm
        val ledm = conjunct1_L (le dF mF, dvd dF mF) rest   (* le d m *)
      in Thm.forall_intr (ctermDL dF) (Thm.implies_intr (ctermDL (jT (lmem dF L))) ledm) end
    (* sum_supp_collapse [f=swt m, L=dvl m, N=m] *)
    val ssc = beta_norm (Drule.infer_instantiate ctxtDL
                [(("f",0), ctermDL swtm),(("L",0), ctermDL L),(("N",0), ctermDL mF)] sum_supp_collapse_vL)
    val s1 = Thm.implies_elim ssc hnodup
    val s2 = Thm.implies_elim s1 h1meta
    val s3 = Thm.implies_elim s2 h2meta   (* oeq (sumf (swt m) m)(lsumf (swt m)(dvl m)) *)
    (* sigma_def at m : sigma m = sumf (swt m) m *)
    val sdef = beta_norm (Drule.infer_instantiate ctxtDL [(("n",0), ctermDL mF)] sigma_def_vL)
    (* lsumf_cong (swt m -> idw) on members : object-Forall  !!d. lmem d (dvl m) ==> swt m d = idw d *)
    val perMemObj =
      let
        val dF = Free("d_cg", natT)
        val congPred = Term.lambda (Free("dd",natT))
                         (mkImp (lmem (Free("dd",natT)) L)(oeq (swtm $ (Free("dd",natT)))(idw $ (Free("dd",natT)))))
        fun perD dF =
          let
            val hmem = Thm.assume (ctermDL (jT (lmem dF L)))
            val fwd = conjunct1_L (mkImp (lmem dF L)(rhsP dF), mkImp (rhsP dF)(lmem dF L))
                        (allE_L (Term.lambda (Free("d",natT)) (iffP (Free("d",natT))), dF) compInst)
            val rhsThm = mp_L (lmem dF L, rhsP dF) fwd hmem
            val rest = conjunct2_L (lt ZeroC dF, mkConj (le dF mF)(dvd dF mF)) rhsThm
            val dvdd = conjunct2_L (le dF mF, dvd dF mF) rest
            val sw = swt_dvdL (dF, mF) dvdd
            val tgt = oeq (swtm $ dF) (idw $ dF)
          in impI_L (lmem dF L, tgt) sw end
      in allI_L congPred (Thm.forall_intr (ctermDL dF) (perD dF)) end
    val congEq = apply_lsumf_congL (swtm, idw, L) perMemObj   (* lsumf (swt m)(dvl m) = lsumf idw (dvl m) *)
    (* chain : sigma m = sumf (swt m) m = lsumf (swt m)(dvl m) = lsumf idw (dvl m) ; then sym to get lsumf idw (dvl m) = sigma m *)
    val sig_to_lsumf = trans2L (sdef, s3)        (* sigma m = lsumf (swt m)(dvl m) *)
    val sig_to_idw = trans2L (sig_to_lsumf, congEq)   (* sigma m = lsumf idw (dvl m) *)
    val r = symmL sig_to_idw                      (* lsumf idw (dvl m) = sigma m *)
  in varify r end;

val i_dvl_sigma = jT (oeq (lsumf idw (dvl mVc)) (sigma mVc));
val r_sigma = chkDL ("dvl_sigma", dvl_sigma, i_dvl_sigma);
val () = if r_sigma then out "DVL_SIGMA_OK\n" else out "DVL_SIGMA_FAIL\n";
val () = out "DIVLIST_M_ALL_DONE\n";

(* ===========================================================================
   SOUNDNESS PROBES.
   =========================================================================== *)
(* (iii) probe : dvl_sigma is NOT the trivial reflexive/degenerate form. *)
val s_sigma_nontrivial =
  not ((Thm.prop_of dvl_sigma) aconv (jT (oeq (lsumf idw (dvl mVc)) (lsumf idw (dvl mVc)))));
val () = if s_sigma_nontrivial then out "PROBE_OK dvl_sigma is sigma (not reflexive)\n"
         else out "PROBE_FAIL dvl_sigma collapsed to reflexive!\n";
(* and it is genuinely sigma, not e.g. = m. *)
val s_sigma_not_m =
  not ((Thm.prop_of dvl_sigma) aconv (jT (oeq (lsumf idw (dvl mVc)) mVc)));
val () = if s_sigma_not_m then out "PROBE_OK dvl_sigma RHS is sigma m, not m\n"
         else out "PROBE_FAIL dvl_sigma RHS is m!\n";

(* (ii) probe : dvl_nodup is genuinely lnodup, not the trivial lnodup lnil. *)
val s_nodup_genuine =
  not ((Thm.prop_of dvl_nodup) aconv (jT (lnodup lnilC)));
val () = if s_nodup_genuine then out "PROBE_OK dvl_nodup is lnodup (dvl m), not lnodup lnil\n"
         else out "PROBE_FAIL dvl_nodup degenerate!\n";

(* (i) probe : completeness genuinely carries dvd d m in the membership condition
   (a kernel rejection of the false "drop dvd" variant). *)
val s_complete_has_dvd =
  let
    val dV = Free("d", natT)
    fun rhsNoDvd dt = mkConj (lt ZeroC dt) (le dt mVc)   (* missing dvd *)
    val falseForm = jT (mkForall (Term.lambda dV
       (mkConj (mkImp (lmem dV (dvl mVc)) (rhsNoDvd dV))
               (mkImp (rhsNoDvd dV) (lmem dV (dvl mVc))))))
  in not ((Thm.prop_of dvl_complete) aconv falseForm) end;
val () = if s_complete_has_dvd then out "PROBE_OK dvl_complete keeps dvd d m in the membership condition\n"
         else out "PROBE_FAIL dvl_complete dropped dvd!\n";

(* hyps check (belt-and-suspenders : chkDL already enforces 0 hyps) *)
val () = out ("DVL_COMPLETE_HYPS = " ^ Int.toString (length (Thm.hyps_of dvl_complete)) ^ "\n");
val () = out ("DVL_NODUP_HYPS = " ^ Int.toString (length (Thm.hyps_of dvl_nodup)) ^ "\n");
val () = out ("DVL_SIGMA_HYPS = " ^ Int.toString (length (Thm.hyps_of dvl_sigma)) ^ "\n");

(* ===========================================================================
   AXIOM AUDIT : the 4 new dvl axioms must NOT mention sigma/perfect.
   =========================================================================== *)
val () =
  let
    val newAxL = [("dvla_0", Thm.prop_of dvla_0_ax),
                  ("dvla_dvd", Thm.prop_of dvla_dvd_ax),
                  ("dvla_ndvd", Thm.prop_of dvla_ndvd_ax),
                  ("dvl_def", Thm.prop_of dvl_def_ax)]
    fun mentions sub t =
      let val s = Syntax.string_of_term ctxtDL t
          val n = size sub
          fun look i = i + n <= size s andalso (String.substring (s, i, n) = sub orelse look (i+1))
      in look 0 end
    val bad = List.filter (fn (_,t) => mentions "sigma" t orelse mentions "perfect" t orelse mentions "swt" t) newAxL
  in if null bad then out "DVL_AXIOM_AUDIT_OK: no dvl axiom mentions sigma/perfect/swt\n"
     else out ("DVL_AXIOM_AUDIT_FAIL: " ^ String.concatWith "," (map #1 bad) ^ "\n")
  end;
val () = out ("DVL_NEW_AXIOM_COUNT = " ^ Int.toString 4 ^ "\n");
val () = out "DIVLIST_M_FENCE_DONE\n";

(* print the exact proved statements for the report *)
val () = out ("STMT_complete = " ^ Syntax.string_of_term ctxtDL (Thm.prop_of dvl_complete) ^ "\n");
val () = out ("STMT_nodup = " ^ Syntax.string_of_term ctxtDL (Thm.prop_of dvl_nodup) ^ "\n");
val () = out ("STMT_sigma = " ^ Syntax.string_of_term ctxtDL (Thm.prop_of dvl_sigma) ^ "\n");
(* ============================================================================
   SECTION B — assemble SCG on ctxtDL (which now carries BOTH dvl and dl2), then
   discharge euclid_euler_cond -> the unconditional euclid_euler.

   Runs AFTER : bases + ee_dl2_complete + bridge_prelude + sig2a_section
                + ee_divlist_m_onEC (dvl_complete/nodup/sigma on thyDL extending thyEC).

   On ctxtDL we already have (from ee_divlist_m_onEC) the full FOL+arith+natlist
   suite (impI_L, mp_L, allI_L, allE_L, disjI/disjE_L, conjI/conjunct_L, exMiddleL,
   oFalse_elimL, reflL, trans2L, symmL, mult/add cong, substPredL, exE_atL,
   lsumf*L, lmem*L, lnodup*L, swt_dvdL, swt_ndvdL, lmem_leqL, lnodup_leqL,
   leqL_symL, apply_lsumf_congL, sum_supp_collapse_vL, sigma_def_vL, dvd_le_vL).

   We ADD : a few dvd/mult/exI/exE combinators, port mkH1/mkH2/supportBridge to
   ctxtDL, transfer the dl2 lemmas + sigma_mult_reduction + sig2a + euclid_euler_cond,
   then build bridge_m / bridge_N at D = dvl m and close SCG, then discharge.
   ============================================================================ *)
val () = out "EE_SCG_BEGIN\n";

(* ---------------------------------------------------------------------------
   Transfer the dl2 lemmas (thyEC) + reduction + sig2a up to thyDL.
   --------------------------------------------------------------------------- *)
val dl2_complete_L     = Thm.transfer thyDL dl2_complete;
val dl2_lnodup_L       = Thm.transfer thyDL dl2_lnodup;
val dl2_members_dvd_L  = Thm.transfer thyDL dl2_members_dvd;
val sigma_mult_reduction_L = Thm.transfer thyDL sigma_mult_reduction;
val sig2a_L            = Thm.transfer thyDL sig2a;
val () = out ("transfer hyps : dl2c="^Int.toString(length(Thm.hyps_of dl2_complete_L))
              ^" dl2ln="^Int.toString(length(Thm.hyps_of dl2_lnodup_L))
              ^" dl2md="^Int.toString(length(Thm.hyps_of dl2_members_dvd_L))
              ^" smr="^Int.toString(length(Thm.hyps_of sigma_mult_reduction_L))
              ^" sig2a="^Int.toString(length(Thm.hyps_of sig2a_L))^"\n");

(* the dl2 / lmap2 / lappend constants live on thyEC < thyDL : reuse dl2/lmap2/lappend
   term builders from the partial (they are Const terms, theory-independent once
   declared in an ancestor). idw is theory-independent (Abs). *)

(* ---------------------------------------------------------------------------
   Extra combinators on ctxtDL.
   --------------------------------------------------------------------------- *)
val mult_comm_vL2  = upL mult_comm_vD;
val mult_assoc_vL2 = upL mult_assoc_vD;
val mult_1_right_vL2 = upL mult_1_right_vD;
val mult_0_right_vL2 = upL mult_0_right_vD2;
val exI_vL2 = upL exI_vD;
val exE_vL2 = upL exE_vD;
val pow_Suc_vL2 = upL pow_Suc_vD;
val geo_add_vL2 = upL geo_add_vD;

fun mult1rL t = beta_norm (Drule.infer_instantiate ctxtDL [(("n",0), ctermDL t)] mult_1_right_vL2);
fun mult0rL t = beta_norm (Drule.infer_instantiate ctxtDL [(("n",0), ctermDL t)] mult_0_right_vL2);
fun multcommL (m,n) = beta_norm (Drule.infer_instantiate ctxtDL
      [(("m",0), ctermDL m),(("n",0), ctermDL n)] mult_comm_vL2);
fun multassocL (m,n,k) = beta_norm (Drule.infer_instantiate ctxtDL
      [(("m",0), ctermDL m),(("n",0), ctermDL n),(("k",0), ctermDL k)] mult_assoc_vL2);
fun mult_cong_lL (p,q,k) hpq =
  let val Pabs = Abs("z", natT, oeq (mult p k) (mult (Bound 0) k))
      val inst = beta_norm (Drule.infer_instantiate ctxtDL
            [(("P",0), ctermDL Pabs),(("a",0), ctermDL p),(("b",0), ctermDL q)] oeq_subst_vL)
  in inst OF [hpq, reflL (mult p k)] end;
fun mult_cong_rL (h,p,q) hpq =
  let val Pabs = Abs("z", natT, oeq (mult h p) (mult h (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtDL
            [(("P",0), ctermDL Pabs),(("a",0), ctermDL p),(("b",0), ctermDL q)] oeq_subst_vL)
  in inst OF [hpq, reflL (mult h p)] end;
fun powSucL (aT,nT) = beta_norm (Drule.infer_instantiate ctxtDL
      [(("a",0), ctermDL aT),(("n",0), ctermDL nT)] pow_Suc_vL2);

(* FOL extras on ctxtDL : disjE_L/disjI_L/conjI_L already present. add exE_E-style
   on L via exE_atL (already present). *)

(* dvd combinators on ctxtDL : dvd a b == Ex(%k. b = a*k) *)
fun dvd_introL (aT, bT, w) hyp =
  let val Pabs = Abs("k", natT, oeq bT (mult aT (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtDL
            [(("P",0), ctermDL Pabs),(("a",0), ctermDL w)] exI_vL2)
  in Thm.implies_elim inst hyp end;
fun dvd_reflL t = dvd_introL (t, t, one) (symmL (mult1rL t));
(* dvd a x , oeq x y -> dvd a y *)
fun dvd_cong_targetL (aT, xT, yT) hxy hdvd =
  let val Pabs = Term.lambda (Free("zdt", natT)) (dvd aT (Free("zdt",natT)))
  in substPredL (Pabs, xT, yT) hxy hdvd end;
(* oeq a b -> dvd a x -> dvd b x *)
fun dvd_cong_divisorL (aT, bT, xT) hab hdvd =
  let val Pabs = Term.lambda (Free("zdd", natT)) (dvd (Free("zdd",natT)) xT)
  in substPredL (Pabs, aT, bT) hab hdvd end;
val mult_eq_zero_vL2 = upL mult_eq_zero_vD2;
fun mult_eq_zeroL (aT,bT) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtDL
    [(("a_mez",0), ctermDL aT),(("b_mez",0), ctermDL bT)] mult_eq_zero_vL2)) h;
val dvd_trans_vL2 = upL (varify (up dvd_trans));
fun dvd_transL (aT,bT,cT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("a",0), ctermDL aT),(("b",0), ctermDL bT),(("c",0), ctermDL cT)] dvd_trans_vL2)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
(* exE_E on ctxtDL with a global fresh-name counter (avoids nested-witness clash).
   exE_atL takes a CURRIED body (wF hyp); we accept a TUPLED body (wF, hyp). *)
val exDLctr = Unsynchronized.ref 0;
fun exE_E_L (Pabs, Qt) hEx body =
  let val n = !exDLctr val () = exDLctr := n+1
      val wnm = "w_exDL_" ^ Int.toString n
  in exE_atL (Pabs, Qt) hEx wnm (fn wF => fn hyp => body (wF, hyp)) end;
(* dvd a b -> body : Ex(%k. b = a*k) -> goal  (TUPLED body, like dvd_destE) *)
fun dvd_destL (aT, bT, goalT) hdvd body =
  let val Pabs = Abs("k", natT, oeq bT (mult aT (Bound 0)))
  in exE_E_L (Pabs, goalT) hdvd body end;
(* dvd_le : dvd d n ==> (oeq n 0 ==> oFalse) ==> le d n *)
fun dvdLeL (dT,nT) hdvd hnz =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("d",0), ctermDL dT),(("n",0), ctermDL nT)] dvd_le_vL)
  in Thm.implies_elim (Thm.implies_elim inst hdvd) hnz end;

val () = out "EE_SCG_INFRA_OK\n";

(* ---------------------------------------------------------------------------
   small nat helpers on ctxtDL needed for ltZeroSuc / N != 0.  (Defined BEFORE
   the bridge machinery, which uses ltZeroSucL.)
   --------------------------------------------------------------------------- *)
val Suc_neq_Zero_vL = upL Suc_neq_Zero_vD;
val add_Suc_vL2     = upL (varify (up add_Suc));
val pow2_pos_vL     = upL pow2_pos_vD;
fun SneqZL t = beta_norm (Drule.infer_instantiate ctxtDL [(("n",0), ctermDL t)] Suc_neq_Zero_vL);
fun add0L2 t = beta_norm (Drule.infer_instantiate ctxtDL [(("n",0), ctermDL t)] add_0_vL);
fun addSucL (mT,nT) = beta_norm (Drule.infer_instantiate ctxtDL
      [(("m",0), ctermDL mT),(("n",0), ctermDL nT)] add_Suc_vL2);
fun exI_L (Pabs, wT) hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtDL
        [(("P",0), ctermDL Pabs),(("a",0), ctermDL wT)] exI_vL2)
  in Thm.implies_elim inst hbody end;
fun ltZeroSucL (cT, mT) hcSm =   (* hcSm : oeq c (Suc m) -> lt 0 c *)
  let
    val a1m = addSucL (ZeroC, mT)
    val a0m = add0L2 mT
    val sucEq = Suc_congL (add ZeroC mT, mT) a0m
    val a1m_sm = trans2L (a1m, sucEq)
    val c_a1m = trans2L (hcSm, symmL a1m_sm)
    val wAbs = Abs("p", natT, oeq cT (add (suc ZeroC) (Bound 0)))
  in exI_L (wAbs, mT) c_a1m end;
val () = out "EE_SCG_NATHELP_OK\n";

(* ---------------------------------------------------------------------------
   swt / sigma_def / sum_supp_collapse on ctxtDL.
   --------------------------------------------------------------------------- *)
fun sigmaDefL nT = beta_norm (Drule.infer_instantiate ctxtDL [(("n",0), ctermDL nT)] sigma_def_vL);
val swtCL = swtC;            (* theory-independent const *)
fun swtFL nT = swtCL $ nT;

(* mkH1 / mkH2 / supportBridge on ctxtDL  (ports of the EC versions). *)
fun mkH1_L (KT, LT) hKnz memProve =
  let
    val dF = Free("d_h1L", natT)
    val concl = mkDisj (lmem dF LT)(oeq (swtFL KT $ dF) ZeroC)
    val hle = Thm.assume (ctermDL (jT (le dF KT)))
    val em = exMiddleL (dvd dF KT)
    val caseDvd =
      let
        val hdvd = Thm.assume (ctermDL (jT (dvd dF KT)))
        val emp = exMiddleL (lt ZeroC dF)
        val cPos =
          let val hpos = Thm.assume (ctermDL (jT (lt ZeroC dF)))
              val mem = memProve (dF, hpos, hle, hdvd)   (* lmem d L *)
          in Thm.implies_intr (ctermDL (jT (lt ZeroC dF))) (disjI1_L (lmem dF LT, oeq (swtFL KT $ dF) ZeroC) mem) end
        val cZero =
          let val hnp = Thm.assume (ctermDL (jT (neg (lt ZeroC dF))))
              val dz = dzosL dF
              val d0 = let val cZ = let val h0 = Thm.assume (ctermDL (jT (oeq dF ZeroC))) in Thm.implies_intr (ctermDL (jT (oeq dF ZeroC))) h0 end
                           val cS = let val Pq = Abs("q",natT, oeq dF (suc (Bound 0)))
                                        val hx = Thm.assume (ctermDL (jT (mkEx Pq)))
                                    in Thm.implies_intr (ctermDL (jT (mkEx Pq)))
                                         (exE_E_L (Pq, oeq dF ZeroC) hx (fn (qF,hq) =>
                                            let val ltp = ltZeroSucL (dF, qF) hq
                                                val ff = mp_L (lt ZeroC dF, oFalseC) hnp ltp
                                            in Thm.implies_elim (oFalse_elimL (oeq dF ZeroC)) ff end)) end
                       in disjE_L (oeq dF ZeroC, mkEx (Abs("q",natT, oeq dF (suc (Bound 0)))), oeq dF ZeroC) dz cZ cS end
              (* neg(dvd 0 K) : dvd 0 K -> K = 0*k = 0 -> contra hKnz. *)
              val ndvd0 = let val hdK = Thm.assume (ctermDL (jT (dvd ZeroC KT)))
                              val kK0 = dvd_destL (ZeroC, KT, oFalseC) hdK (fn (kF,hk) =>
                                          let val z = trans2L (hk, trans2L (multcommL (ZeroC,kF), mult0rL kF))  (* K = 0 *)
                                          in Thm.implies_elim hKnz z end)
                          in impI_L (dvd ZeroC KT, oFalseC) kK0 end
              val swt0at0 = swt_ndvdL (ZeroC, KT) ndvd0   (* oeq (swt K 0) 0 *)
              val Ps = Term.lambda (Free("zs",natT)) (oeq (swtFL KT $ (Free("zs",natT))) ZeroC)
              val swt0atd = substPredL (Ps, ZeroC, dF) (symmL d0) swt0at0   (* oeq (swt K d) 0 *)
          in Thm.implies_intr (ctermDL (jT (neg (lt ZeroC dF)))) (disjI2_L (lmem dF LT, oeq (swtFL KT $ dF) ZeroC) swt0atd) end
      in Thm.implies_intr (ctermDL (jT (dvd dF KT))) (disjE_L (lt ZeroC dF, neg (lt ZeroC dF), concl) emp cPos cZero) end
    val caseNdvd =
      let val hnd = Thm.assume (ctermDL (jT (neg (dvd dF KT))))
          val swt0 = swt_ndvdL (dF, KT) hnd
      in Thm.implies_intr (ctermDL (jT (neg (dvd dF KT)))) (disjI2_L (lmem dF LT, oeq (swtFL KT $ dF) ZeroC) swt0) end
    val body = disjE_L (dvd dF KT, neg (dvd dF KT), concl) em caseDvd caseNdvd
  in Thm.forall_intr (ctermDL dF) (Thm.implies_intr (ctermDL (jT (le dF KT))) body) end;

fun mkH2_L (KT, LT) hKnz hMembersDvd =
  let
    val dF = Free("d_h2L", natT)
    val hmem = Thm.assume (ctermDL (jT (lmem dF LT)))
    val hdvd = Thm.implies_elim (Thm.forall_elim (ctermDL dF) hMembersDvd) hmem   (* dvd d K *)
    val hle = dvdLeL (dF, KT) hdvd hKnz   (* le d K *)
  in Thm.forall_intr (ctermDL dF) (Thm.implies_intr (ctermDL (jT (lmem dF LT))) hle) end;

fun supportBridge_L (KT, LT) hLnodup hH1meta hH2meta hMembersDvd =
  let
    val ssc = beta_norm (Drule.infer_instantiate ctxtDL
                [(("f",0), ctermDL (swtFL KT)),(("L",0), ctermDL LT),(("N",0), ctermDL KT)] sum_supp_collapse_vL)
    val s1 = Thm.implies_elim ssc hLnodup
    val s2 = Thm.implies_elim s1 hH1meta
    val s3 = Thm.implies_elim s2 hH2meta   (* oeq (sumf (swt K) K)(lsumf (swt K) L) *)
    val sdef = sigmaDefL KT
    val sig_lsumf = trans2L (sdef, s3)   (* oeq (sigma K)(lsumf (swt K) L) *)
    val congMinor =
      let
        val dF = Free("d_sbL", natT)
        val hmem = Thm.assume (ctermDL (jT (lmem dF LT)))
        val hdvd = Thm.implies_elim (Thm.forall_elim (ctermDL dF) hMembersDvd) hmem
        val swtd = swt_dvdL (dF, KT) hdvd   (* oeq (swt K d) d *)
        val impd = impI_L (lmem dF LT, oeq (swtFL KT $ dF) dF) swtd
      in allI_L (Term.lambda (Free("d",natT))
                   (mkImp (lmem (Free("d",natT)) LT)(oeq (swtFL KT $ (Free("d",natT))) (Free("d",natT)))))
                (Thm.forall_intr (ctermDL dF) impd) end
    val congInst = beta_norm (Drule.infer_instantiate ctxtDL
                     [(("f",0), ctermDL (swtFL KT)),(("g",0), ctermDL idw),(("L",0), ctermDL LT)] lsumf_cong_vL)
    val forallT = mkForall (Term.lambda (Free("d",natT))
                    (mkImp (lmem (Free("d",natT)) LT)(oeq (swtFL KT $ (Free("d",natT))) (Free("d",natT)))))
    val congEq = mp_L (forallT, oeq (lsumf (swtFL KT) LT)(lsumf idw LT)) congInst congMinor
    val res = trans2L (sig_lsumf, congEq)   (* oeq (sigma K)(lsumf idw L) *)
  in res end;

val () = out "EE_SCG_BRIDGE_L_OK\n";

(* ===========================================================================
   THE GENERAL SCG, on ctxtDL.  For Frees a, m :
     under hOdd : neg(dvd 2 m),  D = dvl m,
       bridge_m : oeq (sigma m)(lsumf idw (dvl m))     [symm dvl_sigma]
       bridge_N : oeq (sigma (2^a*m))(lsumf idw (dl2 a (dvl m)))  [supportBridge_L]
       sig2a    : oeq (sigma (2^a))(sumf (pow 2) a)     [transferred]
     feed sigma_mult_reduction -> oeq (sigma N)(mult (sigma 2^a)(sigma m))
     factor-bridge (sig2a) : -> oeq (sigma N)(mult (sumf(pow 2) a)(sigma m))
   =========================================================================== *)
val scgInner =
  let
    val aF = Free("a", natT)
    val mF = Free("m", natT)
    val D  = dvl mF
    val N  = mult (p2 aF) mF
    val hOdd = Thm.assume (ctermDL (jT (neg (dvd two mF))))   (* neg(dvd 2 m) *)

    (* dvl_complete at m : object Forall(%d. (lmem d D -> rhs d) AND (rhs d -> lmem d D))
       where rhs d = 0<d AND le d m AND dvd d m. *)
    val compInst = beta_norm (Drule.infer_instantiate ctxtDL [(("m",0), ctermDL mF)] dvl_complete)
    fun rhsT dt = mkConj (lt ZeroC dt) (mkConj (le dt mF) (dvd dt mF))
    fun iffBodyT dt = mkConj (mkImp (lmem dt D)(rhsT dt)) (mkImp (rhsT dt)(lmem dt D))
    (* DHsnd_meta : !!d. lmem d D ==> dvd d m  (forward of dvl_complete) *)
    val DHsnd_meta =
      let val dF = Free("d_snd", natT)
          val atd = allE_L (Term.lambda (Free("d",natT)) (iffBodyT (Free("d",natT))), dF) compInst  (* iffBody d *)
          val fwd = conjunct1_L (mkImp (lmem dF D)(rhsT dF), mkImp (rhsT dF)(lmem dF D)) atd  (* lmem d D -> rhs d *)
          val hmem = Thm.assume (ctermDL (jT (lmem dF D)))
          val rh = mp_L (lmem dF D, rhsT dF) fwd hmem
          val dvdd = conjunct2_L (le dF mF, dvd dF mF)
                       (conjunct2_L (lt ZeroC dF, mkConj (le dF mF)(dvd dF mF)) rh)
      in Thm.forall_intr (ctermDL dF) (Thm.implies_intr (ctermDL (jT (lmem dF D))) dvdd) end
    (* DHsnd_obj : Forall(%d. Imp(lmem d D)(dvd d m))  (object form, for dl2_members_dvd) *)
    val DHsnd_obj =
      let val dF = Free("d_sndo", natT)
          val perd = Thm.implies_elim (Thm.forall_elim (ctermDL dF) DHsnd_meta) (Thm.assume (ctermDL (jT (lmem dF D))))
          val impd = impI_L (lmem dF D, dvd dF mF) perd
      in allI_L (Term.lambda (Free("d",natT)) (mkImp (lmem (Free("d",natT)) D)(dvd (Free("d",natT)) mF)))
                (Thm.forall_intr (ctermDL dF) impd) end
    (* DHcmp_meta : !!d. 0<d ==> le d m ==> dvd d m ==> lmem d D  (backward of dvl_complete) *)
    val DHcmp_meta =
      let val dF = Free("d_cmp", natT)
          val atd = allE_L (Term.lambda (Free("d",natT)) (iffBodyT (Free("d",natT))), dF) compInst
          val bwd = conjunct2_L (mkImp (lmem dF D)(rhsT dF), mkImp (rhsT dF)(lmem dF D)) atd  (* rhs d -> lmem d D *)
          val hpos = Thm.assume (ctermDL (jT (lt ZeroC dF)))
          val hle  = Thm.assume (ctermDL (jT (le dF mF)))
          val hdvd = Thm.assume (ctermDL (jT (dvd dF mF)))
          val rh = conjI_L (lt ZeroC dF, mkConj (le dF mF)(dvd dF mF)) hpos
                     (conjI_L (le dF mF, dvd dF mF) hle hdvd)
          val mem = mp_L (rhsT dF, lmem dF D) bwd rh
      in Thm.forall_intr (ctermDL dF)
           (Thm.implies_intr (ctermDL (jT (lt ZeroC dF)))
             (Thm.implies_intr (ctermDL (jT (le dF mF)))
               (Thm.implies_intr (ctermDL (jT (dvd dF mF))) mem))) end

    (* lnodup (dvl m) *)
    val hNodupD = beta_norm (Drule.infer_instantiate ctxtDL [(("m",0), ctermDL mF)] dvl_nodup)

    (* N != 0 : 2^a*m ; m != 0 from hOdd (else dvd 2 0). hKnz : oeq N 0 ==> oFalse. *)
    val hKnz =
      let val h0 = Thm.assume (ctermDL (jT (oeq N ZeroC)))   (* 2^a*m = 0 *)
          (* 2^a != 0 : pow2_pos.  m != 0 : from hOdd. mult x y = 0 -> x=0 or y=0. *)
          (* simpler : show m = 0 leads to contra via hOdd, but we have N=0 not m=0.
             use : 2^a*m = 0 and 2^a = Suc p (pow2_pos) -> Suc p * m = 0.
             (Suc p)*m = m + p*m  [mult_Suc_left? ]  ... instead: prove m != 0 from hOdd, and 2^a != 0,
             then mult of two nonzeros != 0.  Cleaner: derive oFalse from N=0 by showing m | N and 2^a | N
             ... Actually use mult_eq_zero : oeq (mult a b) 0 ==> Disj(oeq a 0)(oeq b 0). *)
          val meq0_disj = mult_eq_zeroL (p2 aF, mF) h0   (* Disj(oeq (2^a) 0)(oeq m 0) *)
          val ca = let val h2a0 = Thm.assume (ctermDL (jT (oeq (p2 aF) ZeroC)))
                       (* 2^a = Suc p -> Suc p = 0 -> SneqZ *)
                       val pp2 = beta_norm (Drule.infer_instantiate ctxtDL [(("k",0), ctermDL aF)] pow2_pos_vL)
                       val ff = exE_E_L (Abs("p",natT, oeq (p2 aF)(suc (Bound 0))), oFalseC) pp2
                                  (fn (pF, hp) => Thm.implies_elim (SneqZL pF) (trans2L (symmL hp, h2a0)))
                   in Thm.implies_intr (ctermDL (jT (oeq (p2 aF) ZeroC))) ff end
          val cm = let val hm0 = Thm.assume (ctermDL (jT (oeq mF ZeroC)))   (* m = 0 *)
                       (* dvd 2 0 : 0 = 2*0 ; so dvd 2 m via cong (m=0) -> contra hOdd. *)
                       val dvd20 = dvd_introL (two, ZeroC, ZeroC) (symmL (mult0rL two))  (* dvd 2 0 *)
                       val dvd2m = dvd_cong_targetL (two, ZeroC, mF) (symmL hm0) dvd20   (* dvd 2 m *)
                       val ff = mp_L (dvd two mF, oFalseC) hOdd dvd2m
                   in Thm.implies_intr (ctermDL (jT (oeq mF ZeroC))) ff end
          val ff = disjE_L (oeq (p2 aF) ZeroC, oeq mF ZeroC, oFalseC) meq0_disj ca cm
      in Thm.implies_intr (ctermDL (jT (oeq N ZeroC))) ff end

    (* ---- bridge_N ingredients ---- *)
    (* dl2_members_dvd at (a,m,D) : (Forall d. lmem d D -> dvd d m) ==> (Forall e. lmem e (dl2 a D) -> dvd e N) *)
    val mdInst = beta_norm (Drule.infer_instantiate ctxtDL
                   [(("a",0), ctermDL aF),(("m",0), ctermDL mF),(("D",0), ctermDL D)] dl2_members_dvd_L)
    val membersDvd_dl2 = Thm.implies_elim mdInst DHsnd_obj   (* Forall e. lmem e (dl2 a D) -> dvd e N *)
    val hMembersDvd =   (* META : !!e. lmem e (dl2 a D) ==> dvd e N *)
      let val eF = Free("e_md", natT)
          val pred = Term.lambda (Free("e",natT)) (mkImp (lmem (Free("e",natT)) (dl2 aF D))(dvd (Free("e",natT)) N))
          val at = allE_L (pred, eF) membersDvd_dl2
          val concl = mp_L (lmem eF (dl2 aF D), dvd eF N) at (Thm.assume (ctermDL (jT (lmem eF (dl2 aF D)))))
      in Thm.forall_intr (ctermDL eF) (Thm.implies_intr (ctermDL (jT (lmem eF (dl2 aF D)))) concl) end

    (* dl2_lnodup at (a,m,D) : neg(dvd 2 m) ==> (!!d. lmem d D ==> dvd d m) ==> lnodup D ==> lnodup (dl2 a D) *)
    val lnodupInst = beta_norm (Drule.infer_instantiate ctxtDL
                       [(("a_ld",0), ctermDL aF),(("m",0), ctermDL mF),(("D",0), ctermDL D)] dl2_lnodup_L)
    val hLnodup = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim lnodupInst hOdd) DHsnd_meta) hNodupD
                  (* lnodup (dl2 a D) *)

    (* dl2_complete at (a,m,D) : neg(dvd 2 m) ==> DHcmp ==> !!e. dvd e N ==> 0<e ==> le e N ==> lmem e (dl2 a D) *)
    val completeInst = beta_norm (Drule.infer_instantiate ctxtDL
                         [(("a",0), ctermDL aF),(("m",0), ctermDL mF),(("D",0), ctermDL D)] dl2_complete_L)
    val complete_e = Thm.implies_elim (Thm.implies_elim completeInst hOdd) DHcmp_meta
    fun memProve (eF, hpos, hle, hdvd) =   (* mkH1's memProve : (eF, 0<e, le e N, dvd e N) -> lmem e (dl2 a D) *)
      let val s0 = Thm.forall_elim (ctermDL eF) complete_e
          val s1 = Thm.implies_elim s0 hdvd
          val s2 = Thm.implies_elim s1 hpos
          val s3 = Thm.implies_elim s2 hle
      in s3 end

    val hH1 = mkH1_L (N, dl2 aF D) hKnz memProve
    val hH2 = mkH2_L (N, dl2 aF D) hKnz hMembersDvd
    val bridge_N = supportBridge_L (N, dl2 aF D) hLnodup hH1 hH2 hMembersDvd
                   (* oeq (sigma N)(lsumf idw (dl2 a D)) *)

    (* bridge_m : oeq (sigma m)(lsumf idw (dvl m))  = symm dvl_sigma *)
    val dvlSigInst = beta_norm (Drule.infer_instantiate ctxtDL [(("m",0), ctermDL mF)] dvl_sigma)
                     (* oeq (lsumf idw (dvl m)) (sigma m) *)
    val bridge_m = symmL dvlSigInst   (* oeq (sigma m)(lsumf idw (dvl m)) *)

    (* sig2a at a : oeq (sigma (2^a))(sumf (pow 2) a) *)
    val sig2a_at = beta_norm (Drule.infer_instantiate ctxtDL [(("a",0), ctermDL aF)] sig2a_L)

    (* feed sigma_mult_reduction at (a,m,D=dvl m) :
         bridge_m ==> bridge_N ==> sig2a ==> oeq (sigma N)(mult (sigma 2^a)(sigma m)) *)
    val smrInst = beta_norm (Drule.infer_instantiate ctxtDL
                    [(("a",0), ctermDL aF),(("m",0), ctermDL mF),(("D",0), ctermDL D)] sigma_mult_reduction_L)
    val red1 = Thm.implies_elim smrInst bridge_m
    val red2 = Thm.implies_elim red1 bridge_N
    val red3 = Thm.implies_elim red2 sig2a_at   (* oeq (sigma N)(mult (sigma 2^a)(sigma m)) *)

    (* factor-bridge : rewrite (sigma 2^a) -> (sumf(pow 2) a) via sig2a, in mult _ (sigma m). *)
    val scgConcl = mult_cong_lL (sigma (p2 aF), sumf pwAbs2 aF, sigma mF) sig2a_at
                   (* oeq (mult (sigma 2^a)(sigma m))(mult (sumf(pow 2) a)(sigma m)) *)
    val scgam = trans2L (red3, scgConcl)   (* oeq (sigma N)(mult (sumf(pow 2) a)(sigma m)) *)
    (* discharge hOdd as object meta : the scgImpl wants  neg(dvd 2 m) ==> <conclusion> as META impl *)
    val scgImplThm = Thm.implies_intr (ctermDL (jT (neg (dvd two mF)))) scgam
  in (aF, mF, scgImplThm) end;

val () = out "EE_SCG_INNER_OK\n";

(* ===========================================================================
   SCG as the meta theorem scgProp = !!a m. neg(dvd 2 m) ==> sigma(2^a*m)=(sumf(pow2)a)*sigma m.
   forall_intr m then a (matching scgProp's binder order : Logic.all scg_aF (Logic.all scg_mF ...)).
   =========================================================================== *)
val (scg_aF, scg_mF, scgImplThm) = scgInner;
val scg_thm = Thm.forall_intr (ctermDL scg_aF) (Thm.forall_intr (ctermDL scg_mF) scgImplThm);
val () = out ("SCG hyps = " ^ Int.toString (length (Thm.hyps_of scg_thm)) ^ "\n");
val () = out ("SCG shyps = " ^ Int.toString (length (Thm.extra_shyps scg_thm)) ^ "\n");

(* intended scgProp (matching euler_converse.sml:1691-1694), with Frees a_scg, m_scg *)
val scg_aFi = Free("a_scg", natT); val scg_mFi = Free("m_scg", natT);
fun scgImplI aF mF = Logic.mk_implies (jT (neg (dvd two mF)),
                      jT (oeq (sigma (mult (p2 aF) mF)) (mult (sumf pwAbs2 aF) (sigma mF))));
val scgPropI = Logic.all scg_aFi (Logic.all scg_mFi (scgImplI scg_aFi scg_mFi));
val r_scg_aconv = (Thm.prop_of scg_thm) aconv scgPropI;
val () = out ("SCG_ACONV = " ^ Bool.toString r_scg_aconv ^ "\n");
val () = if r_scg_aconv then out "SCG_ACONV_OK\n"
         else (out ("  got      = " ^ Syntax.string_of_term ctxtDL (Thm.prop_of scg_thm) ^ "\n");
               out ("  intended = " ^ Syntax.string_of_term ctxtDL scgPropI ^ "\n"));
val () = if r_scg_aconv andalso length (Thm.hyps_of scg_thm) = 0 then out "SCG_PROVED_0HYP_OK\n"
         else out "SCG_NOT_CLEAN\n";

(* SCG soundness probe : genuinely needs the odd hyp (NOT the unconditional sigma-mult). *)
val s_scg_cond =
  not ((Thm.prop_of scgImplThm) aconv
       (jT (oeq (sigma (mult (p2 scg_aF) scg_mF)) (mult (sumf pwAbs2 scg_aF) (sigma scg_mF)))));
val () = if s_scg_cond then out "PROBE_OK scg needs the odd(m) hypothesis\n"
         else out "PROBE_FAIL scg dropped the odd hypothesis!\n";

val () = out "EE_SCG_PROVED\n";

(* ===========================================================================
   DISCHARGE : apply the BANKED euclid_euler_cond to scg_thm -> the unconditional
   euclid_euler : lt 0 n ==> even n ==> (perfect n <-> euclidForm n).
   euclid_euler_cond lives on thySigD < thyDL ; transfer it up, then implies_elim.
   =========================================================================== *)
val euclid_euler_cond_L = Thm.transfer thyDL euclid_euler_cond;
val () = out ("eec_L hyps = " ^ Int.toString (length (Thm.hyps_of euclid_euler_cond_L)) ^ "\n");
(* euclid_euler_cond_L : scgProp ==> lt 0 n ==> even n ==> (perfect n <-> euclidForm n)  [schematic n]
   first premise is scgProp (Var-free, with bound a_scg/m_scg).  implies_elim with scg_thm. *)
val euclid_euler = Thm.implies_elim euclid_euler_cond_L scg_thm;
val () = out ("EUCLID_EULER hyps = " ^ Int.toString (length (Thm.hyps_of euclid_euler)) ^ "\n");
val () = out ("EUCLID_EULER shyps = " ^ Int.toString (length (Thm.extra_shyps euclid_euler)) ^ "\n");

(* aconv-intended : lt 0 n ==> even n ==> (perfect n <-> euclidForm n)  [schematic n].
   Build the intended term using the converse block's builders, with schematic n. *)
val nVee = Var(("n",0), natT);
fun evenV n  = mkEx (Term.lambda (Free("k", natT)) (oeq n (mult two (Free("k",natT)))));
fun perfectV n = oeq (sigma n) (mult two n);
fun euclidFormV n =
  mkEx (Term.lambda (Free("p", natT))
    (mkConj (prime2 (sub (pow two (Free("p",natT))) one))
            (oeq n (mult (pow two (sub (Free("p",natT)) one)) (sub (pow two (Free("p",natT))) one)))));
val i_euclid_euler =
  Logic.mk_implies (jT (lt ZeroC nVee),
    Logic.mk_implies (jT (evenV nVee),
      jT (mkConj (mkImp (perfectV nVee)(euclidFormV nVee))
                 (mkImp (euclidFormV nVee)(perfectV nVee)))));
val r_ee = (Thm.prop_of euclid_euler) aconv i_euclid_euler;
val () = out ("EUCLID_EULER_ACONV = " ^ Bool.toString r_ee ^ "\n");
val () = if r_ee then out "EUCLID_EULER_ACONV_OK\n"
         else (out ("  got      = " ^ Syntax.string_of_term ctxtDL (Thm.prop_of euclid_euler) ^ "\n");
               out ("  intended = " ^ Syntax.string_of_term ctxtDL i_euclid_euler ^ "\n"));

(* soundness probes on the unconditional euclid_euler *)
val eeProp = Thm.prop_of euclid_euler;
val ee_noeven =
  Logic.mk_implies (jT (lt ZeroC nVee),
    jT (mkConj (mkImp (perfectV nVee)(euclidFormV nVee)) (mkImp (euclidFormV nVee)(perfectV nVee))));
val () = if not (eeProp aconv ee_noeven) then out "PROBE_OK euclid_euler needs even n\n"
         else out "PROBE_FAIL euclid_euler even dropped\n";
val ee_collapsed =
  Logic.mk_implies (jT (lt ZeroC nVee),
    Logic.mk_implies (jT (evenV nVee),
      jT (mkConj (mkImp (perfectV nVee) nVee) (mkImp nVee (perfectV nVee)))));
val () = if not (eeProp aconv ee_collapsed) then out "PROBE_OK euclidForm is the Euclid shape (not n)\n"
         else out "PROBE_FAIL euclidForm collapsed\n";

val () =
  if r_ee andalso length (Thm.hyps_of euclid_euler) = 0
     andalso length (Thm.extra_shyps euclid_euler) = 0
     andalso r_scg_aconv andalso length (Thm.hyps_of scg_thm) = 0
  then out "EUCLID_EULER_UNCONDITIONAL_OK\n"
  else out "EUCLID_EULER_INCOMPLETE\n";

(* AXIOM AUDIT : the whole assembly adds NO new axiom over the 10 conservative
   list/divisor recursion axioms already in thyDL. *)
val () = out "EE_FINAL_AXIOM_AUDIT_BEGIN\n";
val baseAxN2 = map #1 (Theory.all_axioms_of thySigD);
val finAxN2  = map #1 (Theory.all_axioms_of (Thm.theory_of_thm euclid_euler));
val newAx2 = List.filter (fn nm => not (List.exists (fn b => b=nm) baseAxN2)) finAxN2;
val () = out ("EE_FINAL_NEW_AXIOM_COUNT = " ^ Int.toString (length newAx2) ^ "\n");
val () = List.app (fn nm => out ("  EE_FINALAX " ^ nm ^ "\n")) newAx2;
fun mentions2 sub t =
  let val s = Syntax.string_of_term ctxtDL t
      val n = size sub
      fun look i = i + n <= size s andalso (String.substring (s, i, n) = sub orelse look (i+1))
  in look 0 end;
val finAxTerms = List.filter (fn (nm,_) => List.exists (fn b => b = nm) newAx2) (Theory.all_axioms_of (Thm.theory_of_thm euclid_euler));
val anyBad2 = List.exists (fn (_, t) => mentions2 "sigma" t orelse mentions2 "perfect" t) finAxTerms;
val () = if anyBad2 then out "EE_FINAL_AXIOM_AUDIT_FAIL: a new axiom mentions sigma/perfect!\n"
         else out "EE_FINAL_AXIOM_AUDIT_OK: no new axiom mentions sigma/perfect\n";
val () = out "EE_FINAL_AXIOM_AUDIT_END\n";

val () = out "EE_SCG_ASSEMBLY_DONE\n";

(* ---- print the exact final statements for the record ---- *)
val () = out ("SCG_STATEMENT = " ^ Syntax.string_of_term ctxtDL (Thm.prop_of scg_thm) ^ "\n");
val () = out ("EUCLID_EULER_STATEMENT = " ^ Syntax.string_of_term ctxtDL (Thm.prop_of euclid_euler) ^ "\n");
val () = out ("FINAL euclid_euler hyps_of = [" ^ Int.toString (length (Thm.hyps_of euclid_euler)) ^ "]\n");
val () = out "EE_PRINT_DONE\n";
