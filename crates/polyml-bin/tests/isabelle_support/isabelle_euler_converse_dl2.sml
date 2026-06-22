(* ============================================================================
   ee_dl2_complete.sml  —  THE PRODUCT-LIST  dl2  bridges  (the SCG crux).

   Appended after  isabelle_euclid_perfect.sml + isabelle_euler_converse.sml
   + isabelle_euler_converse_sigma_mult.sml  (the SCG partial), so it runs on
   the FINAL context  ctxtEC / thyEC  with the full *_E combinator suite,
   lmap2 / lappend / dl2, mem_map2 / mem_append, dl2_members_dvd, etc.

   For  m ODD,  N = 2^a * m,  D a deduplicated list of exactly the divisors of
   m (carried as object hypotheses), and
        dl2 a D  =  { 2^i * d : 0<=i<=a , d in D },
   we prove the TWO bridge ingredients sum_supp_collapse needs:

     (a) dl2_lnodup     :  lnodup (dl2 a D)
     (b) dl2_complete   :  dvd e N /\ lt 0 e /\ le e N  ==>  lmem e (dl2 a D)

   (a) cross-level 2^i*d distinctness (the 2-adic valuation pins the level i,
       the odd cofactor pins d in D);
   (b) the 2-ADIC SPLIT  e = 2^i * d  (i<=a by pow2_dvd_char on the 2-part;
       d|m the odd cofactor peeled by euclid_lemma at prime 2; then d in D by
       the D-completeness hypothesis).

   D-hypotheses (matching sigma_mult_reduction's generic divisor list D for m):
     (DHN)  neg (dvd 2 m)                                    [m odd]
     (DH1)  lnodup D
     (DHsnd) !!d. lmem d D ==> dvd d m                       [members divide m]
     (DHcmp) !!d. lt 0 d ==> le d m ==> dvd d m ==> lmem d D [completeness of D]
   ============================================================================ *)

val () = out "EE_DL2_BEGIN\n";

(* ---------------------------------------------------------------------------
   STEP 0 : transfer the remaining base lemmas onto thyEC and build the
   instantiators we need (pow2_dvd_char, euclid_lemma, prime2_two,
   mult_left_cancel, pow_add/Suc/Zero, le_refl/trans/suc_mono/add, mult_le_mono,
   ex_middle, dvd_le).
   --------------------------------------------------------------------------- *)
val pow2_dvd_char_vE = upE pow2_dvd_char_vD;     (* dvd d (p2 k) ==> Ex i. le i k /\ d = p2 i *)
val euclid_lemma_vE  = upE (varify euclid_lemma);(* prime2 p ==> dvd p (a*b) ==> Disj(dvd p a)(dvd p b) *)
val prime2_two_vE    = upE prime2_two;           (* prime2 2 *)
val mult_left_cancel_vE = upE mult_left_cancel_vD;
val pow_add_vE       = upE (varify pow_add);     (* pow a (m+n) = pow a m * pow a n *)
val pow_Suc_vE       = upE pow_Suc_vD;           (* pow a (Suc n) = a * pow a n *)
val ex_middle_vE     = upE ex_middle_vD;
val dvd_le_vE        = upE dvd_le_vD;            (* dvd d n ==> (n=0 ==> False) ==> le d n *)
val le_refl_vE       = upE (varify le_refl);
val le_trans_vE      = upE (varify le_trans);
val le_suc_mono_vE   = upE (varify le_suc_mono);
val le_add_vE        = upE (varify le_add);      (* le m (add m p) *)
val lmem_cons_fwd_vE = upE lmem_cons_fwd_vD;
val lmem_nil_elim_vE = upE lmem_nil_elim_vD;

(* ---- instantiators ---- *)
fun pow2DvdCharE (dT, kT) hdvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("d",0), ctermEC dT),(("k",0), ctermEC kT)] pow2_dvd_char_vE)
  in Thm.implies_elim inst hdvd end;
fun euclidLemmaE (pT, aT, bT) hPrime hDvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("p",0), ctermEC pT),(("a",0), ctermEC aT),(("b",0), ctermEC bT)] euclid_lemma_vE)
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hDvd end;
fun multLeftCancelE (cT,aT,bT) hPos hEq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("c",0), ctermEC cT),(("a",0), ctermEC aT),(("b",0), ctermEC bT)] mult_left_cancel_vE)
  in Thm.implies_elim (Thm.implies_elim inst hPos) hEq end;
fun powAddE (aT,mT,nT) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("a",0), ctermEC aT),(("m",0), ctermEC mT),(("n",0), ctermEC nT)] pow_add_vE);
fun powSucE (aT,nT) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("a",0), ctermEC aT),(("n",0), ctermEC nT)] pow_Suc_vE);
fun powZeroE aT = beta_norm (Drule.infer_instantiate ctxtEC [(("a",0), ctermEC aT)] (upE pow_Zero_vD));
fun exMiddleE At = beta_norm (Drule.infer_instantiate ctxtEC [(("A",0), ctermEC At)] ex_middle_vE);
fun dvdLeE (dT,nT) hdvd hnz =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("d",0), ctermEC dT),(("n",0), ctermEC nT)] dvd_le_vE)
  in Thm.implies_elim (Thm.implies_elim inst hdvd) hnz end;
fun leReflE t = beta_norm (Drule.infer_instantiate ctxtEC [(("n",0), ctermEC t)] le_refl_vE);
fun leTransE (mT,nT,kT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("m",0), ctermEC mT),(("n",0), ctermEC nT),(("k",0), ctermEC kT)] le_trans_vE)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun leSucMonoE (mT,nT) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("m",0), ctermEC mT),(("n",0), ctermEC nT)] le_suc_mono_vE)
  in Thm.implies_elim inst h end;
fun leAddE (mT,pT) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("m",0), ctermEC mT),(("p",0), ctermEC pT)] le_add_vE);
fun lmemConsFwdE2 (x,y,t) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("x",0), ctermEC x),(("y",0), ctermEC y),(("t",0), ctermEC t)] lmem_cons_fwd_vE);
fun lmemNilElimE2 x = beta_norm (Drule.infer_instantiate ctxtEC [(("x",0), ctermEC x)] lmem_nil_elim_vE);

(* nat induction at a predicate / value already wired : nat_induct_atE *)
(* exE wrapper : from Ex P and (!!w. P w ==> Q) get Q.  Uses a GLOBAL counter to
   generate a FRESH witness Free per call so nested exE_E do not clash (the
   forall_intr otherwise fails with "variable free in assumptions"). *)
val exE_ctr = Unsynchronized.ref 0;
fun exE_E (Pabs, Qt) hEx body =
  let val n = !exE_ctr
      val () = exE_ctr := n + 1
      val wnm = "w_exE_" ^ Int.toString n
      val exE_inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("P",0), ctermEC Pabs),(("Q",0), ctermEC Qt)] exE_vE)
      val partial = Thm.implies_elim exE_inst hEx
      val wF = Free(wnm, natT)
      val hbody = Thm.assume (ctermEC (jT (Term.betapply (Pabs, wF))))
      val rbody = body (wF, hbody)
      val minor = Thm.forall_intr (ctermEC wF) (Thm.implies_intr (ctermEC (jT (Term.betapply (Pabs, wF)))) rbody)
  in Thm.implies_elim partial minor end;
(* exI wrapper *)
fun exI_E (Pabs, wT) hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("P",0), ctermEC Pabs),(("a",0), ctermEC wT)] exI_vE)
  in Thm.implies_elim inst hbody end;

(* two as a term : already `two` (= suc(suc Zero)) and p2 / pow available from base. *)
(* lt 0 (p2 a) on ctxtEC, from pow2_pos (Ex m. p2 a = Suc m). *)
val pow2_pos_vE = upE pow2_pos_vD;   (* Ex m. p2 k = Suc m  (var k) *)
val () = out "EE_DL2_INFRA_OK\n";

(* ---------------------------------------------------------------------------
   dvd helpers we still need on ctxtEC (intro/refl/dest/cancel-left).
   --------------------------------------------------------------------------- *)
(* dvd_introE already defined in the partial (hyp : oeq b (a*w) -> dvd a b). *)
(* dvd a a *)
fun dvdReflE2 t = dvd_reflE t;
(* dvd 1 t : t = 1*t *)
fun dvd_oneE t =
  let val m1 = symmE (trans2E (multcommE (one, t), mult1rE t))  (* oeq t (mult 1 t) *)
  in dvd_introE (one, t, t) m1 end;
(* dvd dest : from dvd a b expose k with b = a*k *)
fun dvd_destE (aT, bT, goalT) hdvd body =
  let val Pabs = Abs("k", natT, oeq bT (mult aT (Bound 0)))
  in exE_E (Pabs, goalT) hdvd body end;
(* dvd_cancel_left : lt 0 c ==> dvd (c*x)(c*y) ==> dvd x y *)
fun dvdCancelLeftE (cT, xT, yT) hPos hdvd =
  dvd_destE (mult cT xT, mult cT yT, dvd xT yT) hdvd
    (fn (kF, hk) =>    (* hk : oeq (c*y)(mult (c*x) k) *)
      let val assoc = multassocE (cT, xT, kF)          (* (c*x)*k = c*(x*k) *)
          val cy_cxk = trans2E (hk, assoc)             (* c*y = c*(x*k) *)
          val y_xk = multLeftCancelE (cT, yT, mult xT kF) hPos cy_cxk  (* y = x*k *)
      in dvd_introE (xT, yT, kF) y_xk end);

val () = out "EE_DL2_DVDHELP_OK\n";

(* ---------------------------------------------------------------------------
   STEP 1 : transfer strong_induct, dzos, Suc helpers ; build lt-0 helpers.
   --------------------------------------------------------------------------- *)
val strong_induct_vE = upE (varify (up strong_induct));   (* (!!n.(!!m. lt m n ==> P m) ==> P n) ==> P k *)
val dzos_vE      = upE (varify disj_zero_or_suc);         (* Disj (oeq p 0)(Ex q. p = Suc q) *)
val Suc_neq_Zero_vE = upE Suc_neq_Zero_vD;
val add_Suc_vE   = upE (varify (up add_Suc));            (* add (Suc m) n = Suc(add m n) *)
val Suc_cong_vE  = upE (varify (up Suc_cong));           (* a=b ==> Suc a = Suc b *)
val Suc_inj_vE   = upE (varify Suc_inj_ax);              (* Suc a = Suc b ==> a = b *)

fun dzosE t = beta_norm (Drule.infer_instantiate ctxtEC [(("p",0), ctermEC t)] dzos_vE);
(* Suc_cong : a=b -> Suc a = Suc b *)
fun ScongE (aT,bT) hab = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtEC
      [(("a",0), ctermEC aT),(("b",0), ctermEC bT)] Suc_cong_vE)) hab;
fun SinjE (aT,bT) hSab = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtEC
      [(("a",0), ctermEC aT),(("b",0), ctermEC bT)] Suc_inj_vE)) hSab;
fun SneqZE t = beta_norm (Drule.infer_instantiate ctxtEC [(("n",0), ctermEC t)] Suc_neq_Zero_vE);
fun add0E2 t = beta_norm (Drule.infer_instantiate ctxtEC [(("n",0), ctermEC t)] add_0_vE);
fun addSucE (mT,nT) = beta_norm (Drule.infer_instantiate ctxtEC
      [(("m",0), ctermEC mT),(("n",0), ctermEC nT)] add_Suc_vE);

(* lt 0 c on ctxtEC : from oeq c (Suc m) build witness. lt 0 c = le 1 c = Ex p. c = add 1 p. *)
fun ltZeroSucE (cT, mT) hcSm =   (* hcSm : oeq c (Suc m) -> lt 0 c *)
  let
    val a1m = addSucE (ZeroC, mT)            (* add (Suc 0) m = Suc(add 0 m) *)
    val a0m = add0E2 mT                       (* add 0 m = m *)
    val sucEq = ScongE (add ZeroC mT, mT) a0m (* Suc(add 0 m) = Suc m *)
    val a1m_sm = trans2E (a1m, sucEq)         (* add (Suc 0) m = Suc m *)
    val c_a1m = trans2E (hcSm, symmE a1m_sm)  (* c = add (Suc 0) m *)
    val wAbs = Abs("p", natT, oeq cT (add (suc ZeroC) (Bound 0)))
  in exI_E (wAbs, mT) c_a1m end;

(* lt m n term : lt m n = le (Suc m) n.  We use the base `lt` from the partial scope. *)
(* lt 0 (p2 a) : from pow2_pos (Ex m. p2 a = Suc m) + ltZeroSucE. *)
fun lt0p2E aT =
  let val pp = beta_norm (Drule.infer_instantiate ctxtEC [(("k",0), ctermEC aT)] pow2_pos_vE)  (* Ex m. p2 a = Suc m *)
      val exAbs = Abs("m", natT, oeq (p2 aT)(suc (Bound 0)))
  in exE_E (exAbs, lt ZeroC (p2 aT)) pp (fn (mF, hm) => ltZeroSucE (p2 aT, mF) hm) end;
val () = out "EE_DL2_STRONG_OK\n";

(* ---------------------------------------------------------------------------
   STEP 2 : two_dvd_pow2_suc  :  dvd 2 (p2 (Suc i))     (witness p2 i)
   --------------------------------------------------------------------------- *)
fun two_dvd_pow2_sucE i =
  let val ps = powSucE (two, i)   (* p2 (Suc i) = mult 2 (p2 i) *)
  in dvd_introE (two, p2 (suc i), p2 i) ps end;

(* ---------------------------------------------------------------------------
   STEP 3 : THE 2-ADIC SPLIT (self-contained, strong induction; cofactor odd):
     pow2_split : lt 0 e ==> Ex i. Ex d. oeq e (mult (p2 i) d) /\ neg (dvd 2 d)
   Strong induction on e.  Split on dvd 2 e (ex_middle):
     neg(2|e) : i=0, d=e ; e = 2^0*e = 1*e = e.
     2|e      : e = 2*e' ; e'<e ; e'>0 ; IH(e') gives e'=2^i'*d', odd d' ;
                e = 2*2^i'*d' = 2^(Suc i')*d'.  i=Suc i', d=d'.
   --------------------------------------------------------------------------- *)
val pow2_split =
  let
    val eF = Free("e_sp", natT)
    fun splitGoal et = mkEx (Term.lambda (Free("i",natT))
                         (mkEx (Term.lambda (Free("d",natT))
                            (mkConj (oeq et (mult (p2 (Free("i",natT))) (Free("d",natT))))
                                    (neg (dvd two (Free("d",natT))))))))
    fun Pbody et = mkImp (lt ZeroC et) (splitGoal et)
    val Ppred = Term.lambda eF (Pbody eF)
    (* strong induct step : !!n. (!!m. lt m n ==> jT (P m)) ==> jT (P n) *)
    val nS = Free("n_sp", natT)
    val mG = Free("m_spg", natT)
    val Gprop = Logic.all mG (Logic.mk_implies (jT (lt mG nS), jT (Pbody mG)))
    val IH = Thm.assume (ctermEC Gprop)
    fun applyIH (cT, hltc) = Thm.implies_elim (Thm.forall_elim (ctermEC cT) IH) hltc
    (* prove jT (P n) : assume lt 0 n, produce splitGoal n *)
    val hPos = Thm.assume (ctermEC (jT (lt ZeroC nS)))
    val em = exMiddleE (dvd two nS)   (* Disj (dvd 2 n)(neg(dvd 2 n)) *)
    val goalC = splitGoal nS
    (* case neg(2|n) : i=0, d=n *)
    val caseOdd =
      let
        val hodd = Thm.assume (ctermEC (jT (neg (dvd two nS))))
        (* n = 2^0 * n = 1*n = n : oeq n (mult (p2 0) n) *)
        val pz = powZeroE two                        (* p2 0 = 1 *)
        (* mult (p2 0) n = mult 1 n = n ; want oeq n (mult (p2 0) n) *)
        val m1n = trans2E (mult_cong_lE (p2 ZeroC, one, nS) pz,
                           trans2E (multcommE (one, nS), mult1rE nS))  (* mult (p2 0) n = n *)
        val n_eq = symmE m1n                          (* n = mult (p2 0) n *)
        val cj = conjI_E (oeq nS (mult (p2 ZeroC) nS), neg (dvd two nS)) n_eq hodd
        val Pd = Term.lambda (Free("d",natT))
                   (mkConj (oeq nS (mult (p2 ZeroC) (Free("d",natT)))) (neg (dvd two (Free("d",natT)))))
        val exd = exI_E (Pd, nS) cj
        val Pi = Term.lambda (Free("i",natT))
                   (mkEx (Term.lambda (Free("d",natT))
                      (mkConj (oeq nS (mult (p2 (Free("i",natT))) (Free("d",natT))))
                              (neg (dvd two (Free("d",natT)))))))
        val exi = exI_E (Pi, ZeroC) exd
      in Thm.implies_intr (ctermEC (jT (neg (dvd two nS)))) exi end
    (* case 2|n : n = 2*e' *)
    val caseEven =
      let
        val h2n = Thm.assume (ctermEC (jT (dvd two nS)))
        (* dvd 2 n : n = 2*e' *)
        val Pk = Abs("k", natT, oeq nS (mult two (Bound 0)))
      in Thm.implies_intr (ctermEC (jT (dvd two nS)))
           (dvd_destE (two, nS, goalC) h2n
             (fn (e'F, he') =>    (* he' : oeq n (mult 2 e') *)
               let
                 (* e' > 0 : else n = 2*0 = 0, contra lt 0 n.  e' = Suc e'' (dzos). *)
                 val dz = dzosE e'F   (* Disj (oeq e' 0)(Ex q. e' = Suc q) *)
                 val PqES = Abs("q", natT, oeq e'F (suc (Bound 0)))
                 val caseE0 =
                   let
                     val he0 = Thm.assume (ctermEC (jT (oeq e'F ZeroC)))
                     (* n = 2*e' = 2*0 = 0 ; lt 0 n -> lt 0 0 -> false *)
                     val n0 = trans2E (he', trans2E (mult_cong_rE (two, e'F, ZeroC) he0, mult0rE two))  (* n = 0 *)
                     (* lt 0 n = le 1 n ; rewrite n->0 in (le 1 n) -> le 1 0 -> Ex p. 0 = Suc(add 0 p)... false *)
                     val Plt = Term.lambda (Free("zln",natT)) (lt ZeroC (Free("zln",natT)))
                     val lt00 = substPredE (Plt, nS, ZeroC) n0 hPos    (* lt 0 0 = le 1 0 = Ex p. 0 = add 1 p *)
                     (* le 1 0 : Ex p. 0 = add (Suc 0) p = Suc(add 0 p) -> Suc_neq_Zero *)
                     val ff =
                       let val Pp = Abs("p", natT, oeq ZeroC (add (suc ZeroC) (Bound 0)))
                       in exE_E (Pp, oFalseC) lt00
                            (fn (pF, hp) =>   (* hp : 0 = add (Suc 0) p *)
                               let val aS = addSucE (ZeroC, pF)   (* add (Suc 0) p = Suc(add 0 p) *)
                                   val z_S = trans2E (hp, aS)      (* 0 = Suc(add 0 p) *)
                               in Thm.implies_elim (SneqZE (add ZeroC pF)) (symmE z_S) end)
                       end
                   in Thm.implies_intr (ctermEC (jT (oeq e'F ZeroC))) (Thm.implies_elim (oFalse_elimE goalC) ff) end
                 val caseES =
                   let
                     val hex = Thm.assume (ctermEC (jT (mkEx PqES)))
                   in Thm.implies_intr (ctermEC (jT (mkEx PqES)))
                        (exE_E (PqES, goalC) hex
                          (fn (qF, hq) =>   (* hq : e' = Suc q *)
                            let
                              val ePos = ltZeroSucE (e'F, qF) hq   (* lt 0 e' *)
                              (* lt e' n : n = 2*e' = e' + e' > e' ; le (Suc e') n. *)
                              (* n = 2*e' ; 2*e' = e'+e' ? use: n = 2*e' and le (Suc e')(2*e').
                                 le (Suc e')(2*e') : 2*e' = e' + e' [from mult 2 e'].  Easier:
                                 lt e' n  via  n = mult 2 e' = add e' (mult 1 e')? Let's build directly:
                                 le (Suc e') n :  n = add (Suc q) (something)? Use le_add chain.
                                 Cleanest: 2*e' = e' + e' (two_mult), then le (Suc e')(e'+e') from e'=Suc q. *)
                              (* 2*e' = e' + e' : mult 2 e' = mult (Suc(Suc 0)) e' = e' + (e' + 0)... use base two_mult if present *)
                              val twoMul = trans2E (multcommE (two, e'F),  (* e'*2 *)
                                              (* e'*2 = e'*Suc(Suc 0) = e' + e'*Suc 0 = e' + (e' + e'*0) ... messy *)
                                              reflE (mult e'F two))   (* placeholder, replaced below *)
                              (* Build lt e' n directly:  lt e' n = le (Suc e') n.
                                 n = mult 2 e'.  We show le (Suc e')(mult 2 e') then transport via sym he'. *)
                              val le_Se_2e =
                                let
                                  (* mult 2 e' = add e' e' :  mult 2 e' = mult e' 2 [comm]
                                     mult e' 2 = mult e' (Suc(Suc 0)) = add e' (mult e' (Suc 0)) [mult_Suc_right]
                                       = add e' (add e' (mult e' 0)) = add e' (add e' 0) = add e' e'. *)
                                  val msr1 = beta_norm (Drule.infer_instantiate ctxtEC
                                        [(("n",0), ctermEC e'F),(("m",0), ctermEC (suc ZeroC))] (upE (varify mult_Suc_right)))
                                        (* mult e' (Suc(Suc 0)) = add e' (mult e' (Suc 0)) *)
                                  val msr2 = beta_norm (Drule.infer_instantiate ctxtEC
                                        [(("n",0), ctermEC e'F),(("m",0), ctermEC ZeroC)] (upE (varify mult_Suc_right)))
                                        (* mult e' (Suc 0) = add e' (mult e' 0) *)
                                  val me0 = mult0rE e'F                       (* mult e' 0 = 0 *)
                                  val msr2b = trans2E (msr2, add_cong_rE (e'F, mult e'F ZeroC, ZeroC) me0)  (* mult e'(Suc 0) = add e' 0 *)
                                  val ae0 = add0rE e'F                        (* add e' 0 = e' *)
                                  val me1 = trans2E (msr2b, ae0)              (* mult e'(Suc 0) = e' *)
                                  val msr1b = trans2E (msr1, add_cong_rE (e'F, mult e'F (suc ZeroC), e'F) me1)  (* mult e'(Suc(Suc 0)) = add e' e' *)
                                  val e2_ee = trans2E (multcommE (two, e'F), msr1b)   (* mult 2 e' = add e' e' *)
                                  (* le (Suc e')(add e' e') : add e' e' = add (Suc q) e' [e'=Suc q]
                                     = Suc(add q e') ; le (Suc e')(Suc(add q e')) <- le e' (add q e')? messy.
                                     Simpler: le (Suc e')(add e' e') via:  add e' e' = add e' (Suc q) [sym hq on 2nd]
                                       = Suc(add e' q)? no add e' (Suc q) = Suc(add e' q) [add_Suc_right].
                                     Then le (Suc e') (Suc(add e' q)) from le e' (add e' q) [le_add] via le_suc_mono. *)
                                  val addSucR = beta_norm (Drule.infer_instantiate ctxtEC
                                        [(("m",0), ctermEC e'F),(("n",0), ctermEC qF)] (upE (varify (up add_Suc_right))))
                                        (* add e' (Suc q) = Suc(add e' q) *)
                                  val ee_eSq = add_cong_rE (e'F, e'F, suc qF) hq   (* add e' e' = add e' (Suc q) *)
                                  val ee_S = trans2E (ee_eSq, addSucR)             (* add e' e' = Suc(add e' q) *)
                                  val le_e_eq = leAddE (e'F, qF)                   (* le e' (add e' q) *)
                                  val le_Se_Seq = leSucMonoE (e'F, add e'F qF) le_e_eq  (* le (Suc e')(Suc(add e' q)) *)
                                  (* transport le (Suc e')(Suc(add e' q)) -> le (Suc e')(add e' e') via sym ee_S *)
                                  val Ple = Term.lambda (Free("zle",natT)) (le (suc e'F) (Free("zle",natT)))
                                  val le_Se_ee = substPredE (Ple, suc (add e'F qF), add e'F e'F) (symmE ee_S) le_Se_Seq
                                  (* transport le (Suc e')(add e' e') -> le (Suc e')(mult 2 e') via sym e2_ee *)
                                  val le_Se_2e = substPredE (Ple, add e'F e'F, mult two e'F) (symmE e2_ee) le_Se_ee
                                in le_Se_2e end
                              (* le (Suc e') n : transport le (Suc e')(mult 2 e') via sym he' *)
                              val Ple2 = Term.lambda (Free("zle2",natT)) (le (suc e'F) (Free("zle2",natT)))
                              val lt_e_n = substPredE (Ple2, mult two e'F, nS) (symmE he') le_Se_2e   (* lt e' n *)
                              (* IH at e' : jT (P e') = Imp (lt 0 e')(splitGoal e') *)
                              val pE = applyIH (e'F, lt_e_n)
                              val gE = mp_E (lt ZeroC e'F, splitGoal e'F) pE ePos   (* splitGoal e' *)
                              (* destruct splitGoal e' : Ex i'. Ex d'. e' = 2^i' d' /\ odd d' *)
                              val Pi' = Term.lambda (Free("i",natT))
                                          (mkEx (Term.lambda (Free("d",natT))
                                             (mkConj (oeq e'F (mult (p2 (Free("i",natT))) (Free("d",natT))))
                                                     (neg (dvd two (Free("d",natT)))))))
                            in exE_E (Pi', goalC) gE
                                 (fn (i'F, hi') =>
                                   let
                                     val Pd' = Term.lambda (Free("d",natT))
                                                 (mkConj (oeq e'F (mult (p2 i'F) (Free("d",natT))))
                                                         (neg (dvd two (Free("d",natT)))))
                                   in exE_E (Pd', goalC) hi'
                                        (fn (d'F, hd') =>   (* hd' : e' = 2^i' d' /\ odd d' *)
                                          let
                                            val hee  = conjunct1_E (oeq e'F (mult (p2 i'F) d'F), neg (dvd two d'F)) hd'  (* e' = 2^i' d' *)
                                            val hodd = conjunct2_E (oeq e'F (mult (p2 i'F) d'F), neg (dvd two d'F)) hd'  (* odd d' *)
                                            (* n = 2*e' = 2*(2^i' d') = (2*2^i') d' = 2^(Suc i') d' *)
                                            val c1 = mult_cong_rE (two, e'F, mult (p2 i'F) d'F) hee   (* 2*e' = 2*(2^i' d') *)
                                            val assoc = symmE (multassocE (two, p2 i'F, d'F))         (* 2*(2^i' d') = (2*2^i') d' *)
                                            val psuc = symmE (powSucE (two, i'F))                     (* 2*2^i' = 2^(Suc i') ... powSuc: 2^(Suc i')=2*2^i' so sym *)
                                            (* (2*2^i') d' = (2^(Suc i')) d' via cong-l psuc *)
                                            val congP = mult_cong_lE (mult two (p2 i'F), p2 (suc i'F), d'F) psuc
                                            val n_form = trans2E (he', trans2E (c1, trans2E (assoc, congP)))  (* n = 2^(Suc i') d' *)
                                            val cj = conjI_E (oeq nS (mult (p2 (suc i'F)) d'F), neg (dvd two d'F)) n_form hodd
                                            val Pd = Term.lambda (Free("d",natT))
                                                       (mkConj (oeq nS (mult (p2 (suc i'F)) (Free("d",natT)))) (neg (dvd two (Free("d",natT)))))
                                            val exd = exI_E (Pd, d'F) cj
                                            val Pi = Term.lambda (Free("i",natT))
                                                       (mkEx (Term.lambda (Free("d",natT))
                                                          (mkConj (oeq nS (mult (p2 (Free("i",natT))) (Free("d",natT))))
                                                                  (neg (dvd two (Free("d",natT)))))))
                                          in exI_E (Pi, suc i'F) exd end)
                                   end)
                            end)
                          )
                   end
               in disjE_E (oeq e'F ZeroC, mkEx PqES, goalC) dz caseE0 caseES end))
      end
    val pN = impI_E (lt ZeroC nS, splitGoal nS) (disjE_E (dvd two nS, neg (dvd two nS), goalC) em caseEven caseOdd)  (* jT (Pbody nS) = jT(mkImp(lt 0 n)(splitGoal n)) *)
    val stepDisch = Thm.forall_intr (ctermEC nS) (Thm.implies_intr (ctermEC Gprop) pN)  (* !!n. G n ==> jT (P n) *)
    val kF = Free("e", natT)
    val siInst = beta_norm (Drule.infer_instantiate ctxtEC
                   [(("P",0), ctermEC Ppred),(("k",0), ctermEC kF)] strong_induct_vE)
    val Pk = Thm.implies_elim siInst stepDisch   (* jT (P e) = Imp (lt 0 e)(splitGoal e) *)
    val hPk = Thm.assume (ctermEC (jT (lt ZeroC kF)))
    val s1 = mp_E (lt ZeroC kF, splitGoal kF) Pk hPk
    val d1 = Thm.implies_intr (ctermEC (jT (lt ZeroC kF))) s1
  in varify d1 end;

val eVsp = Var(("e",0), natT)
val i_pow2_split =
  Logic.mk_implies (jT (lt ZeroC eVsp),
    jT (mkEx (Term.lambda (Free("i",natT))
          (mkEx (Term.lambda (Free("d",natT))
             (mkConj (oeq eVsp (mult (p2 (Free("i",natT))) (Free("d",natT))))
                     (neg (dvd two (Free("d",natT))))))))));
val r_split = chkEC ("pow2_split", pow2_split, i_pow2_split);
val () = if r_split then out "POW2_SPLIT_OK\n" else out "POW2_SPLIT_FAIL\n";


(* ===========================================================================
   POW2_PEEL : neg(dvd 2 m) ==> !!i. dvd (p2 i)(mult (p2 a) m) ==> dvd (p2 i)(p2 a)
   powers of 2 dividing 2^a*m (m odd) divide 2^a.   Induction on a, i UNIVERSAL.
   (object-Forall over i so the IH applies at the peeled i'.)
   =========================================================================== *)
val pow2_peel =
  let
    val mF = Free("m_pk", natT)
    val hOdd = Thm.assume (ctermEC (jT (neg (dvd two mF))))
    (* inner object body over i : Imp (dvd (p2 i)(2^a*m))(dvd (p2 i)(2^a)) *)
    fun iBodyAbs at = Term.lambda (Free("i",natT))
          (mkImp (dvd (p2 (Free("i",natT))) (mult (p2 at) mF))
                 (dvd (p2 (Free("i",natT))) (p2 at)))
    fun bodyA at = mkForall (iBodyAbs at)
    val zV = Free("z_pk", natT)
    val Qpred = Term.lambda zV (bodyA zV)
    val kIndA = Free("a_pk", natT)
    val ind = nat_induct_atE (Qpred, kIndA)
    (* base a=0 : !!i. dvd (p2 i) m ==> dvd (p2 i) 1.  (after mult (p2 0) m = m, p2 0 = 1) *)
    val base =
      let
        fun perI iF =
          let
            val hdvd = Thm.assume (ctermEC (jT (dvd (p2 iF) (mult (p2 ZeroC) mF))))
            val pz = powZeroE two
            val n0m = trans2E (mult_cong_lE (p2 ZeroC, one, mF) pz, trans2E (multcommE (one, mF), mult1rE mF))  (* mult (p2 0) m = m *)
            val hdvdM = dvd_cong_targetE (p2 iF, mult (p2 ZeroC) mF, mF) n0m hdvd   (* dvd (p2 i) m *)
            val goalI = dvd (p2 iF) (p2 ZeroC)
            val dz = dzosE iF
            val PqI = Abs("q", natT, oeq iF (suc (Bound 0)))
            val caseI0 =
              let
                val hi0 = Thm.assume (ctermEC (jT (oeq iF ZeroC)))
                val dref = dvd_reflE (p2 ZeroC)  (* dvd (p2 0)(p2 0) *)
                val p2i_eq_p20 =
                  let val Pe = Term.lambda (Free("ze",natT)) (oeq (p2 iF) (p2 (Free("ze",natT))))
                  in substPredE (Pe, iF, ZeroC) hi0 (reflE (p2 iF)) end   (* p2 i = p2 0 *)
                val res = dvd_cong_divisorE (p2 ZeroC, p2 iF, p2 ZeroC) (symmE p2i_eq_p20) dref  (* dvd (p2 i)(p2 0) *)
              in Thm.implies_intr (ctermEC (jT (oeq iF ZeroC))) res end
            val caseIS =
              let
                val hex = Thm.assume (ctermEC (jT (mkEx PqI)))
              in Thm.implies_intr (ctermEC (jT (mkEx PqI)))
                   (exE_E (PqI, goalI) hex
                     (fn (qF, hq) =>   (* hq : i = Suc q *)
                       let
                         val d2pi = dvd_cong_targetE (two, p2 (suc qF), p2 iF)
                                      (let val Pe = Term.lambda (Free("ze",natT)) (oeq (p2 (suc qF))(p2 (Free("ze",natT))))
                                       in substPredE (Pe, suc qF, iF) (symmE hq) (reflE (p2 (suc qF))) end)
                                      (two_dvd_pow2_sucE qF)   (* dvd 2 (p2 i) *)
                         val d2m = dvd_transE (two, p2 iF, mF) d2pi hdvdM
                         val ff = mp_E (dvd two mF, oFalseC) hOdd d2m
                       in Thm.implies_elim (oFalse_elimE goalI) ff end))
              end
            val res = disjE_E (oeq iF ZeroC, mkEx PqI, goalI) dz caseI0 caseIS
          in impI_E (dvd (p2 iF) (mult (p2 ZeroC) mF), goalI) res end
        val iFb = Free("i_pkb", natT)
      in allI_E (iBodyAbs ZeroC) (Thm.forall_intr (ctermEC iFb) (perI iFb)) end
    (* step a -> Suc a *)
    val xF = Free("x_pk", natT)
    val IH = Thm.assume (ctermEC (jT (bodyA xF)))   (* !!i. dvd (p2 i)(2^x*m) ==> dvd (p2 i)(2^x) *)
    val stepconcl =
      let
        fun perI iF =
          let
            val hdvd = Thm.assume (ctermEC (jT (dvd (p2 iF) (mult (p2 (suc xF)) mF))))
            val goalI = dvd (p2 iF) (p2 (suc xF))
            val dz = dzosE iF
            val PqI = Abs("q", natT, oeq iF (suc (Bound 0)))
            val caseI0 =
              let
                val hi0 = Thm.assume (ctermEC (jT (oeq iF ZeroC)))
                val dref1 = dvd_oneE (p2 (suc xF))   (* dvd 1 (p2(Suc x)) *)
                val pz = powZeroE two
                val p2i_1 =
                  let val Pe = Term.lambda (Free("ze",natT)) (oeq (p2 iF)(p2 (Free("ze",natT))))
                      val p2i_p20 = substPredE (Pe, iF, ZeroC) hi0 (reflE (p2 iF))
                  in trans2E (p2i_p20, pz) end        (* p2 i = 1 *)
                val res = dvd_cong_divisorE (one, p2 iF, p2 (suc xF)) (symmE p2i_1) dref1
              in Thm.implies_intr (ctermEC (jT (oeq iF ZeroC))) res end
            val caseIS =
              let
                val hex = Thm.assume (ctermEC (jT (mkEx PqI)))
              in Thm.implies_intr (ctermEC (jT (mkEx PqI)))
                   (exE_E (PqI, goalI) hex
                     (fn (i'F, hi) =>   (* hi : i = Suc i' *)
                       let
                         val pii  = powSucE (two, i'F)   (* p2(Suc i') = 2*p2 i' *)
                         val psx  = powSucE (two, xF)    (* p2(Suc x) = 2*p2 x *)
                         val tgt1 = mult_cong_lE (p2 (suc xF), mult two (p2 xF), mF) psx
                         val tgt2 = multassocE (two, p2 xF, mF)
                         val tgtN = trans2E (tgt1, tgt2)   (* mult(p2(Suc x)) m = 2*(p2 x*m) *)
                         val divEq =
                           let val Pe = Term.lambda (Free("ze",natT)) (oeq (p2 iF)(p2 (Free("ze",natT))))
                               val p2i_p2Si = substPredE (Pe, iF, suc i'F) hi (reflE (p2 iF))
                           in trans2E (p2i_p2Si, pii) end   (* p2 i = 2*p2 i' *)
                         val hd1 = dvd_cong_divisorE (p2 iF, mult two (p2 i'F), mult (p2 (suc xF)) mF) divEq hdvd
                         val hd2 = dvd_cong_targetE (mult two (p2 i'F), mult (p2 (suc xF)) mF, mult two (mult (p2 xF) mF)) tgtN hd1
                         val lt0two = ltZeroSucE (two, suc ZeroC) (reflE two)   (* lt 0 2 *)
                         val hd3 = dvdCancelLeftE (two, p2 i'F, mult (p2 xF) mF) lt0two hd2   (* dvd (p2 i')(2^x*m) *)
                         (* IH at i' : dvd (p2 i')(2^x*m) ==> dvd (p2 i')(2^x) *)
                         val ihAt = allE_E (iBodyAbs xF, i'F) IH   (* Imp (dvd (p2 i')(2^x*m))(dvd (p2 i')(2^x)) *)
                         val ihd  = mp_E (dvd (p2 i'F) (mult (p2 xF) mF), dvd (p2 i'F) (p2 xF)) ihAt hd3  (* dvd (p2 i')(2^x) *)
                         (* dvd (p2 i)(p2(Suc x)) : p2 i = 2*p2 i' , p2(Suc x) = 2*p2 x ;
                            dvd (p2 i')(p2 x) -> dvd (2*p2 i')(2*p2 x) -> rewrite. *)
                         (* dvd (2*p2 i')(2*p2 x) : p2 x = p2 i' * k -> 2*p2 x = (2*p2 i')*k *)
                         val hd2x = dvd_destE (p2 i'F, p2 xF, dvd (mult two (p2 i'F)) (mult two (p2 xF))) ihd
                                      (fn (kF, hk) =>   (* hk : oeq (p2 x)(mult (p2 i') k) *)
                                        let val c1 = mult_cong_rE (two, p2 xF, mult (p2 i'F) kF) hk   (* 2*p2 x = 2*(p2 i'*k) *)
                                            val c2 = symmE (multassocE (two, p2 i'F, kF))             (* 2*(p2 i'*k) = (2*p2 i')*k *)
                                            val eqn = trans2E (c1, c2)                                (* 2*p2 x = (2*p2 i')*k *)
                                        in dvd_introE (mult two (p2 i'F), mult two (p2 xF), kF) eqn end)
                         (* rewrite divisor 2*p2 i' -> p2 i and target 2*p2 x -> p2(Suc x) *)
                         val divBack = symmE divEq   (* 2*p2 i' = p2 i *)
                         val r1 = dvd_cong_divisorE (mult two (p2 i'F), p2 iF, mult two (p2 xF)) divBack hd2x  (* dvd (p2 i)(2*p2 x) *)
                         val tgtBack = symmE psx     (* 2*p2 x = p2(Suc x) *)
                         val r2 = dvd_cong_targetE (p2 iF, mult two (p2 xF), p2 (suc xF)) tgtBack r1  (* dvd (p2 i)(p2(Suc x)) *)
                       in r2 end))
              end
            val res = disjE_E (oeq iF ZeroC, mkEx PqI, goalI) dz caseI0 caseIS
          in impI_E (dvd (p2 iF) (mult (p2 (suc xF)) mF), goalI) res end
        val iFs = Free("i_pks", natT)
      in allI_E (iBodyAbs (suc xF)) (Thm.forall_intr (ctermEC iFs) (perI iFs)) end
    val step1 = Thm.forall_intr (ctermEC xF) (Thm.implies_intr (ctermEC (jT (bodyA xF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1            (* bodyA a, under hOdd *)
    val d2 = Thm.implies_intr (ctermEC (jT (neg (dvd two mF)))) r2
  in varify d2 end;

(* pow2_peel : neg(dvd 2 m) ==> Forall i. Imp (dvd (p2 i)(2^a*m))(dvd (p2 i)(2^a)). *)
val () = out ("POW2_PEEL_HYPS = " ^ Int.toString (length (Thm.hyps_of pow2_peel)) ^ "\n");
val () = out "POW2_PEEL_BUILT\n";


(* ===========================================================================
   LIST MEMBERSHIP BACKWARD helpers (inductions on the list).
     sym_leqE         : leq L M ==> leq M L
     mem_map2_bwd     : lmem d D ==> lmem (mult c d)(lmap2 c D)
     mem_append_left  : lmem y A ==> lmem y (lappend A B)
     mem_append_right : lmem y B ==> lmem y (lappend A B)
   =========================================================================== *)
val leq_refl_vE2 = upE leq_refl_vD;
fun leq_reflE2 LT = beta_norm (Drule.infer_instantiate ctxtEC [(("L",0), ctermEC LT)] leq_refl_vE2);
fun sym_leqE (LT, MT) hleq =
  let val Pz = Term.lambda (Free("zsl", natlistT)) (leqL (Free("zsl",natlistT)) LT)
      val inst = beta_norm (Drule.infer_instantiate ctxtEC
            [(("P",0), ctermEC Pz),(("L",0), ctermEC LT),(("M",0), ctermEC MT)] leq_subst_vE)
  in Thm.implies_elim (Thm.implies_elim inst hleq) (leq_reflE2 LT) end;
(* lnodup transport along leq : leq L M ==> lnodup L ==> lnodup M *)
fun lnodup_leqE (LT, MT) hleq hnd =
  let val Pz = Term.lambda (Free("znl", natlistT)) (lnodup (Free("znl",natlistT)))
      val inst = beta_norm (Drule.infer_instantiate ctxtEC
            [(("P",0), ctermEC Pz),(("L",0), ctermEC LT),(("M",0), ctermEC MT)] leq_subst_vE)
  in Thm.implies_elim (Thm.implies_elim inst hleq) hnd end;

val mem_map2_bwd =
  let
    val cF = Free("c", natT); val dF = Free("d_mb", natT)
    fun body Lt = mkImp (lmem dF Lt) (lmem (mult cF dF) (lmap2 cF Lt))
    val zL = Free("zL", natlistT)
    val Qpred = Term.lambda zL (body zL)
    val kIndL = Free("L", natlistT)
    val ind = list_induct_atE (Qpred, kIndL)
    val base =
      let val hmem = Thm.assume (ctermEC (jT (lmem dF lnilC)))
          val ff = Thm.implies_elim (lmemNilElimE2 dF) hmem
      in impI_E (lmem dF lnilC, lmem (mult cF dF)(lmap2 cF lnilC))
           (Thm.implies_elim (oFalse_elimE (lmem (mult cF dF)(lmap2 cF lnilC))) ff) end
    val xF = Free("x", natT); val tF = Free("t", natlistT)
    val IH = Thm.assume (ctermEC (jT (body tF)))
    val stepconcl =
      let
        val goal = lmem (mult cF dF) (lmap2 cF (lcons xF tF))
        val consForm = lcons (mult cF xF)(lmap2 cF tF)   (* lmap2 c (lcons x t) = this (via mleq) *)
        val innerGoal = lmem (mult cF dF) consForm
        val hmem = Thm.assume (ctermEC (jT (lmem dF (lcons xF tF))))
        val dj   = Thm.implies_elim (lmemConsFwdE2 (dF, xF, tF)) hmem   (* Disj(oeq d x)(lmem d t) *)
        val caseEq =
          let val heq = Thm.assume (ctermEC (jT (oeq dF xF)))   (* d = x *)
              val cdcx = mult_cong_rE (cF, dF, xF) heq    (* c*d = c*x *)
              val memcx = Thm.implies_elim (lmemConsBwdE (mult cF xF, mult cF xF, lmap2 cF tF))
                            (disjI1_E (oeq (mult cF xF)(mult cF xF), lmem (mult cF xF)(lmap2 cF tF)) (reflE (mult cF xF)))
              val Pe = Term.lambda (Free("ze",natT)) (lmem (Free("ze",natT)) consForm)
              val memcd = substPredE (Pe, mult cF xF, mult cF dF) (symmE cdcx) memcx  (* lmem (c*d) consForm *)
          in Thm.implies_intr (ctermEC (jT (oeq dF xF))) memcd end
        val caseMem =
          let val hmt = Thm.assume (ctermEC (jT (lmem dF tF)))
              val memt = mp_E (lmem dF tF, lmem (mult cF dF)(lmap2 cF tF)) IH hmt
              val memlc = Thm.implies_elim (lmemConsBwdE (mult cF dF, mult cF xF, lmap2 cF tF))
                            (disjI2_E (oeq (mult cF dF)(mult cF xF), lmem (mult cF dF)(lmap2 cF tF)) memt)
          in Thm.implies_intr (ctermEC (jT (lmem dF tF))) memlc end
        val resInner = disjE_E (oeq dF xF, lmem dF tF, innerGoal) dj caseEq caseMem
        val mleq = lmap2ConsE (cF, xF, tF)   (* leq (lmap2 c (lcons x t)) consForm *)
        val memG = lmem_leqE (mult cF dF, consForm, lmap2 cF (lcons xF tF))
                     (sym_leqE (lmap2 cF (lcons xF tF), consForm) mleq) resInner
      in impI_E (lmem dF (lcons xF tF), goal) memG end
    val step1 = Thm.forall_intr (ctermEC xF)
                  (Thm.forall_intr (ctermEC tF)
                    (Thm.implies_intr (ctermEC (jT (body tF))) stepconcl))
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in varify r2 end;
val () = out "MEM_MAP2_BWD_BUILT\n";

val mem_append_left =
  let
    val yF = Free("y", natT); val BF = Free("B", natlistT)
    fun body At = mkImp (lmem yF At) (lmem yF (lappend At BF))
    val zL = Free("zL", natlistT)
    val Qpred = Term.lambda zL (body zL)
    val kIndL = Free("A", natlistT)
    val ind = list_induct_atE (Qpred, kIndL)
    val base =
      let val hmem = Thm.assume (ctermEC (jT (lmem yF lnilC)))
          val ff = Thm.implies_elim (lmemNilElimE2 yF) hmem
      in impI_E (lmem yF lnilC, lmem yF (lappend lnilC BF))
           (Thm.implies_elim (oFalse_elimE (lmem yF (lappend lnilC BF))) ff) end
    val xF = Free("x", natT); val tF = Free("t", natlistT)
    val IH = Thm.assume (ctermEC (jT (body tF)))
    val stepconcl =
      let
        val goal = lmem yF (lappend (lcons xF tF) BF)
        val consForm = lcons xF (lappend tF BF)   (* lappend (lcons x t) B = this *)
        val innerGoal = lmem yF consForm
        val hmem = Thm.assume (ctermEC (jT (lmem yF (lcons xF tF))))
        val dj = Thm.implies_elim (lmemConsFwdE2 (yF, xF, tF)) hmem  (* Disj(oeq y x)(lmem y t) *)
        val caseEq =
          let val heq = Thm.assume (ctermEC (jT (oeq yF xF)))
              val mem = Thm.implies_elim (lmemConsBwdE (yF, xF, lappend tF BF))
                          (disjI1_E (oeq yF xF, lmem yF (lappend tF BF)) heq)
          in Thm.implies_intr (ctermEC (jT (oeq yF xF))) mem end
        val caseMem =
          let val hmt = Thm.assume (ctermEC (jT (lmem yF tF)))
              val memt = mp_E (lmem yF tF, lmem yF (lappend tF BF)) IH hmt
              val mem = Thm.implies_elim (lmemConsBwdE (yF, xF, lappend tF BF))
                          (disjI2_E (oeq yF xF, lmem yF (lappend tF BF)) memt)
          in Thm.implies_intr (ctermEC (jT (lmem yF tF))) mem end
        val resInner = disjE_E (oeq yF xF, lmem yF tF, innerGoal) dj caseEq caseMem
        val aleq = lappendConsE (xF, tF, BF)   (* leq (lappend (lcons x t) B) consForm *)
        val memG = lmem_leqE (yF, consForm, lappend (lcons xF tF) BF)
                     (sym_leqE (lappend (lcons xF tF) BF, consForm) aleq) resInner
      in impI_E (lmem yF (lcons xF tF), goal) memG end
    val step1 = Thm.forall_intr (ctermEC xF)
                  (Thm.forall_intr (ctermEC tF)
                    (Thm.implies_intr (ctermEC (jT (body tF))) stepconcl))
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in varify r2 end;
val () = out "MEM_APPEND_LEFT_BUILT\n";

(* mem_append_right : lmem y B ==> lmem y (lappend A B) ; induction on A *)
val mem_append_right =
  let
    val yF = Free("y", natT); val BF = Free("B", natlistT)
    fun body At = mkImp (lmem yF BF) (lmem yF (lappend At BF))
    val zL = Free("zL", natlistT)
    val Qpred = Term.lambda zL (body zL)
    val kIndL = Free("A", natlistT)
    val ind = list_induct_atE (Qpred, kIndL)
    val base =
      let val hmem = Thm.assume (ctermEC (jT (lmem yF BF)))
          val aleq = lappendNilE BF   (* leq (lappend lnil B) B *)
          val mem = lmem_leqE (yF, BF, lappend lnilC BF) (sym_leqE (lappend lnilC BF, BF) aleq) hmem
      in impI_E (lmem yF BF, lmem yF (lappend lnilC BF)) mem end
    val xF = Free("x", natT); val tF = Free("t", natlistT)
    val IH = Thm.assume (ctermEC (jT (body tF)))
    val stepconcl =
      let
        val goal = lmem yF (lappend (lcons xF tF) BF)
        val consForm = lcons xF (lappend tF BF)
        val hmem = Thm.assume (ctermEC (jT (lmem yF BF)))
        val memt = mp_E (lmem yF BF, lmem yF (lappend tF BF)) IH hmem   (* lmem y (lappend t B) *)
        val memC = Thm.implies_elim (lmemConsBwdE (yF, xF, lappend tF BF))
                     (disjI2_E (oeq yF xF, lmem yF (lappend tF BF)) memt)   (* lmem y consForm *)
        val aleq = lappendConsE (xF, tF, BF)
        val memG = lmem_leqE (yF, consForm, lappend (lcons xF tF) BF)
                     (sym_leqE (lappend (lcons xF tF) BF, consForm) aleq) memC
      in impI_E (lmem yF BF, goal) memG end
    val step1 = Thm.forall_intr (ctermEC xF)
                  (Thm.forall_intr (ctermEC tF)
                    (Thm.implies_intr (ctermEC (jT (body tF))) stepconcl))
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in varify r2 end;
val () = out "MEM_APPEND_RIGHT_BUILT\n";

(* ===========================================================================
   transfer le_split / le_zero_eq onto ctxtEC.
   =========================================================================== *)
val le_split_vE   = upE (varify le_split);     (* le i (Suc a) ==> Disj (oeq i (Suc a))(le i a) *)
val le_zero_eq_vE = upE (varify le_zero_eq);   (* le i 0 ==> oeq i 0 *)
fun leSplitE (iT, aT) hle =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("i",0), ctermEC iT),(("a",0), ctermEC aT)] le_split_vE)
  in Thm.implies_elim inst hle end;
fun leZeroEqE iT hle =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC [(("i",0), ctermEC iT)] le_zero_eq_vE)
  in Thm.implies_elim inst hle end;

(* ===========================================================================
   DL2_MEM_BWD : lmem d D ==> Forall i. Imp (le i a)(lmem (mult (p2 i) d)(dl2 a D))
   the converse of dl2_members : if d in D and i<=a then 2^i*d in dl2 a D.
   Induction on a, i UNIVERSAL.
   =========================================================================== *)
val dl2_mem_bwd =
  let
    val DF = Free("D", natlistT); val dF = Free("d_mw", natT)
    val hMemD = Thm.assume (ctermEC (jT (lmem dF DF)))    (* lmem d D *)
    fun iBodyAbs at = Term.lambda (Free("i",natT))
          (mkImp (le (Free("i",natT)) at) (lmem (mult (p2 (Free("i",natT))) dF) (dl2 at DF)))
    fun bodyA at = mkForall (iBodyAbs at)
    val zV = Free("z_mw", natT)
    val Qpred = Term.lambda zV (bodyA zV)
    val kIndA = Free("a_mw", natT)
    val ind = nat_induct_atE (Qpred, kIndA)
    (* base a=0 : !!i. le i 0 ==> lmem (2^i*d)(dl2 0 D).  le i 0 -> i=0 -> 2^i*d = d ; dl2 0 D = D. *)
    val base =
      let
        fun perI iF =
          let
            val hle = Thm.assume (ctermEC (jT (le iF ZeroC)))
            val i0 = leZeroEqE iF hle    (* i = 0 *)
            val goalI = lmem (mult (p2 iF) dF) (dl2 ZeroC DF)
            (* 2^i*d = 2^0*d = 1*d = d *)
            val p2i_1 =
              let val Pe = Term.lambda (Free("ze",natT)) (oeq (p2 iF)(p2 (Free("ze",natT))))
                  val p2i_p20 = substPredE (Pe, iF, ZeroC) i0 (reflE (p2 iF))   (* p2 i = p2 0 *)
              in trans2E (p2i_p20, powZeroE two) end   (* p2 i = 1 *)
            val md_d = trans2E (mult_cong_lE (p2 iF, one, dF) p2i_1, trans2E (multcommE (one, dF), mult1rE dF))  (* 2^i*d = d *)
            (* dl2 0 D = D : transport lmem d D -> lmem d (dl2 0 D) via sym(dl20E) *)
            val dleq = dl20E DF   (* leq (dl2 0 D) D *)
            val memD0 = lmem_leqE (dF, DF, dl2 ZeroC DF) (sym_leqE (dl2 ZeroC DF, DF) dleq) hMemD  (* lmem d (dl2 0 D) *)
            (* rewrite d -> 2^i*d in membership *)
            val Pm = Term.lambda (Free("zm",natT)) (lmem (Free("zm",natT)) (dl2 ZeroC DF))
            val res = substPredE (Pm, dF, mult (p2 iF) dF) (symmE md_d) memD0   (* lmem (2^i*d)(dl2 0 D) *)
          in impI_E (le iF ZeroC, goalI) res end
        val iFb = Free("i_mwb", natT)
      in allI_E (iBodyAbs ZeroC) (Thm.forall_intr (ctermEC iFb) (perI iFb)) end
    (* step a -> Suc a *)
    val xF = Free("x_mw", natT)
    val IH = Thm.assume (ctermEC (jT (bodyA xF)))   (* !!i. le i x ==> lmem (2^i*d)(dl2 x D) *)
    val stepconcl =
      let
        fun perI iF =
          let
            val hle = Thm.assume (ctermEC (jT (le iF (suc xF))))
            val goalI = lmem (mult (p2 iF) dF) (dl2 (suc xF) DF)
            val A2s = p2 (suc xF)
            (* dl2 (Suc x) D = lappend (lmap2 A2s D)(dl2 x D) ; build membership there then transport. *)
            val tgtList = lappend (lmap2 A2s DF)(dl2 xF DF)
            val dj = leSplitE (iF, xF) hle   (* Disj (oeq i (Suc x))(le i x) *)
            val caseEq =
              let
                val hi = Thm.assume (ctermEC (jT (oeq iF (suc xF))))   (* i = Suc x *)
                (* 2^i*d = 2^(Suc x)*d = A2s*d ; lmem (A2s*d)(lmap2 A2s D) [mem_map2_bwd] ;
                   then lmem (A2s*d)(lappend ..) [left]. rewrite A2s*d -> 2^i*d. *)
                val memMap = mp_E (lmem dF DF, lmem (mult A2s dF)(lmap2 A2s DF))
                               (beta_norm (Drule.infer_instantiate ctxtEC
                                  [(("c",0), ctermEC A2s),(("d_mb",0), ctermEC dF),(("L",0), ctermEC DF)] mem_map2_bwd))
                               hMemD   (* lmem (A2s*d)(lmap2 A2s D) *)
                val memL = mp_E (lmem (mult A2s dF)(lmap2 A2s DF), lmem (mult A2s dF) tgtList)
                             (beta_norm (Drule.infer_instantiate ctxtEC
                                [(("y",0), ctermEC (mult A2s dF)),(("A",0), ctermEC (lmap2 A2s DF)),(("B",0), ctermEC (dl2 xF DF))] mem_append_left))
                             memMap   (* lmem (A2s*d)(lappend ..) *)
                (* 2^i*d = A2s*d : p2 i = p2 (Suc x) = A2s [from hi] *)
                val p2iEq = let val Pe = Term.lambda (Free("ze",natT)) (oeq (p2 iF)(p2 (Free("ze",natT))))
                            in substPredE (Pe, iF, suc xF) hi (reflE (p2 iF)) end   (* p2 i = A2s *)
                val mdEq = mult_cong_lE (p2 iF, A2s, dF) p2iEq   (* 2^i*d = A2s*d *)
                val Pm = Term.lambda (Free("zm",natT)) (lmem (Free("zm",natT)) tgtList)
                val res = substPredE (Pm, mult A2s dF, mult (p2 iF) dF) (symmE mdEq) memL  (* lmem (2^i*d)(lappend ..) *)
              in Thm.implies_intr (ctermEC (jT (oeq iF (suc xF)))) res end
            val caseLe =
              let
                val hlex = Thm.assume (ctermEC (jT (le iF xF)))   (* le i x *)
                val ihAt = allE_E (iBodyAbs xF, iF) IH   (* Imp (le i x)(lmem (2^i*d)(dl2 x D)) *)
                val memDl = mp_E (le iF xF, lmem (mult (p2 iF) dF)(dl2 xF DF)) ihAt hlex   (* lmem (2^i*d)(dl2 x D) *)
                val memR = mp_E (lmem (mult (p2 iF) dF)(dl2 xF DF), lmem (mult (p2 iF) dF) tgtList)
                             (beta_norm (Drule.infer_instantiate ctxtEC
                                [(("y",0), ctermEC (mult (p2 iF) dF)),(("A",0), ctermEC (lmap2 A2s DF)),(("B",0), ctermEC (dl2 xF DF))] mem_append_right))
                             memDl   (* lmem (2^i*d)(lappend ..) *)
              in Thm.implies_intr (ctermEC (jT (le iF xF))) memR end
            val resInner = disjE_E (oeq iF (suc xF), le iF xF, lmem (mult (p2 iF) dF) tgtList) dj caseEq caseLe
            (* transport lmem (2^i*d)(lappend ..) -> lmem (2^i*d)(dl2 (Suc x) D) via sym(dl2SucE) *)
            val dleq = dl2SucE (xF, DF)   (* leq (dl2 (Suc x) D) tgtList *)
            val memG = lmem_leqE (mult (p2 iF) dF, tgtList, dl2 (suc xF) DF)
                         (sym_leqE (dl2 (suc xF) DF, tgtList) dleq) resInner
          in impI_E (le iF (suc xF), goalI) memG end
        val iFs = Free("i_mws", natT)
      in allI_E (iBodyAbs (suc xF)) (Thm.forall_intr (ctermEC iFs) (perI iFs)) end
    val step1 = Thm.forall_intr (ctermEC xF) (Thm.implies_intr (ctermEC (jT (bodyA xF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1            (* bodyA a, under hMemD *)
    val d2 = Thm.implies_intr (ctermEC (jT (lmem dF DF))) r2
  in varify d2 end;
val () = out ("DL2_MEM_BWD_HYPS = " ^ Int.toString (length (Thm.hyps_of dl2_mem_bwd)) ^ "\n");
val () = out "DL2_MEM_BWD_BUILT\n";

(* ===========================================================================
   ODD_COPRIME_2_CANCEL : neg(dvd 2 d) ==> dvd d (mult two X) ==> dvd d X
     d | 2X, d odd  ==>  d | X.   (Gauss cancellation at the prime 2.)
   Proof : 2X = d*k ; 2 | d*k [witness X] ; euclid_lemma@2 -> 2|d (no) or 2|k ;
           k = 2k' ; 2X = d*2k' = 2*(d*k') ; cancel 2 -> X = d*k'.
   =========================================================================== *)
fun odd_coprime_2_cancelE (dT, XT) hOddd hdvd =
  dvd_destE (dT, mult two XT, dvd dT XT) hdvd
    (fn (kF, hk) =>    (* hk : oeq (mult 2 X)(mult d k) *)
      let
        (* 2 | d*k : d*k = 2*X [sym hk] -> witness X *)
        val d2dk = dvd_introE (two, mult dT kF, XT) (symmE hk)   (* dvd 2 (d*k) *)
        val disj = euclidLemmaE (two, dT, kF) prime2_two_vE d2dk  (* Disj(2|d)(2|k) *)
        val caseL =
          let val h2d = Thm.assume (ctermEC (jT (dvd two dT)))
              val ff = mp_E (dvd two dT, oFalseC) hOddd h2d
          in Thm.implies_intr (ctermEC (jT (dvd two dT))) (Thm.implies_elim (oFalse_elimE (dvd dT XT)) ff) end
        val caseR =
          let val h2k = Thm.assume (ctermEC (jT (dvd two kF)))
          in Thm.implies_intr (ctermEC (jT (dvd two kF)))
               (dvd_destE (two, kF, dvd dT XT) h2k
                 (fn (k'F, hk') =>   (* hk' : oeq k (mult 2 k') *)
                   let
                     (* 2X = d*k = d*(2k') = (d*2)k' = (2*d)k' = 2*(d*k') *)
                     val e1 = mult_cong_rE (dT, kF, mult two k'F) hk'   (* d*k = d*(2k') *)
                     val e2 = symmE (multassocE (dT, two, k'F))         (* d*(2k') = (d*2)k' *)
                     val e3 = mult_cong_lE (mult dT two, mult two dT, k'F) (multcommE (dT, two))  (* (d*2)k' = (2*d)k' *)
                     val e4 = multassocE (two, dT, k'F)                 (* (2*d)k' = 2*(d*k') *)
                     val dk_chain = trans2E (e1, trans2E (e2, trans2E (e3, e4)))   (* d*k = 2*(d*k') *)
                     val twoX_eq = trans2E (hk, dk_chain)               (* 2X = 2*(d*k') *)
                     val lt0two = ltZeroSucE (two, suc ZeroC) (reflE two)  (* lt 0 2 *)
                     val Xeq = multLeftCancelE (two, XT, mult dT k'F) lt0two twoX_eq  (* X = d*k' *)
                   in dvd_introE (dT, XT, k'F) Xeq end))
          end
      in disjE_E (dvd two dT, dvd two kF, dvd dT XT) disj caseL caseR end);

(* ODD_DVD_PEEL : neg(dvd 2 d) ==> dvd d (mult (p2 w) m) ==> dvd d m.  Induction on w. *)
val odd_dvd_peel =
  let
    val dF = Free("d_op", natT); val mF = Free("m_op", natT)
    val hOddd = Thm.assume (ctermEC (jT (neg (dvd two dF))))
    fun bodyW wt = mkImp (dvd dF (mult (p2 wt) mF)) (dvd dF mF)
    val zV = Free("z_op", natT)
    val Qpred = Term.lambda zV (bodyW zV)
    val kIndW = Free("w_op", natT)
    val ind = nat_induct_atE (Qpred, kIndW)
    val base =
      let
        val hdvd = Thm.assume (ctermEC (jT (dvd dF (mult (p2 ZeroC) mF))))
        val pz = powZeroE two
        val n0m = trans2E (mult_cong_lE (p2 ZeroC, one, mF) pz, trans2E (multcommE (one, mF), mult1rE mF))  (* mult (p2 0) m = m *)
        val res = dvd_cong_targetE (dF, mult (p2 ZeroC) mF, mF) n0m hdvd   (* dvd d m *)
      in impI_E (dvd dF (mult (p2 ZeroC) mF), dvd dF mF) res end
    val xF = Free("x_op", natT)
    val IH = Thm.assume (ctermEC (jT (bodyW xF)))
    val stepconcl =
      let
        val hdvd = Thm.assume (ctermEC (jT (dvd dF (mult (p2 (suc xF)) mF))))
        (* mult (p2(Suc x)) m = 2*(p2 x*m) *)
        val psx = powSucE (two, xF)   (* p2(Suc x) = 2*p2 x *)
        val t1 = mult_cong_lE (p2 (suc xF), mult two (p2 xF), mF) psx
        val t2 = multassocE (two, p2 xF, mF)
        val tgt = trans2E (t1, t2)   (* mult(p2(Suc x)) m = 2*(p2 x*m) *)
        val hd2 = dvd_cong_targetE (dF, mult (p2 (suc xF)) mF, mult two (mult (p2 xF) mF)) tgt hdvd  (* dvd d (2*(p2 x*m)) *)
        val hd3 = odd_coprime_2_cancelE (dF, mult (p2 xF) mF) hOddd hd2   (* dvd d (p2 x*m) *)
        val res = mp_E (dvd dF (mult (p2 xF) mF), dvd dF mF) IH hd3   (* dvd d m *)
      in impI_E (dvd dF (mult (p2 (suc xF)) mF), dvd dF mF) res end
    val step1 = Thm.forall_intr (ctermEC xF) (Thm.implies_intr (ctermEC (jT (bodyW xF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
    val d2 = Thm.implies_intr (ctermEC (jT (neg (dvd two dF)))) r2
  in varify d2 end;
val () = out ("ODD_DVD_PEEL_HYPS = " ^ Int.toString (length (Thm.hyps_of odd_dvd_peel)) ^ "\n");
val () = out "ODD_DVD_PEEL_BUILT\n";
fun oddDvdPeelE (dT, wT, mT) hOddd hdvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
        [(("d_op",0), ctermEC dT),(("w_op",0), ctermEC wT),(("m_op",0), ctermEC mT)] odd_dvd_peel)
      val objImp = Thm.implies_elim inst hOddd   (* jT (Imp (dvd d (2^w m))(dvd d m)) : OBJECT impl *)
  in mp_E (dvd dT (mult (p2 wT) mT), dvd dT mT) objImp hdvd end;

(* ===========================================================================
   helper : odd m ==> neg(oeq m 0)   (m odd => m != 0, since 2|0)
   and     odd m ==> m != 0 as a meta (oeq m 0 ==> oFalse) for dvd_le.
   =========================================================================== *)
(* dvd 2 0 : 0 = 2*0 *)
val dvd_2_zero = dvd_introE (two, ZeroC, ZeroC) (symmE (mult0rE two));  (* dvd 2 0 *)
fun odd_nz_meta (mT, hOdd) =   (* hOdd : neg(dvd 2 m) ; returns (oeq m 0 ==> oFalse) *)
  let val hm0 = Thm.assume (ctermEC (jT (oeq mT ZeroC)))
      (* dvd 2 m : rewrite 0->m in dvd 2 0 *)
      val d2m = dvd_cong_targetE (two, ZeroC, mT) (symmE hm0) dvd_2_zero  (* dvd 2 m *)
      val ff = mp_E (dvd two mT, oFalseC) hOdd d2m
  in Thm.implies_intr (ctermEC (jT (oeq mT ZeroC))) ff end;

(* ===========================================================================
   DL2_COMPLETE :
     neg (dvd 2 m)
     ==> (!!d. lt 0 d ==> le d m ==> dvd d m ==> lmem d D)        [DHcmp]
     ==> !!e. dvd e (mult (p2 a) m) ==> lt 0 e ==> le e (mult (p2 a) m)
              ==> lmem e (dl2 a D)
   THE 2-ADIC SPLIT.  (a, m, D free ; e universal via the !!e meta form.)
   =========================================================================== *)
val dl2_complete =
  let
    val aF = Free("a", natT); val mF = Free("m", natT); val DF = Free("D", natlistT)
    val N = mult (p2 aF) mF
    val hOdd = Thm.assume (ctermEC (jT (neg (dvd two mF))))
    (* DHcmp as an object-Forall meta hypothesis : !!d. lt 0 d ==> le d m ==> dvd d m ==> lmem d D *)
    val dMeta = Free("d_cmp", natT)
    val dhcmpProp = Logic.all dMeta
        (Logic.mk_implies (jT (lt ZeroC dMeta),
          Logic.mk_implies (jT (le dMeta mF),
            Logic.mk_implies (jT (dvd dMeta mF), jT (lmem dMeta DF)))))
    val hDHcmp = Thm.assume (ctermEC dhcmpProp)
    fun applyDHcmp (dT, hpos, hle, hdvd) =
      let val s0 = Thm.forall_elim (ctermEC dT) hDHcmp
          val s1 = Thm.implies_elim s0 hpos
          val s2 = Thm.implies_elim s1 hle
          val s3 = Thm.implies_elim s2 hdvd
      in s3 end
    (* m > 0 (odd) , nz-meta for dvd_le *)
    val m_nz = odd_nz_meta (mF, hOdd)   (* oeq m 0 ==> oFalse *)
    (* per-e *)
    val eF = Free("e_c", natT)
    val goalE = lmem eF (dl2 aF DF)
    val hdvdEN = Thm.assume (ctermEC (jT (dvd eF N)))
    val hPosE  = Thm.assume (ctermEC (jT (lt ZeroC eF)))
    val hLeE   = Thm.assume (ctermEC (jT (le eF N)))
    (* split e : Ex i. Ex d'. e = 2^i*d' /\ odd d' *)
    val splitInst = beta_norm (Drule.infer_instantiate ctxtEC [(("e",0), ctermEC eF)] pow2_split)
    val splitTh = Thm.implies_elim splitInst hPosE   (* Ex i. Ex d'. e = 2^i*d' /\ odd d' *)
    val Pi = Term.lambda (Free("i",natT))
               (mkEx (Term.lambda (Free("d",natT))
                  (mkConj (oeq eF (mult (p2 (Free("i",natT))) (Free("d",natT))))
                          (neg (dvd two (Free("d",natT)))))))
    val body =
      exE_E (Pi, goalE) splitTh
        (fn (iF, hi) =>
          let
            val Pd = Term.lambda (Free("d",natT))
                       (mkConj (oeq eF (mult (p2 iF) (Free("d",natT))))
                               (neg (dvd two (Free("d",natT)))))
          in exE_E (Pd, goalE) hi
               (fn (dpF, hd) =>   (* hd : e = 2^i*dp /\ odd dp *)
                 let
                   val heE  = conjunct1_E (oeq eF (mult (p2 iF) dpF), neg (dvd two dpF)) hd  (* e = 2^i*dp *)
                   val hodp = conjunct2_E (oeq eF (mult (p2 iF) dpF), neg (dvd two dpF)) hd  (* odd dp *)
                   (* dvd (p2 i) e : witness dp ; e = (p2 i)*dp *)
                   val dvd_pi_e = dvd_introE (p2 iF, eF, dpF) heE   (* dvd (p2 i) e *)
                   (* dvd (p2 i) N : dvd_trans (p2 i) e N *)
                   val dvd_pi_N = dvd_transE (p2 iF, eF, N) dvd_pi_e hdvdEN   (* dvd (p2 i) N *)
                   (* pow2_peel : dvd (p2 i)(p2 a) *)
                   val peelInst = beta_norm (Drule.infer_instantiate ctxtEC
                                    [(("m_pk",0), ctermEC mF),(("a_pk",0), ctermEC aF)] pow2_peel)
                   val peelA = Thm.implies_elim peelInst hOdd   (* Forall i. dvd (p2 i)(p2 a*m) ==> dvd (p2 i)(p2 a) *)
                   val peelIBody = Term.lambda (Free("i",natT))
                         (mkImp (dvd (p2 (Free("i",natT))) (mult (p2 aF) mF))
                                (dvd (p2 (Free("i",natT))) (p2 aF)))
                   val peelAt = allE_E (peelIBody, iF) peelA
                   val dvd_pi_p2a = mp_E (dvd (p2 iF) (mult (p2 aF) mF), dvd (p2 iF) (p2 aF)) peelAt dvd_pi_N  (* dvd (p2 i)(p2 a) *)
                   (* pow2_dvd_char : Ex j. le j a /\ p2 i = p2 j *)
                   val pcTh = pow2DvdCharE (p2 iF, aF) dvd_pi_p2a
                   val Pj = Term.lambda (Free("j",natT))
                              (mkConj (le (Free("j",natT)) aF) (oeq (p2 iF) (p2 (Free("j",natT)))))
                 in exE_E (Pj, goalE) pcTh
                      (fn (jF, hj) =>   (* hj : le j a /\ p2 i = p2 j *)
                        let
                          val hlej   = conjunct1_E (le jF aF, oeq (p2 iF) (p2 jF)) hj   (* le j a *)
                          val hpij   = conjunct2_E (le jF aF, oeq (p2 iF) (p2 jF)) hj   (* p2 i = p2 j *)
                          (* dp | m : peel.  dvd (p2 j) dp? No: e = 2^i*dp = 2^j*dp [via hpij].
                             dvd e N -> 2^j*dp | 2^a*m.  le j a -> a = j+w -> 2^a = 2^j*2^w.
                             cancel 2^j -> dp | 2^w*m -> oddDvdPeel -> dp | m. *)
                          (* e = 2^j*dp : e = 2^i*dp [heE] ; 2^i = 2^j -> 2^i*dp = 2^j*dp *)
                          val e_2j_dp = trans2E (heE, mult_cong_lE (p2 iF, p2 jF, dpF) hpij)  (* e = 2^j*dp *)
                          (* dvd (2^j*dp) N : rewrite e -> 2^j*dp in hdvdEN *)
                          val dvd_2jdp_N = dvd_cong_divisorE (eF, mult (p2 jF) dpF, N) e_2j_dp hdvdEN  (* dvd (2^j*dp) N *)
                          (* le j a -> a = j+w *)
                          val Pw = Abs("w", natT, oeq aF (add jF (Bound 0)))
                        in exE_E (Pw, goalE) hlej
                             (fn (wF, hw) =>   (* hw : a = j+w *)
                               let
                                 (* 2^a = 2^(j+w) = 2^j*2^w *)
                                 val pa_eq = let val Pe = Term.lambda (Free("ze",natT)) (oeq (p2 aF)(p2 (Free("ze",natT))))
                                             in substPredE (Pe, aF, add jF wF) hw (reflE (p2 aF)) end  (* p2 a = p2 (j+w) *)
                                 val pa_prod = trans2E (pa_eq, powAddE (two, jF, wF))   (* p2 a = 2^j * 2^w *)
                                 (* N = 2^a*m = (2^j*2^w)*m = 2^j*(2^w*m) *)
                                 val N1 = mult_cong_lE (p2 aF, mult (p2 jF)(p2 wF), mF) pa_prod  (* N = (2^j*2^w)*m *)
                                 val N2 = multassocE (p2 jF, p2 wF, mF)                          (* (2^j*2^w)*m = 2^j*(2^w*m) *)
                                 val Nform = trans2E (N1, N2)   (* N = 2^j*(2^w*m) *)
                                 (* dvd (2^j*dp)(2^j*(2^w*m)) *)
                                 val dvd_2jdp_2jX = dvd_cong_targetE (mult (p2 jF) dpF, N, mult (p2 jF)(mult (p2 wF) mF)) Nform dvd_2jdp_N
                                 (* cancel 2^j (lt 0 (2^j)) *)
                                 val lt0p2j = lt0p2E jF
                                 val dvd_dp_X = dvdCancelLeftE (p2 jF, dpF, mult (p2 wF) mF) lt0p2j dvd_2jdp_2jX  (* dvd dp (2^w*m) *)
                                 (* oddDvdPeel : dp | m *)
                                 val dvd_dp_m = oddDvdPeelE (dpF, wF, mF) hodp dvd_dp_X   (* dvd dp m *)
                                 (* lt 0 dp : e = 2^i*dp , e>0 -> dp>0 (if dp=0 then e=0). *)
                                 val dp_pos =
                                   let
                                     (* assume dp=0 -> e = 2^i*0 = 0 -> lt 0 0 false ; use ex_middle on lt 0 dp *)
                                     val emdp = exMiddleE (lt ZeroC dpF)
                                     val caseP = let val h = Thm.assume (ctermEC (jT (lt ZeroC dpF)))
                                                 in Thm.implies_intr (ctermEC (jT (lt ZeroC dpF))) h end
                                     val caseN =
                                       let val hng = Thm.assume (ctermEC (jT (neg (lt ZeroC dpF))))
                                           (* neg(lt 0 dp) -> dp = 0 (dzos: dp=0 or dp=Suc q -> lt 0 dp).  *)
                                           val dz = dzosE dpF
                                           val dp0 =
                                             let val cZ = let val h0 = Thm.assume (ctermEC (jT (oeq dpF ZeroC)))
                                                          in Thm.implies_intr (ctermEC (jT (oeq dpF ZeroC))) h0 end
                                                 val cS = let val Pq = Abs("q",natT, oeq dpF (suc (Bound 0)))
                                                              val hx = Thm.assume (ctermEC (jT (mkEx Pq)))
                                                          in Thm.implies_intr (ctermEC (jT (mkEx Pq)))
                                                               (exE_E (Pq, oeq dpF ZeroC) hx
                                                                 (fn (qF,hq) =>
                                                                    let val ltp = ltZeroSucE (dpF, qF) hq  (* lt 0 dp *)
                                                                        val ff = mp_E (lt ZeroC dpF, oFalseC) hng ltp
                                                                    in Thm.implies_elim (oFalse_elimE (oeq dpF ZeroC)) ff end)) end
                                             in disjE_E (oeq dpF ZeroC, mkEx (Abs("q",natT, oeq dpF (suc (Bound 0)))), oeq dpF ZeroC) dz cZ cS end
                                           (* e = 2^i*dp = 2^i*0 = 0 -> lt 0 e false *)
                                           val e0 = trans2E (heE, trans2E (mult_cong_rE (p2 iF, dpF, ZeroC) dp0, mult0rE (p2 iF)))  (* e = 0 *)
                                           val Plt = Term.lambda (Free("zl",natT)) (lt ZeroC (Free("zl",natT)))
                                           val lt00 = substPredE (Plt, eF, ZeroC) e0 hPosE  (* lt 0 0 *)
                                           val ff = let val Pp = Abs("p",natT, oeq ZeroC (add (suc ZeroC) (Bound 0)))
                                                    in exE_E (Pp, oFalseC) lt00
                                                         (fn (pF,hp) => Thm.implies_elim (SneqZE (add ZeroC pF)) (symmE (trans2E (hp, addSucE (ZeroC,pF))))) end
                                       in Thm.implies_intr (ctermEC (jT (neg (lt ZeroC dpF)))) (Thm.implies_elim (oFalse_elimE (lt ZeroC dpF)) ff) end
                                   in disjE_E (lt ZeroC dpF, neg (lt ZeroC dpF), lt ZeroC dpF) emdp caseP caseN end
                                 (* le dp m : dvd dp m + m != 0 *)
                                 val le_dp_m = dvdLeE (dpF, mF) dvd_dp_m m_nz   (* le dp m *)
                                 (* dp in D *)
                                 val memD = applyDHcmp (dpF, dp_pos, le_dp_m, dvd_dp_m)   (* lmem dp D *)
                                 (* dl2_mem_bwd : lmem dp D ==> Forall j. le j a ==> lmem (2^j*dp)(dl2 a D) *)
                                 val mbInst = beta_norm (Drule.infer_instantiate ctxtEC
                                                [(("D",0), ctermEC DF),(("d_mw",0), ctermEC dpF),(("a_mw",0), ctermEC aF)] dl2_mem_bwd)
                                 val mbA = Thm.implies_elim mbInst memD   (* Forall j. le j a ==> lmem (2^j*dp)(dl2 a D) *)
                                 val mbIBody = Term.lambda (Free("i",natT))
                                       (mkImp (le (Free("i",natT)) aF) (lmem (mult (p2 (Free("i",natT))) dpF) (dl2 aF DF)))
                                 val mbAt = allE_E (mbIBody, jF) mbA   (* le j a ==> lmem (2^j*dp)(dl2 a D) *)
                                 val mem_2jdp = mp_E (le jF aF, lmem (mult (p2 jF) dpF)(dl2 aF DF)) mbAt hlej  (* lmem (2^j*dp)(dl2 a D) *)
                                 (* rewrite 2^j*dp -> e via sym e_2j_dp *)
                                 val Pm = Term.lambda (Free("zm",natT)) (lmem (Free("zm",natT)) (dl2 aF DF))
                                 val res = substPredE (Pm, mult (p2 jF) dpF, eF) (symmE e_2j_dp) mem_2jdp  (* lmem e (dl2 a D) *)
                               in res end)
                        end)
                 end)
          end)
    (* discharge : e-premises (innermost first), then DHcmp, then odd. *)
    val d_le = Thm.implies_intr (ctermEC (jT (le eF N))) body
    val d_pos = Thm.implies_intr (ctermEC (jT (lt ZeroC eF))) d_le
    val d_dvd = Thm.implies_intr (ctermEC (jT (dvd eF N))) d_pos
    val d_e = Thm.forall_intr (ctermEC eF) d_dvd     (* !!e. dvd e N ==> lt 0 e ==> le e N ==> lmem e (dl2 a D) *)
    val d_cmp = Thm.implies_intr (ctermEC dhcmpProp) d_e
    val d_odd = Thm.implies_intr (ctermEC (jT (neg (dvd two mF)))) d_cmp
  in varify d_odd end;
val () = out ("DL2_COMPLETE_HYPS = " ^ Int.toString (length (Thm.hyps_of dl2_complete)) ^ "\n");
val () = out "DL2_COMPLETE_BUILT\n";

(* ===========================================================================
   VALIDATION : dl2_complete is 0-hyp + aconv intended.
   =========================================================================== *)
val aVcc = Var(("a",0), natT); val mVcc = Var(("m",0), natT); val DVcc = Var(("D",0), natlistT)
val Ncc = mult (p2 aVcc) mVcc
val dMcc = Free("d_cmp", natT)   (* same Free used in the construction *)
val eMcc = Free("e_c", natT)
val dhcmp_intended = Logic.all dMcc
    (Logic.mk_implies (jT (lt ZeroC dMcc),
      Logic.mk_implies (jT (le dMcc mVcc),
        Logic.mk_implies (jT (dvd dMcc mVcc), jT (lmem dMcc DVcc)))))
val i_dl2_complete =
  Logic.mk_implies (jT (neg (dvd two mVcc)),
    Logic.mk_implies (dhcmp_intended,
      Logic.all eMcc
        (Logic.mk_implies (jT (dvd eMcc Ncc),
          Logic.mk_implies (jT (lt ZeroC eMcc),
            Logic.mk_implies (jT (le eMcc Ncc), jT (lmem eMcc (dl2 aVcc DVcc))))))));
val nh_dc = length (Thm.hyps_of dl2_complete);
val ac_dc = (Thm.prop_of dl2_complete) aconv i_dl2_complete;
val () = out ("DL2_COMPLETE hyps=" ^ Int.toString nh_dc ^ " aconv=" ^ Bool.toString ac_dc ^ "\n");
val () =
  if nh_dc = 0 andalso ac_dc then out "DL2_COMPLETE_OK\n"
  else (out ("  got      = " ^ Syntax.string_of_term ctxtEC (Thm.prop_of dl2_complete) ^ "\n"
             ^ "  intended = " ^ Syntax.string_of_term ctxtEC i_dl2_complete ^ "\n");
        out "DL2_COMPLETE_BAD\n");

(* SOUNDNESS PROBE : dl2_complete genuinely needs the odd (neg dvd 2 m) hypothesis
   (else it would claim every divisor of 2^a*m is 2^i*d with d|m, false for even m). *)
val s_dc_needs_odd =
  not ((Thm.prop_of dl2_complete) aconv
       (Logic.mk_implies (dhcmp_intended,
          Logic.all eMcc
            (Logic.mk_implies (jT (dvd eMcc Ncc),
              Logic.mk_implies (jT (lt ZeroC eMcc),
                Logic.mk_implies (jT (le eMcc Ncc), jT (lmem eMcc (dl2 aVcc DVcc)))))))));
val () = if s_dc_needs_odd then out "PROBE_OK dl2_complete needs the odd(m) hypothesis\n"
         else out "PROBE_FAIL dl2_complete dropped the odd hypothesis!\n";
(* PROBE : genuinely conditional on the divisor premise (not unconditional lmem). *)
val s_dc_needs_dvd =
  not ((Thm.prop_of dl2_complete) aconv
       (Logic.mk_implies (jT (neg (dvd two mVcc)),
          Logic.mk_implies (dhcmp_intended,
            Logic.all eMcc (jT (lmem eMcc (dl2 aVcc DVcc)))))));
val () = if s_dc_needs_dvd then out "PROBE_OK dl2_complete is conditional on dvd e N\n"
         else out "PROBE_FAIL dl2_complete unconditional!\n";

val () = out "EE_DL2_COMPLETE_SECTION_DONE\n";

(* ===========================================================================
   PART (a) — LNODUP (dl2 a D).   Needs: cross-level 2^i*d distinctness.
   ----------------------------------------------------------------------------
   D-hyps used here: lnodup D ; (!!d. lmem d D ==> dvd d m) ; neg(dvd 2 m).
   ----------------------------------------------------------------------------
   dl2_members_form : lmem e (dl2 a D) ==> Ex j. Ex d'. le j a /\ lmem d' D /\ e = 2^j*d'
     (forward decomposition ; induction on a via mem_append + mem_map2).
   =========================================================================== *)
val dl2_members_form =
  let
    val DF = Free("D", natlistT)
    fun formGoal at et = mkEx (Term.lambda (Free("j",natT))
                           (mkEx (Term.lambda (Free("d",natT))
                              (mkConj (le (Free("j",natT)) at)
                                 (mkConj (lmem (Free("d",natT)) DF)
                                         (oeq et (mult (p2 (Free("j",natT))) (Free("d",natT)))))))))
    fun eBodyAbs at = Term.lambda (Free("e",natT))
          (mkImp (lmem (Free("e",natT)) (dl2 at DF)) (formGoal at (Free("e",natT))))
    fun bodyA at = mkForall (eBodyAbs at)
    val zV = Free("z_mf", natT)
    val Qpred = Term.lambda zV (bodyA zV)
    val kIndA = Free("a_mf", natT)
    val ind = nat_induct_atE (Qpred, kIndA)
    (* base a=0 : lmem e (dl2 0 D) -> lmem e D ; j=0, d'=e ; le 0 0 ; e = 2^0*e = e. *)
    val base =
      let
        fun perE eF =
          let
            val hmem = Thm.assume (ctermEC (jT (lmem eF (dl2 ZeroC DF))))
            val dleq = dl20E DF   (* leq (dl2 0 D) D *)
            val hmemD = lmem_leqE (eF, dl2 ZeroC DF, DF) dleq hmem   (* lmem e D *)
            (* le 0 0 *)
            val le00 = leReflE ZeroC   (* le 0 0 *)
            (* e = 2^0*e = 1*e = e ; want oeq e (mult (p2 0) e) *)
            val pz = powZeroE two
            val m0e = trans2E (mult_cong_lE (p2 ZeroC, one, eF) pz, trans2E (multcommE (one, eF), mult1rE eF))  (* 2^0*e = e *)
            val e_eq = symmE m0e   (* e = 2^0*e *)
            val cj = conjI_E (le ZeroC ZeroC, mkConj (lmem eF DF) (oeq eF (mult (p2 ZeroC) eF)))
                       le00 (conjI_E (lmem eF DF, oeq eF (mult (p2 ZeroC) eF)) hmemD e_eq)
            val Pd = Term.lambda (Free("d",natT))
                       (mkConj (le ZeroC ZeroC) (mkConj (lmem (Free("d",natT)) DF)
                          (oeq eF (mult (p2 ZeroC) (Free("d",natT))))))
            val exd = exI_E (Pd, eF) cj
            val Pj = Term.lambda (Free("j",natT))
                       (mkEx (Term.lambda (Free("d",natT))
                          (mkConj (le (Free("j",natT)) ZeroC)
                             (mkConj (lmem (Free("d",natT)) DF)
                                     (oeq eF (mult (p2 (Free("j",natT))) (Free("d",natT))))))))
            val exj = exI_E (Pj, ZeroC) exd
          in impI_E (lmem eF (dl2 ZeroC DF), formGoal ZeroC eF) exj end
        val eFb = Free("e_mfb", natT)
      in allI_E (eBodyAbs ZeroC) (Thm.forall_intr (ctermEC eFb) (perE eFb)) end
    (* step a -> Suc a : lmem e (dl2 (Suc a) D) ; dl2 (Suc a) D = lappend (lmap2 A2s D)(dl2 a D).
       mem_append -> Disj(lmem e (lmap2 A2s D))(lmem e (dl2 a D)).
       case map : mem_map2 -> Ex d. lmem d D /\ e = A2s*d ; j=Suc a, le (Suc a)(Suc a), e=2^(Suc a)*d.
       case dl2 : IH -> Ex j d'. le j a /\ lmem d' D /\ e = 2^j*d' ; le j (Suc a) via le_trans. *)
    val xF = Free("x_mf", natT)
    val IH = Thm.assume (ctermEC (jT (bodyA xF)))
    val stepconcl =
      let
        val A2s = p2 (suc xF)
        fun perE eF =
          let
            val goalF = formGoal (suc xF) eF
            val hmem = Thm.assume (ctermEC (jT (lmem eF (dl2 (suc xF) DF))))
            val dleq = dl2SucE (xF, DF)   (* leq (dl2 (Suc x) D)(lappend (lmap2 A2s D)(dl2 x D)) *)
            val hmem2 = lmem_leqE (eF, dl2 (suc xF) DF, lappend (lmap2 A2s DF)(dl2 xF DF)) dleq hmem
            val dj = mp_E (lmem eF (lappend (lmap2 A2s DF)(dl2 xF DF)),
                           mkDisj (lmem eF (lmap2 A2s DF))(lmem eF (dl2 xF DF)))
                       (beta_norm (Drule.infer_instantiate ctxtEC
                          [(("y",0), ctermEC eF),(("A",0), ctermEC (lmap2 A2s DF)),(("B",0), ctermEC (dl2 xF DF))] mem_append))
                       hmem2   (* Disj(lmem e (lmap2 A2s D))(lmem e (dl2 x D)) *)
            val caseMap =
              let
                val hmap = Thm.assume (ctermEC (jT (lmem eF (lmap2 A2s DF))))
                val exwit = mkEx (Term.lambda (Free("d",natT))
                              (mkConj (lmem (Free("d",natT)) DF)(oeq eF (mult A2s (Free("d",natT))))))
                val exT = mp_E (lmem eF (lmap2 A2s DF), exwit)
                            (beta_norm (Drule.infer_instantiate ctxtEC
                               [(("y",0), ctermEC eF),(("c",0), ctermEC A2s),(("L",0), ctermEC DF)] mem_map2))
                            hmap   (* Ex d. lmem d D /\ e = A2s*d *)
                val Pt = Term.lambda (Free("d",natT))
                           (mkConj (lmem (Free("d",natT)) DF)(oeq eF (mult A2s (Free("d",natT)))))
              in Thm.implies_intr (ctermEC (jT (lmem eF (lmap2 A2s DF))))
                   (exE_E (Pt, goalF) exT
                     (fn (dF, hdb) =>
                        let
                          val hmemd = conjunct1_E (lmem dF DF, oeq eF (mult A2s dF)) hdb   (* lmem d D *)
                          val heq   = conjunct2_E (lmem dF DF, oeq eF (mult A2s dF)) hdb   (* e = A2s*d *)
                          val leSS  = leReflE (suc xF)   (* le (Suc x)(Suc x) *)
                          val cj = conjI_E (le (suc xF)(suc xF), mkConj (lmem dF DF)(oeq eF (mult A2s dF)))
                                     leSS (conjI_E (lmem dF DF, oeq eF (mult A2s dF)) hmemd heq)
                          val Pd = Term.lambda (Free("d",natT))
                                     (mkConj (le (suc xF)(suc xF)) (mkConj (lmem (Free("d",natT)) DF)
                                        (oeq eF (mult A2s (Free("d",natT))))))
                          val exd = exI_E (Pd, dF) cj
                          val Pj = Term.lambda (Free("j",natT))
                                     (mkEx (Term.lambda (Free("d",natT))
                                        (mkConj (le (Free("j",natT)) (suc xF))
                                           (mkConj (lmem (Free("d",natT)) DF)
                                                   (oeq eF (mult (p2 (Free("j",natT))) (Free("d",natT))))))))
                        in exI_E (Pj, suc xF) exd end))
              end
            val caseDl =
              let
                val hdl = Thm.assume (ctermEC (jT (lmem eF (dl2 xF DF))))
                val ihAt = allE_E (eBodyAbs xF, eF) IH   (* Imp (lmem e (dl2 x D))(formGoal x e) *)
                val gx = mp_E (lmem eF (dl2 xF DF), formGoal xF eF) ihAt hdl   (* formGoal x e *)
                val Pj = Term.lambda (Free("j",natT))
                           (mkEx (Term.lambda (Free("d",natT))
                              (mkConj (le (Free("j",natT)) xF)
                                 (mkConj (lmem (Free("d",natT)) DF)
                                         (oeq eF (mult (p2 (Free("j",natT))) (Free("d",natT))))))))
              in Thm.implies_intr (ctermEC (jT (lmem eF (dl2 xF DF))))
                   (exE_E (Pj, goalF) gx
                     (fn (jF, hj) =>
                        let
                          val Pd = Term.lambda (Free("d",natT))
                                     (mkConj (le jF xF)
                                        (mkConj (lmem (Free("d",natT)) DF)
                                                (oeq eF (mult (p2 jF) (Free("d",natT))))))
                        in exE_E (Pd, goalF) hj
                             (fn (dF, hd) =>
                                let
                                  val hle  = conjunct1_E (le jF xF, mkConj (lmem dF DF)(oeq eF (mult (p2 jF) dF))) hd  (* le j x *)
                                  val rest = conjunct2_E (le jF xF, mkConj (lmem dF DF)(oeq eF (mult (p2 jF) dF))) hd
                                  val hmemd = conjunct1_E (lmem dF DF, oeq eF (mult (p2 jF) dF)) rest  (* lmem d D *)
                                  val heq   = conjunct2_E (lmem dF DF, oeq eF (mult (p2 jF) dF)) rest  (* e = 2^j*d *)
                                  (* le j (Suc x) : le j x , le x (Suc x) , le_trans *)
                                  val lex_Sx = leAddE (xF, suc ZeroC)   (* le x (add x 1) ; need le x (Suc x) *)
                                  (* le x (Suc x) : Suc x = x + 1 ; le_add (x, Suc 0) gives le x (add x (Suc 0)) ; add x (Suc 0) = Suc x *)
                                  val axS = beta_norm (Drule.infer_instantiate ctxtEC
                                        [(("m",0), ctermEC xF),(("n",0), ctermEC ZeroC)] (upE (varify (up add_Suc_right))))  (* add x (Suc 0) = Suc(add x 0) *)
                                  val ax0 = add0rE xF   (* add x 0 = x *)
                                  val axSx = trans2E (axS, ScongE (add xF ZeroC, xF) ax0)  (* add x (Suc 0) = Suc x *)
                                  val Ple = Term.lambda (Free("zle",natT)) (le xF (Free("zle",natT)))
                                  val le_x_Sx = substPredE (Ple, add xF (suc ZeroC), suc xF) axSx lex_Sx  (* le x (Suc x) *)
                                  val le_j_Sx = leTransE (jF, xF, suc xF) hle le_x_Sx   (* le j (Suc x) *)
                                  val cj = conjI_E (le jF (suc xF), mkConj (lmem dF DF)(oeq eF (mult (p2 jF) dF)))
                                             le_j_Sx (conjI_E (lmem dF DF, oeq eF (mult (p2 jF) dF)) hmemd heq)
                                  val Pd2 = Term.lambda (Free("d",natT))
                                             (mkConj (le jF (suc xF)) (mkConj (lmem (Free("d",natT)) DF)
                                                (oeq eF (mult (p2 jF) (Free("d",natT))))))
                                  val exd = exI_E (Pd2, dF) cj
                                  val Pj2 = Term.lambda (Free("j",natT))
                                             (mkEx (Term.lambda (Free("d",natT))
                                                (mkConj (le (Free("j",natT)) (suc xF))
                                                   (mkConj (lmem (Free("d",natT)) DF)
                                                           (oeq eF (mult (p2 (Free("j",natT))) (Free("d",natT))))))))
                                in exI_E (Pj2, jF) exd end)
                        end))
              end
            val res = disjE_E (lmem eF (lmap2 A2s DF), lmem eF (dl2 xF DF), goalF) dj caseMap caseDl
          in impI_E (lmem eF (dl2 (suc xF) DF), goalF) res end
        val eFs = Free("e_mfs", natT)
      in allI_E (eBodyAbs (suc xF)) (Thm.forall_intr (ctermEC eFs) (perE eFs)) end
    val step1 = Thm.forall_intr (ctermEC xF) (Thm.implies_intr (ctermEC (jT (bodyA xF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in varify r2 end;
val () = out "DL2_MEMBERS_FORM_BUILT\n";

(* ===========================================================================
   odd_of_dvd : neg(dvd 2 m) ==> dvd d m ==> neg(dvd 2 d)
     d | m, m odd ==> d odd  (else 2|d|m -> 2|m).
   =========================================================================== *)
fun odd_of_dvdE (dT, mT) hOddm hdvd =
  let val h2d = Thm.assume (ctermEC (jT (dvd two dT)))
      val d2m = dvd_transE (two, dT, mT) h2d hdvd   (* dvd 2 m *)
      val ff = mp_E (dvd two mT, oFalseC) hOddm d2m
  in impI_E (dvd two dT, oFalseC) ff end;   (* neg(dvd 2 d) : OBJECT Imp(dvd 2 d) oFalse *)

(* ===========================================================================
   NOTMEM_CROSS :
     neg(dvd 2 m) ==> (!!d. lmem d D ==> dvd d m)
       ==> lmem d D ==> neg(lmem (mult (p2 (Suc a)) d)(dl2 a D))
   (for a fixed a, d ; uses dl2_members_form + 2-adic cross-level argument.)
   We build it as a FUNCTION (per a, d) rather than a packaged thm.
   =========================================================================== *)
(* dl2_members_form is varified with the SAME var-name scheme : Forall over e, var a (a_mf? no:
   it was proven with induction var a_mf, predicate Forall e).  Check: the conclusion is
   bodyA a_mf = Forall e. lmem e (dl2 a_mf D) ==> formGoal a_mf e ; vars D, a_mf. *)
fun dl2MembersFormE (aT, DT, eT) hmem =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtEC
                 [(("D",0), ctermEC DT),(("a_mf",0), ctermEC aT)] dl2_members_form)
    val eBody = Term.lambda (Free("e",natT))
          (mkImp (lmem (Free("e",natT)) (dl2 aT DT))
             (mkEx (Term.lambda (Free("j",natT))
                (mkEx (Term.lambda (Free("d",natT))
                   (mkConj (le (Free("j",natT)) aT)
                      (mkConj (lmem (Free("d",natT)) DT)
                              (oeq (Free("e",natT)) (mult (p2 (Free("j",natT))) (Free("d",natT)))))))))))
    val atE = allE_E (eBody, eT) inst
  in mp_E (lmem eT (dl2 aT DT),
        mkEx (Term.lambda (Free("j",natT))
           (mkEx (Term.lambda (Free("d",natT))
              (mkConj (le (Free("j",natT)) aT)
                 (mkConj (lmem (Free("d",natT)) DT)
                         (oeq eT (mult (p2 (Free("j",natT))) (Free("d",natT))))))))) ) atE hmem
  end;
val () = out "EE_DL2_MEMBERSFORM_INST_OK\n";

(* lnodup cons wrappers on ctxtEC *)
fun lnodupConsBwdE (xT, tT) hConj =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtEC
      [(("x",0), ctermEC xT),(("t",0), ctermEC tT)] lnodup_cons_bwd_vE)) hConj;
fun lnodupConsFwdE (xT, tT) hnd =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtEC
      [(("x",0), ctermEC xT),(("t",0), ctermEC tT)] lnodup_cons_fwd_vE)) hnd;
val lnodup_nil_E = lnodup_nil_vE;

(* ===========================================================================
   NOTMEM_CROSS (function) : per (aT, dT) with hMemDvd : !!d. lmem d D ==> dvd d m,
   hOddm, hMemd : lmem d D, returns  neg(lmem (mult (p2 (Suc a)) d)(dl2 a D)).
     If 2^(Suc a)*d in dl2 a D then = 2^j*d', j<=a, d' in D.
     d,d' odd (divide m).  Suc a = j + Suc w (j<=a).  2^(Suc a) = 2^j*2^(Suc w).
     2^j*2^(Suc w)*d = 2^j*d' -> cancel 2^j -> 2^(Suc w)*d = d' -> 2 | d' (2|2^(Suc w)) -> contra.
   =========================================================================== *)
fun notmem_cross (aT, DT, mT, dT) hOddm hMemDvdAll hMemd =
  let
    val A2s = p2 (suc aT)
    val target = mult A2s dT
    val hmem = Thm.assume (ctermEC (jT (lmem target (dl2 aT DT))))
    val formTh = dl2MembersFormE (aT, DT, target) hmem   (* Ex j d'. le j a /\ lmem d' D /\ A2s*d = 2^j*d' *)
    val Pj = Term.lambda (Free("j",natT))
               (mkEx (Term.lambda (Free("dq",natT))
                  (mkConj (le (Free("j",natT)) aT)
                     (mkConj (lmem (Free("dq",natT)) DT)
                             (oeq target (mult (p2 (Free("j",natT))) (Free("dq",natT))))))))
    val ff =
      exE_E (Pj, oFalseC) formTh
        (fn (jF, hj) =>
           let
             val Pd = Term.lambda (Free("dq",natT))
                        (mkConj (le jF aT)
                           (mkConj (lmem (Free("dq",natT)) DT)
                                   (oeq target (mult (p2 jF) (Free("dq",natT))))))
           in exE_E (Pd, oFalseC) hj
                (fn (dqF, hd) =>
                   let
                     val hle  = conjunct1_E (le jF aT, mkConj (lmem dqF DT)(oeq target (mult (p2 jF) dqF))) hd  (* le j a *)
                     val rest = conjunct2_E (le jF aT, mkConj (lmem dqF DT)(oeq target (mult (p2 jF) dqF))) hd
                     val hmemdq = conjunct1_E (lmem dqF DT, oeq target (mult (p2 jF) dqF)) rest  (* lmem d' D *)
                     val heq    = conjunct2_E (lmem dqF DT, oeq target (mult (p2 jF) dqF)) rest  (* A2s*d = 2^j*d' *)
                     (* d' odd : d'|m, m odd *)
                     val dvd_dq_m = Thm.implies_elim (Thm.forall_elim (ctermEC dqF) hMemDvdAll) hmemdq  (* META all+impl *)
                     val odd_dq = odd_of_dvdE (dqF, mT) hOddm dvd_dq_m   (* neg(dvd 2 d') *)
                     (* le j a -> a = j + w *)
                     val Pw = Abs("w", natT, oeq aT (add jF (Bound 0)))
                   in exE_E (Pw, oFalseC) hle
                        (fn (wF, hw) =>
                           let
                             (* Suc a = j + Suc w :  Suc a = Suc(j+w) [Suc cong hw] = j + Suc w [add_Suc_right sym] *)
                             val saw = ScongE (aT, add jF wF) hw   (* Suc a = Suc(j+w) *)
                             val addSR = beta_norm (Drule.infer_instantiate ctxtEC
                                   [(("m",0), ctermEC jF),(("n",0), ctermEC wF)] (upE (varify (up add_Suc_right))))  (* add j (Suc w) = Suc(add j w) *)
                             val sa_jSw = trans2E (saw, symmE addSR)   (* Suc a = add j (Suc w) *)
                             (* 2^(Suc a) = 2^(j + Suc w) = 2^j * 2^(Suc w) *)
                             val pSa_eq = let val Pe = Term.lambda (Free("ze",natT)) (oeq (p2 (suc aT))(p2 (Free("ze",natT))))
                                          in substPredE (Pe, suc aT, add jF (suc wF)) sa_jSw (reflE (p2 (suc aT))) end  (* 2^(Suc a) = 2^(j+Suc w) *)
                             val pSa_prod = trans2E (pSa_eq, powAddE (two, jF, suc wF))   (* 2^(Suc a) = 2^j * 2^(Suc w) *)
                             (* target = A2s*d = (2^j*2^(Suc w))*d = 2^j*(2^(Suc w)*d) *)
                             val tg1 = mult_cong_lE (A2s, mult (p2 jF)(p2 (suc wF)), dT) pSa_prod  (* A2s*d = (2^j*2^(Suc w))*d *)
                             val tg2 = multassocE (p2 jF, p2 (suc wF), dT)                          (* (2^j*2^(Suc w))*d = 2^j*(2^(Suc w)*d) *)
                             val tgt_form = trans2E (tg1, tg2)   (* target = 2^j*(2^(Suc w)*d) *)
                             (* 2^j*(2^(Suc w)*d) = 2^j*d' [from heq sym + tgt_form] *)
                             val lhs_rhs = trans2E (symmE tgt_form, heq)   (* 2^j*(2^(Suc w)*d) = 2^j*d' *)
                             (* cancel 2^j : 2^(Suc w)*d = d' *)
                             val lt0p2j = lt0p2E jF
                             val cancel = multLeftCancelE (p2 jF, mult (p2 (suc wF)) dT, dqF) lt0p2j lhs_rhs  (* 2^(Suc w)*d = d' *)
                             (* 2 | 2^(Suc w)*d : 2 | 2^(Suc w) [two_dvd_pow2_suc] -> 2 | 2^(Suc w)*d [dvd_mult] *)
                             val d2_pSw = two_dvd_pow2_sucE wF   (* dvd 2 (2^(Suc w)) *)
                             (* dvd 2 (2^(Suc w)*d) : 2^(Suc w) = 2*k -> 2^(Suc w)*d = 2*(k*d) *)
                             val d2_prod = dvd_destE (two, p2 (suc wF), dvd two (mult (p2 (suc wF)) dT)) d2_pSw
                                             (fn (kF, hk) =>   (* hk : 2^(Suc w) = 2*k *)
                                                let val e1 = mult_cong_lE (p2 (suc wF), mult two kF, dT) hk   (* 2^(Suc w)*d = (2*k)*d *)
                                                    val e2 = multassocE (two, kF, dT)                        (* (2*k)*d = 2*(k*d) *)
                                                    val eqn = trans2E (e1, e2)                               (* 2^(Suc w)*d = 2*(k*d) *)
                                                in dvd_introE (two, mult (p2 (suc wF)) dT, mult kF dT) eqn end)
                             (* dvd 2 d' : rewrite 2^(Suc w)*d -> d' via cancel *)
                             val d2_dq = dvd_cong_targetE (two, mult (p2 (suc wF)) dT, dqF) cancel d2_prod  (* dvd 2 d' *)
                             val ff = mp_E (dvd two dqF, oFalseC) odd_dq d2_dq
                           in ff end)
                   end)
           end)
  in impI_E (lmem target (dl2 aT DT), oFalseC) ff end;   (* neg(lmem (A2s*d)(dl2 a D)) : OBJECT Imp *)
val () = out "EE_DL2_NOTMEM_CROSS_OK\n";

(* ===========================================================================
   LNODUP_LMAP2 : lt 0 c ==> lnodup D ==> lnodup (lmap2 c D).  Induction on D.
   =========================================================================== *)
val lnodup_lmap2 =
  let
    val cF = Free("c", natT)
    val hPosC = Thm.assume (ctermEC (jT (lt ZeroC cF)))
    fun body Lt = mkImp (lnodup Lt) (lnodup (lmap2 cF Lt))
    val zL = Free("zL", natlistT)
    val Qpred = Term.lambda zL (body zL)
    val kIndL = Free("L", natlistT)
    val ind = list_induct_atE (Qpred, kIndL)
    val base =
      let
        val hnd = Thm.assume (ctermEC (jT (lnodup lnilC)))
        (* lmap2 c lnil = lnil ; lnodup lnil ; transport. *)
        val mleq = lmap2NilE cF   (* leq (lmap2 c lnil) lnil *)
        val res = lnodup_leqE (lnilC, lmap2 cF lnilC) (sym_leqE (lmap2 cF lnilC, lnilC) mleq) lnodup_nil_E
      in impI_E (lnodup lnilC, lnodup (lmap2 cF lnilC)) res end
    val xF = Free("x", natT); val tF = Free("t", natlistT)
    val IH = Thm.assume (ctermEC (jT (body tF)))
    val stepconcl =
      let
        val hnd = Thm.assume (ctermEC (jT (lnodup (lcons xF tF))))
        val ndConj = lnodupConsFwdE (xF, tF) hnd   (* neg(lmem x t) /\ lnodup t *)
        val negxt = conjunct1_E (neg (lmem xF tF), lnodup tF) ndConj   (* neg(lmem x t) *)
        val ndt   = conjunct2_E (neg (lmem xF tF), lnodup tF) ndConj   (* lnodup t *)
        val ndmt  = mp_E (lnodup tF, lnodup (lmap2 cF tF)) IH ndt   (* lnodup (lmap2 c t) *)
        (* neg(lmem (c*x)(lmap2 c t)) : if c*x in lmap2 c t -> Ex d. lmem d t /\ c*x = c*d -> cancel c -> x=d -> lmem x t contra. *)
        val negcx =
          let
            val hmem = Thm.assume (ctermEC (jT (lmem (mult cF xF)(lmap2 cF tF))))
            val exwit = mkEx (Term.lambda (Free("d",natT))
                          (mkConj (lmem (Free("d",natT)) tF)(oeq (mult cF xF)(mult cF (Free("d",natT))))))
            val exT = mp_E (lmem (mult cF xF)(lmap2 cF tF), exwit)
                        (beta_norm (Drule.infer_instantiate ctxtEC
                           [(("y",0), ctermEC (mult cF xF)),(("c",0), ctermEC cF),(("L",0), ctermEC tF)] mem_map2))
                        hmem   (* Ex d. lmem d t /\ c*x = c*d *)
            val Pt = Term.lambda (Free("d",natT))
                       (mkConj (lmem (Free("d",natT)) tF)(oeq (mult cF xF)(mult cF (Free("d",natT)))))
            val ff = exE_E (Pt, oFalseC) exT
                       (fn (dF, hd) =>
                          let
                            val hmemd = conjunct1_E (lmem dF tF, oeq (mult cF xF)(mult cF dF)) hd  (* lmem d t *)
                            val heq   = conjunct2_E (lmem dF tF, oeq (mult cF xF)(mult cF dF)) hd  (* c*x = c*d *)
                            val xeqd  = multLeftCancelE (cF, xF, dF) hPosC heq   (* x = d *)
                            (* lmem x t : rewrite d -> x in lmem d t via sym xeqd *)
                            val Pm = Term.lambda (Free("zm",natT)) (lmem (Free("zm",natT)) tF)
                            val memxt = substPredE (Pm, dF, xF) (symmE xeqd) hmemd  (* lmem x t *)
                          in mp_E (lmem xF tF, oFalseC) negxt memxt end)
          in impI_E (lmem (mult cF xF)(lmap2 cF tF), oFalseC) ff end
        (* lnodup (lcons (c*x)(lmap2 c t)) *)
        val ndcons = lnodupConsBwdE (mult cF xF, lmap2 cF tF)
                       (conjI_E (neg (lmem (mult cF xF)(lmap2 cF tF)), lnodup (lmap2 cF tF)) negcx ndmt)
        (* transport to lnodup (lmap2 c (lcons x t)) via sym(lmap2ConsE) *)
        val mleq = lmap2ConsE (cF, xF, tF)   (* leq (lmap2 c (lcons x t))(lcons (c*x)(lmap2 c t)) *)
        val res = lnodup_leqE (lcons (mult cF xF)(lmap2 cF tF), lmap2 cF (lcons xF tF))
                    (sym_leqE (lmap2 cF (lcons xF tF), lcons (mult cF xF)(lmap2 cF tF)) mleq) ndcons
      in impI_E (lnodup (lcons xF tF), lnodup (lmap2 cF (lcons xF tF))) res end
    val step1 = Thm.forall_intr (ctermEC xF)
                  (Thm.forall_intr (ctermEC tF)
                    (Thm.implies_intr (ctermEC (jT (body tF))) stepconcl))
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
    val d1 = Thm.implies_intr (ctermEC (jT (lt ZeroC cF))) r2
  in varify d1 end;
val () = out "LNODUP_LMAP2_BUILT\n";

(* ===========================================================================
   LNODUP_APPEND : lnodup A ==> lnodup B
       ==> (!!y. lmem y A ==> neg(lmem y B))
       ==> lnodup (lappend A B).   Induction on A.
   =========================================================================== *)
val lnodup_append =
  let
    val BF = Free("B", natlistT)
    val hndB = Thm.assume (ctermEC (jT (lnodup BF)))
    fun disjAbs At = Term.lambda (Free("y",natT)) (mkImp (lmem (Free("y",natT)) At)(neg (lmem (Free("y",natT)) BF)))
    fun body At = mkImp (lnodup At) (lnodup (lappend At BF))   (* the disjointness hyp is added per-call as a meta hyp *)
    (* We carry the disjointness as an explicit object-Forall meta-hyp parameterised by A,
       so the IH-predicate is over A : we make the predicate  P A := (Forall y. y in A -> ~ y in B) -> lnodup A -> lnodup (lappend A B). *)
    fun fullBody At = mkImp (mkForall (disjAbs At)) (mkImp (lnodup At) (lnodup (lappend At BF)))
    val zL = Free("zL", natlistT)
    val Qpred = Term.lambda zL (fullBody zL)
    val kIndL = Free("A", natlistT)
    val ind = list_induct_atE (Qpred, kIndL)
    val base =
      let
        val hdis = Thm.assume (ctermEC (jT (mkForall (disjAbs lnilC))))
        val hnd  = Thm.assume (ctermEC (jT (lnodup lnilC)))
        (* lappend lnil B = B ; lnodup B ; transport *)
        val aleq = lappendNilE BF   (* leq (lappend lnil B) B *)
        val res = lnodup_leqE (BF, lappend lnilC BF) (sym_leqE (lappend lnilC BF, BF) aleq) hndB
      in impI_E (mkForall (disjAbs lnilC), mkImp (lnodup lnilC)(lnodup (lappend lnilC BF)))
           (impI_E (lnodup lnilC, lnodup (lappend lnilC BF)) res) end
    val xF = Free("x", natT); val tF = Free("t", natlistT)
    val IH = Thm.assume (ctermEC (jT (fullBody tF)))
    val stepconcl =
      let
        val hdis = Thm.assume (ctermEC (jT (mkForall (disjAbs (lcons xF tF)))))   (* !!y. y in (lcons x t) -> ~y in B *)
        val hnd  = Thm.assume (ctermEC (jT (lnodup (lcons xF tF))))
        val ndConj = lnodupConsFwdE (xF, tF) hnd   (* neg(lmem x t) /\ lnodup t *)
        val negxt = conjunct1_E (neg (lmem xF tF), lnodup tF) ndConj
        val ndt   = conjunct2_E (neg (lmem xF tF), lnodup tF) ndConj
        (* disjointness for t : !!y. y in t -> ~y in B  (from hdis, since y in t -> y in lcons x t) *)
        val hdis_t =
          let
            fun perY yF =
              let val hyt = Thm.assume (ctermEC (jT (lmem yF tF)))
                  (* y in lcons x t *)
                  val ylc = Thm.implies_elim (lmemConsBwdE (yF, xF, tF)) (disjI2_E (oeq yF xF, lmem yF tF) hyt)
                  val atY = allE_E (disjAbs (lcons xF tF), yF) hdis   (* y in lcons x t -> ~y in B *)
                  val nyB = mp_E (lmem yF (lcons xF tF), neg (lmem yF BF)) atY ylc
              in impI_E (lmem yF tF, neg (lmem yF BF)) nyB end
            val yFb = Free("y_lnd", natT)
          in allI_E (disjAbs tF) (Thm.forall_intr (ctermEC yFb) (perY yFb)) end
        (* IH : disjointness t -> lnodup t -> lnodup (lappend t B) *)
        val ihD = mp_E (mkForall (disjAbs tF), mkImp (lnodup tF)(lnodup (lappend tF BF))) IH hdis_t
        val ndtB = mp_E (lnodup tF, lnodup (lappend tF BF)) ihD ndt   (* lnodup (lappend t B) *)
        (* neg(lmem x (lappend t B)) : mem_append -> Disj(lmem x t)(lmem x B) ; both contra. *)
        val negx_tB =
          let
            val hm = Thm.assume (ctermEC (jT (lmem xF (lappend tF BF))))
            val dj = mp_E (lmem xF (lappend tF BF), mkDisj (lmem xF tF)(lmem xF BF))
                       (beta_norm (Drule.infer_instantiate ctxtEC
                          [(("y",0), ctermEC xF),(("A",0), ctermEC tF),(("B",0), ctermEC BF)] mem_append))
                       hm
            val caseT = let val h = Thm.assume (ctermEC (jT (lmem xF tF)))
                        in Thm.implies_intr (ctermEC (jT (lmem xF tF))) (mp_E (lmem xF tF, oFalseC) negxt h) end
            val caseB = let val h = Thm.assume (ctermEC (jT (lmem xF BF)))
                            (* x in lcons x t -> ~x in B *)
                            val xlc = Thm.implies_elim (lmemConsBwdE (xF, xF, tF)) (disjI1_E (oeq xF xF, lmem xF tF) (reflE xF))
                            val atX = allE_E (disjAbs (lcons xF tF), xF) hdis
                            val nxB = mp_E (lmem xF (lcons xF tF), neg (lmem xF BF)) atX xlc
                        in Thm.implies_intr (ctermEC (jT (lmem xF BF))) (mp_E (lmem xF BF, oFalseC) nxB h) end
            val ff = disjE_E (lmem xF tF, lmem xF BF, oFalseC) dj caseT caseB
          in impI_E (lmem xF (lappend tF BF), oFalseC) ff end
        (* lnodup (lcons x (lappend t B)) *)
        val ndcons = lnodupConsBwdE (xF, lappend tF BF)
                       (conjI_E (neg (lmem xF (lappend tF BF)), lnodup (lappend tF BF)) negx_tB ndtB)
        (* transport to lnodup (lappend (lcons x t) B) via sym(lappendConsE) *)
        val aleq = lappendConsE (xF, tF, BF)   (* leq (lappend (lcons x t) B)(lcons x (lappend t B)) *)
        val res = lnodup_leqE (lcons xF (lappend tF BF), lappend (lcons xF tF) BF)
                    (sym_leqE (lappend (lcons xF tF) BF, lcons xF (lappend tF BF)) aleq) ndcons
      in impI_E (mkForall (disjAbs (lcons xF tF)), mkImp (lnodup (lcons xF tF))(lnodup (lappend (lcons xF tF) BF)))
           (impI_E (lnodup (lcons xF tF), lnodup (lappend (lcons xF tF) BF)) res) end
    val step1 = Thm.forall_intr (ctermEC xF)
                  (Thm.forall_intr (ctermEC tF)
                    (Thm.implies_intr (ctermEC (jT (fullBody tF))) stepconcl))
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1            (* fullBody A, under hndB *)
    val d1 = Thm.implies_intr (ctermEC (jT (lnodup BF))) r2
  in varify d1 end;
val () = out "LNODUP_APPEND_BUILT\n";

(* instantiators for lnodup_lmap2 / lnodup_append *)
fun lnodupLmap2E (cT, LT) hPosC hnd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
                   [(("c",0), ctermEC cT),(("L",0), ctermEC LT)] lnodup_lmap2)
      val objImp = Thm.implies_elim inst hPosC   (* jT(Imp(lnodup L)(lnodup(lmap2 c L))) *)
  in mp_E (lnodup LT, lnodup (lmap2 cT LT)) objImp hnd end;
fun lnodupAppendE (AT, BT) hndA hndB hdisj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtEC
                   [(("A",0), ctermEC AT),(("B",0), ctermEC BT)] lnodup_append)
      val objImp = Thm.implies_elim inst hndB   (* jT(Imp(Forall...)(Imp(lnodup A)(lnodup(lappend A B)))) *)
      val disjAbsA = Term.lambda (Free("y",natT)) (mkImp (lmem (Free("y",natT)) AT)(neg (lmem (Free("y",natT)) BT)))
      val s1 = mp_E (mkForall disjAbsA, mkImp (lnodup AT)(lnodup (lappend AT BT))) objImp hdisj
  in mp_E (lnodup AT, lnodup (lappend AT BT)) s1 hndA end;

(* ===========================================================================
   DL2_LNODUP :
     neg (dvd 2 m)
     ==> (!!d. lmem d D ==> dvd d m)        [members divide m, => members odd]
     ==> lnodup D
     ==> lnodup (dl2 a D).   Induction on a.
   =========================================================================== *)
val dl2_lnodup =
  let
    val aF0 = Free("a", natT); val mF = Free("m", natT); val DF = Free("D", natlistT)
    val hOddm = Thm.assume (ctermEC (jT (neg (dvd two mF))))
    val dMeta = Free("d_md", natT)
    val hMemDvdProp = Logic.all dMeta (Logic.mk_implies (jT (lmem dMeta DF), jT (dvd dMeta mF)))
    val hMemDvdAll = Thm.assume (ctermEC hMemDvdProp)
    val hndD = Thm.assume (ctermEC (jT (lnodup DF)))
    fun bodyA at = lnodup (dl2 at DF)
    val zV = Free("z_ld", natT)
    val Qpred = Term.lambda zV (bodyA zV)
    val kIndA = Free("a_ld", natT)
    val ind = nat_induct_atE (Qpred, kIndA)
    (* base a=0 : dl2 0 D = D ; lnodup D ; transport *)
    val base =
      let
        val dleq = dl20E DF   (* leq (dl2 0 D) D *)
        val res = lnodup_leqE (DF, dl2 ZeroC DF) (sym_leqE (dl2 ZeroC DF, DF) dleq) hndD
      in res end
    (* step a -> Suc a *)
    val xF = Free("x_ld", natT)
    val IH = Thm.assume (ctermEC (jT (bodyA xF)))   (* lnodup (dl2 x D) *)
    val stepconcl =
      let
        val A2s = p2 (suc xF)
        (* lnodup (lmap2 A2s D) : A2s > 0, lnodup D *)
        val lt0A2s = lt0p2E (suc xF)   (* lt 0 (p2 (Suc x)) *)
        val ndMap = lnodupLmap2E (A2s, DF) lt0A2s hndD   (* lnodup (lmap2 A2s D) *)
        (* disjointness : !!y. y in lmap2 A2s D ==> ~y in dl2 x D *)
        val hdisj =
          let
            fun perY yF =
              let
                val hmem = Thm.assume (ctermEC (jT (lmem yF (lmap2 A2s DF))))
                (* mem_map2 : Ex d. lmem d D /\ y = A2s*d *)
                val exwit = mkEx (Term.lambda (Free("d",natT))
                              (mkConj (lmem (Free("d",natT)) DF)(oeq yF (mult A2s (Free("d",natT))))))
                val exT = mp_E (lmem yF (lmap2 A2s DF), exwit)
                            (beta_norm (Drule.infer_instantiate ctxtEC
                               [(("y",0), ctermEC yF),(("c",0), ctermEC A2s),(("L",0), ctermEC DF)] mem_map2))
                            hmem
                val Pt = Term.lambda (Free("d",natT))
                           (mkConj (lmem (Free("d",natT)) DF)(oeq yF (mult A2s (Free("d",natT)))))
                val negG = exE_E (Pt, neg (lmem yF (dl2 xF DF))) exT
                  (fn (dF, hd) =>
                     let
                       val hmemd = conjunct1_E (lmem dF DF, oeq yF (mult A2s dF)) hd   (* lmem d D *)
                       val heq   = conjunct2_E (lmem dF DF, oeq yF (mult A2s dF)) hd   (* y = A2s*d *)
                       (* notmem_cross : neg(lmem (A2s*d)(dl2 x D)) *)
                       val ncross = notmem_cross (xF, DF, mF, dF) hOddm hMemDvdAll hmemd  (* neg(lmem (mult (p2(Suc x)) d)(dl2 x D)) *)
                       (* rewrite A2s*d -> y via sym heq *)
                       val Pm = Term.lambda (Free("zm",natT)) (neg (lmem (Free("zm",natT)) (dl2 xF DF)))
                       val res = substPredE (Pm, mult A2s dF, yF) (symmE heq) ncross   (* neg(lmem y (dl2 x D)) *)
                     in res end)
              in impI_E (lmem yF (lmap2 A2s DF), neg (lmem yF (dl2 xF DF))) negG end
            val yFb = Free("y_dld", natT)
            val disjAbsM = Term.lambda (Free("y",natT)) (mkImp (lmem (Free("y",natT)) (lmap2 A2s DF))(neg (lmem (Free("y",natT)) (dl2 xF DF))))
          in allI_E disjAbsM (Thm.forall_intr (ctermEC yFb) (perY yFb)) end
        (* lnodup (lappend (lmap2 A2s D)(dl2 x D)) *)
        val ndApp = lnodupAppendE (lmap2 A2s DF, dl2 xF DF) ndMap IH hdisj
        (* transport to lnodup (dl2 (Suc x) D) via sym(dl2SucE) *)
        val dleq = dl2SucE (xF, DF)   (* leq (dl2 (Suc x) D)(lappend (lmap2 A2s D)(dl2 x D)) *)
        val res = lnodup_leqE (lappend (lmap2 A2s DF)(dl2 xF DF), dl2 (suc xF) DF)
                    (sym_leqE (dl2 (suc xF) DF, lappend (lmap2 A2s DF)(dl2 xF DF)) dleq) ndApp
      in res end
    val step1 = Thm.forall_intr (ctermEC xF) (Thm.implies_intr (ctermEC (jT (bodyA xF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1            (* lnodup (dl2 a D), under hyps *)
    val d_nd = Thm.implies_intr (ctermEC (jT (lnodup DF))) r2
    val d_md = Thm.implies_intr (ctermEC hMemDvdProp) d_nd
    val d_odd = Thm.implies_intr (ctermEC (jT (neg (dvd two mF)))) d_md
  in varify d_odd end;
val () = out ("DL2_LNODUP_HYPS = " ^ Int.toString (length (Thm.hyps_of dl2_lnodup)) ^ "\n");
val () = out "DL2_LNODUP_BUILT\n";

(* ===========================================================================
   VALIDATION : dl2_lnodup 0-hyp + aconv intended.
   =========================================================================== *)
val aVln = Var(("a_ld",0), natT); val mVln = Var(("m",0), natT); val DVln = Var(("D",0), natlistT)
val dMln = Free("d_md", natT)
val i_dl2_lnodup =
  Logic.mk_implies (jT (neg (dvd two mVln)),
    Logic.mk_implies (Logic.all dMln (Logic.mk_implies (jT (lmem dMln DVln), jT (dvd dMln mVln))),
      Logic.mk_implies (jT (lnodup DVln), jT (lnodup (dl2 aVln DVln)))));
val nh_ln = length (Thm.hyps_of dl2_lnodup);
val ac_ln = (Thm.prop_of dl2_lnodup) aconv i_dl2_lnodup;
val () = out ("DL2_LNODUP hyps=" ^ Int.toString nh_ln ^ " aconv=" ^ Bool.toString ac_ln ^ "\n");
val () =
  if nh_ln = 0 andalso ac_ln then out "DL2_LNODUP_OK\n"
  else (out ("  got      = " ^ Syntax.string_of_term ctxtEC (Thm.prop_of dl2_lnodup) ^ "\n"
             ^ "  intended = " ^ Syntax.string_of_term ctxtEC i_dl2_lnodup ^ "\n");
        out "DL2_LNODUP_BAD\n");

(* SOUNDNESS PROBE : dl2_lnodup genuinely needs the odd(m) hypothesis. *)
val s_ln_needs_odd =
  not ((Thm.prop_of dl2_lnodup) aconv
       (Logic.mk_implies (Logic.all dMln (Logic.mk_implies (jT (lmem dMln DVln), jT (dvd dMln mVln))),
          Logic.mk_implies (jT (lnodup DVln), jT (lnodup (dl2 aVln DVln))))));
val () = if s_ln_needs_odd then out "PROBE_OK dl2_lnodup needs the odd(m) hypothesis\n"
         else out "PROBE_FAIL dl2_lnodup dropped the odd hypothesis!\n";
(* PROBE : needs lnodup D. *)
val s_ln_needs_ndD =
  not ((Thm.prop_of dl2_lnodup) aconv
       (Logic.mk_implies (jT (neg (dvd two mVln)),
          Logic.mk_implies (Logic.all dMln (Logic.mk_implies (jT (lmem dMln DVln), jT (dvd dMln mVln))),
            jT (lnodup (dl2 aVln DVln))))));
val () = if s_ln_needs_ndD then out "PROBE_OK dl2_lnodup needs lnodup D\n"
         else out "PROBE_FAIL dl2_lnodup dropped lnodup D!\n";

val () = out "EE_DL2_LNODUP_SECTION_DONE\n";
val () = out "EE_DL2_ALL_DONE\n";
