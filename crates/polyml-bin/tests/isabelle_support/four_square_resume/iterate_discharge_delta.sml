(* ============================================================================
   ITERATE + DISCHARGE  —  Lagrange four-square reduction to the descent step.
   ============================================================================
   Resume delta for four_square_resume/.  Run on the warm checkpoint
   /tmp/l4_foursq_star (which carries: base + four_sq_mult + lagrange_assembly
   + descent_residue + star_v + primemult_thm, all in the exported heap), with
   the FIRST line `val () = restore_l4_context ();`.

       POLYML_HEAP_BYTES=8000000000 POLYML_GC_THRESHOLD=88 \
         ./target/release/poly run --max-steps 1000000000000 \
         /tmp/l4_foursq_star < this_delta.sml

   This chunk is LOW RAM (pure logical assembly over EXISTING lemmas; NO divide
   leaf is re-run).  It is MECHANICAL given the strict descent step.

   ----------------------------------------------------------------------------
   THEOREM (this delta, CONDITIONAL on the descent step):

     iterate_discharge :
       (  !!p m. prime2 p ==> 1<m ==> m<p ==> four_sq(m*p)
                  ==> Ex r. 0<r /\ r<m /\ four_sq(r*p)  )           [= descent_step]
       ==> !!n. four_sq n

   i.e. ASSUMING the strict Euler descent step (one m*p -> r*p step with r<m),
   EVERY natural number is a sum of four squares.  This REDUCES the full
   four-square theorem to the single descent step.

   conditional_on : the descent step (named `descent_step_prop` below) — the
   ONLY open premise; iterate_discharge itself is 0-hyp (the descent step is the
   antecedent of a meta-implication, not a free hypothesis).

   ----------------------------------------------------------------------------
   PROOF STRUCTURE (all genuine LCF kernel inference; 0 add_axiom_global):

   1. n_parity        : !!n. (Ex k. n = k+k) \/ (Ex k. n = Suc(k+k))   [nat induction]
   2. even_prime_is_two : prime2 p ==> (Ex k. p = k+k) ==> p = 2       [2|p -> p=2]
   3. fsq2            : four_sq 2   (witness 1,1,0,0)                   [0-hyp]
   4. build_prime_is_fsq p hPrime  : four_sq p (open hyp: descent_step) by
        STRONG INDUCTION on m of the object predicate
          Pdesc m := Imp (0<m) (Imp (m<p) (Imp (four_sq(m*p)) (four_sq p)))
        descending m*p -> r*p (r<m) via the assumed descent_step down to m=1
        (mult 1 p = p), then a parity case-split seeds it:
          - even prime -> p=2 -> four_sq 2 rewritten;
          - odd prime  -> primemult_thm gives 0<m'<p with four_sq(m'*p),
            then Pdesc m' yields four_sq p.
   5. prime_is_fsq    : !!p. prime2 p ==> four_sq p   (open hyp: descent_step)
   6. discharge the PROVEN lagrange_assembly:
        lagrange_assembly : (!!p. prime2 p ==> four_sq p) ==> (!!n. four_sq n)
        ==> !!n. four_sq n  (open hyp: descent_step), then implies_intr the
        descent step.

   NB base-merge: `primemult_thm` lives on thyB which EXTENDS thyGR (where the
   rest of the lemmas live).  So the odd-case instantiation of primemult is done
   on ctxtB/ctermB; the ctxtGR-built hyps compose up to thyB automatically.
   ============================================================================ *)
val () = restore_l4_context ();
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
