(* ============================================================================
   THE CENTRAL BINOMIAL COEFFICIENT IDENTITY in Isabelle/Pure on the polyml-rs
   interpreter.  (test: isabelle_central_binomial.rs)
   ----------------------------------------------------------------------------
   Two theorems on binomial coefficients, each 0-hyp by genuine kernel inference:

     binom_symmetry   : |- !n k. le k n ==> binom n k = binom n (sub n k)
                        C(n,k) = C(n, n-k) for k <= n, by nat induction (k object-
                        universally quantified so the IH applies at k and Suc k) +
                        Pascal + a sub case-split.
     central_binomial : |- sumf (%k. binom n k * binom n k) n = binom (add n n) n
                        sum_{k=0}^n C(n,k)^2 = C(2n,n) -- the central binomial
                        coefficient. A COROLLARY of VANDERMONDE (instantiated at
                        m=n,k=n: sum_j C(n,j)C(n,n-j) = C(2n,n)) with the summand
                        rewritten by binom_symmetry under sum_cong.

   Built on the combinatorial-identities development (isabelle_combinatorics.sml,
   which carries Vandermonde) over the binomial-theorem base, spliced in by
   common::with_combinatorics. Each carries a soundness probe. Proved by a
   2-phase ultracode fleet (wf_f6d7e8db-f16); re-verified end-to-end by hand.
   ============================================================================ *)

(* ============================================================================
   PHASE 1 : BINOMIAL SYMMETRY  (seat sym0)
     binom_symmetry : !n. !k. le k n ==> oeq (binom n k) (binom n (sub n k))
   ============================================================================ *)
val () = out "BINOM_SYM_BEGIN\n";

(* ground instances of Suc_inj on ctxtSub *)
fun Suc_inj_atS2 (uT,vT) = beta_norm (Drule.infer_instantiate ctxtSub
      [(("a",0), ctermSub uT),(("b",0), ctermSub vT)] Suc_inj_v);

(* binom_n_n instantiator on ctxtSub : oeq (binom t t)(Suc 0) *)
val binom_n_n_vS2 = varify binom_n_n;
fun binom_n_n_at t = beta_norm (Drule.infer_instantiate ctxtSub
      [(("n",0), ctermSub t)] binom_n_n_vS2);

(* ----------------------------------------------------------------------------
   le_Suc_Suc_rev : le (Suc a) (Suc b) ==> le a b
   ---------------------------------------------------------------------------- *)
val le_Suc_Suc_rev =
  let
    val aF = Free("a", natT); val bF = Free("b", natT);
    val hyp = jT (le (suc aF) (suc bF));
    val Habs = Abs("p", natT, oeq (suc bF) (add (suc aF) (Bound 0)));
    val goalC = le aF bF;
    fun bodyFn pF hpThm =
      let
        val asuc = addSucS2_at (aF, pF);                        (* add (Suc a) p = Suc (add a p) *)
        val chain = oeq_trans OF [hpThm, asuc];                 (* oeq (Suc b)(Suc (add a p)) *)
        val binj  = Suc_inj_atS2 (bF, add aF pF) OF [chain];    (* oeq b (add a p) *)
      in le_introS2 (aF, bF, pF) binj end;
    val elimd = exE_elimS2 (Habs, goalC) (Thm.assume (ctermSub hyp)) "p" bodyFn;
    val dis = Thm.implies_intr (ctermSub hyp) elimd;
  in varify dis end;

val aVs = Var (("a",0), natT); val bVs = Var (("b",0), natT);
val i_le_Suc_Suc_rev = Logic.mk_implies (jT (le (suc aVs) (suc bVs)), jT (le aVs bVs));
val r_le_Suc_Suc_rev = checkSub ("le_Suc_Suc_rev", le_Suc_Suc_rev, i_le_Suc_Suc_rev);

val le_Suc_Suc_rev_vS2 = varify le_Suc_Suc_rev;
fun le_SS_rev_at (aT,bT) h = Thm.implies_elim
      (beta_norm (Drule.infer_instantiate ctxtSub
         [(("a",0), ctermSub aT),(("b",0), ctermSub bT)] le_Suc_Suc_rev_vS2)) h;

(* ============================================================================
   binom_symmetry : !n. !k. le k n ==> oeq (binom n k)(binom n (sub n k))
   induction on n, k object-universally quantified (object Forall of object Imp).
   ============================================================================ *)
val binom_symmetry =
  let
    val kFV = Free("k", natT);
    fun obody nT kT = mkImp (le kT nT) (oeq (binom nT kT) (binom nT (sub nT kT)));
    fun predAbs nT  = Term.lambda kFV (obody nT kFV);
    fun predForall nT = mkForall (predAbs nT);
    val zV = Free("z", natT);
    val Qpred = Term.lambda zV (predForall zV);
    val nIndV = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nIndV);

    (* ====================================================================
       BASE n = 0 : forall k. le k 0 --> binom 0 k = binom 0 (sub 0 k)
       ==================================================================== *)
    val base =
      let
        val kF = Free("k", natT)
        val anteO = le kF ZeroC
        val conO  = oeq (binom ZeroC kF) (binom ZeroC (sub ZeroC kF))
        val hAnt  = Thm.assume (ctermSub (jT anteO))
        val Habs  = Abs("p", natT, oeq ZeroC (add kF (Bound 0)))
        fun bodyFn pF hpThm =
          let
            val sym = oeq_sym OF [hpThm]                       (* oeq (add k p) 0 *)
            val kz  = add_eq_zero_left_vT OF [sym]             (* oeq k 0 *)
            val b00  = binomN0S2_at ZeroC                      (* oeq (binom 0 0)(Suc 0) *)
            val s00  = subN0S2_at ZeroC                        (* oeq (sub 0 0) 0 *)
            val bcr  = binom_cong_r2 (ZeroC, sub ZeroC ZeroC, ZeroC) s00  (* binom 0 (sub 0 0)=binom 0 0 *)
            val con00 = oeq_trans OF [b00, oeq_sym OF [oeq_trans OF [bcr, b00]]]
                        (* oeq (binom 0 0)(binom 0 (sub 0 0)) *)
            val zfk = Free("zk",natT)
            val PsubAbs = Term.lambda zfk
                            (oeq (binom ZeroC zfk) (binom ZeroC (sub ZeroC zfk)))
            val kzsym = oeq_sym OF [kz]                        (* oeq 0 k *)
            val conK = substPredS2 (PsubAbs, ZeroC, kF) kzsym con00
          in conK end
        val conThm = exE_elimS2 (Habs, conO) hAnt "p" bodyFn
        val impThm = impI_S2 (anteO, conO)
                       (Thm.implies_intr (ctermSub (jT anteO)) conThm)
        val allMinor = Thm.forall_intr (ctermSub kF) impThm
      in allI_S2 (predAbs ZeroC) allMinor end;

    (* ====================================================================
       STEP n = x -> Suc x.   IH : Forall k. obody x k.
       ==================================================================== *)
    val xF = Free("x", natT);
    val ihprop = jT (predForall xF);
    val IH = Thm.assume (ctermSub ihprop);
    fun IH_at t = allE_S2 (predAbs xF) t IH;   (* jT (obody x t) = object Imp *)
    fun IH_use (kT, hle) =                       (* discharge le kT x -> binom x kT = binom x (sub x kT) *)
      mp_S2 (le kT xF, oeq (binom xF kT)(binom xF (sub xF kT))) (IH_at kT) hle;

    val stepconcl =
      let
        val kF = Free("k", natT);
        val dz = dzos_at kF;
        val goalC = obody (suc xF) kF;

        (* ---- k = 0 ----
           binom (Suc x) 0 = 1 = binom (Suc x)(Suc x) = binom (Suc x)(sub (Suc x) 0) *)
        val caseA =
          let
            val hA = jT (oeq kF ZeroC)
            val ante0 = le ZeroC (suc xF)
            val con0  = oeq (binom (suc xF) ZeroC) (binom (suc xF) (sub (suc xF) ZeroC))
            val bsx0  = binomN0S2_at (suc xF)                 (* oeq (binom (Sx) 0)(Suc 0) *)
            val sSx0  = subN0S2_at (suc xF)                   (* oeq (sub (Sx) 0)(Sx) *)
            val bcr   = binom_cong_r2 (suc xF, sub (suc xF) ZeroC, suc xF) sSx0
            val bnn   = binom_n_n_at (suc xF)                 (* oeq (binom (Sx)(Sx))(Suc 0) *)
            val rhs1  = oeq_trans OF [bcr, bnn]               (* oeq (binom (Sx)(sub (Sx) 0))(Suc 0) *)
            val con0Thm = oeq_trans OF [bsx0, oeq_sym OF [rhs1]]
            val hAnt = Thm.assume (ctermSub (jT ante0))
            val impThm = impI_S2 (ante0, con0)
                           (Thm.implies_intr (ctermSub (jT ante0)) con0Thm)
            val hAsym = oeq_sym OF [Thm.assume (ctermSub hA)]  (* oeq 0 k *)
            val transported = substPredS2 (predAbs (suc xF), ZeroC, kF) hAsym impThm
          in Thm.implies_intr (ctermSub hA) transported end;

        (* ---- k = Suc k0 ---- *)
        val exTerm = mkExSuc kF;
        val caseB =
          let
            val hB = jT exTerm
            val PabsE = Abs("q", natT, oeq kF (suc (Bound 0)))
            fun bodyFn k0F hk0Thm =
              let
                val ante = le (suc k0F) (suc xF)
                val con  = oeq (binom (suc xF) (suc k0F)) (binom (suc xF) (sub (suc xF) (suc k0F)))
                val hAnt = Thm.assume (ctermSub (jT ante))
                val lek0x = le_SS_rev_at (k0F, xF) hAnt        (* le k0 x : ?p. x = k0 + p *)
                (* eliminate le k0 x ONCE -> witness p, hp : oeq x (add k0 p) *)
                val HabsP = Abs("p", natT, oeq xF (add k0F (Bound 0)))
                fun pBody pF hp =
                  let
                    (* sub x k0 = p :  sub (add k0 p) k0 = p [subAddL], cong with hp *)
                    val subAdd = subAddL_at (k0F, pF)          (* oeq (sub (add k0 p) k0) p *)
                    val zk = Free("zs", natT)
                    val Pcong = Term.lambda zk (oeq (sub zk k0F) (sub (add k0F pF) k0F))
                    val subXcong = substPredS2 (Pcong, add k0F pF, xF) (oeq_sym OF [hp])
                                     (oeqreflS2_at (sub (add k0F pF) k0F))
                                   (* oeq (sub x k0)(sub (add k0 p) k0) *)
                    val subEqP = oeq_trans OF [subXcong, subAdd]   (* oeq (sub x k0) p *)
                    (* case-split on p *)
                    val dzP = dzos_at pF
                    val exP = mkExSuc pF
                    (* ===== p = 0 : k0 = x ; LHS=1, RHS=1 ===== *)
                    val cZ =
                      let
                        val hpz = jT (oeq pF ZeroC)
                        val hpzThm = Thm.assume (ctermSub hpz)
                        (* x = add k0 p = add k0 0 = k0 ; so oeq x k0, oeq k0 x *)
                        val congP = add_cong_rS2 (k0F, pF, ZeroC) hpzThm   (* add k0 p = add k0 0 *)
                        val a0r   = add0rS2_at k0F                          (* add k0 0 = k0 *)
                        val xEqk0 = oeq_trans OF [hp, oeq_trans OF [congP, a0r]]  (* oeq x k0 *)
                        val k0Eqx = oeq_sym OF [xEqk0]                      (* oeq k0 x *)
                        (* binom x k0 = binom x x = 1 *)
                        val bxk0_xx = binom_cong_r2 (xF, k0F, xF) k0Eqx     (* binom x k0 = binom x x *)
                        val bnnx    = binom_n_n_at xF                       (* binom x x = 1 *)
                        val bxk0_1  = oeq_trans OF [bxk0_xx, bnnx]          (* binom x k0 = 1 *)
                        (* binom x (Suc k0) = binom x (Suc x) = 0 *)
                        val sk0Eqsx = Suc_cong OF [k0Eqx]                   (* oeq (Suc k0)(Suc x) *)
                        val bxsk0_sx= binom_cong_r2 (xF, suc k0F, suc xF) sk0Eqsx
                        val bnSnx   = binomNSn_at xF                        (* binom x (Suc x) = 0 *)
                        val bxsk0_0 = oeq_trans OF [bxsk0_sx, bnSnx]        (* binom x (Suc k0) = 0 *)
                        (* LHS = binom (Suc x)(Suc k0) = binom x k0 + binom x (Suc k0) [Pascal] = 1+0 = 1 *)
                        val pasc = binomSSS2_at (xF, k0F)
                        val cL   = add_cong_lS2 (binom xF k0F, suc ZeroC, binom xF (suc k0F)) bxk0_1
                        val cR   = add_cong_rS2 (suc ZeroC, binom xF (suc k0F), ZeroC) bxsk0_0
                        val a10  = add0rS2_at (suc ZeroC)                   (* add (Suc 0) 0 = Suc 0 *)
                        val lhsTo1 = oeq_trans OF [oeq_trans OF [oeq_trans OF [pasc, cL], cR], a10]
                                     (* oeq LHS (Suc 0) *)
                        (* RHS = binom (Suc x)(sub (Suc x)(Suc k0)) = binom (Suc x)(sub x k0) [subSS]
                                = binom (Suc x) 0 [sub x k0 = p = 0] = 1 *)
                        val sssR = subSSS2_at (xF, k0F)                     (* oeq (sub (Sx)(Sk0))(sub x k0) *)
                        val rhsCong1 = binom_cong_r2 (suc xF, sub (suc xF) (suc k0F), sub xF k0F) sssR
                        val subXEq0 = oeq_trans OF [subEqP, hpzThm]         (* oeq (sub x k0) 0 *)
                        val rhsCong2 = binom_cong_r2 (suc xF, sub xF k0F, ZeroC) subXEq0
                        val bSx0  = binomN0S2_at (suc xF)                   (* binom (Sx) 0 = 1 *)
                        val rhsTo1 = oeq_trans OF [oeq_trans OF [rhsCong1, rhsCong2], bSx0]
                        val conThm = oeq_trans OF [lhsTo1, oeq_sym OF [rhsTo1]]
                      in Thm.implies_intr (ctermSub hpz) conThm end
                    (* ===== p = Suc r : k0 < x ; Pascal+IH both sides ===== *)
                    val cS =
                      let
                        val hpe = jT exP
                        val PrAbs = Abs("r", natT, oeq pF (suc (Bound 0)))
                        fun rBody rF hrThm =
                          let
                            (* hrThm : oeq p (Suc r) ; sub x k0 = p = Suc r *)
                            val subXSr = oeq_trans OF [subEqP, hrThm]       (* oeq (sub x k0)(Suc r) *)
                            (* x = add k0 p = add k0 (Suc r) = Suc (add k0 r) = add (Suc k0) r *)
                            val congP2 = add_cong_rS2 (k0F, pF, suc rF) hrThm  (* add k0 p = add k0 (Suc r) *)
                            val asr    = addSrS2_at (k0F, rF)               (* add k0 (Suc r) = Suc (add k0 r) *)
                            val asl    = addSucS2_at (k0F, rF)              (* add (Suc k0) r = Suc (add k0 r) *)
                            val xEqSk0r = oeq_trans OF [hp,
                                            oeq_trans OF [congP2,
                                              oeq_trans OF [asr, oeq_sym OF [asl]]]]
                                          (* oeq x (add (Suc k0) r) *)
                            (* le (Suc k0) x  witness r *)
                            val leSk0x = le_introS2 (suc k0F, xF, rF) xEqSk0r
                            (* sub x (Suc k0) = r :  sub (add (Suc k0) r)(Suc k0) = r [subAddL], cong with x=... *)
                            val subAdd2 = subAddL_at (suc k0F, rF)          (* oeq (sub (add (Suc k0) r)(Suc k0)) r *)
                            val zk2 = Free("zs2", natT)
                            val Pc2 = Term.lambda zk2 (oeq (sub zk2 (suc k0F)) (sub (add (suc k0F) rF) (suc k0F)))
                            val subXsk0cong = substPredS2 (Pc2, add (suc k0F) rF, xF) (oeq_sym OF [xEqSk0r])
                                                (oeqreflS2_at (sub (add (suc k0F) rF) (suc k0F)))
                                              (* oeq (sub x (Suc k0))(sub (add (Suc k0) r)(Suc k0)) *)
                            val subXsk0_r = oeq_trans OF [subXsk0cong, subAdd2]  (* oeq (sub x (Suc k0)) r *)
                            (* IH at k0 : binom x k0 = binom x (sub x k0) = binom x (Suc r) *)
                            val ihk0 = IH_use (k0F, lek0x)                  (* binom x k0 = binom x (sub x k0) *)
                            val bk0_Sr = oeq_trans OF [ihk0,
                                           binom_cong_r2 (xF, sub xF k0F, suc rF) subXSr]
                                         (* binom x k0 = binom x (Suc r) *)
                            (* IH at Suc k0 : binom x (Suc k0) = binom x (sub x (Suc k0)) = binom x r *)
                            val ihSk0 = IH_use (suc k0F, leSk0x)            (* binom x (Suc k0) = binom x (sub x (Suc k0)) *)
                            val bSk0_r = oeq_trans OF [ihSk0,
                                           binom_cong_r2 (xF, sub xF (suc k0F), rF) subXsk0_r]
                                         (* binom x (Suc k0) = binom x r *)
                            (* RHS = binom (Suc x)(sub (Suc x)(Suc k0)) = binom (Suc x)(sub x k0) [subSS]
                                   = binom (Suc x)(Suc r) [sub x k0 = Suc r]
                                   = binom x r + binom x (Suc r) [Pascal] *)
                            val sssR = subSSS2_at (xF, k0F)
                            val rcong1 = binom_cong_r2 (suc xF, sub (suc xF) (suc k0F), sub xF k0F) sssR
                            val rcong2 = binom_cong_r2 (suc xF, sub xF k0F, suc rF) subXSr
                            val pascR  = binomSSS2_at (xF, rF)              (* binom (Sx)(Sr) = binom x r + binom x (Sr) *)
                            val rhsToSum = oeq_trans OF [oeq_trans OF [rcong1, rcong2], pascR]
                                           (* oeq RHS (add (binom x r)(binom x (Suc r))) *)
                            (* rewrite the sum : binom x r = binom x (Suc k0) [bSk0_r sym],
                                                 binom x (Suc r) = binom x k0 [bk0_Sr sym] *)
                            val sumL = add_cong_lS2 (binom xF rF, binom xF (suc k0F), binom xF (suc rF))
                                         (oeq_sym OF [bSk0_r])
                                       (* add (binom x r)(binom x (Sr)) = add (binom x (Sk0))(binom x (Sr)) *)
                            val sumR = add_cong_rS2 (binom xF (suc k0F), binom xF (suc rF), binom xF k0F)
                                         (oeq_sym OF [bk0_Sr])
                                       (* = add (binom x (Sk0))(binom x k0) *)
                            val comm = addcommS2_at (binom xF (suc k0F), binom xF k0F)
                                       (* = add (binom x k0)(binom x (Sk0)) *)
                            (* LHS = binom (Suc x)(Suc k0) = add (binom x k0)(binom x (Suc k0)) [Pascal] *)
                            val pascL = binomSSS2_at (xF, k0F)
                            val rhsToLHSform = oeq_trans OF [rhsToSum,
                                                 oeq_trans OF [sumL, oeq_trans OF [sumR, comm]]]
                                               (* oeq RHS (add (binom x k0)(binom x (Sk0))) *)
                            (* pascL : LHS = sumform ; rhsToLHSform : RHS = sumform.
                               so con : oeq LHS RHS  =  pascL then sym rhsToLHSform *)
                            val conFinal = oeq_trans OF [pascL, oeq_sym OF [rhsToLHSform]]
                          in conFinal end
                        val rElim = exE_elimS2 (PrAbs, con) (Thm.assume (ctermSub hpe)) "r" rBody
                      in Thm.implies_intr (ctermSub hpe) rElim end
                    val conThm = disjE_elimS2 (oeq pF ZeroC, exP, con) dzP cZ cS
                  in conThm end   (* con, depending on hAnt (via lek0x) *)
                (* eliminate le k0 x -> con (still under hAnt) *)
                val conUnderAnt = exE_elimS2 (HabsP, con) lek0x "p" pBody
                (* discharge ante : impI con  ->  object Imp (ante --> con) = obody (Suc x)(Suc k0) *)
                val impThm0 = impI_S2 (ante, con)
                                (Thm.implies_intr (ctermSub (jT ante)) conUnderAnt)
                (* transport obody (Suc x)(Suc k0) to obody (Suc x) k via k = Suc k0 *)
                val hksym = oeq_sym OF [hk0Thm]                 (* oeq (Suc k0) k *)
                val transported = substPredS2 (predAbs (suc xF), suc k0F, kF) hksym impThm0
              in transported end
            val elimd = exE_elimS2 (PabsE, goalC) (Thm.assume (ctermSub hB)) "k0" bodyFn
          in Thm.implies_intr (ctermSub hB) elimd end;

        val bodyK = disjE_elimS2 (oeq kF ZeroC, exTerm, goalC) dz caseA caseB
        val allMinor = Thm.forall_intr (ctermSub kF) bodyK
      in allI_S2 (predAbs (suc xF)) allMinor end;

    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val () = out "BINOM_SYM_BUILT\n";

(* ---- intended statement (n,k general) + 0-hyp check ---- *)
val i_binom_symmetry =
  jT (mkForall (Term.lambda (Free("kk",natT))
        (mkImp (le (Free("kk",natT)) nVs)
               (oeq (binom nVs (Free("kk",natT)))
                    (binom nVs (sub nVs (Free("kk",natT))))))));
val r_binom_symmetry = checkSub ("binom_symmetry", binom_symmetry, i_binom_symmetry);

(* instantiator : from le k n derive oeq (binom n k)(binom n (sub n k)) *)
val binom_symmetry_vS2 = varify binom_symmetry;
fun binom_sym_at (nT, kT) hle =
  let
    val allInst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("n",0), ctermSub nT)] binom_symmetry_vS2)   (* forall k. obody n k *)
    val Pabs = Term.lambda (Free("kk",natT))
                 (mkImp (le (Free("kk",natT)) nT)
                        (oeq (binom nT (Free("kk",natT)))
                             (binom nT (sub nT (Free("kk",natT))))))
    val impThm = allE_S2 Pabs kT allInst
  in mp_S2 (le kT nT, oeq (binom nT kT)(binom nT (sub nT kT))) impThm hle end;

(* ---- soundness probe : dropping the le hypothesis must NOT be provable.
        binom_symmetry must still CARRY the le-premise inside its object Forall
        body (the prop is not aconv to the le-free universal). ---- *)
val s_sym_needs_le =
  let
    val badBody = Term.lambda (Free("kk",natT))
                    (oeq (binom nVs (Free("kk",natT)))
                         (binom nVs (sub nVs (Free("kk",natT)))))
    val badProp = jT (mkForall badBody)
  in not ((Thm.prop_of binom_symmetry) aconv badProp) end;

val () = out ("binom_symmetry-0hyp=" ^ Bool.toString (length (Thm.hyps_of binom_symmetry) = 0)
              ^ " needs_le=" ^ Bool.toString s_sym_needs_le ^ "\n");

val () =
  if r_binom_symmetry then out "OK binom_symmetry\n" else out "FAIL binom_symmetry\n";

val () =
  if r_binom_symmetry andalso s_sym_needs_le
  then out "BINOM_SYMMETRY_OK\n"
  else out "BINOM_SYMMETRY_FAIL\n";
(* ============================================================================
   PHASE 2 : THE CENTRAL BINOMIAL COEFFICIENT IDENTITY  (seat cb0)
     central_binomial : |- oeq (sumf (%k. mult (binom n k)(binom n k)) n)
                               (binom (add n n) n)
       sum_{k=0..n} C(n,k)^2 = C(2n, n)
   A short corollary of Vandermonde (m:=n,n:=n,k:=n) + Phase-1 binom_symmetry.
   ============================================================================ *)
val () = out "CENTRAL_BEGIN\n";

val central_binomial =
  let
    val nF = Free("n", natT);

    (* ---- 1.  Instantiate vandermonde at m:=n, n:=n  (both schematic ?m,?n),
              then allE @ k:=n to drop the object-Forall over k. ---------------- *)
    val vand_inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("m",0), ctermSub nF), (("n",0), ctermSub nF)] vandermonde);
    (* vand_inst : jT (Forall (%k. oeq (sumf (%j. C(n,j)*C(n,k-j)) k) (C(n+n, k)))) *)

    (* the object-Forall predicate abstraction (over k), matching vand_inst *)
    val kFV = Free("k", natT);
    val FsrcAt = Abs("j", natT, mult (binom nF (Bound 0)) (binom nF (sub kFV (Bound 0))));
    val vandPredAbs =
      Term.lambda kFV (oeq (sumf FsrcAt kFV) (binom (add nF nF) kFV));
    (* allE @ n *)
    val vand_at_n = allE_S2 vandPredAbs nF vand_inst;
    (* vand_at_n : oeq (sumf (%j. C(n,j)*C(n,n-j)) n) (C(n+n, n)) *)

    (* the concrete source summand abstraction at k:=n *)
    val Fsrc = Abs("j", natT, mult (binom nF (Bound 0)) (binom nF (sub nF (Bound 0))));
    (* target summand abstraction : %k. mult (C(n,k))(C(n,k)) *)
    val Gtgt = Abs("k", natT, mult (binom nF (Bound 0)) (binom nF (Bound 0)));

    (* ---- 2.  sum_cong : sumf Fsrc n = sumf Gtgt n
              congProof : !!j. le j n ==> Fsrc_at j = Gtgt_at j --------------- *)
    val congSum =
      let
        val jF = Free("j", natT);
        val hle = Thm.assume (ctermSub (jT (le jF nF)));
        (* binom_symmetry at (n,j) : le j n ==> oeq (binom n j) (binom n (sub n j)) *)
        val symj = binom_sym_at (nF, jF) hle;        (* oeq (binom n j) (binom n (sub n j)) *)
        val symjS = oeq_sym OF [symj];               (* oeq (binom n (sub n j)) (binom n j) *)
        (* rewrite the RIGHT factor of  mult (C n j) (C n (n-j))  ->  mult (C n j) (C n j) *)
        val body = mult_cong_rS2 (binom nF jF, binom nF (sub nF jF), binom nF jF) symjS;
                   (* oeq (mult (C n j)(C n (n-j))) (mult (C n j)(C n j)) = Fsrc_at j = Gtgt_at j *)
        val dis  = Thm.implies_intr (ctermSub (jT (le jF nF))) body;
        val allm = Thm.forall_intr (ctermSub jF) dis;  (* !!j. le j n ==> Fsrc_at j = Gtgt_at j *)
      in sum_cong_at (Fsrc, Gtgt, nF) allm end;       (* oeq (sumf Fsrc n) (sumf Gtgt n) *)

    (* ---- 3.  chain :
         sumf Gtgt n = sumf Fsrc n        [sym congSum]
                     = C(n+n, n)          [vand_at_n]
       i.e. goal : oeq (sumf Gtgt n) (binom (add n n) n) ----------------------- *)
    val congSumS = oeq_sym OF [congSum];              (* oeq (sumf Gtgt n) (sumf Fsrc n) *)
    val finalEq  = oeq_trans OF [congSumS, vand_at_n];(* oeq (sumf Gtgt n) (binom (add n n) n) *)
  in varify finalEq end;

val () = out "CENTRAL_BUILT\n";

(* ---- intended statement (n general) + 0-hyp check.
        NB: varify will NOT eta-contract Gtgt (%k. mult (C n k)(C n k) is not
        eta-reducible), so the intended uses the same lambda form. ---- *)
val i_central_binomial =
  let
    val nVp = Var (("n",0), natT);
    val Gv  = Abs("k", natT, mult (binom nVp (Bound 0)) (binom nVp (Bound 0)));
  in jT (oeq (sumf Gv nVp) (binom (add nVp nVp) nVp)) end;
val r_central_binomial = checkSub ("central_binomial", central_binomial, i_central_binomial);

(* ---- soundness probe : the kernel must reject replacing C(2n,n) by C(2n,Suc n). ---- *)
val i_central_wrong =
  let
    val nVp = Var (("n",0), natT);
    val Gv  = Abs("k", natT, mult (binom nVp (Bound 0)) (binom nVp (Bound 0)));
  in jT (oeq (sumf Gv nVp) (binom (add nVp nVp) (suc nVp))) end;
val r_central_wrong_rejected =
  not ((Thm.prop_of central_binomial) aconv i_central_wrong);

val () =
  out ("central_binomial-0hyp=" ^ Bool.toString (length (Thm.hyps_of central_binomial) = 0)
       ^ " wrong_rejected=" ^ Bool.toString r_central_wrong_rejected ^ "\n");

val () =
  if r_central_binomial then out "OK central_binomial\n" else out "FAIL central_binomial\n";

val () =
  if r_central_binomial andalso r_central_wrong_rejected
  then out "CENTRAL_BINOMIAL_OK\n"
  else out "CENTRAL_BINOMIAL_FAIL\n";

