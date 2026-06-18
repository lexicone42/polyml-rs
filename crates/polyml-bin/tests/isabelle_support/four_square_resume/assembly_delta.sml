(* ============================================================================
   PART (ASSEMBLY) — Lagrange four-square: multiplicative-closure assembly.
   Delta appended after the FULL identity delta (which builds `four_sq_mult`).
   Final context ctxtGR/ctermGR on thyGR.

   GOAL (this seat):  reduce the full four-square theorem to "every prime is a
   sum of four squares".  Concretely, prove on the kernel:

     lagrange_assembly :
       ( !!p. prime2 p ==> four_sq p )                 [the prime hypothesis]
       ==> !!n. Trueprop (four_sq n)                   [every n is four_sq]

   by STRONG INDUCTION on n + prime_cases factorisation, using:
     - four_sq 0, four_sq 1, four_sq 2                  (base cases, witnesses)
     - four_sq_mult  (PART A, multiplicativity)
     - prime_cases   (classical primality split, from base)
     - strong_induct (course-of-values, from base)
     - the cofactor/bound lemma  k = n/d  has  k < n   (proved inline)

   With "every prime is four_sq" (PART B front-end + PART C descent — in
   progress in sibling seats) this yields  !!n. four_sq n  unconditionally.
   ============================================================================ *)
val () = out "L4_ASM_BEGIN\n";

fun sqA x = mult x x;

(* ---------------------------------------------------------------------------
   varify the big theorems onto GR.
   --------------------------------------------------------------------------- *)
val four_sq_mult_vGR = varify four_sq_mult;       (* four_sq m ==> four_sq n ==> four_sq (mult m n) *)
val strong_induct_vGR = varify strong_induct;     (* (!!n.(!!m. lt m n ==> P m)==> P n) ==> P k *)
val prime_cases_vGR  = varify prime_cases;        (* lt 1 n ==> Disj (prime2 n)(Ex d. 1<d /\ d<n /\ d|n) *)
val () = out "L4_ASM_VARIFY_OK\n";

(* instantiators on ctxtGR *)
fun four_sq_mult_at (mT, nT) hm hn =
  Thm.implies_elim (Thm.implies_elim
    (beta_norm (Drule.infer_instantiate ctxtGR
       [(("m_mul",0), ctermGR mT),(("n_mul",0), ctermGR nT)] four_sq_mult_vGR)) hm) hn;

fun prime_cases_at nT hgt1 =
  Thm.implies_elim
    (beta_norm (Drule.infer_instantiate ctxtGR [(("n",0), ctermGR nT)] prime_cases_vGR)) hgt1;

(* prime_cases's schematic var name: discover it from the prop *)
val () = out ("L4_ASM_PRIMECASES_PROP "^Syntax.string_of_term ctxtGR (Thm.prop_of prime_cases_vGR)^"\n");
val () = out ("L4_ASM_SI_PROP "^Syntax.string_of_term ctxtGR (Thm.prop_of strong_induct_vGR)^"\n");

(* ============================================================================
   BASE CASES :  four_sq 0, four_sq 1, four_sq 2 via four_sq_witness.
   four_sq_witness (n,a,b,c,d) hbody : hbody : oeq n (a*a+b*b+c*c+d*d) ==> four_sq n
   ============================================================================ *)
val twoN = suc (suc ZeroC);

(* helper: oeq T (T) reflexivity, then build body equations via proveIdentityG /
   simple recursion.  We build oeq n (a^2+b^2+c^2+d^2) for the chosen witnesses. *)

(* four_sq 0 : 0 = 0*0 + 0*0 + 0*0 + 0*0.  RHS reduces to 0 by mult0 + add0. *)
val fsq0 =
  let
    val rhs = add (add (sqA ZeroC)(sqA ZeroC))(add (sqA ZeroC)(sqA ZeroC))
    (* prove oeq 0 rhs : rhs = 0. *)
    val m00 = mult0r_d ZeroC                              (* 0*0 = 0 *)
    (* add (0*0)(0*0) = add 0 0 = 0 *)
    val ac1 = add_cong_l_g (sqA ZeroC, ZeroC, sqA ZeroC) m00   (* add (0*0)(0*0)=add 0 (0*0) *)
    val ac2 = add_cong_r_g (ZeroC, sqA ZeroC, ZeroC) m00       (* add 0 (0*0)=add 0 0 *)
    val a00 = add0_d ZeroC                                       (* add 0 0 = 0 *)
    val half = oeqTrans_r2 (oeqTrans_r2 (ac1, ac2), a00)        (* add (0*0)(0*0) = 0 *)
    val full1 = add_cong_l_g (add (sqA ZeroC)(sqA ZeroC), ZeroC, add (sqA ZeroC)(sqA ZeroC)) half
    val full2 = add_cong_r_g (ZeroC, add (sqA ZeroC)(sqA ZeroC), ZeroC) half
    val rhsEq = oeqTrans_r2 (oeqTrans_r2 (full1, full2), a00)   (* rhs = 0 *)
    val body  = oeqSym_r2 rhsEq                                  (* oeq 0 rhs *)
  in four_sq_witness (ZeroC, ZeroC, ZeroC, ZeroC, ZeroC) body end;
val () = out ("L4_ASM_FSQ0 hyps="^Int.toString(length(Thm.hyps_of fsq0))^"\n");

(* four_sq 1 : 1 = 1*1 + 0 + 0 + 0.  1*1=1, the zero-squares vanish. *)
val oneT = suc ZeroC;
val fsq1 =
  let
    val rhs = add (add (sqA oneT)(sqA ZeroC))(add (sqA ZeroC)(sqA ZeroC))
    (* 1*1 = 1 : mult (Suc 0) 0? no, sqA 1 = mult 1 1.  mult (Suc 0) 1 = add 1 (mult 0 1).
       Easier: mult 1 1 = mult 1 1; use multSuc_d (0,1): mult (Suc 0) 1 = add 1 (mult 0 1).
       mult 0 1 = mult0l? we have mult_0_left? use multcomm + mult0r. *)
    val m01 = mult0r_d oneT          (* mult 1 0 = 0 -- not what we want *)
    (* mult 1 1 = add 1 (mult 0 1)  [multSuc_d (0,1)] *)
    val ms  = multSuc_d (ZeroC, oneT)        (* mult (Suc 0) 1 = add 1 (mult 0 1) *)
    (* mult 0 1 = 0 : multcomm then mult0r *)
    val mc  = multcomm_g (ZeroC, oneT)       (* mult 0 1 = mult 1 0 *)
    val m10 = mult0r_d oneT                  (* mult 1 0 = 0 *)
    val m0_1 = oeqTrans_r2 (mc, m10)         (* mult 0 1 = 0 *)
    (* add 1 (mult 0 1) = add 1 0 = 1 *)
    val ac  = add_cong_r_g (oneT, mult ZeroC oneT, ZeroC) m0_1  (* add 1 (mult 0 1) = add 1 0 *)
    val a10 = add0r_d oneT                    (* add 1 0 = 1 *)
    val sq1eq = oeqTrans_r2 (oeqTrans_r2 (ms, ac), a10)  (* mult 1 1 = 1 *)
    (* the three zero squares vanish : sqA 0 = 0 *)
    val z00 = mult0r_d ZeroC                  (* 0*0 = 0 *)
    (* rhs = add (add 1 0)(add 0 0) = add 1 0 = 1 *)
    val r1  = add_cong_l_g (sqA oneT, oneT, sqA ZeroC) sq1eq  (* add (1*1)(0*0) = add 1 (0*0) *)
    val r2  = add_cong_r_g (oneT, sqA ZeroC, ZeroC) z00       (* add 1 (0*0) = add 1 0 *)
    val r3  = add0r_d oneT                                     (* add 1 0 = 1 *)
    val leftEq = oeqTrans_r2 (oeqTrans_r2 (r1, r2), r3)       (* add (1*1)(0*0) = 1 *)
    val rr1 = add_cong_l_g (sqA ZeroC, ZeroC, sqA ZeroC) z00  (* add (0*0)(0*0) = add 0 (0*0) *)
    val rr2 = add_cong_r_g (ZeroC, sqA ZeroC, ZeroC) z00      (* add 0 (0*0) = add 0 0 *)
    val rr3 = add0_d ZeroC                                     (* add 0 0 = 0 *)
    val rightEq = oeqTrans_r2 (oeqTrans_r2 (rr1, rr2), rr3)   (* add (0*0)(0*0) = 0 *)
    val f1 = add_cong_l_g (add (sqA oneT)(sqA ZeroC), oneT, add (sqA ZeroC)(sqA ZeroC)) leftEq
    val f2 = add_cong_r_g (oneT, add (sqA ZeroC)(sqA ZeroC), ZeroC) rightEq
    val f3 = add0r_d oneT                                      (* add 1 0 = 1 *)
    val rhsEq = oeqTrans_r2 (oeqTrans_r2 (f1, f2), f3)        (* rhs = 1 *)
    val body  = oeqSym_r2 rhsEq                                (* oeq 1 rhs *)
  in four_sq_witness (oneT, oneT, ZeroC, ZeroC, ZeroC) body end;
val () = out ("L4_ASM_FSQ1 hyps="^Int.toString(length(Thm.hyps_of fsq1))^"\n");

val () = out "L4_ASM_BASECASES_OK\n";

(* ============================================================================
   BOUND LEMMA :  from  1 < d  and  oeq n (mult d k)  and  lt 0 n,
   derive  lt k n.

     d = Suc(Suc d0)  (since 1<d).  n = d*k.
       step 1 : 0 < k  (else n = d*0 = 0, contra 0<n).
       step 2 : k = Suc k0.  n = mult (Suc(Suc d0)) k = add k (mult (Suc d0) k)
                  = add k (add k (mult d0 k)).
                Let R = add k (mult d0 k).  R = add (Suc k0)(mult d0 k)
                  = Suc (add k0 (mult d0 k))  [addSuc_d] = Suc r.
                n = add k (Suc r) = Suc (add k r)  [addSucr_d]
                  = add (Suc k) r                  [addSuc_d reversed].
                so  le (Suc k) n  i.e.  lt k n  (witness r).
   ============================================================================ *)
(* lt0_of : 1 < d  ==>  Ex d0. oeq d (Suc(Suc d0))   via dzos twice *)
(* We instead just need:  from  1<d  we can write d = Suc(Suc d0).
   1<d = le 2 d = le (Suc(Suc 0)) d.  le (Suc(Suc 0)) d => Ex w. oeq d (add (Suc(Suc 0)) w)
   => oeq d (Suc(Suc w))  [addSuc twice + add0].  So d0 := w. *)

(* le_elim_d : le m n  ==>  Ex w. oeq n (add m w)  (le is exactly this Ex; expose witness) *)
(* le m n abbreviates Ex p. oeq n (add m p).  We exE on it. *)
fun le_witness (mT, nT, goalC) hle bodyFn =
  let
    val Pabs = Abs("w_le", natT, oeq nT (add mT (Bound 0)))
  in exE_r (Pabs, goalC) hle "w_le" natT bodyFn end;

(* bound_lemma :  lt (suc ZeroC) d  ->  oeq n (mult d k)  ->  lt ZeroC n  ->  lt k n  *)
fun bound_lemma (dT, kT, nT) h1ltd hNeqDK hPosN =
  let
    val goalC = lt kT nT     (* = le (Suc k) n *)
    (* d = Suc(Suc d0) : from 1<d = le (Suc(Suc 0)) d *)
    val twoC = suc (suc ZeroC)
    (* h1ltd : lt 1 d = le (Suc 1) d = le (Suc(Suc 0)) d = le 2 d *)
    fun afterD0 w hw =      (* hw : oeq d (add (Suc(Suc 0)) w) ; d0 := w *)
      let
        val d0 = w
        (* oeq d (Suc(Suc d0)) :  add (Suc(Suc 0)) d0 = Suc(add (Suc 0) d0) = Suc(Suc(add 0 d0)) = Suc(Suc d0) *)
        val s1 = addSuc_d (suc ZeroC, d0)        (* add (Suc(Suc 0)) d0 = Suc(add (Suc 0) d0) *)
        val s2 = addSuc_d (ZeroC, d0)            (* add (Suc 0) d0 = Suc(add 0 d0) *)
        val s3 = add0_d d0                         (* add 0 d0 = d0 *)
        val s2' = let val P = Term.lambda (Free("zbd",natT)) (oeq (suc (add ZeroC d0))(suc (Free("zbd",natT))))
                  in oeq_rw_r (P, add ZeroC d0, d0) s3 (oeqRefl_r2 (suc (add ZeroC d0))) end (* Suc(add 0 d0)=Suc d0 *)
        val s2'' = oeqTrans_r2 (s2, s2')          (* add (Suc 0) d0 = Suc d0 *)
        val s1' = let val P = Term.lambda (Free("zbd2",natT)) (oeq (suc (add (suc ZeroC) d0))(suc (Free("zbd2",natT))))
                  in oeq_rw_r (P, add (suc ZeroC) d0, suc d0) s2'' (oeqRefl_r2 (suc (add (suc ZeroC) d0))) end (* Suc(add(Suc 0)d0)=Suc(Suc d0) *)
        val twoAddD0 = oeqTrans_r2 (s1, s1')      (* add (Suc(Suc 0)) d0 = Suc(Suc d0) *)
        val dEq = oeqTrans_r2 (hw, twoAddD0)      (* oeq d (Suc(Suc d0)) *)
        (* STEP 1 : 0 < k.  dzos k. *)
        val pos_k =
          let
            val dzk = dzos_d kT     (* Disj (oeq k 0)(Ex q. oeq k (Suc q)) *)
            val caseK0 =
              let val hk0 = Thm.assume (ctermGR (jT (oeq kT ZeroC)))
                  (* n = d*k = d*0 = 0 *)
                  val dk0 = mult_cong_r_g (dT, kT, ZeroC) hk0   (* d*k = d*0 *)
                  val d0z = mult0r_d dT                          (* d*0 = 0 *)
                  val nZ  = oeqTrans_r2 (oeqTrans_r2 (hNeqDK, dk0), d0z)  (* n = 0 *)
                  val z   = Free("zbk",natT)
                  val Plt = Term.lambda z (lt ZeroC z)
                  val hlt0= oeq_rw_r (Plt, nT, ZeroC) nZ hPosN   (* lt 0 0 *)
                  val fls = lt_irrefl_g ZeroC hlt0
              in Thm.implies_intr (ctermGR (jT (oeq kT ZeroC)))
                   (Thm.implies_elim (oFalse_elim_r (lt ZeroC kT)) fls) end
            val PkSuc = Abs("q", natT, oeq kT (suc (Bound 0)))
            val caseKS =
              let val hs = Thm.assume (ctermGR (jT (mkEx PkSuc)))
                  fun bodyKS q hq =   (* hq : oeq k (Suc q) *)
                    let val a1 = addSuc_d (ZeroC, q)    (* add (Suc 0) q = Suc(add 0 q) *)
                        val a2 = add0_d q
                        val a2s= Suc_cong_r a2
                        val a1c= oeqTrans_r2 (a1, a2s)   (* add (Suc 0) q = Suc q *)
                        val a1cs=oeqSym_r2 a1c           (* Suc q = add (Suc 0) q *)
                        val keq= oeqTrans_r2 (hq, a1cs)  (* k = add (Suc 0) q *)
                        val le1k= le_intro_d (suc ZeroC, kT, q) keq   (* le (Suc 0) k = lt 0 k *)
                    in le1k end
              in Thm.implies_intr (ctermGR (jT (mkEx PkSuc)))
                   (exE_r (PkSuc, lt ZeroC kT) hs "qbk" natT bodyKS) end
          in disjE_r (oeq kT ZeroC, mkEx PkSuc, lt ZeroC kT) dzk caseK0 caseKS end
        (* STEP 2 : lt k n.  use 0<k to write k = Suc k0, then unfold n. *)
        val ltkn =
          let
            (* expose k0 from 0<k = le (Suc 0) k = Ex w. oeq k (add (Suc 0) w) *)
            val Pk0 = Abs("w_k0", natT, oeq kT (add (suc ZeroC) (Bound 0)))
            fun afterK0 k0w hk0w =     (* hk0w : oeq k (add (Suc 0) k0w) *)
              let
                (* k = Suc k0w : add (Suc 0) k0w = Suc(add 0 k0w) = Suc k0w *)
                val ka = addSuc_d (ZeroC, k0w)         (* add (Suc 0) k0w = Suc(add 0 k0w) *)
                val kb = add0_d k0w
                val kbs= Suc_cong_r kb                  (* Suc(add 0 k0w) = Suc k0w *)
                val kEq= oeqTrans_r2 (hk0w, oeqTrans_r2 (ka, kbs))  (* k = Suc k0w *)
                (* n = mult d k.  rewrite d -> Suc(Suc d0). *)
                val ndk = hNeqDK                          (* n = mult d k *)
                (* mult d k = mult (Suc(Suc d0)) k *)
                val mdEq = mult_cong_l_g (dT, suc (suc d0), kT) dEq   (* mult d k = mult (Suc(Suc d0)) k *)
                (* mult (Suc(Suc d0)) k = add k (mult (Suc d0) k)  [multSuc_d (Suc d0, k)] *)
                val ms1 = multSuc_d (suc d0, kT)          (* mult (Suc(Suc d0)) k = add k (mult (Suc d0) k) *)
                (* mult (Suc d0) k = add k (mult d0 k)  [multSuc_d (d0,k)] *)
                val ms2 = multSuc_d (d0, kT)              (* mult (Suc d0) k = add k (mult d0 k) *)
                (* add k (mult (Suc d0) k) = add k (add k (mult d0 k)) *)
                val ms2c = add_cong_r_g (kT, mult (suc d0) kT, add kT (mult d0 kT)) ms2
                val nExp = oeqTrans_r2 (oeqTrans_r2 (oeqTrans_r2 (ndk, mdEq), ms1), ms2c)
                          (* n = add k (add k (mult d0 k)) *)
                (* let R = add k (mult d0 k).  R = add (Suc k0w)(mult d0 k) = Suc(add k0w (mult d0 k)) *)
                val R = add kT (mult d0 kT)
                val r0 = mult d0 kT
                (* rewrite the inner k -> Suc k0w in R via kEq, in BOTH positions?  Only the leading k.
                   R = add k (mult d0 k).  rewrite the FIRST k to Suc k0w. *)
                val zR = Free("zR", natT)
                val PR = Term.lambda zR (oeq (add kT R)(add kT (add zR (mult d0 kT))))
                (* Actually simpler: directly compute add k R where R=add k r0; show n = add (Suc k) (add k0w r0). *)
                (* n = add k (add k r0).  We want oeq n (add (Suc k) W) with W = add k0w r0.
                   add k (add k r0) : rewrite the SECOND k (the one inside the inner add) to Suc k0w:
                     add k (add (Suc k0w) r0) = add k (Suc (add k0w r0))  [addSuc_d]
                       = Suc (add k (add k0w r0))  [addSucr_d]
                       = add (Suc k) (add k0w r0)  [addSuc_d reversed]. *)
                val innerK = add kT r0                  (* = R, the inner add k r0 *)
                (* rewrite inner-add's leading k -> Suc k0w *)
                val zI = Free("zI", natT)
                val PI = Term.lambda zI (oeq (add kT (add kT r0))(add kT (add zI r0)))
                val n1 = oeq_rw_r (PI, kT, suc k0w) kEq (oeqRefl_r2 (add kT (add kT r0)))
                          (* add k (add k r0) = add k (add (Suc k0w) r0) *)
                (* add (Suc k0w) r0 = Suc(add k0w r0) *)
                val n2a = addSuc_d (k0w, r0)            (* add (Suc k0w) r0 = Suc(add k0w r0) *)
                val n2  = add_cong_r_g (kT, add (suc k0w) r0, suc (add k0w r0)) n2a
                          (* add k (add (Suc k0w) r0) = add k (Suc(add k0w r0)) *)
                (* add k (Suc(add k0w r0)) = Suc(add k (add k0w r0))  [addSucr_d] *)
                val n3 = addSucr_d (kT, add k0w r0)     (* add k (Suc(add k0w r0)) = Suc(add k (add k0w r0)) *)
                (* Suc(add k (add k0w r0)) = add (Suc k)(add k0w r0)  [addSuc_d reversed] *)
                val n4a = addSuc_d (kT, add k0w r0)     (* add (Suc k)(add k0w r0) = Suc(add k (add k0w r0)) *)
                val n4  = oeqSym_r2 n4a                  (* Suc(add k (add k0w r0)) = add (Suc k)(add k0w r0) *)
                val W   = add k0w r0
                val nFinal = oeqTrans_r2 (oeqTrans_r2 (oeqTrans_r2 (oeqTrans_r2 (nExp, n1), n2), n3), n4)
                          (* n = add (Suc k) W *)
                val ltThm = le_intro_d (suc kT, nT, W) nFinal   (* le (Suc k) n = lt k n *)
              in ltThm end
          in exE_r (Pk0, lt kT nT) pos_k "wk0" natT afterK0 end
      in ltkn end
    (* h1ltd : lt 1 d = le (Suc(Suc 0)) d.  expose witness w with oeq d (add (Suc(Suc 0)) w). *)
  in le_witness (twoC, dT, goalC) h1ltd afterD0 end;

val () = out "L4_ASM_BOUND_FN_READY\n";

(* smoke : bound_lemma on concrete frees with assumed hyps *)
val () =
  let
    val dF = Free("d_bl", natT); val kF = Free("k_bl", natT); val nF = Free("n_bl", natT)
    val h1 = Thm.assume (ctermGR (jT (lt (suc ZeroC) dF)))
    val h2 = Thm.assume (ctermGR (jT (oeq nF (mult dF kF))))
    val h3 = Thm.assume (ctermGR (jT (lt ZeroC nF)))
    val r = bound_lemma (dF, kF, nF) h1 h2 h3
  in out ("SMOKE bound_lemma : "^Syntax.string_of_term ctxtGR (Thm.prop_of r)
          ^" hyps="^Int.toString(length(Thm.hyps_of r))^"\n") end
  handle e => out ("SMOKE bound_lemma FAIL "^exnMessage e^"\n");
val () = out "L4_ASM_BOUND_SMOKE_OK\n";

(* ============================================================================
   four_sq 2 : 2 = 1 + 1 + 0 + 0  (needed as a base case only if we special-case
   it; the strong induction actually handles n>=2 uniformly via prime_cases, so 2
   is reached as prime.  We still build it for the soundness/marker set.)
   ============================================================================ *)
val fsq2 =
  let
    val rhs = add (add (sqA oneT)(sqA oneT))(add (sqA ZeroC)(sqA ZeroC))
    (* sqA 1 = 1 (reuse fsq1's computation inline) *)
    val ms  = multSuc_d (ZeroC, oneT)
    val mc  = multcomm_g (ZeroC, oneT)
    val m10 = mult0r_d oneT
    val m0_1= oeqTrans_r2 (mc, m10)
    val ac  = add_cong_r_g (oneT, mult ZeroC oneT, ZeroC) m0_1
    val a10 = add0r_d oneT
    val sq1eq = oeqTrans_r2 (oeqTrans_r2 (ms, ac), a10)     (* mult 1 1 = 1 *)
    val z00 = mult0r_d ZeroC                                 (* 0*0 = 0 *)
    (* left = add (1*1)(1*1) = add 1 1 = 2 *)
    val l1 = add_cong_l_g (sqA oneT, oneT, sqA oneT) sq1eq   (* add(1*1)(1*1)=add 1 (1*1) *)
    val l2 = add_cong_r_g (oneT, sqA oneT, oneT) sq1eq        (* add 1 (1*1)=add 1 1 *)
    val leftEq = oeqTrans_r2 (l1, l2)                          (* add(1*1)(1*1)=add 1 1 = 2 *)
    (* right = add (0*0)(0*0) = 0 *)
    val rr1 = add_cong_l_g (sqA ZeroC, ZeroC, sqA ZeroC) z00
    val rr2 = add_cong_r_g (ZeroC, sqA ZeroC, ZeroC) z00
    val rr3 = add0_d ZeroC
    val rightEq = oeqTrans_r2 (oeqTrans_r2 (rr1, rr2), rr3)   (* add(0*0)(0*0)=0 *)
    val f1 = add_cong_l_g (add (sqA oneT)(sqA oneT), add oneT oneT, add (sqA ZeroC)(sqA ZeroC)) leftEq
    val f2 = add_cong_r_g (add oneT oneT, add (sqA ZeroC)(sqA ZeroC), ZeroC) rightEq
    val f3 = add0r_d (add oneT oneT)                          (* add (1+1) 0 = 1+1 *)
    val rhsEq = oeqTrans_r2 (oeqTrans_r2 (f1, f2), f3)        (* rhs = add 1 1 *)
    (* now show oeq 2 rhs : 2 = Suc(Suc 0) ; add 1 1 = Suc(Suc 0) too *)
    val a11 = addSuc_d (ZeroC, oneT)        (* add (Suc 0) 1 = Suc(add 0 1) *)
    val a01 = add0_d oneT                    (* add 0 1 = 1 *)
    val a11s= oeqTrans_r2 (a11, Suc_cong_r a01)  (* add 1 1 = Suc 1 = Suc(Suc 0) = 2 *)
    val twoEqAdd = oeqSym_r2 a11s             (* 2 = add 1 1 *)
    val body = oeqTrans_r2 (twoEqAdd, oeqSym_r2 rhsEq)   (* oeq 2 rhs *)
  in four_sq_witness (twoN, oneT, oneT, ZeroC, ZeroC) body end;
val () = out ("L4_ASM_FSQ2 hyps="^Int.toString(length(Thm.hyps_of fsq2))^"\n");

(* ============================================================================
   helper:  lt1_of_two_plus : for nn = Suc(Suc n''), prove lt (Suc Zero) nn.
     lt 1 nn = le (Suc(Suc 0)) (Suc(Suc n'')) ; witness n'' :
       oeq (Suc(Suc n'')) (add (Suc(Suc 0)) n'')      [twoAdd identity]
   ============================================================================ *)
fun lt1_of_two_plus npp =
  let
    val nn = suc (suc npp)
    (* add (Suc(Suc 0)) n'' = Suc(Suc n'') *)
    val s1 = addSuc_d (suc ZeroC, npp)       (* add (Suc(Suc 0)) n'' = Suc(add (Suc 0) n'') *)
    val s2 = addSuc_d (ZeroC, npp)           (* add (Suc 0) n'' = Suc(add 0 n'') *)
    val s3 = add0_d npp
    val s2' = oeqTrans_r2 (s2, Suc_cong_r s3)  (* add (Suc 0) n'' = Suc n'' *)
    val s1' = oeqTrans_r2 (s1, Suc_cong_r s2') (* add (Suc(Suc 0)) n'' = Suc(Suc n'') *)
    val twoAdd = oeqSym_r2 s1'                  (* Suc(Suc n'') = add (Suc(Suc 0)) n'' *)
  in le_intro_d (suc (suc ZeroC), nn, npp) twoAdd end;   (* le (Suc(Suc 0)) nn = lt 1 nn *)

val () = out "L4_ASM_LT1_FN_READY\n";

(* ============================================================================
   THE STRONG-INDUCTION STEP.
   Prime hypothesis carried as a META assumption hPrimeFsq : !!p. prime2 p ==> four_sq p.
   We build it as a Free meta-thm via Thm.assume on the meta-implication, then
   discharge with forall_intr/implies_intr at the end.
   ============================================================================ *)

(* The meta prime hypothesis term:  !!p. Trueprop(prime2 p) ==> Trueprop(four_sq p) *)
val pHyp = Free("p_hyp", natT);
val primeHypProp = Logic.all pHyp (Logic.mk_implies (jT (prime2 pHyp), jT (four_sq pHyp)));
val hPrimeHyp = Thm.assume (ctermGR primeHypProp);
fun prime_is_fsq nt hpr =     (* prime2 n -> four_sq n *)
  let val inst = Thm.forall_elim (ctermGR nt) hPrimeHyp
  in Thm.implies_elim inst hpr end;

val () = out "L4_ASM_PRIMEHYP_READY\n";

(* predicate R n := four_sq n  (nat=>o) *)
val Rpred =
  let val nR = Free("n_R", natT)
  in Term.lambda nR (four_sq nR) end;

(* strong-induction body : fix n_step, assume G = (!!m. lt m n ==> four_sq m),
   prove four_sq n. *)
val lagrange_for_free_n =
  let
    val nStep = Free("n_step", natT);
    val mIH   = Free("m_ih", natT);
    val Gprop = Logic.all mIH (Logic.mk_implies (jT (lt mIH nStep), jT (four_sq mIH)));
    val Hthm  = Thm.assume (ctermGR Gprop);
    fun applyIH dt h_lt =                       (* lt d n -> four_sq d *)
      Thm.implies_elim (Thm.forall_elim (ctermGR dt) Hthm) h_lt;

    val goalC = four_sq nStep;

    (* case-split nStep : dzos -> 0 or Suc n' *)
    val dz0 = dzos_d nStep;     (* Disj (oeq n 0)(Ex q. oeq n (Suc q)) *)

    (* CASE n = 0 : rewrite four_sq 0 from fsq0 *)
    val caseN0 =
      let val hn0 = Thm.assume (ctermGR (jT (oeq nStep ZeroC)))
          val z = Free("zn0", natT)
          val Pfs = Term.lambda z (four_sq z)
          val r = oeq_rw_r (Pfs, ZeroC, nStep) (oeqSym_r2 hn0) fsq0   (* four_sq n *)
      in Thm.implies_intr (ctermGR (jT (oeq nStep ZeroC))) r end;

    (* CASE n = Suc n' : further split n' *)
    val PnSuc = Abs("q", natT, oeq nStep (suc (Bound 0)));
    val caseNS =
      let
        val hs = Thm.assume (ctermGR (jT (mkEx PnSuc)))
        fun bodyNS np hnp =     (* hnp : oeq n (Suc np) *)
          let
            val dz1 = dzos_d np    (* Disj (oeq np 0)(Ex q. oeq np (Suc q)) *)
            (* SUBCASE np = 0 : n = Suc 0 = 1 *)
            val sub1 =
              let val hnp0 = Thm.assume (ctermGR (jT (oeq np ZeroC)))
                  (* n = Suc np = Suc 0 = 1 *)
                  val nEq1 = oeqTrans_r2 (hnp, Suc_cong_r hnp0)   (* n = Suc 0 = 1 *)
                  val z = Free("zn1", natT)
                  val Pfs = Term.lambda z (four_sq z)
                  val r = oeq_rw_r (Pfs, oneT, nStep) (oeqSym_r2 nEq1) fsq1  (* four_sq n *)
              in Thm.implies_intr (ctermGR (jT (oeq np ZeroC))) r end
            (* SUBCASE np = Suc npp : n = Suc(Suc npp) >= 2 *)
            val Pnpp = Abs("q", natT, oeq np (suc (Bound 0)))
            val sub2 =
              let
                val hss = Thm.assume (ctermGR (jT (mkEx Pnpp)))
                fun bodyPP npp hnpp =    (* hnpp : oeq np (Suc npp) *)
                  let
                    (* n = Suc(Suc npp) *)
                    val nEq = oeqTrans_r2 (hnp, Suc_cong_r hnpp)   (* oeq n (Suc(Suc npp)) *)
                    val nn  = suc (suc npp)
                    (* lt 1 nn, then rewrite nn->n? Better: work with nn then rewrite result. *)
                    val hlt1_nn = lt1_of_two_plus npp              (* lt 1 (Suc(Suc npp)) *)
                    (* rewrite lt 1 nn  -> lt 1 n via nEq (sym): n = nn so 1<nn becomes 1<n.
                       Predicate %z. lt 1 z. *)
                    val zl = Free("zlt1", natT)
                    val Plt1 = Term.lambda zl (lt (suc ZeroC) zl)
                    val hlt1_n = oeq_rw_r (Plt1, nn, nStep) (oeqSym_r2 nEq) hlt1_nn   (* lt 1 n *)
                    (* lt 0 n : n >= 2 so 0 < n.  lt 0 n = le (Suc 0) n.  witness (Suc npp):
                       oeq n (add (Suc 0)(Suc npp))?  add (Suc 0)(Suc npp)=Suc(add 0 (Suc npp))=Suc(Suc npp)=n. *)
                    val pos_n =
                      let val a1 = addSuc_d (ZeroC, suc npp)   (* add (Suc 0)(Suc npp)=Suc(add 0 (Suc npp)) *)
                          val a2 = add0_d (suc npp)             (* add 0 (Suc npp)=Suc npp *)
                          val a1s= oeqTrans_r2 (a1, Suc_cong_r a2)  (* add (Suc 0)(Suc npp)=Suc(Suc npp) *)
                          val nAdd= oeqTrans_r2 (nEq, oeqSym_r2 a1s) (* n = add (Suc 0)(Suc npp) *)
                      in le_intro_d (suc ZeroC, nStep, suc npp) nAdd end   (* le (Suc 0) n = lt 0 n *)
                    (* prime_cases n *)
                    val pdAbs =
                      let val dF = Free("d_pd", natT)
                      in Term.lambda dF (mkConj (mkConj (lt (suc ZeroC) dF) (lt dF nStep)) (dvd dF nStep)) end;
                    val pdEx = mkEx pdAbs;
                    val dThm = prime_cases_at nStep hlt1_n   (* Disj (prime2 n) pdEx *)
                    (* CASE prime *)
                    val cPrime =
                      let val hp = Thm.assume (ctermGR (jT (prime2 nStep)))
                          val r = prime_is_fsq nStep hp     (* four_sq n *)
                      in Thm.implies_intr (ctermGR (jT (prime2 nStep))) r end
                    (* CASE composite : exE d, conjuncts, exE k from d|n, bound, IH x2, mult *)
                    val cComp =
                      let
                        val hpd = Thm.assume (ctermGR (jT pdEx))
                        fun pdBody d hConj =
                          let
                            val innerC = mkConj (lt (suc ZeroC) d) (lt d nStep)
                            val hInner = conjunct1_r (innerC, dvd d nStep) hConj
                            val hDvdDN = conjunct2_r (innerC, dvd d nStep) hConj   (* d|n *)
                            val h_1ltd = conjunct1_r (lt (suc ZeroC) d, lt d nStep) hInner   (* 1<d *)
                            val h_ltdn = conjunct2_r (lt (suc ZeroC) d, lt d nStep) hInner   (* d<n *)
                            (* d|n = Ex k. oeq n (mult d k) *)
                            val dvdBody = Abs("k", natT, oeq nStep (mult d (Bound 0)))
                            fun afterK k hk =     (* hk : oeq n (mult d k) *)
                              let
                                val hltkn = bound_lemma (d, k, nStep) h_1ltd hk pos_n   (* lt k n *)
                                val fsqD  = applyIH d h_ltdn      (* four_sq d *)
                                val fsqK  = applyIH k hltkn       (* four_sq k *)
                                val fsqDK = four_sq_mult_at (d, k) fsqD fsqK   (* four_sq (mult d k) *)
                                (* rewrite mult d k -> n via hk (sym) *)
                                val z = Free("zdk", natT)
                                val Pfs = Term.lambda z (four_sq z)
                                val r = oeq_rw_r (Pfs, mult d k, nStep) (oeqSym_r2 hk) fsqDK  (* four_sq n *)
                              in r end
                            val g = exE_r (dvdBody, goalC) hDvdDN "k_co" natT afterK
                          in g end
                        val g = exE_r (pdAbs, goalC) hpd "d_co" natT pdBody
                      in Thm.implies_intr (ctermGR (jT pdEx)) g end
                    val concl = disjE_r (prime2 nStep, pdEx, goalC) dThm cPrime cComp   (* four_sq n *)
                  in concl end
              in Thm.implies_intr (ctermGR (jT (mkEx Pnpp)))
                   (exE_r (Pnpp, goalC) hss "npp" natT bodyPP) end
          in disjE_r (oeq np ZeroC, mkEx Pnpp, goalC) dz1 sub1 sub2 end
      in Thm.implies_intr (ctermGR (jT (mkEx PnSuc)))
           (exE_r (PnSuc, goalC) hs "np" natT bodyNS) end;

    val stepConcl = disjE_r (oeq nStep ZeroC, mkEx PnSuc, goalC) dz0 caseN0 caseNS  (* four_sq n *)
    (* package as the strong_induct step:  !!n. G n ==> four_sq n *)
    val stepThm = Thm.forall_intr (ctermGR nStep) (Thm.implies_intr (ctermGR Gprop) stepConcl)

    (* apply strong_induct at P := Rpred, k := free kFinal *)
    val kFinal = Free("k_fin", natT)
    val siInst = beta_norm (Drule.infer_instantiate ctxtGR
                   [(("P",0), ctermGR Rpred),(("k",0), ctermGR kFinal)] strong_induct_vGR)
    val Rk = Thm.implies_elim siInst stepThm   (* four_sq k_fin *)
  in Rk end;

val () = out ("L4_ASM_FOR_FREE_N hyps="^Int.toString(length(Thm.hyps_of lagrange_for_free_n))^"\n");
val () = out ("L4_ASM_FOR_FREE_N prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of lagrange_for_free_n)^"\n");

(* ============================================================================
   FINAL THEOREM : discharge the prime hypothesis + generalize n.
     lagrange_assembly :
       (!!p. prime2 p ==> four_sq p) ==> !!n. four_sq n
   ============================================================================ *)
val lagrange_assembly =
  let
    val kFinal = Free("k_fin", natT)
    (* lagrange_for_free_n : four_sq k_fin  (with hyps: Gprop discharged inside; only hPrimeHyp open) *)
    val genN = Thm.forall_intr (ctermGR kFinal) lagrange_for_free_n   (* !!k. four_sq k *)
    val disch= Thm.implies_intr (ctermGR primeHypProp) genN
  in disch end;

val () = out ("lagrange_assembly hyps="^Int.toString(length(Thm.hyps_of lagrange_assembly))^"\n");
val () = out ("lagrange_assembly prop = "^Syntax.string_of_term ctxtGR (Thm.prop_of lagrange_assembly)^"\n");

(* validate against intended *)
val lagrange_assembly_intended =
  let
    val pV = Free("p_hyp", natT); val kV = Free("k_fin", natT)
    val primeHyp = Logic.all pV (Logic.mk_implies (jT (prime2 pV), jT (four_sq pV)))
  in Logic.mk_implies (primeHyp, Logic.all kV (jT (four_sq kV))) end;
val asm_aconv = ((Thm.prop_of lagrange_assembly) aconv lagrange_assembly_intended);
val asm_0hyp  = (length (Thm.hyps_of lagrange_assembly) = 0);
val () = out ("L4_ASM_VALIDATE aconv="^Bool.toString asm_aconv^" zero_hyp="^Bool.toString asm_0hyp^"\n");
val () = if asm_aconv andalso asm_0hyp then out "L4_ASM_OK\n" else out "L4_ASM_VALIDATE_FAILED\n";

(* soundness probe : NOT the unconditional !!n. four_sq n (would drop the prime hyp) *)
val asm_probe =
  let val kV = Free("k_fin", natT)
  in not ((Thm.prop_of lagrange_assembly) aconv (Logic.all kV (jT (four_sq kV)))) end;
val () = out ("L4_ASM_PROBE conditional="^Bool.toString asm_probe^"\n");

val () = if asm_aconv andalso asm_0hyp andalso asm_probe then out "L4_ASM_ALL_OK\n" else out "L4_ASM_PROBES_FAILED\n";
