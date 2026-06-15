(* ============================================================================
   THE CHINESE REMAINDER THEOREM in Isabelle/Pure on the polyml-rs interpreter.
   (test: isabelle_crt.rs)
   ----------------------------------------------------------------------------
   For coprime moduli m, n and any residues a, b there is an x congruent to a
   mod m and to b mod n, and it is unique mod m*n. Proved by genuine LCF kernel
   inference over the naturals (two-sided cong, NO subtraction); the only
   classical assumption anywhere below is excluded middle.

     gen_inverse      : |- (!d. d dvd a ==> d dvd m ==> d = 1) ==> 0 < m
                           ==> ?b. cong m (a*b) 1
                        general modular inverse for coprimes (from coprime_bezout).
     crt_exists       : |- (!d. d dvd m ==> d dvd n ==> d = 1) ==> 0 < m ==> 0 < n
                           ==> !a b. ?x. cong m x a /\ cong n x b
                        EXISTENCE, by the construction x = a*(n*s) + b*(m*t) where
                        n*s == 1 (mod m) and m*t == 1 (mod n).
     gauss            : |- (!d. d dvd n ==> d dvd m ==> d = 1) ==> n dvd (m*c) ==> n dvd c
     coprime_mult_dvd : |- coprime m n ==> m dvd k ==> n dvd k ==> (m*n) dvd k
     crt_unique       : |- coprime m n ==> cong m x y ==> cong n x y ==> cong (m*n) x y
                        UNIQUENESS (two solutions agree mod m*n), via gauss.

   Built on the full gcd/Bezout development (isabelle_gcd.sml: coprime_bezout,
   mod_inverse, dvd_diff, ...) over the unified number-theory base, spliced in by
   common::with_gcd. Each lemma carries a soundness probe.

   Proved by a 3-phase ultracode fleet (wf_f77ae210-0f5): gen-inverse ->
   crt-existence -> crt-uniqueness, each phase a parallel multi-seat race feeding
   the next. Re-verified end-to-end by hand before landing.
   ============================================================================ *)

(* ============================================================================
   PHASE 1 (seat geninv0) : general modular inverse for coprimes
     gen_inverse : |- (!d. d dvd a ==> d dvd m ==> d = 1)
                      ==> 0 < m ==> ?b. cong m (a*b) 1
   Strategy : coprime_bezout(a,m) gives x,y with
       (a*x = m*y + 1)  OR  (m*y = a*x + 1).
     - LEFT  : a*x = m*y + 1  =>  a*x = 1 + m*y  => cong m (a*x) 1 via congR ; b := x.
     - RIGHT : m*y = a*x + 1  =>  a*x = -1 (mod m) ; b := x*(a*x), so
                 a*b = (a*x)^2 ; case on (a*x):
                   * a*x = 0 : then m*y = 1, a*b = 0, cong m 0 1 via congL (k := y).
                   * a*x = Suc k0 : square trick, cong m (a*b) 1 via congR.
   ============================================================================ *)
val () = out "GEN_INVERSE_BEGIN\n";

(* goal-existential builder : Ex b. cong m (mult a b) 1  (reuse mi shapes, with m) *)
fun gi_innerAbs (mt, at) =
  let val bF = Free("b_gi", natT)
  in Term.lambda bF (cong mt (mult at bF) oneC) end;
fun gi_goal (mt, at) = mkEx (gi_innerAbs (mt, at));
fun gi_mkGoal (mt, at) bWit hcong =
  exI_atS2 (gi_innerAbs (mt, at)) bWit hcong;

val () = out "GEN_INVERSE_HELPERS_READY\n";

val gen_inverse =
  let
    val aF = Free("a", natT);
    val mF = Free("m", natT);

    (* the two meta hypotheses *)
    val HcopP = jT (cb_cop (aF, mF));              (* Forall (%d. Imp (Conj (dvd d a)(dvd d m))(oeq d 1)) *)
    val Hcop  = Thm.assume (ctermS2 HcopP);
    val HposP = jT (lt ZeroC mF);                  (* 0 < m  (unused in body; kept in statement) *)
    val Hpos  = Thm.assume (ctermS2 HposP);

    (* ---- apply coprime_bezout at a := a, b := m ---- *)
    val cbInst = beta_norm (Drule.infer_instantiate ctxtS2
                   [(("a",0), ctermS2 aF), (("b",0), ctermS2 mF)] coprime_bezout);
    val cbDisjEx = Thm.implies_elim cbInst Hcop;   (* Ex x. Ex y. Disj (a*x = m*y+1)(m*y = a*x+1) *)

    val goalC = gi_goal (mF, aF);

    fun xbody xW (hExY : thm) =
      let
        fun ybody yW (hDisj : thm) =
          let
            val ax = mult aF xW;                                  (* a*x *)
            val dL = oeq ax (add (mult mF yW) oneC);              (* a*x = m*y + 1 *)
            val dR = oeq (mult mF yW) (add ax oneC);              (* m*y = a*x + 1 *)

            (* ===== CASE LEFT : a*x = m*y + 1.  Witness b := x. ===== *)
            val caseL =
              let
                val hL = Thm.assume (ctermS2 (jT dL));            (* a*x = m*y + 1 *)
                val cm = addcommS_at (mult mF yW, oneC);          (* (m*y + 1) = (1 + m*y) *)
                val axeq = oeq_trans OF [hL, cm];                 (* a*x = (1 + m*y) *)
                val congRabs = Abs("k", natT, oeq ax (add oneC (mult mF (Bound 0))));
                val exCongR  = exI_atS2 congRabs yW axeq;         (* congR m (a*x) 1 *)
                val hcong    = disjI2S2_at (congL mF ax oneC, congR mF ax oneC) exCongR;
                val res      = gi_mkGoal (mF, aF) xW hcong;       (* Ex b. cong m (a*b) 1, b := x *)
              in Thm.implies_intr (ctermS2 (jT dL)) res end;

            (* ===== CASE RIGHT : m*y = a*x + 1. ===== *)
            val caseR =
              let
                val hR = Thm.assume (ctermS2 (jT dR));            (* m*y = a*x + 1 *)
                val sq = mult ax ax;                              (* (a*x)^2 *)
                val Q  = mult ax yW;                              (* (a*x)*y *)
                val bWit = mult xW ax;                            (* x*(a*x) *)

                (* eq_ab : oeq (mult a bWit) sq  [ a*(x*ax) = (a*x)*ax = ax*ax ] *)
                val eq_ab = oeq_sym OF [mult_assoc_atS (aF, xW, ax)];   (* a*bWit = sq *)

                (* case-split on ax : (ax = 0) OR (Ex k. ax = Suc k) *)
                val axCases = dzosS_at ax;                        (* Disj (oeq ax 0) (Ex k. oeq ax (Suc k)) *)

                (* ---- SUBCASE ax = 0 ---- *)
                val subZero =
                  let
                    val hz = Thm.assume (ctermS2 (jT (oeq ax ZeroC)));   (* ax = 0 *)
                    (* a*bWit = sq = ax*ax = ax*0 = 0 *)
                    val sq_ax0 = mult_cong_rS (ax, ax, ZeroC) hz;        (* ax*ax = ax*0 *)
                    val ax0_0  = mult0rS_at ax;                          (* ax*0 = 0 *)
                    val sq0    = oeq_trans OF [sq_ax0, ax0_0];           (* sq = 0 *)
                    val ab0    = oeq_trans OF [eq_ab, sq0];              (* a*bWit = 0 *)
                    (* m*y = 1 : m*y = ax+1 = 0+1 = 1 *)
                    val rw1    = add_cong_lS (ax, ZeroC, oneC) hz;       (* (ax+1) = (0+1) *)
                    val z1     = add0S_at oneC;                          (* (0+1) = 1 *)
                    val my1    = oeq_trans OF [oeq_trans OF [hR, rw1], z1];  (* m*y = 1 *)
                    (* target congL m (a*bWit) 1 : Ex k. 1 = (a*bWit) + m*k, witness y *)
                    val abPlus = add_cong_lS (mult aF bWit, ZeroC, mult mF yW) ab0;  (* (a*bWit + m*y) = (0 + m*y) *)
                    val zmy    = add0S_at (mult mF yW);                  (* (0 + m*y) = m*y *)
                    val sumEq1 = oeq_trans OF [oeq_trans OF [abPlus, zmy], my1];  (* (a*bWit + m*y) = 1 *)
                    val oneEq  = oeq_sym OF [sumEq1];                    (* 1 = (a*bWit + m*y) *)
                    val congLabs = Abs("k", natT, oeq oneC (add (mult aF bWit) (mult mF (Bound 0))));
                    val exCongL  = exI_atS2 congLabs yW oneEq;           (* congL m (a*bWit) 1 *)
                    val hcong    = disjI1S2_at (congL mF (mult aF bWit) oneC, congR mF (mult aF bWit) oneC) exCongL;
                    val res      = gi_mkGoal (mF, aF) bWit hcong;        (* Ex b. cong m (a*b) 1 *)
                  in Thm.implies_intr (ctermS2 (jT (oeq ax ZeroC))) res end;

                (* ---- SUBCASE ax = Suc k0 : the square trick ---- *)
                val subSuc =
                  let
                    val hExSuc = Thm.assume (ctermS2 (jT (mkExSuc ax)));  (* Ex k. oeq ax (Suc k) *)
                    (* (i) : oeq (add sq ax) (mult m Q) -- same chain as mod_inverse, m for p *)
                    val c1 = mult_cong_rS (ax, mult mF yW, add ax oneC) hR;
                    val l1 = oeq_sym OF [mult_assoc_atS (ax, mF, yW)]; (* ax*(m*y) = (ax*m)*y *)
                    val l2 = mult_cong_lS (mult ax mF, mult mF ax, yW) (mult_comm_atS (ax, mF)); (* (ax*m)*y = (m*ax)*y *)
                    val l3 = mult_assoc_atS (mF, ax, yW);             (* (m*ax)*y = m*(ax*y) = m*Q *)
                    val lLHS = oeq_trans OF [oeq_trans OF [l1, l2], l3];  (* ax*(m*y) = m*Q *)
                    val r1 = left_distrib_atS (ax, ax, oneC);         (* ax*(ax+1) = ax*ax + ax*1 *)
                    val r2 = mult1rS_at ax;                           (* ax*1 = ax *)
                    val r2c= add_cong_rS (mult ax ax, mult ax oneC, ax) r2;  (* (ax*ax + ax*1) = (sq+ax) *)
                    val rRHS = oeq_trans OF [r1, r2c];                (* ax*(ax+1) = sq+ax *)
                    val mQ_eq = oeq_trans OF [oeq_trans OF [oeq_sym OF [lLHS], c1], rRHS];  (* m*Q = sq+ax *)
                    val iEq   = oeq_sym OF [mQ_eq];                   (* (i) : sq+ax = m*Q *)

                    fun axSucBody k0 (hk0 : thm) =                   (* hk0 : oeq ax (Suc k0) *)
                      let
                        val ms   = mult_Suc_atS (k0, yW);             (* (Suc k0)*y = y + k0*y *)
                        val qcong= mult_cong_lS (ax, suc k0, yW) hk0; (* ax*y = (Suc k0)*y *)
                        val qEq  = oeq_trans OF [qcong, ms];          (* Q = (y + k0*y) *)
                        val leY  = le_add_atS (yW, mult k0 yW);       (* le y (y + k0*y) *)
                        val qEqs = oeq_sym OF [qEq];                  (* (y+k0*y) = Q *)
                        val lePabs = Term.lambda (Free("z_le", natT)) (le yW (Free("z_le", natT)));
                        val leYQ = oeq_rewrite_atS (lePabs, add yW (mult k0 yW), Q) qEqs leY;  (* le y Q *)
                        val leAbs = Abs("p", natT, oeq Q (add yW (Bound 0)));
                        fun mbody mW (hm : thm) =                     (* hm : oeq Q (add y M) *)
                          let
                            (* LEFT value : (m*y + sq) = (1 + m*Q) *)
                            val L_a = addcommS_at (mult mF yW, sq);          (* (m*y + sq) = (sq + m*y) *)
                            val L_b = add_cong_rS (sq, mult mF yW, add ax oneC) hR;  (* (sq + m*y) = (sq + (ax+1)) *)
                            val L_c = oeq_sym OF [addassocS_at (sq, ax, oneC)];      (* (sq + (ax+1)) = ((sq+ax)+1) *)
                            val L_d = add_cong_lS (add sq ax, mult mF Q, oneC) iEq;  (* ((sq+ax)+1) = ((m*Q)+1) *)
                            val L_e = addcommS_at (mult mF Q, oneC);                 (* ((m*Q)+1) = (1 + m*Q) *)
                            val Lval = oeq_trans OF [oeq_trans OF [oeq_trans OF [oeq_trans OF [L_a, L_b], L_c], L_d], L_e]; (* (m*y + sq) = (1 + m*Q) *)
                            (* RIGHT value : (m*y + (1 + m*M)) = (1 + m*Q) *)
                            val R_a = addcommS_at (mult mF yW, add oneC (mult mF mW));  (* (m*y + (1 + m*M)) = ((1 + m*M) + m*y) *)
                            val R_b = addassocS_at (oneC, mult mF mW, mult mF yW);      (* ((1 + m*M) + m*y) = (1 + (m*M + m*y)) *)
                            val R_c = add_cong_rS (oneC, add (mult mF mW) (mult mF yW), add (mult mF yW) (mult mF mW))
                                        (addcommS_at (mult mF mW, mult mF yW));        (* (1 + (m*M + m*y)) = (1 + (m*y + m*M)) *)
                            val ld  = left_distrib_atS (mF, yW, mW);                   (* m*(y+M) = (m*y + m*M) *)
                            val pQeq= mult_cong_rS (mF, Q, add yW mW) hm;             (* m*Q = m*(y+M) *)
                            val pyM_mQ = oeq_sym OF [oeq_trans OF [pQeq, ld]];        (* (m*y + m*M) = m*Q *)
                            val R_d = add_cong_rS (oneC, add (mult mF yW) (mult mF mW), mult mF Q) pyM_mQ;  (* (1 + (m*y+m*M)) = (1 + m*Q) *)
                            val Rval = oeq_trans OF [oeq_trans OF [oeq_trans OF [R_a, R_b], R_c], R_d];  (* (m*y + (1+m*M)) = (1 + m*Q) *)
                            val both = oeq_trans OF [Lval, oeq_sym OF [Rval]];        (* (m*y + sq) = (m*y + (1 + m*M)) *)
                            val sqEq = add_left_cancel_atS (mult mF yW, sq, add oneC (mult mF mW)) both;  (* oeq sq (add 1 (m*M)) *)
                            val abEq = oeq_trans OF [eq_ab, sqEq];                    (* oeq (a*bWit) (add 1 (m*M)) *)
                            val congRabs = Abs("k", natT, oeq (mult aF bWit) (add oneC (mult mF (Bound 0))));
                            val exCongR  = exI_atS2 congRabs mW abEq;                 (* congR m (a*bWit) 1 *)
                            val hcong    = disjI2S2_at (congL mF (mult aF bWit) oneC, congR mF (mult aF bWit) oneC) exCongR;
                            val res      = gi_mkGoal (mF, aF) bWit hcong;            (* Ex b. cong m (a*b) 1 *)
                          in res end;
                        val res = exE_elimS2 (leAbs, goalC) leYQ "M_gi" mbody;
                      in res end;
                    val resSuc = exE_elimS2 (Abs("k", natT, oeq ax (suc (Bound 0))), goalC) hExSuc "k0_gi" axSucBody;
                  in Thm.implies_intr (ctermS2 (jT (mkExSuc ax))) resSuc end;

                (* combine the two ax-subcases *)
                val resR = disjE_elimS2 (oeq ax ZeroC, mkExSuc ax, goalC) axCases subZero subSuc;
              in Thm.implies_intr (ctermS2 (jT dR)) resR end;

            val res = disjE_elimS2 (dL, dR, goalC) hDisj caseL caseR;
          in res end;
        val g = exE_elimS2 (cb_innerAbs (aF, mF, xW), goalC) hExY "y_gi" ybody;
      in g end;
    val bodyGoal = exE_elimS2 (cb_outerAbs (aF, mF), goalC) cbDisjEx "x_gi" xbody;
    (* discharge the two hypotheses -> meta implications (0<m outermost-but-one) *)
    val disch1 = Thm.implies_intr (ctermS2 HposP) bodyGoal;
    val disch2 = Thm.implies_intr (ctermS2 HcopP) disch1;
  in varify disch2 end;

val () = out "GEN_INVERSE_PROVED\n";

(* ---- validation ---- *)
val aVgi = Var (("a",0), natT);
val mVgi = Var (("m",0), natT);
val gen_inverse_intended =
  Logic.mk_implies (jT (cb_cop (aVgi, mVgi)),
    Logic.mk_implies (jT (lt ZeroC mVgi),
      jT (gi_goal (mVgi, aVgi))));
val r_gi = checkS2 ("gen_inverse", gen_inverse, gen_inverse_intended);
val () = if r_gi then out "OK gen_inverse\n" else out "FAIL gen_inverse\n";

(* soundness probe : dropping the coprimality hypothesis is unsound *)
val probe_gi =
  let
    val bogus = Logic.mk_implies (jT (lt ZeroC mVgi), jT (gi_goal (mVgi, aVgi)));
  in not ((Thm.prop_of gen_inverse) aconv bogus) end;
val () = if r_gi andalso probe_gi then out "PROBE_OK\n" else out "PROBE_UNSOUND\n";
val () = if r_gi andalso probe_gi then out "GEN_INVERSE_OK\n" else out "GEN_INVERSE_FAILED\n";

(* ============================================================================
   PHASE 2 (seat crtex0) : Chinese Remainder Theorem, EXISTENCE
     crt_exists : |- (!d. d dvd m ==> d dvd n ==> d = 1)
                     ==> 0 < m ==> 0 < n
                     ==> !a. !b. ?x. cong m x a /\ cong n x b
   Construction (all in N, no subtraction):
     gen_inverse(n,m) : coprime(n,m) ==> 0<m ==> ?s. cong m (n*s) 1   [symmetry of cop]
     gen_inverse(m,n) : coprime(m,n) ==> 0<n ==> ?t. cong n (m*t) 1
     x := a*(n*s) + b*(m*t).
       cong m x a : a*(n*s) ~ a*1 = a ;  b*(m*t) ~ b*0 = 0 ; sum ~ a+0 = a.
       cong n x b : symmetric.
   ============================================================================ *)
val () = out "CRT_EXISTS_BEGIN\n";

(* ---- cong-lemma instantiators on the FINAL context ctxtS2 ---- *)
val cong_refl_vS  = varify cong_refl;
val cong_add_vS   = varify cong_add;
val cong_mult_vS  = varify cong_mult;
val cong_trans_vS = varify cong_trans;

fun cong_refl_atS (mt, at) = beta_norm (Drule.infer_instantiate ctxtS2
      [(("m",0), ctermS2 mt), (("a",0), ctermS2 at)] cong_refl_vS);

fun cong_add_atS (mt, a1, a2, b1, b2) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mt), (("a",0), ctermS2 a1), (("a2",0), ctermS2 a2),
         (("b",0), ctermS2 b1), (("b2",0), ctermS2 b2)] cong_add_vS)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

fun cong_mult_atS (mt, a1, a2, b1, b2) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mt), (("a",0), ctermS2 a1), (("a2",0), ctermS2 a2),
         (("b",0), ctermS2 b1), (("b2",0), ctermS2 b2)] cong_mult_vS)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

fun cong_trans_atS (mt, at, bt, ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mt), (("a",0), ctermS2 at), (("b",0), ctermS2 bt),
         (("c",0), ctermS2 ct)] cong_trans_vS)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* eq_to_congS (m, Y, Z) (heq : oeq Y Z) : jT (cong m Y Z)
   via cong_introL with witness 0 :  Z = Y + m*0  from  Y = Z (sym) chained with
   Y = (Y + m*0).  cong_introL/R are ctxtC-built but produce ordinary thms. *)
fun eq_to_congS (mt, Yt, Zt) heq =
  let
    val m0   = mult0rS_at mt;                                   (* (m*0) = 0 *)
    val cg   = add_cong_rS (Yt, mult mt ZeroC, ZeroC) m0;       (* (Y + m*0) = (Y + 0) *)
    val a0   = add0rS_at Yt;                                    (* (Y + 0) = Y *)
    val YeqYm0 = oeq_sym OF [oeq_trans OF [cg, a0]];            (* Y = (Y + m*0) *)
    val ZeqYm0 = oeq_trans OF [oeq_sym OF [heq], YeqYm0];       (* Z = (Y + m*0) *)
  in cong_introL (mt, Yt, Zt, ZeroC) ZeqYm0 end;               (* jT (cong m Y Z) *)

(* cong_tidy_right (m, X, Y, Z) (hc : cong m X Y) (heq : oeq Y Z) : cong m X Z *)
fun cong_tidy_right (mt, Xt, Yt, Zt) hc heq =
  cong_trans_atS (mt, Xt, Yt, Zt) hc (eq_to_congS (mt, Yt, Zt) heq);

val () = out "CRT_HELPERS_READY\n";

(* ---- statement helpers ---- *)
fun crt_inner (mt, nt, at, bt) =                    (* %x. Conj (cong m x a)(cong n x b) *)
  let val xF = Free("x_crt", natT)
  in Term.lambda xF (mkConj (cong mt xF at) (cong nt xF bt)) end;
fun crt_exGoal (mt, nt, at, bt) = mkEx (crt_inner (mt, nt, at, bt));  (* Ex x. ... *)
fun crt_bAbs (mt, nt, at) =                         (* %b. Ex x. ... *)
  let val bF = Free("b_crt", natT)
  in Term.lambda bF (crt_exGoal (mt, nt, at, bF)) end;
fun crt_aAbs (mt, nt) =                             (* %a. Forall (%b. Ex x. ...) *)
  let val aF = Free("a_crt", natT)
  in Term.lambda aF (mkForall (crt_bAbs (mt, nt, aF))) end;
fun crt_goal (mt, nt) = mkForall (crt_aAbs (mt, nt));

val () = out "CRT_GOAL_READY\n";

val crt_exists =
  let
    val mF = Free("m", natT);
    val nF = Free("n", natT);

    (* hypotheses *)
    val HcopP  = jT (cb_cop (mF, nF));                 (* Forall(%d. Imp(Conj(dvd d m)(dvd d n))(oeq d 1)) *)
    val Hcop   = Thm.assume (ctermS2 HcopP);
    val HposmP = jT (lt ZeroC mF);
    val Hposm  = Thm.assume (ctermS2 HposmP);
    val HposnP = jT (lt ZeroC nF);
    val Hposn  = Thm.assume (ctermS2 HposnP);

    (* ---- coprimality is symmetric : Hcop' : cb_cop (n, m) ---- *)
    val HcopSym =
      let
        val dF   = Free("d_sw", natT);
        val cnjP = jT (mkConj (dvd dF nF) (dvd dF mF));        (* Conj (dvd d n)(dvd d m) *)
        val hCnj = Thm.assume (ctermS2 cnjP);
        val ddn  = conjunct1_atS2 (dvd dF nF, dvd dF mF) hCnj; (* dvd d n *)
        val ddm  = conjunct2_atS2 (dvd dF nF, dvd dF mF) hCnj; (* dvd d m *)
        val cnj2 = conjI_atS2 (dvd dF mF, dvd dF nF) ddm ddn;  (* Conj (dvd d m)(dvd d n) *)
        val hImp = allE_atS2 (cb_copAbs (mF, nF)) dF Hcop;     (* Imp(Conj(dvd d m)(dvd d n))(oeq d 1) *)
        val d1   = mp_atS2 (mkConj (dvd dF mF) (dvd dF nF), oeq dF oneC) hImp cnj2;  (* oeq d 1 *)
        val metaImp = Thm.implies_intr (ctermS2 cnjP) d1;
        val objImp  = impI_atS2 (mkConj (dvd dF nF) (dvd dF mF), oeq dF oneC) metaImp;
        val minor   = Thm.forall_intr (ctermS2 dF) objImp;
      in allI_atS2 (cb_copAbs (nF, mF)) minor end;             (* Forall(%d. Imp(Conj(dvd d n)(dvd d m))(oeq d 1)) *)

    (* ---- gen_inverse(n, m) : ?s. cong m (n*s) 1 ---- *)
    val giNM = beta_norm (Drule.infer_instantiate ctxtS2
                 [(("a",0), ctermS2 nF), (("m",0), ctermS2 mF)] gen_inverse);
    val sExGoal = gi_goal (mF, nF);                            (* Ex b. cong m (n*b) 1 *)
    val sEx = Thm.implies_elim (Thm.implies_elim giNM HcopSym) Hposm;  (* jT (Ex b. cong m (n*b) 1) *)

    (* ---- gen_inverse(m, n) : ?t. cong n (m*t) 1 ---- *)
    val giMN = beta_norm (Drule.infer_instantiate ctxtS2
                 [(("a",0), ctermS2 mF), (("m",0), ctermS2 nF)] gen_inverse);
    val tExGoal = gi_goal (nF, mF);                            (* Ex b. cong n (m*b) 1 *)
    val tEx = Thm.implies_elim (Thm.implies_elim giMN Hcop) Hposn;  (* jT (Ex b. cong n (m*b) 1) *)

    val goalC = crt_goal (mF, nF);

    (* ---- body : exE the inverse s, then exE the inverse t, then prove !a.!b.Ex x ---- *)
    fun sBody sW (hs : thm) =                                  (* hs : cong m (n*s) 1 *)
      let
        fun tBody tW (ht : thm) =                              (* ht : cong n (m*t) 1 *)
          let
            val ns = mult nF sW;                              (* n*s *)
            val mt = mult mF tW;                              (* m*t *)

            (* cong m (m*t) 0  via congR witness t : m*t = 0 + m*t *)
            val a0mt   = add0S_at mt;                          (* (0 + m*t) = m*t *)
            val mt_eq  = oeq_sym OF [a0mt];                    (* m*t = (0 + m*t) *)
            val cong_mt0 = cong_introR (mF, mt, ZeroC, tW) mt_eq;  (* cong m (m*t) 0 *)

            (* cong n (n*s) 0  via congR witness s : n*s = 0 + n*s *)
            val a0ns   = add0S_at ns;                          (* (0 + n*s) = n*s *)
            val ns_eq  = oeq_sym OF [a0ns];                    (* n*s = (0 + n*s) *)
            val cong_ns0 = cong_introR (nF, ns, ZeroC, sW) ns_eq;  (* cong n (n*s) 0 *)

            (* the predicate to prove for each a : Forall(%b. Ex x. Conj(cong m x a)(cong n x b)) *)
            fun bBody aF bF =
              let
                val xWit = add (mult aF ns) (mult bF mt);     (* a*(n*s) + b*(m*t) *)

                (* ===== cong m xWit a ===== *)
                (* term1 : cong m (a*(n*s)) a *)
                val cmRefl_a = cong_refl_atS (mF, aF);                          (* cong m a a *)
                val cm_t1_0  = cong_mult_atS (mF, aF, aF, ns, oneC) cmRefl_a hs; (* cong m (a*(n*s)) (a*1) *)
                val a1eqa    = mult1rS_at aF;                                   (* (a*1) = a *)
                val cm_t1    = cong_tidy_right (mF, mult aF ns, mult aF oneC, aF) cm_t1_0 a1eqa;
                                                                               (* cong m (a*(n*s)) a *)
                (* term2 : cong m (b*(m*t)) 0 *)
                val cmRefl_b = cong_refl_atS (mF, bF);                          (* cong m b b *)
                val cm_t2_b0 = cong_mult_atS (mF, bF, bF, mt, ZeroC) cmRefl_b cong_mt0; (* cong m (b*(m*t)) (b*0) *)
                val b0eq0    = mult0rS_at bF;                                   (* (b*0) = 0 *)
                val cm_t2    = cong_tidy_right (mF, mult bF mt, mult bF ZeroC, ZeroC) cm_t2_b0 b0eq0;
                                                                               (* cong m (b*(m*t)) 0 *)
                (* sum : cong m xWit (a+0) *)
                val cm_sum   = cong_add_atS (mF, mult aF ns, aF, mult bF mt, ZeroC) cm_t1 cm_t2;
                                                                               (* cong m xWit (a+0) *)
                val a0eqa    = add0rS_at aF;                                    (* (a+0) = a *)
                val congM    = cong_tidy_right (mF, xWit, add aF ZeroC, aF) cm_sum a0eqa;
                                                                               (* cong m xWit a *)

                (* ===== cong n xWit b ===== *)
                (* term1 : cong n (a*(n*s)) 0 *)
                val cnRefl_a = cong_refl_atS (nF, aF);                          (* cong n a a *)
                val cn_t1_a0 = cong_mult_atS (nF, aF, aF, ns, ZeroC) cnRefl_a cong_ns0; (* cong n (a*(n*s)) (a*0) *)
                val a0eq0    = mult0rS_at aF;                                   (* (a*0) = 0 *)
                val cn_t1    = cong_tidy_right (nF, mult aF ns, mult aF ZeroC, ZeroC) cn_t1_a0 a0eq0;
                                                                               (* cong n (a*(n*s)) 0 *)
                (* term2 : cong n (b*(m*t)) b *)
                val cnRefl_b = cong_refl_atS (nF, bF);                          (* cong n b b *)
                val cn_t2_0  = cong_mult_atS (nF, bF, bF, mt, oneC) cnRefl_b ht; (* cong n (b*(m*t)) (b*1) *)
                val b1eqb    = mult1rS_at bF;                                   (* (b*1) = b *)
                val cn_t2    = cong_tidy_right (nF, mult bF mt, mult bF oneC, bF) cn_t2_0 b1eqb;
                                                                               (* cong n (b*(m*t)) b *)
                (* sum : cong n xWit (0 + b) *)
                val cn_sum   = cong_add_atS (nF, mult aF ns, ZeroC, mult bF mt, bF) cn_t1 cn_t2;
                                                                               (* cong n xWit (0 + b) *)
                val zbeqb    = add0S_at bF;                                     (* (0 + b) = b *)
                val congN    = cong_tidy_right (nF, xWit, add ZeroC bF, bF) cn_sum zbeqb;
                                                                               (* cong n xWit b *)

                (* conjoin + exI on x *)
                val conj = conjI_atS2 (cong mF xWit aF, cong nF xWit bF) congM congN;  (* Conj(cong m x a)(cong n x b) *)
                val exX  = exI_atS2 (crt_inner (mF, nF, aF, bF)) xWit conj;            (* Ex x. ... *)
              in exX end;

            (* !a. !b. Ex x. ... *)
            fun aBody aF =
              let
                val bF = Free("b_crt", natT);
                val inner = bBody aF bF;                          (* Ex x. Conj(cong m x a)(cong n x b) *)
                val minorB = Thm.forall_intr (ctermS2 bF) inner;  (* !!b. Ex x. ... *)
              in allI_atS2 (crt_bAbs (mF, nF, aF)) minorB end;    (* Forall(%b. Ex x. ...) *)

            val aF = Free("a_crt", natT);
            val innerA = aBody aF;                                (* Forall(%b. Ex x. ...) *)
            val minorA = Thm.forall_intr (ctermS2 aF) innerA;     (* !!a. Forall(%b. ...) *)
          in allI_atS2 (crt_aAbs (mF, nF)) minorA end;            (* Forall(%a. Forall(%b. ...)) *)

        val g = exE_elimS2 (gi_innerAbs (nF, mF), goalC) tEx "t_crt" tBody;
      in g end;
    val bodyGoal = exE_elimS2 (gi_innerAbs (mF, nF), goalC) sEx "s_crt" sBody;

    (* discharge the three hypotheses (innermost first: 0<n, then 0<m, then coprime) *)
    val disch1 = Thm.implies_intr (ctermS2 HposnP) bodyGoal;
    val disch2 = Thm.implies_intr (ctermS2 HposmP) disch1;
    val disch3 = Thm.implies_intr (ctermS2 HcopP) disch2;
  in varify disch3 end;

val () = out "CRT_EXISTS_PROVED\n";

(* ---- validation ---- *)
val mVcrt = Var (("m",0), natT);
val nVcrt = Var (("n",0), natT);
val crt_exists_intended =
  Logic.mk_implies (jT (cb_cop (mVcrt, nVcrt)),
    Logic.mk_implies (jT (lt ZeroC mVcrt),
      Logic.mk_implies (jT (lt ZeroC nVcrt),
        jT (crt_goal (mVcrt, nVcrt)))));
val r_crt = checkS2 ("crt_exists", crt_exists, crt_exists_intended);
val () = if r_crt then out "OK crt_exists\n" else out "FAIL crt_exists\n";

(* soundness probe : dropping the coprimality hypothesis is unsound *)
val probe_crt =
  let
    val bogus = Logic.mk_implies (jT (lt ZeroC mVcrt),
                  Logic.mk_implies (jT (lt ZeroC nVcrt),
                    jT (crt_goal (mVcrt, nVcrt))));
  in not ((Thm.prop_of crt_exists) aconv bogus) end;
val () = if r_crt andalso probe_crt then out "PROBE_OK\n" else out "PROBE_UNSOUND\n";
val () = if r_crt andalso probe_crt then out "CRT_EXISTS_OK\n" else out "CRT_EXISTS_FAILED\n";
(* ============================================================================
   PHASE 3 (seat crtuq0) : CRT UNIQUENESS
     gauss            : (!d. d dvd n ==> d dvd m ==> d=1) ==> n dvd (m*c) ==> n dvd c
     coprime_mult_dvd : (!d. d dvd m ==> d dvd n ==> d=1) ==> m dvd k ==> n dvd k ==> (m*n) dvd k
     crt_unique       : (!d. d dvd m ==> d dvd n ==> d=1) ==> cong m x y ==> cong n x y ==> cong (m*n) x y
   ============================================================================ *)
val () = out "CRT_UNIQUE_BEGIN\n";

(* ---- add_eq_zero on ctxtS2 : oeq (add a b) 0 ==> oeq a 0 / oeq b 0 ---- *)
val add_eq_zero_left_vS = varify add_eq_zero_left;   (* jT (oeq (add ?a ?b) 0) ==> jT (oeq ?a 0) *)
(* right variant : derive via add_comm, build a 0-hyp varified lemma *)
val add_eq_zero_right_vS =
  let
    val aF = Free("a_ezr", natT);
    val bF = Free("b_ezr", natT);
    val hP = jT (oeq (add aF bF) ZeroC);
    val h  = Thm.assume (ctermS2 hP);
    val comm = addcommS_at (bF, aF);                  (* oeq (add b a)(add a b) *)
    val hcomm = oeq_trans OF [comm, h];              (* oeq (add b a) 0 *)
    val res = add_eq_zero_left_vS OF [hcomm];        (* oeq b 0 *)
  in varify (Thm.implies_intr (ctermS2 hP) res) end; (* jT (oeq (add ?a ?b) 0) ==> jT (oeq ?b 0) *)

(* ---- coprimality swap : jT (cb_cop (a,b)) -> jT (cb_cop (b,a)) ----
   (copied from crt_exists' HcopSym pattern) *)
fun cop_swap (aF, bF) hCop =
  let
    val dF   = Free("d_sw", natT);
    val cnjP = jT (mkConj (dvd dF bF) (dvd dF aF));          (* Conj (dvd d b)(dvd d a) *)
    val hCnj = Thm.assume (ctermS2 cnjP);
    val ddb  = conjunct1_atS2 (dvd dF bF, dvd dF aF) hCnj;   (* dvd d b *)
    val dda  = conjunct2_atS2 (dvd dF bF, dvd dF aF) hCnj;   (* dvd d a *)
    val cnj2 = conjI_atS2 (dvd dF aF, dvd dF bF) dda ddb;    (* Conj (dvd d a)(dvd d b) *)
    val hImp = allE_atS2 (cb_copAbs (aF, bF)) dF hCop;       (* Imp(Conj(dvd d a)(dvd d b))(oeq d 1) *)
    val d1   = mp_atS2 (mkConj (dvd dF aF) (dvd dF bF), oeq dF oneC) hImp cnj2;  (* oeq d 1 *)
    val metaImp = Thm.implies_intr (ctermS2 cnjP) d1;
    val objImp  = impI_atS2 (mkConj (dvd dF bF) (dvd dF aF), oeq dF oneC) metaImp;
    val minor   = Thm.forall_intr (ctermS2 dF) objImp;
  in allI_atS2 (cb_copAbs (bF, aF)) minor end;              (* Forall(%d. Imp(Conj(dvd d b)(dvd d a))(oeq d 1)) *)

val () = out "CRT_UNIQUE_HELPERS_READY\n";

(* ============================================================================
   gauss : jT (cb_cop (n,m)) ==> jT (dvd n (mult m c)) ==> jT (dvd n c)
   ============================================================================ *)
val gauss =
  let
    val nF = Free("n", natT);
    val mF = Free("m", natT);
    val cF = Free("c", natT);

    val HcopP  = jT (cb_cop (nF, mF));
    val Hcop   = Thm.assume (ctermS2 HcopP);
    val HdvdP  = jT (dvd nF (mult mF cF));            (* Ex k. (m*c) = n*k *)
    val Hdvd   = Thm.assume (ctermS2 HdvdP);

    (* coprime_bezout at a := n, b := m : Ex x. Ex y. Disj (n*x = m*y+1)(m*y = n*x+1) *)
    val cbInst = beta_norm (Drule.infer_instantiate ctxtS2
                   [(("a",0), ctermS2 nF), (("b",0), ctermS2 mF)] coprime_bezout);
    val cbDisjEx = Thm.implies_elim cbInst Hcop;

    val goalC = dvd nF cF;                            (* target : dvd n c *)

    (* exE the bezout witnesses x:=u, y:=v ; then exE the dvd witness j ;
       case on the bezout disjunction. *)
    fun uBody uW (hExV : thm) =
      let
        fun vBody vW (hDisj : thm) =
          let
            (* the two bezout disjuncts (with a:=n, b:=m) *)
            val dL = oeq (mult nF uW) (add (mult mF vW) oneC);   (* n*u = m*v + 1 *)
            val dR = oeq (mult mF vW) (add (mult nF uW) oneC);   (* m*v = n*u + 1 *)

            (* exE the dvd witness j : (m*c) = n*j *)
            val dvdAbs = Abs("k", natT, oeq (mult mF cF) (mult nF (Bound 0)));
            fun jBody jW (hj : thm) =                  (* hj : oeq (m*c) (n*j) *)
              let
                (* common : dvd n (c*(n*u))  via witness (c*u) *)
                val cnu = mult cF (mult nF uW);                 (* c*(n*u) *)
                val cnu_e1 = oeq_sym OF [mult_assoc_atS (cF, nF, uW)];           (* c*(n*u) = (c*n)*u *)
                val cnu_e2 = mult_cong_lS (mult cF nF, mult nF cF, uW) (mult_comm_atS (cF, nF)); (* (c*n)*u = (n*c)*u *)
                val cnu_e3 = mult_assoc_atS (nF, cF, uW);                        (* (n*c)*u = n*(c*u) *)
                val cnu_eq = oeq_trans OF [oeq_trans OF [cnu_e1, cnu_e2], cnu_e3]; (* c*(n*u) = n*(c*u) *)
                val dvd_cnu = dvd_introS (nF, cnu, mult cF uW) cnu_eq;           (* dvd n (c*(n*u)) *)

                (* common : dvd n (c*(m*v))  via witness (j*v) *)
                val cmv = mult cF (mult mF vW);                 (* c*(m*v) *)
                val cmv_e1 = oeq_sym OF [mult_assoc_atS (cF, mF, vW)];           (* c*(m*v) = (c*m)*v *)
                val cmv_e2 = mult_cong_lS (mult cF mF, mult mF cF, vW) (mult_comm_atS (cF, mF)); (* (c*m)*v = (m*c)*v *)
                val cmv_e3 = mult_cong_lS (mult mF cF, mult nF jW, vW) hj;       (* (m*c)*v = (n*j)*v *)
                val cmv_e4 = mult_assoc_atS (nF, jW, vW);                        (* (n*j)*v = n*(j*v) *)
                val cmv_eq = oeq_trans OF [oeq_trans OF [oeq_trans OF [cmv_e1, cmv_e2], cmv_e3], cmv_e4]; (* c*(m*v) = n*(j*v) *)
                val dvd_cmv = dvd_introS (nF, cmv, mult jW vW) cmv_eq;           (* dvd n (c*(m*v)) *)

                (* %z. dvd n z, for rewriting the dvd target *)
                val zF = Free("z_dvd", natT);
                val ndvdAbs = Term.lambda zF (dvd nF zF);

                (* ===== CASE LEFT : n*u = m*v + 1 ===== *)
                val caseL =
                  let
                    val hL = Thm.assume (ctermS2 (jT dL));
                    (* c*(n*u) = c*(m*v + 1) = c*(m*v) + c*1 = c*(m*v) + c *)
                    val s1 = mult_cong_rS (cF, mult nF uW, add (mult mF vW) oneC) hL;  (* c*(n*u) = c*(m*v + 1) *)
                    val s2 = left_distrib_atS (cF, mult mF vW, oneC);                  (* c*(m*v + 1) = (c*(m*v) + c*1) *)
                    val s3 = mult1rS_at cF;                                            (* c*1 = c *)
                    val s3c= add_cong_rS (mult cF (mult mF vW), mult cF oneC, cF) s3;  (* (c*(m*v)+c*1) = (c*(m*v)+c) *)
                    val E  = oeq_trans OF [oeq_trans OF [s1, s2], s3c];                (* c*(n*u) = (c*(m*v) + c) *)
                    (* dvd n (c*(m*v) + c) by rewriting dvd_cnu via E *)
                    val dvd_sum = oeq_rewrite_atS (ndvdAbs, cnu, add cmv cF) E dvd_cnu; (* dvd n (c*(m*v) + c) *)
                    val res = dvd_diff_atS (nF, cmv, cF) dvd_cmv dvd_sum;              (* dvd n c *)
                  in Thm.implies_intr (ctermS2 (jT dL)) res end;

                (* ===== CASE RIGHT : m*v = n*u + 1 ===== *)
                val caseR =
                  let
                    val hR = Thm.assume (ctermS2 (jT dR));
                    (* c*(m*v) = c*(n*u + 1) = c*(n*u) + c*1 = c*(n*u) + c *)
                    val s1 = mult_cong_rS (cF, mult mF vW, add (mult nF uW) oneC) hR;  (* c*(m*v) = c*(n*u + 1) *)
                    val s2 = left_distrib_atS (cF, mult nF uW, oneC);                  (* c*(n*u + 1) = (c*(n*u) + c*1) *)
                    val s3 = mult1rS_at cF;                                            (* c*1 = c *)
                    val s3c= add_cong_rS (mult cF (mult nF uW), mult cF oneC, cF) s3;  (* (c*(n*u)+c*1) = (c*(n*u)+c) *)
                    val E  = oeq_trans OF [oeq_trans OF [s1, s2], s3c];                (* c*(m*v) = (c*(n*u) + c) *)
                    val dvd_sum = oeq_rewrite_atS (ndvdAbs, cmv, add cnu cF) E dvd_cmv; (* dvd n (c*(n*u) + c) *)
                    val res = dvd_diff_atS (nF, cnu, cF) dvd_cnu dvd_sum;              (* dvd n c *)
                  in Thm.implies_intr (ctermS2 (jT dR)) res end;

                val res = disjE_elimS2 (dL, dR, goalC) hDisj caseL caseR;
              in res end;
            val g = exE_elimS2 (dvdAbs, goalC) Hdvd "j_g" jBody;
          in g end;
        val g = exE_elimS2 (cb_innerAbs (nF, mF, uW), goalC) hExV "v_g" vBody;
      in g end;
    val bodyGoal = exE_elimS2 (cb_outerAbs (nF, mF), goalC) cbDisjEx "u_g" uBody;
    val disch1 = Thm.implies_intr (ctermS2 HdvdP) bodyGoal;
    val disch2 = Thm.implies_intr (ctermS2 HcopP) disch1;
  in varify disch2 end;

val () = out "GAUSS_PROVED\n";

(* ---- validation ---- *)
val nVg = Var (("n",0), natT);
val mVg = Var (("m",0), natT);
val cVg = Var (("c",0), natT);
val gauss_intended =
  Logic.mk_implies (jT (cb_cop (nVg, mVg)),
    Logic.mk_implies (jT (dvd nVg (mult mVg cVg)),
      jT (dvd nVg cVg)));
val r_gauss = checkS2 ("gauss", gauss, gauss_intended);
val () = if r_gauss then out "OK gauss\n" else out "FAIL gauss\n";

(* soundness probe : dropping coprimality is unsound (n=2,m=4 has 2|4*c but not 2|c for odd c) *)
val probe_gauss =
  let val bogus = Logic.mk_implies (jT (dvd nVg (mult mVg cVg)), jT (dvd nVg cVg))
  in not ((Thm.prop_of gauss) aconv bogus) end;
val () = if r_gauss andalso probe_gauss then out "PROBE_OK\n" else out "PROBE_UNSOUND\n";

(* re-varify gauss for instantiation inside coprime_mult_dvd *)
val gauss_vS = gauss;   (* already varified *)
fun gauss_atS (nt, mt, ct) hcop hdvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("n",0), ctermS2 nt), (("m",0), ctermS2 mt), (("c",0), ctermS2 ct)] gauss_vS)
  in Thm.implies_elim (Thm.implies_elim inst hcop) hdvd end;

(* ============================================================================
   coprime_mult_dvd : jT (cb_cop (m,n)) ==> jT (dvd m k) ==> jT (dvd n k) ==> jT (dvd (m*n) k)
   ============================================================================ *)
val coprime_mult_dvd =
  let
    val mF = Free("m", natT);
    val nF = Free("n", natT);
    val kF = Free("k", natT);

    val HcopP  = jT (cb_cop (mF, nF));
    val Hcop   = Thm.assume (ctermS2 HcopP);
    val HmkP   = jT (dvd mF kF);               (* Ex e. k = m*e *)
    val Hmk    = Thm.assume (ctermS2 HmkP);
    val HnkP   = jT (dvd nF kF);               (* Ex f. k = n*f *)
    val Hnk    = Thm.assume (ctermS2 HnkP);

    val goalC = dvd (mult mF nF) kF;           (* target : dvd (m*n) k *)

    (* coprimality swapped for gauss : cb_cop(n,m) *)
    val HcopNM = cop_swap (mF, nF) Hcop;       (* jT (cb_cop (n,m)) *)

    (* exE Hmk : witness c, hc : k = m*c *)
    val mkAbs = Abs("e", natT, oeq kF (mult mF (Bound 0)));
    fun cBody cW (hc : thm) =                   (* hc : oeq k (m*c) *)
      let
        (* dvd n (m*c) : rewrite Hnk (dvd n k) via hc *)
        val zF = Free("z_dvdn", natT);
        val ndvdAbs = Term.lambda zF (dvd nF zF);
        val dvd_n_mc = oeq_rewrite_atS (ndvdAbs, kF, mult mF cW) hc Hnk;   (* dvd n (m*c) *)
        (* gauss(n,m,c) : dvd n c *)
        val dvd_n_c = gauss_atS (nF, mF, cW) HcopNM dvd_n_mc;              (* dvd n c *)
        (* exE dvd n c : witness e, he : c = n*e *)
        val ncAbs = Abs("e2", natT, oeq cW (mult nF (Bound 0)));
        fun eBody eW (he : thm) =               (* he : oeq c (n*e) *)
          let
            (* k = m*c = m*(n*e) = (m*n)*e *)
            val t1 = mult_cong_rS (mF, cW, mult nF eW) he;            (* m*c = m*(n*e) *)
            val t2 = oeq_sym OF [mult_assoc_atS (mF, nF, eW)];        (* m*(n*e) = (m*n)*e *)
            val keq = oeq_trans OF [oeq_trans OF [hc, t1], t2];       (* k = (m*n)*e *)
            val res = dvd_introS (mult mF nF, kF, eW) keq;            (* dvd (m*n) k *)
          in res end;
        val g = exE_elimS2 (ncAbs, goalC) dvd_n_c "e_cmd" eBody;
      in g end;
    val bodyGoal = exE_elimS2 (mkAbs, goalC) Hmk "c_cmd" cBody;
    val disch1 = Thm.implies_intr (ctermS2 HnkP) bodyGoal;
    val disch2 = Thm.implies_intr (ctermS2 HmkP) disch1;
    val disch3 = Thm.implies_intr (ctermS2 HcopP) disch2;
  in varify disch3 end;

val () = out "COPRIME_MULT_DVD_PROVED\n";

(* ---- validation ---- *)
val mVc = Var (("m",0), natT);
val nVc = Var (("n",0), natT);
val kVc = Var (("k",0), natT);
val coprime_mult_dvd_intended =
  Logic.mk_implies (jT (cb_cop (mVc, nVc)),
    Logic.mk_implies (jT (dvd mVc kVc),
      Logic.mk_implies (jT (dvd nVc kVc),
        jT (dvd (mult mVc nVc) kVc))));
val r_cmd = checkS2 ("coprime_mult_dvd", coprime_mult_dvd, coprime_mult_dvd_intended);
val () = if r_cmd then out "OK coprime_mult_dvd\n" else out "FAIL coprime_mult_dvd\n";

val probe_cmd =
  let val bogus = Logic.mk_implies (jT (dvd mVc kVc),
                    Logic.mk_implies (jT (dvd nVc kVc),
                      jT (dvd (mult mVc nVc) kVc)))
  in not ((Thm.prop_of coprime_mult_dvd) aconv bogus) end;
val () = if r_cmd andalso probe_cmd then out "PROBE_OK\n" else out "PROBE_UNSOUND\n";

(* instantiator for coprime_mult_dvd on ctxtS2 *)
fun cmd_atS (mt, nt, kt) hcop hmk hnk =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mt), (("n",0), ctermS2 nt), (("k",0), ctermS2 kt)] coprime_mult_dvd)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hcop) hmk) hnk end;

(* ============================================================================
   crt_unique : jT (cb_cop (m,n)) ==> jT (cong m x y) ==> jT (cong n x y)
                ==> jT (cong (m*n) x y)
   ============================================================================ *)
(* capture-avoiding congL/congR predicate abstractions (matching the base's
   congL m a b = Ex k. oeq b (add a (mult m k)),
   congR m a b = Ex k. oeq a (add b (mult m k)) ) *)
fun congLAbs (mt, at, bt) =
  let val kF = Free("kk_cu", natT) in Term.lambda kF (oeq bt (add at (mult mt kF))) end;
fun congRAbs (mt, at, bt) =
  let val kF = Free("kk_cu", natT) in Term.lambda kF (oeq at (add bt (mult mt kF))) end;

val crt_unique =
  let
    val mF = Free("m", natT);
    val nF = Free("n", natT);
    val xF = Free("x", natT);
    val yF = Free("y", natT);

    val HcopP  = jT (cb_cop (mF, nF));
    val Hcop   = Thm.assume (ctermS2 HcopP);
    val HcmP   = jT (cong mF xF yF);
    val Hcm    = Thm.assume (ctermS2 HcmP);
    val HcnP   = jT (cong nF xF yF);
    val Hcn    = Thm.assume (ctermS2 HcnP);

    val goalC = cong (mult mF nF) xF yF;
    val mn = mult mF nF;

    (* the four disjuncts *)
    val cLm = congL mF xF yF;   val cRm = congR mF xF yF;
    val cLn = congL nF xF yF;   val cRn = congR nF xF yF;

    (* helper : build dvd (m*n) D from (dvd m D) and (dvd n D) *)
    fun build_mn_dvd (D, wm, wn) (hDm, hDn) =
      cmd_atS (mF, nF, D) Hcop hDm hDn;       (* jT (dvd (m*n) D) *)

    (* ===== combine congL m (y = x + m*a) with congL n (y = x + n*b) ===== *)
    fun caseLL hLm hLn aW bW =
      (* hLm : oeq y (add x (mult m a)) ; hLn : oeq y (add x (mult n b)) *)
      let
        val D = mult mF aW;                                       (* difference m*a *)
        (* m*a = n*b *)
        val eqXmaXnb = oeq_trans OF [oeq_sym OF [hLm], hLn];      (* oeq (x+m*a)(x+n*b) *)
        val hMaNb = add_left_cancel_atS (xF, mult mF aW, mult nF bW) eqXmaXnb;  (* oeq (m*a)(n*b) *)
        val hDm = dvd_introS (mF, D, aW) (oeqreflS_at D);         (* dvd m (m*a) *)
        val hDn = dvd_introS (nF, D, bW) hMaNb;                   (* dvd n (m*a) *)
        val hMNdvd = build_mn_dvd (D, aW, bW) (hDm, hDn);         (* dvd (m*n)(m*a) *)
        (* exE : witness e, he : (m*a) = (m*n)*e *)
        val DAbs = Abs("ee", natT, oeq D (mult mn (Bound 0)));
        fun eB eW (he : thm) =                                    (* he : oeq (m*a) ((m*n)*e) *)
          let
            val yeq = oeq_trans OF [hLm, add_cong_rS (xF, mult mF aW, mult mn eW) he];  (* oeq y (add x ((m*n)*e)) *)
          in cong_introL (mn, xF, yF, eW) yeq end;                (* jT (cong (m*n) x y) *)
        val g = exE_elimS2 (DAbs, goalC) hMNdvd "e_LL" eB;
      in g end;

    (* ===== combine congR m (x = y + m*a) with congR n (x = y + n*b) ===== *)
    fun caseRR hRm hRn aW bW =
      let
        val D = mult mF aW;
        val eqYmaYnb = oeq_trans OF [oeq_sym OF [hRm], hRn];      (* oeq (y+m*a)(y+n*b) *)
        val hMaNb = add_left_cancel_atS (yF, mult mF aW, mult nF bW) eqYmaYnb;  (* oeq (m*a)(n*b) *)
        val hDm = dvd_introS (mF, D, aW) (oeqreflS_at D);
        val hDn = dvd_introS (nF, D, bW) hMaNb;
        val hMNdvd = build_mn_dvd (D, aW, bW) (hDm, hDn);
        val DAbs = Abs("ee", natT, oeq D (mult mn (Bound 0)));
        fun eB eW (he : thm) =
          let
            val xeq = oeq_trans OF [hRm, add_cong_rS (yF, mult mF aW, mult mn eW) he];  (* oeq x (add y ((m*n)*e)) *)
          in cong_introR (mn, xF, yF, eW) xeq end;
        val g = exE_elimS2 (DAbs, goalC) hMNdvd "e_RR" eB;
      in g end;

    (* ===== cross case congL m (y=x+m*a) with congR n (x=y+n*b) : forces x=y ===== *)
    fun caseLR hLm hRn aW bW =
      (* hLm : oeq y (add x (mult m a)) ; hRn : oeq x (add y (mult n b)) *)
      let
        (* y = (y + n*b) + m*a = y + (n*b + m*a) *)
        val st1 = oeq_trans OF [hLm, add_cong_lS (xF, add yF (mult nF bW), mult mF aW) hRn];
                                                                 (* oeq y (add (add y (n*b)) (m*a)) *)
        val st2 = addassocS_at (yF, mult nF bW, mult mF aW);     (* oeq (add (add y (n*b))(m*a)) (add y (add (n*b)(m*a))) *)
        val yEqSum = oeq_trans OF [st1, st2];                    (* oeq y (add y (add (n*b)(m*a))) *)
        (* cancel : 0 = (n*b + m*a) *)
        val yEqY0  = oeq_sym OF [add0rS_at yF];                  (* oeq y (add y 0) *)
        val y0EqSum= oeq_trans OF [oeq_sym OF [yEqY0], yEqSum];  (* oeq (add y 0) (add y (n*b+m*a)) *)
        val zEqSum = add_left_cancel_atS (yF, ZeroC, add (mult nF bW) (mult mF aW)) y0EqSum;  (* oeq 0 (n*b+m*a) *)
        val sumEq0 = oeq_sym OF [zEqSum];                        (* oeq (n*b+m*a) 0 *)
        (* m*a = 0 *)
        val ma0 = add_eq_zero_right_vS OF [sumEq0];              (* oeq (m*a) 0 *)
        (* y = x : from hLm, y = x + m*a = x + 0 = x *)
        val yx1 = add_cong_rS (xF, mult mF aW, ZeroC) ma0;       (* oeq (add x (m*a)) (add x 0) *)
        val yx2 = add0rS_at xF;                                  (* oeq (add x 0) x *)
        val yEqX = oeq_trans OF [oeq_trans OF [hLm, yx1], yx2];  (* oeq y x *)
        (* cong (m*n) x y via congL, witness 0 : y = x + (m*n)*0 *)
        val mn0  = mult0rS_at mn;                                (* oeq ((m*n)*0) 0 *)
        val xeq1 = add_cong_rS (xF, mult mn ZeroC, ZeroC) mn0;   (* oeq (add x ((m*n)*0)) (add x 0) *)
        val xeq2 = add0rS_at xF;                                 (* oeq (add x 0) x *)
        val xEqX0= oeq_sym OF [oeq_trans OF [xeq1, xeq2]];       (* oeq x (add x ((m*n)*0)) *)
        val yEqX0= oeq_trans OF [yEqX, xEqX0];                   (* oeq y (add x ((m*n)*0)) *)
      in cong_introL (mn, xF, yF, ZeroC) yEqX0 end;

    (* ===== cross case congR m (x=y+m*a) with congL n (y=x+n*b) : forces x=y ===== *)
    fun caseRL hRm hLn aW bW =
      (* hRm : oeq x (add y (mult m a)) ; hLn : oeq y (add x (mult n b)) *)
      let
        (* x = (x + n*b) + m*a = x + (n*b + m*a) *)
        val st1 = oeq_trans OF [hRm, add_cong_lS (yF, add xF (mult nF bW), mult mF aW) hLn];
                                                                 (* oeq x (add (add x (n*b)) (m*a)) *)
        val st2 = addassocS_at (xF, mult nF bW, mult mF aW);     (* oeq (add (add x (n*b))(m*a)) (add x (add (n*b)(m*a))) *)
        val xEqSum = oeq_trans OF [st1, st2];                    (* oeq x (add x (add (n*b)(m*a))) *)
        val xEqX0  = oeq_sym OF [add0rS_at xF];                  (* oeq x (add x 0) *)
        val x0EqSum= oeq_trans OF [oeq_sym OF [xEqX0], xEqSum];  (* oeq (add x 0)(add x (n*b+m*a)) *)
        val zEqSum = add_left_cancel_atS (xF, ZeroC, add (mult nF bW) (mult mF aW)) x0EqSum;
        val sumEq0 = oeq_sym OF [zEqSum];                        (* oeq (n*b+m*a) 0 *)
        val ma0 = add_eq_zero_right_vS OF [sumEq0];              (* oeq (m*a) 0 *)
        (* x = y : from hRm, x = y + m*a = y + 0 = y *)
        val xy1 = add_cong_rS (yF, mult mF aW, ZeroC) ma0;       (* oeq (add y (m*a))(add y 0) *)
        val xy2 = add0rS_at yF;                                  (* oeq (add y 0) y *)
        val xEqY = oeq_trans OF [oeq_trans OF [hRm, xy1], xy2];  (* oeq x y *)
        (* cong (m*n) x y via congR, witness 0 : x = y + (m*n)*0 *)
        val mn0  = mult0rS_at mn;
        val yeq1 = add_cong_rS (yF, mult mn ZeroC, ZeroC) mn0;   (* oeq (add y ((m*n)*0))(add y 0) *)
        val yeq2 = add0rS_at yF;
        val yEqY0= oeq_sym OF [oeq_trans OF [yeq1, yeq2]];       (* oeq y (add y ((m*n)*0)) *)
        val xEqY0= oeq_trans OF [xEqY, yEqY0];                   (* oeq x (add y ((m*n)*0)) *)
      in cong_introR (mn, xF, yF, ZeroC) xEqY0 end;

    (* ---- disjE on cong m, then on cong n, with exE of witnesses ---- *)
    (* outer: cong m = Disj (cLm) (cRm) *)
    val mLeft =
      let
        val hLmDisj = Thm.assume (ctermS2 (jT cLm));     (* congL m x y *)
        fun lmBody aW (hLm : thm) =                      (* hLm : oeq y (add x (mult m a)) *)
          let
            (* inner: cong n = Disj (cLn)(cRn) *)
            val nLeft =
              let
                val hLnDisj = Thm.assume (ctermS2 (jT cLn));
                fun lnBody bW (hLn : thm) = caseLL hLm hLn aW bW;
                val r = exE_elimS2 (congLAbs (nF, xF, yF), goalC) hLnDisj "b_LL" lnBody;
              in Thm.implies_intr (ctermS2 (jT cLn)) r end;
            val nRight =
              let
                val hRnDisj = Thm.assume (ctermS2 (jT cRn));
                fun rnBody bW (hRn : thm) = caseLR hLm hRn aW bW;
                val r = exE_elimS2 (congRAbs (nF, xF, yF), goalC) hRnDisj "b_LR" rnBody;
              in Thm.implies_intr (ctermS2 (jT cRn)) r end;
          in disjE_elimS2 (cLn, cRn, goalC) Hcn nLeft nRight end;
        val r = exE_elimS2 (congLAbs (mF, xF, yF), goalC) hLmDisj "a_Lm" lmBody;
      in Thm.implies_intr (ctermS2 (jT cLm)) r end;

    val mRight =
      let
        val hRmDisj = Thm.assume (ctermS2 (jT cRm));     (* congR m x y *)
        fun rmBody aW (hRm : thm) =                      (* hRm : oeq x (add y (mult m a)) *)
          let
            val nLeft =
              let
                val hLnDisj = Thm.assume (ctermS2 (jT cLn));
                fun lnBody bW (hLn : thm) = caseRL hRm hLn aW bW;
                val r = exE_elimS2 (congLAbs (nF, xF, yF), goalC) hLnDisj "b_RL" lnBody;
              in Thm.implies_intr (ctermS2 (jT cLn)) r end;
            val nRight =
              let
                val hRnDisj = Thm.assume (ctermS2 (jT cRn));
                fun rnBody bW (hRn : thm) = caseRR hRm hRn aW bW;
                val r = exE_elimS2 (congRAbs (nF, xF, yF), goalC) hRnDisj "b_RR" rnBody;
              in Thm.implies_intr (ctermS2 (jT cRn)) r end;
          in disjE_elimS2 (cLn, cRn, goalC) Hcn nLeft nRight end;
        val r = exE_elimS2 (congRAbs (mF, xF, yF), goalC) hRmDisj "a_Rm" rmBody;
      in Thm.implies_intr (ctermS2 (jT cRm)) r end;

    val bodyGoal = disjE_elimS2 (cLm, cRm, goalC) Hcm mLeft mRight;
    val disch1 = Thm.implies_intr (ctermS2 HcnP) bodyGoal;
    val disch2 = Thm.implies_intr (ctermS2 HcmP) disch1;
    val disch3 = Thm.implies_intr (ctermS2 HcopP) disch2;
  in varify disch3 end;

val () = out "CRT_UNIQUE_PROVED\n";

(* ---- validation ---- *)
val mVu = Var (("m",0), natT);
val nVu = Var (("n",0), natT);
val xVu = Var (("x",0), natT);
val yVu = Var (("y",0), natT);
val crt_unique_intended =
  Logic.mk_implies (jT (cb_cop (mVu, nVu)),
    Logic.mk_implies (jT (cong mVu xVu yVu),
      Logic.mk_implies (jT (cong nVu xVu yVu),
        jT (cong (mult mVu nVu) xVu yVu))));
val r_cu = checkS2 ("crt_unique", crt_unique, crt_unique_intended);
val () = if r_cu then out "OK crt_unique\n" else out "FAIL crt_unique\n";

(* soundness probe : dropping coprimality is unsound *)
val probe_cu =
  let val bogus = Logic.mk_implies (jT (cong mVu xVu yVu),
                    Logic.mk_implies (jT (cong nVu xVu yVu),
                      jT (cong (mult mVu nVu) xVu yVu)))
  in not ((Thm.prop_of crt_unique) aconv bogus) end;
val () = if r_cu andalso probe_cu then out "PROBE_OK\n" else out "PROBE_UNSOUND\n";

val () = if r_cu then out "CRT_UNIQUE_OK\n" else out "CRT_UNIQUE_FAILED\n";
