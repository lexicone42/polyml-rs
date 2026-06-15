(* ============================================================================
   THE DIVISION THEOREM over the naturals, in Isabelle/Pure on the polyml-rs
   interpreter — Stage 1 of the FTA-uniqueness arc.  (test: isabelle_division.rs)
   ----------------------------------------------------------------------------
     div_mod_exists : |- 0 < b ==> ?q r. a = b*q + r  /\  r < b
     div_mod_unique : |- 0 < b ==> a = b*q1+r1 /\ r1<b ==> a = b*q2+r2 /\ r2<b
                            ==> q1 = q2 /\ r1 = r2
   For a divisor b>0, the quotient and remainder EXIST and are UNIQUE.  Both
   0-hypothesis theorems, pure LCF kernel inference; only classical assumption =
   excluded middle (from the base).

   Existence is by strong (course-of-values) induction on a, with NO subtraction:
   if a<b then (q,r)=(0,a); else b<=a gives a = b + a2 (the le-witness) with
   a2<a (since b>0), recurse to (q2,r2) for a2, recompose q := Suc q2 (via
   mult_Suc_right: b + b*q2 = b*(Suc q2)), r := r2.

   The foundation for gcd / Bezout / Euclid's lemma / FTA uniqueness (Stages 2-4).
   Built (on isabelle_classical_primes.sml) by a 3-seat ultracode fleet
   (wf_17792bed-545); all three proved existence, one also proved uniqueness
   (banked that variant).
   ============================================================================ *)


(* ============================================================================
   ============================================================================
   ***  DIVISION THEOREM over the naturals  ***  (div_mod_exists)
   ----------------------------------------------------------------------------
   TARGET:
     div_mod_exists : jT (lt Zero b)
        ==> jT (Ex (%q. Ex (%r. Conj (oeq a (add (mult b q) r)) (lt r b))))
   i.e. for b>0 there exist q,r with  a = b*q + r  and  r < b.

   PROOF: strong induction on a (b fixed Free), course-of-values predicate
     R a := Imp (lt Zero b) (Ex q. Ex r. Conj (oeq a (add (mult b q) r)) (lt r b)).
   Given 0<b, ex_middle on (lt a b):
     - lt a b : witnesses q:=Zero, r:=a.   a = b*0 + a = 0 + a = a, and a<b.
     - neg(lt a b) -> le b a (helper nlt_le).  le b a gives a = b + a2.  a2<a
       (since b=Suc b0>0).  Apply the strong IH at a2 (lt a2 a) with 0<b: get
       q2,r2 with a2 = b*q2 + r2 and r2<b.  Then a = b + (b*q2 + r2) =
       (b + b*q2) + r2 = b*(Suc q2) + r2.  Witnesses q:=Suc q2, r:=r2.
   Everything routes through ctxtS2/ctermS2 (where strong_induct lives).
   Capture-avoiding nested Ex built with Term.lambda over fresh Frees.
   ============================================================================ *)

val () = out "DIVISION_BEGIN\n";

(* ---- the fixed positive divisor parameter b ---- *)
val bDiv = Free ("b", natT);

(* ---- arithmetic instantiators on ctxtS2 (every new cterm via ctermS2) ---- *)
val mult_0_right_vS    = varify mult_0_right;    (* oeq (mult n 0) 0           *)
val mult_1_right_vS    = varify mult_1_right;    (* oeq (mult n (Suc 0)) n     *)
val mult_Suc_right_vS  = varify mult_Suc_right;  (* oeq (mult n (Suc m)) (add n (mult n m)) *)
val add_0_vS           = varify add_0;           (* oeq (add 0 n) n            *)
val add_Suc_vS         = varify add_Suc;         (* oeq (add (Suc m) n) (Suc (add m n)) *)
val add_0_right_vS     = varify add_0_right;     (* oeq (add n 0) n            *)
val add_comm_vS        = varify add_comm;        (* oeq (add m n) (add n m)    *)
val add_assoc_vS       = varify add_assoc;       (* oeq (add (add m n) k) (add m (add n k)) *)
val oeq_refl_vS        = varify oeq_refl;
val oeq_subst_vS       = varify oeq_subst;
val le_total_vS        = varify le_total;        (* Disj (le m n) (le n m)     *)
val disj_zero_or_suc_vS= varify disj_zero_or_suc;
val ex_middle_vS       = varify ex_middle_ax;
val oFalse_elim_vS     = varify oFalse_elim_ax;

fun mult0rS_at t       = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] mult_0_right_vS);
fun mult1rS_at t       = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] mult_1_right_vS);
fun multSrS_at (nt,mt) = beta_norm (Drule.infer_instantiate ctxtS2
                            [(("n",0), ctermS2 nt),(("m",0), ctermS2 mt)] mult_Suc_right_vS);
fun add0S_at t         = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] add_0_vS);
fun addSucS_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtS2
                            [(("m",0), ctermS2 mt),(("n",0), ctermS2 nt)] add_Suc_vS);
fun add0rS_at t        = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] add_0_right_vS);
val add_Suc_right_vS   = varify add_Suc_right;   (* oeq (add m (Suc n)) (Suc (add m n)) *)
fun addSrS_at (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtS2
                            [(("m",0), ctermS2 mt),(("n",0), ctermS2 nt)] add_Suc_right_vS);
fun addcommS_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtS2
                            [(("m",0), ctermS2 mt),(("n",0), ctermS2 nt)] add_comm_vS);
fun addassocS_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtS2
                            [(("m",0), ctermS2 mt),(("n",0), ctermS2 nt),(("k",0), ctermS2 kt)] add_assoc_vS);
fun oeqreflS_at t      = beta_norm (Drule.infer_instantiate ctxtS2 [(("a",0), ctermS2 t)] oeq_refl_vS);

(* add-congruence on LEFT / RIGHT operand, on ctxtS2 *)
fun add_cong_lS (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 pT), (("b",0), ctermS2 qT)] oeq_subst_vS);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtS2 [(("a",0), ctermS2 (add pT kT))] oeq_refl_vS);
  in inst OF [hpq, refl_pk] end;
fun add_cong_rS (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 pT), (("b",0), ctermS2 qT)] oeq_subst_vS);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtS2 [(("a",0), ctermS2 (add hT pT))] oeq_refl_vS);
  in inst OF [hpq, refl_hp] end;

(* le_intro on ctxtS2 (uses exI_vC, beta_norm via le abbreviation) *)
fun le_introS (mT, nT, w) hyp =
  let
    val Pabs = Abs ("p", natT, oeq nT (add mT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 w)] exI_vC);
  in inst OF [hyp] end;

(* le_total ground instance on ctxtS2 *)
fun le_total_atS (mt, nt) = beta_norm (Drule.infer_instantiate ctxtS2
      [(("m",0), ctermS2 mt), (("n",0), ctermS2 nt)] le_total_vS);

(* disj_zero_or_suc ground instance on ctxtS2 *)
fun dzosS_at t = beta_norm (Drule.infer_instantiate ctxtS2 [(("p",0), ctermS2 t)] disj_zero_or_suc_vS);

(* ex_middle / oFalse_elim ground instances on ctxtS2 *)
fun ex_middle_atS At = beta_norm (Drule.infer_instantiate ctxtS2 [(("A",0), ctermS2 At)] ex_middle_vS);
fun oFalse_elimS_at rT = beta_norm (Drule.infer_instantiate ctxtS2 [(("R",0), ctermS2 rT)] oFalse_elim_vS);

val () = out "DIVISION_HELPERS_READY\n";

(* ============================================================================
   HELPER  nlt_le : jT (neg (lt d c)) ==> jT (le c d)
   ----------------------------------------------------------------------------
   "not (d < c)  ==>  c <= d".   le_total (c, d) = Disj (le c d) (le d c).
     left  (le c d) : done.
     right (le d c) : c = d + p.  dzos p:
        p = 0     : c = d + 0 = d ; build le c d witness 0  (oeq d (add c 0)).
        p = Suc q : c = d + Suc q = Suc(d+q) = (Suc d)+q  => le (Suc d) c = lt d c,
                    contradicts neg(lt d c) => oFalse => oFalse_elim => le c d.
   ============================================================================ *)
val nlt_le =
  let
    val dF = Free("d", natT); val cF = Free("c", natT);
    val negHypP = jT (neg (lt dF cF));
    val negHyp  = Thm.assume (ctermS2 negHypP);          (* Imp (lt d c) oFalse *)
    val goalC   = le cF dF;
    val tot     = le_total_atS (cF, dF);                 (* Disj (le c d) (le d c) *)

    val caseL =
      let val hLcd = Thm.assume (ctermS2 (jT (le cF dF)))
      in Thm.implies_intr (ctermS2 (jT (le cF dF))) hLcd end;

    val PabsR = Abs("p", natT, oeq cF (add dF (Bound 0)));  (* body of le d c *)
    val caseR =
      let
        val hLdc = Thm.assume (ctermS2 (jT (le dF cF)));
        fun body p (hp : thm) =                            (* hp : oeq c (add d p) *)
          let
            val dz = dzosS_at p;                           (* Disj (oeq p 0) (Ex(%q. oeq p (Suc q))) *)
            val caseZero =
              let
                val epz  = Thm.assume (ctermS2 (jT (oeq p ZeroC)));   (* oeq p 0 *)
                val cong = add_cong_rS (dF, p, ZeroC) epz;  (* (d + p) = (d + 0) *)
                val c_d0 = oeq_trans OF [hp, cong];         (* c = (d + 0) *)
                val c_d  = oeq_trans OF [c_d0, add0rS_at dF];(* c = d *)
                val d_c  = oeq_sym OF [c_d];                (* d = c *)
                (* le c d witness 0 : need oeq d (add c 0).  add c 0 = c; oeq d c via d_c *)
                val ac0  = add0rS_at cF;                    (* (c + 0) = c *)
                val ac0s = oeq_sym OF [ac0];                (* c = (c + 0) *)
                val d_c0 = oeq_trans OF [d_c, ac0s];        (* d = (c + 0) *)
                val leThm= le_introS (cF, dF, ZeroC) d_c0;  (* le c d *)
              in Thm.implies_intr (ctermS2 (jT (oeq p ZeroC))) leThm end;
            val PabsQ = Abs("q", natT, oeq p (suc (Bound 0)));
            val caseSuc =
              let
                val exq = Thm.assume (ctermS2 (jT (mkEx PabsQ)));
                fun sucBody q (hq : thm) =                  (* hq : oeq p (Suc q) *)
                  let
                    val cong   = add_cong_rS (dF, p, suc q) hq;  (* (d + p) = (d + Suc q) *)
                    val c_dSq  = oeq_trans OF [hp, cong];        (* c = (d + Suc q) *)
                    val dSq_S  = addSrS_at (dF, q);              (* (d + Suc q) = Suc(d + q) *)
                    val c_Sdq  = oeq_trans OF [c_dSq, dSq_S];    (* c = Suc(d + q) *)
                    val Sdq_a  = addSucS_at (dF, q);             (* (Suc d + q) = Suc(d + q) *)
                    val c_add  = oeq_trans OF [c_Sdq, oeq_sym OF [Sdq_a]]; (* c = (Suc d + q) *)
                    val ltThm  = le_introS (suc dF, cF, q) c_add;(* le (Suc d) c = lt d c *)
                    val fls    = mp_atS2 (lt dF cF, oFalseC) negHyp ltThm; (* oFalse *)
                    val g      = Thm.implies_elim (oFalse_elimS_at goalC) fls; (* le c d *)
                  in g end;
                val g = exE_elimS2 (PabsQ, goalC) exq "q0" sucBody;
              in Thm.implies_intr (ctermS2 (jT (mkEx PabsQ))) g end;
            val combined = disjE_elimS2 (oeq p ZeroC, mkEx PabsQ, goalC) dz caseZero caseSuc;
          in combined end;
        val g = exE_elimS2 (PabsR, goalC) hLdc "wp" body;
      in Thm.implies_intr (ctermS2 (jT (le dF cF))) g end;

    val concl = disjE_elimS2 (le cF dF, le dF cF, goalC) tot caseL caseR;
    val disch = Thm.implies_intr (ctermS2 negHypP) concl;
  in varify disch end;

val dVnl = Var (("d",0), natT);
val cVnl = Var (("c",0), natT);
val nlt_le_intended =
  Logic.mk_implies (jT (neg (lt dVnl cVnl)), jT (le cVnl dVnl));
val r_nlt_le = checkS2 ("nlt_le", nlt_le, nlt_le_intended);

val nlt_le_vS = varify nlt_le;
fun nlt_le_atS (dt, ct) hneg =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2 [(("d",0), ctermS2 dt), (("c",0), ctermS2 ct)] nlt_le_vS)
  in Thm.implies_elim inst hneg end;

(* ============================================================================
   The result existential (capture-avoiding), parameterised by the dividend.
     resultEx2 a = Ex (%q. Ex (%r. Conj (oeq a (add (mult b q) r)) (lt r b)))
   ============================================================================ *)
fun innerDivAbs aTerm qTerm =                  (* %r. Conj (oeq a (add (mult b q) r)) (lt r b) *)
  let val rF = Free("r_rb", natT)
  in Term.lambda rF (mkConj (oeq aTerm (add (mult bDiv qTerm) rF)) (lt rF bDiv)) end;
fun rmDivBody aTerm =                           (* %q. Ex (%r. ...) *)
  let val qF = Free("q_rb", natT)
  in Term.lambda qF (mkEx (innerDivAbs aTerm qF)) end;
fun resultDivEx aTerm = mkEx (rmDivBody aTerm);
fun RDivTerm aTerm = mkImp (lt ZeroC bDiv) (resultDivEx aTerm);   (* Imp (0<b) (Ex ...) *)

(* build the inner Conj + double exI for given dividend a, q-witness, r-witness *)
fun buildResult aTerm (qWit, rWit) (hEqn : thm) (hLtR : thm) =
  let
    val conj = conjI_atS2 (oeq aTerm (add (mult bDiv qWit) rWit), lt rWit bDiv) hEqn hLtR;
    val exInner = exI_atS2 (innerDivAbs aTerm qWit) rWit conj;   (* Ex (%r. ...) at q=qWit *)
    val exOuter = exI_atS2 (rmDivBody aTerm) qWit exInner;       (* Ex (%q. Ex (%r. ...)) *)
  in exOuter end;

(* ============================================================================
   THE STEP BODY: fix n, given strong IH, prove Trueprop (R n).
   ============================================================================ *)
val div_mod_exists =
  let
    val nStep = Free("n_step", natT);
    val mIH   = Free("m_ih", natT);
    val Gprop = Logic.all mIH (Logic.mk_implies (jT (lt mIH nStep), jT (RDivTerm mIH)));
    val Hthm  = Thm.assume (ctermS2 Gprop);
    fun applyIH dt h_lt =
      let val hAt = Thm.forall_elim (ctermS2 dt) Hthm        (* lt d n ==> jT (R d) *)
      in Thm.implies_elim hAt h_lt end;

    (* prove jT (R n) = jT (Imp (lt 0 b) (resultDivEx n)) by impI; assume 0<b *)
    val posP   = jT (lt ZeroC bDiv);
    val h_pos  = Thm.assume (ctermS2 posP);                  (* lt 0 b = le (Suc 0) b *)
    val goalC  = resultDivEx nStep;

    (* ex_middle on (lt n b) *)
    val em = ex_middle_atS (lt nStep bDiv);                  (* Disj (lt n b) (neg (lt n b)) *)

    (* ---- CASE A : lt n b  -> q:=0, r:=n ---- *)
    val caseA =
      let
        val hLt = Thm.assume (ctermS2 (jT (lt nStep bDiv)));
        (* oeq n (add (mult b 0) n) *)
        val mb0   = mult0rS_at bDiv;                          (* (b*0) = 0 *)
        val congL = add_cong_lS (mult bDiv ZeroC, ZeroC, nStep) mb0;  (* (b*0 + n) = (0 + n) *)
        val a0n   = add0S_at nStep;                           (* (0 + n) = n *)
        val sum_n = oeq_trans OF [congL, a0n];                (* (b*0 + n) = n *)
        val eqn   = oeq_sym OF [sum_n];                       (* n = (b*0 + n) *)
        val res   = buildResult nStep (ZeroC, nStep) eqn hLt; (* jT (resultDivEx n) *)
      in Thm.implies_intr (ctermS2 (jT (lt nStep bDiv))) res end;

    (* ---- CASE B : neg (lt n b)  -> descent ---- *)
    val caseB =
      let
        val hNeg = Thm.assume (ctermS2 (jT (neg (lt nStep bDiv))));
        val hLeBN = nlt_le_atS (nStep, bDiv) hNeg;            (* le b n :  n = b + a2 *)
        (* exE over le b n : witness a2, hA2 : oeq n (add b a2) *)
        val PabsLe = Abs("p", natT, oeq nStep (add bDiv (Bound 0)));
        fun leBody a2 (hA2 : thm) =                           (* hA2 : oeq n (add b a2) *)
          let
            (* b = Suc b0 from h_pos : lt 0 b = le (Suc 0) b = Ex(%p. oeq b (add (Suc 0) p)) *)
            val PabsPos = Abs("p", natT, oeq bDiv (add (suc ZeroC) (Bound 0)));
            fun posBody b0 (hB0 : thm) =                       (* hB0 : oeq b (add (Suc 0) b0) *)
              let
                (* b = Suc b0 :  add (Suc 0) b0 = Suc(add 0 b0) = Suc b0 *)
                val aS1  = addSucS_at (ZeroC, b0);             (* (Suc 0 + b0) = Suc(0 + b0) *)
                val s0b0 = Suc_cong OF [add0S_at b0];          (* Suc(0 + b0) = Suc b0 *)
                val a1c  = oeq_trans OF [aS1, s0b0];           (* (Suc 0 + b0) = Suc b0 *)
                val b_Sb0= oeq_trans OF [hB0, a1c];            (* b = Suc b0 *)
                (* n = add b a2 = add (Suc b0) a2 = Suc(add b0 a2) *)
                val congb= add_cong_lS (bDiv, suc b0, a2) b_Sb0; (* (b + a2) = (Suc b0 + a2) *)
                val n_Sb0a2_pre = oeq_trans OF [hA2, congb];   (* n = (Suc b0 + a2) *)
                val Sb0a2 = addSucS_at (b0, a2);               (* (Suc b0 + a2) = Suc(b0 + a2) *)
                val n_Sb0a2 = oeq_trans OF [n_Sb0a2_pre, Sb0a2]; (* n = Suc(b0 + a2) *)
                (* lt a2 n witness b0 :  add (Suc a2) b0 = Suc(a2 + b0) = Suc(b0 + a2) = n *)
                val aSa2b0 = addSucS_at (a2, b0);              (* (Suc a2 + b0) = Suc(a2 + b0) *)
                val comm   = addcommS_at (a2, b0);             (* (a2 + b0) = (b0 + a2) *)
                val sComm  = Suc_cong OF [comm];               (* Suc(a2 + b0) = Suc(b0 + a2) *)
                val aSa2b0_S = oeq_trans OF [aSa2b0, sComm];   (* (Suc a2 + b0) = Suc(b0 + a2) *)
                val n_aSa2b0 = oeq_trans OF [n_Sb0a2, oeq_sym OF [aSa2b0_S]]; (* n = (Suc a2 + b0) *)
                val lt_a2_n = le_introS (suc a2, nStep, b0) n_aSa2b0; (* le (Suc a2) n = lt a2 n *)
                (* apply IH at a2 -> jT (R a2) = Imp (lt 0 b)(resultDivEx a2); mp with h_pos *)
                val Ra2  = applyIH a2 lt_a2_n;                 (* jT (Imp (lt 0 b)(resultDivEx a2)) *)
                val exA2 = mp_atS2 (lt ZeroC bDiv, resultDivEx a2) Ra2 h_pos; (* jT (resultDivEx a2) *)
                (* exE q2, exE r2 *)
                fun q2Body q2 (hQ2ex : thm) =                  (* hQ2ex : jT (Ex (%r. Conj (oeq a2 (add (mult b q2) r))(lt r b))) *)
                  let
                    fun r2Body r2 (hConj : thm) =              (* hConj : jT (Conj (oeq a2 (add (mult b q2) r2)) (lt r2 b)) *)
                      let
                        val hEqA2 = conjunct1_atS2 (oeq a2 (add (mult bDiv q2) r2), lt r2 bDiv) hConj; (* a2 = b*q2 + r2 *)
                        val hLtR2 = conjunct2_atS2 (oeq a2 (add (mult bDiv q2) r2), lt r2 bDiv) hConj; (* r2 < b *)
                        (* n = add b a2 = add b (b*q2 + r2) = (b + b*q2) + r2 = b*(Suc q2) + r2 *)
                        val congA2 = add_cong_rS (bDiv, a2, add (mult bDiv q2) r2) hEqA2; (* (b + a2) = (b + (b*q2 + r2)) *)
                        val n_b_sum = oeq_trans OF [hA2, congA2];  (* n = (b + (b*q2 + r2)) *)
                        val assoc = addassocS_at (bDiv, mult bDiv q2, r2); (* ((b + b*q2) + r2) = (b + (b*q2 + r2)) *)
                        val n_assoc = oeq_trans OF [n_b_sum, oeq_sym OF [assoc]]; (* n = ((b + b*q2) + r2) *)
                        val mSr   = multSrS_at (bDiv, q2);     (* (b*(Suc q2)) = (b + b*q2) *)
                        val mSrs  = oeq_sym OF [mSr];          (* (b + b*q2) = (b*(Suc q2)) *)
                        val congFold = add_cong_lS (add bDiv (mult bDiv q2), mult bDiv (suc q2), r2) mSrs; (* ((b + b*q2)+r2) = ((b*(Suc q2))+r2) *)
                        val n_final = oeq_trans OF [n_assoc, congFold]; (* n = (b*(Suc q2) + r2) *)
                        val res = buildResult nStep (suc q2, r2) n_final hLtR2; (* jT (resultDivEx n) *)
                      in res end;
                    val g = exE_elimS2 (innerDivAbs a2 q2, goalC) hQ2ex "r2w" r2Body;
                  in g end;
                val g = exE_elimS2 (rmDivBody a2, goalC) exA2 "q2w" q2Body;
              in g end;
            val g = exE_elimS2 (PabsPos, goalC) h_pos "b0w" posBody;
          in g end;
        val resB = exE_elimS2 (PabsLe, goalC) hLeBN "a2w" leBody;
      in Thm.implies_intr (ctermS2 (jT (neg (lt nStep bDiv)))) resB end;

    val concl = disjE_elimS2 (lt nStep bDiv, neg (lt nStep bDiv), goalC) em caseA caseB; (* jT (resultDivEx n) *)
    val impRn = impI_atS2 (lt ZeroC bDiv, resultDivEx nStep)
                  (Thm.implies_intr (ctermS2 posP) concl);   (* jT (R n) *)
    val stepThm = Thm.forall_intr (ctermS2 nStep) (Thm.implies_intr (ctermS2 Gprop) impRn);

    (* the strong_induct predicate %a. R a *)
    val Rpred =
      let val aF = Free("a_R", natT) in Term.lambda aF (RDivTerm aF) end;

    val kF = Free("a", natT);
    val siInst = beta_norm (Drule.infer_instantiate ctxtS2
                   [(("P",0), ctermS2 Rpred), (("k",0), ctermS2 kF)] (varify strong_induct));
    val Rk = Thm.implies_elim siInst stepThm;                (* jT (R a) = jT (Imp (lt 0 b)(resultDivEx a)) *)
    (* turn into  jT (lt 0 b) ==> jT (resultDivEx a) (META) and that is the TARGET *)
    val h_pos_k = Thm.assume (ctermS2 (jT (lt ZeroC bDiv)));
    val exK = mp_atS2 (lt ZeroC bDiv, resultDivEx kF) Rk h_pos_k; (* jT (resultDivEx a) *)
    val disch = Thm.implies_intr (ctermS2 (jT (lt ZeroC bDiv))) exK;
  in varify disch end;

(* ============================================================================
   VALIDATION : 0-hyp AND aconv the intended schematic goal (built the SAME way).
   ============================================================================ *)
val aVdiv = Var (("a",0), natT);
val bVdiv = Var (("b",0), natT);
val div_mod_exists_intended =
  let
    fun innerI aTerm qTerm =
      let val rF = Free("r_rb", natT)
      in Term.lambda rF (mkConj (oeq aTerm (add (multC $ bVdiv $ qTerm) rF)) (le (suc rF) bVdiv)) end;
    fun rmI aTerm =
      let val qF = Free("q_rb", natT)
      in Term.lambda qF (mkEx (innerI aTerm qF)) end;
  in Logic.mk_implies (jT (le (suc ZeroC) bVdiv), jT (mkEx (rmI aVdiv))) end;

val r_div = checkS2 ("div_mod_exists", div_mod_exists, div_mod_exists_intended);

(* ---- SOUNDNESS PROBE : kernel must REJECT a false variant ----
   Dropping the (lt r b) conjunct (r<b) would make it trivially provable with
   r:=a, q:=0 for ALL a (no remainder bound) - that must NOT be what we proved. *)
val probe_div_rltb =
  let
    fun innerB aTerm qTerm =
      let val rF = Free("r_rb", natT)
      in Term.lambda rF (oeq aTerm (add (mult bDiv qTerm) rF)) end;   (* drops (lt r b) *)
    fun rmB aTerm =
      let val qF = Free("q_rb", natT) in Term.lambda qF (mkEx (innerB aTerm qF)) end;
    val bogus = Logic.mk_implies (jT (lt ZeroC bDiv), jT (mkEx (rmB (Free("a",natT)))));
  in not ((Thm.prop_of div_mod_exists) aconv bogus) end;
(* and garbling the equation (a = b*q + Suc r instead of b*q + r) must be rejected *)
val probe_div_eqn =
  let
    fun innerB aTerm qTerm =
      let val rF = Free("r_rb", natT)
      in Term.lambda rF (mkConj (oeq aTerm (add (mult bDiv qTerm) (suc rF))) (lt rF bDiv)) end;
    fun rmB aTerm =
      let val qF = Free("q_rb", natT) in Term.lambda qF (mkEx (innerB aTerm qF)) end;
    val bogus = Logic.mk_implies (jT (lt ZeroC bDiv), jT (mkEx (rmB (Free("a",natT)))));
  in not ((Thm.prop_of div_mod_exists) aconv bogus) end;

val () =
  if probe_div_rltb andalso probe_div_eqn
  then out "PROBE_OK div_mod_exists keeps the r<b bound and the exact equation\n"
  else out "PROBE_UNSOUND div_mod_exists dropped/garbled a conjunct!\n";

val () =
  if r_div andalso probe_div_rltb andalso probe_div_eqn
  then out "DIVISION_DONE\n"
  else out "DIVISION_FAILED\n";

(* ============================================================================
   ***  BONUS : div_mod_unique  ***
   ----------------------------------------------------------------------------
   If a = b*q1 + r1 (r1<b) and a = b*q2 + r2 (r2<b) then q1=q2 AND r1=r2.
   Core statement proved (on ctxtS2):
     div_mod_unique :
       jT (oeq (add (mult b q1) r1) (add (mult b q2) r2))
         ==> jT (lt r1 b) ==> jT (lt r2 b)
           ==> jT (Conj (oeq q1 q2) (oeq r1 r2))
   q-equality by induction on q1 with q2 reflected through the object Forall;
   the contra lemma lt_not_ge rules out the "one quotient 0, other Suc" cross
   cases; r-equality by add_left_cancel after substituting q1=q2.
   ============================================================================ *)
val () = out "UNIQUE_BEGIN\n";

(* ---- extra instantiators on ctxtS2 ---- *)
val add_left_cancel_vS = varify add_left_cancel;   (* oeq (add m a)(add m b) ==> oeq a b *)
fun add_left_cancel_atS (mt, at, bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mt),(("a",0), ctermS2 at),(("b",0), ctermS2 bt)] add_left_cancel_vS)
  in Thm.implies_elim inst h end;
val Suc_neq_Zero_vS = varify Suc_neq_Zero_ax;
fun Suc_neq_Zero_atS t = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] Suc_neq_Zero_vS);
val nat_induct_vSU = varify nat_induct;
val mult_0_right_vSU = mult_0_right_vS;            (* (b*0)=0 instantiator mult0rS_at already exists *)
fun mult_cong_rS (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 pT), (("b",0), ctermS2 qT)] oeq_subst_vS);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtS2 [(("a",0), ctermS2 (mult hT pT))] oeq_refl_vS);
  in inst OF [hpq, refl_hp] end;

(* allI / allE native on ctxtS2 (reuse the varified _vC axioms) *)
fun allI_atS2 Pabs hAllThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2 [(("P",0), ctermS2 Pabs)] allI_vC)
  in Thm.implies_elim inst hAllThm end;
fun allE_atS2 Pabs at hForall =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 at)] allE_vC)
  in Thm.implies_elim inst hForall end;

(* ----------------------------------------------------------------------------
   CONTRA lemma  lt_not_ge : jT (lt r b) ==> jT (oeq r (add b x)) ==> jT oFalse
   ---------------------------------------------------------------------------- *)
val lt_not_ge =
  let
    val rF = Free("r", natT); val xF = Free("x", natT);
    val ltHypP = jT (lt rF bDiv);
    val eqHypP = jT (oeq rF (add bDiv xF));
    val ltHyp  = Thm.assume (ctermS2 ltHypP);
    val eqHyp  = Thm.assume (ctermS2 eqHypP);
    val PabsLt = Abs("p", natT, oeq bDiv (add (suc rF) (Bound 0)));  (* body of le (Suc r) b *)
    fun body p (hp : thm) =                              (* hp : oeq b (add (Suc r) p) *)
      let
        val aS    = addSucS_at (rF, p);                  (* (Suc r + p) = Suc(r + p) *)
        val b_S   = oeq_trans OF [hp, aS];               (* b = Suc(r + p) *)
        val congB = add_cong_lS (bDiv, suc (add rF p), xF) b_S;  (* (b + x) = (Suc(r+p) + x) *)
        val r_bx  = oeq_trans OF [eqHyp, congB];          (* r = (Suc(r+p) + x) *)
        val aS2   = addSucS_at (add rF p, xF);            (* (Suc(r+p) + x) = Suc((r+p) + x) *)
        val r_S2  = oeq_trans OF [r_bx, aS2];             (* r = Suc((r+p) + x) *)
        val assoc = addassocS_at (rF, p, xF);             (* ((r+p)+x) = (r + (p+x)) *)
        val sAssoc= Suc_cong OF [assoc];                  (* Suc((r+p)+x) = Suc(r+(p+x)) *)
        val r_S3  = oeq_trans OF [r_S2, sAssoc];          (* r = Suc(r + (p+x)) *)
        val aSr   = addSrS_at (rF, add p xF);             (* (r + Suc(p+x)) = Suc(r + (p+x)) *)
        val r_addS= oeq_trans OF [r_S3, oeq_sym OF [aSr]];(* r = (r + Suc(p+x)) *)
        val ar0   = add0rS_at rF;                         (* (r + 0) = r *)
        val r0_add= oeq_trans OF [ar0, r_addS];           (* (r + 0) = (r + Suc(p+x)) *)
        val canc  = add_left_cancel_atS (rF, ZeroC, suc (add p xF)) r0_add; (* 0 = Suc(p+x) *)
        val cancS = oeq_sym OF [canc];                    (* Suc(p+x) = 0 *)
        val fls   = (Suc_neq_Zero_atS (add p xF)) OF [cancS]; (* oFalse *)
      in fls end;
    val afterExE = exE_elimS2 (PabsLt, oFalseC) ltHyp "pp" body;
    val d1 = Thm.implies_intr (ctermS2 eqHypP) afterExE;
    val d2 = Thm.implies_intr (ctermS2 ltHypP) d1;
  in varify d2 end;

(* varify generalises r,x AND the parameter b -> ?r ?x ?b.  Validate against the
   Var-b intended (so aconv matches); but for USE inside the fixed-b development
   re-PIN ?b := bDiv (Free) so the lemma composes with fixed-b hypotheses. *)
val bVc = Var (("b",0), natT);
val rVc = Var (("r",0), natT);
val xVc = Var (("x",0), natT);
val lt_not_ge_intended =
  Logic.mk_implies (jT (le (suc rVc) bVc),
    Logic.mk_implies (jT (oeq rVc (add bVc xVc)), jT oFalseC));
val r_lng = checkS2 ("lt_not_ge", lt_not_ge, lt_not_ge_intended);

val lt_not_ge_vS = beta_norm (Drule.infer_instantiate ctxtS2 [(("b",0), ctermS2 bDiv)] (varify lt_not_ge));
fun lt_not_ge_atS (rt, xt) hlt heq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2 [(("r",0), ctermS2 rt),(("x",0), ctermS2 xt)] lt_not_ge_vS)
  in Thm.implies_elim (Thm.implies_elim inst hlt) heq end;

(* ============================================================================
   div_mod_unique
   ============================================================================ *)
val div_mod_unique =
  let
    val q1F = Free("q1", natT); val q2F = Free("q2", natT);
    val r1F = Free("r1", natT); val r2F = Free("r2", natT);
    val EQp  = jT (oeq (add (mult bDiv q1F) r1F) (add (mult bDiv q2F) r2F));
    val LT1p = jT (lt r1F bDiv);
    val LT2p = jT (lt r2F bDiv);
    val hEQ  = Thm.assume (ctermS2 EQp);
    val hLT1 = Thm.assume (ctermS2 LT1p);
    val hLT2 = Thm.assume (ctermS2 LT2p);

    (* EQ a c  ==  oeq (add (mult b a) r1) (add (mult b c) r2)   (r1,r2 fixed) *)
    fun EQt a c = oeq (add (mult bDiv a) r1F) (add (mult bDiv c) r2F);
    (* P q1 = Forall(%q2. Imp (EQ q1 q2)(oeq q1 q2)) , capture-avoiding *)
    fun qImpAbs q1t =                                   (* %q2. Imp (EQ q1 q2)(oeq q1 q2) *)
      let val q2v = Free("q2_p", natT)
      in Term.lambda q2v (mkImp (EQt q1t q2v) (oeq q1t q2v)) end;
    fun Ppred_body q1t = mkForall (qImpAbs q1t);
    val Ppred =
      let val q1v = Free("q1_p", natT) in Term.lambda q1v (Ppred_body q1v) end;

    val nat_ind = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Ppred), (("k",0), ctermS2 q1F)] nat_induct_vSU);

    (* ---- BASE : P 0 = Forall(%q2. Imp (EQ 0 q2)(oeq 0 q2)) ---- *)
    val baseThm =
      let
        val q2v = Free("q2_b", natT);
        (* prove Imp (EQ 0 q2)(oeq 0 q2) by impI *)
        val eq0  = jT (EQt ZeroC q2v);                   (* oeq (add (mult b 0) r1)(add (mult b q2) r2) *)
        val heq0 = Thm.assume (ctermS2 eq0);
        (* simplify LHS: add (mult b 0) r1 = add 0 r1 = r1 *)
        val mb0  = mult0rS_at bDiv;                       (* (b*0) = 0 *)
        val congL= add_cong_lS (mult bDiv ZeroC, ZeroC, r1F) mb0;  (* (b*0 + r1) = (0 + r1) *)
        val a0r1 = add0S_at r1F;                          (* (0 + r1) = r1 *)
        val lhs_r1 = oeq_trans OF [congL, a0r1];          (* (b*0 + r1) = r1 *)
        val lhs_r1s= oeq_sym OF [lhs_r1];                 (* r1 = (b*0 + r1) *)
        val r1_rhs = oeq_trans OF [lhs_r1s, heq0];        (* r1 = (add (mult b q2) r2) *)
        (* goal oeq 0 q2 ; case on q2 *)
        val goalEq = oeq ZeroC q2v;
        val dz = dzosS_at q2v;
        val caseZ =
          let
            val ez = Thm.assume (ctermS2 (jT (oeq q2v ZeroC)));  (* q2 = 0 *)
            val g  = oeq_sym OF [ez];                            (* 0 = q2 *)
          in Thm.implies_intr (ctermS2 (jT (oeq q2v ZeroC))) g end;
        val PabsQ = Abs("q", natT, oeq q2v (suc (Bound 0)));
        val caseS =
          let
            val exq = Thm.assume (ctermS2 (jT (mkEx PabsQ)));
            fun sBody q (hq : thm) =                            (* hq : oeq q2 (Suc q) *)
              let
                (* rewrite r1_rhs's RHS using q2 = Suc q:
                   add (mult b q2) r2 = add (mult b (Suc q)) r2
                                      = add (add b (mult b q)) r2
                                      = add b (add (mult b q) r2)  *)
                val mcong = mult_cong_rS (bDiv, q2v, suc q) hq;  (* (b*q2) = (b*(Suc q)) *)
                val acong = add_cong_lS (mult bDiv q2v, mult bDiv (suc q), r2F) mcong; (* (b*q2 + r2) = (b*(Suc q) + r2) *)
                val mSr   = multSrS_at (bDiv, q);               (* (b*(Suc q)) = (b + b*q) *)
                val acong2= add_cong_lS (mult bDiv (suc q), add bDiv (mult bDiv q), r2F) mSr; (* (b*(Suc q)+r2) = ((b + b*q)+r2) *)
                val assoc = addassocS_at (bDiv, mult bDiv q, r2F);  (* ((b + b*q)+r2) = (b + (b*q + r2)) *)
                val rhs_chain = oeq_trans OF [oeq_trans OF [acong, acong2], assoc]; (* (b*q2 + r2) = (b + (b*q+r2)) *)
                val r1_form = oeq_trans OF [r1_rhs, rhs_chain]; (* r1 = (b + (b*q + r2)) *)
                val fls = lt_not_ge_atS (r1F, add (mult bDiv q) r2F) hLT1 r1_form;  (* oFalse *)
                val g   = Thm.implies_elim (oFalse_elimS_at goalEq) fls;  (* oeq 0 q2 *)
              in g end;
            val g = exE_elimS2 (PabsQ, goalEq) exq "q0" sBody;
          in Thm.implies_intr (ctermS2 (jT (mkEx PabsQ))) g end;
        val combined = disjE_elimS2 (oeq q2v ZeroC, mkEx PabsQ, goalEq) dz caseZ caseS;
        val impThm = impI_atS2 (EQt ZeroC q2v, oeq ZeroC q2v)
                       (Thm.implies_intr (ctermS2 eq0) combined);  (* Imp (EQ 0 q2)(oeq 0 q2) *)
        (* allI : !!q2. jT (Imp ...) ==> jT (Forall (qImpAbs 0)) *)
        val minor = Thm.forall_intr (ctermS2 q2v) impThm;
      in allI_atS2 (qImpAbs ZeroC) minor end;

    (* ---- STEP : !!q1. P q1 ==> P (Suc q1) ---- *)
    val stepThm =
      let
        val q1v = Free("q1_s", natT);
        val IHprop = jT (Ppred_body q1v);                 (* Forall(%q2. Imp (EQ q1 q2)(oeq q1 q2)) *)
        val IH = Thm.assume (ctermS2 IHprop);
        val q2v = Free("q2_s", natT);
        val eqS  = jT (EQt (suc q1v) q2v);                (* oeq (add (mult b (Suc q1)) r1)(add (mult b q2) r2) *)
        val heqS = Thm.assume (ctermS2 eqS);
        (* LHS: add (mult b (Suc q1)) r1 = add (add b (mult b q1)) r1 = add b (add (mult b q1) r1) *)
        val mSrL  = multSrS_at (bDiv, q1v);               (* (b*(Suc q1)) = (b + b*q1) *)
        val acL   = add_cong_lS (mult bDiv (suc q1v), add bDiv (mult bDiv q1v), r1F) mSrL; (* (b*(Suc q1)+r1) = ((b + b*q1)+r1) *)
        val asL   = addassocS_at (bDiv, mult bDiv q1v, r1F); (* ((b + b*q1)+r1) = (b + (b*q1 + r1)) *)
        val lhsF  = oeq_trans OF [acL, asL];              (* (b*(Suc q1)+r1) = (b + (b*q1 + r1)) *)
        val lhsFs = oeq_sym OF [lhsF];                    (* (b + (b*q1+r1)) = (b*(Suc q1)+r1) *)
        val goalEq = oeq (suc q1v) q2v;
        val dz = dzosS_at q2v;
        val caseZ =
          let
            val ez = Thm.assume (ctermS2 (jT (oeq q2v ZeroC)));  (* q2 = 0 *)
            (* RHS = add (mult b q2) r2 = add (mult b 0) r2 = add 0 r2 = r2 *)
            val mcong = mult_cong_rS (bDiv, q2v, ZeroC) ez;       (* (b*q2) = (b*0) *)
            val acong = add_cong_lS (mult bDiv q2v, mult bDiv ZeroC, r2F) mcong; (* (b*q2 + r2) = (b*0 + r2) *)
            val mb0   = mult0rS_at bDiv;                         (* (b*0) = 0 *)
            val acong2= add_cong_lS (mult bDiv ZeroC, ZeroC, r2F) mb0; (* (b*0 + r2) = (0 + r2) *)
            val a0r2  = add0S_at r2F;                            (* (0 + r2) = r2 *)
            val rhs_r2= oeq_trans OF [oeq_trans OF [acong, acong2], a0r2]; (* (b*q2 + r2) = r2 *)
            (* heqS : (b*(Suc q1)+r1) = (b*q2 + r2) ; with lhsFs and rhs_r2 :
               (b + (b*q1+r1)) = r2  -> sym -> r2 = (b + (b*q1+r1)) *)
            val mid   = oeq_trans OF [lhsFs, heqS];              (* (b + (b*q1+r1)) = (b*q2 + r2) *)
            val mid2  = oeq_trans OF [mid, rhs_r2];              (* (b + (b*q1+r1)) = r2 *)
            val r2_form = oeq_sym OF [mid2];                     (* r2 = (b + (b*q1+r1)) *)
            val fls   = lt_not_ge_atS (r2F, add (mult bDiv q1v) r1F) hLT2 r2_form; (* oFalse *)
            val g     = Thm.implies_elim (oFalse_elimS_at goalEq) fls;  (* oeq (Suc q1) q2 *)
          in Thm.implies_intr (ctermS2 (jT (oeq q2v ZeroC))) g end;
        val PabsQ = Abs("q", natT, oeq q2v (suc (Bound 0)));
        val caseS =
          let
            val exq = Thm.assume (ctermS2 (jT (mkEx PabsQ)));
            fun sBody q (hq : thm) =                            (* hq : oeq q2 (Suc q) *)
              let
                (* RHS = add (mult b q2) r2 = add (mult b (Suc q)) r2
                       = add (add b (mult b q)) r2 = add b (add (mult b q) r2) *)
                val mcong = mult_cong_rS (bDiv, q2v, suc q) hq;  (* (b*q2) = (b*(Suc q)) *)
                val acong = add_cong_lS (mult bDiv q2v, mult bDiv (suc q), r2F) mcong; (* (b*q2 + r2) = (b*(Suc q) + r2) *)
                val mSr   = multSrS_at (bDiv, q);               (* (b*(Suc q)) = (b + b*q) *)
                val acong2= add_cong_lS (mult bDiv (suc q), add bDiv (mult bDiv q), r2F) mSr; (* (b*(Suc q)+r2) = ((b + b*q)+r2) *)
                val assoc = addassocS_at (bDiv, mult bDiv q, r2F);  (* ((b + b*q)+r2) = (b + (b*q + r2)) *)
                val rhsF  = oeq_trans OF [oeq_trans OF [acong, acong2], assoc]; (* (b*q2 + r2) = (b + (b*q+r2)) *)
                (* (b + (b*q1+r1)) = (b*(Suc q1)+r1) = (b*q2+r2) = (b + (b*q+r2)) *)
                val mid   = oeq_trans OF [lhsFs, heqS];          (* (b + (b*q1+r1)) = (b*q2 + r2) *)
                val both  = oeq_trans OF [mid, rhsF];            (* (b + (b*q1+r1)) = (b + (b*q+r2)) *)
                val canc  = add_left_cancel_atS (bDiv, add (mult bDiv q1v) r1F, add (mult bDiv q) r2F) both;
                                                                (* (b*q1+r1) = (b*q+r2)  == EQ q1 q *)
                (* apply IH at q : allE -> Imp (EQ q1 q)(oeq q1 q) ; mp with canc -> oeq q1 q *)
                val ihAtq = allE_atS2 (qImpAbs q1v) q IH;        (* jT (Imp (EQ q1 q)(oeq q1 q)) *)
                val q1q   = mp_atS2 (EQt q1v q, oeq q1v q) ihAtq canc; (* oeq q1 q *)
                val sq    = Suc_cong OF [q1q];                  (* oeq (Suc q1)(Suc q) *)
                (* goal oeq (Suc q1) q2 ; rewrite q2 = Suc q (sym of hq) *)
                val Psub  = Abs("z", natT, oeq (suc q1v) (Bound 0));
                val subInst = beta_norm (Drule.infer_instantiate ctxtS2
                      [(("P",0), ctermS2 Psub), (("a",0), ctermS2 (suc q)), (("b",0), ctermS2 q2v)] oeq_subst_vS);
                val hq_sym = oeq_sym OF [hq];                   (* oeq (Suc q) q2 *)
                val g     = (subInst OF [hq_sym]) OF [sq];      (* oeq (Suc q1) q2 *)
              in g end;
            val g = exE_elimS2 (PabsQ, goalEq) exq "q0" sBody;
          in Thm.implies_intr (ctermS2 (jT (mkEx PabsQ))) g end;
        val combined = disjE_elimS2 (oeq q2v ZeroC, mkEx PabsQ, goalEq) dz caseZ caseS;
        val impThm = impI_atS2 (EQt (suc q1v) q2v, oeq (suc q1v) q2v)
                       (Thm.implies_intr (ctermS2 eqS) combined);   (* Imp (EQ (Suc q1) q2)(oeq (Suc q1) q2) *)
        val minor  = Thm.forall_intr (ctermS2 q2v) impThm;
        val pSuc   = allI_atS2 (qImpAbs (suc q1v)) minor;          (* jT (P (Suc q1)) *)
        val stepInner = Thm.implies_intr (ctermS2 IHprop) pSuc;
      in Thm.forall_intr (ctermS2 q1v) stepInner end;

    val r1ind = Thm.implies_elim nat_ind baseThm;
    val pq1    = Thm.implies_elim r1ind stepThm;          (* jT (P q1) = jT (Forall(%q2. Imp (EQ q1 q2)(oeq q1 q2))) *)
    (* allE at q2F -> Imp (EQ q1 q2)(oeq q1 q2) ; mp with hEQ -> oeq q1 q2 *)
    val ihq2  = allE_atS2 (qImpAbs q1F) q2F pq1;           (* jT (Imp (EQ q1 q2)(oeq q1 q2)) *)
    val hQeq  = mp_atS2 (EQt q1F q2F, oeq q1F q2F) ihq2 hEQ;  (* oeq q1 q2 *)

    (* ---- r-equality : substitute q1=q2 into hEQ, cancel b*q1 ---- *)
    val mqe   = mult_cong_rS (bDiv, q1F, q2F) hQeq;       (* (b*q1) = (b*q2) *)
    val mqes  = oeq_sym OF [mqe];                         (* (b*q2) = (b*q1) *)
    val rcong = add_cong_lS (mult bDiv q2F, mult bDiv q1F, r2F) mqes; (* (b*q2 + r2) = (b*q1 + r2) *)
    val eq_q1 = oeq_trans OF [hEQ, rcong];                (* (b*q1 + r1) = (b*q1 + r2) *)
    val hReq  = add_left_cancel_atS (mult bDiv q1F, r1F, r2F) eq_q1;  (* oeq r1 r2 *)

    val conj  = conjI_atS2 (oeq q1F q2F, oeq r1F r2F) hQeq hReq;  (* Conj (oeq q1 q2)(oeq r1 r2) *)
    val d1 = Thm.implies_intr (ctermS2 LT2p) conj;
    val d2 = Thm.implies_intr (ctermS2 LT1p) d1;
    val d3 = Thm.implies_intr (ctermS2 EQp)  d2;
  in varify d3 end;

(* ---- validation : 0-hyp AND aconv the intended schematic goal ---- *)
val q1Vu = Var (("q1",0), natT); val q2Vu = Var (("q2",0), natT);
val r1Vu = Var (("r1",0), natT); val r2Vu = Var (("r2",0), natT);
val div_mod_unique_intended =
  Logic.mk_implies (jT (oeq (add (mult bVc q1Vu) r1Vu) (add (mult bVc q2Vu) r2Vu)),
    Logic.mk_implies (jT (le (suc r1Vu) bVc),
      Logic.mk_implies (jT (le (suc r2Vu) bVc),
        jT (mkConj (oeq q1Vu q2Vu) (oeq r1Vu r2Vu)))));
val r_uniq = checkS2 ("div_mod_unique", div_mod_unique, div_mod_unique_intended);

(* ---- SOUNDNESS PROBE : dropping (lt r1 b)/(lt r2 b) must change the theorem ---- *)
val probe_uniq_bounds =
  let
    val bogus = Logic.mk_implies (jT (oeq (add (mult bVc q1Vu) r1Vu) (add (mult bVc q2Vu) r2Vu)),
                  jT (mkConj (oeq q1Vu q2Vu) (oeq r1Vu r2Vu)));  (* drops BOTH lt bounds *)
  in not ((Thm.prop_of div_mod_unique) aconv bogus) end;

val () =
  if r_uniq andalso probe_uniq_bounds
  then out "UNIQUE_DONE\n"
  else out "UNIQUE_FAILED\n";
