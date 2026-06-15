(* ============================================================================
   EUCLID'S LEMMA over the naturals, in Isabelle/Pure on the polyml-rs
   interpreter — Stage 2 of the FTA-uniqueness arc.  (test: isabelle_euclid_lemma.rs)
   ----------------------------------------------------------------------------
     euclid_lemma : |- prime p ==> p | a*b ==> p|a \/ p|b
   A prime dividing a product divides one of the factors.  0-hypothesis,
   pure LCF kernel inference, over the STRUCTURAL prime; only classical
   assumption = excluded middle.

   Proved by the GAUSS DESCENT (NO gcd, NO Bezout, NO integers needed):
     bounded_euclid : lt a p ==> prime p ==> p | a*b ==> p|a \/ p|b
       by strong induction on a (a<p): if p|a done; if a<=1 trivial; else
       1<a<p, divide p by a (division theorem) -> p = a*q + r with 0<r<a, show
       p | r*b via dvd_diff (p*b = (a*q)*b + r*b, p divides p*b and (a*q)*b),
       strong IH at r (<a<p) -> p|r or p|b; p|r impossible (prime_not_dvd_pos_lt),
       so p|b.
     euclid_lemma (general): reduce a mod p (a = p*q + r, r<p) -> p | r*b via
       dvd_diff -> bounded_euclid at r -> p|r (=> p|a, dvd_add) or p|b.

   Key helpers (Stage-2): dvd_diff (p|x /\ p|(x+y) => p|y), prime_not_dvd_pos_lt
   (no p divides a positive r<p), mult_le_mono, dvd_mult_assoc_l.  All rest on
   the Stage-1 division theorem (isabelle_division.sml).

   Built by a 2-phase ultracode pipeline (wf_904dd5f8-976): helpers -> euclid_lemma
   (3 seats, all proved it).  Stages 3-4 (Euclid lemma for lists -> FTA uniqueness)
   remain; see task #75.
   ============================================================================ *)

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

(* ============================================================================
   ============================================================================
   ***  EUCLID-LEMMA HELPERS (Stage 2 of FTA, via GAUSS DESCENT)  ***
   ----------------------------------------------------------------------------
   Everything routes through the SINGLE FINAL context ctxtS2 / ctermS2 (where
   strong_induct, div_mod_exists, nlt_le, lt_not_ge, div_mod_unique already
   live; thyS2 extends thyC which extends thyT, so every earlier schematic
   0-hyp lemma lifts to ctxtS2 by `varify`).

   ADDED + PROVED (each a 0-hyp / 0-extra-hyp named val, validated aconv):
     mult_le_mono          : jT (le j k) ==> jT (le (mult c j) (mult c k))
     dvd_diff              : jT (dvd p x) ==> jT (dvd p (add x y)) ==> jT (dvd p y)
     prime_not_dvd_pos_lt  : jT (dvd p r) ==> jT (lt Zero r) ==> jT (lt r p)
                                ==> jT oFalse
     dvd_mult_assoc_l      : jT (dvd p (mult a b)) ==> jT (dvd p (mult (mult a q) b))
   ============================================================================ *)

val () = out "EL_HELPERS_BEGIN\n";

(* ---- lift the dependency lemmas onto ctxtS2 (schematic; thyS2 extends thyT) ---- *)
val left_distrib_vS  = varify left_distrib;   (* oeq (mult ?x (add ?m ?n)) (add (mult ?x ?m) (mult ?x ?n)) *)
val mult_assoc_vS    = varify mult_assoc;     (* oeq (mult (mult ?m ?n) ?k) (mult ?m (mult ?n ?k)) *)
val mult_comm_vSU    = varify mult_comm;      (* oeq (mult ?m ?n) (mult ?n ?m) *)
val dvd_le_vS        = varify dvd_le;         (* jT (dvd ?d ?n) ==> (jT(oeq ?n 0)==>jT oFalse) ==> jT (le ?d ?n) *)
val dvd_zero_vS      = varify dvd_zero;       (* jT (dvd ?a 0) *)
val dvd_mult_right_vS= varify dvd_mult_right; (* jT (dvd ?a ?b) ==> jT (dvd ?a (mult ?b ?c)) *)
val le_trans_vSU     = varify le_trans;       (* jT (le ?m ?n) ==> jT (le ?n ?k) ==> jT (le ?m ?k) *)
val le_antisym_vS    = varify le_antisym;     (* jT (le ?m ?n) ==> jT (le ?n ?m) ==> jT (oeq ?m ?n) *)
val lt_irrefl_vS     = varify lt_irrefl;      (* jT (lt ?n ?n) ==> jT oFalse *)

(* ground instantiators on ctxtS2 *)
fun left_distrib_atS (xT, mT, nT) =
  beta_norm (Drule.infer_instantiate ctxtS2
      [(("x",0), ctermS2 xT), (("m",0), ctermS2 mT), (("n",0), ctermS2 nT)] left_distrib_vS);
fun mult_assoc_atS (mT, nT, kT) =
  beta_norm (Drule.infer_instantiate ctxtS2
      [(("m",0), ctermS2 mT), (("n",0), ctermS2 nT), (("k",0), ctermS2 kT)] mult_assoc_vS);
fun mult_comm_atS (mT, nT) =
  beta_norm (Drule.infer_instantiate ctxtS2
      [(("m",0), ctermS2 mT), (("n",0), ctermS2 nT)] mult_comm_vSU);
fun le_trans_atS (mT, nT, kT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mT), (("n",0), ctermS2 nT), (("k",0), ctermS2 kT)] le_trans_vSU)
  in (inst OF [h1]) OF [h2] end;
fun le_antisym_atS (mT, nT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mT), (("n",0), ctermS2 nT)] le_antisym_vS)
  in (inst OF [h1]) OF [h2] end;
fun lt_irrefl_atS nT h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 nT)] lt_irrefl_vS)
  in Thm.implies_elim inst h end;

(* dvd_intro on ctxtS2 : from a proof of `oeq bT (mult aT w)`, get jT (dvd aT bT). *)
fun dvd_introS (aT, bT, w) hyp =
  let
    val Pabs = Abs ("k", natT, oeq bT (mult aT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 w)] exI_vC);
  in inst OF [hyp] end;

(* mult-congruence on LEFT operand (k fixed): oeq p q ==> oeq (mult p k) (mult q k) *)
fun mult_cong_lS (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 pT), (("b",0), ctermS2 qT)] oeq_subst_vS);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtS2 [(("a",0), ctermS2 (mult pT kT))] oeq_refl_vS);
  in inst OF [hpq, refl_pk] end;

(* dvd_zero ground instance on ctxtS2 *)
fun dvd_zeroS_at t = beta_norm (Drule.infer_instantiate ctxtS2 [(("a",0), ctermS2 t)] dvd_zero_vS);

(* dvd_mult_right ground/applied on ctxtS2 :
     jT (dvd a b)  ->  jT (dvd a (mult b c)) *)
fun dvd_mult_right_atS (aT, bT, cT) hdvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("a",0), ctermS2 aT), (("b",0), ctermS2 bT), (("c",0), ctermS2 cT)] dvd_mult_right_vS)
  in Thm.implies_elim inst hdvd end;

(* dvd_le applied on ctxtS2 :  jT (dvd d n) -> (META jT(oeq n 0)==>jT oFalse) -> jT (le d n) *)
fun dvd_le_atS (dT, nT) hdvd hnzMeta =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("d",0), ctermS2 dT), (("n",0), ctermS2 nT)] dvd_le_vS)
  in Thm.implies_elim (Thm.implies_elim inst hdvd) hnzMeta end;

(* dvd-congruence on the 2nd (dividend) operand (CAPTURE-AVOIDING via Term.lambda
   over a fresh Free):  oeq x y  ==>  jT (dvd p x)  ==>  jT (dvd p y).
   We use oeq_subst with predicate %z. dvd p z (z a genuine Free, then abstracted). *)
fun dvd_cong_rS (pT, xT, yT) hxy hdvd =
  let
    val zF   = Free("z_dc", natT);
    val Pabs = Term.lambda zF (dvd pT zF);    (* %z. dvd p z, correct de Bruijn *)
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 xT), (("b",0), ctermS2 yT)] oeq_subst_vS);
  in (inst OF [hxy]) OF [hdvd] end;

val () = out "EL_HELPERS_READY\n";

(* ============================================================================
   mult_le_mono : jT (le j k) ==> jT (le (mult c j) (mult c k))
   ----------------------------------------------------------------------------
   le j k = Ex(e. oeq k (add j e)).  exE witness e, he : oeq k (add j e).
   Goal le (mult c j)(mult c k) witness (mult c e):
     mult c k = mult c (add j e)          (mult_cong_r on he)
              = add (mult c j) (mult c e)  (left_distrib).
   ============================================================================ *)
val mult_le_mono =
  let
    val jF = Free("j", natT); val kF = Free("k", natT); val cF = Free("c", natT);
    val leHypP = jT (le jF kF);
    val leHyp  = Thm.assume (ctermS2 leHypP);
    val Pabs   = Abs("p", natT, oeq kF (add jF (Bound 0)));   (* body of le j k *)
    val goalC  = le (mult cF jF) (mult cF kF);
    fun body e (he : thm) =                          (* he : oeq k (add j e) *)
      let
        val mcong = mult_cong_rS (cF, kF, add jF e) he;        (* (c*k) = (c*(j+e)) *)
        val ld    = left_distrib_atS (cF, jF, e);              (* (c*(j+e)) = ((c*j)+(c*e)) *)
        val witEq = oeq_trans OF [mcong, ld];                  (* (c*k) = ((c*j)+(c*e)) *)
        val leNew = le_introS (mult cF jF, mult cF kF, mult cF e) witEq;
      in leNew end;
    val afterExE = exE_elimS2 (Pabs, goalC) leHyp "ew" body;
    val disch    = Thm.implies_intr (ctermS2 leHypP) afterExE;
  in varify disch end;

val mult_le_mono_vS = varify mult_le_mono;
fun mult_le_mono_atS (cT, jT_, kT) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("c",0), ctermS2 cT), (("j",0), ctermS2 jT_), (("k",0), ctermS2 kT)] mult_le_mono_vS)
  in Thm.implies_elim inst h end;

(* ============================================================================
   dvd_diff : jT (dvd p x) ==> jT (dvd p (add x y)) ==> jT (dvd p y)
   ----------------------------------------------------------------------------
   exE dvd p x        -> witness j,  hj : oeq x (mult p j)
   exE dvd p (add x y)-> witness kk, hk : oeq (add x y) (mult p kk)
   From hj : add x y = add (mult p j) y  (add_cong_l) ; with hk (sym) :
     mult p kk = add (mult p j) y.                            [STAR]
   le_total j kk:
     le j kk : kk = add j e (exE).  mult p kk = add (mult p j)(mult p e) [left_distrib
       after mult_cong_r].  With [STAR] + add_left_cancel : oeq y (mult p e) -> dvd p y.
     le kk j : mult p kk <= mult p j [mult_le_mono].  But from [STAR] mult p kk =
       add (mult p j) y = add y (mult p j) >= mult p j [le_add], so by le_antisym
       mult p kk = mult p j ; add_left_cancel on [STAR] => y = 0 => dvd p y [dvd_zero].
   ============================================================================ *)
val dvd_diff =
  let
    val pF = Free("p", natT); val xF = Free("x", natT); val yF = Free("y", natT);
    val H1prop = jT (dvd pF xF);            (* dvd p x *)
    val H2prop = jT (dvd pF (add xF yF));   (* dvd p (add x y) *)
    val H1 = Thm.assume (ctermS2 H1prop);
    val H2 = Thm.assume (ctermS2 H2prop);
    val P1abs = Abs("k", natT, oeq xF (mult pF (Bound 0)));            (* dvd p x body *)
    val P2abs = Abs("k", natT, oeq (add xF yF) (mult pF (Bound 0)));   (* dvd p (add x y) body *)
    val goalC = dvd pF yF;

    fun outer j (hj : thm) =                 (* hj : oeq x (mult p j) *)
      let
        fun inner kk (hk : thm) =            (* hk : oeq (add x y) (mult p kk) *)
          let
            (* [STAR] : mult p kk = add (mult p j) y *)
            val congXY = add_cong_lS (xF, mult pF j, yF) hj;   (* (x+y) = ((p*j)+y) *)
            val hk_sym = oeq_sym OF [hk];                      (* (p*kk) = (x+y) *)
            val star   = oeq_trans OF [hk_sym, congXY];        (* (p*kk) = ((p*j)+y) *)

            val tot = le_total_atS (j, kk);                    (* Disj (le j kk)(le kk j) *)

            (* CASE A : le j kk -> exE witness e (kk = j+e), oeq y (p*e), dvd p y *)
            val caseA =
              let
                val hLE = Thm.assume (ctermS2 (jT (le j kk)));
                val Q1abs = Abs("e", natT, oeq kk (add j (Bound 0)));   (* body of le j kk *)
                fun ebody e (he : thm) =          (* he : oeq kk (add j e) *)
                  let
                    val mcong = mult_cong_rS (pF, kk, add j e) he;     (* (p*kk) = (p*(j+e)) *)
                    val ld    = left_distrib_atS (pF, j, e);           (* (p*(j+e)) = ((p*j)+(p*e)) *)
                    val pkk_split = oeq_trans OF [mcong, ld];          (* (p*kk) = ((p*j)+(p*e)) *)
                    val starSym = oeq_sym OF [star];                   (* ((p*j)+y) = (p*kk) *)
                    val eqj   = oeq_trans OF [starSym, pkk_split];     (* ((p*j)+y) = ((p*j)+(p*e)) *)
                    val canc  = add_left_cancel_atS (mult pF j, yF, mult pF e) eqj;  (* oeq y (p*e) *)
                    val dvdY  = dvd_introS (pF, yF, e) canc;           (* dvd p y *)
                  in dvdY end;
                val g = exE_elimS2 (Q1abs, goalC) hLE "e_le" ebody;
              in Thm.implies_intr (ctermS2 (jT (le j kk))) g end;

            (* CASE B : le kk j -> p*kk <= p*j, but p*kk = p*j + y >= p*j; antisym => y=0 *)
            val caseB =
              let
                val hLE2 = Thm.assume (ctermS2 (jT (le kk j)));
                val le_pk_pj = mult_le_mono_atS (pF, kk, j) hLE2;          (* le (p*kk)(p*j) *)
                val le_pj_pk = le_introS (mult pF j, mult pF kk, yF) star; (* le (p*j)(p*kk) wit y *)
                val eqM = le_antisym_atS (mult pF kk, mult pF j) le_pk_pj le_pj_pk; (* oeq (p*kk)(p*j) *)
                val eqM_sym = oeq_sym OF [eqM];                    (* (p*j) = (p*kk) *)
                val pj_star = oeq_trans OF [eqM_sym, star];        (* (p*j) = ((p*j)+y) *)
                val pj0     = add0rS_at (mult pF j);               (* ((p*j)+0) = (p*j) *)
                val lhs0    = oeq_trans OF [pj0, pj_star];         (* ((p*j)+0) = ((p*j)+y) *)
                val cancY   = add_left_cancel_atS (mult pF j, ZeroC, yF) lhs0;  (* oeq 0 y *)
                val dvd_p0  = dvd_zeroS_at pF;                     (* dvd p 0 *)
                val dvdY    = dvd_cong_rS (pF, ZeroC, yF) cancY dvd_p0;  (* dvd p y (subst 0->y) *)
              in Thm.implies_intr (ctermS2 (jT (le kk j))) dvdY end;

            val combined = disjE_elimS2 (le j kk, le kk j, goalC) tot caseA caseB;
          in combined end;
        val g = exE_elimS2 (P2abs, goalC) H2 "kk_w" inner;
      in g end;

    val res = exE_elimS2 (P1abs, goalC) H1 "j_w" outer;
    val d1 = Thm.implies_intr (ctermS2 H2prop) res;
    val d2 = Thm.implies_intr (ctermS2 H1prop) d1;
  in varify d2 end;

(* ============================================================================
   prime_not_dvd_pos_lt : jT (dvd p r) ==> jT (lt Zero r) ==> jT (lt r p) ==> jT oFalse
   ----------------------------------------------------------------------------
   dvd p r + r != 0 (from lt Zero r) => dvd_le => le p r.  lt r p = le (Suc r) p,
   and le p r => le (Suc r) r [le_trans] = lt r r => lt_irrefl => oFalse.
   ============================================================================ *)
val prime_not_dvd_pos_lt =
  let
    val pF = Free("p", natT); val rF = Free("r", natT);
    val dvdHypP = jT (dvd pF rF);
    val posHypP = jT (lt ZeroC rF);            (* le (Suc 0) r *)
    val ltHypP  = jT (lt rF pF);               (* le (Suc r) p *)
    val dvdHyp  = Thm.assume (ctermS2 dvdHypP);
    val posHyp  = Thm.assume (ctermS2 posHypP);
    val ltHyp   = Thm.assume (ctermS2 ltHypP);

    (* META nonzero premise (oeq r 0 ==> oFalse) for dvd_le, from lt Zero r.
       lt 0 r = le (Suc 0) r = Ex(e. oeq r (add (Suc 0) e)).  assume oeq r 0;
       exE: r = add (Suc 0) e = Suc(0 + e) = Suc e; with oeq r 0 -> Suc e = 0 -> oFalse. *)
    val nzMeta =
      let
        val ez = Thm.assume (ctermS2 (jT (oeq rF ZeroC)));    (* oeq r 0 *)
        val PabsPos = Abs("e", natT, oeq rF (add (suc ZeroC) (Bound 0)));   (* body of le (Suc 0) r *)
        fun body e (he : thm) =                  (* he : oeq r (add (Suc 0) e) *)
          let
            val aS   = addSucS_at (ZeroC, e);     (* (Suc 0 + e) = Suc(0 + e) *)
            val s0e  = Suc_cong OF [add0S_at e];  (* Suc(0 + e) = Suc e *)
            val a1c  = oeq_trans OF [aS, s0e];    (* (Suc 0 + e) = Suc e *)
            val r_Se = oeq_trans OF [he, a1c];    (* r = Suc e *)
            val z_Se = oeq_trans OF [oeq_sym OF [ez], r_Se];  (* 0 = Suc e *)
            val Se_z = oeq_sym OF [z_Se];         (* Suc e = 0 *)
          in (Suc_neq_Zero_atS e) OF [Se_z] end;  (* oFalse *)
        val falseThm = exE_elimS2 (PabsPos, oFalseC) posHyp "e_pos" body;
      in Thm.implies_intr (ctermS2 (jT (oeq rF ZeroC))) falseThm end;  (* jT(oeq r 0)==>jT oFalse *)

    val le_p_r   = dvd_le_atS (pF, rF) dvdHyp nzMeta;          (* le p r *)
    (* le (Suc r) r from le (Suc r) p and le p r  by le_trans *)
    val le_Sr_r  = le_trans_atS (suc rF, pF, rF) ltHyp le_p_r; (* le (Suc r) r = lt r r *)
    val fls      = lt_irrefl_atS rF le_Sr_r;                   (* oFalse *)
    val d1 = Thm.implies_intr (ctermS2 ltHypP)  fls;
    val d2 = Thm.implies_intr (ctermS2 posHypP) d1;
    val d3 = Thm.implies_intr (ctermS2 dvdHypP) d2;
  in varify d3 end;

(* ============================================================================
   dvd_mult_assoc_l : jT (dvd p (mult a b)) ==> jT (dvd p (mult (mult a q) b))
   ----------------------------------------------------------------------------
   reassoc :  (a*q)*b = a*(q*b) = a*(b*q) = (a*b)*q.  So
     dvd_mult_right (dvd p (mult a b)) : dvd p (mult (mult a b) q)
   then rewrite the dividend (mult (mult a b) q) to (mult (mult a q) b) via
   dvd_cong_r with the equation  oeq (mult (mult a b) q) (mult (mult a q) b).
   ============================================================================ *)
val dvd_mult_assoc_l =
  let
    val pF = Free("p", natT); val aF = Free("a", natT);
    val bF = Free("b", natT); val qF = Free("q", natT);
    val dvdHypP = jT (dvd pF (mult aF bF));
    val dvdHyp  = Thm.assume (ctermS2 dvdHypP);

    (* dvd p (mult (mult a b) q) *)
    val dvd_abq = dvd_mult_right_atS (pF, mult aF bF, qF) dvdHyp;   (* dvd p ((a*b)*q) *)

    (* reassoc equation : ((a*b)*q) = ((a*q)*b)
         (a*b)*q = a*(b*q)            [mult_assoc]
                 = a*(q*b)            [mult_cong_r (mult_comm b q)]
                 = (a*q)*b            [mult_assoc sym] *)
    val e1 = mult_assoc_atS (aF, bF, qF);                  (* ((a*b)*q) = (a*(b*q)) *)
    val cbq = mult_comm_atS (bF, qF);                      (* (b*q) = (q*b) *)
    val e2 = mult_cong_rS (aF, mult bF qF, mult qF bF) cbq;(* (a*(b*q)) = (a*(q*b)) *)
    val e3 = mult_assoc_atS (aF, qF, bF);                  (* ((a*q)*b) = (a*(q*b)) *)
    val e3s = oeq_sym OF [e3];                             (* (a*(q*b)) = ((a*q)*b) *)
    val reassoc = oeq_trans OF [oeq_trans OF [e1, e2], e3s]; (* ((a*b)*q) = ((a*q)*b) *)

    val res = dvd_cong_rS (pF, mult (mult aF bF) qF, mult (mult aF qF) bF) reassoc dvd_abq;
    val disch = Thm.implies_intr (ctermS2 dvdHypP) res;
  in varify disch end;

(* ============================================================================
   VALIDATION : each helper 0-hyp AND aconv its intended schematic goal
   (built with the SAME le/lt/dvd abbreviations so Ex-bodies match exactly).
   ============================================================================ *)
val jVe = Var (("j",0), natT);
val kVe = Var (("k",0), natT);
val cVe = Var (("c",0), natT);
val pVe = Var (("p",0), natT);
val rVe = Var (("r",0), natT);
val xVe = Var (("x",0), natT);
val yVe = Var (("y",0), natT);
val aVe = Var (("a",0), natT);
val bVe = Var (("b",0), natT);
val qVe = Var (("q",0), natT);

val mult_le_mono_intended =
  Logic.mk_implies (jT (le jVe kVe), jT (le (mult cVe jVe) (mult cVe kVe)));
val dvd_diff_intended =
  Logic.mk_implies (jT (dvd pVe xVe),
    Logic.mk_implies (jT (dvd pVe (add xVe yVe)), jT (dvd pVe yVe)));
val prime_not_dvd_pos_lt_intended =
  Logic.mk_implies (jT (dvd pVe rVe),
    Logic.mk_implies (jT (lt ZeroC rVe),
      Logic.mk_implies (jT (lt rVe pVe), jT oFalseC)));
val dvd_mult_assoc_l_intended =
  Logic.mk_implies (jT (dvd pVe (mult aVe bVe)),
    jT (dvd pVe (mult (mult aVe qVe) bVe)));

val r_mlm = checkS2 ("mult_le_mono",         mult_le_mono,         mult_le_mono_intended);
val r_ddf = checkS2 ("dvd_diff",             dvd_diff,             dvd_diff_intended);
val r_pnd = checkS2 ("prime_not_dvd_pos_lt", prime_not_dvd_pos_lt, prime_not_dvd_pos_lt_intended);
val r_dma = checkS2 ("dvd_mult_assoc_l",     dvd_mult_assoc_l,     dvd_mult_assoc_l_intended);

(* ---- SOUNDNESS PROBES : kernel must reject obvious weakenings ---- *)
val probe_pnd =     (* prime_not_dvd_pos_lt must NOT be the unconditional oFalse *)
  not ((Thm.prop_of prime_not_dvd_pos_lt) aconv (jT oFalseC));
val probe_dma =     (* dvd_mult_assoc_l must NOT collapse to a trivial reflexive dvd *)
  not ((Thm.prop_of dvd_mult_assoc_l) aconv (jT (dvd pVe (mult aVe bVe))));

val () =
  if probe_pnd andalso probe_dma
  then out "PROBE_OK euclid helpers are conditional/nontrivial\n"
  else out "PROBE_UNSOUND a euclid helper collapsed!\n";

val () =
  if r_mlm andalso r_ddf andalso r_pnd andalso r_dma andalso probe_pnd andalso probe_dma
  then out "EL_HELPERS_OK\n"
  else out "EL_HELPERS_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  EUCLID'S LEMMA  (Stage 2 of FTA uniqueness, via GAUSS DESCENT)  ***
   ----------------------------------------------------------------------------
   Everything routes through ctxtS2 / ctermS2.  The structural prime is `prime2`
   (the capture-avoiding one that prime_cases / prime_divisor_exists already use):
     prime2 p = Conj (lt (Suc Zero) p)
                     (Forall (%d. Imp (dvd d p) (Disj (oeq d (Suc Zero)) (oeq d p))))
   TARGET:
     euclid_lemma : jT (prime2 p) ==> jT (dvd p (mult a b))
                      ==> jT (Disj (dvd p a) (dvd p b))
   Proved in two steps:
     bounded_euclid : jT (lt a p) ==> jT (prime2 p) ==> jT (dvd p (mult a b))
                        ==> jT (Disj (dvd p a) (dvd p b))   [strong_induct on a]
     euclid_lemma   : reduce a mod p, descend to bounded_euclid at the remainder.
   ============================================================================ *)

val () = out "EUCLID_BEGIN\n";

(* ---- lift the remaining dependency lemmas onto ctxtS2 ---- *)
val dvd_add_vS       = varify dvd_add;        (* jT (dvd ?d ?m) ==> jT (dvd ?d ?n) ==> jT (dvd ?d (add ?m ?n)) *)
val mult_1_left_vS   = varify mult_1_left;    (* oeq (mult (Suc 0) ?n) ?n *)
val lt_trans_vS      = varify lt_trans;       (* jT (lt ?a ?b) ==> jT (lt ?b ?c) ==> jT (lt ?a ?c) *)
val le_add_vS        = varify le_add;         (* jT (le ?m (add ?m ?p)) *)

fun dvd_add_atS (dT, mT, nT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("d",0), ctermS2 dT), (("m",0), ctermS2 mT), (("n",0), ctermS2 nT)] dvd_add_vS)
  in (inst OF [h1]) OF [h2] end;
fun mult1lS_at t = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] mult_1_left_vS);
fun lt_trans_atS (aT, bT, cT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("a",0), ctermS2 aT), (("b",0), ctermS2 bT), (("c",0), ctermS2 cT)] lt_trans_vS)
  in (inst OF [h1]) OF [h2] end;
fun le_add_atS (mT, pT) = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mT), (("p",0), ctermS2 pT)] le_add_vS);

(* div_mod_exists applied on ctxtS2 : divisor dt, dividend at, given (lt 0 dt) ->
     jT (Ex q. Ex r. Conj (oeq at (add (mult dt q) r)) (lt r dt)) *)
fun div_mod_atS (atDividend, dtDivisor) hpos =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("a",0), ctermS2 atDividend), (("b",0), ctermS2 dtDivisor)] (varify div_mod_exists))
  in Thm.implies_elim inst hpos end;

(* ---- prime2 destructors on ctxtS2 ---- *)
fun prime2_gt1_atS p hPrime =                  (* jT (prime2 p) -> jT (lt (Suc 0) p) *)
  conjunct1_atS2 (lt (suc ZeroC) p, mkForall (ppAbs p)) hPrime;
fun prime2_div_atS (p, d) hPrime hDvdDP =      (* jT (prime2 p) -> jT (dvd d p) -> jT (Disj (oeq d 1)(oeq d p)) *)
  let
    val faThm = conjunct2_atS2 (lt (suc ZeroC) p, mkForall (ppAbs p)) hPrime;  (* Forall (ppAbs p) *)
    val impAt = allE_atS2 (ppAbs p) d faThm;   (* jT (Imp (dvd d p)(Disj (oeq d 1)(oeq d p))) *)
  in mp_atS2 (dvd d p, mkDisj (oeq d (suc ZeroC)) (oeq d p)) impAt hDvdDP end;

(* ---- oeq-subst helper on ctxtS2 : oeq x y -> jT (P x) -> jT (P y) with P = %z. lt c z etc.
   we just use oeq_subst_vS directly through small inline closures below. ---- *)
fun oeq_rewrite_atS (Pabs, xT, yT) hxy hPx =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 xT), (("b",0), ctermS2 yT)] oeq_subst_vS)
  in (inst OF [hxy]) OF [hPx] end;

(* lt 0 (Suc t) for any t : witness via le (Suc 0) (Suc t).  0 < Suc t = le 1 (Suc t).
   Suc t = add (Suc 0) t  (since add (Suc 0) t = Suc (add 0 t) = Suc t). *)
fun lt_zero_suc_atS t =
  let
    val aS  = addSucS_at (ZeroC, t);                 (* (Suc 0 + t) = Suc(0 + t) *)
    val s0t = Suc_cong OF [add0S_at t];              (* Suc(0 + t) = Suc t *)
    val a1  = oeq_trans OF [aS, s0t];                (* (Suc 0 + t) = Suc t *)
    val eqn = oeq_sym OF [a1];                       (* Suc t = (Suc 0 + t) *)
  in le_introS (suc ZeroC, suc t, t) eqn end;        (* le (Suc 0) (Suc t) = lt 0 (Suc t) *)

(* right_distrib on ctxtS2 : oeq (mult (add ?m ?n) ?k) (add (mult ?m ?k)(mult ?n ?k)) *)
val right_distrib_vS = varify right_distrib;
fun rdist_at_S2 (mT, nT, kT) = beta_norm (Drule.infer_instantiate ctxtS2
      [(("m",0), ctermS2 mT), (("n",0), ctermS2 nT), (("k",0), ctermS2 kT)] right_distrib_vS);

(* applicators for the four euclid helpers, lifted to ctxtS2 *)
val dvd_diff_vS_ap             = varify dvd_diff;
val dvd_mult_assoc_l_vS_ap     = varify dvd_mult_assoc_l;
val prime_not_dvd_pos_lt_vS_ap = varify prime_not_dvd_pos_lt;
fun dvd_diff_atS (pT, xT, yT) hdpx hdpxy =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("p",0), ctermS2 pT), (("x",0), ctermS2 xT), (("y",0), ctermS2 yT)] dvd_diff_vS_ap)
  in (inst OF [hdpx]) OF [hdpxy] end;
fun dvd_mult_assoc_l_atS (pT, aT, bT, qT) hdvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("p",0), ctermS2 pT), (("a",0), ctermS2 aT), (("b",0), ctermS2 bT), (("q",0), ctermS2 qT)] dvd_mult_assoc_l_vS_ap)
  in Thm.implies_elim inst hdvd end;
fun prime_not_dvd_pos_lt_atS (pT, rT) hdvd hpos hlt =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("p",0), ctermS2 pT), (("r",0), ctermS2 rT)] prime_not_dvd_pos_lt_vS_ap)
  in ((inst OF [hdvd]) OF [hpos]) OF [hlt] end;

(* general division-result abstraction builders matching div_mod_atS's Ex body *)
fun innerDivAbsN divisorT dividendT qTerm =     (* %r. Conj (oeq dividend (add (mult divisor q) r))(lt r divisor) *)
  let val rF = Free("r_rb", natT)
  in Term.lambda rF (mkConj (oeq dividendT (add (mult divisorT qTerm) rF)) (lt rF divisorT)) end;
fun rmDivBodyN divisorT dividendT =             (* %q. Ex (%r. ...) *)
  let val qF = Free("q_rb", natT)
  in Term.lambda qF (mkEx (innerDivAbsN divisorT dividendT qF)) end;

val () = out "EUCLID_HELPERS_READY\n";

(* ============================================================================
   bounded_euclid : jT (lt a p) ==> jT (prime2 p) ==> jT (dvd p (mult a b))
                      ==> jT (Disj (dvd p a) (dvd p b))
   Strong induction on a.  Predicate
     Bpred a := Imp (lt a p) (Imp (prime2 p) (Imp (dvd p (mult a b))
                              (Disj (dvd p a) (dvd p b))))
   (p and b are FIXED Frees of the surrounding let; the descent IH is over a.)
   ============================================================================ *)
val bounded_euclid =
  let
    val pF = Free("p", natT); val bF = Free("b", natT);

    (* the course-of-values predicate, capture-free (p,b free; bound var = a) *)
    fun Bbody aT = mkImp (lt aT pF)
                     (mkImp (prime2 pF)
                        (mkImp (dvd pF (mult aT bF))
                           (mkDisj (dvd pF aT) (dvd pF bF))));
    val Bpred = let val aV = Free("a_B", natT) in Term.lambda aV (Bbody aV) end;

    (* ---- the strong-induction STEP body : fix n, given strong IH, prove Trueprop (B n) ---- *)
    val nStep = Free("n_be", natT);
    val mIH   = Free("m_be", natT);
    val Gprop = Logic.all mIH (Logic.mk_implies (jT (lt mIH nStep), jT (Bbody mIH)));
    val Hthm  = Thm.assume (ctermS2 Gprop);
    fun applyIH dt h_lt =
      let val hAt = Thm.forall_elim (ctermS2 dt) Hthm  (* lt d n ==> jT (B d) *)
      in Thm.implies_elim hAt h_lt end;

    (* assume the three premises lt n p, prime2 p, dvd p (mult n b) *)
    val ltP    = jT (lt nStep pF);          val hLtNP = Thm.assume (ctermS2 ltP);
    val prP    = jT (prime2 pF);            val hPr   = Thm.assume (ctermS2 prP);
    val dvdP   = jT (dvd pF (mult nStep bF)); val hDvdNB= Thm.assume (ctermS2 dvdP);
    val goalC  = mkDisj (dvd pF nStep) (dvd pF bF);

    (* ex_middle on (dvd p n) *)
    val em = ex_middle_atS (dvd pF nStep);  (* Disj (dvd p n) (neg (dvd p n)) *)

    (* CASE 1 : dvd p n -> disjI1 *)
    val case_dvd =
      let val hd = Thm.assume (ctermS2 (jT (dvd pF nStep)))
      in Thm.implies_intr (ctermS2 (jT (dvd pF nStep)))
           (disjI1S2_at (dvd pF nStep, dvd pF bF) hd) end;

    (* CASE 2 : neg (dvd p n) -> case on n (zero/suc) *)
    val case_ndvd =
      let
        val hNeg = Thm.assume (ctermS2 (jT (neg (dvd pF nStep))));
        val dz   = dzosS_at nStep;          (* Disj (oeq n 0) (Ex q. oeq n (Suc q)) *)

        (* n = 0 : dvd p 0 -> disjI1 (dvd_zero rewritten to dvd p n) *)
        val caseZero =
          let
            val ez   = Thm.assume (ctermS2 (jT (oeq nStep ZeroC)));   (* n = 0 *)
            val ez_s = oeq_sym OF [ez];                               (* 0 = n *)
            val dvdp0= dvd_zeroS_at pF;                               (* dvd p 0 *)
            val dvdpn= dvd_cong_rS (pF, ZeroC, nStep) ez_s dvdp0;     (* dvd p n *)
            val g    = disjI1S2_at (dvd pF nStep, dvd pF bF) dvdpn;
          in Thm.implies_intr (ctermS2 (jT (oeq nStep ZeroC))) g end;

        (* n = Suc q : sub-case on q (zero -> n=1 ; suc -> 1<n descent) *)
        val PabsQ = Abs("q", natT, oeq nStep (suc (Bound 0)));
        val caseSuc =
          let
            val exq = Thm.assume (ctermS2 (jT (mkEx PabsQ)));
            fun qbody q (hq : thm) =          (* hq : oeq n (Suc q) *)
              let
                val dzq = dzosS_at q;          (* Disj (oeq q 0)(Ex q'. oeq q (Suc q')) *)

                (* q = 0  ->  n = Suc 0 = 1 ; mult 1 b = b -> dvd p b -> disjI2 *)
                val caseQZero =
                  let
                    val eqz   = Thm.assume (ctermS2 (jT (oeq q ZeroC)));   (* q = 0 *)
                    val n_S0  = oeq_trans OF [hq, Suc_cong OF [eqz]];       (* n = Suc 0 *)
                    (* dvd p (mult n b) ; rewrite mult n b -> mult (Suc 0) b -> b *)
                    val mcong = mult_cong_lS (nStep, suc ZeroC, bF) n_S0;   (* (n*b) = ((Suc 0)*b) *)
                    val m1b   = mult1lS_at bF;                             (* ((Suc 0)*b) = b *)
                    val nb_b  = oeq_trans OF [mcong, m1b];                  (* (n*b) = b *)
                    val dvdpb = dvd_cong_rS (pF, mult nStep bF, bF) nb_b hDvdNB;  (* dvd p b *)
                    val g     = disjI2S2_at (dvd pF nStep, dvd pF bF) dvdpb;
                  in Thm.implies_intr (ctermS2 (jT (oeq q ZeroC))) g end;

                (* q = Suc q' -> n = Suc (Suc q'), so 1 < n.  THE DESCENT. *)
                val PabsQ2 = Abs("q2", natT, oeq q (suc (Bound 0)));
                val caseQSuc =
                  let
                    val exq2 = Thm.assume (ctermS2 (jT (mkEx PabsQ2)));
                    fun q2body q2 (hq2 : thm) =      (* hq2 : oeq q (Suc q2) *)
                      let
                        (* n = Suc q = Suc (Suc q2) ; 1 < n :  lt (Suc 0) n.
                           lt (Suc 0) n = le (Suc(Suc 0)) n.  n = Suc(Suc q2);
                           le 2 (Suc(Suc q2)) witness q2 : Suc(Suc q2) = (Suc(Suc 0)) + q2 *)
                        val n_Sq   = hq;                              (* n = Suc q *)
                        val q_Sq2  = hq2;                             (* q = Suc q2 *)
                        val n_SSq2 = oeq_trans OF [n_Sq, Suc_cong OF [q_Sq2]];  (* n = Suc(Suc q2) *)
                        (* (Suc(Suc 0)) + q2 = Suc((Suc 0)+q2) = Suc(Suc(0+q2)) = Suc(Suc q2) *)
                        val a1 = addSucS_at (suc ZeroC, q2);          (* ((Suc(Suc 0)) + q2) = Suc((Suc 0)+q2) *)
                        val a2 = Suc_cong OF [addSucS_at (ZeroC, q2)];(* Suc((Suc 0)+q2) = Suc(Suc(0+q2)) *)
                        val a3 = Suc_cong OF [Suc_cong OF [add0S_at q2]];  (* Suc(Suc(0+q2)) = Suc(Suc q2) *)
                        val sum_n = oeq_trans OF [oeq_trans OF [a1, a2], a3];  (* (2 + q2) = Suc(Suc q2) *)
                        val n_sum = oeq_trans OF [n_SSq2, oeq_sym OF [sum_n]]; (* n = (2 + q2) *)
                        val lt1n  = le_introS (suc (suc ZeroC), nStep, q2) n_sum; (* le 2 n = lt 1 n *)

                        (* div_mod_exists : divisor n, dividend p, need lt 0 n (n = Suc(Suc q2)) *)
                        val pos_n = lt_zero_suc_atS (suc q2);         (* lt 0 (Suc(Suc q2)) *)
                        (* rewrite lt 0 (Suc(Suc q2)) -> lt 0 n via n = Suc(Suc q2) (sym).
                           CAPTURE-AVOIDING: build %z. lt 0 z with Term.lambda over a Free. *)
                        val PabsPos = let val zF = Free("z_lt",natT) in Term.lambda zF (lt ZeroC zF) end;
                        val pos_n'  = oeq_rewrite_atS (PabsPos, suc (suc q2), nStep) (oeq_sym OF [n_SSq2]) pos_n;  (* lt 0 n *)

                        val dmEx = div_mod_atS (pF, nStep) pos_n';    (* Ex qq. Ex r. Conj (oeq p (add (mult n qq) r))(lt r n) *)

                        (* inner double exE : qq, then r *)
                        fun innerQ qq (hQQex : thm) =
                          let
                            fun innerR r (hConj : thm) =     (* hConj : Conj (oeq p (add (mult n qq) r)) (lt r n) *)
                              let
                                val hPeq  = conjunct1_atS2 (oeq pF (add (mult nStep qq) r), lt r nStep) hConj;  (* p = n*qq + r *)
                                val hRltN = conjunct2_atS2 (oeq pF (add (mult nStep qq) r), lt r nStep) hConj;  (* r < n *)

                                (* r < p  by lt_trans (r < n)(n < p)   [n < p = hLtNP] *)
                                val hRltP = lt_trans_atS (r, nStep, pF) hRltN hLtNP;   (* lt r p *)

                                (* ex_middle on (oeq r 0) to split r=0 (contra) / r != 0 (descent) *)
                                val emr = ex_middle_atS (oeq r ZeroC);   (* Disj (oeq r 0)(neg(oeq r 0)) *)

                                (* SUBCASE r = 0 : p = n*qq -> n | p -> prime: n=1 \/ n=p, both contra *)
                                val subZero =
                                  let
                                    val er0   = Thm.assume (ctermS2 (jT (oeq r ZeroC)));   (* r = 0 *)
                                    (* p = add (mult n qq) r = add (mult n qq) 0 = mult n qq *)
                                    val cong0 = add_cong_rS (mult nStep qq, r, ZeroC) er0;  (* (n*qq + r) = (n*qq + 0) *)
                                    val a0r   = add0rS_at (mult nStep qq);                  (* (n*qq + 0) = (n*qq) *)
                                    val sum_nq= oeq_trans OF [cong0, a0r];                  (* (n*qq + r) = (n*qq) *)
                                    val p_nq  = oeq_trans OF [hPeq, sum_nq];                (* p = (n*qq) *)
                                    val dvd_np= dvd_introS (nStep, pF, qq) p_nq;            (* dvd n p *)
                                    (* prime2 p : n | p -> n=1 \/ n=p *)
                                    val disj_n= prime2_div_atS (pF, nStep) hPr dvd_np;      (* Disj (oeq n 1)(oeq n p) *)
                                    (* n=1 contra (1<n) ; n=p contra (n<p) *)
                                    val cA =
                                      let
                                        val hn1 = Thm.assume (ctermS2 (jT (oeq nStep (suc ZeroC))));  (* n = 1 *)
                                        (* lt 1 n  with n=1 -> lt 1 1 -> lt_irrefl (capture-avoiding pred) *)
                                        val Plt1 = let val zF = Free("z_p1",natT) in Term.lambda zF (lt (suc ZeroC) zF) end;
                                        val lt11 = oeq_rewrite_atS (Plt1, nStep, suc ZeroC) hn1 lt1n;  (* lt 1 1 *)
                                        val fls  = lt_irrefl_atS (suc ZeroC) lt11;
                                        val g    = Thm.implies_elim (oFalse_elimS_at goalC) fls;
                                      in Thm.implies_intr (ctermS2 (jT (oeq nStep (suc ZeroC)))) g end;
                                    val cB =
                                      let
                                        val hnp = Thm.assume (ctermS2 (jT (oeq nStep pF)));    (* n = p *)
                                        (* lt n p  with n=p -> lt p p -> lt_irrefl (capture-avoiding pred) *)
                                        val Pltp = let val zF = Free("z_pp",natT) in Term.lambda zF (lt zF pF) end;
                                        val ltpp = oeq_rewrite_atS (Pltp, nStep, pF) hnp hLtNP;  (* lt p p *)
                                        val fls  = lt_irrefl_atS pF ltpp;
                                        val g    = Thm.implies_elim (oFalse_elimS_at goalC) fls;
                                      in Thm.implies_intr (ctermS2 (jT (oeq nStep pF))) g end;
                                    val g = disjE_elimS2 (oeq nStep (suc ZeroC), oeq nStep pF, goalC) disj_n cA cB;
                                  in Thm.implies_intr (ctermS2 (jT (oeq r ZeroC))) g end;

                                (* SUBCASE r != 0 : 0 < r ; derive dvd p (mult r b), descend at r *)
                                val subNZ =
                                  let
                                    val hRnz = Thm.assume (ctermS2 (jT (neg (oeq r ZeroC))));  (* r != 0 *)
                                    (* 0 < r from r != 0 : case r (zero -> contra ; suc -> lt_zero_suc) *)
                                    val pos_r =
                                      let
                                        val dzr = dzosS_at r;     (* Disj (oeq r 0)(Ex r'. oeq r (Suc r')) *)
                                        val crz =
                                          let val erz = Thm.assume (ctermS2 (jT (oeq r ZeroC)))
                                              val fls = mp_atS2 (oeq r ZeroC, oFalseC) hRnz erz
                                          in Thm.implies_intr (ctermS2 (jT (oeq r ZeroC)))
                                               (Thm.implies_elim (oFalse_elimS_at (lt ZeroC r)) fls) end;
                                        val PabsR' = Abs("r2", natT, oeq r (suc (Bound 0)));
                                        val crs =
                                          let val exr' = Thm.assume (ctermS2 (jT (mkEx PabsR')))
                                              fun rb r' (hr' : thm) =   (* hr' : oeq r (Suc r') *)
                                                let
                                                  val pos = lt_zero_suc_atS r';   (* lt 0 (Suc r') *)
                                                  val Ppos= let val zF = Free("z_pr",natT) in Term.lambda zF (lt ZeroC zF) end;
                                                in oeq_rewrite_atS (Ppos, suc r', r) (oeq_sym OF [hr']) pos end;  (* lt 0 r *)
                                              val g = exE_elimS2 (PabsR', lt ZeroC r) exr' "rp" rb
                                          in Thm.implies_intr (ctermS2 (jT (mkEx PabsR'))) g end;
                                      in disjE_elimS2 (oeq r ZeroC, mkEx PabsR', lt ZeroC r) dzr crz crs end;  (* lt 0 r *)

                                    (* DERIVE dvd p (mult r b) :
                                       mult p b = mult (add (mult n qq) r) b      (mult_cong_l on hPeq)
                                                = add (mult (mult n qq) b) (mult r b)   (right_distrib)
                                       p | mult p b   (witness b : mult p b = p * b)
                                       p | mult (mult n qq) b   (dvd_mult_assoc_l on dvd p (mult n b))
                                       dvd_diff (p | (n*qq)*b)(p | ((n*qq)*b + r*b) = p*b) => p | (r*b) *)
                                    val mcong = mult_cong_lS (pF, add (mult nStep qq) r, bF) hPeq;  (* (p*b) = ((n*qq + r)*b) *)
                                    val rdist = rdist_at_S2 (mult nStep qq, r, bF);   (* ((n*qq + r)*b) = ((n*qq)*b + r*b) *)
                                    val pb_split = oeq_trans OF [mcong, rdist];       (* (p*b) = ((n*qq)*b + r*b) *)
                                    (* p | mult p b : witness b ; oeq (mult p b)(mult p b) *)
                                    val dvd_p_pb = dvd_introS (pF, mult pF bF, bF) (oeqreflS_at (mult pF bF));  (* dvd p (mult p b) *)
                                    (* rewrite dividend (mult p b) -> ((n*qq)*b + r*b) *)
                                    val dvd_p_sum = dvd_cong_rS (pF, mult pF bF, add (mult (mult nStep qq) bF) (mult r bF)) pb_split dvd_p_pb;  (* dvd p ((n*qq)*b + r*b) *)
                                    (* p | (n*qq)*b  from dvd p (mult n b) via dvd_mult_assoc_l (a:=n,b:=b,q:=qq) *)
                                    val dvd_nqb = dvd_mult_assoc_l_atS (pF, nStep, bF, qq) hDvdNB;  (* dvd p ((n*qq)*b) *)
                                    (* dvd_diff : dvd p ((n*qq)*b) -> dvd p (((n*qq)*b) + (r*b)) -> dvd p (r*b) *)
                                    val dvd_rb = dvd_diff_atS (pF, mult (mult nStep qq) bF, mult r bF) dvd_nqb dvd_p_sum;  (* dvd p (mult r b) *)

                                    (* descend : IH at r needs lt r n ; gives B r = Imp(lt r p)(Imp prime2 p)(Imp dvd p (r*b))(Disj (dvd p r)(dvd p b)) *)
                                    val Br   = applyIH r hRltN;       (* jT (B r) *)
                                    val s1   = mp_atS2 (lt r pF, mkImp (prime2 pF) (mkImp (dvd pF (mult r bF)) (mkDisj (dvd pF r) (dvd pF bF)))) Br hRltP;
                                    val s2   = mp_atS2 (prime2 pF, mkImp (dvd pF (mult r bF)) (mkDisj (dvd pF r) (dvd pF bF))) s1 hPr;
                                    val disjR= mp_atS2 (dvd pF (mult r bF), mkDisj (dvd pF r) (dvd pF bF)) s2 dvd_rb;  (* Disj (dvd p r)(dvd p b) *)

                                    (* dvd p r impossible : prime_not_dvd_pos_lt (dvd p r)(0<r)(r<p) -> oFalse *)
                                    val cR1 =
                                      let
                                        val hdr = Thm.assume (ctermS2 (jT (dvd pF r)));
                                        val fls = prime_not_dvd_pos_lt_atS (pF, r) hdr pos_r hRltP;  (* oFalse *)
                                        val g   = Thm.implies_elim (oFalse_elimS_at goalC) fls;
                                      in Thm.implies_intr (ctermS2 (jT (dvd pF r))) g end;
                                    val cR2 =
                                      let
                                        val hdb = Thm.assume (ctermS2 (jT (dvd pF bF)));
                                        val g   = disjI2S2_at (dvd pF nStep, dvd pF bF) hdb;
                                      in Thm.implies_intr (ctermS2 (jT (dvd pF bF))) g end;
                                    val g = disjE_elimS2 (dvd pF r, dvd pF bF, goalC) disjR cR1 cR2;
                                  in Thm.implies_intr (ctermS2 (jT (neg (oeq r ZeroC)))) g end;

                                val g = disjE_elimS2 (oeq r ZeroC, neg (oeq r ZeroC), goalC) emr subZero subNZ;
                              in g end;
                            val g = exE_elimS2 (innerDivAbsN nStep pF qq, goalC) hQQex "rdm" innerR;
                          in g end;
                        val g = exE_elimS2 (rmDivBodyN nStep pF, goalC) dmEx "qdm" innerQ;
                      in g end;
                    val g = exE_elimS2 (PabsQ2, goalC) exq2 "q2w" q2body;
                  in Thm.implies_intr (ctermS2 (jT (mkEx PabsQ2))) g end;

                val g = disjE_elimS2 (oeq q ZeroC, mkEx PabsQ2, goalC) dzq caseQZero caseQSuc;
              in g end;
            val g = exE_elimS2 (PabsQ, goalC) exq "qw" qbody;
          in Thm.implies_intr (ctermS2 (jT (mkEx PabsQ))) g end;

        val g = disjE_elimS2 (oeq nStep ZeroC, mkEx PabsQ, goalC) dz caseZero caseSuc;
      in Thm.implies_intr (ctermS2 (jT (neg (dvd pF nStep)))) g end;

    val concl = disjE_elimS2 (dvd pF nStep, neg (dvd pF nStep), goalC) em case_dvd case_ndvd;  (* Disj (dvd p n)(dvd p b) *)

    (* build B n = Imp(lt n p)(Imp prime2 p)(Imp dvd p (n*b))(goal)) by 3 impI under the 3 assumed hyps *)
    val i3 = impI_atS2 (dvd pF (mult nStep bF), mkDisj (dvd pF nStep) (dvd pF bF))
               (Thm.implies_intr (ctermS2 dvdP) concl);
    val i2 = impI_atS2 (prime2 pF, mkImp (dvd pF (mult nStep bF)) (mkDisj (dvd pF nStep) (dvd pF bF)))
               (Thm.implies_intr (ctermS2 prP) i3);
    val i1 = impI_atS2 (lt nStep pF, mkImp (prime2 pF) (mkImp (dvd pF (mult nStep bF)) (mkDisj (dvd pF nStep) (dvd pF bF))))
               (Thm.implies_intr (ctermS2 ltP) i2);  (* jT (B n) *)

    val stepThm = Thm.forall_intr (ctermS2 nStep) (Thm.implies_intr (ctermS2 Gprop) i1);

    (* feed to strong_induct: P := Bpred, k := a *)
    val aK = Free("a", natT);
    val siInst = beta_norm (Drule.infer_instantiate ctxtS2
                   [(("P",0), ctermS2 Bpred), (("k",0), ctermS2 aK)] (varify strong_induct));
    val Ba = Thm.implies_elim siInst stepThm;       (* jT (B a) = jT (Imp(lt a p)(Imp prime2 p)(Imp dvd p (a*b))(goal))) *)
    (* turn into the META rule jT(lt a p)==>jT(prime2 p)==>jT(dvd p (a*b))==>jT goal *)
    val hlt = Thm.assume (ctermS2 (jT (lt aK pF)));
    val hpr = Thm.assume (ctermS2 (jT (prime2 pF)));
    val hdv = Thm.assume (ctermS2 (jT (dvd pF (mult aK bF))));
    val u1  = mp_atS2 (lt aK pF, mkImp (prime2 pF) (mkImp (dvd pF (mult aK bF)) (mkDisj (dvd pF aK) (dvd pF bF)))) Ba hlt;
    val u2  = mp_atS2 (prime2 pF, mkImp (dvd pF (mult aK bF)) (mkDisj (dvd pF aK) (dvd pF bF))) u1 hpr;
    val u3  = mp_atS2 (dvd pF (mult aK bF), mkDisj (dvd pF aK) (dvd pF bF)) u2 hdv;  (* jT goal *)
    val d1  = Thm.implies_intr (ctermS2 (jT (dvd pF (mult aK bF)))) u3;
    val d2  = Thm.implies_intr (ctermS2 (jT (prime2 pF))) d1;
    val d3  = Thm.implies_intr (ctermS2 (jT (lt aK pF))) d2;
  in varify d3 end;

(* ---- validation : bounded_euclid 0-hyp + aconv ---- *)
val pVbe = Var (("p",0), natT);
val aVbe = Var (("a",0), natT);
val bVbe = Var (("b",0), natT);
val bounded_euclid_intended =
  Logic.mk_implies (jT (lt aVbe pVbe),
    Logic.mk_implies (jT (prime2 pVbe),
      Logic.mk_implies (jT (dvd pVbe (mult aVbe bVbe)),
        jT (mkDisj (dvd pVbe aVbe) (dvd pVbe bVbe)))));
val r_be = checkS2 ("bounded_euclid", bounded_euclid, bounded_euclid_intended);

val bounded_euclid_vS = varify bounded_euclid;
fun bounded_euclid_atS (aT, bT, pT) hlt hpr hdvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("a",0), ctermS2 aT), (("b",0), ctermS2 bT), (("p",0), ctermS2 pT)] bounded_euclid_vS)
  in ((inst OF [hlt]) OF [hpr]) OF [hdvd] end;

(* ============================================================================
   euclid_lemma : jT (prime2 p) ==> jT (dvd p (mult a b))
                    ==> jT (Disj (dvd p a) (dvd p b))
   Reduce a mod p (p > 0 from prime), descend to bounded_euclid at the remainder.
   ============================================================================ *)
val euclid_lemma =
  let
    val pF = Free("p", natT); val aF = Free("a", natT); val bF = Free("b", natT);
    val prP   = jT (prime2 pF);              val hPr   = Thm.assume (ctermS2 prP);
    val dvdP  = jT (dvd pF (mult aF bF));     val hDvdAB= Thm.assume (ctermS2 dvdP);
    val goalC = mkDisj (dvd pF aF) (dvd pF bF);

    (* p > 0 : from prime2 p we have lt 1 p = le 2 p ; need lt 0 p.  lt 0 p = le 1 p.
       le 2 p -> le 1 p by le_trans (le 1 2)(le 2 p).  le 1 2 = lt 0 1 = lt_zero_suc 0. *)
    val gt1p   = prime2_gt1_atS pF hPr;        (* lt 1 p = le 2 p *)
    (* le 1 2 directly via le_introS (Suc 0, Suc(Suc 0), Suc 0):
         add (Suc 0)(Suc 0) = Suc(0 + Suc 0) = Suc(Suc 0), so Suc(Suc 0) = (Suc 0)+(Suc 0). *)
    val le_1_2 =
      let
        val aS  = addSucS_at (ZeroC, suc ZeroC);            (* (Suc 0 + Suc 0) = Suc(0 + Suc 0) *)
        val s0  = Suc_cong OF [add0S_at (suc ZeroC)];        (* Suc(0 + Suc 0) = Suc(Suc 0) *)
        val sumv= oeq_trans OF [aS, s0];                     (* (Suc 0 + Suc 0) = Suc(Suc 0) *)
        val eqn = oeq_sym OF [sumv];                         (* Suc(Suc 0) = (Suc 0 + Suc 0) *)
      in le_introS (suc ZeroC, suc (suc ZeroC), suc ZeroC) eqn end;  (* le 1 2 *)
    val pos_p  = le_trans_atS (suc ZeroC, suc (suc ZeroC), pF) le_1_2 gt1p;  (* le 1 p = lt 0 p *)

    (* div_mod_exists : divisor p, dividend a -> a = p*qq + r, r < p *)
    val dmEx = div_mod_atS (aF, pF) pos_p;   (* Ex qq. Ex r. Conj (oeq a (add (mult p qq) r))(lt r p) *)

    fun innerQ qq (hQQex : thm) =
      let
        fun innerR r (hConj : thm) =      (* hConj : Conj (oeq a (add (mult p qq) r))(lt r p) *)
          let
            val hAeq  = conjunct1_atS2 (oeq aF (add (mult pF qq) r), lt r pF) hConj;  (* a = p*qq + r *)
            val hRltP = conjunct2_atS2 (oeq aF (add (mult pF qq) r), lt r pF) hConj;  (* r < p *)

            (* p | mult r b :
               mult a b = mult (add (mult p qq) r) b = add (mult (mult p qq) b)(mult r b)
               p | mult (mult p qq) b  (= p | p*(qq*b) : dvd_introS witness qq*b after assoc)
               dvd_diff(p | (p*qq)*b)(p | ((p*qq)*b + r*b) = a*b) => p | r*b *)
            val mcong = mult_cong_lS (aF, add (mult pF qq) r, bF) hAeq;  (* (a*b) = ((p*qq + r)*b) *)
            val rdist = rdist_at_S2 (mult pF qq, r, bF);                 (* ((p*qq + r)*b) = ((p*qq)*b + r*b) *)
            val ab_split = oeq_trans OF [mcong, rdist];                  (* (a*b) = ((p*qq)*b + r*b) *)
            val dvd_p_ab2 = dvd_cong_rS (pF, mult aF bF, add (mult (mult pF qq) bF) (mult r bF)) ab_split hDvdAB;  (* dvd p ((p*qq)*b + r*b) *)
            (* p | (p*qq)*b :  (p*qq)*b = p*(qq*b) (mult_assoc) ; dvd_introS witness (qq*b) *)
            val assoc_pqqb = mult_assoc_atS (pF, qq, bF);   (* ((p*qq)*b) = (p*(qq*b)) *)
            val dvd_pqqb = dvd_introS (pF, mult (mult pF qq) bF, mult qq bF) assoc_pqqb;  (* dvd p ((p*qq)*b) *)
            val dvd_rb = dvd_diff_atS (pF, mult (mult pF qq) bF, mult r bF) dvd_pqqb dvd_p_ab2;  (* dvd p (mult r b) *)

            (* bounded_euclid at r : need lt r p (= hRltP) ; gives Disj (dvd p r)(dvd p b) *)
            val disjR = bounded_euclid_atS (r, bF, pF) hRltP hPr dvd_rb;  (* Disj (dvd p r)(dvd p b) *)

            (* dvd p r -> dvd p a (since a = p*qq + r, p | p*qq and p | r) ; dvd p b -> disjI2 *)
            val cR1 =
              let
                val hdr = Thm.assume (ctermS2 (jT (dvd pF r)));
                (* dvd p (p*qq) : (p*qq) = p*qq ; dvd_introS witness qq *)
                val dvd_pqq = dvd_introS (pF, mult pF qq, qq) (oeqreflS_at (mult pF qq));  (* dvd p (p*qq) *)
                (* dvd p (add (p*qq) r) via dvd_add *)
                val dvd_sum = dvd_add_atS (pF, mult pF qq, r) dvd_pqq hdr;   (* dvd p (add (p*qq) r) *)
                (* rewrite add (p*qq) r -> a via sym hAeq *)
                val dvd_a   = dvd_cong_rS (pF, add (mult pF qq) r, aF) (oeq_sym OF [hAeq]) dvd_sum;  (* dvd p a *)
                val g = disjI1S2_at (dvd pF aF, dvd pF bF) dvd_a;
              in Thm.implies_intr (ctermS2 (jT (dvd pF r))) g end;
            val cR2 =
              let
                val hdb = Thm.assume (ctermS2 (jT (dvd pF bF)));
                val g = disjI2S2_at (dvd pF aF, dvd pF bF) hdb;
              in Thm.implies_intr (ctermS2 (jT (dvd pF bF))) g end;
            val g = disjE_elimS2 (dvd pF r, dvd pF bF, goalC) disjR cR1 cR2;
          in g end;
        val g = exE_elimS2 (innerDivAbsN pF aF qq, goalC) hQQex "rdm" innerR;
      in g end;
    val concl = exE_elimS2 (rmDivBodyN pF aF, goalC) dmEx "qdm" innerQ;  (* Disj (dvd p a)(dvd p b) *)

    val d1 = Thm.implies_intr (ctermS2 dvdP) concl;
    val d2 = Thm.implies_intr (ctermS2 prP)  d1;
  in varify d2 end;

(* ---- validation : euclid_lemma 0-hyp + aconv the TARGET ---- *)
val pVel = Var (("p",0), natT);
val aVel = Var (("a",0), natT);
val bVel = Var (("b",0), natT);
val euclid_lemma_intended =
  Logic.mk_implies (jT (prime2 pVel),
    Logic.mk_implies (jT (dvd pVel (mult aVel bVel)),
      jT (mkDisj (dvd pVel aVel) (dvd pVel bVel))));
val r_el = checkS2 ("euclid_lemma", euclid_lemma, euclid_lemma_intended);

(* ---- SOUNDNESS PROBE : dropping the prime hypothesis must NOT be provable ----
   (composite p=4, a=b=2 : 4 | 2*2 but 4 does not divide 2.)  The kernel certificate
   must therefore NOT match the prime-free variant. *)
val probe_el_needs_prime =
  let
    val bogus = Logic.mk_implies (jT (dvd pVel (mult aVel bVel)),
                  jT (mkDisj (dvd pVel aVel) (dvd pVel bVel)));  (* drops prime2 p *)
  in not ((Thm.prop_of euclid_lemma) aconv bogus) end;
(* and it must not be the unconditional disjunction *)
val probe_el_nontrivial =
  not ((Thm.prop_of euclid_lemma) aconv (jT (mkDisj (dvd pVel aVel) (dvd pVel bVel))));

val () =
  if probe_el_needs_prime andalso probe_el_nontrivial
  then out "PROBE_OK euclid_lemma is conditional on prime2 p / nontrivial\n"
  else out "PROBE_UNSOUND euclid_lemma collapsed!\n";

val () =
  if r_be andalso r_el andalso probe_el_needs_prime andalso probe_el_nontrivial
  then out "EUCLID_LEMMA_DONE\n"
  else out "EUCLID_LEMMA_FAILED\n";
