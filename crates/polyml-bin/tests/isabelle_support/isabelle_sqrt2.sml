(* ============================================================================
   SQRT 2 IS IRRATIONAL in Isabelle/Pure on the polyml-rs interpreter.
   (test: isabelle_sqrt2.rs)
   ----------------------------------------------------------------------------
     sqrt2_irrational :
       |- ~ (?a. 0 < a /\ (?b. a*a = 2*(b*b)))
   There are NO positive naturals a, b with a^2 = 2*b^2 — i.e. sqrt 2 is
   irrational.  A 0-hypothesis theorem (checkD: hyps = 0 AND prop aconv the
   intended goal), proved by INFINITE DESCENT via strong (course-of-values)
   induction, on the classical Isabelle/Pure number-theory development.  Only
   classical assumption anywhere = excluded middle.

   PROOF (infinite descent):  define Sol x := 0<x /\ ?b. x*x = 2*(b*b).  Show
   !x. ~ Sol x by strong induction.  If Sol x then x*x = 2*(b*b) is even, so x is
   even (sq_even_even, via the odd^2-is-odd parity argument — no Euclid's lemma);
   write x = 2c.  Then (2c)^2 = 2*b^2 gives 2*(2*c^2) = 2*b^2, and cancelling the
   common factor 2 (mult_left_cancel) gives b^2 = 2*c^2, i.e. Sol b.  But b < x
   (since x*x = 2*b*b > b*b for b>0, sq_lt_cancel) and 0 < b — a strictly smaller
   solution, contradicting the strong-induction hypothesis.  Hence no Sol x, so
   no positive a, b solve a^2 = 2*b^2.

   A companion to Euclid's theorem: two of the most famous results in elementary
   number theory, both proved from first principles (modulo excluded middle) on
   the Rust PolyML interpreter.

   Built (on isabelle_classical_primes.sml) by a 2-phase ultracode pipeline
   (wf_d7246a73-e08): parity helpers (mult_left_cancel, mult_zero_cancel, parity,
   odd_not_even, sq_even_even, sq_lt_cancel, mult_le_mono) -> descent (2 seats,
   both proved it).  Soundness probe confirms the kernel REJECTS the false
   positivity-dropped variant (a=b=0 is a solution).
   ============================================================================ *)


(* ============================================================================
   ============================================================================
   ***  SQRT2 HELPERS  ***  (multiplicative cancellation + PARITY)
   ----------------------------------------------------------------------------
   Built on the SINGLE FINAL classical context ctxtC / ctermC (it carries
   oeq/add/mult/Suc/Zero, Ex/oFalse/Disj/Imp/Conj/Forall, the abbreviations
   le/lt/dvd/neg, and every connective helper).  No new constants are added;
   everything routes through ctxtC / ctermC.

   two  ==  Suc (Suc Zero)

   ADDED (each a 0-hyp / 0-extra-hyp named val, validated by checkSq via
   aconv of its intended schematic implication form):
     mult_le_mono     : jT (le j k) ==> jT (le (mult c j) (mult c k))
     mult_zero_cancel : jT (lt Zero c) ==> jT (oeq (mult c e) Zero) ==> jT (oeq e Zero)
     mult_left_cancel : jT (lt Zero c) ==> jT (oeq (mult c a) (mult c b)) ==> jT (oeq a b)
     parity           : jT (Disj (Ex (%c. oeq x (mult two c)))
                                 (Ex (%c. oeq x (add (mult two c) (Suc Zero)))))
     odd_not_even     : jT (oeq (add (mult two a) (Suc Zero)) (mult two b)) ==> jT oFalse
     sq_even_even     : jT (oeq (mult x x) (mult two k)) ==> jT (Ex (%c. oeq x (mult two c)))
     sq_lt_cancel     : jT (lt (mult y y) (mult x x)) ==> jT (lt y x)
   ============================================================================ *)

val () = out "SQRT2_HELPERS_BEGIN\n";

(* two abbreviation *)
val two = suc (suc ZeroC);

(* ---- multiplication lemmas re-varified for ctxtC + ground instantiators ---- *)
val left_distrib_vC  = varify left_distrib;
val right_distrib_vC = varify right_distrib;
val mult_assoc_vC    = varify mult_assoc;
val mult_1_left_vC   = varify mult_1_left;
val mult_1_right_vC  = varify mult_1_right;
val mult_comm_vCsq   = varify mult_comm;
val add_assoc_vC     = varify add_assoc;
val add_comm_vCsq    = varify add_comm;

(* left_distrib : oeq (mult ?x (add ?m ?n)) (add (mult ?x ?m) (mult ?x ?n)) *)
fun left_distrib_atC (xT, mT, nT) = beta_norm (Drule.infer_instantiate ctxtC
      [(("x",0), ctermC xT), (("m",0), ctermC mT), (("n",0), ctermC nT)] left_distrib_vC);
(* right_distrib : oeq (mult (add ?m ?n) ?k) (add (mult ?m ?k) (mult ?n ?k)) *)
fun right_distrib_atC (mT, nT, kT) = beta_norm (Drule.infer_instantiate ctxtC
      [(("m",0), ctermC mT), (("n",0), ctermC nT), (("k",0), ctermC kT)] right_distrib_vC);
(* mult_assoc : oeq (mult (mult ?m ?n) ?k) (mult ?m (mult ?n ?k)) *)
fun mult_assoc_atC (mT, nT, kT) = beta_norm (Drule.infer_instantiate ctxtC
      [(("m",0), ctermC mT), (("n",0), ctermC nT), (("k",0), ctermC kT)] mult_assoc_vC);
fun mult1l_atCsq t = beta_norm (Drule.infer_instantiate ctxtC [(("n",0), ctermC t)] mult_1_left_vC);
fun mult1r_atCsq t = beta_norm (Drule.infer_instantiate ctxtC [(("n",0), ctermC t)] mult_1_right_vC);
fun multcomm_atCsq (mt,nt) = beta_norm (Drule.infer_instantiate ctxtC
      [(("m",0), ctermC mt),(("n",0), ctermC nt)] mult_comm_vCsq);
fun add_assoc_atC (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtC
      [(("m",0), ctermC mt),(("n",0), ctermC nt),(("k",0), ctermC kt)] add_assoc_vC);

(* mult-congruence on LEFT / RIGHT operand, on ctxtC *)
fun mult_cong_lC (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("a",0), ctermC pT), (("b",0), ctermC qT)] oeq_subst_vC);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtC [(("a",0), ctermC (mult pT kT))] oeq_refl_vC);
  in inst OF [hpq, refl_pk] end;
fun mult_cong_rC (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("a",0), ctermC pT), (("b",0), ctermC qT)] oeq_subst_vC);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtC [(("a",0), ctermC (mult hT pT))] oeq_refl_vC);
  in inst OF [hpq, refl_hp] end;

(* le-argument rewriting via oeq_subst with CAPTURE-AVOIDING predicate (Term.lambda
   over a Free, because the predicate body contains `le` of the substituted slot). *)
(* le_subst_l : oeq p q  ->  le p r  ->  le q r *)
fun le_subst_l (pT, qT, rT) hoeq hle =
  let
    val zF   = Free("z_lsl", natT);
    val Pabs = Term.lambda zF (le zF rT);
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("a",0), ctermC pT), (("b",0), ctermC qT)] oeq_subst_vC);
  in (inst OF [hoeq]) OF [hle] end;
(* le_subst_r : oeq p q  ->  le r p  ->  le r q *)
fun le_subst_r (rT, pT, qT) hoeq hle =
  let
    val zF   = Free("z_lsr", natT);
    val Pabs = Term.lambda zF (le rT zF);
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("a",0), ctermC pT), (("b",0), ctermC qT)] oeq_subst_vC);
  in (inst OF [hoeq]) OF [hle] end;
(* lt-argument rewriting (lt m n == le (Suc m) n) *)
fun lt_subst_r (rT, pT, qT) hoeq hlt =
  let
    val zF   = Free("z_ltr", natT);
    val Pabs = Term.lambda zF (lt rT zF);
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("a",0), ctermC pT), (("b",0), ctermC qT)] oeq_subst_vC);
  in (inst OF [hoeq]) OF [hlt] end;
fun lt_subst_l (pT, qT, rT) hoeq hlt =
  let
    val zF   = Free("z_ltl", natT);
    val Pabs = Term.lambda zF (lt zF rT);
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("a",0), ctermC pT), (("b",0), ctermC qT)] oeq_subst_vC);
  in (inst OF [hoeq]) OF [hlt] end;

(* lt_irrefl / lt_trans lifted to ctxtC *)
val lt_irrefl_vC = varify lt_irrefl;
fun lt_irrefl_atC t h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtC [(("n",0), ctermC t)] lt_irrefl_vC)
  in Thm.implies_elim inst h end;
val le_neq_lt_vCsq = varify le_neq_lt;
fun le_neq_lt_atCsq (dt, nt) hle hneq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtC
        [(("d",0), ctermC dt), (("n",0), ctermC nt)] le_neq_lt_vCsq)
  in Thm.implies_elim (Thm.implies_elim inst hle) hneq end;

(* add_two_at y : oeq (add two y) (Suc (Suc y))
     add (Suc(Suc 0)) y = Suc((Suc 0)+y) = Suc(Suc(0+y)) = Suc(Suc y). *)
fun add_two_at y =
  let
    val a1 = addSucC_at (suc ZeroC, y);          (* (2+y) = Suc((1)+y) *)
    val a2 = addSucC_at (ZeroC, y);              (* (1+y) = Suc(0+y) *)
    val a3 = add0C_at y;                         (* (0+y) = y *)
    val sa3 = Suc_cong OF [a3];                  (* Suc(0+y) = Suc y *)
    val a2c = oeq_trans OF [a2, sa3];            (* (1+y) = Suc y *)
    val sa2c = Suc_cong OF [a2c];                (* Suc((1)+y) = Suc(Suc y) *)
  in oeq_trans OF [a1, sa2c] end;               (* (2+y) = Suc(Suc y) *)

(* mult_two_eqC y : oeq (mult two y) (add y y).  Uses mult_Suc (LEFT recursion):
     mult (Suc m) n = add n (mult m n).  We re-state mult_Suc on ctxtC. *)
val mult_Suc_vC = varify mult_Suc;
fun multSucC_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtC
      [(("m",0), ctermC mt),(("n",0), ctermC nt)] mult_Suc_vC);
fun mult_two_eqC y =
  let
    val s1 = multSucC_at (suc ZeroC, y);          (* mult (Suc(Suc 0)) y = add y (mult (Suc 0) y) *)
    val s2 = multSucC_at (ZeroC, y);              (* mult (Suc 0) y = add y (mult 0 y) *)
    val m0 = mult0l_at y;                          (* mult 0 y = 0 *)
    val s2b = add_cong_rC (y, mult ZeroC y, ZeroC) m0;   (* add y (mult 0 y) = add y 0 *)
    val s2c = oeq_trans OF [s2, s2b];             (* mult (Suc 0) y = add y 0 *)
    val a0 = add0rC_at y;                          (* add y 0 = y *)
    val s2d = oeq_trans OF [s2c, a0];             (* mult (Suc 0) y = y *)
    val s1b = add_cong_rC (y, mult (suc ZeroC) y, y) s2d;  (* add y (mult(Suc 0) y) = add y y *)
  in oeq_trans OF [s1, s1b] end;                  (* mult two y = add y y *)

(* ============================================================================
   mult_le_mono : jT (le j k) ==> jT (le (mult c j) (mult c k))
     le j k = Ex(e. oeq k (add j e)).  exE witness e, he : oeq k (add j e).
       mult c k = mult c (add j e)            (mult_cong_r)
                = add (mult c j) (mult c e)    (left_distrib)
       witness (mult c e) for le (mult c j)(mult c k).
   ============================================================================ *)
val mult_le_mono =
  let
    val cF = Free("c", natT); val jF = Free("j", natT); val kF = Free("k", natT);
    val leHypP = jT (le jF kF);
    val leHyp  = Thm.assume (ctermC leHypP);
    val Pabs   = Abs("e", natT, oeq kF (add jF (Bound 0)));      (* le j k body *)
    val goalC  = le (mult cF jF) (mult cF kF);
    fun body e (he : thm) =                          (* he : oeq k (add j e) *)
      let
        val cong = mult_cong_rC (cF, kF, add jF e) he;           (* (c*k) = (c*(j+e)) *)
        val ld   = left_distrib_atC (cF, jF, e);                 (* (c*(j+e)) = (c*j + c*e) *)
        val eqn  = oeq_trans OF [cong, ld];                      (* (c*k) = (c*j + c*e) *)
      in le_introC (mult cF jF, mult cF kF, mult cF e) eqn end;
    val afterExE = exE_elimC (Pabs, goalC) leHyp "ew" body;
    val disch = Thm.implies_intr (ctermC leHypP) afterExE;
  in varify disch end;

(* ============================================================================
   inline : c_ne0_of_lt0  : jT (lt Zero c) ==> jT (neg (oeq c Zero))
     lt Zero c = le (Suc Zero) c = Ex(p. oeq c (add (Suc Zero) p)).
     exE witness p: c = (1 + p) = Suc(0+p).  assume oeq c 0; sym/trans => Suc(..)=0; oFalse.
   ============================================================================ *)
fun c_ne0_of_lt0 cF h_lt0 =
  let
    val Pabs = Abs("p", natT, oeq cF (add (suc ZeroC) (Bound 0)));
    val ez   = Thm.assume (ctermC (jT (oeq cF ZeroC)));
    fun body p (hp : thm) =                               (* hp : oeq c (add 1 p) *)
      let
        val aS    = addSucC_at (ZeroC, p);                (* (1 + p) = Suc (0 + p) *)
        val c_Sp  = oeq_trans OF [hp, aS];                (* c = Suc (0 + p) *)
        val z_Sp  = oeq_trans OF [oeq_sym OF [ez], c_Sp]; (* 0 = Suc (0 + p) *)
        val Sp_z  = oeq_sym OF [z_Sp];                    (* Suc (0 + p) = 0 *)
      in (Suc_neq_Zero_atC (add ZeroC p)) OF [Sp_z] end;  (* oFalse *)
    val falseThm = exE_elimC (Pabs, oFalseC) h_lt0 "wp" body;
    val imp = Thm.implies_intr (ctermC (jT (oeq cF ZeroC))) falseThm;
  in impI_atT (oeq cF ZeroC, oFalseC) imp end;            (* jT (neg (oeq c 0)) *)

(* ============================================================================
   mult_zero_cancel : jT (lt Zero c) ==> jT (oeq (mult c e) Zero) ==> jT (oeq e Zero)
     dzosC_at e:
       e = 0     : goal oeq e 0 holds directly (we have oeq e 0).
       e = Suc e2: mult c (Suc e2) = add c (mult c e2)   (mult_Suc_right)
                   so oeq (mult c e) (add c (mult c e2)); with hyp =0 =>
                   oeq (add c (mult c e2)) 0 => add_eq_zero_left => oeq c 0,
                   contradicting (neg (oeq c 0)) from lt Zero c => oFalse =>
                   oFalse_elim => oeq e 0.
   ============================================================================ *)
val mult_zero_cancel =
  let
    val cF = Free("c", natT); val eF = Free("e", natT);
    val ltHypP = jT (lt ZeroC cF);
    val mzHypP = jT (oeq (mult cF eF) ZeroC);
    val ltHyp  = Thm.assume (ctermC ltHypP);
    val mzHyp  = Thm.assume (ctermC mzHypP);
    val goalC  = oeq eF ZeroC;
    val cNe0   = c_ne0_of_lt0 cF ltHyp;                  (* jT (neg (oeq c 0)) *)
    val dz     = dzosC_at eF;                            (* Disj (oeq e 0) (Ex(%q. oeq e (Suc q))) *)
    val caseZero =
      let val hz = Thm.assume (ctermC (jT (oeq eF ZeroC)))
      in Thm.implies_intr (ctermC (jT (oeq eF ZeroC))) hz end;
    val PabsQ = Abs("q", natT, oeq eF (suc (Bound 0)));
    val caseSuc =
      let
        val exq = Thm.assume (ctermC (jT (mkEx PabsQ)));
        fun sucBody e2 (he2 : thm) =                     (* he2 : oeq e (Suc e2) *)
          let
            val cong  = mult_cong_rC (cF, eF, suc e2) he2;     (* (c*e) = (c*(Suc e2)) *)
            val msr   = multSrC_at (cF, e2);                   (* (c*(Suc e2)) = (c + c*e2) *)
            val ce_form = oeq_trans OF [cong, msr];            (* (c*e) = (c + c*e2) *)
            val form0 = oeq_trans OF [oeq_sym OF [ce_form], mzHyp];  (* (c + c*e2) = 0 *)
            val c0    = add_eq_zero_left_vC OF [form0];        (* oeq c 0 *)
            val fls   = mp_atT (oeq cF ZeroC, oFalseC) cNe0 c0;     (* oFalse *)
            val g     = (oFalse_elimC_at goalC) OF [fls];     (* oeq e 0 *)
          in g end;
        val g = exE_elimC (PabsQ, goalC) exq "q0" sucBody;
      in Thm.implies_intr (ctermC (jT (mkEx PabsQ))) g end;
    val concl = disjE_elimC (oeq eF ZeroC, mkEx PabsQ, goalC) dz caseZero caseSuc;
    val d1 = Thm.implies_intr (ctermC mzHypP) concl;
    val d2 = Thm.implies_intr (ctermC ltHypP) d1;
  in varify d2 end;

(* ============================================================================
   mult_left_cancel : jT (lt Zero c) ==> jT (oeq (mult c a) (mult c b)) ==> jT (oeq a b)
     le_total a b:
       le a b : b = add a e ; mult c b = add (mult c a)(mult c e) (cong_r+left_distrib);
                with (c*a)=(c*b): (c*a) = add (c*a)(c*e); = add (c*a) 0 (add0r sym);
                add_left_cancel => oeq 0 (c*e) => sym => (c*e)=0 => mult_zero_cancel
                => e=0 => b = add a 0 = a => sym => a = b.
       le b a : symmetric (swap a,b), then sym at the end.
   ============================================================================ *)
val mult_zero_cancel_vC = varify mult_zero_cancel;
fun mult_zero_cancel_atC (ct, et) hlt hmz =
  let val inst = beta_norm (Drule.infer_instantiate ctxtC
        [(("c",0), ctermC ct), (("e",0), ctermC et)] mult_zero_cancel_vC)
  in Thm.implies_elim (Thm.implies_elim inst hlt) hmz end;

val mult_left_cancel =
  let
    val cF = Free("c", natT); val aF = Free("a", natT); val bF = Free("b", natT);
    val ltHypP = jT (lt ZeroC cF);
    val eqHypP = jT (oeq (mult cF aF) (mult cF bF));
    val ltHyp  = Thm.assume (ctermC ltHypP);
    val eqHyp  = Thm.assume (ctermC eqHypP);             (* oeq (c*a) (c*b) *)
    val goalC  = oeq aF bF;
    val lt_tot = le_total_at (aF, bF);                   (* Disj (le a b)(le b a) *)

    (* given p,q with hp: oeq q (add p w) and a proof that (c*p) = (c*q), derive oeq p q *)
    fun cancel_branch (pT, qT, eqpq) w (hw : thm) =      (* hw : oeq q (add p w) *)
      let
        (* (c*q) = (c*(p+w)) = (c*p + c*w) *)
        val cong = mult_cong_rC (cF, qT, add pT w) hw;       (* (c*q) = (c*(p+w)) *)
        val ld   = left_distrib_atC (cF, pT, w);             (* (c*(p+w)) = (c*p + c*w) *)
        val cq   = oeq_trans OF [cong, ld];                  (* (c*q) = (c*p + c*w) *)
        (* (c*p) = (c*q) = (c*p + c*w) *)
        val cp_sum = oeq_trans OF [eqpq, cq];                (* (c*p) = (c*p + c*w) *)
        (* (c*p + 0) = (c*p) = (c*p + c*w) *)
        val cp0  = add0rC_at (mult cF pT);                   (* (c*p + 0) = (c*p) *)
        val cp0_sum = oeq_trans OF [cp0, cp_sum];            (* (c*p + 0) = (c*p + c*w) *)
        val canc = add_left_cancel_vC OF [cp0_sum];          (* oeq 0 (c*w) *)
        val cw0  = oeq_sym OF [canc];                        (* (c*w) = 0 *)
        val w0   = mult_zero_cancel_atC (cF, w) ltHyp cw0;   (* oeq w 0 *)
        (* q = add p w = add p 0 = p ;  then oeq p q via sym *)
        val congw = add_cong_rC (pT, w, ZeroC) w0;           (* (p + w) = (p + 0) *)
        val q_p0  = oeq_trans OF [hw, congw];                (* q = (p + 0) *)
        val q_p   = oeq_trans OF [q_p0, add0rC_at pT];       (* q = p *)
      in oeq_sym OF [q_p] end;                               (* p = q *)

    (* CASE le a b : witness e, he: oeq b (add a e); cancel_branch (a,b, eqHyp) => a=b *)
    val caseAB =
      let
        val hle = Thm.assume (ctermC (jT (le aF bF)));
        val Pab = Abs("e", natT, oeq bF (add aF (Bound 0)));
        fun bodyAB w hw = cancel_branch (aF, bF, eqHyp) w hw;  (* oeq a b *)
        val g = exE_elimC (Pab, goalC) hle "wab" bodyAB;
      in Thm.implies_intr (ctermC (jT (le aF bF))) g end;
    (* CASE le b a : witness e, he: oeq a (add b e); cancel_branch (b,a, sym eqHyp) => b=a;
       then sym => a=b. *)
    val caseBA =
      let
        val hle = Thm.assume (ctermC (jT (le bF aF)));
        val Pba = Abs("e", natT, oeq aF (add bF (Bound 0)));
        val eqHypSym = oeq_sym OF [eqHyp];                  (* (c*b) = (c*a) *)
        fun bodyBA w hw =                                    (* oeq b a *)
          let val bEqa = cancel_branch (bF, aF, eqHypSym) w hw  (* oeq b a *)
          in oeq_sym OF [bEqa] end;                          (* oeq a b *)
        val g = exE_elimC (Pba, goalC) hle "wba" bodyBA;
      in Thm.implies_intr (ctermC (jT (le bF aF))) g end;

    val concl = disjE_elimC (le aF bF, le bF aF, goalC) lt_tot caseAB caseBA;
    val d1 = Thm.implies_intr (ctermC eqHypP) concl;
    val d2 = Thm.implies_intr (ctermC ltHypP) d1;
  in varify d2 end;

(* ============================================================================
   parity : jT (Disj (Ex (%c. oeq x (mult two c)))
                     (Ex (%c. oeq x (add (mult two c) (Suc Zero)))))
     BY INDUCTION on x (capture-avoiding predicate via Term.lambda over a Free).
   ============================================================================ *)
fun evenBody t = mkEx (Abs("c", natT, oeq t (mult two (Bound 0))));
fun oddBody  t = mkEx (Abs("c", natT, oeq t (add (mult two (Bound 0)) (suc ZeroC))));

val parity =
  let
    val zF0  = Free("zz_par", natT);
    val Qpred = Term.lambda zF0 (mkDisj (evenBody zF0) (oddBody zF0));
    val xF   = Free("x", natT);
    val ind  = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Qpred), (("k",0), ctermC xF)] nat_induct_vC);

    (* BASE : x = 0 even, witness 0.  oeq 0 (mult two 0) :  mult two 0 = 0, sym. *)
    val base =
      let
        val m0  = mult0rC_at two;                          (* (two * 0) = 0 *)
        val hyp = oeq_sym OF [m0];                         (* 0 = (two * 0) *)
        val Pe  = Abs("c", natT, oeq ZeroC (mult two (Bound 0)));
        val ex  = exI_atC Pe ZeroC hyp;                    (* Ex(%c. oeq 0 (two*c)) *)
      in disjI1C_at (evenBody ZeroC, oddBody ZeroC) ex end;

    (* STEP : IH = Disj (even x)(odd x) ; goal Disj (even (Suc x))(odd (Suc x)) *)
    val xS   = Free("x_s", natT);
    val ihprop = jT (mkDisj (evenBody xS) (oddBody xS));
    val IH   = Thm.assume (ctermC ihprop);
    val goalStep = mkDisj (evenBody (suc xS)) (oddBody (suc xS));

    (* CASE even x : Ex(c. oeq x (two*c)).  Suc x = two*c + 1 => odd (Suc x). *)
    val PevenX = Abs("c", natT, oeq xS (mult two (Bound 0)));
    fun caseEvenBody c (hc : thm) =                        (* hc : oeq x (two*c) *)
      let
        val sx_S  = Suc_cong OF [hc];                      (* Suc x = Suc(two*c) *)
        val asr   = addSrC_at (mult two c, ZeroC);         (* (two*c + Suc 0) = Suc(two*c + 0) *)
        val a0    = add0rC_at (mult two c);                (* (two*c + 0) = (two*c) *)
        val sa0   = Suc_cong OF [a0];                      (* Suc(two*c + 0) = Suc(two*c) *)
        val add1_S= oeq_trans OF [asr, sa0];               (* (two*c + Suc 0) = Suc(two*c) *)
        val add1_Ss = oeq_sym OF [add1_S];                 (* Suc(two*c) = (two*c + Suc 0) *)
        val witEq = oeq_trans OF [sx_S, add1_Ss];          (* Suc x = (two*c + Suc 0) *)
        val Po    = Abs("c", natT, oeq (suc xS) (add (mult two (Bound 0)) (suc ZeroC)));
        val ex    = exI_atC Po c witEq;                    (* odd (Suc x) *)
      in disjI2C_at (evenBody (suc xS), oddBody (suc xS)) ex end;
    val caseEven =
      let
        val hE = Thm.assume (ctermC (jT (evenBody xS)));
        val g  = exE_elimC (PevenX, goalStep) hE "ce" caseEvenBody;
      in Thm.implies_intr (ctermC (jT (evenBody xS))) g end;

    (* CASE odd x : Ex(c. oeq x (two*c + 1)).  Suc x = two*(Suc c) => even (Suc x). *)
    val PoddX = Abs("c", natT, oeq xS (add (mult two (Bound 0)) (suc ZeroC)));
    fun caseOddBody c (hc : thm) =                         (* hc : oeq x (two*c + 1) *)
      let
        (* x = two*c + 1 = Suc(two*c)  (add _ (Suc 0) = Suc(_ + 0) = Suc _) *)
        val asr   = addSrC_at (mult two c, ZeroC);         (* (two*c + Suc 0) = Suc(two*c + 0) *)
        val a0    = add0rC_at (mult two c);                (* (two*c + 0) = (two*c) *)
        val sa0   = Suc_cong OF [a0];                      (* Suc(two*c + 0) = Suc(two*c) *)
        val add1_S= oeq_trans OF [asr, sa0];               (* (two*c + Suc 0) = Suc(two*c) *)
        val x_S   = oeq_trans OF [hc, add1_S];             (* x = Suc(two*c) *)
        val sx_SS = Suc_cong OF [x_S];                     (* Suc x = Suc(Suc(two*c)) *)
        (* two*(Suc c) = add two (two*c) = Suc(Suc(two*c)) *)
        val msr   = multSrC_at (two, c);                   (* two*(Suc c) = add two (two*c) *)
        val a2    = add_two_at (mult two c);               (* add two (two*c) = Suc(Suc(two*c)) *)
        val mSc_SS= oeq_trans OF [msr, a2];                (* two*(Suc c) = Suc(Suc(two*c)) *)
        val mSc_SSs = oeq_sym OF [mSc_SS];                 (* Suc(Suc(two*c)) = two*(Suc c) *)
        val witEq = oeq_trans OF [sx_SS, mSc_SSs];         (* Suc x = two*(Suc c) *)
        val Pe    = Abs("c", natT, oeq (suc xS) (mult two (Bound 0)));
        val ex    = exI_atC Pe (suc c) witEq;              (* even (Suc x) *)
      in disjI1C_at (evenBody (suc xS), oddBody (suc xS)) ex end;
    val caseOdd =
      let
        val hO = Thm.assume (ctermC (jT (oddBody xS)));
        val g  = exE_elimC (PoddX, goalStep) hO "co" caseOddBody;
      in Thm.implies_intr (ctermC (jT (oddBody xS))) g end;

    val stepconcl = disjE_elimC (evenBody xS, oddBody xS, goalStep) IH caseEven caseOdd;
    val step1 = Thm.forall_intr (ctermC xS) (Thm.implies_intr (ctermC ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

(* ============================================================================
   parity_one_contra : from jT (oeq (Suc Zero) (mult two e)) derive jT oFalse
     dzosC_at e:
       e = 0     : (two*e) = (two*0) = 0 ; oeq (Suc 0) 0 => Suc_neq_Zero => oFalse.
       e = Suc e2: (two*e) = two*(Suc e2) = add two (two*e2) = Suc(Suc(two*e2)) ;
                   oeq (Suc 0)(Suc(Suc(two*e2))) ; Suc_inj => oeq 0 (Suc(two*e2)) ;
                   sym => Suc_neq_Zero => oFalse.
   ============================================================================ *)
fun parity_one_contra eF h1 =                           (* h1 : oeq (Suc 0) (two*e) *)
  let
    val dz = dzosC_at eF;
    val caseZero =
      let
        val hz   = Thm.assume (ctermC (jT (oeq eF ZeroC)));    (* oeq e 0 *)
        val cong = mult_cong_rC (two, eF, ZeroC) hz;           (* (two*e) = (two*0) *)
        val m0   = mult0rC_at two;                             (* (two*0) = 0 *)
        val te_0 = oeq_trans OF [cong, m0];                    (* (two*e) = 0 *)
        val one_0= oeq_trans OF [h1, te_0];                    (* (Suc 0) = 0 *)
        val fls  = (Suc_neq_Zero_atC ZeroC) OF [one_0];        (* oFalse *)
      in Thm.implies_intr (ctermC (jT (oeq eF ZeroC))) fls end;
    val PabsQ = Abs("q", natT, oeq eF (suc (Bound 0)));
    val caseSuc =
      let
        val exq = Thm.assume (ctermC (jT (mkEx PabsQ)));
        fun sucBody e2 (he2 : thm) =                           (* he2 : oeq e (Suc e2) *)
          let
            val cong  = mult_cong_rC (two, eF, suc e2) he2;    (* (two*e) = two*(Suc e2) *)
            val msr   = multSrC_at (two, e2);                  (* two*(Suc e2) = add two (two*e2) *)
            val a2    = add_two_at (mult two e2);              (* add two (two*e2) = Suc(Suc(two*e2)) *)
            val te_SS = oeq_trans OF [oeq_trans OF [cong, msr], a2];  (* (two*e) = Suc(Suc(two*e2)) *)
            val one_SS= oeq_trans OF [h1, te_SS];              (* (Suc 0) = Suc(Suc(two*e2)) *)
            val inj   = (Suc_inj_atC (ZeroC, suc (mult two e2))) OF [one_SS]; (* oeq 0 (Suc(two*e2)) *)
            val sym0  = oeq_sym OF [inj];                      (* oeq (Suc(two*e2)) 0 *)
            val fls   = (Suc_neq_Zero_atC (mult two e2)) OF [sym0];  (* oFalse *)
          in fls end;
        val g = exE_elimC (PabsQ, oFalseC) exq "q0" sucBody;
      in Thm.implies_intr (ctermC (jT (mkEx PabsQ))) g end;
  in disjE_elimC (oeq eF ZeroC, mkEx PabsQ, oFalseC) dz caseZero caseSuc end;

(* ============================================================================
   odd_not_even : jT (oeq (add (mult two a) (Suc Zero)) (mult two b)) ==> jT oFalse
     le_total a b:
       le a b (b = add a e):
         (two*b) = (two*(a+e)) = (two*a + two*e)  (cong_r + left_distrib)
         hyp: (two*a + 1) = (two*b) = (two*a + two*e)
         add_left_cancel => oeq (Suc 0) (two*e) => parity_one_contra => oFalse.
       le b a (a = add b e):
         (two*a) = (two*b + two*e).
         hyp: (two*a + 1) = (two*b).
         (two*b + two*e) + 1 = (two*a) + 1 = (two*b) ; assoc:
           (two*b) + (two*e + 1) = (two*b) = (two*b) + 0  (add0r sym)
         add_left_cancel => oeq (two*e + 1) 0 => (two*e+1) = Suc(two*e) => Suc_neq_Zero
         => oFalse.
   ============================================================================ *)
val odd_not_even =
  let
    val aF = Free("a", natT); val bF = Free("b", natT);
    val hypP = jT (oeq (add (mult two aF) (suc ZeroC)) (mult two bF));
    val hyp  = Thm.assume (ctermC hypP);                 (* (two*a + 1) = (two*b) *)
    val goalC = oFalseC;
    val lt_tot = le_total_at (aF, bF);                   (* Disj (le a b)(le b a) *)

    val caseAB =
      let
        val hle = Thm.assume (ctermC (jT (le aF bF)));
        val Pab = Abs("e", natT, oeq bF (add aF (Bound 0)));
        fun bodyAB e (he : thm) =                         (* he : oeq b (add a e) *)
          let
            val cong = mult_cong_rC (two, bF, add aF e) he;    (* (two*b) = (two*(a+e)) *)
            val ld   = left_distrib_atC (two, aF, e);          (* (two*(a+e)) = (two*a + two*e) *)
            val tb   = oeq_trans OF [cong, ld];                (* (two*b) = (two*a + two*e) *)
            (* hyp: (two*a + 1) = (two*b) ; chain => (two*a + 1) = (two*a + two*e) *)
            val lhs_form = oeq_trans OF [hyp, tb];             (* (two*a + 1) = (two*a + two*e) *)
            val canc = add_left_cancel_vC OF [lhs_form];       (* oeq (Suc 0) (two*e) *)
            val fls  = parity_one_contra e canc;               (* oFalse *)
          in fls end;
        val g = exE_elimC (Pab, goalC) hle "wab" bodyAB;
      in Thm.implies_intr (ctermC (jT (le aF bF))) g end;

    val caseBA =
      let
        val hle = Thm.assume (ctermC (jT (le bF aF)));
        val Pba = Abs("e", natT, oeq aF (add bF (Bound 0)));
        fun bodyBA e (he : thm) =                         (* he : oeq a (add b e) *)
          let
            val cong = mult_cong_rC (two, aF, add bF e) he;    (* (two*a) = (two*(b+e)) *)
            val ld   = left_distrib_atC (two, bF, e);          (* (two*(b+e)) = (two*b + two*e) *)
            val ta   = oeq_trans OF [cong, ld];                (* (two*a) = (two*b + two*e) *)
            (* hyp sym: (two*b) = (two*a + 1).  also (two*a) = (two*b + two*e). *)
            (* want: (two*b) = (two*b) + 0 = (two*b) + (two*e + 1) and cancel. *)
            (* build (two*b) = add (two*b)(add (two*e)(Suc 0)) :
                 (two*b) = (two*a + 1)            [hyp sym]
                         = ((two*b + two*e) + 1)  [cong_l on ta]
                         = (two*b) + (two*e + 1)  [add_assoc] *)
            val hypS = oeq_sym OF [hyp];                       (* (two*b) = (two*a + 1) *)
            val congL = add_cong_lC (mult two aF, add (mult two bF) (mult two e), suc ZeroC) ta;
                                                               (* (two*a + 1) = ((two*b + two*e) + 1) *)
            val tb_1 = oeq_trans OF [hypS, congL];             (* (two*b) = ((two*b + two*e) + 1) *)
            val assoc = add_assoc_atC (mult two bF, mult two e, suc ZeroC);
                                                               (* ((two*b + two*e) + 1) = (two*b + (two*e + 1)) *)
            val tb_sum = oeq_trans OF [tb_1, assoc];           (* (two*b) = (two*b + (two*e + 1)) *)
            val tb0   = add0rC_at (mult two bF);               (* (two*b + 0) = (two*b) *)
            val tb0_sum = oeq_trans OF [tb0, tb_sum];          (* (two*b + 0) = (two*b + (two*e + 1)) *)
            val canc  = add_left_cancel_vC OF [tb0_sum];       (* oeq 0 (two*e + 1) *)
            (* (two*e + 1) = Suc(two*e) ; oeq 0 (two*e+1) => oeq 0 (Suc(two*e)) => sym => Suc_neq_Zero *)
            val asr   = addSrC_at (mult two e, ZeroC);         (* (two*e + Suc 0) = Suc(two*e + 0) *)
            val a0    = add0rC_at (mult two e);                (* (two*e + 0) = (two*e) *)
            val sa0   = Suc_cong OF [a0];                      (* Suc(two*e + 0) = Suc(two*e) *)
            val sum_S = oeq_trans OF [asr, sa0];               (* (two*e + Suc 0) = Suc(two*e) *)
            val z_S   = oeq_trans OF [canc, sum_S];            (* oeq 0 (Suc(two*e)) *)
            val S_z   = oeq_sym OF [z_S];                      (* oeq (Suc(two*e)) 0 *)
            val fls   = (Suc_neq_Zero_atC (mult two e)) OF [S_z];  (* oFalse *)
          in fls end;
        val g = exE_elimC (Pba, goalC) hle "wba" bodyBA;
      in Thm.implies_intr (ctermC (jT (le bF aF))) g end;

    val concl = disjE_elimC (le aF bF, le bF aF, goalC) lt_tot caseAB caseBA;
    val disch = Thm.implies_intr (ctermC hypP) concl;
  in varify disch end;

(* ============================================================================
   sq_even_even : jT (oeq (mult x x) (mult two k)) ==> jT (Ex (%c. oeq x (mult two c)))
     parity x:  even -> the goal directly.
                odd (x = two*c + 1) -> show (mult x x) = (two*A + 1) with
                A = add (mult c (mult two c)) (mult two c), i.e. x*x is odd;
                with x*x = two*k, odd_not_even (A, k) => oFalse => oFalse_elim => goal.
   ============================================================================ *)
val odd_not_even_vC = varify odd_not_even;
fun odd_not_even_atC (at, bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtC
        [(("a",0), ctermC at), (("b",0), ctermC bt)] odd_not_even_vC)
  in Thm.implies_elim inst h end;

val sq_even_even =
  let
    val xF = Free("x", natT); val kF = Free("k", natT);
    val sqHypP = jT (oeq (mult xF xF) (mult two kF));
    val sqHyp  = Thm.assume (ctermC sqHypP);            (* (x*x) = (two*k) *)
    val goalEx = evenBody xF;                            (* Ex(%c. oeq x (two*c)) *)
    val par    = beta_norm (Drule.infer_instantiate ctxtC
          [(("k",0), ctermC xF)]                         (* parity is stated with induction var k? NO *)
          (varify parity));                              (* parity has no schematic var; just use it *)

    (* parity is a 0-hyp theorem about a SPECIFIC schematic x.  Instantiate at xF. *)
    (* Its prop : Disj (Ex(%c. oeq ?x (two*c))) (Ex(%c. oeq ?x (two*c + 1))).  The
       schematic var is the induction var named "x" -> Var(("x",0),natT). *)
    val parV   = varify parity;
    val parAt  = beta_norm (Drule.infer_instantiate ctxtC [(("x",0), ctermC xF)] parV);

    val evenX = evenBody xF;
    val oddX  = oddBody xF;

    val caseEven =
      let val hE = Thm.assume (ctermC (jT evenX))
      in Thm.implies_intr (ctermC (jT evenX)) hE end;   (* even x = goal directly *)

    val PoddX = Abs("c", natT, oeq xF (add (mult two (Bound 0)) (suc ZeroC)));
    val caseOdd =
      let
        val hO = Thm.assume (ctermC (jT oddX));
        fun oddBodyFn c (hc : thm) =                     (* hc : oeq x (two*c + 1) *)
          let
            val u  = mult two c;                          (* u = two*c *)
            val s1 = suc ZeroC;
            (* mult x x = add (add (mult u u) u) (add u s1) , then = (two*A) + 1 *)
            (* e1: (x*x) = ((u+1)*x)  [cong_l on hc] *)
            val e1 = mult_cong_lC (xF, add u s1, xF) hc;             (* (x*x) = ((u+1)*x) *)
            (* e2: ((u+1)*x) = (u*x + 1*x)  [right_distrib] *)
            val e2 = right_distrib_atC (u, s1, xF);                  (* ((u+1)*x) = (u*x + (1*x)) *)
            (* e3: (1*x) = x  ; cong_r: (u*x + 1*x) = (u*x + x) *)
            val e3 = mult1l_atCsq xF;                                (* (1*x) = x *)
            val e3c= add_cong_rC (mult u xF, mult s1 xF, xF) e3;     (* (u*x + 1*x) = (u*x + x) *)
            val chainA = oeq_trans OF [oeq_trans OF [e1, e2], e3c];  (* (x*x) = (u*x + x) *)
            (* now (u*x) = (add (mult u u) u) :
                 e4: (u*x) = (u*(u+1))      [cong_r on hc]
                 e5: (u*(u+1)) = (u*u + u*1) [left_distrib]
                 e6: (u*1) = u ; cong_r: (u*u + u*1) = (u*u + u) *)
            val e4 = mult_cong_rC (u, xF, add u s1) hc;              (* (u*x) = (u*(u+1)) *)
            val e5 = left_distrib_atC (u, u, s1);                    (* (u*(u+1)) = (u*u + u*1) *)
            val e6 = mult1r_atCsq u;                                 (* (u*1) = u *)
            val e6c= add_cong_rC (mult u u, mult u s1, u) e6;        (* (u*u + u*1) = (u*u + u) *)
            val ux_form = oeq_trans OF [oeq_trans OF [e4, e5], e6c]; (* (u*x) = (u*u + u) *)
            (* substitute into (u*x + x): cong_l *)
            val congUX = add_cong_lC (mult u xF, add (mult u u) u, xF) ux_form;
                                                                     (* (u*x + x) = ((u*u + u) + x) *)
            val chainB = oeq_trans OF [chainA, congUX];              (* (x*x) = ((u*u + u) + x) *)
            (* x = u+1 : cong_r on the trailing x *)
            val congX = add_cong_rC (add (mult u u) u, xF, add u s1) hc;
                                                                     (* ((u*u+u)+x) = ((u*u+u)+(u+1)) *)
            val chainC = oeq_trans OF [chainB, congX];               (* (x*x) = ((u*u+u)+(u+1)) *)
            (* reassociate: ((u*u+u)+(u+1)) = (((u*u+u)+u)+1)  [add_assoc sym] *)
            val asA = add_assoc_atC (add (mult u u) u, u, s1);       (* (((u*u+u)+u)+1) = ((u*u+u)+(u+1)) *)
            val asAs= oeq_sym OF [asA];                              (* ((u*u+u)+(u+1)) = (((u*u+u)+u)+1) *)
            val chainD = oeq_trans OF [chainC, asAs];                (* (x*x) = (((u*u+u)+u)+1) *)
            (* ((u*u+u)+u) = (u*u + (u+u))  [add_assoc] ; cong_l on +1 *)
            val asB = add_assoc_atC (mult u u, u, u);                (* ((u*u+u)+u) = (u*u + (u+u)) *)
            val asBc= add_cong_lC (add (add (mult u u) u) u, add (mult u u) (add u u), s1) asB;
                                                                     (* (((u*u+u)+u)+1) = ((u*u+(u+u))+1) *)
            val chainE = oeq_trans OF [chainD, asBc];                (* (x*x) = ((u*u+(u+u))+1) *)
            (* u*u = two*(c*u) :  mult_assoc (two,c,u) : ((two*c)*u) = (two*(c*u)) ;
               u = two*c so (u*u) = ((two*c)*u). *)
            val ass = mult_assoc_atC (two, c, u);                    (* ((two*c)*u) = (two*(c*u)) *)
            (* (u+u) = (two*u)  [mult_two_eqC sym] *)
            val tt  = mult_two_eqC u;                                (* (two*u) = (u+u) *)
            val tts = oeq_sym OF [tt];                               (* (u+u) = (two*u) *)
            (* (u*u + (u+u)) = (two*(c*u) + two*u) *)
            val c1  = add_cong_lC (mult u u, mult two (mult c u), add u u) ass;
                                                                     (* (u*u+(u+u)) = (two*(c*u)+(u+u)) *)
            val c2  = add_cong_rC (mult two (mult c u), add u u, mult two u) tts;
                                                                     (* (two*(c*u)+(u+u)) = (two*(c*u)+two*u) *)
            val sumEq = oeq_trans OF [c1, c2];                       (* (u*u+(u+u)) = (two*(c*u)+two*u) *)
            (* (two*(c*u) + two*u) = two*((c*u)+u)  [left_distrib sym] *)
            val ld  = left_distrib_atC (two, mult c u, u);           (* two*((c*u)+u) = (two*(c*u)+two*u) *)
            val lds = oeq_sym OF [ld];                               (* (two*(c*u)+two*u) = two*((c*u)+u) *)
            val twoA = oeq_trans OF [sumEq, lds];                    (* (u*u+(u+u)) = two*((c*u)+u) *)
            (* cong_l on +1 : ((u*u+(u+u))+1) = (two*A + 1) *)
            val Aexpr = add (mult c u) u;                            (* A = (c*u)+u *)
            val congA = add_cong_lC (add (mult u u) (add u u), mult two Aexpr, s1) twoA;
                                                                     (* ((u*u+(u+u))+1) = (two*A + 1) *)
            val xx_odd = oeq_trans OF [chainE, congA];               (* (x*x) = (two*A + 1) *)
            (* now (two*A + 1) = (two*k) :  from (x*x) = (two*A+1) and (x*x)=(two*k) *)
            val odd_eq = oeq_trans OF [oeq_sym OF [xx_odd], sqHyp];  (* (two*A + 1) = (two*k) *)
            val fls = odd_not_even_atC (Aexpr, kF) odd_eq;           (* oFalse *)
            val g   = (oFalse_elimC_at goalEx) OF [fls];             (* goal *)
          in g end;
        val g = exE_elimC (PoddX, goalEx) hO "co" oddBodyFn;
      in Thm.implies_intr (ctermC (jT oddX)) g end;

    val concl = disjE_elimC (evenX, oddX, goalEx) parAt caseEven caseOdd;
    val disch = Thm.implies_intr (ctermC sqHypP) concl;
  in varify disch end;

(* ============================================================================
   sq_lt_cancel : jT (lt (mult y y) (mult x x)) ==> jT (lt y x)
     le_total y x:
       le x y : mono => le (x*x)(y*y) ; with lt(y*y)(x*x)=le(Suc(y*y))(x*x):
                le_trans (Suc(y*y))(x*x)(y*y) => le(Suc(y*y))(y*y)=lt(y*y)(y*y) =>
                lt_irrefl => oFalse => oFalse_elim => lt y x.
       le y x : ex_middle (oeq y x):
                  oeq y x : (x*x)=(y*y) (cong both) ; subst into hyp =>
                            lt(y*y)(y*y) => lt_irrefl => oFalse => goal.
                  neg(oeq y x) : le_neq_lt (le y x)(neg) => lt y x = goal.
   ============================================================================ *)
val mult_le_mono_vC = varify mult_le_mono;
fun mult_le_mono_atC (ct, jt, kt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtC
        [(("c",0), ctermC ct), (("j",0), ctermC jt), (("k",0), ctermC kt)] mult_le_mono_vC)
  in Thm.implies_elim inst h end;

val sq_lt_cancel =
  let
    val xF = Free("x", natT); val yF = Free("y", natT);
    val ltHypP = jT (lt (mult yF yF) (mult xF xF));
    val ltHyp  = Thm.assume (ctermC ltHypP);            (* le (Suc(y*y)) (x*x) *)
    val goalC  = lt yF xF;
    val lt_tot = le_total_at (yF, xF);                  (* Disj (le y x)(le x y) *)

    (* helper : le x y => le (x*x)(y*y) *)
    fun sq_mono_le hle_xy =                              (* hle_xy : le x y *)
      let
        (* le (x*x)(x*y) : mult_le_mono c:=x on (le x y) *)
        val m1 = mult_le_mono_atC (xF, xF, yF) hle_xy;        (* le (x*x)(x*y) *)
        (* le (y*x)(y*y) : mult_le_mono c:=y on (le x y) *)
        val m2 = mult_le_mono_atC (yF, xF, yF) hle_xy;        (* le (y*x)(y*y) *)
        (* (x*y) = (y*x)  [mult_comm] ; le_subst_l: le (y*x)(y*y) -> le (x*y)(y*y) *)
        val cyx = multcomm_atCsq (yF, xF);                    (* (y*x) = (x*y) *)
        val m2'  = le_subst_l (mult yF xF, mult xF yF, mult yF yF) cyx m2;  (* le (x*y)(y*y) *)
        (* le_trans (x*x)(x*y)(y*y) *)
      in le_trans_at (mult xF xF, mult xF yF, mult yF yF) m1 m2' end;       (* le (x*x)(y*y) *)

    (* CASE le x y -> contradiction -> lt y x *)
    val caseXY =
      let
        val hle = Thm.assume (ctermC (jT (le xF yF)));
        val le_xx_yy = sq_mono_le hle;                       (* le (x*x)(y*y) *)
        (* lt (y*y)(x*x) = le (Suc(y*y))(x*x) = ltHyp ; le_trans (Suc(y*y))(x*x)(y*y) *)
        val le_S_yy = le_trans_at (suc (mult yF yF), mult xF xF, mult yF yF) ltHyp le_xx_yy;
                                                             (* le (Suc(y*y))(y*y) = lt (y*y)(y*y) *)
        val fls = lt_irrefl_atC (mult yF yF) le_S_yy;        (* oFalse *)
        val g   = (oFalse_elimC_at goalC) OF [fls];          (* lt y x *)
      in Thm.implies_intr (ctermC (jT (le xF yF))) g end;

    (* CASE le y x -> ex_middle (oeq y x) *)
    val caseYX =
      let
        val hle = Thm.assume (ctermC (jT (le yF xF)));
        val em  = ex_middle_at (oeq yF xF);                  (* Disj (oeq y x)(neg(oeq y x)) *)
        val sub_caseEq =
          let
            val heq = Thm.assume (ctermC (jT (oeq yF xF)));  (* oeq y x *)
            (* (x*x) = (y*y) via cong both (using oeq x y) ; then subst into ltHyp *)
            val hxy = oeq_sym OF [heq];                       (* oeq x y *)
            (* lt (y*y)(x*x) -> lt (y*y)(y*y) by rewriting x*x's args to y.
               (x*x) = (y*x) [cong_l with oeq x y] ; (y*x) = (y*y) [cong_r with oeq x y] *)
            val cl  = mult_cong_lC (xF, yF, xF) hxy;          (* (x*x) = (y*x) *)
            val cr  = mult_cong_rC (yF, xF, yF) hxy;          (* (y*x) = (y*y) *)
            val xx_yy = oeq_trans OF [cl, cr];                (* (x*x) = (y*y) *)
            (* lt (y*y)(x*x) -> lt (y*y)(y*y) : lt_subst_r on second arg *)
            val lt_yy = lt_subst_r (mult yF yF, mult xF xF, mult yF yF) xx_yy ltHyp;
                                                             (* lt (y*y)(y*y) *)
            val fls = lt_irrefl_atC (mult yF yF) lt_yy;       (* oFalse *)
            val g   = (oFalse_elimC_at goalC) OF [fls];       (* lt y x *)
          in Thm.implies_intr (ctermC (jT (oeq yF xF))) g end;
        val sub_caseNeq =
          let
            val hneq = Thm.assume (ctermC (jT (neg (oeq yF xF))));  (* neg(oeq y x) *)
            val g = le_neq_lt_atCsq (yF, xF) hle hneq;        (* lt y x *)
          in Thm.implies_intr (ctermC (jT (neg (oeq yF xF)))) g end;
        val g = disjE_elimC (oeq yF xF, neg (oeq yF xF), goalC) em sub_caseEq sub_caseNeq;
      in Thm.implies_intr (ctermC (jT (le yF xF))) g end;

    val concl = disjE_elimC (le yF xF, le xF yF, goalC) lt_tot caseYX caseXY;
    val disch = Thm.implies_intr (ctermC ltHypP) concl;
  in varify disch end;

(* ============================================================================
   VALIDATION
   ============================================================================ *)
fun checkSq (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtC (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtC intended ^ "\n");
          false)
  end;

val cVsq = Var (("c",0), natT);
val jVsq = Var (("j",0), natT);
val kVsq = Var (("k",0), natT);
val aVsq = Var (("a",0), natT);
val bVsq = Var (("b",0), natT);
val eVsq = Var (("e",0), natT);
val xVsq = Var (("x",0), natT);
val yVsq = Var (("y",0), natT);

val mult_le_mono_intended =
  Logic.mk_implies (jT (le jVsq kVsq), jT (le (mult cVsq jVsq) (mult cVsq kVsq)));
val mult_zero_cancel_intended =
  Logic.mk_implies (jT (lt ZeroC cVsq),
    Logic.mk_implies (jT (oeq (mult cVsq eVsq) ZeroC), jT (oeq eVsq ZeroC)));
val mult_left_cancel_intended =
  Logic.mk_implies (jT (lt ZeroC cVsq),
    Logic.mk_implies (jT (oeq (mult cVsq aVsq) (mult cVsq bVsq)), jT (oeq aVsq bVsq)));
val parity_intended =
  jT (mkDisj (mkEx (Abs("c", natT, oeq xVsq (mult two (Bound 0)))))
             (mkEx (Abs("c", natT, oeq xVsq (add (mult two (Bound 0)) (suc ZeroC))))));
val odd_not_even_intended =
  Logic.mk_implies (jT (oeq (add (mult two aVsq) (suc ZeroC)) (mult two bVsq)), jT oFalseC);
val sq_even_even_intended =
  Logic.mk_implies (jT (oeq (mult xVsq xVsq) (mult two kVsq)),
    jT (mkEx (Abs("c", natT, oeq xVsq (mult two (Bound 0))))));
val sq_lt_cancel_intended =
  Logic.mk_implies (jT (lt (mult yVsq yVsq) (mult xVsq xVsq)), jT (lt yVsq xVsq));

val r_mlm  = checkSq ("mult_le_mono",     mult_le_mono,     mult_le_mono_intended);
val r_mzc  = checkSq ("mult_zero_cancel", mult_zero_cancel, mult_zero_cancel_intended);
val r_mlc  = checkSq ("mult_left_cancel", mult_left_cancel, mult_left_cancel_intended);
val r_par  = checkSq ("parity",           parity,           parity_intended);
val r_one  = checkSq ("odd_not_even",     odd_not_even,     odd_not_even_intended);
val r_see  = checkSq ("sq_even_even",     sq_even_even,     sq_even_even_intended);
val r_slc  = checkSq ("sq_lt_cancel",     sq_lt_cancel,     sq_lt_cancel_intended);

val () =
  if r_par then out "PARITY_OK\n" else out "PARITY_FAILED\n";

val () =
  if r_mlm andalso r_mzc andalso r_mlc andalso r_par
     andalso r_one andalso r_see andalso r_slc
  then out "SQRT2_HELPERS_DONE\n"
  else out "SQRT2_HELPERS_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  SQRT 2 IS IRRATIONAL  —  by INFINITE DESCENT (strong_induct)  ***
   ----------------------------------------------------------------------------
   Everything routes through ctxtS2 / ctermS2 (where strong_induct lives; thyS2
   extends thyC so every thyC theorem — the SQRT2 helpers, arithmetic, the
   classical connectives — lifts by varify).  All NEW cterms use ctermS2.

   Sol x := Conj (lt Zero x) (Ex (%b. oeq (mult x x) (mult two (mult b b))))

   TARGET sqrt2_irrational : jT (neg (Ex (%a. Sol a)))
     i.e. there are NO positive naturals a,b with a*a = 2*(b*b).
   ============================================================================ *)

val () = out "DESCENT_BEGIN\n";

(* ---- S2 congruence / arithmetic instantiators (build from the _vC axioms) ---- *)
fun mult_cong_lS2 (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 pT), (("b",0), ctermS2 qT)] oeq_subst_vC);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtS2 [(("a",0), ctermS2 (mult pT kT))] oeq_refl_vC);
  in inst OF [hpq, refl_pk] end;
fun mult_cong_rS2 (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 pT), (("b",0), ctermS2 qT)] oeq_subst_vC);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtS2 [(("a",0), ctermS2 (mult hT pT))] oeq_refl_vC);
  in inst OF [hpq, refl_hp] end;
fun add_cong_lS2 (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 pT), (("b",0), ctermS2 qT)] oeq_subst_vC);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtS2 [(("a",0), ctermS2 (add pT kT))] oeq_refl_vC);
  in inst OF [hpq, refl_pk] end;
fun add_cong_rS2 (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 pT), (("b",0), ctermS2 qT)] oeq_subst_vC);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtS2 [(("a",0), ctermS2 (add hT pT))] oeq_refl_vC);
  in inst OF [hpq, refl_hp] end;

fun add0S2_at t         = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] add_0_vC);
fun addSucS2_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtS2
                            [(("m",0), ctermS2 mt),(("n",0), ctermS2 nt)] add_Suc_vC);
fun add0rS2_at t        = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] add_0_right_vC);
fun addSrS2_at (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtS2
                            [(("m",0), ctermS2 mt),(("n",0), ctermS2 nt)] add_Suc_right_vC);
fun mult0rS2_at t       = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] mult_0_right_vC);
fun multSrS2_at (nt,mt) = beta_norm (Drule.infer_instantiate ctxtS2
                            [(("n",0), ctermS2 nt),(("m",0), ctermS2 mt)] mult_Suc_right_vC);
val mult_0_vS2 = varify mult_0;
fun mult0lS2_at t       = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] mult_0_vS2);
fun Suc_neq_Zero_atS2 t = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] Suc_neq_Zero_vC);
fun oFalse_elimS2_at rT = beta_norm (Drule.infer_instantiate ctxtS2 [(("R",0), ctermS2 rT)] oFalse_elim_vC);

val mult_assoc_vS2 = varify mult_assoc;
fun mult_assoc_atS2 (mT,nT,kT) = beta_norm (Drule.infer_instantiate ctxtS2
      [(("m",0), ctermS2 mT),(("n",0), ctermS2 nT),(("k",0), ctermS2 kT)] mult_assoc_vS2);
val mult_comm_vS2 = varify mult_comm;
fun multcomm_atS2 (mt,nt) = beta_norm (Drule.infer_instantiate ctxtS2
      [(("m",0), ctermS2 mt),(("n",0), ctermS2 nt)] mult_comm_vS2);
val add_assoc_vS2 = varify add_assoc;
fun add_assoc_atS2 (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtS2
      [(("m",0), ctermS2 mt),(("n",0), ctermS2 nt),(("k",0), ctermS2 kt)] add_assoc_vS2);

(* mult_two_eqS2 y : oeq (mult two y) (add y y)  on ctxtS2 *)
val mult_Suc_vS2 = varify mult_Suc;
fun multSucS2_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtS2
      [(("m",0), ctermS2 mt),(("n",0), ctermS2 nt)] mult_Suc_vS2);
fun mult_two_eqS2 y =
  let
    val s1 = multSucS2_at (suc ZeroC, y);          (* mult (Suc(Suc 0)) y = add y (mult (Suc 0) y) *)
    val s2 = multSucS2_at (ZeroC, y);              (* mult (Suc 0) y = add y (mult 0 y) *)
    val m0 = mult0lS2_at y;                         (* mult 0 y = 0 *)
    val s2b = add_cong_rS2 (y, mult ZeroC y, ZeroC) m0;   (* add y (mult 0 y) = add y 0 *)
    val s2c = oeq_trans OF [s2, s2b];             (* mult (Suc 0) y = add y 0 *)
    val a0 = add0rS2_at y;                          (* add y 0 = y *)
    val s2d = oeq_trans OF [s2c, a0];             (* mult (Suc 0) y = y *)
    val s1b = add_cong_rS2 (y, mult (suc ZeroC) y, y) s2d;  (* add y (mult(Suc 0) y) = add y y *)
  in oeq_trans OF [s1, s1b] end;                  (* mult two y = add y y *)

(* le_intro on ctxtS2 *)
fun le_introS2 (mT, nT, w) hyp =
  let
    val Pabs = Abs ("p", natT, oeq nT (add mT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 w)] exI_vC);
  in inst OF [hyp] end;

(* zero_le on ctxtS2 *)
val zero_le_vS2 = varify zero_le;
fun zero_leS2_at t = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] zero_le_vS2);

(* le_neq_lt on ctxtS2 *)
val le_neq_lt_vS2 = varify le_neq_lt;
fun le_neq_lt_atS2 (dt, nt) hle hneq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("d",0), ctermS2 dt), (("n",0), ctermS2 nt)] le_neq_lt_vS2)
  in Thm.implies_elim (Thm.implies_elim inst hle) hneq end;

(* disj_zero_or_suc on ctxtS2 *)
val disj_zero_or_suc_vS2 = varify disj_zero_or_suc;
fun dzosS2_at t = beta_norm (Drule.infer_instantiate ctxtS2 [(("p",0), ctermS2 t)] disj_zero_or_suc_vS2);

(* lt-substitution on ctxtS2 (lt m n == le (Suc m) n) *)
fun lt_subst_r_S2 (rT, pT, qT) hoeq hlt =
  let
    val zF   = Free("z_ltrS2", natT);
    val Pabs = Term.lambda zF (lt rT zF);
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 pT), (("b",0), ctermS2 qT)] oeq_subst_vC);
  in (inst OF [hoeq]) OF [hlt] end;

(* mp on ctxtS2 (already have mp_atS2) ; neg abbreviation already in scope *)

(* c_ne0_of_lt0 on ctxtS2 : jT (lt Zero c) ==> jT (neg (oeq c Zero)) *)
fun c_ne0_of_lt0_S2 cF h_lt0 =
  let
    val Pabs = Abs("p", natT, oeq cF (add (suc ZeroC) (Bound 0)));
    val ez   = Thm.assume (ctermS2 (jT (oeq cF ZeroC)));
    fun body p (hp : thm) =                               (* hp : oeq c (add 1 p) *)
      let
        val aS    = addSucS2_at (ZeroC, p);                (* (1 + p) = Suc (0 + p) *)
        val c_Sp  = oeq_trans OF [hp, aS];                (* c = Suc (0 + p) *)
        val z_Sp  = oeq_trans OF [oeq_sym OF [ez], c_Sp]; (* 0 = Suc (0 + p) *)
        val Sp_z  = oeq_sym OF [z_Sp];                    (* Suc (0 + p) = 0 *)
      in (Suc_neq_Zero_atS2 (add ZeroC p)) OF [Sp_z] end; (* oFalse *)
    val falseThm = exE_elimS2 (Pabs, oFalseC) h_lt0 "wp_cne0" body;
    val imp = Thm.implies_intr (ctermS2 (jT (oeq cF ZeroC))) falseThm;
  in impI_atS2 (oeq cF ZeroC, oFalseC) imp end;

(* ---- lift the SQRT2 helpers onto ctxtS2 ---- *)
val sq_even_even_vS2     = varify sq_even_even;
fun sq_even_even_atS2 (xt, kt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("x",0), ctermS2 xt), (("k",0), ctermS2 kt)] sq_even_even_vS2)
  in Thm.implies_elim inst h end;

val mult_left_cancel_vS2 = varify mult_left_cancel;
fun mult_left_cancel_atS2 (ct, at, bt) hlt heq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("c",0), ctermS2 ct), (("a",0), ctermS2 at), (("b",0), ctermS2 bt)] mult_left_cancel_vS2)
  in Thm.implies_elim (Thm.implies_elim inst hlt) heq end;

val mult_zero_cancel_vS2 = varify mult_zero_cancel;
fun mult_zero_cancel_atS2 (ct, et) hlt hmz =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("c",0), ctermS2 ct), (("e",0), ctermS2 et)] mult_zero_cancel_vS2)
  in Thm.implies_elim (Thm.implies_elim inst hlt) hmz end;

val sq_lt_cancel_vS2     = varify sq_lt_cancel;
fun sq_lt_cancel_atS2 (yt, xt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("y",0), ctermS2 yt), (("x",0), ctermS2 xt)] sq_lt_cancel_vS2)
  in Thm.implies_elim inst h end;

(* two_abbrev already = two = suc (suc ZeroC) from the base. *)

(* lt_0_two : jT (lt Zero two)  (= le (Suc Zero) two)  witness (Suc Zero):
     add (Suc Zero) (Suc Zero) = Suc (add Zero (Suc Zero)) = Suc (Suc Zero) = two. *)
val lt_0_two =
  let
    val a1  = addSucS2_at (ZeroC, suc ZeroC);     (* (1 + 1) = Suc (0 + 1) *)
    val a0  = add0S2_at (suc ZeroC);              (* (0 + 1) = 1 *)
    val sa0 = Suc_cong OF [a0];                    (* Suc(0+1) = Suc 1 = two *)
    val two_eq = oeq_trans OF [a1, sa0];          (* (1 + 1) = two *)
    val hyp = oeq_sym OF [two_eq];                (* two = (1 + 1) *)
  in le_introS2 (suc ZeroC, two, suc ZeroC) hyp end;  (* le (Suc 0) two = lt Zero two *)

(* The body-abstraction of Sol's existential and Sol itself (capture-avoiding). *)
fun solExBody t = mkEx (Abs("b", natT, oeq (mult t t) (mult two (mult (Bound 0) (Bound 0)))));
fun solTerm t = mkConj (lt ZeroC t) (solExBody t);

val () = out "DESCENT_HELPERS_READY\n";

(* ============================================================================
   THE DESCENT STEP : fix n, given the strong IH (!!m. lt m n ==> jT (neg (Sol m))),
   prove jT (neg (Sol n)) = jT (Imp (Sol n) oFalse).
   ============================================================================ *)
val sqrt2_no_sol =       (* = strong_induct result : jT (neg (Sol k)) for schematic k *)
  let
    val nStep = Free("n_step", natT);
    (* P := %x. neg (Sol x).  IH : !!m. lt m n ==> jT (P m) = jT (neg (Sol m)) *)
    val mIH   = Free("m_ih", natT);
    val Gprop = Logic.all mIH (Logic.mk_implies (jT (lt mIH nStep), jT (neg (solTerm mIH))));
    val Hthm  = Thm.assume (ctermS2 Gprop);
    fun applyIH dt h_lt =                       (* h_lt : jT (lt d n) -> jT (neg (Sol d)) *)
      let val hAt = Thm.forall_elim (ctermS2 dt) Hthm
      in Thm.implies_elim hAt h_lt end;

    (* prove jT (neg (Sol n)) by impI: assume Sol n, derive oFalse *)
    val solN_P = jT (solTerm nStep);
    val hSolN  = Thm.assume (ctermS2 solN_P);

    val falseFromSol =
      let
        (* break Sol n *)
        val h_pos = conjunct1_atS2 (lt ZeroC nStep, solExBody nStep) hSolN;   (* lt Zero n *)
        val h_ex  = conjunct2_atS2 (lt ZeroC nStep, solExBody nStep) hSolN;   (* Ex(b. n*n = 2*(b*b)) *)
        val PexB  = Abs("b", natT, oeq (mult nStep nStep) (mult two (mult (Bound 0) (Bound 0))));
        fun exBody b (hb : thm) =        (* hb : oeq (mult n n) (mult two (mult b b)) *)
          let
            val bb = mult b b;
            (* n*n = 2*(b*b) is even : sq_even_even x:=n k:=(b*b) -> Ex(c. n = 2*c) *)
            val evenN = sq_even_even_atS2 (nStep, bb) hb;       (* Ex(c. oeq n (2*c)) *)
            val PevC  = Abs("c", natT, oeq nStep (mult two (Bound 0)));
            fun evBody c (hc : thm) =    (* hc : oeq n (mult two c) *)
              let
                val u  = mult two c;     (* u = 2*c, and hc : n = u *)
                val cc = mult c c;
                (* ---- n*n = 2*(2*(c*c)) ---- *)
                (* n*n = u*u *)
                val cl   = mult_cong_lS2 (nStep, u, nStep) hc;    (* (n*n) = (u*n) *)
                val cr   = mult_cong_rS2 (u, nStep, u) hc;        (* (u*n) = (u*u) *)
                val nn_uu= oeq_trans OF [cl, cr];                 (* (n*n) = (u*u) *)
                (* u*u = (2c)*(2c) ; assoc: ((2*c)*u) = (2*(c*u)) *)
                val a1   = mult_assoc_atS2 (two, c, u);           (* ((2*c)*u) = (2*(c*u)) *)
                                                                  (* note u*u = (2*c)*u syntactically *)
                (* c*u = 2*(c*c) :
                     c*u = c*(2*c)            [u = 2*c]
                         = (c*2)*c            [assoc sym]
                         = (2*c)*c            [comm on c*2]
                         = 2*(c*c)            [assoc] *)
                val cu_assoc = mult_assoc_atS2 (c, two, c);       (* ((c*2)*c) = (c*(2*c)) *)
                val cu_assocS= oeq_sym OF [cu_assoc];             (* (c*(2*c)) = ((c*2)*c) *)
                (* c*u = c*(2*c) is just definitional (u = 2*c), so cu_assocS : (c*u) = ((c*2)*c) *)
                val ccomm = multcomm_atS2 (c, two);               (* (c*2) = (2*c) *)
                val ccomm_l = mult_cong_lS2 (mult c two, u, c) ccomm; (* ((c*2)*c) = ((2*c)*c) *)
                val a2    = mult_assoc_atS2 (two, c, c);          (* ((2*c)*c) = (2*(c*c)) *)
                val cu_eq = oeq_trans OF [oeq_trans OF [cu_assocS, ccomm_l], a2]; (* (c*u) = (2*(c*c)) *)
                (* 2*(c*u) = 2*(2*(c*c)) *)
                val cong2 = mult_cong_rS2 (two, mult c u, mult two cc) cu_eq;
                                                                  (* (2*(c*u)) = (2*(2*(c*c))) *)
                val uu_2   = oeq_trans OF [a1, cong2];            (* (u*u) = (2*(2*(c*c))) *)
                val nn_2   = oeq_trans OF [nn_uu, uu_2];          (* (n*n) = (2*(2*(c*c))) *)
                (* combine with hb : n*n = 2*(b*b) ->  2*(b*b) = 2*(2*(c*c)) *)
                val sum_eq = oeq_trans OF [oeq_sym OF [hb], nn_2]; (* (2*(b*b)) = (2*(2*(c*c))) *)
                (* mult_left_cancel (lt 0 two) -> (b*b) = (2*(c*c)) *)
                val bb_eq  = mult_left_cancel_atS2 (two, bb, mult two cc) lt_0_two sum_eq;
                                                                  (* (b*b) = (2*(c*c)) *)
                (* ============ b is a SMALLER positive solution ============ *)
                (* neg (oeq b 0) : assume b=0 -> b*b=0 -> n*n=0 -> n=0 -> contradicts lt 0 n *)
                val bNe0 =
                  let
                    val hb0 = Thm.assume (ctermS2 (jT (oeq b ZeroC)));     (* b = 0 *)
                    val bbl = mult_cong_lS2 (b, ZeroC, b) hb0;             (* (b*b) = (0*b) *)
                    val z0b = mult0lS2_at b;                               (* (0*b) = 0 *)
                    val bb0 = oeq_trans OF [bbl, z0b];                     (* (b*b) = 0 *)
                    (* n*n = 2*(b*b) = 2*0 = 0 *)
                    val cong = mult_cong_rS2 (two, bb, ZeroC) bb0;         (* (2*(b*b)) = (2*0) *)
                    val m20  = mult0rS2_at two;                            (* (2*0) = 0 *)
                    val nn0  = oeq_trans OF [oeq_trans OF [hb, cong], m20]; (* (n*n) = 0 *)
                    val n0   = mult_zero_cancel_atS2 (nStep, nStep) h_pos nn0; (* oeq n 0 *)
                    val nNe0 = c_ne0_of_lt0_S2 nStep h_pos;                (* neg (oeq n 0) *)
                    val fls  = mp_atS2 (oeq nStep ZeroC, oFalseC) nNe0 n0; (* oFalse *)
                    val imp  = Thm.implies_intr (ctermS2 (jT (oeq b ZeroC))) fls;
                  in impI_atS2 (oeq b ZeroC, oFalseC) imp end;            (* neg (oeq b 0) *)
                (* lt Zero b : le_neq_lt (zero_le b)(neg(oeq Zero b)) *)
                val zle_b = zero_leS2_at b;                               (* le Zero b *)
                val zNeb  =
                  let
                    val hzb = Thm.assume (ctermS2 (jT (oeq ZeroC b)));    (* 0 = b *)
                    val bz  = oeq_sym OF [hzb];                           (* b = 0 *)
                    val fls = mp_atS2 (oeq b ZeroC, oFalseC) bNe0 bz;     (* oFalse *)
                    val imp = Thm.implies_intr (ctermS2 (jT (oeq ZeroC b))) fls;
                  in impI_atS2 (oeq ZeroC b, oFalseC) imp end;           (* neg (oeq 0 b) *)
                val lt0b = le_neq_lt_atS2 (ZeroC, b) zle_b zNeb;          (* lt Zero b *)
                (* ============ lt b n ============ *)
                (* n*n = (b*b) + (b*b) : 2*(b*b) = (b*b)+(b*b) [mult_two_eqS2] *)
                val two_bb = mult_two_eqS2 bb;                            (* (2*(b*b)) = ((b*b)+(b*b)) *)
                val nn_sum = oeq_trans OF [hb, two_bb];                   (* (n*n) = ((b*b)+(b*b)) *)
                (* lt Zero (b*b) : b*b != 0 (else mult_zero_cancel(lt 0 b)(b*b=0)->b=0 contra) *)
                val bbNe0 =
                  let
                    val hbb0 = Thm.assume (ctermS2 (jT (oeq bb ZeroC)));  (* b*b = 0 *)
                    val b0   = mult_zero_cancel_atS2 (b, b) lt0b hbb0;    (* oeq b 0 *)
                    val fls  = mp_atS2 (oeq b ZeroC, oFalseC) bNe0 b0;    (* oFalse *)
                    val imp  = Thm.implies_intr (ctermS2 (jT (oeq bb ZeroC))) fls;
                  in impI_atS2 (oeq bb ZeroC, oFalseC) imp end;          (* neg (oeq (b*b) 0) *)
                val zle_bb = zero_leS2_at bb;                            (* le Zero (b*b) *)
                val zNebb  =
                  let
                    val hzbb = Thm.assume (ctermS2 (jT (oeq ZeroC bb)));  (* 0 = b*b *)
                    val bbz  = oeq_sym OF [hzbb];                         (* b*b = 0 *)
                    val fls  = mp_atS2 (oeq bb ZeroC, oFalseC) bbNe0 bbz; (* oFalse *)
                    val imp  = Thm.implies_intr (ctermS2 (jT (oeq ZeroC bb))) fls;
                  in impI_atS2 (oeq ZeroC bb, oFalseC) imp end;          (* neg (oeq 0 (b*b)) *)
                val lt0bb = le_neq_lt_atS2 (ZeroC, bb) zle_bb zNebb;      (* lt Zero (b*b) = le (Suc 0)(b*b) *)
                (* exE over lt0bb = le (Suc 0)(b*b) : witness p, hp : (b*b) = (1 + p) *)
                val Plt0bb = Abs("p", natT, oeq bb (add (suc ZeroC) (Bound 0)));
                fun ltbn_body p (hp : thm) =     (* hp : oeq (b*b) (add (Suc 0) p) *)
                  let
                    (* (b*b)+(b*b) = (b*b) + (1 + p)  [cong_r on hp, RIGHT operand] *)
                    val congR = add_cong_rS2 (bb, bb, add (suc ZeroC) p) hp;
                                                          (* ((b*b)+(b*b)) = ((b*b)+(1+p)) *)
                    (* ((b*b)+(1+p)) = (((b*b)+1)+p)  [add_assoc sym] *)
                    val asc   = add_assoc_atS2 (bb, suc ZeroC, p);  (* (((b*b)+1)+p) = ((b*b)+(1+p)) *)
                    val ascS  = oeq_sym OF [asc];                   (* ((b*b)+(1+p)) = (((b*b)+1)+p) *)
                    (* (b*b)+1 = Suc(b*b) *)
                    val bb1   = addSrS2_at (bb, ZeroC);             (* ((b*b)+Suc 0) = Suc((b*b)+0) *)
                    val bb0a  = add0rS2_at bb;                      (* ((b*b)+0) = (b*b) *)
                    val sbb0  = Suc_cong OF [bb0a];                 (* Suc((b*b)+0) = Suc(b*b) *)
                    val bb1_S = oeq_trans OF [bb1, sbb0];           (* ((b*b)+1) = Suc(b*b) *)
                    val congL = add_cong_lS2 (add bb (suc ZeroC), suc bb, p) bb1_S;
                                                          (* (((b*b)+1)+p) = ((Suc(b*b))+p) *)
                    (* chain : ((b*b)+(b*b)) = ((Suc(b*b))+p) *)
                    val sumChain = oeq_trans OF [oeq_trans OF [congR, ascS], congL];
                    (* le (Suc(b*b)) ((b*b)+(b*b)) = lt (b*b) ((b*b)+(b*b)) , witness p *)
                    val lt_bb_sum = le_introS2 (suc bb, add bb bb, p) sumChain;
                    (* rewrite ((b*b)+(b*b)) -> (n*n) :  lt (b*b)(sum) -> lt (b*b)(n*n) *)
                    val sum_nn = oeq_sym OF [nn_sum];               (* ((b*b)+(b*b)) = (n*n) *)
                    val lt_bb_nn = lt_subst_r_S2 (bb, add bb bb, mult nStep nStep) sum_nn lt_bb_sum;
                                                          (* lt (b*b) (n*n) *)
                    (* sq_lt_cancel y:=b x:=n : lt (b*b)(n*n) -> lt b n *)
                    val lt_b_n = sq_lt_cancel_atS2 (b, nStep) lt_bb_nn;   (* lt b n *)
                  in lt_b_n end;
                val lt_b_n = exE_elimS2 (Plt0bb, lt b nStep) lt0bb "p_ltbn" ltbn_body;
                (* ============ apply IH : neg (Sol b) ============ *)
                val negSolB = applyIH b lt_b_n;        (* jT (neg (Sol b)) = jT (Imp (Sol b) oFalse) *)
                (* build Sol b = Conj (lt 0 b) (Ex(bb. b*b = 2*(bb*bb))) , witness c *)
                val PsolB = Abs("b", natT, oeq (mult b b) (mult two (mult (Bound 0) (Bound 0))));
                val solExB = exI_atS2 PsolB c bb_eq;    (* Ex(bb. b*b = 2*(bb*bb)) *)
                val solB   = conjI_atS2 (lt ZeroC b, solExBody b) lt0b solExB;  (* Sol b *)
                val fls    = mp_atS2 (solTerm b, oFalseC) negSolB solB;          (* oFalse *)
              in fls end;
            val g = exE_elimS2 (PevC, oFalseC) evenN "c_w" evBody;
          in g end;
        val g = exE_elimS2 (PexB, oFalseC) h_ex "b_w" exBody;
      in g end;

    val negSolN = impI_atS2 (solTerm nStep, oFalseC)
                    (Thm.implies_intr (ctermS2 solN_P) falseFromSol);   (* jT (neg (Sol n)) *)

    (* step for strong_induct : !!n. (!!m. lt m n ==> jT(P m)) ==> jT (P n) *)
    val stepThm = Thm.forall_intr (ctermS2 nStep) (Thm.implies_intr (ctermS2 Gprop) negSolN);

    (* P := %x. neg (Sol x), capture-avoiding *)
    val Ppred =
      let val zF = Free("z_P", natT)
      in Term.lambda zF (neg (solTerm zF)) end;
    val kF = Free("k", natT);
    val siInst = beta_norm (Drule.infer_instantiate ctxtS2
                   [(("P",0), ctermS2 Ppred), (("k",0), ctermS2 kF)] (varify strong_induct));
    val negSolK = Thm.implies_elim siInst stepThm;       (* jT (neg (Sol k)) *)
  in varify negSolK end;

val () = out "DESCENT_STEP_DONE\n";

(* ============================================================================
   FINAL : sqrt2_irrational : jT (neg (Ex (%a. Sol a)))
     assume Ex(a. Sol a) ; exE witness a, Sol a ; instantiate sqrt2_no_sol at a
     -> neg (Sol a) ; mp -> oFalse ; discharge -> neg (Ex ...).
   ============================================================================ *)
val sqrt2_no_sol_vS2 = varify sqrt2_no_sol;
fun no_sol_at t = beta_norm (Drule.infer_instantiate ctxtS2 [(("k",0), ctermS2 t)] sqrt2_no_sol_vS2);

val sqrt2_irrational =
  let
    (* the existential abstraction %a. Sol a , capture-avoiding via Term.lambda *)
    val ExAbs =
      let val aF = Free("a_sol", natT)
      in Term.lambda aF (solTerm aF) end;
    val exSol = mkEx ExAbs;
    val hEx   = Thm.assume (ctermS2 (jT exSol));
    fun body a (hSolA : thm) =          (* hSolA : jT (Sol a) *)
      let
        val negSolA = no_sol_at a;      (* jT (neg (Sol a)) = jT (Imp (Sol a) oFalse) *)
        val fls = mp_atS2 (solTerm a, oFalseC) negSolA hSolA;   (* oFalse *)
      in fls end;
    val falseThm = exE_elimS2 (ExAbs, oFalseC) hEx "a_ex" body;  (* oFalse *)
    val imp = Thm.implies_intr (ctermS2 (jT exSol)) falseThm;    (* jT exSol ==> jT oFalse *)
  in varify (impI_atS2 (exSol, oFalseC) imp) end;                (* jT (neg (Ex (%a. Sol a))) *)

(* ============================================================================
   VALIDATION : 0-hyp AND aconv the intended schematic goal.
   ============================================================================ *)
fun checkD (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtS2 (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtS2 intended ^ "\n");
          false)
  end;

(* intended : neg (Ex (%a. Conj (lt Zero a) (Ex (%b. oeq (mult a a) (mult two (mult b b)))))) *)
val sqrt2_intended =
  let
    val aF = Free("a_int", natT)
    val ExAbsI = Term.lambda aF (solTerm aF)
  in jT (neg (mkEx ExAbsI)) end;

val r_sqrt2 = checkD ("sqrt2_irrational", sqrt2_irrational, sqrt2_intended);

(* ---- SOUNDNESS PROBE : the kernel must REJECT the positivity-dropped variant ----
   Without `lt Zero a`, a=b=0 IS a solution (0*0 = 2*(0*0)=0), so the statement
   `there are no a,b with a*a = 2*(b*b)` is FALSE.  Our theorem must NOT aconv it. *)
val probe_pos_needed =
  let
    val aF = Free("a_int", natT)
    val bogusBody = Term.lambda aF
          (mkEx (Abs("b", natT, oeq (mult aF aF) (mult two (mult (Bound 0) (Bound 0))))))
    val bogus = jT (neg (mkEx bogusBody))
  in not ((Thm.prop_of sqrt2_irrational) aconv bogus) end;

val () = if probe_pos_needed
         then out "PROBE_OK sqrt2_irrational keeps the lt-Zero-a positivity\n"
         else out "PROBE_UNSOUND sqrt2_irrational dropped positivity (false statement)!\n";

val () =
  if r_sqrt2 then out "OK sqrt2_irrational\n" else out "FAILED sqrt2_irrational\n";

val () =
  if r_sqrt2 andalso probe_pos_needed
  then out "SQRT2_DONE\n"
  else out "SQRT2_FAILED\n";
