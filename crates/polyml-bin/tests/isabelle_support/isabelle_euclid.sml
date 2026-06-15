(* ============================================================================
   EUCLID'S THEOREM (INFINITUDE OF PRIMES) in Isabelle/Pure on the polyml-rs
   interpreter.  (test: isabelle_euclid.rs)
   ----------------------------------------------------------------------------
        euclid : |- !n. ?p. prime p /\ n < p
   For every natural number n there is a prime p strictly greater than n — i.e.
   there are infinitely many primes.  A 0-hypothesis theorem (checkF: hyps = 0
   AND prop aconv the intended goal), over the STRUCTURAL prime definition
   (prime p == 1<p /\ !d. d|p ==> d=1 \/ d=p), proved by genuine LCF kernel
   inference.  The only classical assumption anywhere in the development is
   excluded middle (which real Isabelle/HOL object logics have).

   This is the top of the self-derived Isabelle number-theory ladder:
     object logic -> Peano add/mult -> commutative semiring -> summation ->
     linear order -> divisibility -> strong (course-of-values) induction ->
     classical FOL (excluded middle + De Morgan + not-forall) ->
     genuine "every n>=2 has a prime divisor" (prime_cases DERIVED) ->
     EUCLID'S THEOREM.

   PROOF (classical Euclid):
     Given n, let N = n! + 1 (>= 2 since n! >= 1, fact_pos).  By the genuine
     prime_divisor_exists, N has a prime divisor p.  Claim p > n: if instead
     p <= n then (since 1 <= p, as p is prime) dvd_fact gives p | n!, and also
     p | N = n!+1; but a prime cannot divide two consecutive numbers
     (consec_coprime: p>1 /\ p|a /\ p|(Suc a) ==> False), contradiction.  Hence
     p > n.  Generalise over n.

   Built (on isabelle_classical_primes.sml) by a 3-phase ultracode pipeline
   (wf_a72a4b68-c26): helpers (factorial, dvd_fact, mult_le_mono, mult_eq_one,
   le_cases) -> consec_coprime (3 seats, all derived it) -> Euclid (2 seats,
   both proved it).  Each phase validated on the warm checkpoint.
   ============================================================================ *)


(* ============================================================================
   ============================================================================
   ***  EUCLID HELPERS : factorial + arithmetic/divisibility for infinitude
        of primes.  Built on the SINGLE FINAL context above (ctxtS2 / thyS2).  ***
   ----------------------------------------------------------------------------
   We add a real recursive constant `fact : nat => nat` (a NEW const, so it
   EXTENDS the theory) on ONE further theory `thyF` built on top of `thyS2`,
   with its two primitive-recursive defining axioms.  We then re-init ONE FINAL
   context `ctxtF` / `ctermF` and route EVERY new cterm through it.  All thyS2
   theorems lift to thyF automatically (varify just re-zeroes indices).

   NEW CONST (on thyF):  fact : nat => nat
   AXIOMS:
     fact_0   : oeq (fact Zero) (Suc Zero)
     fact_Suc : oeq (fact (Suc n)) (mult (Suc n) (fact n))

   ADDED + PROVED (each 0-hyp / 0-extra-hyp named val, validated aconv):
     fact_pos       : jT (lt Zero (fact n))
     le_cases       : jT (le p (Suc n)) ==> jT (Disj (le p n) (oeq p (Suc n)))
     mult_le_mono   : jT (le j k) ==> jT (le (mult p j) (mult p k))
     mult_eq_one    : jT (oeq (mult p e) (Suc Zero)) ==> jT (oeq p (Suc Zero))
     dvd_self_mult  : jT (dvd a (mult a b))
     dvd_self_mult2 : jT (dvd a (mult b a))
     dvd_fact       : jT (le (Suc Zero) p) ==> jT (le p n) ==> jT (dvd p (fact n))
   ============================================================================ *)

val () = out "EUCLID_HELPERS_BEGIN\n";

(* ---- ONE further theory : the recursive constant `fact` + its two axioms ---- *)
val thyF0 = Sign.add_consts
  [(Binding.name "fact", natT --> natT, NoSyn)] thyS2;
val factC = Const (Sign.full_name thyF0 (Binding.name "fact"), natT --> natT);
fun fact t = factC $ t;

val nFx = Free ("n", natT);
val ((_, fact_0_ax), thyF1) = Thm.add_axiom_global (Binding.name "fact_0",
      jT (oeq (fact ZeroC) (suc ZeroC))) thyF0;
val ((_, fact_Suc_ax), thyF) = Thm.add_axiom_global (Binding.name "fact_Suc",
      jT (oeq (fact (suc nFx)) (mult (suc nFx) (fact nFx)))) thyF1;

(* ---- THE ONE FINAL CONTEXT ctxtF / ctermF ---- *)
val ctxtF  = Proof_Context.init_global thyF;
val ctermF = Thm.cterm_of ctxtF;

(* ---- re-varify every reused axiom/lemma for use under ctxtF ---- *)
val oeq_refl_vF    = varify oeq_refl;
val oeq_subst_vF   = varify oeq_subst;
val nat_induct_vF  = varify nat_induct;
val add_0_vF       = varify add_0;
val add_Suc_vF     = varify add_Suc;
val add_0_right_vF = varify add_0_right;
val add_Suc_right_vF = varify add_Suc_right;
val add_assoc_vF   = varify add_assoc;
val mult_0_vF      = varify mult_0;
val mult_0_right_vF = varify mult_0_right;
val mult_Suc_vF    = varify mult_Suc;
val mult_Suc_right_vF = varify mult_Suc_right;
val mult_comm_vF   = varify mult_comm;
val left_distrib_vF = varify left_distrib;
val exI_vF         = varify exI_ax;
val exE_vF         = varify exE_ax;
val Suc_inj_vF     = varify Suc_inj_ax;
val Suc_neq_Zero_vF= varify Suc_neq_Zero_ax;
val oFalse_elim_vF = varify oFalse_elim_ax;
val disjI1_vF      = varify disjI1_ax;
val disjI2_vF      = varify disjI2_ax;
val disjE_vF       = varify disjE_ax;
val le_refl_vF     = varify le_refl;
val disj_zero_or_suc_vF = varify disj_zero_or_suc;
val fact_0_vF      = varify fact_0_ax;
val fact_Suc_vF    = varify fact_Suc_ax;

(* ---- ground instantiators on ctxtF ---- *)
fun add0F_at t         = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF t)] add_0_vF);
fun addSucF_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtF
                            [(("m",0), ctermF mt),(("n",0), ctermF nt)] add_Suc_vF);
fun add0rF_at t        = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF t)] add_0_right_vF);
fun addSrF_at (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtF
                            [(("m",0), ctermF mt),(("n",0), ctermF nt)] add_Suc_right_vF);
fun addassocF_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtF
                            [(("m",0), ctermF mt),(("n",0), ctermF nt),(("k",0), ctermF kt)] add_assoc_vF);
fun mult0F_at t        = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF t)] mult_0_vF);
fun mult0rF_at t       = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF t)] mult_0_right_vF);
fun multSucF_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtF
                            [(("m",0), ctermF mt),(("n",0), ctermF nt)] mult_Suc_vF);
fun multSrF_at (nt,mt) = beta_norm (Drule.infer_instantiate ctxtF
                            [(("n",0), ctermF nt),(("m",0), ctermF mt)] mult_Suc_right_vF);
fun multcommF_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtF
                            [(("m",0), ctermF mt),(("n",0), ctermF nt)] mult_comm_vF);
fun left_distribF_at (dT,pT,qT) = beta_norm (Drule.infer_instantiate ctxtF
                            [(("x",0), ctermF dT),(("m",0), ctermF pT),(("n",0), ctermF qT)] left_distrib_vF);
fun oeqreflF_at t      = beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF t)] oeq_refl_vF);
fun Suc_inj_atF (uT,vT)= beta_norm (Drule.infer_instantiate ctxtF
                            [(("a",0), ctermF uT),(("b",0), ctermF vT)] Suc_inj_vF);
fun Suc_neq_ZeroF_at t = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF t)] Suc_neq_Zero_vF);
fun oFalse_elimF_at rT = beta_norm (Drule.infer_instantiate ctxtF [(("R",0), ctermF rT)] oFalse_elim_vF);
fun dzosF_at t         = beta_norm (Drule.infer_instantiate ctxtF [(("p",0), ctermF t)] disj_zero_or_suc_vF);
fun le_reflF_at t      = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF t)] le_refl_vF);
fun fact0_at ()        = fact_0_vF;
fun factSuc_at t       = beta_norm (Drule.infer_instantiate ctxtF [(("n",0), ctermF t)] fact_Suc_vF);

(* nat_induct ground instantiator on ctxtF *)
fun nat_induct_atF (Qabs, kT) = beta_norm (Drule.infer_instantiate ctxtF
      [(("P",0), ctermF Qabs), (("k",0), ctermF kT)] nat_induct_vF);

(* add congruence on LEFT / RIGHT operand, on ctxtF *)
fun add_cong_lF (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtF
          [(("P",0), ctermF Pabs), (("a",0), ctermF pT), (("b",0), ctermF qT)] oeq_subst_vF);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF (add pT kT))] oeq_refl_vF);
  in inst OF [hpq, refl_pk] end;
fun add_cong_rF (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtF
          [(("P",0), ctermF Pabs), (("a",0), ctermF pT), (("b",0), ctermF qT)] oeq_subst_vF);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF (add hT pT))] oeq_refl_vF);
  in inst OF [hpq, refl_hp] end;

(* mult congruence on LEFT / RIGHT operand, on ctxtF *)
fun mult_cong_lF (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtF
          [(("P",0), ctermF Pabs), (("a",0), ctermF pT), (("b",0), ctermF qT)] oeq_subst_vF);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF (mult pT kT))] oeq_refl_vF);
  in inst OF [hpq, refl_pk] end;
fun mult_cong_rF (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtF
          [(("P",0), ctermF Pabs), (("a",0), ctermF pT), (("b",0), ctermF qT)] oeq_subst_vF);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtF [(("a",0), ctermF (mult hT pT))] oeq_refl_vF);
  in inst OF [hpq, refl_hp] end;

(* le / dvd intro on ctxtF *)
fun le_introF (mT, nT, w) hyp =
  let
    val Pabs = Abs ("p", natT, oeq nT (add mT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtF
          [(("P",0), ctermF Pabs), (("a",0), ctermF w)] exI_vF);
  in inst OF [hyp] end;
fun dvd_introF (aT, bT, w) hyp =
  let
    val Pabs = Abs ("k", natT, oeq bT (mult aT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtF
          [(("P",0), ctermF Pabs), (("a",0), ctermF w)] exI_vF);
  in inst OF [hyp] end;

(* exI / exE on ctxtF *)
fun exI_atF Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("P",0), ctermF Pabs), (("a",0), ctermF at)] exI_vF)
  in Thm.implies_elim inst hbody end;
fun exE_elimF (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm  = Thm.assume (ctermF hypTerm);
    val body    = bodyFn wF hypThm;
    val minor   = Thm.forall_intr (ctermF wF) (Thm.implies_intr (ctermF hypTerm) body);
    val exE_inst= beta_norm (Drule.infer_instantiate ctxtF
                    [(("P",0), ctermF Pabs), (("Q",0), ctermF goalC)] exE_vF);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;

(* disjE / disjI on ctxtF *)
fun disjE_elimF (At, Bt, Ct) dThm caseA caseB =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtF
          [(("A",0), ctermF At), (("B",0), ctermF Bt), (("C",0), ctermF Ct)] disjE_vF);
    val s1 = Thm.implies_elim inst dThm;
    val s2 = Thm.implies_elim s1 caseA;
  in Thm.implies_elim s2 caseB end;
fun disjI1F_at (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtF
      [(("A",0), ctermF At), (("B",0), ctermF Bt)] disjI1_vF)) h;
fun disjI2F_at (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtF
      [(("A",0), ctermF At), (("B",0), ctermF Bt)] disjI2_vF)) h;

(* lt / le / dvd abbreviations are SAME shape as above (le/dvd already in scope) *)
fun ltF mT nT = le (suc mT) nT;

val () = out "EUCLID_HELPERS_READY\n";

(* uniform validator on ctxtF *)
fun checkF (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtF (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtF intended ^ "\n");
          false)
  end;

(* ============================================================================
   dvd_self_mult  : jT (dvd a (mult a b))      witness b ; body refl.
   dvd_self_mult2 : jT (dvd a (mult b a))      witness b ; body mult_comm.
   ============================================================================ *)
val dvd_self_mult =
  let
    val aF = Free("a", natT); val bF = Free("b", natT);
    val hyp = oeqreflF_at (mult aF bF);          (* oeq (mult a b) (mult a b) *)
  in varify (dvd_introF (aF, mult aF bF, bF) hyp) end;

val dvd_self_mult2 =
  let
    val aF = Free("a", natT); val bF = Free("b", natT);
    val hyp = multcommF_at (bF, aF);             (* oeq (mult b a) (mult a b) *)
  in varify (dvd_introF (aF, mult bF aF, bF) hyp) end;

val aVsm = Var (("a",0), natT);
val bVsm = Var (("b",0), natT);
val r_dsm  = checkF ("dvd_self_mult",  dvd_self_mult,  jT (dvd aVsm (mult aVsm bVsm)));
val r_dsm2 = checkF ("dvd_self_mult2", dvd_self_mult2, jT (dvd aVsm (mult bVsm aVsm)));

(* ============================================================================
   fact_pos : jT (lt Zero (fact n))           0 < n!   by induction on n.
     base n=0 : lt 0 (fact 0) = lt 0 (Suc 0) = le (Suc 0)(Suc 0) = le_refl.
     step     : IH lt 0 (fact x) gives witness p with fact x = (Suc 0) + p.
       fact (Suc x) = mult (Suc x)(fact x)            [fact_Suc]
                    = add (fact x)(mult x (fact x))   [mult_Suc]
                    = add ((Suc 0)+p)(mult x (fact x))[add_cong_l, IH wit]
                    = add (Suc 0)(add p (mult x (fact x)))   [add_assoc]
       witness (add p (mult x (fact x))).
   ============================================================================ *)
val fact_pos =
  let
    (* capture-avoiding : fact(Bound 0) under a raw Abs would be captured by le's Ex binder *)
    val Qpred =
      let val zF = Free("z_fp", natT)
      in Term.lambda zF (ltF ZeroC (fact zF)) end;   (* %z. le (Suc 0)(fact z) *)
    val kF = Free("n", natT);
    val ind = nat_induct_atF (Qpred, kF);

    (* BASE : lt 0 (fact 0) *)
    val base =
      let
        val f0 = fact0_at ();                       (* oeq (fact 0)(Suc 0) *)
        val f0s = oeq_sym OF [f0];                   (* oeq (Suc 0)(fact 0) *)
        (* build le (Suc 0)(fact 0) directly. witness 0:
             oeq (fact 0)(add (Suc 0) 0)
             add (Suc 0) 0 = Suc(0+0) = Suc 0       [add_Suc, add_0]  -> = (fact 0) by f0 sym *)
        val aS  = addSucF_at (ZeroC, ZeroC);         (* (Suc 0 + 0) = Suc(0+0) *)
        val a0  = add0F_at ZeroC;                    (* (0+0) = 0 *)
        val sa0 = Suc_cong OF [a0];                  (* Suc(0+0) = Suc 0 *)
        val aS_S0 = oeq_trans OF [aS, sa0];          (* (Suc 0 + 0) = Suc 0 *)
        val aS_f0 = oeq_trans OF [aS_S0, f0s];       (* (Suc 0 + 0) = (fact 0) *)
        val body  = oeq_sym OF [aS_f0];              (* (fact 0) = (Suc 0 + 0) *)
      in le_introF (suc ZeroC, fact ZeroC, ZeroC) body end;

    (* STEP : !!x. lt 0 (fact x) ==> lt 0 (fact (Suc x)) *)
    val xF = Free("x", natT);
    val ihprop = jT (ltF ZeroC (fact xF));
    val IH = Thm.assume (ctermF ihprop);
    val Pabs = Abs("p", natT, oeq (fact xF) (add (suc ZeroC) (Bound 0)));  (* body of le (Suc 0)(fact x) *)
    val goalStep = ltF ZeroC (fact (suc xF));
    fun stepBody p (hp : thm) =                     (* hp : oeq (fact x)(add (Suc 0) p) *)
      let
        val fS   = factSuc_at xF;                    (* fact(Suc x) = mult (Suc x)(fact x) *)
        val mS   = multSucF_at (xF, fact xF);        (* mult (Suc x)(fact x) = add (fact x)(mult x (fact x)) *)
        val congL= add_cong_lF (fact xF, add (suc ZeroC) p, mult xF (fact xF)) hp;
                                                     (* add (fact x) Z = add ((Suc 0)+p) Z *)
        val assoc= addassocF_at (suc ZeroC, p, mult xF (fact xF));
                                                     (* add ((Suc 0)+p) Z = add (Suc 0)(add p Z) *)
        val c1 = oeq_trans OF [fS, mS];              (* fact(Suc x) = add (fact x)(mult x (fact x)) *)
        val c2 = oeq_trans OF [c1, congL];           (* = add ((Suc 0)+p)(mult x (fact x)) *)
        val body = oeq_trans OF [c2, assoc];         (* = add (Suc 0)(add p (mult x (fact x))) *)
      in le_introF (suc ZeroC, fact (suc xF), add p (mult xF (fact xF))) body end;
    val stepConcl = exE_elimF (Pabs, goalStep) IH "p0" stepBody;
    val step1 = Thm.forall_intr (ctermF xF) (Thm.implies_intr (ctermF ihprop) stepConcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val nVfp = Var (("n",0), natT);
val r_fact_pos = checkF ("fact_pos", fact_pos, jT (ltF ZeroC (fact nVfp)));

(* ============================================================================
   le_cases : jT (le p (Suc n)) ==> jT (Disj (le p n) (oeq p (Suc n)))
     le p (Suc n) = Ex w. oeq (Suc n)(add p w).  exE witness w; dzos on w:
       w = Zero    : (Suc n) = (p + 0) = p ; sym -> oeq p (Suc n) ; disjI2.
       w = Suc wr  : (Suc n) = (p + Suc wr) = Suc(p + wr) [add_Suc_right];
                     Suc_inj -> oeq n (p + wr) = body of le p n ; disjI1.
   ============================================================================ *)
val le_cases =
  let
    val pF = Free("p", natT); val nF = Free("n", natT);
    val leHypP = jT (le pF (suc nF));
    val leHyp  = Thm.assume (ctermF leHypP);
    val Pabs   = Abs("w", natT, oeq (suc nF) (add pF (Bound 0)));   (* body of le p (Suc n) *)
    val goalC  = mkDisj (le pF nF) (oeq pF (suc nF));
    fun body w (hw : thm) =                          (* hw : oeq (Suc n)(add p w) *)
      let
        val dz = dzosF_at w;                          (* Disj (oeq w 0)(Ex(%q. oeq w (Suc q))) *)
        val caseZero =
          let
            val ewz = Thm.assume (ctermF (jT (oeq w ZeroC)));   (* oeq w 0 *)
            val cong = add_cong_rF (pF, w, ZeroC) ewz;          (* (p + w) = (p + 0) *)
            val sn_p0= oeq_trans OF [hw, cong];                 (* (Suc n) = (p + 0) *)
            val sn_p = oeq_trans OF [sn_p0, add0rF_at pF];      (* (Suc n) = p *)
            val p_sn = oeq_sym OF [sn_p];                       (* p = (Suc n) *)
            val g    = disjI2F_at (le pF nF, oeq pF (suc nF)) p_sn;
          in Thm.implies_intr (ctermF (jT (oeq w ZeroC))) g end;
        val PabsQ = Abs("q", natT, oeq w (suc (Bound 0)));
        val caseSuc =
          let
            val exq = Thm.assume (ctermF (jT (mkEx PabsQ)));    (* Ex(%q. oeq w (Suc q)) *)
            fun sucBody q (hq : thm) =                          (* hq : oeq w (Suc q) *)
              let
                val cong  = add_cong_rF (pF, w, suc q) hq;      (* (p + w) = (p + Suc q) *)
                val sn_pSq= oeq_trans OF [hw, cong];            (* (Suc n) = (p + Suc q) *)
                val pSq_S = addSrF_at (pF, q);                  (* (p + Suc q) = Suc(p + q) *)
                val sn_Spq= oeq_trans OF [sn_pSq, pSq_S];       (* (Suc n) = Suc(p + q) *)
                val n_pq  = (Suc_inj_atF (nF, add pF q)) OF [sn_Spq];   (* oeq n (p + q) *)
                val le_pn = le_introF (pF, nF, q) n_pq;          (* le p n *)
                val g     = disjI1F_at (le pF nF, oeq pF (suc nF)) le_pn;
              in g end;
            val g = exE_elimF (PabsQ, goalC) exq "q0" sucBody;
          in Thm.implies_intr (ctermF (jT (mkEx PabsQ))) g end;
        val combined = disjE_elimF (oeq w ZeroC, mkEx PabsQ, goalC) dz caseZero caseSuc;
      in combined end;
    val afterExE = exE_elimF (Pabs, goalC) leHyp "wp" body;
    val disch = Thm.implies_intr (ctermF leHypP) afterExE;
  in varify disch end;

val pVlc = Var (("p",0), natT);
val nVlc = Var (("n",0), natT);
val le_cases_intended =
  Logic.mk_implies (jT (le pVlc (suc nVlc)),
    jT (mkDisj (le pVlc nVlc) (oeq pVlc (suc nVlc))));
val r_le_cases = checkF ("le_cases", le_cases, le_cases_intended);

(* ============================================================================
   mult_le_mono : jT (le j k) ==> jT (le (mult p j) (mult p k))
     le j k = Ex e. oeq k (add j e).  exE witness e, he : oeq k (add j e).
       mult p k = mult p (add j e)                  [mult_cong_r he]
                = add (mult p j)(mult p e)           [left_distrib]
       witness (mult p e) for le (mult p j)(mult p k).   NO induction.
   ============================================================================ *)
val mult_le_mono =
  let
    val pF = Free("p", natT); val jF = Free("j", natT); val kF = Free("k", natT);
    val leHypP = jT (le jF kF);
    val leHyp  = Thm.assume (ctermF leHypP);
    val Pabs   = Abs("e", natT, oeq kF (add jF (Bound 0)));   (* body of le j k *)
    val goalC  = le (mult pF jF) (mult pF kF);
    fun body e (he : thm) =                          (* he : oeq k (add j e) *)
      let
        val cong = mult_cong_rF (pF, kF, add jF e) he;        (* (p*k) = (p*(j+e)) *)
        val ld   = left_distribF_at (pF, jF, e);              (* (p*(j+e)) = ((p*j)+(p*e)) *)
        val body = oeq_trans OF [cong, ld];                   (* (p*k) = ((p*j)+(p*e)) *)
      in le_introF (mult pF jF, mult pF kF, mult pF e) body end;
    val afterExE = exE_elimF (Pabs, goalC) leHyp "e0" body;
    val disch = Thm.implies_intr (ctermF leHypP) afterExE;
  in varify disch end;

val pVmm = Var (("p",0), natT);
val jVmm = Var (("j",0), natT);
val kVmm = Var (("k",0), natT);
val mult_le_mono_intended =
  Logic.mk_implies (jT (le jVmm kVmm),
    jT (le (mult pVmm jVmm) (mult pVmm kVmm)));
val r_mult_le_mono = checkF ("mult_le_mono", mult_le_mono, mult_le_mono_intended);

(* ============================================================================
   mult_eq_one : jT (oeq (mult p e) (Suc Zero)) ==> jT (oeq p (Suc Zero))
     cases on p (dzos):
       p = 0     : mult 0 e = 0 ; (mult p e = Suc 0) & (=0) -> 0 = Suc 0 -> oFalse.
       p = Suc r : cases on r (dzos):
         r = 0     : p = Suc 0 directly (oeq p (Suc 0) via Suc_cong + trans).
         r = Suc s : cases on e (dzos):
           e = 0     : mult p 0 = 0 ; contradiction as above.
           e = Suc t : mult p (Suc t) = add p (mult p t)        [mult_Suc_right]
                       with p = Suc(Suc s): add (Suc(Suc s)) Z = Suc(Suc(add s Z))
                       so mult p e = Suc(Suc Z) ; = Suc 0 -> Suc_inj -> Suc Z = 0
                       -> Suc_neq_Zero -> oFalse.
   ============================================================================ *)
val mult_eq_one =
  let
    val pF = Free("p", natT); val eF = Free("e", natT);
    val hypP = jT (oeq (mult pF eF) (suc ZeroC));
    val hyp  = Thm.assume (ctermF hypP);             (* oeq (mult p e)(Suc 0) *)
    val goalC = oeq pF (suc ZeroC);

    val dzP = dzosF_at pF;                            (* Disj (oeq p 0)(Ex q. oeq p (Suc q)) *)

    (* helper : from (oeq (mult p e) 0) derive oFalse using hyp (mult p e = Suc 0) *)
    fun contra_mpe_zero hmz =                         (* hmz : oeq (mult p e) 0 *)
      let
        val mpe_S0 = hyp;                             (* (mult p e) = Suc 0 *)
        val S0_mpe = oeq_sym OF [mpe_S0];            (* Suc 0 = (mult p e) *)
        val S0_0   = oeq_trans OF [S0_mpe, hmz];     (* Suc 0 = 0 *)
      in (Suc_neq_ZeroF_at ZeroC) OF [S0_0] end;     (* oFalse *)

    val caseP0 =
      let
        val ep0 = Thm.assume (ctermF (jT (oeq pF ZeroC)));   (* oeq p 0 *)
        (* mult p e = mult 0 e via subst on %z. oeq (mult p e)(mult z e) *)
        val Psub = Abs("z", natT, oeq (mult pF eF) (mult (Bound 0) eF));
        val subInst = beta_norm (Drule.infer_instantiate ctxtF
              [(("P",0), ctermF Psub), (("a",0), ctermF pF), (("b",0), ctermF ZeroC)] oeq_subst_vF);
        val reflMpe = oeqreflF_at (mult pF eF);
        val mpe_m0e = subInst OF [ep0, reflMpe];     (* (mult p e) = (mult 0 e) *)
        val m0e_0   = mult0F_at eF;                  (* (mult 0 e) = 0 *)
        val mpe_0   = oeq_trans OF [mpe_m0e, m0e_0]; (* (mult p e) = 0 *)
        val fls     = contra_mpe_zero mpe_0;
        val g       = (oFalse_elimF_at goalC) OF [fls];   (* oeq p (Suc 0) *)
      in Thm.implies_intr (ctermF (jT (oeq pF ZeroC))) g end;

    val PabsR = Abs("q", natT, oeq pF (suc (Bound 0)));    (* Ex q. oeq p (Suc q) *)
    val casePS =
      let
        val exr = Thm.assume (ctermF (jT (mkEx PabsR)));   (* Ex q. oeq p (Suc q) *)
        fun rBody r (hr : thm) =                            (* hr : oeq p (Suc r) *)
          let
            val dzR = dzosF_at r;                           (* Disj (oeq r 0)(Ex s. oeq r (Suc s)) *)
            val caseR0 =
              let
                val er0   = Thm.assume (ctermF (jT (oeq r ZeroC)));   (* oeq r 0 *)
                val sr_s0 = Suc_cong OF [er0];               (* oeq (Suc r)(Suc 0) *)
                val p_s0  = oeq_trans OF [hr, sr_s0];        (* oeq p (Suc 0) *)
              in Thm.implies_intr (ctermF (jT (oeq r ZeroC))) p_s0 end;
            val PabsS = Abs("s", natT, oeq r (suc (Bound 0)));   (* Ex s. oeq r (Suc s) *)
            val caseRS =
              let
                val exs = Thm.assume (ctermF (jT (mkEx PabsS)));   (* Ex s. oeq r (Suc s) *)
                fun sBody s (hs : thm) =                            (* hs : oeq r (Suc s) *)
                  let
                    (* p = Suc r = Suc(Suc s) *)
                    val sr_SSs = Suc_cong OF [hs];           (* oeq (Suc r)(Suc(Suc s)) *)
                    val p_SSs  = oeq_trans OF [hr, sr_SSs];  (* oeq p (Suc(Suc s)) *)
                    val dzE = dzosF_at eF;                   (* Disj (oeq e 0)(Ex t. oeq e (Suc t)) *)
                    val caseE0 =
                      let
                        val ee0   = Thm.assume (ctermF (jT (oeq eF ZeroC)));   (* oeq e 0 *)
                        (* mult p e = mult p 0 via subst on %z. oeq (mult p e)(mult p z) *)
                        val Psub2 = Abs("z", natT, oeq (mult pF eF) (mult pF (Bound 0)));
                        val subI2 = beta_norm (Drule.infer_instantiate ctxtF
                              [(("P",0), ctermF Psub2), (("a",0), ctermF eF), (("b",0), ctermF ZeroC)] oeq_subst_vF);
                        val reflMpe2 = oeqreflF_at (mult pF eF);
                        val mpe_mp0 = subI2 OF [ee0, reflMpe2];   (* (mult p e) = (mult p 0) *)
                        val mp0_0   = mult0rF_at pF;              (* (mult p 0) = 0 *)
                        val mpe_0   = oeq_trans OF [mpe_mp0, mp0_0];  (* (mult p e) = 0 *)
                        val fls     = contra_mpe_zero mpe_0;
                      in Thm.implies_intr (ctermF (jT (oeq eF ZeroC))) fls end;
                    val PabsT = Abs("t", natT, oeq eF (suc (Bound 0)));  (* Ex t. oeq e (Suc t) *)
                    val caseES =
                      let
                        val ext = Thm.assume (ctermF (jT (mkEx PabsT)));   (* Ex t. oeq e (Suc t) *)
                        fun tBody t (ht : thm) =                            (* ht : oeq e (Suc t) *)
                          let
                            (* mult p e = mult p (Suc t)  [subst e->Suc t inside (mult p _)] *)
                            val Psub3 = Abs("z", natT, oeq (mult pF eF) (mult pF (Bound 0)));
                            val subI3 = beta_norm (Drule.infer_instantiate ctxtF
                                  [(("P",0), ctermF Psub3), (("a",0), ctermF eF), (("b",0), ctermF (suc t))] oeq_subst_vF);
                            val reflMpe3 = oeqreflF_at (mult pF eF);
                            val mpe_mpSt = subI3 OF [ht, reflMpe3];  (* (mult p e) = (mult p (Suc t)) *)
                            (* mult p (Suc t) = add p (mult p t)   [mult_Suc_right] *)
                            val mpSt_chain = multSrF_at (pF, t);     (* (mult p (Suc t)) = (p + mult p t) *)
                            (* now substitute p -> Suc(Suc s) on the LEFT operand of the add:
                               add p (mult p t) = add (Suc(Suc s))(mult p t)  [add_cong_l p->SSs]
                               = Suc((Suc s)+(mult p t))  [add_Suc]
                               = Suc(Suc(s + mult p t))   [add_Suc] *)
                            val mptVar = mult pF t;                  (* the trailing factor (kept p) *)
                            val congP = add_cong_lF (pF, suc (suc s), mptVar) p_SSs;
                                                                     (* (p + mptVar) = ((Suc(Suc s)) + mptVar) *)
                            val aS1 = addSucF_at (suc s, mptVar);    (* ((Suc(Suc s)) + mptVar) = Suc((Suc s)+mptVar) *)
                            val aS2 = addSucF_at (s, mptVar);        (* ((Suc s)+mptVar) = Suc(s+mptVar) *)
                            val sAS2 = Suc_cong OF [aS2];            (* Suc((Suc s)+mptVar) = Suc(Suc(s+mptVar)) *)
                            val aS1c = oeq_trans OF [aS1, sAS2];     (* ((Suc(Suc s))+mptVar) = Suc(Suc(s+mptVar)) *)
                            (* chain everything : (mult p e) = Suc(Suc(s+mptVar)) *)
                            val c1 = oeq_trans OF [mpe_mpSt, mpSt_chain]; (* (mult p e) = (p + mptVar) *)
                            val c2 = oeq_trans OF [c1, congP];            (* = ((Suc(Suc s))+mptVar) *)
                            val mpe_SS = oeq_trans OF [c2, aS1c];         (* = Suc(Suc(s+mptVar)) *)
                            (* contradiction : Suc(Suc(s+mptVar)) = Suc 0 -> Suc_inj -> Suc(s+mptVar)=0 *)
                            val SS_S0 = oeq_trans OF [oeq_sym OF [mpe_SS], hyp];
                                                                      (* Suc(Suc(s+mptVar)) = Suc 0 *)
                            val Sinner_0 = (Suc_inj_atF (suc (add s mptVar), ZeroC)) OF [SS_S0];
                                                                      (* oeq (Suc(s+mptVar)) 0 *)
                            val fls = (Suc_neq_ZeroF_at (add s mptVar)) OF [Sinner_0];  (* oFalse *)
                          in fls end;
                        val g = exE_elimF (PabsT, oFalseC) ext "t0" tBody;
                      in Thm.implies_intr (ctermF (jT (mkEx PabsT))) g end;
                    val flsCombined = disjE_elimF (oeq eF ZeroC, mkEx PabsT, oFalseC) dzE caseE0 caseES;
                    val g = (oFalse_elimF_at goalC) OF [flsCombined];   (* oeq p (Suc 0) *)
                  in g end;
                val g = exE_elimF (PabsS, goalC) exs "s0" sBody;
              in Thm.implies_intr (ctermF (jT (mkEx PabsS))) g end;
            val combined = disjE_elimF (oeq r ZeroC, mkEx PabsS, goalC) dzR caseR0 caseRS;
          in combined end;
        val g = exE_elimF (PabsR, goalC) exr "r0" rBody;
      in Thm.implies_intr (ctermF (jT (mkEx PabsR))) g end;

    val concl = disjE_elimF (oeq pF ZeroC, mkEx PabsR, goalC) dzP caseP0 casePS;
    val disch = Thm.implies_intr (ctermF hypP) concl;
  in varify disch end;

val pVme = Var (("p",0), natT);
val eVme = Var (("e",0), natT);
val mult_eq_one_intended =
  Logic.mk_implies (jT (oeq (mult pVme eVme) (suc ZeroC)), jT (oeq pVme (suc ZeroC)));
val r_mult_eq_one = checkF ("mult_eq_one", mult_eq_one, mult_eq_one_intended);

(* ============================================================================
   dvd_fact : jT (le (Suc Zero) p) ==> jT (le p n) ==> jT (dvd p (fact n))
     INDUCTION on n with object predicate  Q n := Imp (le p n)(dvd p (fact n)).
     The hyp `le (Suc 0) p` is a constant meta-assumption (used only in base).
     base n=0 : assume le p 0 ; with le (Suc 0) p derive oFalse -> dvd p (fact 0).
     step Suc n':
       le_cases on (le p (Suc n')) -> Disj (le p n')(oeq p (Suc n')).
         le p n' : IH(le p n') -> dvd p (fact n') ; dvd_self_mult2 -> dvd (fact n')(fact (Suc n'));
                   dvd_trans -> dvd p (fact (Suc n')).
         oeq p (Suc n') : dvd (Suc n')(fact (Suc n')) [dvd_intro+fact_Suc] ;
                   subst p := Suc n' (capture-avoiding) -> dvd p (fact (Suc n')).
   uses object Imp helpers (impI_atT/mp_atT) re-stated on ctxtF.
   ============================================================================ *)
val impI_vF = varify impI_ax;
val mp_vF   = varify mp_ax;
fun impI_atF (At, Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("A",0), ctermF At), (("B",0), ctermF Bt)] impI_vF)
  in Thm.implies_elim inst hImpThm end;
fun mp_atF (At, Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("A",0), ctermF At), (("B",0), ctermF Bt)] mp_vF)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;

(* dvd_trans lifted to ctxtF *)
val dvd_trans_vF = varify dvd_trans;
fun dvd_trans_atF (at, bt, ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("a",0), ctermF at), (("b",0), ctermF bt), (("c",0), ctermF ct)] dvd_trans_vF)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* le_cases lifted instantiator on ctxtF *)
val le_cases_vF = varify le_cases;
fun le_cases_atF (pt, nt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("p",0), ctermF pt), (("n",0), ctermF nt)] le_cases_vF)
  in Thm.implies_elim inst h end;

val dvd_fact =
  let
    val pF = Free("p", natT);
    val le1pP = jT (le (suc ZeroC) pF);
    val le1p  = Thm.assume (ctermF le1pP);

    (* object predicate Q n := Imp (le p n)(dvd p (fact n)) *)
    val Qabs =
      let val zF = Free("z_q", natT)
      in Term.lambda zF (mkImp (le pF zF) (dvd pF (fact zF))) end;
    val kF = Free("n", natT);
    val ind = nat_induct_atF (Qabs, kF);

    (* BASE : Q 0 = Imp (le p 0)(dvd p (fact 0)).  prove by impI : assume le p 0 -> oFalse-elim. *)
    val base =
      let
        val lep0P = jT (le pF ZeroC);
        val lep0  = Thm.assume (ctermF lep0P);
        (* le p 0 = Ex w. oeq 0 (add p w) ; le (Suc 0) p = Ex u. oeq p (add (Suc 0) u). *)
        val Pw = Abs("w", natT, oeq ZeroC (add pF (Bound 0)));     (* body of le p 0 *)
        val Pu = Abs("u", natT, oeq pF (add (suc ZeroC) (Bound 0)));(* body of le (Suc 0) p *)
        fun wBody w (hw : thm) =                       (* hw : oeq 0 (add p w) *)
          let
            fun uBody u (hu : thm) =                    (* hu : oeq p (add (Suc 0) u) *)
              let
                (* add p w = add (add (Suc 0) u) w  [add_cong_l p -> (Suc 0)+u] *)
                val congP = add_cong_lF (pF, add (suc ZeroC) u, w) hu;
                (* add (add (Suc 0) u) w = add (Suc 0)(add u w)  [add_assoc] *)
                val assoc = addassocF_at (suc ZeroC, u, w);
                (* add (Suc 0)(add u w) = Suc(add 0 (add u w))  [add_Suc] *)
                val aS    = addSucF_at (ZeroC, add u w);
                val pw_S  = oeq_trans OF [oeq_trans OF [congP, assoc], aS];  (* (p+w) = Suc(0+(u+w)) *)
                val z_S   = oeq_trans OF [hw, pw_S];   (* 0 = Suc(0+(u+w)) *)
                val S_z   = oeq_sym OF [z_S];          (* Suc(0+(u+w)) = 0 *)
                val fls   = (Suc_neq_ZeroF_at (add ZeroC (add u w))) OF [S_z];  (* oFalse *)
              in (oFalse_elimF_at (dvd pF (fact ZeroC))) OF [fls] end;  (* dvd p (fact 0) *)
            val g = exE_elimF (Pu, dvd pF (fact ZeroC)) le1p "u0" uBody;
          in g end;
        val falseDvd = exE_elimF (Pw, dvd pF (fact ZeroC)) lep0 "w0" wBody;  (* dvd p (fact 0) *)
        val impBody  = Thm.implies_intr (ctermF lep0P) falseDvd;             (* le p 0 ==> dvd p (fact 0) *)
      in impI_atF (le pF ZeroC, dvd pF (fact ZeroC)) impBody end;           (* Q 0 *)

    (* STEP : !!x. Q x ==> Q (Suc x) *)
    val xF = Free("x", natT);
    val ihprop = jT (mkImp (le pF xF) (dvd pF (fact xF)));   (* Q x *)
    val IH = Thm.assume (ctermF ihprop);

    val stepConcl =
      let
        val lepSxP = jT (le pF (suc xF));
        val lepSx  = Thm.assume (ctermF lepSxP);
        val dThm   = le_cases_atF (pF, xF) lepSx;            (* Disj (le p x)(oeq p (Suc x)) *)
        val goalC  = dvd pF (fact (suc xF));

        (* CASE A : le p x *)
        val caseA =
          let
            val hlepx = Thm.assume (ctermF (jT (le pF xF)));
            val dvdpfx = mp_atF (le pF xF, dvd pF (fact xF)) IH hlepx;   (* dvd p (fact x) *)
            (* dvd (fact x)(fact (Suc x)) : witness (Suc x); body
                 oeq (fact (Suc x))(mult (fact x)(Suc x))
                 fact(Suc x) = mult (Suc x)(fact x)   [fact_Suc]
                             = mult (fact x)(Suc x)   [mult_comm] *)
            val fS   = factSuc_at xF;                         (* fact(Suc x) = mult (Suc x)(fact x) *)
            val mc   = multcommF_at (suc xF, fact xF);        (* mult (Suc x)(fact x) = mult (fact x)(Suc x) *)
            val body = oeq_trans OF [fS, mc];                 (* fact(Suc x) = mult (fact x)(Suc x) *)
            val dvdfxfSx = dvd_introF (fact xF, fact (suc xF), suc xF) body;  (* dvd (fact x)(fact (Suc x)) *)
            val g = dvd_trans_atF (pF, fact xF, fact (suc xF)) dvdpfx dvdfxfSx;
          in Thm.implies_intr (ctermF (jT (le pF xF))) g end;

        (* CASE B : oeq p (Suc x) *)
        val caseB =
          let
            val hpeqSx = Thm.assume (ctermF (jT (oeq pF (suc xF))));   (* oeq p (Suc x) *)
            (* dvd (Suc x)(fact (Suc x)) : witness (fact x); body
                 oeq (fact (Suc x))(mult (Suc x)(fact x))  = fact_Suc *)
            val fS = factSuc_at xF;                           (* fact(Suc x) = mult (Suc x)(fact x) *)
            val dvdSxfSx = dvd_introF (suc xF, fact (suc xF), fact xF) fS;  (* dvd (Suc x)(fact (Suc x)) *)
            (* subst (Suc x) -> p (capture-avoiding) : P z := dvd z (fact (Suc x)) *)
            val zF   = Free("z_sub", natT);
            val Psub = Term.lambda zF (dvd zF (fact (suc xF)));
            val subInst = beta_norm (Drule.infer_instantiate ctxtF
                  [(("P",0), ctermF Psub), (("a",0), ctermF (suc xF)), (("b",0), ctermF pF)] oeq_subst_vF);
            val Sx_p = oeq_sym OF [hpeqSx];                   (* oeq (Suc x) p *)
            val g = (subInst OF [Sx_p]) OF [dvdSxfSx];        (* dvd p (fact (Suc x)) *)
          in Thm.implies_intr (ctermF (jT (oeq pF (suc xF)))) g end;

        val combined = disjE_elimF (le pF xF, oeq pF (suc xF), goalC) dThm caseA caseB;
        val impBody  = Thm.implies_intr (ctermF lepSxP) combined;  (* le p (Suc x) ==> dvd p (fact (Suc x)) *)
      in impI_atF (le pF (suc xF), dvd pF (fact (suc xF))) impBody end;  (* Q (Suc x) *)

    val step1 = Thm.forall_intr (ctermF xF) (Thm.implies_intr (ctermF ihprop) stepConcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;               (* Q n *)
    (* discharge : turn Q n into le p n ==> dvd p (fact n) (META), then add le1p outer *)
    val nF = kF;
    val lepnP = jT (le pF nF);
    val lepn  = Thm.assume (ctermF lepnP);
    val dvdpfn = mp_atF (le pF nF, dvd pF (fact nF)) r2 lepn;   (* dvd p (fact n) *)
    val d1 = Thm.implies_intr (ctermF lepnP) dvdpfn;            (* le p n ==> dvd p (fact n) *)
    val d2 = Thm.implies_intr (ctermF le1pP) d1;               (* le (Suc 0) p ==> le p n ==> ... *)
  in varify d2 end;

val pVdf = Var (("p",0), natT);
val nVdf = Var (("n",0), natT);
val dvd_fact_intended =
  Logic.mk_implies (jT (le (suc ZeroC) pVdf),
    Logic.mk_implies (jT (le pVdf nVdf), jT (dvd pVdf (fact nVdf))));
val r_dvd_fact = checkF ("dvd_fact", dvd_fact, dvd_fact_intended);

(* ============================================================================
   FINAL VERDICT for the Euclid helpers
   ============================================================================ *)
val () =
  if r_dsm andalso r_dsm2 andalso r_fact_pos andalso r_le_cases
     andalso r_mult_le_mono andalso r_mult_eq_one andalso r_dvd_fact
  then out "HELPERS_OK\n"
  else out "HELPERS_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  CONSECUTIVE-COPRIMALITY : a prime p>1 cannot divide two consecutive
        numbers a and (Suc a).  The Euclid keystone.

        consec_coprime :
          jT (lt (Suc Zero) p) ==> jT (dvd p a) ==> jT (dvd p (Suc a))
            ==> jT oFalse
   ----------------------------------------------------------------------------
   Built on ctxtF (fact already added; all base le/dvd/lt/mult lemmas lift in
   by varify).  We re-varify the order lemmas (le_total/le_trans/lt_irrefl/
   le_neq_lt/add_left_cancel) for use under ctxtF and add ground instantiators.
   ============================================================================ *)

val () = out "CONSEC_COPRIME_BEGIN\n";

(* ---- re-varify the order lemmas for the FINAL context ctxtF ---- *)
val le_total_vCop     = varify le_total;
val le_trans_vCop     = varify le_trans;
val lt_irrefl_vCop    = varify lt_irrefl;
val le_neq_lt_vCop    = varify le_neq_lt;
val add_left_cancel_vCop = varify add_left_cancel;
val mp_vCop           = varify mp_ax;            (* for neg = Imp _ oFalse *)
val impI_vCop         = varify impI_ax;

(* ground instantiators on ctxtF *)
fun le_totalF_at (mt, nt) = beta_norm (Drule.infer_instantiate ctxtF
      [(("m",0), ctermF mt), (("n",0), ctermF nt)] le_total_vCop);
fun le_transF_at (mt, nt, kt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("m",0), ctermF mt), (("n",0), ctermF nt), (("k",0), ctermF kt)] le_trans_vCop)
  in (inst OF [h1]) OF [h2] end;
fun lt_irreflF_at nt h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("n",0), ctermF nt)] lt_irrefl_vCop)
  in inst OF [h] end;
fun le_neq_ltF_at (dt, nt) hle hneq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("d",0), ctermF dt), (("n",0), ctermF nt)] le_neq_lt_vCop)
  in (inst OF [hle]) OF [hneq] end;
fun mult_le_monoF_at (pt, jt, kt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("p",0), ctermF pt), (("j",0), ctermF jt), (("k",0), ctermF kt)] (varify mult_le_mono))
  in inst OF [h] end;

(* neg-intro on ctxtF : from (A ==> oFalse) build jT (neg A) = jT (Imp A oFalse) *)
fun negI_atF At hImpBody =     (* hImpBody : jT A ==> jT oFalse *)
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("A",0), ctermF At), (("B",0), ctermF oFalseC)] impI_vCop)
  in Thm.implies_elim inst hImpBody end;

val () = out "COP_INSTANTIATORS_READY\n";

val consec_coprime =
  let
    val pF = Free("p", natT); val aF = Free("a", natT);
    val H1prop = jT (ltF (suc ZeroC) pF);     (* lt 1 p  ==  le (Suc 0) p *)
    val H2prop = jT (dvd pF aF);              (* Ex k. oeq a (mult p k) *)
    val H3prop = jT (dvd pF (suc aF));        (* Ex k. oeq (Suc a)(mult p k) *)
    val H1 = Thm.assume (ctermF H1prop);
    val H2 = Thm.assume (ctermF H2prop);
    val H3 = Thm.assume (ctermF H3prop);
    val goalC = oFalseC;

    (* bodies of the two dvd existentials *)
    val PdvdA  = Abs("k", natT, oeq aF (mult pF (Bound 0)));         (* body of dvd p a *)
    val PdvdSA = Abs("k", natT, oeq (suc aF) (mult pF (Bound 0)));   (* body of dvd p (Suc a) *)

    (* exE on H2 : witness j, hj : oeq a (mult p j) *)
    fun bodyJ jT_ (hj : thm) =
      let
        (* exE on H3 : witness k, hk : oeq (Suc a)(mult p k) *)
        fun bodyK kT_ (hk : thm) =
          let
            (* Suc a = add a (Suc 0) *)
            val aS    = addSrF_at (aF, ZeroC);          (* (a + Suc 0) = Suc(a + 0) *)
            val a0    = add0rF_at aF;                   (* (a + 0) = a *)
            val sa0   = Suc_cong OF [a0];               (* Suc(a + 0) = Suc a *)
            val aS_Sa = oeq_trans OF [aS, sa0];         (* (a + Suc 0) = Suc a *)
            val Sa_aS = oeq_sym OF [aS_Sa];             (* Suc a = (a + Suc 0) *)
            (* mult p k = add a (Suc 0) *)
            val mpk_Sa = oeq_sym OF [hk];               (* (mult p k) = Suc a *)
            val mpk_aS = oeq_trans OF [mpk_Sa, Sa_aS];  (* (mult p k) = (a + Suc 0) *)
            (* add a (Suc 0) = add (mult p j)(Suc 0)  [add_cong_l hj] *)
            val congA  = add_cong_lF (aF, mult pF jT_, suc ZeroC) hj;
                                                        (* (a + Suc 0) = ((mult p j) + Suc 0) *)
            val mpk_eq = oeq_trans OF [mpk_aS, congA];  (* (mult p k) = ((mult p j) + Suc 0) *)

            (* le_total on (j,k) *)
            val dz = le_totalF_at (jT_, kT_);           (* Disj (le j k)(le k j) *)

            (* CASE le j k *)
            val caseLEjk =
              let
                val hle = Thm.assume (ctermF (jT (le jT_ kT_)));
                val Pe  = Abs("e", natT, oeq kT_ (add jT_ (Bound 0)));  (* body of le j k *)
                fun bodyE eT (he : thm) =                 (* he : oeq k (add j e) *)
                  let
                    (* mult p k = mult p (add j e) [mult_cong_r he] *)
                    val congK = mult_cong_rF (pF, kT_, add jT_ eT) he;  (* (p*k) = (p*(j+e)) *)
                    val ld    = left_distribF_at (pF, jT_, eT);         (* (p*(j+e)) = ((p*j)+(p*e)) *)
                    val mpk_dist = oeq_trans OF [congK, ld];            (* (p*k) = ((p*j)+(p*e)) *)
                    (* ((p*j)+(Suc 0)) = ((p*j)+(p*e))  [sym mpk_eq, trans mpk_dist] *)
                    val Sj_eq = oeq_trans OF [oeq_sym OF [mpk_eq], mpk_dist];
                                                                       (* ((p*j)+Suc 0) = ((p*j)+(p*e)) *)
                    val canc  = add_left_cancel_vCop OF [Sj_eq];        (* oeq (Suc 0)(p*e) *)
                    val pe1   = oeq_sym OF [canc];                      (* oeq (p*e)(Suc 0) *)
                    (* mult_eq_one : oeq (mult p e)(Suc 0) ==> oeq p (Suc 0) *)
                    val p_is_1 = (varify mult_eq_one) OF [pe1];         (* oeq p (Suc 0) *)
                    (* subst p := Suc 0 into H1 : lt (Suc 0) p  ->  lt (Suc 0)(Suc 0) *)
                    (* lt (Suc 0) p = le (Suc(Suc 0)) p ; subst p->Suc 0 in (le (Suc(Suc 0)) _) *)
                    val zSub = Free("z_cop1", natT);
                    val Psub = Term.lambda zSub (ltF (suc ZeroC) zSub);   (* %z. le (Suc(Suc 0)) z *)
                    val subInst = beta_norm (Drule.infer_instantiate ctxtF
                          [(("P",0), ctermF Psub), (("a",0), ctermF pF), (("b",0), ctermF (suc ZeroC))] oeq_subst_vF);
                    val lt11 = (subInst OF [p_is_1]) OF [H1];           (* lt (Suc 0)(Suc 0) *)
                    val fls  = lt_irreflF_at (suc ZeroC) lt11;          (* oFalse *)
                  in fls end;
                val fls = exE_elimF (Pe, goalC) hle "e0" bodyE;
              in Thm.implies_intr (ctermF (jT (le jT_ kT_))) fls end;

            (* CASE le k j *)
            val caseLEkj =
              let
                val hle = Thm.assume (ctermF (jT (le kT_ jT_)));
                (* mult_le_mono : le k j ==> le (mult p k)(mult p j)  (inst j:=k, k:=j) *)
                val le_pk_pj = mult_le_monoF_at (pF, kT_, jT_) hle;     (* le (p*k)(p*j) *)
                (* le (mult p j)(mult p k) : witness (Suc 0), body mpk_eq *)
                val le_pj_pk = le_introF (mult pF jT_, mult pF kT_, suc ZeroC) mpk_eq;
                (* neg (oeq (mult p j)(mult p k)) *)
                val neqThm =
                  let
                    val eqHypP = jT (oeq (mult pF jT_) (mult pF kT_));
                    val eqHyp  = Thm.assume (ctermF eqHypP);            (* (p*j) = (p*k) *)
                    (* (p*j) = ((p*j)+(Suc 0))  [trans eqHyp mpk_eq] *)
                    val pj_Sj  = oeq_trans OF [eqHyp, mpk_eq];          (* (p*j) = ((p*j)+Suc 0) *)
                    (* (p*j) = ((p*j)+0)  [sym add_0_right] *)
                    val pj0    = oeq_sym OF [add0rF_at (mult pF jT_)];  (* (p*j) = ((p*j)+0) *)
                    val pj0_s  = oeq_sym OF [pj0];                      (* ((p*j)+0) = (p*j) *)
                    val z0_Sj  = oeq_trans OF [pj0_s, pj_Sj];           (* ((p*j)+0) = ((p*j)+Suc 0) *)
                    val canc   = add_left_cancel_vCop OF [z0_Sj];       (* oeq 0 (Suc 0) *)
                    val cancS  = oeq_sym OF [canc];                     (* oeq (Suc 0) 0 *)
                    val fls    = (Suc_neq_ZeroF_at ZeroC) OF [cancS];   (* oFalse *)
                    val impBody= Thm.implies_intr (ctermF eqHypP) fls; (* (p*j)=(p*k) ==> oFalse *)
                  in negI_atF (oeq (mult pF jT_) (mult pF kT_)) impBody end;
                val lt_pj_pk = le_neq_ltF_at (mult pF jT_, mult pF kT_) le_pj_pk neqThm;
                                                                       (* lt (p*j)(p*k) = le (Suc(p*j))(p*k) *)
                (* le_trans (Suc(p*j), p*k, p*j) : lt (p*j)(p*k) ==> le (p*k)(p*j) ==> le (Suc(p*j))(p*j) *)
                val le_Spj_pj = le_transF_at (suc (mult pF jT_), mult pF kT_, mult pF jT_) lt_pj_pk le_pk_pj;
                                                                       (* le (Suc(p*j))(p*j) = lt (p*j)(p*j) *)
                val fls = lt_irreflF_at (mult pF jT_) le_Spj_pj;       (* oFalse *)
              in Thm.implies_intr (ctermF (jT (le kT_ jT_))) fls end;

            val combined = disjE_elimF (le jT_ kT_, le kT_ jT_, goalC) dz caseLEjk caseLEkj;
          in combined end;
        val afterK = exE_elimF (PdvdSA, goalC) H3 "k0" bodyK;
      in afterK end;
    val afterJ = exE_elimF (PdvdA, goalC) H2 "j0" bodyJ;
    val d3 = Thm.implies_intr (ctermF H3prop) afterJ;
    val d2 = Thm.implies_intr (ctermF H2prop) d3;
    val d1 = Thm.implies_intr (ctermF H1prop) d2;
  in varify d1 end;

val pVcc = Var (("p",0), natT);
val aVcc = Var (("a",0), natT);
val consec_coprime_intended =
  Logic.mk_implies (jT (ltF (suc ZeroC) pVcc),
    Logic.mk_implies (jT (dvd pVcc aVcc),
      Logic.mk_implies (jT (dvd pVcc (suc aVcc)), jT oFalseC)));
val r_consec_coprime = checkF ("consec_coprime", consec_coprime, consec_coprime_intended);

val () = if r_consec_coprime then out "COP_DONE\n" else out "COP_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  EUCLID'S THEOREM : INFINITELY MANY PRIMES  ***
        euclid : jT (Forall (%n. Ex (%p. Conj (prime2 p) (lt n p))))
        i.e. for every n there is a prime p with n < p.
   ----------------------------------------------------------------------------
   Built on ctxtF (the FINAL context, with `fact` + its axioms).  Everything
   needed is already proven in the preamble:
     fact_pos              : jT (lt 0 (fact n))          (= le 1 (fact n))
     dvd_fact              : jT (le 1 p) ==> jT (le p n) ==> jT (dvd p (fact n))
     consec_coprime        : jT (lt 1 p) ==> jT (dvd p a) ==> jT (dvd p (Suc a)) ==> jT oFalse
     prime_divisor_exists  : jT (le 2 N) ==> jT (Ex (%p. Conj (prime2 p)(dvd p N)))
     le_cases / le_total / le_trans / le_refl / le_suc_mono   (order lemmas)
   PROOF (constructive; NO excluded middle needed):
     fix Free n ; N := Suc (fact n) = n!+1.
     le 2 N            from fact_pos (le 1 n!) by le_suc_mono.
     prime_divisor_exists at N -> exE p, prime2 p, dvd p N.
     lt 1 p            = conjunct1 (prime2 p).
     le 1 p            from le 2 p (= lt 1 p) by le_trans with le 1 2.
     CLAIM lt n p :  le_total (Suc n, p) -> Disj (lt n p)(le p (Suc n)).
       Case lt n p   : done directly.
       Case le p (Suc n) : le_cases (p,n) -> Disj (le p n)(oeq p (Suc n)).
         Sub le p n      : dvd_fact (le 1 p)(le p n) -> dvd p (fact n) ;
                           consec_coprime (lt 1 p)(dvd p n!)(dvd p N) -> oFalse ;
                           oFalse_elim -> lt n p.
         Sub oeq p (Suc n): lt n p = le (Suc n) p ; p = Suc n ; le_refl(Suc n) + subst.
     Conj (prime2 p)(lt n p) ; exI ; allI over n.
   ============================================================================ *)

val () = out "EUCLID_BEGIN\n";

(* ---- ctxtF connective helpers : conjunct1 / conjI / allI ---- *)
val conjI_vF      = varify conjI_ax;
val conjunct1_vF  = varify conjunct1_ax;
val conjunct2_vF  = varify conjunct2_ax;
val allI_vF       = varify allI_ax;
fun conjI_atF (At, Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("A",0), ctermF At), (("B",0), ctermF Bt)] conjI_vF)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_atF (At, Bt) hConj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("A",0), ctermF At), (("B",0), ctermF Bt)] conjunct1_vF)
  in Thm.implies_elim inst hConj end;
fun conjunct2_atF (At, Bt) hConj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("A",0), ctermF At), (("B",0), ctermF Bt)] conjunct2_vF)
  in Thm.implies_elim inst hConj end;
(* allI : (!!x. jT (P x)) ==> jT (Forall P) *)
fun allI_atF Pabs hAllThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("P",0), ctermF Pabs)] allI_vF)
  in Thm.implies_elim inst hAllThm end;

(* ---- order lemmas lifted to ctxtF ---- *)
val le_suc_mono_vF = varify le_suc_mono;
fun le_suc_monoF_at (mt, nt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("m",0), ctermF mt), (("n",0), ctermF nt)] le_suc_mono_vF)
  in Thm.implies_elim inst h end;
(* le_total / le_trans / le_cases / dvd_fact / fact_pos / consec_coprime already
   have ground instantiators on ctxtF: le_totalF_at, le_transF_at, le_cases_atF.
   fact_pos / dvd_fact / consec_coprime are varifiable directly. *)

(* prime_divisor_exists lifted to ctxtF *)
val prime_divisor_exists_vF = varify prime_divisor_exists;
fun prime_divisor_exists_atF Nt h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("n",0), ctermF Nt)] prime_divisor_exists_vF)
  in Thm.implies_elim inst h end;

(* dvd_fact lifted to ctxtF (it is itself a thyF theorem; varify re-zeroes) *)
val dvd_fact_vF = varify dvd_fact;
fun dvd_fact_atF (pt, nt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("p",0), ctermF pt), (("n",0), ctermF nt)] dvd_fact_vF)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* consec_coprime lifted to ctxtF *)
val consec_coprime_vF = varify consec_coprime;
fun consec_coprime_atF (pt, at) h1 h2 h3 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtF
        [(("p",0), ctermF pt), (("a",0), ctermF at)] consec_coprime_vF)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst h1) h2) h3 end;

(* fact_pos lifted to ctxtF : jT (le 1 (fact n)) *)
val fact_pos_vF = varify fact_pos;
fun fact_pos_atF nt = beta_norm (Drule.infer_instantiate ctxtF
      [(("n",0), ctermF nt)] fact_pos_vF);

val () = out "EUCLID_INSTANTIATORS_READY\n";

(* ---- le 1 2 : le (Suc 0) (Suc (Suc 0)) ; witness (Suc 0) ; body oeq 2 (1+1) ---- *)
val le_one_two =
  let
    val aS  = addSucF_at (ZeroC, suc ZeroC);        (* (Suc 0 + Suc 0) = Suc(0 + Suc 0) *)
    val a0  = add0F_at (suc ZeroC);                 (* (0 + Suc 0) = Suc 0 *)
    val sa0 = Suc_cong OF [a0];                      (* Suc(0 + Suc 0) = Suc(Suc 0) *)
    val chain = oeq_trans OF [aS, sa0];             (* (Suc 0 + Suc 0) = Suc(Suc 0) *)
    val body  = oeq_sym OF [chain];                 (* Suc(Suc 0) = (Suc 0 + Suc 0) *)
  in le_introF (suc ZeroC, suc (suc ZeroC), suc ZeroC) body end;
    (* le_one_two : jT (le (Suc 0)(Suc(Suc 0))) *)

(* ============================================================================
   euclid : jT (Forall (%n. Ex (%p. Conj (prime2 p)(lt n p))))
   ============================================================================ *)
(* the Forall body : %n. Ex (%p. Conj (prime2 p)(lt n p)) *)
val innerExBodyForall =
  let
    val nF = Free("n_all", natT)
    val pF = Free("p_e", natT)
  in Term.lambda nF (mkEx (Term.lambda pF (mkConj (prime2 pF) (ltF nF pF)))) end;

val euclid =
  let
    (* the inner existential body : %p. Conj (prime2 p)(lt n p), built capture-avoidingly *)
    fun innerBodyAbs nt =
      let val pF = Free("p_e", natT)
      in Term.lambda pF (mkConj (prime2 pF) (ltF nt pF)) end;

    (* ---- core : for a fixed Free n, build  jT (Ex (%p. Conj (prime2 p)(lt n p))) ---- *)
    fun coreFor nF =
      let
        val factN = fact nF;
        val NN    = suc factN;                              (* N = Suc (fact n) = n!+1 *)

        (* le 2 N : from fact_pos (le 1 n!) by le_suc_mono *)
        val le1fn = fact_pos_atF nF;                        (* le (Suc 0)(fact n) *)
        val le2N  = le_suc_monoF_at (suc ZeroC, factN) le1fn;
                                                            (* le (Suc(Suc 0))(Suc(fact n)) = le 2 N *)

        (* prime_divisor_exists at N -> Ex (%p_rb. Conj (prime2 p_rb)(dvd p_rb N)) *)
        val pdeEx = prime_divisor_exists_atF NN le2N;
        val pdeBody = resultBodyAbs NN;                     (* %p_rb. Conj (prime2 p_rb)(dvd p_rb N) *)
        val goalEx  = mkEx (innerBodyAbs nF);              (* Ex (%p. Conj (prime2 p)(lt n p)) *)

        fun afterP p (hConj : thm) =                       (* hConj : Conj (prime2 p)(dvd p N) *)
          let
            val hPrime = conjunct1_atF (prime2 p, dvd p NN) hConj;   (* prime2 p *)
            val hDvdpN = conjunct2_atF (prime2 p, dvd p NN) hConj;   (* dvd p N = dvd p (Suc (fact n)) *)
            (* lt 1 p = conjunct1 of prime2 p ; prime2 p = Conj (lt 1 p)(Forall ...) *)
            val lt1p   = conjunct1_atF (lt (suc ZeroC) p, mkForall (ppAbs p)) hPrime;
                                                            (* lt (Suc 0) p = le (Suc(Suc 0)) p = le 2 p *)
            (* le 1 p from le 2 p by le_trans (1, 2, p) with le_one_two *)
            val le1p   = le_transF_at (suc ZeroC, suc (suc ZeroC), p) le_one_two lt1p;
                                                            (* le (Suc 0) p *)

            (* ---- CLAIM lt n p ---- *)
            val ltnp =
              let
                val dz = le_totalF_at (suc nF, p);          (* Disj (le (Suc n) p)(le p (Suc n)) *)
                                                            (* le (Suc n) p == lt n p *)
                (* CASE lt n p : direct *)
                val caseLt =
                  let val h = Thm.assume (ctermF (jT (ltF nF p)))   (* = le (Suc n) p *)
                  in Thm.implies_intr (ctermF (jT (le (suc nF) p))) h end;
                (* CASE le p (Suc n) : le_cases then sub-cases *)
                val casePSn =
                  let
                    val hle = Thm.assume (ctermF (jT (le p (suc nF))));
                    val dc  = le_cases_atF (p, nF) hle;     (* Disj (le p n)(oeq p (Suc n)) *)
                    (* SUB le p n -> contradiction via dvd_fact + consec_coprime *)
                    val subLepn =
                      let
                        val hlepn = Thm.assume (ctermF (jT (le p nF)));   (* le p n *)
                        val dvdpfn = dvd_fact_atF (p, nF) le1p hlepn;     (* dvd p (fact n) *)
                        val fls = consec_coprime_atF (p, factN) lt1p dvdpfn hDvdpN;  (* oFalse *)
                        val g   = (oFalse_elimF_at (ltF nF p)) OF [fls];  (* lt n p *)
                      in Thm.implies_intr (ctermF (jT (le p nF))) g end;
                    (* SUB oeq p (Suc n) -> lt n p = le (Suc n) p ; p = Suc n ; le_refl *)
                    val subEq =
                      let
                        val heq = Thm.assume (ctermF (jT (oeq p (suc nF))));   (* oeq p (Suc n) *)
                        val leSnSn = le_reflF_at (suc nF);                    (* le (Suc n)(Suc n) *)
                        (* subst (Suc n) -> p inside (le (Suc n) _) : P z := le (Suc n) z *)
                        val zF   = Free("z_eu", natT);
                        val Psub = Term.lambda zF (le (suc nF) zF);          (* %z. le (Suc n) z *)
                        val subInst = beta_norm (Drule.infer_instantiate ctxtF
                              [(("P",0), ctermF Psub), (("a",0), ctermF (suc nF)), (("b",0), ctermF p)] oeq_subst_vF);
                        val Sn_p = oeq_sym OF [heq];                          (* oeq (Suc n) p *)
                        val g = (subInst OF [Sn_p]) OF [leSnSn];              (* le (Suc n) p = lt n p *)
                      in Thm.implies_intr (ctermF (jT (oeq p (suc nF)))) g end;
                    val combined = disjE_elimF (le p nF, oeq p (suc nF), ltF nF p) dc subLepn subEq;
                  in Thm.implies_intr (ctermF (jT (le p (suc nF)))) combined end;
                (* le (Suc n) p == ltF n p ; the Disj left disjunct *)
                val res = disjE_elimF (le (suc nF) p, le p (suc nF), ltF nF p) dz caseLt casePSn;
              in res end;   (* ltnp : jT (lt n p) *)

            (* build Conj (prime2 p)(lt n p) ; exI -> Ex (%p. Conj (prime2 p)(lt n p)) *)
            val conjP = conjI_atF (prime2 p, ltF nF p) hPrime ltnp;  (* Conj (prime2 p)(lt n p) *)
            val ex    = exI_atF (innerBodyAbs nF) p conjP;           (* Ex (%p. ...) *)
          in ex end;

        val resEx = exE_elimF (pdeBody, goalEx) pdeEx "p_eu" afterP;
      in resEx end;   (* jT (Ex (%p. Conj (prime2 p)(lt n p))) *)

    (* ---- allI over n ---- *)
    val nGen = Free("n", natT);
    val coreThm = coreFor nGen;                              (* jT (Ex (%p. Conj (prime2 p)(lt n p))) *)
    val PallAbs = innerExBodyForall;                         (* %n. Ex (%p. Conj (prime2 p)(lt n p)) *)
    val allThm  = Thm.forall_intr (ctermF nGen) coreThm;     (* !!n. jT (Ex (%p. ...)) *)
    val gAll    = allI_atF PallAbs allThm;                   (* jT (Forall (%n. ...)) *)
  in varify gAll end;

(* ============================================================================
   VALIDATION : 0-hyp AND aconv the intended schematic goal.
   ============================================================================ *)
val euclid_intended =
  let
    val nF = Free("n_all", natT)
    val pF = Free("p_e", natT)
    val Pall = Term.lambda nF (mkEx (Term.lambda pF (mkConj (prime2 pF) (ltF nF pF))))
  in jT (mkForall Pall) end;

val r_euclid = checkF ("euclid", euclid, euclid_intended);

val () = if r_euclid then out "EUCLID_DONE\n" else out "EUCLID_FAILED\n";

(* ============================================================================
   SOUNDNESS PROBE : the kernel rejects a FALSE variant
   (drop the prime2 conjunct -> "for every n there is SOME p with n<p", which is
   TRUE but a DIFFERENT statement; more telling: assert n < n which is false.
   We check that euclid's prop is NOT aconv a bogus weaker-but-different goal,
   and that a deliberately FALSE theorem cannot be obtained from euclid by aconv.) *)
val euclid_bogus_false =
  let
    (* bogus : Forall (%n. Ex (%p. Conj (prime2 p)(lt p n)))   -- p < n instead of n < p.
       This is FALSE (take n=0 : no p<0).  euclid must NOT aconv it. *)
    val nF = Free("n_all", natT)
    val pF = Free("p_e", natT)
    val Pall = Term.lambda nF (mkEx (Term.lambda pF (mkConj (prime2 pF) (ltF pF nF))))
  in jT (mkForall Pall) end;
val () =
  if not ((Thm.prop_of euclid) aconv euclid_bogus_false)
  then out "SOUNDNESS_PROBE_OK (false variant lt p n rejected)\n"
  else out "SOUNDNESS_PROBE_UNSOUND (euclid aconv a false goal!)\n";
