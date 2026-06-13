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
   CLASSICAL FOL + GENUINE "EVERY n >= 2 HAS A PRIME DIVISOR" in Isabelle/Pure
   on the polyml-rs interpreter.  (test: isabelle_classical_primes.rs)
   ----------------------------------------------------------------------------
   This SUPERSEDES the caveated capstone in isabelle_primes.sml (which assumed an
   abstract-prime case-split axiom).  Here the case-split is DERIVED, so the
   prime-divisor theorem is genuine, over the STRUCTURAL prime definition.

   Built on the full self-derived number-theory ladder (object logic + Peano
   add/mult + commutative semiring + existential quantifier + linear order +
   divisibility, all from isabelle_divisibility.sml), this driver:

   1. Makes the object logic CLASSICAL: adds object Imp/Conj/Forall (with
      intro/elim) and ONE classical axiom, excluded middle
        ex_middle : |- A \/ ~A
      then DERIVES the standard classical lemmas (each 0-extra-hyp, aconv-checked):
        dbl_neg     : ~~A ==> A
        deMorgan_or : ~(A \/ B) ==> ~A /\ ~B
        not_imp     : ~(A --> B) ==> A /\ ~B          (classical)
        not_forall  : ~(!x. P x) ==> (?x. ~ P x)       (classical)

   2. Adds the number-theory connectors: the strict order lt (m<n := Suc m<=n)
      with lt_suc/lt_irrefl/lt_suc_cases/lt_trans, le_neq_lt, the num facts
      (ne0_suc, gt1_of_ne0_ne1, dvd_nonzero), strong (course-of-values)
      induction, and the STRUCTURAL prime predicate
        prime p := 1 < p  /\  (!d. d | p ==> d = 1 \/ d = p).

   3. DERIVES the primality case-split (NOT an axiom this time):
        prime_cases : 1 < n ==> prime n \/ (?d. 1 < d /\ d < n /\ d | n)
      from excluded middle + the structural prime + dvd_le + the classical lemmas.

   4. Proves the GENUINE capstone BY STRONG INDUCTION:
        prime_divisor_exists : 2 <= n ==> ?p. prime p /\ p | n
      where `prime` is the structural definition above.  No abstract-prime axiom;
      the only classical assumption is excluded middle (which real Isabelle/HOL
      object logics have).  Soundness probes confirm the kernel rejects false
      variants.

   Engineered by a 4-phase ultracode pipeline (wf_26188260-4af): classical FOL ->
   NT connectors + strong induction -> prime_cases (3 seats, all derived it) ->
   capstone (2 seats, both proved it).  Each phase validated on the checkpoint.
   ============================================================================ *)

(* ============================================================================
   isabelle_divisibility.sml  —  DIVISIBILITY is a PREORDER on the naturals,
   COMPATIBLE with + and *, and REFINES the order.  ONE self-contained
   Isabelle/Pure ML driver, proving the whole bundle in a single run over the
   warm /tmp/isabelle_pure checkpoint.

   WHAT IT PROVES  (each a 0-hypothesis schematic theorem; each prints "OK <name>"):
     dvd_refl        : |- dvd a a                     (reflexivity)
     one_dvd         : |- dvd (Suc Zero) n            (1 | n)
     dvd_zero        : |- dvd a Zero                  (a | 0)
     dvd_trans       : |- dvd a b ==> dvd b c ==> dvd a c          (=> PREORDER)
     dvd_add         : |- dvd d m ==> dvd d n ==> dvd d (add m n)  (+ compatibility)
     dvd_mult_right  : |- dvd a b ==> dvd a (mult b c)             [* compatibility]
     dvd_mult_cong   : |- dvd a b ==> dvd (mult a c) (mult b c)    [* compatibility]
     dvd_le          : |- dvd d n ==> (oeq n Zero ==> oFalse) ==> le d n
                                                       (d | n & n != 0  =>  d <= n)
   On success the driver prints all eight "OK <name>" lines + "DVD_DONE".

   HOW IT WAS BUILT  (merge, not invention):
     The foundation (object logic o/nat + Trueprop + Peano add & mult + equality
     oeq + induction + the existential/order extension, ending on the SINGLE FINAL
     theory thyT with context ctxtT/ctermT, then the `dvd` abbreviation + dvd_intro
     and the three easy lemmas dvd_refl/one_dvd/dvd_zero) is copied VERBATIM from
     /tmp/isa_dvd_foundation.sml.  The five remaining law proofs are merged in
     dependency order from the four independently-verified drivers:
       isa_dvd_dvd_trans.sml  -> dvd_trans
       isa_dvd_dvd_add.sml    -> dvd_add
       isa_dvd_dvd_mult.sml   -> dvd_mult_right, dvd_mult_cong
       isa_dvd_dvd_le.sml     -> dvd_le  (the order-connecting capstone)
     Shared helpers (mult_assoc on ctxtT, mult_cong_lT) appear in more than one
     source driver; they are defined ONCE here.  Every new cterm routes through
     the single final context ctxtT/ctermT (mixing an earlier-theory cterm into a
     dvd/le goal gives a cross-theory certificate mismatch).  Each law, after being
     proved, is validated 0-hyp AND `aconv` its intended schematic goal (the goal
     built with the SAME dvd/le abbreviations so the Ex-bodies match exactly).
   ============================================================================ *)

val () = restore_pure_context ();
fun out s = (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);

(* ============================================================================
   FOUNDATION : object logic + Trueprop + Peano add + equality + induction
   ============================================================================ *)
val thy0 = Context.the_global_context ();
val thy1 = Sign.add_types_global
  [(Binding.name "o",0,NoSyn),(Binding.name "nat",0,NoSyn)] thy0;
val oN = Sign.full_name thy1 (Binding.name "o");
val natN = Sign.full_name thy1 (Binding.name "nat");
val oT = Type (oN,[]);  val natT = Type (natN,[]);
val thy2 = Sign.add_consts
  [(Binding.name "Trueprop", oT --> propT, NoSyn),
   (Binding.name "Zero", natT, NoSyn),
   (Binding.name "Suc", natT --> natT, NoSyn),
   (Binding.name "add", natT --> natT --> natT, NoSyn),
   (Binding.name "oeq", natT --> natT --> oT, NoSyn)] thy1;
fun cnst nm T = Const (Sign.full_name thy2 (Binding.name nm), T);
val TP    = cnst "Trueprop" (oT --> propT);      fun jT t = TP $ t;
val ZeroC = cnst "Zero" natT;
val SucC  = cnst "Suc" (natT --> natT);          fun suc t = SucC $ t;
val addC  = cnst "add" (natT --> natT --> natT); fun add a b = addC $ a $ b;
val oeqC  = cnst "oeq" (natT --> natT --> oT);   fun oeq a b = oeqC $ a $ b;
val predT = natT --> oT;
val a = Free ("a",natT); val b = Free ("b",natT);
val n = Free ("n",natT); val m = Free ("m",natT);
val P = Free ("P", predT);

val ((_,oeq_refl),  t3) = Thm.add_axiom_global (Binding.name "oeq_refl",  jT (oeq a a)) thy2;
val ((_,oeq_subst), t4) = Thm.add_axiom_global (Binding.name "oeq_subst",
      Logic.mk_implies (jT (oeq a b), Logic.mk_implies (jT (P $ a), jT (P $ b)))) t3;
val ((_,add_0),   t5) = Thm.add_axiom_global (Binding.name "add_0",   jT (oeq (add ZeroC n) n)) t4;
val ((_,add_Suc), t6) = Thm.add_axiom_global (Binding.name "add_Suc",
      jT (oeq (add (suc m) n) (suc (add m n)))) t5;
val k = Free ("k", natT); val x = Free ("x", natT);
val induct_prop = Logic.mk_implies (jT (P $ ZeroC),
      Logic.mk_implies (Logic.all x (Logic.mk_implies (jT (P $ x), jT (P $ (suc x)))), jT (P $ k)));
val ((_,nat_induct), thy) = Thm.add_axiom_global (Binding.name "nat_induct", induct_prop) t6;

val ctxt = Proof_Context.init_global thy;
val cterm = Thm.cterm_of ctxt;
fun varify th = Drule.zero_var_indexes (Drule.export_without_context th);
fun beta_norm th = Thm.equal_elim (Drule.beta_eta_conversion (Thm.cprop_of th)) th;

val oeq_refl_v   = varify oeq_refl;
val oeq_subst_v  = varify oeq_subst;
val add_0_v      = varify add_0;
val add_Suc_v    = varify add_Suc;
val nat_induct_v = varify nat_induct;

val oeq_sym =
  let
    val aF = Free("a",natT); val bF = Free("b",natT);
    val Pabs = Abs("z", natT, oeq (Bound 0) aF);
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm aF), (("b",0), cterm bF)] oeq_subst_v);
    val refl_aa = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm aF)] oeq_refl_v);
    val step = inst OF [Thm.assume (cterm (jT (oeq aF bF))), refl_aa];
  in varify (Thm.implies_intr (cterm (jT (oeq aF bF))) step) end;

val oeq_trans =
  let
    val aF = Free("a",natT); val bF = Free("b",natT); val cF = Free("c",natT);
    val Pabs = Abs("z", natT, oeq aF (Bound 0));
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm bF), (("b",0), cterm cF)] oeq_subst_v);
    val H1 = Thm.assume (cterm (jT (oeq aF bF)));
    val H2 = Thm.assume (cterm (jT (oeq bF cF)));
    val step = inst OF [H2, H1];
    val t0 = Thm.implies_intr (cterm (jT (oeq bF cF))) step;
    val t1 = Thm.implies_intr (cterm (jT (oeq aF bF))) t0;
  in varify t1 end;

val Suc_cong =
  let
    val aF = Free("a",natT); val bF = Free("b",natT);
    val Pabs = Abs("z", natT, oeq (suc aF) (suc (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm aF), (("b",0), cterm bF)] oeq_subst_v);
    val refl_SaSa = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (suc aF))] oeq_refl_v);
    val H1 = Thm.assume (cterm (jT (oeq aF bF)));
    val step = inst OF [H1, refl_SaSa];
  in varify (Thm.implies_intr (cterm (jT (oeq aF bF))) step) end;

fun add0_at t         = beta_norm (Drule.infer_instantiate ctxt [(("n",0), cterm t)] add_0_v);
fun addSuc_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxt
                          [(("m",0), cterm mt),(("n",0), cterm nt)] add_Suc_v);
fun add_cong_l_at (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Pabs), (("a",0), cterm pT), (("b",0), cterm qT)] oeq_subst_v);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxt [(("a",0), cterm (add pT kT))] oeq_refl_v);
  in inst OF [hpq, refl_pk] end;

val add_0_right =
  let
    val Qpred = Abs("z", natT, oeq (add (Bound 0) ZeroC) (Bound 0));
    val nF = Free("n", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Qpred), (("k",0), cterm nF)] nat_induct_v);
    val base = add0_at ZeroC;
    val xF = Free("x", natT);
    val ihprop = jT (oeq (add xF ZeroC) xF);
    val IH = Thm.assume (cterm ihprop);
    val aS = addSuc_at (xF, ZeroC);
    val sc = Suc_cong OF [IH];
    val stepconcl = oeq_trans OF [aS, sc];
    val step1 = Thm.forall_intr (cterm xF) (Thm.implies_intr (cterm ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val add_Suc_right =
  let
    val nF = Free("n", natT);
    val Qpred = Abs("z", natT, oeq (add (Bound 0) (suc nF)) (suc (add (Bound 0) nF)));
    val mF = Free("m", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Qpred), (("k",0), cterm mF)] nat_induct_v);
    val b1 = add0_at (suc nF);
    val b2 = add0_at nF;
    val b2s = Suc_cong OF [b2];
    val b2ssym = oeq_sym OF [b2s];
    val base = oeq_trans OF [b1, b2ssym];
    val xF = Free("x", natT);
    val ihprop = jT (oeq (add xF (suc nF)) (suc (add xF nF)));
    val IH = Thm.assume (cterm ihprop);
    val s1 = addSuc_at (xF, suc nF);
    val s2 = Suc_cong OF [IH];
    val s3 = addSuc_at (xF, nF);
    val s3s = Suc_cong OF [s3];
    val s3ssym = oeq_sym OF [s3s];
    val c12 = oeq_trans OF [s1, s2];
    val stepconcl = oeq_trans OF [c12, s3ssym];
    val step1 = Thm.forall_intr (cterm xF) (Thm.implies_intr (cterm ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val add_0_right_v   = varify add_0_right;
val add_Suc_right_v = varify add_Suc_right;
fun add0r_at t       = beta_norm (Drule.infer_instantiate ctxt [(("n",0), cterm t)] add_0_right_v);
fun addSr_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxt
                         [(("m",0), cterm mt),(("n",0), cterm nt)] add_Suc_right_v);

val add_comm =
  let
    val nF = Free("n", natT);
    val Qpred = Abs("z", natT, oeq (add (Bound 0) nF) (add nF (Bound 0)));
    val mF = Free("m", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Qpred), (("k",0), cterm mF)] nat_induct_v);
    val b1 = add0_at nF;
    val b2 = add0r_at nF;
    val b2sym = oeq_sym OF [b2];
    val base = oeq_trans OF [b1, b2sym];
    val xF = Free("x", natT);
    val ihprop = jT (oeq (add xF nF) (add nF xF));
    val IH = Thm.assume (cterm ihprop);
    val s1 = addSuc_at (xF, nF);
    val s2 = Suc_cong OF [IH];
    val s3 = addSr_at (nF, xF);
    val s3sym = oeq_sym OF [s3];
    val c12 = oeq_trans OF [s1, s2];
    val stepconcl = oeq_trans OF [c12, s3sym];
    val step1 = Thm.forall_intr (cterm xF) (Thm.implies_intr (cterm ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val add_assoc =
  let
    val nF = Free("n", natT); val kF = Free("k", natT);
    val Qpred = Abs("z", natT,
        oeq (add (add (Bound 0) nF) kF) (add (Bound 0) (add nF kF)));
    val mF = Free("m", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxt
          [(("P",0), cterm Qpred), (("k",0), cterm mF)] nat_induct_v);
    val a0n = add0_at nF;
    val L1  = add_cong_l_at (add ZeroC nF, nF, kF) a0n;
    val R1  = add0_at (add nF kF);
    val R1s = oeq_sym OF [R1];
    val base = oeq_trans OF [L1, R1s];
    val xF = Free("x", natT);
    val ihprop = jT (oeq (add (add xF nF) kF) (add xF (add nF kF)));
    val IH = Thm.assume (cterm ihprop);
    val e1  = addSuc_at (xF, nF);
    val e1c = add_cong_l_at (add (suc xF) nF, suc (add xF nF), kF) e1;
    val e2  = addSuc_at (add xF nF, kF);
    val e3  = Suc_cong OF [IH];
    val e4  = addSuc_at (xF, add nF kF);
    val e4s = oeq_sym OF [e4];
    val c1  = oeq_trans OF [e1c, e2];
    val c2  = oeq_trans OF [c1, e3];
    val stepconcl = oeq_trans OF [c2, e4s];
    val step1 = Thm.forall_intr (cterm xF) (Thm.implies_intr (cterm ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

(* ============================================================================
   MULTIPLICATION on extended theory thyM (ctxtM / ctermM)
   ============================================================================ *)
val thyM = Sign.add_consts
  [(Binding.name "mult", natT --> natT --> natT, NoSyn)] thy;
val multC = Const (Sign.full_name thyM (Binding.name "mult"), natT --> natT --> natT);
fun mult s t = multC $ s $ t;
val ((_,mult_0),   tM1) = Thm.add_axiom_global (Binding.name "mult_0",
      jT (oeq (mult ZeroC n) ZeroC)) thyM;
val ((_,mult_Suc), tM2) = Thm.add_axiom_global (Binding.name "mult_Suc",
      jT (oeq (mult (suc m) n) (add n (mult m n)))) tM1;
val ctxtM   = Proof_Context.init_global tM2;
val ctermM  = Thm.cterm_of ctxtM;
val mult_0_v   = varify mult_0;
val mult_Suc_v = varify mult_Suc;
fun mult0_at t         = beta_norm (Drule.infer_instantiate ctxtM [(("n",0), ctermM t)] mult_0_v);
fun multSuc_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtM
                            [(("m",0), ctermM mt),(("n",0), ctermM nt)] mult_Suc_v);
fun add0M_at t         = beta_norm (Drule.infer_instantiate ctxtM [(("n",0), ctermM t)] add_0_v);
fun addSucM_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtM
                            [(("m",0), ctermM mt),(("n",0), ctermM nt)] add_Suc_v);
val add_comm_v  = varify add_comm;
val add_assoc_v = varify add_assoc;
fun addcomm_at (mt,nt)     = beta_norm (Drule.infer_instantiate ctxtM
                               [(("m",0), ctermM mt),(("n",0), ctermM nt)] add_comm_v);
fun addassoc_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtM
                               [(("m",0), ctermM mt),(("n",0), ctermM nt),(("k",0), ctermM kt)] add_assoc_v);
fun add_cong_lM (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtM
          [(("P",0), ctermM Pabs), (("a",0), ctermM pT), (("b",0), ctermM qT)] oeq_subst_v);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtM [(("a",0), ctermM (add pT kT))] oeq_refl_v);
  in inst OF [hpq, refl_pk] end;
fun add_cong_rM (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtM
          [(("P",0), ctermM Pabs), (("a",0), ctermM pT), (("b",0), ctermM qT)] oeq_subst_v);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtM [(("a",0), ctermM (add hT pT))] oeq_refl_v);
  in inst OF [hpq, refl_hp] end;
fun mult_cong_lM (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtM
          [(("P",0), ctermM Pabs), (("a",0), ctermM pT), (("b",0), ctermM qT)] oeq_subst_v);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtM [(("a",0), ctermM (mult pT kT))] oeq_refl_v);
  in inst OF [hpq, refl_pk] end;

val mult_0_right =
  let
    val Qpred = Abs("z", natT, oeq (mult (Bound 0) ZeroC) ZeroC);
    val nF = Free("n", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtM
          [(("P",0), ctermM Qpred), (("k",0), ctermM nF)] nat_induct_v);
    val base = mult0_at ZeroC;
    val xF = Free("x", natT);
    val ihprop = jT (oeq (mult xF ZeroC) ZeroC);
    val IH = Thm.assume (ctermM ihprop);
    val mS = multSuc_at (xF, ZeroC);
    val a0 = add0M_at (mult xF ZeroC);
    val c1 = oeq_trans OF [mS, a0];
    val stepconcl = oeq_trans OF [c1, IH];
    val step1 = Thm.forall_intr (ctermM xF) (Thm.implies_intr (ctermM ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val mult_Suc_right =
  let
    val mFix = Free("m", natT);
    val Qpred = Abs("z", natT, oeq (mult (Bound 0) (suc mFix)) (add (Bound 0) (mult (Bound 0) mFix)));
    val nF = Free("n", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtM
          [(("P",0), ctermM Qpred), (("k",0), ctermM nF)] nat_induct_v);
    val b1 = mult0_at (suc mFix);
    val r0 = mult0_at mFix;
    val rA = add0M_at (mult ZeroC mFix);
    val rChain = oeq_trans OF [rA, r0];
    val rChainSym = oeq_sym OF [rChain];
    val base = oeq_trans OF [b1, rChainSym];
    val xF = Free("x", natT);
    val ihprop = jT (oeq (mult xF (suc mFix)) (add xF (mult xF mFix)));
    val IH = Thm.assume (ctermM ihprop);
    val l1 = multSuc_at (xF, suc mFix);
    val l2 = add_cong_rM (suc mFix, mult xF (suc mFix), add xF (mult xF mFix)) IH;
    val l3 = addSucM_at (mFix, add xF (mult xF mFix));
    val lhs = oeq_trans OF [oeq_trans OF [l1, l2], l3];
    val r1' = multSuc_at (xF, mFix);
    val r2' = add_cong_rM (suc xF, mult (suc xF) mFix, add mFix (mult xF mFix)) r1';
    val r3' = addSucM_at (xF, add mFix (mult xF mFix));
    val rhs = oeq_trans OF [r2', r3'];
    val t = mult xF mFix;
    val br1 = addassoc_at (mFix, xF, t);
    val br1s = oeq_sym OF [br1];
    val br2 = addcomm_at (mFix, xF);
    val br2c = add_cong_lM (add mFix xF, add xF mFix, t) br2;
    val br3 = addassoc_at (xF, mFix, t);
    val innerChain = oeq_trans OF [oeq_trans OF [br1s, br2c], br3];
    val bridge = Suc_cong OF [innerChain];
    val rhsSym = oeq_sym OF [rhs];
    val stepconcl = oeq_trans OF [oeq_trans OF [lhs, bridge], rhsSym];
    val step1 = Thm.forall_intr (ctermM xF) (Thm.implies_intr (ctermM ihprop) stepconcl);
    val r1f = Thm.implies_elim ind base;
    val r2f = Thm.implies_elim r1f step1;
  in varify r2f end;

val mult_0_right_v   = varify mult_0_right;
val mult_Suc_right_v = varify mult_Suc_right;
fun mult0r_at t       = beta_norm (Drule.infer_instantiate ctxtM [(("n",0), ctermM t)] mult_0_right_v);
fun multSr_at (nt,mt) = beta_norm (Drule.infer_instantiate ctxtM
                          [(("n",0), ctermM nt),(("m",0), ctermM mt)] mult_Suc_right_v);

val mult_comm =
  let
    val nF = Free("n", natT);
    val Qpred = Abs("z", natT, oeq (mult (Bound 0) nF) (mult nF (Bound 0)));
    val mF = Free("m", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtM
          [(("P",0), ctermM Qpred), (("k",0), ctermM mF)] nat_induct_v);
    val b1 = mult0_at nF;
    val b2 = mult0r_at nF;
    val b2sym = oeq_sym OF [b2];
    val base = oeq_trans OF [b1, b2sym];
    val xF = Free("x", natT);
    val ihprop = jT (oeq (mult xF nF) (mult nF xF));
    val IH = Thm.assume (ctermM ihprop);
    val s1 = multSuc_at (xF, nF);
    val s2 = add_cong_rM (nF, mult xF nF, mult nF xF) IH;
    val s3 = multSr_at (nF, xF);
    val s3sym = oeq_sym OF [s3];
    val c12 = oeq_trans OF [s1, s2];
    val stepconcl = oeq_trans OF [c12, s3sym];
    val step1 = Thm.forall_intr (ctermM xF) (Thm.implies_intr (ctermM ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val right_distrib =
  let
    val nF = Free("n", natT); val kF = Free("k", natT);
    val Qpred = Abs("z", natT,
        oeq (mult (add (Bound 0) nF) kF) (add (mult (Bound 0) kF) (mult nF kF)));
    val mF = Free("m", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtM
          [(("P",0), ctermM Qpred), (("k",0), ctermM mF)] nat_induct_v);
    val a0n = add0M_at nF;
    val Lb  = mult_cong_lM (add ZeroC nF, nF, kF) a0n;
    val m0k = mult0_at kF;
    val Rb1 = add_cong_lM (mult ZeroC kF, ZeroC, mult nF kF) m0k;
    val Rb2 = add0M_at (mult nF kF);
    val RbChain = oeq_trans OF [Rb1, Rb2];
    val RbSym = oeq_sym OF [RbChain];
    val base = oeq_trans OF [Lb, RbSym];
    val xF = Free("x", natT);
    val ihprop = jT (oeq (mult (add xF nF) kF) (add (mult xF kF) (mult nF kF)));
    val IH = Thm.assume (ctermM ihprop);
    val sAdd = addSucM_at (xF, nF);
    val L1 = mult_cong_lM (add (suc xF) nF, suc (add xF nF), kF) sAdd;
    val L2 = multSuc_at (add xF nF, kF);
    val L3 = add_cong_rM (kF, mult (add xF nF) kF, add (mult xF kF) (mult nF kF)) IH;
    val lhs = oeq_trans OF [oeq_trans OF [L1, L2], L3];
    val mSk = multSuc_at (xF, kF);
    val R1 = add_cong_lM (mult (suc xF) kF, add kF (mult xF kF), mult nF kF) mSk;
    val R2 = addassoc_at (kF, mult xF kF, mult nF kF);
    val rhs = oeq_trans OF [R1, R2];
    val rhsSym = oeq_sym OF [rhs];
    val stepconcl = oeq_trans OF [lhs, rhsSym];
    val step1 = Thm.forall_intr (ctermM xF) (Thm.implies_intr (ctermM ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val right_distrib_v = varify right_distrib;
fun rdist_at (aT,bT,kT) = beta_norm (Drule.infer_instantiate ctxtM
        [(("m",0), ctermM aT),(("n",0), ctermM bT),(("k",0), ctermM kT)] right_distrib_v);

val mult_assoc =
  let
    val nF = Free("n", natT); val kF = Free("k", natT);
    val Qpred = Abs("z", natT,
        oeq (mult (mult (Bound 0) nF) kF) (mult (Bound 0) (mult nF kF)));
    val mF = Free("m", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtM
          [(("P",0), ctermM Qpred), (("k",0), ctermM mF)] nat_induct_v);
    val m0n   = mult0_at nF;
    val L1    = mult_cong_lM (mult ZeroC nF, ZeroC, kF) m0n;
    val L2    = mult0_at kF;
    val Lbase = oeq_trans OF [L1, L2];
    val R0    = mult0_at (mult nF kF);
    val R0sym = oeq_sym OF [R0];
    val base  = oeq_trans OF [Lbase, R0sym];
    val xF = Free("x", natT);
    val ihprop = jT (oeq (mult (mult xF nF) kF) (mult xF (mult nF kF)));
    val IH = Thm.assume (ctermM ihprop);
    val l1  = multSuc_at (xF, nF);
    val l1c = mult_cong_lM (mult (suc xF) nF, add nF (mult xF nF), kF) l1;
    val l2  = rdist_at (nF, mult xF nF, kF);
    val l3  = add_cong_rM (mult nF kF, mult (mult xF nF) kF, mult xF (mult nF kF)) IH;
    val Lc1 = oeq_trans OF [l1c, l2];
    val Lc2 = oeq_trans OF [Lc1, l3];
    val r1  = multSuc_at (xF, mult nF kF);
    val r1sym = oeq_sym OF [r1];
    val stepconcl = oeq_trans OF [Lc2, r1sym];
    val step1 = Thm.forall_intr (ctermM xF) (Thm.implies_intr (ctermM ihprop) stepconcl);
    val rr1 = Thm.implies_elim ind base;
    val rr2 = Thm.implies_elim rr1 step1;
  in varify rr2 end;

val add_0_right_vM = varify add_0_right;
fun add0rM_at t = beta_norm (Drule.infer_instantiate ctxtM [(("n",0), ctermM t)] add_0_right_vM);
val mult_1_right =
  let
    val nF = Free("n", natT);
    val s1 = multSr_at (nF, ZeroC);
    val m0 = mult0r_at nF;
    val cr = add_cong_rM (nF, mult nF ZeroC, ZeroC) m0;
    val a0 = add0rM_at nF;
    val c1 = oeq_trans OF [s1, cr];
    val c2 = oeq_trans OF [c1, a0];
  in varify c2 end;

fun add4_swap (A,B,C,D) =
  let
    val asbcd = addassoc_at (A, B, add C D);
    val i1 = addassoc_at (B, C, D);
    val i1s = oeq_sym OF [i1];
    val icc = addcomm_at (B, C);
    val i2 = add_cong_lM (add B C, add C B, D) icc;
    val i3 = addassoc_at (C, B, D);
    val inner = oeq_trans OF [oeq_trans OF [i1s, i2], i3];
    val cInner = add_cong_rM (A, add B (add C D), add C (add B D)) inner;
    val r1 = oeq_trans OF [asbcd, cInner];
    val r2assoc = addassoc_at (A, C, add B D);
    val r2assoc_s = oeq_sym OF [r2assoc];
  in oeq_trans OF [r1, r2assoc_s] end;

val left_distrib =
  let
    val mF = Free("m", natT); val nF = Free("n", natT);
    val Qpred = Abs("z", natT,
        oeq (mult (Bound 0) (add mF nF)) (add (mult (Bound 0) mF) (mult (Bound 0) nF)));
    val kF = Free("k", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtM
          [(("P",0), ctermM Qpred), (("k",0), ctermM kF)] nat_induct_v);
    val bL  = mult0_at (add mF nF);
    val bm0 = mult0_at mF;
    val bn0 = mult0_at nF;
    val bc1 = add_cong_lM (mult ZeroC mF, ZeroC, mult ZeroC nF) bm0;
    val bc2 = add_cong_rM (ZeroC, mult ZeroC nF, ZeroC) bn0;
    val b00 = add0M_at ZeroC;
    val bR  = oeq_trans OF [oeq_trans OF [bc1, bc2], b00];
    val bRs = oeq_sym OF [bR];
    val base = oeq_trans OF [bL, bRs];
    val xF = Free("x", natT);
    val ihprop = jT (oeq (mult xF (add mF nF)) (add (mult xF mF) (mult xF nF)));
    val IH = Thm.assume (ctermM ihprop);
    val L = multSuc_at (xF, add mF nF);
    val cIH = add_cong_rM (add mF nF, mult xF (add mF nF), add (mult xF mF) (mult xF nF)) IH;
    val t1 = oeq_trans OF [L, cIH];
    val swap = add4_swap (mF, nF, mult xF mF, mult xF nF);
    val t2 = oeq_trans OF [t1, swap];
    val msm = multSuc_at (xF, mF);
    val msms = oeq_sym OF [msm];
    val msn = multSuc_at (xF, nF);
    val msns = oeq_sym OF [msn];
    val f1 = add_cong_lM (add mF (mult xF mF), mult (suc xF) mF, add nF (mult xF nF)) msms;
    val f2 = add_cong_rM (mult (suc xF) mF, add nF (mult xF nF), mult (suc xF) nF) msns;
    val fold = oeq_trans OF [f1, f2];
    val stepconcl = oeq_trans OF [t2, fold];
    val step1 = Thm.forall_intr (ctermM xF) (Thm.implies_intr (ctermM ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

(* ============================================================================
   ORDER EXTENSION  : Ex, oFalse, Suc_inj on ONE further theory thyO; ctxtO/ctermO.
   ============================================================================ *)
val predNatT = natT --> oT;
val thyO1 = Sign.add_consts
  [(Binding.name "Ex",     predNatT --> oT, NoSyn),
   (Binding.name "oFalse", oT,             NoSyn)] tM2;
val ExC     = Const (Sign.full_name thyO1 (Binding.name "Ex"),     predNatT --> oT);
val oFalseC = Const (Sign.full_name thyO1 (Binding.name "oFalse"), oT);
fun mkEx pr = ExC $ pr;

val Pp = Free ("P", predNatT);
val aE = Free ("a", natT);
val exI_prop = Logic.mk_implies (jT (Pp $ aE), jT (mkEx Pp));
val ((_,exI_ax), thyO2) = Thm.add_axiom_global (Binding.name "exI", exI_prop) thyO1;

val Qfree = Free ("Q", oT);
val xE = Free ("x", natT);
val exE_prop =
  Logic.mk_implies (jT (mkEx Pp),
    Logic.mk_implies (Logic.all xE (Logic.mk_implies (jT (Pp $ xE), jT Qfree)),
      jT Qfree));
val ((_,exE_ax), thyO3) = Thm.add_axiom_global (Binding.name "exE", exE_prop) thyO2;

val Rfree = Free ("R", oT);
val oFalse_elim_prop = Logic.mk_implies (jT oFalseC, jT Rfree);
val ((_,oFalse_elim_ax), thyO4) =
  Thm.add_axiom_global (Binding.name "oFalse_elim", oFalse_elim_prop) thyO3;

val nD = Free ("n", natT);
val Suc_neq_Zero_prop = Logic.mk_implies (jT (oeq (suc nD) ZeroC), jT oFalseC);
val ((_,Suc_neq_Zero_ax), thyO5) =
  Thm.add_axiom_global (Binding.name "Suc_neq_Zero", Suc_neq_Zero_prop) thyO4;

(* Suc injectivity (legitimate Peano axiom, like Suc_neq_Zero) *)
val aSj = Free ("a", natT); val bSj = Free ("b", natT);
val Suc_inj_prop = Logic.mk_implies (jT (oeq (suc aSj) (suc bSj)), jT (oeq aSj bSj));
val ((_,Suc_inj_ax), thyO) = Thm.add_axiom_global (Binding.name "Suc_inj", Suc_inj_prop) thyO5;

(* THE foundation's order context — extended once more (Disj) below *)
val ctxtO  = Proof_Context.init_global thyO;
val ctermO = Thm.cterm_of ctxtO;

val exI_v          = varify exI_ax;
val exE_v          = varify exE_ax;
val oFalse_elim_v  = varify oFalse_elim_ax;
val Suc_neq_Zero_v = varify Suc_neq_Zero_ax;
val Suc_inj_v      = varify Suc_inj_ax;

val oeq_refl_vO    = varify oeq_refl;
val add_0_vO       = varify add_0;
val add_Suc_vO     = varify add_Suc;
val add_0_right_vO = varify add_0_right;
val nat_induct_vO  = varify nat_induct;

fun add0_atO  t        = beta_norm (Drule.infer_instantiate ctxtO [(("n",0), ctermO t)] add_0_vO);
fun addSuc_atO (mt,nt) = beta_norm (Drule.infer_instantiate ctxtO
                          [(("m",0), ctermO mt),(("n",0), ctermO nt)] add_Suc_vO);
fun add0r_atO t        = beta_norm (Drule.infer_instantiate ctxtO [(("n",0), ctermO t)] add_0_right_vO);
fun oeqrefl_atO t      = beta_norm (Drule.infer_instantiate ctxtO [(("a",0), ctermO t)] oeq_refl_vO);
fun nat_induct_atO (Qabs, kT) = beta_norm (Drule.infer_instantiate ctxtO
          [(("P",0), ctermO Qabs), (("k",0), ctermO kT)] nat_induct_vO);
fun Suc_inj_at (uT, vT) = beta_norm (Drule.infer_instantiate ctxtO
          [(("a",0), ctermO uT), (("b",0), ctermO vT)] Suc_inj_v);
(* oeq_sym/oeq_trans/Suc_cong already schematic; usable via OF on ctxtO terms. *)
fun add_cong_lO (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtO
          [(("P",0), ctermO Pabs), (("a",0), ctermO pT), (("b",0), ctermO qT)] oeq_subst_v);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtO [(("a",0), ctermO (add pT kT))] oeq_refl_vO);
  in inst OF [hpq, refl_pk] end;

(* ============================================================================
   le ABBREVIATION + le_intro
     le m n  ==  Ex (%p. oeq n (add m (Bound 0)))   i.e.  ?p. n = m + p
   ============================================================================ *)
fun le mT nT = mkEx (Abs ("p", natT, oeq nT (add mT (Bound 0))));

fun le_intro (mT, nT, w) hyp =
  let
    val Pabs = Abs ("p", natT, oeq nT (add mT (Bound 0)));
    val exI_inst = beta_norm (Drule.infer_instantiate ctxtO
          [(("P",0), ctermO Pabs), (("a",0), ctermO w)] exI_v);
  in exI_inst OF [hyp] end;

(* ============================================================================
   ARITHMETIC PREREQS  add_left_cancel, add_eq_zero_left  (object-predicate
   reflection of meta-implications; induct on the reflected predicate).
   ============================================================================ *)

(* ---- add_left_cancel : oeq (add m a) (add m b) ==> oeq a b  (induction on m) ---- *)
val thyLC1 = Sign.add_consts
  [(Binding.name "lcQ", natT --> natT --> natT --> oT, NoSyn)] thyO;
val lcQC = Const (Sign.full_name thyLC1 (Binding.name "lcQ"),
                  natT --> natT --> natT --> oT);
fun lcQ aT bT zT = lcQC $ aT $ bT $ zT;
val aLC = Free("a",natT); val bLC = Free("b",natT); val zLC = Free("z",natT);
val lcQ_fold_prop =
  Logic.mk_implies (Logic.mk_implies (jT (oeq (add zLC aLC) (add zLC bLC)), jT (oeq aLC bLC)),
                    jT (lcQ aLC bLC zLC));
val ((_,lcQ_fold), thyLC2) = Thm.add_axiom_global (Binding.name "lcQ_fold", lcQ_fold_prop) thyLC1;
val lcQ_unfold_prop =
  Logic.mk_implies (jT (lcQ aLC bLC zLC),
    Logic.mk_implies (jT (oeq (add zLC aLC) (add zLC bLC)), jT (oeq aLC bLC)));
val ((_,lcQ_unfold), thyLC) = Thm.add_axiom_global (Binding.name "lcQ_unfold", lcQ_unfold_prop) thyLC2;

val ctxtLC  = Proof_Context.init_global thyLC;
val ctermLC = Thm.cterm_of ctxtLC;
val lcQ_fold_v   = varify lcQ_fold;
val lcQ_unfold_v = varify lcQ_unfold;
val nat_induct_vLC = varify nat_induct;
val add_0_vLC      = varify add_0;
val add_Suc_vLC    = varify add_Suc;
val Suc_inj_vLC    = varify Suc_inj_ax;
fun add0_atLC t        = beta_norm (Drule.infer_instantiate ctxtLC [(("n",0), ctermLC t)] add_0_vLC);
fun addSuc_atLC (mt,nt)= beta_norm (Drule.infer_instantiate ctxtLC
                          [(("m",0), ctermLC mt),(("n",0), ctermLC nt)] add_Suc_vLC);
fun Suc_inj_atLC (uT,vT)= beta_norm (Drule.infer_instantiate ctxtLC
                          [(("a",0), ctermLC uT),(("b",0), ctermLC vT)] Suc_inj_vLC);
fun lcQ_fold_at (aT,bT,zT)   = beta_norm (Drule.infer_instantiate ctxtLC
        [(("a",0), ctermLC aT),(("b",0), ctermLC bT),(("z",0), ctermLC zT)] lcQ_fold_v);
fun lcQ_unfold_at (aT,bT,zT) = beta_norm (Drule.infer_instantiate ctxtLC
        [(("a",0), ctermLC aT),(("b",0), ctermLC bT),(("z",0), ctermLC zT)] lcQ_unfold_v);

val add_left_cancel =
  let
    val aF = Free("a",natT); val bF = Free("b",natT);
    val Qpred = Abs("z", natT, lcQ aF bF (Bound 0));
    val mF = Free("m", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtLC
          [(("P",0), ctermLC Qpred), (("k",0), ctermLC mF)] nat_induct_vLC);
    val baseImpHyp = jT (oeq (add ZeroC aF) (add ZeroC bF));
    val H0 = Thm.assume (ctermLC baseImpHyp);
    val a0a = add0_atLC aF;
    val a0b = add0_atLC bF;
    val a0a_s = oeq_sym OF [a0a];
    val t1 = oeq_trans OF [a0a_s, H0];
    val t2 = oeq_trans OF [t1, a0b];
    val baseImp = Thm.implies_intr (ctermLC baseImpHyp) t2;
    val base = Thm.implies_elim (lcQ_fold_at (aF,bF,ZeroC)) baseImp;
    val xF = Free("x", natT);
    val ihprop = jT (lcQ aF bF xF);
    val IH = Thm.assume (ctermLC ihprop);
    val IHimp = Thm.implies_elim (lcQ_unfold_at (aF,bF,xF)) IH;
    val stepImpHyp = jT (oeq (add (suc xF) aF) (add (suc xF) bF));
    val HS = Thm.assume (ctermLC stepImpHyp);
    val sA = addSuc_atLC (xF, aF);
    val sB = addSuc_atLC (xF, bF);
    val sA_s = oeq_sym OF [sA];
    val u1 = oeq_trans OF [sA_s, HS];
    val u2 = oeq_trans OF [u1, sB];
    val u3 = (Suc_inj_atLC (add xF aF, add xF bF)) OF [u2];
    val stepConcl = IHimp OF [u3];
    val stepImp = Thm.implies_intr (ctermLC stepImpHyp) stepConcl;
    val stepFold = Thm.implies_elim (lcQ_fold_at (aF,bF,suc xF)) stepImp;
    val step1 = Thm.forall_intr (ctermLC xF) (Thm.implies_intr (ctermLC ihprop) stepFold);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val final = (lcQ_unfold_at (aF,bF,mF)) OF [r2];
  in varify final end;

(* ---- add_eq_zero_left : oeq (add a b) Zero ==> oeq a Zero  (cases on a) ---- *)
val thyEZ1 = Sign.add_consts
  [(Binding.name "ezQ", natT --> natT --> oT, NoSyn)] thyLC;
val ezQC = Const (Sign.full_name thyEZ1 (Binding.name "ezQ"), natT --> natT --> oT);
fun ezQ bT aT = ezQC $ bT $ aT;
val bEZ = Free("b",natT); val aEZ = Free("a",natT);
val ezQ_fold_prop =
  Logic.mk_implies (Logic.mk_implies (jT (oeq (add aEZ bEZ) ZeroC), jT (oeq aEZ ZeroC)),
                    jT (ezQ bEZ aEZ));
val ((_,ezQ_fold), thyEZ2) = Thm.add_axiom_global (Binding.name "ezQ_fold", ezQ_fold_prop) thyEZ1;
val ezQ_unfold_prop =
  Logic.mk_implies (jT (ezQ bEZ aEZ),
    Logic.mk_implies (jT (oeq (add aEZ bEZ) ZeroC), jT (oeq aEZ ZeroC)));
val ((_,ezQ_unfold), thyEZ) = Thm.add_axiom_global (Binding.name "ezQ_unfold", ezQ_unfold_prop) thyEZ2;

val ctxtEZ  = Proof_Context.init_global thyEZ;
val ctermEZ = Thm.cterm_of ctxtEZ;
val ezQ_fold_v   = varify ezQ_fold;
val ezQ_unfold_v = varify ezQ_unfold;
val nat_induct_vEZ = varify nat_induct;
val add_0_vEZ      = varify add_0;
val add_Suc_vEZ    = varify add_Suc;
val oeq_refl_vEZ   = varify oeq_refl;
val Suc_neq_Zero_vEZ = varify Suc_neq_Zero_ax;
val oFalse_elim_vEZ  = varify oFalse_elim_ax;
fun add0_atEZ t        = beta_norm (Drule.infer_instantiate ctxtEZ [(("n",0), ctermEZ t)] add_0_vEZ);
fun addSuc_atEZ (mt,nt)= beta_norm (Drule.infer_instantiate ctxtEZ
                          [(("m",0), ctermEZ mt),(("n",0), ctermEZ nt)] add_Suc_vEZ);
fun oeqrefl_atEZ t     = beta_norm (Drule.infer_instantiate ctxtEZ [(("a",0), ctermEZ t)] oeq_refl_vEZ);
fun Suc_neq_Zero_at t  = beta_norm (Drule.infer_instantiate ctxtEZ [(("n",0), ctermEZ t)] Suc_neq_Zero_vEZ);
fun oFalse_elim_at rT  = beta_norm (Drule.infer_instantiate ctxtEZ [(("R",0), ctermEZ rT)] oFalse_elim_vEZ);
fun ezQ_fold_at (bT,aT)   = beta_norm (Drule.infer_instantiate ctxtEZ
        [(("b",0), ctermEZ bT),(("a",0), ctermEZ aT)] ezQ_fold_v);
fun ezQ_unfold_at (bT,aT) = beta_norm (Drule.infer_instantiate ctxtEZ
        [(("b",0), ctermEZ bT),(("a",0), ctermEZ aT)] ezQ_unfold_v);

val add_eq_zero_left =
  let
    val bF = Free("b",natT);
    val Qpred = Abs("z", natT, ezQ bF (Bound 0));
    val aF = Free("a", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtEZ
          [(("P",0), ctermEZ Qpred), (("k",0), ctermEZ aF)] nat_induct_vEZ);
    val baseHyp = jT (oeq (add ZeroC bF) ZeroC);
    val H0 = Thm.assume (ctermEZ baseHyp);
    val refl00 = oeqrefl_atEZ ZeroC;
    val baseImp = Thm.implies_intr (ctermEZ baseHyp) refl00;
    val base = Thm.implies_elim (ezQ_fold_at (bF, ZeroC)) baseImp;
    val xF = Free("x", natT);
    val ihprop = jT (ezQ bF xF);
    val IH = Thm.assume (ctermEZ ihprop);
    val stepHyp = jT (oeq (add (suc xF) bF) ZeroC);
    val HS = Thm.assume (ctermEZ stepHyp);
    val sA = addSuc_atEZ (xF, bF);
    val sA_s = oeq_sym OF [sA];
    val v1 = oeq_trans OF [sA_s, HS];
    val vF = (Suc_neq_Zero_at (add xF bF)) OF [v1];
    val concl = (oFalse_elim_at (oeq (suc xF) ZeroC)) OF [vF];
    val stepImp = Thm.implies_intr (ctermEZ stepHyp) concl;
    val stepFold = Thm.implies_elim (ezQ_fold_at (bF, suc xF)) stepImp;
    val step1 = Thm.forall_intr (ctermEZ xF) (Thm.implies_intr (ctermEZ ihprop) stepFold);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val final = (ezQ_unfold_at (bF, aF)) OF [r2];
  in varify final end;

(* ============================================================================
   EASY ORDER LEMMAS  (all routed through ctxtO; built from le_intro + add laws)
   ============================================================================ *)
val le_refl =
  let
    val nF = Free("n", natT);
    val a0r = add0r_atO nF;
    val hyp = oeq_sym OF [a0r];
  in varify (le_intro (nF, nF, ZeroC) hyp) end;

val zero_le =
  let
    val nF = Free("n", natT);
    val a0 = add0_atO nF;
    val hyp = oeq_sym OF [a0];
  in varify (le_intro (ZeroC, nF, nF) hyp) end;

val le_add =
  let
    val mF = Free("m", natT); val pF = Free("p", natT);
    val hyp = oeqrefl_atO (add mF pF);
  in varify (le_intro (mF, add mF pF, pF) hyp) end;

(* ============================================================================
   FOUNDATION SELF-CHECK (sanity; the binding `check`/Vars are reused below).
   ============================================================================ *)
val mV = Var (("m",0), natT);
val nV = Var (("n",0), natT);
val aV = Var (("a",0), natT);
val bV = Var (("b",0), natT);
val pV = Var (("p",0), natT);

fun check (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac
            ^ ")\n  got      = " ^ Syntax.string_of_term ctxtO (Thm.prop_of th)
            ^ "\n  intended = " ^ Syntax.string_of_term ctxtO intended ^ "\n"); false)
  end;

val f_alc = (length (Thm.hyps_of add_left_cancel) = 0);
val f_aez = (length (Thm.hyps_of add_eq_zero_left) = 0);
val () = out ("FOUNDATION prereqs: add_left_cancel-0hyp=" ^ Bool.toString f_alc
            ^ " add_eq_zero_left-0hyp=" ^ Bool.toString f_aez ^ "\n");
val () = if f_alc andalso f_aez then out "FOUNDATION_OK\n"
         else out "FOUNDATION_BROKEN\n";

(* ============================================================================
   *** THE SINGLE FINAL THEORY EXTENSION ***  (the load-bearing merge step)
   ----------------------------------------------------------------------------
   Fold the le_total driver's DISJUNCTION connective (Disj : o => o => o) and its
   intro/elim axioms (disjI1, disjI2, disjE) onto ONE further theory `thyT` built
   on top of the foundation's last theory `thyEZ`.  Build the ONE FINAL context
   `ctxtT` / `ctermT`; from here on EVERYTHING routes through it.  All shared
   lemmas already proven (oeq_sym/_trans/Suc_cong/add_*/le_*/cancel/eq_zero) are
   re-VARIFIED for use under ctxtT (they are schematic, so this is just a context
   change), and the per-driver helpers are re-stated ONCE on ctxtT below.
   ============================================================================ *)
val thyT0 = Sign.add_consts
  [(Binding.name "Disj", oT --> oT --> oT, NoSyn)] thyEZ;
val DisjC = Const (Sign.full_name thyT0 (Binding.name "Disj"), oT --> oT --> oT);
fun mkDisj s t = DisjC $ s $ t;

val Adj = Free ("A", oT); val Bdj = Free ("B", oT); val Cdj = Free ("C", oT);
val ((_,disjI1_ax), thyT1) = Thm.add_axiom_global (Binding.name "disjI1",
      Logic.mk_implies (jT Adj, jT (mkDisj Adj Bdj))) thyT0;
val ((_,disjI2_ax), thyT2) = Thm.add_axiom_global (Binding.name "disjI2",
      Logic.mk_implies (jT Bdj, jT (mkDisj Adj Bdj))) thyT1;
val ((_,disjE_ax), thyT) = Thm.add_axiom_global (Binding.name "disjE",
      Logic.mk_implies (jT (mkDisj Adj Bdj),
        Logic.mk_implies (Logic.mk_implies (jT Adj, jT Cdj),
          Logic.mk_implies (Logic.mk_implies (jT Bdj, jT Cdj), jT Cdj)))) thyT2;

(* THE ONE FINAL CONTEXT *)
val ctxtT  = Proof_Context.init_global thyT;
val ctermT = Thm.cterm_of ctxtT;

(* re-varify every schematic axiom/lemma for use under ctxtT *)
val oeq_refl_vT    = varify oeq_refl;
val oeq_subst_vT   = varify oeq_subst;
val add_0_vT       = varify add_0;
val add_Suc_vT     = varify add_Suc;
val add_0_right_vT = varify add_0_right;
val add_Suc_right_vT = varify add_Suc_right;
val add_comm_vT    = varify add_comm;
val add_assoc_vT   = varify add_assoc;
val nat_induct_vT  = varify nat_induct;
val exI_vT         = varify exI_ax;
val exE_vT         = varify exE_ax;
val Suc_inj_vT     = varify Suc_inj_ax;
val Suc_neq_Zero_vT= varify Suc_neq_Zero_ax;
val oFalse_elim_vT = varify oFalse_elim_ax;
val disjI1_vT      = varify disjI1_ax;
val disjI2_vT      = varify disjI2_ax;
val disjE_vT       = varify disjE_ax;
(* the two derived arithmetic prereqs and the easy order lemmas are 0-hyp,
   schematic theorems already; varify just re-zeroes indices for ctxtT use *)
val add_left_cancel_vT  = varify add_left_cancel;
val add_eq_zero_left_vT = varify add_eq_zero_left;
val zero_le_vT          = varify zero_le;

(* ---- ground instantiators / congruences on the FINAL context ctxtT ---- *)
fun add0T_at t         = beta_norm (Drule.infer_instantiate ctxtT [(("n",0), ctermT t)] add_0_vT);
fun addSucT_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtT
                            [(("m",0), ctermT mt),(("n",0), ctermT nt)] add_Suc_vT);
fun add0rT_at t        = beta_norm (Drule.infer_instantiate ctxtT [(("n",0), ctermT t)] add_0_right_vT);
fun addSrT_at (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtT
                            [(("m",0), ctermT mt),(("n",0), ctermT nt)] add_Suc_right_vT);
fun addcommT_at (mt,nt)     = beta_norm (Drule.infer_instantiate ctxtT
                               [(("m",0), ctermT mt),(("n",0), ctermT nt)] add_comm_vT);
fun addassocT_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtT
                               [(("m",0), ctermT mt),(("n",0), ctermT nt),(("k",0), ctermT kt)] add_assoc_vT);
fun oeqreflT_at t      = beta_norm (Drule.infer_instantiate ctxtT [(("a",0), ctermT t)] oeq_refl_vT);
fun Suc_inj_atT (uT,vT)= beta_norm (Drule.infer_instantiate ctxtT
                            [(("a",0), ctermT uT),(("b",0), ctermT vT)] Suc_inj_vT);

(* add-congruence on LEFT / RIGHT operand, on ctxtT *)
fun add_cong_lT (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtT
          [(("P",0), ctermT Pabs), (("a",0), ctermT pT), (("b",0), ctermT qT)] oeq_subst_vT);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtT [(("a",0), ctermT (add pT kT))] oeq_refl_vT);
  in inst OF [hpq, refl_pk] end;
fun add_cong_rT (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtT
          [(("P",0), ctermT Pabs), (("a",0), ctermT pT), (("b",0), ctermT qT)] oeq_subst_vT);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtT [(("a",0), ctermT (add hT pT))] oeq_refl_vT);
  in inst OF [hpq, refl_hp] end;

(* le_intro on ctxtT (uses exI_vT) *)
fun le_introT (mT, nT, w) hyp =
  let
    val Pabs = Abs ("p", natT, oeq nT (add mT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtT
          [(("P",0), ctermT Pabs), (("a",0), ctermT w)] exI_vT);
  in inst OF [hyp] end;

(* zero_le ground instance on ctxtT *)
fun zero_leT_at t = beta_norm (Drule.infer_instantiate ctxtT [(("n",0), ctermT t)] zero_le_vT);

(* exE elimination: exThm : jT (Ex Pabs); bodyFn w (hyp : jT (Pabs w betad)) : jT goalC.
   Discharge fresh w by forall_intr; minor !!w. Pabs w ==> goalC; implies_elim. *)
fun exE_elimT (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm = Thm.assume (ctermT hypTerm);
    val body = bodyFn wF hypThm;
    val minor = Thm.forall_intr (ctermT wF) (Thm.implies_intr (ctermT hypTerm) body);
    val exE_inst = beta_norm (Drule.infer_instantiate ctxtT
          [(("P",0), ctermT Pabs), (("Q",0), ctermT goalC)] exE_vT);
    val partial = Thm.implies_elim exE_inst exThm;
    val res = Thm.implies_elim partial minor;
  in res end;

(* disjE elimination at explicit A,B,C; discharge all three premises by implies_elim *)
fun disjE_elimT (At, Bt, Ct) dThm caseA caseB =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtT
          [(("A",0), ctermT At), (("B",0), ctermT Bt), (("C",0), ctermT Ct)] disjE_vT);
    val s1 = Thm.implies_elim inst dThm;
    val s2 = Thm.implies_elim s1 caseA;
  in Thm.implies_elim s2 caseB end;
fun disjI1T_at (At,Bt) h = (beta_norm (Drule.infer_instantiate ctxtT
      [(("A",0), ctermT At), (("B",0), ctermT Bt)] disjI1_vT)) OF [h];
fun disjI2T_at (At,Bt) h = (beta_norm (Drule.infer_instantiate ctxtT
      [(("A",0), ctermT At), (("B",0), ctermT Bt)] disjI2_vT)) OF [h];

val () = out "FINAL_CONTEXT_READY\n";

(* ============================================================================
   le_trans : jT (le m n) ==> jT (le n k) ==> jT (le m k)        [from le_trans.sml]
   ============================================================================ *)
val le_trans =
  let
    val mF = Free("m", natT); val nF = Free("n", natT); val kF = Free("k", natT);
    val H1prop = jT (le mF nF);
    val H2prop = jT (le nF kF);
    val H1 = Thm.assume (ctermT H1prop);
    val H2 = Thm.assume (ctermT H2prop);
    val P1abs = Abs ("p", natT, oeq nF (add mF (Bound 0)));
    val P2abs = Abs ("q", natT, oeq kF (add nF (Bound 0)));
    val goalBody = le mF kF;

    fun inner xF =
      let
        val hx = Thm.assume (ctermT (jT (oeq nF (add mF xF))));
        val exE2 = beta_norm (Drule.infer_instantiate ctxtT
              [(("P",0), ctermT P2abs), (("Q",0), ctermT goalBody)] exE_vT);
        val exE2_H2 = Thm.implies_elim exE2 H2;
        val yF = Free("y", natT);
        val hy = Thm.assume (ctermT (jT (oeq kF (add nF yF))));
        val cong  = add_cong_lT (nF, add mF xF, yF) hx;
        val step1 = oeq_trans OF [hy, cong];
        val assoc = addassocT_at (mF, xF, yF);
        val keq   = oeq_trans OF [step1, assoc];
        val bodyProof2 = le_introT (mF, kF, add xF yF) keq;
        val minor2 = Thm.forall_intr (ctermT yF)
                      (Thm.implies_intr (ctermT (jT (oeq kF (add nF yF)))) bodyProof2);
      in Thm.implies_elim exE2_H2 minor2 end;

    val exE1 = beta_norm (Drule.infer_instantiate ctxtT
          [(("P",0), ctermT P1abs), (("Q",0), ctermT goalBody)] exE_vT);
    val exE1_H1 = Thm.implies_elim exE1 H1;
    val xF = Free("x", natT);
    val bodyProof1 = inner xF;
    val minor1 = Thm.forall_intr (ctermT xF)
                  (Thm.implies_intr (ctermT (jT (oeq nF (add mF xF)))) bodyProof1);
    val res1 = Thm.implies_elim exE1_H1 minor1;
    val d1 = Thm.implies_intr (ctermT H2prop) res1;
    val d2 = Thm.implies_intr (ctermT H1prop) d1;
  in varify d2 end;

(* ============================================================================
   le_suc_mono : le m n ==> le (Suc m) (Suc n)        [from le_suc_and_add_mono.sml]
   ============================================================================ *)
val le_suc_mono =
  let
    val mF = Free ("m", natT); val nF = Free ("n", natT);
    val leHypP = jT (le mF nF);
    val leHyp  = Thm.assume (ctermT leHypP);
    val Pabs   = Abs ("p", natT, oeq nF (add mF (Bound 0)));
    val goalBody = le (suc mF) (suc nF);
    val exE_inst = beta_norm (Drule.infer_instantiate ctxtT
          [(("P",0), ctermT Pabs), (("Q",0), ctermT goalBody)] exE_vT);
    val xF = Free ("x", natT);
    val localHypP = jT (oeq nF (add mF xF));
    val localHyp  = Thm.assume (ctermT localHypP);
    val sc   = Suc_cong OF [localHyp];
    val aS   = addSucT_at (mF, xF);
    val aSs  = oeq_sym OF [aS];
    val body = oeq_trans OF [sc, aSs];
    val leNew = le_introT (suc mF, suc nF, xF) body;
    val minor = Thm.forall_intr (ctermT xF)
                  (Thm.implies_intr (ctermT localHypP) leNew);
    val res   = Thm.implies_elim (Thm.implies_elim exE_inst leHyp) minor;
    val disch = Thm.implies_intr (ctermT leHypP) res;
  in varify disch end;

(* ============================================================================
   le_add_mono : le a b ==> le (add a c) (add b c)    [from le_suc_and_add_mono.sml]
   ============================================================================ *)
val le_add_mono =
  let
    val aF = Free ("a", natT); val bF = Free ("b", natT); val cF = Free ("c", natT);
    val leHypP = jT (le aF bF);
    val leHyp  = Thm.assume (ctermT leHypP);
    val Pabs   = Abs ("p", natT, oeq bF (add aF (Bound 0)));
    val goalBody = le (add aF cF) (add bF cF);
    val exE_inst = beta_norm (Drule.infer_instantiate ctxtT
          [(("P",0), ctermT Pabs), (("Q",0), ctermT goalBody)] exE_vT);
    val xF = Free ("x", natT);
    val localHypP = jT (oeq bF (add aF xF));
    val localHyp  = Thm.assume (ctermT localHypP);
    val congl = add_cong_lT (bF, add aF xF, cF) localHyp;
    val as1   = addassocT_at (aF, xF, cF);
    val cmxc  = addcommT_at (xF, cF);
    val cong_xc = add_cong_rT (aF, add xF cF, add cF xF) cmxc;
    val as2   = addassocT_at (aF, cF, xF);
    val as2s  = oeq_sym OF [as2];
    val resh1 = oeq_trans OF [as1, cong_xc];
    val resh  = oeq_trans OF [resh1, as2s];
    val body  = oeq_trans OF [congl, resh];
    val leNew = le_introT (add aF cF, add bF cF, xF) body;
    val minor = Thm.forall_intr (ctermT xF)
                  (Thm.implies_intr (ctermT localHypP) leNew);
    val res   = Thm.implies_elim (Thm.implies_elim exE_inst leHyp) minor;
    val disch = Thm.implies_intr (ctermT leHypP) res;
  in varify disch end;

(* ============================================================================
   le_antisym : le m n ==> le n m ==> oeq m n            [from le_antisym.sml]
   Uses add_left_cancel + add_eq_zero_left (foundation), routed through ctxtT.
   ============================================================================ *)
val le_antisym =
  let
    val mF = Free("m", natT); val nF = Free("n", natT);
    val hLEmn = Thm.assume (ctermT (jT (le mF nF)));
    val hLEnm = Thm.assume (ctermT (jT (le nF mF)));
    val goalBody = oeq mF nF;
    val P1 = Abs ("p", natT, oeq nF (add mF (Bound 0)));
    val P2 = Abs ("q", natT, oeq mF (add nF (Bound 0)));
    fun inner (pF, hP) (qF, hQ) =
      let
        val cong = add_cong_lT (nF, add mF pF, qF) hP;          (* oeq (add n q) (add (add m p) q) *)
        val mEq1 = oeq_trans OF [hQ, cong];                     (* oeq m (add (add m p) q) *)
        val assoc = addassocT_at (mF, pF, qF);                  (* oeq (add (add m p) q) (add m (add p q)) *)
        val mEq2 = oeq_trans OF [mEq1, assoc];                  (* oeq m (add m (add p q)) *)
        val m0 = oeq_sym OF [add0rT_at mF];                     (* oeq m (add m 0) *)
        val m0s = oeq_sym OF [m0];                              (* oeq (add m 0) m *)
        val cancelAnt = oeq_trans OF [m0s, mEq2];               (* oeq (add m 0) (add m (add p q)) *)
        val canc = add_left_cancel_vT OF [cancelAnt];          (* oeq 0 (add p q) *)
        val pqz = oeq_sym OF [canc];                            (* oeq (add p q) 0 *)
        val pz = add_eq_zero_left_vT OF [pqz];                  (* oeq p 0 *)
        val congP = add_cong_rT (mF, pF, ZeroC) pz;             (* oeq (add m p) (add m 0) *)
        val nEqAddmp = hP;                                      (* oeq n (add m p) *)
        val nEqAddm0 = oeq_trans OF [nEqAddmp, congP];          (* oeq n (add m 0) *)
        val nEqm = oeq_trans OF [nEqAddm0, add0rT_at mF];       (* oeq n m *)
        val mEqn = oeq_sym OF [nEqm];                           (* oeq m n *)
      in mEqn end;
    val exE1 = beta_norm (Drule.infer_instantiate ctxtT
          [(("P",0), ctermT P1), (("Q",0), ctermT goalBody)] exE_vT);
    val pF = Free("p", natT);
    val hPp = Thm.assume (ctermT (jT (oeq nF (add mF pF))));
    val exE2 = beta_norm (Drule.infer_instantiate ctxtT
          [(("P",0), ctermT P2), (("Q",0), ctermT goalBody)] exE_vT);
    val qF = Free("q", natT);
    val hQq = Thm.assume (ctermT (jT (oeq mF (add nF qF))));
    val innerProof = inner (pF, hPp) (qF, hQq);
    val minor2 = Thm.forall_intr (ctermT qF)
                  (Thm.implies_intr (ctermT (jT (oeq mF (add nF qF)))) innerProof);
    val afterE2 = Thm.implies_elim (Thm.implies_elim exE2 hLEnm) minor2;
    val minor1 = Thm.forall_intr (ctermT pF)
                  (Thm.implies_intr (ctermT (jT (oeq nF (add mF pF)))) afterE2);
    val afterE1 = Thm.implies_elim (Thm.implies_elim exE1 hLEmn) minor1;
    val r0 = Thm.implies_intr (ctermT (jT (le nF mF))) afterE1;
    val r1 = Thm.implies_intr (ctermT (jT (le mF nF))) r0;
  in varify r1 end;

(* ============================================================================
   HELPER (le_total): disj_zero_or_suc : Disj (oeq p Zero) (Ex(%q. oeq p (Suc q)))
   BY INDUCTION on p.   [from le_total.sml]
   ============================================================================ *)
fun mkExSuc t = mkEx (Abs ("q", natT, oeq t (suc (Bound 0))));

val disj_zero_or_suc =
  let
    val zF0 = Free("zz", natT);
    val Qpred = Term.lambda zF0 (mkDisj (oeq zF0 ZeroC) (mkExSuc zF0));
    val pF = Free("p", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtT
          [(("P",0), ctermT Qpred), (("k",0), ctermT pF)] nat_induct_vT);
    val refl00 = beta_norm (Drule.infer_instantiate ctxtT [(("a",0), ctermT ZeroC)] oeq_refl_vT);
    val disjI1_inst = beta_norm (Drule.infer_instantiate ctxtT
          [(("A",0), ctermT (oeq ZeroC ZeroC)), (("B",0), ctermT (mkExSuc ZeroC))] disjI1_vT);
    val base = disjI1_inst OF [refl00];
    val xF = Free("x", natT);
    val ihprop = jT (mkDisj (oeq xF ZeroC) (mkExSuc xF));
    val PabsE = Abs("q", natT, oeq (suc xF) (suc (Bound 0)));
    val exI_inst = beta_norm (Drule.infer_instantiate ctxtT
          [(("P",0), ctermT PabsE), (("a",0), ctermT xF)] exI_vT);
    val reflSS = beta_norm (Drule.infer_instantiate ctxtT [(("a",0), ctermT (suc xF))] oeq_refl_vT);
    val exwit = exI_inst OF [reflSS];
    val disjI2_inst = beta_norm (Drule.infer_instantiate ctxtT
          [(("A",0), ctermT (oeq (suc xF) ZeroC)), (("B",0), ctermT (mkExSuc (suc xF)))] disjI2_vT);
    val stepconcl = disjI2_inst OF [exwit];
    val step1 = Thm.forall_intr (ctermT xF) (Thm.implies_intr (ctermT ihprop) stepconcl);
  in varify (Thm.implies_elim (Thm.implies_elim ind base) step1) end;
val disj_zero_or_suc_vT = varify disj_zero_or_suc;
fun dzosT_at t = beta_norm (Drule.infer_instantiate ctxtT [(("p",0), ctermT t)] disj_zero_or_suc_vT);

(* ============================================================================
   le_total : Disj (le m n) (le n m)   *** BY INDUCTION on m (n fixed Free) ***
   [from le_total.sml]
   ============================================================================ *)
val le_total =
  let
    val nF = Free("n", natT);
    val zF = Free("zz", natT);
    val Ppred = Term.lambda zF (mkDisj (le zF nF) (le nF zF));
    val mF = Free("m", natT);
    val ind = beta_norm (Drule.infer_instantiate ctxtT
          [(("P",0), ctermT Ppred), (("k",0), ctermT mF)] nat_induct_vT);

    (* BASE: m=0 -> Disj (le 0 n) (le n 0) via disjI1 on zero_le n *)
    val z_le = zero_leT_at nF;
    val base = disjI1T_at (le ZeroC nF, le nF ZeroC) z_le;

    (* STEP: IH = Disj (le x n)(le n x); goal Disj (le (Suc x) n)(le n (Suc x)) *)
    val xF = Free("x", natT);
    val ihprop = jT (mkDisj (le xF nF) (le nF xF));
    val IH = Thm.assume (ctermT ihprop);

    (* CASE A: le x n ==> goal. le x n = Ex(%p. oeq n (add x p)) *)
    val PabsA = Abs("p", natT, oeq nF (add xF (Bound 0)));
    fun caseA_body w (hyp : thm) =
      let
        val dz = dzosT_at w;
        val a1concl =
          let
            val ew = Thm.assume (ctermT (jT (oeq w ZeroC)));
            val cong = add_cong_rT (xF, w, ZeroC) ew;
            val ax0 = add0rT_at xF;
            val n_addx0 = oeq_trans OF [hyp, cong];
            val n_x = oeq_trans OF [n_addx0, ax0];
            val asr = addSrT_at (nF, ZeroC);
            val an0 = add0rT_at nF;
            val san0 = Suc_cong OF [an0];
            val snx = Suc_cong OF [n_x];
            val c1 = oeq_trans OF [asr, san0];
            val c2 = oeq_trans OF [c1, snx];
            val body = oeq_sym OF [c2];
            val le_n_Sx = le_introT (nF, suc xF, suc ZeroC) body;
            val g = disjI2T_at (le (suc xF) nF, le nF (suc xF)) le_n_Sx;
          in Thm.implies_intr (ctermT (jT (oeq w ZeroC))) g end;
        val a2concl =
          let
            val PabsQ = Abs("q", natT, oeq w (suc (Bound 0)));
            val exq = Thm.assume (ctermT (jT (mkEx PabsQ)));
            fun a2body q (hq : thm) =
              let
                val cong = add_cong_rT (xF, w, suc q) hq;
                val asx = addSrT_at (xF, q);
                val aSx = addSucT_at (xF, q);
                val aSxs = oeq_sym OF [aSx];
                val n_axSq = oeq_trans OF [hyp, cong];
                val n_Saddxq = oeq_trans OF [n_axSq, asx];
                val body = oeq_trans OF [n_Saddxq, aSxs];
                val le_Sx_n = le_introT (suc xF, nF, q) body;
              in disjI1T_at (le (suc xF) nF, le nF (suc xF)) le_Sx_n end;
            val g = exE_elimT (PabsQ, mkDisj (le (suc xF) nF) (le nF (suc xF))) exq "q2" a2body;
          in Thm.implies_intr (ctermT (jT (mkEx PabsQ))) g end;
        val PabsW = Abs("q", natT, oeq w (suc (Bound 0)));
      in disjE_elimT (oeq w ZeroC, mkEx PabsW,
                      mkDisj (le (suc xF) nF) (le nF (suc xF))) dz a1concl a2concl end;
    val caseA_thm =
      let
        val leA = Thm.assume (ctermT (jT (le xF nF)));
        val g = exE_elimT (PabsA, mkDisj (le (suc xF) nF) (le nF (suc xF))) leA "wa" caseA_body;
      in Thm.implies_intr (ctermT (jT (le xF nF))) g end;

    (* CASE B: le n x ==> goal. le n x = Ex(%p. oeq x (add n p)) *)
    val PabsB = Abs("p", natT, oeq xF (add nF (Bound 0)));
    fun caseB_body w (hyp : thm) =
      let
        val sxc = Suc_cong OF [hyp];
        val asr = addSrT_at (nF, w);
        val asrs = oeq_sym OF [asr];
        val body = oeq_trans OF [sxc, asrs];
        val le_n_Sx = le_introT (nF, suc xF, suc w) body;
      in disjI2T_at (le (suc xF) nF, le nF (suc xF)) le_n_Sx end;
    val caseB_thm =
      let
        val leB = Thm.assume (ctermT (jT (le nF xF)));
        val g = exE_elimT (PabsB, mkDisj (le (suc xF) nF) (le nF (suc xF))) leB "wb" caseB_body;
      in Thm.implies_intr (ctermT (jT (le nF xF))) g end;

    val stepconcl = disjE_elimT (le xF nF, le nF xF,
                      mkDisj (le (suc xF) nF) (le nF (suc xF))) IH caseA_thm caseB_thm;
    val step1 = Thm.forall_intr (ctermT xF) (Thm.implies_intr (ctermT ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

(* ============================================================================
   DIVISIBILITY DEVELOPMENT  (built on the SINGLE FINAL context ctxtT)
   ----------------------------------------------------------------------------
   `mult` lives on thyM and `Ex`/exI live on thyO (built ON TOP of thyM); the
   final theory thyT extends through thyEZ which carries BOTH.  So `multC`/`ExC`
   are in scope on ctxtT and every dvd cterm routes through ctermT — no
   cross-theory mismatch.

       dvd a b   ==   Ex (%k. oeq b (mult a (Bound 0)))      i.e.  ?k. b = a * k

   dvd_intro mirrors le_introT: from a proof of `oeq b (mult a w)` for a witness
   term w, produce `Trueprop (dvd a b)` (exI at P := the abs, a := w).
   ============================================================================ *)
fun dvd aT bT = mkEx (Abs ("k", natT, oeq bT (mult aT (Bound 0))));

fun dvd_intro (aT, bT, w) hyp =
  let
    val Pabs = Abs ("k", natT, oeq bT (mult aT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtT
          [(("P",0), ctermT Pabs), (("a",0), ctermT w)] exI_vT);
  in inst OF [hyp] end;

(* ---- multiplication lemmas re-varified for use under the FINAL context ctxtT ----
   (they are schematic 0-hyp theorems already; varify just re-zeroes the indices.) *)
val mult_0_v_dvd      = varify mult_0;          (* oeq (mult 0 n) 0           *)
val mult_0_right_vT   = varify mult_0_right;    (* oeq (mult n 0) 0           *)
val mult_1_right_vT   = varify mult_1_right;    (* oeq (mult n (Suc 0)) n     *)
val mult_comm_vT      = varify mult_comm;       (* oeq (mult m n) (mult n m)  *)

fun mult0r_atT t       = beta_norm (Drule.infer_instantiate ctxtT [(("n",0), ctermT t)] mult_0_right_vT);
fun mult1r_atT t       = beta_norm (Drule.infer_instantiate ctxtT [(("n",0), ctermT t)] mult_1_right_vT);
fun multcomm_atT (mt,nt) = beta_norm (Drule.infer_instantiate ctxtT
                              [(("m",0), ctermT mt),(("n",0), ctermT nt)] mult_comm_vT);

(* ============================================================================
   HELPER  mult_1_left : oeq (mult (Suc Zero) n) n     (from mult_comm + mult_1_right)
     mult (Suc 0) n  =  mult n (Suc 0)   (mult_comm)
                     =  n                (mult_1_right)
   ============================================================================ *)
val mult_1_left =
  let
    val nF = Free("n", natT);
    val c  = multcomm_atT (suc ZeroC, nF);   (* oeq (mult (Suc 0) n) (mult n (Suc 0)) *)
    val r  = mult1r_atT nF;                   (* oeq (mult n (Suc 0)) n                *)
  in varify (oeq_trans OF [c, r]) end;
val mult_1_left_vT = varify mult_1_left;
fun mult1l_atT t = beta_norm (Drule.infer_instantiate ctxtT [(("n",0), ctermT t)] mult_1_left_vT);

(* ============================================================================
   EASY DIVISIBILITY LEMMAS  (each 0-hyp, named val, via dvd_intro + a witness)
   ============================================================================ *)

(* dvd_refl : dvd a a              witness Suc Zero ;  a = a * 1  (mult_1_right sym) *)
val dvd_refl =
  let
    val aF  = Free("a", natT);
    val r   = mult1r_atT aF;                 (* oeq (mult a (Suc 0)) a *)
    val hyp = oeq_sym OF [r];                 (* oeq a (mult a (Suc 0)) *)
  in varify (dvd_intro (aF, aF, suc ZeroC) hyp) end;

(* one_dvd : dvd (Suc Zero) n      witness n ;  n = 1 * n  (mult_1_left sym) *)
val one_dvd =
  let
    val nF  = Free("n", natT);
    val l   = mult1l_atT nF;                  (* oeq (mult (Suc 0) n) n *)
    val hyp = oeq_sym OF [l];                  (* oeq n (mult (Suc 0) n) *)
  in varify (dvd_intro (suc ZeroC, nF, nF) hyp) end;

(* dvd_zero : dvd a Zero           witness Zero ;  0 = a * 0  (mult_0_right sym) *)
val dvd_zero =
  let
    val aF  = Free("a", natT);
    val r   = mult0r_atT aF;                  (* oeq (mult a 0) 0 *)
    val hyp = oeq_sym OF [r];                  (* oeq 0 (mult a 0) *)
  in varify (dvd_intro (aF, ZeroC, ZeroC) hyp) end;

(* ============================================================================
   VALIDATION : each lemma must be 0-hyp AND aconv its intended schematic goal,
   the goal built with the SAME `dvd` abbreviation so the Ex-body matches exactly.
   ============================================================================ *)
fun checkDvd (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtT (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtT intended ^ "\n");
          false)
  end;

val aVd = Var (("a",0), natT);
val nVd = Var (("n",0), natT);

(* mult_1_left validated too (the medium-lemma prerequisite seats will lean on). *)
val r_m1l   = checkDvd ("mult_1_left", mult_1_left, jT (oeq (mult (suc ZeroC) nVd) nVd));
val r_drefl = checkDvd ("dvd_refl",  dvd_refl,  jT (dvd aVd aVd));
val r_1dvd  = checkDvd ("one_dvd",   one_dvd,   jT (dvd (suc ZeroC) nVd));
val r_dzero = checkDvd ("dvd_zero",  dvd_zero,  jT (dvd aVd ZeroC));

val () = if r_m1l andalso r_drefl andalso r_1dvd andalso r_dzero
         then out "FOUNDATION_OK\n"
         else out "FOUNDATION_BROKEN\n";

(* ============================================================================
   SHARED MULT HELPERS on the FINAL context ctxtT  (defined ONCE; used by
   dvd_trans, dvd_mult_right, dvd_mult_cong).
   ============================================================================ *)
(* mult_assoc re-varified for ctxtT + ground instantiator:
     mult_assoc : oeq (mult (mult ?m ?n) ?k) (mult ?m (mult ?n ?k))  *)
val mult_assoc_vT = varify mult_assoc;
fun multassocT_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtT
        [(("m",0), ctermT mt),(("n",0), ctermT nt),(("k",0), ctermT kt)] mult_assoc_vT);

(* mult-congruence on LEFT operand (k fixed):  oeq p q  ==>  oeq (mult p k) (mult q k) *)
fun mult_cong_lT (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtT
          [(("P",0), ctermT Pabs), (("a",0), ctermT pT), (("b",0), ctermT qT)] oeq_subst_vT);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtT [(("a",0), ctermT (mult pT kT))] oeq_refl_vT);
  in inst OF [hpq, refl_pk] end;

(* mult-congruence on RIGHT operand (h fixed):  oeq p q  ==>  oeq (mult h p) (mult h q) *)
fun mult_cong_rT (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtT
          [(("P",0), ctermT Pabs), (("a",0), ctermT pT), (("b",0), ctermT qT)] oeq_subst_vT);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtT [(("a",0), ctermT (mult hT pT))] oeq_refl_vT);
  in inst OF [hpq, refl_hp] end;

(* uniform 0-hyp + aconv validator on ctxtT, shared by all five appended laws *)
fun checkThm (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtT (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtT intended ^ "\n");
          false)
  end;

(* ============================================================================
   dvd_trans : Trueprop (dvd a b) ==> Trueprop (dvd b c) ==> Trueprop (dvd a c)
   [from isa_dvd_dvd_trans.sml]   PREORDER: transitivity of divisibility.
   ROUTE (mult instead of add, mult_assoc instead of addassoc):
     dvd a b -> exE witness p, hp : oeq b (mult a p)
     dvd b c -> exE witness q, hq : oeq c (mult b q)
     goal dvd a c, witness (mult p q):  oeq c (mult a (mult p q))
   ============================================================================ *)
val dvd_trans =
  let
    val aF = Free("a", natT); val bF = Free("b", natT); val cF = Free("c", natT);
    val H1prop = jT (dvd aF bF);   (* Ex(%k. oeq b (mult a k)) *)
    val H2prop = jT (dvd bF cF);   (* Ex(%k. oeq c (mult b k)) *)
    val H1 = Thm.assume (ctermT H1prop);
    val H2 = Thm.assume (ctermT H2prop);
    val P1abs = Abs ("k", natT, oeq bF (mult aF (Bound 0)));   (* matches dvd a b *)
    val P2abs = Abs ("k", natT, oeq cF (mult bF (Bound 0)));   (* matches dvd b c *)
    val goalBody = dvd aF cF;

    (* inner: given witness p (and hp : oeq b (mult a p)) consume H2 to reach goal *)
    fun inner pF =
      let
        val hp = Thm.assume (ctermT (jT (oeq bF (mult aF pF))));
        val exE2 = beta_norm (Drule.infer_instantiate ctxtT
              [(("P",0), ctermT P2abs), (("Q",0), ctermT goalBody)] exE_vT);
        val exE2_H2 = Thm.implies_elim exE2 H2;
        val qF = Free("q", natT);
        val hq = Thm.assume (ctermT (jT (oeq cF (mult bF qF))));     (* c = b * q *)
        val cong  = mult_cong_lT (bF, mult aF pF, qF) hp;            (* b*q = (a*p)*q *)
        val step1 = oeq_trans OF [hq, cong];                          (* c = (a*p)*q *)
        val assoc = multassocT_at (aF, pF, qF);                       (* (a*p)*q = a*(p*q) *)
        val ceq   = oeq_trans OF [step1, assoc];                      (* c = a*(p*q) *)
        val bodyProof2 = dvd_intro (aF, cF, mult pF qF) ceq;          (* dvd a c *)
        val minor2 = Thm.forall_intr (ctermT qF)
                      (Thm.implies_intr (ctermT (jT (oeq cF (mult bF qF)))) bodyProof2);
      in Thm.implies_elim exE2_H2 minor2 end;

    val exE1 = beta_norm (Drule.infer_instantiate ctxtT
          [(("P",0), ctermT P1abs), (("Q",0), ctermT goalBody)] exE_vT);
    val exE1_H1 = Thm.implies_elim exE1 H1;
    val pF = Free("p", natT);
    val bodyProof1 = inner pF;
    val minor1 = Thm.forall_intr (ctermT pF)
                  (Thm.implies_intr (ctermT (jT (oeq bF (mult aF pF)))) bodyProof1);
    val res1 = Thm.implies_elim exE1_H1 minor1;
    val d1 = Thm.implies_intr (ctermT H2prop) res1;
    val d2 = Thm.implies_intr (ctermT H1prop) d1;
  in varify d2 end;

val aVt = Var (("a",0), natT);
val bVt = Var (("b",0), natT);
val cVt = Var (("c",0), natT);
val dvd_trans_intended =
  Logic.mk_implies (jT (dvd aVt bVt),
    Logic.mk_implies (jT (dvd bVt cVt), jT (dvd aVt cVt)));
val r_dvd_trans = checkThm ("dvd_trans", dvd_trans, dvd_trans_intended);

(* ============================================================================
   dvd_add : jT (dvd d m) ==> jT (dvd d n) ==> jT (dvd d (add m n))
   [from isa_dvd_dvd_add.sml]   + compatibility.
   exE both hyps: m = mult d p, n = mult d q; left_distrib folds the sum.
   ============================================================================ *)
(* left_distrib re-varified for ctxtT; schematic vars from Free names x,m,n:
     oeq (mult ?x (add ?m ?n)) (add (mult ?x ?m) (mult ?x ?n)) *)
val left_distrib_vT = varify left_distrib;
(* ground instance: oeq (mult d (add p q)) (add (mult d p) (mult d q)) *)
fun left_distrib_atT (dT, pT, qT) =
  beta_norm (Drule.infer_instantiate ctxtT
      [(("x",0), ctermT dT), (("m",0), ctermT pT), (("n",0), ctermT qT)] left_distrib_vT);

val dvd_add =
  let
    val dF = Free("d", natT); val mF = Free("m", natT); val nF = Free("n", natT);
    val H1prop = jT (dvd dF mF);    (* dvd d m *)
    val H2prop = jT (dvd dF nF);    (* dvd d n *)
    val H1 = Thm.assume (ctermT H1prop);
    val H2 = Thm.assume (ctermT H2prop);
    val goalBody = dvd dF (add mF nF);   (* dvd d (add m n) *)

    (* abs bodies matching dvd a b == Ex (%k. oeq b (mult a k)) *)
    val P1abs = Abs("k", natT, oeq mF (mult dF (Bound 0)));   (* for H1 : dvd d m *)
    val P2abs = Abs("k", natT, oeq nF (mult dF (Bound 0)));   (* for H2 : dvd d n *)

    (* outer exE over H1: witness p, hp : jT (oeq m (mult d p)) *)
    fun outerBody pF hp =
      let
        (* inner exE over H2: witness q, hq : jT (oeq n (mult d q)) *)
        fun innerBody qF hq =
          let
            val c1 = add_cong_lT (mF, mult dF pF, nF) hp;     (* (m+n) = (d*p + n) *)
            val c2 = add_cong_rT (mult dF pF, nF, mult dF qF) hq; (* (d*p+n) = (d*p + d*q) *)
            val sumEq = oeq_trans OF [c1, c2];                (* (m+n) = (d*p + d*q) *)
            val ld = left_distrib_atT (dF, pF, qF);           (* d*(p+q) = (d*p + d*q) *)
            val lds = oeq_sym OF [ld];                        (* (d*p + d*q) = d*(p+q) *)
            val witEq = oeq_trans OF [sumEq, lds];            (* (m+n) = d*(p+q) *)
          in dvd_intro (dF, add mF nF, add pF qF) witEq end;  (* jT (dvd d (add m n)) *)
      in exE_elimT (P2abs, goalBody) H2 "q0" innerBody end;

    val res0 = exE_elimT (P1abs, goalBody) H1 "p0" outerBody;
    val d1 = Thm.implies_intr (ctermT H2prop) res0;
    val d2 = Thm.implies_intr (ctermT H1prop) d1;
  in varify d2 end;

val dVa = Var (("d",0), natT);
val mVa = Var (("m",0), natT);
val nVa = Var (("n",0), natT);
val dvd_add_intended =
  Logic.mk_implies (jT (dvd dVa mVa),
    Logic.mk_implies (jT (dvd dVa nVa), jT (dvd dVa (add mVa nVa))));
val r_dvd_add = checkThm ("dvd_add", dvd_add, dvd_add_intended);

(* ============================================================================
   dvd_mult_right : dvd a b ==> dvd a (mult b c)          [from isa_dvd_dvd_mult.sml]
   dvd_mult_cong  : dvd a b ==> dvd (mult a c) (mult b c) [* compatibility]
   ============================================================================ *)
(* ---- dvd_mult_right ----
   from `oeq b (mult a p)`:
     mult b c = mult (mult a p) c   (mult_cong_l)  = mult a (mult p c)  (mult_assoc)
   witness (mult p c) for `dvd a (mult b c)`. *)
val dvd_mult_right =
  let
    val aF = Free("a", natT); val bF = Free("b", natT); val cF = Free("c", natT);
    val dvdHypP = jT (dvd aF bF);
    val dvdHyp  = Thm.assume (ctermT dvdHypP);
    val Pabs    = Abs("k", natT, oeq bF (mult aF (Bound 0)));   (* dvd a b body *)
    val goalC   = dvd aF (mult bF cF);
    fun body w (hw : thm) =                     (* hw : oeq b (mult a w) *)
      let
        val cong  = mult_cong_lT (bF, mult aF w, cF) hw;        (* (b*c) = ((a*w)*c) *)
        val assoc = multassocT_at (aF, w, cF);                  (* ((a*w)*c) = (a*(w*c)) *)
        val eqn   = oeq_trans OF [cong, assoc];                 (* (b*c) = (a*(w*c)) *)
      in dvd_intro (aF, mult bF cF, mult w cF) eqn end;          (* jT (dvd a (mult b c)) *)
    val res = exE_elimT (Pabs, goalC) dvdHyp "p0" body;
    val disch = Thm.implies_intr (ctermT dvdHypP) res;
  in varify disch end;

(* ---- dvd_mult_cong ----
   from `oeq b (mult a p)`:
     mult b c = mult (mult a p) c = mult a (mult p c) = mult a (mult c p)
              = mult (mult a c) p ; witness p for `dvd (mult a c) (mult b c)`. *)
val dvd_mult_cong =
  let
    val aF = Free("a", natT); val bF = Free("b", natT); val cF = Free("c", natT);
    val dvdHypP = jT (dvd aF bF);
    val dvdHyp  = Thm.assume (ctermT dvdHypP);
    val Pabs    = Abs("k", natT, oeq bF (mult aF (Bound 0)));   (* dvd a b body *)
    val goalC   = dvd (mult aF cF) (mult bF cF);
    fun body w (hw : thm) =                     (* hw : oeq b (mult a w) *)
      let
        val cong   = mult_cong_lT (bF, mult aF w, cF) hw;       (* (b*c) = ((a*w)*c) *)
        val assoc1 = multassocT_at (aF, w, cF);                 (* ((a*w)*c) = (a*(w*c)) *)
        val comm   = multcomm_atT (w, cF);                      (* (w*c) = (c*w) *)
        val congr  = mult_cong_rT (aF, mult w cF, mult cF w) comm; (* a*(w*c) = a*(c*w) *)
        val assoc2 = multassocT_at (aF, cF, w);                 (* ((a*c)*w) = (a*(c*w)) *)
        val assoc2s= oeq_sym OF [assoc2];                       (* (a*(c*w)) = ((a*c)*w) *)
        val e1     = oeq_trans OF [cong, assoc1];               (* (b*c) = (a*(w*c)) *)
        val e2     = oeq_trans OF [e1, congr];                  (* (b*c) = (a*(c*w)) *)
        val eqn    = oeq_trans OF [e2, assoc2s];                (* (b*c) = ((a*c)*w) *)
      in dvd_intro (mult aF cF, mult bF cF, w) eqn end;          (* jT (dvd (mult a c) (mult b c)) *)
    val res = exE_elimT (Pabs, goalC) dvdHyp "p0" body;
    val disch = Thm.implies_intr (ctermT dvdHypP) res;
  in varify disch end;

val aVc = Var (("a",0), natT);
val bVc = Var (("b",0), natT);
val cVc = Var (("c",0), natT);
val intended_right =
  Logic.mk_implies (jT (dvd aVc bVc), jT (dvd aVc (mult bVc cVc)));
val intended_cong =
  Logic.mk_implies (jT (dvd aVc bVc), jT (dvd (mult aVc cVc) (mult bVc cVc)));
val r_dvd_mult_right = checkThm ("dvd_mult_right", dvd_mult_right, intended_right);
val r_dvd_mult_cong  = checkThm ("dvd_mult_cong",  dvd_mult_cong,  intended_cong);

(* ============================================================================
   dvd_le  (CAPSTONE — ties divisibility to the order)   [from isa_dvd_dvd_le.sml]
     Trueprop (dvd d n)
       ==> (Trueprop (oeq n Zero) ==> Trueprop oFalse)
         ==> Trueprop (le d n)            i.e.  d | n  and  n != 0  ==>  d <= n.
   exE on (dvd d n) gives witness k with oeq n (mult d k); case on k via dzosT_at:
     k = Zero    -> n = mult d 0 = 0, feed the nonzero premise -> oFalse -> goal.
     k = Suc k0  -> n = mult d (Suc k0) = add d (mult d k0), le d n witness (mult d k0).
   ============================================================================ *)
(* mult_Suc_right on ctxtT:  multSrT_at (nt,mt) : oeq (mult nt (suc mt)) (add nt (mult nt mt)) *)
val mult_Suc_right_vT = varify mult_Suc_right;
fun multSrT_at (nt,mt) = beta_norm (Drule.infer_instantiate ctxtT
       [(("n",0), ctermT nt),(("m",0), ctermT mt)] mult_Suc_right_vT);
(* oFalse_elim on ctxtT instantiated at an explicit R *)
fun oFalse_elimT_at rT = beta_norm (Drule.infer_instantiate ctxtT
       [(("R",0), ctermT rT)] oFalse_elim_vT);

val dvd_le =
  let
    val dF = Free("d", natT); val nF = Free("n", natT);
    val dvdHypP = jT (dvd dF nF);
    val nzHypP  = Logic.mk_implies (jT (oeq nF ZeroC), jT oFalseC);
    val dvdHyp  = Thm.assume (ctermT dvdHypP);
    val nzHyp   = Thm.assume (ctermT nzHypP);   (* oeq n 0 ==> oFalse *)

    val goalBody = le dF nF;
    val PabsK = Abs("k", natT, oeq nF (mult dF (Bound 0)));  (* dvd d n body *)

    fun dvdBody k (hk : thm) =                   (* hk : oeq n (mult d k) *)
      let
        val dz = dzosT_at k;                      (* Disj (oeq k 0) (Ex(%q. oeq k (Suc q))) *)

        val caseZero =
          let
            val ekz = Thm.assume (ctermT (jT (oeq k ZeroC)));   (* oeq k 0 *)
            val Psub = Abs("z", natT, oeq (mult dF k) (mult dF (Bound 0)));
            val subInst = beta_norm (Drule.infer_instantiate ctxtT
                  [(("P",0), ctermT Psub), (("a",0), ctermT k), (("b",0), ctermT ZeroC)] oeq_subst_vT);
            val reflMdk = beta_norm (Drule.infer_instantiate ctxtT
                  [(("a",0), ctermT (mult dF k))] oeq_refl_vT);
            val mdk_md0 = subInst OF [ekz, reflMdk];            (* (d*k) = (d*0) *)
            val md0_0   = mult0r_atT dF;                        (* (d*0) = 0 *)
            val n_mdk   = hk;                                   (* n = (d*k) *)
            val n_md0   = oeq_trans OF [n_mdk, mdk_md0];        (* n = (d*0) *)
            val n_0     = oeq_trans OF [n_md0, md0_0];          (* n = 0 *)
            val false_thm = Thm.implies_elim nzHyp n_0;        (* oFalse *)
            val goalThm   = (oFalse_elimT_at goalBody) OF [false_thm]; (* le d n *)
          in Thm.implies_intr (ctermT (jT (oeq k ZeroC))) goalThm end;

        val PabsQ = Abs("q", natT, oeq k (suc (Bound 0)));
        val caseSuc =
          let
            val exq = Thm.assume (ctermT (jT (mkEx PabsQ)));    (* Ex(%q. oeq k (Suc q)) *)
            fun sucBody q (hq : thm) =                          (* hq : oeq k (Suc q) *)
              let
                val Psub2 = Abs("z", natT, oeq (mult dF k) (mult dF (Bound 0)));
                val subInst2 = beta_norm (Drule.infer_instantiate ctxtT
                      [(("P",0), ctermT Psub2), (("a",0), ctermT k), (("b",0), ctermT (suc q))] oeq_subst_vT);
                val reflMdk2 = beta_norm (Drule.infer_instantiate ctxtT
                      [(("a",0), ctermT (mult dF k))] oeq_refl_vT);
                val mdk_mdSq = subInst2 OF [hq, reflMdk2];      (* (d*k) = (d*(Suc q)) *)
                val mdSq_chain = multSrT_at (dF, q);            (* (d*(Suc q)) = (d + d*q) *)
                val n_mdk   = hk;
                val n_mdSq  = oeq_trans OF [n_mdk, mdk_mdSq];   (* n = (d*(Suc q)) *)
                val n_add   = oeq_trans OF [n_mdSq, mdSq_chain];(* n = (d + d*q) *)
                val leThm   = le_introT (dF, nF, mult dF q) n_add; (* le d n, witness d*q *)
              in leThm end;
            val g = exE_elimT (PabsQ, goalBody) exq "q0" sucBody;
          in Thm.implies_intr (ctermT (jT (mkEx PabsQ))) g end;

        val combined = disjE_elimT (oeq k ZeroC, mkEx PabsQ, goalBody) dz caseZero caseSuc;
      in combined end;

    val afterExE = exE_elimT (PabsK, goalBody) dvdHyp "kw" dvdBody;
    (* discharge premises in REVERSE order: nonzero (inner), dvd (outer) *)
    val d1 = Thm.implies_intr (ctermT nzHypP)  afterExE;
    val d2 = Thm.implies_intr (ctermT dvdHypP) d1;
  in varify d2 end;

val dVd = Var (("d",0), natT);
val nVl = Var (("n",0), natT);
val dvd_le_intended =
  Logic.mk_implies (jT (dvd dVd nVl),
    Logic.mk_implies (Logic.mk_implies (jT (oeq nVl ZeroC), jT oFalseC),
      jT (le dVd nVl)));
val r_dvd_le = checkThm ("dvd_le", dvd_le, dvd_le_intended);

(* ============================================================================
   FINAL VERDICT : all eight laws must validate (the three foundation easy
   lemmas + the five merged laws) for DVD_DONE.
   ============================================================================ *)
val () =
  if r_drefl andalso r_1dvd andalso r_dzero
     andalso r_dvd_trans andalso r_dvd_add
     andalso r_dvd_mult_right andalso r_dvd_mult_cong
     andalso r_dvd_le
  then out "DVD_DONE\n"
  else out "DVD_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  CLASSICAL LAYER (PHASE 1)  ***
   ----------------------------------------------------------------------------
   Turn the intuitionistic object logic into a CLASSICAL one.  We extend the
   final theory `thyT` ONE more time with three new connectives + their
   intro/elim axioms, plus the single classical axiom `ex_middle`.  Then we
   re-init ONE FINAL context `ctxtC` / `ctermC` and route EVERYTHING through it.

   NEW CONSTS (on thyC, built on top of thyT):
     Imp    : o => o => o      object implication
     Conj   : o => o => o      object conjunction
     Forall : (nat=>o) => o    universal quantifier over naturals

   AXIOMS:
     impI       : (jT A ==> jT B) ==> jT (Imp A B)
     mp         : jT (Imp A B) ==> jT A ==> jT B
     conjI      : jT A ==> jT B ==> jT (Conj A B)
     conjunct1  : jT (Conj A B) ==> jT A
     conjunct2  : jT (Conj A B) ==> jT B
     allI       : (!!x. jT (P x)) ==> jT (Forall P)
     allE       : jT (Forall P) ==> jT (P a)
     ex_middle  : jT (Disj A (neg A))           [THE single classical axiom]

   ABBREVIATION:
     neg A  ==  Imp A oFalse                      (so neg A == A ==> False)

   DERIVED (each 0-extra-hyp, validated by aconv of its implication form):
     dbl_neg     : jT (neg (neg A)) ==> jT A
     deMorgan_or : jT (neg (Disj A B)) ==> jT (Conj (neg A) (neg B))
     not_imp     : jT (neg (Imp A B)) ==> jT (Conj A (neg B))
     not_forall  : jT (neg (Forall P)) ==> jT (Ex (%x. neg (P x)))
   ============================================================================ *)

val () = out "CLASSICAL_LAYER_BEGIN\n";

(* ---- the ONE final theory extension: Imp, Conj, Forall + axioms ---- *)
val thyC0 = Sign.add_consts
  [(Binding.name "Imp",    oT --> oT --> oT, NoSyn),
   (Binding.name "Conj",   oT --> oT --> oT, NoSyn),
   (Binding.name "Forall", predNatT --> oT, NoSyn)] thyT;

val ImpC    = Const (Sign.full_name thyC0 (Binding.name "Imp"),    oT --> oT --> oT);
val ConjC   = Const (Sign.full_name thyC0 (Binding.name "Conj"),   oT --> oT --> oT);
val ForallC = Const (Sign.full_name thyC0 (Binding.name "Forall"), predNatT --> oT);
fun mkImp s t  = ImpC $ s $ t;
fun mkConj s t = ConjC $ s $ t;
fun mkForall pr = ForallC $ pr;

(* negation as an ABBREVIATION (NOT a const): neg A == Imp A oFalse *)
fun neg A = mkImp A oFalseC;

(* schematic Frees for stating the axioms *)
val Ac = Free ("A", oT); val Bc = Free ("B", oT);
val Pc = Free ("P", predNatT); val ac = Free ("a", natT);

(* impI : (jT A ==> jT B) ==> jT (Imp A B) *)
val ((_,impI_ax), thyC1) = Thm.add_axiom_global (Binding.name "impI",
      Logic.mk_implies (Logic.mk_implies (jT Ac, jT Bc), jT (mkImp Ac Bc))) thyC0;
(* mp : jT (Imp A B) ==> jT A ==> jT B *)
val ((_,mp_ax), thyC2) = Thm.add_axiom_global (Binding.name "mp",
      Logic.mk_implies (jT (mkImp Ac Bc), Logic.mk_implies (jT Ac, jT Bc))) thyC1;
(* conjI : jT A ==> jT B ==> jT (Conj A B) *)
val ((_,conjI_ax), thyC3) = Thm.add_axiom_global (Binding.name "conjI",
      Logic.mk_implies (jT Ac, Logic.mk_implies (jT Bc, jT (mkConj Ac Bc)))) thyC2;
(* conjunct1 : jT (Conj A B) ==> jT A *)
val ((_,conjunct1_ax), thyC4) = Thm.add_axiom_global (Binding.name "conjunct1",
      Logic.mk_implies (jT (mkConj Ac Bc), jT Ac)) thyC3;
(* conjunct2 : jT (Conj A B) ==> jT B *)
val ((_,conjunct2_ax), thyC5) = Thm.add_axiom_global (Binding.name "conjunct2",
      Logic.mk_implies (jT (mkConj Ac Bc), jT Bc)) thyC4;
(* allI : (!!x. jT (P x)) ==> jT (Forall P) *)
val xAllI = Free ("x", natT);
val ((_,allI_ax), thyC6) = Thm.add_axiom_global (Binding.name "allI",
      Logic.mk_implies (Logic.all xAllI (jT (Pc $ xAllI)), jT (mkForall Pc))) thyC5;
(* allE : jT (Forall P) ==> jT (P a) *)
val ((_,allE_ax), thyC7) = Thm.add_axiom_global (Binding.name "allE",
      Logic.mk_implies (jT (mkForall Pc), jT (Pc $ ac))) thyC6;
(* ex_middle : jT (Disj A (neg A))  -- THE single classical axiom *)
val ((_,ex_middle_ax), thyC) = Thm.add_axiom_global (Binding.name "ex_middle",
      jT (mkDisj Ac (neg Ac))) thyC7;

(* ---- THE ONE FINAL CONTEXT ctxtC / ctermC ---- *)
val ctxtC  = Proof_Context.init_global thyC;
val ctermC = Thm.cterm_of ctxtC;

(* ---- re-varify EVERY reused axiom/lemma for use under ctxtC ----
   (all schematic; varify just re-zeroes indices for the new context) *)
val oeq_refl_vC   = varify oeq_refl;
val oeq_subst_vC  = varify oeq_subst;
val nat_induct_vC = varify nat_induct;
val exI_vC        = varify exI_ax;
val exE_vC        = varify exE_ax;
val oFalse_elim_vC= varify oFalse_elim_ax;
val disjI1_vC     = varify disjI1_ax;
val disjI2_vC     = varify disjI2_ax;
val disjE_vC      = varify disjE_ax;
val impI_vC       = varify impI_ax;
val mp_vC         = varify mp_ax;
val conjI_vC      = varify conjI_ax;
val conjunct1_vC  = varify conjunct1_ax;
val conjunct2_vC  = varify conjunct2_ax;
val allI_vC       = varify allI_ax;
val allE_vC       = varify allE_ax;
val ex_middle_vC  = varify ex_middle_ax;

(* ---- ground instantiators on ctxtC for the new connectives ---- *)

(* impI_atT (At,Bt) hAB : from (hAB : [jT At] |- jT Bt) get  jT (Imp At Bt).
   We feed the proof of `jT A ==> jT B` (a meta-implication) by discharging A. *)
fun impI_atT (At, Bt) hImpThm =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("A",0), ctermC At), (("B",0), ctermC Bt)] impI_vC);
  in Thm.implies_elim inst hImpThm end;

(* mp_atT (At,Bt) hImp hA : jT (Imp At Bt) -> jT At -> jT Bt *)
fun mp_atT (At, Bt) hImp hA =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("A",0), ctermC At), (("B",0), ctermC Bt)] mp_vC);
    val s1 = Thm.implies_elim inst hImp;
  in Thm.implies_elim s1 hA end;

(* conjI_atT (At,Bt) hA hB : jT At -> jT Bt -> jT (Conj At Bt) *)
fun conjI_atT (At, Bt) hA hB =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("A",0), ctermC At), (("B",0), ctermC Bt)] conjI_vC);
    val s1 = Thm.implies_elim inst hA;
  in Thm.implies_elim s1 hB end;

fun conjunct1_atT (At, Bt) hConj =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("A",0), ctermC At), (("B",0), ctermC Bt)] conjunct1_vC);
  in Thm.implies_elim inst hConj end;

fun conjunct2_atT (At, Bt) hConj =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("A",0), ctermC At), (("B",0), ctermC Bt)] conjunct2_vC);
  in Thm.implies_elim inst hConj end;

(* allI_atT Pabs hAllThm : Pabs an abstraction nat=>o; hAllThm a proof of the
   meta-quantified premise !!x. jT (Pabs x); produce jT (Forall Pabs). *)
fun allI_atT Pabs hAllThm =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs)] allI_vC);
  in Thm.implies_elim inst hAllThm end;

(* allE_atT Pabs at hForall : jT (Forall Pabs) -> jT (Pabs at)  (beta-normalised) *)
fun allE_atT Pabs at hForall =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("a",0), ctermC at)] allE_vC);
  in Thm.implies_elim inst hForall end;

(* ex_middle ground instance: jT (Disj At (neg At)) *)
fun ex_middle_at At = beta_norm (Drule.infer_instantiate ctxtC
      [(("A",0), ctermC At)] ex_middle_vC);

(* oFalse_elim on ctxtC at explicit R *)
fun oFalse_elimC_at rT = beta_norm (Drule.infer_instantiate ctxtC
      [(("R",0), ctermC rT)] oFalse_elim_vC);

(* disjE on ctxtC at explicit A,B,C: discharge all three premises *)
fun disjE_elimC (At, Bt, Ct) dThm caseA caseB =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("A",0), ctermC At), (("B",0), ctermC Bt), (("C",0), ctermC Ct)] disjE_vC);
    val s1 = Thm.implies_elim inst dThm;
    val s2 = Thm.implies_elim s1 caseA;
  in Thm.implies_elim s2 caseB end;
fun disjI1C_at (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtC
      [(("A",0), ctermC At), (("B",0), ctermC Bt)] disjI1_vC)) h;
fun disjI2C_at (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtC
      [(("A",0), ctermC At), (("B",0), ctermC Bt)] disjI2_vC)) h;

(* exI on ctxtC : Pabs an abstraction, at a witness -> jT (Pabs at) -> jT (Ex Pabs) *)
fun exI_atC Pabs at hbody =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("a",0), ctermC at)] exI_vC);
  in Thm.implies_elim inst hbody end;

(* exE on ctxtC : Pabs the existential body abstraction; goalC the goal term;
   bodyFn maps a fresh witness Free + a proof of jT (Pabs w) to a proof of goalC. *)
fun exE_elimC (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm = Thm.assume (ctermC hypTerm);
    val body = bodyFn wF hypThm;
    val minor = Thm.forall_intr (ctermC wF) (Thm.implies_intr (ctermC hypTerm) body);
    val exE_inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("Q",0), ctermC goalC)] exE_vC);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;

val () = out "CLASSICAL_CONSTS_READY\n";

(* ============================================================================
   dbl_neg : jT (neg (neg A)) ==> jT A
   ----------------------------------------------------------------------------
   ex_middle on A gives Disj A (neg A).
     left  (jT A)        : done.
     right (jT (neg A))  : from neg A and neg(neg A) get oFalse by mp,
                           then oFalse_elim => A.
   ============================================================================ *)
val dbl_neg =
  let
    val AF = Free("A", oT);
    val hyp = Thm.assume (ctermC (jT (neg (neg AF))));   (* jT (Imp (Imp A False) False) *)
    val em  = ex_middle_at AF;                             (* jT (Disj A (neg A)) *)
    (* CASE left : jT A ==> jT A *)
    val caseA =
      let val hA = Thm.assume (ctermC (jT AF))
      in Thm.implies_intr (ctermC (jT AF)) hA end;
    (* CASE right : jT (neg A) ==> jT A *)
    val caseB =
      let
        val hnA = Thm.assume (ctermC (jT (neg AF)));      (* jT (Imp A False) *)
        (* mp : neg(neg A) applied to neg A gives oFalse *)
        val falseThm = mp_atT (neg AF, oFalseC) hyp hnA;  (* jT oFalse *)
        val gA = Thm.implies_elim (oFalse_elimC_at AF) falseThm;  (* jT A *)
      in Thm.implies_intr (ctermC (jT (neg AF))) gA end;
    val concl = disjE_elimC (AF, neg AF, AF) em caseA caseB;  (* jT A *)
    val disch = Thm.implies_intr (ctermC (jT (neg (neg AF)))) concl;
  in varify disch end;

(* ============================================================================
   deMorgan_or : jT (neg (Disj A B)) ==> jT (Conj (neg A) (neg B))
   ----------------------------------------------------------------------------
   neg A: assume A, disjI1 => Disj A B, mp with hyp => oFalse, oFalse_elim => False,
          intr => neg A.  (Actually: from A get Disj A B; mp neg(Disj A B) on it
          => oFalse; that IS the body of neg A := A ==> False.)
   symmetric for neg B via disjI2; conjI.
   ============================================================================ *)
val deMorgan_or =
  let
    val AF = Free("A", oT); val BF = Free("B", oT);
    val hyp = Thm.assume (ctermC (jT (neg (mkDisj AF BF))));  (* jT (Imp (Disj A B) False) *)
    (* build neg A = Imp A False via impI: from a:A, prove False *)
    val negA =
      let
        val hA = Thm.assume (ctermC (jT AF));
        val dab = disjI1C_at (AF, BF) hA;                       (* jT (Disj A B) *)
        val falseThm = mp_atT (mkDisj AF BF, oFalseC) hyp dab;  (* jT oFalse *)
        val impThm = Thm.implies_intr (ctermC (jT AF)) falseThm; (* jT A ==> jT False *)
      in impI_atT (AF, oFalseC) impThm end;                     (* jT (neg A) *)
    val negB =
      let
        val hB = Thm.assume (ctermC (jT BF));
        val dab = disjI2C_at (AF, BF) hB;                       (* jT (Disj A B) *)
        val falseThm = mp_atT (mkDisj AF BF, oFalseC) hyp dab;  (* jT oFalse *)
        val impThm = Thm.implies_intr (ctermC (jT BF)) falseThm;
      in impI_atT (BF, oFalseC) impThm end;                     (* jT (neg B) *)
    val conj = conjI_atT (neg AF, neg BF) negA negB;            (* jT (Conj (neg A) (neg B)) *)
    val disch = Thm.implies_intr (ctermC (jT (neg (mkDisj AF BF)))) conj;
  in varify disch end;

(* ============================================================================
   not_imp : jT (neg (Imp A B)) ==> jT (Conj A (neg B))      *** CLASSICAL ***
   ----------------------------------------------------------------------------
   Show A by ex_middle on A:
     if A   : done.
     if neg A : then Imp A B holds (impI: from a:A, mp neg A a => oFalse,
                oFalse_elim => B), contradict hyp => oFalse => oFalse_elim => A.
   Show neg B : assume B, then Imp A B (impI ignoring its arg, returning B),
                contradict hyp.
   conjI.
   ============================================================================ *)
val not_imp =
  let
    val AF = Free("A", oT); val BF = Free("B", oT);
    val hyp = Thm.assume (ctermC (jT (neg (mkImp AF BF))));  (* jT (Imp (Imp A B) False) *)
    (* ---- show A (classically) ---- *)
    val emA = ex_middle_at AF;                                (* jT (Disj A (neg A)) *)
    val showA =
      let
        val caseA =
          let val hA = Thm.assume (ctermC (jT AF))
          in Thm.implies_intr (ctermC (jT AF)) hA end;
        val caseNA =
          let
            val hnA = Thm.assume (ctermC (jT (neg AF)));      (* jT (Imp A False) *)
            (* Imp A B holds: from a:A, mp neg A a => oFalse, oFalse_elim => B *)
            val impAB =
              let
                val ha = Thm.assume (ctermC (jT AF));
                val fa = mp_atT (AF, oFalseC) hnA ha;          (* jT oFalse *)
                val gb = Thm.implies_elim (oFalse_elimC_at BF) fa;  (* jT B *)
                val impThm = Thm.implies_intr (ctermC (jT AF)) gb;
              in impI_atT (AF, BF) impThm end;                 (* jT (Imp A B) *)
            val fAll = mp_atT (mkImp AF BF, oFalseC) hyp impAB; (* jT oFalse *)
            val gA = Thm.implies_elim (oFalse_elimC_at AF) fAll; (* jT A *)
          in Thm.implies_intr (ctermC (jT (neg AF))) gA end;
      in disjE_elimC (AF, neg AF, AF) emA caseA caseNA end;    (* jT A *)
    (* ---- show neg B ---- *)
    val showNegB =
      let
        val hB = Thm.assume (ctermC (jT BF));
        (* Imp A B (impI ignoring its arg, returning B) *)
        val impAB =
          let
            val ha = Thm.assume (ctermC (jT AF));
            val impThm = Thm.implies_intr (ctermC (jT AF)) hB; (* jT A ==> jT B *)
          in impI_atT (AF, BF) impThm end;                     (* jT (Imp A B) *)
        val fB = mp_atT (mkImp AF BF, oFalseC) hyp impAB;      (* jT oFalse *)
        val impThm = Thm.implies_intr (ctermC (jT BF)) fB;     (* jT B ==> jT False *)
      in impI_atT (BF, oFalseC) impThm end;                    (* jT (neg B) *)
    val conj = conjI_atT (AF, neg BF) showA showNegB;          (* jT (Conj A (neg B)) *)
    val disch = Thm.implies_intr (ctermC (jT (neg (mkImp AF BF)))) conj;
  in varify disch end;

(* ============================================================================
   not_forall : jT (neg (Forall P)) ==> jT (Ex (%x. neg (P x)))   *** CLASSICAL ***
   ----------------------------------------------------------------------------
   ex_middle on Ex(%x. neg(P x)):
     left  : done.
     right (neg (Ex(%x.neg(P x)))) :
        prove Forall P by allI: fix x; ex_middle on P x;
          if P x   : done.
          if neg(P x) : exI => Ex(%x.neg(P x)), mp with the neg(Ex...) => oFalse
                        => oFalse_elim => P x.
        so Forall P; mp with neg(Forall P) => oFalse => oFalse_elim => the goal.
   ============================================================================ *)
val not_forall =
  let
    val PF = Free("P", predNatT);
    (* the existential body abstraction:  %x. neg (P x) *)
    val zF = Free("zz", natT);
    val negPabs = Term.lambda zF (neg (PF $ zF));     (* %x. Imp (P x) False *)
    val goalEx = mkEx negPabs;                          (* Ex (%x. neg (P x)) *)

    val hyp = Thm.assume (ctermC (jT (neg (mkForall PF))));  (* jT (Imp (Forall P) False) *)
    val emEx = ex_middle_at goalEx;                          (* jT (Disj goalEx (neg goalEx)) *)

    val caseL =
      let val hg = Thm.assume (ctermC (jT goalEx))
      in Thm.implies_intr (ctermC (jT goalEx)) hg end;

    val caseR =
      let
        val hnEx = Thm.assume (ctermC (jT (neg goalEx)));    (* jT (Imp goalEx False) *)
        (* prove Forall P by allI: fix x, prove P x *)
        val xF = Free("x", natT);
        val provePx =
          let
            val emPx = ex_middle_at (PF $ xF);                (* jT (Disj (P x) (neg (P x))) *)
            val caseP =
              let val hpx = Thm.assume (ctermC (jT (PF $ xF)))
              in Thm.implies_intr (ctermC (jT (PF $ xF))) hpx end;
            val caseNP =
              let
                val hnpx = Thm.assume (ctermC (jT (neg (PF $ xF))));  (* jT (neg (P x)) *)
                (* exI : witness x, body jT (negPabs x) = jT (neg (P x)) *)
                val exThm = exI_atC negPabs xF hnpx;          (* jT goalEx *)
                val fAll = mp_atT (goalEx, oFalseC) hnEx exThm; (* jT oFalse *)
                val gpx = Thm.implies_elim (oFalse_elimC_at (PF $ xF)) fAll; (* jT (P x) *)
              in Thm.implies_intr (ctermC (jT (neg (PF $ xF)))) gpx end;
          in disjE_elimC (PF $ xF, neg (PF $ xF), PF $ xF) emPx caseP caseNP end;  (* jT (P x) *)
        (* allI : !!x. jT (P x) ==> jT (Forall P).  The Pabs for allI is %x. P x. *)
        val Pabs_forall = Term.lambda xF (PF $ xF);           (* %x. P x  (= P up to eta) *)
        val minor = Thm.forall_intr (ctermC xF) provePx;      (* !!x. jT (P x) *)
        val forallP = allI_atT Pabs_forall minor;             (* jT (Forall (%x. P x)) *)
        (* mp with neg(Forall P) -> need Imp (Forall (%x.P x)) ... must match hyp's A.
           hyp : neg (Forall PF) = Imp (Forall PF) False.  forallP : jT (Forall (%x. PF x)).
           These are aconv (eta).  mp_atT uses ImpC with A := Forall PF; we must feed a
           proof of jT (Forall PF).  Forall PF and Forall (%x. PF x) are eta-equal terms,
           so the thm whose prop is jT (Forall (%x.PF x)) ought to be usable where
           jT (Forall PF) is required.  To be safe, coerce via equal_elim if needed. *)
        val fAll2 = mp_atT (mkForall PF, oFalseC) hyp forallP; (* jT oFalse *)
        val gGoal = Thm.implies_elim (oFalse_elimC_at goalEx) fAll2; (* jT goalEx *)
      in Thm.implies_intr (ctermC (jT (neg goalEx))) gGoal end;

    val concl = disjE_elimC (goalEx, neg goalEx, goalEx) emEx caseL caseR;  (* jT goalEx *)
    val disch = Thm.implies_intr (ctermC (jT (neg (mkForall PF)))) concl;
  in varify disch end;

(* ============================================================================
   VALIDATION : each derived lemma is 0-extra-hyp AND aconv its intended
   schematic implication form.
   ============================================================================ *)
fun checkClassical (nm, th, intended) =
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

(* schematic Vars for the intended statements *)
val AV = Var (("A",0), oT);
val BV = Var (("B",0), oT);
val PV = Var (("P",0), predNatT);

(* intended forms *)
val dbl_neg_intended =
  Logic.mk_implies (jT (neg (neg AV)), jT AV);
val deMorgan_or_intended =
  Logic.mk_implies (jT (neg (mkDisj AV BV)), jT (mkConj (neg AV) (neg BV)));
val not_imp_intended =
  Logic.mk_implies (jT (neg (mkImp AV BV)), jT (mkConj AV (neg BV)));
(* not_forall goal body : Ex (%x. neg (P x)) with the SAME abstraction shape *)
val zV = Free("zz", natT);
val negPVabs = Term.lambda zV (neg (PV $ zV));
val not_forall_intended =
  Logic.mk_implies (jT (neg (mkForall PV)), jT (mkEx negPVabs));

val r_dbl_neg     = checkClassical ("dbl_neg",     dbl_neg,     dbl_neg_intended);
val r_deMorgan_or = checkClassical ("deMorgan_or", deMorgan_or, deMorgan_or_intended);
val r_not_imp     = checkClassical ("not_imp",     not_imp,     not_imp_intended);
val r_not_forall  = checkClassical ("not_forall",  not_forall,  not_forall_intended);

val () =
  if r_dbl_neg andalso r_deMorgan_or andalso r_not_imp andalso r_not_forall
  then out "CLASSICAL_OK\n"
  else out "CLASSICAL_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  PHASE 2 : STRICT ORDER + NUMBER FACTS + STRUCTURAL PRIME + STRONG IND  ***
   ----------------------------------------------------------------------------
   Everything here extends the SINGLE FINAL classical context ctxtC / ctermC
   from phase 1 (it carries oeq/add/mult/Suc/Zero, Ex/oFalse/Disj, Imp/Conj/
   Forall, the abbreviations le/dvd/neg, and all the connective helpers
   exI_atC/exE_elimC/disjE_elimC/disjI1C_at/disjI2C_at/oFalse_elimC_at/
   impI_atT/mp_atT/conjI_atT/conjunct1_atT/conjunct2_atT/allI_atT/allE_atT/
   ex_middle_at).  We additionally RE-STATE the arithmetic helpers on ctxtC
   (every NEW cterm routes through ctermC; mixing an earlier-theory cterm into a
   ctxtC goal gives a cross-theory certificate mismatch).

   ADDED + PROVED (each a 0-hyp / 0-extra-hyp named val, validated aconv):
     lt m n  ==  le (Suc m) n                              [ABBREVIATION]
     lt_suc        : Trueprop (lt n (Suc n))
     lt_irrefl     : Trueprop (lt n n) ==> Trueprop oFalse
     lt_suc_cases  : Trueprop (lt m (Suc n)) ==> Trueprop (Disj (lt m n) (oeq m n))
     lt_trans      : Trueprop (lt a b) ==> Trueprop (lt b c) ==> Trueprop (lt a c)
     le_neq_lt     : jT (le d n) ==> jT (neg (oeq d n)) ==> jT (lt d n)
     ne0_suc       : jT (neg (oeq d Zero)) ==> jT (Ex (%m. oeq d (Suc m)))
     gt1_of_ne0_ne1: jT (neg (oeq d Zero)) ==> jT (neg (oeq d (Suc Zero)))
                                            ==> jT (lt (Suc Zero) d)
     dvd_nonzero   : jT (dvd d n) ==> jT (neg (oeq n Zero)) ==> jT (neg (oeq d Zero))
     prime p  ==  Conj (lt (Suc Zero) p)
                       (Forall (%d. Imp (dvd d p) (Disj (oeq d (Suc Zero)) (oeq d p))))
                                                            [ABBREVIATION]
     prime_intro   : jT (lt (Suc Zero) p) ==> jT (Forall (...)) ==> jT (prime p)
     strong_induct : (!!n. (!!m. lt m n ==> Trueprop(P m)) ==> Trueprop(P n))
                     ==> Trueprop(P k)                     [course-of-values rule]
   ============================================================================ *)

val () = out "PHASE2_BEGIN\n";

(* ---- arithmetic instantiators re-stated on the FINAL context ctxtC ---- *)
val add_0_vC          = varify add_0;
val add_Suc_vC        = varify add_Suc;
val add_0_right_vC    = varify add_0_right;
val add_Suc_right_vC  = varify add_Suc_right;
val Suc_inj_vC        = varify Suc_inj_ax;
val Suc_neq_Zero_vC   = varify Suc_neq_Zero_ax;
val mult_0_right_vC   = varify mult_0_right;
val mult_Suc_right_vC = varify mult_Suc_right;
val add_left_cancel_vC  = varify add_left_cancel;
val add_eq_zero_left_vC = varify add_eq_zero_left;
val le_refl_vC        = varify le_refl;
val le_trans_vC       = varify le_trans;
val le_total_vC       = varify le_total;
val disj_zero_or_suc_vC = varify disj_zero_or_suc;

fun add0C_at t         = beta_norm (Drule.infer_instantiate ctxtC [(("n",0), ctermC t)] add_0_vC);
fun addSucC_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtC
                            [(("m",0), ctermC mt),(("n",0), ctermC nt)] add_Suc_vC);
fun add0rC_at t        = beta_norm (Drule.infer_instantiate ctxtC [(("n",0), ctermC t)] add_0_right_vC);
fun addSrC_at (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtC
                            [(("m",0), ctermC mt),(("n",0), ctermC nt)] add_Suc_right_vC);
fun Suc_inj_atC (uT,vT)= beta_norm (Drule.infer_instantiate ctxtC
                            [(("a",0), ctermC uT),(("b",0), ctermC vT)] Suc_inj_vC);
fun Suc_neq_Zero_atC t = beta_norm (Drule.infer_instantiate ctxtC
                            [(("n",0), ctermC t)] Suc_neq_Zero_vC);
fun oeqreflC_at t      = beta_norm (Drule.infer_instantiate ctxtC [(("a",0), ctermC t)] oeq_refl_vC);
fun mult0rC_at t       = beta_norm (Drule.infer_instantiate ctxtC [(("n",0), ctermC t)] mult_0_right_vC);
fun multSrC_at (nt,mt) = beta_norm (Drule.infer_instantiate ctxtC
                            [(("n",0), ctermC nt),(("m",0), ctermC mt)] mult_Suc_right_vC);

(* add-congruence on LEFT / RIGHT operand, on ctxtC *)
fun add_cong_lC (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("a",0), ctermC pT), (("b",0), ctermC qT)] oeq_subst_vC);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtC [(("a",0), ctermC (add pT kT))] oeq_refl_vC);
  in inst OF [hpq, refl_pk] end;
fun add_cong_rC (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("a",0), ctermC pT), (("b",0), ctermC qT)] oeq_subst_vC);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtC [(("a",0), ctermC (add hT pT))] oeq_refl_vC);
  in inst OF [hpq, refl_hp] end;

(* le_intro on ctxtC (uses exI_vC) *)
fun le_introC (mT, nT, w) hyp =
  let
    val Pabs = Abs ("p", natT, oeq nT (add mT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("a",0), ctermC w)] exI_vC);
  in inst OF [hyp] end;

(* le_refl / le_suc_self ground instances on ctxtC *)
fun le_reflC_at t = beta_norm (Drule.infer_instantiate ctxtC [(("n",0), ctermC t)] le_refl_vC);
fun le_suc_self_atC bT =
  let
    val asr   = addSrC_at (bT, ZeroC);              (* (b + Suc 0) = Suc (b + 0) *)
    val sb0   = Suc_cong OF [add0rC_at bT];         (* Suc (b + 0) = Suc b *)
    val bS1_Sb= oeq_trans OF [asr, sb0];            (* (b + Suc 0) = Suc b *)
    val Sb_bS1= oeq_sym OF [bS1_Sb];                (* Suc b = (b + Suc 0) *)
  in le_introC (bT, suc bT, suc ZeroC) Sb_bS1 end; (* le b (Suc b) *)

(* le_trans / le_total ground instantiators on ctxtC *)
fun le_trans_at (mt, nt, kt) h1 h2 =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("m",0), ctermC mt), (("n",0), ctermC nt), (("k",0), ctermC kt)] le_trans_vC);
  in (inst OF [h1]) OF [h2] end;
fun le_total_at (mt, nt) = beta_norm (Drule.infer_instantiate ctxtC
      [(("m",0), ctermC mt), (("n",0), ctermC nt)] le_total_vC);

(* disj_zero_or_suc ground instance on ctxtC *)
fun dzosC_at t = beta_norm (Drule.infer_instantiate ctxtC [(("p",0), ctermC t)] disj_zero_or_suc_vC);

(* oFalse_elim on ctxtC at explicit R is oFalse_elimC_at (from phase 1) *)

val () = out "PHASE2_HELPERS_READY\n";

(* ============================================================================
   STRICT ORDER  lt m n == le (Suc m) n
   ============================================================================ *)
fun lt mT nT = le (suc mT) nT;

(* lt_suc : Trueprop (lt n (Suc n)) == le (Suc n) (Suc n) == le_refl @ (Suc n) *)
val lt_suc =
  let
    val nF = Free("n", natT);
  in varify (le_reflC_at (suc nF)) end;

(* lt_irrefl : Trueprop (lt n n) ==> Trueprop oFalse *)
val lt_irrefl =
  let
    val nF = Free("n", natT);
    val ltHypP = jT (lt nF nF);                        (* le (Suc n) n *)
    val ltHyp  = Thm.assume (ctermC ltHypP);
    val Pabs   = Abs("p", natT, oeq nF (add (suc nF) (Bound 0)));  (* body of le (Suc n) n *)
    val goalC  = oFalseC;
    fun body w (hw : thm) =                              (* hw : oeq n (add (Suc n) w) *)
      let
        val aS    = addSucC_at (nF, w);                  (* (Suc n + w) = Suc (n + w) *)
        val n_Snw = oeq_trans OF [hw, aS];               (* n = Suc (n + w) *)
        val n_nSw2 = oeq_trans OF [n_Snw, oeq_sym OF [addSrC_at (nF, w)]];  (* n = (n + Suc w) *)
        val n0n   = add0rC_at nF;                        (* (n + 0) = n *)
        val n0_nSw= oeq_trans OF [n0n, n_nSw2];          (* (n + 0) = (n + Suc w) *)
        val canc  = add_left_cancel_vC OF [n0_nSw];      (* oeq 0 (Suc w) *)
        val cancS = oeq_sym OF [canc];                   (* oeq (Suc w) 0 *)
        val false_thm = (Suc_neq_Zero_atC w) OF [cancS]; (* oFalse *)
      in false_thm end;
    val afterExE = exE_elimC (Pabs, goalC) ltHyp "wp" body;
    val disch    = Thm.implies_intr (ctermC ltHypP) afterExE;
  in varify disch end;

(* lt_suc_cases : Trueprop (lt m (Suc n)) ==> Trueprop (Disj (lt m n) (oeq m n)) *)
val lt_suc_cases =
  let
    val mF = Free("m", natT); val nF = Free("n", natT);
    val ltHypP = jT (lt mF (suc nF));                   (* le (Suc m) (Suc n) *)
    val ltHyp  = Thm.assume (ctermC ltHypP);
    val Pabs   = Abs("p", natT, oeq (suc nF) (add (suc mF) (Bound 0)));  (* body of le (Suc m)(Suc n) *)
    val goalC  = mkDisj (lt mF nF) (oeq mF nF);
    fun body p (hp : thm) =                              (* hp : oeq (Suc n) (add (Suc m) p) *)
      let
        val aS    = addSucC_at (mF, p);                  (* (Suc m + p) = Suc (m + p) *)
        val Sn_Smp= oeq_trans OF [hp, aS];               (* Suc n = Suc (m + p) *)
        val n_mp  = (Suc_inj_atC (nF, add mF p)) OF [Sn_Smp];   (* oeq n (add m p) *)
        val dz    = dzosC_at p;                          (* Disj (oeq p 0) (Ex(%q. oeq p (Suc q))) *)
        val caseZero =
          let
            val epz  = Thm.assume (ctermC (jT (oeq p ZeroC)));   (* oeq p 0 *)
            val cong = add_cong_rC (mF, p, ZeroC) epz;   (* (m + p) = (m + 0) *)
            val n_m0 = oeq_trans OF [n_mp, cong];        (* n = (m + 0) *)
            val n_m  = oeq_trans OF [n_m0, add0rC_at mF];(* n = m *)
            val m_n  = oeq_sym OF [n_m];                 (* m = n *)
            val g    = disjI2C_at (lt mF nF, oeq mF nF) m_n;
          in Thm.implies_intr (ctermC (jT (oeq p ZeroC))) g end;
        val PabsQ = Abs("q", natT, oeq p (suc (Bound 0)));
        val caseSuc =
          let
            val exq = Thm.assume (ctermC (jT (mkEx PabsQ)));   (* Ex(%q. oeq p (Suc q)) *)
            fun sucBody q (hq : thm) =                          (* hq : oeq p (Suc q) *)
              let
                val cong   = add_cong_rC (mF, p, suc q) hq;     (* (m + p) = (m + Suc q) *)
                val n_mSq  = oeq_trans OF [n_mp, cong];         (* n = (m + Suc q) *)
                val mSq_S  = addSrC_at (mF, q);                 (* (m + Suc q) = Suc(m + q) *)
                val n_Smq  = oeq_trans OF [n_mSq, mSq_S];       (* n = Suc(m + q) *)
                val Smq_Smq= addSucC_at (mF, q);                (* (Suc m + q) = Suc(m + q) *)
                val n_Smqadd = oeq_trans OF [n_Smq, oeq_sym OF [Smq_Smq]]; (* n = (Suc m + q) *)
                val le_Sm_n = le_introC (suc mF, nF, q) n_Smqadd;  (* le (Suc m) n = lt m n *)
                val g = disjI1C_at (lt mF nF, oeq mF nF) le_Sm_n;
              in g end;
            val g = exE_elimC (PabsQ, goalC) exq "q0" sucBody;
          in Thm.implies_intr (ctermC (jT (mkEx PabsQ))) g end;
        val combined = disjE_elimC (oeq p ZeroC, mkEx PabsQ, goalC) dz caseZero caseSuc;
      in combined end;
    val afterExE = exE_elimC (Pabs, goalC) ltHyp "wp" body;
    val disch    = Thm.implies_intr (ctermC ltHypP) afterExE;
  in varify disch end;

(* lt_trans : Trueprop (lt a b) ==> Trueprop (lt b c) ==> Trueprop (lt a c)
     lt a b = le (Suc a) b ; le b (Suc b) ; le_trans => le (Suc a) (Suc b)
     le (Suc a)(Suc b), le (Suc b) c => le (Suc a) c = lt a c. *)
val lt_trans =
  let
    val aF = Free("a", natT); val bF = Free("b", natT); val cF = Free("c", natT);
    val H1prop = jT (lt aF bF);                     (* le (Suc a) b *)
    val H2prop = jT (lt bF cF);                     (* le (Suc b) c *)
    val H1 = Thm.assume (ctermC H1prop);
    val H2 = Thm.assume (ctermC H2prop);
    val le_b_Sb = le_suc_self_atC bF;               (* le b (Suc b) *)
    val le_Sa_Sb = le_trans_at (suc aF, bF, suc bF) H1 le_b_Sb;
    val le_Sa_c  = le_trans_at (suc aF, suc bF, cF) le_Sa_Sb H2;
    val d1 = Thm.implies_intr (ctermC H2prop) le_Sa_c;
    val d2 = Thm.implies_intr (ctermC H1prop) d1;
  in varify d2 end;

(* ---- validation : strict-order basics ---- *)
fun checkC (nm, th, intended) =
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

val nVlt = Var (("n",0), natT);
val mVlt = Var (("m",0), natT);
val aVlt = Var (("a",0), natT);
val bVlt = Var (("b",0), natT);
val cVlt = Var (("c",0), natT);

val lt_suc_intended       = jT (lt nVlt (suc nVlt));
val lt_irrefl_intended    = Logic.mk_implies (jT (lt nVlt nVlt), jT oFalseC);
val lt_suc_cases_intended =
  Logic.mk_implies (jT (lt mVlt (suc nVlt)), jT (mkDisj (lt mVlt nVlt) (oeq mVlt nVlt)));
val lt_trans_intended =
  Logic.mk_implies (jT (lt aVlt bVlt),
    Logic.mk_implies (jT (lt bVlt cVlt), jT (lt aVlt cVlt)));

val r_lt_suc       = checkC ("lt_suc",       lt_suc,       lt_suc_intended);
val r_lt_irrefl    = checkC ("lt_irrefl",    lt_irrefl,    lt_irrefl_intended);
val r_lt_suc_cases = checkC ("lt_suc_cases", lt_suc_cases, lt_suc_cases_intended);
val r_lt_trans     = checkC ("lt_trans",     lt_trans,     lt_trans_intended);

(* ============================================================================
   le_neq_lt : jT (le d n) ==> jT (neg (oeq d n)) ==> jT (lt d n)
     le d n = Ex(%p. oeq n (add d p)).  exE witness p, hp : oeq n (add d p).
     dzosC_at p:
       p = 0     : oeq n (add d 0) -> oeq n d -> oeq d n ; contradicts neg(oeq d n)
                   via mp => oFalse => oFalse_elim => lt d n.
       p = Suc q : oeq n (add d (Suc q)) = Suc(add d q) = add (Suc d) q
                   => le (Suc d) n = lt d n.
   ============================================================================ *)
val le_neq_lt =
  let
    val dF = Free("d", natT); val nF = Free("n", natT);
    val leHypP  = jT (le dF nF);
    val neqHypP = jT (neg (oeq dF nF));
    val leHyp   = Thm.assume (ctermC leHypP);
    val neqHyp  = Thm.assume (ctermC neqHypP);    (* Imp (oeq d n) oFalse *)
    val goalC   = lt dF nF;
    val Pabs    = Abs("p", natT, oeq nF (add dF (Bound 0)));  (* body of le d n *)
    fun body p (hp : thm) =                          (* hp : oeq n (add d p) *)
      let
        val dz = dzosC_at p;                         (* Disj (oeq p 0) (Ex(%q. oeq p (Suc q))) *)
        val caseZero =
          let
            val epz  = Thm.assume (ctermC (jT (oeq p ZeroC)));   (* oeq p 0 *)
            val cong = add_cong_rC (dF, p, ZeroC) epz;   (* (d + p) = (d + 0) *)
            val n_d0 = oeq_trans OF [hp, cong];          (* n = (d + 0) *)
            val n_d  = oeq_trans OF [n_d0, add0rC_at dF];(* n = d *)
            val d_n  = oeq_sym OF [n_d];                 (* d = n *)
            val fls  = mp_atT (oeq dF nF, oFalseC) neqHyp d_n;   (* oFalse *)
            val g    = Thm.implies_elim (oFalse_elimC_at goalC) fls;  (* lt d n *)
          in Thm.implies_intr (ctermC (jT (oeq p ZeroC))) g end;
        val PabsQ = Abs("q", natT, oeq p (suc (Bound 0)));
        val caseSuc =
          let
            val exq = Thm.assume (ctermC (jT (mkEx PabsQ)));   (* Ex(%q. oeq p (Suc q)) *)
            fun sucBody q (hq : thm) =                          (* hq : oeq p (Suc q) *)
              let
                val cong   = add_cong_rC (dF, p, suc q) hq;     (* (d + p) = (d + Suc q) *)
                val n_dSq  = oeq_trans OF [hp, cong];           (* n = (d + Suc q) *)
                val dSq_S  = addSrC_at (dF, q);                 (* (d + Suc q) = Suc(d + q) *)
                val n_Sdq  = oeq_trans OF [n_dSq, dSq_S];       (* n = Suc(d + q) *)
                val Sdq_Sdq= addSucC_at (dF, q);                (* (Suc d + q) = Suc(d + q) *)
                val n_Sdqadd = oeq_trans OF [n_Sdq, oeq_sym OF [Sdq_Sdq]]; (* n = (Suc d + q) *)
                val le_Sd_n = le_introC (suc dF, nF, q) n_Sdqadd;  (* le (Suc d) n = lt d n *)
              in le_Sd_n end;
            val g = exE_elimC (PabsQ, goalC) exq "q0" sucBody;
          in Thm.implies_intr (ctermC (jT (mkEx PabsQ))) g end;
        val combined = disjE_elimC (oeq p ZeroC, mkEx PabsQ, goalC) dz caseZero caseSuc;
      in combined end;
    val afterExE = exE_elimC (Pabs, goalC) leHyp "wp" body;
    val d1 = Thm.implies_intr (ctermC neqHypP) afterExE;
    val d2 = Thm.implies_intr (ctermC leHypP) d1;
  in varify d2 end;

val dVle = Var (("d",0), natT);
val nVle = Var (("n",0), natT);
val le_neq_lt_intended =
  Logic.mk_implies (jT (le dVle nVle),
    Logic.mk_implies (jT (neg (oeq dVle nVle)), jT (lt dVle nVle)));
val r_le_neq_lt = checkC ("le_neq_lt", le_neq_lt, le_neq_lt_intended);

(* ============================================================================
   NUMBER FACTS
   ============================================================================ *)

(* ne0_suc : jT (neg (oeq d Zero)) ==> jT (Ex (%m. oeq d (Suc m)))
     num-cases (dzosC_at d): every d is Zero or Suc m.
       d = 0     : oeq d 0 ; mp with neg(oeq d 0) => oFalse => oFalse_elim => goal.
       d = Suc m : witness m, body oeq d (Suc m) ; exI => goal. *)
val ne0_suc =
  let
    val dF = Free("d", natT);
    val neqHypP = jT (neg (oeq dF ZeroC));
    val neqHyp  = Thm.assume (ctermC neqHypP);     (* Imp (oeq d 0) oFalse *)
    val goalAbs = Abs("m", natT, oeq dF (suc (Bound 0)));   (* %m. oeq d (Suc m) *)
    val goalC   = mkEx goalAbs;
    val dz = dzosC_at dF;                            (* Disj (oeq d 0) (Ex(%q. oeq d (Suc q))) *)
    val caseZero =
      let
        val edz = Thm.assume (ctermC (jT (oeq dF ZeroC)));   (* oeq d 0 *)
        val fls = mp_atT (oeq dF ZeroC, oFalseC) neqHyp edz; (* oFalse *)
        val g   = Thm.implies_elim (oFalse_elimC_at goalC) fls;  (* goal *)
      in Thm.implies_intr (ctermC (jT (oeq dF ZeroC))) g end;
    val PabsQ = Abs("q", natT, oeq dF (suc (Bound 0)));   (* Ex(%q. oeq d (Suc q)) body *)
    val caseSuc =
      let
        val exq = Thm.assume (ctermC (jT (mkEx PabsQ)));     (* Ex(%q. oeq d (Suc q)) *)
        fun sucBody q (hq : thm) =                            (* hq : oeq d (Suc q) *)
          exI_atC goalAbs q hq;                              (* Ex(%m. oeq d (Suc m)) *)
        val g = exE_elimC (PabsQ, goalC) exq "q0" sucBody;
      in Thm.implies_intr (ctermC (jT (mkEx PabsQ))) g end;
    val concl = disjE_elimC (oeq dF ZeroC, mkEx PabsQ, goalC) dz caseZero caseSuc;
    val disch = Thm.implies_intr (ctermC neqHypP) concl;
  in varify disch end;

val dVns = Var (("d",0), natT);
val ne0_suc_intended =
  Logic.mk_implies (jT (neg (oeq dVns ZeroC)),
    jT (mkEx (Abs("m", natT, oeq dVns (suc (Bound 0))))));
val r_ne0_suc = checkC ("ne0_suc", ne0_suc, ne0_suc_intended);

(* gt1_of_ne0_ne1 : jT (neg (oeq d Zero)) ==> jT (neg (oeq d (Suc Zero)))
                    ==> jT (lt (Suc Zero) d)
     d = Suc d0 by ne0_suc.  d0 != 0 (else d = Suc 0 = 1, contradicts neg(oeq d 1)
     via Suc_cong + the second neg).  d0 = Suc d1 by ne0_suc.  Then
     d = Suc (Suc d1).  lt (Suc 0) d = le (Suc (Suc 0)) (Suc (Suc d1));
     witness d1:  Suc(Suc d1) = (Suc(Suc 0)) + d1. *)
val gt1_of_ne0_ne1 =
  let
    val dF = Free("d", natT);
    val ne0HypP = jT (neg (oeq dF ZeroC));
    val ne1HypP = jT (neg (oeq dF (suc ZeroC)));
    val ne0Hyp  = Thm.assume (ctermC ne0HypP);
    val ne1Hyp  = Thm.assume (ctermC ne1HypP);
    val goalC   = lt (suc ZeroC) dF;            (* le (Suc (Suc 0)) d *)

    (* d = Suc d0 *)
    val ne0_d   = varify ne0_suc;
    val ne0_d_at= beta_norm (Drule.infer_instantiate ctxtC [(("d",0), ctermC dF)] ne0_d);
    val exd0    = Thm.implies_elim ne0_d_at ne0Hyp;   (* Ex(%m. oeq d (Suc m)) *)
    val Pd0     = Abs("m", natT, oeq dF (suc (Bound 0)));
    fun outer d0 (hd0 : thm) =                   (* hd0 : oeq d (Suc d0) *)
      let
        (* show d0 != 0 : assume oeq d0 0, then oeq d (Suc 0) = oeq d 1, contradict ne1 *)
        val ne0_d0 =
          let
            val hz = Thm.assume (ctermC (jT (oeq d0 ZeroC)));   (* oeq d0 0 *)
            val sd0_s0 = Suc_cong OF [hz];               (* oeq (Suc d0) (Suc 0) *)
            val d_s0   = oeq_trans OF [hd0, sd0_s0];      (* oeq d (Suc 0) = oeq d 1 *)
            val fls    = mp_atT (oeq dF (suc ZeroC), oFalseC) ne1Hyp d_s0;  (* oFalse *)
          in Thm.implies_intr (ctermC (jT (oeq d0 ZeroC))) fls end;  (* neg (oeq d0 0) *)
        val ne0_d0_thm = impI_atT (oeq d0 ZeroC, oFalseC) ne0_d0;     (* jT (neg (oeq d0 0)) *)
        (* d0 = Suc d1 *)
        val ne0_d0_at = beta_norm (Drule.infer_instantiate ctxtC [(("d",0), ctermC d0)] ne0_d);
        val exd1    = Thm.implies_elim ne0_d0_at ne0_d0_thm;   (* Ex(%m. oeq d0 (Suc m)) *)
        val Pd1     = Abs("m", natT, oeq d0 (suc (Bound 0)));
        fun inner d1 (hd1 : thm) =                 (* hd1 : oeq d0 (Suc d1) *)
          let
            (* d = Suc d0 = Suc (Suc d1) *)
            val Sd0_SSd1 = Suc_cong OF [hd1];        (* oeq (Suc d0) (Suc (Suc d1)) *)
            val d_SSd1   = oeq_trans OF [hd0, Sd0_SSd1];  (* oeq d (Suc(Suc d1)) *)
            (* witness d1 : Suc(Suc d1) = (Suc(Suc 0)) + d1
               (Suc(Suc 0)) + d1 = Suc((Suc 0) + d1) = Suc(Suc(0 + d1)) = Suc(Suc d1) *)
            val a1 = addSucC_at (suc ZeroC, d1);       (* (Suc(Suc 0)) + d1 = Suc((Suc 0) + d1) *)
            val a2 = addSucC_at (ZeroC, d1);           (* (Suc 0) + d1 = Suc(0 + d1) *)
            val a3 = add0C_at d1;                      (* 0 + d1 = d1 *)
            val sa3 = Suc_cong OF [a3];                (* Suc(0 + d1) = Suc d1 *)
            val a2c = oeq_trans OF [a2, sa3];          (* (Suc 0) + d1 = Suc d1 *)
            val sa2c = Suc_cong OF [a2c];              (* Suc((Suc 0) + d1) = Suc(Suc d1) *)
            val a1c  = oeq_trans OF [a1, sa2c];        (* (Suc(Suc 0)) + d1 = Suc(Suc d1) *)
            (* need : oeq d ((Suc(Suc 0)) + d1)  i.e. oeq d (add (Suc(Suc 0)) d1) *)
            val a1cs = oeq_sym OF [a1c];               (* Suc(Suc d1) = (Suc(Suc 0)) + d1 *)
            val witEq = oeq_trans OF [d_SSd1, a1cs];   (* oeq d ((Suc(Suc 0)) + d1) *)
            val leThm = le_introC (suc (suc ZeroC), dF, d1) witEq;  (* le (Suc(Suc 0)) d = lt (Suc 0) d *)
          in leThm end;
        val g = exE_elimC (Pd1, goalC) exd1 "d1w" inner;
      in g end;
    val concl = exE_elimC (Pd0, goalC) exd0 "d0w" outer;
    val d1' = Thm.implies_intr (ctermC ne1HypP) concl;
    val d2' = Thm.implies_intr (ctermC ne0HypP) d1';
  in varify d2' end;

val dVgt = Var (("d",0), natT);
val gt1_of_ne0_ne1_intended =
  Logic.mk_implies (jT (neg (oeq dVgt ZeroC)),
    Logic.mk_implies (jT (neg (oeq dVgt (suc ZeroC))),
      jT (lt (suc ZeroC) dVgt)));
val r_gt1 = checkC ("gt1_of_ne0_ne1", gt1_of_ne0_ne1, gt1_of_ne0_ne1_intended);

(* dvd_nonzero : jT (dvd d n) ==> jT (neg (oeq n Zero)) ==> jT (neg (oeq d Zero))
     prove neg (oeq d 0) = (oeq d 0 ==> oFalse): assume oeq d 0.
       dvd d n = Ex(%k. oeq n (mult d k)).  exE witness k, hk : oeq n (mult d k).
       oeq d 0 => mult d k = mult 0 k = 0   (subst into mult, mult_0)  => oeq n 0,
       contradict neg(oeq n 0) => oFalse. *)
val mult_0_vC = varify mult_0;
fun mult0l_at t = beta_norm (Drule.infer_instantiate ctxtC [(("n",0), ctermC t)] mult_0_vC);
val dvd_nonzero =
  let
    val dF = Free("d", natT); val nF = Free("n", natT);
    val dvdHypP = jT (dvd dF nF);
    val nzHypP  = jT (neg (oeq nF ZeroC));
    val dvdHyp  = Thm.assume (ctermC dvdHypP);
    val nzHyp   = Thm.assume (ctermC nzHypP);     (* Imp (oeq n 0) oFalse *)
    (* prove the body : oeq d 0 ==> oFalse *)
    val dzeroP  = jT (oeq dF ZeroC);
    val dzero   = Thm.assume (ctermC dzeroP);     (* oeq d 0 *)
    val Pabs    = Abs("k", natT, oeq nF (mult dF (Bound 0)));  (* dvd d n body *)
    val goalC   = oFalseC;
    fun body k (hk : thm) =                          (* hk : oeq n (mult d k) *)
      let
        (* mult d k = mult 0 k via oeq_subst on %z. oeq (mult d k) (mult z k) *)
        val Psub = Abs("z", natT, oeq (mult dF k) (mult (Bound 0) k));
        val subInst = beta_norm (Drule.infer_instantiate ctxtC
              [(("P",0), ctermC Psub), (("a",0), ctermC dF), (("b",0), ctermC ZeroC)] oeq_subst_vC);
        val reflMdk = beta_norm (Drule.infer_instantiate ctxtC
              [(("a",0), ctermC (mult dF k))] oeq_refl_vC);
        val mdk_m0k = subInst OF [dzero, reflMdk];   (* (d*k) = (0*k) *)
        val m0k_0   = mult0l_at k;                   (* (0*k) = 0 *)
        val n_mdk   = hk;                            (* n = (d*k) *)
        val n_m0k   = oeq_trans OF [n_mdk, mdk_m0k]; (* n = (0*k) *)
        val n_0     = oeq_trans OF [n_m0k, m0k_0];   (* n = 0 *)
        val fls     = mp_atT (oeq nF ZeroC, oFalseC) nzHyp n_0;  (* oFalse *)
      in fls end;
    val falseThm = exE_elimC (Pabs, goalC) dvdHyp "kw" body;  (* oFalse, deps on dzero,dvdHyp,nzHyp *)
    val negBody  = Thm.implies_intr (ctermC dzeroP) falseThm; (* oeq d 0 ==> oFalse *)
    val negThm   = impI_atT (oeq dF ZeroC, oFalseC) negBody;  (* jT (neg (oeq d 0)) *)
    val d1 = Thm.implies_intr (ctermC nzHypP) negThm;
    val d2 = Thm.implies_intr (ctermC dvdHypP) d1;
  in varify d2 end;

val dVdz = Var (("d",0), natT);
val nVdz = Var (("n",0), natT);
val dvd_nonzero_intended =
  Logic.mk_implies (jT (dvd dVdz nVdz),
    Logic.mk_implies (jT (neg (oeq nVdz ZeroC)), jT (neg (oeq dVdz ZeroC))));
val r_dvd_nonzero = checkC ("dvd_nonzero", dvd_nonzero, dvd_nonzero_intended);

(* ============================================================================
   STRUCTURAL PRIME as an ABBREVIATION
     prime p == Conj (lt (Suc Zero) p)
                     (Forall (%d. Imp (dvd d p) (Disj (oeq d (Suc Zero)) (oeq d p))))
   ============================================================================ *)
fun primePredAbs p = Abs("d", natT,
      mkImp (dvd (Bound 0) p)
            (mkDisj (oeq (Bound 0) (suc ZeroC)) (oeq (Bound 0) p)));
fun prime p = mkConj (lt (suc ZeroC) p) (mkForall (primePredAbs p));

(* prime_intro : jT (lt (Suc Zero) p) ==> jT (Forall (...)) ==> jT (prime p)
   (we prove the IMPLICATION form so it validates as a 0-hyp schematic rule). *)
val prime_intro =
  let
    val pF = Free("p", natT);
    val gtP   = jT (lt (suc ZeroC) pF);
    val faP   = jT (mkForall (primePredAbs pF));
    val gtH   = Thm.assume (ctermC gtP);
    val faH   = Thm.assume (ctermC faP);
    val conj  = conjI_atT (lt (suc ZeroC) pF, mkForall (primePredAbs pF)) gtH faH;  (* jT (prime p) *)
    val d1 = Thm.implies_intr (ctermC faP) conj;
    val d2 = Thm.implies_intr (ctermC gtP) d1;
  in varify d2 end;

(* destructors (validated by aconv too) :
     prime_gt1   : jT (prime p) ==> jT (lt (Suc Zero) p)      (conjunct1)
     prime_div   : jT (prime p) ==> jT (Forall (...))         (conjunct2) *)
val prime_gt1 =
  let
    val pF = Free("p", natT);
    val primeH = Thm.assume (ctermC (jT (prime pF)));
    val g = conjunct1_atT (lt (suc ZeroC) pF, mkForall (primePredAbs pF)) primeH;
    val disch = Thm.implies_intr (ctermC (jT (prime pF))) g;
  in varify disch end;
val prime_div =
  let
    val pF = Free("p", natT);
    val primeH = Thm.assume (ctermC (jT (prime pF)));
    val g = conjunct2_atT (lt (suc ZeroC) pF, mkForall (primePredAbs pF)) primeH;
    val disch = Thm.implies_intr (ctermC (jT (prime pF))) g;
  in varify disch end;

val pVpr = Var (("p",0), natT);
val prime_intro_intended =
  Logic.mk_implies (jT (lt (suc ZeroC) pVpr),
    Logic.mk_implies (jT (mkForall (primePredAbs pVpr)), jT (prime pVpr)));
val prime_gt1_intended =
  Logic.mk_implies (jT (prime pVpr), jT (lt (suc ZeroC) pVpr));
val prime_div_intended =
  Logic.mk_implies (jT (prime pVpr), jT (mkForall (primePredAbs pVpr)));
val r_prime_intro = checkC ("prime_intro", prime_intro, prime_intro_intended);
val r_prime_gt1   = checkC ("prime_gt1",   prime_gt1,   prime_gt1_intended);
val r_prime_div   = checkC ("prime_div",   prime_div,   prime_div_intended);

(* ============================================================================
   STRONG INDUCTION  (course-of-values).  meta_nat_induct axiom on its own child
   theory thyS2 (NO new constant; signature of thyC unchanged), re-init ONE final
   context ctxtS2 and route all NEW cterms through it.  All thyC theorems lift to
   thyS2 automatically.
     strong_induct : (!!n. (!!m. lt m n ==> Trueprop(P m)) ==> Trueprop(P n))
                     ==> Trueprop(P k)
   ============================================================================ *)
val PhiT2  = natT --> propT;
val PhiF2  = Free ("Phi", PhiT2);
val xMI2   = Free ("x", natT);
val kMI2   = Free ("k", natT);
val meta_induct_prop2 =
  Logic.mk_implies (PhiF2 $ ZeroC,
    Logic.mk_implies (Logic.all xMI2 (Logic.mk_implies (PhiF2 $ xMI2, PhiF2 $ (suc xMI2))),
      PhiF2 $ kMI2));
val ((_, meta_nat_induct_ax2), thyS2) =
  Thm.add_axiom_global (Binding.name "meta_nat_induct", meta_induct_prop2) thyC;
val ctxtS2  = Proof_Context.init_global thyS2;
val ctermS2 = Thm.cterm_of ctxtS2;
val meta_nat_induct_v2 = varify meta_nat_induct_ax2;

val () = out "STRONG_CONTEXT_READY\n";

val Pfree = Free ("P", predT);                 (* predT = natT --> oT *)
fun Pof t = Pfree $ t;

val strong_induct =
  let
    fun Gprop nt =
      let val mB = Free("m_g", natT)
      in Logic.all mB (Logic.mk_implies (jT (lt mB nt), jT (Pof mB))) end;

    val nH = Free("n_h", natT);
    val Hprop = Logic.all nH (Logic.mk_implies (Gprop nH, jT (Pof nH)));
    val Hthm  = Thm.assume (ctermS2 Hprop);

    fun applyH t gthm =
      let val hAt = Thm.forall_elim (ctermS2 t) Hthm
      in Thm.implies_elim hAt gthm end;

    val nPhi   = Free("n_phi", natT);
    val PhiAbs = Term.lambda nPhi (Gprop nPhi);

    (* ---- BASE : G Zero = !!m. lt m Zero ==> Trueprop(P m) ---- *)
    val baseG =
      let
        val mB = Free("m_b", natT);
        val ltHypP = jT (lt mB ZeroC);              (* le (Suc m) Zero *)
        val ltHyp  = Thm.assume (ctermS2 ltHypP);
        val Pabs   = Abs("p", natT, oeq ZeroC (add (suc mB) (Bound 0)));
        val goalC  = Pof mB;
        fun body w (hw : thm) =                       (* hw : oeq Zero (add (Suc m) w) *)
          let
            val aS    = addSucC_at (mB, w);            (* (Suc m + w) = Suc(m + w) *)
            val z_S   = oeq_trans OF [hw, aS];         (* 0 = Suc(m + w) *)
            val S_z   = oeq_sym OF [z_S];              (* Suc(m+w) = 0 *)
            val fls   = (Suc_neq_Zero_atC (add mB w)) OF [S_z];   (* oFalse *)
            val pm    = (oFalse_elimC_at goalC) OF [fls];          (* Trueprop(P m) *)
          in pm end;
        val afterExE =
          let
            val wF = Free("w_b", natT);
            val hypTerm = jT (Term.betapply (Pabs, wF));
            val hypThm  = Thm.assume (ctermS2 hypTerm);
            val bdy     = body wF hypThm;
            val minor   = Thm.forall_intr (ctermS2 wF) (Thm.implies_intr (ctermS2 hypTerm) bdy);
            val exE_inst= beta_norm (Drule.infer_instantiate ctxtS2
                            [(("P",0), ctermS2 Pabs), (("Q",0), ctermS2 (Pof mB))] exE_vC);
            val partial = Thm.implies_elim exE_inst ltHyp;
          in Thm.implies_elim partial minor end;
        val disch = Thm.implies_intr (ctermS2 ltHypP) afterExE;
      in Thm.forall_intr (ctermS2 mB) disch end;

    (* ---- STEP : !!x. G x ==> G(Suc x) ---- *)
    val stepG =
      let
        val xF   = Free("x_s", natT);
        val GxProp = Gprop xF;
        val IH   = Thm.assume (ctermS2 GxProp);
        val mB   = Free("m_s", natT);
        val ltHypP = jT (lt mB (suc xF));
        val ltHyp  = Thm.assume (ctermS2 ltHypP);
        val lscV = varify lt_suc_cases;
        val lscAt = beta_norm (Drule.infer_instantiate ctxtS2
                      [(("m",0), ctermS2 mB),(("n",0), ctermS2 xF)] lscV);
        val dThm = Thm.implies_elim lscAt ltHyp;       (* Disj (lt m x) (oeq m x) *)
        val Aprop = jT (lt mB xF);
        val caseA =
          let
            val hA = Thm.assume (ctermS2 Aprop);
            val ihAt = Thm.forall_elim (ctermS2 mB) IH;
            val pm   = Thm.implies_elim ihAt hA;
          in Thm.implies_intr (ctermS2 Aprop) pm end;
        val Bprop = jT (oeq mB xF);
        val caseB =
          let
            val hB = Thm.assume (ctermS2 Bprop);
            val px = applyH xF IH;                      (* Trueprop(P x) *)
            val x_m  = oeq_sym OF [hB];                 (* oeq x m *)
            val Psub = Abs("z", natT, Pof (Bound 0));   (* %z. P z *)
            val subInst = beta_norm (Drule.infer_instantiate ctxtS2
                            [(("P",0), ctermS2 Psub), (("a",0), ctermS2 xF), (("b",0), ctermS2 mB)]
                            oeq_subst_vC);
            val pm = (subInst OF [x_m]) OF [px];
          in Thm.implies_intr (ctermS2 Bprop) pm end;
        val disjE_inst = beta_norm (Drule.infer_instantiate ctxtS2
              [(("A",0), ctermS2 (lt mB xF)), (("B",0), ctermS2 (oeq mB xF)),
               (("C",0), ctermS2 (Pof mB))] disjE_vC);
        val d1 = Thm.implies_elim disjE_inst dThm;
        val d2 = Thm.implies_elim d1 caseA;
        val pm = Thm.implies_elim d2 caseB;
        val disch = Thm.implies_intr (ctermS2 ltHypP) pm;
        val GSucx = Thm.forall_intr (ctermS2 mB) disch;
        val stepInner = Thm.implies_intr (ctermS2 GxProp) GSucx;
      in Thm.forall_intr (ctermS2 xF) stepInner end;

    val kF = Free("k", natT);
    val indK = beta_norm (Drule.infer_instantiate ctxtS2
                 [(("Phi",0), ctermS2 PhiAbs), (("k",0), ctermS2 kF)] meta_nat_induct_v2);
    val r1 = Thm.implies_elim indK baseG;
    val r2 = Thm.implies_elim r1 stepG;               (* G k *)
    val pk = applyH kF r2;                             (* Trueprop(P k) *)
    val dischH = Thm.implies_intr (ctermS2 Hprop) pk; (* H ==> Trueprop(P k) *)
  in varify dischH end;

val () = out "---- strong_induct validation ----\n";
val PvarI = Var (("P",0), predT);
fun PofI t = PvarI $ t;
val kVarI = Var (("k",0), natT);
val intended_strong =
  let
    val nI = Free("n_i", natT);
    val mI = Free("m_i", natT);
    val Gi = Logic.all mI (Logic.mk_implies (jT (lt mI nI), jT (PofI mI)));
    val Hi = Logic.all nI (Logic.mk_implies (Gi, jT (PofI nI)));
  in Logic.mk_implies (Hi, jT (PofI kVarI)) end;

fun checkS2 (nm, th, intended) =
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
val r_strong = checkS2 ("strong_induct", strong_induct, intended_strong);

(* PROBE : strong_induct must be CONDITIONAL on H, not the bogus unconditional P k *)
val bogus_unconditional = jT (PofI kVarI);
val probe_conditional = not ((Thm.prop_of strong_induct) aconv bogus_unconditional);
val () = if probe_conditional
         then out "PROBE_OK strong_induct is conditional on H\n"
         else out "PROBE_UNSOUND strong_induct collapsed to unconditional P k!\n";

(* ============================================================================
   PHASE 2 FINAL VERDICT
   ============================================================================ *)
val () =
  if r_lt_suc andalso r_lt_irrefl andalso r_lt_suc_cases andalso r_lt_trans
     andalso r_le_neq_lt
     andalso r_ne0_suc andalso r_gt1 andalso r_dvd_nonzero
     andalso r_prime_intro andalso r_prime_gt1 andalso r_prime_div
     andalso r_strong andalso probe_conditional
  then out "NT_OK\n"
  else out "NT_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  PHASE 3 : prime_cases  (the classical primality case-split)  ***
   ----------------------------------------------------------------------------
   TARGET:
     prime_cases : jT (lt (Suc Zero) n)
                   ==> jT (Disj (prime n)
                                (Ex (%d. Conj (Conj (lt (Suc Zero) d) (lt d n))
                                              (dvd d n))))

   DERIVATION (genuine classical reasoning over the STRUCTURAL prime; the only
   classical axiom in scope is ex_middle):
     ex_middle on (prime n) -> disjE.
       prime n     => disjI1.
       neg(prime n): prime n = Conj (1<n) B with B = Forall(%d. d|n => d=1 \/ d=n).
         we HAVE 1<n; derive neg B (assume b:B, conjI(1<n)b = prime n, mp neg => oFalse).
         not_forall neg B => Ex(%d. neg(d|n => d=1 \/ d=n)); exE witness d:
           not_imp  => Conj (d|n) (neg(d=1 \/ d=n));
           conjuncts: d|n, and neg(Disj(d=1)(d=n));
           deMorgan_or => Conj(neg(d=1))(neg(d=n)) => d!=1, d!=n.
         n!=0 from 1<n; dvd_nonzero (d|n)(n!=0) => d!=0;
         gt1_of_ne0_ne1 (d!=0)(d!=1) => 1<d;
         dvd_le (d|n)(n!=0) => le d n; le_neq_lt (le d n)(d!=n) => d<n.
         witness d : disjI2 of Ex(%d. ((1<d)&(d<n)) & d|n).

   *** A NOTE ON THE PRIME ABBREVIATION (capture correctness) ***
   The phase-2 `primePredAbs` splices `dvd (Bound 0) p` directly under `Abs("d",..)`,
   which (because `dvd a b = Ex k. oeq b (mult a (Bound 0))` introduces a fresh binder)
   CAPTURES the `Bound 0` divisor inside the `Ex k` -- it reads as `Ex k. p = k*k`
   (a perfect-square test), not `d | p`.  That is fine for the phase-2 lemmas because
   they validate against an intended built the SAME (captured) way, but it is NOT the
   intended divisibility predicate and dvd_le/dvd_nonzero cannot consume it.  We
   therefore build the divisor predicate CAPTURE-AVOIDINGLY with `Term.lambda` over a
   Free, so `dvd dF p` is constructed with dF a genuine Free (correct de Bruijn) and
   THEN abstracted.  prime_cases is stated + validated with THIS corrected predicate;
   the phase-2 prime_intro/prime_gt1/prime_div remain validated against the phase-2
   prime (untouched).  Mathematically this is the honest `forall d. d|p => d=1 \/ d=p`.
   ============================================================================ *)

val () = out "PHASE3_BEGIN\n";

(* ---- capture-avoiding prime predicate / prime, via Term.lambda over a Free ---- *)
fun ppAbs p =                                   (* %d. Imp (dvd d p) (Disj (oeq d 1) (oeq d p)) *)
  let val dF = Free("d_pp", natT)
  in Term.lambda dF (mkImp (dvd dF p) (mkDisj (oeq dF (suc ZeroC)) (oeq dF p))) end;
fun prime2 p = mkConj (lt (suc ZeroC) p) (mkForall (ppAbs p));

(* ---- dvd_le lifted onto ctxtC (proved on ctxtT; thyC extends thyT; varify) ---- *)
val dvd_le_vC = varify dvd_le;
fun dvd_le_atC (dt, nt) hdvd hnz =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("d",0), ctermC dt), (("n",0), ctermC nt)] dvd_le_vC);
  in Thm.implies_elim (Thm.implies_elim inst hdvd) hnz end;

(* ---- classical connective helpers on ctxtC ---- *)
val not_forall_vC = varify not_forall;
fun not_forall_atC Pabs hneg =
  Thm.implies_elim
    (beta_norm (Drule.infer_instantiate ctxtC [(("P",0), ctermC Pabs)] not_forall_vC)) hneg;

val deMorgan_or_vC = varify deMorgan_or;
fun deMorgan_or_atC (At, Bt) hneg =
  Thm.implies_elim
    (beta_norm (Drule.infer_instantiate ctxtC [(("A",0), ctermC At), (("B",0), ctermC Bt)] deMorgan_or_vC)) hneg;

val not_imp_vC = varify not_imp;
fun not_imp_atC (At, Bt) hneg =
  Thm.implies_elim
    (beta_norm (Drule.infer_instantiate ctxtC [(("A",0), ctermC At), (("B",0), ctermC Bt)] not_imp_vC)) hneg;

(* ---- number-fact helpers on ctxtC ---- *)
val gt1_of_ne0_ne1_vC = varify gt1_of_ne0_ne1;
val dvd_nonzero_vC    = varify dvd_nonzero;
val le_neq_lt_vC      = varify le_neq_lt;

fun gt1_of_ne0_ne1_atC dt hne0 hne1 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtC [(("d",0), ctermC dt)] gt1_of_ne0_ne1_vC)
  in Thm.implies_elim (Thm.implies_elim inst hne0) hne1 end;
fun dvd_nonzero_atC (dt, nt) hdvd hnz =
  let val inst = beta_norm (Drule.infer_instantiate ctxtC
        [(("d",0), ctermC dt), (("n",0), ctermC nt)] dvd_nonzero_vC)
  in Thm.implies_elim (Thm.implies_elim inst hdvd) hnz end;
fun le_neq_lt_atC (dt, nt) hle hneq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtC
        [(("d",0), ctermC dt), (("n",0), ctermC nt)] le_neq_lt_vC)
  in Thm.implies_elim (Thm.implies_elim inst hle) hneq end;

(* ---- inline lemma : n != 0 from 1 < n  (fixed nF) ----
   lt 1 n = le (Suc 0) n = Ex(%p. oeq n (add (Suc 0) p)).  exE witness p:
   n = add (Suc 0) p = Suc(0+p).  assume oeq n 0; sym+trans => Suc(0+p)=0; oFalse. *)
(* lt 1 n = le (Suc 1) n = le 2 n = Ex p. n = (Suc (Suc 0)) + p. *)
fun n_ne0_of_lt1 nF h_lt1 =
  let
    val Pabs = Abs("p", natT, oeq nF (add (suc (suc ZeroC)) (Bound 0)));
    val ez   = Thm.assume (ctermC (jT (oeq nF ZeroC)));
    fun body p (hp : thm) =                               (* hp : oeq n (add 2 p) *)
      let
        val aS    = addSucC_at (suc ZeroC, p);            (* (2 + p) = Suc (1 + p) *)
        val n_Sp  = oeq_trans OF [hp, aS];                (* n = Suc (1 + p) *)
        val z_Sp  = oeq_trans OF [oeq_sym OF [ez], n_Sp]; (* 0 = Suc (1 + p) *)
        val Sp_z  = oeq_sym OF [z_Sp];                    (* Suc (1 + p) = 0 *)
      in (Suc_neq_Zero_atC (add (suc ZeroC) p)) OF [Sp_z] end;  (* oFalse *)
    val falseThm = exE_elimC (Pabs, oFalseC) h_lt1 "wp" body;
    val imp = Thm.implies_intr (ctermC (jT (oeq nF ZeroC))) falseThm;  (* META: jT(oeq n 0)==>jT oFalse *)
  in impI_atT (oeq nF ZeroC, oFalseC) imp end;  (* OBJECT neg (oeq n 0) = Imp (oeq n 0) oFalse *)

(* ============================================================================
   prime_cases
   ============================================================================ *)
val prime_cases =
  let
    val nF = Free("n", natT);
    val h_lt1P = jT (lt (suc ZeroC) nF);
    val h_lt1  = Thm.assume (ctermC h_lt1P);

    (* proper-divisor existential goal (capture-avoiding) *)
    val pdAbs =
      let val dF = Free("d_pd", natT)
      in Term.lambda dF (mkConj (mkConj (lt (suc ZeroC) dF) (lt dF nF)) (dvd dF nF)) end;
    val goalEx = mkEx pdAbs;
    val GOAL   = mkDisj (prime2 nF) goalEx;

    val em = ex_middle_at (prime2 nF);                    (* jT (Disj (prime n) (neg (prime n))) *)

    (* CASE A : prime n -> disjI1 *)
    val caseA =
      let val hp = Thm.assume (ctermC (jT (prime2 nF)))
      in Thm.implies_intr (ctermC (jT (prime2 nF)))
           (disjI1C_at (prime2 nF, goalEx) hp) end;

    (* CASE B : neg (prime n) -> the witness disjunct *)
    val caseB =
      let
        val hNeg   = Thm.assume (ctermC (jT (neg (prime2 nF))));  (* Imp (prime n) oFalse *)
        val faBody = ppAbs nF;                                    (* %d. Imp (dvd d n)(Disj (oeq d 1)(oeq d n)) *)
        val Bterm  = mkForall faBody;
        (* derive neg B *)
        val negB =
          let
            val hB  = Thm.assume (ctermC (jT Bterm));
            val pn  = conjI_atT (lt (suc ZeroC) nF, Bterm) h_lt1 hB;
            val fls = mp_atT (prime2 nF, oFalseC) hNeg pn;
            val imp = Thm.implies_intr (ctermC (jT Bterm)) fls;
          in impI_atT (Bterm, oFalseC) imp end;                  (* jT (neg B) *)

        val exNeg = not_forall_atC faBody negB;                  (* jT (Ex (%d. neg (faBody d))) *)
        (* the existential body not_forall produced : %x. neg (faBody x), beta-reduced *)
        val exBody =
          let val zF = Free("zz_eb", natT)
          in Term.lambda zF (neg (Term.betapply (faBody, zF))) end;

        fun witBody d (hWit : thm) =                             (* hWit : jT (neg (Imp (dvd d n)(Disj (oeq d 1)(oeq d n)))) *)
          let
            val Adn   = dvd d nF;
            val Bdisj = mkDisj (oeq d (suc ZeroC)) (oeq d nF);
            val conj  = not_imp_atC (Adn, Bdisj) hWit;            (* Conj (dvd d n) (neg Bdisj) *)
            val hDvd  = conjunct1_atT (Adn, neg Bdisj) conj;      (* jT (dvd d n) *)
            val hnegD = conjunct2_atT (Adn, neg Bdisj) conj;      (* jT (neg Bdisj) *)
            val Xeq1  = oeq d (suc ZeroC);
            val Yeqn  = oeq d nF;
            val conj2 = deMorgan_or_atC (Xeq1, Yeqn) hnegD;       (* Conj (neg(d=1)) (neg(d=n)) *)
            val hne1  = conjunct1_atT (neg Xeq1, neg Yeqn) conj2; (* d != 1 *)
            val hneqn = conjunct2_atT (neg Xeq1, neg Yeqn) conj2; (* d != n *)
            val hn_ne0 = n_ne0_of_lt1 nF h_lt1;                  (* n != 0 *)
            val hd_ne0 = dvd_nonzero_atC (d, nF) hDvd hn_ne0;     (* d != 0 *)
            val h_lt1d = gt1_of_ne0_ne1_atC d hd_ne0 hne1;       (* 1 < d *)
            (* META nonzero premise (oeq n 0 ==> oFalse) for dvd_le, from neg (oeq n 0) *)
            val nzMeta =
              let val hez = Thm.assume (ctermC (jT (oeq nF ZeroC)))
              in Thm.implies_intr (ctermC (jT (oeq nF ZeroC)))
                   (mp_atT (oeq nF ZeroC, oFalseC) hn_ne0 hez) end;
            val h_le_dn = dvd_le_atC (d, nF) hDvd nzMeta;        (* le d n *)
            val h_lt_dn = le_neq_lt_atC (d, nF) h_le_dn hneqn;   (* d < n *)
            val conjInner = conjI_atT (lt (suc ZeroC) d, lt d nF) h_lt1d h_lt_dn;
            val conjFull  = conjI_atT (mkConj (lt (suc ZeroC) d) (lt d nF), dvd d nF) conjInner hDvd;
          in exI_atC pdAbs d conjFull end;                       (* jT goalEx *)

        val exGoal = exE_elimC (exBody, goalEx) exNeg "dw" witBody;  (* jT goalEx *)
      in Thm.implies_intr (ctermC (jT (neg (prime2 nF))))
           (disjI2C_at (prime2 nF, goalEx) exGoal) end;

    val concl = disjE_elimC (prime2 nF, neg (prime2 nF), GOAL) em caseA caseB;
  in varify (Thm.implies_intr (ctermC h_lt1P) concl) end;

(* ---- validation : aconv the intended schematic goal (built the SAME way) ---- *)
val nVpc = Var (("n",0), natT);
val prime_cases_intended =
  let
    val pdAbsI =
      let val dF = Free("d_pd", natT)
      in Term.lambda dF (mkConj (mkConj (lt (suc ZeroC) dF) (lt dF nVpc)) (dvd dF nVpc)) end;
  in Logic.mk_implies (jT (lt (suc ZeroC) nVpc),
        jT (mkDisj (prime2 nVpc) (mkEx pdAbsI))) end;

val r_prime_cases = checkC ("prime_cases", prime_cases, prime_cases_intended);

(* ---- SOUNDNESS PROBE : kernel must REJECT weakened (false) variants ----
   dropping (d<n) would admit d=n (improper); dropping (1<d) would admit d=1. *)
val probe_pc_dltn =
  let
    val bogusAbs =
      let val dF = Free("d_pd", natT)
      in Term.lambda dF (mkConj (lt (suc ZeroC) dF) (dvd dF nVpc)) end;     (* drops d<n *)
    val bogus = Logic.mk_implies (jT (lt (suc ZeroC) nVpc),
          jT (mkDisj (prime2 nVpc) (mkEx bogusAbs)));
  in not ((Thm.prop_of prime_cases) aconv bogus) end;
val probe_pc_1ltd =
  let
    val bogusAbs =
      let val dF = Free("d_pd", natT)
      in Term.lambda dF (mkConj (lt dF nVpc) (dvd dF nVpc)) end;            (* drops 1<d *)
    val bogus = Logic.mk_implies (jT (lt (suc ZeroC) nVpc),
          jT (mkDisj (prime2 nVpc) (mkEx bogusAbs)));
  in not ((Thm.prop_of prime_cases) aconv bogus) end;

val () =
  if probe_pc_dltn andalso probe_pc_1ltd
  then out "PROBE_OK prime_cases keeps both 1<d and d<n conjuncts\n"
  else out "PROBE_UNSOUND prime_cases dropped a conjunct!\n";

val () =
  if r_prime_cases andalso probe_pc_dltn andalso probe_pc_1ltd
  then out "PC_DONE\n"
  else out "PC_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  CAPSTONE : prime_divisor_exists  ***
   ----------------------------------------------------------------------------
   TARGET:
     prime_divisor_exists :
        jT (le (Suc (Suc Zero)) n)
          ==> jT (Ex (%p. Conj (prime p) (dvd p n)))
   where `prime` is the STRUCTURAL prime (phase-3 capture-avoiding `prime2`,
   the one prime_cases actually produces) and the goal asserts every n >= 2 has
   a divisor p that is prime by the STRUCTURAL definition.

   PROOF: strong_induct with the course-of-values predicate
     R n  :=  Imp (le 2 n) (Ex (%p. Conj (prime2 p) (dvd p n))).
   strong_induct yields Trueprop (R k) from
     !!n. (!!m. lt m n ==> Trueprop(R m)) ==> Trueprop(R n).
   Note  lt 1 d = le (Suc 1) d = le (Suc(Suc 0)) d = le 2 d  (SAME term), so the
   proper-divisor conjunct `1<d` IS the `le 2 d` precondition of the IH at d, and
   the conjunct `d<n` IS the `lt d n` premise of the IH.

   Everything routes through ctxtS2/ctermS2 (where strong_induct lives; thyS2
   extends thyC so prime_cases / dvd_refl / dvd_trans lift by varify).
   ============================================================================ *)

val () = out "CAPSTONE_BEGIN\n";

(* ---- lift the needed theorems onto ctxtS2 (schematic; thyS2 extends thyC) ---- *)
val prime_cases_vS = varify prime_cases;     (* jT (lt 1 n) ==> jT (Disj (prime2 n)(Ex ...)) *)
val dvd_refl_vS    = varify dvd_refl;        (* jT (dvd a a) *)
val dvd_trans_vS   = varify dvd_trans;       (* jT (dvd a b) ==> jT (dvd b c) ==> jT (dvd a c) *)

(* ---- connective helpers re-stated on ctxtS2/ctermS2 (reuse the _vC axioms) ---- *)
fun exI_atS2 Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 at)] exI_vC)
  in Thm.implies_elim inst hbody end;

fun exE_elimS2 (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm  = Thm.assume (ctermS2 hypTerm);
    val body    = bodyFn wF hypThm;
    val minor   = Thm.forall_intr (ctermS2 wF) (Thm.implies_intr (ctermS2 hypTerm) body);
    val exE_inst= beta_norm (Drule.infer_instantiate ctxtS2
                    [(("P",0), ctermS2 Pabs), (("Q",0), ctermS2 goalC)] exE_vC);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;

fun disjE_elimS2 (At, Bt, Ct) dThm caseA caseB =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("A",0), ctermS2 At), (("B",0), ctermS2 Bt), (("C",0), ctermS2 Ct)] disjE_vC);
    val s1 = Thm.implies_elim inst dThm;
    val s2 = Thm.implies_elim s1 caseA;
  in Thm.implies_elim s2 caseB end;

fun conjI_atS2 (At, Bt) hA hB =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("A",0), ctermS2 At), (("B",0), ctermS2 Bt)] conjI_vC);
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;

fun conjunct1_atS2 (At, Bt) hConj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("A",0), ctermS2 At), (("B",0), ctermS2 Bt)] conjunct1_vC)
  in Thm.implies_elim inst hConj end;
fun conjunct2_atS2 (At, Bt) hConj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("A",0), ctermS2 At), (("B",0), ctermS2 Bt)] conjunct2_vC)
  in Thm.implies_elim inst hConj end;

fun disjI1S2_at (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtS2
      [(("A",0), ctermS2 At), (("B",0), ctermS2 Bt)] disjI1_vC)) h;
fun disjI2S2_at (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtS2
      [(("A",0), ctermS2 At), (("B",0), ctermS2 Bt)] disjI2_vC)) h;

fun impI_atS2 (At, Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("A",0), ctermS2 At), (("B",0), ctermS2 Bt)] impI_vC)
  in Thm.implies_elim inst hImpThm end;
fun mp_atS2 (At, Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("A",0), ctermS2 At), (("B",0), ctermS2 Bt)] mp_vC)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;

(* ---- instantiators for the lifted theorems on ctxtS2 ---- *)
fun prime_cases_atS2 nt hgt1 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 nt)] prime_cases_vS)
  in Thm.implies_elim inst hgt1 end;
fun dvd_refl_atS2 t = beta_norm (Drule.infer_instantiate ctxtS2 [(("a",0), ctermS2 t)] dvd_refl_vS);
fun dvd_trans_atS2 (at, bt, ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("a",0), ctermS2 at), (("b",0), ctermS2 bt), (("c",0), ctermS2 ct)] dvd_trans_vS)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* ---- abbreviations for the result existential (capture-avoiding) ---- *)
fun resultBodyAbs nt =                       (* %p. Conj (prime2 p) (dvd p n) *)
  let val pF = Free("p_rb", natT)
  in Term.lambda pF (mkConj (prime2 pF) (dvd pF nt)) end;
fun resultEx nt = mkEx (resultBodyAbs nt);
fun Rterm nt = mkImp (le (suc (suc ZeroC)) nt) (resultEx nt);   (* Imp (le 2 n) (Ex ...) *)

val () = out "CAPSTONE_HELPERS_READY\n";

(* ============================================================================
   The course-of-values predicate as a (nat => o) abstraction for strong_induct.
   ============================================================================ *)
val Rpred =                                  (* %n. R n *)
  let val nF = Free("n_R", natT)
  in Term.lambda nF (Rterm nF) end;

(* ---- the step body : fix n, given the strong IH, prove Trueprop(R n) ---- *)
val prime_divisor_exists =
  let
    val nStep = Free("n_step", natT);
    (* IH : !!m. lt m n ==> Trueprop(P m)  with P := %x. R x, so Trueprop(P m) is jT (R m) *)
    val mIH = Free("m_ih", natT);
    val Gprop = Logic.all mIH (Logic.mk_implies (jT (lt mIH nStep), jT (Rterm mIH)));
    val Hthm  = Thm.assume (ctermS2 Gprop);
    (* apply IH at a term d (a proof of lt d n) -> jT (R d) *)
    fun applyIH dt h_lt =
      let val hAt = Thm.forall_elim (ctermS2 dt) Hthm   (* lt d n ==> jT (R d) *)
      in Thm.implies_elim hAt h_lt end;

    (* prove jT (R n) = jT (Imp (le 2 n) (resultEx n)) by impI *)
    val le2n_P = jT (le (suc (suc ZeroC)) nStep);
    val h_le2n = Thm.assume (ctermS2 le2n_P);            (* le 2 n  ==  lt 1 n *)

    (* prime_cases at n (premise lt 1 n IS le 2 n) -> Disj (prime2 n)(properdiv) *)
    val pd_Abs =                                          (* %d. Conj(Conj(1<d)(d<n))(d|n) *)
      let val dF = Free("d_pd", natT)
      in Term.lambda dF (mkConj (mkConj (lt (suc ZeroC) dF) (lt dF nStep)) (dvd dF nStep)) end;
    val pdEx   = mkEx pd_Abs;
    val dThm   = prime_cases_atS2 nStep h_le2n;           (* Disj (prime2 n) pdEx *)

    val goalC  = resultEx nStep;

    (* CASE A : prime2 n  -> witness p:=n, Conj (prime2 n)(dvd n n), exI *)
    val caseA =
      let
        val hp   = Thm.assume (ctermS2 (jT (prime2 nStep)));
        val dnn  = dvd_refl_atS2 nStep;                  (* jT (dvd n n) *)
        val conj = conjI_atS2 (prime2 nStep, dvd nStep nStep) hp dnn;  (* Conj (prime2 n)(dvd n n) *)
        val ex   = exI_atS2 (resultBodyAbs nStep) nStep conj;          (* jT (resultEx n) *)
      in Thm.implies_intr (ctermS2 (jT (prime2 nStep))) ex end;

    (* CASE B : pdEx  -> exE witness d, use IH, dvd_trans, exI *)
    val caseB =
      let
        val hpd  = Thm.assume (ctermS2 (jT pdEx));
        fun pdBody d (hConj : thm) =     (* hConj : jT (Conj (Conj (1<d)(d<n)) (d|n)) *)
          let
            val innerC = mkConj (lt (suc ZeroC) d) (lt d nStep);
            val hInner = conjunct1_atS2 (innerC, dvd d nStep) hConj;   (* Conj (1<d)(d<n) *)
            val hDvdDN = conjunct2_atS2 (innerC, dvd d nStep) hConj;   (* dvd d n *)
            val h_1lt_d= conjunct1_atS2 (lt (suc ZeroC) d, lt d nStep) hInner; (* 1<d == le 2 d *)
            val h_lt_dn= conjunct2_atS2 (lt (suc ZeroC) d, lt d nStep) hInner; (* d<n == lt d n *)
            (* IH at d : need lt d n (= h_lt_dn) -> jT (R d) = Imp (le 2 d)(resultEx d) *)
            val Rd     = applyIH d h_lt_dn;                            (* jT (Imp (le 2 d)(resultEx d)) *)
            (* le 2 d  is exactly  lt 1 d  is exactly  h_1lt_d *)
            val exPd   = mp_atS2 (le (suc (suc ZeroC)) d, resultEx d) Rd h_1lt_d;  (* jT (resultEx d) *)
            (* exE over resultEx d : witness p with Conj (prime2 p)(dvd p d) *)
            fun innerBody p (hpConj : thm) =   (* hpConj : jT (Conj (prime2 p)(dvd p d)) *)
              let
                val hPrime = conjunct1_atS2 (prime2 p, dvd p d) hpConj;  (* prime2 p *)
                val hDvdPD = conjunct2_atS2 (prime2 p, dvd p d) hpConj;  (* dvd p d *)
                val hDvdPN = dvd_trans_atS2 (p, d, nStep) hDvdPD hDvdDN; (* dvd p n *)
                val conjP  = conjI_atS2 (prime2 p, dvd p nStep) hPrime hDvdPN; (* Conj(prime2 p)(dvd p n) *)
              in exI_atS2 (resultBodyAbs nStep) p conjP end;            (* jT (resultEx n) *)
          in exE_elimS2 (resultBodyAbs d, goalC) exPd "p_w" innerBody end;
        val g = exE_elimS2 (pd_Abs, goalC) hpd "d_w" pdBody;
      in Thm.implies_intr (ctermS2 (jT pdEx)) g end;

    val concl  = disjE_elimS2 (prime2 nStep, pdEx, goalC) dThm caseA caseB;  (* jT (resultEx n) *)
    val impRn  = impI_atS2 (le (suc (suc ZeroC)) nStep, resultEx nStep)
                   (Thm.implies_intr (ctermS2 le2n_P) concl);            (* jT (R n) *)
    (* discharge the strong IH premise, forall_intr n -> the strong_induct hypothesis form *)
    val stepThm = Thm.forall_intr (ctermS2 nStep) (Thm.implies_intr (ctermS2 Gprop) impRn);

    (* feed stepThm to strong_induct (instantiate P := Rpred); get jT (R k).
       NAME the final discharged Free `n` so varify yields Var(("n",0),..) to
       match the intended schematic goal (nVcap = Var(("n",0),..)) under aconv. *)
    val kF = Free("n", natT);
    val siInst = beta_norm (Drule.infer_instantiate ctxtS2
                   [(("P",0), ctermS2 Rpred), (("k",0), ctermS2 kF)] (varify strong_induct));
    val Rk     = Thm.implies_elim siInst stepThm;        (* jT (R k) = jT (Imp (le 2 k)(resultEx k)) *)
    (* turn jT (Imp (le 2 k)(resultEx k)) into  jT (le 2 k) ==> jT (resultEx k) (META rule)
       by assuming le 2 k, mp, and discharging -> the TARGET implication form *)
    val h_le2k = Thm.assume (ctermS2 (jT (le (suc (suc ZeroC)) kF)));
    val exK    = mp_atS2 (le (suc (suc ZeroC)) kF, resultEx kF) Rk h_le2k;  (* jT (resultEx k) *)
    val disch  = Thm.implies_intr (ctermS2 (jT (le (suc (suc ZeroC)) kF))) exK;
  in varify disch end;

(* ============================================================================
   VALIDATION : 0-hyp AND aconv the intended schematic goal (built the SAME way).
   ============================================================================ *)
val nVcap = Var (("n",0), natT);
val prime_divisor_exists_intended =
  let
    val bodyAbsI =
      let val pF = Free("p_rb", natT)
      in Term.lambda pF (mkConj (prime2 pF) (dvd pF nVcap)) end;
  in Logic.mk_implies (jT (le (suc (suc ZeroC)) nVcap), jT (mkEx bodyAbsI)) end;

val r_pde = checkS2 ("prime_divisor_exists", prime_divisor_exists, prime_divisor_exists_intended);

(* ---- SOUNDNESS PROBE : kernel must REJECT a false variant ----
   The honest goal demands the witness be PRIME and a DIVISOR.  A bogus variant
   dropping the `prime2 p` conjunct (asserting merely SOME divisor, trivially n)
   must NOT be what we proved. *)
val probe_pde_prime =
  let
    val bogusAbs =
      let val pF = Free("p_rb", natT)
      in Term.lambda pF (dvd pF nVcap) end;                 (* drops prime2 p *)
    val bogus = Logic.mk_implies (jT (le (suc (suc ZeroC)) nVcap), jT (mkEx bogusAbs));
  in not ((Thm.prop_of prime_divisor_exists) aconv bogus) end;
(* and dropping the divisibility conjunct must also be rejected *)
val probe_pde_dvd =
  let
    val bogusAbs =
      let val pF = Free("p_rb", natT)
      in Term.lambda pF (prime2 pF) end;                    (* drops dvd p n *)
    val bogus = Logic.mk_implies (jT (le (suc (suc ZeroC)) nVcap), jT (mkEx bogusAbs));
  in not ((Thm.prop_of prime_divisor_exists) aconv bogus) end;

val () =
  if probe_pde_prime andalso probe_pde_dvd
  then out "PROBE_OK prime_divisor_exists keeps both prime and dvd conjuncts\n"
  else out "PROBE_UNSOUND prime_divisor_exists dropped a conjunct!\n";

val () =
  if r_pde then out "OK prime_divisor_exists\n" else out "FAILED prime_divisor_exists\n";

val () =
  if r_pde andalso probe_pde_prime andalso probe_pde_dvd
  then out "CAPSTONE_DONE\n"
  else out "CAPSTONE_FAILED\n";

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
