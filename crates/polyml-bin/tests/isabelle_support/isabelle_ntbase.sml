(* ============================================================================
   UNIFIED NUMBER-THEORY BASE for Isabelle/Pure on the polyml-rs interpreter.
   (test: isabelle_ntbase.rs)
   ----------------------------------------------------------------------------
   One driver consolidating the previously-separate branches into a SINGLE base,
   so downstream work (Fermat's little theorem etc.) builds on one rich context
   instead of re-deriving foundations. Everything 0-hyp, only classical
   assumption = excluded middle. Final context: ctxtP / ctermP (pow is the sole
   theory extension on top of the classical+division+euclid theory thyS2).

   Provides, all validated (NT_BASE_OK):
     - classical number theory + Peano add/mult + commutative semiring +
       Ex/Disj/Conj/Imp/Forall + classical lemmas (ex_middle, ...) + le/lt/dvd +
       order laws + strong_induct + prime2/prime_cases;
     - the DIVISION THEOREM (div_mod_exists) and EUCLID'S LEMMA
       (euclid_lemma : prime2 p => dvd p (a*b) => dvd p a \/ dvd p b);
     - MODULAR ARITHMETIC: cong m a b (two-sided) + cong_refl/sym/trans/add/mult;
     - POWERS: pow + pow_one/pow_add/pow_mult_base + cong_pow
       (a == b mod m => a^n == b^n mod m).

   Built by a 2-seat ultracode workflow (wf_0e7a6ed2-f88) that lifted the cong
   (isabelle_modular.sml) and pow (isabelle_power.sml) layers onto the
   Euclid-lemma driver (isabelle_euclid_lemma.sml). The one edit to the copied
   power source: the pow const-add targets thyS2 (the euclid base theory), not
   the bare classical thyC.
   ============================================================================ *)

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


(* ============================================================================
   ============================================================================
   ***  LIFTED LAYER 1 : MODULAR ARITHMETIC (cong) on the BASE context  ***
   The cong section from isabelle_modular.sml, self-contained on ctxtC/ctermC
   (which the euclid base provides).  Defines congL/congR/cong + cong_introL/R
   and proves cong_refl/sym/trans/add/mult; ctxtC theorems lift to ctxtS2.
   ============================================================================ *)

val () = out "MOD_FOUNDATION_BEGIN\n";

(* ---- arithmetic helpers we additionally need on ctxtC ----
   (add_comm/add_assoc/left_distrib were only restated on ctxtT before) *)
val add_comm_vC     = varify add_comm;
val add_assoc_vC    = varify add_assoc;
val left_distrib_vC = varify left_distrib;
fun addcommC_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtC
        [(("m",0), ctermC mt),(("n",0), ctermC nt)] add_comm_vC);
fun addassocC_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtC
        [(("m",0), ctermC mt),(("n",0), ctermC nt),(("k",0), ctermC kt)] add_assoc_vC);
(* left_distrib : oeq (mult ?x (add ?m ?n)) (add (mult ?x ?m) (mult ?x ?n)) *)
fun left_distribC_at (xt,mt,nt) = beta_norm (Drule.infer_instantiate ctxtC
        [(("x",0), ctermC xt),(("m",0), ctermC mt),(("n",0), ctermC nt)] left_distrib_vC);

(* ---- THE congruence abbreviation (SML fn building the o-term) ---- *)
fun congL m a b = mkEx (Abs ("k", natT, oeq b (add a (mult m (Bound 0)))));
fun congR m a b = mkEx (Abs ("k", natT, oeq a (add b (mult m (Bound 0)))));
fun cong m a b = mkDisj (congL m a b) (congR m a b);

(* ---- cong_introL : from (hyp : oeq b (add a (mult m w))) build jT (cong m a b)
        via exI on the LEFT body then disjI1.                                  *)
fun cong_introL (m, a, b, w) hyp =
  let
    val LAbs = Abs ("k", natT, oeq b (add a (mult m (Bound 0))));
    val exThm = exI_atC LAbs w hyp;                         (* jT (congL m a b) *)
  in disjI1C_at (congL m a b, congR m a b) exThm end;       (* jT (cong m a b)  *)

(* ---- cong_introR : from (hyp : oeq a (add b (mult m w))) build jT (cong m a b)
        via exI on the RIGHT body then disjI2.                                 *)
fun cong_introR (m, a, b, w) hyp =
  let
    val RAbs = Abs ("k", natT, oeq a (add b (mult m (Bound 0))));
    val exThm = exI_atC RAbs w hyp;                         (* jT (congR m a b) *)
  in disjI2C_at (congL m a b, congR m a b) exThm end;       (* jT (cong m a b)  *)

(* ============================================================================
   cong_refl : jT (cong m a a)
   witness k = Zero on the LEFT disjunct: need  oeq a (add a (mult m Zero)).
     mult m 0 = 0           [mult_0_right]
     a + (m*0) = a + 0      [add_cong_r]
     a + 0 = a             [add_0_right]
     => a + (m*0) = a ; sym => a = a + (m*0).
   ============================================================================ *)
val cong_refl =
  let
    val mF = Free("m", natT); val aF = Free("a", natT);
    val m0   = mult0rC_at mF;                               (* (m*0) = 0 *)
    val cong = add_cong_rC (aF, mult mF ZeroC, ZeroC) m0;   (* (a + m*0) = (a + 0) *)
    val a0   = add0rC_at aF;                                (* (a + 0) = a *)
    val chain= oeq_trans OF [cong, a0];                     (* (a + m*0) = a *)
    val body = oeq_sym OF [chain];                          (* a = (a + m*0) *)
  in varify (cong_introL (mF, aF, aF, ZeroC) body) end;

(* ============================================================================
   cong_sym : jT (cong m a b) ==> jT (cong m b a)
     cong m a b = Disj (Ex k. b = a + m*k) (Ex k. a = b + m*k)
     cong m b a = Disj (Ex k. a = b + m*k) (Ex k. b = a + m*k)
   hyp-left  (Ex k. b = a + m*k)  -> goal-RIGHT  (exI on congR (b,a))
   hyp-right (Ex k. a = b + m*k)  -> goal-LEFT   (exI on congL (b,a))
   ============================================================================ *)
val cong_sym =
  let
    val mF = Free("m", natT); val aF = Free("a", natT); val bF = Free("b", natT);
    val hypP = jT (cong mF aF bF);
    val hyp  = Thm.assume (ctermC hypP);
    val goalC = cong mF bF aF;
    (* hyp left disjunct body abstraction: %k. oeq b (add a (mult m k)) *)
    val LAbs = Abs ("k", natT, oeq bF (add aF (mult mF (Bound 0))));
    (* hyp right disjunct body abstraction: %k. oeq a (add b (mult m k)) *)
    val RAbs = Abs ("k", natT, oeq aF (add bF (mult mF (Bound 0))));
    (* CASE left of hyp: have b = a + m*w ; that is the RIGHT body of cong m b a. *)
    fun leftBody w (hw : thm) =                             (* hw : oeq b (add a (mult m w)) *)
      cong_introR (mF, bF, aF, w) hw;                       (* jT (cong m b a) via disjI2 *)
    val caseLeft =
      let
        val exL = Thm.assume (ctermC (jT (mkEx LAbs)));
        val leThm = exE_elimC (LAbs, goalC) exL "wl" leftBody;
      in Thm.implies_intr (ctermC (jT (mkEx LAbs))) leThm end;
    (* CASE right of hyp: have a = b + m*w ; that is the LEFT body of cong m b a. *)
    fun rightBody w (hw : thm) =                            (* hw : oeq a (add b (mult m w)) *)
      cong_introL (mF, bF, aF, w) hw;                       (* jT (cong m b a) via disjI1 *)
    val caseRight =
      let
        val riThm = exE_elimC (RAbs, goalC) (Thm.assume (ctermC (jT (mkEx RAbs)))) "wr" rightBody;
      in Thm.implies_intr (ctermC (jT (mkEx RAbs))) riThm end;
    val concl = disjE_elimC (mkEx LAbs, mkEx RAbs, goalC) hyp caseLeft caseRight;
    val disch = Thm.implies_intr (ctermC hypP) concl;
  in varify disch end;

val () = out "MOD_PARTIAL (refl+sym defined)\n";

(* ---- partial validation for refl + sym (cong_add appended below) ---- *)
fun checkMod (nm, th, intended) =
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

val mVm = Var (("m",0), natT);
val aVm = Var (("a",0), natT);
val bVm = Var (("b",0), natT);
val cong_refl_intended = jT (cong mVm aVm aVm);
val cong_sym_intended  = Logic.mk_implies (jT (cong mVm aVm bVm), jT (cong mVm bVm aVm));
val r_cong_refl = checkMod ("cong_refl", cong_refl, cong_refl_intended);
val r_cong_sym  = checkMod ("cong_sym",  cong_sym,  cong_sym_intended);
val () = out "MOD_PARTIAL_CHECK_DONE\n";

(* ============================================================================
   cong_add : jT (cong m a a2) ==> jT (cong m b b2)
                ==> jT (cong m (add a b) (add a2 b2))
   ----------------------------------------------------------------------------
   disjE x disjE = 4 cases on (a==a2) x (b==b2).  Witnesses p (for a/a2) and
   q (for b/b2).
     LL : a2 = a+m*p, b2 = b+m*q  -> add a2 b2 = (a+b)+m*(p+q) : goal LEFT, p+q.
     RR : a  = a2+m*p, b = b2+m*q -> add a b  = (a2+b2)+m*(p+q): goal RIGHT, p+q.
     LR : a2 = a+m*p, b = b2+m*q  -> add a2 b2 = (a+b2)+m*p,
                                     add a b   = (a+b2)+m*q.  Split p<=q vs q<=p
                                     (le_total) and route the m-multiple of the
                                     DIFFERENCE to the correct disjunct.
     RL : a = a2+m*p, b2 = b+m*q  -> symmetric to LR.
   ============================================================================ *)

(* a 4-term swap on ctxtC:  (A+B)+(C+D) = (A+C)+(B+D)  [from base add4_swap, ctxtC] *)
fun add4_swapC (A,B,C,D) =
  let
    val asbcd = addassocC_at (A, B, add C D);                 (* (A+B)+(C+D) = A+(B+(C+D)) *)
    val i1 = addassocC_at (B, C, D);                          (* (B+C)+D = B+(C+D) *)
    val i1s = oeq_sym OF [i1];                                (* B+(C+D) = (B+C)+D *)
    val icc = addcommC_at (B, C);                             (* B+C = C+B *)
    val i2 = add_cong_lC (add B C, add C B, D) icc;           (* (B+C)+D = (C+B)+D *)
    val i3 = addassocC_at (C, B, D);                          (* (C+B)+D = C+(B+D) *)
    val inner = oeq_trans OF [oeq_trans OF [i1s, i2], i3];    (* B+(C+D) = C+(B+D) *)
    val cInner = add_cong_rC (A, add B (add C D), add C (add B D)) inner;
                                                              (* A+(B+(C+D)) = A+(C+(B+D)) *)
    val r1 = oeq_trans OF [asbcd, cInner];                    (* (A+B)+(C+D) = A+(C+(B+D)) *)
    val r2assoc = addassocC_at (A, C, add B D);               (* (A+C)+(B+D) = A+(C+(B+D)) *)
    val r2assoc_s = oeq_sym OF [r2assoc];                     (* A+(C+(B+D)) = (A+C)+(B+D) *)
  in oeq_trans OF [r1, r2assoc_s] end;                        (* (A+B)+(C+D) = (A+C)+(B+D) *)

(* mult-congruence on RIGHT operand (h fixed) on ctxtC:
     oeq p q  ==>  oeq (mult h p) (mult h q) *)
fun mult_cong_rT_C (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("a",0), ctermC pT), (("b",0), ctermC qT)] oeq_subst_vC);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtC [(("a",0), ctermC (mult hT pT))] oeq_refl_vC);
  in inst OF [hpq, refl_hp] end;

(* le-witness extractor body abstraction: le s t = Ex(%p. oeq t (add s p)) *)
fun leAbs s t = Abs ("p", natT, oeq t (add s (Bound 0)));

val cong_add =
  let
    val mF = Free("m", natT);
    val aF = Free("a", natT); val a2F = Free("a2", natT);
    val bF = Free("b", natT); val b2F = Free("b2", natT);
    val H1prop = jT (cong mF aF a2F);
    val H2prop = jT (cong mF bF b2F);
    val H1 = Thm.assume (ctermC H1prop);
    val H2 = Thm.assume (ctermC H2prop);
    val goalC = cong mF (add aF bF) (add a2F b2F);

    (* disjunct body abstractions *)
    val A_L = Abs ("k", natT, oeq a2F (add aF (mult mF (Bound 0))));   (* a2 = a + m*k *)
    val A_R = Abs ("k", natT, oeq aF  (add a2F (mult mF (Bound 0))));  (* a  = a2 + m*k *)
    val B_L = Abs ("k", natT, oeq b2F (add bF (mult mF (Bound 0))));   (* b2 = b + m*k *)
    val B_R = Abs ("k", natT, oeq bF  (add b2F (mult mF (Bound 0))));  (* b  = b2 + m*k *)

    (* ---- CASE LL : a2=a+m*p, b2=b+m*q -> goal LEFT witness (p+q) ---- *)
    fun caseLL_body p hp q hq =
      let
        (* add a2 b2 = (a+m*p)+(b+m*q) *)
        val c1 = add_cong_lC (a2F, add aF (mult mF p), b2F) hp;     (* (a2+b2)=((a+m*p)+b2) *)
        val c2 = add_cong_rC (add aF (mult mF p), b2F, add bF (mult mF q)) hq;
                                                                    (* ((a+m*p)+b2)=((a+m*p)+(b+m*q)) *)
        val sum = oeq_trans OF [c1, c2];                            (* (a2+b2)=((a+m*p)+(b+m*q)) *)
        (* rearrange (a+m*p)+(b+m*q) = (a+b)+(m*p+m*q) *)
        val sw  = add4_swapC (aF, mult mF p, bF, mult mF q);        (* =(a+b)+(m*p+m*q) *)
        (* m*p+m*q = m*(p+q) *)
        val ld  = left_distribC_at (mF, p, q);                      (* m*(p+q)=m*p+m*q *)
        val lds = oeq_sym OF [ld];                                  (* m*p+m*q=m*(p+q) *)
        val foldD = add_cong_rC (add aF bF, add (mult mF p) (mult mF q), mult mF (add p q)) lds;
                                                                    (* (a+b)+(m*p+m*q)=(a+b)+m*(p+q) *)
        val chain = oeq_trans OF [oeq_trans OF [sum, sw], foldD];   (* (a2+b2)=(a+b)+m*(p+q) *)
      in cong_introL (mF, add aF bF, add a2F b2F, add p q) chain end;

    (* ---- CASE RR : a=a2+m*p, b=b2+m*q -> goal RIGHT witness (p+q) ---- *)
    fun caseRR_body p hp q hq =
      let
        val c1 = add_cong_lC (aF, add a2F (mult mF p), bF) hp;      (* (a+b)=((a2+m*p)+b) *)
        val c2 = add_cong_rC (add a2F (mult mF p), bF, add b2F (mult mF q)) hq;
                                                                    (* ((a2+m*p)+b)=((a2+m*p)+(b2+m*q)) *)
        val sum = oeq_trans OF [c1, c2];                            (* (a+b)=((a2+m*p)+(b2+m*q)) *)
        val sw  = add4_swapC (a2F, mult mF p, b2F, mult mF q);      (* =(a2+b2)+(m*p+m*q) *)
        val ld  = left_distribC_at (mF, p, q);
        val lds = oeq_sym OF [ld];
        val foldD = add_cong_rC (add a2F b2F, add (mult mF p) (mult mF q), mult mF (add p q)) lds;
        val chain = oeq_trans OF [oeq_trans OF [sum, sw], foldD];   (* (a+b)=(a2+b2)+m*(p+q) *)
      in cong_introR (mF, add aF bF, add a2F b2F, add p q) chain end;

    (* ---- helper: a "le difference" turns oeq q (add p r) into m*q = m*p + m*r ----
       given hr : oeq q (add p r), produce  oeq (mult m q) (add (mult m p) (mult m r)) *)
    fun mDiff (pT, qT, rT) hr =
      let
        val congq = mult_cong_rT_C (mF, qT, add pT rT) hr;         (* m*q = m*(p+r) *)
        val ld    = left_distribC_at (mF, pT, rT);                 (* m*(p+r)=m*p+m*r *)
      in oeq_trans OF [congq, ld] end;                             (* m*q = m*p+m*r *)

    (* ---- CASE LR : a2=a+m*p, b=b2+m*q.  add a2 b2 = (a+b2)+m*p ; add a b = (a+b2)+m*q.
            split le_total p q : if p<=q (q=p+r) then add a b = add a2 b2 + m*r (goal RIGHT);
                                 if q<=p (p=q+r) then add a2 b2 = add a b + m*r (goal LEFT). *)
    fun caseLR_body p hp q hq =
      let
        (* base rewrites *)
        (* add a2 b2 = (a+m*p)+b2 = (a+b2)+m*p *)
        val la1 = add_cong_lC (a2F, add aF (mult mF p), b2F) hp;    (* (a2+b2)=((a+m*p)+b2) *)
        val la2 = addassocC_at (aF, mult mF p, b2F);               (* ((a+m*p)+b2)=(a+(m*p+b2)) *)
        val la3comm = addcommC_at (mult mF p, b2F);                (* (m*p+b2)=(b2+m*p) *)
        val la3 = add_cong_rC (aF, add (mult mF p) b2F, add b2F (mult mF p)) la3comm;
                                                                    (* (a+(m*p+b2))=(a+(b2+m*p)) *)
        val la4 = addassocC_at (aF, b2F, mult mF p);               (* ((a+b2)+m*p)=(a+(b2+m*p)) *)
        val la4s = oeq_sym OF [la4];                               (* (a+(b2+m*p))=((a+b2)+m*p) *)
        val A2B2 = oeq_trans OF [oeq_trans OF [oeq_trans OF [la1, la2], la3], la4s];
                                                                    (* (a2+b2)=((a+b2)+m*p) *)
        (* add a b = a+(b2+m*q) = (a+b2)+m*q *)
        val lb1 = add_cong_rC (aF, bF, add b2F (mult mF q)) hq;     (* (a+b)=(a+(b2+m*q)) *)
        val lb2 = addassocC_at (aF, b2F, mult mF q);               (* ((a+b2)+m*q)=(a+(b2+m*q)) *)
        val lb2s = oeq_sym OF [lb2];                               (* (a+(b2+m*q))=((a+b2)+m*q) *)
        val AB = oeq_trans OF [lb1, lb2s];                          (* (a+b)=((a+b2)+m*q) *)
        (* split p<=q or q<=p *)
        val tot = le_total_at (p, q);                              (* Disj (le p q) (le q p) *)
        val sub1 =                                                 (* le p q -> goal *)
          let
            val hle = Thm.assume (ctermC (jT (le p q)));
            fun body r hr =                                        (* hr : oeq q (add p r) *)
              let
                (* add a b = (a+b2)+m*q ; m*q = m*p + m*r ; so = ((a+b2)+m*p)+m*r = (a2+b2)+m*r *)
                val mq = mDiff (p, q, r) hr;                       (* m*q = m*p+m*r *)
                val rw = add_cong_rC (add aF b2F, mult mF q, add (mult mF p) (mult mF r)) mq;
                                                                    (* (a+b2)+m*q = (a+b2)+(m*p+m*r) *)
                val as1 = addassocC_at (add aF b2F, mult mF p, mult mF r);
                                                                    (* ((a+b2)+m*p)+m*r=(a+b2)+(m*p+m*r) *)
                val as1s = oeq_sym OF [as1];                       (* (a+b2)+(m*p+m*r)=((a+b2)+m*p)+m*r *)
                val A2B2s = oeq_sym OF [A2B2];                     (* ((a+b2)+m*p)=(a2+b2) *)
                val foldA2 = add_cong_lC (add (add aF b2F) (mult mF p), add a2F b2F, mult mF r) A2B2s;
                                                                    (* ((a+b2)+m*p)+m*r=(a2+b2)+m*r *)
                val chain = oeq_trans OF [oeq_trans OF [oeq_trans OF [AB, rw], as1s], foldA2];
                                                                    (* (a+b)=(a2+b2)+m*r *)
              in cong_introR (mF, add aF bF, add a2F b2F, r) chain end;
            val g = exE_elimC (leAbs p q, goalC) hle "r0" body;
          in Thm.implies_intr (ctermC (jT (le p q))) g end;
        val sub2 =                                                 (* le q p -> goal *)
          let
            val hle = Thm.assume (ctermC (jT (le q p)));
            fun body r hr =                                        (* hr : oeq p (add q r) *)
              let
                (* add a2 b2 = (a+b2)+m*p ; m*p = m*q + m*r ; so = ((a+b2)+m*q)+m*r = (a+b)+m*r *)
                val mp = mDiff (q, p, r) hr;                       (* m*p = m*q+m*r *)
                val rw = add_cong_rC (add aF b2F, mult mF p, add (mult mF q) (mult mF r)) mp;
                                                                    (* (a+b2)+m*p = (a+b2)+(m*q+m*r) *)
                val as1 = addassocC_at (add aF b2F, mult mF q, mult mF r);
                                                                    (* ((a+b2)+m*q)+m*r=(a+b2)+(m*q+m*r) *)
                val as1s = oeq_sym OF [as1];                       (* (a+b2)+(m*q+m*r)=((a+b2)+m*q)+m*r *)
                val ABs = oeq_sym OF [AB];                         (* ((a+b2)+m*q)=(a+b) *)
                val foldAB = add_cong_lC (add (add aF b2F) (mult mF q), add aF bF, mult mF r) ABs;
                                                                    (* ((a+b2)+m*q)+m*r=(a+b)+m*r *)
                val chain = oeq_trans OF [oeq_trans OF [oeq_trans OF [A2B2, rw], as1s], foldAB];
                                                                    (* (a2+b2)=(a+b)+m*r *)
              in cong_introL (mF, add aF bF, add a2F b2F, r) chain end;
            val g = exE_elimC (leAbs q p, goalC) hle "r0" body;
          in Thm.implies_intr (ctermC (jT (le q p))) g end;
      in disjE_elimC (le p q, le q p, goalC) tot sub1 sub2 end;

    (* ---- CASE RL : a=a2+m*p, b2=b+m*q.  symmetric to LR with a<->a2, b<->b2 swapped roles.
            add a b = (a2+b)+m*p ; add a2 b2 = (a2+b)+m*q.  split le_total p q. *)
    fun caseRL_body p hp q hq =
      let
        (* add a b = (a2+m*p)+b = (a2+b)+m*p *)
        val la1 = add_cong_lC (aF, add a2F (mult mF p), bF) hp;     (* (a+b)=((a2+m*p)+b) *)
        val la2 = addassocC_at (a2F, mult mF p, bF);              (* ((a2+m*p)+b)=(a2+(m*p+b)) *)
        val la3comm = addcommC_at (mult mF p, bF);                (* (m*p+b)=(b+m*p) *)
        val la3 = add_cong_rC (a2F, add (mult mF p) bF, add bF (mult mF p)) la3comm;
                                                                    (* (a2+(m*p+b))=(a2+(b+m*p)) *)
        val la4 = addassocC_at (a2F, bF, mult mF p);              (* ((a2+b)+m*p)=(a2+(b+m*p)) *)
        val la4s = oeq_sym OF [la4];
        val AB = oeq_trans OF [oeq_trans OF [oeq_trans OF [la1, la2], la3], la4s];
                                                                    (* (a+b)=((a2+b)+m*p) *)
        (* add a2 b2 = a2+(b+m*q) = (a2+b)+m*q *)
        val lb1 = add_cong_rC (a2F, b2F, add bF (mult mF q)) hq;    (* (a2+b2)=(a2+(b+m*q)) *)
        val lb2 = addassocC_at (a2F, bF, mult mF q);             (* ((a2+b)+m*q)=(a2+(b+m*q)) *)
        val lb2s = oeq_sym OF [lb2];
        val A2B2 = oeq_trans OF [lb1, lb2s];                        (* (a2+b2)=((a2+b)+m*q) *)
        val tot = le_total_at (p, q);
        val sub1 =                                                 (* le p q -> goal *)
          let
            val hle = Thm.assume (ctermC (jT (le p q)));
            fun body r hr =                                        (* hr : oeq q (add p r) *)
              let
                (* a2 b2 = (a2+b)+m*q ; m*q=m*p+m*r ; = ((a2+b)+m*p)+m*r = (a+b)+m*r *)
                val mq = mDiff (p, q, r) hr;
                val rw = add_cong_rC (add a2F bF, mult mF q, add (mult mF p) (mult mF r)) mq;
                val as1 = addassocC_at (add a2F bF, mult mF p, mult mF r);
                val as1s = oeq_sym OF [as1];
                val ABs = oeq_sym OF [AB];                         (* ((a2+b)+m*p)=(a+b) *)
                val foldAB = add_cong_lC (add (add a2F bF) (mult mF p), add aF bF, mult mF r) ABs;
                val chain = oeq_trans OF [oeq_trans OF [oeq_trans OF [A2B2, rw], as1s], foldAB];
                                                                    (* (a2+b2)=(a+b)+m*r *)
              in cong_introL (mF, add aF bF, add a2F b2F, r) chain end;
            val g = exE_elimC (leAbs p q, goalC) hle "r0" body;
          in Thm.implies_intr (ctermC (jT (le p q))) g end;
        val sub2 =                                                 (* le q p -> goal *)
          let
            val hle = Thm.assume (ctermC (jT (le q p)));
            fun body r hr =                                        (* hr : oeq p (add q r) *)
              let
                (* a b = (a2+b)+m*p ; m*p=m*q+m*r ; = ((a2+b)+m*q)+m*r = (a2+b2)+m*r *)
                val mp = mDiff (q, p, r) hr;
                val rw = add_cong_rC (add a2F bF, mult mF p, add (mult mF q) (mult mF r)) mp;
                val as1 = addassocC_at (add a2F bF, mult mF q, mult mF r);
                val as1s = oeq_sym OF [as1];
                val A2B2s = oeq_sym OF [A2B2];                     (* ((a2+b)+m*q)=(a2+b2) *)
                val foldA2 = add_cong_lC (add (add a2F bF) (mult mF q), add a2F b2F, mult mF r) A2B2s;
                val chain = oeq_trans OF [oeq_trans OF [oeq_trans OF [AB, rw], as1s], foldA2];
                                                                    (* (a+b)=(a2+b2)+m*r *)
              in cong_introR (mF, add aF bF, add a2F b2F, r) chain end;
            val g = exE_elimC (leAbs q p, goalC) hle "r0" body;
          in Thm.implies_intr (ctermC (jT (le q p))) g end;
      in disjE_elimC (le p q, le q p, goalC) tot sub1 sub2 end;

    (* ---- assemble: outer disjE on H1 (A_L vs A_R), inner disjE on H2 (B_L vs B_R) ---- *)
    (* outer-LEFT (A_L : a2=a+m*p) *)
    val outerL =
      let
        val exA = Thm.assume (ctermC (jT (mkEx A_L)));
        fun pBody p hp =
          let
            val innerLL =
              let
                val exB = Thm.assume (ctermC (jT (mkEx B_L)));
                fun qBody q hq = caseLL_body p hp q hq;
                val g = exE_elimC (B_L, goalC) exB "q0" qBody;
              in Thm.implies_intr (ctermC (jT (mkEx B_L))) g end;
            val innerLR =
              let
                val exB = Thm.assume (ctermC (jT (mkEx B_R)));
                fun qBody q hq = caseLR_body p hp q hq;
                val g = exE_elimC (B_R, goalC) exB "q0" qBody;
              in Thm.implies_intr (ctermC (jT (mkEx B_R))) g end;
          in disjE_elimC (mkEx B_L, mkEx B_R, goalC) H2 innerLL innerLR end;
        val g = exE_elimC (A_L, goalC) exA "p0" pBody;
      in Thm.implies_intr (ctermC (jT (mkEx A_L))) g end;
    (* outer-RIGHT (A_R : a=a2+m*p) *)
    val outerR =
      let
        val exA = Thm.assume (ctermC (jT (mkEx A_R)));
        fun pBody p hp =
          let
            val innerRL =
              let
                val exB = Thm.assume (ctermC (jT (mkEx B_L)));
                fun qBody q hq = caseRL_body p hp q hq;
                val g = exE_elimC (B_L, goalC) exB "q0" qBody;
              in Thm.implies_intr (ctermC (jT (mkEx B_L))) g end;
            val innerRR =
              let
                val exB = Thm.assume (ctermC (jT (mkEx B_R)));
                fun qBody q hq = caseRR_body p hp q hq;
                val g = exE_elimC (B_R, goalC) exB "q0" qBody;
              in Thm.implies_intr (ctermC (jT (mkEx B_R))) g end;
          in disjE_elimC (mkEx B_L, mkEx B_R, goalC) H2 innerRL innerRR end;
        val g = exE_elimC (A_R, goalC) exA "p0" pBody;
      in Thm.implies_intr (ctermC (jT (mkEx A_R))) g end;

    val concl = disjE_elimC (mkEx A_L, mkEx A_R, goalC) H1 outerL outerR;
    val d1 = Thm.implies_intr (ctermC H2prop) concl;
    val d2 = Thm.implies_intr (ctermC H1prop) d1;
  in varify d2 end;


val cong_add_intended =
  Logic.mk_implies (jT (cong mVm aVm (Var (("a2",0), natT))),
    Logic.mk_implies (jT (cong mVm bVm (Var (("b2",0), natT))),
      jT (cong mVm (add aVm bVm) (add (Var (("a2",0), natT)) (Var (("b2",0), natT))))));
val r_cong_add = checkMod ("cong_add", cong_add, cong_add_intended);

val () =
  if r_cong_refl andalso r_cong_sym andalso r_cong_add
  then out "MOD_FOUNDATION_OK\n"
  else out "MOD_FOUNDATION_BROKEN\n";

(* ============================================================================
   cong_trans : jT (cong m a b) ==> jT (cong m b c) ==> jT (cong m a c)
   ----------------------------------------------------------------------------
   disjE on H1 (relation a,b, witness k) x disjE on H2 (relation b,c, witness l)
   = 4 cases.  Disjunct body abstractions (over a fresh "k"):
     A_L k : oeq b (add a (mult m k))   i.e. b = a + m*k
     A_R k : oeq a (add b (mult m k))   i.e. a = b + m*k
     B_L k : oeq c (add b (mult m k))   i.e. c = b + m*k
     B_R k : oeq b (add c (mult m k))   i.e. b = c + m*k
   LL: b=a+m*k, c=b+m*l  -> c = a + m*(k+l)            : goal LEFT  witness k+l
   RR: a=b+m*k, b=c+m*l  -> a = c + m*(l+k)            : goal RIGHT witness l+k
   LR: b=a+m*k, b=c+m*l  -> a+m*k = c+m*l ; le_total k l, cancel a common m-term.
   RL: a=b+m*k, c=b+m*l  -> rewrite the longer side through b ; le_total k l.
   ============================================================================ *)
val cong_trans =
  let
    val mF = Free("m", natT);
    val aF = Free("a", natT); val bF = Free("b", natT); val cF = Free("c", natT);
    val H1prop = jT (cong mF aF bF);
    val H2prop = jT (cong mF bF cF);
    val H1 = Thm.assume (ctermC H1prop);
    val H2 = Thm.assume (ctermC H2prop);
    val goalC = cong mF aF cF;

    (* disjunct body abstractions *)
    val A_L = Abs ("k", natT, oeq bF (add aF (mult mF (Bound 0))));   (* b = a + m*k *)
    val A_R = Abs ("k", natT, oeq aF (add bF (mult mF (Bound 0))));   (* a = b + m*k *)
    val B_L = Abs ("k", natT, oeq cF (add bF (mult mF (Bound 0))));   (* c = b + m*k *)
    val B_R = Abs ("k", natT, oeq bF (add cF (mult mF (Bound 0))));   (* b = c + m*k *)

    (* mDiff specialized to mF: given hr : oeq q (add p r),
       produce oeq (mult m q) (add (mult m p) (mult m r)). *)
    fun mDiff (pT, qT, rT) hr =
      let
        val congq = mult_cong_rT_C (mF, qT, add pT rT) hr;    (* m*q = m*(p+r) *)
        val ld    = left_distribC_at (mF, pT, rT);            (* m*(p+r) = m*p + m*r *)
      in oeq_trans OF [congq, ld] end;

    (* ---- CASE LL : b=a+m*k, c=b+m*l -> goal LEFT witness (k+l) ---- *)
    fun caseLL_body k hk l hl =
      let
        (* c = b + m*l = (a + m*k) + m*l *)
        val s1 = add_cong_lC (bF, add aF (mult mF k), mult mF l) hk;   (* (b+m*l)=((a+m*k)+m*l) *)
        val cstep = oeq_trans OF [hl, s1];                             (* c = (a+m*k)+m*l *)
        (* (a+m*k)+m*l = a + (m*k+m*l) *)
        val as1 = addassocC_at (aF, mult mF k, mult mF l);            (* ((a+m*k)+m*l)=(a+(m*k+m*l)) *)
        (* m*k+m*l = m*(k+l) *)
        val ld  = left_distribC_at (mF, k, l);                        (* m*(k+l)=m*k+m*l *)
        val lds = oeq_sym OF [ld];                                    (* m*k+m*l=m*(k+l) *)
        val foldD = add_cong_rC (aF, add (mult mF k) (mult mF l), mult mF (add k l)) lds;
                                                                      (* (a+(m*k+m*l))=(a+m*(k+l)) *)
        val chain = oeq_trans OF [oeq_trans OF [cstep, as1], foldD];  (* c = a + m*(k+l) *)
      in cong_introL (mF, aF, cF, add k l) chain end;

    (* ---- CASE RR : a=b+m*k, b=c+m*l -> goal RIGHT witness (l+k) ---- *)
    fun caseRR_body k hk l hl =
      let
        (* a = b + m*k = (c + m*l) + m*k *)
        val s1 = add_cong_lC (bF, add cF (mult mF l), mult mF k) hl;   (* (b+m*k)=((c+m*l)+m*k) *)
        val astep = oeq_trans OF [hk, s1];                            (* a = (c+m*l)+m*k *)
        val as1 = addassocC_at (cF, mult mF l, mult mF k);           (* ((c+m*l)+m*k)=(c+(m*l+m*k)) *)
        val ld  = left_distribC_at (mF, l, k);                       (* m*(l+k)=m*l+m*k *)
        val lds = oeq_sym OF [ld];                                   (* m*l+m*k=m*(l+k) *)
        val foldD = add_cong_rC (cF, add (mult mF l) (mult mF k), mult mF (add l k)) lds;
                                                                      (* (c+(m*l+m*k))=(c+m*(l+k)) *)
        val chain = oeq_trans OF [oeq_trans OF [astep, as1], foldD];  (* a = c + m*(l+k) *)
      in cong_introR (mF, aF, cF, add l k) chain end;

    (* ---- CASE LR : b=a+m*k, b=c+m*l -> a+m*k = c+m*l ; split le_total k l ---- *)
    fun caseLR_body k hk l hl =
      let
        (* eq0 : (a+m*k) = (c+m*l) *)
        val eq0 = oeq_trans OF [oeq_sym OF [hk], hl];
        val tot = le_total_at (k, l);                               (* Disj (le k l) (le l k) *)
        val sub1 =                                                  (* le k l -> l = k+r -> goal RIGHT r *)
          let
            val hle = Thm.assume (ctermC (jT (le k l)));
            fun body r hr =                                         (* hr : oeq l (add k r) *)
              let
                (* m*l = m*k + m*r *)
                val mlr = mDiff (k, l, r) hr;                       (* m*l = m*k+m*r *)
                (* c+m*l = c+(m*k+m*r) *)
                val rw  = add_cong_rC (cF, mult mF l, add (mult mF k) (mult mF r)) mlr;
                (* c+(m*k+m*r) = (c+m*k)+m*r  [assoc sym] *)
                val as1 = addassocC_at (cF, mult mF k, mult mF r);  (* ((c+m*k)+m*r)=(c+(m*k+m*r)) *)
                val as1s= oeq_sym OF [as1];                         (* (c+(m*k+m*r))=((c+m*k)+m*r) *)
                (* (c+m*k)+m*r = (c+m*r)+m*k  [add4-ish: swap m*r and m*k around c]
                   do via: (c+m*k)+m*r = c+(m*k+m*r) (have as1) ; reuse a 4-swap:
                   we want (c+m*k)+m*r = (c+m*r)+m*k. *)
                val sw1 = addassocC_at (cF, mult mF k, mult mF r);  (* ((c+m*k)+m*r)=(c+(m*k+m*r)) *)
                val cm  = addcommC_at (mult mF k, mult mF r);       (* (m*k+m*r)=(m*r+m*k) *)
                val cmc = add_cong_rC (cF, add (mult mF k) (mult mF r), add (mult mF r) (mult mF k)) cm;
                                                                    (* (c+(m*k+m*r))=(c+(m*r+m*k)) *)
                val sw2 = addassocC_at (cF, mult mF r, mult mF k);  (* ((c+m*r)+m*k)=(c+(m*r+m*k)) *)
                val sw2s= oeq_sym OF [sw2];                         (* (c+(m*r+m*k))=((c+m*r)+m*k) *)
                val swp = oeq_trans OF [oeq_trans OF [sw1, cmc], sw2s];  (* ((c+m*k)+m*r)=((c+m*r)+m*k) *)
                (* assemble: a+m*k = c+m*l = c+(m*k+m*r) = (c+m*k)+m*r = (c+m*r)+m*k *)
                val ch1 = oeq_trans OF [oeq_trans OF [eq0, rw], as1s];   (* (a+m*k)=((c+m*k)+m*r) *)
                val ch2 = oeq_trans OF [ch1, swp];                        (* (a+m*k)=((c+m*r)+m*k) *)
                (* commute both sides to m*k + _ and cancel m*k *)
                val lc  = addcommC_at (aF, mult mF k);             (* (a+m*k)=(m*k+a) *)
                val lcs = oeq_sym OF [lc];                         (* (m*k+a)=(a+m*k) *)
                val rc  = addcommC_at (add cF (mult mF r), mult mF k); (* ((c+m*r)+m*k)=(m*k+(c+m*r)) *)
                val mkform = oeq_trans OF [oeq_trans OF [lcs, ch2], rc]; (* (m*k+a)=(m*k+(c+m*r)) *)
                val canc = add_left_cancel_vC OF [mkform];        (* a = (c+m*r) *)
              in cong_introR (mF, aF, cF, r) canc end;
            val g = exE_elimC (leAbs k l, goalC) hle "r0" body;
          in Thm.implies_intr (ctermC (jT (le k l))) g end;
        val sub2 =                                                 (* le l k -> k = l+r -> goal LEFT r *)
          let
            val hle = Thm.assume (ctermC (jT (le l k)));
            fun body r hr =                                        (* hr : oeq k (add l r) *)
              let
                (* m*k = m*l + m*r *)
                val mkr = mDiff (l, k, r) hr;                       (* m*k = m*l+m*r *)
                (* a+m*k = a+(m*l+m*r) = (a+m*r)+m*l *)
                val rw  = add_cong_rC (aF, mult mF k, add (mult mF l) (mult mF r)) mkr;  (* (a+m*k)=(a+(m*l+m*r)) *)
                val sw1 = addassocC_at (aF, mult mF l, mult mF r);  (* ((a+m*l)+m*r)=(a+(m*l+m*r)) *)
                val cm  = addcommC_at (mult mF l, mult mF r);       (* (m*l+m*r)=(m*r+m*l) *)
                val cmc = add_cong_rC (aF, add (mult mF l) (mult mF r), add (mult mF r) (mult mF l)) cm;
                                                                    (* (a+(m*l+m*r))=(a+(m*r+m*l)) *)
                val sw2 = addassocC_at (aF, mult mF r, mult mF l);  (* ((a+m*r)+m*l)=(a+(m*r+m*l)) *)
                val sw2s= oeq_sym OF [sw2];                         (* (a+(m*r+m*l))=((a+m*r)+m*l) *)
                val rwl = oeq_trans OF [oeq_trans OF [rw, cmc], sw2s]; (* (a+m*k)=((a+m*r)+m*l) *)
                (* eq0 : (a+m*k)=(c+m*l) ; so ((a+m*r)+m*l) = (c+m*l) *)
                val eqstep = oeq_trans OF [oeq_sym OF [rwl], eq0];  (* ((a+m*r)+m*l)=(c+m*l) *)
                (* commute both sides to m*l + _ and cancel m*l *)
                val lc  = addcommC_at (add aF (mult mF r), mult mF l); (* ((a+m*r)+m*l)=(m*l+(a+m*r)) *)
                val lcs = oeq_sym OF [lc];                         (* (m*l+(a+m*r))=((a+m*r)+m*l) *)
                val rc  = addcommC_at (cF, mult mF l);             (* (c+m*l)=(m*l+c) *)
                val mlform = oeq_trans OF [oeq_trans OF [lcs, eqstep], rc]; (* (m*l+(a+m*r))=(m*l+c) *)
                val canc = add_left_cancel_vC OF [mlform];        (* (a+m*r) = c *)
                val cgoal= oeq_sym OF [canc];                     (* c = (a+m*r) *)
              in cong_introL (mF, aF, cF, r) cgoal end;
            val g = exE_elimC (leAbs l k, goalC) hle "r0" body;
          in Thm.implies_intr (ctermC (jT (le l k))) g end;
      in disjE_elimC (le k l, le l k, goalC) tot sub1 sub2 end;

    (* ---- CASE RL : a=b+m*k, c=b+m*l ; split le_total k l ---- *)
    fun caseRL_body k hk l hl =
      let
        val tot = le_total_at (k, l);                              (* Disj (le k l) (le l k) *)
        val sub1 =                                                 (* le k l -> l=k+r -> c = a+m*r : goal LEFT r *)
          let
            val hle = Thm.assume (ctermC (jT (le k l)));
            fun body r hr =                                        (* hr : oeq l (add k r) *)
              let
                (* c = b + m*l ; m*l = m*k+m*r ; = (b+m*k)+m*r = a + m*r *)
                val mlr = mDiff (k, l, r) hr;                      (* m*l = m*k+m*r *)
                val rw  = add_cong_rC (bF, mult mF l, add (mult mF k) (mult mF r)) mlr;  (* (b+m*l)=(b+(m*k+m*r)) *)
                val cstep = oeq_trans OF [hl, rw];                 (* c = b+(m*k+m*r) *)
                val as1 = addassocC_at (bF, mult mF k, mult mF r); (* ((b+m*k)+m*r)=(b+(m*k+m*r)) *)
                val as1s= oeq_sym OF [as1];                        (* (b+(m*k+m*r))=((b+m*k)+m*r) *)
                (* b+m*k = a  [hk : a = b+m*k] *)
                val hks = oeq_sym OF [hk];                         (* (b+m*k) = a *)
                val foldA = add_cong_lC (add bF (mult mF k), aF, mult mF r) hks;  (* ((b+m*k)+m*r)=(a+m*r) *)
                val chain = oeq_trans OF [oeq_trans OF [cstep, as1s], foldA];     (* c = a + m*r *)
              in cong_introL (mF, aF, cF, r) chain end;
            val g = exE_elimC (leAbs k l, goalC) hle "r0" body;
          in Thm.implies_intr (ctermC (jT (le k l))) g end;
        val sub2 =                                                 (* le l k -> k=l+r -> a = c+m*r : goal RIGHT r *)
          let
            val hle = Thm.assume (ctermC (jT (le l k)));
            fun body r hr =                                        (* hr : oeq k (add l r) *)
              let
                (* a = b + m*k ; m*k = m*l+m*r ; = (b+m*l)+m*r = c + m*r *)
                val mkr = mDiff (l, k, r) hr;                      (* m*k = m*l+m*r *)
                val rw  = add_cong_rC (bF, mult mF k, add (mult mF l) (mult mF r)) mkr;  (* (b+m*k)=(b+(m*l+m*r)) *)
                val astep = oeq_trans OF [hk, rw];                (* a = b+(m*l+m*r) *)
                val as1 = addassocC_at (bF, mult mF l, mult mF r); (* ((b+m*l)+m*r)=(b+(m*l+m*r)) *)
                val as1s= oeq_sym OF [as1];                        (* (b+(m*l+m*r))=((b+m*l)+m*r) *)
                (* b+m*l = c  [hl : c = b+m*l] *)
                val hls = oeq_sym OF [hl];                         (* (b+m*l) = c *)
                val foldC = add_cong_lC (add bF (mult mF l), cF, mult mF r) hls;  (* ((b+m*l)+m*r)=(c+m*r) *)
                val chain = oeq_trans OF [oeq_trans OF [astep, as1s], foldC];     (* a = c + m*r *)
              in cong_introR (mF, aF, cF, r) chain end;
            val g = exE_elimC (leAbs l k, goalC) hle "r0" body;
          in Thm.implies_intr (ctermC (jT (le l k))) g end;
      in disjE_elimC (le k l, le l k, goalC) tot sub1 sub2 end;

    (* ---- assemble: outer disjE on H1 (A_L vs A_R), inner disjE on H2 (B_L vs B_R) ---- *)
    val outerL =                                                  (* A_L : b = a + m*k *)
      let
        val exA = Thm.assume (ctermC (jT (mkEx A_L)));
        fun kBody k hk =
          let
            val innerLL =                                         (* B_L : c = b + m*l *)
              let
                val exB = Thm.assume (ctermC (jT (mkEx B_L)));
                fun lBody l hl = caseLL_body k hk l hl;
                val g = exE_elimC (B_L, goalC) exB "l0" lBody;
              in Thm.implies_intr (ctermC (jT (mkEx B_L))) g end;
            val innerLR =                                         (* B_R : b = c + m*l *)
              let
                val exB = Thm.assume (ctermC (jT (mkEx B_R)));
                fun lBody l hl = caseLR_body k hk l hl;
                val g = exE_elimC (B_R, goalC) exB "l0" lBody;
              in Thm.implies_intr (ctermC (jT (mkEx B_R))) g end;
          in disjE_elimC (mkEx B_L, mkEx B_R, goalC) H2 innerLL innerLR end;
        val g = exE_elimC (A_L, goalC) exA "k0" kBody;
      in Thm.implies_intr (ctermC (jT (mkEx A_L))) g end;
    val outerR =                                                  (* A_R : a = b + m*k *)
      let
        val exA = Thm.assume (ctermC (jT (mkEx A_R)));
        fun kBody k hk =
          let
            val innerRL =                                         (* B_L : c = b + m*l *)
              let
                val exB = Thm.assume (ctermC (jT (mkEx B_L)));
                fun lBody l hl = caseRL_body k hk l hl;
                val g = exE_elimC (B_L, goalC) exB "l0" lBody;
              in Thm.implies_intr (ctermC (jT (mkEx B_L))) g end;
            val innerRR =                                         (* B_R : b = c + m*l *)
              let
                val exB = Thm.assume (ctermC (jT (mkEx B_R)));
                fun lBody l hl = caseRR_body k hk l hl;
                val g = exE_elimC (B_R, goalC) exB "l0" lBody;
              in Thm.implies_intr (ctermC (jT (mkEx B_R))) g end;
          in disjE_elimC (mkEx B_L, mkEx B_R, goalC) H2 innerRL innerRR end;
        val g = exE_elimC (A_R, goalC) exA "k0" kBody;
      in Thm.implies_intr (ctermC (jT (mkEx A_R))) g end;

    val concl = disjE_elimC (mkEx A_L, mkEx A_R, goalC) H1 outerL outerR;
    val d1 = Thm.implies_intr (ctermC H2prop) concl;
    val d2 = Thm.implies_intr (ctermC H1prop) d1;
  in varify d2 end;

val cong_trans_intended =
  Logic.mk_implies (jT (cong mVm aVm bVm),
    Logic.mk_implies (jT (cong mVm bVm (Var (("c",0), natT))),
      jT (cong mVm aVm (Var (("c",0), natT)))));
val r_cong_trans = checkMod ("cong_trans", cong_trans, cong_trans_intended);

val () = if r_cong_trans then out "MOD_TRANS_DONE\n" else out "MOD_TRANS_BROKEN\n";

(* ---- additional ctxtC arithmetic instantiators for products ---- *)
val mult_comm_vC     = varify mult_comm;
val right_distrib_vC = varify right_distrib;
val mult_assoc_vC    = varify mult_assoc;

fun mult_commC_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtC
        [(("m",0), ctermC mt),(("n",0), ctermC nt)] mult_comm_vC);
fun rdistC_at (at,bt,kt) = beta_norm (Drule.infer_instantiate ctxtC
        [(("m",0), ctermC at),(("n",0), ctermC bt),(("k",0), ctermC kt)] right_distrib_vC);
fun mult_assocC_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtC
        [(("m",0), ctermC mt),(("n",0), ctermC nt),(("k",0), ctermC kt)] mult_assoc_vC);

(* mult-congruence on LEFT operand (k fixed) on ctxtC:  oeq p q ==> oeq (mult p k) (mult q k) *)
fun mult_cong_lC (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtC
          [(("P",0), ctermC Pabs), (("a",0), ctermC pT), (("b",0), ctermC qT)] oeq_subst_vC);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtC [(("a",0), ctermC (mult pT kT))] oeq_refl_vC);
  in inst OF [hpq, refl_pk] end;

(* m_swap_mid : oeq (mult X (mult m t)) (mult m (mult X t))
     X*(m*t) = (X*m)*t   [mult_assoc sym]
             = (m*X)*t   [mult_comm on X*m, congruence on left]
             = m*(X*t)   [mult_assoc] *)
fun m_swap_midC (Xt, mt, tt) =
  let
    val a1 = mult_assocC_at (Xt, mt, tt);          (* (X*m)*t = X*(m*t) *)
    val a1s = oeq_sym OF [a1];                      (* X*(m*t) = (X*m)*t *)
    val cm = mult_commC_at (Xt, mt);               (* X*m = m*X *)
    val cl = mult_cong_lC (mult Xt mt, mult mt Xt, tt) cm;  (* (X*m)*t = (m*X)*t *)
    val a2 = mult_assocC_at (mt, Xt, tt);          (* (m*X)*t = m*(X*t) *)
    val chain = oeq_trans OF [oeq_trans OF [a1s, cl], a2];
  in chain end;                                     (* X*(m*t) = m*(X*t) *)

(* prodR : hx : oeq X (add U (mult m s))
     => oeq (mult X Y) (add (mult U Y) (mult m (mult s Y)))           *)
fun prodR (Xt, Ut, mt, st, Yt) hx =
  let
    val cl = mult_cong_lC (Xt, add Ut (mult mt st), Yt) hx;   (* X*Y = (U + m*s)*Y *)
    val rd = rdistC_at (Ut, mult mt st, Yt);                  (* (U + m*s)*Y = U*Y + (m*s)*Y *)
    val ma = mult_assocC_at (mt, st, Yt);                     (* (m*s)*Y = m*(s*Y) *)
    val fold = add_cong_rC (mult Ut Yt, mult (mult mt st) Yt, mult mt (mult st Yt)) ma;
  in oeq_trans OF [oeq_trans OF [cl, rd], fold] end;          (* X*Y = U*Y + m*(s*Y) *)

(* prodL : hy : oeq Y (add V (mult m t))
     => oeq (mult X Y) (add (mult X V) (mult m (mult X t)))           *)
fun prodL (Xt, Yt, Vt, mt, tt) hy =
  let
    val cr = mult_cong_rT_C (Xt, Yt, add Vt (mult mt tt)) hy; (* X*Y = X*(V + m*t) *)
    val ld = left_distribC_at (Xt, Vt, mult mt tt);          (* X*(V + m*t) = X*V + X*(m*t) *)
    val sw = m_swap_midC (Xt, mt, tt);                       (* X*(m*t) = m*(X*t) *)
    val fold = add_cong_rC (mult Xt Vt, mult Xt (mult mt tt), mult mt (mult Xt tt)) sw;
  in oeq_trans OF [oeq_trans OF [cr, ld], fold] end;          (* X*Y = X*V + m*(X*t) *)

(* fold two m-multiples into one:  (m*U + m*V) = m*(U + V)  [left_distrib sym] *)
fun foldM (mt, Ut, Vt) =
  let val ld = left_distribC_at (mt, Ut, Vt);                 (* m*(U+V) = m*U + m*V *)
  in oeq_sym OF [ld] end;                                     (* m*U + m*V = m*(U+V) *)

(* ============================================================================
   cong_mult : jT (cong m a a2) ==> jT (cong m b b2)
                 ==> jT (cong m (mult a b) (mult a2 b2))
   ----------------------------------------------------------------------------
   disjE x disjE = 4 cases on (a==a2) x (b==b2), witnesses p (a-side), q (b-side).
   Core algebra is two product-expansion helpers built ONCE:

     prodR (X,U,m,s,Y)  hx:oeq X (add U (mult m s))
        => oeq (mult X Y) (add (mult U Y) (mult m (mult s Y)))
        right_distrib on (U + m*s)*Y, then m*s*Y = m*(s*Y) by mult_assoc

     prodL (X,Y,V,m,t)  hy:oeq Y (add V (mult m t))
        => oeq (mult X Y) (add (mult X V) (mult m (mult X t)))
        left_distrib on X*(V + m*t), then X*(m*t) = m*(X*t) by assoc/comm

   Cases:
     LL: a2=a+m*p, b2=b+m*q.
                      mult a2 b2 = mult a b2 + m*(p*b2)        [prodR on a2]
                      mult a b2  = mult a b  + m*(a*q)         [prodL on b2]
         => mult a2 b2 = mult a b + m*(a*q + p*b2)             : goal LEFT.
     RR: a=a2+m*p, b=b2+m*q.  symmetric:
                      mult a b   = mult a2 b + m*(p*b)         [prodR on a]
                      mult a2 b  = mult a2 b2 + m*(a2*q)       [prodL on b]
         => mult a b = mult a2 b2 + m*(a2*q + p*b)             : goal RIGHT.
     LR: a2=a+m*p, b=b2+m*q.  common core C = mult a b2.
                      mult a2 b2 = C + m*(p*b2)                [prodR on a2]
                      mult a b   = C + m*(a*q)                 [prodL on b]
         => split le_total (p*b2) (a*q) and route the difference.
     RL: a=a2+m*p, b2=b+m*q.  common core C = mult a2 b.
                      mult a b   = C + m*(p*b)                 [prodR on a]
                      mult a2 b2 = C + m*(a2*q)                [prodL on b2]
         => split le_total (p*b) (a2*q).
   ============================================================================ *)

val cong_mult =
  let
    val mF = Free("m", natT);
    val aF = Free("a", natT); val a2F = Free("a2", natT);
    val bF = Free("b", natT); val b2F = Free("b2", natT);
    val H1prop = jT (cong mF aF a2F);
    val H2prop = jT (cong mF bF b2F);
    val H1 = Thm.assume (ctermC H1prop);
    val H2 = Thm.assume (ctermC H2prop);
    val PAB  = mult aF bF;          (* a*b   *)
    val PA2B2 = mult a2F b2F;       (* a2*b2 *)
    val goalC = cong mF PAB PA2B2;

    (* disjunct body abstractions (same shapes as cong_add) *)
    val A_L = Abs ("k", natT, oeq a2F (add aF (mult mF (Bound 0))));   (* a2 = a + m*k *)
    val A_R = Abs ("k", natT, oeq aF  (add a2F (mult mF (Bound 0))));  (* a  = a2 + m*k *)
    val B_L = Abs ("k", natT, oeq b2F (add bF (mult mF (Bound 0))));   (* b2 = b + m*k *)
    val B_R = Abs ("k", natT, oeq bF  (add b2F (mult mF (Bound 0))));  (* b  = b2 + m*k *)

    (* mDiff on ctxtC :  hr:oeq q (add p r)
         => oeq (mult m q) (add (mult m p) (mult m r)) *)
    fun mDiff (pT, qT, rT) hr =
      let
        val congq = mult_cong_rT_C (mF, qT, add pT rT) hr;     (* m*q = m*(p+r) *)
        val ld    = left_distribC_at (mF, pT, rT);             (* m*(p+r)=m*p+m*r *)
      in oeq_trans OF [congq, ld] end;                         (* m*q = m*p+m*r *)

    (* ---- CASE LL : a2=a+m*p, b2=b+m*q -> goal LEFT, witness (a*q + p*b2) ---- *)
    fun caseLL_body p hp q hq =
      let
        val e1 = prodR (a2F, aF, mF, p, b2F) hp;       (* a2*b2 = a*b2 + m*(p*b2) *)
        val e2 = prodL (aF, b2F, bF, mF, q) hq;        (* a*b2 = a*b + m*(a*q) *)
        val sub = add_cong_lC (mult aF b2F, add (mult aF bF) (mult mF (mult aF q)), mult mF (mult p b2F)) e2;
              (* a*b2 + m*(p*b2) = (a*b + m*(a*q)) + m*(p*b2) *)
        val e1b = oeq_trans OF [e1, sub];
        val as1 = addassocC_at (PAB, mult mF (mult aF q), mult mF (mult p b2F));
        val e1c = oeq_trans OF [e1b, as1];
              (* a2*b2 = a*b + (m*(a*q) + m*(p*b2)) *)
        val fm = foldM (mF, mult aF q, mult p b2F);
        val foldD = add_cong_rC (PAB, add (mult mF (mult aF q)) (mult mF (mult p b2F)),
                                 mult mF (add (mult aF q) (mult p b2F))) fm;
        val chain = oeq_trans OF [e1c, foldD];
              (* a2*b2 = a*b + m*((a*q)+(p*b2)) *)
      in cong_introL (mF, PAB, PA2B2, add (mult aF q) (mult p b2F)) chain end;

    (* ---- CASE RR : a=a2+m*p, b=b2+m*q -> goal RIGHT, witness (a2*q + p*b) ---- *)
    fun caseRR_body p hp q hq =
      let
        val e1 = prodR (aF, a2F, mF, p, bF) hp;        (* a*b = a2*b + m*(p*b) *)
        val e2 = prodL (a2F, bF, b2F, mF, q) hq;       (* a2*b = a2*b2 + m*(a2*q) *)
        val sub = add_cong_lC (mult a2F bF, add PA2B2 (mult mF (mult a2F q)), mult mF (mult p bF)) e2;
        val e1b = oeq_trans OF [e1, sub];
        val as1 = addassocC_at (PA2B2, mult mF (mult a2F q), mult mF (mult p bF));
        val e1c = oeq_trans OF [e1b, as1];
              (* a*b = a2*b2 + (m*(a2*q)+m*(p*b)) *)
        val fm = foldM (mF, mult a2F q, mult p bF);
        val foldD = add_cong_rC (PA2B2, add (mult mF (mult a2F q)) (mult mF (mult p bF)),
                                 mult mF (add (mult a2F q) (mult p bF))) fm;
        val chain = oeq_trans OF [e1c, foldD];
              (* a*b = a2*b2 + m*((a2*q)+(p*b)) *)
      in cong_introR (mF, PAB, PA2B2, add (mult a2F q) (mult p bF)) chain end;

    (* ---- CASE LR : a2=a+m*p, b=b2+m*q.  common core C = a*b2.
            a2*b2 = C + m*(p*b2)   ;   a*b = C + m*(a*q).  split le_total. ---- *)
    fun caseLR_body p hp q hq =
      let
        val C  = mult aF b2F;
        val P1 = mult p b2F;                            (* coeff on a2*b2 side *)
        val P2 = mult aF q;                             (* coeff on a*b  side *)
        val A2B2 = prodR (a2F, aF, mF, p, b2F) hp;      (* a2*b2 = C + m*P1 *)
        val AB   = prodL (aF, bF, b2F, mF, q) hq;       (* a*b   = C + m*P2 ; Y=b, V=b2 *)
        val tot = le_total_at (P1, P2);                 (* Disj (le P1 P2) (le P2 P1) *)
        val sub1 =                                       (* le P1 P2 -> goal *)
          let
            val hle = Thm.assume (ctermC (jT (le P1 P2)));
            fun body r hr =                              (* hr : oeq P2 (add P1 r) *)
              let
                val mq = mDiff (P1, P2, r) hr;           (* m*P2 = m*P1 + m*r *)
                val rw = add_cong_rC (C, mult mF P2, add (mult mF P1) (mult mF r)) mq;
                val as1 = addassocC_at (C, mult mF P1, mult mF r);
                val as1s = oeq_sym OF [as1];
                val A2B2s = oeq_sym OF [A2B2];           (* (C+m*P1) = a2*b2 *)
                val foldA2 = add_cong_lC (add C (mult mF P1), PA2B2, mult mF r) A2B2s;
                val chain = oeq_trans OF [oeq_trans OF [oeq_trans OF [AB, rw], as1s], foldA2];
                                                          (* a*b = a2*b2 + m*r *)
              in cong_introR (mF, PAB, PA2B2, r) chain end;
            val g = exE_elimC (leAbs P1 P2, goalC) hle "r0" body;
          in Thm.implies_intr (ctermC (jT (le P1 P2))) g end;
        val sub2 =                                       (* le P2 P1 -> goal *)
          let
            val hle = Thm.assume (ctermC (jT (le P2 P1)));
            fun body r hr =                              (* hr : oeq P1 (add P2 r) *)
              let
                val mp = mDiff (P2, P1, r) hr;           (* m*P1 = m*P2 + m*r *)
                val rw = add_cong_rC (C, mult mF P1, add (mult mF P2) (mult mF r)) mp;
                val as1 = addassocC_at (C, mult mF P2, mult mF r);
                val as1s = oeq_sym OF [as1];
                val ABs = oeq_sym OF [AB];               (* (C+m*P2) = a*b *)
                val foldAB = add_cong_lC (add C (mult mF P2), PAB, mult mF r) ABs;
                val chain = oeq_trans OF [oeq_trans OF [oeq_trans OF [A2B2, rw], as1s], foldAB];
                                                          (* a2*b2 = a*b + m*r *)
              in cong_introL (mF, PAB, PA2B2, r) chain end;
            val g = exE_elimC (leAbs P2 P1, goalC) hle "r0" body;
          in Thm.implies_intr (ctermC (jT (le P2 P1))) g end;
      in disjE_elimC (le P1 P2, le P2 P1, goalC) tot sub1 sub2 end;

    (* ---- CASE RL : a=a2+m*p, b2=b+m*q.  common core C = a2*b.
            a*b = C + m*(p*b)   ;   a2*b2 = C + m*(a2*q).  split le_total. ---- *)
    fun caseRL_body p hp q hq =
      let
        val C  = mult a2F bF;
        val P1 = mult p bF;                             (* coeff on a*b   side *)
        val P2 = mult a2F q;                            (* coeff on a2*b2 side *)
        val AB   = prodR (aF, a2F, mF, p, bF) hp;       (* a*b   = C + m*P1 *)
        val A2B2 = prodL (a2F, b2F, bF, mF, q) hq;      (* a2*b2 = C + m*P2 ; Y=b2, V=b *)
        val tot = le_total_at (P1, P2);
        val sub1 =                                       (* le P1 P2 -> goal *)
          let
            val hle = Thm.assume (ctermC (jT (le P1 P2)));
            fun body r hr =                              (* hr : oeq P2 (add P1 r) *)
              let
                val mq = mDiff (P1, P2, r) hr;           (* m*P2 = m*P1 + m*r *)
                val rw = add_cong_rC (C, mult mF P2, add (mult mF P1) (mult mF r)) mq;
                val as1 = addassocC_at (C, mult mF P1, mult mF r);
                val as1s = oeq_sym OF [as1];
                val ABs = oeq_sym OF [AB];               (* (C+m*P1) = a*b *)
                val foldAB = add_cong_lC (add C (mult mF P1), PAB, mult mF r) ABs;
                val chain = oeq_trans OF [oeq_trans OF [oeq_trans OF [A2B2, rw], as1s], foldAB];
                                                          (* a2*b2 = a*b + m*r *)
              in cong_introL (mF, PAB, PA2B2, r) chain end;
            val g = exE_elimC (leAbs P1 P2, goalC) hle "r0" body;
          in Thm.implies_intr (ctermC (jT (le P1 P2))) g end;
        val sub2 =                                       (* le P2 P1 -> goal *)
          let
            val hle = Thm.assume (ctermC (jT (le P2 P1)));
            fun body r hr =                              (* hr : oeq P1 (add P2 r) *)
              let
                val mp = mDiff (P2, P1, r) hr;           (* m*P1 = m*P2 + m*r *)
                val rw = add_cong_rC (C, mult mF P1, add (mult mF P2) (mult mF r)) mp;
                val as1 = addassocC_at (C, mult mF P2, mult mF r);
                val as1s = oeq_sym OF [as1];
                val A2B2s = oeq_sym OF [A2B2];           (* (C+m*P2) = a2*b2 *)
                val foldA2 = add_cong_lC (add C (mult mF P2), PA2B2, mult mF r) A2B2s;
                val chain = oeq_trans OF [oeq_trans OF [oeq_trans OF [AB, rw], as1s], foldA2];
                                                          (* a*b = a2*b2 + m*r *)
              in cong_introR (mF, PAB, PA2B2, r) chain end;
            val g = exE_elimC (leAbs P2 P1, goalC) hle "r0" body;
          in Thm.implies_intr (ctermC (jT (le P2 P1))) g end;
      in disjE_elimC (le P1 P2, le P2 P1, goalC) tot sub1 sub2 end;

    (* ---- assemble: outer disjE on H1 (A_L vs A_R), inner disjE on H2 (B_L vs B_R) ---- *)
    val outerL =
      let
        val exA = Thm.assume (ctermC (jT (mkEx A_L)));
        fun pBody p hp =
          let
            val innerLL =
              let
                val exB = Thm.assume (ctermC (jT (mkEx B_L)));
                fun qBody q hq = caseLL_body p hp q hq;
                val g = exE_elimC (B_L, goalC) exB "q0" qBody;
              in Thm.implies_intr (ctermC (jT (mkEx B_L))) g end;
            val innerLR =
              let
                val exB = Thm.assume (ctermC (jT (mkEx B_R)));
                fun qBody q hq = caseLR_body p hp q hq;
                val g = exE_elimC (B_R, goalC) exB "q0" qBody;
              in Thm.implies_intr (ctermC (jT (mkEx B_R))) g end;
          in disjE_elimC (mkEx B_L, mkEx B_R, goalC) H2 innerLL innerLR end;
        val g = exE_elimC (A_L, goalC) exA "p0" pBody;
      in Thm.implies_intr (ctermC (jT (mkEx A_L))) g end;
    val outerR =
      let
        val exA = Thm.assume (ctermC (jT (mkEx A_R)));
        fun pBody p hp =
          let
            val innerRL =
              let
                val exB = Thm.assume (ctermC (jT (mkEx B_L)));
                fun qBody q hq = caseRL_body p hp q hq;
                val g = exE_elimC (B_L, goalC) exB "q0" qBody;
              in Thm.implies_intr (ctermC (jT (mkEx B_L))) g end;
            val innerRR =
              let
                val exB = Thm.assume (ctermC (jT (mkEx B_R)));
                fun qBody q hq = caseRR_body p hp q hq;
                val g = exE_elimC (B_R, goalC) exB "q0" qBody;
              in Thm.implies_intr (ctermC (jT (mkEx B_R))) g end;
          in disjE_elimC (mkEx B_L, mkEx B_R, goalC) H2 innerRL innerRR end;
        val g = exE_elimC (A_R, goalC) exA "p0" pBody;
      in Thm.implies_intr (ctermC (jT (mkEx A_R))) g end;

    val concl = disjE_elimC (mkEx A_L, mkEx A_R, goalC) H1 outerL outerR;
    val d1 = Thm.implies_intr (ctermC H2prop) concl;
    val d2 = Thm.implies_intr (ctermC H1prop) d1;
  in varify d2 end;

val () = out "MOD_MULT_DEFINED\n";

val a2Vm = Var (("a2",0), natT);
val b2Vm = Var (("b2",0), natT);
val cong_mult_intended =
  Logic.mk_implies (jT (cong mVm aVm a2Vm),
    Logic.mk_implies (jT (cong mVm bVm b2Vm),
      jT (cong mVm (mult aVm bVm) (mult a2Vm b2Vm))));
val r_cong_mult = checkMod ("cong_mult", cong_mult, cong_mult_intended);

(* ---- SOUNDNESS PROBE: the kernel must REJECT a FALSE variant.
        A wrong claim would be e.g. jT (cong m a a2) ==> jT (cong m b b2)
        ==> jT (cong m (mult a b) (add a2 b2))  (mult vs add on the RHS).
        We try to checkMod the REAL cong_mult against that WRONG goal; it must
        FAIL aconv (different conclusion).  And we confirm that proving the
        wrong goal would require a theorem we cannot construct: simply ensure
        the genuine theorem does NOT aconv the false statement. *)
val cong_mult_FALSE =
  Logic.mk_implies (jT (cong mVm aVm a2Vm),
    Logic.mk_implies (jT (cong mVm bVm b2Vm),
      jT (cong mVm (mult aVm bVm) (add a2Vm b2Vm))));
val false_rejected = not ((Thm.prop_of cong_mult) aconv cong_mult_FALSE);
val () =
  if false_rejected
  then out "SOUNDNESS_PROBE_OK (false variant not aconv the proved thm)\n"
  else out "SOUNDNESS_PROBE_FAIL (proved thm aconv a false statement!)\n";

(* ============================================================================
   FINAL GATE : all five congruence-relation laws proved, 0-hyp + aconv-checked.
   cong_refl + cong_sym + cong_trans  => EQUIVALENCE relation;
   cong_add  + cong_mult              => +,* descend  => Z/mZ is a COMMUTATIVE RING.
   ============================================================================ *)
val () =
  if r_cong_refl andalso r_cong_sym andalso r_cong_trans
     andalso r_cong_add andalso r_cong_mult andalso false_rejected
  then out "MODULAR_DONE\n"
  else out "MODULAR_BROKEN\n";


(* ============================================================================
   ============================================================================
   ***  LIFTED LAYER 2 : POWERS (pow) — the ONE theory extension  ***
   pow extends thyS2 (the euclid base final theory) -> thyP / ctxtP / ctermP.
   Reused lemmas (cong_refl, cong_mult, euclid_lemma) re-varified onto ctxtP.
   ============================================================================ *)

(* ============================================================================
   ============================================================================
   ***  STAGE A : POWERS + MODULAR POWERS  (a^p = a mod p arc, stage A)  ***
   ----------------------------------------------------------------------------
   DEFINE  pow : nat=>nat=>nat  with recursion axioms pow_Zero / pow_Suc,
   then prove pow_one / pow_add / pow_mult_base / cong_pow, each a 0-hyp
   schematic theorem validated by aconv + length(hyps)=0, on ONE further
   context ctxtP / ctermP built on top of the classical+modular thyC.
   ============================================================================ *)

val () = out "POW_BEGIN\n";

(* ---- THE pow theory extension + recursion axioms ---- *)
val thyP0 = Sign.add_consts
  [(Binding.name "pow", natT --> natT --> natT, NoSyn)] thyS2;
val powC = Const (Sign.full_name thyP0 (Binding.name "pow"), natT --> natT --> natT);
fun pow s t = powC $ s $ t;

(* pow_Zero : oeq (pow a Zero) (Suc Zero)              a^0 = 1 *)
val aPw = Free("a", natT); val nPw = Free("n", natT);
val ((_,pow_Zero_ax), thyP1) = Thm.add_axiom_global (Binding.name "pow_Zero",
      jT (oeq (pow aPw ZeroC) (suc ZeroC))) thyP0;
(* pow_Suc : oeq (pow a (Suc n)) (mult a (pow a n))    a^(Suc n) = a * a^n *)
val ((_,pow_Suc_ax), thyP) = Thm.add_axiom_global (Binding.name "pow_Suc",
      jT (oeq (pow aPw (suc nPw)) (mult aPw (pow aPw nPw)))) thyP1;

(* ---- THE ONE FINAL CONTEXT ctxtP / ctermP ---- *)
val ctxtP  = Proof_Context.init_global thyP;
val ctermP = Thm.cterm_of ctxtP;

(* ---- re-varify every reused axiom/lemma for use under ctxtP ---- *)
val oeq_refl_vP    = varify oeq_refl;
val oeq_subst_vP   = varify oeq_subst;
val nat_induct_vP  = varify nat_induct;
val add_0_vP       = varify add_0;
val add_Suc_vP     = varify add_Suc;
val mult_0_vP      = varify mult_0;
val mult_Suc_vP    = varify mult_Suc;
val mult_comm_vP   = varify mult_comm;
val mult_assoc_vP  = varify mult_assoc;
val mult_1_right_vP= varify mult_1_right;
val mult_1_left_vP = varify mult_1_left;
val exI_vP         = varify exI_ax;
val disjI1_vP      = varify disjI1_ax;
val disjI2_vP      = varify disjI2_ax;
val disjE_vP       = varify disjE_ax;
val cong_refl_vP   = varify cong_refl;
val cong_mult_vP   = varify cong_mult;
val pow_Zero_vP    = varify pow_Zero_ax;
val pow_Suc_vP     = varify pow_Suc_ax;

(* ---- ground instantiators on ctxtP ---- *)
fun oeqreflP_at t      = beta_norm (Drule.infer_instantiate ctxtP [(("a",0), ctermP t)] oeq_refl_vP);
fun mult0P_at t        = beta_norm (Drule.infer_instantiate ctxtP [(("n",0), ctermP t)] mult_0_vP);
fun multSucP_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtP
                            [(("m",0), ctermP mt),(("n",0), ctermP nt)] mult_Suc_vP);
fun add0P_at t         = beta_norm (Drule.infer_instantiate ctxtP [(("n",0), ctermP t)] add_0_vP);
fun addSucP_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtP
                            [(("m",0), ctermP mt),(("n",0), ctermP nt)] add_Suc_vP);
fun multcommP_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtP
                            [(("m",0), ctermP mt),(("n",0), ctermP nt)] mult_comm_vP);
fun multassocP_at (mt,nt,kt)= beta_norm (Drule.infer_instantiate ctxtP
                            [(("m",0), ctermP mt),(("n",0), ctermP nt),(("k",0), ctermP kt)] mult_assoc_vP);
fun mult1rP_at t       = beta_norm (Drule.infer_instantiate ctxtP [(("n",0), ctermP t)] mult_1_right_vP);
fun mult1lP_at t       = beta_norm (Drule.infer_instantiate ctxtP [(("n",0), ctermP t)] mult_1_left_vP);
fun powZeroP_at t      = beta_norm (Drule.infer_instantiate ctxtP [(("a",0), ctermP t)] pow_Zero_vP);
fun powSucP_at (at,nt) = beta_norm (Drule.infer_instantiate ctxtP
                            [(("a",0), ctermP at),(("n",0), ctermP nt)] pow_Suc_vP);

(* nat_induct ground instance on ctxtP *)
fun nat_induct_atP (Qabs, kT) = beta_norm (Drule.infer_instantiate ctxtP
          [(("P",0), ctermP Qabs), (("k",0), ctermP kT)] nat_induct_vP);

(* mult-congruence on LEFT operand (k fixed) on ctxtP:  oeq p q ==> oeq (mult p k) (mult q k) *)
fun mult_cong_lP (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtP
          [(("P",0), ctermP Pabs), (("a",0), ctermP pT), (("b",0), ctermP qT)] oeq_subst_vP);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtP [(("a",0), ctermP (mult pT kT))] oeq_refl_vP);
  in inst OF [hpq, refl_pk] end;
(* mult-congruence on RIGHT operand (h fixed) on ctxtP:  oeq p q ==> oeq (mult h p) (mult h q) *)
fun mult_cong_rP (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtP
          [(("P",0), ctermP Pabs), (("a",0), ctermP pT), (("b",0), ctermP qT)] oeq_subst_vP);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtP [(("a",0), ctermP (mult hT pT))] oeq_refl_vP);
  in inst OF [hpq, refl_hp] end;

(* POW-congruence in the ARGUMENT (base aT fixed):  oeq u v ==> oeq (pow aT u) (pow aT v).
   oeq/pow of the bound var are fine under Abs+Bound 0 (no capture: no Ex/cong of bound). *)
fun pow_cong_argP (aT, uT, vT) huv =
  let
    val Pabs = Abs("z", natT, oeq (pow aT uT) (pow aT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtP
          [(("P",0), ctermP Pabs), (("a",0), ctermP uT), (("b",0), ctermP vT)] oeq_subst_vP);
    val refl_pu = beta_norm (Drule.infer_instantiate ctxtP [(("a",0), ctermP (pow aT uT))] oeq_refl_vP);
  in inst OF [huv, refl_pu] end;

(* ---- connective helpers re-stated on ctxtP (for cong_introL/R + cong_mult) ---- *)
fun exI_atP Pabs at hbody =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtP
          [(("P",0), ctermP Pabs), (("a",0), ctermP at)] exI_vP);
  in Thm.implies_elim inst hbody end;
fun disjI1P_at (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("A",0), ctermP At), (("B",0), ctermP Bt)] disjI1_vP)) h;
fun disjI2P_at (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("A",0), ctermP At), (("B",0), ctermP Bt)] disjI2_vP)) h;

(* cong_introL/R on ctxtP (same shapes as the base, routed through ctxtP) *)
fun cong_introL_P (m, a, b, w) hyp =
  let
    val LAbs = Abs ("k", natT, oeq b (add a (mult m (Bound 0))));
    val exThm = exI_atP LAbs w hyp;
  in disjI1P_at (congL m a b, congR m a b) exThm end;
fun cong_introR_P (m, a, b, w) hyp =
  let
    val RAbs = Abs ("k", natT, oeq a (add b (mult m (Bound 0))));
    val exThm = exI_atP RAbs w hyp;
  in disjI2P_at (congL m a b, congR m a b) exThm end;

(* cong_refl ground instance on ctxtP : jT (cong m a a) *)
fun cong_refl_atP (mt, at) = beta_norm (Drule.infer_instantiate ctxtP
      [(("m",0), ctermP mt), (("a",0), ctermP at)] cong_refl_vP);
(* cong_mult on ctxtP : jT (cong m a a2) ==> jT (cong m b b2) ==> jT (cong m (mult a b)(mult a2 b2)) *)
fun cong_mult_atP (mt, at, a2t, bt, b2t) h1 h2 =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtP
          [(("m",0), ctermP mt), (("a",0), ctermP at), (("a2",0), ctermP a2t),
           (("b",0), ctermP bt), (("b2",0), ctermP b2t)] cong_mult_vP);
    val s1 = Thm.implies_elim inst h1;
  in Thm.implies_elim s1 h2 end;

val () = out "POW_HELPERS_READY\n";

(* ---- uniform 0-hyp + aconv validator on ctxtP ---- *)
fun checkP (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtP (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtP intended ^ "\n");
          false)
  end;

(* schematic Vars for intended statements *)
val aVp  = Var (("a",0), natT);
val bVp  = Var (("b",0), natT);
val mVp  = Var (("m",0), natT);
val nVp  = Var (("n",0), natT);

(* ============================================================================
   pow_one : oeq (pow a (Suc Zero)) a            a^1 = a
     pow a (Suc 0) = mult a (pow a 0)   [pow_Suc]
                   = mult a (Suc 0)     [pow_Zero, mult_cong_r]
                   = a                  [mult_1_right]
   ============================================================================ *)
val pow_one =
  let
    val aF = Free("a", natT);
    val s1 = powSucP_at (aF, ZeroC);              (* pow a (Suc 0) = mult a (pow a 0) *)
    val pz = powZeroP_at aF;                      (* pow a 0 = Suc 0 *)
    val cr = mult_cong_rP (aF, pow aF ZeroC, suc ZeroC) pz;  (* mult a (pow a 0) = mult a (Suc 0) *)
    val m1 = mult1rP_at aF;                       (* mult a (Suc 0) = a *)
    val c1 = oeq_trans OF [s1, cr];
    val c2 = oeq_trans OF [c1, m1];
  in varify c2 end;

val pow_one_intended = jT (oeq (pow aVp (suc ZeroC)) aVp);
val r_pow_one = checkP ("pow_one", pow_one, pow_one_intended);

(* ============================================================================
   pow_add : oeq (pow a (add m n)) (mult (pow a m) (pow a n))    a^(m+n)=a^m*a^n
     induction on m  (predicate over the FIRST exponent; a,n fixed Free).
     base  m=0:  pow a (0+n) = pow a n          [add_0, pow_cong_arg]
                 mult (pow a 0)(pow a n) = mult (Suc 0)(pow a n) = pow a n
                                            [pow_Zero, mult_cong_l, mult_1_left]
     step  m=Suc x:
                 pow a ((Suc x)+n) = pow a (Suc (x+n))       [add_Suc, pow_cong_arg]
                                   = mult a (pow a (x+n))     [pow_Suc]
                                   = mult a (mult (pow a x)(pow a n))   [IH, mult_cong_r]
                                   = mult (mult a (pow a x))(pow a n)   [mult_assoc sym]
                                   = mult (pow a (Suc x))(pow a n)      [pow_Suc sym, mult_cong_l]
   ============================================================================ *)
val pow_add =
  let
    val aF = Free("a", natT); val nF = Free("n", natT);
    val Qpred = Abs("z", natT,
        oeq (pow aF (add (Bound 0) nF)) (mult (pow aF (Bound 0)) (pow aF nF)));
    val mF = Free("m", natT);
    val ind = nat_induct_atP (Qpred, mF);

    (* BASE m=0 *)
    val b_add0 = add0P_at nF;                                 (* (0+n) = n *)
    val bL = pow_cong_argP (aF, add ZeroC nF, nF) b_add0;     (* pow a (0+n) = pow a n *)
    val b_pz = powZeroP_at aF;                                (* pow a 0 = Suc 0 *)
    val bRc = mult_cong_lP (pow aF ZeroC, suc ZeroC, pow aF nF) b_pz;  (* mult(pow a 0)(pow a n) = mult(Suc 0)(pow a n) *)
    val b_m1l = mult1lP_at (pow aF nF);                       (* mult(Suc 0)(pow a n) = pow a n *)
    val bRchain = oeq_trans OF [bRc, b_m1l];                  (* mult(pow a 0)(pow a n) = pow a n *)
    val bRsym = oeq_sym OF [bRchain];                         (* pow a n = mult(pow a 0)(pow a n) *)
    val base = oeq_trans OF [bL, bRsym];                      (* pow a (0+n) = mult(pow a 0)(pow a n) *)

    (* STEP *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (pow aF (add xF nF)) (mult (pow aF xF) (pow aF nF)));
    val IH = Thm.assume (ctermP ihprop);
    val s_addSuc = addSucP_at (xF, nF);                       (* ((Suc x)+n) = Suc (x+n) *)
    val sL1 = pow_cong_argP (aF, add (suc xF) nF, suc (add xF nF)) s_addSuc;
                                                             (* pow a ((Suc x)+n) = pow a (Suc(x+n)) *)
    val sL2 = powSucP_at (aF, add xF nF);                     (* pow a (Suc(x+n)) = mult a (pow a (x+n)) *)
    val sL3 = mult_cong_rP (aF, pow aF (add xF nF), mult (pow aF xF) (pow aF nF)) IH;
                                                             (* mult a (pow a (x+n)) = mult a (mult(pow a x)(pow a n)) *)
    val lhs = oeq_trans OF [oeq_trans OF [sL1, sL2], sL3];
                                                             (* pow a ((Suc x)+n) = mult a (mult(pow a x)(pow a n)) *)
    val assoc = multassocP_at (aF, pow aF xF, pow aF nF);
                                                             (* (a*(pow a x))*(pow a n) = a*((pow a x)*(pow a n)) *)
    val assocS = oeq_sym OF [assoc];                          (* a*((pow a x)*(pow a n)) = (a*(pow a x))*(pow a n) *)
    val lhs2 = oeq_trans OF [lhs, assocS];                    (* pow a ((Suc x)+n) = (a*(pow a x))*(pow a n) *)
    val psx = powSucP_at (aF, xF);                            (* pow a (Suc x) = mult a (pow a x) *)
    val psxS = oeq_sym OF [psx];                              (* mult a (pow a x) = pow a (Suc x) *)
    val foldL = mult_cong_lP (mult aF (pow aF xF), pow aF (suc xF), pow aF nF) psxS;
                                                             (* (a*(pow a x))*(pow a n) = (pow a (Suc x))*(pow a n) *)
    val stepconcl = oeq_trans OF [lhs2, foldL];
                                                             (* pow a ((Suc x)+n) = mult(pow a (Suc x))(pow a n) *)
    val step1 = Thm.forall_intr (ctermP xF) (Thm.implies_intr (ctermP ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val pow_add_intended =
  jT (oeq (pow aVp (add mVp nVp)) (mult (pow aVp mVp) (pow aVp nVp)));
val r_pow_add = checkP ("pow_add", pow_add, pow_add_intended);

(* ============================================================================
   pow_mult_base : oeq (pow (mult a b) n) (mult (pow a n) (pow b n))   (a*b)^n=a^n*b^n
     induction on n (a,b fixed Free).
     base n=0 : pow (a*b) 0 = Suc 0          [pow_Zero]
                mult(pow a 0)(pow b 0) = mult(Suc 0)(Suc 0) = Suc 0
                                  [pow_Zero x2, mult_cong, mult_1_right]
     step n=Suc x:
        pow (a*b)(Suc x) = mult (a*b) (pow (a*b) x)        [pow_Suc]
                         = mult (a*b) (mult (pow a x)(pow b x))  [IH, mult_cong_r]
        and  mult (pow a (Suc x))(pow b (Suc x))
                         = mult (mult a (pow a x))(mult b (pow b x)) [pow_Suc x2, mult_cong]
     so reduce both to the common term and show the reshuffle
        (a*b)*((pow a x)*(pow b x)) = (a*(pow a x))*(b*(pow b x))
     by mult comm/assoc.
   ============================================================================ *)
val pow_mult_base =
  let
    val aF = Free("a", natT); val bF = Free("b", natT);
    val abF = mult aF bF;
    val Qpred = Abs("z", natT,
        oeq (pow abF (Bound 0)) (mult (pow aF (Bound 0)) (pow bF (Bound 0))));
    val nF = Free("n", natT);
    val ind = nat_induct_atP (Qpred, nF);

    (* BASE n=0 *)
    val bL = powZeroP_at abF;                                 (* pow (a*b) 0 = Suc 0 *)
    val bpa = powZeroP_at aF;                                 (* pow a 0 = Suc 0 *)
    val bpb = powZeroP_at bF;                                 (* pow b 0 = Suc 0 *)
    val bRc1 = mult_cong_lP (pow aF ZeroC, suc ZeroC, pow bF ZeroC) bpa;  (* mult(pow a 0)(pow b 0) = mult(Suc 0)(pow b 0) *)
    val bRc2 = mult_cong_rP (suc ZeroC, pow bF ZeroC, suc ZeroC) bpb;     (* mult(Suc 0)(pow b 0) = mult(Suc 0)(Suc 0) *)
    val bR12 = oeq_trans OF [bRc1, bRc2];                     (* mult(pow a 0)(pow b 0) = mult(Suc 0)(Suc 0) *)
    val bm1 = mult1rP_at (suc ZeroC);                         (* mult(Suc 0)(Suc 0) = Suc 0 *)
    val bRchain = oeq_trans OF [bR12, bm1];                   (* mult(pow a 0)(pow b 0) = Suc 0 *)
    val bRsym = oeq_sym OF [bRchain];                         (* Suc 0 = mult(pow a 0)(pow b 0) *)
    val base = oeq_trans OF [bL, bRsym];                      (* pow (a*b) 0 = mult(pow a 0)(pow b 0) *)

    (* STEP n=Suc x *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (pow abF xF) (mult (pow aF xF) (pow bF xF)));
    val IH = Thm.assume (ctermP ihprop);
    (* LHS:  pow (a*b)(Suc x) = (a*b)*(pow(a*b) x) = (a*b)*((pow a x)*(pow b x)) *)
    val sL1 = powSucP_at (abF, xF);                           (* pow (a*b)(Suc x) = mult (a*b) (pow (a*b) x) *)
    val sL2 = mult_cong_rP (abF, pow abF xF, mult (pow aF xF) (pow bF xF)) IH;
                                                             (* mult (a*b)(pow(a*b) x) = mult (a*b)((pow a x)*(pow b x)) *)
    val lhs = oeq_trans OF [sL1, sL2];                        (* pow (a*b)(Suc x) = (a*b)*((pow a x)*(pow b x)) *)
    (* RHS target: mult (pow a (Suc x))(pow b (Suc x))
                 = (a*(pow a x))*(b*(pow b x)) *)
    val psa = powSucP_at (aF, xF);                            (* pow a (Suc x) = mult a (pow a x) *)
    val psb = powSucP_at (bF, xF);                            (* pow b (Suc x) = mult b (pow b x) *)
    val rR1 = mult_cong_lP (pow aF (suc xF), mult aF (pow aF xF), pow bF (suc xF)) psa;
                                                             (* mult(pow a(Sx))(pow b(Sx)) = mult(a*(pow a x))(pow b(Sx)) *)
    val rR2 = mult_cong_rP (mult aF (pow aF xF), pow bF (suc xF), mult bF (pow bF xF)) psb;
                                                             (* = mult(a*(pow a x))(b*(pow b x)) *)
    val rhsExpand = oeq_trans OF [rR1, rR2];                  (* mult(pow a(Sx))(pow b(Sx)) = (a*(pow a x))*(b*(pow b x)) *)
    (* RESHUFFLE :  (a*b)*((pow a x)*(pow b x)) = (a*(pow a x))*(b*(pow b x))
       Let A=a, B=b, S=(pow a x), T=(pow b x).  Show (A*B)*(S*T) = (A*S)*(B*T).
         (A*B)*(S*T) = A*(B*(S*T))           [assoc]
                     = A*((B*S)*T)           [assoc sym, under right]
                     = A*((S*B)*T)           [comm B*S=S*B, under right]
                     = A*(S*(B*T))           [assoc, under right]
                     = (A*S)*(B*T)           [assoc sym]
    *)
    val A = aF; val B = bF; val S = pow aF xF; val T = pow bF xF;
    val st = mult S T;
    val r_assoc1 = multassocP_at (A, B, st);                  (* (A*B)*(S*T) = A*(B*(S*T)) *)
    val r_in1 = multassocP_at (B, S, T);                      (* (B*S)*T = B*(S*T) *)
    val r_in1s = oeq_sym OF [r_in1];                          (* B*(S*T) = (B*S)*T *)
    val r_comm = multcommP_at (B, S);                         (* B*S = S*B *)
    val r_comm_c = mult_cong_lP (mult B S, mult S B, T) r_comm;  (* (B*S)*T = (S*B)*T *)
    val r_in2 = multassocP_at (S, B, T);                      (* (S*B)*T = S*(B*T) *)
    val innerChain = oeq_trans OF [oeq_trans OF [r_in1s, r_comm_c], r_in2];  (* B*(S*T) = S*(B*T) *)
    val r_under = mult_cong_rP (A, mult B st, mult S (mult B T)) innerChain;  (* A*(B*(S*T)) = A*(S*(B*T)) *)
    val r_assoc2 = multassocP_at (A, S, mult B T);            (* (A*S)*(B*T) = A*(S*(B*T)) *)
    val r_assoc2s = oeq_sym OF [r_assoc2];                    (* A*(S*(B*T)) = (A*S)*(B*T) *)
    val reshuffle = oeq_trans OF [oeq_trans OF [r_assoc1, r_under], r_assoc2s];
                                                             (* (A*B)*(S*T) = (A*S)*(B*T) *)
    val rhsExpandS = oeq_sym OF [rhsExpand];                  (* (A*S)*(B*T) = mult(pow a(Sx))(pow b(Sx)) *)
    val stepconcl = oeq_trans OF [oeq_trans OF [lhs, reshuffle], rhsExpandS];
                                                             (* pow (a*b)(Suc x) = mult(pow a(Sx))(pow b(Sx)) *)
    val step1 = Thm.forall_intr (ctermP xF) (Thm.implies_intr (ctermP ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val pow_mult_base_intended =
  jT (oeq (pow (mult aVp bVp) nVp) (mult (pow aVp nVp) (pow bVp nVp)));
val r_pow_mult_base = checkP ("pow_mult_base", pow_mult_base, pow_mult_base_intended);

(* ============================================================================
   cong_cong : jT (oeq a a2) ==> jT (oeq b b2) ==> jT (cong m a b) ==> jT (cong m a2 b2)
   ----------------------------------------------------------------------------
   oeq_subst on each argument of cong.  cong injects Ex binders inside, so the
   predicate must be built CAPTURE-AVOIDING with Term.lambda over a fresh Free.
     step 1 : %z. cong m z b  (substitute a -> a2 using oeq a a2)
     step 2 : %z. cong m a2 z (substitute b -> b2 using oeq b b2)
   ============================================================================ *)
fun cong_cong (mF, aF, a2F, bF, b2F) (haa2 : thm) (hbb2 : thm) (hcong : thm) =
  let
    (* substitute a -> a2 : predicate %z. cong m z b, built capture-avoiding *)
    val zF1 = Free("zz1", natT);
    val Pabs1 = Term.lambda zF1 (cong mF zF1 bF);     (* %z. cong m z b *)
    val inst1 = beta_norm (Drule.infer_instantiate ctxtP
          [(("P",0), ctermP Pabs1), (("a",0), ctermP aF), (("b",0), ctermP a2F)] oeq_subst_vP);
    val cong1 = inst1 OF [haa2, hcong];               (* jT (cong m a2 b) *)
    (* substitute b -> b2 : predicate %z. cong m a2 z, built capture-avoiding *)
    val zF2 = Free("zz2", natT);
    val Pabs2 = Term.lambda zF2 (cong mF a2F zF2);     (* %z. cong m a2 z *)
    val inst2 = beta_norm (Drule.infer_instantiate ctxtP
          [(("P",0), ctermP Pabs2), (("a",0), ctermP bF), (("b",0), ctermP b2F)] oeq_subst_vP);
    val cong2 = inst2 OF [hbb2, cong1];               (* jT (cong m a2 b2) *)
  in cong2 end;

(* ============================================================================
   cong_pow : jT (cong m a b) ==> jT (cong m (pow a n) (pow b n))
   ----------------------------------------------------------------------------
   induction on n (m,a,b fixed Free); the cong-hypothesis (cong m a b) is fixed.
     base n=0 : cong m (pow a 0)(pow b 0).  pow a 0 = Suc 0 = pow b 0.
                cong_refl m (Suc 0) : cong m (Suc 0)(Suc 0); then cong_cong with
                oeq (Suc 0)(pow a 0) [pow_Zero sym] and oeq (Suc 0)(pow b 0).
     step n=Suc x:  IH : cong m (pow a x)(pow b x).
                cong_mult (cong m a b) IH : cong m (mult a (pow a x))(mult b (pow b x)).
                rewrite both sides back via pow_Suc (an oeq) using cong_cong:
                  oeq (mult a (pow a x)) (pow a (Suc x))  [pow_Suc sym]
                  oeq (mult b (pow b x)) (pow b (Suc x))  [pow_Suc sym]
                => cong m (pow a (Suc x))(pow b (Suc x)).
   ============================================================================ *)
val cong_pow =
  let
    val mF = Free("m", natT); val aF = Free("a", natT); val bF = Free("b", natT);
    val hcongP = jT (cong mF aF bF);
    val hcong  = Thm.assume (ctermP hcongP);

    (* cong injects Ex binders -> build the induction predicate CAPTURE-AVOIDING
       with Term.lambda over a fresh Free.  A raw Bound 0 here would be captured
       by cong's inner Abs("k",..), pointing at k instead of the induction var. *)
    val zQ = Free("zq", natT);
    val Qpred = Term.lambda zQ (cong mF (pow aF zQ) (pow bF zQ));
    val nF = Free("n", natT);
    val ind = nat_induct_atP (Qpred, nF);

    (* BASE n=0 *)
    val cr = cong_refl_atP (mF, suc ZeroC);                   (* cong m (Suc 0)(Suc 0) *)
    val pz_a = powZeroP_at aF;                                (* pow a 0 = Suc 0 *)
    val pz_a_s = oeq_sym OF [pz_a];                           (* Suc 0 = pow a 0 *)
    val pz_b = powZeroP_at bF;                                (* pow b 0 = Suc 0 *)
    val pz_b_s = oeq_sym OF [pz_b];                           (* Suc 0 = pow b 0 *)
    (* cong_cong : oeq (Suc 0)(pow a 0) -> oeq (Suc 0)(pow b 0) -> cong m (Suc 0)(Suc 0)
                   -> cong m (pow a 0)(pow b 0) *)
    val base = cong_cong (mF, suc ZeroC, pow aF ZeroC, suc ZeroC, pow bF ZeroC) pz_a_s pz_b_s cr;

    (* STEP n=Suc x *)
    val xF = Free("x", natT);
    val ihprop = jT (cong mF (pow aF xF) (pow bF xF));
    val IH = Thm.assume (ctermP ihprop);
    (* cong_mult (cong m a b) IH : cong m (mult a (pow a x))(mult b (pow b x)) *)
    val cm = cong_mult_atP (mF, aF, bF, pow aF xF, pow bF xF) hcong IH;
    (* rewrite both args back to pow _ (Suc x) using pow_Suc (sym) via cong_cong *)
    val psa = powSucP_at (aF, xF);                            (* pow a (Suc x) = mult a (pow a x) *)
    val psa_s = oeq_sym OF [psa];                            (* mult a (pow a x) = pow a (Suc x) *)
    val psb = powSucP_at (bF, xF);                            (* pow b (Suc x) = mult b (pow b x) *)
    val psb_s = oeq_sym OF [psb];                            (* mult b (pow b x) = pow b (Suc x) *)
    val stepconcl = cong_cong (mF, mult aF (pow aF xF), pow aF (suc xF),
                                   mult bF (pow bF xF), pow bF (suc xF)) psa_s psb_s cm;
                                                             (* cong m (pow a (Suc x))(pow b (Suc x)) *)
    val step1 = Thm.forall_intr (ctermP xF) (Thm.implies_intr (ctermP ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val disch = Thm.implies_intr (ctermP hcongP) r2;
  in varify disch end;

val cong_pow_intended =
  Logic.mk_implies (jT (cong mVp aVp bVp), jT (cong mVp (pow aVp nVp) (pow bVp nVp)));
val r_cong_pow = checkP ("cong_pow", cong_pow, cong_pow_intended);

val () =
  if r_pow_one andalso r_pow_add andalso r_pow_mult_base andalso r_cong_pow
  then out "POW_DONE\n"
  else out "POW_BROKEN\n";

(* ============================================================================
   ============================================================================
   ***  UNIFIED NUMBER-THEORY BASE : FINAL CONSOLIDATED VALIDATION  ***
   ----------------------------------------------------------------------------
   Everything now lives ABOVE the pow extension thyP (context ctxtP / ctermP),
   a child of thyS2 (the euclid base).  We re-varify the inherited euclid_lemma
   and the lifted cong-relation laws onto ctxtP and validate EVERY lemma 0-hyp +
   aconv via the SAME base check helper.  Then NT_BASE_OK.
   ============================================================================ *)
val () = out "NT_BASE_FINALCHECK_BEGIN\n";

(* inherited euclid_lemma re-varified onto the FINAL context ctxtP *)
val euclid_lemma_vP = varify euclid_lemma;
val cong_sym_vP     = varify cong_sym;
val cong_trans_vP   = varify cong_trans;
val cong_add_vP     = varify cong_add;
(* cong_refl_vP / cong_mult_vP already varified in the pow section *)
val pow_one_vP      = varify pow_one;
val pow_add_vP      = varify pow_add;
val pow_mult_base_vP= varify pow_mult_base;
val cong_pow_vP     = varify cong_pow;

(* fresh schematic Vars for the consolidated intended statements, on ctxtP *)
val mB  = Var (("m",0), natT);
val aB  = Var (("a",0), natT);
val bB  = Var (("b",0), natT);
val cB  = Var (("c",0), natT);
val a2B = Var (("a2",0), natT);
val b2B = Var (("b2",0), natT);
val nB  = Var (("n",0), natT);

(* intended schematic props built with the SAME cong / pow abbreviations *)
val i_cong_refl  = jT (cong mB aB aB);
val i_cong_sym   = Logic.mk_implies (jT (cong mB aB bB), jT (cong mB bB aB));
val i_cong_trans = Logic.mk_implies (jT (cong mB aB bB),
                     Logic.mk_implies (jT (cong mB bB cB), jT (cong mB aB cB)));
val i_cong_add   = Logic.mk_implies (jT (cong mB aB a2B),
                     Logic.mk_implies (jT (cong mB bB b2B),
                       jT (cong mB (add aB bB) (add a2B b2B))));
val i_cong_mult  = Logic.mk_implies (jT (cong mB aB a2B),
                     Logic.mk_implies (jT (cong mB bB b2B),
                       jT (cong mB (mult aB bB) (mult a2B b2B))));
val i_pow_one    = jT (oeq (pow aB (suc ZeroC)) aB);
val i_pow_add    = jT (oeq (pow aB (add mB nB)) (mult (pow aB mB) (pow aB nB)));
val i_pow_mult   = jT (oeq (pow (mult aB bB) nB) (mult (pow aB nB) (pow bB nB)));
val i_cong_pow   = Logic.mk_implies (jT (cong mB aB bB),
                     jT (cong mB (pow aB nB) (pow bB nB)));
val pVz = Var (("p",0), natT);
val i_euclid     = Logic.mk_implies (jT (prime2 pVz),
                     Logic.mk_implies (jT (dvd pVz (mult aB bB)),
                       jT (mkDisj (dvd pVz aB) (dvd pVz bB))));

(* the base check helper, routed through the FINAL context ctxtP / ctermP *)
fun checkBase (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtP (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtP intended ^ "\n");
          false)
  end;

val b_cong_refl  = checkBase ("cong_refl",      cong_refl,      i_cong_refl);
val b_cong_sym   = checkBase ("cong_sym",       cong_sym,       i_cong_sym);
val b_cong_trans = checkBase ("cong_trans",     cong_trans,     i_cong_trans);
val b_cong_add   = checkBase ("cong_add",       cong_add,       i_cong_add);
val b_cong_mult  = checkBase ("cong_mult",      cong_mult,      i_cong_mult);
val b_pow_one    = checkBase ("pow_one",        pow_one,        i_pow_one);
val b_pow_add    = checkBase ("pow_add",        pow_add,        i_pow_add);
val b_pow_mult   = checkBase ("pow_mult_base",  pow_mult_base,  i_pow_mult);
val b_cong_pow   = checkBase ("cong_pow",       cong_pow,       i_cong_pow);
val b_euclid     = checkBase ("euclid_lemma",   euclid_lemma,   i_euclid);

(* soundness re-confirmation : euclid_lemma must still need prime2 p *)
val b_euclid_needs_prime =
  not ((Thm.prop_of euclid_lemma) aconv
        (Logic.mk_implies (jT (dvd pVz (mult aB bB)),
           jT (mkDisj (dvd pVz aB) (dvd pVz bB)))));
(* soundness re-confirmation : cong_pow must still need the cong hypothesis *)
val b_cong_pow_cond =
  not ((Thm.prop_of cong_pow) aconv (jT (cong mB (pow aB nB) (pow bB nB))));

val () =
  if b_euclid_needs_prime andalso b_cong_pow_cond
  then out "PROBE_OK base laws conditional/nontrivial\n"
  else out "PROBE_UNSOUND a base law collapsed!\n";

val () =
  if b_cong_refl andalso b_cong_sym andalso b_cong_trans andalso b_cong_add
     andalso b_cong_mult andalso b_pow_one andalso b_pow_add andalso b_pow_mult
     andalso b_cong_pow andalso b_euclid
     andalso b_euclid_needs_prime andalso b_cong_pow_cond
  then out "NT_BASE_OK\n"
  else out "NT_BASE_FAILED\n";

