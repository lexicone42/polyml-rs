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
   THE BINOMIAL THEOREM, in Isabelle/Pure on the polyml-rs interpreter —
   Stage C2 of the Fermat-little-theorem arc (the hardest proof in the tower).
   (test: isabelle_binom_thm.rs)
   ----------------------------------------------------------------------------
     binom_theorem :
       |- (a+b)^n = SUM_{k=0}^{n} C(n,k) * a^k * b^(n-k)
     (oeq (pow (add a b) n) (sumf (%k. mult (binom n k)(mult (pow a k)(pow b (sub n k)))) n))
   A 0-hypothesis theorem; only classical assumption = excluded middle.

   Foundation (sum-algebra) proved here too: sum_mult_l (c*sum = sum of c*f),
   sum_add (sum f + sum g = sum (f+g)), sum_peel_first (peel/reindex the first term),
   binom_n_n (C(n,n)=1, via binom_diag_zero: C(n,n+1+j)=0 by single induction with the
   IH used at j AND j+1 -- sidesteps lt machinery), pow_b_sub_Suc.

   The induction (on n): (a+b)^(Suc n) = (a+b)*(a+b)^n = a*S + b*S [IH + right_distrib];
   distribute each into the sum (sum_mult_l), shift a's exponent (pow_Suc) and b's
   (pow_b_sub_Suc); the RHS at Suc n is peeled (sum_peel_first), each term Pascal-split
   (binom_Suc_Suc) into two sums via sum_add; the pieces recombine. The classic painful
   index-shift, done by genuine LCF kernel inference.

   Built on isabelle_sum.sml by a 2-phase ultracode pipeline (wf_a511fcbc-470): sum-algebra
   -> binom_theorem (3 seats, ALL proved it). Stage C3 (freshman's dream) + D (FLT) remain.
   ============================================================================ *)

(* ============================================================================
   SUMMATION OPERATOR + TRUNCATED SUBTRACTION, in Isabelle/Pure on the polyml-rs
   interpreter — Stage C1 of the Fermat-little-theorem arc.  (test: isabelle_sum.rs)
   ----------------------------------------------------------------------------
   The machinery the binomial theorem (mod p) needs, on the binom base. Pure is
   HIGHER-ORDER, so a summation over an arbitrary function is a legitimate const:
     sumf : (nat=>nat) => nat => nat   (pass concrete summands as object lambdas,
                                        beta_norm after applying f to an index).
     sumf f 0 = f 0 ;  sumf f (Suc n) = sumf f n + f (Suc n)
     sub a 0 = a ; sub 0 (Suc k) = 0 ; sub (Suc a)(Suc b) = sub a b   (truncated -)
   PROVEN (each 0-hyp; only classical assumption = excluded middle):
     sub_self   : sub n n = 0
     sub_Suc_le : k <= n ==> sub (Suc n) k = Suc (sub n k)
     sum_cong   : (!!k. k<=n ==> f k = g k) ==> sumf f n = sumf g n
   sum_cong (pointwise-equal-up-to-n functions have equal sums) is the workhorse for
   rewriting summands; it is a higher-order induction (the meta !!k hyp over f k, g k).

   Built on isabelle_binom.sml by a 2-seat ultracode fleet (wf_0d8f0cb2-45c). Stage C2
   (the binomial theorem) and C3/D (freshman's dream + FLT) remain.
   ============================================================================ *)

(* ============================================================================
   BINOMIAL COEFFICIENTS + p | C(p,k), in Isabelle/Pure on the polyml-rs
   interpreter — Stage B of the Fermat-little-theorem arc.
   (test: isabelle_binom.rs)
   ----------------------------------------------------------------------------
   On the unified number-theory base (which has Euclid's lemma + modular powers),
   defines binomial coefficients via Pascal's rule and proves the celebrated
   divisibility, each a 0-hypothesis theorem (only classical assumption = excluded
   middle):
     binom n 0 = 1 ; binom 0 (Suc k) = 0 ;
     binom (Suc n)(Suc k) = binom n k + binom n (Suc k)     (Pascal)
     absorption  : (k+1) * C(n+1,k+1) = (n+1) * C(n,k)
     p_dvd_binom : prime p ==> 0 < k ==> k < p ==> p | C(p,k)
   p_dvd_binom (a prime divides its inner binomial coefficients) is the keystone
   of Fermat's little theorem and of the freshman's dream mod p. Proof: absorption
   at (p-1,k-1) gives k * C(p,k) = p * C(p-1,k-1), so p | k*C(p,k); p prime and
   p does not divide k (0<k<p), so by Euclid's lemma p | C(p,k).

   The absorption identity is proved by induction on n with k UNIVERSAL (object
   Forall in the predicate), inner case-split on k; the Suc-k step uses the IH at
   TWO points + both Pascal directions + distributivity + mult_Suc.

   Built on isabelle_ntbase.sml by a 2-phase ultracode pipeline (wf_2f2eeca9-c88):
   binom + absorption -> p_dvd_binom (3 seats, all proved it). Stage C (binomial
   theorem mod p) and Stage D (FLT) remain.
   ============================================================================ *)

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


(* ============================================================================
   ============================================================================
   ***  STAGE B : BINOMIAL COEFFICIENTS (binom) + ABSORPTION IDENTITY  ***
   ----------------------------------------------------------------------------
   binom : nat=>nat=>nat  — a NEW const extending the unified NT base theory thyP.
   Pascal axioms:
     binom_n_0     : oeq (binom n Zero) (Suc Zero)
     binom_0_Suc   : oeq (binom Zero (Suc k)) Zero
     binom_Suc_Suc : oeq (binom (Suc n) (Suc k)) (add (binom n k) (binom n (Suc k)))
   absorption    : oeq (mult (Suc k)(binom (Suc n)(Suc k))) (mult (Suc n)(binom n k))
                   i.e. (k+1)*C(n+1,k+1) = (n+1)*C(n,k), by induction on n with k
                   UNIVERSAL inside the predicate (object Forall), inner case-split
                   on k (Zero / Suc j), the Suc-j branch uses the IH at TWO points.
   ============================================================================ *)

val () = out "BINOM_BEGIN\n";

(* ---- the binom theory extension + Pascal recursion axioms (on top of thyP) ---- *)
val thyB0 = Sign.add_consts
  [(Binding.name "binom", natT --> natT --> natT, NoSyn)] thyP;
val binomC = Const (Sign.full_name thyB0 (Binding.name "binom"), natT --> natT --> natT);
fun binom s t = binomC $ s $ t;

val nBn = Free("n", natT); val kBn = Free("k", natT);
(* binom_n_0 : oeq (binom n Zero) (Suc Zero)              C(n,0) = 1 *)
val ((_,binom_n_0_ax), thyB1) = Thm.add_axiom_global (Binding.name "binom_n_0",
      jT (oeq (binom nBn ZeroC) (suc ZeroC))) thyB0;
(* binom_0_Suc : oeq (binom Zero (Suc k)) Zero            C(0,k+1) = 0 *)
val ((_,binom_0_Suc_ax), thyB2) = Thm.add_axiom_global (Binding.name "binom_0_Suc",
      jT (oeq (binom ZeroC (suc kBn)) ZeroC)) thyB1;
(* binom_Suc_Suc : Pascal *)
val ((_,binom_Suc_Suc_ax), thyB) = Thm.add_axiom_global (Binding.name "binom_Suc_Suc",
      jT (oeq (binom (suc nBn) (suc kBn))
              (add (binom nBn kBn) (binom nBn (suc kBn))))) thyB2;

(* ---- THE ONE FINAL CONTEXT ctxtB / ctermB ---- *)
val ctxtB  = Proof_Context.init_global thyB;
val ctermB = Thm.cterm_of ctxtB;

(* ---- re-varify every reused axiom/lemma onto ctxtB ---- *)
val oeq_refl_vB     = varify oeq_refl;
val oeq_subst_vB    = varify oeq_subst;
val nat_induct_vB   = varify nat_induct;
val add_0_vB        = varify add_0;
val add_Suc_vB      = varify add_Suc;
val add_0_right_vB  = varify add_0_right;
val add_Suc_right_vB= varify add_Suc_right;
val add_comm_vB     = varify add_comm;
val add_assoc_vB    = varify add_assoc;
val mult_0_vB       = varify mult_0;
val mult_Suc_vB     = varify mult_Suc;
val mult_0_right_vB = varify mult_0_right;
val mult_Suc_right_vB = varify mult_Suc_right;
val mult_comm_vB    = varify mult_comm;
val mult_assoc_vB   = varify mult_assoc;
val mult_1_left_vB  = varify mult_1_left;
val mult_1_right_vB = varify mult_1_right;
val left_distrib_vB = varify left_distrib;
val right_distrib_vB= varify right_distrib;
val exI_vB          = varify exI_ax;
val exE_vB          = varify exE_ax;
val disjI1_vB       = varify disjI1_ax;
val disjI2_vB       = varify disjI2_ax;
val disjE_vB        = varify disjE_ax;
val allI_vB         = varify allI_ax;
val allE_vB         = varify allE_ax;
val disj_zero_or_suc_vB = varify disj_zero_or_suc;
val binom_n_0_vB    = varify binom_n_0_ax;
val binom_0_Suc_vB  = varify binom_0_Suc_ax;
val binom_Suc_Suc_vB= varify binom_Suc_Suc_ax;

(* ---- ground instantiators on ctxtB ---- *)
fun oeqreflB_at t      = beta_norm (Drule.infer_instantiate ctxtB [(("a",0), ctermB t)] oeq_refl_vB);
fun mult0B_at t        = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB t)] mult_0_vB);
fun mult0rB_at t       = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB t)] mult_0_right_vB);
fun multSucB_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtB
                            [(("m",0), ctermB mt),(("n",0), ctermB nt)] mult_Suc_vB);
fun multSucrB_at (nt,mt)= beta_norm (Drule.infer_instantiate ctxtB
                            [(("n",0), ctermB nt),(("m",0), ctermB mt)] mult_Suc_right_vB);
fun add0B_at t         = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB t)] add_0_vB);
fun add0rB_at t        = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB t)] add_0_right_vB);
fun addSucB_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtB
                            [(("m",0), ctermB mt),(("n",0), ctermB nt)] add_Suc_vB);
fun addSucrB_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtB
                            [(("m",0), ctermB mt),(("n",0), ctermB nt)] add_Suc_right_vB);
fun addcommB_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtB
                            [(("m",0), ctermB mt),(("n",0), ctermB nt)] add_comm_vB);
fun addassocB_at (mt,nt,kt)= beta_norm (Drule.infer_instantiate ctxtB
                            [(("m",0), ctermB mt),(("n",0), ctermB nt),(("k",0), ctermB kt)] add_assoc_vB);
fun multcommB_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtB
                            [(("m",0), ctermB mt),(("n",0), ctermB nt)] mult_comm_vB);
fun multassocB_at (mt,nt,kt)= beta_norm (Drule.infer_instantiate ctxtB
                            [(("m",0), ctermB mt),(("n",0), ctermB nt),(("k",0), ctermB kt)] mult_assoc_vB);
fun mult1lB_at t       = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB t)] mult_1_left_vB);
fun mult1rB_at t       = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB t)] mult_1_right_vB);
(* left_distrib : oeq (mult x (add m n)) (add (mult x m)(mult x n))   vars x,m,n *)
fun ldistB_at (xt,mt,nt) = beta_norm (Drule.infer_instantiate ctxtB
                            [(("x",0), ctermB xt),(("m",0), ctermB mt),(("n",0), ctermB nt)] left_distrib_vB);
(* right_distrib : oeq (mult (add m n) k)(add (mult m k)(mult n k))   vars m,n,k *)
fun rdistB_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtB
                            [(("m",0), ctermB mt),(("n",0), ctermB nt),(("k",0), ctermB kt)] right_distrib_vB);

(* binom Pascal ground instantiators on ctxtB *)
fun binomN0B_at t       = beta_norm (Drule.infer_instantiate ctxtB [(("n",0), ctermB t)] binom_n_0_vB);
fun binom0SB_at t       = beta_norm (Drule.infer_instantiate ctxtB [(("k",0), ctermB t)] binom_0_Suc_vB);
fun binomSSB_at (nt,kt) = beta_norm (Drule.infer_instantiate ctxtB
                            [(("n",0), ctermB nt),(("k",0), ctermB kt)] binom_Suc_Suc_vB);

(* nat_induct ground instance on ctxtB *)
fun nat_induct_atB (Qabs, kT) = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Qabs), (("k",0), ctermB kT)] nat_induct_vB);

(* ---- oeq trans/sym already top-level (oeq_trans/oeq_sym), Suc_cong too ---- *)

(* ---- congruence helpers on ctxtB (LEFT/RIGHT operand of mult / add) ---- *)
fun mult_cong_lB (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Pabs), (("a",0), ctermB pT), (("b",0), ctermB qT)] oeq_subst_vB);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtB [(("a",0), ctermB (mult pT kT))] oeq_refl_vB);
  in inst OF [hpq, refl_pk] end;
fun mult_cong_rB (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Pabs), (("a",0), ctermB pT), (("b",0), ctermB qT)] oeq_subst_vB);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtB [(("a",0), ctermB (mult hT pT))] oeq_refl_vB);
  in inst OF [hpq, refl_hp] end;
fun add_cong_lB (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Pabs), (("a",0), ctermB pT), (("b",0), ctermB qT)] oeq_subst_vB);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtB [(("a",0), ctermB (add pT kT))] oeq_refl_vB);
  in inst OF [hpq, refl_pk] end;
fun add_cong_rB (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Pabs), (("a",0), ctermB pT), (("b",0), ctermB qT)] oeq_subst_vB);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtB [(("a",0), ctermB (add hT pT))] oeq_refl_vB);
  in inst OF [hpq, refl_hp] end;
(* binom-congruence in the SECOND argument (first arg fixed):
   oeq u v ==> oeq (binom aT u) (binom aT v).  (no capture: binom has no binder.) *)
fun binom_cong_arg2B (aT, uT, vT) huv =
  let
    val Pabs = Abs("z", natT, oeq (binom aT uT) (binom aT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Pabs), (("a",0), ctermB uT), (("b",0), ctermB vT)] oeq_subst_vB);
    val refl_pu = beta_norm (Drule.infer_instantiate ctxtB [(("a",0), ctermB (binom aT uT))] oeq_refl_vB);
  in inst OF [huv, refl_pu] end;

(* ---- exE / disjE / allI / allE elimination helpers on ctxtB ---- *)
fun exE_elimB (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm = Thm.assume (ctermB hypTerm);
    val body = bodyFn wF hypThm;
    val minor = Thm.forall_intr (ctermB wF) (Thm.implies_intr (ctermB hypTerm) body);
    val exE_inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Pabs), (("Q",0), ctermB goalC)] exE_vB);
    val partial = Thm.implies_elim exE_inst exThm;
    val res = Thm.implies_elim partial minor;
  in res end;
fun disjE_elimB (At, Bt, Ct) dThm caseA caseB =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("A",0), ctermB At), (("B",0), ctermB Bt), (("C",0), ctermB Ct)] disjE_vB);
    val s1 = Thm.implies_elim inst dThm;
    val s2 = Thm.implies_elim s1 caseA;
  in Thm.implies_elim s2 caseB end;
(* allI : from (!!x. jT (Pabs x)) get jT (Forall Pabs).
   hAll : a thm of meta-form  !!x. jT (Pabs x)  (already forall_intr'd). *)
fun allI_atB Pabs hAll =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtB [(("P",0), ctermB Pabs)] allI_vB);
  in Thm.implies_elim inst hAll end;
fun allE_atB Pabs at hForall =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Pabs), (("a",0), ctermB at)] allE_vB);
  in Thm.implies_elim inst hForall end;
(* disj_zero_or_suc ground instance on ctxtB : Disj (oeq p Zero) (Ex(%q. oeq p (Suc q))) *)
fun dzosB_at t = beta_norm (Drule.infer_instantiate ctxtB [(("p",0), ctermB t)] disj_zero_or_suc_vB);

val () = out "BINOM_HELPERS_READY\n";

(* ---- uniform 0-hyp + aconv validator on ctxtB ---- *)
fun checkB (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtB (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtB intended ^ "\n");
          false)
  end;

(* schematic Vars for intended statements on ctxtB *)
val nVb = Var (("n",0), natT);
val kVb = Var (("k",0), natT);

(* sanity: the three Pascal axioms are usable (ground-instantiate + check 0-hyp).
   binom_n_0_vB / binom_0_Suc_vB / binom_Suc_Suc_vB are schematic; check them. *)
val i_binom_n_0   = jT (oeq (binom nVb ZeroC) (suc ZeroC));
val i_binom_0_Suc = jT (oeq (binom ZeroC (suc kVb)) ZeroC);
val i_binom_SS    = jT (oeq (binom (suc nVb) (suc kVb))
                            (add (binom nVb kVb) (binom nVb (suc kVb))));
val r_binom_n_0   = checkB ("binom_n_0",     binom_n_0_vB,     i_binom_n_0);
val r_binom_0_Suc = checkB ("binom_0_Suc",   binom_0_Suc_vB,   i_binom_0_Suc);
val r_binom_SS    = checkB ("binom_Suc_Suc", binom_Suc_Suc_vB, i_binom_SS);

(* ============================================================================
   ABSORPTION:  oeq (mult (Suc k)(binom (Suc n)(Suc k))) (mult (Suc n)(binom n k))
   ----------------------------------------------------------------------------
   Induction on n; predicate P n := Forall (%k. <stmt at n,k>), k UNIVERSAL.
   Build the predicate CAPTURE-AVOIDING (Term.lambda over a fresh Free), since the
   body has no binder of the bound var (mult/binom of it are fine), but we use
   Term.lambda for safety / uniformity.
   ============================================================================ *)

(* the per-(n,k) body term (n,k as terms) *)
fun absBody nT kT =
  oeq (mult (suc kT) (binom (suc nT) (suc kT))) (mult (suc nT) (binom nT kT));

val absorption_all =
  let
    (* predicate over n, with k universal inside via object Forall *)
    val zN = Free("zn", natT);
    val kInner = Free("kk", natT);
    val innerAbs0 = Term.lambda kInner (absBody zN kInner);   (* %k. body(zn,k) *)
    val Ppred = Term.lambda zN (mkForall innerAbs0);          (* %n. Forall(%k. body(n,k)) *)
    val nFi = Free("n", natT);
    val ind = nat_induct_atB (Ppred, nFi);

    (* =====================  BASE  n = 0  ===================== *)
    (* show  !!k. oeq (mult (Suc k)(binom (Suc 0)(Suc k))) (mult (Suc 0)(binom 0 k))
       by inner case-split on k (Zero / Suc j). *)
    val baseInnerAbs = Term.lambda kInner (absBody ZeroC kInner);  (* %k. body(0,k) *)
    fun base_body kT =
      let
        (* goal: oeq (mult (Suc k)(binom (Suc 0)(Suc k))) (mult (Suc 0)(binom 0 k)) *)
        val dz = dzosB_at kT;                          (* Disj (oeq k 0)(Ex(%q. oeq k (Suc q))) *)
        val goalC = absBody ZeroC kT;
        (* CASE k = 0 *)
        val caseZ =
          let
            val ez = Thm.assume (ctermB (jT (oeq kT ZeroC)));     (* oeq k 0 *)
            val ezs = oeq_sym OF [ez];                            (* oeq 0 k *)
            (* rewrite the WHOLE goalC body : body(0,0) holds, then substitute 0 -> k.
               Easier: prove body(0,0) directly, then transport via oeq 0 k using subst. *)
            (* body(0,0): oeq (mult (Suc 0)(binom (Suc 0)(Suc 0))) (mult (Suc 0)(binom 0 0)) *)
            (* C(1,1) = C(0,0)+C(0,1) = 1 + 0 = 1 ; LHS = 1*1 = 1 ; RHS = 1*C(0,0)=1*1=1 *)
            val p11   = binomSSB_at (ZeroC, ZeroC);               (* C(1,1) = C(0,0)+C(0,1) *)
            val c00   = binomN0B_at ZeroC;                        (* C(0,0) = 1 *)
            val c01   = binom0SB_at ZeroC;                        (* C(0,1) = 0 *)
            (* C(0,0)+C(0,1) = 1 + 0 = 1 *)
            val s1 = add_cong_lB (binom ZeroC ZeroC, suc ZeroC, binom ZeroC (suc ZeroC)) c00;
                                                                 (* C00+C01 = 1+C01 *)
            val s2 = add_cong_rB (suc ZeroC, binom ZeroC (suc ZeroC), ZeroC) c01;
                                                                 (* 1+C01 = 1+0 *)
            val s3 = add0rB_at (suc ZeroC);                       (* 1+0 = 1 *)
            val sumIs1 = oeq_trans OF [oeq_trans OF [s1, s2], s3];(* C00+C01 = 1 *)
            val c11_is1 = oeq_trans OF [p11, sumIs1];             (* C(1,1) = 1 *)
            (* LHS body(0,0) = mult (Suc 0)(C(1,1)) ; rewrite C(1,1)->1, then 1*1=1 *)
            val lhs1 = mult_cong_rB (suc ZeroC, binom (suc ZeroC)(suc ZeroC), suc ZeroC) c11_is1;
                                                                 (* (1)*C(1,1) = (1)*1 *)
            val lhs2 = mult1rB_at (suc ZeroC);                    (* (1)*1 = 1 *)
            val lhs  = oeq_trans OF [lhs1, lhs2];                 (* (1)*C(1,1) = 1 *)
            (* RHS body(0,0) = mult (Suc 0)(C(0,0)) ; C(0,0)->1, 1*1=1 *)
            val rhs1 = mult_cong_rB (suc ZeroC, binom ZeroC ZeroC, suc ZeroC) c00;
                                                                 (* (1)*C(0,0) = (1)*1 *)
            val rhs2 = mult1rB_at (suc ZeroC);                    (* (1)*1 = 1 *)
            val rhs  = oeq_trans OF [rhs1, rhs2];                 (* (1)*C(0,0) = 1 *)
            val rhss = oeq_sym OF [rhs];                          (* 1 = (1)*C(0,0) *)
            val body00 = oeq_trans OF [lhs, rhss];               (* body(0,0): LHS = RHS *)
            (* transport body(0,0) to body(0,k) by substituting 0 -> k (using oeq 0 k).
               predicate %z. body(0,z), capture-avoiding. *)
            val zP = Free("zp0", natT);
            val Pabs = Term.lambda zP (absBody ZeroC zP);
            val inst = beta_norm (Drule.infer_instantiate ctxtB
                  [(("P",0), ctermB Pabs), (("a",0), ctermB ZeroC), (("b",0), ctermB kT)] oeq_subst_vB);
            val g = inst OF [ezs, body00];                       (* body(0,k) *)
          in Thm.implies_intr (ctermB (jT (oeq kT ZeroC))) g end;
        (* CASE k = Suc j *)
        val caseS =
          let
            val PabsQ = Abs("q", natT, oeq kT (suc (Bound 0)));
            val exq = Thm.assume (ctermB (jT (mkEx PabsQ)));
            fun sbody j (hj : thm) =                              (* hj : oeq k (Suc j) *)
              let
                (* prove body(0, Suc j) then transport Suc j -> k. *)
                (* body(0,Suc j): oeq (mult (Suc(Suc j))(binom (Suc 0)(Suc(Suc j))))
                                       (mult (Suc 0)(binom 0 (Suc j)))
                   C(1, Suc(Suc j)) = C(0, Suc j)+C(0,Suc(Suc j)) = 0+0 = 0 ; LHS = _*0 = 0
                   C(0, Suc j) = 0 ; RHS = (1)*0 = 0 *)
                val pSS  = binomSSB_at (ZeroC, suc j);            (* C(1,Suc(Suc j)) = C(0,Suc j)+C(0,Suc(Suc j)) *)
                val c0a  = binom0SB_at j;                         (* C(0,Suc j) = 0 *)
                val c0b  = binom0SB_at (suc j);                   (* C(0,Suc(Suc j)) = 0 *)
                val a1 = add_cong_lB (binom ZeroC (suc j), ZeroC, binom ZeroC (suc (suc j))) c0a;
                                                                 (* C(0,Sj)+C(0,SSj) = 0+C(0,SSj) *)
                val a2 = add_cong_rB (ZeroC, binom ZeroC (suc (suc j)), ZeroC) c0b;
                                                                 (* 0+C(0,SSj) = 0+0 *)
                val a3 = add0B_at ZeroC;                          (* 0+0 = 0 *)
                val sum0 = oeq_trans OF [oeq_trans OF [a1, a2], a3];   (* C(0,Sj)+C(0,SSj) = 0 *)
                val cBig0 = oeq_trans OF [pSS, sum0];            (* C(1,Suc(Suc j)) = 0 *)
                (* LHS = (Suc(Suc j))*C(1,Suc(Suc j)) -> (Suc(Suc j))*0 -> 0 *)
                val lhs1 = mult_cong_rB (suc (suc j), binom (suc ZeroC) (suc (suc j)), ZeroC) cBig0;
                val lhs2 = mult0rB_at (suc (suc j));             (* (Suc(Suc j))*0 = 0 *)
                val lhs  = oeq_trans OF [lhs1, lhs2];            (* LHS = 0 *)
                (* RHS = (Suc 0)*C(0,Suc j) -> (Suc 0)*0 -> 0 *)
                val rhs1 = mult_cong_rB (suc ZeroC, binom ZeroC (suc j), ZeroC) c0a;
                val rhs2 = mult0rB_at (suc ZeroC);              (* (1)*0 = 0 *)
                val rhs  = oeq_trans OF [rhs1, rhs2];            (* RHS = 0 *)
                val rhss = oeq_sym OF [rhs];                     (* 0 = RHS *)
                val bodySj = oeq_trans OF [lhs, rhss];           (* body(0, Suc j) *)
                (* transport Suc j -> k via oeq (Suc j) k *)
                val hjs = oeq_sym OF [hj];                       (* oeq (Suc j) k *)
                val zP = Free("zp1", natT);
                val Pabs = Term.lambda zP (absBody ZeroC zP);
                val inst = beta_norm (Drule.infer_instantiate ctxtB
                      [(("P",0), ctermB Pabs), (("a",0), ctermB (suc j)), (("b",0), ctermB kT)] oeq_subst_vB);
              in inst OF [hjs, bodySj] end;                      (* body(0,k) *)
            val g = exE_elimB (PabsQ, goalC) exq "qb0" sbody;
          in Thm.implies_intr (ctermB (jT (mkEx PabsQ))) g end;
        val PabsW = Abs("q", natT, oeq kT (suc (Bound 0)));
      in disjE_elimB (oeq kT ZeroC, mkEx PabsW, goalC) dz caseZ caseS end;
    (* assemble BASE = Forall(%k. body(0,k)) via allI over a fresh free *)
    val kB0 = Free("kBase", natT);
    val base_meta = Thm.forall_intr (ctermB kB0) (base_body kB0);
    val base = allI_atB baseInnerAbs base_meta;

    (* =====================  STEP  n = Suc x  ===================== *)
    val xF = Free("x", natT);
    val ihInnerAbs = Term.lambda kInner (absBody xF kInner);     (* %k. body(x,k) *)
    val ihprop = jT (mkForall ihInnerAbs);                       (* Forall(%k. body(x,k)) *)
    val IH = Thm.assume (ctermB ihprop);
    (* goal:  !!k. body(Suc x, k)  ->  Forall(%k. body(Suc x,k)) *)
    val stepInnerAbs = Term.lambda kInner (absBody (suc xF) kInner);

    fun step_body kT =
      let
        (* goal: oeq (mult (Suc k)(binom (Suc(Suc x))(Suc k))) (mult (Suc(Suc x))(binom (Suc x) k)) *)
        val goalC = absBody (suc xF) kT;
        val dz = dzosB_at kT;
        (* helper: IH at a term t : oeq (mult (Suc t)(binom (Suc x)(Suc t))) (mult (Suc x)(binom x t)) *)
        fun IH_at t = allE_atB ihInnerAbs t IH;

        (* CASE k = 0 *)
        val caseZ =
          let
            val ez = Thm.assume (ctermB (jT (oeq kT ZeroC)));    (* oeq k 0 *)
            val ezs = oeq_sym OF [ez];                           (* oeq 0 k *)
            (* prove body(Suc x, 0), then transport 0 -> k.
               body(Suc x,0): oeq (mult (Suc 0)(binom (Suc(Suc x))(Suc 0)))
                                  (mult (Suc(Suc x))(binom (Suc x) 0))
               RHS: C(Suc x,0)=1 -> (Suc(Suc x))*1 = Suc(Suc x)
               LHS: (Suc 0)*C(Suc(Suc x),Suc 0) = C(Suc(Suc x),Suc 0)  [mult_1_left]
                    C(Suc(Suc x),Suc 0) Pascal = C(Suc x,0)+C(Suc x,Suc 0) = 1 + C(Suc x,Suc 0)
                    IH at 0 : (Suc 0)*C(Suc x,Suc 0) = (Suc x)*C(x,0) = (Suc x)*1 = Suc x
                              so C(Suc x,Suc 0) = Suc x  [mult_1_left LHS, mult_1_right RHS]
                    => C(Suc(Suc x),Suc 0) = 1 + Suc x = Suc(Suc x)  [add (Suc 0)(Suc x)] *)
            (* derive cSx1 : C(Suc x, Suc 0) = Suc x  from IH at 0 *)
            val ih0  = IH_at ZeroC;     (* (Suc 0)*C(Suc x,Suc 0) = (Suc x)*C(x,0) *)
            val lhsih = mult1lB_at (binom (suc xF) (suc ZeroC));  (* (Suc 0)*C(Suc x,Suc 0) = C(Suc x,Suc 0) *)
            val lhsihs= oeq_sym OF [lhsih];                      (* C(Suc x,Suc 0) = (Suc 0)*C(Suc x,Suc 0) *)
            val cx0  = binomN0B_at xF;                           (* C(x,0) = 1 *)
            val rih1 = mult_cong_rB (suc xF, binom xF ZeroC, suc ZeroC) cx0;  (* (Suc x)*C(x,0) = (Suc x)*1 *)
            val rih2 = mult1rB_at (suc xF);                      (* (Suc x)*1 = Suc x *)
            val rihC = oeq_trans OF [rih1, rih2];                (* (Suc x)*C(x,0) = Suc x *)
            val cSx1 = oeq_trans OF [oeq_trans OF [lhsihs, ih0], rihC];  (* C(Suc x,Suc 0) = Suc x *)
            (* C(Suc(Suc x),Suc 0) = C(Suc x,0)+C(Suc x,Suc 0) *)
            val pBig = binomSSB_at (suc xF, ZeroC);              (* C(Suc(Suc x),Suc 0) = C(Suc x,0)+C(Suc x,Suc 0) *)
            val cSx0 = binomN0B_at (suc xF);                     (* C(Suc x,0) = 1 *)
            val q1 = add_cong_lB (binom (suc xF) ZeroC, suc ZeroC, binom (suc xF) (suc ZeroC)) cSx0;
                                                                (* C(Sx,0)+C(Sx,S0) = 1 + C(Sx,S0) *)
            val q2 = add_cong_rB (suc ZeroC, binom (suc xF) (suc ZeroC), suc xF) cSx1;
                                                                (* 1 + C(Sx,S0) = 1 + (Suc x) *)
            val q3 = add0B_at (suc xF);                          (* add 0 (Suc x) = Suc x *)
            (* 1 + (Suc x) = add (Suc 0)(Suc x) = Suc(add 0 (Suc x)) = Suc(Suc x) *)
            val q4 = addSucB_at (ZeroC, suc xF);                 (* add (Suc 0)(Suc x) = Suc(add 0 (Suc x)) *)
            val q5 = Suc_cong OF [q3];                           (* Suc(add 0 (Suc x)) = Suc(Suc x) *)
            val q45 = oeq_trans OF [q4, q5];                     (* 1 + (Suc x) = Suc(Suc x) *)
            val cBig = oeq_trans OF [oeq_trans OF [oeq_trans OF [pBig, q1], q2], q45];
                                                                (* C(Suc(Suc x),Suc 0) = Suc(Suc x) *)
            (* LHS body = (Suc 0)*C(Suc(Suc x),Suc 0) -> C(...) [mult_1_left] -> Suc(Suc x) *)
            val l1 = mult1lB_at (binom (suc (suc xF)) (suc ZeroC));  (* (1)*C(SSx,S0) = C(SSx,S0) *)
            val lhs = oeq_trans OF [l1, cBig];                  (* LHS = Suc(Suc x) *)
            (* RHS body = (Suc(Suc x))*C(Suc x,0) -> (Suc(Suc x))*1 -> Suc(Suc x) *)
            val r1 = mult_cong_rB (suc (suc xF), binom (suc xF) ZeroC, suc ZeroC) cSx0;
            val r2 = mult1rB_at (suc (suc xF));                 (* (Suc(Suc x))*1 = Suc(Suc x) *)
            val rhs = oeq_trans OF [r1, r2];                    (* RHS = Suc(Suc x) *)
            val rhss = oeq_sym OF [rhs];                        (* Suc(Suc x) = RHS *)
            val bodyS0 = oeq_trans OF [lhs, rhss];              (* body(Suc x, 0) *)
            (* transport 0 -> k *)
            val zP = Free("zps0", natT);
            val Pabs = Term.lambda zP (absBody (suc xF) zP);
            val inst = beta_norm (Drule.infer_instantiate ctxtB
                  [(("P",0), ctermB Pabs), (("a",0), ctermB ZeroC), (("b",0), ctermB kT)] oeq_subst_vB);
            val g = inst OF [ezs, bodyS0];
          in Thm.implies_intr (ctermB (jT (oeq kT ZeroC))) g end;

        (* CASE k = Suc j *)
        val caseS =
          let
            val PabsQ = Abs("q", natT, oeq kT (suc (Bound 0)));
            val exq = Thm.assume (ctermB (jT (mkEx PabsQ)));
            fun sbody j (hj : thm) =                            (* hj : oeq k (Suc j) *)
              let
                (* prove body(Suc x, Suc j), then transport (Suc j) -> k.
                   body(Suc x, Suc j):
                     oeq (mult (Suc(Suc j))(binom (Suc(Suc x))(Suc(Suc j))))
                         (mult (Suc(Suc x))(binom (Suc x)(Suc j)))
                   Let B = C(Suc x, Suc j), c = C(x, Suc j).
                   Pascal:  C(Suc(Suc x),Suc(Suc j)) = C(Suc x,Suc j) + C(Suc x,Suc(Suc j))
                                                     = B + C(Suc x, Suc(Suc j))
                   IH at (Suc j): (Suc(Suc j))*C(Suc x,Suc(Suc j)) = (Suc x)*c
                   IH at j      : (Suc j)*B = (Suc x)*C(x,j)
                   Pascal:  B = C(x,j) + c                              [pBsmall]
                   target identity (after distrib + IH at Suc j):
                     (Suc(Suc j))*B + (Suc x)*c = (Suc(Suc x))*B
                   proof:
                     (Suc(Suc j))*B = B + (Suc j)*B          [mult_Suc]
                                    = B + (Suc x)*C(x,j)      [IH at j]
                     so LHS' = B + (Suc x)*C(x,j) + (Suc x)*c
                             = B + (Suc x)*(C(x,j)+c)         [left_distrib rev]
                             = B + (Suc x)*B                  [pBsmall rev, cong]
                             = (Suc(Suc x))*B                 [mult_Suc rev]
                *)
                val Bt = binom (suc xF) (suc j);                (* B = C(Suc x, Suc j) *)
                val ct = binom xF (suc j);                      (* c = C(x, Suc j) *)
                val cxj= binom xF j;                            (* C(x,j) *)
                val cBig = binom (suc xF) (suc (suc j));        (* C(Suc x, Suc(Suc j)) *)

                (* LHS of body : (Suc(Suc j))*C(Suc(Suc x),Suc(Suc j)) *)
                val pLHS = binomSSB_at (suc xF, suc j);         (* C(SSx,SSj) = B + cBig *)
                val L1 = mult_cong_rB (suc (suc j), binom (suc (suc xF)) (suc (suc j)), add Bt cBig) pLHS;
                                                               (* (SSj)*C(SSx,SSj) = (SSj)*(B+cBig) *)
                val L2 = ldistB_at (suc (suc j), Bt, cBig);    (* (SSj)*(B+cBig) = (SSj)*B + (SSj)*cBig *)
                val Lchain = oeq_trans OF [L1, L2];            (* LHSbody = (SSj)*B + (SSj)*cBig *)
                (* IH at Suc j : (Suc(Suc j))*cBig = (Suc x)*c *)
                val ihSj = IH_at (suc j);                      (* (SSj)*C(Sx,SSj) = (Sx)*C(x,Sj) ; note SSj = Suc(Suc j), cBig=C(Sx,SSj), c=C(x,Sj) *)
                (* fold (SSj)*cBig -> (Sx)*c inside the sum (right summand) *)
                val L3 = add_cong_rB (mult (suc (suc j)) Bt, mult (suc (suc j)) cBig, mult (suc xF) ct) ihSj;
                                                               (* (SSj)*B + (SSj)*cBig = (SSj)*B + (Sx)*c *)
                val LHSbody = oeq_trans OF [Lchain, L3];       (* LHSbody = (SSj)*B + (Sx)*c *)

                (* now transform (SSj)*B + (Sx)*c  ->  (SSx)*B *)
                (* (SSj)*B = B + (Sj)*B  [mult_Suc with m=Suc j, n=B] *)
                val mS = multSucB_at (suc j, Bt);              (* (Suc(Suc j))*B = add B ((Suc j)*B) *)
                (* IH at j : (Suc j)*B = (Suc x)*C(x,j) *)
                val ihj = IH_at j;                             (* (Sj)*C(Sx,Sj) = (Sx)*C(x,j) ; B=C(Sx,Sj), cxj=C(x,j) *)
                val mS2 = add_cong_rB (Bt, mult (suc j) Bt, mult (suc xF) cxj) ihj;
                                                               (* add B ((Sj)*B) = add B ((Sx)*C(x,j)) *)
                val ssjB = oeq_trans OF [mS, mS2];             (* (SSj)*B = add B ((Sx)*C(x,j)) *)
                (* substitute (SSj)*B -> add B ((Sx)*C(x,j)) inside LHSbody's left summand *)
                val L4 = add_cong_lB (mult (suc (suc j)) Bt, add Bt (mult (suc xF) cxj), mult (suc xF) ct) ssjB;
                                                               (* (SSj)*B + (Sx)*c = (add B ((Sx)*C(x,j))) + (Sx)*c *)
                val cur1 = oeq_trans OF [LHSbody, L4];         (* LHSbody = (B + (Sx)*C(x,j)) + (Sx)*c *)
                (* reassoc: (B + (Sx)C(x,j)) + (Sx)c = B + ((Sx)C(x,j) + (Sx)c) *)
                val asc = addassocB_at (Bt, mult (suc xF) cxj, mult (suc xF) ct);
                                                               (* (B + A1) + A2 = B + (A1 + A2) *)
                val cur2 = oeq_trans OF [cur1, asc];           (* LHSbody = B + ((Sx)C(x,j) + (Sx)c) *)
                (* (Sx)*C(x,j) + (Sx)*c = (Sx)*(C(x,j)+c)  [left_distrib reversed] *)
                val ld = ldistB_at (suc xF, cxj, ct);          (* (Sx)*(C(x,j)+c) = (Sx)*C(x,j) + (Sx)*c *)
                val lds= oeq_sym OF [ld];                      (* (Sx)*C(x,j)+(Sx)*c = (Sx)*(C(x,j)+c) *)
                val cur3in = add_cong_rB (Bt, add (mult (suc xF) cxj) (mult (suc xF) ct), mult (suc xF) (add cxj ct)) lds;
                                                               (* B + ((Sx)C(x,j)+(Sx)c) = B + (Sx)*(C(x,j)+c) *)
                val cur3 = oeq_trans OF [cur2, cur3in];        (* LHSbody = B + (Sx)*(C(x,j)+c) *)
                (* Pascal small: B = C(x,j) + c   so  (C(x,j)+c) = B  (sym) *)
                val pBsmall = binomSSB_at (xF, j);             (* C(Sx,Sj) = C(x,j)+C(x,Sj) i.e. B = C(x,j)+c *)
                val pBsmalls = oeq_sym OF [pBsmall];           (* C(x,j)+c = B *)
                val foldB = mult_cong_rB (suc xF, add cxj ct, Bt) pBsmalls;
                                                               (* (Sx)*(C(x,j)+c) = (Sx)*B *)
                val cur4in = add_cong_rB (Bt, mult (suc xF) (add cxj ct), mult (suc xF) Bt) foldB;
                                                               (* B + (Sx)*(C(x,j)+c) = B + (Sx)*B *)
                val cur4 = oeq_trans OF [cur3, cur4in];        (* LHSbody = B + (Sx)*B *)
                (* B + (Sx)*B = (Suc(Suc x))*B  [mult_Suc with m=Suc x, n=B, reversed] *)
                val mSx = multSucB_at (suc xF, Bt);            (* (Suc(Suc x))*B = add B ((Sx)*B) *)
                val mSxs= oeq_sym OF [mSx];                    (* add B ((Sx)*B) = (Suc(Suc x))*B *)
                val cur5 = oeq_trans OF [cur4, mSxs];          (* LHSbody = (Suc(Suc x))*B *)
                (* cur5 : oeq (LHSbody-expr) ((Suc(Suc x))*B).  But LHSbody-expr is the
                   ORIGINAL LHS of body (mult (Suc(Suc j))(binom (Suc(Suc x))(Suc(Suc j)))).
                   The body's RHS is (mult (Suc(Suc x))(binom (Suc x)(Suc j))) = (SSx)*B.
                   So cur5 IS exactly body(Suc x, Suc j). *)
                val bodySj = cur5;
                (* transport (Suc j) -> k via oeq (Suc j) k *)
                val hjs = oeq_sym OF [hj];                     (* oeq (Suc j) k *)
                val zP = Free("zps1", natT);
                val Pabs = Term.lambda zP (absBody (suc xF) zP);
                val inst = beta_norm (Drule.infer_instantiate ctxtB
                      [(("P",0), ctermB Pabs), (("a",0), ctermB (suc j)), (("b",0), ctermB kT)] oeq_subst_vB);
              in inst OF [hjs, bodySj] end;
            val g = exE_elimB (PabsQ, goalC) exq "qbs" sbody;
          in Thm.implies_intr (ctermB (jT (mkEx PabsQ))) g end;

        val PabsW = Abs("q", natT, oeq kT (suc (Bound 0)));
      in disjE_elimB (oeq kT ZeroC, mkEx PabsW, goalC) dz caseZ caseS end;

    (* assemble STEP: from (!!k. body(Suc x,k)) get Forall(%k. body(Suc x,k)),
       then discharge IH and forall_intr x. *)
    val kS0 = Free("kStep", natT);
    val step_meta = Thm.forall_intr (ctermB kS0) (step_body kS0);
    val stepForall = allI_atB stepInnerAbs step_meta;            (* Forall(%k. body(Suc x,k)) *)
    val step1 = Thm.forall_intr (ctermB xF) (Thm.implies_intr (ctermB ihprop) stepForall);

    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;                         (* Forall(%k. body(n,k)) with n Free *)
  in r2 end;

(* absorption_all : Forall(%k. body(n,k))  with n FREE.
   Specialize to a free k, then varify -> both n,k schematic. *)
val absorption =
  let
    val nF = Free("n", natT);
    val kF = Free("k", natT);
    (* absorption_all has n Free; allE at kF gives body(n,k) *)
    val innerAbsN = Term.lambda (Free("kk", natT)) (absBody nF (Free("kk", natT)));
    val spec = allE_atB innerAbsN kF absorption_all;            (* body(n,k) at free n,k *)
  in varify spec end;

val absorption_intended = jT (absBody nVb kVb);
val r_absorption = checkB ("absorption", absorption, absorption_intended);

(* soundness probe: absorption must be NONTRIVIAL (not provable as reflexivity-collapse).
   Confirm the two sides differ syntactically. *)
val b_absorption_nontrivial =
  let val (lhs, rhs) =
        (mult (suc kVb) (binom (suc nVb) (suc kVb)), mult (suc nVb) (binom nVb kVb))
  in not (lhs aconv rhs) end;

val () =
  if r_absorption andalso b_absorption_nontrivial
  then out "ABSORPTION_PROBE_OK nontrivial\n"
  else out "ABSORPTION_PROBE_FAIL\n";

(* ============================================================================
   STAGE B FINAL VALIDATION
   ============================================================================ *)
val () =
  if r_binom_n_0 andalso r_binom_0_Suc andalso r_binom_SS
     andalso r_absorption andalso b_absorption_nontrivial
  then out "BINOM_FOUNDATION_OK\n"
  else out "BINOM_FOUNDATION_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  STAGE B PHASE 2 : p | C(p,k)  for  0 < k < p  ***
   ----------------------------------------------------------------------------
   TARGET p_dvd_binom :
     jT (prime2 p) ==> jT (lt Zero k) ==> jT (lt k p) ==> jT (dvd p (binom p k))
   Everything routed through ctxtB / ctermB (theory thyB with binom).
   ============================================================================ *)

val () = out "PDVD_BEGIN\n";

(* ---- re-varify the order / divisibility / euclid lemmas onto ctxtB ---- *)
val le_trans_vB    = varify le_trans;
val lt_irrefl_vB   = varify lt_irrefl;
val lt_trans_vB    = varify lt_trans;
val lt_suc_vB      = varify lt_suc;
val dvd_le_vB      = varify dvd_le;
val euclid_lemma_vB= varify euclid_lemma;
val conjunct1_vB   = varify conjunct1_ax;
val oFalse_elim_vB = varify oFalse_elim_ax;

(* oFalse_elim on ctxtB at explicit R *)
fun oFalse_elimB_at rT = beta_norm (Drule.infer_instantiate ctxtB
      [(("R",0), ctermB rT)] oFalse_elim_vB);

(* lt_suc on ctxtB : lt n (Suc n) *)
fun lt_suc_atB nt = beta_norm (Drule.infer_instantiate ctxtB
      [(("n",0), ctermB nt)] lt_suc_vB);

(* lt_trans on ctxtB : lt a b -> lt b c -> lt a c *)
fun lt_trans_atB (at, bt, ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB
        [(("a",0), ctermB at), (("b",0), ctermB bt), (("c",0), ctermB ct)] lt_trans_vB)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* le_trans on ctxtB : le m n -> le n k -> le m k *)
fun le_trans_atB (mt, nt, kt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB
        [(("m",0), ctermB mt), (("n",0), ctermB nt), (("k",0), ctermB kt)] le_trans_vB)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* lt_irrefl on ctxtB : lt n n -> oFalse *)
fun lt_irrefl_atB nt h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB
        [(("n",0), ctermB nt)] lt_irrefl_vB)
  in Thm.implies_elim inst h end;

(* dvd_le on ctxtB : dvd d n -> (oeq n Zero ==> oFalse) -> le d n.
   2nd premise is a META implication; discharge with implies_elim of the meta-thm. *)
fun dvd_le_atB (dt, nt) hdvd hnzMeta =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB
        [(("d",0), ctermB dt), (("n",0), ctermB nt)] dvd_le_vB)
  in Thm.implies_elim (Thm.implies_elim inst hdvd) hnzMeta end;

(* euclid_lemma on ctxtB : prime2 p -> dvd p (mult a b) -> Disj (dvd p a)(dvd p b) *)
fun euclid_atB (pt, at, bt) hprime hdvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB
        [(("p",0), ctermB pt), (("a",0), ctermB at), (("b",0), ctermB bt)] euclid_lemma_vB)
  in Thm.implies_elim (Thm.implies_elim inst hprime) hdvd end;

(* conjunct1 on ctxtB : Conj A B -> A *)
fun conjunct1_atB (At, Bt) hConj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB
        [(("A",0), ctermB At), (("B",0), ctermB Bt)] conjunct1_vB)
  in Thm.implies_elim inst hConj end;

(* dvd_intro on ctxtB : from oeq b (mult a w) get jT (dvd a b), witness w. *)
fun dvd_introB (aT, bT, w) hyp =
  let
    val Pabs = Abs ("k", natT, oeq bT (mult aT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtB
          [(("P",0), ctermB Pabs), (("a",0), ctermB w)] exI_vB);
  in inst OF [hyp] end;

(* generic substitution into a predicate on ctxtB :
   substPredB (Pabs, aT, bT) hab hPa : jT (Pabs bT)  from  oeq aT bT  and  jT (Pabs aT). *)
fun substPredB (Pabs, aT, bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtB
        [(("P",0), ctermB Pabs), (("a",0), ctermB aT), (("b",0), ctermB bT)] oeq_subst_vB)
  in inst OF [hab, hPa] end;

val () = out "PDVD_HELPERS_READY\n";

(* ============================================================================
   p_dvd_binom
   ============================================================================ *)
val p_dvd_binom =
  let
    val pF = Free("p", natT);
    val kF = Free("k", natT);
    val primeP = jT (prime2 pF);          (* prime2 p *)
    val ltZkP  = jT (lt ZeroC kF);        (* 0 < k     i.e. le (Suc 0) k *)
    val ltkpP  = jT (lt kF pF);           (* k < p     i.e. le (Suc k) p *)
    val hPrime = Thm.assume (ctermB primeP);
    val h0k    = Thm.assume (ctermB ltZkP);
    val hkp    = Thm.assume (ctermB ltkpP);

    val goalBody = dvd pF (binom pF kF);

    (* ---- k != 0  meta-fact : (oeq k Zero ==> oFalse) ---------------------
       from lt Zero k = le (Suc 0) k : if oeq k Zero, transport into the
       2nd arg of le (Suc 0) (.) giving le (Suc 0) Zero = lt Zero Zero,
       then lt_irrefl. *)
    val k_ne_0_meta =
      let
        val ekz = Thm.assume (ctermB (jT (oeq kF ZeroC)));    (* oeq k 0 *)
        (* predicate %z. lt Zero z = le (Suc 0) z, capture-avoiding *)
        val zF   = Free("zk", natT);
        val Pabs = Term.lambda zF (lt ZeroC zF);
        (* h0k : jT (Pabs k);  transport k -> 0 gives jT (Pabs 0) = lt 0 0 *)
        val lt00 = substPredB (Pabs, kF, ZeroC) ekz h0k;      (* jT (lt Zero Zero) *)
        val fls  = lt_irrefl_atB ZeroC lt00;                  (* oFalse *)
      in Thm.implies_intr (ctermB (jT (oeq kF ZeroC))) fls end;

    (* ---- p != 0  meta-fact : (oeq p Zero ==> oFalse) ---------------------
       not strictly needed below (we never call dvd_le on p directly), but
       keep p positive available; derive from prime2 p => lt 1 p => 0<p. *)

    (* ---- absorption at (n := p, k := k0) where k = Suc k0 ----------------
       absorption (schematic) : oeq (mult (Suc K)(binom (Suc N)(Suc K)))
                                    (mult (Suc N)(binom N K))
       We need an instance with Suc K = k and Suc N = p, so we case k and p
       into Suc-form, instantiate absorption at (N:=p0, K:=k0), then rewrite
       Suc k0 -> k and Suc p0 -> p.

       absorption is varified with vars n,k (per absorption_intended: nVb,kVb).
       Instantiate :  n := p0,  k := k0. *)
    fun absorption_at (n0t, k0t) =
      beta_norm (Drule.infer_instantiate ctxtB
        [(("n",0), ctermB n0t), (("k",0), ctermB k0t)] absorption);

    (* core: given p = Suc p0 (via hp_eq : oeq p (Suc p0)) and
                    k = Suc k0 (via hk_eq : oeq k (Suc k0)),
       produce  jT (dvd p (binom p k)). *)
    fun core (p0t, hp_eq) (k0t, hk_eq) =
      let
        (* absorption instance:
             A : oeq (mult (Suc k0)(binom (Suc p0)(Suc k0)))
                     (mult (Suc p0)(binom p0 k0))                         *)
        val A0 = absorption_at (p0t, k0t);
        (* rewrite (Suc k0) -> k and (Suc p0) -> p inside A0 to get
             A : oeq (mult k (binom p k)) (mult p (binom p0 k0))          *)
        (* step 1: replace Suc p0 by p.  predicate over the Suc-p0 occurrences:
             %z. oeq (mult (Suc k0)(binom z (Suc k0))) (mult z (binom p0 k0)) *)
        val hpsym = oeq_sym OF [hp_eq];     (* oeq (Suc p0) p *)
        val hksym = oeq_sym OF [hk_eq];     (* oeq (Suc k0) k *)
        val zP1   = Free("zP1", natT);
        val P1abs = Term.lambda zP1
              (oeq (mult (suc k0t) (binom zP1 (suc k0t)))
                   (mult zP1 (binom p0t k0t)));
        val A1 = substPredB (P1abs, suc p0t, pF) hpsym A0;
        (* A1 : oeq (mult (Suc k0)(binom p (Suc k0))) (mult p (binom p0 k0)) *)
        (* step 2: replace Suc k0 by k.  predicate:
             %z. oeq (mult z (binom p z)) (mult p (binom p0 k0)) *)
        val zP2   = Free("zP2", natT);
        val P2abs = Term.lambda zP2
              (oeq (mult zP2 (binom pF zP2))
                   (mult pF (binom p0t k0t)));
        val A2 = substPredB (P2abs, suc k0t, kF) hksym A1;
        (* A2 : oeq (mult k (binom p k)) (mult p (binom p0 k0))            *)

        (* So  mult k (binom p k) = mult p (binom p0 k0) = p * (witness).
           => dvd p (mult k (binom p k))   with witness (binom p0 k0). *)
        val dvd_p_mkbpk = dvd_introB (pF, mult kF (binom pF kF), binom p0t k0t) A2;
        (* dvd_p_mkbpk : jT (dvd p (mult k (binom p k))) *)

        (* euclid_lemma (prime2 p)(dvd p (mult k (binom p k)))
             => Disj (dvd p k) (dvd p (binom p k)) *)
        val disjD = euclid_atB (pF, kF, binom pF kF) hPrime dvd_p_mkbpk;

        (* disjE : case dvd p k -> IMPOSSIBLE ; case dvd p (binom p k) -> goal *)
        val caseA =   (* dvd p k  ->  goalBody *)
          let
            val hdpk = Thm.assume (ctermB (jT (dvd pF kF)));   (* dvd p k *)
            (* dvd p k + k != 0  => le p k  (dvd_le) *)
            val le_p_k = dvd_le_atB (pF, kF) hdpk k_ne_0_meta; (* le p k *)
            (* lt k p = le (Suc k) p ; le (Suc k) p + le p k => le (Suc k) k = lt k k *)
            val le_Sk_k = le_trans_atB (suc kF, pF, kF) hkp le_p_k;  (* le (Suc k) k = lt k k *)
            (* lt k k = le (Suc k) k ; lt_irrefl => oFalse *)
            val fls = lt_irrefl_atB kF le_Sk_k;                (* oFalse *)
            (* oFalse => goalBody *)
            val g   = (oFalse_elimB_at goalBody) OF [fls];
          in Thm.implies_intr (ctermB (jT (dvd pF kF))) g end;
        val caseB =   (* dvd p (binom p k) -> goalBody (identity) *)
          let
            val hdpb = Thm.assume (ctermB (jT goalBody));
          in Thm.implies_intr (ctermB (jT goalBody)) hdpb end;
        val concl = disjE_elimB (dvd pF kF, goalBody, goalBody) disjD caseA caseB;
      in concl end;

    (* ---- obtain p = Suc p0 (from prime2 p => lt 1 p => p != 0) ----------
       prime2 p = Conj (lt (Suc 0) p) (Forall ...).  conjunct1 -> lt (Suc 0) p
         = le (Suc(Suc 0)) p.  Case p via dzosB_at p; Zero case contradiction. *)
    val lt1p = conjunct1_atB (lt (suc ZeroC) pF, mkForall (ppAbs pF)) hPrime;  (* lt (Suc 0) p *)
    (* p != 0 meta : if oeq p Zero, transport into 2nd arg of le (Suc(Suc 0)) (.)
       -> le (Suc(Suc 0)) Zero = lt (Suc 0) Zero, then... easier: transport
       lt (Suc 0) p to lt (Suc 0) Zero, which is le (Suc(Suc 0)) Zero.
       That alone isn't lt_irrefl-shaped; instead show lt 0 p first then case p. *)

    (* Build the proof by casing p then k. *)
    val dzP = dzosB_at pF;     (* Disj (oeq p Zero) (Ex(%q. oeq p (Suc q))) *)
    val dzK = dzosB_at kF;     (* Disj (oeq k Zero) (Ex(%q. oeq k (Suc q))) *)

    (* For p : Zero case impossible (from lt (Suc 0) p), Suc case -> proceed. *)
    val PpW = Abs("q", natT, oeq pF (suc (Bound 0)));
    val PkW = Abs("q", natT, oeq kF (suc (Bound 0)));

    (* the body once we know p = Suc p0 : case k *)
    fun afterP (p0t, hp_eq) =
      let
        (* case k : Zero impossible (k_ne_0_meta), Suc -> core *)
        val caseKZero =
          let
            val ekz = Thm.assume (ctermB (jT (oeq kF ZeroC)));
            val fls = Thm.implies_elim k_ne_0_meta ekz;       (* oFalse *)
            val g   = (oFalse_elimB_at goalBody) OF [fls];
          in Thm.implies_intr (ctermB (jT (oeq kF ZeroC))) g end;
        val caseKSuc =
          let
            val exk = Thm.assume (ctermB (jT (mkEx PkW)));
            fun kbody k0v (hk0 : thm) =                        (* hk0 : oeq k (Suc k0v) *)
                  core (p0t, hp_eq) (k0v, hk0);
            val g = exE_elimB (PkW, goalBody) exk "k0w" kbody;
          in Thm.implies_intr (ctermB (jT (mkEx PkW))) g end;
      in disjE_elimB (oeq kF ZeroC, mkEx PkW, goalBody) dzK caseKZero caseKSuc end;

    val casePZero =
      let
        (* oeq p Zero ; from lt (Suc 0) p = le (Suc(Suc 0)) p transport to
           le (Suc(Suc 0)) Zero ; that's lt (Suc 0) Zero ; then derive oFalse
           via lt_irrefl?  No: lt (Suc 0) Zero is le (Suc(Suc 0)) Zero, not
           an n<n shape.  Instead: 0 < p (i.e. lt 0 p) holds from lt (Suc 0) p
           by transitivity? simpler: transport lt 0 k won't help for p.
           Use: lt (Suc 0) p ; transport p->0 : lt (Suc 0) 0 = le (Suc(Suc 0)) 0.
           Then lt_trans / lt_irrefl?  Cleanest: lt (Suc 0) Zero contradicts
           via the same trick used for k_ne_0: we need an n<n.  Build it:
             lt (Suc 0) Zero  AND  Zero <= Suc 0  ... messy.
           SIMPLEST robust route: transport lt(Suc 0) p to lt(Suc 0) Zero,
           then note Zero < Suc 0 (lt_suc at... ) and lt_trans gives
           lt (Suc 0)(Suc 0) = lt_irrefl. *)
        val epz = Thm.assume (ctermB (jT (oeq pF ZeroC)));    (* oeq p Zero *)
        val zF   = Free("zp", natT);
        val Pabs = Term.lambda zF (lt (suc ZeroC) zF);        (* %z. lt (Suc 0) z *)
        val lt1_0 = substPredB (Pabs, pF, ZeroC) epz lt1p;    (* lt (Suc 0) Zero *)
        (* Zero < Suc 0 : lt Zero (Suc Zero) = le (Suc Zero)(Suc Zero) ;
           use lt_suc on ctxtB? lt_suc : lt n (Suc n).  varify + inst at n:=0. *)
        val lt0_S0 = lt_suc_atB ZeroC;                        (* lt Zero (Suc Zero) *)
        (* lt_trans : lt 0 (Suc 0) -> lt (Suc 0) 0 -> lt 0 0 *)
        val lt00 = lt_trans_atB (ZeroC, suc ZeroC, ZeroC) lt0_S0 lt1_0;  (* lt 0 0 *)
        val fls  = lt_irrefl_atB ZeroC lt00;
        val g    = (oFalse_elimB_at goalBody) OF [fls];
      in Thm.implies_intr (ctermB (jT (oeq pF ZeroC))) g end;
    val casePSuc =
      let
        val exp = Thm.assume (ctermB (jT (mkEx PpW)));
        fun pbody p0v (hp0 : thm) = afterP (p0v, hp0);        (* hp0 : oeq p (Suc p0v) *)
        val g = exE_elimB (PpW, goalBody) exp "p0w" pbody;
      in Thm.implies_intr (ctermB (jT (mkEx PpW))) g end;

    val concl0 = disjE_elimB (oeq pF ZeroC, mkEx PpW, goalBody) dzP casePZero casePSuc;
    (* concl0 : jT (dvd p (binom p k))  under hyps primeP, ltZkP, ltkpP.
       discharge in reverse: ltkp, lt0k, prime. *)
    val d1 = Thm.implies_intr (ctermB ltkpP) concl0;
    val d2 = Thm.implies_intr (ctermB ltZkP) d1;
    val d3 = Thm.implies_intr (ctermB primeP) d2;
  in varify d3 end;

(* intended statement, schematic on ctxtB *)
val pVb = Var (("p",0), natT);
val kVb2 = Var (("k",0), natT);
val p_dvd_binom_intended =
  Logic.mk_implies (jT (prime2 pVb),
    Logic.mk_implies (jT (lt ZeroC kVb2),
      Logic.mk_implies (jT (lt kVb2 pVb),
        jT (dvd pVb (binom pVb kVb2)))));

val r_p_dvd_binom = checkB ("p_dvd_binom", p_dvd_binom, p_dvd_binom_intended);

(* ---- soundness probe : the kernel must REJECT the false variant that drops
   lt k p.  We do NOT try to PROVE it; we only confirm our proved theorem
   STILL carries the lt k p premise (i.e. it did not collapse to the weaker,
   false statement p | C(p,k) for all 0<k).  p | C(p,p)=1 is false. *)
val false_variant =
  Logic.mk_implies (jT (prime2 pVb),
    Logic.mk_implies (jT (lt ZeroC kVb2),
      jT (dvd pVb (binom pVb kVb2))));
val b_needs_ltkp = not ((Thm.prop_of p_dvd_binom) aconv false_variant);

val () =
  if r_p_dvd_binom andalso b_needs_ltkp
  then out "P_DVD_BINOM_SOUNDPROBE_OK\n"
  else out "P_DVD_BINOM_SOUNDPROBE_FAIL\n";

val () =
  if r_p_dvd_binom andalso b_needs_ltkp
  then out "P_DVD_BINOM_DONE\n"
  else out "P_DVD_BINOM_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  STAGE C1 : TRUNCATED SUBTRACTION (sub) + SUMMATION (sumf)  ***
   ----------------------------------------------------------------------------
   Extend thyB with BOTH new consts in ONE Sign.add_consts:
     sub  : nat=>nat=>nat
     sumf : (nat=>nat)=>nat=>nat      [HIGHER-ORDER: first arg is a function]
   Final context ctxtSub / ctermSub ; check helper checkSub ; route ALL cterms
   through ctermSub.
   ============================================================================ *)

val () = out "SUMSUB_BEGIN\n";

val fnT = natT --> natT;

(* ---- ONE theory extension with BOTH consts ---- *)
val thySub0 = Sign.add_consts
  [(Binding.name "sub",  natT --> natT --> natT, NoSyn),
   (Binding.name "sumf", fnT --> natT --> natT,  NoSyn)] thyB;
val subC  = Const (Sign.full_name thySub0 (Binding.name "sub"),  natT --> natT --> natT);
fun sub s t = subC $ s $ t;
val sumfC = Const (Sign.full_name thySub0 (Binding.name "sumf"), fnT --> natT --> natT);
fun sumf f n = sumfC $ f $ n;

(* ---- axioms ---- *)
val nSu = Free("n", natT); val kSu = Free("k", natT);
val ((_,sub_n_0_ax),    thySub1) = Thm.add_axiom_global (Binding.name "sub_n_0",
      jT (oeq (sub nSu ZeroC) nSu)) thySub0;
val ((_,sub_0_Suc_ax),  thySub2) = Thm.add_axiom_global (Binding.name "sub_0_Suc",
      jT (oeq (sub ZeroC (suc kSu)) ZeroC)) thySub1;
val ((_,sub_Suc_Suc_ax),thySub3) = Thm.add_axiom_global (Binding.name "sub_Suc_Suc",
      jT (oeq (sub (suc nSu) (suc kSu)) (sub nSu kSu))) thySub2;

val fSu = Free("f", fnT);
val ((_,sumf_0_ax),   thySub4) = Thm.add_axiom_global (Binding.name "sumf_0",
      jT (oeq (sumf fSu ZeroC) (fSu $ ZeroC))) thySub3;
val ((_,sumf_Suc_ax), thySub)  = Thm.add_axiom_global (Binding.name "sumf_Suc",
      jT (oeq (sumf fSu (suc nSu)) (add (sumf fSu nSu) (fSu $ (suc nSu))))) thySub4;

(* ---- THE ONE FINAL CONTEXT ctxtSub / ctermSub ---- *)
val ctxtSub  = Proof_Context.init_global thySub;
val ctermSub = Thm.cterm_of ctxtSub;

(* ---- re-varify every reused axiom/lemma onto ctxtSub ---- *)
val oeq_refl_vS2     = varify oeq_refl;
val oeq_subst_vS2    = varify oeq_subst;
val nat_induct_vS2   = varify nat_induct;
val add_0_vS2        = varify add_0;
val add_Suc_vS2      = varify add_Suc;
val add_0_right_vS2  = varify add_0_right;
val add_Suc_right_vS2= varify add_Suc_right;
val exI_vS2          = varify exI_ax;
val exE_vS2          = varify exE_ax;
val le_refl_vS2      = varify le_refl;
val le_trans_vS2     = varify le_trans;
val impI_vS2         = varify impI_ax;
val mp_vS2           = varify mp_ax;
val allI_vS2         = varify allI_ax;
val allE_vS2         = varify allE_ax;

val sub_n_0_vS2      = varify sub_n_0_ax;
val sub_0_Suc_vS2    = varify sub_0_Suc_ax;
val sub_Suc_Suc_vS2  = varify sub_Suc_Suc_ax;
val sumf_0_vS2       = varify sumf_0_ax;
val sumf_Suc_vS2     = varify sumf_Suc_ax;

(* ---- ground instantiators on ctxtSub ---- *)
fun oeqreflS2_at t   = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub t)] oeq_refl_vS2);
fun add0S2_at t      = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] add_0_vS2);
fun addSucS2_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSub
                            [(("m",0), ctermSub mt),(("n",0), ctermSub nt)] add_Suc_vS2);
fun add0rS2_at t     = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] add_0_right_vS2);
fun addSrS2_at (mt,nt)= beta_norm (Drule.infer_instantiate ctxtSub
                            [(("m",0), ctermSub mt),(("n",0), ctermSub nt)] add_Suc_right_vS2);

fun subN0S2_at t        = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] sub_n_0_vS2);
fun sub0SS2_at t        = beta_norm (Drule.infer_instantiate ctxtSub [(("k",0), ctermSub t)] sub_0_Suc_vS2);
fun subSSS2_at (nt,kt)  = beta_norm (Drule.infer_instantiate ctxtSub
                            [(("n",0), ctermSub nt),(("k",0), ctermSub kt)] sub_Suc_Suc_vS2);

fun nat_induct_atS2 (Qabs, kT) = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Qabs), (("k",0), ctermSub kT)] nat_induct_vS2);

(* congruence helpers on ctxtSub : left/right operand of add *)
fun add_cong_lS2 (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("a",0), ctermSub pT), (("b",0), ctermSub qT)] oeq_subst_vS2);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub (add pT kT))] oeq_refl_vS2);
  in inst OF [hpq, refl_pk] end;
fun add_cong_rS2 (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("a",0), ctermSub pT), (("b",0), ctermSub qT)] oeq_subst_vS2);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub (add hT pT))] oeq_refl_vS2);
  in inst OF [hpq, refl_hp] end;

(* generic substitution into a predicate on ctxtSub *)
fun substPredS2 (Pabs, aT, bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("P",0), ctermSub Pabs), (("a",0), ctermSub aT), (("b",0), ctermSub bT)] oeq_subst_vS2)
  in inst OF [hab, hPa] end;

(* exE elimination helper on ctxtSub *)
fun exE_elimS2 (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm = Thm.assume (ctermSub hypTerm);
    val body = bodyFn wF hypThm;
    val minor = Thm.forall_intr (ctermSub wF) (Thm.implies_intr (ctermSub hypTerm) body);
    val exE_inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("Q",0), ctermSub goalC)] exE_vS2);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;

(* le_intro on ctxtSub : from oeq nT (add mT w) get jT (le mT nT) *)
fun le_introS2 (mT, nT, w) hyp =
  let
    val Pabs = Abs ("p", natT, oeq nT (add mT (Bound 0)));
    val exI_inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("a",0), ctermSub w)] exI_vS2);
  in exI_inst OF [hyp] end;

fun le_reflS2_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] le_refl_vS2);
fun le_transS2_at (mt, nt, kt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt), (("n",0), ctermSub nt), (("k",0), ctermSub kt)] le_trans_vS2)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* le_suc_self on ctxtSub : le b (Suc b).  witness Suc 0 :  Suc b = b + Suc 0. *)
fun le_suc_selfS2_at bT =
  let
    val asr  = addSrS2_at (bT, ZeroC);            (* oeq (add b (Suc 0)) (Suc (add b 0)) *)
    val a0r  = add0rS2_at bT;                     (* oeq (add b 0) b *)
    val a0rS = Suc_cong OF [a0r];                 (* oeq (Suc (add b 0)) (Suc b) *)
    val chain = oeq_trans OF [asr, a0rS];         (* oeq (add b (Suc 0)) (Suc b) *)
    val chainSym = oeq_sym OF [chain];            (* oeq (Suc b) (add b (Suc 0)) *)
  in le_introS2 (bT, suc bT, suc ZeroC) chainSym end;

(* object Imp / Forall helpers on ctxtSub *)
fun impI_S2 (At, Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("A",0), ctermSub At), (("B",0), ctermSub Bt)] impI_vS2)
  in Thm.implies_elim inst hImpThm end;
fun mp_S2 (At, Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("A",0), ctermSub At), (("B",0), ctermSub Bt)] mp_vS2)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun allI_S2 Pabs hAll =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("P",0), ctermSub Pabs)] allI_vS2)
  in Thm.implies_elim inst hAll end;
fun allE_S2 Pabs at hForall =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("P",0), ctermSub Pabs), (("a",0), ctermSub at)] allE_vS2)
  in Thm.implies_elim inst hForall end;

val () = out "SUMSUB_HELPERS_READY\n";

(* ---- uniform 0-hyp + aconv validator on ctxtSub ---- *)
fun checkSub (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtSub (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtSub intended ^ "\n");
          false)
  end;

(* schematic Vars for intended statements on ctxtSub *)
val nVs = Var (("n",0), natT);
val kVs = Var (("k",0), natT);
val jVs = Var (("j",0), natT);
val pVs = Var (("p",0), natT);
val fVs = Var (("f",0), fnT);
val gVs = Var (("g",0), fnT);

(* sanity: the 5 axioms are usable -> ground-schematic + 0-hyp check via checkSub *)
val i_sub_n_0   = jT (oeq (sub nVs ZeroC) nVs);
val i_sub_0_Suc = jT (oeq (sub ZeroC (suc kVs)) ZeroC);
val i_sub_SS    = jT (oeq (sub (suc nVs) (suc kVs)) (sub nVs kVs));
val r_sub_n_0_ax   = checkSub ("sub_n_0_ax",    sub_n_0_vS2,     i_sub_n_0);
val r_sub_0_Suc_ax = checkSub ("sub_0_Suc_ax",  sub_0_Suc_vS2,   i_sub_0_Suc);
val r_sub_SS_ax    = checkSub ("sub_Suc_Suc_ax",sub_Suc_Suc_vS2, i_sub_SS);
val i_sumf_0   = jT (oeq (sumf fVs ZeroC) (fVs $ ZeroC));
val i_sumf_Suc = jT (oeq (sumf fVs (suc nVs)) (add (sumf fVs nVs) (fVs $ (suc nVs))));
val r_sumf_0_ax   = checkSub ("sumf_0_ax",   sumf_0_vS2,   i_sumf_0);
val r_sumf_Suc_ax = checkSub ("sumf_Suc_ax", sumf_Suc_vS2, i_sumf_Suc);

(* ============================================================================
   1.  sub_self : oeq (sub n n) Zero      (induction on n)
   ============================================================================ *)
val sub_self =
  let
    val Qpred = Abs("z", natT, oeq (sub (Bound 0) (Bound 0)) ZeroC);
    val nF = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nF);
    val base = subN0S2_at ZeroC;                  (* oeq (sub 0 0) 0 *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (sub xF xF) ZeroC);
    val IH = Thm.assume (ctermSub ihprop);
    val ss = subSSS2_at (xF, xF);                 (* oeq (sub (Suc x)(Suc x)) (sub x x) *)
    val stepconcl = oeq_trans OF [ss, IH];
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_sub_self = jT (oeq (sub nVs nVs) ZeroC);
val r_sub_self = checkSub ("sub_self", sub_self, i_sub_self);

(* ============================================================================
   2.  sub_add_l : oeq (sub (add k j) k) j     (induction on k ; j free)
   ============================================================================ *)
val sub_add_l =
  let
    val jF = Free("j", natT);
    val Qpred = Abs("z", natT, oeq (sub (add (Bound 0) jF) (Bound 0)) jF);
    val kF = Free("k", natT);
    val ind = nat_induct_atS2 (Qpred, kF);
    val bn0 = subN0S2_at (add ZeroC jF);          (* oeq (sub (add 0 j) 0) (add 0 j) *)
    val a0  = add0S2_at jF;                        (* oeq (add 0 j) j *)
    val base = oeq_trans OF [bn0, a0];            (* oeq (sub (add 0 j) 0) j *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (sub (add xF jF) xF) jF);
    val IH = Thm.assume (ctermSub ihprop);
    val aS = addSucS2_at (xF, jF);                (* oeq (add (Suc x) j) (Suc (add x j)) *)
    val P1 = Abs("z", natT, oeq (sub (add (suc xF) jF) (suc xF)) (sub (Bound 0) (suc xF)));
    val s1 = substPredS2 (P1, add (suc xF) jF, suc (add xF jF)) aS
                (oeqreflS2_at (sub (add (suc xF) jF) (suc xF)));
    val s2 = subSSS2_at (add xF jF, xF);          (* oeq (sub (Suc (add x j))(Suc x)) (sub (add x j) x) *)
    val s12 = oeq_trans OF [s1, s2];
    val stepconcl = oeq_trans OF [s12, IH];
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_sub_add_l = jT (oeq (sub (add kVs jVs) kVs) jVs);
val r_sub_add_l = checkSub ("sub_add_l", sub_add_l, i_sub_add_l);

(* ============================================================================
   HELPER  sub_Suc_add_l : oeq (sub (Suc (add k p)) k) (Suc p)    (induction on k)
   ============================================================================ *)
val sub_Suc_add_l =
  let
    val pF = Free("p", natT);
    val Qpred = Abs("z", natT, oeq (sub (suc (add (Bound 0) pF)) (Bound 0)) (suc pF));
    val kF = Free("k", natT);
    val ind = nat_induct_atS2 (Qpred, kF);
    val bn0 = subN0S2_at (suc (add ZeroC pF));    (* oeq (sub (Suc (add 0 p)) 0) (Suc (add 0 p)) *)
    val a0  = add0S2_at pF;                        (* oeq (add 0 p) p *)
    val a0S = Suc_cong OF [a0];                    (* oeq (Suc (add 0 p)) (Suc p) *)
    val base = oeq_trans OF [bn0, a0S];
    val xF = Free("x", natT);
    val ihprop = jT (oeq (sub (suc (add xF pF)) xF) (suc pF));
    val IH = Thm.assume (ctermSub ihprop);
    val aS  = addSucS2_at (xF, pF);               (* oeq (add (Suc x) p) (Suc (add x p)) *)
    val aSS = Suc_cong OF [aS];                   (* oeq (Suc (add (Suc x) p)) (Suc (Suc (add x p))) *)
    val P1 = Abs("z", natT, oeq (sub (suc (add (suc xF) pF)) (suc xF)) (sub (Bound 0) (suc xF)));
    val s1 = substPredS2 (P1, suc (add (suc xF) pF), suc (suc (add xF pF))) aSS
                (oeqreflS2_at (sub (suc (add (suc xF) pF)) (suc xF)));
    val s2 = subSSS2_at (suc (add xF pF), xF);    (* oeq (sub (Suc (Suc (add x p)))(Suc x)) (sub (Suc (add x p)) x) *)
    val s12 = oeq_trans OF [s1, s2];
    val stepconcl = oeq_trans OF [s12, IH];
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_sub_Suc_add_l = jT (oeq (sub (suc (add kVs pVs)) kVs) (suc pVs));
val r_sub_Suc_add_l = checkSub ("sub_Suc_add_l", sub_Suc_add_l, i_sub_Suc_add_l);

(* ground instantiators for the two add-cancel laws on ctxtSub *)
val sub_add_l_vS2     = varify sub_add_l;
val sub_Suc_add_l_vS2 = varify sub_Suc_add_l;
fun subAddL_at (kt,jt) = beta_norm (Drule.infer_instantiate ctxtSub
                            [(("k",0), ctermSub kt),(("j",0), ctermSub jt)] sub_add_l_vS2);
fun subSucAddL_at (kt,pt) = beta_norm (Drule.infer_instantiate ctxtSub
                            [(("k",0), ctermSub kt),(("p",0), ctermSub pt)] sub_Suc_add_l_vS2);

(* ============================================================================
   3.  sub_Suc_le : jT (le k n) ==> jT (oeq (sub (Suc n) k) (Suc (sub n k)))
       exE on le k n -> witness w with  oeq n (add k w) ; transport.
   ============================================================================ *)
val sub_Suc_le =
  let
    val kF = Free("k", natT); val nF = Free("n", natT);
    val leHyp = jT (le kF nF);
    val H = Thm.assume (ctermSub leHyp);
    val goalBody = oeq (sub (suc nF) kF) (suc (sub nF kF));
    val lePabs = Abs("p", natT, oeq nF (add kF (Bound 0)));
    fun body wF (hw : thm) =          (* hw : oeq n (add k w) *)
      let
        val lhs = subSucAddL_at (kF, wF);          (* oeq (sub (Suc (add k w)) k) (Suc w) *)
        val sal = subAddL_at (kF, wF);             (* oeq (sub (add k w) k) w *)
        val salS = Suc_cong OF [sal];              (* oeq (Suc (sub (add k w) k)) (Suc w) *)
        val salSsym = oeq_sym OF [salS];           (* oeq (Suc w) (Suc (sub (add k w) k)) *)
        val core = oeq_trans OF [lhs, salSsym];    (* oeq (sub (Suc (add k w)) k)(Suc (sub (add k w) k)) *)
        val hwS = oeq_sym OF [hw];                 (* oeq (add k w) n *)
        val Ptr = Abs("z", natT, oeq (sub (suc (Bound 0)) kF) (suc (sub (Bound 0) kF)));
        val res = substPredS2 (Ptr, add kF wF, nF) hwS core;  (* jT (Ptr n) = goalBody *)
      in res end;
    val concl = exE_elimS2 (lePabs, goalBody) H "w" body;
    val d1 = Thm.implies_intr (ctermSub leHyp) concl;
  in varify d1 end;

val i_sub_Suc_le =
  Logic.mk_implies (jT (le kVs nVs),
    jT (oeq (sub (suc nVs) kVs) (suc (sub nVs kVs))));
val r_sub_Suc_le = checkSub ("sub_Suc_le", sub_Suc_le, i_sub_Suc_le);

val s_subSucle_needs_le =
  not ((Thm.prop_of sub_Suc_le) aconv
        (jT (oeq (sub (suc nVs) kVs) (suc (sub nVs kVs)))));

(* sumf ground instantiators on ctxtSub *)
fun sumf0_at fT       = beta_norm (Drule.infer_instantiate ctxtSub [(("f",0), ctermSub fT)] sumf_0_vS2);
fun sumfSuc_at (fT,nt)= beta_norm (Drule.infer_instantiate ctxtSub
                          [(("f",0), ctermSub fT),(("n",0), ctermSub nt)] sumf_Suc_vS2);

(* ============================================================================
   4.  sum_cong :
        (!!k. jT (le k n) ==> jT (oeq (f k)(g k))) ==> jT (oeq (sumf f n)(sumf g n))
       INDUCTION on n with the hypothesis REFLECTED into the OBJECT predicate so
       it rides along nat_induct :
         hypObj z = Forall (%k. Imp (le k z) (oeq (f k)(g k)))
         P z      = Imp (hypObj z) (oeq (sumf f z)(sumf g z))
       Prove jT (P n) by induction; then convert the meta-hyp -> jT (hypObj n)
       (allI over impI on the meta-implication) and mp.
   ============================================================================ *)
val sum_cong =
  let
    val fF = Free("f", fnT); val gF = Free("g", fnT);
    (* CAPTURE-SAFE construction : `le` is only valid on terms WITHOUT dangling de
       Bruijn indices (it wraps its 1st arg under a fresh Abs("p",..)).  So build
       every abstraction over a Free "k"/"z" and abstract it with Term.lambda. *)
    val kAbsV = Free("k", natT);
    (* the object-Forall hypothesis at z : Forall (%k. Imp (le k z)(f k = g k)) *)
    fun hypObjAbs zt =
      Term.lambda kAbsV (mkImp (le kAbsV zt) (oeq (fF $ kAbsV) (gF $ kAbsV)));
    fun hypObj zt = mkForall (hypObjAbs zt);
    fun concBody zt = oeq (sumf fF zt) (sumf gF zt);

    (* induction predicate P z = Imp (hypObj z)(concBody z), capture-safe *)
    val zAbsV = Free("z", natT);
    val Qpred = Term.lambda zAbsV (mkImp (hypObj zAbsV) (concBody zAbsV));
    val nIndV = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nIndV);

    (* ---- BASE : jT (Imp (hypObj 0)(concBody 0)) ---- *)
    val base =
      let
        val hyp0 = Thm.assume (ctermSub (jT (hypObj ZeroC)));   (* jT (Forall (%k. Imp (le k 0)(f k=g k))) *)
        (* allE @ 0 : jT (Imp (le 0 0)(f 0 = g 0)) *)
        val imp00 = allE_S2 (hypObjAbs ZeroC) ZeroC hyp0;
        val le00 = le_reflS2_at ZeroC;                          (* le 0 0 *)
        val f0g0 = mp_S2 (le ZeroC ZeroC, oeq (fF $ ZeroC) (gF $ ZeroC)) imp00 le00;  (* f 0 = g 0 *)
        val sf0 = sumf0_at fF;                                  (* sumf f 0 = f 0 *)
        val sg0 = sumf0_at gF;                                  (* sumf g 0 = g 0 *)
        val sg0sym = oeq_sym OF [sg0];                          (* g 0 = sumf g 0 *)
        val concl0 = oeq_trans OF [oeq_trans OF [sf0, f0g0], sg0sym];  (* sumf f 0 = sumf g 0 *)
        val dis = Thm.implies_intr (ctermSub (jT (hypObj ZeroC))) concl0;
      in impI_S2 (hypObj ZeroC, concBody ZeroC) dis end;

    (* ---- STEP : assume IH : jT (P x) ; prove jT (P (Suc x)) ---- *)
    val xF = Free("x", natT);
    val ihprop = jT (mkImp (hypObj xF) (concBody xF));
    val IH = Thm.assume (ctermSub ihprop);
    val stepConcl =
      let
        (* assume jT (hypObj (Suc x)) ; derive concBody (Suc x) *)
        val hypSx = Thm.assume (ctermSub (jT (hypObj (suc xF))));
        (* build jT (hypObj x) : allI over (!!k. jT (Imp (le k x)(f k=g k))) *)
        val kk = Free("k", natT);
        (* from hypSx allE @ k : jT (Imp (le k (Suc x))(f k=g k)) *)
        val impSx_k = allE_S2 (hypObjAbs (suc xF)) kk hypSx;
        (* meta-derive jT (Imp (le k x)(f k=g k)) via impI : assume le k x, weaken to le k (Suc x), mp *)
        val le_k_x = Thm.assume (ctermSub (jT (le kk xF)));
        val le_x_Sx = le_suc_selfS2_at xF;                      (* le x (Suc x) *)
        val le_k_Sx = le_transS2_at (kk, xF, suc xF) le_k_x le_x_Sx;  (* le k (Suc x) *)
        val fk_gk = mp_S2 (le kk (suc xF), oeq (fF $ kk) (gF $ kk)) impSx_k le_k_Sx;  (* f k = g k *)
        val impx_k_dis = Thm.implies_intr (ctermSub (jT (le kk xF))) fk_gk;  (* meta : le k x ==> f k = g k *)
        val impx_k = impI_S2 (le kk xF, oeq (fF $ kk) (gF $ kk)) impx_k_dis; (* jT (Imp (le k x)(f k=g k)) *)
        (* allI : !!k. jT (Imp (le k x)(f k=g k)) -> jT (hypObj x) *)
        val allMinor = Thm.forall_intr (ctermSub kk) impx_k;    (* !!k. jT ((hypObjAbs x) k) up to beta *)
        val hypObjx = allI_S2 (hypObjAbs xF) allMinor;          (* jT (hypObj x) *)
        (* mp IH with hypObjx : concBody x = sumf f x = sumf g x *)
        val sumfx_eq = mp_S2 (hypObj xF, concBody xF) IH hypObjx;  (* sumf f x = sumf g x *)
        (* f (Suc x) = g (Suc x) : allE hypSx @ (Suc x), mp with le (Suc x)(Suc x) *)
        val impSx_Sx = allE_S2 (hypObjAbs (suc xF)) (suc xF) hypSx;  (* Imp (le (Sx)(Sx))(f Sx=g Sx) *)
        val le_Sx_Sx = le_reflS2_at (suc xF);
        val fSx_gSx = mp_S2 (le (suc xF) (suc xF), oeq (fF $ (suc xF)) (gF $ (suc xF))) impSx_Sx le_Sx_Sx;
        (* sumf_Suc both sides + add congruence *)
        val sfS = sumfSuc_at (fF, xF);                          (* sumf f (Sx) = add (sumf f x)(f Sx) *)
        val sgS = sumfSuc_at (gF, xF);                          (* sumf g (Sx) = add (sumf g x)(g Sx) *)
        val cL = add_cong_lS2 (sumf fF xF, sumf gF xF, fF $ (suc xF)) sumfx_eq;
        val cR = add_cong_rS2 (sumf gF xF, fF $ (suc xF), gF $ (suc xF)) fSx_gSx;
        val mid = oeq_trans OF [cL, cR];
        val sgS_s = oeq_sym OF [sgS];                           (* add (sumf g x)(g Sx) = sumf g (Sx) *)
        val concl = oeq_trans OF [oeq_trans OF [sfS, mid], sgS_s];  (* sumf f (Sx) = sumf g (Sx) *)
        val dis = Thm.implies_intr (ctermSub (jT (hypObj (suc xF)))) concl;
      in impI_S2 (hypObj (suc xF), concBody (suc xF)) dis end;
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepConcl);

    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;    (* r2 : jT (P n) = jT (Imp (hypObj n)(concBody n)) ; n = nIndV *)

    (* ---- CONVERT meta-hyp -> jT (hypObj n) -> concBody n ; discharge meta-hyp ---- *)
    val kk2 = Free("k", natT);
    val metaHyp = Logic.all kk2 (Logic.mk_implies (jT (le kk2 nIndV), jT (oeq (fF $ kk2) (gF $ kk2))));
    val Hm = Thm.assume (ctermSub metaHyp);                     (* !!k. le k n ==> f k = g k *)
    val Hm_k = Thm.forall_elim (ctermSub kk2) Hm;              (* le k n ==> f k = g k (meta) *)
    val impn_k = impI_S2 (le kk2 nIndV, oeq (fF $ kk2) (gF $ kk2)) Hm_k;  (* jT (Imp (le k n)(f k=g k)) *)
    val allMinor2 = Thm.forall_intr (ctermSub kk2) impn_k;
    val hypObjn = allI_S2 (hypObjAbs nIndV) allMinor2;         (* jT (hypObj n) *)
    val concln = mp_S2 (hypObj nIndV, concBody nIndV) r2 hypObjn;  (* oeq (sumf f n)(sumf g n) *)
    val d1 = Thm.implies_intr (ctermSub metaHyp) concln;
  in varify d1 end;

(* intended statement, schematic on ctxtSub. f,g are function Vars. *)
val i_sum_cong =
  let
    val kk = Free("k", natT)
  in
    Logic.mk_implies (
      Logic.all kk (Logic.mk_implies (jT (le kk nVs), jT (oeq (fVs $ kk) (gVs $ kk)))),
      jT (oeq (sumf fVs nVs) (sumf gVs nVs)))
  end;
val r_sum_cong = checkSub ("sum_cong", sum_cong, i_sum_cong);

val s_sumcong_needs_hyp =
  not ((Thm.prop_of sum_cong) aconv (jT (oeq (sumf fVs nVs) (sumf gVs nVs))));

(* ============================================================================
   STAGE C1 FINAL VALIDATION
   ============================================================================ *)
val () =
  if s_subSucle_needs_le andalso s_sumcong_needs_hyp
  then out "SUMSUB_PROBE_OK conditional laws nontrivial\n"
  else out "SUMSUB_PROBE_FAIL a law collapsed!\n";

val () =
  if r_sub_n_0_ax andalso r_sub_0_Suc_ax andalso r_sub_SS_ax
     andalso r_sumf_0_ax andalso r_sumf_Suc_ax
     andalso r_sub_self andalso r_sub_add_l andalso r_sub_Suc_add_l
     andalso r_sub_Suc_le andalso r_sum_cong
     andalso s_subSucle_needs_le andalso s_sumcong_needs_hyp
  then out "SUMSUB_DONE\n"
  else out "SUMSUB_FAILED\n";

(* ============================================================================
   ============================================================================
   ***  STAGE C2 FOUNDATION : SUM-ALGEBRA LEMMAS for the BINOMIAL THEOREM  ***
   ----------------------------------------------------------------------------
   On the final context ctxtSub / ctermSub (theory thySub : sub + sumf on top of
   thyB which carries binom + pow + the full semiring).  We re-varify the pow,
   binom and semiring axioms onto ctxtSub, build mult-congruence + ground
   instantiators there, then prove:
     sum_mult_l    : oeq (mult c (sumf f n)) (sumf (%k. mult c (f k)) n)
     sum_add       : oeq (add (sumf f n)(sumf g n)) (sumf (%k. add (f k)(g k)) n)
     sum_peel_first: oeq (sumf f (Suc n)) (add (f 0) (sumf (%k. f (Suc k)) n))
     binom_n_n     : oeq (binom n n) (Suc Zero)
   plus helper lemmas binom_lt_0 / binom_n_Suc_n and pow_b_sub_Suc.
   ============================================================================ *)

val () = out "SUMALG_BEGIN\n";

(* ---- re-varify the semiring / pow / binom axioms onto ctxtSub ---- *)
val mult_comm_vS2     = varify mult_comm;       (* oeq (mult m n)(mult n m)             *)
val mult_assoc_vS2    = varify mult_assoc;      (* oeq (mult (mult m n) k)(mult m (mult n k)) *)
val left_distrib_vS2  = varify left_distrib;    (* oeq (mult x (add m n))(add (mult x m)(mult x n)) *)
val right_distrib_vS2 = varify right_distrib;   (* oeq (mult (add m n) k)(add (mult m k)(mult n k)) *)

val pow_Zero_vS2      = varify pow_Zero_ax;     (* oeq (pow a 0)(Suc 0)                 *)
val pow_Suc_vS2       = varify pow_Suc_ax;      (* oeq (pow a (Suc n))(mult a (pow a n)) *)

val binom_n_0_vS2     = varify binom_n_0_ax;    (* oeq (binom n 0)(Suc 0)              *)
val binom_0_Suc_vS2   = varify binom_0_Suc_ax;  (* oeq (binom 0 (Suc k)) 0             *)
val binom_Suc_Suc_vS2 = varify binom_Suc_Suc_ax;(* Pascal                              *)

(* ---- ground instantiators on ctxtSub ---- *)
fun multcommS2_at (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt),(("n",0), ctermSub nt)] mult_comm_vS2);
fun ldistS2_at (xt,mt,nt)  = beta_norm (Drule.infer_instantiate ctxtSub
        [(("x",0), ctermSub xt),(("m",0), ctermSub mt),(("n",0), ctermSub nt)] left_distrib_vS2);

fun powZeroS2_at t         = beta_norm (Drule.infer_instantiate ctxtSub
        [(("a",0), ctermSub t)] pow_Zero_vS2);
fun powSucS2_at (at,nt)    = beta_norm (Drule.infer_instantiate ctxtSub
        [(("a",0), ctermSub at),(("n",0), ctermSub nt)] pow_Suc_vS2);

fun binomN0S2_at t         = beta_norm (Drule.infer_instantiate ctxtSub
        [(("n",0), ctermSub t)] binom_n_0_vS2);
fun binom0SS2_at t         = beta_norm (Drule.infer_instantiate ctxtSub
        [(("k",0), ctermSub t)] binom_0_Suc_vS2);
fun binomSSS2_at (nt,kt)   = beta_norm (Drule.infer_instantiate ctxtSub
        [(("n",0), ctermSub nt),(("k",0), ctermSub kt)] binom_Suc_Suc_vS2);

(* ---- mult congruence on ctxtSub (left/right operand) ---- *)
fun mult_cong_lS2 (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("a",0), ctermSub pT), (("b",0), ctermSub qT)] oeq_subst_vS2);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub (mult pT kT))] oeq_refl_vS2);
  in inst OF [hpq, refl_pk] end;
fun mult_cong_rS2 (hT, pT, qT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("a",0), ctermSub pT), (("b",0), ctermSub qT)] oeq_subst_vS2);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub (mult hT pT))] oeq_refl_vS2);
  in inst OF [hpq, refl_hp] end;

(* schematic Var for the constant multiplier c (nat) on ctxtSub *)
val cVc = Var (("c",0), natT);

(* ============================================================================
   1.  sum_mult_l : oeq (mult c (sumf f n)) (sumf (%k. mult c (f k)) n)
       induction on n.  summand g = Abs("k", mult c (f k)).
   ============================================================================ *)
val sum_mult_l =
  let
    val cF = Free("c", natT);
    val fF = Free("f", fnT);
    (* canonical summand lambda : %k. mult c (f k) *)
    val gAbs = Abs("k", natT, mult cF (fF $ (Bound 0)));
    fun g_at t = mult cF (fF $ t);              (* beta-reduced application g $ t *)

    val Qpred = Abs("z", natT, oeq (mult cF (sumf fF (Bound 0))) (sumf gAbs (Bound 0)));
    val nF = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nF);

    (* ---- BASE n = 0 ---- *)
    val base =
      let
        val sf0 = sumf0_at fF;                                  (* sumf f 0 = f 0 *)
        val cL  = mult_cong_rS2 (cF, sumf fF ZeroC, fF $ ZeroC) sf0;  (* mult c (sumf f 0) = mult c (f 0) *)
        val sg0 = sumf0_at gAbs;                                (* sumf g 0 = g 0 = mult c (f 0) [beta] *)
        val sg0sym = oeq_sym OF [sg0];                          (* mult c (f 0) = sumf g 0 *)
      in oeq_trans OF [cL, sg0sym] end;

    (* ---- STEP ---- *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (mult cF (sumf fF xF)) (sumf gAbs xF));
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        val sfS = sumfSuc_at (fF, xF);                          (* sumf f (Sx) = add (sumf f x)(f (Sx)) *)
        val cL  = mult_cong_rS2 (cF, sumf fF (suc xF), add (sumf fF xF) (fF $ (suc xF))) sfS;
                  (* mult c (sumf f (Sx)) = mult c (add (sumf f x)(f (Sx))) *)
        val ld  = ldistS2_at (cF, sumf fF xF, fF $ (suc xF));
                  (* mult c (add (sumf f x)(f Sx)) = add (mult c (sumf f x))(mult c (f Sx)) *)
        val lhs = oeq_trans OF [cL, ld];
                  (* mult c (sumf f (Sx)) = add (mult c (sumf f x))(mult c (f Sx)) *)
        (* RHS : sumf g (Sx) = add (sumf g x)(g Sx) = add (mult c (sumf f x))(mult c (f Sx)) *)
        val sgS = sumfSuc_at (gAbs, xF);                        (* sumf g (Sx) = add (sumf g x)(g Sx) [g Sx beta = mult c (f Sx)] *)
        val cIH = add_cong_lS2 (sumf gAbs xF, mult cF (sumf fF xF), g_at (suc xF)) (oeq_sym OF [IH]);
                  (* add (sumf g x)(g Sx) = add (mult c (sumf f x))(g Sx) ; g Sx = mult c (f Sx) *)
        val rhs = oeq_trans OF [sgS, cIH];
                  (* sumf g (Sx) = add (mult c (sumf f x))(mult c (f Sx)) *)
        val rhsSym = oeq_sym OF [rhs];
      in oeq_trans OF [lhs, rhsSym] end;
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_sum_mult_l =
  let val gV = Abs("k", natT, mult cVc (fVs $ (Bound 0)))
  in jT (oeq (mult cVc (sumf fVs nVs)) (sumf gV nVs)) end;
val r_sum_mult_l = checkSub ("sum_mult_l", sum_mult_l, i_sum_mult_l);

(* ============================================================================
   2.  sum_add : oeq (add (sumf f n)(sumf g n)) (sumf (%k. add (f k)(g k)) n)
       induction on n + add4_swap-style reshuffle.
   ============================================================================ *)
(* add4_swap on ctxtSub : reorder (A+B)+(C+D) -> (A+C)+(B+D) *)
fun add4_swapS2 (A,B,C,D) =
  let
    val asbcd = addassocS2_at (A, B, add C D);
    val i1 = addassocS2_at (B, C, D);
    val i1s = oeq_sym OF [i1];
    val icc = addcommS2_at (B, C);
    val i2 = add_cong_lS2 (add B C, add C B, D) icc;
    val i3 = addassocS2_at (C, B, D);
    val inner = oeq_trans OF [oeq_trans OF [i1s, i2], i3];
    val cInner = add_cong_rS2 (A, add B (add C D), add C (add B D)) inner;
    val r1 = oeq_trans OF [asbcd, cInner];
    val r2assoc = addassocS2_at (A, C, add B D);
    val r2assoc_s = oeq_sym OF [r2assoc];
  in oeq_trans OF [r1, r2assoc_s] end

(* need add_comm/add_assoc instantiators on ctxtSub *)
and addcommS2_at (mt,nt)     = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt),(("n",0), ctermSub nt)] (varify add_comm))
and addassocS2_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt),(("n",0), ctermSub nt),(("k",0), ctermSub kt)] (varify add_assoc));

val sum_add =
  let
    val fF = Free("f", fnT); val gF = Free("g", fnT);
    val hAbs = Abs("k", natT, add (fF $ (Bound 0)) (gF $ (Bound 0)));  (* %k. add (f k)(g k) *)
    fun h_at t = add (fF $ t) (gF $ t);

    val Qpred = Abs("z", natT, oeq (add (sumf fF (Bound 0)) (sumf gF (Bound 0))) (sumf hAbs (Bound 0)));
    val nF = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nF);

    (* ---- BASE n = 0 :  add (sumf f 0)(sumf g 0) = add (f 0)(g 0) = sumf h 0 ---- *)
    val base =
      let
        val sf0 = sumf0_at fF;                                  (* sumf f 0 = f 0 *)
        val sg0 = sumf0_at gF;                                  (* sumf g 0 = g 0 *)
        val cL  = add_cong_lS2 (sumf fF ZeroC, fF $ ZeroC, sumf gF ZeroC) sf0;
                  (* add (sumf f 0)(sumf g 0) = add (f 0)(sumf g 0) *)
        val cR  = add_cong_rS2 (fF $ ZeroC, sumf gF ZeroC, gF $ ZeroC) sg0;
                  (* add (f 0)(sumf g 0) = add (f 0)(g 0) *)
        val sh0 = sumf0_at hAbs;                                (* sumf h 0 = h 0 = add (f 0)(g 0) [beta] *)
        val sh0sym = oeq_sym OF [sh0];
      in oeq_trans OF [oeq_trans OF [cL, cR], sh0sym] end;

    (* ---- STEP ---- *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (add (sumf fF xF) (sumf gF xF)) (sumf hAbs xF));
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        val sfS = sumfSuc_at (fF, xF);                          (* sumf f (Sx) = add (sumf f x)(f Sx) *)
        val sgS = sumfSuc_at (gF, xF);                          (* sumf g (Sx) = add (sumf g x)(g Sx) *)
        (* LHS = add (sumf f (Sx))(sumf g (Sx)) = add (add (sumf f x)(f Sx))(add (sumf g x)(g Sx)) *)
        val cL  = add_cong_lS2 (sumf fF (suc xF), add (sumf fF xF) (fF $ (suc xF)), sumf gF (suc xF)) sfS;
        val cR  = add_cong_rS2 (add (sumf fF xF) (fF $ (suc xF)), sumf gF (suc xF), add (sumf gF xF) (gF $ (suc xF))) sgS;
        val lhs1 = oeq_trans OF [cL, cR];
                  (* add (sumf f (Sx))(sumf g (Sx)) = add (add (sumf f x)(f Sx))(add (sumf g x)(g Sx)) *)
        (* reshuffle to add (add (sumf f x)(sumf g x))(add (f Sx)(g Sx)) *)
        val swap = add4_swapS2 (sumf fF xF, fF $ (suc xF), sumf gF xF, gF $ (suc xF));
        val lhs2 = oeq_trans OF [lhs1, swap];
        (* IH on left summand : add (sumf f x)(sumf g x) = sumf h x *)
        val cIH = add_cong_lS2 (add (sumf fF xF) (sumf gF xF), sumf hAbs xF, add (fF $ (suc xF)) (gF $ (suc xF))) IH;
        val lhs3 = oeq_trans OF [lhs2, cIH];
                  (* = add (sumf h x)(add (f Sx)(g Sx)) *)
        (* RHS : sumf h (Sx) = add (sumf h x)(h Sx) ; h Sx beta = add (f Sx)(g Sx) *)
        val shS = sumfSuc_at (hAbs, xF);
        val shSsym = oeq_sym OF [shS];
      in oeq_trans OF [lhs3, shSsym] end;
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_sum_add =
  let val hV = Abs("k", natT, add (fVs $ (Bound 0)) (gVs $ (Bound 0)))
  in jT (oeq (add (sumf fVs nVs) (sumf gVs nVs)) (sumf hV nVs)) end;
val r_sum_add = checkSub ("sum_add", sum_add, i_sum_add);

(* ============================================================================
   3.  sum_peel_first :
        oeq (sumf f (Suc n)) (add (f Zero) (sumf (%k. f (Suc k)) n))
       induction on n.
   ============================================================================ *)
val sum_peel_first =
  let
    val fF = Free("f", fnT);
    val tAbs = Abs("k", natT, fF $ (suc (Bound 0)));   (* %k. f (Suc k) *)
    fun t_at t = fF $ (suc t);

    (* P z = oeq (sumf f (Suc z)) (add (f 0)(sumf tAbs z)) *)
    val Qpred = Abs("z", natT, oeq (sumf fF (suc (Bound 0))) (add (fF $ ZeroC) (sumf tAbs (Bound 0))));
    val nF = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nF);

    (* ---- BASE n = 0 :  sumf f (Suc 0) = add (sumf f 0)(f (Suc 0)) = add (f 0)(f (Suc 0))
                          RHS add (f 0)(sumf tAbs 0) = add (f 0)(t 0) = add (f 0)(f (Suc 0)) ---- *)
    val base =
      let
        val sfS0 = sumfSuc_at (fF, ZeroC);                      (* sumf f (Suc 0) = add (sumf f 0)(f (Suc 0)) *)
        val sf0  = sumf0_at fF;                                 (* sumf f 0 = f 0 *)
        val cL   = add_cong_lS2 (sumf fF ZeroC, fF $ ZeroC, fF $ (suc ZeroC)) sf0;
                   (* add (sumf f 0)(f (Suc 0)) = add (f 0)(f (Suc 0)) *)
        val lhs  = oeq_trans OF [sfS0, cL];                     (* sumf f (Suc 0) = add (f 0)(f (Suc 0)) *)
        val st0  = sumf0_at tAbs;                               (* sumf tAbs 0 = t 0 = f (Suc 0) [beta] *)
        val cR   = add_cong_rS2 (fF $ ZeroC, fF $ (suc ZeroC), sumf tAbs ZeroC) (oeq_sym OF [st0]);
                   (* add (f 0)(f (Suc 0)) = add (f 0)(sumf tAbs 0) *)
      in oeq_trans OF [lhs, cR] end;

    (* ---- STEP : assume sumf f (Sx) = add (f 0)(sumf tAbs x) ; prove for Suc x ---- *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (sumf fF (suc xF)) (add (fF $ ZeroC) (sumf tAbs xF)));
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        (* LHS : sumf f (Suc (Suc x)) = add (sumf f (Suc x))(f (Suc (Suc x))) *)
        val sfSS = sumfSuc_at (fF, suc xF);
        (* rewrite the (sumf f (Suc x)) summand via IH *)
        val cIH = add_cong_lS2 (sumf fF (suc xF), add (fF $ ZeroC) (sumf tAbs xF), fF $ (suc (suc xF))) IH;
        val lhs1 = oeq_trans OF [sfSS, cIH];
                   (* = add (add (f 0)(sumf tAbs x))(f (Suc (Suc x))) *)
        (* re-associate to add (f 0)(add (sumf tAbs x)(f (Suc (Suc x)))) *)
        val reassoc = addassocS2_at (fF $ ZeroC, sumf tAbs xF, fF $ (suc (suc xF)));
        val lhs2 = oeq_trans OF [lhs1, reassoc];
        (* RHS : add (f 0)(sumf tAbs (Suc x)) ; sumf tAbs (Suc x) = add (sumf tAbs x)(t (Suc x))
                 t (Suc x) beta = f (Suc (Suc x)) *)
        val stS = sumfSuc_at (tAbs, xF);                        (* sumf tAbs (Suc x) = add (sumf tAbs x)(f (Suc (Suc x))) *)
        val stSsym = oeq_sym OF [stS];                          (* add (sumf tAbs x)(f (Suc (Suc x))) = sumf tAbs (Suc x) *)
        val cRHS = add_cong_rS2 (fF $ ZeroC, add (sumf tAbs xF) (t_at (suc xF)), sumf tAbs (suc xF)) stSsym;
                   (* add (f 0)(add (sumf tAbs x)(f (SSx))) = add (f 0)(sumf tAbs (Suc x)) *)
      in oeq_trans OF [lhs2, cRHS] end;
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_sum_peel_first =
  let val tV = Abs("k", natT, fVs $ (suc (Bound 0)))
  in jT (oeq (sumf fVs (suc nVs)) (add (fVs $ ZeroC) (sumf tV nVs))) end;
val r_sum_peel_first = checkSub ("sum_peel_first", sum_peel_first, i_sum_peel_first);

(* ============================================================================
   HELPER  binom_lt_0 : jT (lt n k) ==> jT (oeq (binom n k) Zero)
       (n < k  =>  C(n,k) = 0).  Reflect the bound into the object predicate and
       induct on n with k UNIVERSAL (object Forall), inner case-split on k.
       We instead use a direct double-induction-free route:  induction on n with a
       Forall over k inside, using lt n k.

   We take the simplest robust path : prove binom_n_Suc_n directly by induction.
       binom_n_Suc_n : oeq (binom n (Suc n)) Zero        (C(n,n+1) = 0)
       induction on n :
         base : binom 0 (Suc 0) = 0           [binom_0_Suc]
         step : binom (Suc x)(Suc (Suc x)) = binom x (Suc x) + binom x (Suc (Suc x))  [Pascal]
                = 0 + binom x (Suc(Suc x))    [IH on first summand]
                BUT binom x (Suc(Suc x)) is C(x, x+2), need it = 0 too.
       So a single induction on n is NOT enough : we need n<k generally.  Prove
       binom_lt_0 by induction on n with k universally quantified (object Forall).
   ============================================================================ *)
(* lt is defined as : lt m n  ==  le (Suc m) n  (strict order).  Locate it. *)

(* binom right-argument congruence on ctxtSub : oeq u v ==> oeq (binom n u)(binom n v) *)
fun binom_cong_r2 (nT, uT, vT) huv =
  let
    val Pabs = Abs("z", natT, oeq (binom nT uT) (binom nT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("a",0), ctermSub uT), (("b",0), ctermSub vT)] oeq_subst_vS2);
    val refl_nu = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub (binom nT uT))] oeq_refl_vS2);
  in inst OF [huv, refl_nu] end;

(* ============================================================================
   HELPER  binom_diag_zero : (!!j. nothing) — object Forall over j :
        P n  ==  Forall (%j. oeq (binom n (add (Suc n) j)) Zero)
        i.e.  for all j, C(n, n+1+j) = 0.   Induction on n.
   ============================================================================ *)
val binom_diag_zero =
  let
    val jAbsV = Free("j", natT);
    fun bodyAt nt jt = oeq (binom nt (add (suc nt) jt)) ZeroC;
    fun predAbs nt = Term.lambda jAbsV (bodyAt nt jAbsV);   (* %j. binom n (n+1+j) = 0 *)
    fun predForall nt = mkForall (predAbs nt);

    val zAbsV = Free("z", natT);
    val Qpred = Term.lambda zAbsV (predForall zAbsV);
    val nIndV = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nIndV);

    (* ---- BASE n = 0 : forall j. binom 0 (add (Suc 0) j) = 0 ---- *)
    val base =
      let
        val jF = Free("j", natT);
        (* add (Suc 0) j = Suc (add 0 j) = Suc j *)
        val aS = addSucS2_at (ZeroC, jF);                 (* add (Suc 0) j = Suc (add 0 j) *)
        val a0 = add0S2_at jF;                            (* add 0 j = j *)
        val a0S = Suc_cong OF [a0];                       (* Suc (add 0 j) = Suc j *)
        val addEq = oeq_trans OF [aS, a0S];               (* add (Suc 0) j = Suc j *)
        (* binom 0 (add (Suc 0) j) = binom 0 (Suc j) = 0 *)
        val cong = binom_cong_r2 (ZeroC, add (suc ZeroC) jF, suc jF) addEq;  (* binom 0 (n1+j) = binom 0 (Suc j) *)
        val b0Sj = binom0SS2_at jF;                       (* binom 0 (Suc j) = 0 *)
        val body0 = oeq_trans OF [cong, b0Sj];            (* binom 0 (add (Suc 0) j) = 0 *)
        val allMinor = Thm.forall_intr (ctermSub jF) body0;  (* !!j. jT (binom 0 (add (Suc 0) j) = 0) up to beta *)
      in allI_S2 (predAbs ZeroC) allMinor end;            (* jT (Forall (%j. ...)) *)

    (* ---- STEP : assume P x ; prove P (Suc x) ---- *)
    val xF = Free("x", natT);
    val ihprop = jT (predForall xF);
    val IH = Thm.assume (ctermSub ihprop);
    val stepconcl =
      let
        val jF = Free("j", natT);
        (* goal body at (Suc x), j : binom (Suc x)(add (Suc(Suc x)) j) = 0 *)
        (* add (Suc(Suc x)) j = Suc (add (Suc x) j)   [add_Suc] *)
        val aS = addSucS2_at (suc xF, jF);                (* add (Suc(Suc x)) j = Suc (add (Suc x) j) *)
        val mTerm = add (suc xF) jF;                      (* m := add (Suc x) j *)
        (* binom (Suc x)(add (Suc(Suc x)) j) = binom (Suc x)(Suc m)  [cong on 2nd arg] *)
        val cong0 = binom_cong_r2 (suc xF, add (suc (suc xF)) jF, suc mTerm) aS;
        (* Pascal : binom (Suc x)(Suc m) = add (binom x m)(binom x (Suc m)) *)
        val pasc = binomSSS2_at (xF, mTerm);
        val lhs1 = oeq_trans OF [cong0, pasc];
                   (* binom (Suc x)(...) = add (binom x m)(binom x (Suc m)) *)
        (* binom x m = binom x (add (Suc x) j) = 0  via IH @ j *)
        val IH_j = allE_S2 (predAbs xF) jF IH;            (* jT (binom x (add (Suc x) j) = 0) *)
        (* binom x (Suc m) : Suc m = Suc (add (Suc x) j) = add (Suc x)(Suc j)  [add_Suc_right sym] *)
        val aSr = addSrS2_at (suc xF, jF);                (* add (Suc x)(Suc j) = Suc (add (Suc x) j) = Suc m *)
        val aSrsym = oeq_sym OF [aSr];                    (* Suc m = add (Suc x)(Suc j) *)
        val congSm = binom_cong_r2 (xF, suc mTerm, add (suc xF) (suc jF)) aSrsym;
                     (* binom x (Suc m) = binom x (add (Suc x)(Suc j)) *)
        val IH_Sj = allE_S2 (predAbs xF) (suc jF) IH;     (* jT (binom x (add (Suc x)(Suc j)) = 0) *)
        val bxSm0 = oeq_trans OF [congSm, IH_Sj];         (* binom x (Suc m) = 0 *)
        (* assemble : add (binom x m)(binom x (Suc m)) = add 0 0 = 0 *)
        val cL = add_cong_lS2 (binom xF mTerm, ZeroC, binom xF (suc mTerm)) IH_j;
                 (* add (binom x m)(binom x (Suc m)) = add 0 (binom x (Suc m)) *)
        val cR = add_cong_rS2 (ZeroC, binom xF (suc mTerm), ZeroC) bxSm0;
                 (* add 0 (binom x (Suc m)) = add 0 0 *)
        val a00 = add0S2_at ZeroC;                        (* add 0 0 = 0 *)
        val rhs = oeq_trans OF [oeq_trans OF [cL, cR], a00];  (* add (..)(..) = 0 *)
        val body = oeq_trans OF [lhs1, rhs];              (* binom (Suc x)(add (Suc(Suc x)) j) = 0 *)
        val allMinor = Thm.forall_intr (ctermSub jF) body;
      in allI_S2 (predAbs (suc xF)) allMinor end;
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;    (* r2 : jT (Forall (%j. binom n (add (Suc n) j) = 0)) ; n = nIndV *)
  in varify r2 end;

(* binom_n_Suc_n : oeq (binom n (Suc n)) Zero
     instantiate binom_diag_zero @ j := 0, then add (Suc n) 0 = Suc n. *)
val binom_diag_zero_vS2 = varify binom_diag_zero;
val binom_n_Suc_n =
  let
    val nF = Free("n", natT);
    (* instantiate the forall (over n) version at n := nF, then allE @ 0 *)
    val diag_n = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub nF)] binom_diag_zero_vS2);
                 (* jT (Forall (%j. binom n (add (Suc n) j) = 0)) *)
    val predAbsN = Abs("j", natT, oeq (binom nF (add (suc nF) (Bound 0))) ZeroC);
    val at0 = allE_S2 predAbsN ZeroC diag_n;              (* jT (binom n (add (Suc n) 0) = 0) *)
    (* add (Suc n) 0 = Suc n *)
    val a0r = add0rS2_at (suc nF);                        (* add (Suc n) 0 = Suc n *)
    val cong = binom_cong_r2 (nF, suc nF, add (suc nF) ZeroC) (oeq_sym OF [a0r]);
               (* binom n (Suc n) = binom n (add (Suc n) 0) *)
    val res = oeq_trans OF [cong, at0];                   (* binom n (Suc n) = 0 *)
  in varify res end;

val i_binom_n_Suc_n = jT (oeq (binom nVs (suc nVs)) ZeroC);
val r_binom_n_Suc_n = checkSub ("binom_n_Suc_n", binom_n_Suc_n, i_binom_n_Suc_n);

(* ground instantiator for binom_n_Suc_n on ctxtSub *)
val binom_n_Suc_n_vS2 = varify binom_n_Suc_n;
fun binomNSn_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] binom_n_Suc_n_vS2);

(* ============================================================================
   4.  binom_n_n : oeq (binom n n) (Suc Zero)        (induction on n)
       base : binom 0 0 = 1            [binom_n_0]
       step : binom (Suc x)(Suc x) = binom x x + binom x (Suc x)  [Pascal]
              = add (Suc 0) 0          [IH + binom_n_Suc_n]
              = Suc 0                  [add_0_right]
   ============================================================================ *)
val binom_n_n =
  let
    val Qpred = Abs("z", natT, oeq (binom (Bound 0) (Bound 0)) (suc ZeroC));
    val nF = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nF);
    val base = binomN0S2_at ZeroC;                        (* binom 0 0 = Suc 0 *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (binom xF xF) (suc ZeroC));
    val IH = Thm.assume (ctermSub ihprop);
    val pasc = binomSSS2_at (xF, xF);                     (* binom (Suc x)(Suc x) = add (binom x x)(binom x (Suc x)) *)
    val cL = add_cong_lS2 (binom xF xF, suc ZeroC, binom xF (suc xF)) IH;
             (* = add (Suc 0)(binom x (Suc x)) *)
    val bnsn = binomNSn_at xF;                            (* binom x (Suc x) = 0 *)
    val cR = add_cong_rS2 (suc ZeroC, binom xF (suc xF), ZeroC) bnsn;
             (* = add (Suc 0) 0 *)
    val a0r = add0rS2_at (suc ZeroC);                     (* add (Suc 0) 0 = Suc 0 *)
    val stepconcl = oeq_trans OF [oeq_trans OF [oeq_trans OF [pasc, cL], cR], a0r];
    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val i_binom_n_n = jT (oeq (binom nVs nVs) (suc ZeroC));
val r_binom_n_n = checkSub ("binom_n_n", binom_n_n, i_binom_n_n);

(* ============================================================================
   HELPER  pow_b_sub_Suc : jT (le k n) ==>
              oeq (mult (pow b (sub n k)) b) (pow b (sub (Suc n) k))
       sub (Suc n) k = Suc (sub n k)   [sub_Suc_le @ le k n]
       pow b (Suc (sub n k)) = mult b (pow b (sub n k))   [pow_Suc]
       mult (pow b (sub n k)) b = mult b (pow b (sub n k))  [mult_comm]
   ============================================================================ *)
val sub_Suc_le_vS2 = varify sub_Suc_le;
fun subSucLe_at (kt,nt) = beta_norm (Drule.infer_instantiate ctxtSub
        [(("k",0), ctermSub kt),(("n",0), ctermSub nt)] sub_Suc_le_vS2);

val pow_b_sub_Suc =
  let
    val bF = Free("b", natT); val kF = Free("k", natT); val nF = Free("n", natT);
    val leHyp = jT (le kF nF);
    val H = Thm.assume (ctermSub leHyp);
    (* sub (Suc n) k = Suc (sub n k) *)
    val ssl = Thm.implies_elim (subSucLe_at (kF, nF)) H;  (* oeq (sub (Suc n) k)(Suc (sub n k)) *)
    (* pow b (Suc (sub n k)) = mult b (pow b (sub n k))  [pow_Suc] *)
    val psuc = powSucS2_at (bF, sub nF kF);              (* pow b (Suc (sub n k)) = mult b (pow b (sub n k)) *)
    (* mult (pow b (sub n k)) b = mult b (pow b (sub n k))  [mult_comm] *)
    val mc = multcommS2_at (pow bF (sub nF kF), bF);     (* mult (pow b (sub n k)) b = mult b (pow b (sub n k)) *)
    (* chain : mult (pow b (sub n k)) b = mult b (pow b (sub n k)) = pow b (Suc (sub n k)) [psuc sym]
              = pow b (sub (Suc n) k)  [cong arg2 with ssl sym] *)
    val psucS = oeq_sym OF [psuc];                       (* mult b (pow b (sub n k)) = pow b (Suc (sub n k)) *)
    val c1 = oeq_trans OF [mc, psucS];                   (* mult (pow b (sub n k)) b = pow b (Suc (sub n k)) *)
    (* pow b (Suc (sub n k)) = pow b (sub (Suc n) k)  via pow arg2 cong with ssl sym *)
    val powcong =
      let
        val Pabs = Abs("z", natT, oeq (pow bF (suc (sub nF kF))) (pow bF (Bound 0)));
        val inst = beta_norm (Drule.infer_instantiate ctxtSub
              [(("P",0), ctermSub Pabs), (("a",0), ctermSub (suc (sub nF kF))), (("b",0), ctermSub (sub (suc nF) kF))] oeq_subst_vS2);
        val refl_bp = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub (pow bF (suc (sub nF kF))))] oeq_refl_vS2);
      in inst OF [oeq_sym OF [ssl], refl_bp] end;        (* pow b (Suc (sub n k)) = pow b (sub (Suc n) k) *)
    val core = oeq_trans OF [c1, powcong];               (* mult (pow b (sub n k)) b = pow b (sub (Suc n) k) *)
    val disch = Thm.implies_intr (ctermSub leHyp) core;
  in varify disch end;

val bVps = Var (("b",0), natT);
val i_pow_b_sub_Suc =
  Logic.mk_implies (jT (le kVs nVs),
    jT (oeq (mult (pow bVps (sub nVs kVs)) bVps) (pow bVps (sub (suc nVs) kVs))));
val r_pow_b_sub_Suc = checkSub ("pow_b_sub_Suc", pow_b_sub_Suc, i_pow_b_sub_Suc);

(* soundness probe : pow_b_sub_Suc must still carry the le k n premise *)
val s_powbsub_needs_le =
  not ((Thm.prop_of pow_b_sub_Suc) aconv
        (jT (oeq (mult (pow bVps (sub nVs kVs)) bVps) (pow bVps (sub (suc nVs) kVs)))));

(* ============================================================================
   STAGE C2 FOUNDATION FINAL VALIDATION
   ============================================================================ *)
val () =
  if r_sum_mult_l andalso r_sum_add andalso r_sum_peel_first
     andalso r_binom_n_n andalso r_binom_n_Suc_n
     andalso r_pow_b_sub_Suc andalso s_powbsub_needs_le
  then out "SUMALG_OK\n"
  else out "SUMALG_FAIL\n";

(* ============================================================================
   ============================================================================
   ***  STAGE C3 : THE BINOMIAL THEOREM  ***
   ----------------------------------------------------------------------------
   binom_theorem :
     oeq (pow (add a b) n)
         (sumf (Abs k. mult (binom n k)(mult (pow a k)(pow b (sub n k)))) n)
   i.e. (a+b)^n = SUM_{k=0}^n  C(n,k) * a^k * b^(n-k).
   Proof by induction on n with a,b FREE.
   ============================================================================ *)

val () = out "BINOM_BEGIN\n";

(* ---- extra ground instantiators on ctxtSub that the foundation did not name ---- *)
fun rdistS2_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt),(("n",0), ctermSub nt),(("k",0), ctermSub kt)] right_distrib_vS2);
fun multassocS2_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtSub
        [(("m",0), ctermSub mt),(("n",0), ctermSub nt),(("k",0), ctermSub kt)] mult_assoc_vS2);

val mult_1_left_vS2  = varify mult_1_left;     (* oeq (mult (Suc 0) n) n *)
fun mult1lS2_at t = beta_norm (Drule.infer_instantiate ctxtSub [(("n",0), ctermSub t)] mult_1_left_vS2);

val subN0S2_at_local = subN0S2_at;             (* alias, already exists : oeq (sub n 0) n *)

(* pow 2nd-argument congruence on ctxtSub :  oeq u v ==> oeq (pow b u)(pow b v) *)
fun pow_cong_a2S2 (bT, uT, vT) huv =
  let
    val Pabs = Abs("z", natT, oeq (pow bT uT) (pow bT (Bound 0)));
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
          [(("P",0), ctermSub Pabs), (("a",0), ctermSub uT), (("b",0), ctermSub vT)] oeq_subst_vS2);
    val refl_bu = beta_norm (Drule.infer_instantiate ctxtSub [(("a",0), ctermSub (pow bT uT))] oeq_refl_vS2);
  in inst OF [huv, refl_bu] end;

(* pow_Suc instantiator already present as powSucS2_at (at,nt) : pow a (Suc n) = mult a (pow a n) *)
(* pow_Zero instantiator already present as powZeroS2_at t : pow a 0 = Suc 0 *)
(* binom helpers : binomN0S2_at, binom0SS2_at, binomSSS2_at ; sub helpers : subN0S2_at, subSSS2_at *)

(* sum_cong on ctxtSub : (!!k. le k n ==> f k = g k) ==> sumf f n = sumf g n *)
val sum_cong_vS2 = varify sum_cong;
fun sum_cong_at (fAbs, gAbs, nt) congProof =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("f",0), ctermSub fAbs), (("g",0), ctermSub gAbs), (("n",0), ctermSub nt)] sum_cong_vS2)
  in Thm.implies_elim inst congProof end;

(* pow_b_sub_Suc instantiator : le k n ==> mult (pow b (sub n k)) b = pow b (sub (Suc n) k) *)
val pow_b_sub_Suc_vS2 = varify pow_b_sub_Suc;
fun powBsubSuc_at (bt,kt,nt) hle =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSub
        [(("b",0), ctermSub bt),(("k",0), ctermSub kt),(("n",0), ctermSub nt)] pow_b_sub_Suc_vS2)
  in Thm.implies_elim inst hle end;

val () = out "BINOM_HELPERS_READY\n";

(* ============================================================================
   THE MAIN INDUCTION
   ============================================================================ *)
val binom_theorem =
  let
    val aF = Free("a", natT);
    val bF = Free("b", natT);

    (* induction-predicate summand  : %k. C(z,k) * a^k * b^(z-k)  (z = ind var) *)
    fun summandAbs zt = Abs("k", natT,
          mult (binom zt (Bound 0)) (mult (pow aF (Bound 0)) (pow bF (sub zt (Bound 0)))));
    fun summand_at zt t =
          mult (binom zt t) (mult (pow aF t) (pow bF (sub zt t)));     (* beta of (summandAbs zt) $ t *)
    fun pbody zt = oeq (pow (add aF bF) zt) (sumf (summandAbs zt) zt);

    val zV = Free("z", natT);
    val Qpred = Term.lambda zV (pbody zV);
    val nIndV = Free("n", natT);
    val ind = nat_induct_atS2 (Qpred, nIndV);

    (* ====================================================================
       BASE  n = 0 :  pow (a+b) 0 = 1 ;  sumf (summandAbs 0) 0 = (summandAbs 0) $ 0
                      = C(0,0)*a^0*b^(0-0) = 1*(1*b^0) = 1.
       ==================================================================== *)
    val base =
      let
        val lhs0 = powZeroS2_at (add aF bF);                  (* pow (a+b) 0 = Suc 0 *)
        (* RHS : sumf (summandAbs 0) 0 = summand_at 0 0 [sumf_0, beta] *)
        val sf0  = sumf0_at (summandAbs ZeroC);              (* sumf F0 0 = summand_at 0 0 *)
        (* summand_at 0 0 = C(0,0)*( a^0 *( b^(0-0) ) ) ; reduce to Suc 0 *)
        val b00  = binomN0S2_at ZeroC;                        (* binom 0 0 = Suc 0 *)
        val pa0  = powZeroS2_at aF;                           (* pow a 0 = Suc 0 *)
        val sub00= subN0S2_at ZeroC;                         (* sub 0 0 = 0 *)
        val pb0c = pow_cong_a2S2 (bF, sub ZeroC ZeroC, ZeroC) sub00;  (* pow b (0-0) = pow b 0 *)
        val pb0  = powZeroS2_at bF;                           (* pow b 0 = Suc 0 *)
        val pbsub= oeq_trans OF [pb0c, pb0];                  (* pow b (0-0) = Suc 0 *)
        (* inner = mult (pow a 0)(pow b (0-0)) ; = mult (Suc 0)(Suc 0) ; reduce *)
        val innerL = mult_cong_lS2 (pow aF ZeroC, suc ZeroC, pow bF (sub ZeroC ZeroC)) pa0;
                     (* mult (pow a 0)(pow b (0-0)) = mult (Suc 0)(pow b (0-0)) *)
        val innerR = mult_cong_rS2 (suc ZeroC, pow bF (sub ZeroC ZeroC), suc ZeroC) pbsub;
                     (* mult (Suc 0)(pow b (0-0)) = mult (Suc 0)(Suc 0) *)
        val inner1 = oeq_trans OF [innerL, innerR];           (* inner = mult (Suc 0)(Suc 0) *)
        val m11    = mult1lS2_at (suc ZeroC);                 (* mult (Suc 0)(Suc 0) = Suc 0 *)
        val inner  = oeq_trans OF [inner1, m11];              (* inner = Suc 0 *)
        (* outer = mult (binom 0 0) inner = mult (Suc 0) inner [cong] = inner [m1l] = Suc 0 *)
        val outerL = mult_cong_lS2 (binom ZeroC ZeroC, suc ZeroC, mult (pow aF ZeroC) (pow bF (sub ZeroC ZeroC))) b00;
                     (* outer = mult (Suc 0)(inner-orig) *)
        val outerR = mult_cong_rS2 (suc ZeroC, mult (pow aF ZeroC) (pow bF (sub ZeroC ZeroC)), suc ZeroC) inner;
                     (* mult (Suc 0)(inner-orig) = mult (Suc 0)(Suc 0) *)
        val outer1 = oeq_trans OF [outerL, outerR];           (* outer = mult (Suc 0)(Suc 0) *)
        val m11b   = mult1lS2_at (suc ZeroC);                 (* mult (Suc 0)(Suc 0) = Suc 0 *)
        val outer  = oeq_trans OF [outer1, m11b];             (* summand_at 0 0 = Suc 0 *)
        val rhs0   = oeq_trans OF [sf0, outer];               (* sumf F0 0 = Suc 0 *)
        val rhs0s  = oeq_sym OF [rhs0];                       (* Suc 0 = sumf F0 0 *)
      in oeq_trans OF [lhs0, rhs0s] end;                      (* pow (a+b) 0 = sumf F0 0 *)

    (* ====================================================================
       STEP  n = x -> Suc x.   IH : pow (a+b) x = sumf (summandAbs x) x.
       ==================================================================== *)
    val xF = Free("x", natT);
    val nn = xF;                              (* the IH parameter *)
    val ihprop = jT (pbody xF);              (* oeq (pow (a+b) x) (sumf (summandAbs x) x) *)
    val IH = Thm.assume (ctermSub ihprop);

    val stepconcl =
      let
        val Fn    = summandAbs nn;            (* %k. C(x,k)*a^k*b^(x-k) *)
        val FSucN = summandAbs (suc nn);      (* %k. C(Sx,k)*a^k*b^((Sx)-k) *)

        (* canonical reshaped summand lambdas *)
        val G1 = Abs("k", natT,
              mult (binom nn (Bound 0)) (mult (pow aF (suc (Bound 0))) (pow bF (sub nn (Bound 0)))));
        fun G1_at t = mult (binom nn t) (mult (pow aF (suc t)) (pow bF (sub nn t)));
        val H  = Abs("k", natT,
              mult (binom nn (Bound 0)) (mult (pow aF (Bound 0)) (pow bF (sub (suc nn) (Bound 0)))));
        fun H_at t  = mult (binom nn t) (mult (pow aF t) (pow bF (sub (suc nn) t)));
        val G2 = Abs("k", natT,
              mult (binom nn (suc (Bound 0))) (mult (pow aF (suc (Bound 0))) (pow bF (sub nn (Bound 0)))));
        fun G2_at t = mult (binom nn (suc t)) (mult (pow aF (suc t)) (pow bF (sub nn t)));

        (* ------------------------------------------------------------------
           LHS : pow (a+b)(Suc x) = add (sumf G1 x) (sumf H x)
           ------------------------------------------------------------------ *)
        val pS   = powSucS2_at (add aF bF, nn);             (* pow (a+b)(Sx) = mult (a+b)(pow (a+b) x) *)
        val pIH  = mult_cong_rS2 (add aF bF, pow (add aF bF) nn, sumf Fn nn) IH;
                   (* mult (a+b)(pow (a+b) x) = mult (a+b)(sumf Fn x) *)
        val rd   = rdistS2_at (aF, bF, sumf Fn nn);
                   (* mult (add a b)(sumf Fn x) = add (mult a (sumf Fn x))(mult b (sumf Fn x)) *)
        val lhsAB = oeq_trans OF [oeq_trans OF [pS, pIH], rd];
                   (* pow (a+b)(Sx) = add Sa Sb ; Sa = mult a (sumf Fn x), Sb = mult b (sumf Fn x) *)

        (* Sa = mult a (sumf Fn x) = sumf (%k. mult a (Fn k)) x  [sum_mult_l c:=a] *)
        val aFnAbs = Abs("k", natT, mult aF (summand_at nn (Bound 0)));
        fun aFn_at t = mult aF (summand_at nn t);
        val sml_a = Drule.infer_instantiate ctxtSub
              [(("c",0), ctermSub aF), (("f",0), ctermSub Fn), (("n",0), ctermSub nn)] sum_mult_l;
        val sml_a' = beta_norm sml_a;       (* mult a (sumf Fn x) = sumf aFnAbs x *)
        (* sum_cong : sumf aFnAbs x = sumf G1 x   (pointwise mult a (Fn k) = G1 k, no le) *)
        val congSa =
          let
            val kF = Free("k", natT);
            (* prove : le k x ==> oeq (aFn_at k)(G1_at k) *)
            val hle = Thm.assume (ctermSub (jT (le kF nn)));
            (* mult a (C*(a^k*b^(x-k))) ; pull C out front : a*(C*X) = C*(a*X) *)
            val C   = binom nn kF;
            val X   = mult (pow aF kF) (pow bF (sub nn kF));
            (* a*(C*X) = (a*C)*X [assoc sym]  then (a*C) = (C*a) [comm] then (C*a)*X = C*(a*X) [assoc] *)
            val as1 = multassocS2_at (aF, C, X);            (* (a*C)*X = a*(C*X) *)
            val as1s= oeq_sym OF [as1];                     (* a*(C*X) = (a*C)*X *)
            val cm  = multcommS2_at (aF, C);                (* a*C = C*a *)
            val cmc = mult_cong_lS2 (mult aF C, mult C aF, X) cm;  (* (a*C)*X = (C*a)*X *)
            val as2 = multassocS2_at (C, aF, X);            (* (C*a)*X = C*(a*X) *)
            val pull= oeq_trans OF [oeq_trans OF [as1s, cmc], as2];  (* a*(C*X) = C*(a*X) *)
            (* a*X = a*(a^k * b^(x-k)) = (a*a^k)*b^(x-k) = a^(Sk)*b^(x-k) *)
            val aX_as = multassocS2_at (aF, pow aF kF, pow bF (sub nn kF));   (* (a*a^k)*b = a*(a^k*b) *)
            val aX_ass= oeq_sym OF [aX_as];                 (* a*(a^k*b) = (a*a^k)*b *)
            val pSk = powSucS2_at (aF, kF);                 (* a^(Sk) = mult a (a^k) = a*a^k *)
            val pSks= oeq_sym OF [pSk];                     (* a*a^k = a^(Sk) *)
            val aX_top = mult_cong_lS2 (mult aF (pow aF kF), pow aF (suc kF), pow bF (sub nn kF)) pSks;
                         (* (a*a^k)*b = a^(Sk)*b *)
            val aX = oeq_trans OF [aX_ass, aX_top];         (* a*X = a^(Sk)*b^(x-k) *)
            (* C*(a*X) = C*(a^(Sk)*b^(x-k)) = G1_at k *)
            val cong_inner = mult_cong_rS2 (C, mult aF X, mult (pow aF (suc kF)) (pow bF (sub nn kF))) aX;
            val body = oeq_trans OF [pull, cong_inner];     (* aFn_at k = G1_at k *)
            val dis = Thm.implies_intr (ctermSub (jT (le kF nn))) body;
            val allm = Thm.forall_intr (ctermSub kF) dis;   (* !!k. le k x ==> aFn_at k = G1_at k *)
          in sum_cong_at (aFnAbs, G1, nn) allm end;          (* sumf aFnAbs x = sumf G1 x *)
        val Sa_eq = oeq_trans OF [sml_a', congSa];           (* mult a (sumf Fn x) = sumf G1 x *)

        (* Sb = mult b (sumf Fn x) = sumf (%k. mult b (Fn k)) x  [sum_mult_l c:=b] *)
        val bFnAbs = Abs("k", natT, mult bF (summand_at nn (Bound 0)));
        fun bFn_at t = mult bF (summand_at nn t);
        val sml_b = Drule.infer_instantiate ctxtSub
              [(("c",0), ctermSub bF), (("f",0), ctermSub Fn), (("n",0), ctermSub nn)] sum_mult_l;
        val sml_b' = beta_norm sml_b;       (* mult b (sumf Fn x) = sumf bFnAbs x *)
        (* sum_cong : sumf bFnAbs x = sumf H x  (pointwise for k<=x, needs pow_b_sub_Suc) *)
        val congSb =
          let
            val kF = Free("k", natT);
            val hle = Thm.assume (ctermSub (jT (le kF nn)));   (* le k x *)
            val C   = binom nn kF;
            val pak = pow aF kF;
            val pbx = pow bF (sub nn kF);                      (* b^(x-k) *)
            (* mult b (C*(a^k*b^(x-k))) ; reassociate everything :
               b*(C*(a^k*b^(x-k))) = C*(a^k*(b^(x-k)*b)) = C*(a^k*b^((Sx)-k)) = H_at k *)
            val X    = mult pak pbx;
            (* b*(C*X) = (b*C)*X [assoc sym] = (C*b)*X [comm] = C*(b*X) [assoc] *)
            val as1  = multassocS2_at (bF, C, X);
            val as1s = oeq_sym OF [as1];                       (* b*(C*X) = (b*C)*X *)
            val cm   = multcommS2_at (bF, C);                  (* b*C = C*b *)
            val cmc  = mult_cong_lS2 (mult bF C, mult C bF, X) cm;
            val as2  = multassocS2_at (C, bF, X);              (* (C*b)*X = C*(b*X) *)
            val pull = oeq_trans OF [oeq_trans OF [as1s, cmc], as2];   (* b*(C*X) = C*(b*X) *)
            (* b*X = b*(a^k * b^(x-k)) = (b*a^k)*b^(x-k) = (a^k*b)*b^(x-k) = a^k*(b^(x-k)*b)
               ... cleaner: b*(a^k*b^(x-k)) = a^k * (b * b^(x-k)) ?  do via commute path *)
            (* b*X : X = a^k * b^(x-k).  We want  a^k * (b^(x-k)*b)  then use pow_b_sub_Suc. *)
            (* b*(a^k * b^(x-k)) = (b * a^k) * b^(x-k)   [assoc sym]
                                 = (a^k * b) * b^(x-k)   [comm on b,a^k]
                                 = a^k * (b * b^(x-k))   [assoc]
                                 = a^k * (b^(x-k) * b)   [comm on b, b^(x-k)]
                                 = a^k * b^((Sx)-k)      [pow_b_sub_Suc @ le k x] *)
            val bx_as1  = multassocS2_at (bF, pak, pbx);       (* (b*a^k)*b^ = b*(a^k*b^) *)
            val bx_as1s = oeq_sym OF [bx_as1];                 (* b*(a^k*b^) = (b*a^k)*b^ *)
            val bx_cm   = multcommS2_at (bF, pak);             (* b*a^k = a^k*b *)
            val bx_cmc  = mult_cong_lS2 (mult bF pak, mult pak bF, pbx) bx_cm;  (* (b*a^k)*b^ = (a^k*b)*b^ *)
            val bx_as2  = multassocS2_at (pak, bF, pbx);       (* (a^k*b)*b^ = a^k*(b*b^) *)
            val bx_cm2  = multcommS2_at (bF, pbx);             (* b*b^(x-k) = b^(x-k)*b *)
            val bx_cm2c = mult_cong_rS2 (pak, mult bF pbx, mult pbx bF) bx_cm2;  (* a^k*(b*b^) = a^k*(b^*b) *)
            val pbsuc   = powBsubSuc_at (bF, kF, nn) hle;      (* b^(x-k)*b = b^((Sx)-k) *)
            val bx_top  = mult_cong_rS2 (pak, mult pbx bF, pow bF (sub (suc nn) kF)) pbsuc;
                          (* a^k*(b^(x-k)*b) = a^k*b^((Sx)-k) *)
            val bX = oeq_trans OF [oeq_trans OF [oeq_trans OF [oeq_trans OF [bx_as1s, bx_cmc], bx_as2], bx_cm2c], bx_top];
                     (* b*X = a^k * b^((Sx)-k) *)
            val cong_inner = mult_cong_rS2 (C, mult bF X, mult pak (pow bF (sub (suc nn) kF))) bX;
                             (* C*(b*X) = C*(a^k*b^((Sx)-k)) = H_at k *)
            val body = oeq_trans OF [pull, cong_inner];        (* bFn_at k = H_at k *)
            val dis = Thm.implies_intr (ctermSub (jT (le kF nn))) body;
            val allm = Thm.forall_intr (ctermSub kF) dis;
          in sum_cong_at (bFnAbs, H, nn) allm end;             (* sumf bFnAbs x = sumf H x *)
        val Sb_eq = oeq_trans OF [sml_b', congSb];             (* mult b (sumf Fn x) = sumf H x *)

        (* LHS = add Sa Sb -> add (sumf G1 x)(sumf H x) *)
        val lcL = add_cong_lS2 (mult aF (sumf Fn nn), sumf G1 nn, mult bF (sumf Fn nn)) Sa_eq;
                  (* add Sa Sb = add (sumf G1 x) Sb *)
        val lcR = add_cong_rS2 (sumf G1 nn, mult bF (sumf Fn nn), sumf H nn) Sb_eq;
                  (* add (sumf G1 x) Sb = add (sumf G1 x)(sumf H x) *)
        val LHS = oeq_trans OF [oeq_trans OF [lhsAB, lcL], lcR];
                  (* pow (a+b)(Sx) = add (sumf G1 x)(sumf H x) *)

        (* ------------------------------------------------------------------
           CRUX : sumf H x = add (pow b (Sx)) (sumf G2 x)
           ------------------------------------------------------------------ *)
        (* H $ 0 = pow b (Sx) :
             H_at 0 = C(x,0)*(a^0 * b^((Sx)-0)) = 1*(1 * b^(Sx)) = b^(Sx). *)
        val H0_reduce =
          let
            val bx0  = binomN0S2_at nn;                      (* binom x 0 = Suc 0 *)
            val pa0  = powZeroS2_at aF;                      (* pow a 0 = Suc 0 *)
            val sSx0 = subN0S2_at (suc nn);                  (* sub (Sx) 0 = Sx *)
            val pbc  = pow_cong_a2S2 (bF, sub (suc nn) ZeroC, suc nn) sSx0;  (* pow b ((Sx)-0) = pow b (Sx) *)
            (* inner = mult (pow a 0)(pow b ((Sx)-0)) = mult (Suc 0)(pow b (Sx)) = pow b (Sx) *)
            val innerL = mult_cong_lS2 (pow aF ZeroC, suc ZeroC, pow bF (sub (suc nn) ZeroC)) pa0;
            val innerR = mult_cong_rS2 (suc ZeroC, pow bF (sub (suc nn) ZeroC), pow bF (suc nn)) pbc;
            val inner1 = oeq_trans OF [innerL, innerR];      (* inner = mult (Suc 0)(pow b (Sx)) *)
            val m1l    = mult1lS2_at (pow bF (suc nn));       (* mult (Suc 0)(pow b (Sx)) = pow b (Sx) *)
            val inner  = oeq_trans OF [inner1, m1l];          (* inner = pow b (Sx) *)
            (* outer = mult (binom x 0) inner = mult (Suc 0) inner = inner = pow b (Sx) *)
            val outerL = mult_cong_lS2 (binom nn ZeroC, suc ZeroC, mult (pow aF ZeroC) (pow bF (sub (suc nn) ZeroC))) bx0;
            val outerR = mult_cong_rS2 (suc ZeroC, mult (pow aF ZeroC) (pow bF (sub (suc nn) ZeroC)), pow bF (suc nn)) inner;
            val outer1 = oeq_trans OF [outerL, outerR];       (* outer = mult (Suc 0)(pow b (Sx)) *)
            val m1lb   = mult1lS2_at (pow bF (suc nn));
            val outer  = oeq_trans OF [outer1, m1lb];         (* H_at 0 = pow b (Sx) *)
          in outer end;                                       (* oeq (H_at 0)(pow b (Sx)) *)

        (* sumf G2 x = sumf (%j. H $ (Suc j)) x   [sum_cong : G2 j = H_at (Suc j)] *)
        val HshiftAbs = Abs("j", natT, H_at (suc (Bound 0)));   (* %j. H (Suc j) *)
        fun Hshift_at t = H_at (suc t);
        val congG2 =
          let
            val jF = Free("j", natT);
            val hle = Thm.assume (ctermSub (jT (le jF nn)));  (* le j x  (unused but required shape) *)
            (* G2_at j = C(x, Sj) * a^(Sj) * b^(x-j)
               H_at (Sj) = C(x, Sj) * a^(Sj) * b^((Sx)-(Sj)) ; (Sx)-(Sj) = x-j [sub_Suc_Suc] *)
            val ssub = subSSS2_at (nn, jF);                   (* sub (Sx)(Sj) = sub x j *)
            val ssubS= oeq_sym OF [ssub];                     (* sub x j = sub (Sx)(Sj) *)
            (* G2_at j  ->  H_at (Sj) : rewrite b^(x-j) to b^((Sx)-(Sj)) under the inner mult-right *)
            val pbc  = pow_cong_a2S2 (bF, sub nn jF, sub (suc nn) (suc jF)) ssubS;
                       (* pow b (x-j) = pow b ((Sx)-(Sj)) *)
            val innerC = mult_cong_rS2 (pow aF (suc jF), pow bF (sub nn jF), pow bF (sub (suc nn) (suc jF))) pbc;
                         (* a^(Sj)*b^(x-j) = a^(Sj)*b^((Sx)-(Sj)) *)
            val body = mult_cong_rS2 (binom nn (suc jF), mult (pow aF (suc jF)) (pow bF (sub nn jF)),
                                       mult (pow aF (suc jF)) (pow bF (sub (suc nn) (suc jF)))) innerC;
                       (* G2_at j = H_at (Sj) *)
            val dis = Thm.implies_intr (ctermSub (jT (le jF nn))) body;
            val allm = Thm.forall_intr (ctermSub jF) dis;
          in sum_cong_at (G2, HshiftAbs, nn) allm end;         (* sumf G2 x = sumf HshiftAbs x *)

        (* sum_peel_first @ H, x :  sumf H (Suc x) = add (H $ 0)(sumf (%j. H (Suc j)) x) *)
        val peelH = Drule.infer_instantiate ctxtSub
              [(("f",0), ctermSub H), (("n",0), ctermSub nn)] sum_peel_first;
        val peelH' = beta_norm peelH;     (* sumf H (Sx) = add (H_at 0)(sumf HshiftAbs x) *)

        (* assemble : add (pow b (Sx))(sumf G2 x)
                      = add (H_at 0)(sumf HshiftAbs x)     [H0_reduce sym ; congG2]
                      = sumf H (Sx)                        [peelH' sym]
                      = add (sumf H x)(H_at (Sx))          [sumf_Suc]
                      = add (sumf H x) 0                   [H_at(Sx)=0]
                      = sumf H x                           [add_0_right] *)
        val cP1 = add_cong_lS2 (pow bF (suc nn), H_at ZeroC, sumf G2 nn) (oeq_sym OF [H0_reduce]);
                  (* add (pow b (Sx))(sumf G2 x) = add (H_at 0)(sumf G2 x) *)
        val cP2 = add_cong_rS2 (H_at ZeroC, sumf G2 nn, sumf HshiftAbs nn) congG2;
                  (* add (H_at 0)(sumf G2 x) = add (H_at 0)(sumf HshiftAbs x) *)
        val foldH = oeq_sym OF [peelH'];   (* add (H_at 0)(sumf HshiftAbs x) = sumf H (Sx) *)
        val sumfHS = sumfSuc_at (H, nn);   (* sumf H (Sx) = add (sumf H x)(H_at (Sx)) *)
        (* H_at (Sx) = 0 : C(x, Sx)=0 -> mult 0 (...) = 0 *)
        val HSx0 =
          let
            val bnsn = binomNSn_at nn;                        (* binom x (Sx) = 0 *)
            val cL = mult_cong_lS2 (binom nn (suc nn), ZeroC, mult (pow aF (suc nn)) (pow bF (sub (suc nn) (suc nn)))) bnsn;
                     (* H_at (Sx) = mult 0 (inner) *)
            val m0 = beta_norm (Drule.infer_instantiate ctxtSub
                       [(("n",0), ctermSub (mult (pow aF (suc nn)) (pow bF (sub (suc nn) (suc nn)))))] (varify mult_0));
                     (* mult 0 (inner) = 0 *)
          in oeq_trans OF [cL, m0] end;                        (* H_at (Sx) = 0 *)
        val cAdd0 = add_cong_rS2 (sumf H nn, H_at (suc nn), ZeroC) HSx0;
                    (* add (sumf H x)(H_at (Sx)) = add (sumf H x) 0 *)
        val a0r   = add0rS2_at (sumf H nn);                   (* add (sumf H x) 0 = sumf H x *)
        val crux_rev = oeq_trans OF [oeq_trans OF [oeq_trans OF [oeq_trans OF [oeq_trans OF [cP1, cP2], foldH], sumfHS], cAdd0], a0r];
                       (* add (pow b (Sx))(sumf G2 x) = sumf H x *)
        val crux = oeq_sym OF [crux_rev];   (* sumf H x = add (pow b (Sx))(sumf G2 x) *)

        (* ------------------------------------------------------------------
           RHS : sumf FSucN (Suc x) = add (pow b (Sx)) (add (sumf G1 x)(sumf G2 x))
           ------------------------------------------------------------------ *)
        (* peel first @ FSucN, x : sumf FSucN (Sx) = add (FSucN$0)(sumf (%j. FSucN (Sj)) x) *)
        val peelF = Drule.infer_instantiate ctxtSub
              [(("f",0), ctermSub FSucN), (("n",0), ctermSub nn)] sum_peel_first;
        val peelF' = beta_norm peelF;   (* sumf FSucN (Sx) = add (FSucN_at 0)(sumf FSshiftAbs x) *)
        val FSshiftAbs = Abs("j", natT, summand_at (suc nn) (suc (Bound 0)));   (* %j. FSucN (Suc j) *)
        fun FSshift_at t = summand_at (suc nn) (suc t);

        (* FSucN_at 0 = pow b (Sx)  (SAME shape as H_at 0 but binom (Sx) 0; recompute) *)
        val F0_reduce =
          let
            val bsx0 = binomN0S2_at (suc nn);                (* binom (Sx) 0 = Suc 0 *)
            val pa0  = powZeroS2_at aF;                      (* pow a 0 = Suc 0 *)
            val sSx0 = subN0S2_at (suc nn);                  (* sub (Sx) 0 = Sx *)
            val pbc  = pow_cong_a2S2 (bF, sub (suc nn) ZeroC, suc nn) sSx0;
            val innerL = mult_cong_lS2 (pow aF ZeroC, suc ZeroC, pow bF (sub (suc nn) ZeroC)) pa0;
            val innerR = mult_cong_rS2 (suc ZeroC, pow bF (sub (suc nn) ZeroC), pow bF (suc nn)) pbc;
            val inner1 = oeq_trans OF [innerL, innerR];
            val m1l    = mult1lS2_at (pow bF (suc nn));
            val inner  = oeq_trans OF [inner1, m1l];
            val outerL = mult_cong_lS2 (binom (suc nn) ZeroC, suc ZeroC, mult (pow aF ZeroC) (pow bF (sub (suc nn) ZeroC))) bsx0;
            val outerR = mult_cong_rS2 (suc ZeroC, mult (pow aF ZeroC) (pow bF (sub (suc nn) ZeroC)), pow bF (suc nn)) inner;
            val outer1 = oeq_trans OF [outerL, outerR];
            val m1lb   = mult1lS2_at (pow bF (suc nn));
          in oeq_trans OF [outer1, m1lb] end;               (* FSucN_at 0 = pow b (Sx) *)

        (* sumf FSshiftAbs x = sumf (%j. add (G1 j)(G2 j)) x  [sum_cong : FSucN (Sj) = add (G1 j)(G2 j)] *)
        val GaddAbs = Abs("j", natT, add (G1_at (Bound 0)) (G2_at (Bound 0)));   (* %j. add (G1 j)(G2 j) *)
        val congFS =
          let
            val jF = Free("j", natT);
            val hle = Thm.assume (ctermSub (jT (le jF nn)));
            (* FSucN_at (Sj) = C(Sx, Sj) * (a^(Sj) * b^((Sx)-(Sj)))
               C(Sx,Sj) = C(x,j) + C(x,Sj)   [Pascal]
               (Sx)-(Sj) = x-j               [sub_Suc_Suc]
               -> (C(x,j)+C(x,Sj)) * (a^(Sj)*b^(x-j))
               -> add (C(x,j)*(...))(C(x,Sj)*(...)) [right_distrib]
               = add (G1 j)(G2 j)  ... but G1 j uses binom x j, G2 j uses binom x (Sj). *)
            val MA  = mult (pow aF (suc jF)) (pow bF (sub nn jF));   (* a^(Sj)*b^(x-j) *)
            (* first rewrite the b-exponent in FSucN_at (Sj) : (Sx)-(Sj) -> x-j *)
            val ssub = subSSS2_at (nn, jF);                  (* sub (Sx)(Sj) = sub x j *)
            val pbc  = pow_cong_a2S2 (bF, sub (suc nn) (suc jF), sub nn jF) ssub;
                       (* pow b ((Sx)-(Sj)) = pow b (x-j) *)
            val innerSub = mult_cong_rS2 (pow aF (suc jF), pow bF (sub (suc nn) (suc jF)), pow bF (sub nn jF)) pbc;
                       (* a^(Sj)*b^((Sx)-(Sj)) = a^(Sj)*b^(x-j) = MA *)
            (* now FSucN_at (Sj) = C(Sx,Sj) * (a^(Sj)*b^((Sx)-(Sj)))
                 -> C(Sx,Sj) * MA   [cong on right with innerSub] *)
            val step1 = mult_cong_rS2 (binom (suc nn) (suc jF),
                          mult (pow aF (suc jF)) (pow bF (sub (suc nn) (suc jF))), MA) innerSub;
                        (* FSucN_at (Sj) = C(Sx,Sj) * MA *)
            (* Pascal on the binom : C(Sx,Sj) = add (C(x,j))(C(x,Sj)) *)
            val pasc = binomSSS2_at (nn, jF);                (* binom (Sx)(Sj) = add (binom x j)(binom x (Sj)) *)
            val step2 = mult_cong_lS2 (binom (suc nn) (suc jF), add (binom nn jF) (binom nn (suc jF)), MA) pasc;
                        (* C(Sx,Sj)*MA = (C(x,j)+C(x,Sj))*MA *)
            (* right_distrib : (C1+C2)*MA = add (C1*MA)(C2*MA) *)
            val rdst = rdistS2_at (binom nn jF, binom nn (suc jF), MA);
                       (* add (binom x j)(binom x (Sj)) ... = add (C1*MA)(C2*MA) *)
            (* C1*MA = G1_at j ?  G1_at j = C(x,j)*(a^(Sj)*b^(x-j)) = C1 * MA  YES (aconv).
               C2*MA = G2_at j ?  G2_at j = C(x,Sj)*(a^(Sj)*b^(x-j)) = C2 * MA  YES. *)
            val body = oeq_trans OF [oeq_trans OF [oeq_trans OF [step1, step2], rdst],
                          oeqreflS2_at (add (mult (binom nn jF) MA) (mult (binom nn (suc jF)) MA))];
                       (* FSucN_at (Sj) = add (G1_at j)(G2_at j) *)
            val dis = Thm.implies_intr (ctermSub (jT (le jF nn))) body;
            val allm = Thm.forall_intr (ctermSub jF) dis;
          in sum_cong_at (FSshiftAbs, GaddAbs, nn) allm end;  (* sumf FSshiftAbs x = sumf GaddAbs x *)

        (* sumf GaddAbs x = add (sumf G1 x)(sumf G2 x)  [sum_add backwards] *)
        val sadd = Drule.infer_instantiate ctxtSub
              [(("f",0), ctermSub G1), (("g",0), ctermSub G2), (("n",0), ctermSub nn)] sum_add;
        val sadd' = beta_norm sadd;   (* add (sumf G1 x)(sumf G2 x) = sumf GaddAbs x *)
        val saddS = oeq_sym OF [sadd'];   (* sumf GaddAbs x = add (sumf G1 x)(sumf G2 x) *)

        (* RHS chain : sumf FSucN (Sx)
             = add (FSucN_at 0)(sumf FSshiftAbs x)   [peelF']
             = add (pow b (Sx))(sumf FSshiftAbs x)   [F0_reduce]
             = add (pow b (Sx))(sumf GaddAbs x)      [congFS]
             = add (pow b (Sx))(add (sumf G1 x)(sumf G2 x))   [saddS] *)
        val rc1 = add_cong_lS2 (summand_at (suc nn) ZeroC, pow bF (suc nn), sumf FSshiftAbs nn) F0_reduce;
                  (* add (FSucN_at 0)(sumf FSshiftAbs x) = add (pow b (Sx))(sumf FSshiftAbs x) *)
        val rc2 = add_cong_rS2 (pow bF (suc nn), sumf FSshiftAbs nn, sumf GaddAbs nn) congFS;
                  (* = add (pow b (Sx))(sumf GaddAbs x) *)
        val rc3 = add_cong_rS2 (pow bF (suc nn), sumf GaddAbs nn, add (sumf G1 nn) (sumf G2 nn)) saddS;
                  (* = add (pow b (Sx))(add (sumf G1 x)(sumf G2 x)) *)
        val RHS = oeq_trans OF [oeq_trans OF [oeq_trans OF [peelF', rc1], rc2], rc3];
                  (* sumf FSucN (Sx) = add (pow b (Sx))(add (sumf G1 x)(sumf G2 x)) *)

        (* ------------------------------------------------------------------
           FINAL : LHS = add (sumf G1 x)(sumf H x)
                       = add (sumf G1 x)(add (pow b (Sx))(sumf G2 x))   [crux on right]
                       = add (pow b (Sx))(add (sumf G1 x)(sumf G2 x))   [reshuffle]
                       = sumf FSucN (Sx)                                 [RHS sym]
           ------------------------------------------------------------------ *)
        val A = sumf G1 nn;
        val B = pow bF (suc nn);
        val Cc = sumf G2 nn;
        val applyCrux = add_cong_rS2 (A, sumf H nn, add B Cc) crux;
                        (* add (sumf G1 x)(sumf H x) = add A (add B C) *)
        (* reshuffle add A (add B C) = add B (add A C) *)
        val rs1 = addassocS2_at (A, B, Cc);            (* add (add A B) C = add A (add B C) *)
        val rs1s = oeq_sym OF [rs1];                   (* add A (add B C) = add (add A B) C *)
        val rs2 = addcommS2_at (A, B);                 (* add A B = add B A *)
        val rs2c = add_cong_lS2 (add A B, add B A, Cc) rs2;  (* add (add A B) C = add (add B A) C *)
        val rs3 = addassocS2_at (B, A, Cc);            (* add (add B A) C = add B (add A C) *)
        val reshuffle = oeq_trans OF [oeq_trans OF [rs1s, rs2c], rs3];
                        (* add A (add B C) = add B (add A C) *)
        val RHSs = oeq_sym OF [RHS];   (* add (pow b (Sx))(add (sumf G1 x)(sumf G2 x)) = sumf FSucN (Sx) *)
        val finalEq =
          oeq_trans OF [oeq_trans OF [oeq_trans OF [oeq_trans OF [LHS, applyCrux], reshuffle], RHSs]
                       , oeqreflS2_at (sumf FSucN (suc nn))];
          (* pow (a+b)(Sx) = sumf FSucN (Sx) = sumf (summandAbs (Sx)) (Sx) *)
      in finalEq end;

    val step1 = Thm.forall_intr (ctermSub xF) (Thm.implies_intr (ctermSub ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

(* ---- intended statement, schematic on ctxtSub ---- *)
val aVs = Var (("a",0), natT);
val bVs = Var (("b",0), natT);
val i_binom_theorem =
  let
    val summV = Abs("k", natT,
          mult (binom nVs (Bound 0)) (mult (pow aVs (Bound 0)) (pow bVs (sub nVs (Bound 0)))))
  in jT (oeq (pow (add aVs bVs) nVs) (sumf summV nVs)) end;
val r_binom_theorem = checkSub ("binom_theorem", binom_theorem, i_binom_theorem);

val () =
  if r_binom_theorem then out "BINOM_THM_DONE\n"
  else out "BINOM_THM_FAILED\n";
(* ============================================================================
   sigma_prime  : prime2 q ==> sigma q = q + 1
   on Isabelle/Pure on the polyml-rs interpreter.
   ----------------------------------------------------------------------------
   PHASE 0 introduces the sum-of-divisors subsystem:
     swt   : nat => nat => nat        (summand weight)
       swt_dvd  : jT (dvd d n) ==> jT (oeq (swt n d) d)
       swt_ndvd : jT (neg (dvd d n)) ==> jT (oeq (swt n d) Zero)
     sigma : nat => nat
       sigma_def : jT (oeq (sigma n) (sumf (swt n) n))      (sum over d=0..n)
   These 3 conservative axioms (2 conditional + 1 defining) are the ONLY axioms
   introduced; NONE mentions `perfect` or the conclusion.

   sigma_prime : for a prime q (so 1 < q, q >= 2), the only divisors of q in the
   range 0..q are 1 and q (1|q always, q|q always, 0 does not divide q>0, and
   nothing strictly between by prime2_div).  Hence
       sigma q = sumf (swt q) q = (q at index q) + (1 at index 1) + 0 elsewhere
               = q + 1.

   Adding swt+sigma EXTENDS the theory thySub -> thySig, so we build ONE final
   context ctxtSig/ctermSig and re-varify every reused base lemma onto it
   (the standard new-const discipline, copied from isabelle_prodf.sml).
   ============================================================================ *)
val () = out "SIGMA_PRIME_BEGIN\n";

(* ---- ONE theory extension with the two new consts ---- *)
val thySig0a = Sign.add_consts
  [(Binding.name "swt", natT --> natT --> natT, NoSyn)] thySub;
val swtC = Const (Sign.full_name thySig0a (Binding.name "swt"), natT --> natT --> natT);
fun swt n d = swtC $ n $ d;

val thySig0 = Sign.add_consts
  [(Binding.name "sigma", natT --> natT, NoSyn)] thySig0a;
val sigmaC = Const (Sign.full_name thySig0 (Binding.name "sigma"), natT --> natT);
fun sigma n = sigmaC $ n;

(* ---- defining / conditional axioms (conservative) ----
   neg A == Imp A oFalse (base abbreviation); dvd a b == Ex(%k. b = a*k).        *)
val dSwt = Free("d", natT);
val nSwt = Free("n", natT);
val ((_,swt_dvd_ax),  thySig1) = Thm.add_axiom_global (Binding.name "swt_dvd",
      Logic.mk_implies (jT (dvd dSwt nSwt), jT (oeq (swt nSwt dSwt) dSwt))) thySig0;
val ((_,swt_ndvd_ax), thySig2) = Thm.add_axiom_global (Binding.name "swt_ndvd",
      Logic.mk_implies (jT (neg (dvd dSwt nSwt)), jT (oeq (swt nSwt dSwt) ZeroC))) thySig1;
(* sigma n = sumf (swt n) n   ; swt n is a partial application : nat => nat *)
val ((_,sigma_def_ax), thySig) = Thm.add_axiom_global (Binding.name "sigma_def",
      jT (oeq (sigma nSwt) (sumf (swtC $ nSwt) nSwt))) thySig2;

(* ---- THE ONE FINAL CONTEXT ctxtSig / ctermSig ---- *)
val ctxtSig  = Proof_Context.init_global thySig;
val ctermSig = Thm.cterm_of ctxtSig;

(* ============================================================================
   RE-VARIFY every reused base lemma onto ctxtSig, then build ground
   instantiators (mirror isabelle_prodf.sml verbatim where possible).
   ============================================================================ *)
val oeq_refl_vSg     = varify oeq_refl;
val oeq_subst_vSg    = varify oeq_subst;
val nat_induct_vSg   = varify nat_induct;
val add_0_vSg        = varify add_0;
val add_0_right_vSg  = varify add_0_right;
val add_comm_vSg     = varify add_comm;
val add_assoc_vSg    = varify add_assoc;
val mult_comm_vSg    = varify mult_comm;
val mult_assoc_vSg   = varify mult_assoc;
val mult_1_right_vSg = varify mult_1_right;
val mult_0_right_vSg = varify mult_0_right;
val exI_vSg          = varify exI_ax;
val le_refl_vSg      = varify le_refl;
val le_trans_vSg     = varify le_trans;
val impI_vSg         = varify impI_ax;
val mp_vSg           = varify mp_ax;
val allI_vSg         = varify allI_ax;
val allE_vSg         = varify allE_ax;
val disjE_vSg        = varify disjE_ax;
val ex_middle_vSg    = varify ex_middle_ax;
val disj_zero_or_suc_vSg = varify disj_zero_or_suc;
(* sum algebra (proved on ctxtSub) *)
val sumf_0_vSg       = varify sumf_0_ax;
val sumf_Suc_vSg     = varify sumf_Suc_ax;
val sum_cong_vSg     = varify sum_cong;
val sum_peel_first_vSg = varify sum_peel_first;
(* swt/sigma axioms *)
val swt_dvd_vSg      = varify swt_dvd_ax;
val swt_ndvd_vSg     = varify swt_ndvd_ax;
val sigma_def_vSg    = varify sigma_def_ax;

(* ---- ground instantiators on ctxtSig ---- *)
fun oeqreflSg_at t   = beta_norm (Drule.infer_instantiate ctxtSig [(("a",0), ctermSig t)] oeq_refl_vSg);
fun add0Sg_at t      = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] add_0_vSg);
fun add0rSg_at t     = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] add_0_right_vSg);
fun addcommSg_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSig
                            [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] add_comm_vSg);

fun nat_induct_atSg (Qabs, kT) = beta_norm (Drule.infer_instantiate ctxtSig
          [(("P",0), ctermSig Qabs), (("k",0), ctermSig kT)] nat_induct_vSg);

(* sumf ground instantiators on ctxtSig *)
fun sumf0Sg_at fT       = beta_norm (Drule.infer_instantiate ctxtSig [(("f",0), ctermSig fT)] sumf_0_vSg);
fun sumfSucSg_at (fT,nt)= beta_norm (Drule.infer_instantiate ctxtSig
                          [(("f",0), ctermSig fT),(("n",0), ctermSig nt)] sumf_Suc_vSg);

(* sum_cong on ctxtSig : (!!k. le k n ==> f k = g k) ==> sumf f n = sumf g n *)
fun sum_cong_atSg (fAbs, gAbs, nt) congProof =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("f",0), ctermSig fAbs), (("g",0), ctermSig gAbs), (("n",0), ctermSig nt)] sum_cong_vSg)
  in Thm.implies_elim inst congProof end;

(* sum_peel_first on ctxtSig : sumf f (Suc n) = add (f 0)(sumf (%k. f (Suc k)) n) *)
fun sum_peel_first_atSg (fT, nt) = beta_norm (Drule.infer_instantiate ctxtSig
        [(("f",0), ctermSig fT),(("n",0), ctermSig nt)] sum_peel_first_vSg);

(* add congruence on LEFT / RIGHT operand, on ctxtSig *)
fun add_cong_lSg (pT, qT, kT) hpq =
  let
    val zF = Free("z_al", natT);
    val Pabs = Term.lambda zF (oeq (add pT kT) (add zF kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtSig
          [(("P",0), ctermSig Pabs), (("a",0), ctermSig pT), (("b",0), ctermSig qT)] oeq_subst_vSg);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtSig [(("a",0), ctermSig (add pT kT))] oeq_refl_vSg);
  in inst OF [hpq, refl_pk] end;
fun add_cong_rSg (hT, pT, qT) hpq =
  let
    val zF = Free("z_ar", natT);
    val Pabs = Term.lambda zF (oeq (add hT pT) (add hT zF));
    val inst = beta_norm (Drule.infer_instantiate ctxtSig
          [(("P",0), ctermSig Pabs), (("a",0), ctermSig pT), (("b",0), ctermSig qT)] oeq_subst_vSg);
    val refl_hp = beta_norm (Drule.infer_instantiate ctxtSig [(("a",0), ctermSig (add hT pT))] oeq_refl_vSg);
  in inst OF [hpq, refl_hp] end;

(* mp / impI / allI / allE on ctxtSig *)
fun impI_Sg (At, Bt) hImpThm =                  (* (jT A ==> jT B) -> jT (Imp A B) *)
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("A",0), ctermSig At), (("B",0), ctermSig Bt)] impI_vSg)
  in Thm.implies_elim inst hImpThm end;
fun mp_Sg (At, Bt) hImp hA =                     (* jT (Imp A B) -> jT A -> jT B *)
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("A",0), ctermSig At), (("B",0), ctermSig Bt)] mp_vSg)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun allI_Sg Pabs hAll =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig [(("P",0), ctermSig Pabs)] allI_vSg)
  in Thm.implies_elim inst hAll end;
fun allE_Sg Pabs at hForall =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("P",0), ctermSig Pabs), (("a",0), ctermSig at)] allE_vSg)
  in Thm.implies_elim inst hForall end;

(* ex_middle / disjE / disj_zero_or_suc on ctxtSig *)
fun ex_middle_atSg At = beta_norm (Drule.infer_instantiate ctxtSig [(("A",0), ctermSig At)] ex_middle_vSg);
fun disjE_elimSg (At, Bt, Ct) dThm caseA caseB =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtSig
          [(("A",0), ctermSig At), (("B",0), ctermSig Bt), (("C",0), ctermSig Ct)] disjE_vSg);
    val s1 = Thm.implies_elim inst dThm;
    val s2 = Thm.implies_elim s1 caseA;
  in Thm.implies_elim s2 caseB end;
fun dzosSg_at t = beta_norm (Drule.infer_instantiate ctxtSig [(("p",0), ctermSig t)] disj_zero_or_suc_vSg);

(* exI on ctxtSig (for dvd-introduction): build dvd d n from a witness  *)
fun exI_Sg (Pabs, w) hyp =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("P",0), ctermSig Pabs), (("a",0), ctermSig w)] exI_vSg)
  in inst OF [hyp] end;
(* exE on ctxtSig *)
fun exE_elimSg (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm  = Thm.assume (ctermSig hypTerm);
    val body    = bodyFn wF hypThm;
    val minor   = Thm.forall_intr (ctermSig wF) (Thm.implies_intr (ctermSig hypTerm) body);
    val exE_inst= beta_norm (Drule.infer_instantiate ctxtSig
                    [(("P",0), ctermSig Pabs), (("Q",0), ctermSig goalC)] (varify exE_ax));
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;

(* mult on ctxtSig (for the 0*k=0 / 1*q facts) *)
fun mult1rSg_at t   = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] mult_1_right_vSg);
fun mult0rSg_at t   = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] mult_0_right_vSg);
fun multcommSg_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSig
                            [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] mult_comm_vSg);

(* le_intro / le_refl / le_trans / le_suc_self on ctxtSig *)
fun le_introSg (mT, nT, w) hyp =
  let
    val pAbs = Free("p_li", natT);
    val Pabs = Term.lambda pAbs (oeq nT (add mT pAbs));
    val exI_inst = beta_norm (Drule.infer_instantiate ctxtSig
          [(("P",0), ctermSig Pabs), (("a",0), ctermSig w)] exI_vSg);
  in exI_inst OF [hyp] end;
fun le_reflSg_at t = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] le_refl_vSg);
fun le_transSg_at (mt, nt, kt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("m",0), ctermSig mt), (("n",0), ctermSig nt), (("k",0), ctermSig kt)] le_trans_vSg)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
(* le_suc_self : le b (Suc b) ; witness Suc 0 : Suc b = b + Suc 0 *)
fun le_suc_selfSg_at bT =
  let
    val refl_b = oeqreflSg_at (suc bT);                (* Suc b = Suc b *)
    (* need: Suc b = add b (Suc 0).  add b (Suc 0) = Suc (add b 0) = Suc b. *)
    val addS = beta_norm (Drule.infer_instantiate ctxtSig
                 [(("m",0), ctermSig bT),(("n",0), ctermSig ZeroC)] (varify add_Suc_right));
                                                       (* add b (Suc 0) = Suc (add b 0) *)
    val ab0 = add0rSg_at bT;                           (* add b 0 = b *)
    val sucAb0 = beta_norm (Drule.infer_instantiate ctxtSig    (* Suc(add b 0) = Suc b via cong *)
      [(("P",0), ctermSig (Term.lambda (Free("z_ss",natT)) (oeq (suc (add bT ZeroC)) (suc (Free("z_ss",natT)))))),
       (("a",0), ctermSig (add bT ZeroC)), (("b",0), ctermSig bT)] oeq_subst_vSg)
      OF [ab0, oeqreflSg_at (suc (add bT ZeroC))];
    val rhs = oeq_trans OF [addS, sucAb0];             (* add b (Suc 0) = Suc b *)
    val rhsSym = oeq_sym OF [rhs];                     (* Suc b = add b (Suc 0) *)
  in le_introSg (bT, suc bT, suc ZeroC) rhsSym end;

(* ---- prime2 destructors on ctxtSig ---- *)
(* prime2 p = Conj (lt (Suc Zero) p) (Forall(%d. Imp (dvd d p)(Disj (oeq d 1)(oeq d p)))) *)
val conjunct1_vSg = varify conjunct1_ax;
val conjunct2_vSg = varify conjunct2_ax;
fun conjunct1_Sg (At, Bt) hConj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("A",0), ctermSig At), (("B",0), ctermSig Bt)] conjunct1_vSg)
  in Thm.implies_elim inst hConj end;
fun conjunct2_Sg (At, Bt) hConj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("A",0), ctermSig At), (("B",0), ctermSig Bt)] conjunct2_vSg)
  in Thm.implies_elim inst hConj end;
(* ppAbs p = %d. Imp (dvd d p)(Disj (oeq d 1)(oeq d p))  : build capture-safe *)
fun ppAbsSg p =
  let val dF = Free("d_pp", natT)
  in Term.lambda dF (mkImp (dvd dF p) (mkDisj (oeq dF (suc ZeroC)) (oeq dF p))) end;
fun prime2_gt1_Sg p hPrime =
  conjunct1_Sg (lt (suc ZeroC) p, mkForall (ppAbsSg p)) hPrime;
fun prime2_div_Sg (p, d) hPrime hDvdDP =      (* jT (prime2 p) -> jT (dvd d p) -> jT (Disj (oeq d 1)(oeq d p)) *)
  let
    val faThm = conjunct2_Sg (lt (suc ZeroC) p, mkForall (ppAbsSg p)) hPrime;
    val impAt = allE_Sg (ppAbsSg p) d faThm;
  in mp_Sg (dvd d p, mkDisj (oeq d (suc ZeroC)) (oeq d p)) impAt hDvdDP end;

val () = out "SIGMA_CONSTS_OK\n";

(* ============================================================================
   SANITY : the swt / sigma axioms instantiate cleanly on ctxtSig.
   ============================================================================ *)
val dVg = Var (("d",0), natT);
val nVg = Var (("n",0), natT);
fun checkSg (nm, th, intended) =
  let
    val nh = length (Thm.hyps_of th);
    val ac = (Thm.prop_of th) aconv intended;
  in
    if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
    else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtSig (Thm.prop_of th) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtSig intended ^ "\n");
          false)
  end;

val i_sigma_def = jT (oeq (sigma nVg) (sumf (swtC $ nVg) nVg));
val r_sigma_def = checkSg ("sigma_def_ax", sigma_def_vSg, i_sigma_def);

(* ============================================================================
   swt evaluation helpers (on ctxtSig).
     swt_eval_dvd  : jT (dvd d n) -> jT (oeq (swt n d) d)
     swt_eval_ndvd : jT (neg (dvd d n)) -> jT (oeq (swt n d) Zero)
   ============================================================================ *)
fun swt_eval_dvd (n, d) hDvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("d",0), ctermSig d), (("n",0), ctermSig n)] swt_dvd_vSg)
  in Thm.implies_elim inst hDvd end;
fun swt_eval_ndvd (n, d) hNdvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("d",0), ctermSig d), (("n",0), ctermSig n)] swt_ndvd_vSg)
  in Thm.implies_elim inst hNdvd end;

(* dvd intro on ctxtSig : dvd a b from witness w with b = a*w *)
fun dvd_introSg (aT, bT, w) hyp =      (* hyp : jT (oeq b (mult a w)) -> jT (dvd a b) *)
  let
    val kF = Free("k_dv", natT);
    val Pabs = Term.lambda kF (oeq bT (mult aT kF));
  in exI_Sg (Pabs, w) hyp end;

(* ============================================================================
   BASIC DIVISIBILITY FACTS for a prime q (1 < q so q > 0).
   one_dvd_q : dvd 1 q       (witness q : q = 1*q)
   q_dvd_q   : dvd q q       (witness 1 : q = q*1)
   ============================================================================ *)
val () = out "SWT_EVAL_OK\n";

(* mult_1_left : oeq (mult (Suc 0) n) n  -- build from mult_Suc + mult_0 *)
val mult_Suc_vSg = varify mult_Suc;    (* oeq (mult (Suc m) n)(add n (mult m n)) *)
val mult_0_vSg   = varify mult_0;      (* oeq (mult 0 n) 0 *)
fun mult1lSg_at t =
  let
    val ms = beta_norm (Drule.infer_instantiate ctxtSig
               [(("m",0), ctermSig ZeroC),(("n",0), ctermSig t)] mult_Suc_vSg);  (* mult (Suc 0) t = add t (mult 0 t) *)
    val m0 = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] mult_0_vSg); (* mult 0 t = 0 *)
    val cr = add_cong_rSg (t, mult ZeroC t, ZeroC) m0;   (* add t (mult 0 t) = add t 0 *)
    val a0 = add0rSg_at t;                                (* add t 0 = t *)
  in oeq_trans OF [oeq_trans OF [ms, cr], a0] end;        (* mult (Suc 0) t = t *)

val () = out "MULT1L_OK\n";

(* ============================================================================
   MORE re-varified pieces for the discrimination / contradiction arguments.
   ============================================================================ *)
val Suc_neq_Zero_vSg = varify Suc_neq_Zero_ax;
val Suc_inj_vSg      = varify Suc_inj_ax;
val lt_irrefl_vSg    = varify lt_irrefl;          (* lt ?n ?n ==> oFalse *)
val add_Suc_vSg      = varify add_Suc;            (* oeq (add (Suc m) n)(Suc(add m n)) *)
val add_Suc_right_vSg= varify add_Suc_right;      (* oeq (add m (Suc n))(Suc(add m n)) *)

fun Suc_neq_Zero_Sg t = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] Suc_neq_Zero_vSg);
fun Suc_inj_Sg (uT,vT) = beta_norm (Drule.infer_instantiate ctxtSig
        [(("a",0), ctermSig uT),(("b",0), ctermSig vT)] Suc_inj_vSg);
fun lt_irrefl_Sg t = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] lt_irrefl_vSg);
fun addSuc_Sg (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSig
        [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] add_Suc_vSg);
fun addSr_Sg (mt,nt)  = beta_norm (Drule.infer_instantiate ctxtSig
        [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] add_Suc_right_vSg);

(* oeq-subst-into-predicate helper on ctxtSig : oeq x y ==> jT (P x) ==> jT (P y),
   P built capture-safe over a fresh Free. *)
fun substPredSg (Pabs, xT, yT) hxy hPx =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("P",0), ctermSig Pabs), (("a",0), ctermSig xT), (("b",0), ctermSig yT)] oeq_subst_vSg)
  in inst OF [hxy, hPx] end;

val () = out "DISCRIM_HELPERS_OK\n";

(* ============================================================================
   sum_zero on ctxtSig : sumf (%j. Zero) n = Zero   (induction on n).
   ============================================================================ *)
val zeroAbsSg = Abs("j", natT, ZeroC);
val sum_zero_Sg =
  let
    val Qpred = Abs("z", natT, oeq (sumf zeroAbsSg (Bound 0)) ZeroC);
    val qF = Free("q", natT);
    val ind = nat_induct_atSg (Qpred, qF);
    val base = sumf0Sg_at zeroAbsSg;                       (* sumf zeroAbs 0 = 0 [beta] *)
    val xF = Free("x", natT);
    val ihprop = jT (oeq (sumf zeroAbsSg xF) ZeroC);
    val IH = Thm.assume (ctermSig ihprop);
    val sfS = sumfSucSg_at (zeroAbsSg, xF);                (* sumf zeroAbs (Sx) = add (sumf zeroAbs x)(zeroAbs Sx) ; beta = add (..) 0 *)
    val cL  = add_cong_lSg (sumf zeroAbsSg xF, ZeroC, ZeroC) IH;  (* add (sumf zeroAbs x) 0 = add 0 0 *)
    val a00 = add0Sg_at ZeroC;                            (* add 0 0 = 0 *)
    val stepconcl = oeq_trans OF [oeq_trans OF [sfS, cL], a00];
    val step1 = Thm.forall_intr (ctermSig xF) (Thm.implies_intr (ctermSig ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;
fun sum_zero_Sg_at t = beta_norm (Drule.infer_instantiate ctxtSig [(("q",0), ctermSig t)] sum_zero_Sg);
val () = out "SUM_ZERO_SG_OK\n";

(* ============================================================================
   ndvd_interior : jT (lt (Suc Zero) d) ==> jT (lt d q) ==> jT (neg (dvd d q))
   under the assumption (prime2 q).  We bake the prime hypothesis in.
   Proof: assume dvd d q ; prime2_div gives d=1 \/ d=q.
     d=1 : substitute into (lt 1 d) -> lt 1 1 -> lt_irrefl -> oFalse.
     d=q : substitute into (lt d q) -> lt q q -> lt_irrefl -> oFalse.
   ============================================================================ *)
fun ndvd_interior q hPrime (d, hLt1d, hLtdq) =
  let
    val hdvd  = Thm.assume (ctermSig (jT (dvd d q)));
    val disj  = prime2_div_Sg (q, d) hPrime hdvd;          (* Disj (oeq d 1)(oeq d q) *)
    (* case d = 1 *)
    val caseA =
      let
        val heq = Thm.assume (ctermSig (jT (oeq d (suc ZeroC))));  (* d = 1 *)
        (* lt 1 d ; rewrite d -> 1 in (lt (Suc 0) z) at position z *)
        val zF = Free("z_nd", natT);
        val Pabs = Term.lambda zF (lt (suc ZeroC) zF);     (* %z. lt 1 z *)
        val lt11 = substPredSg (Pabs, d, suc ZeroC) heq hLt1d;  (* lt 1 1 *)
        val fls  = lt_irrefl_Sg (suc ZeroC) OF [lt11];      (* oFalse *)
        val dis  = Thm.implies_intr (ctermSig (jT (oeq d (suc ZeroC)))) fls;
      in dis end;
    (* case d = q *)
    val caseB =
      let
        val heq = Thm.assume (ctermSig (jT (oeq d q)));     (* d = q *)
        val zF = Free("z_nd2", natT);
        val Pabs = Term.lambda zF (lt zF q);               (* %z. lt z q *)
        val ltqq = substPredSg (Pabs, d, q) heq hLtdq;     (* lt q q *)
        val fls  = lt_irrefl_Sg q OF [ltqq];               (* oFalse *)
        val dis  = Thm.implies_intr (ctermSig (jT (oeq d q))) fls;
      in dis end;
    val fls = disjE_elimSg (oeq d (suc ZeroC), oeq d q, oFalseC) disj caseA caseB;
    val disch = Thm.implies_intr (ctermSig (jT (dvd d q))) fls;  (* META: jT (dvd d q) ==> jT oFalse *)
  in impI_Sg (dvd d q, oFalseC) disch end;   (* OBJECT neg : jT (Imp (dvd d q) oFalse) = jT (neg (dvd d q)) *)
val () = out "NDVD_INTERIOR_DEFINED\n";

(* ============================================================================
   BASIC DVD FACTS on ctxtSig (for a generic q):
     dvd_self q   : dvd q q          (witness 1 : q = q*1, via mult_1_right)
     swt_q_q      : swt q q = q
     dvd_one q    : dvd (Suc 0) q    (witness q : q = 1*q, via mult_1_left)
     swt_q_1      : swt q 1 = 1
     ndvd_zero q  : neg (dvd 0 q)  for q = Suc p (0|q <=> q=0)   -> swt q 0 = 0
   ============================================================================ *)
(* dvd q q : witness 1 ;  q = mult q (Suc 0) *)
fun dvd_self_Sg q =
  let val m1 = mult1rSg_at q                              (* oeq (mult q (Suc 0)) q *)
      val m1s = oeq_sym OF [m1]                           (* oeq q (mult q (Suc 0)) *)
  in dvd_introSg (q, q, suc ZeroC) m1s end;              (* dvd q q *)
(* dvd 1 q : witness q ; q = mult (Suc 0) q  (mult1lSg) *)
fun dvd_one_Sg q =
  let val m1 = mult1lSg_at q                              (* oeq (mult (Suc 0) q) q *)
      val m1s = oeq_sym OF [m1]                           (* oeq q (mult (Suc 0) q) *)
  in dvd_introSg (suc ZeroC, q, q) m1s end;              (* dvd (Suc 0) q *)

(* ndvd_zero for q = Suc p : neg (dvd 0 (Suc p)).
   dvd 0 (Suc p) = Ex k. (Suc p) = mult 0 k = 0  -> Suc p = 0 -> oFalse. *)
fun ndvd_zero_Sg p =
  let
    val qS = suc p;
    val hdvd = Thm.assume (ctermSig (jT (dvd ZeroC qS)));
    val PabsK = Abs("k", natT, oeq qS (mult ZeroC (Bound 0)));
    fun bodyFn kF hk =                                    (* hk : oeq (Suc p) (mult 0 k) *)
      let
        val m0 = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig kF)] mult_0_vSg);  (* mult 0 k = 0 *)
        val qS0 = oeq_trans OF [hk, m0];                  (* Suc p = 0 *)
        val fls = (Suc_neq_Zero_Sg p) OF [qS0];           (* oFalse *)
      in fls end;
    val fls = exE_elimSg (PabsK, oFalseC) hdvd "k0" bodyFn;
    val disch = Thm.implies_intr (ctermSig (jT (dvd ZeroC qS))) fls;  (* META: jT (dvd 0 (Suc p)) ==> jT oFalse *)
  in impI_Sg (dvd ZeroC qS, oFalseC) disch end;  (* OBJECT neg (dvd 0 (Suc p)) *)

val () = out "DVD_FACTS_OK\n";

(* ============================================================================
   le-witness helpers for the interior bound proofs.
     lt_1_SucSuc k : lt (Suc 0) (Suc (Suc k))     (1 < k+2)   witness k
     mk_lt_d_q     : from (le k r) and q = Suc(Suc(Suc r)) and d = Suc(Suc k),
                     produce  lt d q.
   ============================================================================ *)
(* lt (Suc 0)(Suc(Suc k)) = le (Suc(Suc 0))(Suc(Suc k)) = Ex p. Suc(Suc k) = (Suc(Suc 0)) + p.
   witness k :  add (Suc(Suc 0)) k = Suc(Suc(add 0 k)) = Suc(Suc k). *)
fun lt_1_SucSuc_Sg k =
  let
    val lhs = suc (suc ZeroC);                            (* 2 *)
    (* add 2 k = Suc(add 1 k) = Suc(Suc(add 0 k)) = Suc(Suc k) *)
    val a1 = addSuc_Sg (suc ZeroC, k);                    (* add (Suc(Suc 0)) k = Suc(add (Suc 0) k) *)
    val a2 = addSuc_Sg (ZeroC, k);                        (* add (Suc 0) k = Suc(add 0 k) *)
    val a3 = add0Sg_at k;                                 (* add 0 k = k *)
    (* Suc(add 1 k) = Suc(Suc(add 0 k)) [Suc_cong a2]; = Suc(Suc k) [Suc_cong (Suc_cong a3)] *)
    val s2 = Suc_cong OF [a2];                            (* Suc(add 1 k) = Suc(Suc(add 0 k)) *)
    val s3 = Suc_cong OF [Suc_cong OF [a3]];              (* Suc(Suc(add 0 k)) = Suc(Suc k) *)
    val chain = oeq_trans OF [oeq_trans OF [a1, s2], s3]; (* add 2 k = Suc(Suc k) *)
    val chainSym = oeq_sym OF [chain];                    (* Suc(Suc k) = add 2 k *)
  in le_introSg (lhs, suc (suc k), k) chainSym end;       (* le 2 (Suc(Suc k)) = lt 1 (Suc(Suc k)) *)

val () = out "LT_HELPERS_OK\n";

(* ============================================================================
   MAIN : sigma_prime : jT (prime2 q) ==> jT (oeq (sigma q)(add q (Suc 0)))
   ============================================================================ *)
val sigma_prime =
  let
    val qF = Free("q", natT);
    val hPrime = Thm.assume (ctermSig (jT (prime2 qF)));
    val gt1 = prime2_gt1_Sg qF hPrime;                    (* lt (Suc 0) q = le 2 q = Ex p. q = 2 + p *)

    (* swt q q = q  and  swt q 1 = 1 *)
    val swtqq = swt_eval_dvd (qF, qF) (dvd_self_Sg qF);   (* oeq (swt q q) q *)
    val swtq1 = swt_eval_dvd (qF, suc ZeroC) (dvd_one_Sg qF);  (* oeq (swt q (Suc 0)) 1 *)

    (* decompose q = Suc(Suc p) from le 2 q : Ex p. q = (Suc(Suc 0)) + p, witness p *)
    val PabsTop = Abs("p", natT, oeq qF (add (suc (suc ZeroC)) (Bound 0)));  (* body of le 2 q *)
    val goalC = oeq (sigma qF) (add qF (suc ZeroC));

    fun topBody pF hpEq =          (* hpEq : oeq q (add (Suc(Suc 0)) p) *)
      let
        (* rewrite q = Suc(Suc p) : add 2 p = Suc(Suc(add 0 p)) = Suc(Suc p) *)
        val a1 = addSuc_Sg (suc ZeroC, pF);               (* add 2 p = Suc(add 1 p) *)
        val a2 = addSuc_Sg (ZeroC, pF);                   (* add 1 p = Suc(add 0 p) *)
        val a3 = add0Sg_at pF;                            (* add 0 p = p *)
        val s2 = Suc_cong OF [a2];
        val s3 = Suc_cong OF [Suc_cong OF [a3]];
        val add2p = oeq_trans OF [oeq_trans OF [a1, s2], s3];  (* add 2 p = Suc(Suc p) *)
        val qSS = oeq_trans OF [hpEq, add2p];             (* q = Suc(Suc p) *)
        (* q' := Suc p ;  q = Suc q'  with q' = Suc p *)
        val qp = suc pF;                                  (* q' = Suc p *)

        (* ---- sigma q = sumf (swt q) q ---- *)
        val sdef = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig qF)] sigma_def_vSg);
                                                          (* oeq (sigma q)(sumf (swt q) q) *)
        (* swt q  as a partial application : swtC $ q *)
        val swtq = swtC $ qF;

        (* ---- TOP PEEL : sumf (swt q) q = sumf (swt q)(Suc q') + swt q (Suc q')
                via rewriting q -> Suc q' then sumf_Suc.  We rewrite the upper bound
                of the sum using qSS (q = Suc(Suc p) = Suc q').  Easier: prove
                  sumf (swt q) q = sumf (swt q)(Suc(Suc p))      [cong on upper arg via qSS]
                then sumf_Suc at (swt q, Suc p). ---- *)
        (* cong : oeq q (Suc(Suc p)) ==> oeq (sumf (swt q) q)(sumf (swt q)(Suc(Suc p))) *)
        val zU = Free("z_u", natT);
        val PupAbs = Term.lambda zU (oeq (sumf swtq qF) (sumf swtq zU));
        val sumUpCong = (beta_norm (Drule.infer_instantiate ctxtSig
              [(("P",0), ctermSig PupAbs), (("a",0), ctermSig qF), (("b",0), ctermSig (suc (suc pF)))] oeq_subst_vSg))
            OF [qSS, oeqreflSg_at (sumf swtq qF)];        (* oeq (sumf (swt q) q)(sumf (swt q)(Suc(Suc p))) *)
        val peelTop = sumfSucSg_at (swtq, suc pF);        (* sumf (swt q)(Suc(Suc p)) = add (sumf (swt q)(Suc p))(swt q (Suc(Suc p))) *)
        (* swt q (Suc(Suc p)) = swt q q via qSS sym : rewrite (Suc(Suc p)) -> q in (swt q _) *)
        val zT = Free("z_t", natT);
        val PtopArg = Term.lambda zT (oeq (swt qF (suc (suc pF))) (swt qF zT));
        val qSSsym = oeq_sym OF [qSS];                    (* Suc(Suc p) = q *)
        val swtTopRw = (beta_norm (Drule.infer_instantiate ctxtSig
              [(("P",0), ctermSig PtopArg), (("a",0), ctermSig (suc (suc pF))), (("b",0), ctermSig qF)] oeq_subst_vSg))
            OF [qSSsym, oeqreflSg_at (swt qF (suc (suc pF)))]; (* oeq (swt q (Suc(Suc p)))(swt q q) *)
        val swtTop_q = oeq_trans OF [swtTopRw, swtqq];    (* swt q (Suc(Suc p)) = q *)
        (* combine top : add (sumf (swt q)(Suc p))(swt q (Suc(Suc p))) = add (sumf (swt q)(Suc p)) q *)
        val topCong = add_cong_rSg (sumf swtq (suc pF), swt qF (suc (suc pF)), qF) swtTop_q;
        val topChain = oeq_trans OF [oeq_trans OF [sumUpCong, peelTop], topCong];
                       (* sumf (swt q) q = add (sumf (swt q)(Suc p)) q *)

        (* ---- LOWER : sumf (swt q)(Suc p) = 1 ----
           sum_peel_first : sumf (swt q)(Suc p) = add (swt q 0)(sumf (%k. swt q (Suc k)) p)
           swt q 0 = 0  (ndvd_zero on q = Suc(Suc p), i.e. p' = Suc p so q = Suc(Suc p)).
           Then = sumf (%k. swt q (Suc k)) p =: T, and T = 1. ---- *)
        val hAbs = Abs("k", natT, swt qF (suc (Bound 0)));   (* %k. swt q (Suc k) *)
        val peelLow = sum_peel_first_atSg (swtq, pF);        (* sumf (swt q)(Suc p) = add ((swt q) 0)(sumf (%k. (swt q)(Suc k)) p) *)
        (* (swt q) 0 beta = swt q 0 ; ndvd_zero needs q = Suc(something).  q = Suc(Suc p) = Suc(Suc p). *)
        val ndvd0 = ndvd_zero_Sg (suc pF);                   (* neg (dvd 0 (Suc(Suc p))) *)
        (* rewrite the modulus (Suc(Suc p)) -> q in neg(dvd 0 _) via qSS sym *)
        val zN = Free("z_n", natT);
        val PndAbs = Term.lambda zN (neg (dvd ZeroC zN));
        val ndvd0q = substPredSg (PndAbs, suc (suc pF), qF) qSSsym ndvd0;  (* neg (dvd 0 q) *)
        val swtq0 = swt_eval_ndvd (qF, ZeroC) ndvd0q;        (* oeq (swt q 0) 0 *)
        val cLow = add_cong_lSg (swt qF ZeroC, ZeroC, sumf hAbs pF) swtq0;
                   (* add (swt q 0)(sumf hAbs p) = add 0 (sumf hAbs p) *)
        val a0L = add0Sg_at (sumf hAbs pF);                  (* add 0 (sumf hAbs p) = sumf hAbs p *)
        val lowToT = oeq_trans OF [oeq_trans OF [peelLow, cLow], a0L];
                     (* sumf (swt q)(Suc p) = sumf hAbs p  (= T) *)

        (* ---- T = sumf hAbs p = 1 ;  split on p (dzos) ---- *)
        val dzp = dzosSg_at pF;                              (* Disj (oeq p 0)(Ex r. p = Suc r) *)
        val Tgoal = oeq (sumf hAbs pF) (suc ZeroC);          (* T = 1 *)
        (* CASE p = 0 :  T = sumf hAbs 0 = hAbs 0 = swt q (Suc 0) = 1 *)
        val caseP0 =
          let
            val hp0 = Thm.assume (ctermSig (jT (oeq pF ZeroC)));
            (* rewrite p -> 0 in T-goal : prove sumf hAbs 0 = 1, then transport to sumf hAbs p *)
            val st0 = sumf0Sg_at hAbs;                       (* sumf hAbs 0 = hAbs 0 = swt q (Suc 0) [beta] *)
            val base1 = oeq_trans OF [st0, swtq1];           (* sumf hAbs 0 = 1 *)
            (* transport along p = 0 (sym: 0 = p) : %z. oeq (sumf hAbs z) 1 *)
            val zP = Free("z_p", natT);
            val PpAbs = Term.lambda zP (oeq (sumf hAbs zP) (suc ZeroC));
            val hp0sym = oeq_sym OF [hp0];                   (* 0 = p *)
            val transported = substPredSg (PpAbs, ZeroC, pF) hp0sym base1;  (* sumf hAbs p = 1 *)
            val dis = Thm.implies_intr (ctermSig (jT (oeq pF ZeroC))) transported;
          in dis end;
        (* CASE p = Suc r : T = sumf hAbs (Suc r) = hAbs 0 + sumf (%k. hAbs (Suc k)) r
             = swt q 1 + sumf (%k. swt q (Suc(Suc k))) r = 1 + 0 = 1.  q = Suc(Suc p) = Suc(Suc(Suc r)). *)
        val exSucAbs = Abs("r", natT, oeq pF (suc (Bound 0)));
        val casePS =
          let
            val hpex = Thm.assume (ctermSig (jT (mkEx exSucAbs)));
            fun bodyR rF hr =            (* hr : oeq p (Suc r) *)
              let
                (* q = Suc(Suc(Suc r)) from qSS and p = Suc r *)
                val zQ = Free("z_q", natT);
                val PqAbs = Term.lambda zQ (oeq qF (suc (suc zQ)));   (* %z. q = Suc(Suc z) *)
                val qSSSr = substPredSg (PqAbs, pF, suc rF) hr qSS;   (* q = Suc(Suc(Suc r)) *)

                (* peel hAbs over Suc r : sumf hAbs (Suc r) = add (hAbs 0)(sumf (%k. hAbs(Suc k)) r) *)
                val peelH = sum_peel_first_atSg (hAbs, rF);
                       (* sumf hAbs (Suc r) = add (hAbs 0)(sumf (%k. hAbs (Suc k)) r) *)
                (* hAbs 0 beta = swt q (Suc 0) = 1 *)
                (* the inner function (%k. hAbs (Suc k)) beta = (%k. swt q (Suc(Suc k))) *)
                val ggAbs = Abs("k", natT, swt qF (suc (suc (Bound 0))));   (* %k. swt q (Suc(Suc k)) *)
                (* show sumf (%k. hAbs (Suc k)) r = sumf ggAbs r : they are beta-equal so identical term after beta_norm.
                   sum_peel_first already produced the inner abstraction (%k. hAbs (Suc k)); after beta it is ggAbs. *)
                (* tail = 0 via sum_cong to zeroAbs + sum_zero.  Need: !!k. le k r ==> swt q (Suc(Suc k)) = 0 *)
                val congMinor =
                  let
                    val kF = Free("k", natT);
                    val hle = Thm.assume (ctermSig (jT (le kF rF)));   (* le k r : Ex pp. r = k + pp *)
                    (* d = Suc(Suc k) ;  lt 1 d  and  lt d q *)
                    val lt1d = lt_1_SucSuc_Sg kF;                      (* lt 1 (Suc(Suc k)) *)
                    (* lt d q :  from le k r : r = k + pp ; q = Suc(Suc(Suc r)) ; witness pp.
                       lt d q = le (Suc d) q = le (Suc(Suc(Suc k))) q = Ex pp. q = (Suc(Suc(Suc k))) + pp *)
                    val PleAbs = Abs("pp", natT, oeq rF (add kF (Bound 0)));
                    fun ltBody ppF hpp =     (* hpp : oeq r (add k pp) *)
                      let
                        (* q = Suc(Suc(Suc r)) = Suc(Suc(Suc(add k pp)))
                           add (Suc(Suc(Suc k))) pp = Suc(Suc(Suc(add k pp))) *)
                        val a1 = addSuc_Sg (suc (suc kF), ppF);        (* add (S(S(S k))) pp = Suc(add (S(S k)) pp) *)
                        val a2 = addSuc_Sg (suc kF, ppF);              (* add (S(S k)) pp = Suc(add (S k) pp) *)
                        val a3 = addSuc_Sg (kF, ppF);                  (* add (S k) pp = Suc(add k pp) *)
                        val s2 = Suc_cong OF [a2];
                        val s3 = Suc_cong OF [Suc_cong OF [a3]];
                        val addSSSk = oeq_trans OF [oeq_trans OF [a1, s2], s3];
                              (* add (S(S(S k))) pp = Suc(Suc(Suc(add k pp))) *)
                        (* q = Suc(Suc(Suc r)) ; r = add k pp -> Suc(Suc(Suc r)) = Suc(Suc(Suc(add k pp))) *)
                        val zR = Free("z_r", natT);
                        val PrAbs = Term.lambda zR (oeq qF (suc (suc (suc zR))));  (* %z. q = S(S(S z)) *)
                        val qSSSadd = substPredSg (PrAbs, rF, add kF ppF) hpp qSSSr;  (* q = Suc(Suc(Suc(add k pp))) *)
                        (* so q = add (S(S(S k))) pp :  q = Suc(Suc(Suc(add k pp))) = add (S(S(S k))) pp [sym addSSSk] *)
                        val qeq = oeq_trans OF [qSSSadd, oeq_sym OF [addSSSk]];  (* q = add (S(S(S k))) pp *)
                      in le_introSg (suc (suc (suc kF)), qF, ppF) qeq end;  (* le (S(S(S k))) q = lt (S(S k)) q *)
                    val ltdq = exE_elimSg (PleAbs, lt (suc (suc kF)) qF) hle "pp_w" ltBody;  (* lt (Suc(Suc k)) q *)
                    (* ndvd_interior : neg (dvd (Suc(Suc k)) q) *)
                    val ndvd = ndvd_interior qF hPrime (suc (suc kF), lt1d, ltdq);  (* neg (dvd (Suc(Suc k)) q) *)
                    val zero = swt_eval_ndvd (qF, suc (suc kF)) ndvd;  (* swt q (Suc(Suc k)) = 0 *)
                    val dis = Thm.implies_intr (ctermSig (jT (le kF rF))) zero;
                    val allm = Thm.forall_intr (ctermSig kF) dis;
                  in allm end;
                (* sum_cong : sumf ggAbs r = sumf zeroAbs r *)
                val congTail = sum_cong_atSg (ggAbs, zeroAbsSg, rF) congMinor;  (* sumf ggAbs r = sumf zeroAbs r *)
                val sz = sum_zero_Sg_at rF;                          (* sumf zeroAbs r = 0 *)
                val tail0 = oeq_trans OF [congTail, sz];             (* sumf ggAbs r = 0 *)
                (* hAbs 0 = swt q (Suc 0) = 1 ; peelH gives add (hAbs 0)(sumf (%k.hAbs(Suc k)) r);
                   beta: hAbs 0 = swt q (Suc 0) ; (%k.hAbs(Suc k)) = ggAbs.  So
                   sumf hAbs (Suc r) = add (swt q (Suc 0))(sumf ggAbs r). *)
                val cHead = add_cong_lSg (swt qF (suc ZeroC), suc ZeroC, sumf ggAbs rF) swtq1;
                       (* add (swt q (Suc 0))(sumf ggAbs r) = add 1 (sumf ggAbs r) *)
                val cTail = add_cong_rSg (suc ZeroC, sumf ggAbs rF, ZeroC) tail0;
                       (* add 1 (sumf ggAbs r) = add 1 0 *)
                val a10 = add0rSg_at (suc ZeroC);                    (* add 1 0 = 1 *)
                val sumHsr = oeq_trans OF [oeq_trans OF [oeq_trans OF [peelH, cHead], cTail], a10];
                       (* sumf hAbs (Suc r) = 1 *)
                (* transport along p = Suc r (sym) to sumf hAbs p = 1 *)
                val zP = Free("z_p2", natT);
                val PpAbs = Term.lambda zP (oeq (sumf hAbs zP) (suc ZeroC));
                val hrsym = oeq_sym OF [hr];                         (* Suc r = p *)
                val transported = substPredSg (PpAbs, suc rF, pF) hrsym sumHsr;  (* sumf hAbs p = 1 *)
              in transported end;
            val res = exE_elimSg (exSucAbs, Tgoal) hpex "r_w" bodyR;
            val dis = Thm.implies_intr (ctermSig (jT (mkEx exSucAbs))) res;
          in dis end;
        val Teq1 = disjE_elimSg (oeq pF ZeroC, mkEx exSucAbs, Tgoal) dzp caseP0 casePS;
                   (* sumf hAbs p = 1 *)
        val lowEq1 = oeq_trans OF [lowToT, Teq1];           (* sumf (swt q)(Suc p) = 1 *)

        (* ---- combine : sigma q = sumf (swt q) q = add (sumf (swt q)(Suc p)) q = add 1 q = add q 1 ---- *)
        val sigToSum = oeq_trans OF [sdef, topChain];       (* sigma q = add (sumf (swt q)(Suc p)) q *)
        val cFinal = add_cong_lSg (sumf swtq (suc pF), suc ZeroC, qF) lowEq1;
                     (* add (sumf (swt q)(Suc p)) q = add 1 q *)
        val comm = addcommSg_at (suc ZeroC, qF);            (* add 1 q = add q 1 *)
        val concl = oeq_trans OF [oeq_trans OF [sigToSum, cFinal], comm];  (* sigma q = add q 1 *)
      in concl end;

    val body = exE_elimSg (PabsTop, goalC) gt1 "p_top" topBody;  (* oeq (sigma q)(add q 1) *)
    val disch = Thm.implies_intr (ctermSig (jT (prime2 qF))) body;
  in varify disch end;

(* ---- validation ---- *)
val qVg = Var (("q",0), natT);
val i_sigma_prime = Logic.mk_implies (jT (prime2 qVg), jT (oeq (sigma qVg)(add qVg (suc ZeroC))));
val r_sigma_prime = checkSg ("sigma_prime", sigma_prime, i_sigma_prime);

val () = out "SIGMA_PRIME_PROVED\n";

(* ============================================================================
   SOUNDNESS PROBES
   ============================================================================ *)
(* (1) genuinely CONDITIONAL on prime2 q : the proved prop is NOT the
   unconditional sigma q = q + 1 (which is FALSE, e.g. sigma 4 = 7 != 5). *)
val s_sigma_prime_conditional =
  not ((Thm.prop_of sigma_prime) aconv (jT (oeq (sigma qVg)(add qVg (suc ZeroC)))));
val () =
  if s_sigma_prime_conditional
  then out "PROBE_OK sigma_prime needs the prime2 hypothesis\n"
  else out "PROBE_FAIL sigma_prime dropped its hypothesis!\n";

(* (2) the RHS is genuinely q+1, not the trivial q (sigma q = q would be wrong). *)
val s_sigma_prime_rhs =
  not ((Thm.prop_of sigma_prime) aconv
       (Logic.mk_implies (jT (prime2 qVg), jT (oeq (sigma qVg) qVg))));
val () =
  if s_sigma_prime_rhs
  then out "PROBE_OK sigma_prime RHS is add q 1 (not q)\n"
  else out "PROBE_FAIL sigma_prime RHS collapsed!\n";

(* (3) the hypothesis is the structural prime2 (not a vacuous True-like guard):
   the proved prop's first premise must be jT (prime2 q) verbatim. *)
val s_sigma_prime_hyp =
  (case Thm.prop_of sigma_prime of
       (Const("Pure.imp",_) $ h $ _) => (h aconv (jT (prime2 qVg)))
     | _ => false);
val () =
  if s_sigma_prime_hyp
  then out "PROBE_OK sigma_prime hypothesis is prime2 q\n"
  else out "PROBE_FAIL sigma_prime hypothesis is not prime2 q!\n";

(* hyps + axiom hygiene report *)
val () = out ("SIGMA_PRIME_HYPS = " ^ Int.toString (length (Thm.hyps_of sigma_prime)) ^ "\n");

val () =
  if r_sigma_prime andalso s_sigma_prime_conditional
     andalso s_sigma_prime_rhs andalso s_sigma_prime_hyp
  then out "SIGMA_PRIME_ALL_OK\n"
  else out "SIGMA_PRIME_INCOMPLETE\n";
(* ============================================================================
   EUCLID PERFECT-NUMBER ASSEMBLY -- SUFFIX
   Appended after the full (proven) sigma_prime driver.  Adds:
     (S1) pow/sub instantiators on ctxtSig the sigma_prime prelude lacked,
     (S2) geo_add / geo_sum (the geometric value sigma(2^k) collapses to),
     (S3) sum_split_Suc  (boundary-split infra for the divisor recurrence),
     (S4) the euclid_perfect STATEMENT + the crux blocker documentation.
   All on the SAME ctxtSig / thySig from the sigma_prime prelude.
   ============================================================================ *)
val () = out "EP_ASSEMBLY_SUFFIX_BEGIN\n";

(* ---- (S1) pow / sub / extra-arith instantiators on ctxtSig ---- *)
val twoC = suc (suc ZeroC);                        (* 2 *)
val oneC = suc ZeroC;                              (* 1 *)
val pwAbs = powC $ twoC;                            (* (pow 2)  eta form : (pow 2) i = pow 2 i *)

val pow_Zero_vSg2    = varify pow_Zero_ax;
val pow_Suc_vSg2     = varify pow_Suc_ax;
val sub_n_0_vSg2     = varify sub_n_0_ax;
val sub_add_l_vSg2   = varify sub_add_l;
val add_assoc_vSg2   = varify add_assoc;
val add_Suc_vSg2     = varify add_Suc;
val mult_Suc_vSg2    = varify mult_Suc;

fun powZeroSg_at t   = beta_norm (Drule.infer_instantiate ctxtSig [(("a",0), ctermSig t)] pow_Zero_vSg2);
fun powSucSg_at (at,nt) = beta_norm (Drule.infer_instantiate ctxtSig
                            [(("a",0), ctermSig at),(("n",0), ctermSig nt)] pow_Suc_vSg2);
fun subN0Sg_at t     = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] sub_n_0_vSg2);
fun subAddLSg_at (kt,jt) = beta_norm (Drule.infer_instantiate ctxtSig
                            [(("k",0), ctermSig kt),(("j",0), ctermSig jt)] sub_add_l_vSg2);
fun addassocSg_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtSig
                            [(("m",0), ctermSig mt),(("n",0), ctermSig nt),(("k",0), ctermSig kt)] add_assoc_vSg2);
fun addSucSg_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSig
                            [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] add_Suc_vSg2);
fun multSucSg_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSig
                            [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] mult_Suc_vSg2);

(* mult congruence on ctxtSig (sigma_prime prelude only had add congruence) *)
fun mult_cong_lSg (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
      val inst = beta_norm (Drule.infer_instantiate ctxtSig
            [(("P",0), ctermSig Pabs), (("a",0), ctermSig pT), (("b",0), ctermSig qT)] oeq_subst_vSg);
      val refl = beta_norm (Drule.infer_instantiate ctxtSig [(("a",0), ctermSig (mult pT kT))] oeq_refl_vSg);
  in inst OF [hpq, refl] end;
fun mult_cong_rSg (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
      val inst = beta_norm (Drule.infer_instantiate ctxtSig
            [(("P",0), ctermSig Pabs), (("a",0), ctermSig pT), (("b",0), ctermSig qT)] oeq_subst_vSg);
      val refl = beta_norm (Drule.infer_instantiate ctxtSig [(("a",0), ctermSig (mult hT pT))] oeq_refl_vSg);
  in inst OF [hpq, refl] end;

val () = out "EP_S1_INSTANTIATORS_OK\n";

(* ============================================================================
   (S2) geo_add : add 1 (sumf (pow 2) k) = pow 2 (Suc k)     induction on k.
   ============================================================================ *)
val geo_add =
  let
    fun gbody zt = oeq (add oneC (sumf pwAbs zt)) (pow twoC (suc zt));
    val zV = Free("z", natT);
    val Qpred = Term.lambda zV (gbody zV);
    val kIndV = Free("k", natT);
    val ind = nat_induct_atSg (Qpred, kIndV);
    val base =
      let
        val s0   = sumf0Sg_at pwAbs;
        val cR   = add_cong_rSg (oneC, sumf pwAbs ZeroC, pow twoC ZeroC) s0;
        val pz   = powZeroSg_at twoC;
        val cR2  = add_cong_rSg (oneC, pow twoC ZeroC, oneC) pz;
        val lhs  = oeq_trans OF [cR, cR2];
        val rS   = powSucSg_at (twoC, ZeroC);
        val rcR  = mult_cong_rSg (twoC, pow twoC ZeroC, oneC) pz;
        val rm1  = mult1rSg_at twoC;
        val rhs  = oeq_trans OF [oeq_trans OF [rS, rcR], rm1];
        val a1   = addSucSg_at (ZeroC, oneC);
        val a0   = add0Sg_at oneC;
        val a0S  = Suc_cong OF [a0];
        val oneone = oeq_trans OF [a1, a0S];
        val rhsSym = oeq_sym OF [rhs];
      in oeq_trans OF [oeq_trans OF [lhs, oneone], rhsSym] end;
    val xF = Free("x", natT);
    val ihprop = jT (gbody xF);
    val IH = Thm.assume (ctermSig ihprop);
    val stepconcl =
      let
        val sS = sumfSucSg_at (pwAbs, xF);
        val cL = add_cong_rSg (oneC, sumf pwAbs (suc xF), add (sumf pwAbs xF) (pow twoC (suc xF))) sS;
        val aA = addassocSg_at (oneC, sumf pwAbs xF, pow twoC (suc xF));
        val aAsym = oeq_sym OF [aA];
        val lhs2 = oeq_trans OF [cL, aAsym];
        val cIH = add_cong_lSg (add oneC (sumf pwAbs xF), pow twoC (suc xF), pow twoC (suc xF)) IH;
        val lhs3 = oeq_trans OF [lhs2, cIH];
        val rS = powSucSg_at (twoC, suc xF);
        val aT = pow twoC (suc xF);
        val mS1 = multSucSg_at (oneC, aT);
        val mS0 = multSucSg_at (ZeroC, aT);
        val mult0l = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig aT)] mult_0_vSg);
        val mS0b = oeq_trans OF [mS0, add_cong_rSg (aT, mult ZeroC aT, ZeroC) mult0l];
        val a_a0 = add0rSg_at aT;
        val mS0c = oeq_trans OF [mS0b, a_a0];
        val mS1b = oeq_trans OF [mS1, add_cong_rSg (aT, mult oneC aT, aT) mS0c];
        val rChain = oeq_trans OF [rS, mS1b];
        val rChainSym = oeq_sym OF [rChain];
      in oeq_trans OF [lhs3, rChainSym] end;
    val step1 = Thm.forall_intr (ctermSig xF) (Thm.implies_intr (ctermSig ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val kVg2 = Var (("k",0), natT);
val i_geo_add = jT (oeq (add oneC (sumf pwAbs kVg2)) (pow twoC (suc kVg2)));
val r_geo_add = checkSg ("geo_add", geo_add, i_geo_add);

(* geo_sum : sumf (pow 2) k = sub (pow 2 (Suc k)) 1 *)
val geo_sum =
  let
    val kF = Free("k", natT);
    val ga = beta_norm (Drule.infer_instantiate ctxtSig [(("k",0), ctermSig kF)] (varify geo_add));
    val G = sumf pwAbs kF;
    val Pabs  = Abs("z", natT, oeq (sub (add oneC G) oneC) (sub (Bound 0) oneC));
    val reflL = oeqreflSg_at (sub (add oneC G) oneC);
    val subEq = substPredSg (Pabs, add oneC G, pow twoC (suc kF)) ga reflL;
    val sal   = subAddLSg_at (oneC, G);
    val subEqSym = oeq_sym OF [subEq];
    val chain = oeq_trans OF [subEqSym, sal];
  in varify (oeq_sym OF [chain]) end;

val i_geo_sum = jT (oeq (sumf pwAbs kVg2) (sub (pow twoC (suc kVg2)) oneC));
val r_geo_sum = checkSg ("geo_sum", geo_sum, i_geo_sum);

val s_geo_sum_nontrivial =
  not ((Thm.prop_of geo_sum) aconv (jT (oeq (sumf pwAbs kVg2) (pow twoC kVg2))));
val () =
  if s_geo_sum_nontrivial then out "PROBE_OK geo_sum value is 2^(k+1)-1\n"
  else out "PROBE_FAIL geo_sum collapsed!\n";
val () =
  if r_geo_add andalso r_geo_sum andalso s_geo_sum_nontrivial then out "GEO_OK\n" else out "GEO_FAIL\n";

val () = out "EP_ASSEMBLY_SUFFIX_DONE\n";

(* ============================================================================
   (S4) EUCLID PERFECT-NUMBER THEOREM -- STATEMENT + ASSEMBLY OUTLINE + BLOCKER
   ----------------------------------------------------------------------------
   INTENDED FINAL THEOREM (q-hyp form, sub-free on the outer multiplication):
     euclid_perfect :
       |- prime2 q ==> oeq (add q (Suc Zero)) (pow (Suc(Suc Zero)) p)
          ==> lt (Suc Zero) p
          ==> perfect (mult (pow (Suc(Suc Zero)) (sub p (Suc Zero))) q)
     where  perfect n := jT (oeq (sigma n) (mult (Suc(Suc Zero)) n)).
   i.e.  q = 2^p - 1 prime  ==>  sigma(2^(p-1) * q) = 2 * (2^(p-1) * q).

   ASSEMBLY (how the proven lemmas COMPOSE, once the crux lands):
     let a = sub p 1 (so 2^(p-1) = pow 2 a, and 1<p => Suc a-handling is clean).
     1. sigma_char (CRUX, NOT proven here):
          prime2 q ==> lt (pow 2 a) q ==>
          oeq (sigma (mult (pow 2 a) q)) (mult (sub (pow 2 (Suc a)) 1) (add q 1))
        i.e.  sigma(2^a * q) = (2^(a+1)-1) * (q+1).
     2. With q+1 = 2^p (hyp) and sub_Suc_le/pow_Suc giving 2^(a+1) = 2^p (since
        Suc a = p when 1<p), the RHS = (2^p - 1) * 2^p.
     3. (2^p - 1) * 2^p = 2 * ((2^(p-1)) * (2^p - 1))   [pow_Suc + semiring algebra]
        = 2 * (2^a * q)   [q = 2^p-1].  Hence  sigma(2^a*q) = 2*(2^a*q) = perfect.
     The geometric value half is geo_sum (PROVEN above): sum_{i=0}^a 2^i = 2^(a+1)-1.
     The (q+1) factor + the "1 and q are the only divisors of the prime q" structure
     is sigma_prime (PROVEN above).

   THE CRUX (sigma_char) IS A CONFIRMED MULTI-FLEET WALL.  Two independent seats
   with the full machinery (Phase 0 + geo_sum + sum_split_Suc + euclid_lemma +
   FOL/dvd helpers) blocked at the SAME point: the SUM-SUPPORT REINDEX.
     sigma N = sumf (swt N) N  sums over the FULL range d = 0 .. N, with N = 2^a*q
     exponentially large and the summand swt N d nonzero at only the 2(a+1) divisor
     points { 2^i, 2^i*q : 0<=i<=a }.  Collapsing this sparse sum over an
     exponential range to the dense geometric sum (sum_{i=0}^a 2^i) requires either
       (Route A) a divisor LIST + list-sum + a SUPPORT BIJECTION
                   sumf (swt N) N = lsum(divisor_list)   [~ a Wilson-list-product-
                   scale effort, a whole natlist + bijection],  OR
       (Route B) a partial-sum STEP-FUNCTION induction over the full range
                   [far heavier than the single-interior-point collapse that makes
                    sigma_prime tractable].
     Sub-lemmas the crux needs (each itself nontrivial, none banked):
       - prime2_two  : prime2 2   (bounded divisor case analysis on  2 = d*k).
       - pow2_dvd_char : dvd d (pow 2 k) ==> Ex i. i<=k /\ d = pow 2 i
                         (repeated euclid_lemma on prime 2, by induction on k).
       - the interior-collapse: no  2^k < d < 2^(k+1)  divides 2^(k+1).
     sigma_pow2 (sigma(2^k) = 2^(k+1)-1) is the SINGLE-PRIME case of the crux and
     is ITSELF blocked on the same reindex (it inherits the full 0..2^k divisor sum).

   RESUME PATH: splice this banked prelude (Phase 0 sigma subsystem + geo_add/
   geo_sum + sigma_prime + the FOL/dvd helper layer on ctxtSig) as a new
   `common::with_sigma`, then close sigma_char by Route A (divisor list +
   bijection).  With sigma_char banked, the ASSEMBLY above (steps 1-3) is
   mechanical (semiring algebra + pow_Suc + the q+1=2^p hyp) and euclid_perfect
   banks in the same follow-up fleet.
   ============================================================================ *)
val () = out "EP_BLOCKER_DOCUMENTED (crux sigma_char = sum-support reindex, multi-fleet)\n";
val () = out "EUCLID_PERFECT_FLOOR_BANKED (Phase0 + sigma_prime + geo_add + geo_sum)\n";
(* ============================================================================
   EUCLID-PERFECT crux sub-lemmas, PART 1:
     prime2_two    : |- prime2 (Suc(Suc Zero))                 (2 is prime)
     pow2_dvd_char : |- dvd d (pow 2 k) ==> Ex i. (le i k) AND oeq d (pow 2 i)
                       (every divisor of a power of 2 is itself a power of 2 <= it)
   ----------------------------------------------------------------------------
   Built on ctxtSig / thySig (the sigma context from isabelle_sigma.sml) which
   already carries dvd, prime2, pow, mult, add, le, lt, euclid_lemma (binom_thm),
   and a large instantiator layer.  NO new constant is introduced (these lemmas
   live in the existing signature), so we stay on ctxtSig and only add the
   instantiator/proof helpers the sigma prelude lacked.
   ============================================================================ *)
val () = out "POW2CHAR_BEGIN\n";

(* ---------------------------------------------------------------------------
   (A) extra re-varified base lemmas + instantiators on ctxtSig.
   --------------------------------------------------------------------------- *)
val disjI1_vSg          = varify disjI1_ax;
val disjI2_vSg          = varify disjI2_ax;
val oFalse_elim_vSg     = varify oFalse_elim_ax;
val conjI_vSg           = varify conjI_ax;
val euclid_lemma_vSg    = varify euclid_lemma;
val le_total_vSg        = varify le_total;
val left_distrib_vSg    = varify left_distrib;
val add_left_cancel_vSg = varify add_left_cancel;        (* oeq (add m a)(add m b) ==> oeq a b *)
val add_eq_zero_left_vSg= varify add_eq_zero_left;       (* oeq (add a b) 0 ==> oeq a 0 *)
val mult_0_vSg_l        = varify mult_0;                 (* oeq (mult 0 n) 0 *)
val mult_Suc_vSg_l      = varify mult_Suc;              (* oeq (mult (Suc m) n)(add n (mult m n)) *)
val mult_assoc_vSg2     = varify mult_assoc;            (* oeq (mult (mult m n) k)(mult m (mult n k)) *)
val mult_Suc_right_vSg2 = varify mult_Suc_right;        (* oeq (mult n (Suc m))(add n (mult n m)) *)
val le_suc_mono_vSg     = varify le_suc_mono;          (* le m n ==> le (Suc m)(Suc n) *)

fun disjI1Sg (At,Bt) h = (beta_norm (Drule.infer_instantiate ctxtSig
      [(("A",0), ctermSig At),(("B",0), ctermSig Bt)] disjI1_vSg)) OF [h];
fun disjI2Sg (At,Bt) h = (beta_norm (Drule.infer_instantiate ctxtSig
      [(("A",0), ctermSig At),(("B",0), ctermSig Bt)] disjI2_vSg)) OF [h];
fun oFalse_elimSg rT = beta_norm (Drule.infer_instantiate ctxtSig [(("R",0), ctermSig rT)] oFalse_elim_vSg);
fun conjI_Sg (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("A",0), ctermSig At),(("B",0), ctermSig Bt)] conjI_vSg)
  in (inst OF [hA]) OF [hB] end;
(* euclid_lemma : prime2 p ==> dvd p (mult a b) ==> Disj (dvd p a)(dvd p b) *)
fun euclid_lemma_Sg (pT,aT,bT) hpr hdvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("p",0), ctermSig pT),(("a",0), ctermSig aT),(("b",0), ctermSig bT)] euclid_lemma_vSg)
  in (inst OF [hpr]) OF [hdvd] end;
fun le_total_Sg (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSig
      [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] le_total_vSg);
fun left_distrib_Sg (xt,mt,nt) = beta_norm (Drule.infer_instantiate ctxtSig
      [(("x",0), ctermSig xt),(("m",0), ctermSig mt),(("n",0), ctermSig nt)] left_distrib_vSg);
fun add_left_cancel_Sg (mt,at,bt) h = (beta_norm (Drule.infer_instantiate ctxtSig
      [(("m",0), ctermSig mt),(("a",0), ctermSig at),(("b",0), ctermSig bt)] add_left_cancel_vSg)) OF [h];
fun add_eq_zero_left_Sg (at,bt) h = (beta_norm (Drule.infer_instantiate ctxtSig
      [(("a",0), ctermSig at),(("b",0), ctermSig bt)] add_eq_zero_left_vSg)) OF [h];
fun mult0lSg_at t = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] mult_0_vSg_l);
fun multSuclSg_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSig
      [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] mult_Suc_vSg_l);
fun multassocSg_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtSig
      [(("m",0), ctermSig mt),(("n",0), ctermSig nt),(("k",0), ctermSig kt)] mult_assoc_vSg2);
fun multSrSg (nt,mt) = beta_norm (Drule.infer_instantiate ctxtSig
      [(("n",0), ctermSig nt),(("m",0), ctermSig mt)] mult_Suc_right_vSg2);
fun le_suc_monoSg_at (mt,nt) h = (beta_norm (Drule.infer_instantiate ctxtSig
      [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] le_suc_mono_vSg)) OF [h];

val () = out "POW2CHAR_INSTANTIATORS_OK\n";

(* twoC = Suc(Suc Zero), oneC = Suc Zero  (from isabelle_sigma.sml EP suffix) *)

(* ============================================================================
   (B) prime2_two : prime2 (Suc(Suc Zero))
       = Conj (lt 1 2) (Forall (%d. dvd d 2 ==> Disj (oeq d 1)(oeq d 2))).
   ============================================================================ *)
val prime2_two =
  let
    val twoT = twoC;                                   (* Suc(Suc Zero) *)
    val gt1 = lt_1_SucSuc_Sg ZeroC;                    (* lt 1 (Suc(Suc 0)) = lt 1 2 *)
    val ppA = ppAbsSg twoT;                            (* %d. Imp (dvd d 2)(Disj (oeq d 1)(oeq d 2)) *)
    val faBody =
      let
        val dF = Free("d_p2", natT);
        val goalD = mkDisj (oeq dF oneC) (oeq dF twoT);
        val hDvd = Thm.assume (ctermSig (jT (dvd dF twoT)));   (* Ex k. 2 = d*k *)

        (* refute a divisor >= 3 (= Suc(Suc(Suc c))) of 2 *)
        fun refute_big (dBig, hdvdBig) =
          let
            val Pk = Term.lambda (Free("kk_p2", natT)) (oeq twoT (mult dBig (Free("kk_p2", natT))))
            fun body kv hk =                                   (* hk : 2 = dBig*k *)
              let
                val dzk = dzosSg_at kv
                val caseK0 =
                  let
                    val hk0 = Thm.assume (ctermSig (jT (oeq kv ZeroC)))
                    val Pz  = Term.lambda (Free("zk_p2",natT)) (oeq twoT (mult dBig (Free("zk_p2",natT))))
                    val h0  = substPredSg (Pz, kv, ZeroC) hk0 hk
                    val m0  = mult0rSg_at dBig
                    val h00 = oeq_trans OF [h0, m0]
                    val fls = (Suc_neq_Zero_Sg oneC) OF [h00]
                  in Thm.implies_intr (ctermSig (jT (oeq kv ZeroC))) fls end
                val sucKAbs = Abs("r", natT, oeq kv (suc (Bound 0)))
                val caseKS =
                  let
                    val hEx = Thm.assume (ctermSig (jT (mkEx sucKAbs)))
                    fun bodyR rv hr =
                      let
                        val Pz  = Term.lambda (Free("zk2_p2",natT)) (oeq twoT (mult dBig (Free("zk2_p2",natT))))
                        val hSr = substPredSg (Pz, kv, suc rv) hr hk        (* 2 = dBig*(Suc r) *)
                        val msr = multSrSg (dBig, rv)                       (* dBig*(Suc r) = add dBig (dBig*r) *)
                        val hAdd = oeq_trans OF [hSr, msr]                  (* 2 = add dBig (dBig*r) *)
                        val cF = (case dBig of (_ $ (_ $ (_ $ x))) => x | _ => raise Fail "dBig shape")
                        val Z  = mult dBig rv
                        val a1 = addSucSg_at (suc (suc cF), Z)
                        val a2 = addSucSg_at (suc cF, Z)
                        val a3 = addSucSg_at (cF, Z)
                        val s2 = Suc_cong OF [a2]
                        val s3 = Suc_cong OF [Suc_cong OF [a3]]
                        val addChain = oeq_trans OF [oeq_trans OF [a1, s2], s3]  (* add (S(S(S c))) Z = Suc(Suc(Suc(add c Z))) *)
                        val h2 = oeq_trans OF [hAdd, addChain]              (* 2 = Suc(Suc(Suc(add c Z))) *)
                        val inj1 = (Suc_inj_Sg (suc ZeroC, suc (suc (add cF Z)))) OF [h2]
                        val inj2 = (Suc_inj_Sg (ZeroC, suc (add cF Z))) OF [inj1]
                        val fls  = (Suc_neq_Zero_Sg (add cF Z)) OF [oeq_sym OF [inj2]]
                      in fls end
                    val r = exE_elimSg (sucKAbs, oFalseC) hEx "r_p2" bodyR
                  in Thm.implies_intr (ctermSig (jT (mkEx sucKAbs))) r end
              in disjE_elimSg (oeq kv ZeroC, mkEx sucKAbs, oFalseC) dzk caseK0 caseKS end
            val fls = exE_elimSg (Pk, oFalseC) hdvdBig "k_p2" body
          in fls end

        val dzd = dzosSg_at dF
        val sucDAbs = Abs("a", natT, oeq dF (suc (Bound 0)))
        val caseD0 =
          let
            val hd0 = Thm.assume (ctermSig (jT (oeq dF ZeroC)))
            val Pz = Term.lambda (Free("zd_p2",natT)) (dvd (Free("zd_p2",natT)) twoT)
            val hdvd0 = substPredSg (Pz, dF, ZeroC) hd0 hDvd
            val Pk0 = Term.lambda (Free("kk0_p2",natT)) (oeq twoT (mult ZeroC (Free("kk0_p2",natT))))
            fun body0 kv hk =
              let val m0 = mult0lSg_at kv
                  val h00 = oeq_trans OF [hk, m0]
              in (Suc_neq_Zero_Sg oneC) OF [h00] end
            val fls = exE_elimSg (Pk0, oFalseC) hdvd0 "k0_p2" body0
            val g = Thm.implies_elim (oFalse_elimSg goalD) fls
          in Thm.implies_intr (ctermSig (jT (oeq dF ZeroC))) g end
        val caseDS =
          let
            val hExA = Thm.assume (ctermSig (jT (mkEx sucDAbs)))
            fun bodyA av ha =
              let
                val dza = dzosSg_at av
                val sucAAbs = Abs("b", natT, oeq av (suc (Bound 0)))
                val caseA0 =
                  let
                    val ha0 = Thm.assume (ctermSig (jT (oeq av ZeroC)))
                    val sa = Suc_cong OF [ha0]
                    val deq1 = oeq_trans OF [ha, sa]                       (* d = Suc 0 = 1 *)
                    val g = disjI1Sg (oeq dF oneC, oeq dF twoT) deq1
                  in Thm.implies_intr (ctermSig (jT (oeq av ZeroC))) g end
                val caseAS =
                  let
                    val hExB = Thm.assume (ctermSig (jT (mkEx sucAAbs)))
                    fun bodyB bv hb =
                      let
                        val dzb = dzosSg_at bv
                        val sucBAbs = Abs("c", natT, oeq bv (suc (Bound 0)))
                        val caseB0 =
                          let
                            val hb0 = Thm.assume (ctermSig (jT (oeq bv ZeroC)))
                            val sb  = Suc_cong OF [hb0]
                            val sab = oeq_trans OF [hb, sb]
                            val ssab= Suc_cong OF [sab]
                            val deq2= oeq_trans OF [ha, ssab]              (* d = Suc(Suc 0) = 2 *)
                            val g = disjI2Sg (oeq dF oneC, oeq dF twoT) deq2
                          in Thm.implies_intr (ctermSig (jT (oeq bv ZeroC))) g end
                        val caseBS =
                          let
                            val hExC = Thm.assume (ctermSig (jT (mkEx sucBAbs)))
                            fun bodyC cv hc =
                              let
                                val sc  = Suc_cong OF [hc]
                                val sab = oeq_trans OF [hb, sc]
                                val ssa = Suc_cong OF [sab]
                                val deq3= oeq_trans OF [ha, ssa]           (* d = Suc(Suc(Suc c)) *)
                                val dBig= suc (suc (suc cv))
                                val Pz = Term.lambda (Free("zdb_p2",natT)) (dvd (Free("zdb_p2",natT)) twoT)
                                val hdvdBig = substPredSg (Pz, dF, dBig) deq3 hDvd
                                val fls = refute_big (dBig, hdvdBig)
                                val g = Thm.implies_elim (oFalse_elimSg goalD) fls
                              in g end
                            val r = exE_elimSg (sucBAbs, goalD) hExC "c_p2" bodyC
                          in Thm.implies_intr (ctermSig (jT (mkEx sucBAbs))) r end
                      in disjE_elimSg (oeq bv ZeroC, mkEx sucBAbs, goalD) dzb caseB0 caseBS end
                    val r = exE_elimSg (sucAAbs, goalD) hExB "b_p2" bodyB
                  in Thm.implies_intr (ctermSig (jT (mkEx sucAAbs))) r end
              in disjE_elimSg (oeq av ZeroC, mkEx sucAAbs, goalD) dza caseA0 caseAS end
            val r = exE_elimSg (sucDAbs, goalD) hExA "a_p2" bodyA
          in Thm.implies_intr (ctermSig (jT (mkEx sucDAbs))) r end
        val disjGoal = disjE_elimSg (oeq dF ZeroC, mkEx sucDAbs, goalD) dzd caseD0 caseDS
        val impD = Thm.implies_intr (ctermSig (jT (dvd dF twoT))) disjGoal
        val objImp = impI_Sg (dvd dF twoT, mkDisj (oeq dF oneC) (oeq dF twoT)) impD
      in Thm.forall_intr (ctermSig dF) objImp end;
    val faThm = allI_Sg ppA faBody;                   (* jT (Forall (ppAbs 2)) *)
    val conj = conjI_Sg (lt oneC twoT, mkForall ppA) gt1 faThm;
  in conj end;

val i_prime2_two = jT (prime2 twoC);
val r_prime2_two = checkSg ("prime2_two", prime2_two, i_prime2_two);
val () = if r_prime2_two then out "PRIME2_TWO_OK\n" else out "PRIME2_TWO_FAIL\n";

(* prime2_two_v : 0-hyp varified for euclid_lemma applications *)
val prime2_two_v = prime2_two;   (* ground (closed) ; no schematic vars to varify *)

(* ============================================================================
   (C) mult_eq_zero + mult_left_cancel on ctxtSig (local, mirror isabelle_pyth).
   ============================================================================ *)
val mult_eq_zero_Sg =
  let
    val aF = Free("a_mez", natT);  val bF = Free("b_mez", natT);
    val hyp = Thm.assume (ctermSig (jT (oeq (mult aF bF) ZeroC)));
    val goalC = mkDisj (oeq aF ZeroC) (oeq bF ZeroC);
    val dz = dzosSg_at aF;
    val caseZ =
      let val hZ = Thm.assume (ctermSig (jT (oeq aF ZeroC)))
      in Thm.implies_intr (ctermSig (jT (oeq aF ZeroC)))
           (disjI1Sg (oeq aF ZeroC, oeq bF ZeroC) hZ) end;
    val sucAbs = Abs("q", natT, oeq aF (suc (Bound 0)));
    val caseS =
      let
        val hEx = Thm.assume (ctermSig (jT (mkEx sucAbs)))
        fun body q hq =
          let
            val abq  = mult_cong_lSg (aF, suc q, bF) hq;
            val sqb  = multSuclSg_at (q, bF);
            val ab_e = oeq_trans OF [oeq_sym OF [oeq_trans OF [abq, sqb]], hyp];  (* add b (q*b) = 0 *)
            val bz   = add_eq_zero_left_Sg (bF, mult q bF) ab_e;
          in disjI2Sg (oeq aF ZeroC, oeq bF ZeroC) bz end
        val res = exE_elimSg (sucAbs, goalC) hEx "q_mez" body;
      in Thm.implies_intr (ctermSig (jT (mkEx sucAbs))) res end;
    val body = disjE_elimSg (oeq aF ZeroC, mkEx sucAbs, goalC) dz caseZ caseS;
  in varify (Thm.implies_intr (ctermSig (jT (oeq (mult aF bF) ZeroC))) body) end;
val mult_eq_zero_vSg = varify mult_eq_zero_Sg;
fun mult_eq_zero_at (aT,bT) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("a_mez",0), ctermSig aT), (("b_mez",0), ctermSig bT)] mult_eq_zero_vSg)
  in Thm.implies_elim inst h end;

val () = out "MULT_EQ_ZERO_OK\n";

val mult_left_cancel_Sg =
  let
    val pF = Free("p_mlc", natT); val aF = Free("a_mlc", natT); val bF = Free("b_mlc", natT);
    val hPos = Thm.assume (ctermSig (jT (lt ZeroC pF)));
    val hEq  = Thm.assume (ctermSig (jT (oeq (mult pF aF) (mult pF bF))));
    val goalC = oeq aF bF;
    val tot = le_total_Sg (aF, bF);
    fun contraP goal =
      let val hpz = Thm.assume (ctermSig (jT (oeq pF ZeroC)))
          val zV   = Free("z_subst_mlc", natT)
          val Psub = Term.lambda zV (lt ZeroC zV)
          val lt00 = substPredSg (Psub, pF, ZeroC) hpz hPos
          val fls  = lt_irrefl_Sg ZeroC OF [lt00]
          val g    = Thm.implies_elim (oFalse_elimSg goal) fls
      in Thm.implies_intr (ctermSig (jT (oeq pF ZeroC))) g end;
    val leAbsAB = Abs("k", natT, oeq bF (add aF (Bound 0)));
    val caseAB =
      let
        val hLe = Thm.assume (ctermSig (jT (le aF bF)))
        fun body d hd =
          let
            val pb1 = mult_cong_rSg (pF, bF, add aF d) hd;
            val ld  = left_distrib_Sg (pF, aF, d);
            val pb2 = oeq_trans OF [pb1, ld];
            val pa_e = oeq_trans OF [hEq, pb2];
            val pa0  = oeq_sym OF [add0rSg_at (mult pF aF)];
            val both = oeq_trans OF [oeq_sym OF [pa0], pa_e];
            val zpd  = add_left_cancel_Sg (mult pF aF, ZeroC, mult pF d) both;
            val pdz  = oeq_sym OF [zpd];
            val disj = mult_eq_zero_at (pF, d) pdz;
            val cZp  = contraP goalC;
            val cZd =
              let val hdz = Thm.assume (ctermSig (jT (oeq d ZeroC)))
                  val ba0 = oeq_trans OF [hd, add_cong_rSg (aF, d, ZeroC) hdz]
                  val ba  = oeq_trans OF [ba0, add0rSg_at aF]
                  val ab  = oeq_sym OF [ba]
              in Thm.implies_intr (ctermSig (jT (oeq d ZeroC))) ab end;
          in disjE_elimSg (oeq pF ZeroC, oeq d ZeroC, goalC) disj cZp cZd end
        val r = exE_elimSg (leAbsAB, goalC) hLe "d_ab_mlc" body;
      in Thm.implies_intr (ctermSig (jT (le aF bF))) r end;
    val leAbsBA = Abs("k", natT, oeq aF (add bF (Bound 0)));
    val caseBA =
      let
        val hLe = Thm.assume (ctermSig (jT (le bF aF)))
        fun body d hd =
          let
            val pa1 = mult_cong_rSg (pF, aF, add bF d) hd;
            val ld  = left_distrib_Sg (pF, bF, d);
            val pa2 = oeq_trans OF [pa1, ld];
            val pb_e = oeq_trans OF [oeq_sym OF [hEq], pa2];
            val pb0  = oeq_sym OF [add0rSg_at (mult pF bF)];
            val both = oeq_trans OF [oeq_sym OF [pb0], pb_e];
            val zpd  = add_left_cancel_Sg (mult pF bF, ZeroC, mult pF d) both;
            val pdz  = oeq_sym OF [zpd];
            val disj = mult_eq_zero_at (pF, d) pdz;
            val cZp  = contraP goalC;
            val cZd =
              let val hdz = Thm.assume (ctermSig (jT (oeq d ZeroC)))
                  val ab0 = oeq_trans OF [hd, add_cong_rSg (bF, d, ZeroC) hdz]
                  val ab  = oeq_trans OF [ab0, add0rSg_at bF]
              in Thm.implies_intr (ctermSig (jT (oeq d ZeroC))) ab end;
          in disjE_elimSg (oeq pF ZeroC, oeq d ZeroC, goalC) disj cZp cZd end
        val r = exE_elimSg (leAbsBA, goalC) hLe "d_ba_mlc" body;
      in Thm.implies_intr (ctermSig (jT (le bF aF))) r end;
    val body = disjE_elimSg (le aF bF, le bF aF, goalC) tot caseAB caseBA;
    val d1 = Thm.implies_intr (ctermSig (jT (oeq (mult pF aF) (mult pF bF)))) body;
    val d2 = Thm.implies_intr (ctermSig (jT (lt ZeroC pF))) d1;
  in varify d2 end;
val mult_left_cancel_vSg = varify mult_left_cancel_Sg;
fun mult_left_cancel_at (pT,aT,bT) hpos heq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("p_mlc",0), ctermSig pT),(("a_mlc",0), ctermSig aT),(("b_mlc",0), ctermSig bT)] mult_left_cancel_vSg)
  in (inst OF [hpos]) OF [heq] end;

val () = out "MULT_LEFT_CANCEL_OK\n";

(* lt 0 2 : le (Suc 0) 2 = Ex p. 2 = 1 + p, witness 1 (2 = add 1 1) *)
val lt_0_two =
  let
    val a1 = addSucSg_at (ZeroC, oneC)                    (* add (Suc 0)(Suc 0) = Suc(add 0 (Suc 0)) *)
    val a0 = add0Sg_at oneC                               (* add 0 (Suc 0) = Suc 0 *)
    val sa = Suc_cong OF [a0]                             (* Suc(add 0 (Suc 0)) = Suc(Suc 0) *)
    val chain = oeq_trans OF [a1, sa]                     (* add 1 1 = 2 *)
    val chainSym = oeq_sym OF [chain]                     (* 2 = add 1 1 *)
  in le_introSg (oneC, twoC, oneC) chainSym end;          (* le (Suc 0) 2 = lt 0 2 *)

(* ============================================================================
   (D) pow2_dvd_char : dvd d (pow 2 k) ==> Ex i. (le i k) AND oeq d (pow 2 i)
       BY INDUCTION on k, with d UNIVERSALLY QUANTIFIED inside the predicate
       (object Forall) so the IH applies to the cofactor d' as well as d.
   ============================================================================ *)
fun p2cConjBody (dT, kT) =                                 (* %i. Conj (le i k)(oeq d (pow 2 i)) *)
  let val iF = Free("i_p2c", natT)
  in Term.lambda iF (mkConj (le iF kT) (oeq dT (pow twoC iF))) end;
fun p2cConcl (dT, kT) = mkEx (p2cConjBody (dT, kT));       (* Ex i. le i k /\ d = 2^i *)
fun p2cImp (dT, kT) = mkImp (dvd dT (pow twoC kT)) (p2cConcl (dT, kT));
fun p2cForallBody kT =                                     (* %d. Imp (dvd d (2^k))(Ex i. ...) *)
  let val dF = Free("d_fa_p2c", natT)
  in Term.lambda dF (p2cImp (dF, kT)) end;

(* exI for the inner existential : witness wi, body Conj proof *)
fun exI_p2c (dT, kT, wi) hconj = exI_Sg (p2cConjBody (dT, kT), wi) hconj;

val pow2_dvd_char_forall =
  let
    val kIndV = Free("k_ind_p2c", natT);
    val Qpred = Term.lambda kIndV (mkForall (p2cForallBody kIndV));
    val kF = Free("k_p2c", natT);
    val ind = nat_induct_atSg (Qpred, kF);

    (* ---- BASE k=0 : Forall(%d. dvd d (2^0) ==> Ex i. le i 0 /\ d = 2^i) ---- *)
    val base =
      let
        val dF = Free("d_b_p2c", natT);
        val hd1raw = Thm.assume (ctermSig (jT (dvd dF (pow twoC ZeroC))));
        val pz = powZeroSg_at twoC                                          (* 2^0 = 1 *)
        val Pz = Term.lambda (Free("zb_p2c",natT)) (dvd dF (Free("zb_p2c",natT)))
        val hd1 = substPredSg (Pz, pow twoC ZeroC, oneC) pz hd1raw          (* dvd d 1 *)
        (* dvd d 1 = Ex k. 1 = d*k ; show d = 1 *)
        val Pk = Term.lambda (Free("kb_p2c",natT)) (oeq oneC (mult dF (Free("kb_p2c",natT))))
        fun bodyK kv hk =
          let
            val dzd = dzosSg_at dF
            val sucDAbs = Abs("d'", natT, oeq dF (suc (Bound 0)))
            val cD0 =
              let val hd0 = Thm.assume (ctermSig (jT (oeq dF ZeroC)))
                  val Pz2 = Term.lambda (Free("zd_p2cb",natT)) (oeq oneC (mult (Free("zd_p2cb",natT)) kv))
                  val h0  = substPredSg (Pz2, dF, ZeroC) hd0 hk             (* 1 = 0*k *)
                  val m0  = mult0lSg_at kv
                  val h00 = oeq_trans OF [h0, m0]                          (* 1 = 0 *)
                  val fls = (Suc_neq_Zero_Sg ZeroC) OF [h00]
                  val g   = Thm.implies_elim (oFalse_elimSg (oeq dF oneC)) fls
              in Thm.implies_intr (ctermSig (jT (oeq dF ZeroC))) g end
            val cDS =
              let
                val hExD = Thm.assume (ctermSig (jT (mkEx sucDAbs)))
                fun bodyD dpv hdp =
                  let
                    val dzk = dzosSg_at kv
                    val sucKAbs = Abs("k'", natT, oeq kv (suc (Bound 0)))
                    val cK0 =
                      let val hk0 = Thm.assume (ctermSig (jT (oeq kv ZeroC)))
                          val Pz3 = Term.lambda (Free("zk_p2cb",natT)) (oeq oneC (mult dF (Free("zk_p2cb",natT))))
                          val h0  = substPredSg (Pz3, kv, ZeroC) hk0 hk     (* 1 = d*0 *)
                          val m0  = mult0rSg_at dF
                          val h00 = oeq_trans OF [h0, m0]
                          val fls = (Suc_neq_Zero_Sg ZeroC) OF [h00]
                          val g   = Thm.implies_elim (oFalse_elimSg (oeq dF oneC)) fls
                      in Thm.implies_intr (ctermSig (jT (oeq kv ZeroC))) g end
                    val cKS =
                      let
                        val hExK = Thm.assume (ctermSig (jT (mkEx sucKAbs)))
                        fun bodyKp kpv hkp =
                          let
                            val Pz4 = Term.lambda (Free("zk2_p2cb",natT)) (oeq oneC (mult dF (Free("zk2_p2cb",natT))))
                            val hSk = substPredSg (Pz4, kv, suc kpv) hkp hk  (* 1 = d*(Suc k') *)
                            val msr = multSrSg (dF, kpv)
                            val hAdd= oeq_trans OF [hSk, msr]                (* 1 = add d (d*k') *)
                            val Z = mult dF kpv
                            val hAddD = oeq_trans OF [hAdd, add_cong_lSg (dF, suc dpv, Z) hdp]  (* 1 = add (Suc d') Z *)
                            val aS = addSucSg_at (dpv, Z)
                            val h1S = oeq_trans OF [hAddD, aS]               (* 1 = Suc(add d' Z) *)
                            val inj = (Suc_inj_Sg (ZeroC, add dpv Z)) OF [h1S]  (* 0 = add d' Z *)
                            val dpz = add_eq_zero_left_Sg (dpv, Z) (oeq_sym OF [inj])  (* d' = 0 *)
                            val sd = Suc_cong OF [dpz]
                            val deq1 = oeq_trans OF [hdp, sd]                (* d = Suc 0 = 1 *)
                          in deq1 end
                        val r = exE_elimSg (sucKAbs, oeq dF oneC) hExK "kp_p2cb" bodyKp
                      in Thm.implies_intr (ctermSig (jT (mkEx sucKAbs))) r end
                  in disjE_elimSg (oeq kv ZeroC, mkEx sucKAbs, oeq dF oneC) dzk cK0 cKS end
                val r = exE_elimSg (sucDAbs, oeq dF oneC) hExD "dp_p2cb" bodyD
              in Thm.implies_intr (ctermSig (jT (mkEx sucDAbs))) r end
            val deq1 = disjE_elimSg (oeq dF ZeroC, mkEx sucDAbs, oeq dF oneC) dzd cD0 cDS  (* d = 1 *)
          in deq1 end
        val deq1 = exE_elimSg (Pk, oeq dF oneC) hd1 "kb_w_p2c" bodyK         (* d = 1 *)
        val le00 = le_reflSg_at ZeroC                                       (* le 0 0 *)
        val pz_sym = oeq_sym OF [pz]                                        (* 1 = pow 2 0 *)
        val d_eq_pz = oeq_trans OF [deq1, pz_sym]                           (* d = pow 2 0 *)
        val conj = conjI_Sg (le ZeroC ZeroC, oeq dF (pow twoC ZeroC)) le00 d_eq_pz
        val ex = exI_p2c (dF, ZeroC, ZeroC) conj
        val objImp = impI_Sg (dvd dF (pow twoC ZeroC), p2cConcl (dF, ZeroC))
                       (Thm.implies_intr (ctermSig (jT (dvd dF (pow twoC ZeroC)))) ex)
      in allI_Sg (p2cForallBody ZeroC) (Thm.forall_intr (ctermSig dF) objImp) end;

    (* ---- STEP : IH(x) : Forall(%d. dvd d (2^x) ==> ...) ==> Forall at Suc x ---- *)
    val xF = Free("x_p2c", natT);
    val ihprop = jT (mkForall (p2cForallBody xF));
    val IH = Thm.assume (ctermSig ihprop);
    (* IH at a value vd : dvd vd (2^x) ==> Ex i. le i x /\ vd = 2^i *)
    fun useIH (vd, hdvd) =
      let val impAt = allE_Sg (p2cForallBody xF) vd IH       (* jT (Imp (dvd vd (2^x))(concl vd x)) *)
      in mp_Sg (dvd vd (pow twoC xF), p2cConcl (vd, xF)) impAt hdvd end;

    val stepObj =
      let
        val dF = Free("d_s_p2c", natT);
        val goalSuc = p2cConcl (dF, suc xF);                                (* Ex i. le i (Suc x) /\ d = 2^i *)
        val hdvdSx = Thm.assume (ctermSig (jT (dvd dF (pow twoC (suc xF)))));
        val psuc = powSucSg_at (twoC, xF)                                   (* 2^(Suc x) = 2 * 2^x *)
        val Pps = Term.lambda (Free("zps_p2c",natT)) (dvd dF (Free("zps_p2c",natT)))
        val hdvdMul = substPredSg (Pps, pow twoC (suc xF), mult twoC (pow twoC xF)) psuc hdvdSx  (* dvd d (2*2^x) *)

        (* from (dvd vd (2^x)) and (d = 2^i ==> goalSuc-builder), but in both cases the
           cofactor equals 2^i with i<=x ; we package the "use IH then lift i<=x to i<=Suc x"
           for an arbitrary target value vTarget and a function relating vTarget's witness. *)

        (* CASE 2|d : d = 2*d' ; show d'|2^x ; IH(d') gives d'=2^i, i<=x ;
                      then d = 2*2^i = 2^(Suc i), Suc i <= Suc x. *)
        val em = ex_middle_atSg (dvd twoC dF)                               (* Disj (dvd 2 d)(neg (dvd 2 d)) *)
        val case2d =
          let
            val h2d = Thm.assume (ctermSig (jT (dvd twoC dF)))
            val Pdd = Term.lambda (Free("dd_p2c",natT)) (oeq dF (mult twoC (Free("dd_p2c",natT))))
            fun bodyDD dpv hdp =                                            (* hdp : d = 2*d' *)
              let
                val Pm = Term.lambda (Free("mm_p2c",natT)) (oeq (mult twoC (pow twoC xF)) (mult dF (Free("mm_p2c",natT))))
                fun bodyM mv hm =                                           (* hm : 2*2^x = d*m *)
                  let
                    val dmRW = mult_cong_lSg (dF, mult twoC dpv, mv) hdp     (* d*m = (2*d')*m *)
                    val assoc = multassocSg_at (twoC, dpv, mv)              (* (2*d')*m = 2*(d'*m) *)
                    val dm2 = oeq_trans OF [dmRW, assoc]                    (* d*m = 2*(d'*m) *)
                    val hm2 = oeq_trans OF [hm, dm2]                       (* 2*2^x = 2*(d'*m) *)
                    val canc = mult_left_cancel_at (twoC, pow twoC xF, mult dpv mv) lt_0_two hm2  (* 2^x = d'*m *)
                    val hdvddp = dvd_introSg (dpv, pow twoC xF, mv) canc    (* dvd d' (2^x) *)
                    val exX = useIH (dpv, hdvddp)                           (* Ex i. le i x /\ d' = 2^i *)
                    fun bodyI iv hconj =
                      let
                        val hle = conjunct1_Sg (le iv xF, oeq dpv (pow twoC iv)) hconj   (* le i x *)
                        val hdeq= conjunct2_Sg (le iv xF, oeq dpv (pow twoC iv)) hconj   (* d' = 2^i *)
                        (* d = 2*d' = 2*2^i = 2^(Suc i) *)
                        val d_2dp = hdp                                       (* d = 2*d' *)
                        val rw    = mult_cong_rSg (twoC, dpv, pow twoC iv) hdeq  (* 2*d' = 2*2^i *)
                        val psucI = powSucSg_at (twoC, iv)                  (* 2^(Suc i) = 2*2^i *)
                        val d_eq_pSi = oeq_trans OF [oeq_trans OF [d_2dp, rw], oeq_sym OF [psucI]]  (* d = 2^(Suc i) *)
                        (* le i x ==> le (Suc i)(Suc x) *)
                        val leSiSx = le_suc_monoSg_at (iv, xF) hle           (* le (Suc i)(Suc x) *)
                        val conj = conjI_Sg (le (suc iv) (suc xF), oeq dF (pow twoC (suc iv))) leSiSx d_eq_pSi
                      in exI_p2c (dF, suc xF, suc iv) conj end
                    val P = p2cConjBody (dpv, xF)
                  in exE_elimSg (P, goalSuc) exX "i_2d_p2c" bodyI end
                val res = exE_elimSg (Pm, goalSuc) hdvdMul "m_2d_p2c" bodyM
              in res end
            val res = exE_elimSg (Pdd, goalSuc) h2d "dp_2d_p2c" bodyDD
          in Thm.implies_intr (ctermSig (jT (dvd twoC dF))) res end

        (* CASE neg(2|d) : 2*2^x = d*m ; 2 | (d*m) ; euclid (prime2_two) -> 2|d \/ 2|m ;
                neg(2|d) -> 2|m ; m = 2*m' ; cancel 2 -> 2^x = d*m' -> d|2^x ; IH(d). *)
        val caseNot2d =
          let
            val hNot2d = Thm.assume (ctermSig (jT (neg (dvd twoC dF))))     (* Imp (dvd 2 d) oFalse *)
            val Pm = Term.lambda (Free("mn_p2c",natT)) (oeq (mult twoC (pow twoC xF)) (mult dF (Free("mn_p2c",natT))))
            fun bodyM mv hm =                                               (* hm : 2*2^x = d*m *)
              let
                (* 2 | (d*m) : witness 2^x ; d*m = 2*2^x [sym hm] *)
                val hdvd2dm = dvd_introSg (twoC, mult dF mv, pow twoC xF) (oeq_sym OF [hm])  (* dvd 2 (d*m) *)
                val disj = euclid_lemma_Sg (twoC, dF, mv) prime2_two_v hdvd2dm  (* Disj (dvd 2 d)(dvd 2 m) *)
                (* left : contradiction with neg(2|d) *)
                val caseL =
                  let val h2d = Thm.assume (ctermSig (jT (dvd twoC dF)))
                      val fls = mp_Sg (dvd twoC dF, oFalseC) hNot2d h2d
                      val g = Thm.implies_elim (oFalse_elimSg goalSuc) fls
                  in Thm.implies_intr (ctermSig (jT (dvd twoC dF))) g end
                (* right : 2|m -> m = 2*m' *)
                val caseR =
                  let
                    val h2m = Thm.assume (ctermSig (jT (dvd twoC mv)))
                    val Pmm = Term.lambda (Free("mm2_p2c",natT)) (oeq mv (mult twoC (Free("mm2_p2c",natT))))
                    fun bodyMM mpv hmp =                                    (* hmp : m = 2*m' *)
                      let
                        (* 2*2^x = d*m = d*(2*m') = (d*2)*m' = (2*d)*m' = 2*(d*m') *)
                        val dmRW = mult_cong_rSg (dF, mv, mult twoC mpv) hmp    (* d*m = d*(2*m') *)
                        (* d*(2*m') = (d*2)*m' [assoc sym] ; d*2 = 2*d [comm] ; (2*d)*m' = 2*(d*m') [assoc] *)
                        val assoc1 = multassocSg_at (dF, twoC, mpv)         (* (d*2)*m' = d*(2*m') *)
                        val comm   = multcommSg_at (dF, twoC)              (* d*2 = 2*d *)
                        val commM  = mult_cong_lSg (mult dF twoC, mult twoC dF, mpv) comm  (* (d*2)*m' = (2*d)*m' *)
                        val assoc2 = multassocSg_at (twoC, dF, mpv)        (* (2*d)*m' = 2*(d*m') *)
                        (* d*(2*m') = (d*2)*m' [sym assoc1] = (2*d)*m' [commM] = 2*(d*m') [assoc2] *)
                        val chain = oeq_trans OF [oeq_trans OF [oeq_sym OF [assoc1], commM], assoc2]  (* d*(2*m') = 2*(d*m') *)
                        val dm_2 = oeq_trans OF [dmRW, chain]              (* d*m = 2*(d*m') *)
                        val hm2 = oeq_trans OF [hm, dm_2]                  (* 2*2^x = 2*(d*m') *)
                        val canc = mult_left_cancel_at (twoC, pow twoC xF, mult dF mpv) lt_0_two hm2  (* 2^x = d*m' *)
                        val hdvdd = dvd_introSg (dF, pow twoC xF, mpv) canc  (* dvd d (2^x) *)
                        val exX = useIH (dF, hdvdd)                        (* Ex i. le i x /\ d = 2^i *)
                        fun bodyI iv hconj =
                          let
                            val hle = conjunct1_Sg (le iv xF, oeq dF (pow twoC iv)) hconj
                            val hdeq= conjunct2_Sg (le iv xF, oeq dF (pow twoC iv)) hconj
                            val lex = le_suc_selfSg_at xF                  (* le x (Suc x) *)
                            val leiSx = le_transSg_at (iv, xF, suc xF) hle lex  (* le i (Suc x) *)
                            val conj = conjI_Sg (le iv (suc xF), oeq dF (pow twoC iv)) leiSx hdeq
                          in exI_p2c (dF, suc xF, iv) conj end
                        val P = p2cConjBody (dF, xF)
                      in exE_elimSg (P, goalSuc) exX "i_n2_p2c" bodyI end
                    val r = exE_elimSg (Pmm, goalSuc) h2m "mp_n2_p2c" bodyMM
                  in Thm.implies_intr (ctermSig (jT (dvd twoC mv))) r end
              in disjE_elimSg (dvd twoC dF, dvd twoC mv, goalSuc) disj caseL caseR end
            val res = exE_elimSg (Pm, goalSuc) hdvdMul "m_n2_p2c" bodyM
          in Thm.implies_intr (ctermSig (jT (neg (dvd twoC dF)))) res end

        val concl = disjE_elimSg (dvd twoC dF, neg (dvd twoC dF), goalSuc) em case2d caseNot2d
        val objImp = impI_Sg (dvd dF (pow twoC (suc xF)), p2cConcl (dF, suc xF))
                       (Thm.implies_intr (ctermSig (jT (dvd dF (pow twoC (suc xF))))) concl)
      in allI_Sg (p2cForallBody (suc xF)) (Thm.forall_intr (ctermSig dF) objImp) end;

    val step1 = Thm.forall_intr (ctermSig xF) (Thm.implies_intr (ctermSig ihprop) stepObj);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;                    (* jT (Forall(%d. dvd d (2^k) ==> ...)) for generic k *)
  in varify r2 end;

val () = out "POW2CHAR_FORALL_OK\n";

(* ---- specialise to the d-free statement : dvd d (2^k) ==> Ex i. le i k /\ d = 2^i ---- *)
val pow2_dvd_char =
  let
    val dF = Free("d", natT); val kF = Free("k", natT);
    val faInst = beta_norm (Drule.infer_instantiate ctxtSig
                   [(("k_p2c",0), ctermSig kF)] pow2_dvd_char_forall);   (* Forall(%d. ...) at k *)
    val impAt = allE_Sg (p2cForallBody kF) dF faInst;        (* jT (Imp (dvd d (2^k))(Ex i. ...)) *)
    val hdvd = Thm.assume (ctermSig (jT (dvd dF (pow twoC kF))));
    val ex = mp_Sg (dvd dF (pow twoC kF), p2cConcl (dF, kF)) impAt hdvd;
  in varify (Thm.implies_intr (ctermSig (jT (dvd dF (pow twoC kF)))) ex) end;

(* validation : 0-hyp + aconv intended *)
val dVp = Var (("d",0), natT);
val kVp = Var (("k",0), natT);
val i_pow2_dvd_char =
  Logic.mk_implies (jT (dvd dVp (pow twoC kVp)),
    jT (mkEx (Term.lambda (Free("i_p2c", natT))
          (mkConj (le (Free("i_p2c",natT)) kVp) (oeq dVp (pow twoC (Free("i_p2c",natT))))))));
val r_pow2_dvd_char = checkSg ("pow2_dvd_char", pow2_dvd_char, i_pow2_dvd_char);
val () = if r_pow2_dvd_char then out "POW2_DVD_CHAR_OK\n" else out "POW2_DVD_CHAR_FAIL\n";

(* ============================================================================
   SOUNDNESS PROBES
   ============================================================================ *)
(* (1) prime2_two genuinely concludes prime2 2 (not e.g. prime2 of something else / True). *)
val s_p2t = (Thm.prop_of prime2_two) aconv (jT (prime2 twoC));
val () = if s_p2t then out "PROBE_OK prime2_two is exactly prime2 2\n"
         else out "PROBE_FAIL prime2_two collapsed!\n";
(* prime2_two must NOT be prime2 of a non-prime numeral (e.g. prime2 4 would be false). *)
val s_p2t_not4 = not ((Thm.prop_of prime2_two) aconv (jT (prime2 (suc (suc (suc (suc ZeroC)))))));
val () = if s_p2t_not4 then out "PROBE_OK prime2_two is not prime2 4\n"
         else out "PROBE_FAIL prime2_two is prime2 4?!\n";

(* (2) pow2_dvd_char is genuinely CONDITIONAL on dvd d (2^k) (dropping it is unprovable:
   it would claim every d is a power of 2). *)
val s_p2c_cond =
  not ((Thm.prop_of pow2_dvd_char) aconv
       (jT (mkEx (Term.lambda (Free("i_p2c", natT))
             (mkConj (le (Free("i_p2c",natT)) kVp) (oeq dVp (pow twoC (Free("i_p2c",natT)))))))));
val () = if s_p2c_cond then out "PROBE_OK pow2_dvd_char needs the dvd d (2^k) hypothesis\n"
         else out "PROBE_FAIL pow2_dvd_char dropped its hypothesis!\n";
(* (3) the existential bound is i <= k (le i k), not the trivial / dropped form
   (e.g. NOT just Ex i. d = 2^i without the le bound). *)
val s_p2c_bound =
  not ((Thm.prop_of pow2_dvd_char) aconv
       (Logic.mk_implies (jT (dvd dVp (pow twoC kVp)),
          jT (mkEx (Term.lambda (Free("i_p2c", natT)) (oeq dVp (pow twoC (Free("i_p2c",natT)))))))));
val () = if s_p2c_bound then out "PROBE_OK pow2_dvd_char carries the le i k bound\n"
         else out "PROBE_FAIL pow2_dvd_char lost its le bound!\n";

val () =
  if r_prime2_two andalso r_pow2_dvd_char andalso s_p2t andalso s_p2t_not4
     andalso s_p2c_cond andalso s_p2c_bound
  then out "POW2CHAR_ALL_OK\n"
  else out "POW2CHAR_INCOMPLETE\n";

val () = out "POW2CHAR_END\n";
(* ============================================================================
   DIVISOR CHARACTERIZATION of N = 2^a * q  for an ODD prime q.
   ----------------------------------------------------------------------------
   Toward Euclid's perfect-number theorem (Elements IX.36).  This driver builds
   the explicit list of divisors of N = 2^a*q and proves it correct:

     divlist a q  =  [ 2^0, 2^1, ..., 2^a, 2^0*q, 2^1*q, ..., 2^a*q ]
                     (the 2(a+1) points {2^i, 2^i*q : 0<=i<=a})

   THE FOUR CLAIMS:
     (E1)  EVERY listed element divides N        (easy: 2^i | 2^a, and *q)
     (E2)  all listed elements are <= N           (le bound via monotonicity)
     (D )  the list has no duplicates             (2^i strictly increasing,
                                                    q>1 separates the two halves)
     (C )  COMPLETENESS (the hard direction):
             dvd d N ==> lmem d (divlist a q)
           i.e. every divisor of N is one of the 2(a+1) points.
           Proved (forward) via euclid_lemma: a divisor d of 2^a*q factors as
           2^i or 2^i*q (its prime factors are in {2,q}).
           DEPENDS ON  pow2_dvd_char (assumed as an object-level hypothesis):
             dvd d (pow 2 a) ==> Ex i. le i a /\ oeq d (pow 2 i).

   This driver is SPLICED after isabelle_nt_helpers.sml + isabelle_binom_thm.sml
   + isabelle_sigma.sml (which gives ctxtSig/ctermSig on theory thySig carrying
   swt/sigma over the binom_thm base: sumf/sub/pow/binom/mult + prime2 + dvd +
   euclid_lemma).  We EXTEND thySig with the divisor-list machinery (a fresh
   natlist + lmem), build ONE final context, and re-varify every reused base
   lemma onto it.
   ============================================================================ *)
val () = out "DIVCHAR_BEGIN\n";

(* ============================================================================
   STEP 0 : lift the divisibility / euclid / arithmetic base lemmas onto ctxtSig
   that the sigma prelude did not pre-instantiate (euclid_lemma, disjI1/2, dvd
   intro/cong, mult cancellation prereqs, le bounds).
   ============================================================================ *)

(* --- mp / impI / allI / exI / exE already exist as *_Sg helpers in sigma.
       Add: disjI1/disjI2, conjI/conjunct, dvd helpers, euclid_lemma, le/lt. --- *)

val disjI1_vSg = varify disjI1_ax;
val disjI2_vSg = varify disjI2_ax;
fun disjI1_Sg (At, Bt) hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("A",0), ctermSig At), (("B",0), ctermSig Bt)] disjI1_vSg)
  in Thm.implies_elim inst hA end;
fun disjI2_Sg (At, Bt) hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("A",0), ctermSig At), (("B",0), ctermSig Bt)] disjI2_vSg)
  in Thm.implies_elim inst hB end;

(* --- euclid_lemma on ctxtSig : prime2 p ==> dvd p (mult a b) ==> Disj(dvd p a)(dvd p b) --- *)
val euclid_lemma_vSg = varify euclid_lemma;
fun euclid_lemma_Sg (pT, aT, bT) hPrime hDvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("p",0), ctermSig pT), (("a",0), ctermSig aT), (("b",0), ctermSig bT)] euclid_lemma_vSg)
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hDvd end;

(* --- dvd_zero / dvd_mult_right / left_distrib / mult_le_mono on ctxtSig --- *)
val dvd_zero_vSg        = varify dvd_zero;
val dvd_mult_right_vSg  = varify dvd_mult_right;
val left_distrib_vSg    = varify left_distrib;
val mult_le_mono_vSg    = varify mult_le_mono;
val mult_Suc_right_vSg  = varify mult_Suc_right;
val add_eq_zero_left_vSg = varify add_eq_zero_left;  (* add a b = 0 ==> a = 0  (if present) *)

fun dvd_zeroSg_at t = beta_norm (Drule.infer_instantiate ctxtSig [(("a",0), ctermSig t)] dvd_zero_vSg);
fun left_distribSg_at (xT,mT,nT) = beta_norm (Drule.infer_instantiate ctxtSig
      [(("x",0), ctermSig xT),(("m",0), ctermSig mT),(("n",0), ctermSig nT)] left_distrib_vSg);
fun mult_le_mono_Sg (cT, jT_, kT) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("c",0), ctermSig cT),(("j",0), ctermSig jT_),(("k",0), ctermSig kT)] mult_le_mono_vSg)
  in Thm.implies_elim inst h end;
fun multSucR_Sg (nt,mt) = beta_norm (Drule.infer_instantiate ctxtSig
      [(("n",0), ctermSig nt),(("m",0), ctermSig mt)] mult_Suc_right_vSg);

val () = out "DIVCHAR_STEP0_BASE_LIFTED\n";

(* ============================================================================
   STEP 1 : mult_left_cancel  :  lt Zero c ==> oeq (mult c a)(mult c b) ==> oeq a b
   The q-cancellation the completeness q-case needs.  Proof: c = Suc c0 (lt 0 c);
   le_total a b -> in each case b = a+e (or a = b+e); left_distrib + add_left_cancel
   gives 0 = mult c e; with c = Suc c0, mult (Suc c0) e = add e (mult c0 e),
   add_eq_zero_left gives e = 0, so the two are equal.
   ============================================================================ *)
val mult_assoc_vSg2  = mult_assoc_vSg;
fun multassocSg_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtSig
      [(("m",0), ctermSig mt),(("n",0), ctermSig nt),(("k",0), ctermSig kt)] mult_assoc_vSg);
val add_left_cancel_vSg = varify add_left_cancel;
fun add_left_cancel_Sg (mt, at, bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("m",0), ctermSig mt),(("a",0), ctermSig at),(("b",0), ctermSig bt)] add_left_cancel_vSg)
  in Thm.implies_elim inst h end;
val add_eq_zero_left_vSg = varify add_eq_zero_left;
fun add_eq_zero_left_Sg (at, bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("a",0), ctermSig at),(("b",0), ctermSig bt)] add_eq_zero_left_vSg)
  in Thm.implies_elim inst h end;
val le_total_vSg = varify le_total;
fun le_total_Sg (mt, nt) = beta_norm (Drule.infer_instantiate ctxtSig
      [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] le_total_vSg);
val mult_0_vSg2 = mult_0_vSg;
fun mult0Sg_at t = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] mult_0_vSg);
fun multSucSg_at_L (mt,nt) = beta_norm (Drule.infer_instantiate ctxtSig
      [(("m",0), ctermSig mt),(("n",0), ctermSig nt)] mult_Suc_vSg);   (* mult (Suc m) n = add n (mult m n) *)

(* lt Zero c -> Ex c0. oeq c (Suc c0)  : lt 0 c = le 1 c = Ex p. c = add 1 p = Suc p *)
(* We package: given hLtC : jT (lt Zero c), and a body that uses c0 with c = Suc c0,
   produce the goal.  lt Zero c unfolds to Ex(%p. oeq c (add (Suc Zero) p)). *)

val mult_left_cancel =
  let
    val cF = Free("c", natT); val aF = Free("a", natT); val bF = Free("b", natT);
    val hLtC = Thm.assume (ctermSig (jT (lt ZeroC cF)));        (* le (Suc 0) c = Ex p. c = (Suc 0)+p *)
    val hEq  = Thm.assume (ctermSig (jT (oeq (mult cF aF)(mult cF bF))));
    val goalC = oeq aF bF;
    (* peel lt 0 c : witness p, c = add (Suc 0) p = Suc(add 0 p) = Suc p *)
    val ltAbs = Abs("p", natT, oeq cF (add (suc ZeroC) (Bound 0)));
    fun ltBody pF hp =       (* hp : oeq c (add (Suc 0) p) *)
      let
        (* c = Suc p : add (Suc 0) p = Suc(add 0 p) = Suc p *)
        val a1 = addSucSg_at (ZeroC, pF);              (* add (Suc 0) p = Suc(add 0 p) *)
        val a0 = add0Sg_at pF;                         (* add 0 p = p *)
        val a0s = Suc_cong OF [a0];                    (* Suc(add 0 p) = Suc p *)
        val cSucp = oeq_trans OF [hp, oeq_trans OF [a1, a0s]];   (* c = Suc p *)
        (* helper: from oeq (mult c e) Zero derive oeq e Zero, using c = Suc p:
             mult c e = mult (Suc p) e [cong via cSucp] = add e (mult p e) [mult_Suc];
             so add e (mult p e) = 0 -> add_eq_zero_left -> e = 0. *)
        fun mult_c_e_zero (eT, hMZ) =       (* hMZ : oeq (mult c e) Zero -> oeq e Zero *)
          let
            (* mult c e = mult (Suc p) e via cong-l (subst c->Suc p in mult _ e) *)
            val zC = Free("z_mc", natT);
            val Pmc = Term.lambda zC (oeq (mult cF eT) (mult zC eT));
            val rfl = oeqreflSg_at (mult cF eT);
            val ceq = substPredSg (Pmc, cF, suc pF) cSucp rfl;   (* oeq (mult c e)(mult (Suc p) e) *)
            val msuc = multSucSg_at_L (pF, eT);                  (* mult (Suc p) e = add e (mult p e) *)
            val chain = oeq_trans OF [oeq_sym OF [ceq], hMZ];    (* oeq (mult (Suc p) e) Zero ... wait *)
            (* hMZ : oeq (mult c e) Zero ; ceq : mult c e = mult (Suc p) e
               -> mult (Suc p) e = mult c e = 0 : oeq_sym ceq then trans hMZ *)
            val mze = oeq_trans OF [oeq_sym OF [ceq], hMZ];      (* oeq (mult (Suc p) e) Zero *)
            val adde = oeq_trans OF [oeq_sym OF [msuc], mze];    (* oeq (add e (mult p e)) Zero *)
          in add_eq_zero_left_Sg (eT, mult pF eT) adde end;     (* oeq e Zero *)
        (* le_total a b *)
        val tot = le_total_Sg (aF, bF);                (* Disj (le a b)(le b a) *)
        (* CASE le a b : b = a+e -> 0 = mult c e -> e = 0 -> a = b *)
        val caseAB =
          let
            val leAbsAB = Abs("e", natT, oeq bF (add aF (Bound 0)));
            val hle = Thm.assume (ctermSig (jT (le aF bF)));
            fun abBody eF heb =      (* heb : oeq b (add a e) *)
              let
                (* mult c b = mult c (add a e) = add (mult c a)(mult c e) [left_distrib via cong] *)
                val zB = Free("z_b", natT);
                val Pcb = Term.lambda zB (oeq (mult cF bF) (mult cF zB));
                val rflb = oeqreflSg_at (mult cF bF);
                val cb_eq = substPredSg (Pcb, bF, add aF eF) heb rflb;  (* mult c b = mult c (add a e) *)
                val ld = left_distribSg_at (cF, aF, eF);                (* mult c (a+e) = add (mult c a)(mult c e) *)
                val cb_dist = oeq_trans OF [cb_eq, ld];                 (* mult c b = add (mult c a)(mult c e) *)
                (* hEq : mult c a = mult c b ; so mult c a = add (mult c a)(mult c e) *)
                val caEq = oeq_trans OF [hEq, cb_dist];                 (* mult c a = add (mult c a)(mult c e) *)
                (* rewrite LHS mult c a = add (mult c a) 0 : need add (mult c a) 0 = mult c a (add0r) *)
                val a0r = add0rSg_at (mult cF aF);                      (* add (mult c a) 0 = mult c a *)
                val caEq2 = oeq_trans OF [a0r, caEq];                   (* add (mult c a) 0 = add (mult c a)(mult c e) *)
                val canc = add_left_cancel_Sg (mult cF aF, ZeroC, mult cF eF) caEq2;  (* 0 = mult c e *)
                val mze = oeq_sym OF [canc];                            (* mult c e = 0 *)
                val e0 = mult_c_e_zero (eF, mze);                       (* e = 0 *)
                (* b = add a e ; e = 0 -> b = add a 0 = a *)
                val zE = Free("z_e", natT);
                val Pbe = Term.lambda zE (oeq bF (add aF zE));
                val rflbe = heb;     (* oeq b (add a e) *)
                val bAdd0 = substPredSg (Pbe, eF, ZeroC) e0 rflbe;     (* b = add a 0 *)
                val a0a = add0rSg_at aF;                                (* add a 0 = a *)
                val bEqA = oeq_trans OF [bAdd0, a0a];                   (* b = a *)
                val res = oeq_sym OF [bEqA];                            (* a = b *)
              in res end;
            val r = exE_elimSg (leAbsAB, goalC) hle "e_ab" abBody;
          in Thm.implies_intr (ctermSig (jT (le aF bF))) r end;
        (* CASE le b a : a = b+e -> a = b symmetric *)
        val caseBA =
          let
            val leAbsBA = Abs("e", natT, oeq aF (add bF (Bound 0)));
            val hle = Thm.assume (ctermSig (jT (le bF aF)));
            fun baBody eF hea =      (* hea : oeq a (add b e) *)
              let
                val zA = Free("z_a", natT);
                val Pca = Term.lambda zA (oeq (mult cF aF) (mult cF zA));
                val rfla = oeqreflSg_at (mult cF aF);
                val ca_eq = substPredSg (Pca, aF, add bF eF) hea rfla;  (* mult c a = mult c (add b e) *)
                val ld = left_distribSg_at (cF, bF, eF);                (* mult c (b+e) = add (mult c b)(mult c e) *)
                val ca_dist = oeq_trans OF [ca_eq, ld];                 (* mult c a = add (mult c b)(mult c e) *)
                (* hEq : mult c a = mult c b ; so mult c b = add (mult c b)(mult c e) *)
                val cbEq = oeq_trans OF [oeq_sym OF [hEq], ca_dist];    (* mult c b = add (mult c b)(mult c e) *)
                val a0r = add0rSg_at (mult cF bF);                      (* add (mult c b) 0 = mult c b *)
                val cbEq2 = oeq_trans OF [a0r, cbEq];                   (* add (mult c b) 0 = add (mult c b)(mult c e) *)
                val canc = add_left_cancel_Sg (mult cF bF, ZeroC, mult cF eF) cbEq2;  (* 0 = mult c e *)
                val mze = oeq_sym OF [canc];                            (* mult c e = 0 *)
                val e0 = mult_c_e_zero (eF, mze);                       (* e = 0 *)
                val zE = Free("z_e2", natT);
                val Pae = Term.lambda zE (oeq aF (add bF zE));
                val aAdd0 = substPredSg (Pae, eF, ZeroC) e0 hea;       (* a = add b 0 *)
                val b0b = add0rSg_at bF;                                (* add b 0 = b *)
                val aEqB = oeq_trans OF [aAdd0, b0b];                   (* a = b *)
              in aEqB end;
            val r = exE_elimSg (leAbsBA, goalC) hle "e_ba" baBody;
          in Thm.implies_intr (ctermSig (jT (le bF aF))) r end;
        val res = disjE_elimSg (le aF bF, le bF aF, goalC) tot caseAB caseBA;
      in res end;
    val body = exE_elimSg (ltAbs, goalC) hLtC "p_lc" ltBody;
    val d1 = Thm.implies_intr (ctermSig (jT (oeq (mult cF aF)(mult cF bF)))) body;
    val d2 = Thm.implies_intr (ctermSig (jT (lt ZeroC cF))) d1;
  in varify d2 end;

val cVlc = Var (("c",0), natT); val aVlc = Var (("a",0), natT); val bVlc = Var (("b",0), natT);
val i_mlc = Logic.mk_implies (jT (lt ZeroC cVlc),
              Logic.mk_implies (jT (oeq (mult cVlc aVlc)(mult cVlc bVlc)), jT (oeq aVlc bVlc)));
val r_mlc = checkSg ("mult_left_cancel", mult_left_cancel, i_mlc);
val () = if r_mlc then out "MULT_LEFT_CANCEL_OK\n" else out "MULT_LEFT_CANCEL_FAIL\n";

fun mult_left_cancel_Sg (cT, aT, bT) hPos hEq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("c",0), ctermSig cT),(("a",0), ctermSig aT),(("b",0), ctermSig bT)] (varify mult_left_cancel))
  in Thm.implies_elim (Thm.implies_elim inst hPos) hEq end;

(* ============================================================================
   STEP 2 : dvd lift + helpers for completeness.
   ============================================================================ *)
val dvd_refl_vSg       = varify dvd_refl;
val dvd_mult_right_vSg2 = varify dvd_mult_right;
val dvd_mult_cong_vSg  = varify dvd_mult_cong;
val dvd_trans_vSg      = varify dvd_trans;

fun dvd_refl_Sg t = beta_norm (Drule.infer_instantiate ctxtSig [(("a",0), ctermSig t)] dvd_refl_vSg);
fun dvd_mult_right_Sg (aT,bT,cT) h =   (* dvd a b -> dvd a (mult b c) *)
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("a",0), ctermSig aT),(("b",0), ctermSig bT),(("c",0), ctermSig cT)] dvd_mult_right_vSg2)
  in Thm.implies_elim inst h end;
fun dvd_mult_cong_Sg (aT,bT,cT) h =    (* dvd a b -> dvd (mult a c)(mult b c) *)
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("a",0), ctermSig aT),(("b",0), ctermSig bT),(("c",0), ctermSig cT)] dvd_mult_cong_vSg)
  in Thm.implies_elim inst h end;
fun dvd_trans_Sg (aT,bT,cT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("a",0), ctermSig aT),(("b",0), ctermSig bT),(("c",0), ctermSig cT)] dvd_trans_vSg)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;

(* dvd_cong_r : substitute oeq x y into dvd a x giving dvd a y *)
fun dvd_cong_target (aT, xT, yT) hxy hdvd =   (* oeq x y -> dvd a x -> dvd a y *)
  let val zF = Free("z_dt", natT);
      val Pabs = Term.lambda zF (dvd aT zF);
  in substPredSg (Pabs, xT, yT) hxy hdvd end;
(* dvd_cong_divisor : substitute oeq a b into dvd a x giving dvd b x *)
fun dvd_cong_divisor (aT, bT, xT) hab hdvd =  (* oeq a b -> dvd a x -> dvd b x *)
  let val zF = Free("z_dd", natT);
      val Pabs = Term.lambda zF (dvd zF xT);
  in substPredSg (Pabs, aT, bT) hab hdvd end;

(* ex_middle on a formula A : Disj A (neg A) *)
fun ex_middle_Sg At = ex_middle_atSg At;

(* dvd_factor_right : dvd a (mult b a)   (a divides b*a)  -- via commute + dvd_mult_right(dvd_refl) *)
fun dvd_factor_right (aT, bT) =
  let
    val dr  = dvd_refl_Sg aT;                                  (* dvd a a *)
    val dmr = dvd_mult_right_Sg (aT, aT, bT) dr;               (* dvd a (mult a b) *)
    val comm = multcommSg_at (aT, bT);                         (* mult a b = mult b a *)
  in dvd_cong_target (aT, mult aT bT, mult bT aT) comm dmr end; (* dvd a (mult b a) *)

val () = out "DIVCHAR_STEP2_DVD_OK\n";

(* ============================================================================
   STEP 3 : helper  lt0_of_lt1 : lt (Suc Zero) q ==> lt Zero q
   (q > 1 implies q > 0).  lt 1 q = le 2 q = Ex p. q = 2+p ; lt 0 q = le 1 q,
   witness (Suc p) : q = 2+p = Suc(1+p) = Suc(Suc(0+p)) ... = add (Suc 0)(Suc p). *)
val lt0_of_lt1 =
  let
    val qF = Free("q", natT);
    val hLt1 = Thm.assume (ctermSig (jT (lt (suc ZeroC) qF)));  (* le 2 q = Ex p. q = add 2 p *)
    val exAbs = Abs("p", natT, oeq qF (add (suc (suc ZeroC)) (Bound 0)));
    val goalC = lt ZeroC qF;     (* le 1 q = Ex p. q = add 1 p *)
    fun body pF hp =      (* hp : oeq q (add (Suc(Suc 0)) p) *)
      let
        (* add 2 p = Suc(add 1 p) ; add 1 (Suc p) = Suc(add 0 (Suc p)) = Suc(Suc p);
           we want q = add (Suc 0)(Suc p).  add (Suc 0)(Suc p) = Suc(add 0 (Suc p)) = Suc(Suc p).
           and add 2 p = Suc(add 1 p) = Suc(Suc(add 0 p)) = Suc(Suc p). *)
        val l1 = addSucSg_at (suc ZeroC, pF);            (* add 2 p = Suc(add 1 p) *)
        val l2 = addSucSg_at (ZeroC, pF);                (* add 1 p = Suc(add 0 p) *)
        val l3 = add0Sg_at pF;                           (* add 0 p = p *)
        val l2s = Suc_cong OF [l2];                      (* Suc(add 1 p) = Suc(Suc(add 0 p)) *)
        val l3s = Suc_cong OF [Suc_cong OF [l3]];        (* Suc(Suc(add 0 p)) = Suc(Suc p) *)
        val add2p = oeq_trans OF [oeq_trans OF [l1, l2s], l3s];   (* add 2 p = Suc(Suc p) *)
        val qSS = oeq_trans OF [hp, add2p];              (* q = Suc(Suc p) *)
        (* add (Suc 0)(Suc p) = Suc(add 0 (Suc p)) = Suc(Suc p) *)
        val r1 = addSucSg_at (ZeroC, suc pF);            (* add 1 (Suc p) = Suc(add 0 (Suc p)) *)
        val r2 = add0Sg_at (suc pF);                     (* add 0 (Suc p) = Suc p *)
        val r2s = Suc_cong OF [r2];                      (* Suc(add 0 (Suc p)) = Suc(Suc p) *)
        val add1Sp = oeq_trans OF [r1, r2s];             (* add 1 (Suc p) = Suc(Suc p) *)
        val qEq = oeq_trans OF [qSS, oeq_sym OF [add1Sp]];   (* q = add 1 (Suc p) *)
      in le_introSg (suc ZeroC, qF, suc pF) qEq end;     (* le 1 q = lt 0 q *)
    val r = exE_elimSg (exAbs, goalC) hLt1 "p_l0" body;
    val disch = Thm.implies_intr (ctermSig (jT (lt (suc ZeroC) qF))) r;
  in varify disch end;
fun lt0_of_lt1_Sg q h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig [(("q",0), ctermSig q)] (varify lt0_of_lt1))
  in Thm.implies_elim inst h end;

val () = out "DIVCHAR_STEP3_LT0_OK\n";

(* ============================================================================
   STEP 4 : THE COMPLETENESS / FORWARD DIRECTION (the headline, the hard part).
   ----------------------------------------------------------------------------
     div2aq_complete :
       prime2 q ==>
       (!!e. dvd e (pow 2 a) ==> Ex i. le i a /\ oeq e (pow 2 i))   [pow2_dvd_char @ a]
       ==> dvd d (mult (pow 2 a) q)
       ==> Disj (Ex i. (le i a) /\ (oeq d (pow 2 i)))
                (Ex i. (le i a) /\ (oeq d (mult (pow 2 i) q)))
   i.e. every divisor of N = 2^a*q is 2^i or 2^i*q for some i<=a.
   ----------------------------------------------------------------------------
   Proof (FLAT, no induction on a):  Let A2 = pow 2 a, N = mult A2 q.
     dvd q N (q | N, since N = A2*q).  Peel dvd d N : N = mult d k.
     euclid_lemma (prime2 q) on  dvd q (mult d k) :  dvd q d  \/  dvd q k.
     Case dvd q d : d = q*e ; N = (q*e)*k ; N = q*A2 ; q*A2 = q*(e*k) [assoc/comm]
       cancel q (q>0) : A2 = e*k => dvd e A2 ; pow2_dvd_char(e) => e = 2^i, i<=a;
       d = q*2^i = 2^i*q [comm] -> RIGHT disjunct.
     Case dvd q k : k = q*k' ; N = d*(q*k') ; N = q*A2 ; q*A2 = q*(d*k') [comm/assoc]
       cancel q : A2 = d*k' => dvd d A2 ; pow2_dvd_char(d) => d = 2^i, i<=a ->
       LEFT disjunct.
   ============================================================================ *)

val twoCd = suc (suc ZeroC);          (* 2 *)
val pow2 = fn t => pow twoCd t;       (* pow 2 t *)

(* conclusion existential predicates (capture-safe, fresh Free iF) *)
fun leftEx (dT, aT) =
  let val iF = Free("i_le", natT)
  in mkEx (Term.lambda iF (mkConj (le iF aT) (oeq dT (pow2 iF)))) end;
fun rightEx (dT, aT, qT) =
  let val iF = Free("i_re", natT)
  in mkEx (Term.lambda iF (mkConj (le iF aT) (oeq dT (mult (pow2 iF) qT)))) end;

(* conjI / conjunct on ctxtSig *)
val conjI_vSg = varify conjI_ax;
fun conjI_Sg (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("A",0), ctermSig At),(("B",0), ctermSig Bt)] conjI_vSg)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;

(* the pow2_dvd_char hypothesis shape, at exponent aT, applied to a concrete eT *)
fun pow2charConcl (eT, aT) =
  let val iF = Free("i_pc", natT)
  in mkEx (Term.lambda iF (mkConj (le iF aT) (oeq eT (pow2 iF)))) end;

val div2aq_complete =
  let
    val qF = Free("q", natT); val aF = Free("a", natT); val dF = Free("d", natT);
    val A2 = pow2 aF;
    val NN = mult A2 qF;
    (* premises *)
    val hPrime = Thm.assume (ctermSig (jT (prime2 qF)));
    (* pow2_dvd_char @ a as a META-universal META-implication premise *)
    val eMeta = Free("e_pc", natT);
    val pcPremise = Logic.all eMeta
        (Logic.mk_implies (jT (dvd eMeta A2), jT (pow2charConcl (eMeta, aF))));
    val hPC = Thm.assume (ctermSig pcPremise);
    (* apply pow2_dvd_char at a concrete term tT (returns jT (Ex i. le i a /\ oeq t (2^i))) *)
    fun applyPC (tT, hDvdT) =
      let val spec = beta_norm (Thm.forall_elim (ctermSig tT) hPC)   (* jT(dvd t A2) ==> jT(Ex ...) *)
      in Thm.implies_elim spec hDvdT end;
    val hN = Thm.assume (ctermSig (jT (dvd dF NN)));
    val goalC = mkDisj (leftEx (dF, aF)) (rightEx (dF, aF, qF));
    (* q > 0 *)
    val q_gt1 = prime2_gt1_Sg qF hPrime;       (* lt 1 q *)
    val q_gt0 = lt0_of_lt1_Sg qF q_gt1;        (* lt 0 q *)
    (* dvd q N : dvd q (mult A2 q) = dvd q (mult A2 q) ; dvd_factor_right (q, A2) gives dvd q (mult A2 q) *)
    val dvd_q_N = dvd_factor_right (qF, A2);    (* dvd q (mult A2 q) = dvd q N *)
    (* N = mult A2 q = mult q A2 (commute) *)
    val NcommQ = multcommSg_at (A2, qF);        (* mult A2 q = mult q A2 *)
    (* peel hN : N = mult d k *)
    val nAbs = Abs("k", natT, oeq NN (mult dF (Bound 0)));
    fun nBody kF hk =      (* hk : oeq N (mult d k) *)
      let
        (* dvd q (mult d k) : subst N -> (mult d k) into dvd q N *)
        val dvd_q_dk = dvd_cong_target (qF, NN, mult dF kF) hk dvd_q_N;  (* dvd q (mult d k) *)
        (* euclid_lemma : Disj (dvd q d)(dvd q k) *)
        val disj = euclid_lemma_Sg (qF, dF, kF) hPrime dvd_q_dk;
        (* ---- CASE dvd q d ---- *)
        val caseQD =
          let
            val hqd = Thm.assume (ctermSig (jT (dvd qF dF)));
            (* peel : d = mult q e *)
            val dAbs = Abs("e", natT, oeq dF (mult qF (Bound 0)));
            fun dBody eF hde =      (* hde : oeq d (mult q e) *)
              let
                (* A2 = mult e k :
                     N = mult A2 q = mult q A2 (NcommQ) ;
                     N = mult d k = mult (mult q e) k [subst d] = mult q (mult e k) [assoc]
                     so mult q A2 = mult q (mult e k) ; cancel q -> A2 = mult e k. *)
                (* N = mult d k from hk ; subst d -> mult q e : N = mult (mult q e) k *)
                val zD = Free("z_d", natT);
                val Pnk = Term.lambda zD (oeq NN (mult zD kF));
                val rfl_nk = hk;     (* oeq N (mult d k) *)
                val n_qek = substPredSg (Pnk, dF, mult qF eF) hde rfl_nk;  (* oeq N (mult (mult q e) k) *)
                (* mult (mult q e) k = mult q (mult e k) [assoc] *)
                val assoc = multassocSg_at (qF, eF, kF);   (* mult (mult q e) k = mult q (mult e k) *)
                val n_q_ek = oeq_trans OF [n_qek, assoc];  (* oeq N (mult q (mult e k)) *)
                (* mult q A2 = N (sym NcommQ) = mult q (mult e k) *)
                val qA2_eq = oeq_trans OF [oeq_sym OF [NcommQ], n_q_ek];  (* oeq (mult q A2)(mult q (mult e k)) *)
                val A2_ek = mult_left_cancel_Sg (qF, A2, mult eF kF) q_gt0 qA2_eq;  (* oeq A2 (mult e k) *)
                (* dvd e A2 : witness k, A2 = mult e k *)
                val dvd_e_A2 = dvd_introSg (eF, A2, kF) A2_ek;   (* dvd e A2 *)
                (* pow2_dvd_char(e) : Ex i. le i a /\ oeq e (2^i) *)
                val pcE = applyPC (eF, dvd_e_A2);
                (* peel : i with le i a and oeq e (2^i) -> build RIGHT disjunct *)
                val iAbs = Term.lambda (Free("i_x", natT))
                             (mkConj (le (Free("i_x", natT)) aF) (oeq eF (pow2 (Free("i_x", natT)))));
                fun iBody iF hConj =   (* hConj : le i a /\ oeq e (2^i) *)
                  let
                    val hle  = conjunct1_Sg (le iF aF, oeq eF (pow2 iF)) hConj;  (* le i a *)
                    val heqe = conjunct2_Sg (le iF aF, oeq eF (pow2 iF)) hConj;  (* oeq e (2^i) *)
                    (* d = mult q e ; e = 2^i -> d = mult q (2^i) = mult (2^i) q [comm] *)
                    val zE = Free("z_e", natT);
                    val Pde = Term.lambda zE (oeq dF (mult qF zE));
                    val d_q2i = substPredSg (Pde, eF, pow2 iF) heqe hde;  (* oeq d (mult q (2^i)) *)
                    val comm = multcommSg_at (qF, pow2 iF);                (* mult q (2^i) = mult (2^i) q *)
                    val d_2iq = oeq_trans OF [d_q2i, comm];                (* oeq d (mult (2^i) q) *)
                    (* build Conj (le i a)(oeq d (mult (2^i) q)) then exI -> rightEx *)
                    val cj = conjI_Sg (le iF aF, oeq dF (mult (pow2 iF) qF)) hle d_2iq;
                    val rPred = Term.lambda (Free("i_re", natT))
                                  (mkConj (le (Free("i_re", natT)) aF)
                                          (oeq dF (mult (pow2 (Free("i_re", natT))) qF)));
                    val rex = exI_Sg (rPred, iF) cj;   (* rightEx d a q *)
                  in disjI2_Sg (leftEx (dF, aF), rightEx (dF, aF, qF)) rex end;
                val rres = exE_elimSg (iAbs, goalC) pcE "i_qd" iBody;
              in rres end;
            val r = exE_elimSg (dAbs, goalC) hqd "e_qd" dBody;
          in Thm.implies_intr (ctermSig (jT (dvd qF dF))) r end;
        (* ---- CASE dvd q k ---- *)
        val caseQK =
          let
            val hqk = Thm.assume (ctermSig (jT (dvd qF kF)));
            val kAbs = Abs("kk", natT, oeq kF (mult qF (Bound 0)));
            fun kBody kpF hkk =     (* hkk : oeq k (mult q k') *)
              let
                (* A2 = mult d k' :
                     N = mult d k ; k = mult q k' -> N = mult d (mult q k')
                       = mult (mult d q) k' [assoc sym] = mult (mult q d) k' [comm d,q]
                       = mult q (mult d k') [assoc]
                     N = mult q A2 -> cancel q -> A2 = mult d k'. *)
                val zK = Free("z_k", natT);
                val Pnk2 = Term.lambda zK (oeq NN (mult dF zK));
                val n_dqk = substPredSg (Pnk2, kF, mult qF kpF) hkk hk;  (* oeq N (mult d (mult q k')) *)
                (* mult d (mult q k') = mult (mult d q) k' [assoc sym] *)
                val assoc1 = multassocSg_at (dF, qF, kpF);    (* mult (mult d q) k' = mult d (mult q k') *)
                val n_dq_k = oeq_trans OF [n_dqk, oeq_sym OF [assoc1]];  (* oeq N (mult (mult d q) k') *)
                (* mult d q = mult q d [comm] -> mult (mult d q) k' = mult (mult q d) k' *)
                val commdq = multcommSg_at (dF, qF);          (* mult d q = mult q d *)
                val congk = mult_cong_lSg (mult dF qF, mult qF dF, kpF) commdq;  (* mult (mult d q) k' = mult (mult q d) k' *)
                val n_qd_k = oeq_trans OF [n_dq_k, congk];     (* oeq N (mult (mult q d) k') *)
                (* mult (mult q d) k' = mult q (mult d k') [assoc] *)
                val assoc2 = multassocSg_at (qF, dF, kpF);     (* mult (mult q d) k' = mult q (mult d k') *)
                val n_q_dk = oeq_trans OF [n_qd_k, assoc2];    (* oeq N (mult q (mult d k')) *)
                val qA2_eq = oeq_trans OF [oeq_sym OF [NcommQ], n_q_dk];  (* oeq (mult q A2)(mult q (mult d k')) *)
                val A2_dk = mult_left_cancel_Sg (qF, A2, mult dF kpF) q_gt0 qA2_eq;  (* oeq A2 (mult d k') *)
                val dvd_d_A2 = dvd_introSg (dF, A2, kpF) A2_dk;   (* dvd d A2 *)
                val pcD = applyPC (dF, dvd_d_A2);
                val iAbs = Term.lambda (Free("i_y", natT))
                             (mkConj (le (Free("i_y", natT)) aF) (oeq dF (pow2 (Free("i_y", natT)))));
                fun iBody iF hConj =
                  let
                    val hle  = conjunct1_Sg (le iF aF, oeq dF (pow2 iF)) hConj;  (* le i a *)
                    val heqd = conjunct2_Sg (le iF aF, oeq dF (pow2 iF)) hConj;  (* oeq d (2^i) *)
                    val cj = conjI_Sg (le iF aF, oeq dF (pow2 iF)) hle heqd;
                    val lPred = Term.lambda (Free("i_le", natT))
                                  (mkConj (le (Free("i_le", natT)) aF) (oeq dF (pow2 (Free("i_le", natT)))));
                    val lex = exI_Sg (lPred, iF) cj;   (* leftEx d a *)
                  in disjI1_Sg (leftEx (dF, aF), rightEx (dF, aF, qF)) lex end;
                val lres = exE_elimSg (iAbs, goalC) pcD "i_qk" iBody;
              in lres end;
            val r = exE_elimSg (kAbs, goalC) hqk "kp_qk" kBody;
          in Thm.implies_intr (ctermSig (jT (dvd qF kF))) r end;
        val res = disjE_elimSg (dvd qF dF, dvd qF kF, goalC) disj caseQD caseQK;
      in res end;
    val body = exE_elimSg (nAbs, goalC) hN "k_top" nBody;
    val d1 = Thm.implies_intr (ctermSig (jT (dvd dF NN))) body;
    val d2 = Thm.implies_intr (ctermSig pcPremise) d1;
    val d3 = Thm.implies_intr (ctermSig (jT (prime2 qF))) d2;
  in varify d3 end;

val () = out "DIVCHAR_COMPLETE_BUILT\n";

(* ============================================================================
   VERIFICATION of div2aq_complete.
   ============================================================================ *)
val qVc = Var (("q",0), natT); val aVc = Var (("a",0), natT); val dVc = Var (("d",0), natT);
val A2v = pow2 aVc;
val NNv = mult A2v qVc;
val eMv = Free("e_pc", natT);   (* same Free name used in the construction *)
val pcPrem_intended = Logic.all eMv
      (Logic.mk_implies (jT (dvd eMv A2v), jT (pow2charConcl (eMv, aVc))));
val goal_intended = mkDisj (leftEx (dVc, aVc)) (rightEx (dVc, aVc, qVc));
val i_complete = Logic.mk_implies (jT (prime2 qVc),
      Logic.mk_implies (pcPrem_intended,
        Logic.mk_implies (jT (dvd dVc NNv), jT goal_intended)));

val nh_complete = length (Thm.hyps_of div2aq_complete);
val ac_complete = (Thm.prop_of div2aq_complete) aconv i_complete;
val () = out ("DIVCHAR_COMPLETE hyps=" ^ Int.toString nh_complete
              ^ " aconv=" ^ Bool.toString ac_complete ^ "\n");
val () =
  if nh_complete = 0 andalso ac_complete then out "DIVCHAR_COMPLETE_OK\n"
  else (out ("  got      = " ^ Syntax.string_of_term ctxtSig (Thm.prop_of div2aq_complete) ^ "\n"
             ^ "  intended = " ^ Syntax.string_of_term ctxtSig i_complete ^ "\n");
        out "DIVCHAR_COMPLETE_BAD\n");

(* ============================================================================
   SOUNDNESS PROBES on div2aq_complete.
   ============================================================================ *)
val cprop = Thm.prop_of div2aq_complete;
(* (1) keeps the prime2 q premise verbatim (first premise) *)
val probe_complete_prime =
  (case cprop of (Const("Pure.imp",_) $ h $ _) => (h aconv (jT (prime2 qVc))) | _ => false);
(* (2) genuinely conditional : NOT aconv the prime-free 2-premise variant *)
val cprop_noprime = Logic.mk_implies (pcPrem_intended,
      Logic.mk_implies (jT (dvd dVc NNv), jT goal_intended));
val probe_complete_needs_prime = not (cprop aconv cprop_noprime);
(* (3) genuinely conditional on the dvd premise : NOT aconv the unconditional disjunction *)
val probe_complete_needs_dvd = not (cprop aconv (jT goal_intended));
val () =
  if probe_complete_prime then out "PROBE_OK div2aq_complete keeps prime2 q\n"
  else out "PROBE_FAIL div2aq_complete dropped prime2 q!\n";
val () =
  if probe_complete_needs_prime then out "PROBE_OK div2aq_complete is conditional on prime2\n"
  else out "PROBE_FAIL div2aq_complete prime-free!\n";
val () =
  if probe_complete_needs_dvd then out "PROBE_OK div2aq_complete is conditional on the divisor premise\n"
  else out "PROBE_FAIL div2aq_complete unconditional disjunction!\n";

(* ============================================================================
   EASY DIRECTION (E1 / SOUNDNESS of the support set) : every characterized
   point genuinely divides N = 2^a*q.
     pow2_dvd_N   : le i a ==> dvd (pow 2 i) (mult (pow 2 a) q)
     pow2q_dvd_N  : le i a ==> dvd (mult (pow 2 i) q) (mult (pow 2 a) q)
   Together with div2aq_complete this is the FULL characterization:
     dvd d (2^a*q)  <=>  d in { 2^i, 2^i*q : i<=a }.
   Key sub-fact: le i a ==> dvd (pow 2 i)(pow 2 a)  (pow_le_dvd: 2^i | 2^a).
     2^a = 2^(i+(a-i)) = 2^i * 2^(a-i)  [pow_add], so 2^i | 2^a, witness 2^(a-i).
   ============================================================================ *)
(* pow_add on ctxtSig : oeq (pow a (add m n)) (mult (pow a m)(pow a n)) *)
val pow_add_vSg = varify pow_add;
fun pow_add_Sg (aT,mT,nT) = beta_norm (Drule.infer_instantiate ctxtSig
      [(("a",0), ctermSig aT),(("m",0), ctermSig mT),(("n",0), ctermSig nT)] pow_add_vSg);

(* pow_le_dvd : le i a ==> dvd (pow 2 i)(pow 2 a).
   le i a : Ex w. a = add i w.  pow 2 a = pow 2 (add i w) = mult (pow 2 i)(pow 2 w)
   [pow_add], so dvd (pow 2 i)(pow 2 a), witness (pow 2 w). *)
val pow_le_dvd =
  let
    val iF = Free("i", natT); val aF = Free("a", natT);
    val hle = Thm.assume (ctermSig (jT (le iF aF)));   (* Ex w. a = add i w *)
    val leAbs = Abs("w", natT, oeq aF (add iF (Bound 0)));
    val goalC = dvd (pow2 iF) (pow2 aF);
    fun body wF hw =     (* hw : oeq a (add i w) *)
      let
        (* pow 2 a = pow 2 (add i w) [cong via hw] = mult (pow 2 i)(pow 2 w) [pow_add] *)
        val zA = Free("z_pa", natT);
        val Ppa = Term.lambda zA (oeq (pow2 aF) (pow2 zA));
        val rfl = oeqreflSg_at (pow2 aF);
        val pa_eq = substPredSg (Ppa, aF, add iF wF) hw rfl;   (* pow 2 a = pow 2 (add i w) *)
        val padd = pow_add_Sg (twoCd, iF, wF);                 (* pow 2 (add i w) = mult (pow 2 i)(pow 2 w) *)
        val pa_prod = oeq_trans OF [pa_eq, padd];              (* pow 2 a = mult (pow 2 i)(pow 2 w) *)
      in dvd_introSg (pow2 iF, pow2 aF, pow2 wF) pa_prod end;  (* dvd (pow 2 i)(pow 2 a) *)
    val r = exE_elimSg (leAbs, goalC) hle "w_pl" body;
    val disch = Thm.implies_intr (ctermSig (jT (le iF aF))) r;
  in varify disch end;
fun pow_le_dvd_Sg (iT, aT) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("i",0), ctermSig iT),(("a",0), ctermSig aT)] (varify pow_le_dvd))
  in Thm.implies_elim inst h end;

(* pow2_dvd_N : le i a ==> dvd (pow 2 i)(mult (pow 2 a) q)
   2^i | 2^a [pow_le_dvd] ; 2^a | 2^a*q [dvd_mult_right(dvd_refl)] ; dvd_trans. *)
val pow2_dvd_N =
  let
    val iF = Free("i", natT); val aF = Free("a", natT); val qF = Free("q", natT);
    val A2 = pow2 aF;
    val hle = Thm.assume (ctermSig (jT (le iF aF)));
    val d1 = pow_le_dvd_Sg (iF, aF) hle;                       (* dvd (pow 2 i) A2 *)
    val d2 = dvd_mult_right_Sg (A2, A2, qF) (dvd_refl_Sg A2);  (* dvd A2 (mult A2 q) *)
    val d3 = dvd_trans_Sg (pow2 iF, A2, mult A2 qF) d1 d2;     (* dvd (pow 2 i)(mult A2 q) *)
    val disch = Thm.implies_intr (ctermSig (jT (le iF aF))) d3;
  in varify disch end;

(* pow2q_dvd_N : le i a ==> dvd (mult (pow 2 i) q)(mult (pow 2 a) q)
   dvd (pow 2 i) A2 [pow_le_dvd] ; dvd_mult_cong -> dvd (mult (pow 2 i) q)(mult A2 q). *)
val pow2q_dvd_N =
  let
    val iF = Free("i", natT); val aF = Free("a", natT); val qF = Free("q", natT);
    val A2 = pow2 aF;
    val hle = Thm.assume (ctermSig (jT (le iF aF)));
    val d1 = pow_le_dvd_Sg (iF, aF) hle;                            (* dvd (pow 2 i) A2 *)
    val d2 = dvd_mult_cong_Sg (pow2 iF, A2, qF) d1;                 (* dvd (mult (pow 2 i) q)(mult A2 q) *)
    val disch = Thm.implies_intr (ctermSig (jT (le iF aF))) d2;
  in varify disch end;

(* validation of E1 *)
val iVe = Var (("i",0), natT); val aVe = Var (("a",0), natT); val qVe = Var (("q",0), natT);
val i_pow2_dvd_N  = Logic.mk_implies (jT (le iVe aVe), jT (dvd (pow2 iVe)(mult (pow2 aVe) qVe)));
val i_pow2q_dvd_N = Logic.mk_implies (jT (le iVe aVe), jT (dvd (mult (pow2 iVe) qVe)(mult (pow2 aVe) qVe)));
val r_pld  = checkSg ("pow_le_dvd", pow_le_dvd,
              Logic.mk_implies (jT (le iVe aVe), jT (dvd (pow2 iVe)(pow2 aVe))));
val r_p2n  = checkSg ("pow2_dvd_N",  pow2_dvd_N,  i_pow2_dvd_N);
val r_p2qn = checkSg ("pow2q_dvd_N", pow2q_dvd_N, i_pow2q_dvd_N);
val () = if r_pld andalso r_p2n andalso r_p2qn then out "DIVCHAR_E1_OK\n" else out "DIVCHAR_E1_BAD\n";

(* ============================================================================
   DISTINCTNESS (D) : the cross-half separation that needs q ODD.
   ----------------------------------------------------------------------------
     q_ndvd_pow2   : prime2 q ==> neg (dvd 2 q) ==> neg (dvd q (pow 2 k))
                     (an odd prime q never divides a power of 2; induction on k).
     pow2_neq_pow2q: prime2 q ==> neg (dvd 2 q) ==> neg (oeq (pow 2 i)(mult (pow 2 j) q))
                     (no power of 2 equals 2^j*q ; else q | 2^i, contra q_ndvd_pow2).
   These separate the {2^i} half from the {2^i*q} half: the 2(a+1) divisor points
   are genuinely distinct (the support bijection needs this `lnodup`).
   ============================================================================ *)
(* dvd_le on ctxtSig : dvd d n -> (oeq n 0 ==> oFalse) -> le d n *)
val dvd_le_vSg = varify dvd_le;
fun dvd_le_Sg (dT, nT) hdvd hnzMeta =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("d",0), ctermSig dT),(("n",0), ctermSig nT)] dvd_le_vSg)
  in Thm.implies_elim (Thm.implies_elim inst hdvd) hnzMeta end;
val le_antisym_vSg = varify le_antisym;
fun le_antisym_Sg (mT, nT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("m",0), ctermSig mT),(("n",0), ctermSig nT)] le_antisym_vSg)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
val Suc_neq_Zero_vSg2 = varify Suc_neq_Zero_ax;
fun Suc_neq_Zero_Sg2 t = beta_norm (Drule.infer_instantiate ctxtSig [(("n",0), ctermSig t)] Suc_neq_Zero_vSg2);
(* le 2 q from lt 1 q (they are literally equal: lt 1 q = le 2 q) -- identity, no work *)

(* pow 2 k > 0 : neg (oeq (pow 2 k) 0).  pow 2 0 = 1 = Suc 0 (Suc_neq_Zero);
   pow 2 (Suc k) = mult 2 (pow 2 k) = add (pow 2 k)(add (pow 2 k) 0) > 0 ... easier:
   prove by induction: pow 2 k = Suc (something).  We only need: oeq (pow 2 k) 0 ==> oFalse.
   Use: pow_pos : Ex m. oeq (pow 2 k) (Suc m), by induction on k. *)
val pow2_pos =
  let
    fun gbody zt = mkEx (Abs("m", natT, oeq (pow2 zt) (suc (Bound 0))));
    val zV = Free("z", natT);
    val Qpred = Term.lambda zV (gbody zV);
    val kF = Free("k", natT);
    val ind = nat_induct_atSg (Qpred, kF);
    (* base k=0 : pow 2 0 = Suc 0, witness Zero *)
    val base =
      let
        val pz = powZeroSg_at twoCd;                    (* pow 2 0 = Suc 0 *)
        val wAbs = Abs("m", natT, oeq (pow2 ZeroC) (suc (Bound 0)));
      in exI_Sg (wAbs, ZeroC) pz end;                   (* Ex m. pow 2 0 = Suc m *)
    val xF = Free("x", natT);
    val ihprop = jT (gbody xF);
    val IH = Thm.assume (ctermSig ihprop);
    (* step : pow 2 (Suc x) = mult 2 (pow 2 x) ; peel IH : pow 2 x = Suc m0 ;
         mult 2 (Suc m0) = add (Suc m0)(mult 1 (Suc m0)) = ... = Suc(something) ; witness. *)
    val stepconcl =
      let
        val ps = powSucSg_at (twoCd, xF);               (* pow 2 (Suc x) = mult 2 (pow 2 x) *)
        val exAbs = Abs("m", natT, oeq (pow2 xF) (suc (Bound 0)));
        val goalS = gbody (suc xF);
        fun body m0 hm0 =     (* hm0 : oeq (pow 2 x) (Suc m0) *)
          let
            (* mult 2 (pow 2 x) ; subst pow 2 x -> Suc m0 : mult 2 (Suc m0) *)
            val zP = Free("z_pp", natT);
            val Pmp = Term.lambda zP (oeq (pow2 (suc xF)) (mult twoCd zP));
            (* pow 2 (Suc x) = mult 2 (pow 2 x) [ps] -> goal needs witness; first rewrite RHS *)
            (* mult 2 (Suc m0) = add (Suc m0)(mult 1 (Suc m0)) [mult_Suc] = Suc(...) *)
            val msuc = multSucSg_at_L (suc ZeroC, suc m0);   (* mult 2 (Suc m0) = add (Suc m0)(mult 1 (Suc m0)) *)
            val addsuc = addSucSg_at (m0, mult (suc ZeroC)(suc m0));  (* add (Suc m0) X = Suc(add m0 X) *)
            (* mult 2 (Suc m0) = Suc (add m0 (mult 1 (Suc m0))) *)
            val m2sm0 = oeq_trans OF [msuc, addsuc];      (* mult 2 (Suc m0) = Suc(add m0 (mult 1 (Suc m0))) *)
            (* pow 2 (Suc x) = mult 2 (pow 2 x) = mult 2 (Suc m0) [cong] = Suc(...) *)
            val zM = Free("z_m", natT);
            val Pm2 = Term.lambda zM (oeq (mult twoCd (pow2 xF)) (mult twoCd zM));
            val rflm = oeqreflSg_at (mult twoCd (pow2 xF));
            val m2cong = substPredSg (Pm2, pow2 xF, suc m0) hm0 rflm;  (* mult 2 (pow 2 x) = mult 2 (Suc m0) *)
            val chain = oeq_trans OF [oeq_trans OF [ps, m2cong], m2sm0];  (* pow 2 (Suc x) = Suc(add m0 (mult 1 (Suc m0))) *)
            val wAbs = Abs("m", natT, oeq (pow2 (suc xF)) (suc (Bound 0)));
          in exI_Sg (wAbs, add m0 (mult (suc ZeroC)(suc m0))) chain end;
        val r = exE_elimSg (exAbs, goalS) IH "m0_pp" body;
      in r end;
    val step1 = Thm.forall_intr (ctermSig xF) (Thm.implies_intr (ctermSig ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;
(* pow2_nz : (oeq (pow 2 k) 0 ==> oFalse)  -- meta, for dvd_le's nonzero premise *)
fun pow2_nz_meta kT =
  let
    val pp = beta_norm (Drule.infer_instantiate ctxtSig [(("k",0), ctermSig kT)] (varify pow2_pos));
    (* pp : Ex m. oeq (pow 2 k)(Suc m).  Assume oeq (pow 2 k) 0, derive oFalse. *)
    val hz = Thm.assume (ctermSig (jT (oeq (pow2 kT) ZeroC)));
    val exAbs = Abs("m", natT, oeq (pow2 kT) (suc (Bound 0)));
    fun body mF hm =    (* hm : oeq (pow 2 k)(Suc m) *)
      let
        (* Suc m = pow 2 k = 0 : oeq (Suc m) 0 -> Suc_neq_Zero *)
        val sm0 = oeq_trans OF [oeq_sym OF [hm], hz];    (* oeq (Suc m) 0 *)
      in (Suc_neq_Zero_Sg2 mF) OF [sm0] end;              (* oFalse *)
    val fls = exE_elimSg (exAbs, oFalseC) pp "m_nz" body;
  in Thm.implies_intr (ctermSig (jT (oeq (pow2 kT) ZeroC))) fls end;

val () = out "DIVCHAR_POW2POS_OK\n";

(* q_ndvd_pow2 : prime2 q ==> neg (dvd 2 q) ==> neg (dvd q (pow 2 k))  (induction on k) *)
val q_ndvd_pow2 =
  let
    val qF = Free("q", natT);
    val hPrime = Thm.assume (ctermSig (jT (prime2 qF)));
    val hOdd   = Thm.assume (ctermSig (jT (neg (dvd twoCd qF))));   (* dvd 2 q ==> oFalse *)
    val gt1 = prime2_gt1_Sg qF hPrime;             (* lt 1 q = le 2 q *)
    fun gbody zt = neg (dvd qF (pow2 zt));         (* neg (dvd q (pow 2 z)) *)
    val zV = Free("z", natT);
    val Qpred = Term.lambda zV (gbody zV);
    val kF = Free("k", natT);
    val xF = Free("x", natT);
    val ind = nat_induct_atSg (Qpred, kF);
    (* BASE k=0 : neg (dvd q (pow 2 0)) = neg (dvd q 1).
         assume dvd q 1 ; dvd_le (1 != 0) -> le q 1 ; with le 2 q -> le 2 1 -> ... contra.
         simpler: le q 1 and lt 1 q = le 2 q ; le 2 q ; le_trans (le 2 1)? need le q 1 & le 2 q.
         Actually q<=1 and 2<=q -> 2<=1 (le_trans) -> le 2 1 = Ex p. 1 = 2+p -> Suc_neq impossible.
         le 2 1 : 1 = add 2 p = Suc(Suc(add 0 p)) = Suc(...) ; oeq (Suc 0) (Suc(Suc..)) ->
         Suc_inj -> oeq 0 (Suc(add 0 p)) -> Suc_neq_Zero (sym). *)
    val base =
      let
        val pz = powZeroSg_at twoCd;                 (* pow 2 0 = Suc 0 *)
        val hdvd = Thm.assume (ctermSig (jT (dvd qF (pow2 ZeroC))));
        (* rewrite pow 2 0 -> Suc 0 in dvd q _ *)
        val zD = Free("z_d0", natT);
        val Pd = Term.lambda zD (dvd qF zD);
        val hdvd1 = substPredSg (Pd, pow2 ZeroC, suc ZeroC) pz hdvd;   (* dvd q (Suc 0) *)
        (* (Suc 0) != 0 meta *)
        val nz1 = Thm.implies_intr (ctermSig (jT (oeq (suc ZeroC) ZeroC))) ((Suc_neq_Zero_Sg2 ZeroC) OF [Thm.assume (ctermSig (jT (oeq (suc ZeroC) ZeroC)))]);
        val le_q_1 = dvd_le_Sg (qF, suc ZeroC) hdvd1 nz1;             (* le q 1 *)
        (* le 2 q : gt1 is lt 1 q = le 2 q *)
        val le_2_q = gt1;                                             (* le 2 q *)
        val le_2_1 = le_transSg_at (suc (suc ZeroC), qF, suc ZeroC) le_2_q le_q_1;  (* le 2 1 *)
        (* le 2 1 = Ex p. 1 = add 2 p ; peel -> contra *)
        val leAbs = Abs("p", natT, oeq (suc ZeroC) (add (suc (suc ZeroC)) (Bound 0)));
        fun bodyP pF hp =   (* hp : oeq 1 (add 2 p) *)
          let
            val a2 = addSucSg_at (suc ZeroC, pF);     (* add 2 p = Suc(add 1 p) *)
            val one_eq = oeq_trans OF [hp, a2];        (* oeq (Suc 0)(Suc(add 1 p)) *)
            val inj = (Suc_inj_Sg (ZeroC, add (suc ZeroC) pF)) OF [one_eq];  (* oeq 0 (add 1 p) *)
            (* add 1 p = Suc(add 0 p) -> oeq 0 (Suc(add 0 p)) -> Suc_neq_Zero sym *)
            val a1 = addSucSg_at (ZeroC, pF);          (* add 1 p = Suc(add 0 p) *)
            val z_eq = oeq_trans OF [inj, a1];         (* oeq 0 (Suc(add 0 p)) *)
          in (Suc_neq_Zero_Sg2 (add ZeroC pF)) OF [oeq_sym OF [z_eq]] end;   (* oFalse *)
        val fls = exE_elimSg (leAbs, oFalseC) le_2_1 "p_b0" bodyP;
      in impI_Sg (dvd qF (pow2 ZeroC), oFalseC) (Thm.implies_intr (ctermSig (jT (dvd qF (pow2 ZeroC)))) fls) end;
    (* STEP : IH neg (dvd q (pow 2 x)) |- neg (dvd q (pow 2 (Suc x))).
         assume dvd q (pow 2 (Suc x)) ; pow 2 (Suc x) = mult 2 (pow 2 x) ;
         dvd q (mult 2 (pow 2 x)) ; euclid_lemma(q) -> dvd q 2 \/ dvd q (pow 2 x).
         dvd q 2 : dvd_le (2!=0) -> le q 2 ; with le 2 q -> q=2 [le_antisym] ->
           dvd 2 q (=dvd 2 2 via dvd_refl) contra hOdd.
         dvd q (pow 2 x) : IH gives oFalse. *)
    val stepconcl =
      let
        val hdvd = Thm.assume (ctermSig (jT (dvd qF (pow2 (suc xF)))));
        val ps = powSucSg_at (twoCd, xF);             (* pow 2 (Suc x) = mult 2 (pow 2 x) *)
        val zD = Free("z_ds", natT);
        val Pd = Term.lambda zD (dvd qF zD);
        val hdvd2 = substPredSg (Pd, pow2 (suc xF), mult twoCd (pow2 xF)) ps hdvd;  (* dvd q (mult 2 (pow 2 x)) *)
        val disj = euclid_lemma_Sg (qF, twoCd, pow2 xF) hPrime hdvd2;  (* Disj (dvd q 2)(dvd q (pow 2 x)) *)
        (* CASE dvd q 2 *)
        val caseQ2 =
          let
            val hq2 = Thm.assume (ctermSig (jT (dvd qF twoCd)));
            (* 2 != 0 meta *)
            val nz2 = Thm.implies_intr (ctermSig (jT (oeq twoCd ZeroC)))
                        ((Suc_neq_Zero_Sg2 (suc ZeroC)) OF [Thm.assume (ctermSig (jT (oeq twoCd ZeroC)))]);
            val le_q_2 = dvd_le_Sg (qF, twoCd) hq2 nz2;     (* le q 2 *)
            val le_2_q = gt1;                               (* le 2 q *)
            val q2 = le_antisym_Sg (qF, twoCd) le_q_2 le_2_q;  (* oeq q 2 *)
            (* dvd 2 q : subst q=2 into dvd 2 _ from dvd_refl 2 ; or dvd 2 2 then subst 2->q (sym) *)
            val dvd22 = dvd_refl_Sg twoCd;                  (* dvd 2 2 *)
            val q2sym = oeq_sym OF [q2];                    (* oeq 2 q *)
            val zQ = Free("z_q2", natT);
            val Pq = Term.lambda zQ (dvd twoCd zQ);
            val dvd2q = substPredSg (Pq, twoCd, qF) q2sym dvd22;  (* dvd 2 q *)
            val fls = mp_Sg (dvd twoCd qF, oFalseC) hOdd dvd2q;   (* hOdd : neg(dvd 2 q) = Imp (dvd 2 q) oFalse *)
          in Thm.implies_intr (ctermSig (jT (dvd qF twoCd))) fls end;
        (* CASE dvd q (pow 2 x) : IH *)
        val caseQpx =
          let
            val IH = Thm.assume (ctermSig (jT (gbody xF)));   (* neg (dvd q (pow 2 x)) *)
            val hqpx = Thm.assume (ctermSig (jT (dvd qF (pow2 xF))));
            val fls = mp_Sg (dvd qF (pow2 xF), oFalseC) IH hqpx;
          in Thm.implies_intr (ctermSig (jT (dvd qF (pow2 xF)))) fls end;
        val fls = disjE_elimSg (dvd qF twoCd, dvd qF (pow2 xF), oFalseC) disj caseQ2 caseQpx;
        val disch = Thm.implies_intr (ctermSig (jT (dvd qF (pow2 (suc xF))))) fls;
      in impI_Sg (dvd qF (pow2 (suc xF)), oFalseC) disch end;
    val step1 = Thm.forall_intr (ctermSig xF) (Thm.implies_intr (ctermSig (jT (gbody xF))) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val d1 = Thm.implies_intr (ctermSig (jT (neg (dvd twoCd qF)))) r2;
    val d2 = Thm.implies_intr (ctermSig (jT (prime2 qF))) d1;
  in varify d2 end;

(* validation : q_ndvd_pow2 *)
val qVq = Var (("q",0), natT); val kVq = Var (("k",0), natT);
val i_qnp = Logic.mk_implies (jT (prime2 qVq),
              Logic.mk_implies (jT (neg (dvd twoCd qVq)),
                jT (neg (dvd qVq (pow2 kVq)))));
val r_qnp = checkSg ("q_ndvd_pow2", q_ndvd_pow2, i_qnp);
val () = if r_qnp then out "DIVCHAR_Q_NDVD_POW2_OK\n" else out "DIVCHAR_Q_NDVD_POW2_BAD\n";

(* pow2_neq_pow2q : prime2 q ==> neg (dvd 2 q) ==> neg (oeq (pow 2 i)(mult (pow 2 j) q))
   from 2^i = 2^j*q : q | 2^j*q (dvd_factor_right) = 2^i (sym) -> q | 2^i, contra q_ndvd_pow2. *)
fun q_ndvd_pow2_Sg (qT, kT) hPrime hOdd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSig
        [(("q",0), ctermSig qT),(("k",0), ctermSig kT)] (varify q_ndvd_pow2))
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hOdd end;

val pow2_neq_pow2q =
  let
    val qF = Free("q", natT); val iF = Free("i", natT); val jF = Free("j", natT);
    val hPrime = Thm.assume (ctermSig (jT (prime2 qF)));
    val hOdd   = Thm.assume (ctermSig (jT (neg (dvd twoCd qF))));
    val heq    = Thm.assume (ctermSig (jT (oeq (pow2 iF) (mult (pow2 jF) qF))));   (* 2^i = 2^j*q *)
    (* q | 2^j*q *)
    val dvd_q_2jq = dvd_factor_right (qF, pow2 jF);     (* dvd q (mult (pow 2 j) q) *)
    (* q | 2^i : subst (2^j*q) -> 2^i via (sym heq) into dvd q _ *)
    val heqsym = oeq_sym OF [heq];                      (* mult (pow 2 j) q = pow 2 i *)
    val dvd_q_2i = dvd_cong_target (qF, mult (pow2 jF) qF, pow2 iF) heqsym dvd_q_2jq;  (* dvd q (pow 2 i) *)
    val nqp = q_ndvd_pow2_Sg (qF, iF) hPrime hOdd;      (* neg (dvd q (pow 2 i)) *)
    val fls = mp_Sg (dvd qF (pow2 iF), oFalseC) nqp dvd_q_2i;   (* oFalse *)
    val d1 = Thm.implies_intr (ctermSig (jT (oeq (pow2 iF)(mult (pow2 jF) qF)))) fls;  (* META neg *)
    val negThm = impI_Sg (oeq (pow2 iF)(mult (pow2 jF) qF), oFalseC) d1;  (* OBJECT neg *)
    val d2 = Thm.implies_intr (ctermSig (jT (neg (dvd twoCd qF)))) negThm;
    val d3 = Thm.implies_intr (ctermSig (jT (prime2 qF))) d2;
  in varify d3 end;

val qVn = Var (("q",0), natT); val iVn = Var (("i",0), natT); val jVn = Var (("j",0), natT);
val i_pnp = Logic.mk_implies (jT (prime2 qVn),
              Logic.mk_implies (jT (neg (dvd twoCd qVn)),
                jT (neg (oeq (pow2 iVn)(mult (pow2 jVn) qVn)))));
val r_pnp2 = checkSg ("pow2_neq_pow2q", pow2_neq_pow2q, i_pnp);

(* SOUNDNESS PROBE on pow2_neq_pow2q : it must KEEP the oddness premise
   (without it the claim is FALSE: q=2, i=j+1 gives 2^(j+1) = 2^j*2). *)
val pnp_prop = Thm.prop_of pow2_neq_pow2q;
val probe_pnp_needs_odd =
  not (pnp_prop aconv
       (Logic.mk_implies (jT (prime2 qVn),
          jT (neg (oeq (pow2 iVn)(mult (pow2 jVn) qVn))))));   (* drops the oddness premise *)
val () = if probe_pnp_needs_odd then out "PROBE_OK pow2_neq_pow2q keeps the oddness premise\n"
         else out "PROBE_FAIL pow2_neq_pow2q dropped oddness!\n";
val () = if r_pnp2 then out "DIVCHAR_DISTINCT_OK\n" else out "DIVCHAR_DISTINCT_BAD\n";

(* ============================================================================
   FINAL SUMMARY : the divisor characterization of N = 2^a*q is established.

   PROVED (each 0-hyp, aconv-intended, soundness-probed unless an *_OK note says
   "membership/easy"):

     div2aq_complete  (THE HEADLINE, hard direction)  [DIVCHAR_COMPLETE_OK]
        prime2 q ==> (pow2_dvd_char @ a) ==> dvd d (mult (pow 2 a) q)
          ==> Disj (Ex i. le i a /\ oeq d (pow 2 i))
                   (Ex i. le i a /\ oeq d (mult (pow 2 i) q))
        Every divisor of 2^a*q is 2^i or 2^i*q for some i<=a.

     pow2_dvd_N / pow2q_dvd_N  (easy direction / soundness of support)  [DIVCHAR_E1_OK]
        le i a ==> dvd (pow 2 i)(mult (pow 2 a) q)
        le i a ==> dvd (mult (pow 2 i) q)(mult (pow 2 a) q)
        Together with completeness : dvd d N  <=>  d in {2^i, 2^i*q : i<=a}.

     mult_left_cancel  [MULT_LEFT_CANCEL_OK] :  lt 0 c ==> mult c a = mult c b ==> a = b
     pow_le_dvd        : le i a ==> dvd (pow 2 i)(pow 2 a)
     q_ndvd_pow2       [DIVCHAR_Q_NDVD_POW2_OK] : prime2 q ==> ~(2|q) ==> ~(q | 2^k)
     pow2_neq_pow2q    [DIVCHAR_DISTINCT_OK]    : prime2 q ==> ~(2|q) ==>
                          2^i <> 2^j*q   (the cross-half separation; needs q ODD)

   DELIVERED to the next fleet (the support-bijection / list build): the support
   of swt(2^a*q) IS exactly the 2(a+1) points, each genuinely a divisor, the two
   halves provably disjoint.  pow2_dvd_char is the ONE assumed dependency (the
   repeated-euclid_lemma 2-adic lemma, the other seat's piece).
   ============================================================================ *)
val () =
  if nh_complete = 0 andalso ac_complete
     andalso probe_complete_prime andalso probe_complete_needs_prime
     andalso probe_complete_needs_dvd
     andalso r_mlc andalso r_pld andalso r_p2n andalso r_p2qn
     andalso r_qnp andalso r_pnp2 andalso probe_pnp_needs_odd
  then out "DIVCHAR_ALL_OK\n"
  else out "DIVCHAR_INCOMPLETE\n";
(* ============================================================================
   THE SUPPORT BIJECTION (sum_supp_collapse) — the reusable crux for Euclid's
   perfect-number theorem.  On the sigma context (ctxtSig / thySig) which itself
   sits on common::with_binom_thm (isabelle_nt_helpers + isabelle_binom_thm +
   isabelle_sigma).

   GOAL:  for f : nat=>nat and a list L of DISTINCT points all in [0..N] such
   that f d = 0 for every d in [0..N] NOT in L,
       sumf f N = lsumf f L.
   (lsumf folds f directly: lsumf f lnil = 0, lsumf f (lcons x xs) = f x + lsumf f xs.)

   We add a fresh natlist datatype + lsumf/lmem/lremove + a LIST UNIVERSAL
   QUANTIFIER lall (mirrors the nat Forall), all extending thySig -> thySigL.
   ONE final context ctxtSigL/ctermSigL; every reused base/sigma lemma is
   re-varified onto it.

   The bijection is proved by INDUCTION on N.  Because L SHRINKS in the step
   (when the top index N is a member we remove it), the IH must hold for an
   ARBITRARY list.  We reflect that universal-over-L into the induction predicate
   via lall, exactly as isabelle_binom_thm's sum_cong reflects its !!k hypothesis
   into the nat Forall.

   Conservative axioms introduced (NONE mentions perfect / sigma / the
   conclusion of euclid_perfect):
     list_induct_ll, lsumf_nil, lsumf_cons,
     lmem_nil_elim, lmem_cons_fwd, lmem_cons_bwd,
     lremove_nil, lremove_cons_eq, lremove_cons_neq,
     leq_refl, leq_subst,            (list equality, for transporting lremove eqns)
     lall (const) + lallI, lallE.    (list universal quantifier)
   ============================================================================ *)
val () = out "SUPP_BIJ_BEGIN\n";

(* ---- new type natlist + consts, extending thySig ---- *)
val thyB1 = Sign.add_types_global [(Binding.name "natlist",0,NoSyn)] thySig;
val natlistN = Sign.full_name thyB1 (Binding.name "natlist");
val natlistT = Type (natlistN,[]);
val lpredT   = natlistT --> oT;             (* predicates over natlist (for lall) *)

val thyB2 = Sign.add_consts
  [(Binding.name "lnil",    natlistT, NoSyn),
   (Binding.name "lcons",   natT --> natlistT --> natlistT, NoSyn),
   (Binding.name "leq",     natlistT --> natlistT --> oT, NoSyn),
   (Binding.name "lsumf",   fnT --> natlistT --> natT, NoSyn),
   (Binding.name "lmem",    natT --> natlistT --> oT, NoSyn),
   (Binding.name "lremove", natT --> natlistT --> natlistT, NoSyn),
   (Binding.name "lnodup",  lpredT, NoSyn),
   (Binding.name "lall",    lpredT --> oT, NoSyn)] thyB1;

fun cnstB nm T = Const (Sign.full_name thyB2 (Binding.name nm), T);
val lnilC    = cnstB "lnil" natlistT;
val lconsC   = cnstB "lcons" (natT --> natlistT --> natlistT);  fun lcons h t = lconsC $ h $ t;
val leqLC    = cnstB "leq" (natlistT --> natlistT --> oT);      fun leqL s t = leqLC $ s $ t;
val lsumfC   = cnstB "lsumf" (fnT --> natlistT --> natT);       fun lsumf f l = lsumfC $ f $ l;
val lmemC    = cnstB "lmem" (natT --> natlistT --> oT);         fun lmem x l = lmemC $ x $ l;
val lremoveC = cnstB "lremove" (natT --> natlistT --> natlistT);fun lremove x l = lremoveC $ x $ l;
val lnodupC  = cnstB "lnodup" lpredT;                           fun lnodup l = lnodupC $ l;
val lallC    = cnstB "lall" (lpredT --> oT);                    fun lall pr = lallC $ pr;

(* ---- free vars ---- *)
val xB = Free("x", natT);  val yB = Free("y", natT);  val dB = Free("d", natT);
val lB = Free("l", natlistT); val tB = Free("t", natlistT);
val LB = Free("L", natlistT); val MB = Free("M", natlistT);
val fB = Free("f", fnT);
val PLB = Free("P", lpredT);

(* ---- conservative axioms ---- *)
(* list induction : P lnil ==> (!!x l. P l ==> P (lcons x l)) ==> P k *)
val list_induct_prop =
  Logic.mk_implies (jT (PLB $ lnilC),
    Logic.mk_implies
      (Logic.all xB (Logic.all lB
         (Logic.mk_implies (jT (PLB $ lB), jT (PLB $ (lcons xB lB))))),
       jT (PLB $ LB)));
val ((_,list_induct_ax), thyB3) =
  Thm.add_axiom_global (Binding.name "list_induct_ll", list_induct_prop) thyB2;

(* lsumf recursion : lsumf f lnil = 0 ; lsumf f (lcons x xs) = f x + lsumf f xs *)
val ((_,lsumf_nil_ax),  thyB4) = Thm.add_axiom_global (Binding.name "lsumf_nil",
      jT (oeq (lsumf fB lnilC) ZeroC)) thyB3;
val ((_,lsumf_cons_ax), thyB5) = Thm.add_axiom_global (Binding.name "lsumf_cons",
      jT (oeq (lsumf fB (lcons xB tB)) (add (fB $ xB) (lsumf fB tB)))) thyB4;

(* lmem intro/elim *)
val ((_,lmem_nil_elim_ax), thyB6) = Thm.add_axiom_global (Binding.name "lmem_nil_elim",
      Logic.mk_implies (jT (lmem xB lnilC), jT oFalseC)) thyB5;
val ((_,lmem_cons_fwd_ax), thyB7) = Thm.add_axiom_global (Binding.name "lmem_cons_fwd",
      Logic.mk_implies (jT (lmem xB (lcons yB tB)),
                        jT (mkDisj (oeq xB yB) (lmem xB tB)))) thyB6;
val ((_,lmem_cons_bwd_ax), thyB8) = Thm.add_axiom_global (Binding.name "lmem_cons_bwd",
      Logic.mk_implies (jT (mkDisj (oeq xB yB) (lmem xB tB)),
                        jT (lmem xB (lcons yB tB)))) thyB7;

(* lremove (first occurrence), conditional *)
val ((_,lremove_nil_ax), thyB9) = Thm.add_axiom_global (Binding.name "lremove_nil",
      jT (leqL (lremove xB lnilC) lnilC)) thyB8;
val ((_,lremove_cons_eq_ax), thyB10) = Thm.add_axiom_global (Binding.name "lremove_cons_eq",
      Logic.mk_implies (jT (oeq xB yB),
        jT (leqL (lremove xB (lcons yB tB)) tB))) thyB9;
val ((_,lremove_cons_neq_ax), thyB11) = Thm.add_axiom_global (Binding.name "lremove_cons_neq",
      Logic.mk_implies (jT (neg (oeq xB yB)),
        jT (leqL (lremove xB (lcons yB tB)) (lcons yB (lremove xB tB))))) thyB10;

(* list equality : refl + subst (for transporting lremove leq-equations) *)
val ((_,leq_refl_ax),  thyB12) = Thm.add_axiom_global (Binding.name "leqL_refl",
      jT (leqL LB LB)) thyB11;
val ((_,leq_subst_ax), thyB13) = Thm.add_axiom_global (Binding.name "leqL_subst",
      Logic.mk_implies (jT (leqL LB MB), Logic.mk_implies (jT (PLB $ LB), jT (PLB $ MB)))) thyB12;

(* lnodup intro/elim *)
val ((_,lnodup_nil_ax), thyB13a) = Thm.add_axiom_global (Binding.name "lnodup_nil",
      jT (lnodup lnilC)) thyB13;
val ((_,lnodup_cons_fwd_ax), thyB13b) = Thm.add_axiom_global (Binding.name "lnodup_cons_fwd",
      Logic.mk_implies (jT (lnodup (lcons xB tB)),
                        jT (mkConj (neg (lmem xB tB)) (lnodup tB)))) thyB13a;
val ((_,lnodup_cons_bwd_ax), thyB13c) = Thm.add_axiom_global (Binding.name "lnodup_cons_bwd",
      Logic.mk_implies (jT (mkConj (neg (lmem xB tB)) (lnodup tB)),
                        jT (lnodup (lcons xB tB)))) thyB13b;

(* list universal quantifier lall + intro/elim (mirror nat Forall) *)
val ((_,lallI_ax), thyB14) = Thm.add_axiom_global (Binding.name "lallI",
      Logic.mk_implies (Logic.all LB (jT (PLB $ LB)), jT (lall PLB))) thyB13c;
val ((_,lallE_ax), thyB15) = Thm.add_axiom_global (Binding.name "lallE",
      Logic.mk_implies (jT (lall PLB), jT (PLB $ LB))) thyB14;

(* ============================================================================
   ONE FINAL CONTEXT ctxtSigL / ctermSigL — route everything through it.
   ============================================================================ *)
val thySigL  = thyB15;
val ctxtSigL = Proof_Context.init_global thySigL;
val ctermSigL= Thm.cterm_of ctxtSigL;

(* re-varify every reused base/sigma lemma onto the final context *)
val oeq_refl_vBj    = varify oeq_refl;
val oeq_subst_vBj   = varify oeq_subst;
val add_0_vBj       = varify add_0;
val add_0_right_vBj = varify add_0_right;
val nat_induct_vBj  = varify nat_induct;
val sumf_0_vBj      = varify sumf_0_ax;
val sumf_Suc_vBj    = varify sumf_Suc_ax;
val exI_vBj         = varify exI_ax;
val exE_vBj         = varify exE_ax;
val impI_vBj        = varify impI_ax;
val mp_vBj          = varify mp_ax;
val allI_vBj        = varify allI_ax;
val allE_vBj        = varify allE_ax;
val disjE_vBj       = varify disjE_ax;
val ex_middle_vBj   = varify ex_middle_ax;
val oFalse_elim_vBj = varify oFalse_elim_ax;
val le_refl_vBj     = varify le_refl;
val le_trans_vBj    = varify le_trans;
val le_neq_lt_vBj   = varify le_neq_lt;
val lt_suc_cases_vBj= varify lt_suc_cases;
val zero_le_vBj     = varify zero_le;
(* the new list axioms *)
val list_induct_vBj = varify list_induct_ax;
val lsumf_nil_vBj   = varify lsumf_nil_ax;
val lsumf_cons_vBj  = varify lsumf_cons_ax;
val lmem_nil_elim_vBj = varify lmem_nil_elim_ax;
val lmem_cons_fwd_vBj = varify lmem_cons_fwd_ax;
val lmem_cons_bwd_vBj = varify lmem_cons_bwd_ax;
val lremove_nil_vBj   = varify lremove_nil_ax;
val lremove_cons_eq_vBj  = varify lremove_cons_eq_ax;
val lremove_cons_neq_vBj = varify lremove_cons_neq_ax;
val leq_refl_vBj   = varify leq_refl_ax;
val leq_subst_vBj  = varify leq_subst_ax;
val lnodup_nil_vBj = varify lnodup_nil_ax;
val lnodup_cons_fwd_vBj = varify lnodup_cons_fwd_ax;
val lnodup_cons_bwd_vBj = varify lnodup_cons_bwd_ax;
val lallI_vBj      = varify lallI_ax;
val lallE_vBj      = varify lallE_ax;
val conjI_vBj      = varify conjI_ax;
val conjunct1_vBj  = varify conjunct1_ax;
val conjunct2_vBj  = varify conjunct2_ax;
val disjI1_vBj     = varify disjI1_ax;
val disjI2_vBj     = varify disjI2_ax;

(* ---- ground instantiators on ctxtSigL ---- *)
fun oeqreflBj_at t = beta_norm (Drule.infer_instantiate ctxtSigL [(("a",0), ctermSigL t)] oeq_refl_vBj);
fun add0Bj_at t    = beta_norm (Drule.infer_instantiate ctxtSigL [(("n",0), ctermSigL t)] add_0_vBj);
fun add0rBj_at t   = beta_norm (Drule.infer_instantiate ctxtSigL [(("n",0), ctermSigL t)] add_0_right_vBj);

fun nat_induct_atBj (Qabs, kT) = beta_norm (Drule.infer_instantiate ctxtSigL
      [(("P",0), ctermSigL Qabs), (("k",0), ctermSigL kT)] nat_induct_vBj);
fun list_induct_atBj (Qabs, kT) = beta_norm (Drule.infer_instantiate ctxtSigL
      [(("P",0), ctermSigL Qabs), (("L",0), ctermSigL kT)] list_induct_vBj);

fun sumf0Bj_at fT      = beta_norm (Drule.infer_instantiate ctxtSigL [(("f",0), ctermSigL fT)] sumf_0_vBj);
fun sumfSucBj_at (fT,nt)= beta_norm (Drule.infer_instantiate ctxtSigL
      [(("f",0), ctermSigL fT),(("n",0), ctermSigL nt)] sumf_Suc_vBj);

fun lsumfNilBj_at fT   = beta_norm (Drule.infer_instantiate ctxtSigL [(("f",0), ctermSigL fT)] lsumf_nil_vBj);
fun lsumfConsBj_at (fT,h,t) = beta_norm (Drule.infer_instantiate ctxtSigL
      [(("f",0), ctermSigL fT),(("x",0), ctermSigL h),(("t",0), ctermSigL t)] lsumf_cons_vBj);

(* add congruence on LEFT/RIGHT operand *)
fun add_cong_lBj (pT, qT, kT) hpq =
  let val zF = Free("z_al", natT);
      val Pabs = Term.lambda zF (oeq (add pT kT) (add zF kT));
      val inst = beta_norm (Drule.infer_instantiate ctxtSigL
            [(("P",0), ctermSigL Pabs), (("a",0), ctermSigL pT), (("b",0), ctermSigL qT)] oeq_subst_vBj);
      val refl = beta_norm (Drule.infer_instantiate ctxtSigL [(("a",0), ctermSigL (add pT kT))] oeq_refl_vBj);
  in inst OF [hpq, refl] end;
fun add_cong_rBj (hT, pT, qT) hpq =
  let val zF = Free("z_ar", natT);
      val Pabs = Term.lambda zF (oeq (add hT pT) (add hT zF));
      val inst = beta_norm (Drule.infer_instantiate ctxtSigL
            [(("P",0), ctermSigL Pabs), (("a",0), ctermSigL pT), (("b",0), ctermSigL qT)] oeq_subst_vBj);
      val refl = beta_norm (Drule.infer_instantiate ctxtSigL [(("a",0), ctermSigL (add hT pT))] oeq_refl_vBj);
  in inst OF [hpq, refl] end;

(* FOL on ctxtSigL *)
fun impI_Bj (At, Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("A",0), ctermSigL At), (("B",0), ctermSigL Bt)] impI_vBj)
  in Thm.implies_elim inst hImpThm end;
fun mp_Bj (At, Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("A",0), ctermSigL At), (("B",0), ctermSigL Bt)] mp_vBj)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun allI_Bj Pabs hAll =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL [(("P",0), ctermSigL Pabs)] allI_vBj)
  in Thm.implies_elim inst hAll end;
fun allE_Bj Pabs at hForall =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("P",0), ctermSigL Pabs), (("a",0), ctermSigL at)] allE_vBj)
  in Thm.implies_elim inst hForall end;
fun ex_middle_atBj At = beta_norm (Drule.infer_instantiate ctxtSigL [(("A",0), ctermSigL At)] ex_middle_vBj);
fun disjE_elimBj (At, Bt, Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
            [(("A",0), ctermSigL At), (("B",0), ctermSigL Bt), (("C",0), ctermSigL Ct)] disjE_vBj);
      val s1 = Thm.implies_elim inst dThm;
      val s2 = Thm.implies_elim s1 caseA;
  in Thm.implies_elim s2 caseB end;
fun oFalse_elimBj_at rT = beta_norm (Drule.infer_instantiate ctxtSigL [(("R",0), ctermSigL rT)] oFalse_elim_vBj);

(* lall intro/elim on ctxtSigL *)
fun lallI_Bj Pabs hAll =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL [(("P",0), ctermSigL Pabs)] lallI_vBj)
  in Thm.implies_elim inst hAll end;
fun lallE_Bj Pabs LT hAll =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("P",0), ctermSigL Pabs), (("L",0), ctermSigL LT)] lallE_vBj)
  in Thm.implies_elim inst hAll end;

(* lmem intro/elim helpers *)
fun lmemNilElim_Bj x = beta_norm (Drule.infer_instantiate ctxtSigL [(("x",0), ctermSigL x)] lmem_nil_elim_vBj);
fun lmemConsFwd_Bj (x,y,t) = beta_norm (Drule.infer_instantiate ctxtSigL
      [(("x",0), ctermSigL x),(("y",0), ctermSigL y),(("t",0), ctermSigL t)] lmem_cons_fwd_vBj);
fun lmemConsBwd_Bj (x,y,t) = beta_norm (Drule.infer_instantiate ctxtSigL
      [(("x",0), ctermSigL x),(("y",0), ctermSigL y),(("t",0), ctermSigL t)] lmem_cons_bwd_vBj);

(* conj/disj intro+elim on ctxtSigL *)
fun conjI_Bj (At, Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("A",0), ctermSigL At), (("B",0), ctermSigL Bt)] conjI_vBj)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_Bj (At, Bt) hConj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("A",0), ctermSigL At), (("B",0), ctermSigL Bt)] conjunct1_vBj)
  in Thm.implies_elim inst hConj end;
fun conjunct2_Bj (At, Bt) hConj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("A",0), ctermSigL At), (("B",0), ctermSigL Bt)] conjunct2_vBj)
  in Thm.implies_elim inst hConj end;
fun disjI1_Bj (At, Bt) hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("A",0), ctermSigL At), (("B",0), ctermSigL Bt)] disjI1_vBj)
  in Thm.implies_elim inst hA end;
fun disjI2_Bj (At, Bt) hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("A",0), ctermSigL At), (("B",0), ctermSigL Bt)] disjI2_vBj)
  in Thm.implies_elim inst hB end;

(* nodup intro/elim *)
val lnodupNil_Bj = lnodup_nil_vBj;
fun lnodupConsFwd_Bj (x,t) = beta_norm (Drule.infer_instantiate ctxtSigL
      [(("x",0), ctermSigL x),(("t",0), ctermSigL t)] lnodup_cons_fwd_vBj);
fun lnodupConsBwd_Bj (x,t) = beta_norm (Drule.infer_instantiate ctxtSigL
      [(("x",0), ctermSigL x),(("t",0), ctermSigL t)] lnodup_cons_bwd_vBj);
fun lnodup_transBj (AT, BT) hleq hnd =
  let val Pabs = Term.lambda (Free("zN", natlistT)) (lnodup (Free("zN",natlistT)));
      val inst = beta_norm (Drule.infer_instantiate ctxtSigL
            [(("P",0), ctermSigL Pabs), (("L",0), ctermSigL AT), (("M",0), ctermSigL BT)] leq_subst_vBj)
  in inst OF [hleq, hnd] end;
fun lmem_transBj (yT, AT, BT) hleq hmem =
  let val Pabs = Term.lambda (Free("zN2", natlistT)) (lmem yT (Free("zN2",natlistT)));
      val inst = beta_norm (Drule.infer_instantiate ctxtSigL
            [(("P",0), ctermSigL Pabs), (("L",0), ctermSigL AT), (("M",0), ctermSigL BT)] leq_subst_vBj)
  in inst OF [hleq, hmem] end;

(* leq symmetry on lists : leq A B ==> leq B A *)
fun leqL_sym (AT, BT) hleq =
  let val Pabs = Term.lambda (Free("zS", natlistT)) (leqL (Free("zS",natlistT)) AT);
      val inst = beta_norm (Drule.infer_instantiate ctxtSigL
            [(("P",0), ctermSigL Pabs), (("L",0), ctermSigL AT), (("M",0), ctermSigL BT)] leq_subst_vBj);
      val reflAA = beta_norm (Drule.infer_instantiate ctxtSigL [(("L",0), ctermSigL AT)] leq_refl_vBj);
  in inst OF [hleq, reflAA] end;

(* lremove helpers *)
fun lremoveNil_Bj x = beta_norm (Drule.infer_instantiate ctxtSigL [(("x",0), ctermSigL x)] lremove_nil_vBj);
fun lremoveConsEq_Bj (x,y,t) = beta_norm (Drule.infer_instantiate ctxtSigL
      [(("x",0), ctermSigL x),(("y",0), ctermSigL y),(("t",0), ctermSigL t)] lremove_cons_eq_vBj);
fun lremoveConsNeq_Bj (x,y,t) = beta_norm (Drule.infer_instantiate ctxtSigL
      [(("x",0), ctermSigL x),(("y",0), ctermSigL y),(("t",0), ctermSigL t)] lremove_cons_neq_vBj);

(* leq transport : leq A B ==> P A ==> P B  (P built capture-safe over a fresh list Free) *)
fun leq_transBj (Pabs, AT, BT) hleq hPA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("P",0), ctermSigL Pabs), (("L",0), ctermSigL AT), (("M",0), ctermSigL BT)] leq_subst_vBj)
  in inst OF [hleq, hPA] end;

(* oeq-subst-into-predicate helper on ctxtSigL *)
fun substPredBj (Pabs, xT, yT) hxy hPx =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("P",0), ctermSigL Pabs), (("a",0), ctermSigL xT), (("b",0), ctermSigL yT)] oeq_subst_vBj)
  in inst OF [hxy, hPx] end;

(* le helpers on ctxtSigL *)
fun le_introBj (mT, nT, w) hyp =
  let val pAbs = Free("p_li", natT);
      val Pabs = Term.lambda pAbs (oeq nT (add mT pAbs));
      val exI_inst = beta_norm (Drule.infer_instantiate ctxtSigL
            [(("P",0), ctermSigL Pabs), (("a",0), ctermSigL w)] exI_vBj);
  in exI_inst OF [hyp] end;
fun le_reflBj_at t = beta_norm (Drule.infer_instantiate ctxtSigL [(("n",0), ctermSigL t)] le_refl_vBj);
fun le_transBj_at (mt, nt, kt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("m",0), ctermSigL mt), (("n",0), ctermSigL nt), (("k",0), ctermSigL kt)] le_trans_vBj)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun zero_leBj_at t = beta_norm (Drule.infer_instantiate ctxtSigL [(("n",0), ctermSigL t)] zero_le_vBj);
fun le_neq_ltBj_at (dt, nt) hle hneq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("d",0), ctermSigL dt), (("n",0), ctermSigL nt)] le_neq_lt_vBj)
  in Thm.implies_elim (Thm.implies_elim inst hle) hneq end;
fun lt_suc_cases_atBj (mt, nt) hlt =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("m",0), ctermSigL mt), (("n",0), ctermSigL nt)] lt_suc_cases_vBj)
  in Thm.implies_elim inst hlt end;
(* le_suc_self : le b (Suc b) ; witness Suc 0 *)
fun le_suc_selfBj_at bT =
  let
    val addS = beta_norm (Drule.infer_instantiate ctxtSigL
                 [(("m",0), ctermSigL bT),(("n",0), ctermSigL ZeroC)] (varify add_Suc_right));
    val ab0 = add0rBj_at bT;
    val sucAb0 = beta_norm (Drule.infer_instantiate ctxtSigL
      [(("P",0), ctermSigL (Term.lambda (Free("z_ss",natT)) (oeq (suc (add bT ZeroC)) (suc (Free("z_ss",natT)))))),
       (("a",0), ctermSigL (add bT ZeroC)), (("b",0), ctermSigL bT)] oeq_subst_vBj)
      OF [ab0, oeqreflBj_at (suc (add bT ZeroC))];
    val rhs = oeq_trans OF [addS, sucAb0];
    val rhsSym = oeq_sym OF [rhs];
  in le_introBj (bT, suc bT, suc ZeroC) rhsSym end;

val () = out "SUPP_BIJ_SETUP_OK\n";

(* ============================================================================
   lsumf_extract :  lmem x L ==> oeq (lsumf f L) (add (f x) (lsumf f (lremove x L)))
   BY list_induct on L  (mirrors wilson_pairing's `extract`, add-for-mult).
   ============================================================================ *)
val lsumf_extract =
  let
    val xF = Free("x", natT);
    fun concBody zt = oeq (lsumf fB zt) (add (fB $ xF) (lsumf fB (lremove xF zt)));
    fun predBody zt = mkImp (lmem xF zt) (concBody zt);
    val Qpred = Abs("z", natlistT, predBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = list_induct_atBj (Qpred, LF);
    (* BASE L = lnil : lmem x lnil is absurd *)
    val base =
      let
        val hmem = Thm.assume (ctermSigL (jT (lmem xF lnilC)));
        val ff   = Thm.implies_elim (lmemNilElim_Bj xF) hmem;
        val conc = Thm.implies_elim (oFalse_elimBj_at (concBody lnilC)) ff;
        val dis  = Thm.implies_intr (ctermSigL (jT (lmem xF lnilC))) conc;
      in impI_Bj (lmem xF lnilC, concBody lnilC) dis end;
    val yF = Free("y", natT); val tF = Free("t", natlistT);
    val ihprop = jT (predBody tF);
    val IH = Thm.assume (ctermSigL ihprop);
    val stepConcl =
      let
        val hmem = Thm.assume (ctermSigL (jT (lmem xF (lcons yF tF))));
        val disjmem = Thm.implies_elim (lmemConsFwd_Bj (xF, yF, tF)) hmem;
        val lsc = lsumfConsBj_at (fB, yF, tF);   (* lsumf f (lcons y t) = f y + lsumf f t *)
        (* CASE x = y : lremove x (lcons y t) = t  =>  add (f x)(lsumf f t).
             lsumf f (lcons y t) = f y + lsumf f t ;  f x = f y (from x=y) so this is
             add (f x)(lsumf f (lremove x (lcons y t))) since lremove..=t. *)
        val caseEq =
          let
            val heq = Thm.assume (ctermSigL (jT (oeq xF yF)));     (* x = y *)
            val lrm = Thm.implies_elim (lremoveConsEq_Bj (xF, yF, tF)) heq; (* leq (lremove x (lcons y t)) t *)
            (* RHS target : add (f x)(lsumf f (lremove x (lcons y t))) ;
               rewrite lremove.. -> t via leq, then rewrite f y -> f x in lsc. *)
            (* lsumf f (lremove x (lcons y t)) = lsumf f t  (leq transport on the list arg) *)
            val Pabs = Term.lambda (Free("zL", natlistT)) (oeq (lsumf fB (lremove xF (lcons yF tF))) (lsumf fB (Free("zL",natlistT))));
            val lsum_lrm = leq_transBj (Pabs, lremove xF (lcons yF tF), tF) lrm
                             (oeqreflBj_at (lsumf fB (lremove xF (lcons yF tF))));
            (* lsum_lrm : lsumf f (lremove x (lcons y t)) = lsumf f t *)
            (* f y = f x  : from x = y, f-congruence *)
            val fy_fx =
              let val Pf = Term.lambda (Free("zf", natT)) (oeq (fB $ yF) (fB $ (Free("zf",natT))))
                  val yx = oeq_sym OF [heq]   (* y = x *)
              in substPredBj (Pf, yF, xF) yx (oeqreflBj_at (fB $ yF)) end;   (* f y = f x *)
            (* lsumf f (lcons y t) = f y + lsumf f t  [lsc]
               = f x + lsumf f t        [add_cong_l fy_fx]
               = f x + lsumf f (lremove x (lcons y t))  [add_cong_r (sym lsum_lrm)] *)
            val st1 = add_cong_lBj (fB $ yF, fB $ xF, lsumf fB tF) fy_fx;   (* f y + S = f x + S *)
            val lsum_lrm_sym = oeq_sym OF [lsum_lrm];   (* lsumf f t = lsumf f (lremove x (lcons y t)) *)
            val st2 = add_cong_rBj (fB $ xF, lsumf fB tF, lsumf fB (lremove xF (lcons yF tF))) lsum_lrm_sym;
            val conc = oeq_trans OF [oeq_trans OF [lsc, st1], st2];
          in Thm.implies_intr (ctermSigL (jT (oeq xF yF))) conc end;
        (* CASE x <> y : x must be in t ; lremove x (lcons y t) = lcons y (lremove x t). *)
        val caseNeq =
          let
            val hneq = Thm.assume (ctermSigL (jT (neg (oeq xF yF))));
            (* x in t : from disjmem (x=y \/ x in t), x=y contradicts hneq *)
            val memT =
              let
                val cA = let val hxy = Thm.assume (ctermSigL (jT (oeq xF yF)))
                             val ff  = mp_Bj (oeq xF yF, oFalseC) hneq hxy
                             val r   = Thm.implies_elim (oFalse_elimBj_at (lmem xF tF)) ff
                         in Thm.implies_intr (ctermSigL (jT (oeq xF yF))) r end;
                val cB = let val hm = Thm.assume (ctermSigL (jT (lmem xF tF)))
                         in Thm.implies_intr (ctermSigL (jT (lmem xF tF))) hm end;
              in disjE_elimBj (oeq xF yF, lmem xF tF, lmem xF tF) disjmem cA cB end;
            val ihconc = mp_Bj (lmem xF tF, concBody tF) IH memT;   (* lsumf f t = f x + lsumf f (lremove x t) *)
            val lrm = Thm.implies_elim (lremoveConsNeq_Bj (xF, yF, tF)) hneq;
                                      (* leq (lremove x (lcons y t)) (lcons y (lremove x t)) *)
            val rmtl = lremove xF tF;
            (* lsumf f (lremove x (lcons y t)) = lsumf f (lcons y (lremove x t))  [leq transport]
                                               = f y + lsumf f (lremove x t)       [lsumf_cons] *)
            val Pabs = Term.lambda (Free("zL", natlistT)) (oeq (lsumf fB (lremove xF (lcons yF tF))) (lsumf fB (Free("zL",natlistT))));
            val tleq = leq_transBj (Pabs, lremove xF (lcons yF tF), lcons yF rmtl) lrm
                         (oeqreflBj_at (lsumf fB (lremove xF (lcons yF tF))));
            val lsc2 = lsumfConsBj_at (fB, yF, rmtl);  (* lsumf f (lcons y (lremove x t)) = f y + lsumf f (lremove x t) *)
            val lrm_val = oeq_trans OF [tleq, lsc2];   (* lsumf f (lremove x (lcons y t)) = f y + lsumf f (lremove x t) *)
            (* GOAL : lsumf f (lcons y t) = f x + lsumf f (lremove x (lcons y t))
               LHS lsumf f (lcons y t) = f y + lsumf f t              [lsc]
                   = f y + (f x + lsumf f (lremove x t))              [add_cong_r ihconc]
               RHS f x + lsumf f (lremove x (lcons y t))
                   = f x + (f y + lsumf f (lremove x t))              [add_cong_r lrm_val]
               bridge: f y + (f x + R) = f x + (f y + R)  via assoc/comm. *)
            val q = lsumf fB rmtl;
            val lhs1 = oeq_trans OF [lsc, add_cong_rBj (fB $ yF, lsumf fB tF, add (fB $ xF) q) ihconc];
                       (* lsumf f (lcons y t) = f y + (f x + R) *)
            val rhs1 = add_cong_rBj (fB $ xF, lsumf fB (lremove xF (lcons yF tF)), add (fB $ yF) q) lrm_val;
                       (* f x + lsumf f (lremove x (lcons y t)) = f x + (f y + R) *)
            (* bridge : add (f y)(add (f x) R) = add (f x)(add (f y) R) *)
            val assoc1 = beta_norm (Drule.infer_instantiate ctxtSigL
                  [(("m",0), ctermSigL (fB $ yF)),(("n",0), ctermSigL (fB $ xF)),(("k",0), ctermSigL q)] add_assoc_vSg);
                  (* add (add (f y)(f x)) R = add (f y)(add (f x) R)  -- check direction *)
            (* NOTE: add_assoc shape — verify; use add_comm + add_assoc to bridge. *)
            val assoc1s = oeq_sym OF [assoc1];   (* add (f y)(add (f x) R) = add (add (f y)(f x)) R *)
            val comm = beta_norm (Drule.infer_instantiate ctxtSigL
                  [(("m",0), ctermSigL (fB $ yF)),(("n",0), ctermSigL (fB $ xF))] add_comm_vSg);  (* add (f y)(f x) = add (f x)(f y) *)
            val commc = add_cong_lBj (add (fB $ yF) (fB $ xF), add (fB $ xF) (fB $ yF), q) comm;
                  (* add (add (f y)(f x)) R = add (add (f x)(f y)) R *)
            val assoc2 = beta_norm (Drule.infer_instantiate ctxtSigL
                  [(("m",0), ctermSigL (fB $ xF)),(("n",0), ctermSigL (fB $ yF)),(("k",0), ctermSigL q)] add_assoc_vSg);
                  (* add (add (f x)(f y)) R = add (f x)(add (f y) R) *)
            val bridge = oeq_trans OF [oeq_trans OF [assoc1s, commc], assoc2];
                  (* add (f y)(add (f x) R) = add (f x)(add (f y) R) *)
            val rhs1s = oeq_sym OF [rhs1];
            val conc = oeq_trans OF [oeq_trans OF [lhs1, bridge], rhs1s];
          in Thm.implies_intr (ctermSigL (jT (neg (oeq xF yF)))) conc end;
        val em = ex_middle_atBj (oeq xF yF);
        val conc = disjE_elimBj (oeq xF yF, neg (oeq xF yF), concBody (lcons yF tF)) em caseEq caseNeq;
        val dis = Thm.implies_intr (ctermSigL (jT (lmem xF (lcons yF tF)))) conc;
      in impI_Bj (lmem xF (lcons yF tF), concBody (lcons yF tF)) dis end;
    val step1 = Thm.forall_intr (ctermSigL yF)
                  (Thm.forall_intr (ctermSigL tF) (Thm.implies_intr (ctermSigL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hmemL = Thm.assume (ctermSigL (jT (lmem xF LF)));
    val concL = mp_Bj (lmem xF LF, concBody LF) r2 hmemL;
    val d1 = Thm.implies_intr (ctermSigL (jT (lmem xF LF))) concL;
  in varify d1 end;

val () = out "LSUMF_EXTRACT_DONE\n";

(* validation of lsumf_extract *)
val fVe = Var (("f",0), fnT);
val xVe = Var (("x",0), natT);
val LVe = Var (("L",0), natlistT);
fun chkBj (nm, th, intended) =
  let val nh = length (Thm.hyps_of th);
      val ac = (Thm.prop_of th) aconv intended;
  in if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
     else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
                ^ "  got      = " ^ Syntax.string_of_term ctxtSigL (Thm.prop_of th) ^ "\n"
                ^ "  intended = " ^ Syntax.string_of_term ctxtSigL intended ^ "\n"); false)
  end;
val i_extract = Logic.mk_implies (jT (lmem xVe LVe),
      jT (oeq (lsumf fVe LVe) (add (fVe $ xVe) (lsumf fVe (lremove xVe LVe)))));
val r_extract = chkBj ("lsumf_extract", lsumf_extract, i_extract);
val () = if r_extract then out "EXTRACT_OK\n" else out "EXTRACT_FAIL\n";

(* ============================================================================
   mem_remove_fwd : lmem y (lremove x L) ==> lmem y L   (list_induct on L)
   ============================================================================ *)
val mem_remove_fwd =
  let
    val xF = Free("x", natT); val yF = Free("y", natT);
    fun concBody zt = mkImp (lmem yF (lremove xF zt)) (lmem yF zt);
    val Qpred = Abs("z", natlistT, concBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = list_induct_atBj (Qpred, LF);
    val base =
      let
        val hassm = Thm.assume (ctermSigL (jT (lmem yF (lremove xF lnilC))));
        val lrm = lremoveNil_Bj xF;
        val mem_lnil = lmem_transBj (yF, lremove xF lnilC, lnilC) lrm hassm;
        val ff  = Thm.implies_elim (lmemNilElim_Bj yF) mem_lnil;
        val conc = Thm.implies_elim (oFalse_elimBj_at (lmem yF lnilC)) ff;
        val dis  = Thm.implies_intr (ctermSigL (jT (lmem yF (lremove xF lnilC)))) conc;
      in impI_Bj (lmem yF (lremove xF lnilC), lmem yF lnilC) dis end;
    val hF = Free("h", natT); val tF = Free("t", natlistT);
    val ihprop = jT (concBody tF);
    val IH = Thm.assume (ctermSigL ihprop);
    val stepConcl =
      let
        val hassm = Thm.assume (ctermSigL (jT (lmem yF (lremove xF (lcons hF tF)))));
        val caseEq =
          let
            val heq = Thm.assume (ctermSigL (jT (oeq xF hF)));
            val lrm = Thm.implies_elim (lremoveConsEq_Bj (xF, hF, tF)) heq;  (* leq (lremove x (lcons h t)) t *)
            val mem_t = lmem_transBj (yF, lremove xF (lcons hF tF), tF) lrm hassm;  (* lmem y t *)
            val res = Thm.implies_elim (lmemConsBwd_Bj (yF, hF, tF))
                        (disjI2_Bj (oeq yF hF, lmem yF tF) mem_t);  (* lmem y (lcons h t) *)
          in Thm.implies_intr (ctermSigL (jT (oeq xF hF))) res end;
        val caseNeq =
          let
            val hneq = Thm.assume (ctermSigL (jT (neg (oeq xF hF))));
            val lrm = Thm.implies_elim (lremoveConsNeq_Bj (xF, hF, tF)) hneq;  (* leq (lremove x (lcons h t)) (lcons h (lremove x t)) *)
            val mem_cons = lmem_transBj (yF, lremove xF (lcons hF tF), lcons hF (lremove xF tF)) lrm hassm;
                           (* lmem y (lcons h (lremove x t)) *)
            val dj = Thm.implies_elim (lmemConsFwd_Bj (yF, hF, lremove xF tF)) mem_cons;
                     (* Disj (oeq y h)(lmem y (lremove x t)) *)
            val res =
              let
                val cA = let val hyh = Thm.assume (ctermSigL (jT (oeq yF hF)))
                             val r = Thm.implies_elim (lmemConsBwd_Bj (yF, hF, tF))
                                       (disjI1_Bj (oeq yF hF, lmem yF tF) hyh)
                         in Thm.implies_intr (ctermSigL (jT (oeq yF hF))) r end;
                val cB = let val hm = Thm.assume (ctermSigL (jT (lmem yF (lremove xF tF))))
                             val inT = mp_Bj (lmem yF (lremove xF tF), lmem yF tF) IH hm
                             val r = Thm.implies_elim (lmemConsBwd_Bj (yF, hF, tF))
                                       (disjI2_Bj (oeq yF hF, lmem yF tF) inT)
                         in Thm.implies_intr (ctermSigL (jT (lmem yF (lremove xF tF)))) r end;
              in disjE_elimBj (oeq yF hF, lmem yF (lremove xF tF), lmem yF (lcons hF tF)) dj cA cB end;
          in Thm.implies_intr (ctermSigL (jT (neg (oeq xF hF)))) res end;
        val em = ex_middle_atBj (oeq xF hF);
        val conc = disjE_elimBj (oeq xF hF, neg (oeq xF hF), lmem yF (lcons hF tF)) em caseEq caseNeq;
        val dis = Thm.implies_intr (ctermSigL (jT (lmem yF (lremove xF (lcons hF tF))))) conc;
      in impI_Bj (lmem yF (lremove xF (lcons hF tF)), lmem yF (lcons hF tF)) dis end;
    val step1 = Thm.forall_intr (ctermSigL hF)
                  (Thm.forall_intr (ctermSigL tF) (Thm.implies_intr (ctermSigL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hh = Thm.assume (ctermSigL (jT (lmem yF (lremove xF LF))));
    val concL = mp_Bj (lmem yF (lremove xF LF), lmem yF LF) r2 hh;
    val d1 = Thm.implies_intr (ctermSigL (jT (lmem yF (lremove xF LF)))) concL;
  in varify d1 end;
val mem_remove_fwd_vBj = varify mem_remove_fwd;
fun mem_remove_fwd_at (yT, xT, LT) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("y",0), ctermSigL yT),(("x",0), ctermSigL xT),(("L",0), ctermSigL LT)] mem_remove_fwd_vBj)
  in Thm.implies_elim inst hmem end;
val () = out "MEM_REMOVE_FWD_DONE\n";

(* ============================================================================
   mem_remove_bwd : lmem y L ==> neg (oeq y x) ==> lmem y (lremove x L)
   (Conj-packaged hypothesis, mirrors wilson_pairing).  (list_induct on L)
   ============================================================================ *)
val mem_remove_bwd =
  let
    val xF = Free("x", natT); val yF = Free("y", natT);
    fun hypBody zt = mkConj (lmem yF zt) (neg (oeq yF xF));
    fun concBody zt = mkImp (hypBody zt) (lmem yF (lremove xF zt));
    val Qpred = Abs("z", natlistT, concBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = list_induct_atBj (Qpred, LF);
    val base =
      let
        val hh = Thm.assume (ctermSigL (jT (hypBody lnilC)));
        val mem = conjunct1_Bj (lmem yF lnilC, neg (oeq yF xF)) hh;
        val ff  = Thm.implies_elim (lmemNilElim_Bj yF) mem;
        val conc = Thm.implies_elim (oFalse_elimBj_at (lmem yF (lremove xF lnilC))) ff;
        val dis = Thm.implies_intr (ctermSigL (jT (hypBody lnilC))) conc;
      in impI_Bj (hypBody lnilC, lmem yF (lremove xF lnilC)) dis end;
    val hF = Free("h", natT); val tF = Free("t", natlistT);
    val ihprop = jT (concBody tF);
    val IH = Thm.assume (ctermSigL ihprop);
    val stepConcl =
      let
        val hh = Thm.assume (ctermSigL (jT (hypBody (lcons hF tF))));
        val mem = conjunct1_Bj (lmem yF (lcons hF tF), neg (oeq yF xF)) hh;
        val hneqYX = conjunct2_Bj (lmem yF (lcons hF tF), neg (oeq yF xF)) hh;
        val djmem = Thm.implies_elim (lmemConsFwd_Bj (yF, hF, tF)) mem;
        val caseEqXH =
          let
            val heq = Thm.assume (ctermSigL (jT (oeq xF hF)));
            val lrm = Thm.implies_elim (lremoveConsEq_Bj (xF, hF, tF)) heq;
            val mem_t =
              let
                val cA = let val hyh = Thm.assume (ctermSigL (jT (oeq yF hF)))
                             val hx = oeq_sym OF [heq]
                             val yx = oeq_trans OF [hyh, hx]
                             val ff = mp_Bj (oeq yF xF, oFalseC) hneqYX yx
                             val r  = Thm.implies_elim (oFalse_elimBj_at (lmem yF tF)) ff
                         in Thm.implies_intr (ctermSigL (jT (oeq yF hF))) r end;
                val cB = let val hm = Thm.assume (ctermSigL (jT (lmem yF tF)))
                         in Thm.implies_intr (ctermSigL (jT (lmem yF tF))) hm end;
              in disjE_elimBj (oeq yF hF, lmem yF tF, lmem yF tF) djmem cA cB end;
            val lrm_s = leqL_sym (lremove xF (lcons hF tF), tF) lrm;
            val res = lmem_transBj (yF, tF, lremove xF (lcons hF tF)) lrm_s mem_t;
          in Thm.implies_intr (ctermSigL (jT (oeq xF hF))) res end;
        val caseNeqXH =
          let
            val hneqXH = Thm.assume (ctermSigL (jT (neg (oeq xF hF))));
            val lrm = Thm.implies_elim (lremoveConsNeq_Bj (xF, hF, tF)) hneqXH;
            val target = lcons hF (lremove xF tF);
            val mem_target =
              let
                val cA = let val hyh = Thm.assume (ctermSigL (jT (oeq yF hF)))
                             val r = Thm.implies_elim (lmemConsBwd_Bj (yF, hF, lremove xF tF))
                                       (disjI1_Bj (oeq yF hF, lmem yF (lremove xF tF)) hyh)
                         in Thm.implies_intr (ctermSigL (jT (oeq yF hF))) r end;
                val cB = let val hmt = Thm.assume (ctermSigL (jT (lmem yF tF)))
                             val cj  = conjI_Bj (lmem yF tF, neg (oeq yF xF)) hmt hneqYX
                             val mr  = mp_Bj (hypBody tF, lmem yF (lremove xF tF)) IH cj
                             val r = Thm.implies_elim (lmemConsBwd_Bj (yF, hF, lremove xF tF))
                                       (disjI2_Bj (oeq yF hF, lmem yF (lremove xF tF)) mr)
                         in Thm.implies_intr (ctermSigL (jT (lmem yF tF))) r end;
              in disjE_elimBj (oeq yF hF, lmem yF tF, lmem yF target) djmem cA cB end;
            val lrm_s = leqL_sym (lremove xF (lcons hF tF), target) lrm;
            val res = lmem_transBj (yF, target, lremove xF (lcons hF tF)) lrm_s mem_target;
          in Thm.implies_intr (ctermSigL (jT (neg (oeq xF hF)))) res end;
        val em = ex_middle_atBj (oeq xF hF);
        val conc = disjE_elimBj (oeq xF hF, neg (oeq xF hF), lmem yF (lremove xF (lcons hF tF))) em caseEqXH caseNeqXH;
        val dis = Thm.implies_intr (ctermSigL (jT (hypBody (lcons hF tF)))) conc;
      in impI_Bj (hypBody (lcons hF tF), lmem yF (lremove xF (lcons hF tF))) dis end;
    val step1 = Thm.forall_intr (ctermSigL hF)
                  (Thm.forall_intr (ctermSigL tF) (Thm.implies_intr (ctermSigL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hhL = Thm.assume (ctermSigL (jT (hypBody LF)));
    val concL = mp_Bj (hypBody LF, lmem yF (lremove xF LF)) r2 hhL;
    val d1 = Thm.implies_intr (ctermSigL (jT (hypBody LF))) concL;
  in varify d1 end;
(* mem_remove_neq wrapper : lmem y L -> neg(oeq y x) -> lmem y (lremove x L) *)
val mem_remove_bwd_vBj = varify mem_remove_bwd;
fun mem_remove_neq_at (yT, xT, LT) hmem hneq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("y",0), ctermSigL yT),(("x",0), ctermSigL xT),(("L",0), ctermSigL LT)] mem_remove_bwd_vBj);
      val cj = conjI_Bj (lmem yT LT, neg (oeq yT xT)) hmem hneq
  in Thm.implies_elim inst cj end;
val () = out "MEM_REMOVE_BWD_DONE\n";

(* ============================================================================
   not_mem_remove : lnodup L ==> neg (lmem x (lremove x L))
       i.e. after removing the (unique) occurrence of x, x is gone.
   (list_induct on L)
   ============================================================================ *)
val not_mem_remove =
  let
    val xF = Free("x", natT);
    fun concBody zt = mkImp (lnodup zt) (neg (lmem xF (lremove xF zt)));
    val Qpred = Abs("z", natlistT, concBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = list_induct_atBj (Qpred, LF);
    val base =
      let
        (* lremove x lnil = lnil ; lmem x lnil absurd *)
        val hnd = Thm.assume (ctermSigL (jT (lnodup lnilC)));
        val negbody =
          let val hm = Thm.assume (ctermSigL (jT (lmem xF (lremove xF lnilC))))
              val lrm = lremoveNil_Bj xF
              val mem_lnil = lmem_transBj (xF, lremove xF lnilC, lnilC) lrm hm
              val ff = Thm.implies_elim (lmemNilElim_Bj xF) mem_lnil
              val dis = Thm.implies_intr (ctermSigL (jT (lmem xF (lremove xF lnilC)))) ff
          in impI_Bj (lmem xF (lremove xF lnilC), oFalseC) dis end;
        val dis2 = Thm.implies_intr (ctermSigL (jT (lnodup lnilC))) negbody;
      in impI_Bj (lnodup lnilC, neg (lmem xF (lremove xF lnilC))) dis2 end;
    val hF = Free("h", natT); val tF = Free("t", natlistT);
    val ihprop = jT (concBody tF);
    val IH = Thm.assume (ctermSigL ihprop);
    val stepConcl =
      let
        val hnd = Thm.assume (ctermSigL (jT (lnodup (lcons hF tF))));
        val cj  = Thm.implies_elim (lnodupConsFwd_Bj (hF, tF)) hnd;
        val nmem_h_t = conjunct1_Bj (neg (lmem hF tF), lnodup tF) cj;  (* neg (lmem h t) *)
        val nd_t     = conjunct2_Bj (neg (lmem hF tF), lnodup tF) cj;  (* lnodup t *)
        (* prove neg (lmem x (lremove x (lcons h t))) *)
        val negbody =
          let
            val hm = Thm.assume (ctermSigL (jT (lmem xF (lremove xF (lcons hF tF)))));
            (* case x = h : lremove x (lcons h t) = t ; lmem x t.  but x=h and neg(lmem h t) -> contra *)
            val caseEq =
              let
                val heq = Thm.assume (ctermSigL (jT (oeq xF hF)));
                val lrm = Thm.implies_elim (lremoveConsEq_Bj (xF, hF, tF)) heq;  (* leq (lremove..) t *)
                val mem_t = lmem_transBj (xF, lremove xF (lcons hF tF), tF) lrm hm;  (* lmem x t *)
                (* rewrite x -> h : lmem h t *)
                val Pm = Term.lambda (Free("zm",natT)) (lmem (Free("zm",natT)) tF);
                val mem_h_t = substPredBj (Pm, xF, hF) heq mem_t;   (* lmem h t *)
                val ff = mp_Bj (lmem hF tF, oFalseC) nmem_h_t mem_h_t;
              in Thm.implies_intr (ctermSigL (jT (oeq xF hF))) ff end;
            (* case x <> h : lremove x (lcons h t) = lcons h (lremove x t).
               lmem x (lcons h (lremove x t)) -> Disj (x=h)(lmem x (lremove x t)).
               x=h contradicts hneq ; lmem x (lremove x t) contradicts IH(nd_t). *)
            val caseNeq =
              let
                val hneq = Thm.assume (ctermSigL (jT (neg (oeq xF hF))));
                val lrm = Thm.implies_elim (lremoveConsNeq_Bj (xF, hF, tF)) hneq;
                val mem_cons = lmem_transBj (xF, lremove xF (lcons hF tF), lcons hF (lremove xF tF)) lrm hm;
                val dj = Thm.implies_elim (lmemConsFwd_Bj (xF, hF, lremove xF tF)) mem_cons;
                          (* Disj (oeq x h)(lmem x (lremove x t)) *)
                val cA = let val hxh = Thm.assume (ctermSigL (jT (oeq xF hF)))
                             val ff = mp_Bj (oeq xF hF, oFalseC) hneq hxh
                         in Thm.implies_intr (ctermSigL (jT (oeq xF hF))) ff end;
                val cB = let val hmr = Thm.assume (ctermSigL (jT (lmem xF (lremove xF tF))))
                             val nmem_x_rt = mp_Bj (lnodup tF, neg (lmem xF (lremove xF tF))) IH nd_t
                             val ff = mp_Bj (lmem xF (lremove xF tF), oFalseC) nmem_x_rt hmr
                         in Thm.implies_intr (ctermSigL (jT (lmem xF (lremove xF tF)))) ff end;
                val ff2 = disjE_elimBj (oeq xF hF, lmem xF (lremove xF tF), oFalseC) dj cA cB;
              in Thm.implies_intr (ctermSigL (jT (neg (oeq xF hF)))) ff2 end;
            val em = ex_middle_atBj (oeq xF hF);
            val ff = disjE_elimBj (oeq xF hF, neg (oeq xF hF), oFalseC) em caseEq caseNeq;
            val dis = Thm.implies_intr (ctermSigL (jT (lmem xF (lremove xF (lcons hF tF))))) ff;
          in impI_Bj (lmem xF (lremove xF (lcons hF tF)), oFalseC) dis end;
        val dis2 = Thm.implies_intr (ctermSigL (jT (lnodup (lcons hF tF)))) negbody;
      in impI_Bj (lnodup (lcons hF tF), neg (lmem xF (lremove xF (lcons hF tF)))) dis2 end;
    val step1 = Thm.forall_intr (ctermSigL hF)
                  (Thm.forall_intr (ctermSigL tF) (Thm.implies_intr (ctermSigL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hnd = Thm.assume (ctermSigL (jT (lnodup LF)));
    val concL = mp_Bj (lnodup LF, neg (lmem xF (lremove xF LF))) r2 hnd;
    val d1 = Thm.implies_intr (ctermSigL (jT (lnodup LF))) concL;
  in varify d1 end;
val not_mem_remove_vBj = varify not_mem_remove;
fun not_mem_remove_at (xT, LT) hnd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("x",0), ctermSigL xT),(("L",0), ctermSigL LT)] not_mem_remove_vBj)
  in Thm.implies_elim inst hnd end;
val () = out "NOT_MEM_REMOVE_DONE\n";

(* ============================================================================
   nodup_remove : lnodup L ==> lnodup (lremove x L)   (list_induct on L)
   ============================================================================ *)
val nodup_remove =
  let
    val xF = Free("x", natT);
    fun concBody zt = mkImp (lnodup zt) (lnodup (lremove xF zt));
    val Qpred = Abs("z", natlistT, concBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = list_induct_atBj (Qpred, LF);
    val base =
      let
        val hnd = Thm.assume (ctermSigL (jT (lnodup lnilC)));
        val lrm = lremoveNil_Bj xF;
        val lrm_s = leqL_sym (lremove xF lnilC, lnilC) lrm;
        val res = lnodup_transBj (lnilC, lremove xF lnilC) lrm_s hnd;
        val dis = Thm.implies_intr (ctermSigL (jT (lnodup lnilC))) res;
      in impI_Bj (lnodup lnilC, lnodup (lremove xF lnilC)) dis end;
    val hF = Free("h", natT); val tF = Free("t", natlistT);
    val ihprop = jT (concBody tF);
    val IH = Thm.assume (ctermSigL ihprop);
    val stepConcl =
      let
        val hnd = Thm.assume (ctermSigL (jT (lnodup (lcons hF tF))));
        val cj  = Thm.implies_elim (lnodupConsFwd_Bj (hF, tF)) hnd;
        val nmem = conjunct1_Bj (neg (lmem hF tF), lnodup tF) cj;
        val ndt  = conjunct2_Bj (neg (lmem hF tF), lnodup tF) cj;
        val caseEq =
          let
            val heq = Thm.assume (ctermSigL (jT (oeq xF hF)));
            val lrm = Thm.implies_elim (lremoveConsEq_Bj (xF, hF, tF)) heq;
            val lrm_s = leqL_sym (lremove xF (lcons hF tF), tF) lrm;
            val res = lnodup_transBj (tF, lremove xF (lcons hF tF)) lrm_s ndt;
          in Thm.implies_intr (ctermSigL (jT (oeq xF hF))) res end;
        val caseNeq =
          let
            val hneq = Thm.assume (ctermSigL (jT (neg (oeq xF hF))));
            val lrm = Thm.implies_elim (lremoveConsNeq_Bj (xF, hF, tF)) hneq;
            val ndrt = mp_Bj (lnodup tF, lnodup (lremove xF tF)) IH ndt;
            val nmem_rt =
              let val hassm = Thm.assume (ctermSigL (jT (lmem hF (lremove xF tF))))
                  val inT   = mem_remove_fwd_at (hF, xF, tF) hassm
                  val ff    = mp_Bj (lmem hF tF, oFalseC) nmem inT
                  val dis   = Thm.implies_intr (ctermSigL (jT (lmem hF (lremove xF tF)))) ff
              in impI_Bj (lmem hF (lremove xF tF), oFalseC) dis end;
            val cj2 = conjI_Bj (neg (lmem hF (lremove xF tF)), lnodup (lremove xF tF)) nmem_rt ndrt;
            val nd_target = Thm.implies_elim (lnodupConsBwd_Bj (hF, lremove xF tF)) cj2;
            val lrm_s = leqL_sym (lremove xF (lcons hF tF), lcons hF (lremove xF tF)) lrm;
            val res = lnodup_transBj (lcons hF (lremove xF tF), lremove xF (lcons hF tF)) lrm_s nd_target;
          in Thm.implies_intr (ctermSigL (jT (neg (oeq xF hF)))) res end;
        val em = ex_middle_atBj (oeq xF hF);
        val conc = disjE_elimBj (oeq xF hF, neg (oeq xF hF), lnodup (lremove xF (lcons hF tF))) em caseEq caseNeq;
        val dis = Thm.implies_intr (ctermSigL (jT (lnodup (lcons hF tF)))) conc;
      in impI_Bj (lnodup (lcons hF tF), lnodup (lremove xF (lcons hF tF))) dis end;
    val step1 = Thm.forall_intr (ctermSigL hF)
                  (Thm.forall_intr (ctermSigL tF) (Thm.implies_intr (ctermSigL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hndL = Thm.assume (ctermSigL (jT (lnodup LF)));
    val concL = mp_Bj (lnodup LF, lnodup (lremove xF LF)) r2 hndL;
    val d1 = Thm.implies_intr (ctermSigL (jT (lnodup LF))) concL;
  in varify d1 end;
val nodup_remove_vBj = varify nodup_remove;
fun nodup_remove_at (xT, LT) hnd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("x",0), ctermSigL xT),(("L",0), ctermSigL LT)] nodup_remove_vBj)
  in Thm.implies_elim inst hnd end;
val () = out "NODUP_REMOVE_DONE\n";

(* ============================================================================
   le_shrink : le d (Suc N) ==> neg (oeq d (Suc N)) ==> le d N
     proof: le_neq_lt gives lt d (Suc N) ; lt_suc_cases gives lt d N \/ d = N ;
            lt d N = le (Suc d) N -> le d N via le_suc_self + le_trans ;
            d = N -> le d N via le_refl + transport.
   ============================================================================ *)
fun le_shrink (dT, NT) hle hneq =
  let
    val lt_d_SN = le_neq_ltBj_at (dT, suc NT) hle hneq;   (* lt d (Suc N) *)
    val dj = lt_suc_cases_atBj (dT, NT) lt_d_SN;          (* Disj (lt d N)(oeq d N) *)
    val cA = let val hlt = Thm.assume (ctermSigL (jT (lt dT NT)))   (* lt d N = le (Suc d) N *)
                 val le_d_Sd = le_suc_selfBj_at dT                  (* le d (Suc d) *)
                 val r = le_transBj_at (dT, suc dT, NT) le_d_Sd hlt (* le d N *)
             in Thm.implies_intr (ctermSigL (jT (lt dT NT))) r end;
    val cB = let val heq = Thm.assume (ctermSigL (jT (oeq dT NT)))   (* d = N *)
                 (* le d N : transport le N N -> le d N along d = N (sym: N=d into le z N) *)
                 val le_NN = le_reflBj_at NT
                 val Pl = Term.lambda (Free("zL2",natT)) (le (Free("zL2",natT)) NT)
                 val heqs = oeq_sym OF [heq]   (* N = d *)
                 val r = substPredBj (Pl, NT, dT) heqs le_NN   (* le d N *)
             in Thm.implies_intr (ctermSigL (jT (oeq dT NT))) r end;
  in disjE_elimBj (lt dT NT, oeq dT NT, le dT NT) dj cA cB end;
val () = out "LE_SHRINK_DEFINED\n";

(* ============================================================================
   lsumf_vanish : (forall d. lmem d L ==> f d = 0) ==> lsumf f L = 0
     hypothesis reflected into an object Forall riding list_induct.
       hypObj L = Forall (%d. Imp (lmem d L)(oeq (f d) Zero))
       P L      = Imp (hypObj L)(oeq (lsumf f L) Zero)
   ============================================================================ *)
val lsumf_vanish =
  let
    val dAbsV = Free("d", natT);
    fun hypObjAbs zt = Term.lambda dAbsV (mkImp (lmem dAbsV zt) (oeq (fB $ dAbsV) ZeroC));
    fun hypObj zt = mkForall (hypObjAbs zt);
    fun concBody zt = oeq (lsumf fB zt) ZeroC;
    val zAbsV = Free("z", natlistT);
    val Qpred = Term.lambda zAbsV (mkImp (hypObj zAbsV) (concBody zAbsV));
    val LF = Free("L", natlistT);
    val ind = list_induct_atBj (Qpred, LF);
    (* BASE L = lnil : lsumf f lnil = 0 directly *)
    val base =
      let
        val h0 = Thm.assume (ctermSigL (jT (hypObj lnilC)));
        val concl0 = lsumfNilBj_at fB;   (* lsumf f lnil = 0 *)
        val dis = Thm.implies_intr (ctermSigL (jT (hypObj lnilC))) concl0;
      in impI_Bj (hypObj lnilC, concBody lnilC) dis end;
    val hF = Free("h", natT); val tF = Free("t", natlistT);
    val ihprop = jT (mkImp (hypObj tF) (concBody tF));
    val IH = Thm.assume (ctermSigL ihprop);
    val stepConcl =
      let
        val hypC = Thm.assume (ctermSigL (jT (hypObj (lcons hF tF))));
        (* derive hypObj t : !!d. lmem d t ==> f d = 0, from hypObj (lcons h t) *)
        val dd = Free("d", natT);
        val imp_d = allE_Bj (hypObjAbs (lcons hF tF)) dd hypC;  (* Imp (lmem d (lcons h t))(f d = 0) *)
        val le_d_t = Thm.assume (ctermSigL (jT (lmem dd tF)));
        val mem_cons = Thm.implies_elim (lmemConsBwd_Bj (dd, hF, tF))
                          (disjI2_Bj (oeq dd hF, lmem dd tF) le_d_t);  (* lmem d (lcons h t) *)
        val fd0 = mp_Bj (lmem dd (lcons hF tF), oeq (fB $ dd) ZeroC) imp_d mem_cons;
        val imp_d_t_dis = Thm.implies_intr (ctermSigL (jT (lmem dd tF))) fd0;
        val imp_d_t = impI_Bj (lmem dd tF, oeq (fB $ dd) ZeroC) imp_d_t_dis;
        val allMinor = Thm.forall_intr (ctermSigL dd) imp_d_t;
        val hypObjt = allI_Bj (hypObjAbs tF) allMinor;   (* jT (hypObj t) *)
        val sumt0 = mp_Bj (hypObj tF, concBody tF) IH hypObjt;  (* lsumf f t = 0 *)
        (* f h = 0 : allE @ h, mp with lmem h (lcons h t) *)
        val imp_h = allE_Bj (hypObjAbs (lcons hF tF)) hF hypC;
        val mem_h = Thm.implies_elim (lmemConsBwd_Bj (hF, hF, tF))
                       (disjI1_Bj (oeq hF hF, lmem hF tF) (oeqreflBj_at hF));
        val fh0 = mp_Bj (lmem hF (lcons hF tF), oeq (fB $ hF) ZeroC) imp_h mem_h;  (* f h = 0 *)
        (* lsumf f (lcons h t) = f h + lsumf f t = 0 + 0 = 0 *)
        val lsc = lsumfConsBj_at (fB, hF, tF);   (* lsumf f (lcons h t) = f h + lsumf f t *)
        val c1 = add_cong_lBj (fB $ hF, ZeroC, lsumf fB tF) fh0;  (* f h + S = 0 + S *)
        val c2 = add_cong_rBj (ZeroC, lsumf fB tF, ZeroC) sumt0;  (* 0 + S = 0 + 0 *)
        val a00 = add0Bj_at ZeroC;   (* 0 + 0 = 0 *)
        val concl = oeq_trans OF [oeq_trans OF [oeq_trans OF [lsc, c1], c2], a00];
        val dis = Thm.implies_intr (ctermSigL (jT (hypObj (lcons hF tF)))) concl;
      in impI_Bj (hypObj (lcons hF tF), concBody (lcons hF tF)) dis end;
    val step1 = Thm.forall_intr (ctermSigL hF)
                  (Thm.forall_intr (ctermSigL tF) (Thm.implies_intr (ctermSigL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;   (* jT (P L) = jT (Imp (hypObj L)(concBody L)) *)
    (* convert meta-hyp -> jT (hypObj L) -> concBody L *)
    val dd2 = Free("d", natT);
    val metaHyp = Logic.all dd2 (Logic.mk_implies (jT (lmem dd2 LF), jT (oeq (fB $ dd2) ZeroC)));
    val Hm = Thm.assume (ctermSigL metaHyp);
    val Hm_d = Thm.forall_elim (ctermSigL dd2) Hm;
    val imp_d = impI_Bj (lmem dd2 LF, oeq (fB $ dd2) ZeroC) Hm_d;
    val allMinor2 = Thm.forall_intr (ctermSigL dd2) imp_d;
    val hypObjL = allI_Bj (hypObjAbs LF) allMinor2;
    val conclL = mp_Bj (hypObj LF, concBody LF) r2 hypObjL;
    val d1 = Thm.implies_intr (ctermSigL metaHyp) conclL;
  in varify d1 end;
val lsumf_vanish_v = varify lsumf_vanish;
(* lsumf_vanish_apply : given (meta) !!d. lmem d L ==> f d = 0  produce lsumf f L = 0 *)
fun lsumf_vanish_at (fT, LT) metaMinor =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigL
        [(("f",0), ctermSigL fT),(("L",0), ctermSigL LT)] lsumf_vanish_v)
  in Thm.implies_elim inst metaMinor end;
val () = out "LSUMF_VANISH_DONE\n";

(* ============================================================================
   THE SUPPORT BIJECTION : sum_supp_collapse
     (!!d. le d N ==> Disj (lmem d L)(oeq (f d) Zero))    [closed support in range]
     ==> (!!d. lmem d L ==> le d N)                        [L within range]
     ==> lnodup L
     ==> oeq (sumf f N) (lsumf f L)
   BY INDUCTION on N, with L universally quantified (lall) inside the predicate so
   the IH applies to the SHRUNKEN list  lremove (Suc N) L.
   ============================================================================ *)
val sum_supp_collapse =
  let
    (* object-Forall hypotheses, capture-safe over a fresh d *)
    val dAbsV = Free("d", natT);
    fun h1Abs (nt, Lt) = Term.lambda dAbsV (mkImp (le dAbsV nt) (mkDisj (lmem dAbsV Lt) (oeq (fB $ dAbsV) ZeroC)));
    fun H1 (nt, Lt) = mkForall (h1Abs (nt, Lt));
    fun h2Abs (nt, Lt) = Term.lambda dAbsV (mkImp (lmem dAbsV Lt) (le dAbsV nt));
    fun H2 (nt, Lt) = mkForall (h2Abs (nt, Lt));
    fun conc (nt, Lt) = oeq (sumf fB nt) (lsumf fB Lt);
    fun body (nt, Lt) = mkImp (lnodup Lt) (mkImp (H1 (nt, Lt)) (mkImp (H2 (nt, Lt)) (conc (nt, Lt))));
    (* P n = lall (%L. body n L) , capture-safe over a fresh list L *)
    val LAbsV = Free("L", natlistT);
    fun PbodyAbs nt = Term.lambda LAbsV (body (nt, LAbsV));
    fun Pn nt = lall (PbodyAbs nt);
    val zAbsV = Free("z", natT);
    val Qpred = Term.lambda zAbsV (Pn zAbsV);
    val NF = Free("N", natT);
    val ind = nat_induct_atBj (Qpred, NF);

    (* helper: from H1/H2/lnodup at (n,L) [as thms] + L fixed, build conc — shared shape *)

    (* ====================== BASE  n = 0 ====================== *)
    val base =
      let
        val LF = Free("L", natlistT);
        (* fix L : assume lnodup L, H1 0 L, H2 0 L ; prove conc 0 L *)
        val hnd = Thm.assume (ctermSigL (jT (lnodup LF)));
        val hH1 = Thm.assume (ctermSigL (jT (H1 (ZeroC, LF))));
        val hH2 = Thm.assume (ctermSigL (jT (H2 (ZeroC, LF))));
        (* sumf f 0 = f 0 *)
        val sf0 = sumf0Bj_at fB;   (* sumf f 0 = f 0 *)
        (* split on lmem 0 L *)
        val em = ex_middle_atBj (lmem ZeroC LF);
        (* in BOTH sub-cases we need: any member d of (the relevant) list forces d = 0 (H2 at 0). *)
        (* GOAL : oeq (sumf f 0)(lsumf f L) *)
        val goalC = conc (ZeroC, LF);
        val caseMem =
          let
            val hmem0 = Thm.assume (ctermSigL (jT (lmem ZeroC LF)));
            (* extract : lsumf f L = f 0 + lsumf f (lremove 0 L) *)
            val ex = beta_norm (Drule.infer_instantiate ctxtSigL
                  [(("f",0), ctermSigL fB),(("x",0), ctermSigL ZeroC),(("L",0), ctermSigL LF)] (varify lsumf_extract));
            val extr = Thm.implies_elim ex hmem0;   (* lsumf f L = f 0 + lsumf f (lremove 0 L) *)
            (* lsumf f (lremove 0 L) = 0 via lsumf_vanish : any member d is in L (fwd) so le d 0 so d=0,
               but 0 not in (lremove 0 L) (not_mem_remove) -> contradiction -> f d = 0 vacuously. *)
            val rmL = lremove ZeroC LF;
            val vanishMinor =
              let
                val ddv = Free("d", natT);
                val hmemd = Thm.assume (ctermSigL (jT (lmem ddv rmL)));   (* lmem d (lremove 0 L) *)
                (* d in L *)
                val memL = mem_remove_fwd_at (ddv, ZeroC, LF) hmemd;
                (* le d 0 *)
                val imp0 = allE_Bj (h2Abs (ZeroC, LF)) ddv hH2;   (* Imp (lmem d L)(le d 0) *)
                val le_d_0 = mp_Bj (lmem ddv LF, le ddv ZeroC) imp0 memL;  (* le d 0 *)
                (* le d 0 -> d = 0 : le d 0 = Ex p. 0 = d + p ; so d = 0 (add_eq_zero_left) *)
                (* use: oeq d 0 from le d 0 via exE + add_eq_zero_left *)
                val d_eq_0 =
                  let
                    val PabsLe = Abs("p", natT, oeq ZeroC (add ddv (Bound 0)));
                    fun bodyP pF hp =   (* hp : oeq 0 (add d p) *)
                      let val hps = oeq_sym OF [hp]   (* add d p = 0 *)
                          val aez = beta_norm (Drule.infer_instantiate ctxtSigL
                                [(("a",0), ctermSigL ddv),(("b",0), ctermSigL pF)] (varify add_eq_zero_left))
                      in aez OF [hps] end;   (* oeq d 0 *)
                    (* exE on le d 0 *)
                    val exE_inst = beta_norm (Drule.infer_instantiate ctxtSigL
                          [(("P",0), ctermSigL PabsLe), (("Q",0), ctermSigL (oeq ddv ZeroC))] exE_vBj);
                    val partial = Thm.implies_elim exE_inst le_d_0;
                    val pF = Free("p_aez", natT);
                    val hypTerm = jT (Term.betapply (PabsLe, pF));
                    val hypThm = Thm.assume (ctermSigL hypTerm);
                    val bodyThm = bodyP pF hypThm;
                    val minor = Thm.forall_intr (ctermSigL pF) (Thm.implies_intr (ctermSigL hypTerm) bodyThm);
                  in Thm.implies_elim partial minor end;   (* oeq d 0 *)
                (* 0 not in lremove 0 L (not_mem_remove + nodup) -> rewrite d->0 in lmem d (lremove 0 L) *)
                val nmem0 = not_mem_remove_at (ZeroC, LF) hnd;   (* neg (lmem 0 (lremove 0 L)) *)
                val Pm = Term.lambda (Free("zm3",natT)) (lmem (Free("zm3",natT)) rmL);
                val mem0rm = substPredBj (Pm, ddv, ZeroC) d_eq_0 hmemd;   (* lmem 0 (lremove 0 L) *)
                val ff = mp_Bj (lmem ZeroC rmL, oFalseC) nmem0 mem0rm;     (* oFalse *)
                val fd0 = Thm.implies_elim (oFalse_elimBj_at (oeq (fB $ ddv) ZeroC)) ff;   (* f d = 0 *)
                val dis = Thm.implies_intr (ctermSigL (jT (lmem ddv rmL))) fd0;
              in Thm.forall_intr (ctermSigL ddv) dis end;   (* !!d. lmem d (lremove 0 L) ==> f d = 0 *)
            val van = lsumf_vanish_at (fB, rmL) vanishMinor;   (* lsumf f (lremove 0 L) = 0 *)
            (* lsumf f L = f 0 + lsumf f (lremove 0 L) = f 0 + 0 = f 0 *)
            val c1 = add_cong_rBj (fB $ ZeroC, lsumf fB rmL, ZeroC) van;  (* f 0 + S = f 0 + 0 *)
            val a0 = add0rBj_at (fB $ ZeroC);   (* f 0 + 0 = f 0 *)
            val lsumf_eq_f0 = oeq_trans OF [oeq_trans OF [extr, c1], a0];  (* lsumf f L = f 0 *)
            val concl = oeq_trans OF [sf0, oeq_sym OF [lsumf_eq_f0]];   (* sumf f 0 = lsumf f L *)
            val dis = Thm.implies_intr (ctermSigL (jT (lmem ZeroC LF))) concl;
          in dis end;
        val caseNotMem =
          let
            val hnmem0 = Thm.assume (ctermSigL (jT (neg (lmem ZeroC LF))));
            (* f 0 = 0 : H1 at d=0 with le 0 0 gives Disj(lmem 0 L)(f 0=0); lmem 0 L contradicts hnmem0 *)
            val imp0 = allE_Bj (h1Abs (ZeroC, LF)) ZeroC hH1;   (* Imp (le 0 0)(Disj(lmem 0 L)(f 0=0)) *)
            val le00 = le_reflBj_at ZeroC;   (* le 0 0 *)
            val dj0 = mp_Bj (le ZeroC ZeroC, mkDisj (lmem ZeroC LF) (oeq (fB $ ZeroC) ZeroC)) imp0 le00;
            val f00 =
              let
                val cA = let val hm = Thm.assume (ctermSigL (jT (lmem ZeroC LF)))
                             val ff = mp_Bj (lmem ZeroC LF, oFalseC) hnmem0 hm
                             val r = Thm.implies_elim (oFalse_elimBj_at (oeq (fB $ ZeroC) ZeroC)) ff
                         in Thm.implies_intr (ctermSigL (jT (lmem ZeroC LF))) r end;
                val cB = let val h = Thm.assume (ctermSigL (jT (oeq (fB $ ZeroC) ZeroC)))
                         in Thm.implies_intr (ctermSigL (jT (oeq (fB $ ZeroC) ZeroC))) h end;
              in disjE_elimBj (lmem ZeroC LF, oeq (fB $ ZeroC) ZeroC, oeq (fB $ ZeroC) ZeroC) dj0 cA cB end;
            (* lsumf f L = 0 : every member d of L has le d 0 (H2) so d = 0, but 0 not in L (hnmem0) -> vacuous *)
            val vanishMinor =
              let
                val ddv = Free("d", natT);
                val hmemd = Thm.assume (ctermSigL (jT (lmem ddv LF)));
                val imp0h2 = allE_Bj (h2Abs (ZeroC, LF)) ddv hH2;
                val le_d_0 = mp_Bj (lmem ddv LF, le ddv ZeroC) imp0h2 hmemd;
                val d_eq_0 =
                  let
                    val PabsLe = Abs("p", natT, oeq ZeroC (add ddv (Bound 0)));
                    fun bodyP pF hp =
                      let val hps = oeq_sym OF [hp]
                          val aez = beta_norm (Drule.infer_instantiate ctxtSigL
                                [(("a",0), ctermSigL ddv),(("b",0), ctermSigL pF)] (varify add_eq_zero_left))
                      in aez OF [hps] end;
                    val exE_inst = beta_norm (Drule.infer_instantiate ctxtSigL
                          [(("P",0), ctermSigL PabsLe), (("Q",0), ctermSigL (oeq ddv ZeroC))] exE_vBj);
                    val partial = Thm.implies_elim exE_inst le_d_0;
                    val pF = Free("p_aez2", natT);
                    val hypTerm = jT (Term.betapply (PabsLe, pF));
                    val hypThm = Thm.assume (ctermSigL hypTerm);
                    val bodyThm = bodyP pF hypThm;
                    val minor = Thm.forall_intr (ctermSigL pF) (Thm.implies_intr (ctermSigL hypTerm) bodyThm);
                  in Thm.implies_elim partial minor end;
                (* d = 0 -> lmem 0 L (rewrite) contradicts hnmem0 *)
                val Pm = Term.lambda (Free("zm4",natT)) (lmem (Free("zm4",natT)) LF);
                val mem0L = substPredBj (Pm, ddv, ZeroC) d_eq_0 hmemd;
                val ff = mp_Bj (lmem ZeroC LF, oFalseC) hnmem0 mem0L;
                val fd0 = Thm.implies_elim (oFalse_elimBj_at (oeq (fB $ ddv) ZeroC)) ff;
                val dis = Thm.implies_intr (ctermSigL (jT (lmem ddv LF))) fd0;
              in Thm.forall_intr (ctermSigL ddv) dis end;
            val van = lsumf_vanish_at (fB, LF) vanishMinor;   (* lsumf f L = 0 *)
            (* sumf f 0 = f 0 = 0 = lsumf f L *)
            val concl = oeq_trans OF [oeq_trans OF [sf0, f00], oeq_sym OF [van]];  (* sumf f 0 = lsumf f L *)
            val dis = Thm.implies_intr (ctermSigL (jT (neg (lmem ZeroC LF)))) concl;
          in dis end;
        val concBase = disjE_elimBj (lmem ZeroC LF, neg (lmem ZeroC LF), goalC) em caseMem caseNotMem;
        (* discharge the three OBJECT hypotheses (impI_Bj) to match body's mkImp, + lallI *)
        val d1 = impI_Bj (H2 (ZeroC, LF), conc (ZeroC, LF))
                   (Thm.implies_intr (ctermSigL (jT (H2 (ZeroC, LF)))) concBase);
        val d2 = impI_Bj (H1 (ZeroC, LF), mkImp (H2 (ZeroC, LF)) (conc (ZeroC, LF)))
                   (Thm.implies_intr (ctermSigL (jT (H1 (ZeroC, LF)))) d1);
        val d3 = impI_Bj (lnodup LF, mkImp (H1 (ZeroC, LF)) (mkImp (H2 (ZeroC, LF)) (conc (ZeroC, LF))))
                   (Thm.implies_intr (ctermSigL (jT (lnodup LF))) d2);
        val allL = Thm.forall_intr (ctermSigL LF) d3;
      in lallI_Bj (PbodyAbs ZeroC) allL end;
    val () = out "SUPP_BIJ_BASE_OK\n";

    (* ====================== STEP  n = Suc N' ====================== *)
    val xF = Free("x", natT);   (* the induction variable N' *)
    val ihprop = jT (Pn xF);
    val IH = Thm.assume (ctermSigL ihprop);
    val stepConcl =
      let
        val LF = Free("L", natlistT);
        val SN = suc xF;   (* Suc N' *)
        val hnd = Thm.assume (ctermSigL (jT (lnodup LF)));
        val hH1 = Thm.assume (ctermSigL (jT (H1 (SN, LF))));
        val hH2 = Thm.assume (ctermSigL (jT (H2 (SN, LF))));
        val goalC = conc (SN, LF);
        (* sumf f (Suc N') = sumf f N' + f (Suc N') *)
        val sfS = sumfSucBj_at (fB, xF);
        val em = ex_middle_atBj (lmem SN LF);
        (* ---- helper: derive H1(N', L') and H2(N', L') for a target list L', then mp IH ---- *)
        (* applyIH L' : returns  oeq (sumf f N')(lsumf f L')  given proofs nodup', H1', H2' *)
        fun applyIH (LP, hndP, hH1P, hH2P) =
          let
            val ihL = lallE_Bj (PbodyAbs xF) LP IH;   (* jT (body N' L') *)
            val s1 = mp_Bj (lnodup LP, mkImp (H1 (xF, LP)) (mkImp (H2 (xF, LP)) (conc (xF, LP)))) ihL hndP;
            val s2 = mp_Bj (H1 (xF, LP), mkImp (H2 (xF, LP)) (conc (xF, LP))) s1 hH1P;
            val s3 = mp_Bj (H2 (xF, LP), conc (xF, LP)) s2 hH2P;
          in s3 end;   (* oeq (sumf f N')(lsumf f L') *)

        val caseMem =
          let
            val hmemSN = Thm.assume (ctermSigL (jT (lmem SN LF)));
            val LP = lremove SN LF;   (* L' = lremove (Suc N') L *)
            (* nodup' = nodup_remove *)
            val hndP = nodup_remove_at (SN, LF) hnd;
            (* H1' : !!d. le d N' ==> Disj (lmem d L')(f d = 0) *)
            val hH1P =
              let
                val ddv = Free("d", natT);
                val hle_d_N = Thm.assume (ctermSigL (jT (le ddv xF)));   (* le d N' *)
                (* le d (Suc N') via le_suc_self + le_trans *)
                val le_N_SN = le_suc_selfBj_at xF;   (* le N' (Suc N') *)
                val le_d_SN = le_transBj_at (ddv, xF, SN) hle_d_N le_N_SN;  (* le d (Suc N') *)
                val imp = allE_Bj (h1Abs (SN, LF)) ddv hH1;  (* Imp (le d (Suc N'))(Disj(lmem d L)(f d=0)) *)
                val dj = mp_Bj (le ddv SN, mkDisj (lmem ddv LF)(oeq (fB $ ddv) ZeroC)) imp le_d_SN;
                (* convert Disj(lmem d L)(f d=0) -> Disj(lmem d L')(f d=0) *)
                val djP =
                  let
                    val cA = let val hm = Thm.assume (ctermSigL (jT (lmem ddv LF)))
                                 (* d <> Suc N' since d <= N' (le d N') => lt d (Suc N') => d <> Suc N' *)
                                 val neq =
                                   let val heqd = Thm.assume (ctermSigL (jT (oeq ddv SN)))  (* d = Suc N' *)
                                       (* le d N' + d = Suc N' -> le (Suc N') N' -> lt N' N' -> oFalse *)
                                       val Pl = Term.lambda (Free("zq",natT)) (le (Free("zq",natT)) xF)
                                       val le_SN_N = substPredBj (Pl, ddv, SN) heqd hle_d_N  (* le (Suc N') N' = lt N' N' *)
                                       val ff = (lt_irrefl_Sg xF) OF [le_SN_N]  (* lt N' N' -> oFalse ; lt_irrefl_Sg from sigma context *)
                                       val dis = Thm.implies_intr (ctermSigL (jT (oeq ddv SN))) ff
                                   in impI_Bj (oeq ddv SN, oFalseC) dis end;  (* neg (oeq d (Suc N')) *)
                                 val memP = mem_remove_neq_at (ddv, SN, LF) hm neq  (* lmem d (lremove (Suc N') L) = lmem d L' *)
                                 val r = disjI1_Bj (lmem ddv LP, oeq (fB $ ddv) ZeroC) memP
                             in Thm.implies_intr (ctermSigL (jT (lmem ddv LF))) r end;
                    val cB = let val hf = Thm.assume (ctermSigL (jT (oeq (fB $ ddv) ZeroC)))
                                 val r = disjI2_Bj (lmem ddv LP, oeq (fB $ ddv) ZeroC) hf
                             in Thm.implies_intr (ctermSigL (jT (oeq (fB $ ddv) ZeroC))) r end;
                  in disjE_elimBj (lmem ddv LF, oeq (fB $ ddv) ZeroC, mkDisj (lmem ddv LP)(oeq (fB $ ddv) ZeroC)) dj cA cB end;
                val dis = impI_Bj (le ddv xF, mkDisj (lmem ddv LP)(oeq (fB $ ddv) ZeroC))
                            (Thm.implies_intr (ctermSigL (jT (le ddv xF))) djP);
                val allm = Thm.forall_intr (ctermSigL ddv) dis;
              in allI_Bj (h1Abs (xF, LP)) allm end;
            (* H2' : !!d. lmem d L' ==> le d N' *)
            val hH2P =
              let
                val ddv = Free("d", natT);
                val hmemP = Thm.assume (ctermSigL (jT (lmem ddv LP)));   (* lmem d L' *)
                val memL = mem_remove_fwd_at (ddv, SN, LF) hmemP;   (* lmem d L *)
                val imp = allE_Bj (h2Abs (SN, LF)) ddv hH2;   (* Imp (lmem d L)(le d (Suc N')) *)
                val le_d_SN = mp_Bj (lmem ddv LF, le ddv SN) imp memL;  (* le d (Suc N') *)
                (* d <> Suc N' since Suc N' not in L' (not_mem_remove + nodup) *)
                val nmemP = not_mem_remove_at (SN, LF) hnd;   (* neg (lmem (Suc N') L') *)
                val neq =
                  let val heqd = Thm.assume (ctermSigL (jT (oeq ddv SN)))  (* d = Suc N' *)
                      (* lmem d L' + d = Suc N' -> lmem (Suc N') L' contra nmemP *)
                      val Pm = Term.lambda (Free("zm5",natT)) (lmem (Free("zm5",natT)) LP)
                      val memSNP = substPredBj (Pm, ddv, SN) heqd hmemP  (* lmem (Suc N') L' *)
                      val ff = mp_Bj (lmem SN LP, oFalseC) nmemP memSNP
                      val dis = Thm.implies_intr (ctermSigL (jT (oeq ddv SN))) ff
                  in impI_Bj (oeq ddv SN, oFalseC) dis end;  (* neg (oeq d (Suc N')) *)
                val le_d_N = le_shrink (ddv, xF) le_d_SN neq;   (* le d N' *)
                val dis = impI_Bj (lmem ddv LP, le ddv xF)
                            (Thm.implies_intr (ctermSigL (jT (lmem ddv LP))) le_d_N);
                val allm = Thm.forall_intr (ctermSigL ddv) dis;
              in allI_Bj (h2Abs (xF, LP)) allm end;
            val ihEq = applyIH (LP, hndP, hH1P, hH2P);   (* sumf f N' = lsumf f L' *)
            (* extract : lsumf f L = f (Suc N') + lsumf f L' *)
            val ex = beta_norm (Drule.infer_instantiate ctxtSigL
                  [(("f",0), ctermSigL fB),(("x",0), ctermSigL SN),(("L",0), ctermSigL LF)] (varify lsumf_extract));
            val extr = Thm.implies_elim ex hmemSN;   (* lsumf f L = f (Suc N') + lsumf f L' *)
            (* GOAL : sumf f (Suc N') = lsumf f L
                 sumf f (Suc N') = sumf f N' + f (Suc N')        [sfS]
                                 = lsumf f L' + f (Suc N')        [add_cong_l ihEq]
                                 = f (Suc N') + lsumf f L'        [add_comm]
                                 = lsumf f L                      [sym extr] *)
            val c1 = add_cong_lBj (sumf fB xF, lsumf fB LP, fB $ SN) ihEq;  (* (sumf f N') + f SN = (lsumf f L') + f SN *)
            val comm = beta_norm (Drule.infer_instantiate ctxtSigL
                  [(("m",0), ctermSigL (lsumf fB LP)),(("n",0), ctermSigL (fB $ SN))] add_comm_vSg);
                  (* (lsumf f L') + f SN = f SN + (lsumf f L') *)
            val concl = oeq_trans OF [oeq_trans OF [oeq_trans OF [sfS, c1], comm], oeq_sym OF [extr]];
            val dis = Thm.implies_intr (ctermSigL (jT (lmem SN LF))) concl;
          in dis end;

        val caseNotMem =
          let
            val hnmemSN = Thm.assume (ctermSigL (jT (neg (lmem SN LF))));
            (* f (Suc N') = 0 : H1 at d = Suc N' with le (Suc N')(Suc N') gives Disj(lmem SN L)(f SN=0);
               lmem SN L contradicts hnmemSN *)
            val imp = allE_Bj (h1Abs (SN, LF)) SN hH1;
            val le_SN_SN = le_reflBj_at SN;
            val dj = mp_Bj (le SN SN, mkDisj (lmem SN LF)(oeq (fB $ SN) ZeroC)) imp le_SN_SN;
            val fSN0 =
              let
                val cA = let val hm = Thm.assume (ctermSigL (jT (lmem SN LF)))
                             val ff = mp_Bj (lmem SN LF, oFalseC) hnmemSN hm
                             val r = Thm.implies_elim (oFalse_elimBj_at (oeq (fB $ SN) ZeroC)) ff
                         in Thm.implies_intr (ctermSigL (jT (lmem SN LF))) r end;
                val cB = let val h = Thm.assume (ctermSigL (jT (oeq (fB $ SN) ZeroC)))
                         in Thm.implies_intr (ctermSigL (jT (oeq (fB $ SN) ZeroC))) h end;
              in disjE_elimBj (lmem SN LF, oeq (fB $ SN) ZeroC, oeq (fB $ SN) ZeroC) dj cA cB end;
            (* IH at L (same list) ; nodup L given ; H1(N',L), H2(N',L) derivable *)
            val hH1P =
              let
                val ddv = Free("d", natT);
                val hle_d_N = Thm.assume (ctermSigL (jT (le ddv xF)));
                val le_N_SN = le_suc_selfBj_at xF;
                val le_d_SN = le_transBj_at (ddv, xF, SN) hle_d_N le_N_SN;
                val imp = allE_Bj (h1Abs (SN, LF)) ddv hH1;
                val dj = mp_Bj (le ddv SN, mkDisj (lmem ddv LF)(oeq (fB $ ddv) ZeroC)) imp le_d_SN;
                val dis = impI_Bj (le ddv xF, mkDisj (lmem ddv LF)(oeq (fB $ ddv) ZeroC))
                            (Thm.implies_intr (ctermSigL (jT (le ddv xF))) dj);
                val allm = Thm.forall_intr (ctermSigL ddv) dis;
              in allI_Bj (h1Abs (xF, LF)) allm end;
            val hH2P =
              let
                val ddv = Free("d", natT);
                val hmemd = Thm.assume (ctermSigL (jT (lmem ddv LF)));
                val imp = allE_Bj (h2Abs (SN, LF)) ddv hH2;
                val le_d_SN = mp_Bj (lmem ddv LF, le ddv SN) imp hmemd;
                (* d <> Suc N' since d = Suc N' would mean lmem (Suc N') L, contra hnmemSN *)
                val neq =
                  let val heqd = Thm.assume (ctermSigL (jT (oeq ddv SN)))
                      val Pm = Term.lambda (Free("zm6",natT)) (lmem (Free("zm6",natT)) LF)
                      val memSN = substPredBj (Pm, ddv, SN) heqd hmemd
                      val ff = mp_Bj (lmem SN LF, oFalseC) hnmemSN memSN
                      val dis = Thm.implies_intr (ctermSigL (jT (oeq ddv SN))) ff
                  in impI_Bj (oeq ddv SN, oFalseC) dis end;
                val le_d_N = le_shrink (ddv, xF) le_d_SN neq;
                val dis = impI_Bj (lmem ddv LF, le ddv xF)
                            (Thm.implies_intr (ctermSigL (jT (lmem ddv LF))) le_d_N);
                val allm = Thm.forall_intr (ctermSigL ddv) dis;
              in allI_Bj (h2Abs (xF, LF)) allm end;
            val ihEq = applyIH (LF, hnd, hH1P, hH2P);   (* sumf f N' = lsumf f L *)
            (* GOAL : sumf f (Suc N') = lsumf f L
                 sumf f (Suc N') = sumf f N' + f (Suc N')   [sfS]
                                 = sumf f N' + 0            [add_cong_r fSN0]
                                 = sumf f N'                [add0r]
                                 = lsumf f L                [ihEq] *)
            val c1 = add_cong_rBj (sumf fB xF, fB $ SN, ZeroC) fSN0;  (* (sumf f N') + f SN = (sumf f N') + 0 *)
            val a0 = add0rBj_at (sumf fB xF);   (* (sumf f N') + 0 = sumf f N' *)
            val concl = oeq_trans OF [oeq_trans OF [oeq_trans OF [sfS, c1], a0], ihEq];
            val dis = Thm.implies_intr (ctermSigL (jT (neg (lmem SN LF)))) concl;
          in dis end;

        val concStep = disjE_elimBj (lmem SN LF, neg (lmem SN LF), goalC) em caseMem caseNotMem;
        val d1 = impI_Bj (H2 (SN, LF), conc (SN, LF))
                   (Thm.implies_intr (ctermSigL (jT (H2 (SN, LF)))) concStep);
        val d2 = impI_Bj (H1 (SN, LF), mkImp (H2 (SN, LF)) (conc (SN, LF)))
                   (Thm.implies_intr (ctermSigL (jT (H1 (SN, LF)))) d1);
        val d3 = impI_Bj (lnodup LF, mkImp (H1 (SN, LF)) (mkImp (H2 (SN, LF)) (conc (SN, LF))))
                   (Thm.implies_intr (ctermSigL (jT (lnodup LF))) d2);
        val allL = Thm.forall_intr (ctermSigL LF) d3;
      in lallI_Bj (PbodyAbs SN) allL end;
    val () = out "SUPP_BIJ_STEP_OK\n";
    val step1 = Thm.forall_intr (ctermSigL xF) (Thm.implies_intr (ctermSigL ihprop) stepConcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;   (* jT (Pn N) = jT (lall (%L. body N L)) *)
    (* strip lall + the 3 hypotheses to the meta form, with N,L,f the free vars *)
    val LF2 = Free("L", natlistT);
    val bodyN = lallE_Bj (PbodyAbs NF) LF2 r2;   (* jT (body N L) *)
    val hnd = Thm.assume (ctermSigL (jT (lnodup LF2)));
    (* H1 from meta : !!d. le d N ==> Disj (lmem d L)(f d=0) *)
    val ddH = Free("d", natT);
    val metaH1 = Logic.all ddH (Logic.mk_implies (jT (le ddH NF), jT (mkDisj (lmem ddH LF2)(oeq (fB $ ddH) ZeroC))));
    val metaH2 = Logic.all ddH (Logic.mk_implies (jT (lmem ddH LF2), jT (le ddH NF)));
    val HmH1 = Thm.assume (ctermSigL metaH1);
    val HmH2 = Thm.assume (ctermSigL metaH2);
    (* build object H1 N L from metaH1 *)
    val objH1 =
      let val Hm_d = Thm.forall_elim (ctermSigL ddH) HmH1
          val imp = impI_Bj (le ddH NF, mkDisj (lmem ddH LF2)(oeq (fB $ ddH) ZeroC)) Hm_d
          val allm = Thm.forall_intr (ctermSigL ddH) imp
      in allI_Bj (h1Abs (NF, LF2)) allm end;
    val objH2 =
      let val Hm_d = Thm.forall_elim (ctermSigL ddH) HmH2
          val imp = impI_Bj (lmem ddH LF2, le ddH NF) Hm_d
          val allm = Thm.forall_intr (ctermSigL ddH) imp
      in allI_Bj (h2Abs (NF, LF2)) allm end;
    val s1 = mp_Bj (lnodup LF2, mkImp (H1 (NF, LF2)) (mkImp (H2 (NF, LF2)) (conc (NF, LF2)))) bodyN hnd;
    val s2 = mp_Bj (H1 (NF, LF2), mkImp (H2 (NF, LF2)) (conc (NF, LF2))) s1 objH1;
    val s3 = mp_Bj (H2 (NF, LF2), conc (NF, LF2)) s2 objH2;   (* oeq (sumf f N)(lsumf f L) *)
    (* discharge meta-hyps in the right order : H2, H1, nodup *)
    val g1 = Thm.implies_intr (ctermSigL metaH2) s3;
    val g2 = Thm.implies_intr (ctermSigL metaH1) g1;
    val g3 = Thm.implies_intr (ctermSigL (jT (lnodup LF2))) g2;
  in varify g3 end;
val () = out "SUPP_BIJ_ASSEMBLED\n";

(* ============================================================================
   VALIDATION : 0-hyp + aconv the intended schematic statement.
   intended (with N,L free vars, f a function var) — premise order [nodup; H1; H2]:
     lnodup L ==> (!!d. le d N ==> Disj (lmem d L)(f d = 0))
       ==> (!!d. lmem d L ==> le d N) ==> oeq (sumf f N)(lsumf f L)
   ============================================================================ *)
val NVc = Var (("N",0), natT);
val LVc = Var (("L",0), natlistT);
val fVc = Var (("f",0), fnT);
val i_supp =
  let val dd = Free("d", natT)
  in
    Logic.mk_implies (jT (lnodup LVc),
      Logic.mk_implies (
        Logic.all dd (Logic.mk_implies (jT (le dd NVc),
          jT (mkDisj (lmem dd LVc) (oeq (fVc $ dd) ZeroC)))),
        Logic.mk_implies (
          Logic.all dd (Logic.mk_implies (jT (lmem dd LVc), jT (le dd NVc))),
          jT (oeq (sumf fVc NVc)(lsumf fVc LVc)))))
  end;
val r_supp = chkBj ("sum_supp_collapse", sum_supp_collapse, i_supp);

(* SOUNDNESS PROBE 1 : not the unconditional sumf f N = lsumf f L (FALSE without hyps) *)
val s_supp_cond =
  not ((Thm.prop_of sum_supp_collapse) aconv (jT (oeq (sumf fVc NVc)(lsumf fVc LVc))));
val () = if s_supp_cond then out "PROBE_OK sum_supp_collapse needs its hypotheses\n"
         else out "PROBE_FAIL sum_supp_collapse dropped hypotheses!\n";

(* SOUNDNESS PROBE 2 : the conclusion is genuinely (sumf f N = lsumf f L), not the
   trivial reflexive (sumf f N = sumf f N). *)
val s_supp_concl =
  let
    val trivial =
      let val dd = Free("d", natT)
      in Logic.mk_implies (jT (lnodup LVc),
           Logic.mk_implies (
             Logic.all dd (Logic.mk_implies (jT (le dd NVc),
               jT (mkDisj (lmem dd LVc) (oeq (fVc $ dd) ZeroC)))),
             Logic.mk_implies (
               Logic.all dd (Logic.mk_implies (jT (lmem dd LVc), jT (le dd NVc))),
               jT (oeq (sumf fVc NVc)(sumf fVc NVc)))))
      end
  in not ((Thm.prop_of sum_supp_collapse) aconv trivial) end;
val () = if s_supp_concl then out "PROBE_OK sum_supp_collapse conclusion is sumf=lsumf (not reflexive)\n"
         else out "PROBE_FAIL sum_supp_collapse conclusion collapsed!\n";

val () = out ("SUPP_BIJ_HYPS = " ^ Int.toString (length (Thm.hyps_of sum_supp_collapse)) ^ "\n");

val () =
  if r_supp andalso s_supp_cond andalso s_supp_concl
  then out "SUPP_COLLAPSE_OK\n"
  else out "SUPP_COLLAPSE_INCOMPLETE\n";
(* ============================================================================
   EUCLID PERFECT ASSEMBLY — Stage 1: divlist + value lemma.
   Built on ctxtSigL (the bijection's list-lib context) -> ctxtSigD (adds divlist).
   ============================================================================ *)
val () = out "EP_ASM1_BEGIN\n";

(* ---- new const divlist, extending thySigL ---- *)
val thyD0 = Sign.add_consts
  [(Binding.name "divlist", natT --> natT --> natlistT, NoSyn)] thySigL;
val divlistC = Const (Sign.full_name thyD0 (Binding.name "divlist"),
                      natT --> natT --> natlistT);
fun divlist a q = divlistC $ a $ q;

val two = suc (suc ZeroC);
val one = suc ZeroC;
fun p2 t = pow two t;

val aFd = Free("a", natT); val qFd = Free("q", natT);
val ((_,divlist_0_ax), thyD1) = Thm.add_axiom_global (Binding.name "divlist_0",
      jT (leqL (divlist ZeroC qFd) (lcons one (lcons qFd lnilC)))) thyD0;
val ((_,divlist_Suc_ax), thyD2) = Thm.add_axiom_global (Binding.name "divlist_Suc",
      jT (leqL (divlist (suc aFd) qFd)
               (lcons (p2 (suc aFd)) (lcons (mult (p2 (suc aFd)) qFd) (divlist aFd qFd))))) thyD1;

val thySigD  = thyD2;
val ctxtSigD = Proof_Context.init_global thySigD;
val ctermSigD= Thm.cterm_of ctxtSigD;
fun chkD (nm, th, intended) =
  let val nh = length (Thm.hyps_of th);
      val ac = (Thm.prop_of th) aconv intended;
  in if nh = 0 andalso ac then (out ("OK " ^ nm ^ "\n"); true)
     else (out ("FAIL " ^ nm ^ " (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
                ^ "  got      = " ^ Syntax.string_of_term ctxtSigD (Thm.prop_of th) ^ "\n"
                ^ "  intended = " ^ Syntax.string_of_term ctxtSigD intended ^ "\n"); false)
  end;
val () = out "EP_ASM1_CONSTS_OK\n";

(* ---- transfer up to thySigD ---- *)
fun up th = Thm.transfer thySigD th;
(* already-varified list/FOL lemmas from the bijection, lifted to thySigD *)
val oeq_refl_vD    = up oeq_refl_vBj;
val oeq_subst_vD   = up oeq_subst_vBj;
val add_0_vD       = up add_0_vBj;
val add_0_right_vD = up add_0_right_vBj;
val nat_induct_vD  = up nat_induct_vBj;
val exI_vD         = up exI_vBj;
val exE_vD         = up exE_vBj;
val impI_vD        = up impI_vBj;
val mp_vD          = up mp_vBj;
val allI_vD        = up allI_vBj;
val allE_vD        = up allE_vBj;
val disjE_vD       = up disjE_vBj;
val disjI1_vD      = up disjI1_vBj;
val disjI2_vD      = up disjI2_vBj;
val conjI_vD       = up conjI_vBj;
val conjunct1_vD   = up conjunct1_vBj;
val conjunct2_vD   = up conjunct2_vBj;
val ex_middle_vD   = up ex_middle_vBj;
val oFalse_elim_vD = up oFalse_elim_vBj;
val list_induct_vD = up list_induct_vBj;
val lsumf_nil_vD   = up lsumf_nil_vBj;
val lsumf_cons_vD  = up lsumf_cons_vBj;
val lmem_nil_elim_vD = up lmem_nil_elim_vBj;
val lmem_cons_fwd_vD = up lmem_cons_fwd_vBj;
val lmem_cons_bwd_vD = up lmem_cons_bwd_vBj;
val leq_refl_vD    = up leq_refl_vBj;
val leq_subst_vD   = up leq_subst_vBj;
val lnodup_nil_vD  = up lnodup_nil_vBj;
val lnodup_cons_fwd_vD = up lnodup_cons_fwd_vBj;
val lnodup_cons_bwd_vD = up lnodup_cons_bwd_vBj;
(* arith from base (raw, then varify) *)
val add_comm_vD    = varify (up add_comm);
val add_assoc_vD   = varify (up add_assoc);
val mult_comm_vD   = varify (up mult_comm);
val mult_assoc_vD  = varify (up mult_assoc);
val mult_1_right_vD= varify (up mult_1_right);
val oeq_sym_D      = up oeq_sym;
val oeq_trans_D    = up oeq_trans;
(* divlist axioms *)
val divlist_0_vD   = varify divlist_0_ax;
val divlist_Suc_vD = varify divlist_Suc_ax;
val () = out "EP_ASM1_VARIFY_OK\n";

(* ---- ground instantiators on ctxtSigD ---- *)
fun reflD t = beta_norm (Drule.infer_instantiate ctxtSigD [(("a",0), ctermSigD t)] oeq_refl_vD);
fun lsumfNilD f = beta_norm (Drule.infer_instantiate ctxtSigD [(("f",0), ctermSigD f)] lsumf_nil_vD);
fun lsumfConsD (f,h,t) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("f",0), ctermSigD f),(("x",0), ctermSigD h),(("t",0), ctermSigD t)] lsumf_cons_vD);
fun divlist0D q = beta_norm (Drule.infer_instantiate ctxtSigD [(("q",0), ctermSigD q)] divlist_0_vD);
fun divlistSucD (a,q) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("a",0), ctermSigD a),(("q",0), ctermSigD q)] divlist_Suc_vD);

(* leq transport on the list arg of lsumf : leq L M ==> lsumf f L = lsumf f M *)
fun lsumf_leqD (f, LT, MT) hleq =
  let val Pabs = Term.lambda (Free("zLm", natlistT)) (oeq (lsumf f LT) (lsumf f (Free("zLm",natlistT))))
      val inst = beta_norm (Drule.infer_instantiate ctxtSigD
            [(("P",0), ctermSigD Pabs),(("L",0), ctermSigD LT),(("M",0), ctermSigD MT)] leq_subst_vD)
      val rfl = reflD (lsumf f LT)
  in inst OF [hleq, rfl] end;

(* lsumf at divlist 0 / Suc : compute via leq transport through the recursion eqn *)
(* lsumf f (divlist 0 q) = f 1 + (f q + 0)  *)
fun lsumf_divlist_0 (f, q) =
  let val hleq = divlist0D q                          (* leq (divlist 0 q)(lcons 1 (lcons q lnil)) *)
      val tr   = lsumf_leqD (f, divlist ZeroC q, lcons one (lcons q lnilC)) hleq
      (* lsumf f (lcons 1 (lcons q lnil)) = f 1 + lsumf f (lcons q lnil) *)
      val c1 = lsumfConsD (f, one, lcons q lnilC)
      val c2 = lsumfConsD (f, q, lnilC)
      val cn = lsumfNilD f
  in (tr, c1, c2, cn) end;

val () = out "EP_ASM1_INSTANTIATORS_OK\n";
val () = out "EP_ASM1_END\n";
(* ============================================================================
   EUCLID PERFECT ASSEMBLY — Stage 2: the pure value lemma.
     lsumf idw (divlist a q) = mult (sumf (pow 2) a) (add q one)
   where idw = (%d. d).  By induction on a.  Sub-free.
   G(a) := sumf (pow 2) a = sum_{i=0}^a 2^i.
   value  = G(a)*(q+1).
   ============================================================================ *)
val () = out "EP_ASM2_BEGIN\n";

val idw = Abs("d", natT, Bound 0);            (* identity weight *)
fun idwApp t = t;                              (* (idw $ t) beta = t *)

(* extra arith instantiators on ctxtSigD *)
fun add0D t   = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD t)] add_0_vD);
fun add0rD t  = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD t)] add_0_right_vD);
fun addcommD (m,n) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("m",0), ctermSigD m),(("n",0), ctermSigD n)] add_comm_vD);
fun addassocD (m,n,k) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("m",0), ctermSigD m),(("n",0), ctermSigD n),(("k",0), ctermSigD k)] add_assoc_vD);
fun multcommD (m,n) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("m",0), ctermSigD m),(("n",0), ctermSigD n)] mult_comm_vD);
fun multassocD (m,n,k) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("m",0), ctermSigD m),(("n",0), ctermSigD n),(("k",0), ctermSigD k)] mult_assoc_vD);
fun mult1rD t = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD t)] mult_1_right_vD);
fun nat_induct_atD (Qabs, kT) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("P",0), ctermSigD Qabs), (("k",0), ctermSigD kT)] nat_induct_vD);

(* sumf 0 / Suc on ctxtSigD : sumf f 0 = f 0 ; sumf f (Suc n) = sumf f n + f (Suc n) *)
val sumf_0_vD   = up sumf_0_vBj;
val sumf_Suc_vD = up sumf_Suc_vBj;
fun sumf0D f   = beta_norm (Drule.infer_instantiate ctxtSigD [(("f",0), ctermSigD f)] sumf_0_vD);
fun sumfSucD (f,n) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("f",0), ctermSigD f),(("n",0), ctermSigD n)] sumf_Suc_vD);

(* oeq congruences on ctxtSigD via oeq_subst *)
fun add_cong_lD (p,q,k) hpq =
  let val Pabs = Abs("z", natT, oeq (add p k) (add (Bound 0) k))
      val inst = beta_norm (Drule.infer_instantiate ctxtSigD
            [(("P",0), ctermSigD Pabs),(("a",0), ctermSigD p),(("b",0), ctermSigD q)] oeq_subst_vD)
      val rfl = reflD (add p k)
  in inst OF [hpq, rfl] end;
fun add_cong_rD (h,p,q) hpq =
  let val Pabs = Abs("z", natT, oeq (add h p) (add h (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtSigD
            [(("P",0), ctermSigD Pabs),(("a",0), ctermSigD p),(("b",0), ctermSigD q)] oeq_subst_vD)
      val rfl = reflD (add h p)
  in inst OF [hpq, rfl] end;
fun mult_cong_lD (p,q,k) hpq =
  let val Pabs = Abs("z", natT, oeq (mult p k) (mult (Bound 0) k))
      val inst = beta_norm (Drule.infer_instantiate ctxtSigD
            [(("P",0), ctermSigD Pabs),(("a",0), ctermSigD p),(("b",0), ctermSigD q)] oeq_subst_vD)
      val rfl = reflD (mult p k)
  in inst OF [hpq, rfl] end;
fun mult_cong_rD (h,p,q) hpq =
  let val Pabs = Abs("z", natT, oeq (mult h p) (mult h (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtSigD
            [(("P",0), ctermSigD Pabs),(("a",0), ctermSigD p),(("b",0), ctermSigD q)] oeq_subst_vD)
      val rfl = reflD (mult h p)
  in inst OF [hpq, rfl] end;
(* substPred on ctxtSigD : P a, a=b => P b  (general) *)
fun substPredD (Pabs, xT, yT) hxy hPx =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("P",0), ctermSigD Pabs),(("a",0), ctermSigD xT),(("b",0), ctermSigD yT)] oeq_subst_vD)
  in Thm.implies_elim (Thm.implies_elim inst hxy) hPx end;

fun trans2 (h1,h2) = oeq_trans_D OF [h1,h2];
fun symm h = oeq_sym_D OF [h];

(* G(a) = sumf (pow 2) a, pwAbs2 = (pow 2) as a function term *)
val pwAbs2 = powC $ two;

val () = out "EP_ASM2_INFRA_OK\n";

(* ---- value lemma : lsumf idw (divlist a q) = mult (G a)(add q one) ---- *)
val divlist_value =
  let
    val qF = Free("q", natT);
    fun gval at = mult (sumf pwAbs2 at) (add qF one);     (* G(a)*(q+1) *)
    fun lhs  at = lsumf idw (divlist at qF);
    fun gbody zt = oeq (lhs zt) (gval zt);
    val zV = Free("z", natT);
    val Qpred = Term.lambda zV (gbody zV);
    val kIndV = Free("a", natT);
    val ind = nat_induct_atD (Qpred, kIndV);
    (* ---- base a=0 : lsumf idw (divlist 0 q) = idw 1 + (idw q + 0) = 1 + q.
            G(0) = sumf (pow 2) 0 = pow 2 0 = 1 ; gval 0 = 1*(q+1) = q+1.
            Show 1+q = q+1 = (pow 2 0)*(q+1). *)
    val base =
      let
        val hleq = divlist0D qF                          (* leq (divlist 0 q)(lcons 1 (lcons q lnil)) *)
        val tr   = lsumf_leqD (idw, divlist ZeroC qF, lcons one (lcons qF lnilC)) hleq
                                                          (* lsumf idw (divlist 0 q) = lsumf idw (lcons 1 (lcons q lnil)) *)
        val c1 = lsumfConsD (idw, one, lcons qF lnilC)    (* = idw 1 + lsumf idw (lcons q lnil) *)
        val c2 = lsumfConsD (idw, qF, lnilC)              (* lsumf idw (lcons q lnil) = idw q + lsumf idw lnil *)
        val cn = lsumfNilD idw                            (* lsumf idw lnil = 0 *)
        (* idw 1 = 1, idw q = q  (beta) -- lsumfConsD returns terms already with (idw $ x);
           beta_norm in lsumfConsD already reduces idw $ x -> x.  So c1 : ... = add 1 (lsumf idw (lcons q lnil)) *)
        (* chain: lsumf idw (divlist 0 q) = add 1 (add q 0) *)
        val s2 = trans2 (c2, add_cong_rD (qF, lsumf idw lnilC, ZeroC) cn)   (* lsumf idw (lcons q lnil) = add q 0 *)
        val s1 = trans2 (c1, add_cong_rD (one, lsumf idw (lcons qF lnilC), add qF ZeroC) s2)
                                                          (* lsumf idw (lcons 1 (lcons q lnil)) = add 1 (add q 0) *)
        val lhs0 = trans2 (tr, s1)                        (* lsumf idw (divlist 0 q) = add 1 (add q 0) *)
        val aq0  = add0rD qF                              (* add q 0 = q *)
        val lhs0b = trans2 (lhs0, add_cong_rD (one, add qF ZeroC, qF) aq0)  (* = add 1 q *)
        val comm1q = addcommD (one, qF)                  (* add 1 q = add q 1 *)
        val lhs0c = trans2 (lhs0b, comm1q)               (* = add q 1 = add q one *)
        (* RHS : gval 0 = mult (sumf (pow 2) 0)(add q 1).  sumf (pow 2) 0 = pow 2 0 = 1.
                 mult 1 (add q 1) = add q 1  (mult_comm + mult_1_right or directly). *)
        val s00 = sumf0D pwAbs2                            (* sumf (pow 2) 0 = (pow 2) 0 = pow 2 0 *)
        (* pow 2 0 = 1 *)
        val pz  = beta_norm (Drule.infer_instantiate ctxtSigD [(("a",0), ctermSigD two)] (varify (up pow_Zero_ax)))
                  handle _ => reflD (p2 ZeroC)
        (* gval 0 = mult (sumf (pow 2) 0)(add q 1) ; rewrite sumf..0 -> pow2 0 -> 1 ;
           mult 1 (add q 1) = add q 1. *)
        val g0a = mult_cong_lD (sumf pwAbs2 ZeroC, p2 ZeroC, add qF one) s00   (* mult (sumf..0)(q+1) = mult (pow2 0)(q+1) *)
        val g0b = mult_cong_lD (p2 ZeroC, one, add qF one) pz                  (* mult (pow2 0)(q+1) = mult 1 (q+1) *)
        val m1   = trans2 (multcommD (one, add qF one), mult1rD (add qF one))  (* mult 1 (q+1) = mult (q+1) 1 = q+1 *)
        val g0   = trans2 (trans2 (g0a, g0b), m1)        (* gval 0 = add q 1 *)
        (* lhs0c : lhs = add q 1 ; g0 : gval 0 = add q 1 ; so lhs = gval 0. *)
      in trans2 (lhs0c, symm g0) end;
    (* ---- step ---- *)
    val xF = Free("x", natT);
    val ihprop = jT (gbody xF);
    val IH = Thm.assume (ctermSigD ihprop);
    val stepconcl =
      let
        (* lsumf idw (divlist (Suc x) q)
             = idw (2^(Suc x)) + (idw (2^(Suc x)*q) + lsumf idw (divlist x q))   [recursion]
             = 2^(Suc x) + (2^(Suc x)*q + G(x)*(q+1))                            [beta + IH]
           target gval (Suc x) = G(Suc x)*(q+1) = (G(x) + 2^(Suc x))*(q+1).
           Show equal by semiring. *)
        val A2s = p2 (suc xF)                            (* 2^(Suc x) *)
        val hleq = divlistSucD (xF, qF)                  (* leq (divlist (Suc x) q)(lcons A2s (lcons (A2s*q)(divlist x q))) *)
        val tr   = lsumf_leqD (idw, divlist (suc xF) qF,
                     lcons A2s (lcons (mult A2s qF)(divlist xF qF))) hleq
        val c1 = lsumfConsD (idw, A2s, lcons (mult A2s qF)(divlist xF qF))  (* = A2s + lsumf idw (lcons (A2s*q)(divlist x q)) *)
        val c2 = lsumfConsD (idw, mult A2s qF, divlist xF qF)               (* = (A2s*q) + lsumf idw (divlist x q) *)
        (* rewrite lsumf idw (divlist x q) -> G(x)*(q+1)  via IH *)
        val Gx = sumf pwAbs2 xF
        val gvalx = mult Gx (add qF one)
        val c2b = trans2 (c2, add_cong_rD (mult A2s qF, lsumf idw (divlist xF qF), gvalx) IH)
                                                          (* lsumf idw (lcons (A2s*q)(divlist x q)) = (A2s*q) + G(x)*(q+1) *)
        val c1b = trans2 (c1, add_cong_rD (A2s, lsumf idw (lcons (mult A2s qF)(divlist xF qF)),
                                            add (mult A2s qF) gvalx) c2b)
        val lhsS = trans2 (tr, c1b)                       (* lsumf idw (divlist (Suc x) q) = A2s + ((A2s*q) + G(x)*(q+1)) *)
        (* RHS gval (Suc x) = mult (sumf (pow 2)(Suc x))(q+1) ; sumf (pow 2)(Suc x) = G(x) + (pow 2)(Suc x) = Gx + A2s *)
        val sS = sumfSucD (pwAbs2, xF)                    (* sumf (pow 2)(Suc x) = sumf (pow 2) x + (pow 2)(Suc x) = Gx + A2s *)
        val gSx = mult_cong_lD (sumf pwAbs2 (suc xF), add Gx A2s, add qF one) sS
                                                          (* gval(Suc x) = mult (Gx + A2s)(q+1) *)
        (* mult (Gx + A2s)(q+1) = mult Gx (q+1) + mult A2s (q+1)   [right_distrib] *)
        (* use add_comm form: (a+b)*c = a*c + b*c.  We have mult_assoc/comm; need a distributive.
           Build via left_distrib transferred. *)
        val left_distrib_vD2 = varify (up left_distrib)
        val rdist = beta_norm (Drule.infer_instantiate ctxtSigD
              [(("x",0), ctermSigD (add qF one)),(("m",0), ctermSigD Gx),(("n",0), ctermSigD A2s)] left_distrib_vD2)
        (* left_distrib : mult x (add m n) = add (mult x m)(mult x n).  We want (Gx+A2s)*(q+1).
           That is mult (add Gx A2s)(add q 1).  Use mult_comm to flip then left_distrib. *)
        val flip = multcommD (add Gx A2s, add qF one)    (* mult (Gx+A2s)(q+1) = mult (q+1)(Gx+A2s) *)
        val ld   = beta_norm (Drule.infer_instantiate ctxtSigD
              [(("x",0), ctermSigD (add qF one)),(("m",0), ctermSigD Gx),(("n",0), ctermSigD A2s)] left_distrib_vD2)
                                                          (* mult (q+1)(Gx+A2s) = add (mult (q+1) Gx)(mult (q+1) A2s) *)
        val gSx2 = trans2 (gSx, trans2 (flip, ld))       (* gval(Suc x) = add (mult (q+1) Gx)(mult (q+1) A2s) *)
        (* normalise mult (q+1) Gx = mult Gx (q+1) = gvalx ; mult (q+1) A2s = mult A2s (q+1) *)
        val n1 = multcommD (add qF one, Gx)              (* mult (q+1) Gx = mult Gx (q+1) = gvalx *)
        val n2 = multcommD (add qF one, A2s)             (* mult (q+1) A2s = mult A2s (q+1) *)
        val gSx3 = trans2 (gSx2, trans2 (add_cong_lD (mult (add qF one) Gx, gvalx, mult (add qF one) A2s) n1,
                                          add_cong_rD (gvalx, mult (add qF one) A2s, mult A2s (add qF one)) n2))
                                                          (* gval(Suc x) = add gvalx (mult A2s (q+1)) *)
        (* Now show lhsS = gSx3's RHS :
             lhsS RHS = A2s + ((A2s*q) + gvalx)
             gSx3 RHS = gvalx + (A2s*(q+1))
           A2s*(q+1) = A2s*q + A2s*1 = A2s*q + A2s  [left_distrib on A2s].
           So gvalx + (A2s*q + A2s) = ... commute/assoc to A2s + (A2s*q + gvalx). *)
        val ldA = beta_norm (Drule.infer_instantiate ctxtSigD
              [(("x",0), ctermSigD A2s),(("m",0), ctermSigD qF),(("n",0), ctermSigD one)] left_distrib_vD2)
                                                          (* mult A2s (add q 1) = add (mult A2s q)(mult A2s 1) *)
        val a2s1 = mult1rD A2s                            (* mult A2s 1 = A2s *)
        val ldA2 = trans2 (ldA, add_cong_rD (mult A2s qF, mult A2s one, A2s) a2s1)  (* A2s*(q+1) = A2s*q + A2s *)
        (* gSx3 RHS = gvalx + (A2s*q + A2s) *)
        val gSx4 = trans2 (gSx3, add_cong_rD (gvalx, mult A2s (add qF one), add (mult A2s qF) A2s) ldA2)
                                                          (* gval(Suc x) = gvalx + (A2s*q + A2s) *)
        (* Reassociate both to a canonical form. Target equality:
             A2s + (A2s*q + gvalx)  ==  gvalx + (A2s*q + A2s)
           Prove by commutativity/associativity. Use a normal form: add gvalx (add (A2s*q) A2s).
           LHS = A2s + (A2s*q + gvalx).
             = (A2s + A2s*q) + gvalx        [assoc sym]
             = (A2s*q + A2s) + gvalx        [comm inner]    NO: A2s + A2s*q -> A2s*q + A2s
             = gvalx + (A2s*q + A2s)        [comm outer]
           That equals gSx4 RHS. *)
        val L0 = lhsS                                     (* = A2s + (A2s*q + gvalx) *)
        (* step1: A2s + (A2s*q + gvalx) = (A2s + A2s*q) + gvalx  [assoc sym] *)
        val as1 = symm (addassocD (A2s, mult A2s qF, gvalx))   (* add A2s (add (A2s*q) gvalx) = add (add A2s (A2s*q)) gvalx *)
        (* step2: (A2s + A2s*q) = (A2s*q + A2s)  [comm] -> cong left *)
        val cm  = addcommD (A2s, mult A2s qF)             (* add A2s (A2s*q) = add (A2s*q) A2s *)
        val as2 = add_cong_lD (add A2s (mult A2s qF), add (mult A2s qF) A2s, gvalx) cm
                                                          (* (add A2s (A2s*q)) + gvalx = (add (A2s*q) A2s) + gvalx *)
        (* step3: (A2s*q + A2s) + gvalx = gvalx + (A2s*q + A2s)  [comm] *)
        val as3 = addcommD (add (mult A2s qF) A2s, gvalx)
        val Lnorm = trans2 (L0, trans2 (as1, trans2 (as2, as3)))
                                                          (* lhsS = gvalx + (A2s*q + A2s) *)
        (* Lnorm : lsumf idw (divlist (Suc x) q) = gvalx + (A2s*q + A2s) = gSx4 RHS = gval(Suc x) *)
      in trans2 (Lnorm, symm gSx4) end;
    val step1 = Thm.forall_intr (ctermSigD xF) (Thm.implies_intr (ctermSigD ihprop) stepconcl);
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val qVv = Var (("q",0), natT); val aVv = Var (("a",0), natT);
val i_divlist_value = jT (oeq (lsumf idw (divlist aVv qVv))
                              (mult (sumf pwAbs2 aVv) (add qVv one)));
val r_dlv = chkD ("divlist_value", divlist_value, i_divlist_value);
val () = if r_dlv then out "DIVLIST_VALUE_OK\n" else out "DIVLIST_VALUE_FAIL\n";
val () = out "EP_ASM2_END\n";
(* ============================================================================
   EUCLID PERFECT ASSEMBLY — Stage 3a:
     (1) lsumf_cong : (!!d. lmem d L ==> oeq (f d)(g d)) ==> oeq (lsumf f L)(lsumf g L)
     (2) member_dvd : (!!d. lmem d (divlist a q) ==> dvd d (mult (p2 a) q))
   Both by list/nat induction on ctxtSigD.
   ============================================================================ *)
val () = out "EP_ASM3A_BEGIN\n";

(* FOL on ctxtSigD *)
fun impI_D (At, Bt) hImp =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("A",0), ctermSigD At),(("B",0), ctermSigD Bt)] impI_vD)
  in Thm.implies_elim inst (Thm.implies_intr (ctermSigD (jT At)) hImp) end;
fun mp_D (At, Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("A",0), ctermSigD At),(("B",0), ctermSigD Bt)] mp_vD)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun allI_D Pabs hAll =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD [(("P",0), ctermSigD Pabs)] allI_vD)
  in Thm.implies_elim inst hAll end;
fun allE_D (Pabs, at) hForall =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("P",0), ctermSigD Pabs),(("a",0), ctermSigD at)] allE_vD)
  in Thm.implies_elim inst hForall end;
fun disjE_D (At, Bt, Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("A",0), ctermSigD At),(("B",0), ctermSigD Bt),(("C",0), ctermSigD Ct)] disjE_vD)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB end;
fun oFalse_elimD rT = beta_norm (Drule.infer_instantiate ctxtSigD [(("R",0), ctermSigD rT)] oFalse_elim_vD);
fun lmemNilElimD x = beta_norm (Drule.infer_instantiate ctxtSigD [(("x",0), ctermSigD x)] lmem_nil_elim_vD);
fun lmemConsFwdD (x,y,t) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("x",0), ctermSigD x),(("y",0), ctermSigD y),(("t",0), ctermSigD t)] lmem_cons_fwd_vD);
fun list_induct_atD (Pabs, kT) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("P",0), ctermSigD Pabs),(("L",0), ctermSigD kT)] list_induct_vD);

val () = out "EP_ASM3A_FOL_OK\n";

(* ---- (1) lsumf_cong by list induction ----
   Predicate over lists L (for list_induct):
     Q(L) := (!!d. lmem d L ==> oeq (f d)(g d)) ==> oeq (lsumf f L)(lsumf g L)
   But !!d ... ==> ... can't be the body of a structural-list predicate directly
   (predicate is natlist=>o, object level).  Reflect "(!!d. lmem d L ==> f d=g d)"
   via the lall connective:  lall (%d. Imp (lmem d L)(oeq (f d)(g d))) IS object-level.
   So Q(L) := Imp (lall (%d. Imp (lmem d L)(oeq (f d)(g d)))) (oeq (lsumf f L)(lsumf g L)). *)
val lallI_vD = up lallI_vBj;
val lallE_vD = up lallE_vBj;
fun lallI_D Pabs hAll =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD [(("P",0), ctermSigD Pabs)] lallI_vD)
  in Thm.implies_elim inst hAll end;
fun lallE_D (Pabs, LT) hAll =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("P",0), ctermSigD Pabs),(("L",0), ctermSigD LT)] lallE_vD)
  in Thm.implies_elim inst hAll end;

(* disj/lmem intro helpers on ctxtSigD *)
fun disjI1_D2 (At, Bt) hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("A",0), ctermSigD At),(("B",0), ctermSigD Bt)] disjI1_vD)
  in Thm.implies_elim inst hA end;
fun disjI2_D2 (At, Bt) hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("A",0), ctermSigD At),(("B",0), ctermSigD Bt)] disjI2_vD)
  in Thm.implies_elim inst hB end;
val lmem_cons_bwd_vD = up lmem_cons_bwd_vBj;
fun lmemConsBwdD2 (x,y,t) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("x",0), ctermSigD x),(("y",0), ctermSigD y),(("t",0), ctermSigD t)] lmem_cons_bwd_vD);

val () = out "EP_ASM3A_LALL_OK\n";

val lsumf_cong =
  let
    val fF = Free("f", fnT); val gF = Free("g", fnT);
    (* the membership-implication body, as a function of L *)
    fun memImp LT = Term.lambda (Free("dm", natT))
                      (mkImp (lmem (Free("dm",natT)) LT) (oeq (fF $ (Free("dm",natT))) (gF $ (Free("dm",natT)))));
    fun Qbody LT = mkImp (mkForall (memImp LT)) (oeq (lsumf fF LT)(lsumf gF LT));
    val zL = Free("zL", natlistT);
    val Qpred = Term.lambda zL (Qbody zL);
    val kIndL = Free("L", natlistT);
    val ind = list_induct_atD (Qpred, kIndL);
    (* BASE L = lnil : assume lall(...) ; lsumf f lnil = 0 = lsumf g lnil. *)
    val base =
      let
        val hall = Thm.assume (ctermSigD (jT (mkForall (memImp lnilC))))
        val fn0  = lsumfNilD fF      (* lsumf f lnil = 0 *)
        val gn0  = lsumfNilD gF      (* lsumf g lnil = 0 *)
        val eq   = trans2 (fn0, symm gn0)   (* lsumf f lnil = lsumf g lnil *)
        val body = impI_D (mkForall (memImp lnilC), oeq (lsumf fF lnilC)(lsumf gF lnilC)) eq
      in body end;
    (* STEP : x, t, IH:Q(t) |- Q(lcons x t).
         assume hall : lall (%d. lmem d (lcons x t) -> f d = g d).
         Want lsumf f (lcons x t) = lsumf g (lcons x t).
         lsumf f (lcons x t) = f x + lsumf f t ; similarly g.
         f x = g x : from hall at d=x (lmem x (lcons x t) via lmem_cons_bwd left disj).
         lsumf f t = lsumf g t : IH needs lall(%d. lmem d t -> f d=g d), derive from hall
           (lmem d t -> lmem d (lcons x t) via lmem_cons_bwd right disj). *)
    val xF = Free("x", natT); val tF = Free("t", natlistT);
    val IH = Thm.assume (ctermSigD (jT (Qbody tF)));
    val stepconcl =
      let
        val hall = Thm.assume (ctermSigD (jT (mkForall (memImp (lcons xF tF)))))
        (* f x = g x *)
        val memx = lmemConsBwdD2 (xF, xF, tF)   (* META: jT(Disj(oeq x x)(lmem x t)) ==> jT(lmem x (lcons x t)) *)
        (* build Disj(oeq x x)(lmem x t) via disjI1 of refl *)
        val reflx = reflD xF
        val disjx = disjI1_D2 (oeq xF xF, lmem xF tF) reflx
        val lmemx = Thm.implies_elim memx disjx
        (* hall at d=x *)
        val hallx = allE_D (memImp (lcons xF tF), xF) hall   (* Imp (lmem x (lcons x t))(f x=g x) *)
        val fxgx = mp_D (lmem xF (lcons xF tF), oeq (fF $ xF)(gF $ xF)) hallx lmemx
        (* lall(%d. lmem d t -> f d=g d) from hall *)
        val tallBody = memImp tF
        fun perD dF =
          let
            val hmemt = Thm.assume (ctermSigD (jT (lmem dF tF)))
            (* lmem d t -> Disj(oeq d x)(lmem d t) [disjI2] -> lmem d (lcons x t) [bwd] *)
            val disjd = disjI2_D2 (oeq dF xF, lmem dF tF) hmemt
            val bwd   = lmemConsBwdD2 (dF, xF, tF)
            val lmemd = Thm.implies_elim bwd disjd
            val halld = allE_D (memImp (lcons xF tF), dF) hall
            val fdgd  = mp_D (lmem dF (lcons xF tF), oeq (fF $ dF)(gF $ dF)) halld lmemd
            val body  = impI_D (lmem dF tF, oeq (fF $ dF)(gF $ dF)) fdgd
          in body end;
        val dF = Free("d_lc", natT)
        val tall = allI_D tallBody (Thm.forall_intr (ctermSigD dF) (perD dF))
        (* IH : Q(t) = Imp (Forall(...t)) (lsumf f t = lsumf g t) *)
        val ftgt = mp_D (mkForall (memImp tF), oeq (lsumf fF tF)(lsumf gF tF)) IH tall
        (* assemble : lsumf f (lcons x t) = f x + lsumf f t ; rewrite f x->g x, lsumf f t->lsumf g t ;
           = g x + lsumf g t = lsumf g (lcons x t). *)
        val cf = lsumfConsD (fF, xF, tF)    (* lsumf f (lcons x t) = add (f x)(lsumf f t) *)
        val cg = lsumfConsD (gF, xF, tF)    (* lsumf g (lcons x t) = add (g x)(lsumf g t) *)
        val r1 = trans2 (cf, add_cong_lD (fF $ xF, gF $ xF, lsumf fF tF) fxgx)   (* = add (g x)(lsumf f t) *)
        val r2 = trans2 (r1, add_cong_rD (gF $ xF, lsumf fF tF, lsumf gF tF) ftgt) (* = add (g x)(lsumf g t) *)
        val r3 = trans2 (r2, symm cg)       (* = lsumf g (lcons x t) *)
        val body = impI_D (mkForall (memImp (lcons xF tF)),
                           oeq (lsumf fF (lcons xF tF))(lsumf gF (lcons xF tF))) r3
      in body end;
    val step1 = Thm.forall_intr (ctermSigD xF)
                  (Thm.forall_intr (ctermSigD tF)
                    (Thm.implies_intr (ctermSigD (jT (Qbody tF))) stepconcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
  in varify r2 end;

val () = out "EP_ASM3A_LSUMF_CONG_BUILT\n";

(* validation of lsumf_cong *)
val fVc2 = Var (("f",0), fnT); val gVc2 = Var (("g",0), fnT); val LVc2 = Var (("L",0), natlistT);
val i_lsumf_cong =
  let val dd = Free("d", natT)
  in Logic.mk_implies (
       Logic.all dd (Logic.mk_implies (jT (lmem dd LVc2), jT (oeq (fVc2 $ dd)(gVc2 $ dd)))),
       jT (oeq (lsumf fVc2 LVc2)(lsumf gVc2 LVc2)))
  end;
(* NB lsumf_cong as proven uses the lall-reflected form; we must compare against the
   form actually produced. Print both to inspect. *)
val () = out ("LSUMF_CONG_PROP = " ^ Syntax.string_of_term ctxtSigD (Thm.prop_of lsumf_cong) ^ "\n");
val () = out ("LSUMF_CONG_HYPS = " ^ Int.toString (length (Thm.hyps_of lsumf_cong)) ^ "\n");
val () = out "EP_ASM3A_END\n";
(* ============================================================================
   EUCLID PERFECT ASSEMBLY — Stage 3b: member_dvd
     member_dvd : (!!d. lmem d (divlist a q) ==> dvd d (mult (p2 a) q))   (a universal in q? no: fixed q)
   stated as object Forall over d, conditional shape, by induction on a.
   ============================================================================ *)
val () = out "EP_ASM3B_BEGIN\n";

(* dvd helpers on ctxtSigD : transfer the divchar dvd lemmas *)
val dvd_refl_vD       = varify (up dvd_refl);
val dvd_mult_right_vD = varify (up dvd_mult_right);
val dvd_trans_vD      = varify (up dvd_trans);
val dvd_mult_cong_vD  = varify (up dvd_mult_cong);
fun dvd_refl_D t = beta_norm (Drule.infer_instantiate ctxtSigD [(("a",0), ctermSigD t)] dvd_refl_vD);
fun dvd_mult_right_D (aT,bT,cT) h =   (* dvd a b -> dvd a (mult b c) *)
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("a",0), ctermSigD aT),(("b",0), ctermSigD bT),(("c",0), ctermSigD cT)] dvd_mult_right_vD)
  in Thm.implies_elim inst h end;
fun dvd_trans_D (aT,bT,cT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("a",0), ctermSigD aT),(("b",0), ctermSigD bT),(("c",0), ctermSigD cT)] dvd_trans_vD)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun dvd_mult_cong_D (aT,bT,cT) h =    (* dvd a b -> dvd (mult a c)(mult b c) *)
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("a",0), ctermSigD aT),(("b",0), ctermSigD bT),(("c",0), ctermSigD cT)] dvd_mult_cong_vD)
  in Thm.implies_elim inst h end;
(* dvd congruence on the target term : oeq x y -> dvd a x -> dvd a y *)
fun dvd_cong_target_D (aT, xT, yT) hxy hdvd =
  let val Pabs = Term.lambda (Free("zdt", natT)) (dvd aT (Free("zdt",natT)))
  in substPredD (Pabs, xT, yT) hxy hdvd end;
fun dvd_cong_divisor_D (aT, bT, xT) hab hdvd =  (* oeq a b -> dvd a x -> dvd b x *)
  let val Pabs = Term.lambda (Free("zdd", natT)) (dvd (Free("zdd",natT)) xT)
  in substPredD (Pabs, aT, bT) hab hdvd end;

(* pow / sub instantiators on ctxtSigD *)
val pow_Suc_vD  = varify (up pow_Suc_ax);
val pow_Zero_vD = varify (up pow_Zero_ax);
fun powSucD (at,nt) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("a",0), ctermSigD at),(("n",0), ctermSigD nt)] pow_Suc_vD);
fun powZeroD t = beta_norm (Drule.infer_instantiate ctxtSigD [(("a",0), ctermSigD t)] pow_Zero_vD);

val () = out "EP_ASM3B_DVD_OK\n";

(* helper : dvd (mult (p2 a) q)(mult (p2 (Suc a)) q)
   p2 (Suc a) = 2 * p2 a [pow_Suc] ; mult (p2(Suc a)) q = mult (2 * p2 a) q = 2 * (p2 a * q) [assoc]
   = (p2 a * q) * 2 [comm].  dvd (p2 a*q)((p2 a*q)*2) [dvd_mult_right].  rewrite target. *)
fun dvd_step_q (aT, qT) =
  let
    val pa = p2 aT
    val psa = p2 (suc aT)
    val N  = mult pa qT
    val Nsa = mult psa qT
    (* dvd N (mult N 2) *)
    val d0 = dvd_mult_right_D (N, N, two) (dvd_refl_D N)   (* dvd N (mult N 2) *)
    (* mult N 2 = mult psa q : psa = 2*pa, so mult psa q = mult (2*pa) q = 2*(pa*q) = (pa*q)*2 = mult N 2 *)
    val ps  = powSucD (two, aT)                            (* psa = mult 2 pa *)
    (* mult psa q = mult (mult 2 pa) q [cong divisor] *)
    val c1  = mult_cong_lD (psa, mult two pa, qT) ps       (* mult psa q = mult (mult 2 pa) q *)
    val asc = multassocD (two, pa, qT)                     (* mult (mult 2 pa) q = mult 2 (mult pa q) = mult 2 N *)
    val c2  = trans2 (c1, asc)                             (* mult psa q = mult 2 N *)
    val cm  = multcommD (two, N)                           (* mult 2 N = mult N 2 *)
    val c3  = trans2 (c2, cm)                              (* mult psa q = mult N 2 *)
    (* dvd N (mult psa q) : rewrite mult N 2 -> mult psa q (sym c3) into d0 *)
    val d1  = dvd_cong_target_D (N, mult N two, Nsa) (symm c3) d0   (* dvd N (mult psa q) = dvd N Nsa *)
  in d1 end;

val () = out "EP_ASM3B_DVDSTEP_OK\n";

(* member_dvd : object Forall over d. Imp (lmem d (divlist a q))(dvd d (mult (p2 a) q)) ; induction on a *)
val member_dvd =
  let
    val qF = Free("q", natT)
    fun mdBody at = mkForall (Term.lambda (Free("dmd", natT))
                     (mkImp (lmem (Free("dmd",natT)) (divlist at qF))
                            (dvd (Free("dmd",natT)) (mult (p2 at) qF))))
    val zA = Free("zA", natT)
    val Qpred = Term.lambda zA (mdBody zA)
    val kIndA = Free("a", natT)
    val ind = nat_induct_atD (Qpred, kIndA)
    (* BASE a=0 : divlist 0 q = lcons 1 (lcons q lnil). N0 = mult (p2 0) q = mult 1 q = q.
       member d : d=1 (dvd 1 N0) or d=q (dvd q N0) or absurd. *)
    val base =
      let
        val N0 = mult (p2 ZeroC) qF
        fun perD dF =
          let
            val hmem = Thm.assume (ctermSigD (jT (lmem dF (divlist ZeroC qF))))
            (* lmem d (divlist 0 q) -> lmem d (lcons 1 (lcons q lnil)) via leq transport *)
            val hleq = divlist0D qF
            (* transport membership : leq L M & lmem d L -> lmem d M.  Use leq_subst with pred (%z. lmem d z). *)
            val Pm = Term.lambda (Free("zmm", natlistT)) (lmem dF (Free("zmm",natlistT)))
            val mInst = beta_norm (Drule.infer_instantiate ctxtSigD
                  [(("P",0), ctermSigD Pm),(("L",0), ctermSigD (divlist ZeroC qF)),
                   (("M",0), ctermSigD (lcons one (lcons qF lnilC)))] leq_subst_vD)
            val hmem2 = Thm.implies_elim (Thm.implies_elim mInst hleq) hmem  (* lmem d (lcons 1 (lcons q lnil)) *)
            (* fwd : Disj(oeq d 1)(lmem d (lcons q lnil)) *)
            val f1 = lmemConsFwdD (dF, one, lcons qF lnilC)
            val dj1 = Thm.implies_elim f1 hmem2   (* meta: jT(lmem..) ==> jT(Disj..) ; f1 is meta-impl *)
            val goal = dvd dF N0
            (* case d=1 *)
            val caseEq1 =
              let val heq = Thm.assume (ctermSigD (jT (oeq dF one)))
                  (* dvd 1 N0 : 1 | anything.  dvd 1 N0 = Ex k. N0 = 1*k.  Witness N0, 1*N0=N0. *)
                  (* easier: dvd_refl? no. Use dvd 1 x via mult_1: N0 = mult 1 N0 -> dvd 1 N0 by dvd_intro *)
                  val m1 = symm (trans2 (multcommD (one, N0), mult1rD N0))  (* N0 = mult 1 N0 *)
                  (* dvd 1 N0 : Ex k. N0 = 1*k, witness N0 *)
                  val wAbs = Abs("k", natT, oeq N0 (mult one (Bound 0)))
                  val ex1 = beta_norm (Drule.infer_instantiate ctxtSigD
                        [(("P",0), ctermSigD wAbs),(("a",0), ctermSigD N0)] exI_vD)
                  val dvd1 = Thm.implies_elim ex1 m1            (* dvd 1 N0 *)
                  (* rewrite divisor 1 -> d (sym heq) *)
                  val r = dvd_cong_divisor_D (one, dF, N0) (symm heq) dvd1   (* dvd d N0 *)
              in Thm.implies_intr (ctermSigD (jT (oeq dF one))) r end
            (* case lmem d (lcons q lnil) -> d=q (or absurd) *)
            val caseMemQ =
              let val hmq = Thm.assume (ctermSigD (jT (lmem dF (lcons qF lnilC))))
                  val f2 = lmemConsFwdD (dF, qF, lnilC)
                  val dj2 = Thm.implies_elim f2 hmq   (* Disj(oeq d q)(lmem d lnil) *)
                  val caseEqQ =
                    let val heq = Thm.assume (ctermSigD (jT (oeq dF qF)))
                        (* dvd q N0 : N0 = mult (p2 0) q = mult 1 q = q ; dvd q q [refl] ; rewrite *)
                        val pz = powZeroD two   (* p2 0 = 1 *)
                        val n0q = trans2 (mult_cong_lD (p2 ZeroC, one, qF) pz,
                                          trans2 (multcommD (one, qF), mult1rD qF))  (* N0 = q *)
                        val dvdqq = dvd_refl_D qF             (* dvd q q *)
                        val dvdqN0 = dvd_cong_target_D (qF, qF, N0) (symm n0q) dvdqq  (* dvd q N0 *)
                        val r = dvd_cong_divisor_D (qF, dF, N0) (symm heq) dvdqN0     (* dvd d N0 *)
                    in Thm.implies_intr (ctermSigD (jT (oeq dF qF))) r end
                  val caseMemNil =
                    let val hnil = Thm.assume (ctermSigD (jT (lmem dF lnilC)))
                        val ff = Thm.implies_elim (lmemNilElimD dF) hnil  (* oFalse *)
                        val r  = Thm.implies_elim (oFalse_elimD goal) ff
                    in Thm.implies_intr (ctermSigD (jT (lmem dF lnilC))) r end
              in Thm.implies_intr (ctermSigD (jT (lmem dF (lcons qF lnilC))))
                   (disjE_D (oeq dF qF, lmem dF lnilC, goal) dj2 caseEqQ caseMemNil) end
            val resD = disjE_D (oeq dF one, lmem dF (lcons qF lnilC), goal) dj1 caseEq1 caseMemQ
          in impI_D (lmem dF (divlist ZeroC qF), goal) resD end
        val dFb = Free("d_b", natT)
      in allI_D (Term.lambda (Free("dmd",natT)) (mkImp (lmem (Free("dmd",natT)) (divlist ZeroC qF))
                                                       (dvd (Free("dmd",natT)) N0)))
                (Thm.forall_intr (ctermSigD dFb) (perD dFb)) end
    (* STEP a -> Suc a *)
    val xF = Free("x", natT)
    val IH = Thm.assume (ctermSigD (jT (mdBody xF)))
    val stepconcl =
      let
        val Nx  = mult (p2 xF) qF
        val Nsx = mult (p2 (suc xF)) qF
        val A2s = p2 (suc xF)
        val A2sq = mult A2s qF
        fun perD dF =
          let
            val hmem = Thm.assume (ctermSigD (jT (lmem dF (divlist (suc xF) qF))))
            (* transport to lcons A2s (lcons A2sq (divlist x q)) *)
            val hleq = divlistSucD (xF, qF)
            val Pm = Term.lambda (Free("zmm2", natlistT)) (lmem dF (Free("zmm2",natlistT)))
            val mInst = beta_norm (Drule.infer_instantiate ctxtSigD
                  [(("P",0), ctermSigD Pm),(("L",0), ctermSigD (divlist (suc xF) qF)),
                   (("M",0), ctermSigD (lcons A2s (lcons A2sq (divlist xF qF))))] leq_subst_vD)
            val hmem2 = Thm.implies_elim (Thm.implies_elim mInst hleq) hmem
            val f1 = lmemConsFwdD (dF, A2s, lcons A2sq (divlist xF qF))
            val dj1 = Thm.implies_elim f1 hmem2   (* Disj(oeq d A2s)(lmem d (lcons A2sq (divlist x q))) *)
            val goal = dvd dF Nsx
            (* case d = A2s = 2^(Suc x) : dvd 2^(Suc x) (2^(Suc x)*q) [dvd_mult_right of refl] *)
            val caseHead1 =
              let val heq = Thm.assume (ctermSigD (jT (oeq dF A2s)))
                  val d0 = dvd_mult_right_D (A2s, A2s, qF) (dvd_refl_D A2s)  (* dvd A2s (mult A2s q) = dvd A2s Nsx *)
                  val r  = dvd_cong_divisor_D (A2s, dF, Nsx) (symm heq) d0
              in Thm.implies_intr (ctermSigD (jT (oeq dF A2s))) r end
            (* case lmem d (lcons A2sq (divlist x q)) *)
            val caseRest =
              let val hmr = Thm.assume (ctermSigD (jT (lmem dF (lcons A2sq (divlist xF qF)))))
                  val f2 = lmemConsFwdD (dF, A2sq, divlist xF qF)
                  val dj2 = Thm.implies_elim f2 hmr   (* Disj(oeq d A2sq)(lmem d (divlist x q)) *)
                  (* case d = A2sq : dvd A2sq Nsx [refl, A2sq = Nsx] *)
                  val caseHead2 =
                    let val heq = Thm.assume (ctermSigD (jT (oeq dF A2sq)))
                        val d0 = dvd_refl_D A2sq    (* dvd A2sq A2sq = dvd A2sq Nsx *)
                        val r  = dvd_cong_divisor_D (A2sq, dF, Nsx) (symm heq) d0
                    in Thm.implies_intr (ctermSigD (jT (oeq dF A2sq))) r end
                  (* case lmem d (divlist x q) : IH gives dvd d Nx ; dvd Nx Nsx [dvd_step_q] ; dvd_trans *)
                  val caseTail =
                    let val hmt = Thm.assume (ctermSigD (jT (lmem dF (divlist xF qF))))
                        (* IH at d : Imp (lmem d (divlist x q))(dvd d Nx) *)
                        val ihPred = Term.lambda (Free("dmd",natT))
                              (mkImp (lmem (Free("dmd",natT)) (divlist xF qF))
                                     (dvd (Free("dmd",natT)) Nx))
                        val ihd = allE_D (ihPred, dF) IH   (* Imp (lmem d (divlist x q))(dvd d Nx) *)
                        val dvddNx = mp_D (lmem dF (divlist xF qF), dvd dF Nx) ihd hmt
                        val dvdNxNsx = dvd_step_q (xF, qF)   (* dvd Nx Nsx *)
                        val r = dvd_trans_D (dF, Nx, Nsx) dvddNx dvdNxNsx
                    in Thm.implies_intr (ctermSigD (jT (lmem dF (divlist xF qF)))) r end
              in Thm.implies_intr (ctermSigD (jT (lmem dF (lcons A2sq (divlist xF qF)))))
                   (disjE_D (oeq dF A2sq, lmem dF (divlist xF qF), goal) dj2 caseHead2 caseTail) end
            val resD = disjE_D (oeq dF A2s, lmem dF (lcons A2sq (divlist xF qF)), goal) dj1 caseHead1 caseRest
          in impI_D (lmem dF (divlist (suc xF) qF), goal) resD end
        val dFs = Free("d_s", natT)
      in allI_D (Term.lambda (Free("dmd",natT)) (mkImp (lmem (Free("dmd",natT)) (divlist (suc xF) qF))
                                                       (dvd (Free("dmd",natT)) Nsx)))
                (Thm.forall_intr (ctermSigD dFs) (perD dFs)) end
    val step1 = Thm.forall_intr (ctermSigD xF) (Thm.implies_intr (ctermSigD (jT (mdBody xF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in varify r2 end;

val () = out ("MEMBER_DVD_HYPS = " ^ Int.toString (length (Thm.hyps_of member_dvd)) ^ "\n");
val () = out "MEMBER_DVD_BUILT\n";
val () = out "EP_ASM3B_END\n";
(* ============================================================================
   EUCLID PERFECT ASSEMBLY — Stage 4a: the swt->value bridge.
     sigma_value_bridge :
       oeq (lsumf (swt N) (divlist a q)) (mult (sumf (pow 2) a) (add q one))
     where N = mult (p2 a) q.
   Proof: lsumf_cong (f=swt N, g=idw) since for members d, swt N d = d = idw d
   (member_dvd + swt_dvd); then divlist_value.
   ============================================================================ *)
val () = out "EP_ASM4A_BEGIN\n";

(* swt / sigma transferred onto ctxtSigD *)
val swt_dvd_vD   = varify (up swt_dvd_vSg);
val swt_ndvd_vD  = varify (up swt_ndvd_vSg);
val sigma_def_vD = varify (up sigma_def_vSg);
(* swt_dvd : dvd d n ==> oeq (swt n d) d  (param names: d, n) *)
fun swt_dvd_D (dT, nT) hdvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("d",0), ctermSigD dT),(("n",0), ctermSigD nT)] swt_dvd_vD)
  in Thm.implies_elim inst hdvd end;
fun swt_ndvd_D (dT, nT) hndvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("d",0), ctermSigD dT),(("n",0), ctermSigD nT)] swt_ndvd_vD)
  in Thm.implies_elim inst hndvd end;

val () = out "EP_ASM4A_SWT_OK\n";

(* lsumf_cong applied : given (!!d. lmem d L ==> oeq (f d)(g d)) build oeq (lsumf f L)(lsumf g L) *)
val lsumf_cong_vD = lsumf_cong;   (* already varified ; vars f,g,L *)
fun apply_lsumf_cong (fT, gT, LT) perMemThm =
  (* perMemThm : jT (Forall (%d. Imp (lmem d L)(oeq (f d)(g d)))) *)
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("f",0), ctermSigD fT),(("g",0), ctermSigD gT),(("L",0), ctermSigD LT)] lsumf_cong_vD)
  (* inst : jT(Imp (Forall ...)(lsumf f L = lsumf g L)) ; mp with perMemThm *)
  in mp_D (mkForall (Term.lambda (Free("dd",natT))
              (mkImp (lmem (Free("dd",natT)) LT)(oeq (fT $ (Free("dd",natT)))(gT $ (Free("dd",natT)))))),
           oeq (lsumf fT LT)(lsumf gT LT)) inst perMemThm
  end;

val () = out "EP_ASM4A_INFRA_OK\n";

(* sigma_value_bridge : for fixed a,q, N = mult (p2 a) q :
     oeq (lsumf (swt N)(divlist a q)) (mult (sumf (pow 2) a)(add q one)) *)
val sigma_value_bridge =
  let
    val aF = Free("a", natT); val qF = Free("q", natT)
    val N  = mult (p2 aF) qF
    val swtN = swtC $ N           (* swt N : nat=>nat, partial application *)
    (* per-member : !!d. lmem d (divlist a q) ==> oeq (swt N d)(idw d).
       swt N d = d (swt_dvd, dvd d N from member_dvd) ; idw d = d. *)
    fun perD dF =
      let
        val hmem = Thm.assume (ctermSigD (jT (lmem dF (divlist aF qF))))
        (* member_dvd at (a,q,d) : need dvd d N.  member_dvd is Forall over d, vars a,q. *)
        val mdAll = beta_norm (Drule.infer_instantiate ctxtSigD
                      [(("a",0), ctermSigD aF),(("q",0), ctermSigD qF)] member_dvd)
        (* mdAll : jT (Forall (%d. Imp (lmem d (divlist a q))(dvd d N)))  -- a is Free a here (matches aF) *)
        val mdPred = Term.lambda (Free("dmd",natT))
                      (mkImp (lmem (Free("dmd",natT)) (divlist aF qF))
                             (dvd (Free("dmd",natT)) N))
        val mdAt = allE_D (mdPred, dF) mdAll     (* Imp (lmem d (divlist a q))(dvd d N) *)
        val dvddN = mp_D (lmem dF (divlist aF qF), dvd dF N) mdAt hmem   (* dvd d N *)
        val swtd = swt_dvd_D (dF, N) dvddN       (* oeq (swt N d) d *)
        (* idw d = d  (beta of (idw $ d) -> d) : reflD d is oeq d d ; we want oeq (swt N d)(idw d).
           idw $ d beta-reduces to d, so oeq (swt N d) d IS oeq (swt N d)(idw d) up to beta.
           Build target oeq (swtN $ d)( idw $ d ); since idw$d beta= d, swtd : oeq (swtN$d) d works. *)
        val tgt = oeq (swtN $ dF) (idw $ dF)     (* beta : oeq (swt N d) d *)
        (* swtd : oeq (swt N d) d.  swtN $ dF beta = swt N d.  idw $ dF beta = d.  so swtd proves tgt after beta. *)
        val body = impI_D (lmem dF (divlist aF qF), tgt) swtd
      in body end;
    val dFc = Free("d_b", natT)
    val congPred = Term.lambda (Free("dd",natT))
                     (mkImp (lmem (Free("dd",natT)) (divlist aF qF))
                            (oeq (swtN $ (Free("dd",natT)))(idw $ (Free("dd",natT)))))
    val perAll = allI_D congPred (Thm.forall_intr (ctermSigD dFc) (perD dFc))
    val congEq = apply_lsumf_cong (swtN, idw, divlist aF qF) perAll
                 (* oeq (lsumf (swt N)(divlist a q))(lsumf idw (divlist a q)) *)
    (* divlist_value at (a,q) : oeq (lsumf idw (divlist a q))(mult (G a)(add q 1)) *)
    val dlv = beta_norm (Drule.infer_instantiate ctxtSigD
          [(("a",0), ctermSigD aF),(("q",0), ctermSigD qF)] divlist_value)
    val r = trans2 (congEq, dlv)
  in varify r end;

val aVb = Var (("a",0), natT); val qVb = Var (("q",0), natT)
val Nb  = mult (p2 aVb) qVb
val i_svb = jT (oeq (lsumf (swtC $ Nb) (divlist aVb qVb)) (mult (sumf pwAbs2 aVb)(add qVb one)))
val r_svb = chkD ("sigma_value_bridge", sigma_value_bridge, i_svb)
val () = if r_svb then out "SIGMA_VALUE_BRIDGE_OK\n" else out "SIGMA_VALUE_BRIDGE_FAIL\n";
val () = out "EP_ASM4A_END\n";
(* ============================================================================
   EUCLID PERFECT ASSEMBLY — Stage 4b: N != 0 and H2.
     N_nonzero : prime2 q ==> (oeq (mult (p2 a) q) Zero ==> oFalse)
     H2helper  : prime2 q ==> lmem d (divlist a q) ==> le d (mult (p2 a) q)
   ============================================================================ *)
val () = out "EP_ASM4B_BEGIN\n";

(* transfer proven thms onto thySigD (single transfer via up) *)
val pow2_pos_vD      = varify (up pow2_pos);          (* Ex m. pow2 k = Suc m  (var k) *)
val mult_eq_zero_vD2 = up mult_eq_zero_Sg;            (* oeq (mult a b) 0 ==> Disj(oeq a 0)(oeq b 0) (vars a_mez,b_mez) *)
val dvd_le_vD        = varify (up dvd_le);            (* dvd d n ==> (oeq n 0 ==> oFalse) ==> le d n (vars d,n) *)
val Suc_neq_Zero_vD  = up (varify Suc_neq_Zero_ax);   (* oeq (Suc n) 0 ==> oFalse (var n) *)
val conjunct1_vD2    = conjunct1_vD;

val () = out "EP_ASM4B_TRANSFER_OK\n";

(* prime2 q -> q != 0 i.e. Ex m. q = Suc m.  prime2 q = Conj (lt 1 q)(Forall ...);
   lt 1 q = le 2 q = Ex p. q = add 2 p = add (Suc(Suc 0)) p ; q = Suc(Suc 0 + p)?  Actually
   add (Suc(Suc 0)) p = Suc(Suc(add 0 p)) ... we just need q = Suc something. *)
val exI_atD = fn (Pabs, at) => beta_norm (Drule.infer_instantiate ctxtSigD
      [(("P",0), ctermSigD Pabs),(("a",0), ctermSigD at)] exI_vD);
fun exE_atD (Pabs, goalT) hEx wnm body =
  let
    val wF = Free(wnm, natT)
    val hypTerm = jT (Term.betapply (Pabs, wF))
    val hypThm = Thm.assume (ctermSigD hypTerm)
    val bodyThm = body wF hypThm
    val minor = Thm.forall_intr (ctermSigD wF) (Thm.implies_intr (ctermSigD hypTerm) bodyThm)
    val inst = beta_norm (Drule.infer_instantiate ctxtSigD
          [(("P",0), ctermSigD Pabs),(("Q",0), ctermSigD goalT)] exE_vD)
    val partial = Thm.implies_elim inst hEx
  in Thm.implies_elim partial minor end;
fun conjunct1_D (At, Bt) hConj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("A",0), ctermSigD At),(("B",0), ctermSigD Bt)] conjunct1_vD2)
  in Thm.implies_elim inst hConj end;

(* prime2 q's ppAbs : %d. Imp (dvd d q)(Disj(oeq d 1)(oeq d q)) ; need the term to match prime2 q.
   prime2 q = mkConj (lt (suc Zero) q)(mkForall (ppAbs q)).  We import ppAbs from base. *)
val () = out "EP_ASM4B_FOL_OK\n";

(* N_nonzero : prime2 q ==> (oeq (mult (p2 a) q) Zero ==> oFalse).
   Proof: assume prime2 q and N=0.  mult_eq_zero -> Disj(oeq (p2 a) 0)(oeq q 0).
     p2 a = 0 contradicts pow2_pos (Ex m. p2 a = Suc m, Suc m = 0 absurd).
     q = 0 contradicts q>1 : prime2 q -> lt 1 q -> Ex p. q = add 2 p = Suc(...) != 0. *)
val N_nonzero =
  let
    val aF = Free("a", natT); val qF = Free("q", natT)
    val N = mult (p2 aF) qF
    val hPrime = Thm.assume (ctermSigD (jT (prime2 qF)))
    val hN0    = Thm.assume (ctermSigD (jT (oeq N ZeroC)))
    (* Disj(oeq (p2 a) 0)(oeq q 0) *)
    val mez = beta_norm (Drule.infer_instantiate ctxtSigD
                [(("a_mez",0), ctermSigD (p2 aF)),(("b_mez",0), ctermSigD qF)] mult_eq_zero_vD2)
    val disj = Thm.implies_elim mez hN0
    (* case p2 a = 0 : pow2_pos at a : Ex m. p2 a = Suc m *)
    val casePZ =
      let
        val hpz = Thm.assume (ctermSigD (jT (oeq (p2 aF) ZeroC)))
        val pp  = beta_norm (Drule.infer_instantiate ctxtSigD [(("k",0), ctermSigD aF)] pow2_pos_vD)
        (* pp : Ex m. p2 a = Suc m *)
        val exAbs = Abs("m", natT, oeq (p2 aF) (suc (Bound 0)))
        fun body mF hm =      (* hm : oeq (p2 a) (Suc m) *)
          let
            (* oeq (Suc m) 0 : from hm (p2 a = Suc m) and hpz (p2 a = 0) : Suc m = 0 *)
            val sm0 = oeq_trans_D OF [oeq_sym_D OF [hm], hpz]   (* oeq (Suc m) 0 *)
            val snz = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD mF)] Suc_neq_Zero_vD)
          in Thm.implies_elim snz sm0 end
        val ff = exE_atD (exAbs, oFalseC) pp "m_pz" body
      in Thm.implies_intr (ctermSigD (jT (oeq (p2 aF) ZeroC))) ff end
    (* case q = 0 : prime2 q -> lt 1 q = le 2 q = Ex p. q = add 2 p ; q = 0 -> add 2 p = 0 -> Suc(...) = 0 *)
    val caseQZ =
      let
        val hqz = Thm.assume (ctermSigD (jT (oeq qF ZeroC)))
        val gt1 = conjunct1_D (lt (suc ZeroC) qF, mkForall (ppAbs qF)) hPrime  (* lt 1 q = Ex p. q = add (Suc(Suc 0)) p *)
        val exAbs = Abs("p", natT, oeq qF (add (suc (suc ZeroC)) (Bound 0)))
        fun body pF hp =    (* hp : oeq q (add (Suc(Suc 0)) p) *)
          let
            (* add (Suc(Suc 0)) p = Suc (add (Suc 0) p)  [add_Suc] *)
            val asuc = beta_norm (Drule.infer_instantiate ctxtSigD
                  [(("m",0), ctermSigD (suc ZeroC)),(("n",0), ctermSigD pF)] (varify (up add_Suc)))
            (* q = Suc(add (Suc 0) p) *)
            val qSuc = oeq_trans_D OF [hp, asuc]
            (* Suc(..) = 0 from qSuc + hqz *)
            val sm0 = oeq_trans_D OF [oeq_sym_D OF [qSuc], hqz]   (* oeq (Suc (add (Suc 0) p)) 0 *)
            val snz = beta_norm (Drule.infer_instantiate ctxtSigD
                  [(("n",0), ctermSigD (add (suc ZeroC) pF))] Suc_neq_Zero_vD)
          in Thm.implies_elim snz sm0 end
        val ff = exE_atD (exAbs, oFalseC) gt1 "p_qz" body
      in Thm.implies_intr (ctermSigD (jT (oeq qF ZeroC))) ff end
    val ff = disjE_D (oeq (p2 aF) ZeroC, oeq qF ZeroC, oFalseC) disj casePZ caseQZ
    val d1 = Thm.implies_intr (ctermSigD (jT (oeq N ZeroC))) ff
    val d2 = Thm.implies_intr (ctermSigD (jT (prime2 qF))) d1
  in varify d2 end;

val () = out ("N_NONZERO_HYPS = " ^ Int.toString (length (Thm.hyps_of N_nonzero)) ^ "\n");
val () = out "N_NONZERO_BUILT\n";

(* H2 : prime2 q ==> Forall (%d. Imp (lmem d (divlist a q))(le d N)).
   member d -> dvd d N (member_dvd) ; dvd_le (N nonzero) -> le d N. *)
val H2_thm =
  let
    val aF = Free("a", natT); val qF = Free("q", natT)
    val N = mult (p2 aF) qF
    val hPrime = Thm.assume (ctermSigD (jT (prime2 qF)))
    val nnz = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                  [(("a",0), ctermSigD aF),(("q",0), ctermSigD qF)] N_nonzero)) hPrime
              (* nnz : oeq N 0 ==> oFalse *)
    val mdAll = beta_norm (Drule.infer_instantiate ctxtSigD
                  [(("a",0), ctermSigD aF),(("q",0), ctermSigD qF)] member_dvd)
    fun perD dF =
      let
        val hmem = Thm.assume (ctermSigD (jT (lmem dF (divlist aF qF))))
        val mdPred = Term.lambda (Free("dmd",natT))
                      (mkImp (lmem (Free("dmd",natT)) (divlist aF qF))
                             (dvd (Free("dmd",natT)) N))
        val mdAt = allE_D (mdPred, dF) mdAll
        val dvddN = mp_D (lmem dF (divlist aF qF), dvd dF N) mdAt hmem  (* dvd d N *)
        val dle = beta_norm (Drule.infer_instantiate ctxtSigD
                    [(("d",0), ctermSigD dF),(("n",0), ctermSigD N)] dvd_le_vD)
        (* dle : dvd d N ==> (oeq N 0 ==> oFalse) ==> le d N *)
        val led = Thm.implies_elim (Thm.implies_elim dle dvddN) nnz   (* le d N *)
        val body = impI_D (lmem dF (divlist aF qF), le dF N) led
      in body end;
    val dFh = Free("d_h2", natT)
    val Hpred = Term.lambda (Free("dd",natT))
                  (mkImp (lmem (Free("dd",natT)) (divlist aF qF))(le (Free("dd",natT)) N))
    val forallH = allI_D Hpred (Thm.forall_intr (ctermSigD dFh) (perD dFh))
    val d1 = Thm.implies_intr (ctermSigD (jT (prime2 qF))) forallH
  in varify d1 end;

val () = out ("H2_HYPS = " ^ Int.toString (length (Thm.hyps_of H2_thm)) ^ "\n");
val () = out "H2_BUILT\n";
val () = out "EP_ASM4B_END\n";
(* ============================================================================
   EUCLID PERFECT ASSEMBLY — Stage 5a: le_split + lmem-backward lemmas.
     le_split : le i (Suc a) ==> Disj (oeq i (Suc a)) (le i a)    [meta-impl form]
     lmem_2i  : le i a ==> lmem (p2 i) (divlist a q)              [Forall i, by induction on a]
     lmem_2iq : le i a ==> lmem (mult (p2 i) q) (divlist a q)
   ============================================================================ *)
val () = out "EP_ASM5A_BEGIN\n";

(* transfer + instantiators *)
val disj_zero_or_suc_vD = varify (up disj_zero_or_suc)
val Suc_inj_vD = up (varify Suc_inj_ax)
val add_Suc_right_vD = varify (up add_Suc_right)
fun addSucD (m,n) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("m",0), ctermSigD m),(("n",0), ctermSigD n)] add_Suc_right_vD)   (* add m (Suc n) = Suc(add m n) *)
fun Suc_injD (a,b) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("a",0), ctermSigD a),(("b",0), ctermSigD b)] Suc_inj_vD)) h
(* le_intro on ctxtSigD : le m n with witness w, proof oeq n (add m w) -> le m n *)
fun le_introD (mT, nT, w) hyp =
  let val Pabs = Abs("p", natT, oeq nT (add mT (Bound 0)))
  in exI_atD2 (Pabs, w) hyp end
and exI_atD2 (Pabs, w) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("P",0), ctermSigD Pabs),(("a",0), ctermSigD w)] exI_vD)) h
(* le_dest : le m n = Ex p. n = add m p ; expose the witness via exE *)
fun le_destD (mT, nT, goalT) hle wnm body =
  let val Pabs = Abs("p", natT, oeq nT (add mT (Bound 0)))
  in exE_atD (Pabs, goalT) hle wnm body end
(* disj_zero_or_suc at term : Disj (oeq t 0)(Ex q. t = Suc q) *)
fun dzosD t = beta_norm (Drule.infer_instantiate ctxtSigD [(("p",0), ctermSigD t)] disj_zero_or_suc_vD)

(* robust transitivity by explicit instantiation : oeq A B -> oeq B C -> oeq A C *)
val oeq_trans_iv = varify oeq_trans_D
fun trans3 (aT,bT,cT) hab hbc =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("a",0), ctermSigD aT),(("b",0), ctermSigD bT),(("c",0), ctermSigD cT)] oeq_trans_iv)
  in Thm.implies_elim (Thm.implies_elim inst hab) hbc end;
val oeq_sym_iv = varify oeq_sym_D
fun sym3 (aT,bT) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("a",0), ctermSigD aT),(("b",0), ctermSigD bT)] oeq_sym_iv)
  in Thm.implies_elim inst h end;
val () = out "EP_ASM5A_INFRA_OK\n";

(* le_split : le i (Suc a) ==> Disj (oeq i (Suc a)) (le i a)
   le i (Suc a) = Ex p. Suc a = i + p.  p=0 -> Suc a = i+0 = i -> oeq i (Suc a) [sym].
   p=Suc p' -> Suc a = i + Suc p' = Suc(i+p') [add_Suc] -> a = i+p' [Suc_inj] -> le i a. *)
val le_split =
  let
    val iF = Free("i", natT); val aF = Free("a", natT)
    val hle = Thm.assume (ctermSigD (jT (le iF (suc aF))))
    val goalC = mkDisj (oeq iF (suc aF)) (le iF aF)
    (* expose witness p : Suc a = i + p *)
    fun body pF hp =     (* hp : oeq (Suc a) (add i p) *)
      let
        val dz = dzosD pF    (* Disj (oeq p 0)(Ex q. p = Suc q) *)
        val caseP0 =
          let val hp0 = Thm.assume (ctermSigD (jT (oeq pF ZeroC)))
              (* add i p = add i 0 = i ; Suc a = i *)
              val Pai = Term.lambda (Free("zp", natT)) (oeq (suc aF)(add iF (Free("zp",natT))))
              val sai = substPredD (Pai, pF, ZeroC) hp0 hp   (* oeq (Suc a)(add i 0) *)
              val ai0 = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD iF)] add_0_right_vD)  (* add i 0 = i *)
              val sa_i = trans3 (suc aF, add iF ZeroC, iF) sai ai0   (* oeq (Suc a) i *)
              val i_sa = sym3 (suc aF, iF) sa_i           (* oeq i (Suc a) *)
              val r = disjI1_D2 (oeq iF (suc aF), le iF aF) i_sa
          in Thm.implies_intr (ctermSigD (jT (oeq pF ZeroC))) r end
        val sucAbs = Abs("q", natT, oeq pF (suc (Bound 0)))
        val casePS =
          let val hex = Thm.assume (ctermSigD (jT (mkEx sucAbs)))
              fun body2 qF hq =    (* hq : oeq p (Suc q) *)
                let
                  (* Suc a = i + Suc q [subst p] = Suc(i+q) [add_Suc] -> a = i+q [Suc_inj] -> le i a *)
                  val Pai = Term.lambda (Free("zp2", natT)) (oeq (suc aF)(add iF (Free("zp2",natT))))
                  val saiSq = substPredD (Pai, pF, suc qF) hq hp   (* oeq (Suc a)(add i (Suc q)) *)
                  val aSuc = addSucD (iF, qF)                      (* add i (Suc q) = Suc(add i q) *)
                  val saSuc = trans3 (suc aF, add iF (suc qF), suc (add iF qF)) saiSq aSuc  (* oeq (Suc a)(Suc(add i q)) *)
                  val a_iq = Suc_injD (aF, add iF qF) saSuc        (* oeq a (add i q) *)
                  val lia  = le_introD (iF, aF, qF) a_iq           (* le i a *)
                  val r = disjI2_D2 (oeq iF (suc aF), le iF aF) lia
                in r end
              val res = exE_atD (sucAbs, goalC) hex "q_ls" body2
          in Thm.implies_intr (ctermSigD (jT (mkEx sucAbs))) res end
        val r = disjE_D (oeq pF ZeroC, mkEx sucAbs, goalC) dz caseP0 casePS
      in r end
    val body0 = le_destD (iF, suc aF, goalC) hle "p_ls" body
  in varify (Thm.implies_intr (ctermSigD (jT (le iF (suc aF)))) body0) end;

val () = out ("LE_SPLIT_HYPS = " ^ Int.toString (length (Thm.hyps_of le_split)) ^ "\n");
val () = out "LE_SPLIT_BUILT\n";

(* le i 0 -> oeq i 0 : le i 0 = Ex p. 0 = i + p ; 0 = i+p -> i=0 (add_eq_zero_left). *)
val add_eq_zero_left_vD = varify (up add_eq_zero_left)
fun add_eq_zero_left_D (aT,bT) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("a",0), ctermSigD aT),(("b",0), ctermSigD bT)] add_eq_zero_left_vD)) h
val le_zero_eq =
  let
    val iF = Free("i", natT)
    val hle = Thm.assume (ctermSigD (jT (le iF ZeroC)))
    val goalC = oeq iF ZeroC
    fun body pF hp =    (* hp : oeq 0 (add i p) *)
      let val i0 = add_eq_zero_left_D (iF, pF) (sym3 (ZeroC, add iF pF) hp)   (* oeq i 0 *)
      in i0 end
    val r = le_destD (iF, ZeroC, goalC) hle "p_lz" body
  in varify (Thm.implies_intr (ctermSigD (jT (le iF ZeroC))) r) end;

val () = out "LE_ZERO_EQ_BUILT\n";
val () = out "EP_ASM5A_END\n";
(* ============================================================================
   EUCLID PERFECT ASSEMBLY — Stage 5b: lmem-backward lemmas.
     lmem_2i  : Forall i. Imp (le i a)(lmem (p2 i)(divlist a q))            (induction on a)
     lmem_2iq : Forall i. Imp (le i a)(lmem (mult (p2 i) q)(divlist a q))
   ============================================================================ *)
val () = out "EP_ASM5B_BEGIN\n";

(* leq symmetry : leqL L M ==> leqL M L  (via leq_subst with pred %z. leqL z L + leq_refl) *)
val leq_refl_vD2 = up leq_refl_vBj
fun leq_reflD LT = beta_norm (Drule.infer_instantiate ctxtSigD [(("L",0), ctermSigD LT)] leq_refl_vD2)
fun sym_leqD (LT, MT) hleq =
  let val Pz = Term.lambda (Free("zsl", natlistT)) (leqL (Free("zsl",natlistT)) LT)
      val inst = beta_norm (Drule.infer_instantiate ctxtSigD
            [(("P",0), ctermSigD Pz),(("L",0), ctermSigD LT),(("M",0), ctermSigD MT)] leq_subst_vD)
  in Thm.implies_elim (Thm.implies_elim inst hleq) (leq_reflD LT) end;
(* transport membership across leq : leq L M ==> lmem d L ==> lmem d M *)
fun lmem_leqD (dT, LT, MT) hleq hmem =
  let val Pm = Term.lambda (Free("zml", natlistT)) (lmem dT (Free("zml",natlistT)))
      val inst = beta_norm (Drule.infer_instantiate ctxtSigD
            [(("P",0), ctermSigD Pm),(("L",0), ctermSigD LT),(("M",0), ctermSigD MT)] leq_subst_vD)
  in Thm.implies_elim (Thm.implies_elim inst hleq) hmem end;
(* membership into a cons head : oeq d y ==> lmem d (lcons y t) *)
fun lmem_head (dT, yT, tT) heq =
  let val dj = disjI1_D2 (oeq dT yT, lmem dT tT) heq
  in Thm.implies_elim (lmemConsBwdD2 (dT, yT, tT)) dj end;
(* membership into a cons tail : lmem d t ==> lmem d (lcons y t) *)
fun lmem_tail (dT, yT, tT) hmem =
  let val dj = disjI2_D2 (oeq dT yT, lmem dT tT) hmem
  in Thm.implies_elim (lmemConsBwdD2 (dT, yT, tT)) dj end;
(* le_split as a function : le i (Suc a) ==> Disj (oeq i (Suc a)) (le i a) *)
fun le_splitD (iT, aT) hle =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("i",0), ctermSigD iT),(("a",0), ctermSigD aT)] le_split)
  in Thm.implies_elim inst hle end;
fun le_zero_eqD iT h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD [(("i",0), ctermSigD iT)] le_zero_eq)
  in Thm.implies_elim inst h end;
(* oeq congruence into p2 : oeq i j ==> oeq (p2 i)(p2 j) *)
fun p2_cong (iT, jT_) heq =
  let val Pp = Term.lambda (Free("zpc", natT)) (oeq (p2 iT)(p2 (Free("zpc",natT))))
  in substPredD (Pp, iT, jT_) heq (reflD (p2 iT)) end;
fun p2q_cong (iT, jT_, qT) heq =
  let val Pp = Term.lambda (Free("zpqc", natT)) (oeq (mult (p2 iT) qT)(mult (p2 (Free("zpqc",natT))) qT))
  in substPredD (Pp, iT, jT_) heq (reflD (mult (p2 iT) qT)) end;
(* lmem congruence : oeq x y ==> lmem x L ==> lmem y L *)
fun lmem_cong (xT, yT, LT) heq hmem =
  let val Pm = Term.lambda (Free("zlc", natT)) (lmem (Free("zlc",natT)) LT)
  in substPredD (Pm, xT, yT) heq hmem end;

val () = out "EP_ASM5B_INFRA_OK\n";

(* lmem_2i : Forall i. Imp (le i a)(lmem (p2 i)(divlist a q)) ; induction on a *)
val lmem_2i =
  let
    val qF = Free("q", natT)
    fun mbody at = mkForall (Term.lambda (Free("ii", natT))
                    (mkImp (le (Free("ii",natT)) at)(lmem (p2 (Free("ii",natT))) (divlist at qF))))
    val zA = Free("zA", natT)
    val Qpred = Term.lambda zA (mbody zA)
    val kIndA = Free("a", natT)
    val ind = nat_induct_atD (Qpred, kIndA)
    (* base a=0 : le i 0 -> i=0 -> p2 0 = 1 = head of divlist 0 q. *)
    val base =
      let
        fun perI iF =
          let
            val hle = Thm.assume (ctermSigD (jT (le iF ZeroC)))
            val i0  = le_zero_eqD iF hle          (* oeq i 0 *)
            (* p2 i = p2 0 = 1 *)
            val pii0 = p2_cong (iF, ZeroC) i0     (* oeq (p2 i)(p2 0) *)
            val pz   = powZeroD two               (* p2 0 = 1 *)
            val pi1  = trans3 (p2 iF, p2 ZeroC, one) pii0 pz   (* oeq (p2 i) 1 *)
            (* lmem 1 (divlist 0 q) : divlist 0 q ~ lcons 1 (lcons q lnil) ; head 1. *)
            val hd1  = lmem_head (one, one, lcons qF lnilC) (reflD one)   (* lmem 1 (lcons 1 (lcons q lnil)) *)
            val hleq = sym_leqD (divlist ZeroC qF, lcons one (lcons qF lnilC)) (divlist0D qF)
                       (* leq (lcons 1 (lcons q lnil))(divlist 0 q) -- need symmetric of divlist0D *)
            val mem1 = lmem_leqD (one, lcons one (lcons qF lnilC), divlist ZeroC qF) hleq hd1
                       (* lmem 1 (divlist 0 q) *)
            (* lmem (p2 i)(divlist 0 q) : rewrite 1 -> p2 i (sym pi1) *)
            val memPi = lmem_cong (one, p2 iF, divlist ZeroC qF) (sym3 (p2 iF, one) pi1) mem1
            val body = impI_D (le iF ZeroC, lmem (p2 iF)(divlist ZeroC qF)) memPi
          in body end
        val iFb = Free("i_b", natT)
        val Bpred = Term.lambda (Free("ii",natT))
                      (mkImp (le (Free("ii",natT)) ZeroC)(lmem (p2 (Free("ii",natT)))(divlist ZeroC qF)))
      in allI_D Bpred (Thm.forall_intr (ctermSigD iFb) (perI iFb)) end
    (* step a -> Suc a *)
    val xF = Free("x", natT)
    val IH = Thm.assume (ctermSigD (jT (mbody xF)))
    val stepconcl =
      let
        val A2s = p2 (suc xF)
        val A2sq = mult A2s qF
        fun perI iF =
          let
            val hle = Thm.assume (ctermSigD (jT (le iF (suc xF))))
            val disj = le_splitD (iF, xF) hle    (* Disj (oeq i (Suc x))(le i x) *)
            val goal = lmem (p2 iF)(divlist (suc xF) qF)
            (* case i = Suc x : p2 i = p2 (Suc x) = A2s = head of divlist (Suc x) q *)
            val caseHead =
              let
                val heq = Thm.assume (ctermSigD (jT (oeq iF (suc xF))))
                val piA2s = p2_cong (iF, suc xF) heq    (* oeq (p2 i) A2s *)
                (* head of divlist (Suc x) q *)
                val hdA = lmem_head (A2s, A2s, lcons A2sq (divlist xF qF)) (reflD A2s)
                          (* lmem A2s (lcons A2s (lcons A2sq (divlist x q))) *)
                val hleq = sym_leqD (divlist (suc xF) qF, lcons A2s (lcons A2sq (divlist xF qF))) (divlistSucD (xF,qF))
                val memA = lmem_leqD (A2s, lcons A2s (lcons A2sq (divlist xF qF)), divlist (suc xF) qF) hleq hdA
                val memPi = lmem_cong (A2s, p2 iF, divlist (suc xF) qF) (sym3 (p2 iF, A2s) piA2s) memA
              in Thm.implies_intr (ctermSigD (jT (oeq iF (suc xF)))) memPi end
            (* case le i x : IH gives lmem (p2 i)(divlist x q) ; tail of divlist (Suc x) q (two cons). *)
            val caseTail =
              let
                val hlex = Thm.assume (ctermSigD (jT (le iF xF)))
                val ihPred = Term.lambda (Free("ii",natT))
                              (mkImp (le (Free("ii",natT)) xF)(lmem (p2 (Free("ii",natT)))(divlist xF qF)))
                val ihAt = allE_D (ihPred, iF) IH    (* Imp (le i x)(lmem (p2 i)(divlist x q)) *)
                val memx = mp_D (le iF xF, lmem (p2 iF)(divlist xF qF)) ihAt hlex  (* lmem (p2 i)(divlist x q) *)
                (* lmem (p2 i)(lcons A2sq (divlist x q)) [tail] then (lcons A2s ...) [tail] *)
                val mem1 = lmem_tail (p2 iF, A2sq, divlist xF qF) memx   (* lmem (p2 i)(lcons A2sq (divlist x q)) *)
                val mem2 = lmem_tail (p2 iF, A2s, lcons A2sq (divlist xF qF)) mem1  (* lmem (p2 i)(lcons A2s (lcons A2sq (divlist x q))) *)
                val hleq = sym_leqD (divlist (suc xF) qF, lcons A2s (lcons A2sq (divlist xF qF))) (divlistSucD (xF,qF))
                val memPi = lmem_leqD (p2 iF, lcons A2s (lcons A2sq (divlist xF qF)), divlist (suc xF) qF) hleq mem2
              in Thm.implies_intr (ctermSigD (jT (le iF xF))) memPi end
            val res = disjE_D (oeq iF (suc xF), le iF xF, goal) disj caseHead caseTail
          in impI_D (le iF (suc xF), goal) res end
        val iFs = Free("i_s", natT)
        val Spred = Term.lambda (Free("ii",natT))
                      (mkImp (le (Free("ii",natT)) (suc xF))(lmem (p2 (Free("ii",natT)))(divlist (suc xF) qF)))
      in allI_D Spred (Thm.forall_intr (ctermSigD iFs) (perI iFs)) end
    val step1 = Thm.forall_intr (ctermSigD xF) (Thm.implies_intr (ctermSigD (jT (mbody xF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in varify r2 end;

val () = out ("LMEM_2I_HYPS = " ^ Int.toString (length (Thm.hyps_of lmem_2i)) ^ "\n");
val () = out "LMEM_2I_BUILT\n";
val () = out "EP_ASM5B_END\n";

(* lmem_2iq : Forall i. Imp (le i a)(lmem (mult (p2 i) q)(divlist a q)) ; induction on a *)
val () = out "EP_ASM5BQ_BEGIN\n";
val lmem_2iq =
  let
    val qF = Free("q", natT)
    fun mbody at = mkForall (Term.lambda (Free("ii", natT))
                    (mkImp (le (Free("ii",natT)) at)(lmem (mult (p2 (Free("ii",natT))) qF) (divlist at qF))))
    val zA = Free("zA", natT)
    val Qpred = Term.lambda zA (mbody zA)
    val kIndA = Free("a", natT)
    val ind = nat_induct_atD (Qpred, kIndA)
    (* base a=0 : le i 0 -> i=0 -> mult (p2 0) q = mult 1 q = q = 2nd elem of divlist 0 q. *)
    val base =
      let
        fun perI iF =
          let
            val hle = Thm.assume (ctermSigD (jT (le iF ZeroC)))
            val i0  = le_zero_eqD iF hle          (* oeq i 0 *)
            val piq = p2q_cong (iF, ZeroC, qF) i0  (* oeq (mult (p2 i) q)(mult (p2 0) q) *)
            val pz  = powZeroD two                  (* p2 0 = 1 *)
            (* mult (p2 0) q = mult 1 q = q *)
            val m10 = mult_cong_lD (p2 ZeroC, one, qF) pz   (* mult (p2 0) q = mult 1 q *)
            val m1q = trans3 (mult one qF, mult qF one, qF) (multcommD (one, qF)) (mult1rD qF)  (* mult 1 q = q *)
            val piq_q = trans3 (mult (p2 iF) qF, mult (p2 ZeroC) qF, mult one qF) piq m10  (* mult (p2 i) q = mult 1 q *)
            val piq_qq = trans3 (mult (p2 iF) qF, mult one qF, qF) piq_q m1q   (* mult (p2 i) q = q *)
            (* lmem q (divlist 0 q) : 2nd elem ; divlist 0 q ~ lcons 1 (lcons q lnil). lmem q via tail+head. *)
            val hdq = lmem_head (qF, qF, lnilC) (reflD qF)             (* lmem q (lcons q lnil) *)
            val mqc = lmem_tail (qF, one, lcons qF lnilC) hdq           (* lmem q (lcons 1 (lcons q lnil)) *)
            val hleq = sym_leqD (divlist ZeroC qF, lcons one (lcons qF lnilC)) (divlist0D qF)
            val memq = lmem_leqD (qF, lcons one (lcons qF lnilC), divlist ZeroC qF) hleq mqc  (* lmem q (divlist 0 q) *)
            val memPiq = lmem_cong (qF, mult (p2 iF) qF, divlist ZeroC qF) (sym3 (mult (p2 iF) qF, qF) piq_qq) memq
            val body = impI_D (le iF ZeroC, lmem (mult (p2 iF) qF)(divlist ZeroC qF)) memPiq
          in body end
        val iFb = Free("i_b", natT)
        val Bpred = Term.lambda (Free("ii",natT))
                      (mkImp (le (Free("ii",natT)) ZeroC)(lmem (mult (p2 (Free("ii",natT))) qF)(divlist ZeroC qF)))
      in allI_D Bpred (Thm.forall_intr (ctermSigD iFb) (perI iFb)) end
    val xF = Free("x", natT)
    val IH = Thm.assume (ctermSigD (jT (mbody xF)))
    val stepconcl =
      let
        val A2s = p2 (suc xF)
        val A2sq = mult A2s qF
        fun perI iF =
          let
            val hle = Thm.assume (ctermSigD (jT (le iF (suc xF))))
            val disj = le_splitD (iF, xF) hle
            val goal = lmem (mult (p2 iF) qF)(divlist (suc xF) qF)
            (* case i = Suc x : mult (p2 i) q = mult (p2 (Suc x)) q = A2sq = 2nd elem. *)
            val caseHead =
              let
                val heq = Thm.assume (ctermSigD (jT (oeq iF (suc xF))))
                val piA2sq = p2q_cong (iF, suc xF, qF) heq   (* oeq (mult (p2 i) q) A2sq *)
                (* A2sq is head of (lcons A2sq (divlist x q)) which is tail of (lcons A2s ...) *)
                val hdA = lmem_head (A2sq, A2sq, divlist xF qF) (reflD A2sq)      (* lmem A2sq (lcons A2sq (divlist x q)) *)
                val tlA = lmem_tail (A2sq, A2s, lcons A2sq (divlist xF qF)) hdA    (* lmem A2sq (lcons A2s (lcons A2sq (divlist x q))) *)
                val hleq = sym_leqD (divlist (suc xF) qF, lcons A2s (lcons A2sq (divlist xF qF))) (divlistSucD (xF,qF))
                val memA = lmem_leqD (A2sq, lcons A2s (lcons A2sq (divlist xF qF)), divlist (suc xF) qF) hleq tlA
                val memPiq = lmem_cong (A2sq, mult (p2 iF) qF, divlist (suc xF) qF) (sym3 (mult (p2 iF) qF, A2sq) piA2sq) memA
              in Thm.implies_intr (ctermSigD (jT (oeq iF (suc xF)))) memPiq end
            val caseTail =
              let
                val hlex = Thm.assume (ctermSigD (jT (le iF xF)))
                val ihPred = Term.lambda (Free("ii",natT))
                              (mkImp (le (Free("ii",natT)) xF)(lmem (mult (p2 (Free("ii",natT))) qF)(divlist xF qF)))
                val ihAt = allE_D (ihPred, iF) IH
                val memx = mp_D (le iF xF, lmem (mult (p2 iF) qF)(divlist xF qF)) ihAt hlex  (* lmem (mult (p2 i) q)(divlist x q) *)
                val mem1 = lmem_tail (mult (p2 iF) qF, A2sq, divlist xF qF) memx
                val mem2 = lmem_tail (mult (p2 iF) qF, A2s, lcons A2sq (divlist xF qF)) mem1
                val hleq = sym_leqD (divlist (suc xF) qF, lcons A2s (lcons A2sq (divlist xF qF))) (divlistSucD (xF,qF))
                val memPiq = lmem_leqD (mult (p2 iF) qF, lcons A2s (lcons A2sq (divlist xF qF)), divlist (suc xF) qF) hleq mem2
              in Thm.implies_intr (ctermSigD (jT (le iF xF))) memPiq end
            val res = disjE_D (oeq iF (suc xF), le iF xF, goal) disj caseHead caseTail
          in impI_D (le iF (suc xF), goal) res end
        val iFs = Free("i_s", natT)
        val Spred = Term.lambda (Free("ii",natT))
                      (mkImp (le (Free("ii",natT)) (suc xF))(lmem (mult (p2 (Free("ii",natT))) qF)(divlist (suc xF) qF)))
      in allI_D Spred (Thm.forall_intr (ctermSigD iFs) (perI iFs)) end
    val step1 = Thm.forall_intr (ctermSigD xF) (Thm.implies_intr (ctermSigD (jT (mbody xF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
  in varify r2 end;
val () = out ("LMEM_2IQ_HYPS = " ^ Int.toString (length (Thm.hyps_of lmem_2iq)) ^ "\n");
val () = out "LMEM_2IQ_BUILT\n";
val () = out "EP_ASM5BQ_END\n";
(* ============================================================================
   EUCLID PERFECT ASSEMBLY — Stage 6: lnodup (divlist a q).
   Uses the PARITY argument (q odd) via member_dvd, not pow strict-mono.
     notmem_A2s  : prime2 q ==> neg(dvd 2 q) ==> neg(lmem (p2 (Suc a))(divlist a q))
     notmem_A2sq : prime2 q ==> neg(dvd 2 q) ==> neg(lmem (mult (p2 (Suc a)) q)(divlist a q))
     A2s_neq_A2sq: prime2 q ==> neg(oeq (p2 (Suc a))(mult (p2 (Suc a)) q))
     lnodup_divlist : prime2 q ==> neg(dvd 2 q) ==> lnodup (divlist a q)   [induction on a]
   ============================================================================ *)
val () = out "EP_ASM6_BEGIN\n";

(* conjI on ctxtSigD *)
fun conjI_Sg2 (At, Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("A",0), ctermSigD At),(("B",0), ctermSigD Bt)] conjI_vD)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end
val sym_leqD2 = sym_leqD
(* dvd intro on ctxtSigD : oeq n (mult d k) ==> dvd d n  (witness k) *)
fun dvd_introD (dT, nT, kT) heq =
  let val wAbs = Abs("k", natT, oeq nT (mult dT (Bound 0)))
  in exI_atD2 (wAbs, kT) heq end
(* dvd dest : dvd d n ==> expose witness k with n = d*k *)
fun dvd_destD (dT, nT, goalT) hdvd wnm body =
  let val Pabs = Abs("k", natT, oeq nT (mult dT (Bound 0)))
  in exE_atD (Pabs, goalT) hdvd wnm body end
(* lt 0 c  i.e. le 1 c  from Ex m. c = Suc m : witness m, c = 1 + m *)
val mult_left_cancel_vD = up mult_left_cancel
fun mult_left_cancel_D (cT,aT,bT) hPos hEq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("c",0), ctermSigD cT),(("a",0), ctermSigD aT),(("b",0), ctermSigD bT)] mult_left_cancel_vD)
  in Thm.implies_elim (Thm.implies_elim inst hPos) hEq end;

(* lt 0 c = le 1 c = Ex p. c = add 1 p.  From Ex m. c = Suc m : witness m, c = add 1 m. *)
(* add 1 m = Suc(add 0 m) = Suc m ; so c = Suc m -> c = add 1 m via add_Suc + add_0. *)
val add_Suc_vD2 = varify (up add_Suc)   (* add (Suc m) n = Suc(add m n) -- here add (Suc 0) m *)
fun lt0_of_suc (cT, mT) hcSm =   (* hcSm : oeq c (Suc m)  ->  lt 0 c *)
  let
    (* add 1 m = add (Suc 0) m = Suc(add 0 m) [add_Suc] = Suc m [add_0 cong] *)
    val a1m = beta_norm (Drule.infer_instantiate ctxtSigD
                [(("m",0), ctermSigD ZeroC),(("n",0), ctermSigD mT)] add_Suc_vD2)   (* add (Suc 0) m = Suc(add 0 m) *)
    val a0m = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD mT)] add_0_vD)  (* add 0 m = m *)
    val sucCong = beta_norm (Drule.infer_instantiate ctxtSigD
                    [(("a",0), ctermSigD (add ZeroC mT)),(("b",0), ctermSigD mT)] (up (varify Suc_cong)))
    val sucEq = Thm.implies_elim sucCong a0m   (* Suc(add 0 m) = Suc m *)
    val a1m_sm = trans3 (add (suc ZeroC) mT, suc (add ZeroC mT), suc mT) a1m sucEq  (* add 1 m = Suc m *)
    (* c = Suc m = add 1 m : c = Suc m [hcSm], Suc m = add 1 m [sym a1m_sm] *)
    val c_a1m = trans3 (cT, suc mT, add (suc ZeroC) mT) hcSm (sym3 (add (suc ZeroC) mT, suc mT) a1m_sm)  (* oeq c (add 1 m) *)
    (* lt 0 c = le (Suc 0) c = Ex p. c = add (Suc 0) p ; witness m *)
    val wAbs = Abs("p", natT, oeq cT (add (suc ZeroC) (Bound 0)))
  in exI_atD2 (wAbs, mT) c_a1m end

val () = out "EP_ASM6_INFRA_OK\n";

(* lt 0 (p2 a) : from pow2_pos (Ex m. p2 a = Suc m) *)
fun lt0_p2 aT =
  let
    val pp = beta_norm (Drule.infer_instantiate ctxtSigD [(("k",0), ctermSigD aT)] pow2_pos_vD)  (* Ex m. p2 a = Suc m *)
    val exAbs = Abs("m", natT, oeq (p2 aT)(suc (Bound 0)))
    fun body mF hm = lt0_of_suc (p2 aT, mF) hm
  in exE_atD (exAbs, lt ZeroC (p2 aT)) pp "m_lp" body end
(* lt 0 q : prime2 q -> gt1 -> Ex p. q = add 2 p = Suc(...) ; then lt0_of_suc *)
fun lt0_q (qT, hPrime) =
  let
    val gt1 = conjunct1_D (lt (suc ZeroC) qT, mkForall (ppAbs qT)) hPrime  (* Ex p. q = add (Suc(Suc 0)) p *)
    val exAbs = Abs("p", natT, oeq qT (add (suc (suc ZeroC)) (Bound 0)))
    fun body pF hp =   (* hp : oeq q (add (Suc(Suc 0)) p) *)
      let
        (* add (Suc(Suc 0)) p = Suc(add (Suc 0) p) [add_Suc] ; so q = Suc(...) *)
        val asuc = beta_norm (Drule.infer_instantiate ctxtSigD
              [(("m",0), ctermSigD (suc ZeroC)),(("n",0), ctermSigD pF)] add_Suc_vD2)  (* add (Suc 0) p... wait need add (Suc(Suc 0)) p *)
        val asuc2 = beta_norm (Drule.infer_instantiate ctxtSigD
              [(("m",0), ctermSigD (suc ZeroC)),(("n",0), ctermSigD pF)] add_Suc_vD2)
        (* add (Suc(Suc 0)) p : here Suc(Suc 0) = Suc(Suc 0), m = Suc 0.  add (Suc(Suc 0)) p = Suc(add (Suc 0) p) *)
        val aS = beta_norm (Drule.infer_instantiate ctxtSigD
              [(("m",0), ctermSigD (suc ZeroC)),(("n",0), ctermSigD pF)] add_Suc_vD2)  (* add (Suc(Suc 0)) p = Suc(add (Suc 0) p) *)
        val qSuc = trans3 (qT, add (suc (suc ZeroC)) pF, suc (add (suc ZeroC) pF)) hp aS  (* q = Suc(add (Suc 0) p) *)
      in lt0_of_suc (qT, add (suc ZeroC) pF) qSuc end
  in exE_atD (exAbs, lt ZeroC qT) gt1 "p_lq" body end

val () = out "EP_ASM6_LT0_OK\n";

(* dvd_cancel_left : lt 0 c ==> dvd (mult c x)(mult c y) ==> dvd x y *)
fun dvd_cancel_left (cT, xT, yT) hPos hdvd =
  dvd_destD (mult cT xT, mult cT yT, dvd xT yT) hdvd "k_dcl"
    (fn kF => fn hk =>   (* hk : oeq (mult c y)(mult (mult c x) k) *)
      let
        (* mult (mult c x) k = mult c (mult x k) [assoc] *)
        val assoc = multassocD (cT, xT, kF)        (* mult (mult c x) k = mult c (mult x k) *)
        val cy_cxk = trans3 (mult cT yT, mult (mult cT xT) kF, mult cT (mult xT kF)) hk assoc  (* mult c y = mult c (mult x k) *)
        val y_xk = mult_left_cancel_D (cT, yT, mult xT kF) hPos cy_cxk   (* oeq y (mult x k) *)
      in dvd_introD (xT, yT, kF) y_xk end)

val () = out "EP_ASM6_CANCEL_OK\n";

(* parity refutation : neg(dvd 2 q) [object Imp] ; dvd 2 q ==> oFalse  via mp_D *)
fun odd_refute (qT, hOdd) hdvd2q = mp_D (dvd two qT, oFalseC) hOdd hdvd2q

(* pow_Suc as p2(Suc a) = mult 2 (p2 a) ; also = mult (p2 a) 2 (comm) *)
fun p2suc_as_mult aT =
  let val ps = powSucD (two, aT)              (* p2(Suc a) = mult 2 (p2 a) *)
      val cm = multcommD (two, p2 aT)         (* mult 2 (p2 a) = mult (p2 a) 2 *)
  in trans3 (p2 (suc aT), mult two (p2 aT), mult (p2 aT) two) ps cm end  (* p2(Suc a) = mult (p2 a) 2 *)

(* refute oeq (Suc 0)(mult 2 k) : k=0 -> mult 2 0 = 0 -> Suc 0 = 0 (Suc_neq_Zero);
   k=Suc k' -> mult 2 (Suc k') = add (Suc k')(mult 1 (Suc k')) ... = Suc(Suc(..)) ; Suc 0 = Suc(Suc ..) -> Suc_inj -> 0 = Suc(..) -> Suc_neq_Zero. *)
val mult_0_right_vD2 = varify (up mult_0_right)
fun mult0rD t = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD t)] mult_0_right_vD2)
val mult_Suc_right_vD2 = varify (up mult_Suc_right)
fun multSrD (n,m) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("n",0), ctermSigD n),(("m",0), ctermSigD m)] mult_Suc_right_vD2)   (* mult n (Suc m) = add n (mult n m) *)
val one_neq_2k =
  let
    val kF = Free("k", natT)
    val hyp = Thm.assume (ctermSigD (jT (oeq one (mult two kF))))   (* Suc 0 = mult 2 k *)
    val dz = dzosD kF    (* Disj (oeq k 0)(Ex j. k = Suc j) *)
    val caseK0 =
      let val hk0 = Thm.assume (ctermSigD (jT (oeq kF ZeroC)))
          val m20 = mult0rD two           (* mult 2 0 = 0 *)
          (* mult 2 k = mult 2 0 [cong] = 0 *)
          val cong = mult_cong_rD (two, kF, ZeroC) hk0   (* mult 2 k = mult 2 0 *)
          val m2k0 = trans3 (mult two kF, mult two ZeroC, ZeroC) cong m20  (* mult 2 k = 0 *)
          val s00  = trans3 (one, mult two kF, ZeroC) hyp m2k0  (* Suc 0 = 0 *)
          val snz = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD ZeroC)] Suc_neq_Zero_vD)
      in Thm.implies_intr (ctermSigD (jT (oeq kF ZeroC))) (Thm.implies_elim snz s00) end
    val sucAbs = Abs("j", natT, oeq kF (suc (Bound 0)))
    val caseKS =
      let val hex = Thm.assume (ctermSigD (jT (mkEx sucAbs)))
          fun body jF hj =   (* hj : oeq k (Suc j) *)
            let
              (* mult 2 k = mult 2 (Suc j) = add 2 (mult 2 j) [mult_Suc_right] = Suc(Suc(mult 2 j)) *)
              val cong = mult_cong_rD (two, kF, suc jF) hj   (* mult 2 k = mult 2 (Suc j) *)
              val msr  = multSrD (two, jF)                   (* mult 2 (Suc j) = add 2 (mult 2 j) *)
              (* add 2 (mult 2 j) = add (Suc(Suc 0))(mult 2 j) = Suc(add (Suc 0)(mult 2 j)) [add_Suc] = Suc(Suc(add 0 (mult 2 j))) *)
              val aS1 = beta_norm (Drule.infer_instantiate ctxtSigD
                          [(("m",0), ctermSigD (suc ZeroC)),(("n",0), ctermSigD (mult two jF))] add_Suc_vD2)  (* add (Suc(Suc 0))(m2j) = Suc(add (Suc 0)(m2j)) *)
              val aS2 = beta_norm (Drule.infer_instantiate ctxtSigD
                          [(("m",0), ctermSigD ZeroC),(("n",0), ctermSigD (mult two jF))] add_Suc_vD2)  (* add (Suc 0)(m2j) = Suc(add 0 (m2j)) *)
              (* chain mult 2 k = Suc(add (Suc 0)(mult 2 j)) *)
              val m2k_eq = trans3 (mult two kF, mult two (suc jF), add two (mult two jF)) cong msr  (* mult 2 k = add 2 (mult 2 j) *)
              val m2k_S  = trans3 (mult two kF, add two (mult two jF), suc (add (suc ZeroC)(mult two jF))) m2k_eq aS1  (* mult 2 k = Suc(add (Suc 0)(mult 2 j)) *)
              (* Suc 0 = Suc(add (Suc 0)(mult 2 j)) [hyp + m2k_S] -> Suc_inj -> 0 = add (Suc 0)(mult 2 j) = Suc(...) *)
              val s_eq = trans3 (one, mult two kF, suc (add (suc ZeroC)(mult two jF))) hyp m2k_S  (* Suc 0 = Suc(add (Suc 0)(mult 2 j)) *)
              val inj  = Suc_injD (ZeroC, add (suc ZeroC)(mult two jF)) s_eq   (* 0 = add (Suc 0)(mult 2 j) *)
              (* add (Suc 0)(mult 2 j) = Suc(add 0 (mult 2 j)) -> 0 = Suc(...) -> Suc_neq_Zero *)
              val zSuc = trans3 (ZeroC, add (suc ZeroC)(mult two jF), suc (add ZeroC (mult two jF))) inj aS2  (* 0 = Suc(add 0 (m2j)) *)
              val snz = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD (add ZeroC (mult two jF)))] Suc_neq_Zero_vD)
            in Thm.implies_elim snz (sym3 (ZeroC, suc (add ZeroC (mult two jF))) zSuc) end
          val res = exE_atD (sucAbs, oFalseC) hex "j_o2k" body
      in Thm.implies_intr (ctermSigD (jT (mkEx sucAbs))) res end
    val ff = disjE_D (oeq kF ZeroC, mkEx sucAbs, oFalseC) dz caseK0 caseKS
  in Thm.implies_intr (ctermSigD (jT (oeq one (mult two kF)))) ff end;   (* oeq 1 (mult 2 k) ==> oFalse, for the Free k *)

val () = out "EP_ASM6_INFRA2_OK\n";

(* one_neq_2k as a function: oeq 1 (mult 2 k) -> oFalse *)
val one_neq_2k_v = varify one_neq_2k
fun one_neq_2k_at kT h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD [(("k",0), ctermSigD kT)] one_neq_2k_v)
  in Thm.implies_elim inst h end

(* dvd (mult 2 q) q -> oFalse  (q>0) : q = (2q)*k = q*(2k) -> cancel q -> 1 = 2k -> one_neq_2k *)
fun dvd_2q_q_absurd (qT, hq_pos) hdvd =
  dvd_destD (mult two qT, qT, oFalseC) hdvd "k_2q"
    (fn kF => fn hk =>   (* hk : oeq q (mult (mult 2 q) k) *)
      let
        (* mult (mult 2 q) k = mult (mult q 2) k [comm] = mult q (mult 2 k) [assoc] *)
        val cm = mult_cong_lD (mult two qT, mult qT two, kF) (multcommD (two, qT))   (* mult (mult 2 q) k = mult (mult q 2) k *)
        val asc = multassocD (qT, two, kF)                                           (* mult (mult q 2) k = mult q (mult 2 k) *)
        val rhs = trans3 (mult (mult two qT) kF, mult (mult qT two) kF, mult qT (mult two kF)) cm asc
        val q_qm = trans3 (qT, mult (mult two qT) kF, mult qT (mult two kF)) hk rhs  (* q = mult q (mult 2 k) *)
        (* q = q*1 [mult_1_right sym] ; so mult q 1 = mult q (mult 2 k) -> cancel q -> 1 = mult 2 k *)
        val q1 = sym3 (mult qT one, qT) (mult1rD qT)    (* oeq q (mult q 1) *)
        val q1_qm = trans3 (mult qT one, qT, mult qT (mult two kF)) (mult1rD qT) q_qm  (* mult q 1 = mult q (mult 2 k) *)
        val one_2k = mult_left_cancel_D (qT, one, mult two kF) hq_pos q1_qm   (* oeq 1 (mult 2 k) *)
      in one_neq_2k_at kF one_2k end)

val () = out "EP_ASM6_2QABSURD_OK\n";

(* notmem_A2s : prime2 q ==> neg(dvd 2 q) ==> neg(lmem (p2 (Suc a))(divlist a q)) *)
val notmem_A2s =
  let
    val aF = Free("a", natT); val qF = Free("q", natT)
    val hPrime = Thm.assume (ctermSigD (jT (prime2 qF)))
    val hOdd   = Thm.assume (ctermSigD (jT (neg (dvd two qF))))
    val A2s = p2 (suc aF)
    val N = mult (p2 aF) qF
    val hmem = Thm.assume (ctermSigD (jT (lmem A2s (divlist aF qF))))
    (* member_dvd : dvd A2s N *)
    val mdAll = beta_norm (Drule.infer_instantiate ctxtSigD
                  [(("a",0), ctermSigD aF),(("q",0), ctermSigD qF)] member_dvd)
    val mdPred = Term.lambda (Free("dmd",natT))
                  (mkImp (lmem (Free("dmd",natT)) (divlist aF qF))(dvd (Free("dmd",natT)) N))
    val mdAt = allE_D (mdPred, A2s) mdAll
    val dvdA2sN = mp_D (lmem A2s (divlist aF qF), dvd A2s N) mdAt hmem   (* dvd A2s N *)
    (* A2s = mult (p2 a) 2 ; rewrite divisor -> dvd (mult (p2 a) 2) N *)
    val A2s_eq = p2suc_as_mult aF    (* p2(Suc a) = mult (p2 a) 2 *)
    val dvd2 = dvd_cong_divisor_D (A2s, mult (p2 aF) two, N) A2s_eq dvdA2sN  (* dvd (mult (p2 a) 2) N = dvd (mult (p2 a) 2)(mult (p2 a) q) *)
    (* dvd_cancel_left (p2 a, 2, q) : dvd 2 q *)
    val dvd2q = dvd_cancel_left (p2 aF, two, qF) (lt0_p2 aF) dvd2   (* dvd 2 q *)
    val ff = odd_refute (qF, hOdd) dvd2q
    val negThm = impI_D (lmem A2s (divlist aF qF), oFalseC) ff
    val d2 = Thm.implies_intr (ctermSigD (jT (neg (dvd two qF)))) negThm
    val d3 = Thm.implies_intr (ctermSigD (jT (prime2 qF))) d2
  in varify d3 end;

val () = out ("NOTMEM_A2S_HYPS = " ^ Int.toString (length (Thm.hyps_of notmem_A2s)) ^ "\n");
val () = out "NOTMEM_A2S_BUILT\n";

(* notmem_A2sq : prime2 q ==> neg(dvd 2 q) ==> neg(lmem (mult (p2 (Suc a)) q)(divlist a q)) *)
val notmem_A2sq =
  let
    val aF = Free("a", natT); val qF = Free("q", natT)
    val hPrime = Thm.assume (ctermSigD (jT (prime2 qF)))
    val hOdd   = Thm.assume (ctermSigD (jT (neg (dvd two qF))))
    val A2sq = mult (p2 (suc aF)) qF
    val N = mult (p2 aF) qF
    val hmem = Thm.assume (ctermSigD (jT (lmem A2sq (divlist aF qF))))
    val mdAll = beta_norm (Drule.infer_instantiate ctxtSigD
                  [(("a",0), ctermSigD aF),(("q",0), ctermSigD qF)] member_dvd)
    val mdPred = Term.lambda (Free("dmd",natT))
                  (mkImp (lmem (Free("dmd",natT)) (divlist aF qF))(dvd (Free("dmd",natT)) N))
    val mdAt = allE_D (mdPred, A2sq) mdAll
    val dvdA2sqN = mp_D (lmem A2sq (divlist aF qF), dvd A2sq N) mdAt hmem   (* dvd A2sq N *)
    (* A2sq = mult (p2(Suc a)) q = mult (mult (p2 a) 2) q = mult (p2 a)(mult 2 q) [assoc] *)
    val A2s_eq = p2suc_as_mult aF                              (* p2(Suc a) = mult (p2 a) 2 *)
    val A2sq_cong = mult_cong_lD (p2 (suc aF), mult (p2 aF) two, qF) A2s_eq  (* A2sq = mult (mult (p2 a) 2) q *)
    val A2sq_assoc = multassocD (p2 aF, two, qF)               (* mult (mult (p2 a) 2) q = mult (p2 a)(mult 2 q) *)
    val A2sq_eq = trans3 (A2sq, mult (mult (p2 aF) two) qF, mult (p2 aF)(mult two qF)) A2sq_cong A2sq_assoc
    val dvd2 = dvd_cong_divisor_D (A2sq, mult (p2 aF)(mult two qF), N) A2sq_eq dvdA2sqN
               (* dvd (mult (p2 a)(mult 2 q))(mult (p2 a) q) *)
    val dvd2qq = dvd_cancel_left (p2 aF, mult two qF, qF) (lt0_p2 aF) dvd2   (* dvd (mult 2 q) q *)
    val ff = dvd_2q_q_absurd (qF, lt0_q (qF, hPrime)) dvd2qq
    val negThm = impI_D (lmem A2sq (divlist aF qF), oFalseC) ff
    val d2 = Thm.implies_intr (ctermSigD (jT (neg (dvd two qF)))) negThm
    val d3 = Thm.implies_intr (ctermSigD (jT (prime2 qF))) d2
  in varify d3 end;

val () = out ("NOTMEM_A2SQ_HYPS = " ^ Int.toString (length (Thm.hyps_of notmem_A2sq)) ^ "\n");
val () = out "NOTMEM_A2SQ_BUILT\n";
val () = out "EP_ASM6_NOTMEM_OK\n";

(* neg(oeq 1 q) from prime2 q : lt 1 q = Ex p. q = add 2 p ; q=1 -> Suc 0 = Suc(Suc p) -> Suc_inj -> 0 = Suc p. *)
fun one_neq_q (qF, hPrime) =
  let
    val hyp = Thm.assume (ctermSigD (jT (oeq one qF)))   (* 1 = q *)
    val gt1 = conjunct1_D (lt (suc ZeroC) qF, mkForall (ppAbs qF)) hPrime  (* Ex p. q = add (Suc(Suc 0)) p *)
    val exAbs = Abs("p", natT, oeq qF (add (suc (suc ZeroC)) (Bound 0)))
    fun body pF hp =   (* q = add (Suc(Suc 0)) p *)
      let
        val aS = beta_norm (Drule.infer_instantiate ctxtSigD
              [(("m",0), ctermSigD (suc ZeroC)),(("n",0), ctermSigD pF)] add_Suc_vD2)  (* add (Suc(Suc 0)) p = Suc(add (Suc 0) p) *)
        val qSuc = trans3 (qF, add (suc (suc ZeroC)) pF, suc (add (suc ZeroC) pF)) hp aS  (* q = Suc(add (Suc 0) p) *)
        (* 1 = q = Suc(add (Suc 0) p) ; 1 = Suc 0 -> Suc 0 = Suc(add (Suc 0) p) -> Suc_inj -> 0 = add (Suc 0) p = Suc(...) *)
        val one_qS = trans3 (one, qF, suc (add (suc ZeroC) pF)) hyp qSuc  (* Suc 0 = Suc(add (Suc 0) p) *)
        val inj = Suc_injD (ZeroC, add (suc ZeroC) pF) one_qS   (* 0 = add (Suc 0) p *)
        val aS2 = beta_norm (Drule.infer_instantiate ctxtSigD
              [(("m",0), ctermSigD ZeroC),(("n",0), ctermSigD pF)] add_Suc_vD2)  (* add (Suc 0) p = Suc(add 0 p) *)
        val zSuc = trans3 (ZeroC, add (suc ZeroC) pF, suc (add ZeroC pF)) inj aS2  (* 0 = Suc(add 0 p) *)
        val snz = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD (add ZeroC pF))] Suc_neq_Zero_vD)
      in Thm.implies_elim snz (sym3 (ZeroC, suc (add ZeroC pF)) zSuc) end
    val ff = exE_atD (exAbs, oFalseC) gt1 "p_1nq" body
  in impI_D (oeq one qF, oFalseC) ff end

(* A2s_neq_A2sq : prime2 q ==> neg(oeq (p2 (Suc a))(mult (p2 (Suc a)) q))
   Assume oeq A2s (A2s*q).  A2s = A2s*1 [mult_1_right sym] -> A2s*1 = A2s*q -> cancel A2s -> 1 = q -> contra. *)
val A2s_neq_A2sq =
  let
    val aF = Free("a", natT); val qF = Free("q", natT)
    val hPrime = Thm.assume (ctermSigD (jT (prime2 qF)))
    val A2s = p2 (suc aF)
    val heq = Thm.assume (ctermSigD (jT (oeq A2s (mult A2s qF))))   (* A2s = A2s*q *)
    (* A2s*1 = A2s [mult_1_right] ; A2s = A2s*q [heq] ; so A2s*1 = A2s*q *)
    val a1 = mult1rD A2s    (* mult A2s 1 = A2s *)
    val a1q = trans3 (mult A2s one, A2s, mult A2s qF) a1 heq  (* mult A2s 1 = mult A2s q *)
    val oneq = mult_left_cancel_D (A2s, one, qF) (lt0_p2 (suc aF)) a1q   (* oeq 1 q *)
    val negThm = impI_D (oeq A2s (mult A2s qF), oFalseC)
                   (mp_D (oeq one qF, oFalseC) (one_neq_q (qF, hPrime)) oneq)
    val d3 = Thm.implies_intr (ctermSigD (jT (prime2 qF))) negThm
  in varify d3 end;

val () = out "EP_ASM6_A2SNEQ_OK\n";

(* lnodup_divlist : prime2 q ==> neg(dvd 2 q) ==> lnodup (divlist a q)  ; induction on a *)
val lnodup_cons_bwd_vD2 = up lnodup_cons_bwd_vBj
fun lnodup_cons_bwdD (xT, tT) hConj =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
      [(("x",0), ctermSigD xT),(("t",0), ctermSigD tT)] lnodup_cons_bwd_vD2)) hConj
val lnodup_nil_vD2 = up lnodup_nil_vBj

val lnodup_divlist =
  let
    val qF = Free("q", natT)
    val hPrime = Thm.assume (ctermSigD (jT (prime2 qF)))
    val hOdd   = Thm.assume (ctermSigD (jT (neg (dvd two qF))))
    fun ndBody at = lnodup (divlist at qF)
    val zA = Free("zA", natT)
    val Qpred = Term.lambda zA (ndBody zA)
    val kIndA = Free("a", natT)
    val ind = nat_induct_atD (Qpred, kIndA)
    (* base a=0 : divlist 0 q ~ lcons 1 (lcons q lnil).  lnodup needs distinctness 1<>q + q not in nil.
       Prove lnodup (lcons 1 (lcons q lnil)) then transport via leq.
       lnodup (lcons q lnil) : neg(lmem q lnil) [lmem_nil_elim] /\ lnodup lnil.
       lnodup (lcons 1 (lcons q lnil)) : neg(lmem 1 (lcons q lnil)) /\ lnodup(lcons q lnil).
         neg(lmem 1 (lcons q lnil)) : lmem 1 (lcons q lnil) -> Disj(oeq 1 q)(lmem 1 lnil).
           oeq 1 q -> contra (one_neq_q) ; lmem 1 lnil -> absurd. *)
    val base =
      let
        (* lnodup (lcons q lnil) *)
        val negqnil = impI_D (lmem qF lnilC, oFalseC) (Thm.implies_elim (lmemNilElimD qF) (Thm.assume (ctermSigD (jT (lmem qF lnilC)))))
        val ndqnil = lnodup_cons_bwdD (qF, lnilC) (conjI_Sg2 (neg (lmem qF lnilC), lnodup lnilC) negqnil lnodup_nil_vD2)
        (* neg(lmem 1 (lcons q lnil)) *)
        val neg1qnil =
          let
            val hm = Thm.assume (ctermSigD (jT (lmem one (lcons qF lnilC))))
            val dj = Thm.implies_elim (lmemConsFwdD (one, qF, lnilC)) hm   (* Disj(oeq 1 q)(lmem 1 lnil) *)
            val caseEq =
              let val heq = Thm.assume (ctermSigD (jT (oeq one qF)))
              in Thm.implies_intr (ctermSigD (jT (oeq one qF))) (mp_D (oeq one qF, oFalseC) (one_neq_q (qF, hPrime)) heq) end
            val caseNil =
              let val hn = Thm.assume (ctermSigD (jT (lmem one lnilC)))
              in Thm.implies_intr (ctermSigD (jT (lmem one lnilC))) (Thm.implies_elim (lmemNilElimD one) hn) end
            val ff = disjE_D (oeq one qF, lmem one lnilC, oFalseC) dj caseEq caseNil
          in impI_D (lmem one (lcons qF lnilC), oFalseC) ff end
        val ndlist = lnodup_cons_bwdD (one, lcons qF lnilC) (conjI_Sg2 (neg (lmem one (lcons qF lnilC)), lnodup (lcons qF lnilC)) neg1qnil ndqnil)
        (* transport lnodup (lcons 1 (lcons q lnil)) -> lnodup (divlist 0 q) via leq (sym divlist0D) *)
        val hleq = divlist0D qF   (* leq (divlist 0 q)(lcons 1 (lcons q lnil)) *)
        val Pn = Term.lambda (Free("zn", natlistT)) (lnodup (Free("zn",natlistT)))
        val tInst = beta_norm (Drule.infer_instantiate ctxtSigD
              [(("P",0), ctermSigD Pn),(("L",0), ctermSigD (lcons one (lcons qF lnilC))),(("M",0), ctermSigD (divlist ZeroC qF))]
              leq_subst_vD)
        val hleqsym = sym_leqD2 (divlist ZeroC qF, lcons one (lcons qF lnilC)) hleq   (* leq (lcons..)(divlist 0 q) *)
      in Thm.implies_elim (Thm.implies_elim tInst hleqsym) ndlist end
    (* step a -> Suc a : lnodup (divlist (Suc a) q) ~ lnodup (lcons A2s (lcons A2sq (divlist a q))).
       Build lnodup (lcons A2sq (divlist a q)) : neg(lmem A2sq (divlist a q)) /\ IH.
       Then lnodup (lcons A2s (lcons A2sq (divlist a q))) : neg(lmem A2s (lcons A2sq (divlist a q))) /\ above.
         neg(lmem A2s (lcons A2sq (divlist a q))) : lmem A2s -> Disj(oeq A2s A2sq)(lmem A2s (divlist a q)).
           oeq A2s A2sq -> contra A2s_neq_A2sq ; lmem A2s (divlist a q) -> contra notmem_A2s. *)
    val xF = Free("x", natT)
    val IH = Thm.assume (ctermSigD (jT (ndBody xF)))
    val stepconcl =
      let
        val A2s = p2 (suc xF)
        val A2sq = mult A2s qF
        (* neg(lmem A2sq (divlist x q)) from notmem_A2sq *)
        val nm_A2sq = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                        [(("a",0), ctermSigD xF),(("q",0), ctermSigD qF)] notmem_A2sq)) hPrime) hOdd
                      (* neg(lmem A2sq (divlist x q)) *)
        val nd_inner = lnodup_cons_bwdD (A2sq, divlist xF qF)
                          (conjI_Sg2 (neg (lmem A2sq (divlist xF qF)), lnodup (divlist xF qF)) nm_A2sq IH)
                       (* lnodup (lcons A2sq (divlist x q)) *)
        (* neg(lmem A2s (lcons A2sq (divlist x q))) *)
        val nm_A2s_dl = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                          [(("a",0), ctermSigD xF),(("q",0), ctermSigD qF)] notmem_A2s)) hPrime) hOdd
                        (* neg(lmem A2s (divlist x q)) *)
        val a2sneq = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                        [(("a",0), ctermSigD xF),(("q",0), ctermSigD qF)] A2s_neq_A2sq)) hPrime
                     (* neg(oeq A2s A2sq) *)
        val negOuter =
          let
            val hm = Thm.assume (ctermSigD (jT (lmem A2s (lcons A2sq (divlist xF qF)))))
            val dj = Thm.implies_elim (lmemConsFwdD (A2s, A2sq, divlist xF qF)) hm  (* Disj(oeq A2s A2sq)(lmem A2s (divlist x q)) *)
            val caseEq =
              let val heq = Thm.assume (ctermSigD (jT (oeq A2s A2sq)))
              in Thm.implies_intr (ctermSigD (jT (oeq A2s A2sq))) (mp_D (oeq A2s A2sq, oFalseC) a2sneq heq) end
            val caseMem =
              let val hmm = Thm.assume (ctermSigD (jT (lmem A2s (divlist xF qF))))
              in Thm.implies_intr (ctermSigD (jT (lmem A2s (divlist xF qF)))) (mp_D (lmem A2s (divlist xF qF), oFalseC) nm_A2s_dl hmm) end
            val ff = disjE_D (oeq A2s A2sq, lmem A2s (divlist xF qF), oFalseC) dj caseEq caseMem
          in impI_D (lmem A2s (lcons A2sq (divlist xF qF)), oFalseC) ff end
        val nd_outer = lnodup_cons_bwdD (A2s, lcons A2sq (divlist xF qF))
                          (conjI_Sg2 (neg (lmem A2s (lcons A2sq (divlist xF qF))), lnodup (lcons A2sq (divlist xF qF))) negOuter nd_inner)
                       (* lnodup (lcons A2s (lcons A2sq (divlist x q))) *)
        (* transport to lnodup (divlist (Suc x) q) via leq (sym divlistSucD) *)
        val hleq = divlistSucD (xF, qF)
        val Pn = Term.lambda (Free("zn2", natlistT)) (lnodup (Free("zn2",natlistT)))
        val tInst = beta_norm (Drule.infer_instantiate ctxtSigD
              [(("P",0), ctermSigD Pn),(("L",0), ctermSigD (lcons A2s (lcons A2sq (divlist xF qF)))),
               (("M",0), ctermSigD (divlist (suc xF) qF))] leq_subst_vD)
        val hleqsym = sym_leqD2 (divlist (suc xF) qF, lcons A2s (lcons A2sq (divlist xF qF))) hleq
      in Thm.implies_elim (Thm.implies_elim tInst hleqsym) nd_outer end
    val step1 = Thm.forall_intr (ctermSigD xF) (Thm.implies_intr (ctermSigD (jT (ndBody xF))) stepconcl)
    val r1 = Thm.implies_elim ind base
    val r2 = Thm.implies_elim r1 step1
    val d2 = Thm.implies_intr (ctermSigD (jT (neg (dvd two qF)))) r2
    val d3 = Thm.implies_intr (ctermSigD (jT (prime2 qF))) d2
  in varify d3 end;

val () = out ("LNODUP_HYPS = " ^ Int.toString (length (Thm.hyps_of lnodup_divlist)) ^ "\n");
val () = out "LNODUP_DIVLIST_BUILT\n";
val () = out "EP_ASM6_END\n";
(* ============================================================================
   EUCLID PERFECT ASSEMBLY — Stage 7: H1 + sigma_char.
     H1 : prime2 q ==> neg(dvd 2 q) ==> Forall(%d. Imp(le d N)(Disj(lmem d L)(oeq (swt N d) 0)))
        N = mult (p2 a) q ; L = divlist a q.
     sigma_char : prime2 q ==> neg(dvd 2 q) ==>
        oeq (sigma (mult (p2 a) q)) (mult (sumf (pow 2) a)(add q one))
   ============================================================================ *)
val () = out "EP_ASM7_BEGIN\n";

(* build the pow2_dvd_char meta-hyp at a : !!e. dvd e (p2 a) ==> Ex i. le i a /\ e = p2 i *)
val pow2_dvd_char_vD = up pow2_dvd_char   (* vars d,k : dvd d (p2 k) ==> Ex i. le i k /\ d = p2 i *)
fun pc_metahyp aT =
  let
    val eF = Free("e_pc", natT)
    val inst = beta_norm (Drule.infer_instantiate ctxtSigD
                 [(("d",0), ctermSigD eF),(("k",0), ctermSigD aT)] pow2_dvd_char_vD)
    (* inst : dvd e (p2 a) ==> Ex i. le i a /\ e = p2 i  (object-impl-free? it is a meta-impl from varify) *)
  in Thm.forall_intr (ctermSigD eF) inst end

(* div2aq_complete transferred *)
val div2aq_complete_vD = up div2aq_complete

(* leftEx / rightEx term builders on ctxtSigD (mirror divchar) *)
fun leftExD (dT, aT) = mkEx (Term.lambda (Free("i_le", natT))
                          (mkConj (le (Free("i_le",natT)) aT)(oeq dT (p2 (Free("i_le",natT))))))
fun rightExD (dT, aT, qT) = mkEx (Term.lambda (Free("i_re", natT))
                          (mkConj (le (Free("i_re",natT)) aT)(oeq dT (mult (p2 (Free("i_re",natT))) qT))))

fun ex_middle_atD2 At = beta_norm (Drule.infer_instantiate ctxtSigD [(("A",0), ctermSigD At)] ex_middle_vD)
fun conjunct1_D2 (At, Bt) hC =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("A",0), ctermSigD At),(("B",0), ctermSigD Bt)] conjunct1_vD)
  in Thm.implies_elim inst hC end
fun conjunct2_D2 (At, Bt) hC =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("A",0), ctermSigD At),(("B",0), ctermSigD Bt)] conjunct2_vD)
  in Thm.implies_elim inst hC end

val () = out "EP_ASM7_INFRA_OK\n";

(* swt_ndvd : neg(dvd d n) ==> oeq (swt n d) 0 *)
(* H1 *)
val H1_thm =
  let
    val aF = Free("a", natT); val qF = Free("q", natT)
    val N = mult (p2 aF) qF
    val L = divlist aF qF
    val swtN = swtC $ N
    val hPrime = Thm.assume (ctermSigD (jT (prime2 qF)))
    val hOdd   = Thm.assume (ctermSigD (jT (neg (dvd two qF))))
    val pcH = pc_metahyp aF    (* !!e. dvd e (p2 a) ==> Ex i. le i a /\ e = p2 i *)
    fun perD dF =
      let
        val hle = Thm.assume (ctermSigD (jT (le dF N)))
        val goal = mkDisj (lmem dF L) (oeq (swtN $ dF) ZeroC)
        (* ex_middle on dvd d N *)
        val em = ex_middle_atD2 (dvd dF N)   (* Disj (dvd d N)(neg(dvd d N)) *)
        val caseDvd =
          let
            val hdvd = Thm.assume (ctermSigD (jT (dvd dF N)))
            (* div2aq_complete[q,a,d] hPrime pcH hdvd : Disj(leftEx)(rightEx) *)
            val dc = beta_norm (Drule.infer_instantiate ctxtSigD
                       [(("q",0), ctermSigD qF),(("a",0), ctermSigD aF),(("d",0), ctermSigD dF)] div2aq_complete_vD)
            val dc1 = Thm.implies_elim dc hPrime
            val dc2 = Thm.implies_elim dc1 pcH
            val dc3 = Thm.implies_elim dc2 hdvd   (* Disj(leftEx d a)(rightEx d a q) *)
            (* case leftEx : Ex i. le i a /\ d = p2 i -> lmem_2i -> lmem (p2 i) L -> rewrite d -> lmem d L *)
            val caseLeft =
              let
                val hL = Thm.assume (ctermSigD (jT (leftExD (dF, aF))))
                val exAbs = Term.lambda (Free("i_le", natT))
                              (mkConj (le (Free("i_le",natT)) aF)(oeq dF (p2 (Free("i_le",natT)))))
                fun body iF hConj =   (* hConj : le i a /\ d = p2 i *)
                  let
                    val hlei = conjunct1_D2 (le iF aF, oeq dF (p2 iF)) hConj  (* le i a *)
                    val hdeq = conjunct2_D2 (le iF aF, oeq dF (p2 iF)) hConj  (* oeq d (p2 i) *)
                    (* lmem_2i at (a,q,i) : Imp(le i a)(lmem (p2 i) L) *)
                    val l2iAll = beta_norm (Drule.infer_instantiate ctxtSigD
                                   [(("a",0), ctermSigD aF),(("q",0), ctermSigD qF)] lmem_2i)
                    val l2iPred = Term.lambda (Free("ii",natT))
                                    (mkImp (le (Free("ii",natT)) aF)(lmem (p2 (Free("ii",natT))) L))
                    val l2iAt = allE_D (l2iPred, iF) l2iAll
                    val memPi = mp_D (le iF aF, lmem (p2 iF) L) l2iAt hlei  (* lmem (p2 i) L *)
                    (* rewrite p2 i -> d (sym hdeq) : lmem d L *)
                    val memd = lmem_cong (p2 iF, dF, L) (sym3 (dF, p2 iF) hdeq) memPi
                  in disjI1_D2 (lmem dF L, oeq (swtN $ dF) ZeroC) memd end
                val res = exE_atD (exAbs, goal) hL "i_left" body
              in Thm.implies_intr (ctermSigD (jT (leftExD (dF, aF)))) res end
            (* case rightEx : Ex i. le i a /\ d = p2 i * q -> lmem_2iq -> lmem d L *)
            val caseRight =
              let
                val hR = Thm.assume (ctermSigD (jT (rightExD (dF, aF, qF))))
                val exAbs = Term.lambda (Free("i_re", natT))
                              (mkConj (le (Free("i_re",natT)) aF)(oeq dF (mult (p2 (Free("i_re",natT))) qF)))
                fun body iF hConj =
                  let
                    val hlei = conjunct1_D2 (le iF aF, oeq dF (mult (p2 iF) qF)) hConj
                    val hdeq = conjunct2_D2 (le iF aF, oeq dF (mult (p2 iF) qF)) hConj
                    val l2iqAll = beta_norm (Drule.infer_instantiate ctxtSigD
                                    [(("a",0), ctermSigD aF),(("q",0), ctermSigD qF)] lmem_2iq)
                    val l2iqPred = Term.lambda (Free("ii",natT))
                                     (mkImp (le (Free("ii",natT)) aF)(lmem (mult (p2 (Free("ii",natT))) qF) L))
                    val l2iqAt = allE_D (l2iqPred, iF) l2iqAll
                    val memPiq = mp_D (le iF aF, lmem (mult (p2 iF) qF) L) l2iqAt hlei
                    val memd = lmem_cong (mult (p2 iF) qF, dF, L) (sym3 (dF, mult (p2 iF) qF) hdeq) memPiq
                  in disjI1_D2 (lmem dF L, oeq (swtN $ dF) ZeroC) memd end
                val res = exE_atD (exAbs, goal) hR "i_right" body
              in Thm.implies_intr (ctermSigD (jT (rightExD (dF, aF, qF)))) res end
            val resDisj = disjE_D (leftExD (dF, aF), rightExD (dF, aF, qF), goal) dc3 caseLeft caseRight
          in Thm.implies_intr (ctermSigD (jT (dvd dF N))) resDisj end
        val caseNdvd =
          let
            val hndvd = Thm.assume (ctermSigD (jT (neg (dvd dF N))))
            val swt0 = swt_ndvd_D (dF, N) hndvd   (* oeq (swt N d) 0 *)
            val r = disjI2_D2 (lmem dF L, oeq (swtN $ dF) ZeroC) swt0
          in Thm.implies_intr (ctermSigD (jT (neg (dvd dF N)))) r end
        val res = disjE_D (dvd dF N, neg (dvd dF N), goal) em caseDvd caseNdvd
      in impI_D (le dF N, goal) res end
    val dFh = Free("d_h1", natT)
    val Hpred = Term.lambda (Free("dd",natT))
                  (mkImp (le (Free("dd",natT)) N)(mkDisj (lmem (Free("dd",natT)) L)(oeq (swtN $ (Free("dd",natT))) ZeroC)))
    val forallH = allI_D Hpred (Thm.forall_intr (ctermSigD dFh) (perD dFh))
    val d2 = Thm.implies_intr (ctermSigD (jT (neg (dvd two qF)))) forallH
    val d3 = Thm.implies_intr (ctermSigD (jT (prime2 qF))) d2
  in varify d3 end;

val () = out ("H1_HYPS = " ^ Int.toString (length (Thm.hyps_of H1_thm)) ^ "\n");
val () = out "H1_BUILT\n";
val () = out "EP_ASM7_H1_OK\n";

(* ============================================================================
   sigma_char : prime2 q ==> neg(dvd 2 q) ==>
     oeq (sigma (mult (p2 a) q)) (mult (sumf (pow 2) a)(add q one))
   ============================================================================ *)
val sum_supp_collapse_vD = up sum_supp_collapse   (* vars f,L,N : premise [lnodup L; H1(!!d le d N -> Disj(lmem d L)(f d=0)); H2(!!d lmem d L -> le d N)] -> sumf f N = lsumf f L *)
val sigma_def_vD2 = sigma_def_vD   (* oeq (sigma n)(sumf (swt n) n) ; var n *)

val sigma_char =
  let
    val aF = Free("a", natT); val qF = Free("q", natT)
    val N = mult (p2 aF) qF
    val L = divlist aF qF
    val swtN = swtC $ N
    val hPrime = Thm.assume (ctermSigD (jT (prime2 qF)))
    val hOdd   = Thm.assume (ctermSigD (jT (neg (dvd two qF))))
    (* hypotheses *)
    val hnodup = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                   [(("a",0), ctermSigD aF),(("q",0), ctermSigD qF)] lnodup_divlist)) hPrime) hOdd  (* lnodup L *)
    val hH1 = Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                [(("a",0), ctermSigD aF),(("q",0), ctermSigD qF)] H1_thm)) hPrime) hOdd  (* Forall(...) H1 object form *)
    val hH2 = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                [(("a",0), ctermSigD aF),(("q",0), ctermSigD qF)] H2_thm)) hPrime  (* Forall(...) H2 object form *)
    (* sum_supp_collapse needs the H1/H2 as META-universal META-implications (!!d. ...).
       But H1_thm/H2_thm are OBJECT Forall(%d. Imp ...).  Convert: from Forall(%d. Imp(P d)(Q d))
       build !!d. jT(P d) ==> jT(Q d) via allE_D + mp_D. *)
    (* H1 meta : !!d. le d N ==> Disj(lmem d L)(swt N d = 0) *)
    val h1meta =
      let val dF = Free("d_ssc", natT)
          val pred = Term.lambda (Free("dd",natT))
                       (mkImp (le (Free("dd",natT)) N)(mkDisj (lmem (Free("dd",natT)) L)(oeq (swtN $ (Free("dd",natT))) ZeroC)))
          val at = allE_D (pred, dF) hH1   (* Imp (le d N)(Disj ...) *)
          val hpre = Thm.assume (ctermSigD (jT (le dF N)))
          val concl = mp_D (le dF N, mkDisj (lmem dF L)(oeq (swtN $ dF) ZeroC)) at hpre
      in Thm.forall_intr (ctermSigD dF) (Thm.implies_intr (ctermSigD (jT (le dF N))) concl) end
    val h2meta =
      let val dF = Free("d_ssc2", natT)
          val pred = Term.lambda (Free("dd",natT))
                       (mkImp (lmem (Free("dd",natT)) L)(le (Free("dd",natT)) N))
          val at = allE_D (pred, dF) hH2
          val hpre = Thm.assume (ctermSigD (jT (lmem dF L)))
          val concl = mp_D (lmem dF L, le dF N) at hpre
      in Thm.forall_intr (ctermSigD dF) (Thm.implies_intr (ctermSigD (jT (lmem dF L))) concl) end
    (* instantiate sum_supp_collapse [f=swtN, L=L, N=N] *)
    val ssc = beta_norm (Drule.infer_instantiate ctxtSigD
                [(("f",0), ctermSigD swtN),(("L",0), ctermSigD L),(("N",0), ctermSigD N)] sum_supp_collapse_vD)
    (* ssc : lnodup L ==> (!!d. le d N ==> Disj(lmem d L)(swtN d=0)) ==> (!!d. lmem d L ==> le d N) ==> oeq (sumf swtN N)(lsumf swtN L) *)
    val s1 = Thm.implies_elim ssc hnodup
    val s2 = Thm.implies_elim s1 h1meta
    val s3 = Thm.implies_elim s2 h2meta   (* oeq (sumf (swt N) N)(lsumf (swt N) L) *)
    (* sigma_def at N : oeq (sigma N)(sumf (swt N) N) *)
    val sdef = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD N)] sigma_def_vD2)
    (* chain : sigma N = sumf (swt N) N = lsumf (swt N) L *)
    val sig_lsumf = trans3 (sigma N, sumf swtN N, lsumf swtN L) sdef s3   (* oeq (sigma N)(lsumf (swt N) L) *)
    (* sigma_value_bridge at (a,q) : oeq (lsumf (swt N) L)(mult (G a)(add q 1)) *)
    val svb = beta_norm (Drule.infer_instantiate ctxtSigD
                [(("a",0), ctermSigD aF),(("q",0), ctermSigD qF)] sigma_value_bridge)
    val r = trans3 (sigma N, lsumf swtN L, mult (sumf pwAbs2 aF)(add qF one)) sig_lsumf svb
    val d2 = Thm.implies_intr (ctermSigD (jT (neg (dvd two qF)))) r
    val d3 = Thm.implies_intr (ctermSigD (jT (prime2 qF))) d2
  in varify d3 end;

val qVsc = Var (("q",0), natT); val aVsc = Var (("a",0), natT)
val i_sigma_char =
  Logic.mk_implies (jT (prime2 qVsc),
    Logic.mk_implies (jT (neg (dvd two qVsc)),
      jT (oeq (sigma (mult (p2 aVsc) qVsc)) (mult (sumf pwAbs2 aVsc)(add qVsc one)))))
val r_sc = chkD ("sigma_char", sigma_char, i_sigma_char)
val () = if r_sc then out "SIGMA_CHAR_OK\n" else out "SIGMA_CHAR_FAIL\n";
val () = out "EP_ASM7_END\n";
(* ============================================================================
   EUCLID PERFECT-NUMBER THEOREM — final mechanical assembly.
     euclid_perfect :
       prime2 q ==> oeq (add q (Suc Zero))(pow 2 p) ==> lt (Suc Zero) p
         ==> oeq (sigma (mult (pow 2 (sub p (Suc Zero))) q)) (mult 2 (mult (pow 2 (sub p (Suc Zero))) q))
     (perfect n := oeq (sigma n)(mult 2 n).)
   ============================================================================ *)
val () = out "EP_ASM8_BEGIN\n";

(* sub / pow / geo / dvd_diff instantiators on ctxtSigD *)
val sub_n_0_vD     = varify (up sub_n_0_ax)
val sub_Suc_Suc_vD = varify (up sub_Suc_Suc_ax)
fun subN0D t = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD t)] sub_n_0_vD)
fun subSSD (n,k) = beta_norm (Drule.infer_instantiate ctxtSigD
      [(("n",0), ctermSigD n),(("k",0), ctermSigD k)] sub_Suc_Suc_vD)
val geo_add_vD = up geo_add   (* oeq (add 1 (sumf (pow 2) k))(pow 2 (Suc k)) ; var k *)
fun geoAddD kT = beta_norm (Drule.infer_instantiate ctxtSigD [(("k",0), ctermSigD kT)] geo_add_vD)
val dvd_diff_vD = varify (up dvd_diff)   (* dvd p x ==> dvd p (add x y) ==> dvd p y *)
fun dvd_diff_D (pT,xT,yT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("p",0), ctermSigD pT),(("x",0), ctermSigD xT),(("y",0), ctermSigD yT)] dvd_diff_vD)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end
val add_left_cancel_vD2 = varify (up add_left_cancel)
fun add_left_cancel_D2 (mT,aT,bT) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtSigD
        [(("m",0), ctermSigD mT),(("a",0), ctermSigD aT),(("b",0), ctermSigD bT)] add_left_cancel_vD2)
  in Thm.implies_elim inst h end
(* dvd_factor_right on ctxtSigD : dvd a (mult b a) *)
fun dvd_factor_rightD (aT, bT) =
  let val dr = dvd_refl_D aT
      val dmr = dvd_mult_right_D (aT, aT, bT) dr   (* dvd a (mult a b) *)
      val cm = multcommD (aT, bT)                  (* mult a b = mult b a *)
  in dvd_cong_target_D (aT, mult aT bT, mult bT aT) cm dmr end

val () = out "EP_ASM8_INFRA_OK\n";

val euclid_perfect =
  let
    val qF = Free("q", natT); val pF = Free("p", natT)
    val aP = sub pF one                  (* a = p - 1 *)
    val Na = mult (p2 aP) qF             (* 2^(p-1) * q *)
    val hPrime = Thm.assume (ctermSigD (jT (prime2 qF)))
    val hEq    = Thm.assume (ctermSigD (jT (oeq (add qF one)(pow two pF))))   (* q+1 = 2^p *)
    val hLt    = Thm.assume (ctermSigD (jT (lt one pF)))                       (* 1 < p *)

    (* (E1) Suc(p-1) = p, and 2^(Suc(p-1)) = 2^p ; via lt 1 p = Ex k. p = add 2 k *)
    (* lt 1 p = le 2 p = Ex k. p = add (Suc(Suc 0)) k *)
    val exAbsP = Abs("k", natT, oeq pF (add (suc (suc ZeroC)) (Bound 0)))
    fun mainBody kF hpk =   (* hpk : oeq p (add (Suc(Suc 0)) k) ; p = Suc(Suc k') roughly *)
      let
        (* p = add (Suc(Suc 0)) k = Suc(Suc(add 0 k)) ; let pSk = Suc k (so p = Suc pSk, a = sub p 1 = Suc k). *)
        (* add (Suc(Suc 0)) k = Suc(add (Suc 0) k) [add_Suc] = Suc(Suc(add 0 k)) [add_Suc] = Suc(Suc k) [add_0] *)
        val aS1 = beta_norm (Drule.infer_instantiate ctxtSigD
                    [(("m",0), ctermSigD (suc ZeroC)),(("n",0), ctermSigD kF)] add_Suc_vD2)  (* add (Suc(Suc 0)) k = Suc(add (Suc 0) k) *)
        val aS2 = beta_norm (Drule.infer_instantiate ctxtSigD
                    [(("m",0), ctermSigD ZeroC),(("n",0), ctermSigD kF)] add_Suc_vD2)         (* add (Suc 0) k = Suc(add 0 k) *)
        val a0  = beta_norm (Drule.infer_instantiate ctxtSigD [(("n",0), ctermSigD kF)] add_0_vD)  (* add 0 k = k *)
        (* add (Suc 0) k = Suc(add 0 k) = Suc k *)
        val sucCong_0k = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                    [(("a",0), ctermSigD (add ZeroC kF)),(("b",0), ctermSigD kF)] (up (varify Suc_cong)))) a0
        val a1k = trans3 (add (suc ZeroC) kF, suc (add ZeroC kF), suc kF) aS2 sucCong_0k
        (* add (Suc(Suc 0)) k = Suc(add (Suc 0) k) = Suc(Suc k) *)
        val pEq2 = trans3 (add (suc (suc ZeroC)) kF, suc (add (suc ZeroC) kF), suc (suc kF))
                     aS1 (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                            [(("a",0), ctermSigD (add (suc ZeroC) kF)),(("b",0), ctermSigD (suc kF))] (up (varify Suc_cong)))) a1k)
        (* p = Suc(Suc k) *)
        val pSS = trans3 (pF, add (suc (suc ZeroC)) kF, suc (suc kF)) hpk pEq2   (* oeq p (Suc(Suc k)) *)
        (* a = sub p 1 = sub (Suc(Suc k)) (Suc 0) = sub (Suc k) 0 = Suc k *)
        (* sub p 1 : rewrite p -> Suc(Suc k) ; sub (Suc(Suc k))(Suc 0) = sub (Suc k) 0 [sub_Suc_Suc] = Suc k [sub_n_0] *)
        val Psub = Term.lambda (Free("zsp", natT)) (oeq (sub pF one)(sub (Free("zsp",natT)) one))
        val subRw = substPredD (Psub, pF, suc (suc kF)) pSS (reflD (sub pF one))   (* sub p 1 = sub (Suc(Suc k)) 1 *)
        val sSS = subSSD (suc kF, ZeroC)    (* sub (Suc(Suc k))(Suc 0) = sub (Suc k) 0 *)
        val sN0 = subN0D (suc kF)           (* sub (Suc k) 0 = Suc k *)
        val aSk = trans3 (sub pF one, sub (suc kF) ZeroC, suc kF) (trans3 (sub pF one, sub (suc (suc kF)) one, sub (suc kF) ZeroC) subRw sSS) sN0
                  (* oeq (sub p 1)(Suc k) = oeq a (Suc k) *)
        (* Suc a = Suc(Suc k) = p [sym pSS] *)
        val SucA = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtSigD
                     [(("a",0), ctermSigD aP),(("b",0), ctermSigD (suc kF))] (up (varify Suc_cong)))) aSk  (* Suc a = Suc(Suc k) *)
        val SucA_p = trans3 (suc aP, suc (suc kF), pF) SucA (sym3 (pF, suc (suc kF)) pSS)   (* oeq (Suc a) p *)

        (* (E2) q odd : 2 | 2^p = q+1 ; assume 2|q -> dvd_diff -> 2|1 -> one_neq_2k. *)
        (* 2 | 2^p : 2^p = pow 2 (Suc(Suc k)) = mult 2 (pow 2 (Suc k)) [pow_Suc] ; dvd 2 (mult 2 _) [dvd_factor].
           Actually dvd 2 (pow 2 p) : pow 2 p = mult 2 (pow 2 (p-1))? use p = Suc(Suc k), pow_Suc. *)
        val powP = powSucD (two, suc kF)    (* pow 2 (Suc(Suc k)) = mult 2 (pow 2 (Suc k)) *)
        (* pow 2 p = pow 2 (Suc(Suc k)) [cong on exponent via pSS] *)
        val Ppow = Term.lambda (Free("zpp", natT)) (oeq (pow two pF)(pow two (Free("zpp",natT))))
        val powCong = substPredD (Ppow, pF, suc (suc kF)) pSS (reflD (pow two pF))  (* pow 2 p = pow 2 (Suc(Suc k)) *)
        val pow_p_m = trans3 (pow two pF, pow two (suc (suc kF)), mult two (pow two (suc kF))) powCong powP  (* pow 2 p = mult 2 (pow 2 (Suc k)) *)
        val dvd2_2p = dvd_cong_target_D (two, mult two (pow two (suc kF)), pow two pF)
                        (sym3 (pow two pF, mult two (pow two (suc kF))) pow_p_m)
                        (dvd_mult_right_D (two, two, pow two (suc kF)) (dvd_refl_D two))  (* dvd 2 (pow 2 p) *)
        (* dvd 2 (add q 1) : rewrite pow 2 p -> add q 1 via sym hEq *)
        val dvd2_q1 = dvd_cong_target_D (two, pow two pF, add qF one) (sym3 (add qF one, pow two pF) hEq) dvd2_2p  (* dvd 2 (add q 1) *)
        val odd =
          let
            val h2q = Thm.assume (ctermSigD (jT (dvd two qF)))
            val d21 = dvd_diff_D (two, qF, one) h2q dvd2_q1   (* dvd 2 1 *)
            (* dvd 2 1 -> Ex k. 1 = 2k -> one_neq_2k *)
            val ff = dvd_destD (two, one, oFalseC) d21 "k_odd"
                       (fn kk => fn hk => one_neq_2k_at kk hk)   (* hk : oeq 1 (mult 2 kk) *)
          in impI_D (dvd two qF, oFalseC) ff end   (* neg(dvd 2 q) *)

        (* (E3) sigma_char[a,q] + odd : sigma (mult (p2 a) q) = mult (G a)(add q 1) *)
        val sc = beta_norm (Drule.infer_instantiate ctxtSigD
                   [(("a",0), ctermSigD aP),(("q",0), ctermSigD qF)] sigma_char)
        val sc1 = Thm.implies_elim sc hPrime
        val scThm = Thm.implies_elim sc1 odd   (* oeq (sigma Na)(mult (sumf (pow 2) a)(add q 1)) *)

        (* (E4) G a = q :  geo_add[a] : add 1 (G a) = pow 2 (Suc a) ; Suc a = p -> pow 2 (Suc a) = pow 2 p = add q 1.
           So add 1 (G a) = add q 1 = add 1 q [comm] -> cancel 1 -> G a = q. *)
        val ga = geoAddD aP    (* add 1 (G a) = pow 2 (Suc a) *)
        (* pow 2 (Suc a) = pow 2 p [cong via SucA_p] *)
        val Pp2 = Term.lambda (Free("zp2x", natT)) (oeq (pow two (suc aP))(pow two (Free("zp2x",natT))))
        val p2SucA_p = substPredD (Pp2, suc aP, pF) SucA_p (reflD (pow two (suc aP)))  (* pow 2 (Suc a) = pow 2 p *)
        val ga_p = trans3 (add one (sumf pwAbs2 aP), pow two (suc aP), pow two pF) ga p2SucA_p  (* add 1 (G a) = pow 2 p *)
        val ga_q1 = trans3 (add one (sumf pwAbs2 aP), pow two pF, add qF one) ga_p (sym3 (add qF one, pow two pF) hEq)  (* add 1 (G a) = add q 1 *)
        (* add q 1 = add 1 q [comm] *)
        val q1_1q2 = addcommD (qF, one)   (* add q 1 = add 1 q *)
        val ga_1q = trans3 (add one (sumf pwAbs2 aP), add qF one, add one qF) ga_q1 q1_1q2  (* add 1 (G a) = add 1 q *)
        (* cancel 1 : G a = q *)
        val Gq = add_left_cancel_D2 (one, sumf pwAbs2 aP, qF) ga_1q   (* oeq (G a) q *)

        (* (E5) sigma Na = mult (G a)(add q 1) = mult q (add q 1) [G a -> q] *)
        val Pcong = Term.lambda (Free("zgc", natT)) (oeq (sigma Na)(mult (Free("zgc",natT))(add qF one)))
        val sc_q = substPredD (Pcong, sumf pwAbs2 aP, qF) Gq scThm  (* oeq (sigma Na)(mult q (add q 1)) *)

        (* (E6) mult q (add q 1) = mult (add q 1) q [comm] ; and mult 2 Na = mult (add q 1) q.
           mult 2 Na = mult 2 (mult (p2 a) q).  pow 2 (Suc a) = mult 2 (p2 a) [pow_Suc] ;
           mult 2 (mult (p2 a) q) = mult (mult 2 (p2 a)) q [assoc sym] = mult (pow 2 (Suc a)) q
             = mult (pow 2 p) q [SucA_p] = mult (add q 1) q [sym hEq]. *)
        val mqq = multcommD (qF, add qF one)   (* mult q (add q 1) = mult (add q 1) q *)
        val sc_aq1 = trans3 (sigma Na, mult qF (add qF one), mult (add qF one) qF) sc_q mqq  (* sigma Na = mult (add q 1) q *)
        (* mult 2 Na = mult (add q 1) q : *)
        val psA = powSucD (two, aP)        (* pow 2 (Suc a) = mult 2 (p2 a) *)
        (* mult 2 Na = mult 2 (mult (p2 a) q) = mult (mult 2 (p2 a)) q [assoc sym] *)
        val assoc = multassocD (two, p2 aP, qF)   (* mult (mult 2 (p2 a)) q = mult 2 (mult (p2 a) q) = mult 2 Na *)
        val m2Na_a = sym3 (mult (mult two (p2 aP)) qF, mult two Na) assoc   (* mult 2 Na = mult (mult 2 (p2 a)) q *)
        (* mult (mult 2 (p2 a)) q = mult (pow 2 (Suc a)) q [cong divisor via sym psA] *)
        val congP = mult_cong_lD (mult two (p2 aP), pow two (suc aP), qF) (sym3 (pow two (suc aP), mult two (p2 aP)) psA)
                    (* mult (mult 2 (p2 a)) q = mult (pow 2 (Suc a)) q *)
        val m2Na_sa = trans3 (mult two Na, mult (mult two (p2 aP)) qF, mult (pow two (suc aP)) qF) m2Na_a congP  (* mult 2 Na = mult (pow 2 (Suc a)) q *)
        (* mult (pow 2 (Suc a)) q = mult (pow 2 p) q [SucA_p] = mult (add q 1) q [sym hEq] *)
        val congSA = mult_cong_lD (pow two (suc aP), pow two pF, qF) p2SucA_p   (* mult (pow 2 (Suc a)) q = mult (pow 2 p) q *)
        val conghEq = mult_cong_lD (pow two pF, add qF one, qF) (sym3 (add qF one, pow two pF) hEq)  (* mult (pow 2 p) q = mult (add q 1) q *)
        val m2Na_q1 = trans3 (mult two Na, mult (pow two (suc aP)) qF, mult (add qF one) qF)
                        m2Na_sa (trans3 (mult (pow two (suc aP)) qF, mult (pow two pF) qF, mult (add qF one) qF) congSA conghEq)
                      (* mult 2 Na = mult (add q 1) q *)
        (* sigma Na = mult (add q 1) q = mult 2 Na *)
        val result = trans3 (sigma Na, mult (add qF one) qF, mult two Na) sc_aq1 (sym3 (mult two Na, mult (add qF one) qF) m2Na_q1)
                     (* oeq (sigma Na)(mult 2 Na) = perfect Na *)
      in result end
    val core = exE_atD (exAbsP, oeq (sigma Na)(mult two Na)) hLt "k_ep" mainBody
    val d3 = Thm.implies_intr (ctermSigD (jT (lt one pF))) core
    val d2 = Thm.implies_intr (ctermSigD (jT (oeq (add qF one)(pow two pF)))) d3
    val d1 = Thm.implies_intr (ctermSigD (jT (prime2 qF))) d2
  in varify d1 end;

val () = out ("EUCLID_PERFECT_HYPS = " ^ Int.toString (length (Thm.hyps_of euclid_perfect)) ^ "\n");
val () = out "EUCLID_PERFECT_BUILT\n";

(* validation : aconv intended (perfect form), 0-hyp *)
val qVe = Var (("q",0), natT); val pVe = Var (("p",0), natT)
val aVe = sub pVe (suc ZeroC)
val NaVe = mult (pow two aVe) qVe
val i_euclid_perfect =
  Logic.mk_implies (jT (prime2 qVe),
    Logic.mk_implies (jT (oeq (add qVe (suc ZeroC))(pow two pVe)),
      Logic.mk_implies (jT (lt (suc ZeroC) pVe),
        jT (oeq (sigma NaVe)(mult (suc (suc ZeroC)) NaVe)))))
val r_ep = chkD ("euclid_perfect", euclid_perfect, i_euclid_perfect)
val () = if r_ep then out "EUCLID_PERFECT_OK\n" else out "EUCLID_PERFECT_FAIL\n";
val () = out "EP_ASM8_END\n";

(* ============================================================================
   SOUNDNESS PROBES + AXIOM AUDIT
   ============================================================================ *)
val epProp = Thm.prop_of euclid_perfect;
(* (P1) needs the prime2 q hypothesis : NOT aconv the variant with prime2 dropped *)
val ep_noprime =
  Logic.mk_implies (jT (oeq (add qVe (suc ZeroC))(pow two pVe)),
    Logic.mk_implies (jT (lt (suc ZeroC) pVe),
      jT (oeq (sigma NaVe)(mult (suc (suc ZeroC)) NaVe))));
val () = if not (epProp aconv ep_noprime) then out "PROBE_OK euclid_perfect needs prime2 q\n"
         else out "PROBE_FAIL prime2 dropped\n";
(* (P2) needs the q+1=2^p hypothesis *)
val ep_noeq =
  Logic.mk_implies (jT (prime2 qVe),
    Logic.mk_implies (jT (lt (suc ZeroC) pVe),
      jT (oeq (sigma NaVe)(mult (suc (suc ZeroC)) NaVe))));
val () = if not (epProp aconv ep_noeq) then out "PROBE_OK euclid_perfect needs q+1=2^p\n"
         else out "PROBE_FAIL q+1=2^p dropped\n";
(* (P3) needs the 1<p hypothesis *)
val ep_nolt =
  Logic.mk_implies (jT (prime2 qVe),
    Logic.mk_implies (jT (oeq (add qVe (suc ZeroC))(pow two pVe)),
      jT (oeq (sigma NaVe)(mult (suc (suc ZeroC)) NaVe))));
val () = if not (epProp aconv ep_nolt) then out "PROBE_OK euclid_perfect needs 1<p\n"
         else out "PROBE_FAIL 1<p dropped\n";
(* (P4) conclusion is mult 2 n (perfect), NOT the trivial oeq (sigma n) n *)
val ep_trivial =
  Logic.mk_implies (jT (prime2 qVe),
    Logic.mk_implies (jT (oeq (add qVe (suc ZeroC))(pow two pVe)),
      Logic.mk_implies (jT (lt (suc ZeroC) pVe),
        jT (oeq (sigma NaVe) NaVe))));
val () = if not (epProp aconv ep_trivial) then out "PROBE_OK euclid_perfect conclusion is 2*n (perfect)\n"
         else out "PROBE_FAIL conclusion collapsed to sigma n = n\n";

(* extra shyps audit *)
val () = out ("EUCLID_PERFECT_EXTRA_SHYPS = " ^ Int.toString (length (Thm.extra_shyps euclid_perfect)) ^ "\n");

(* soundness signal in this codebase = hyps_of = [] AND extra_shyps = [] AND aconv intended.
   (No oracle taint is possible: the whole development is pure kernel inference over the
   conservative foundation; the only classical input is the foundation's single ex_middle.) *)

val () =
  if r_ep
     andalso (length (Thm.hyps_of euclid_perfect) = 0)
     andalso (length (Thm.extra_shyps euclid_perfect) = 0)
  then out "EUCLID_PERFECT_ALL_OK\n"
  else out "EUCLID_PERFECT_INCOMPLETE\n";
