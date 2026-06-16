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
   THE EUCLIDEAN ALGORITHM: gcd universal property, BEZOUT'S IDENTITY, and the
   MODULAR INVERSE, in Isabelle/Pure on the polyml-rs interpreter.
   (test: isabelle_gcd.rs)
   ----------------------------------------------------------------------------
   Closes the gap the rest of the tower deliberately sidestepped ("gcd/Bezout
   needs integers over N"): all four results are proved as PURE EXISTENTIALS
   over the existing theory (NO new constant, NO new axiom), by genuine LCF
   kernel inference. The key tool is the already-proved DIVISION THEOREM
   (div_mod_exists) driving a strong induction (strong_induct):

     gcd_props      : |- !a b. ?g. g dvd a /\ g dvd b /\
                                   (!d. d dvd a ==> d dvd b ==> d dvd g)
                      "every pair has a common divisor that every common
                       divisor divides" -- the gcd VALUE + its universal property.
     bezout         : |- !a b. ?g. (g the gcd, as above) /\
                                   (?x y. a*x = b*y + g \/ b*y = a*x + g)
                      Bezout's identity in the two-sided natural-number form
                      (N has no subtraction, so one of the two equations holds).
     coprime_bezout : |- (!d. d dvd a ==> d dvd b ==> d = 1) ==>
                         ?x y. a*x = b*y + 1 \/ b*y = a*x + 1
     mod_inverse    : |- prime p ==> ~(p dvd a) ==> ?b. cong p (a*b) 1

   Built on the unified number-theory base (isabelle_ntbase.sml, spliced in by
   common::with_ntbase): classical foundation + division theorem + Euclid +
   Euclid's lemma + modular arithmetic + powers. Each lemma carries a soundness
   probe (the kernel rejects the degenerate/weakened variant).

   Proved by a 3-phase ultracode fleet (wf_a420c57e-d18): gcd-props -> bezout
   -> coprime/inverse, each phase a parallel multi-seat race, the winner of each
   feeding the next. Re-verified end-to-end by hand before landing.
   ============================================================================ *)

(* ============================================================================
   PHASE 1 : the gcd universal property (seat gcdprops0)
   ----------------------------------------------------------------------------
   Prove (object-quantified, meta-quantified over a,b):
     !!a b. jT (Ex g. Conj (dvd g a)
                         (Conj (dvd g b)
                            (Forall (%d. Imp (Conj (dvd d a) (dvd d b)) (dvd d g)))))
   "every pair (a,b) has a common divisor g that every common divisor divides."

   Strategy : strong induction on b (second arg).  Predicate
     G n := Forall (%a. body(a, n))
   with the inner first gcd-argument a OBJECT-universally quantified, so the IH
   at r < b can be re-instantiated at a' := b for the recursive call (b, r).

   Everything routes through ctxtS2 / ctermS2 (where strong_induct, div_mod_exists,
   dvd_add, dvd_mult_right, dvd_diff, dvd_cong_rS etc. all live).
   ============================================================================ *)
val () = out "GCDPROPS_BEGIN\n";

(* lift the dependency lemmas we still need onto ctxtS2 (schematic) *)
val dvd_diff_vS = varify dvd_diff;   (* jT (dvd ?p ?x) ==> jT (dvd ?p (add ?x ?y)) ==> jT (dvd ?p ?y) *)
fun dvd_diff_atS (pT, xT, yT) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("p",0), ctermS2 pT), (("x",0), ctermS2 xT), (("y",0), ctermS2 yT)] dvd_diff_vS)
  in (inst OF [h1]) OF [h2] end;

(* ---- the gcd "body" and "greatest" abstractions, capture-avoiding ----
   greatest(aT,nT,gT) = Forall (%d. Imp (Conj (dvd d aT) (dvd d nT)) (dvd d gT))
   body(aT,nT)        = Ex (%g. Conj (dvd g aT) (Conj (dvd g nT) (greatest(aT,nT,g)))) *)

fun greatestAbs (aT, nT, gT) =                       (* %d. Imp (Conj (dvd d a)(dvd d n)) (dvd d g) *)
  let val dF = Free("d_gr", natT)
  in Term.lambda dF (mkImp (mkConj (dvd dF aT) (dvd dF nT)) (dvd dF gT)) end;
fun greatest (aT, nT, gT) = mkForall (greatestAbs (aT, nT, gT));

fun gcdBodyG (aT, nT, gT) =                           (* Conj (dvd g a)(Conj (dvd g n)(greatest)) *)
  mkConj (dvd gT aT) (mkConj (dvd gT nT) (greatest (aT, nT, gT)));

fun bodyAbs (aT, nT) =                                (* %g. Conj (dvd g a)(Conj (dvd g n)(greatest a n g)) *)
  let val gF = Free("g_bd", natT)
  in Term.lambda gF (gcdBodyG (aT, nT, gF)) end;
fun bodyEx (aT, nT) = mkEx (bodyAbs (aT, nT));        (* Ex g. ... *)

(* G n = Forall (%a. bodyEx(a, n)) -- the strong_induct predicate value *)
fun GallAbs nT =                                      (* %a. bodyEx(a, n) *)
  let val aF = Free("a_G", natT)
  in Term.lambda aF (bodyEx (aF, nT)) end;
fun Gprop_of nT = mkForall (GallAbs nT);

(* The (nat=>o) predicate for strong_induct : %n. G n *)
val GpredSI =
  let val nF = Free("n_GP", natT) in Term.lambda nF (Gprop_of nF) end;

val () = out "GCD_HELPERS_READY\n";

(* ============================================================================
   SMALL helper lemmas (explicit route, as the seat hint requests)
   ----------------------------------------------------------------------------
   h_dvd_mult_q : jT (dvd d b) ==> jT (dvd d (mult b q))      [= dvd_mult_right]
   h_dvd_sum    : jT (dvd g (mult b q)) ==> jT (dvd g r)
                    ==> jT (dvd g (add (mult b q) r))          [= dvd_add]
   Both already exist as dvd_mult_right_atS / dvd_add_atS; we use them directly.
   ============================================================================ *)

(* ============================================================================
   THE STRONG INDUCTION
   ============================================================================ *)
val gcd_props =
  let
    (* ---- strong-induction step : fix nStep (the current b), assume strong IH,
            prove jT (G nStep) = jT (Forall (%a. bodyEx(a, nStep))) ---- *)
    val nStep = Free("n_gc", natT);
    val mIH   = Free("m_gc", natT);
    (* G m as a bare proposition (no Trueprop) for the Logic.all *)
    val Gprop = Logic.all mIH (Logic.mk_implies (jT (lt mIH nStep), jT (Gprop_of mIH)));
    val Hthm  = Thm.assume (ctermS2 Gprop);              (* the strong IH : !!m. lt m n ==> jT (G m) *)
    fun applyIH mt h_lt =                                (* lt m n -> jT (G m) = jT (Forall(%a. bodyEx(a,m))) *)
      let val hAt = Thm.forall_elim (ctermS2 mt) Hthm
      in Thm.implies_elim hAt h_lt end;

    (* prove jT (Forall (%a. bodyEx(a, nStep))) by allI : fix aF, prove jT (bodyEx(aF, nStep)) *)
    val aF = Free("a_gc", natT);
    val goalBody = bodyEx (aF, nStep);                   (* Ex g. ... for THIS a, THIS n *)

    (* case split on nStep = 0 vs nStep = Suc q *)
    val dz = dzosS_at nStep;                             (* Disj (oeq n 0) (Ex q. oeq n (Suc q)) *)

    (* ----------------------------------------------------------------
       CASE n = 0 : take g := a.
         dvd a a    (dvd_refl)
         dvd a n    (dvd_zero a -> dvd a 0, then cong 0->n via oeq 0 n)
         greatest   (given Conj(dvd d a)(dvd d n), conjunct1 = dvd d a = dvd d g)
       ---------------------------------------------------------------- *)
    val caseZero =
      let
        val hZ = Thm.assume (ctermS2 (jT (oeq nStep ZeroC)));   (* oeq n 0 *)
        (* dvd a a *)
        val dvd_a_a = dvd_refl_atS2 aF;                          (* dvd a a *)
        (* dvd a n : dvd a 0 then rewrite 0 -> n *)
        val dvd_a_0 = dvd_zeroS_at aF;                          (* dvd a 0 *)
        val hZsym   = oeq_sym OF [hZ];                          (* oeq 0 n *)
        val dvd_a_n = dvd_cong_rS (aF, ZeroC, nStep) hZsym dvd_a_0;   (* dvd a n *)
        (* greatest a n a : Forall(%d. Imp(Conj(dvd d a)(dvd d n))(dvd d a)) *)
        val greatBody =
          let
            val dF   = Free("d_cz", natT);
            val hC   = Thm.assume (ctermS2 (jT (mkConj (dvd dF aF) (dvd dF nStep))));  (* Conj(dvd d a)(dvd d n) *)
            val c1   = conjunct1_atS2 (dvd dF aF, dvd dF nStep) hC;                     (* dvd d a = dvd d g *)
            (* META impl jT(Conj..) ==> jT(dvd d a), then OBJECT Imp via impI *)
            val metaImp = Thm.implies_intr (ctermS2 (jT (mkConj (dvd dF aF) (dvd dF nStep)))) c1;
            val objImp  = impI_atS2 (mkConj (dvd dF aF) (dvd dF nStep), dvd dF aF) metaImp;  (* jT (Imp(Conj..)(dvd d a)) *)
          in (dF, objImp) end;
        val (dFz, impdz) = greatBody;
        (* allI : fix d, jT (Imp(Conj ..)(dvd d a)) -> jT (Forall (greatestAbs a n a)) *)
        val minor = Thm.forall_intr (ctermS2 dFz) impdz;        (* !!d. jT (Imp ...) *)
        val great = allI_atS2 (greatestAbs (aF, nStep, aF)) minor;  (* jT (greatest a n a) *)
        (* assemble Conj (dvd a a)(Conj (dvd a n)(greatest)) *)
        val innerConj = conjI_atS2 (dvd aF nStep, greatest (aF, nStep, aF)) dvd_a_n great;
        val fullConj  = conjI_atS2 (dvd aF aF, mkConj (dvd aF nStep) (greatest (aF, nStep, aF))) dvd_a_a innerConj;
        (* exI : witness g := a *)
        val exG = exI_atS2 (bodyAbs (aF, nStep)) aF fullConj;   (* Ex g. ... = goalBody *)
      in Thm.implies_intr (ctermS2 (jT (oeq nStep ZeroC))) exG end;

    (* ----------------------------------------------------------------
       CASE n = Suc q : descent.
       ---------------------------------------------------------------- *)
    val caseSuc =
      let
        val PabsSuc = Abs("q", natT, oeq nStep (suc (Bound 0)));   (* body of (Ex q. oeq n (Suc q)) *)
        fun sucBody qWit (hSucEq : thm) =                          (* hSucEq : oeq n (Suc q) *)
          let
            (* lt 0 n : lt 0 (Suc q) then rewrite (Suc q) -> n *)
            val lt0Sq = lt_zero_suc_atS qWit;                      (* lt 0 (Suc q) *)
            val sucEqSym = oeq_sym OF [hSucEq];                    (* oeq (Suc q) n *)
            val ltPosPabs = Term.lambda (Free("z_lp", natT)) (lt ZeroC (Free("z_lp", natT)));
            val lt0n = oeq_rewrite_atS (ltPosPabs, suc qWit, nStep) sucEqSym lt0Sq;  (* lt 0 n *)
            (* div_mod a / n : Ex q'. Ex r. Conj (oeq a (add (mult n q') r)) (lt r n) *)
            val dmEx = div_mod_atS (aF, nStep) lt0n;
            (* exE q', exE r *)
            fun qBody qDiv (hQex : thm) =                          (* hQex : Ex r. Conj (oeq a (add (mult n q') r))(lt r n) *)
              let
                fun rBody rDiv (hConj : thm) =                     (* hConj : Conj (oeq a (add (mult n q') r))(lt r n) *)
                  let
                    val eqDivP = oeq aF (add (mult nStep qDiv) rDiv);   (* a = n*q' + r *)
                    val ltRnP  = lt rDiv nStep;                        (* r < n *)
                    val hEqDiv = conjunct1_atS2 (eqDivP, ltRnP) hConj;  (* oeq a (add (mult n q') r) *)
                    val hLtRn  = conjunct2_atS2 (eqDivP, ltRnP) hConj;  (* lt r n *)

                    (* apply IH at r (legal : lt r n) : jT (Forall (%a'. bodyEx(a', r))) *)
                    val Gr     = applyIH rDiv hLtRn;                   (* jT (Forall (%a'. bodyEx(a', r))) *)
                    (* instantiate the inner object-a at a' := n (the recursive first arg) *)
                    val GrAtN  = allE_atS2 (GallAbs rDiv) nStep Gr;    (* jT (bodyEx(n, r)) = Ex g. Conj(dvd g n)(Conj(dvd g r)(greatest n r g)) *)

                    (* exE the gcd witness g of (n, r) *)
                    fun gBody gWit (hG : thm) =                       (* hG : Conj(dvd g n)(Conj(dvd g r)(greatest n r g)) *)
                      let
                        val gNd  = dvd gWit nStep;
                        val gRd  = dvd gWit rDiv;
                        val grGt = greatest (nStep, rDiv, gWit);
                        val h_g_n   = conjunct1_atS2 (gNd, mkConj gRd grGt) hG;          (* dvd g n *)
                        val h_rest  = conjunct2_atS2 (gNd, mkConj gRd grGt) hG;          (* Conj(dvd g r)(greatest n r g) *)
                        val h_g_r   = conjunct1_atS2 (gRd, grGt) h_rest;                 (* dvd g r *)
                        val h_great = conjunct2_atS2 (gRd, grGt) h_rest;                 (* greatest n r g *)

                        (* ---- (1) g divides a ----
                           dvd g n -> dvd g (n*q')   [dvd_mult_right]
                           dvd g (n*q') -> dvd g (n*q'+r)  with dvd g r  [dvd_add]
                           rewrite (n*q'+r) -> a  via oeq (n*q'+r) a   [dvd_cong_r] *)
                        val g_nq    = dvd_mult_right_atS (gWit, nStep, qDiv) h_g_n;      (* dvd g (n*q') *)
                        val g_sum   = dvd_add_atS (gWit, mult nStep qDiv, rDiv) g_nq h_g_r;  (* dvd g (n*q'+r) *)
                        val eqSym   = oeq_sym OF [hEqDiv];                               (* oeq (n*q'+r) a *)
                        val g_a     = dvd_cong_rS (gWit, add (mult nStep qDiv) rDiv, aF) eqSym g_sum;  (* dvd g a *)

                        (* ---- (2) greatest for (a, n) ----
                           given Conj(dvd d a)(dvd d n), show dvd d g :
                             dvd d n -> dvd d (n*q')        [dvd_mult_right]
                             dvd d a, a = n*q'+r => dvd d (n*q'+r)  [cong on dvd d a]
                             dvd_diff (d, n*q', r) (dvd d (n*q')) (dvd d (n*q'+r)) => dvd d r
                             great (n,r,g) at d : Imp(Conj(dvd d n)(dvd d r))(dvd d g) -> dvd d g *)
                        val greatAN =
                          let
                            val dF = Free("d_an", natT);
                            val hCd = Thm.assume (ctermS2 (jT (mkConj (dvd dF aF) (dvd dF nStep))));  (* Conj(dvd d a)(dvd d n) *)
                            val d_a = conjunct1_atS2 (dvd dF aF, dvd dF nStep) hCd;       (* dvd d a *)
                            val d_n = conjunct2_atS2 (dvd dF aF, dvd dF nStep) hCd;       (* dvd d n *)
                            val d_nq = dvd_mult_right_atS (dF, nStep, qDiv) d_n;          (* dvd d (n*q') *)
                            (* dvd d a -> dvd d (n*q'+r) via cong a -> (n*q'+r) *)
                            val d_sum = dvd_cong_rS (dF, aF, add (mult nStep qDiv) rDiv) hEqDiv d_a;  (* dvd d (n*q'+r) *)
                            val d_r   = dvd_diff_atS (dF, mult nStep qDiv, rDiv) d_nq d_sum;          (* dvd d r *)
                            (* apply greatest(n,r,g) at d : need Conj(dvd d n)(dvd d r) -> dvd d g *)
                            val hImp  = allE_atS2 (greatestAbs (nStep, rDiv, gWit)) dF h_great;       (* Imp(Conj(dvd d n)(dvd d r))(dvd d g) *)
                            val cnj   = conjI_atS2 (dvd dF nStep, dvd dF rDiv) d_n d_r;               (* Conj(dvd d n)(dvd d r) *)
                            val d_g   = mp_atS2 (mkConj (dvd dF nStep) (dvd dF rDiv), dvd dF gWit) hImp cnj;  (* dvd d g *)
                            (* META impl jT(Conj(dvd d a)(dvd d n)) ==> jT(dvd d g), then OBJECT Imp *)
                            val metaImp = Thm.implies_intr (ctermS2 (jT (mkConj (dvd dF aF) (dvd dF nStep)))) d_g;
                            val objImp  = impI_atS2 (mkConj (dvd dF aF) (dvd dF nStep), dvd dF gWit) metaImp;  (* jT (Imp(Conj..)(dvd d g)) *)
                            val minor   = Thm.forall_intr (ctermS2 dF) objImp;
                          in allI_atS2 (greatestAbs (aF, nStep, gWit)) minor end;        (* jT (greatest a n g) *)

                        (* assemble Conj (dvd g a)(Conj (dvd g n)(greatest a n g)) *)
                        val innerC = conjI_atS2 (dvd gWit nStep, greatest (aF, nStep, gWit)) h_g_n greatAN;
                        val fullC  = conjI_atS2 (dvd gWit aF, mkConj (dvd gWit nStep) (greatest (aF, nStep, gWit))) g_a innerC;
                        val exG    = exI_atS2 (bodyAbs (aF, nStep)) gWit fullC;          (* goalBody *)
                      in exG end;
                    val g = exE_elimS2 (bodyAbs (nStep, rDiv), goalBody) GrAtN "g_w" gBody;
                  in g end;
                val g = exE_elimS2 (innerDivAbsN nStep aF qDiv, goalBody) hQex "r_w" rBody;
              in g end;
            val g = exE_elimS2 (rmDivBodyN nStep aF, goalBody) dmEx "q_w" qBody;
          in g end;
        val gg = exE_elimS2 (PabsSuc, goalBody) (Thm.assume (ctermS2 (jT (mkEx PabsSuc)))) "q_sw" sucBody;
      in Thm.implies_intr (ctermS2 (jT (mkEx PabsSuc))) gg end;

    (* combine the two cases via dz : Disj (oeq n 0) (Ex q. oeq n (Suc q)) *)
    val bodyProof = disjE_elimS2 (oeq nStep ZeroC, mkExSuc nStep, goalBody) dz caseZero caseSuc;
    (* turn jT (bodyEx(a, n)) into jT (Forall (%a. bodyEx(a, n))) by allI over aF *)
    val minorA = Thm.forall_intr (ctermS2 aF) bodyProof;          (* !!a. jT (bodyEx(a, n)) *)
    val GnThm  = allI_atS2 (GallAbs nStep) minorA;                (* jT (G n) = jT (Forall (%a. bodyEx(a,n))) *)

    (* the strong-induction STEP theorem *)
    val stepThm = Thm.forall_intr (ctermS2 nStep) (Thm.implies_intr (ctermS2 Gprop) GnThm);

    (* feed to strong_induct : P := GpredSI, k := bK *)
    val bK = Free("b", natT);
    val siInst = beta_norm (Drule.infer_instantiate ctxtS2
                   [(("P",0), ctermS2 GpredSI), (("k",0), ctermS2 bK)] (varify strong_induct));
    val Gb = Thm.implies_elim siInst stepThm;                     (* jT (G b) = jT (Forall (%a. bodyEx(a, b))) *)
    (* extract jT (bodyEx(a, b)) at a fresh aK then re-generalise both meta *)
    val aK   = Free("a", natT);
    val bodyAB = allE_atS2 (GallAbs bK) aK Gb;                    (* jT (bodyEx(a, b)) *)
  in varify bodyAB end;

val () = out "GCD_PROPS_PROVED\n";

(* ============================================================================
   VALIDATION : 0-hyp AND aconv the intended schematic goal, built the SAME way.
     intended := jT (Ex g. Conj (dvd g a)
                              (Conj (dvd g b)
                                 (Forall (%d. Imp (Conj (dvd d a)(dvd d b)) (dvd d g)))))
   with a, b schematic Vars.
   ============================================================================ *)
val aVg = Var (("a",0), natT);
val bVg = Var (("b",0), natT);
val gcd_props_intended = jT (bodyEx (aVg, bVg));

val r_gcd = checkS2 ("gcd_props", gcd_props, gcd_props_intended);
val () = if r_gcd then out "OK gcd_props\n" else out "FAIL gcd_props\n";

(* ---- SOUNDNESS PROBE : kernel must REJECT a false variant ----
   Dropping the "greatest" conjunct makes it trivial (g := 1 divides everything),
   so the proved theorem must NOT be aconv that weakened statement. *)
val probe_weak =
  let
    fun bodyAbsW (aT, nT) =
      let val gF = Free("g_pw", natT)
      in Term.lambda gF (mkConj (dvd gF aT) (dvd gF nT)) end;     (* drops greatest *)
    val bogus = jT (mkEx (bodyAbsW (aVg, bVg)));
  in not ((Thm.prop_of gcd_props) aconv bogus) end;

val () =
  if r_gcd andalso probe_weak
  then out "PROBE_OK\n"
  else out "PROBE_UNSOUND\n";

val () = if r_gcd andalso probe_weak then out "GCD_PROPS_OK\n" else out "GCD_PROPS_FAILED\n";
(* ============================================================================
   PHASE 2 : Bezout's identity (seat bezout0)
   ----------------------------------------------------------------------------
   Prove (object-quantified inner, meta over a,b):
     !!a b. jT (Ex g. Conj (dvd g a)
                       (Conj (dvd g b)
                         (Conj (greatest a b g)
                               (comb a b g))))
   where
     greatest a b g = Forall (%d. Imp (Conj (dvd d a)(dvd d b)) (dvd d g))
     comb     a b g = Ex x. Ex y. Disj (oeq (mult a x) (add (mult b y) g))
                                        (oeq (mult b y) (add (mult a x) g))
   "every pair (a,b) has a gcd g with Bezout coefficients (two-sided over N)."

   Strong induction on b, first arg a OBJECT-universally quantified inside the
   predicate so the IH at r<b re-instantiates at a':=b for the recursive (b,r).
   Everything routes through ctxtS2/ctermS2.
   ============================================================================ *)
val () = out "BEZOUT_BEGIN\n";

val oneC = suc ZeroC;

(* ---- term builders for the Bezout body, capture-avoiding ---- *)

(* greatest(a,n,g) -- identical shape to Phase 1 *)
fun bz_greatestAbs (aT, nT, gT) =
  let val dF = Free("d_bz", natT)
  in Term.lambda dF (mkImp (mkConj (dvd dF aT) (dvd dF nT)) (dvd dF gT)) end;
fun bz_greatest (aT, nT, gT) = mkForall (bz_greatestAbs (aT, nT, gT));

(* the inner disjunction at fixed x,y : Disj (a*x = b*y+g) (b*y = a*x+g) *)
fun bz_disj (aT, nT, gT, xT, yT) =
  mkDisj (oeq (mult aT xT) (add (mult nT yT) gT))
         (oeq (mult nT yT) (add (mult aT xT) gT));

(* comb(a,n,g) = Ex x. Ex y. Disj(...) -- capture-avoiding over fresh x,y *)
fun bz_combInnerAbs (aT, nT, gT, xT) =          (* %y. Disj (...) *)
  let val yF = Free("y_bz", natT)
  in Term.lambda yF (bz_disj (aT, nT, gT, xT, yF)) end;
fun bz_combOuterAbs (aT, nT, gT) =              (* %x. Ex y. Disj (...) *)
  let val xF = Free("x_bz", natT)
  in Term.lambda xF (mkEx (bz_combInnerAbs (aT, nT, gT, xF))) end;
fun bz_comb (aT, nT, gT) = mkEx (bz_combOuterAbs (aT, nT, gT));

(* gcd body for fixed g : Conj (dvd g a)(Conj (dvd g n)(Conj (greatest)(comb))) *)
fun bz_bodyG (aT, nT, gT) =
  mkConj (dvd gT aT)
    (mkConj (dvd gT nT)
       (mkConj (bz_greatest (aT, nT, gT)) (bz_comb (aT, nT, gT))));

fun bz_bodyAbs (aT, nT) =                        (* %g. Conj (...) *)
  let val gF = Free("g_bz", natT)
  in Term.lambda gF (bz_bodyG (aT, nT, gF)) end;
fun bz_bodyEx (aT, nT) = mkEx (bz_bodyAbs (aT, nT));   (* Ex g. ... *)

(* G n = Forall (%a. bz_bodyEx(a, n)) -- the strong_induct predicate value *)
fun bz_GallAbs nT =                              (* %a. bz_bodyEx(a, n) *)
  let val aF = Free("a_BG", natT)
  in Term.lambda aF (bz_bodyEx (aF, nT)) end;
fun bz_Gprop_of nT = mkForall (bz_GallAbs nT);

val bz_GpredSI =                                 (* %n. G n *)
  let val nF = Free("n_BP", natT) in Term.lambda nF (bz_Gprop_of nF) end;

val () = out "BEZOUT_HELPERS_READY\n";

(* small helper : build the combination existential from a chosen disjunct proof *)
(* exI x, then exI y, around a Disj proof *)
fun bz_mkComb (aT, nT, gT) (xWit, yWit) hDisj =
  let
    val exInner = exI_atS2 (bz_combInnerAbs (aT, nT, gT, xWit)) yWit hDisj;  (* Ex y. Disj(...) at x=xWit *)
    val exOuter = exI_atS2 (bz_combOuterAbs (aT, nT, gT)) xWit exInner;      (* Ex x. Ex y. Disj(...) *)
  in exOuter end;

(* ============================================================================
   THE STRONG INDUCTION
   ============================================================================ *)
val bezout =
  let
    val nStep = Free("n_bz", natT);
    val mIH   = Free("m_bz", natT);
    val Gprop = Logic.all mIH (Logic.mk_implies (jT (lt mIH nStep), jT (bz_Gprop_of mIH)));
    val Hthm  = Thm.assume (ctermS2 Gprop);              (* IH : !!m. lt m n ==> jT (G m) *)
    fun applyIH mt h_lt =
      let val hAt = Thm.forall_elim (ctermS2 mt) Hthm
      in Thm.implies_elim hAt h_lt end;

    val aF = Free("a_bz", natT);
    val goalBody = bz_bodyEx (aF, nStep);               (* Ex g. ... for THIS a, THIS n *)

    val dz = dzosS_at nStep;                            (* Disj (oeq n 0) (Ex q. oeq n (Suc q)) *)

    (* ----------------------------------------------------------------
       CASE n = 0 : g := a, x := 1, y := 0.
         dvd a a, dvd a n (via dvd_zero + cong 0->n), greatest a n a,
         comb : LEFT disjunct  a*1 = (n*0) + a   (= a = 0+a = a).
       ---------------------------------------------------------------- *)
    val caseZero =
      let
        val hZ = Thm.assume (ctermS2 (jT (oeq nStep ZeroC)));   (* oeq n 0 *)
        val dvd_a_a = dvd_refl_atS2 aF;                          (* dvd a a *)
        val dvd_a_0 = dvd_zeroS_at aF;                          (* dvd a 0 *)
        val hZsym   = oeq_sym OF [hZ];                          (* oeq 0 n *)
        val dvd_a_n = dvd_cong_rS (aF, ZeroC, nStep) hZsym dvd_a_0;   (* dvd a n *)
        (* greatest a n a *)
        val (dFz, impdz) =
          let
            val dF   = Free("d_cz", natT);
            val hC   = Thm.assume (ctermS2 (jT (mkConj (dvd dF aF) (dvd dF nStep))));
            val c1   = conjunct1_atS2 (dvd dF aF, dvd dF nStep) hC;   (* dvd d a = dvd d g *)
            val metaImp = Thm.implies_intr (ctermS2 (jT (mkConj (dvd dF aF) (dvd dF nStep)))) c1;
            val objImp  = impI_atS2 (mkConj (dvd dF aF) (dvd dF nStep), dvd dF aF) metaImp;
          in (dF, objImp) end;
        val minor = Thm.forall_intr (ctermS2 dFz) impdz;
        val great = allI_atS2 (bz_greatestAbs (aF, nStep, aF)) minor;  (* greatest a n a *)
        (* comb a n a : LEFT disjunct  a*1 = (n*0) + a *)
        val lhs1   = mult1rS_at aF;                            (* (a*1) = a *)
        val n0     = mult0rS_at nStep;                         (* (n*0) = 0 *)
        val n0a    = add_cong_lS (mult nStep ZeroC, ZeroC, aF) n0;  (* (n*0 + a) = (0 + a) *)
        val zer_a  = add0S_at aF;                              (* (0 + a) = a *)
        val rhs_a  = oeq_trans OF [n0a, zer_a];                (* (n*0 + a) = a *)
        val rhs_as = oeq_sym OF [rhs_a];                       (* a = (n*0 + a) *)
        val disjEq = oeq_trans OF [lhs1, rhs_as];              (* (a*1) = (n*0 + a) *)
        val dLeft  = disjI1S2_at (oeq (mult aF oneC) (add (mult nStep ZeroC) aF),
                                  oeq (mult nStep ZeroC) (add (mult aF oneC) aF)) disjEq;
        val combT  = bz_mkComb (aF, nStep, aF) (oneC, ZeroC) dLeft;   (* comb a n a *)
        (* assemble Conj (dvd a a)(Conj (dvd a n)(Conj greatest comb)) *)
        val c3 = conjI_atS2 (bz_greatest (aF, nStep, aF), bz_comb (aF, nStep, aF)) great combT;
        val c2 = conjI_atS2 (dvd aF nStep, mkConj (bz_greatest (aF, nStep, aF)) (bz_comb (aF, nStep, aF))) dvd_a_n c3;
        val c1 = conjI_atS2 (dvd aF aF, mkConj (dvd aF nStep) (mkConj (bz_greatest (aF, nStep, aF)) (bz_comb (aF, nStep, aF)))) dvd_a_a c2;
        val exG = exI_atS2 (bz_bodyAbs (aF, nStep)) aF c1;     (* Ex g. ... = goalBody *)
      in Thm.implies_intr (ctermS2 (jT (oeq nStep ZeroC))) exG end;

    (* ----------------------------------------------------------------
       CASE n = Suc q : descent.
       ---------------------------------------------------------------- *)
    val caseSuc =
      let
        val PabsSuc = Abs("q", natT, oeq nStep (suc (Bound 0)));
        fun sucBody qWit (hSucEq : thm) =                       (* hSucEq : oeq n (Suc q) *)
          let
            (* lt 0 n *)
            val lt0Sq = lt_zero_suc_atS qWit;                   (* lt 0 (Suc q) *)
            val sucEqSym = oeq_sym OF [hSucEq];                 (* oeq (Suc q) n *)
            val ltPosPabs = Term.lambda (Free("z_lp", natT)) (lt ZeroC (Free("z_lp", natT)));
            val lt0n = oeq_rewrite_atS (ltPosPabs, suc qWit, nStep) sucEqSym lt0Sq;  (* lt 0 n *)
            (* div_mod a / n *)
            val dmEx = div_mod_atS (aF, nStep) lt0n;            (* Ex q'. Ex r. Conj(oeq a (n*q'+r))(lt r n) *)
            fun qBody qDiv (hQex : thm) =
              let
                fun rBody rDiv (hConj : thm) =
                  let
                    val eqDivP = oeq aF (add (mult nStep qDiv) rDiv);   (* a = n*q' + r *)
                    val ltRnP  = lt rDiv nStep;                        (* r < n *)
                    val hEqDiv = conjunct1_atS2 (eqDivP, ltRnP) hConj;  (* oeq a (n*q' + r) *)
                    val hLtRn  = conjunct2_atS2 (eqDivP, ltRnP) hConj;  (* lt r n *)

                    (* IH at r, then instantiate inner object-a at a' := n *)
                    val Gr     = applyIH rDiv hLtRn;                   (* Forall(%a'. bz_bodyEx(a', r)) *)
                    val GrAtN  = allE_atS2 (bz_GallAbs rDiv) nStep Gr; (* bz_bodyEx(n, r) *)

                    fun gBody gWit (hG : thm) =
                      let
                        (* hG : Conj(dvd g n)(Conj(dvd g r)(Conj(greatest n r g)(comb n r g))) *)
                        val gNd   = dvd gWit nStep;
                        val gRd   = dvd gWit rDiv;
                        val grGt  = bz_greatest (nStep, rDiv, gWit);
                        val grCb  = bz_comb (nStep, rDiv, gWit);
                        val h_g_n   = conjunct1_atS2 (gNd, mkConj gRd (mkConj grGt grCb)) hG;          (* dvd g n *)
                        val h_rest1 = conjunct2_atS2 (gNd, mkConj gRd (mkConj grGt grCb)) hG;          (* Conj(dvd g r)(Conj greatest comb) *)
                        val h_g_r   = conjunct1_atS2 (gRd, mkConj grGt grCb) h_rest1;                  (* dvd g r *)
                        val h_rest2 = conjunct2_atS2 (gRd, mkConj grGt grCb) h_rest1;                  (* Conj greatest comb *)
                        val h_great = conjunct1_atS2 (grGt, grCb) h_rest2;                             (* greatest n r g *)
                        val h_comb  = conjunct2_atS2 (grGt, grCb) h_rest2;                             (* comb n r g *)

                        (* ---- (1) g divides a ---- (same as Phase 1) *)
                        val g_nq    = dvd_mult_right_atS (gWit, nStep, qDiv) h_g_n;      (* dvd g (n*q') *)
                        val g_sum   = dvd_add_atS (gWit, mult nStep qDiv, rDiv) g_nq h_g_r;  (* dvd g (n*q'+r) *)
                        val eqSym   = oeq_sym OF [hEqDiv];                               (* oeq (n*q'+r) a *)
                        val g_a     = dvd_cong_rS (gWit, add (mult nStep qDiv) rDiv, aF) eqSym g_sum;  (* dvd g a *)

                        (* ---- (2) greatest for (a, n) ---- (same as Phase 1) *)
                        val greatAN =
                          let
                            val dF = Free("d_an", natT);
                            val hCd = Thm.assume (ctermS2 (jT (mkConj (dvd dF aF) (dvd dF nStep))));
                            val d_a = conjunct1_atS2 (dvd dF aF, dvd dF nStep) hCd;       (* dvd d a *)
                            val d_n = conjunct2_atS2 (dvd dF aF, dvd dF nStep) hCd;       (* dvd d n *)
                            val d_nq = dvd_mult_right_atS (dF, nStep, qDiv) d_n;          (* dvd d (n*q') *)
                            val d_sum = dvd_cong_rS (dF, aF, add (mult nStep qDiv) rDiv) hEqDiv d_a;  (* dvd d (n*q'+r) *)
                            val d_r   = dvd_diff_atS (dF, mult nStep qDiv, rDiv) d_nq d_sum;          (* dvd d r *)
                            val hImp  = allE_atS2 (bz_greatestAbs (nStep, rDiv, gWit)) dF h_great;    (* Imp(Conj(dvd d n)(dvd d r))(dvd d g) *)
                            val cnj   = conjI_atS2 (dvd dF nStep, dvd dF rDiv) d_n d_r;
                            val d_g   = mp_atS2 (mkConj (dvd dF nStep) (dvd dF rDiv), dvd dF gWit) hImp cnj;  (* dvd d g *)
                            val metaImp = Thm.implies_intr (ctermS2 (jT (mkConj (dvd dF aF) (dvd dF nStep)))) d_g;
                            val objImp  = impI_atS2 (mkConj (dvd dF aF) (dvd dF nStep), dvd dF gWit) metaImp;
                            val minor   = Thm.forall_intr (ctermS2 dF) objImp;
                          in allI_atS2 (bz_greatestAbs (aF, nStep, gWit)) minor end;      (* greatest a n g *)

                        (* ---- (3) THE COMBINATION : from comb(n, r, g), derive comb(a, n, g) ---- *)
                        val combAN =
                          let
                            (* starEq: a*y = n*(q'*y) + r*y   for any y, from a = n*q' + r.
                               proof: a*y = (n*q'+r)*y = (n*q')*y + r*y = n*(q'*y) + r*y *)
                            fun starEq yT =                                     (* oeq (a*y) (add (n*(q'*y)) (r*y)) *)
                              let
                                val s1 = mult_cong_lS (aF, add (mult nStep qDiv) rDiv, yT) hEqDiv;  (* (a*y) = ((n*q'+r)*y) *)
                                val s2 = rdist_at_S2 (mult nStep qDiv, rDiv, yT);                   (* ((n*q'+r)*y) = ((n*q')*y + r*y) *)
                                val s3 = mult_assoc_atS (nStep, qDiv, yT);                          (* ((n*q')*y) = (n*(q'*y)) *)
                                val s3l= add_cong_lS (mult (mult nStep qDiv) yT, mult nStep (mult qDiv yT), mult rDiv yT) s3;
                                                                                                   (* ((n*q')*y + r*y) = (n*(q'*y) + r*y) *)
                                val t1 = oeq_trans OF [s1, s2];                 (* (a*y) = ((n*q')*y + r*y) *)
                                val t2 = oeq_trans OF [t1, s3l];                (* (a*y) = (n*(q'*y) + r*y) *)
                              in t2 end;

                            (* the comb(n,r,g) existential : Ex x'. Ex y'. Disj (n*x'=r*y'+g)(r*y'=n*x'+g) *)
                            fun combOuterBody xpW (hExY : thm) =
                              let
                                fun combInnerBody ypW (hDisj : thm) =
                                  let
                                    (* the two IH disjuncts *)
                                    val dL = oeq (mult nStep xpW) (add (mult rDiv ypW) gWit);   (* n*x' = r*y' + g *)
                                    val dR = oeq (mult rDiv ypW) (add (mult nStep xpW) gWit);   (* r*y' = n*x' + g *)

                                    (* targets for comb(a,n,g) *)
                                    fun aDisjL (xT, yT) = oeq (mult aF xT) (add (mult nStep yT) gWit);  (* a*X = n*Y + g  (LEFT) *)
                                    fun aDisjR (xT, yT) = oeq (mult nStep yT) (add (mult aF xT) gWit);  (* n*Y = a*X + g  (RIGHT) *)

                                    (* ===== CASE IH-LEFT : n*x' = r*y' + g  ====>  RIGHT disjunct for (a,n)
                                       X := y', Y := x' + q'*y'.
                                       Show n*(x' + q'*y') = a*y' + g.
                                         LHS = n*x' + n*(q'*y')                 [left_distrib]
                                             = (r*y'+g) + n*(q'*y')             [subst dL]
                                             = n*(q'*y') + r*y' + g             [add comm/assoc]
                                             = a*y' + g                         [starEq y' backwards]  *)
                                    val caseL =
                                      let
                                        val hL  = Thm.assume (ctermS2 (jT dL));    (* n*x' = r*y' + g *)
                                        val Yt = add xpW (mult qDiv ypW);
                                        (* LHS expand : n*(x'+q'*y') = n*x' + n*(q'*y') *)
                                        val ld  = left_distrib_atS (nStep, xpW, mult qDiv ypW);  (* n*(x'+q'y') = n*x' + n*(q'y') *)
                                        (* subst n*x' = r*y'+g *)
                                        val sb  = add_cong_lS (mult nStep xpW, add (mult rDiv ypW) gWit, mult nStep (mult qDiv ypW)) hL;
                                                  (* (n*x' + n*(q'y')) = ((r*y'+g) + n*(q'y')) *)
                                        val e1  = oeq_trans OF [ld, sb];  (* n*(x'+q'y') = ((r*y'+g) + n*(q'y')) *)
                                        (* rearrange ((r*y'+g) + n*(q'y')) = (n*(q'y') + r*y') + g
                                           step a: (r*y'+g) + n*(q'y') = n*(q'y') + (r*y'+g)   [comm]
                                           step b: n*(q'y') + (r*y'+g) = (n*(q'y') + r*y') + g  [assoc backwards] *)
                                        val cm  = addcommS_at (add (mult rDiv ypW) gWit, mult nStep (mult qDiv ypW));
                                                  (* ((r*y'+g) + n*(q'y')) = (n*(q'y') + (r*y'+g)) *)
                                        val asc = addassocS_at (mult nStep (mult qDiv ypW), mult rDiv ypW, gWit);
                                                  (* ((n*(q'y') + r*y') + g) = (n*(q'y') + (r*y' + g)) *)
                                        val ascS= oeq_sym OF [asc];  (* (n*(q'y') + (r*y'+g)) = ((n*(q'y') + r*y') + g) *)
                                        val e2  = oeq_trans OF [e1, cm];   (* n*(x'+q'y') = (n*(q'y') + (r*y'+g)) *)
                                        val e3  = oeq_trans OF [e2, ascS]; (* n*(x'+q'y') = ((n*(q'y') + r*y') + g) *)
                                        (* a*y' = n*(q'y') + r*y'  [starEq y']  =>  (n*(q'y') + r*y') = a*y'  *)
                                        val st  = starEq ypW;              (* a*y' = (n*(q'y') + r*y') *)
                                        val stS = oeq_sym OF [st];         (* (n*(q'y') + r*y') = a*y' *)
                                        val stL = add_cong_lS (add (mult nStep (mult qDiv ypW)) (mult rDiv ypW), mult aF ypW, gWit) stS;
                                                  (* ((n*(q'y') + r*y') + g) = (a*y' + g) *)
                                        val e4  = oeq_trans OF [e3, stL];  (* n*(x'+q'y') = (a*y' + g) *)
                                        (* this is aDisjR (X:=y', Y:=x'+q'y') :  oeq (n*Y) (a*X + g) *)
                                        val dR_an = disjI2S2_at (aDisjL (ypW, Yt), aDisjR (ypW, Yt)) e4;
                                        val combRes = bz_mkComb (aF, nStep, gWit) (ypW, Yt) dR_an;
                                      in Thm.implies_intr (ctermS2 (jT dL)) combRes end;

                                    (* ===== CASE IH-RIGHT : r*y' = n*x' + g  ====>  LEFT disjunct for (a,n)
                                       X := y', Y := q'*y' + x'.
                                       Show a*y' = n*(q'*y' + x') + g.
                                         a*y' = n*(q'*y') + r*y'             [starEq y']
                                              = n*(q'*y') + (n*x' + g)       [subst dR]
                                              = (n*(q'*y') + n*x') + g       [assoc]
                                              = n*(q'*y' + x') + g           [left_distrib backwards] *)
                                    val caseR =
                                      let
                                        val hR  = Thm.assume (ctermS2 (jT dR));    (* r*y' = n*x' + g *)
                                        val Yt = add (mult qDiv ypW) xpW;
                                        val st  = starEq ypW;              (* a*y' = (n*(q'y') + r*y') *)
                                        (* subst r*y' = n*x' + g *)
                                        val sb  = add_cong_rS (mult nStep (mult qDiv ypW), mult rDiv ypW, add (mult nStep xpW) gWit) hR;
                                                  (* (n*(q'y') + r*y') = (n*(q'y') + (n*x' + g)) *)
                                        val e1  = oeq_trans OF [st, sb];   (* a*y' = (n*(q'y') + (n*x' + g)) *)
                                        (* assoc : (n*(q'y') + (n*x' + g)) = ((n*(q'y') + n*x') + g) *)
                                        val asc = addassocS_at (mult nStep (mult qDiv ypW), mult nStep xpW, gWit);
                                                  (* ((n*(q'y') + n*x') + g) = (n*(q'y') + (n*x' + g)) *)
                                        val ascS= oeq_sym OF [asc];  (* (n*(q'y') + (n*x' + g)) = ((n*(q'y') + n*x') + g) *)
                                        val e2  = oeq_trans OF [e1, ascS]; (* a*y' = ((n*(q'y') + n*x') + g) *)
                                        (* left_distrib backwards : n*(q'y'+x') = n*(q'y') + n*x'  =>  reverse  *)
                                        val ld  = left_distrib_atS (nStep, mult qDiv ypW, xpW);  (* n*(q'y'+x') = (n*(q'y') + n*x') *)
                                        val ldS = oeq_sym OF [ld];  (* (n*(q'y') + n*x') = n*(q'y'+x') *)
                                        val ldL = add_cong_lS (add (mult nStep (mult qDiv ypW)) (mult nStep xpW), mult nStep Yt, gWit) ldS;
                                                  (* ((n*(q'y') + n*x') + g) = (n*(q'y'+x') + g) *)
                                        val e3  = oeq_trans OF [e2, ldL];  (* a*y' = (n*(q'y'+x') + g) = (n*Y + g) *)
                                        (* this is aDisjL (X:=y', Y:=q'y'+x') : oeq (a*X) (n*Y + g) *)
                                        val dL_an = disjI1S2_at (aDisjL (ypW, Yt), aDisjR (ypW, Yt)) e3;
                                        val combRes = bz_mkComb (aF, nStep, gWit) (ypW, Yt) dL_an;
                                      in Thm.implies_intr (ctermS2 (jT dR)) combRes end;

                                    val combRes = disjE_elimS2 (dL, dR, bz_comb (aF, nStep, gWit)) hDisj caseL caseR;
                                  in combRes end;
                                val g = exE_elimS2 (bz_combInnerAbs (nStep, rDiv, gWit, xpW), bz_comb (aF, nStep, gWit)) hExY "y_w" combInnerBody;
                              in g end;
                            val g = exE_elimS2 (bz_combOuterAbs (nStep, rDiv, gWit), bz_comb (aF, nStep, gWit)) h_comb "x_w" combOuterBody;
                          in g end;

                        (* assemble Conj (dvd g a)(Conj (dvd g n)(Conj greatest comb)) *)
                        val c3 = conjI_atS2 (bz_greatest (aF, nStep, gWit), bz_comb (aF, nStep, gWit)) greatAN combAN;
                        val c2 = conjI_atS2 (dvd gWit nStep, mkConj (bz_greatest (aF, nStep, gWit)) (bz_comb (aF, nStep, gWit))) h_g_n c3;
                        val c1 = conjI_atS2 (dvd gWit aF, mkConj (dvd gWit nStep) (mkConj (bz_greatest (aF, nStep, gWit)) (bz_comb (aF, nStep, gWit)))) g_a c2;
                        val exG = exI_atS2 (bz_bodyAbs (aF, nStep)) gWit c1;     (* goalBody *)
                      in exG end;
                    val g = exE_elimS2 (bz_bodyAbs (nStep, rDiv), goalBody) GrAtN "g_w" gBody;
                  in g end;
                val g = exE_elimS2 (innerDivAbsN nStep aF qDiv, goalBody) hQex "r_w" rBody;
              in g end;
            val g = exE_elimS2 (rmDivBodyN nStep aF, goalBody) dmEx "q_w" qBody;
          in g end;
        val gg = exE_elimS2 (PabsSuc, goalBody) (Thm.assume (ctermS2 (jT (mkEx PabsSuc)))) "q_sw" sucBody;
      in Thm.implies_intr (ctermS2 (jT (mkEx PabsSuc))) gg end;

    (* combine the two cases *)
    val bodyProof = disjE_elimS2 (oeq nStep ZeroC, mkExSuc nStep, goalBody) dz caseZero caseSuc;
    val minorA = Thm.forall_intr (ctermS2 aF) bodyProof;
    val GnThm  = allI_atS2 (bz_GallAbs nStep) minorA;     (* jT (G n) *)

    val stepThm = Thm.forall_intr (ctermS2 nStep) (Thm.implies_intr (ctermS2 Gprop) GnThm);

    val bK = Free("b", natT);
    val siInst = beta_norm (Drule.infer_instantiate ctxtS2
                   [(("P",0), ctermS2 bz_GpredSI), (("k",0), ctermS2 bK)] (varify strong_induct));
    val Gb = Thm.implies_elim siInst stepThm;             (* jT (G b) *)
    val aK   = Free("a", natT);
    val bodyAB = allE_atS2 (bz_GallAbs bK) aK Gb;         (* jT (bz_bodyEx(a, b)) *)
  in varify bodyAB end;

val () = out "BEZOUT_PROVED\n";

(* ============================================================================
   VALIDATION : 0-hyp AND aconv the intended schematic goal, built the SAME way.
   ============================================================================ *)
val aVb = Var (("a",0), natT);
val bVb = Var (("b",0), natT);
val bezout_intended = jT (bz_bodyEx (aVb, bVb));

val r_bez = checkS2 ("bezout", bezout, bezout_intended);
val () = if r_bez then out "OK bezout\n" else out "FAIL bezout\n";

(* ---- SOUNDNESS PROBE : kernel must REJECT a false variant ----
   Dropping the combination conjunct makes it the weaker Phase-1 statement;
   the proved theorem must NOT be aconv that weakened statement. *)
val probe_bez =
  let
    fun bodyAbsW (aT, nT) =
      let val gF = Free("g_pw", natT)
      in Term.lambda gF (mkConj (dvd gF aT)
                          (mkConj (dvd gF nT) (bz_greatest (aT, nT, gF)))) end;   (* drops comb *)
    val bogus = jT (mkEx (bodyAbsW (aVb, bVb)));
  in not ((Thm.prop_of bezout) aconv bogus) end;

val () =
  if r_bez andalso probe_bez
  then out "PROBE_OK\n"
  else out "PROBE_UNSOUND\n";

val () = if r_bez andalso probe_bez then out "BEZOUT_OK\n" else out "BEZOUT_FAILED\n";
(* ============================================================================
   PHASE 3 : coprime_bezout  (seat crt0)
   ----------------------------------------------------------------------------
   PRIMARY GOAL.  Prove (meta over a,b):
     !!a b. jT (Forall (%d. Imp (Conj (dvd d a)(dvd d b)) (oeq d 1)))
             ==> jT (Ex x. Ex y.
                       Disj (oeq (mult a x) (add (mult b y) 1))
                            (oeq (mult b y) (add (mult a x) 1)))

   COROLLARY of bezout (Phase 2): from bezout get g with
     greatest a b g  and  comb a b g = Ex x. Ex y. Disj (a*x = b*y+g)(b*y = a*x+g).
   g divides a and g divides b (the first two conjuncts), so the coprimality
   hypothesis applied to g gives g = 1; substitute g = 1 into the combination.
   ============================================================================ *)
val () = out "COPRIME_BEZOUT_BEGIN\n";

(* ---- the coprime-coefficient goal's term builders (g replaced by 1) ---- *)
(* one-sided disjunction at fixed x,y, target is 1 not g *)
fun cb_disj (aT, bT, xT, yT) =
  mkDisj (oeq (mult aT xT) (add (mult bT yT) oneC))
         (oeq (mult bT yT) (add (mult aT xT) oneC));

fun cb_innerAbs (aT, bT, xT) =                 (* %y. Disj (...) *)
  let val yF = Free("y_cb", natT)
  in Term.lambda yF (cb_disj (aT, bT, xT, yF)) end;
fun cb_outerAbs (aT, bT) =                      (* %x. Ex y. Disj (...) *)
  let val xF = Free("x_cb", natT)
  in Term.lambda xF (mkEx (cb_innerAbs (aT, bT, xF))) end;
fun cb_goal (aT, bT) = mkEx (cb_outerAbs (aT, bT));   (* Ex x. Ex y. Disj(...) *)

(* exI x, then exI y, around a Disj proof matching cb_disj *)
fun cb_mkGoal (aT, bT) (xWit, yWit) hDisj =
  let
    val exInner = exI_atS2 (cb_innerAbs (aT, bT, xWit)) yWit hDisj;
    val exOuter = exI_atS2 (cb_outerAbs (aT, bT)) xWit exInner;
  in exOuter end;

(* the coprime hypothesis predicate : %d. Imp (Conj (dvd d a)(dvd d b)) (oeq d 1) *)
fun cb_copAbs (aT, bT) =
  let val dF = Free("d_cop", natT)
  in Term.lambda dF (mkImp (mkConj (dvd dF aT) (dvd dF bT)) (oeq dF oneC)) end;
fun cb_cop (aT, bT) = mkForall (cb_copAbs (aT, bT));

val () = out "COPRIME_BEZOUT_HELPERS_READY\n";

val coprime_bezout =
  let
    val aF = Free("a", natT);
    val bF = Free("b", natT);

    (* assume the coprimality hypothesis *)
    val copP  = jT (cb_cop (aF, bF));
    val hCop  = Thm.assume (ctermS2 copP);

    (* instantiate bezout at a := aF, b := bF *)
    val bezAB = beta_norm (Drule.infer_instantiate ctxtS2
                  [(("a",0), ctermS2 aF), (("b",0), ctermS2 bF)] bezout);   (* jT (bz_bodyEx(a,b)) *)

    (* exE the gcd witness g, then build the goal *)
    val goalC = cb_goal (aF, bF);
    fun gBody gWit (hG : thm) =
      let
        (* hG : Conj (dvd g a)(Conj (dvd g b)(Conj (greatest a b g)(comb a b g))) *)
        val gAd  = dvd gWit aF;
        val gBd  = dvd gWit bF;
        val grGt = bz_greatest (aF, bF, gWit);
        val grCb = bz_comb (aF, bF, gWit);
        val h_g_a   = conjunct1_atS2 (gAd, mkConj gBd (mkConj grGt grCb)) hG;        (* dvd g a *)
        val h_rest1 = conjunct2_atS2 (gAd, mkConj gBd (mkConj grGt grCb)) hG;        (* Conj(dvd g b)(Conj greatest comb) *)
        val h_g_b   = conjunct1_atS2 (gBd, mkConj grGt grCb) h_rest1;                (* dvd g b *)
        val h_rest2 = conjunct2_atS2 (gBd, mkConj grGt grCb) h_rest1;                (* Conj greatest comb *)
        val h_comb  = conjunct2_atS2 (grGt, grCb) h_rest2;                           (* comb a b g *)

        (* coprimality at g : Imp (Conj (dvd g a)(dvd g b)) (oeq g 1) *)
        val hImp = allE_atS2 (cb_copAbs (aF, bF)) gWit hCop;                         (* Imp(Conj(dvd g a)(dvd g b))(oeq g 1) *)
        val hCnj = conjI_atS2 (dvd gWit aF, dvd gWit bF) h_g_a h_g_b;                (* Conj(dvd g a)(dvd g b) *)
        val hg1  = mp_atS2 (mkConj (dvd gWit aF) (dvd gWit bF), oeq gWit oneC) hImp hCnj;  (* oeq g 1 *)

        (* exE the combination : Ex x. Ex y. Disj (a*x = b*y+g)(b*y = a*x+g) *)
        fun combOuterBody xpW (hExY : thm) =
          let
            fun combInnerBody ypW (hDisj : thm) =
              let
                (* the two bezout disjuncts (with g) *)
                val dL = oeq (mult aF xpW) (add (mult bF ypW) gWit);   (* a*x = b*y + g *)
                val dR = oeq (mult bF ypW) (add (mult aF xpW) gWit);   (* b*y = a*x + g *)

                (* target disjuncts (with 1) *)
                val tL = oeq (mult aF xpW) (add (mult bF ypW) oneC);   (* a*x = b*y + 1 *)
                val tR = oeq (mult bF ypW) (add (mult aF xpW) oneC);   (* b*y = a*x + 1 *)

                (* CASE LEFT : a*x = b*y + g.  Rewrite g -> 1 :
                     (b*y + g) = (b*y + 1)  by add_cong_rS (b*y, g, 1) hg1
                     then a*x = (b*y + 1) by trans. *)
                val caseL =
                  let
                    val hL   = Thm.assume (ctermS2 (jT dL));            (* a*x = b*y + g *)
                    val rw   = add_cong_rS (mult bF ypW, gWit, oneC) hg1;  (* (b*y + g) = (b*y + 1) *)
                    val eqT  = oeq_trans OF [hL, rw];                   (* a*x = (b*y + 1) = tL *)
                    val dLeft= disjI1S2_at (tL, tR) eqT;
                    val res  = cb_mkGoal (aF, bF) (xpW, ypW) dLeft;
                  in Thm.implies_intr (ctermS2 (jT dL)) res end;

                (* CASE RIGHT : b*y = a*x + g.  Same rewrite on the right summand. *)
                val caseR =
                  let
                    val hR   = Thm.assume (ctermS2 (jT dR));            (* b*y = a*x + g *)
                    val rw   = add_cong_rS (mult aF xpW, gWit, oneC) hg1;  (* (a*x + g) = (a*x + 1) *)
                    val eqT  = oeq_trans OF [hR, rw];                   (* b*y = (a*x + 1) = tR *)
                    val dRight = disjI2S2_at (tL, tR) eqT;
                    val res  = cb_mkGoal (aF, bF) (xpW, ypW) dRight;
                  in Thm.implies_intr (ctermS2 (jT dR)) res end;

                val res = disjE_elimS2 (dL, dR, goalC) hDisj caseL caseR;
              in res end;
            val g = exE_elimS2 (bz_combInnerAbs (aF, bF, gWit, xpW), goalC) hExY "y_cw" combInnerBody;
          in g end;
        val g = exE_elimS2 (bz_combOuterAbs (aF, bF, gWit), goalC) h_comb "x_cw" combOuterBody;
      in g end;
    val bodyGoal = exE_elimS2 (bz_bodyAbs (aF, bF), goalC) bezAB "g_cw" gBody;
    (* discharge the coprimality hypothesis -> meta implication *)
    val disch = Thm.implies_intr (ctermS2 copP) bodyGoal;
  in varify disch end;

val () = out "COPRIME_BEZOUT_PROVED\n";

(* ============================================================================
   VALIDATION : 0-hyp AND aconv the intended schematic goal, built the SAME way.
     intended := jT (cop a b) ==> jT (cb_goal a b)   with a,b schematic Vars.
   ============================================================================ *)
val aVcb = Var (("a",0), natT);
val bVcb = Var (("b",0), natT);
val coprime_bezout_intended =
  Logic.mk_implies (jT (cb_cop (aVcb, bVcb)), jT (cb_goal (aVcb, bVcb)));

val r_cb = checkS2 ("coprime_bezout", coprime_bezout, coprime_bezout_intended);
val () = if r_cb then out "OK coprime_bezout\n" else out "FAIL coprime_bezout\n";

(* ---- SOUNDNESS PROBE : kernel must REJECT a false variant ----
   Dropping the coprimality hypothesis would assert that EVERY a,b have x,y
   with a*x = b*y+1 OR b*y = a*x+1 (false: a=b=0).  The proved theorem must NOT
   be aconv that hypothesis-free statement. *)
val probe_cb =
  let
    val bogus = jT (cb_goal (aVcb, bVcb));   (* drops the cop hypothesis entirely *)
  in not ((Thm.prop_of coprime_bezout) aconv bogus) end;

val () =
  if r_cb andalso probe_cb
  then out "PROBE_OK\n"
  else out "PROBE_UNSOUND\n";

val () =
  if r_cb andalso probe_cb
  then out "COPRIME_BEZOUT_OK\n"
  else out "COPRIME_BEZOUT_FAILED\n";

(* ============================================================================
   STRETCH GOAL : modular inverse for a prime  (seat crt0)
   ----------------------------------------------------------------------------
     !!p a. jT (prime2 p) ==> jT (neg (dvd p a))
              ==> jT (Ex b. cong p (mult a b) 1)
   Strategy : prime p + ~(p|a) make a,p coprime; coprime_bezout(a,p) gives x,y
   with (a*x = p*y+1)  OR  (p*y = a*x+1).
     - LEFT  : a*x = p*y+1  =>  a*x = 1 + p*y  (comm)  => cong p (a*x) 1 via congR.
               witness b := x.
     - RIGHT : p*y = a*x+1  =>  a*x = -1 (mod p)  => choose b := x*(a*x), so
               a*b = (a*x)^2 = 1 + p*M (M from le y ((a*x)*y)); cong via congR.
   ============================================================================ *)
val () = out "MOD_INVERSE_BEGIN\n";

(* lift the base lemmas we need onto ctxtS2 (schematic).
   NOTE: we use the CAPTURE-AVOIDING structural prime `prime2` (base line 2810):
     prime2 p = Conj (lt 1 p) (Forall (ppAbs p)),
   whose destructors we inline via conjunct1/2 + the base `ppAbs`.  The phase-2
   `prime`/`prime_div` use a de-Bruijn-malformed predicate (the inner dvd reads
   `Ex k. p = k*k`), so we do NOT use them. *)
val ne0_suc_vS   = varify ne0_suc;          (* jT (neg (oeq d 0)) ==> jT (Ex m. oeq d (Suc m)) *)
val mult_Suc_vS  = varify mult_Suc;         (* jT (oeq (mult (Suc m) n) (add n (mult m n))) *)

fun ne0_suc_atS dt hne =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2 [(("d",0), ctermS2 dt)] ne0_suc_vS)
  in Thm.implies_elim inst hne end;
fun mult_Suc_atS (mt, nt) = beta_norm (Drule.infer_instantiate ctxtS2
      [(("m",0), ctermS2 mt), (("n",0), ctermS2 nt)] mult_Suc_vS);

(* prime2 destructors on ctxtS2 *)
fun prime2_gt1 pt hprime = conjunct1_atS2 (lt (suc ZeroC) pt, mkForall (ppAbs pt)) hprime;  (* lt 1 p *)
fun prime2_div pt hprime = conjunct2_atS2 (lt (suc ZeroC) pt, mkForall (ppAbs pt)) hprime;  (* Forall (ppAbs p) *)

val () = out "MOD_INVERSE_HELPERS_READY\n";

(* prime predicate body abstraction = base ppAbs (capture-avoiding) *)
val primeBodyAbs = ppAbs;

(* goal-existential builder : Ex b. cong p (mult a b) 1 *)
fun mi_innerAbs (pt, at) =
  let val bF = Free("b_mi", natT)
  in Term.lambda bF (cong pt (mult at bF) oneC) end;
fun mi_goal (pt, at) = mkEx (mi_innerAbs (pt, at));
fun mi_mkGoal (pt, at) bWit hcong =
  exI_atS2 (mi_innerAbs (pt, at)) bWit hcong;

val mod_inverse =
  let
    val pF = Free("p", natT);
    val aF = Free("a", natT);
    val hPrime = Thm.assume (ctermS2 (jT (prime2 pF)));
    val hNdvdP = jT (neg (dvd pF aF));                       (* Imp (dvd p a) oFalse *)
    val hNdvd  = Thm.assume (ctermS2 hNdvdP);

    (* ---- STEP 1 : coprimality  Hcop : Forall (%d. Imp (Conj (dvd d a)(dvd d p))(oeq d 1)) ---- *)
    val Hcop =
      let
        val dF = Free("d_cp", natT);
        (* assume Conj (dvd d a)(dvd d p) *)
        val cnjP = jT (mkConj (dvd dF aF) (dvd dF pF));
        val hCnj = Thm.assume (ctermS2 cnjP);
        val dda  = conjunct1_atS2 (dvd dF aF, dvd dF pF) hCnj;     (* dvd d a *)
        val ddp  = conjunct2_atS2 (dvd dF aF, dvd dF pF) hCnj;     (* dvd d p *)
        (* prime_div : Forall (%d. Imp (dvd d p)(Disj (oeq d 1)(oeq d p))) *)
        val pdiv = prime2_div pF hPrime;
        val hImp = allE_atS2 (primeBodyAbs pF) dF pdiv;            (* Imp (dvd d p)(Disj (oeq d 1)(oeq d p)) *)
        val hDisj= mp_atS2 (dvd dF pF, mkDisj (oeq dF oneC) (oeq dF pF)) hImp ddp;  (* Disj (oeq d 1)(oeq d p) *)
        (* disjE -> oeq d 1 *)
        val caseEq1 =
          let val h = Thm.assume (ctermS2 (jT (oeq dF oneC)))
          in Thm.implies_intr (ctermS2 (jT (oeq dF oneC))) h end;
        val caseEqP =
          let
            val h   = Thm.assume (ctermS2 (jT (oeq dF pF)));       (* oeq d p *)
            (* build dvd p a from dvd d a + oeq d p : exE k, oeq a (mult d k), rewrite d->p *)
            val ddaAbs = Abs("k", natT, oeq aF (mult dF (Bound 0)));
            fun kbody kW (hk : thm) =                              (* hk : oeq a (mult d k) *)
              let
                val cong_dk = mult_cong_lS (dF, pF, kW) h;         (* oeq (mult d k)(mult p k) *)
                val a_pk    = oeq_trans OF [hk, cong_dk];          (* oeq a (mult p k) *)
                val dpa     = dvd_introS (pF, aF, kW) a_pk;        (* dvd p a *)
                val fAls    = mp_atS2 (dvd pF aF, oFalseC) hNdvd dpa;  (* oFalse *)
                val any     = oFalse_elimS_at (oeq dF oneC) ;      (* jT oFalse ==> jT (oeq d 1) *)
              in Thm.implies_elim any fAls end;
            val concl = exE_elimS2 (ddaAbs, oeq dF oneC) dda "k_cp" kbody;  (* oeq d 1 *)
          in Thm.implies_intr (ctermS2 (jT (oeq dF pF))) concl end;
        val res = disjE_elimS2 (oeq dF oneC, oeq dF pF, oeq dF oneC) hDisj caseEq1 caseEqP;
        (* discharge Conj, impI, allI *)
        val metaImp = Thm.implies_intr (ctermS2 cnjP) res;
        val objImp  = impI_atS2 (mkConj (dvd dF aF) (dvd dF pF), oeq dF oneC) metaImp;
        val minor   = Thm.forall_intr (ctermS2 dF) objImp;
      in allI_atS2 (cb_copAbs (aF, pF)) minor end;                (* Forall (%d. Imp (Conj (dvd d a)(dvd d p))(oeq d 1)) *)

    (* ---- STEP 2 : apply coprime_bezout at a := a, b := p ---- *)
    val cbInst = beta_norm (Drule.infer_instantiate ctxtS2
                   [(("a",0), ctermS2 aF), (("b",0), ctermS2 pF)] coprime_bezout);
    val cbDisjEx = Thm.implies_elim cbInst Hcop;                  (* Ex x. Ex y. Disj (a*x = p*y+1)(p*y = a*x+1) *)

    val goalC = mi_goal (pF, aF);

    fun xbody xW (hExY : thm) =
      let
        fun ybody yW (hDisj : thm) =
          let
            val ax = mult aF xW;                                  (* a*x *)
            (* the two bezout disjuncts (b := p) *)
            val dL = oeq ax (add (mult pF yW) oneC);              (* a*x = p*y + 1 *)
            val dR = oeq (mult pF yW) (add ax oneC);              (* p*y = a*x + 1 *)

            (* ===== CASE LEFT : a*x = p*y + 1.  Witness b := x. ===== *)
            val caseL =
              let
                val hL = Thm.assume (ctermS2 (jT dL));            (* a*x = p*y + 1 *)
                (* want congR p (a*x) 1 : Ex k. oeq (a*x) (add 1 (mult p k)), witness k := y *)
                val cm = addcommS_at (mult pF yW, oneC);          (* (p*y + 1) = (1 + p*y) *)
                val axeq = oeq_trans OF [hL, cm];                 (* a*x = (1 + p*y) *)
                (* congR body at k=y is  oeq (a*x) (add 1 (mult p y)) -- matches axeq *)
                val congRabs = Abs("k", natT, oeq ax (add oneC (mult pF (Bound 0))));
                val exCongR  = exI_atS2 congRabs yW axeq;         (* congR p (a*x) 1 *)
                (* cong p (a*x) 1 = Disj (congL ..)(congR ..) ; use disjI2 *)
                val hcong    = disjI2S2_at (congL pF ax oneC, congR pF ax oneC) exCongR;
                val res      = mi_mkGoal (pF, aF) xW hcong;       (* Ex b. cong p (a*b) 1, b := x *)
              in Thm.implies_intr (ctermS2 (jT dL)) res end;

            (* ===== CASE RIGHT : p*y = a*x + 1.  Witness b := x*(a*x). ===== *)
            val caseR =
              let
                val hR = Thm.assume (ctermS2 (jT dR));            (* p*y = a*x + 1 *)
                val sq = mult ax ax;                              (* (a*x)^2 *)
                val Q  = mult ax yW;                              (* (a*x)*y *)
                val bWit = mult xW ax;                            (* x*(a*x) *)

                (* eq_ab : oeq (mult a bWit) sq    [ a*(x*ax) = (a*x)*ax = ax*ax ]
                   mult_assoc gives  sq = (a*x)*ax = a*(x*ax) = a*bWit, so SYM it. *)
                val eq_ab = oeq_sym OF [mult_assoc_atS (aF, xW, ax)];   (* a*bWit = sq *)

                (* (i) : oeq (add sq ax) (mult p Q) *)
                (* c1 : ax*(p*y) = ax*(a*x+1) *)
                val c1 = mult_cong_rS (ax, mult pF yW, add ax oneC) hR;
                (* LHS chain : ax*(p*y) -> p*Q *)
                val l1 = oeq_sym OF [mult_assoc_atS (ax, pF, yW)]; (* ax*(p*y) = (ax*p)*y *)
                val l2 = mult_cong_lS (mult ax pF, mult pF ax, yW) (mult_comm_atS (ax, pF)); (* (ax*p)*y = (p*ax)*y *)
                val l3 = mult_assoc_atS (pF, ax, yW);             (* (p*ax)*y = p*(ax*y) = p*Q *)
                val lLHS = oeq_trans OF [oeq_trans OF [l1, l2], l3];  (* ax*(p*y) = p*Q *)
                (* RHS chain : ax*(ax+1) -> sq + ax *)
                val r1 = left_distrib_atS (ax, ax, oneC);         (* ax*(ax+1) = ax*ax + ax*1 *)
                val r2 = mult1rS_at ax;                           (* ax*1 = ax *)
                val r2c= add_cong_rS (mult ax ax, mult ax oneC, ax) r2;  (* (ax*ax + ax*1) = (ax*ax + ax) = (sq+ax) *)
                val rRHS = oeq_trans OF [r1, r2c];                (* ax*(ax+1) = sq+ax *)
                (* combine : p*Q = sq+ax  =>  sq+ax = p*Q *)
                val pQ_eq = oeq_trans OF [oeq_trans OF [oeq_sym OF [lLHS], c1], rRHS];  (* p*Q = sq+ax *)
                val iEq   = oeq_sym OF [pQ_eq];                   (* (i) : sq+ax = p*Q *)

                (* ---- ax != 0 (else p*y = 1, with y>=1, p>=2 -> contra). We instead
                        prove ax = Suc k via ne0_suc on (neg (oeq ax 0)). ---- *)
                (* neg (oeq ax 0) : assume oeq ax 0, derive oFalse *)
                val axne0 =
                  let
                    val hz = Thm.assume (ctermS2 (jT (oeq ax ZeroC)));  (* ax = 0 *)
                    (* p*y = ax + 1 = 0 + 1 = 1  via hR + rewrite ax->0 *)
                    val rw = add_cong_lS (ax, ZeroC, oneC) hz;     (* (ax + 1) = (0 + 1) *)
                    val z1 = add0S_at oneC;                        (* (0 + 1) = 1 *)
                    val py1 = oeq_trans OF [oeq_trans OF [hR, rw], z1];  (* p*y = 1 = Suc 0 *)
                    (* p divides p*y = 1 ; but dvd p 1 forces p <= 1 (dvd_le),
                       contradicting prime p's 1 < p. *)
                    val dvdp_py = dvd_introS (pF, mult pF yW, yW) (oeqreflS_at (mult pF yW)); (* dvd p (p*y) *)
                    val dvdp_1  = dvd_cong_rS (pF, mult pF yW, oneC) py1 dvdp_py;  (* dvd p 1 *)
                    (* dvd p 1 and 1 != 0 -> le p 1 (dvd_le) *)
                    val one_ne0 =
                      let val h00 = Thm.assume (ctermS2 (jT (oeq oneC ZeroC)))
                      in Thm.implies_intr (ctermS2 (jT (oeq oneC ZeroC))) (Suc_neq_Zero_atS ZeroC OF [h00]) end;
                    val le_p_1  = dvd_le_atS (pF, oneC) dvdp_1 one_ne0;  (* le p 1 *)
                    (* prime p -> lt 1 p = le 2 p ; le p 1 and le 2 p -> le 2 1 (trans) -> contra *)
                    val gt1     = prime2_gt1 pF hPrime;              (* lt 1 p = le 2 p *)
                    val le2_1   = le_trans_atS (suc oneC, pF, oneC) gt1 le_p_1;  (* le (Suc 1) 1 = lt 1 1 *)
                    val contra  = lt_irrefl_atS oneC le2_1;          (* oFalse *)
                    val metaNe  = Thm.implies_intr (ctermS2 (jT (oeq ax ZeroC))) contra;  (* jT(oeq ax 0) ==> jT oFalse *)
                  in impI_atS2 (oeq ax ZeroC, oFalseC) metaNe end;   (* jT (neg (oeq ax 0)) = jT (Imp (oeq ax 0) oFalse) *)

                (* ax = Suc k0 *)
                val axSucEx = ne0_suc_atS ax axne0;               (* Ex m. oeq ax (Suc m) *)
                fun axSucBody k0 (hk0 : thm) =                    (* hk0 : oeq ax (Suc k0) *)
                  let
                    (* le y Q  where Q = ax*y = (Suc k0)*y = y + k0*y  via mult_Suc -> le_add *)
                    val ms   = mult_Suc_atS (k0, yW);             (* (Suc k0)*y = y + k0*y *)
                    (* Q = ax*y ; rewrite ax = Suc k0 : ax*y = (Suc k0)*y *)
                    val qcong= mult_cong_lS (ax, suc k0, yW) hk0; (* ax*y = (Suc k0)*y *)
                    val qEq  = oeq_trans OF [qcong, ms];          (* Q = (y + k0*y) *)
                    val leY  = le_add_atS (yW, mult k0 yW);       (* le y (y + k0*y) *)
                    (* rewrite (y + k0*y) back to Q : le y Q. *)
                    val qEqs = oeq_sym OF [qEq];                  (* (y+k0*y) = Q *)
                    val lePabs = Term.lambda (Free("z_le", natT)) (le yW (Free("z_le", natT)));
                    val leYQ = oeq_rewrite_atS (lePabs, add yW (mult k0 yW), Q) qEqs leY;  (* le y Q *)
                    (* le y Q = Ex M. oeq Q (add y M).  exE M : oeq Q (add y M) *)
                    val leAbs = Abs("p", natT, oeq Q (add yW (Bound 0)));
                    fun mbody mW (hm : thm) =                     (* hm : oeq Q (add y M) *)
                      let
                        (* star-eqn : both sides equal 1 + p*Q ; then add_left_cancel p*y -> sq = 1 + p*M *)
                        (* ---- LEFT value : add (p*y) sq = 1 + p*Q ---- *)
                        val L_a = addcommS_at (mult pF yW, sq);          (* (p*y + sq) = (sq + p*y) *)
                        val L_b = add_cong_rS (sq, mult pF yW, add ax oneC) hR;  (* (sq + p*y) = (sq + (ax+1)) *)
                        val L_c = oeq_sym OF [addassocS_at (sq, ax, oneC)];      (* (sq + (ax+1)) = ((sq+ax)+1) *)
                        val L_d = add_cong_lS (add sq ax, mult pF Q, oneC) iEq;  (* ((sq+ax)+1) = ((p*Q)+1) *)
                        val L_e = addcommS_at (mult pF Q, oneC);                 (* ((p*Q)+1) = (1 + p*Q) *)
                        val Lval = oeq_trans OF [oeq_trans OF [oeq_trans OF [oeq_trans OF [L_a, L_b], L_c], L_d], L_e]; (* (p*y + sq) = (1 + p*Q) *)
                        (* ---- RIGHT value : add (p*y) (add 1 (p*M)) = 1 + p*Q ---- *)
                        val R_a = addcommS_at (mult pF yW, add oneC (mult pF mW));  (* (p*y + (1 + p*M)) = ((1 + p*M) + p*y) *)
                        val R_b = addassocS_at (oneC, mult pF mW, mult pF yW);      (* ((1 + p*M) + p*y) = (1 + (p*M + p*y)) *)
                        val R_c = add_cong_rS (oneC, add (mult pF mW) (mult pF yW), add (mult pF yW) (mult pF mW))
                                    (addcommS_at (mult pF mW, mult pF yW));        (* (1 + (p*M + p*y)) = (1 + (p*y + p*M)) *)
                        val ld  = left_distrib_atS (pF, yW, mW);                   (* p*(y+M) = (p*y + p*M) *)
                        val pQeq= mult_cong_rS (pF, Q, add yW mW) hm;             (* p*Q = p*(y+M) *)
                        val pyM_pQ = oeq_sym OF [oeq_trans OF [pQeq, ld]];        (* (p*y + p*M) = p*Q *)
                        val R_d = add_cong_rS (oneC, add (mult pF yW) (mult pF mW), mult pF Q) pyM_pQ;  (* (1 + (p*y+p*M)) = (1 + p*Q) *)
                        val Rval = oeq_trans OF [oeq_trans OF [oeq_trans OF [R_a, R_b], R_c], R_d];  (* (p*y + (1+p*M)) = (1 + p*Q) *)
                        (* combine : (p*y + sq) = (p*y + (1+p*M)) *)
                        val both = oeq_trans OF [Lval, oeq_sym OF [Rval]];        (* (p*y + sq) = (p*y + (1 + p*M)) *)
                        val sqEq = add_left_cancel_atS (mult pF yW, sq, add oneC (mult pF mW)) both;  (* oeq sq (add 1 (p*M)) *)
                        (* a*bWit = sq (eq_ab) ; so oeq (a*bWit) (add 1 (p*M)) *)
                        val abEq = oeq_trans OF [eq_ab, sqEq];                    (* oeq (a*bWit) (add 1 (p*M)) *)
                        (* congR p (a*bWit) 1 : Ex k. oeq (a*bWit) (add 1 (mult p k)), witness M *)
                        val congRabs = Abs("k", natT, oeq (mult aF bWit) (add oneC (mult pF (Bound 0))));
                        val exCongR  = exI_atS2 congRabs mW abEq;                 (* congR p (a*bWit) 1 *)
                        val hcong    = disjI2S2_at (congL pF (mult aF bWit) oneC, congR pF (mult aF bWit) oneC) exCongR;
                        val res      = mi_mkGoal (pF, aF) bWit hcong;            (* Ex b. cong p (a*b) 1 *)
                      in res end;
                    val res = exE_elimS2 (leAbs, goalC) leYQ "M_mi" mbody;
                  in res end;
                val res = exE_elimS2 (Abs("m", natT, oeq ax (suc (Bound 0))), goalC) axSucEx "k0_mi" axSucBody;
              in Thm.implies_intr (ctermS2 (jT dR)) res end;

            val res = disjE_elimS2 (dL, dR, goalC) hDisj caseL caseR;
          in res end;
        val g = exE_elimS2 (cb_innerAbs (aF, pF, xW), goalC) hExY "y_mi" ybody;
      in g end;
    val bodyGoal = exE_elimS2 (cb_outerAbs (aF, pF), goalC) cbDisjEx "x_mi" xbody;
    (* discharge the two hypotheses -> meta implications *)
    val disch1 = Thm.implies_intr (ctermS2 hNdvdP) bodyGoal;
    val disch2 = Thm.implies_intr (ctermS2 (jT (prime2 pF))) disch1;
  in varify disch2 end;

val () = out "MOD_INVERSE_PROVED\n";

(* ---- validation ---- *)
val pVmi = Var (("p",0), natT);
val aVmi = Var (("a",0), natT);
val mod_inverse_intended =
  Logic.mk_implies (jT (prime2 pVmi),
    Logic.mk_implies (jT (neg (dvd pVmi aVmi)),
      jT (mi_goal (pVmi, aVmi))));
val r_mi = checkS2 ("mod_inverse", mod_inverse, mod_inverse_intended);
val () = if r_mi then out "OK mod_inverse\n" else out "FAIL mod_inverse\n";

val probe_mi =
  let
    (* dropping the ~(p|a) hypothesis is false (a=0 has no inverse). *)
    val bogus = Logic.mk_implies (jT (prime2 pVmi), jT (mi_goal (pVmi, aVmi)));
  in not ((Thm.prop_of mod_inverse) aconv bogus) end;
val () = if r_mi andalso probe_mi then out "PROBE_OK\n" else out "PROBE_UNSOUND\n";
val () = if r_mi andalso probe_mi then out "MOD_INVERSE_OK\n" else out "MOD_INVERSE_FAILED\n";
(* ============================================================================
   THE MULTIPLICATIVE GROUP MOD p (the Wilson keystones) in Isabelle/Pure on the
   polyml-rs interpreter.  (test: isabelle_mult_group.rs)
   ----------------------------------------------------------------------------
   The algebraic core of (Z/pZ)*, each a 0-hypothesis theorem by genuine LCF
   kernel inference over the two-sided congruence cong:

     inverse_unique : |- cong p (a*b) 1 ==> cong p (a*c) 1 ==> cong p b c
                      the modular inverse is unique -- a pure congruence chain
                      (b == b*1 == b*(a*c) = (a*b)*c == 1*c == c), no primality.
     mod_cancel     : |- prime p ==> ~(p dvd a) ==> cong p (a*b) (a*c) ==> cong p b c
                      cancellation by a unit: from a*b == a*c get a*(b-c) == 0,
                      then euclid_lemma + ~(p|a) give p | (b-c).
     lagrange_roots : |- prime p ==> cong p (a*a) 1 ==> (cong p a 1 \/ cong p (Suc a) 0)
                      LAGRANGE'S THEOREM ON SQUARE ROOTS OF UNITY: the only square
                      roots of 1 mod a prime are +-1 (here -1 is Suc a == 0, so no
                      truncated subtraction). Via the identity (a-1)(a+1) = a^2-1
                      and euclid_lemma.

   These are the algebraic heart of Wilson's theorem. Built on the full gcd /
   Bezout / Euclid-lemma development (isabelle_gcd.sml + ntbase) over the
   classical foundation, spliced in by common::with_gcd. Each carries a soundness
   probe. Proved by a multi-seat ultracode fleet racing all three concurrently
   (wf_3eef19b5-87f); re-verified end-to-end by hand.

   (Full Wilson additionally needs the finite-product combinator prodf merged
   onto this modular base + a product-pairing/permutation lemma -- a separate
   base-unification effort.)
   ============================================================================ *)


(* ============================================================================
   INVERSE_UNIQUE :  cong p (mult a b) 1 ==> cong p (mult a c) 1 ==> cong p b c
   (uniqueness of the modular inverse).  No primality, no induction, no euclid.
   Pure congruence chain via cong_trans / cong_mult / cong_refl / cong_sym,
   with plain equalities lifted to congruences by oeq_subst.
   All cterms routed through the FINAL context ctxtS2 / ctermS2.
   ============================================================================ *)

val () = out "INVERSE_UNIQUE_BEGIN\n";

(* ---- lift the modular congruence lemmas onto ctxtS2 (schematic) ---- *)
val cong_refl_vS  = varify cong_refl;
val cong_sym_vS   = varify cong_sym;
val cong_trans_vS = varify cong_trans;
val cong_mult_vS  = varify cong_mult;

(* cong_refl_atS (m,a) : jT (cong m a a) *)
fun cong_refl_atS (mt, at) = beta_norm (Drule.infer_instantiate ctxtS2
      [(("m",0), ctermS2 mt), (("a",0), ctermS2 at)] cong_refl_vS);

(* cong_sym_atS (m,a,b) h : from jT (cong m a b) build jT (cong m b a) *)
fun cong_sym_atS (mt, at, bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mt), (("a",0), ctermS2 at), (("b",0), ctermS2 bt)] cong_sym_vS)
  in Thm.implies_elim inst h end;

(* cong_trans_atS (m,a,b,c) h1 h2 : from cong m a b, cong m b c build cong m a c *)
fun cong_trans_atS (mt, at, bt, ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mt), (("a",0), ctermS2 at),
         (("b",0), ctermS2 bt), (("c",0), ctermS2 ct)] cong_trans_vS)
      val s1 = Thm.implies_elim inst h1
  in Thm.implies_elim s1 h2 end;

(* cong_mult_atS (m,a,a2,b,b2) h1 h2 :
     from cong m a a2, cong m b b2 build cong m (mult a b)(mult a2 b2) *)
fun cong_mult_atS (mt, at, a2t, bt, b2t) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mt), (("a",0), ctermS2 at), (("a2",0), ctermS2 a2t),
         (("b",0), ctermS2 bt), (("b2",0), ctermS2 b2t)] cong_mult_vS)
      val s1 = Thm.implies_elim inst h1
  in Thm.implies_elim s1 h2 end;

(* ---- mult-congruence on the LEFT operand on ctxtS2:
        oeq p q ==> oeq (mult p k) (mult q k) ---- *)
fun mult_cong_lS (pT, qT, kT) hpq =
  let
    val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 pT), (("b",0), ctermS2 qT)] oeq_subst_vS);
    val refl_pk = beta_norm (Drule.infer_instantiate ctxtS2 [(("a",0), ctermS2 (mult pT kT))] oeq_refl_vS);
  in inst OF [hpq, refl_pk] end;

(* ---- mult_1_left / mult_assoc / mult_comm on ctxtS2 ---- *)
val mult_1_left_vS = varify mult_1_left;     (* oeq (mult (Suc 0) n) n *)
val mult_assoc_vS  = varify mult_assoc;       (* oeq (mult (mult m n) k)(mult m (mult n k)) *)
val mult_comm_vS   = varify mult_comm;        (* oeq (mult m n)(mult n m) *)
fun mult1lS_at t       = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] mult_1_left_vS);
fun multassocS_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mt),(("n",0), ctermS2 nt),(("k",0), ctermS2 kt)] mult_assoc_vS);
fun multcommS_at (mt,nt) = beta_norm (Drule.infer_instantiate ctxtS2
        [(("m",0), ctermS2 mt),(("n",0), ctermS2 nt)] mult_comm_vS);

(* ---- cong_of_eq : from heq : oeq X Y build jT (cong p X Y) (p fixed).
        Take cong_refl (cong p X X), then rewrite the SECOND argument X->Y by
        oeq_subst with predicate %z. cong p X z.  CAPTURE-SAFE: build the
        predicate with Term.lambda over a fresh Free, NOT Abs(...,Bound 0)
        (the SML `cong` constructor inserts its own inner existential Abs, so a
        literal Bound 0 would be captured by that inner k-binder). ---- *)
fun cong_of_eqS (pT, X, Y) heq =
  let
    val zF   = Free("z_coe", natT);
    val Pabs = Term.lambda zF (cong pT X zF);                  (* %z. cong p X z (capture-safe) *)
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("P",0), ctermS2 Pabs), (("a",0), ctermS2 X), (("b",0), ctermS2 Y)] oeq_subst_vS);
    val crefl = cong_refl_atS (pT, X);                          (* cong p X X *)
  in inst OF [heq, crefl] end;

(* ============================================================================
   THE PROOF
   ============================================================================ *)
val inverse_unique =
  let
    val pF = Free("p", natT);
    val aF = Free("a", natT);
    val bF = Free("b", natT);
    val cF = Free("c", natT);
    val one = oneC;                                             (* Suc Zero *)

    val H1prop = jT (cong pF (mult aF bF) one);                 (* cong p (a*b) 1 *)
    val H2prop = jT (cong pF (mult aF cF) one);                 (* cong p (a*c) 1 *)
    val H1 = Thm.assume (ctermS2 H1prop);
    val H2 = Thm.assume (ctermS2 H2prop);

    (* intermediate product terms *)
    val bo  = mult bF one;            (* b * 1     *)
    val bac = mult bF (mult aF cF);   (* b * (a*c) *)
    val abc = mult (mult aF bF) cF;   (* (a*b) * c *)
    val oc  = mult one cF;            (* 1 * c     *)

    (* ---- T1 : cong p b (b*1)   [from oeq b (b*1) = sym (mult_1_right b)] ---- *)
    val eq_b_bo = oeq_sym OF [mult1rS_at bF];                   (* oeq b (mult b 1) *)
    val T1 = cong_of_eqS (pF, bF, bo) eq_b_bo;                  (* cong p b (b*1) *)

    (* ---- T2 : cong p (b*1) (b*(a*c))
            = cong_mult (cong_refl b) (cong_sym H2 : cong p 1 (a*c)) ---- *)
    val crefl_b = cong_refl_atS (pF, bF);                       (* cong p b b *)
    val H2sym   = cong_sym_atS (pF, mult aF cF, one) H2;        (* cong p 1 (a*c) *)
    val T2 = cong_mult_atS (pF, bF, bF, one, mult aF cF) crefl_b H2sym;
                                                                (* cong p (b*1)(b*(a*c)) *)

    (* ---- T3 : cong p (b*(a*c)) ((a*b)*c)  [PLAIN equality] ----
       b*(a*c) = (b*a)*c   [sym mult_assoc b a c]
       (b*a)*c = (a*b)*c   [mult_comm b a, lifted on left operand by *c] *)
    val assoc_sym = oeq_sym OF [multassocS_at (bF, aF, cF)];    (* oeq (b*(a*c)) ((b*a)*c) *)
    val comm_ba   = multcommS_at (bF, aF);                      (* oeq (b*a) (a*b) *)
    val comm_lift = mult_cong_lS (mult bF aF, mult aF bF, cF) comm_ba;
                                                                (* oeq ((b*a)*c) ((a*b)*c) *)
    val eq_bac_abc = oeq_trans OF [assoc_sym, comm_lift];       (* oeq (b*(a*c)) ((a*b)*c) *)
    val T3 = cong_of_eqS (pF, bac, abc) eq_bac_abc;

    (* ---- T4 : cong p ((a*b)*c) (1*c)
            = cong_mult (H1 : cong p (a*b) 1) (cong_refl c : cong p c c) ---- *)
    val crefl_c = cong_refl_atS (pF, cF);                       (* cong p c c *)
    val T4 = cong_mult_atS (pF, mult aF bF, one, cF, cF) H1 crefl_c;
                                                                (* cong p ((a*b)*c)(1*c) *)

    (* ---- T5 : cong p (1*c) c   [from oeq (1*c) c = mult_1_left c] ---- *)
    val eq_oc_c = mult1lS_at cF;                                (* oeq (mult 1 c) c *)
    val T5 = cong_of_eqS (pF, oc, cF) eq_oc_c;                  (* cong p (1*c) c *)

    (* ---- chain everything with cong_trans ---- *)
    val C12   = cong_trans_atS (pF, bF, bo, bac) T1 T2;         (* cong p b (b*(a*c)) *)
    val C123  = cong_trans_atS (pF, bF, bac, abc) C12 T3;       (* cong p b ((a*b)*c) *)
    val C1234 = cong_trans_atS (pF, bF, abc, oc) C123 T4;       (* cong p b (1*c) *)
    val Cfull = cong_trans_atS (pF, bF, oc, cF) C1234 T5;       (* cong p b c *)

    (* discharge the two hypotheses *)
    val d1 = Thm.implies_intr (ctermS2 H2prop) Cfull;
    val d2 = Thm.implies_intr (ctermS2 H1prop) d1;
  in varify d2 end;

val () = out "INVERSE_UNIQUE_PROVED\n";

(* ---- validation ---- *)
val pViu = Var (("p",0), natT);
val aViu = Var (("a",0), natT);
val bViu = Var (("b",0), natT);
val cViu = Var (("c",0), natT);
val inverse_unique_intended =
  Logic.mk_implies (jT (cong pViu (mult aViu bViu) oneC),
    Logic.mk_implies (jT (cong pViu (mult aViu cViu) oneC),
      jT (cong pViu bViu cViu)));
val r_iu = checkS2 ("inverse_unique", inverse_unique, inverse_unique_intended);
val () = if r_iu then out "OK inverse_unique\n" else out "FAIL inverse_unique\n";

(* ---- SOUNDNESS PROBE : dropping the SECOND hypothesis is false.
        cong p (a*b) 1 ==> cong p b c  is NOT a theorem (c is unconstrained).
        The genuine theorem must NOT aconv that dropped-hyp statement. ---- *)
val inverse_unique_BOGUS =
  Logic.mk_implies (jT (cong pViu (mult aViu bViu) oneC),
      jT (cong pViu bViu cViu));
val probe_iu = not ((Thm.prop_of inverse_unique) aconv inverse_unique_BOGUS);
val () = if probe_iu then out "PROBE_OK (dropped-hyp variant not aconv proved thm)\n"
                     else out "PROBE_UNSOUND (proved thm aconv a dropped-hyp statement!)\n";

val () = if r_iu andalso probe_iu then out "INVERSE_UNIQUE_OK\n"
                                  else out "INVERSE_UNIQUE_FAILED\n";

(* ============================================================================
   TARGET : mod_cancel
     |- prime p ==> ~(p dvd a) ==> cong p (a*b) (a*c) ==> cong p b c
   A coprime-to-p factor a can be cancelled in a congruence.
   Built on ctxtS2 (the euclid/modular base context).  Reuses euclid_lemma,
   le_total, add_left_cancel, mult monotonicity helpers, cong_introL pattern.
   ============================================================================ *)

val () = out "MOD_CANCEL_BEGIN\n";

(* euclid_lemma on ctxtS2 : jT (prime2 p) ==> jT (dvd p (a*b)) ==> jT (Disj (dvd p a)(dvd p b)) *)
val euclid_lemma_vMC = varify euclid_lemma;
fun euclid_atMC (pT, aT, bT) hPr hDvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtS2
        [(("p",0), ctermS2 pT), (("a",0), ctermS2 aT), (("b",0), ctermS2 bT)] euclid_lemma_vMC)
  in Thm.implies_elim (Thm.implies_elim inst hPr) hDvd end;

val mod_cancel =
  let
    val pF = Free("p", natT);
    val aF = Free("a", natT);
    val bF = Free("b", natT);
    val cF = Free("c", natT);

    val hPrimeP = jT (prime2 pF);          val hPrime = Thm.assume (ctermS2 hPrimeP);
    val hNdvdP  = jT (neg (dvd pF aF));     val hNdvd  = Thm.assume (ctermS2 hNdvdP);
    val hCongP  = jT (cong pF (mult aF bF) (mult aF cF));
    val hCong   = Thm.assume (ctermS2 hCongP);

    val goalC = cong pF bF cF;

    (* ---- a <> 0  (else p | 0 = a contradicts ~(p|a)) ---- *)
    val axne0 =
      let
        val ha0 = Thm.assume (ctermS2 (jT (oeq aF ZeroC)));        (* a = 0 *)
        val z_p0 = oeq_sym OF [mult0rS_at pF];                     (* 0 = p*0 *)
        val dvd_p0 = dvd_introS (pF, ZeroC, ZeroC) z_p0;           (* dvd p 0 *)
        val dvd_pa = dvd_cong_rS (pF, ZeroC, aF) (oeq_sym OF [ha0]) dvd_p0;  (* dvd p a *)
        val fls = mp_atS2 (dvd pF aF, oFalseC) hNdvd dvd_pa;       (* oFalse *)
        val metaNe = Thm.implies_intr (ctermS2 (jT (oeq aF ZeroC))) fls;
      in impI_atS2 (oeq aF ZeroC, oFalseC) metaNe end;            (* jT (neg (oeq a 0)) *)
    val aSucEx = ne0_suc_atS aF axne0;                             (* Ex m. oeq a (Suc m) *)

    (* ---- cancel_core : le X Y  ==>  oeq (a*Y) ((a*X) + p*k)  ==>  jT (congL p X Y)
            (Ex j. Y = X + p*j).  No a>0 needed (euclid kills the a-branch). ---- *)
    fun cancel_core (X, Y, kT) hle heqYX =
      let
        val leAbs = Abs("q", natT, oeq Y (add X (Bound 0)));       (* le X Y body *)
        fun body dW (hd : thm) =                                   (* hd : oeq Y (add X dW) *)
          let
            val mcong = mult_cong_rS (aF, Y, add X dW) hd;         (* a*Y = a*(X+d) *)
            val ld    = left_distrib_atS (aF, X, dW);              (* a*(X+d) = a*X + a*d *)
            val aYeq  = oeq_trans OF [mcong, ld];                  (* a*Y = a*X + a*d *)
            val combined = oeq_trans OF [oeq_sym OF [aYeq], heqYX];(* (a*X + a*d) = (a*X + p*k) *)
            val adk   = add_left_cancel_atS (mult aF X, mult aF dW, mult pF kT) combined; (* a*d = p*k *)
            val dvd_p_ad = dvd_introS (pF, mult aF dW, kT) adk;    (* dvd p (a*d) *)
            val eDisj = euclid_atMC (pF, aF, dW) hPrime dvd_p_ad;  (* Disj (dvd p a)(dvd p d) *)
            val goalCL = congL pF X Y;                             (* Ex j. Y = X + p*j *)
            (* case dvd p a : contradiction *)
            val caseA =
              let
                val hda = Thm.assume (ctermS2 (jT (dvd pF aF)));
                val fls = mp_atS2 (dvd pF aF, oFalseC) hNdvd hda; (* oFalse *)
                val any = oFalse_elimS_at goalCL;                  (* jT oFalse ==> jT goalCL *)
              in Thm.implies_intr (ctermS2 (jT (dvd pF aF))) (Thm.implies_elim any fls) end;
            (* case dvd p d : d = p*j -> Y = X + p*j -> congL *)
            val caseD =
              let
                val hdd = Thm.assume (ctermS2 (jT (dvd pF dW)));
                val dvdAbs = Abs("k", natT, oeq dW (mult pF (Bound 0)));   (* dvd p d body *)
                fun jbody jW (hj : thm) =                          (* hj : oeq d (p*j) *)
                  let
                    val ac = add_cong_rS (X, dW, mult pF jW) hj;  (* (X+d) = (X + p*j) *)
                    val Yeq = oeq_trans OF [hd, ac];               (* Y = X + p*j *)
                    val congLabs = Abs("k", natT, oeq Y (add X (mult pF (Bound 0))));
                  in exI_atS2 congLabs jW Yeq end;                 (* jT (congL p X Y) *)
                val res = exE_elimS2 (dvdAbs, goalCL) hdd "j_mc" jbody;
              in Thm.implies_intr (ctermS2 (jT (dvd pF dW))) res end;
            val g = disjE_elimS2 (dvd pF aF, dvd pF dW, goalCL) eDisj caseA caseD;
          in g end;                                               (* jT (congL p X Y) *)
        val res = exE_elimS2 (leAbs, congL pF X Y) hle "d_mc" body;
      in res end;

    (* ---- deg_core : le X Y ==> oeq (a*X) ((a*Y) + p*k) ==> oeq X Y
            (the "wrong direction": smaller X has bigger multiple -> equality).
            Needs a = Suc a0 (passed in via aSuc on a0W). ---- *)
    fun deg_core (X, Y, kT) (a0W, aSuc) hle heqXY =
      let
        val leAbs = Abs("q", natT, oeq Y (add X (Bound 0)));
        fun body dW (hd : thm) =                                  (* hd : oeq Y (add X dW) *)
          let
            val mcong = mult_cong_rS (aF, Y, add X dW) hd;        (* a*Y = a*(X+d) *)
            val ld    = left_distrib_atS (aF, X, dW);             (* a*(X+d) = a*X + a*d *)
            val aYeq  = oeq_trans OF [mcong, ld];                 (* a*Y = a*X + a*d *)
            (* rewrite a*Y inside heqXY's RHS *)
            val rw1 = add_cong_lS (mult aF Y, add (mult aF X) (mult aF dW), mult pF kT) aYeq;
                                                                   (* (a*Y + p*k) = ((a*X+a*d) + p*k) *)
            val eq2 = oeq_trans OF [heqXY, rw1];                  (* a*X = ((a*X+a*d) + p*k) *)
            val assoc = addassocS_at (mult aF X, mult aF dW, mult pF kT);
                                                                   (* ((a*X+a*d)+p*k) = (a*X + (a*d+p*k)) *)
            val eq3 = oeq_trans OF [eq2, assoc];                  (* a*X = a*X + (a*d+p*k) *)
            val W   = add (mult aF dW) (mult pF kT);
            val lhs0 = add0rS_at (mult aF X);                     (* (a*X + 0) = a*X *)
            val eq4 = oeq_trans OF [lhs0, eq3];                   (* (a*X + 0) = (a*X + W) *)
            val zeroW = add_left_cancel_atS (mult aF X, ZeroC, W) eq4;  (* 0 = W *)
            val Weq0 = oeq_sym OF [zeroW];                        (* W = 0 ; i.e. (a*d + p*k) = 0 *)
            val aedW0 = add_eq_zero_left OF [Weq0];               (* a*d = 0 *)
            (* a = Suc a0 : (Suc a0)*d = d + a0*d ; a*d=0 -> d + a0*d = 0 -> d = 0 *)
            val c1 = mult_cong_lS (aF, suc a0W, dW) aSuc;         (* a*d = (Suc a0)*d *)
            val sucdW0 = oeq_trans OF [oeq_sym OF [c1], aedW0];   (* (Suc a0)*d = 0 *)
            val ms = mult_Suc_atS (a0W, dW);                      (* (Suc a0)*d = d + a0*d *)
            val sum0 = oeq_trans OF [oeq_sym OF [ms], sucdW0];    (* (d + a0*d) = 0 *)
            val dW0 = add_eq_zero_left OF [sum0];                 (* d = 0 *)
            (* Y = X + d, d = 0 -> Y = X *)
            val chain1 = oeq_trans OF [add_cong_rS (X, dW, ZeroC) dW0, add0rS_at X]; (* (X+d) = X *)
            val Yeqx = oeq_trans OF [hd, chain1];                 (* Y = X *)
          in oeq_sym OF [Yeqx] end;                               (* oeq X Y *)
        val res = exE_elimS2 (leAbs, oeq X Y) hle "d_dc" body;
      in res end;

    (* ---- cong_of_eq : oeq X Y ==> jT (cong p X Y)  (witness 0 on congL) ---- *)
    fun cong_of_eq (X, Y) hXY =
      let
        val m0 = mult0rS_at pF;                                   (* p*0 = 0 *)
        val acr = add_cong_rS (X, mult pF ZeroC, ZeroC) m0;       (* (X + p*0) = (X + 0) *)
        val a0r = add0rS_at X;                                    (* (X + 0) = X *)
        val xpx = oeq_trans OF [acr, a0r];                        (* (X + p*0) = X *)
        val x_xp0 = oeq_sym OF [xpx];                             (* X = (X + p*0) *)
        val Ybody = oeq_trans OF [oeq_sym OF [hXY], x_xp0];       (* Y = (X + p*0) *)
        val congLabs = Abs("k", natT, oeq Y (add X (mult pF (Bound 0))));
        val exL = exI_atS2 congLabs ZeroC Ybody;                 (* jT (congL p X Y) *)
      in disjI1S2_at (congL pF X Y, congR pF X Y) exL end;        (* jT (cong p X Y) *)

    (* ---- a = Suc a0 in scope, then case split ---- *)
    fun mainWithASuc a0W aSuc =
      let
        (* hypothesis cong p (a*b) (a*c) = Disj (congL ..)(congR ..) *)
        val dL = congL pF (mult aF bF) (mult aF cF);              (* Ex k. a*c = a*b + p*k *)
        val dR = congR pF (mult aF bF) (mult aF cF);              (* Ex k. a*b = a*c + p*k *)

        (* ===== CASE L : a*c = a*b + p*k ===== *)
        val caseL =
          let
            val hL = Thm.assume (ctermS2 (jT dL));
            val lAbs = Abs("k", natT, oeq (mult aF cF) (add (mult aF bF) (mult pF (Bound 0))));
            fun lbody kW (hk : thm) =          (* hk : a*c = a*b + p*k  (a*Y = a*X + p*k ; Y=c,X=b) *)
              let
                val lt = le_total_atS (bF, cF);                  (* Disj (le b c)(le c b) *)
                (* sub : le b c -> cancel_core(b,c) -> congL p b c -> cong via disjI1 *)
                val subBC =
                  let
                    val hbc = Thm.assume (ctermS2 (jT (le bF cF)));
                    val cl = cancel_core (bF, cF, kW) hbc hk;     (* jT (congL p b c) *)
                    val g  = disjI1S2_at (congL pF bF cF, congR pF bF cF) cl;
                  in Thm.implies_intr (ctermS2 (jT (le bF cF))) g end;
                (* sub : le c b -> deg_core(c,b) -> oeq c b -> oeq b c -> cong_of_eq *)
                val subCB =
                  let
                    val hcb = Thm.assume (ctermS2 (jT (le cF bF)));
                    val ecb = deg_core (cF, bF, kW) (a0W, aSuc) hcb hk;  (* oeq c b *)
                    val ebc = oeq_sym OF [ecb];                  (* oeq b c *)
                    val g   = cong_of_eq (bF, cF) ebc;           (* cong p b c *)
                  in Thm.implies_intr (ctermS2 (jT (le cF bF))) g end;
                val g = disjE_elimS2 (le bF cF, le cF bF, goalC) lt subBC subCB;
              in g end;
            val res = exE_elimS2 (lAbs, goalC) hL "kL_mc" lbody;
          in Thm.implies_intr (ctermS2 (jT dL)) res end;

        (* ===== CASE R : a*b = a*c + p*k ===== *)
        val caseR =
          let
            val hR = Thm.assume (ctermS2 (jT dR));
            val rAbs = Abs("k", natT, oeq (mult aF bF) (add (mult aF cF) (mult pF (Bound 0))));
            fun rbody kW (hk : thm) =          (* hk : a*b = a*c + p*k  (a*Y = a*X + p*k ; Y=b,X=c) *)
              let
                val lt = le_total_atS (cF, bF);                  (* Disj (le c b)(le b c) *)
                (* sub : le c b -> cancel_core(c,b) -> congL p c b = congR p b c -> disjI2 *)
                val subCB =
                  let
                    val hcb = Thm.assume (ctermS2 (jT (le cF bF)));
                    val cl = cancel_core (cF, bF, kW) hcb hk;     (* jT (congL p c b) = (Ex j. b = c + p*j) *)
                    val g  = disjI2S2_at (congL pF bF cF, congR pF bF cF) cl;
                  in Thm.implies_intr (ctermS2 (jT (le cF bF))) g end;
                (* sub : le b c -> deg_core(b,c) -> oeq b c -> cong_of_eq *)
                val subBC =
                  let
                    val hbc = Thm.assume (ctermS2 (jT (le bF cF)));
                    val ebc = deg_core (bF, cF, kW) (a0W, aSuc) hbc hk;  (* oeq b c *)
                    val g   = cong_of_eq (bF, cF) ebc;           (* cong p b c *)
                  in Thm.implies_intr (ctermS2 (jT (le bF cF))) g end;
                val g = disjE_elimS2 (le cF bF, le bF cF, goalC) lt subCB subBC;
              in g end;
            val res = exE_elimS2 (rAbs, goalC) hR "kR_mc" rbody;
          in Thm.implies_intr (ctermS2 (jT dR)) res end;

        val g = disjE_elimS2 (dL, dR, goalC) hCong caseL caseR;
      in g end;

    (* exE on a = Suc a0 *)
    val aSucAbs = Abs("m", natT, oeq aF (suc (Bound 0)));
    fun aSucBody a0W (haSuc : thm) = mainWithASuc a0W haSuc;
    val bodyGoal = exE_elimS2 (aSucAbs, goalC) aSucEx "a0_mc" aSucBody;

    (* discharge the three hypotheses *)
    val d1 = Thm.implies_intr (ctermS2 hCongP) bodyGoal;
    val d2 = Thm.implies_intr (ctermS2 hNdvdP) d1;
    val d3 = Thm.implies_intr (ctermS2 hPrimeP) d2;
  in varify d3 end;

val () = out "MOD_CANCEL_PROVED\n";

(* ---- validation : 0-hyp + aconv the TARGET ---- *)
val pVmc = Var (("p",0), natT);
val aVmc = Var (("a",0), natT);
val bVmc = Var (("b",0), natT);
val cVmc = Var (("c",0), natT);
val mod_cancel_intended =
  Logic.mk_implies (jT (prime2 pVmc),
    Logic.mk_implies (jT (neg (dvd pVmc aVmc)),
      Logic.mk_implies (jT (cong pVmc (mult aVmc bVmc) (mult aVmc cVmc)),
        jT (cong pVmc bVmc cVmc))));
val r_mc =
  let
    val nh = length (Thm.hyps_of mod_cancel);
    val ac = (Thm.prop_of mod_cancel) aconv mod_cancel_intended;
  in
    if nh = 0 andalso ac then (out "OK mod_cancel\n"; true)
    else (out ("FAIL mod_cancel (hyps=" ^ Int.toString nh ^ " aconv=" ^ Bool.toString ac ^ ")\n"
               ^ "  got      = " ^ Syntax.string_of_term ctxtS2 (Thm.prop_of mod_cancel) ^ "\n"
               ^ "  intended = " ^ Syntax.string_of_term ctxtS2 mod_cancel_intended ^ "\n");
          false)
  end;

(* ---- soundness probe : dropping ~(p|a) must NOT be provable
        (p=2, a=2 : cong 2 (2*1) (2*0) i.e. cong 2 2 0 holds, but cong 2 1 0 false). *)
val probe_mc_needs_ndvd =
  let
    val bogus = Logic.mk_implies (jT (prime2 pVmc),
                  Logic.mk_implies (jT (cong pVmc (mult aVmc bVmc) (mult aVmc cVmc)),
                    jT (cong pVmc bVmc cVmc)));   (* drops ~(p|a) *)
  in not ((Thm.prop_of mod_cancel) aconv bogus) end;
val probe_mc_nontrivial =
  not ((Thm.prop_of mod_cancel) aconv (jT (cong pVmc bVmc cVmc)));

val () =
  if r_mc andalso probe_mc_needs_ndvd andalso probe_mc_nontrivial
  then out "PROBE_OK mod_cancel is conditional on ~(p|a) / nontrivial\n"
  else out "PROBE_UNSOUND mod_cancel collapsed!\n";

val () =
  if r_mc andalso probe_mc_needs_ndvd andalso probe_mc_nontrivial
  then out "MOD_CANCEL_OK\n"
  else out "MOD_CANCEL_FAILED\n";
(* ============================================================================
   LAGRANGE'S THEOREM ON SQUARE ROOTS OF UNITY mod p
     lagrange_roots : prime2 p ==> cong p (mult a a) 1
                        ==> Disj (cong p a 1) (cong p (Suc a) 0)
   x^2 == 1 (mod p) ==> x == 1 OR x == -1   (-1 expressed as Suc a == 0).
   Strategy: num-cases on a.
     a = 0   : cong p 0 1 forces p|1, contradicting prime (1<p).
     a = Suc a0 : (a0+1)^2 = a0*(a+1) + 1 ; cong cancels +1 to p | a0*(Suc a);
                  euclid_lemma -> p|a0 (=> a == 1) or p|(Suc a) (=> Suc a == 0).
   Routed through ctxtS2 / ctermS2 (the final base context).
   ============================================================================ *)
val () = out "LAGRANGE_ROOTS_BEGIN\n";

(* ---- extra instantiators on ctxtS2 ---- *)
val Suc_inj_vS2          = varify Suc_inj_ax;            (* oeq (Suc ?a)(Suc ?b) ==> oeq ?a ?b *)
fun Suc_inj_atS (ut, vt) h = Thm.implies_elim
      (beta_norm (Drule.infer_instantiate ctxtS2
        [(("a",0), ctermS2 ut), (("b",0), ctermS2 vt)] Suc_inj_vS2)) h;
val add_eq_zero_left_vS  = varify add_eq_zero_left;      (* oeq (add ?a ?b) Zero ==> oeq ?a Zero *)
fun add_eq_zero_left_atS (at, bt) h = Thm.implies_elim
      (beta_norm (Drule.infer_instantiate ctxtS2
        [(("a",0), ctermS2 at), (("b",0), ctermS2 bt)] add_eq_zero_left_vS)) h;

(* mult left-zero on ctxtS2 : oeq (mult 0 n) 0 *)
val mult_0_vS2 = varify mult_0;
fun mult0lS_at t = beta_norm (Drule.infer_instantiate ctxtS2 [(("n",0), ctermS2 t)] mult_0_vS2);

(* euclid_lemma on ctxtS2 : prime2 p -> dvd p (mult a b) -> Disj (dvd p a)(dvd p b) *)
val euclid_lemma_vS2 = varify euclid_lemma;
fun euclid_atS (pt, at, bt) hPrime hDvd =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("p",0), ctermS2 pt), (("a",0), ctermS2 at), (("b",0), ctermS2 bt)] euclid_lemma_vS2);
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hDvd end;

(* prime_not_dvd_pos_lt on ctxtS2 : dvd p r -> lt 0 r -> lt r p -> oFalse *)
val prime_not_dvd_pos_lt_vS2 = varify prime_not_dvd_pos_lt;
fun prime_not_dvd_pos_lt_atS (pt, rt) hDvd hPos hLt =
  let
    val inst = beta_norm (Drule.infer_instantiate ctxtS2
          [(("p",0), ctermS2 pt), (("r",0), ctermS2 rt)] prime_not_dvd_pos_lt_vS2);
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hDvd) hPos) hLt end;

val () = out "LR_HELPERS_READY\n";

val lagrange_roots =
  let
    val pF = Free("p", natT);
    val aF = Free("a", natT);
    val hPrimeP = jT (prime2 pF);
    val hPrime  = Thm.assume (ctermS2 hPrimeP);
    val hCongP  = jT (cong pF (mult aF aF) oneC);
    val hCong   = Thm.assume (ctermS2 hCongP);

    (* the final goal disjunction *)
    val goalC = mkDisj (cong pF aF oneC) (cong pF (suc aF) ZeroC);

    (* num-cases on a : Disj (oeq a 0) (Ex q. oeq a (Suc q)) *)
    val dz = dzosS_at aF;

    (* ===================== CASE a = 0 ===================== *)
    val caseZero =
      let
        val ha0 = Thm.assume (ctermS2 (jT (oeq aF ZeroC)));    (* a = 0 *)
        (* From hCong : Disj (congL p (a*a) 1)(congR p (a*a) 1).  We derive oFalse,
           then oFalse_elim into goalC.  Both disjuncts of cong are contradictory.
           congL : Ex k. 1 = (a*a) + p*k  -> p|1 -> prime contra
           congR : Ex k. (a*a) = 1 + p*k  -> rewrite a*a -> 0 (since a=0); but
                   0 = 1 + p*k = Suc(p*k) -> Suc_neq_Zero contra.  *)
        val aa_0a = mult_cong_lS (aF, ZeroC, aF) ha0;          (* a*a = 0*a *)
        val z0a   = mult0lS_at aF;                             (* 0*a = 0 *)
        val aa0   = oeq_trans OF [aa_0a, z0a];                 (* a*a = 0 *)

        val LcongL = congL pF (mult aF aF) oneC;
        val LcongR = congR pF (mult aF aF) oneC;

        (* congL case : Ex k. oeq 1 (add (a*a) (mult p k)) *)
        val caseL =
          let
            val PabsL = Abs("k", natT, oeq oneC (add (mult aF aF) (mult pF (Bound 0))));
            fun bodyL kW (hk : thm) =                          (* hk : 1 = (a*a) + p*k *)
              let
                (* rewrite a*a -> 0 : (a*a) + p*k = 0 + p*k = p*k *)
                val r1 = add_cong_lS (mult aF aF, ZeroC, mult pF kW) aa0;  (* (a*a + p*k) = (0 + p*k) *)
                val r2 = add0S_at (mult pF kW);                (* (0 + p*k) = p*k *)
                val one_pk = oeq_trans OF [oeq_trans OF [hk, r1], r2];  (* 1 = p*k *)
                (* dvd p 1 : oeq 1 (mult p k) is exactly one_pk *)
                val dvdp1 = dvd_introS (pF, oneC, kW) one_pk;  (* dvd p 1 *)
                (* lt 0 1 = le (Suc 0) 1 = le 1 1 ; witness 0 : oeq 1 (add 1 0) *)
                val lt01 =
                  let val h = oeq_sym OF [add0rS_at oneC]       (* oeq 1 (add 1 0) *)
                  in le_introS (oneC, oneC, ZeroC) h end;       (* le 1 1 = lt 0 1 *)
                val lt1p  = prime2_gt1_atS pF hPrime;           (* lt 1 p *)
                val fls   = prime_not_dvd_pos_lt_atS (pF, oneC) dvdp1 lt01 lt1p;  (* oFalse *)
              in Thm.implies_elim (oFalse_elimS_at goalC) fls end;  (* goalC *)
            val resL = exE_elimS2 (PabsL, goalC) (Thm.assume (ctermS2 (jT LcongL))) "kL_lr" bodyL;
          in Thm.implies_intr (ctermS2 (jT LcongL)) resL end;

        (* congR case : Ex k. oeq (a*a) (add 1 (mult p k)) *)
        val caseR =
          let
            val PabsR = Abs("k", natT, oeq (mult aF aF) (add oneC (mult pF (Bound 0))));
            fun bodyR kW (hk : thm) =                          (* hk : (a*a) = 1 + p*k *)
              let
                (* a*a = 0 (aa0) and a*a = 1 + p*k -> 0 = 1 + p*k *)
                val z_1pk = oeq_trans OF [oeq_sym OF [aa0], hk];   (* 0 = 1 + p*k *)
                (* 1 + p*k = Suc 0 + p*k = Suc(0 + p*k) = Suc(p*k) *)
                val s1 = addSucS_at (ZeroC, mult pF kW);       (* (Suc 0 + p*k) = Suc(0 + p*k) *)
                val s2 = Suc_cong OF [add0S_at (mult pF kW)];  (* Suc(0 + p*k) = Suc(p*k) *)
                val onepk_suc = oeq_trans OF [s1, s2];         (* (1 + p*k) = Suc(p*k) *)
                val z_suc = oeq_trans OF [z_1pk, onepk_suc];   (* 0 = Suc(p*k) *)
                val suc_z = oeq_sym OF [z_suc];                (* Suc(p*k) = 0 *)
                val fls   = (Suc_neq_Zero_atS (mult pF kW)) OF [suc_z];  (* oFalse *)
              in Thm.implies_elim (oFalse_elimS_at goalC) fls end;
            val resR = exE_elimS2 (PabsR, goalC) (Thm.assume (ctermS2 (jT LcongR))) "kR_lr" bodyR;
          in Thm.implies_intr (ctermS2 (jT LcongR)) resR end;

        val res = disjE_elimS2 (LcongL, LcongR, goalC) hCong caseL caseR;
      in Thm.implies_intr (ctermS2 (jT (oeq aF ZeroC))) res end;

    (* ===================== CASE a = Suc a0 ===================== *)
    val PabsSuc = Abs("q", natT, oeq aF (suc (Bound 0)));
    fun caseSucBody a0 (ha : thm) =                            (* ha : a = Suc a0 *)
      let
        val M  = mult a0 aF;                                   (* a0 * a *)
        val T  = add a0 M;                                     (* a0 + a0*a *)
        val xT = mult a0 (suc aF);                             (* a0 * (Suc a) = the witness x *)

        (* ---- key identity : oeq (mult a a) (add xT 1) ---- *)
        (* LHS chain : mult a a -> Suc T *)
        val L1 = mult_cong_lS (aF, suc a0, aF) ha;             (* a*a = (Suc a0)*a *)
        val L2 = mult_Suc_atS (a0, aF);                        (* (Suc a0)*a = add a (a0*a) *)
        val L3 = add_cong_lS (aF, suc a0, M) ha;               (* (a + a0*a) = (Suc a0 + a0*a) *)
        val L4 = addSucS_at (a0, M);                           (* (Suc a0 + a0*a) = Suc(a0 + a0*a) = Suc T *)
        val LHS = oeq_trans OF [oeq_trans OF [oeq_trans OF [L1, L2], L3], L4];  (* a*a = Suc T *)
        (* RHS chain : add xT 1 -> Suc T *)
        val R0 = multSrS_at (a0, aF);                          (* a0*(Suc a) = add a0 (a0*a) = T *)
        val R1 = add_cong_lS (xT, T, oneC) R0;                 (* (xT + 1) = (T + 1) *)
        val R2 = addSrS_at (T, ZeroC);                         (* (T + Suc 0) = Suc(T + 0) *)
        val R3 = Suc_cong OF [add0rS_at T];                    (* Suc(T + 0) = Suc T *)
        val RHS = oeq_trans OF [oeq_trans OF [R1, R2], R3];    (* (xT + 1) = Suc T *)
        val idEq = oeq_trans OF [LHS, oeq_sym OF [RHS]];       (* a*a = add xT 1 *)

        (* ---- derive  dvd p xT  from hCong + idEq ---- *)
        val LcongL = congL pF (mult aF aF) oneC;
        val LcongR = congR pF (mult aF aF) oneC;

        (* congL : Ex k. oeq 1 (add (a*a) (mult p k))  ->  rewrite a*a->xT+1 ->
           1 = (xT+1)+p*k = Suc(xT+p*k) -> Suc_inj -> 0 = xT+p*k -> xT=0 -> dvd p 0 -> dvd p xT *)
        val dvdL =
          let
            val PabsL = Abs("k", natT, oeq oneC (add (mult aF aF) (mult pF (Bound 0))));
            fun bodyL kW (hk : thm) =                          (* hk : 1 = (a*a) + p*k *)
              let
                (* rewrite a*a -> xT+1 in (a*a)+p*k *)
                val rw  = add_cong_lS (mult aF aF, add xT oneC, mult pF kW) idEq;  (* ((a*a)+p*k) = ((xT+1)+p*k) *)
                val one_eq = oeq_trans OF [hk, rw];            (* 1 = (xT+1)+p*k *)
                (* (xT+1)+p*k = Suc(xT) + p*k = Suc(xT + p*k) *)
                val e1 = add_cong_lS (add xT oneC, suc xT, mult pF kW)
                           (let val a1 = addSrS_at (xT, ZeroC)        (* (xT + Suc 0) = Suc(xT+0) *)
                                val a2 = Suc_cong OF [add0rS_at xT]    (* Suc(xT+0) = Suc xT *)
                            in oeq_trans OF [a1, a2] end);     (* (xT+1) = Suc xT *)
                                                               (* ((xT+1)+p*k) = (Suc xT + p*k) *)
                val e2 = addSucS_at (xT, mult pF kW);          (* (Suc xT + p*k) = Suc(xT + p*k) *)
                val one_suc = oeq_trans OF [oeq_trans OF [one_eq, e1], e2];  (* 1 = Suc(xT+p*k) *)
                (* 1 = Suc 0, so Suc 0 = Suc(xT+p*k) -> Suc_inj -> 0 = xT+p*k *)
                val suc_eq = one_suc;                          (* oeq (Suc 0) (Suc (xT+p*k)) *)
                val zero_eq = Suc_inj_atS (ZeroC, add xT (mult pF kW)) suc_eq;  (* 0 = xT+p*k *)
                val sum_zero = oeq_sym OF [zero_eq];           (* (xT+p*k) = 0 *)
                val xT_zero = add_eq_zero_left_atS (xT, mult pF kW) sum_zero;   (* xT = 0 *)
                (* dvd p 0, then rewrite 0->xT : dvd p xT.  dvd_cong_rS needs oeq 0 xT. *)
                val dvdp0 = dvd_zeroS_at pF;                   (* dvd p 0 *)
                val zero_xT = oeq_sym OF [xT_zero];            (* 0 = xT *)
                val dvdpxT = dvd_cong_rS (pF, ZeroC, xT) zero_xT dvdp0;  (* dvd p xT *)
              in dvdpxT end;
            val r = exE_elimS2 (PabsL, dvd pF xT) (Thm.assume (ctermS2 (jT LcongL))) "kL2_lr" bodyL;
          in Thm.implies_intr (ctermS2 (jT LcongL)) r end;

        (* congR : Ex k. oeq (a*a) (add 1 (mult p k)) -> rewrite a*a->xT+1 ->
           (xT+1) = 1 + p*k = Suc(p*k); also xT+1 = Suc xT -> Suc xT = Suc(p*k) -> xT = p*k -> dvd p xT *)
        val dvdR =
          let
            val PabsR = Abs("k", natT, oeq (mult aF aF) (add oneC (mult pF (Bound 0))));
            fun bodyR kW (hk : thm) =                          (* hk : (a*a) = 1 + p*k *)
              let
                val lhs_eq = oeq_trans OF [oeq_sym OF [idEq], hk];   (* (xT+1) = 1 + p*k *)
                (* xT+1 = Suc xT *)
                val xT1_suc = let val a1 = addSrS_at (xT, ZeroC)
                                  val a2 = Suc_cong OF [add0rS_at xT]
                              in oeq_trans OF [a1, a2] end;     (* (xT+1) = Suc xT *)
                (* 1 + p*k = Suc 0 + p*k = Suc(0+p*k) = Suc(p*k) *)
                val rhs_suc = let val b1 = addSucS_at (ZeroC, mult pF kW)
                                  val b2 = Suc_cong OF [add0S_at (mult pF kW)]
                              in oeq_trans OF [b1, b2] end;     (* (1 + p*k) = Suc(p*k) *)
                (* Suc xT = (xT+1) = (1+p*k) = Suc(p*k) *)
                val suc_eq = oeq_trans OF [oeq_trans OF [oeq_sym OF [xT1_suc], lhs_eq], rhs_suc];  (* Suc xT = Suc(p*k) *)
                val xT_pk = Suc_inj_atS (xT, mult pF kW) suc_eq;  (* xT = p*k *)
                val dvdpxT = dvd_introS (pF, xT, kW) xT_pk;     (* dvd p xT *)
              in dvdpxT end;
            val r = exE_elimS2 (PabsR, dvd pF xT) (Thm.assume (ctermS2 (jT LcongR))) "kR2_lr" bodyR;
          in Thm.implies_intr (ctermS2 (jT LcongR)) r end;

        val dvdpxT = disjE_elimS2 (LcongL, LcongR, dvd pF xT) hCong dvdL dvdR;  (* dvd p xT *)

        (* ---- euclid_lemma : dvd p (mult a0 (Suc a)) -> Disj (dvd p a0)(dvd p (Suc a)) ---- *)
        val euDisj = euclid_atS (pF, a0, suc aF) hPrime dvdpxT;   (* Disj (dvd p a0)(dvd p (Suc a)) *)

        (* CASE p|a0 : a0 = p*j -> a = Suc a0 = Suc(p*j) = 1 + p*j -> cong p a 1 (congR) -> disjI1 goalC *)
        val caseDA0 =
          let
            val hda0 = Thm.assume (ctermS2 (jT (dvd pF a0)));    (* dvd p a0 = Ex k. a0 = p*k *)
            val Pdvd = Abs("k", natT, oeq a0 (mult pF (Bound 0)));
            fun body jW (hj : thm) =                             (* hj : a0 = p*j *)
              let
                (* a = Suc a0 = Suc(p*j) ; 1 + p*j = Suc(p*j) ; so a = 1 + p*j *)
                val a_suc_pj = oeq_trans OF [ha, Suc_cong OF [hj]];  (* a = Suc(p*j) *)
                val onepj_suc = let val b1 = addSucS_at (ZeroC, mult pF jW)
                                    val b2 = Suc_cong OF [add0S_at (mult pF jW)]
                                in oeq_trans OF [b1, b2] end;    (* (1 + p*j) = Suc(p*j) *)
                val a_eq = oeq_trans OF [a_suc_pj, oeq_sym OF [onepj_suc]];  (* a = (1 + p*j) *)
                (* congR p a 1 : Ex k. oeq a (add 1 (mult p k)), witness j *)
                val congRabs = Abs("k", natT, oeq aF (add oneC (mult pF (Bound 0))));
                val exC = exI_atS2 congRabs jW a_eq;             (* congR p a 1 *)
                val hcong = disjI2S2_at (congL pF aF oneC, congR pF aF oneC) exC;  (* cong p a 1 *)
              in disjI1S2_at (cong pF aF oneC, cong pF (suc aF) ZeroC) hcong end;  (* goalC *)
            val r = exE_elimS2 (Pdvd, goalC) hda0 "j0_lr" body;
          in Thm.implies_intr (ctermS2 (jT (dvd pF a0))) r end;

        (* CASE p|(Suc a) : Suc a = p*j -> cong p (Suc a) 0 (congR, b:=0) -> disjI2 goalC *)
        val caseDSa =
          let
            val hdSa = Thm.assume (ctermS2 (jT (dvd pF (suc aF))));  (* dvd p (Suc a) = Ex k. Suc a = p*k *)
            val Pdvd = Abs("k", natT, oeq (suc aF) (mult pF (Bound 0)));
            fun body jW (hj : thm) =                             (* hj : Suc a = p*j *)
              let
                (* Suc a = p*j ; 0 + p*j = p*j ; so Suc a = 0 + p*j *)
                val z_pj = oeq_sym OF [add0S_at (mult pF jW)];   (* p*j = 0 + p*j *)
                val Sa_eq = oeq_trans OF [hj, z_pj];             (* Suc a = 0 + p*j *)
                (* congR p (Suc a) 0 : Ex k. oeq (Suc a) (add 0 (mult p k)), witness j *)
                val congRabs = Abs("k", natT, oeq (suc aF) (add ZeroC (mult pF (Bound 0))));
                val exC = exI_atS2 congRabs jW Sa_eq;            (* congR p (Suc a) 0 *)
                val hcong = disjI2S2_at (congL pF (suc aF) ZeroC, congR pF (suc aF) ZeroC) exC;  (* cong p (Suc a) 0 *)
              in disjI2S2_at (cong pF aF oneC, cong pF (suc aF) ZeroC) hcong end;  (* goalC *)
            val r = exE_elimS2 (Pdvd, goalC) hdSa "jS_lr" body;
          in Thm.implies_intr (ctermS2 (jT (dvd pF (suc aF)))) r end;

        val res = disjE_elimS2 (dvd pF a0, dvd pF (suc aF), goalC) euDisj caseDA0 caseDSa;
      in res end;
    val caseSuc =
      let
        val r = exE_elimS2 (PabsSuc, goalC) (Thm.assume (ctermS2 (jT (mkEx PabsSuc)))) "a0_lr" caseSucBody;
      in Thm.implies_intr (ctermS2 (jT (mkEx PabsSuc))) r end;

    val concl = disjE_elimS2 (oeq aF ZeroC, mkEx PabsSuc, goalC) dz caseZero caseSuc;  (* goalC *)
    val disch1 = Thm.implies_intr (ctermS2 hCongP) concl;
    val disch2 = Thm.implies_intr (ctermS2 hPrimeP) disch1;
  in varify disch2 end;

val () = out "LAGRANGE_ROOTS_PROVED\n";

(* ---- validation ---- *)
val pVlr = Var (("p",0), natT);
val aVlr = Var (("a",0), natT);
val lagrange_roots_intended =
  Logic.mk_implies (jT (prime2 pVlr),
    Logic.mk_implies (jT (cong pVlr (mult aVlr aVlr) oneC),
      jT (mkDisj (cong pVlr aVlr oneC) (cong pVlr (suc aVlr) ZeroC))));
val r_lr = checkS2 ("lagrange_roots", lagrange_roots, lagrange_roots_intended);
val () = if r_lr then out "OK lagrange_roots\n" else out "FAIL lagrange_roots\n";

(* ---- soundness probes ---- *)
(* (1) dropping prime2 p must NOT be provable (kernel must still need it) *)
val probe_drop_prime =
  let val bogus = Logic.mk_implies (jT (cong pVlr (mult aVlr aVlr) oneC),
                    jT (mkDisj (cong pVlr aVlr oneC) (cong pVlr (suc aVlr) ZeroC)))
  in not ((Thm.prop_of lagrange_roots) aconv bogus) end;
(* (2) dropping one disjunct (keeping only x==1) must NOT match *)
val probe_drop_disj =
  let val bogus = Logic.mk_implies (jT (prime2 pVlr),
                    Logic.mk_implies (jT (cong pVlr (mult aVlr aVlr) oneC),
                      jT (cong pVlr aVlr oneC)))
  in not ((Thm.prop_of lagrange_roots) aconv bogus) end;

val () =
  if probe_drop_prime andalso probe_drop_disj
  then out "PROBE_OK lagrange_roots conditional on prime / two-sided\n"
  else out "PROBE_UNSOUND lagrange_roots collapsed!\n";

val () =
  if r_lr andalso probe_drop_prime andalso probe_drop_disj
  then out "LAGRANGE_ROOTS_OK\n"
  else out "LAGRANGE_ROOTS_FAILED\n";

(* ============================================================================
   THE INVOLUTION-PAIRING LEMMA (the historic wall toward Wilson's theorem),
   with its list-product library, in Isabelle/Pure on the polyml-rs interpreter.
   (test: isabelle_wilson_pairing.rs)
   ----------------------------------------------------------------------------
   The classical proof of Wilson's theorem ((p-1)! = -1 mod p) pairs each element
   of {1,...,p-1} with its multiplicative inverse; only 1 and p-1 are self-paired
   (lagrange_roots), so the rest multiply to 1. Formalizing that pairing -- a
   PRODUCT INVARIANT UNDER AN INVOLUTION, with no finite-set library -- has been
   the wall. Here it is proved by genuine LCF kernel inference, in two parts:

   (1) THE LIST-PRODUCT LIBRARY (a natlist datatype defined on the modular base):
       lprod (list product), lmem, lremove (remove first occurrence, conditional),
       llen, lnodup, and the lemmas the pairing needs -- the KEY one being
         extract : lmem x L ==> lprod L = x * lprod (lremove x L)
       plus mem_remove (membership/removal interaction), llen_remove (removal
       strictly shortens), nodup_remove. Each 0-hyp by list induction. (LIST_LIB_OK)

   (2) THE PAIRING LEMMA: for a modulus p, a list L, and a function inv,
         pairing_lemma : lnodup L
            ==> (!x. lmem x L ==> lmem (inv x) L)              [closed under inv]
            ==> (!x. lmem x L ==> cong p (x * inv x) 1)        [inv x is x's inverse]
            ==> (!x. lmem x L ==> ~(inv x = x))                [fixed-point free]
            ==> (!x. lmem x L ==> inv (inv x) = x)             [inv is an involution]
            ==> cong p (lprod L) 1
       By STRONG INDUCTION on llen L: extract the head a and its partner inv a from
       the tail (inv a in L, inv a <> a, so inv a is in the tail), remove both
       (R = L minus {a, inv a}); lprod L = (a * inv a) * lprod R = 1 * lprod R; R
       still satisfies the hypotheses (inv is injective on L from the involution),
       so lprod R = 1 by the IH (llen R < llen L). The pure combinatorial CORE of
       Wilson's theorem, abstracted from the residue range. (PAIRING_OK)

   Soundness probes confirm the pairing genuinely uses the inverse hypothesis (H3)
   and is conditional. Built on the modular/keystone base (isabelle_mult_group.sml
   + gcd + Euclid's lemma + lagrange_roots) via common::with_mult_group. Proved by
   a 2-phase ultracode fleet (wf_1ef6ffe6-859); re-verified end-to-end by hand.

   NEXT toward full Wilson: construct the list [2..p-2] (or [1..p-1]) and prove it
   is closed under the modular inverse (no element maps outside, none self-pairs
   except the excluded 1, p-1), then assemble (p-1)! = 1 * (prod[2..p-2]) * (p-1)
   = -1. Euler's theorem reuses pairing_lemma directly. This lemma is the hard part.
   ============================================================================ *)

(* ============================================================================
   PHASE 1 (seat ll0) — THE LIST-PRODUCT LIBRARY for Wilson's theorem.
   On the final pow/classical/modular theory thyP (context ctxtP), extend with a
   natlist datatype + lprod/lmem/lremove/llen/lnodup and prove the pairing-
   argument lemmas, each by list_induct.  ONE new final context ctxtLL/ctermLL.
   Mirrors isabelle_list_theory.sml (list_induct) and isabelle_fta_unique.sml
   (in_list intro/elim, all_prime Nil/fwd/bwd, remove1 conditional axioms).
   ============================================================================ *)
val () = out "LIST_LIB_BEGIN\n";

(* ---- type natlist + constructors + operations on top of thyP ---- *)
val thyLLt = Sign.add_types_global [(Binding.name "natlist",0,NoSyn)] thyP;
val natlistN = Sign.full_name thyLLt (Binding.name "natlist");
val natlistT = Type (natlistN,[]);
val llpredT  = natlistT --> oT;

val thyLLc = Sign.add_consts
  [(Binding.name "lnil",    natlistT, NoSyn),
   (Binding.name "lcons",   natT --> natlistT --> natlistT, NoSyn),
   (Binding.name "leq",     natlistT --> natlistT --> oT, NoSyn),
   (Binding.name "lprod",   natlistT --> natT, NoSyn),
   (Binding.name "lmem",    natT --> natlistT --> oT, NoSyn),
   (Binding.name "lremove", natT --> natlistT --> natlistT, NoSyn),
   (Binding.name "llen",    natlistT --> natT, NoSyn),
   (Binding.name "lnodup",  natlistT --> oT, NoSyn)] thyLLt;

fun cnstLL nm T = Const (Sign.full_name thyLLc (Binding.name nm), T);
val lnilC    = cnstLL "lnil" natlistT;
val lconsC   = cnstLL "lcons" (natT --> natlistT --> natlistT); fun lcons h t = lconsC $ h $ t;
val leqC     = cnstLL "leq" (natlistT --> natlistT --> oT);     fun leq s t = leqC $ s $ t;
val lprodC   = cnstLL "lprod" (natlistT --> natT);              fun lprod l = lprodC $ l;
val lmemC    = cnstLL "lmem" (natT --> natlistT --> oT);        fun lmem x l = lmemC $ x $ l;
val lremoveC = cnstLL "lremove" (natT --> natlistT --> natlistT); fun lremove x l = lremoveC $ x $ l;
val llenC    = cnstLL "llen" (natlistT --> natT);              fun llen l = llenC $ l;
val lnodupC  = cnstLL "lnodup" (natlistT --> oT);              fun lnodup l = lnodupC $ l;

(* free vars *)
val aLL = Free ("a", natlistT); val bLL = Free ("b", natlistT);
val lLL = Free ("l", natlistT); val tLL = Free ("t", natlistT);
val xLL = Free ("x", natT);     val yLL = Free ("y", natT);     val hLL = Free ("h", natT);
val PLL = Free ("P", llpredT);

(* ---- list equality: refl + subst ---- *)
val ((_,leq_refl_ax),  tLL1) = Thm.add_axiom_global (Binding.name "leq_refl_ll",
      jT (leq aLL aLL)) thyLLc;
val ((_,leq_subst_ax), tLL2) = Thm.add_axiom_global (Binding.name "leq_subst_ll",
      Logic.mk_implies (jT (leq aLL bLL), Logic.mk_implies (jT (PLL $ aLL), jT (PLL $ bLL)))) tLL1;

(* ---- list induction:  P lnil ==> (!!x l. P l ==> P (lcons x l)) ==> P k ---- *)
val list_induct_prop =
  Logic.mk_implies (jT (PLL $ lnilC),
    Logic.mk_implies
      (Logic.all xLL (Logic.all lLL
         (Logic.mk_implies (jT (PLL $ lLL), jT (PLL $ (lcons xLL lLL))))),
       jT (PLL $ aLL)));
val ((_,list_induct_ax), tLL3) = Thm.add_axiom_global (Binding.name "list_induct_ll", list_induct_prop) tLL2;

(* ---- lprod recursion (oeq) :  lprod lnil = Suc Zero ; lprod (lcons x xs) = mult x (lprod xs) ---- *)
val ((_,lprod_nil_ax),  tLL4) = Thm.add_axiom_global (Binding.name "lprod_nil",
      jT (oeq (lprod lnilC) (suc ZeroC))) tLL3;
val ((_,lprod_cons_ax), tLL5) = Thm.add_axiom_global (Binding.name "lprod_cons",
      jT (oeq (lprod (lcons xLL tLL)) (mult xLL (lprod tLL)))) tLL4;

(* ---- lmem (membership) intro/elim ----
     lmem_nil_elim : jT (lmem x lnil) ==> jT oFalse
     lmem_cons_fwd : jT (lmem x (lcons y ys)) ==> jT (Disj (oeq x y) (lmem x ys))
     lmem_cons_bwd : jT (Disj (oeq x y) (lmem x ys)) ==> jT (lmem x (lcons y ys)) *)
val ((_,lmem_nil_elim_ax), tLL6) = Thm.add_axiom_global (Binding.name "lmem_nil_elim",
      Logic.mk_implies (jT (lmem xLL lnilC), jT oFalseC)) tLL5;
val ((_,lmem_cons_fwd_ax), tLL7) = Thm.add_axiom_global (Binding.name "lmem_cons_fwd",
      Logic.mk_implies (jT (lmem xLL (lcons yLL tLL)),
                        jT (mkDisj (oeq xLL yLL) (lmem xLL tLL)))) tLL6;
val ((_,lmem_cons_bwd_ax), tLL8) = Thm.add_axiom_global (Binding.name "lmem_cons_bwd",
      Logic.mk_implies (jT (mkDisj (oeq xLL yLL) (lmem xLL tLL)),
                        jT (lmem xLL (lcons yLL tLL)))) tLL7;

(* ---- lremove (remove FIRST occurrence) : conditional axioms ----
     lremove_nil      : leq (lremove x lnil) lnil
     lremove_cons_eq  : jT (oeq x y) ==> leq (lremove x (lcons y ys)) ys
     lremove_cons_neq : jT (neg (oeq x y)) ==> leq (lremove x (lcons y ys)) (lcons y (lremove x ys)) *)
val ((_,lremove_nil_ax), tLL9) = Thm.add_axiom_global (Binding.name "lremove_nil",
      jT (leq (lremove xLL lnilC) lnilC)) tLL8;
val ((_,lremove_cons_eq_ax), tLL10) = Thm.add_axiom_global (Binding.name "lremove_cons_eq",
      Logic.mk_implies (jT (oeq xLL yLL),
        jT (leq (lremove xLL (lcons yLL tLL)) tLL))) tLL9;
val ((_,lremove_cons_neq_ax), tLL11) = Thm.add_axiom_global (Binding.name "lremove_cons_neq",
      Logic.mk_implies (jT (neg (oeq xLL yLL)),
        jT (leq (lremove xLL (lcons yLL tLL)) (lcons yLL (lremove xLL tLL))))) tLL10;

(* ---- llen recursion (oeq) :  llen lnil = Zero ; llen (lcons x xs) = Suc (llen xs) ---- *)
val ((_,llen_nil_ax),  tLL12) = Thm.add_axiom_global (Binding.name "llen_nil",
      jT (oeq (llen lnilC) ZeroC)) tLL11;
val ((_,llen_cons_ax), tLL13) = Thm.add_axiom_global (Binding.name "llen_cons",
      jT (oeq (llen (lcons xLL tLL)) (suc (llen tLL)))) tLL12;

(* ---- lnodup intro/elim ----
     lnodup_nil       : jT (lnodup lnil)                               (always true)
     lnodup_cons_fwd  : jT (lnodup (lcons x xs)) ==> jT (Conj (neg (lmem x xs)) (lnodup xs))
     lnodup_cons_bwd  : jT (Conj (neg (lmem x xs)) (lnodup xs)) ==> jT (lnodup (lcons x xs)) *)
val ((_,lnodup_nil_ax), tLL14) = Thm.add_axiom_global (Binding.name "lnodup_nil",
      jT (lnodup lnilC)) tLL13;
val ((_,lnodup_cons_fwd_ax), tLL15) = Thm.add_axiom_global (Binding.name "lnodup_cons_fwd",
      Logic.mk_implies (jT (lnodup (lcons xLL tLL)),
                        jT (mkConj (neg (lmem xLL tLL)) (lnodup tLL)))) tLL14;
val ((_,lnodup_cons_bwd_ax), thyLL) = Thm.add_axiom_global (Binding.name "lnodup_cons_bwd",
      Logic.mk_implies (jT (mkConj (neg (lmem xLL tLL)) (lnodup tLL)),
                        jT (lnodup (lcons xLL tLL)))) tLL15;

(* ---- THE ONE FINAL CONTEXT ---- *)
val ctxtLL  = Proof_Context.init_global thyLL;
val ctermLL = Thm.cterm_of ctxtLL;

val () = out "LIST_LIB_CONSTS_READY\n";

(* ============================================================================
   re-varify EVERY reused base axiom/lemma onto ctxtLL (schematic, valid in thyLL)
   ============================================================================ *)
val oeq_refl_vL    = varify oeq_refl;
val oeq_subst_vL   = varify oeq_subst;
val oeq_sym_vL     = varify oeq_sym;
val oeq_trans_vL   = varify oeq_trans;
val Suc_cong_vL    = varify Suc_cong;
val exI_vL         = varify exI_ax;
val exE_vL         = varify exE_ax;
val oFalse_elim_vL = varify oFalse_elim_ax;
val Suc_neq_Zero_vL= varify Suc_neq_Zero_ax;
val Suc_inj_vL     = varify Suc_inj_ax;
val conjI_vL       = varify conjI_ax;
val conjunct1_vL   = varify conjunct1_ax;
val conjunct2_vL   = varify conjunct2_ax;
val disjI1_vL      = varify disjI1_ax;
val disjI2_vL      = varify disjI2_ax;
val disjE_vL       = varify disjE_ax;
val mp_vL          = varify mp_ax;
val impI_vL        = varify impI_ax;
val ex_middle_vL   = varify ex_middle_ax;
val add_0_vL       = varify add_0;
val add_Suc_vL     = varify add_Suc;
val add_0_right_vL = varify add_0_right;
val mult_0_right_vL= varify mult_0_right;
(* list machinery *)
val leq_refl_vL    = varify leq_refl_ax;
val leq_subst_vL   = varify leq_subst_ax;
val list_induct_vL = varify list_induct_ax;
val lprod_nil_vL   = varify lprod_nil_ax;
val lprod_cons_vL  = varify lprod_cons_ax;
val lmem_nil_elim_vL = varify lmem_nil_elim_ax;
val lmem_cons_fwd_vL = varify lmem_cons_fwd_ax;
val lmem_cons_bwd_vL = varify lmem_cons_bwd_ax;
val lremove_nil_vL   = varify lremove_nil_ax;
val lremove_cons_eq_vL  = varify lremove_cons_eq_ax;
val lremove_cons_neq_vL = varify lremove_cons_neq_ax;
val llen_nil_vL    = varify llen_nil_ax;
val llen_cons_vL   = varify llen_cons_ax;
val lnodup_nil_vL  = varify lnodup_nil_ax;
val lnodup_cons_fwd_vL = varify lnodup_cons_fwd_ax;
val lnodup_cons_bwd_vL = varify lnodup_cons_bwd_ax;

(* ============================================================================
   GROUND INSTANTIATORS (final context).
   ============================================================================ *)
fun lprodNil_at ()       = lprod_nil_vL;
fun lprodCons_at (h,t)   = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("x",0), ctermLL h),(("t",0), ctermLL t)] lprod_cons_vL);
fun llenNil_at ()        = llen_nil_vL;
fun llenCons_at (h,t)    = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("x",0), ctermLL h),(("t",0), ctermLL t)] llen_cons_vL);
fun add0_at t            = beta_norm (Drule.infer_instantiate ctxtLL [(("n",0), ctermLL t)] add_0_vL);
fun addSuc_at (mt,nt)    = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("m",0), ctermLL mt),(("n",0), ctermLL nt)] add_Suc_vL);

(* lmem intro/elim *)
fun lmemNilElim_at x     = beta_norm (Drule.infer_instantiate ctxtLL [(("x",0), ctermLL x)] lmem_nil_elim_vL);
fun lmemConsFwd_at (x,y,t) = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("x",0), ctermLL x),(("y",0), ctermLL y),(("t",0), ctermLL t)] lmem_cons_fwd_vL);
fun lmemConsBwd_at (x,y,t) = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("x",0), ctermLL x),(("y",0), ctermLL y),(("t",0), ctermLL t)] lmem_cons_bwd_vL);
(* lremove conditional *)
val lremoveNil = lremove_nil_vL;
fun lremoveNil_at x      = beta_norm (Drule.infer_instantiate ctxtLL [(("x",0), ctermLL x)] lremove_nil_vL);
fun lremoveConsEq_at (x,y,t) = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("x",0), ctermLL x),(("y",0), ctermLL y),(("t",0), ctermLL t)] lremove_cons_eq_vL);
fun lremoveConsNeq_at (x,y,t) = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("x",0), ctermLL x),(("y",0), ctermLL y),(("t",0), ctermLL t)] lremove_cons_neq_vL);
(* lnodup intro/elim *)
fun lnodupConsFwd_at (x,t) = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("x",0), ctermLL x),(("t",0), ctermLL t)] lnodup_cons_fwd_vL);
fun lnodupConsBwd_at (x,t) = beta_norm (Drule.infer_instantiate ctxtLL
                            [(("x",0), ctermLL x),(("t",0), ctermLL t)] lnodup_cons_bwd_vL);

(* ex_middle / disj / conj helpers on ctxtLL *)
fun ex_middle_at At = beta_norm (Drule.infer_instantiate ctxtLL [(("A",0), ctermLL At)] ex_middle_vL);
fun disjE_elim (At, Bt, Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("A",0), ctermLL At), (("B",0), ctermLL Bt), (("C",0), ctermLL Ct)] disjE_vL)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB end;
fun disjI1_at (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtLL
        [(("A",0), ctermLL At),(("B",0), ctermLL Bt)] disjI1_vL)) h;
fun disjI2_at (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtLL
        [(("A",0), ctermLL At),(("B",0), ctermLL Bt)] disjI2_vL)) h;
fun conjI_at (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("A",0), ctermLL At),(("B",0), ctermLL Bt)] conjI_vL)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_at (At,Bt) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtLL
        [(("A",0), ctermLL At),(("B",0), ctermLL Bt)] conjunct1_vL)) h;
fun conjunct2_at (At,Bt) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtLL
        [(("A",0), ctermLL At),(("B",0), ctermLL Bt)] conjunct2_vL)) h;
fun oFalse_elim_at rT = beta_norm (Drule.infer_instantiate ctxtLL [(("R",0), ctermLL rT)] oFalse_elim_vL);
fun mp_at (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("A",0), ctermLL At),(("B",0), ctermLL Bt)] mp_vL)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_at (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("A",0), ctermLL At),(("B",0), ctermLL Bt)] impI_vL)
  in Thm.implies_elim inst hImpThm end;

(* ---- list-equality lemmas leq_sym / leq_trans (from leq_subst) ---- *)
val leq_sym =
  let
    val aF = Free("a",natlistT); val bF = Free("b",natlistT);
    val Pabs = Abs("z", natlistT, leq (Bound 0) aF);
    val inst = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Pabs), (("a",0), ctermLL aF), (("b",0), ctermLL bF)] leq_subst_vL);
    val refl_aa = beta_norm (Drule.infer_instantiate ctxtLL [(("a",0), ctermLL aF)] leq_refl_vL);
    val step = inst OF [Thm.assume (ctermLL (jT (leq aF bF))), refl_aa];
  in varify (Thm.implies_intr (ctermLL (jT (leq aF bF))) step) end;

val leq_trans =
  let
    val aF = Free("a",natlistT); val bF = Free("b",natlistT); val cF = Free("c",natlistT);
    val Pabs = Abs("z", natlistT, leq aF (Bound 0));
    val inst = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Pabs), (("a",0), ctermLL bF), (("b",0), ctermLL cF)] leq_subst_vL);
    val H1 = Thm.assume (ctermLL (jT (leq aF bF)));
    val H2 = Thm.assume (ctermLL (jT (leq bF cF)));
    val step = inst OF [H2, H1];
    val t0 = Thm.implies_intr (ctermLL (jT (leq bF cF))) step;
    val t1 = Thm.implies_intr (ctermLL (jT (leq aF bF))) t0;
  in varify t1 end;

val () = out "LIST_LIB_HELPERS_READY\n";

(* ============================================================================
   SANITY: recursion equations instantiate cleanly (0-hyp, aconv intended).
   ============================================================================ *)
val xV = Var (("x",0), natT);
val tV = Var (("t",0), natlistT);
val yV = Var (("y",0), natT);
fun chk0 (nm, th, intended) =
  let val nh = length (Thm.hyps_of th); val ac = (Thm.prop_of th) aconv intended;
  in if nh=0 andalso ac then (out ("OK "^nm^"\n"); true)
     else (out ("FAIL "^nm^" (hyps="^Int.toString nh^" aconv="^Bool.toString ac^")\n"
                ^"  got      = "^Syntax.string_of_term ctxtLL (Thm.prop_of th)^"\n"
                ^"  intended = "^Syntax.string_of_term ctxtLL intended^"\n"); false) end;

val r_lprod_nil  = chk0 ("lprod_nil",  lprod_nil_vL,  jT (oeq (lprod lnilC) (suc ZeroC)));
val r_lprod_cons = chk0 ("lprod_cons", lprod_cons_vL, jT (oeq (lprod (lcons xV tV)) (mult xV (lprod tV))));
val r_llen_nil   = chk0 ("llen_nil",   llen_nil_vL,   jT (oeq (llen lnilC) ZeroC));
val r_llen_cons  = chk0 ("llen_cons",  llen_cons_vL,  jT (oeq (llen (lcons xV tV)) (suc (llen tV))));
val () = out "LIST_LIB_SANITY_DONE\n";

(* ============================================================================
   mult helpers on ctxtLL (for extract).
   ============================================================================ *)
val mult_comm_vL  = varify mult_comm;
val mult_assoc_vL = varify mult_assoc;
fun multcomm_at (mt,nt)     = beta_norm (Drule.infer_instantiate ctxtLL
        [(("m",0), ctermLL mt),(("n",0), ctermLL nt)] mult_comm_vL);
fun multassoc_at (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtLL
        [(("m",0), ctermLL mt),(("n",0), ctermLL nt),(("k",0), ctermLL kt)] mult_assoc_vL);
(* mult-cong on LEFT operand: oeq p q ==> oeq (mult p k) (mult q k) *)
fun mult_cong_l (pT,qT,kT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT));
      val inst = beta_norm (Drule.infer_instantiate ctxtLL
            [(("P",0), ctermLL Pabs), (("a",0), ctermLL pT), (("b",0), ctermLL qT)] oeq_subst_vL);
      val refl0 = beta_norm (Drule.infer_instantiate ctxtLL [(("a",0), ctermLL (mult pT kT))] oeq_refl_vL);
  in inst OF [hpq, refl0] end;
(* mult-cong on RIGHT operand: oeq p q ==> oeq (mult h p) (mult h q) *)
fun mult_cong_r (hT,pT,qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)));
      val inst = beta_norm (Drule.infer_instantiate ctxtLL
            [(("P",0), ctermLL Pabs), (("a",0), ctermLL pT), (("b",0), ctermLL qT)] oeq_subst_vL);
      val refl0 = beta_norm (Drule.infer_instantiate ctxtLL [(("a",0), ctermLL (mult hT pT))] oeq_refl_vL);
  in inst OF [hpq, refl0] end;
(* lprod-cong (via leq_subst): leq a b ==> oeq (lprod a) (lprod b) *)
fun lprod_cong (aT,bT) hab =
  let val Pabs = Abs("z", natlistT, oeq (lprod aT) (lprod (Bound 0)));
      val inst = beta_norm (Drule.infer_instantiate ctxtLL
            [(("P",0), ctermLL Pabs), (("a",0), ctermLL aT), (("b",0), ctermLL bT)] leq_subst_vL);
      val refl0 = beta_norm (Drule.infer_instantiate ctxtLL [(("a",0), ctermLL (lprod aT))] oeq_refl_vL);
  in inst OF [hab, refl0] end;
(* llen-cong (via leq_subst): leq a b ==> oeq (llen a) (llen b) *)
fun llen_cong (aT,bT) hab =
  let val Pabs = Abs("z", natlistT, oeq (llen aT) (llen (Bound 0)));
      val inst = beta_norm (Drule.infer_instantiate ctxtLL
            [(("P",0), ctermLL Pabs), (("a",0), ctermLL aT), (("b",0), ctermLL bT)] leq_subst_vL);
      val refl0 = beta_norm (Drule.infer_instantiate ctxtLL [(("a",0), ctermLL (llen aT))] oeq_refl_vL);
  in inst OF [hab, refl0] end;

val () = out "LIST_LIB_MULT_HELPERS_READY\n";

(* ============================================================================
   (1) extract : lmem x L ==> oeq (lprod L) (mult x (lprod (lremove x L)))
       BY list_induct on L.  THE key lemma.
   ============================================================================ *)
val extract =
  let
    val xF = Free("x", natT);
    fun concBody zt = oeq (lprod zt) (mult xF (lprod (lremove xF zt)));
    fun predBody zt = mkImp (lmem xF zt) (concBody zt);
    val Qpred = Abs("z", natlistT, predBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Qpred), (("a",0), ctermLL LF)] list_induct_vL);
    val base =
      let
        val hmem = Thm.assume (ctermLL (jT (lmem xF lnilC)));
        val ff   = Thm.implies_elim (lmemNilElim_at xF) hmem;
        val conc = Thm.implies_elim (oFalse_elim_at (concBody lnilC)) ff;
        val dis  = Thm.implies_intr (ctermLL (jT (lmem xF lnilC))) conc;
      in impI_at (lmem xF lnilC, concBody lnilC) dis end;
    val yF = Free("y", natT); val tF = Free("t", natlistT);
    val ihprop = jT (predBody tF);
    val IH = Thm.assume (ctermLL ihprop);
    val stepConcl =
      let
        val hmem = Thm.assume (ctermLL (jT (lmem xF (lcons yF tF))));
        val disjmem = Thm.implies_elim (lmemConsFwd_at (xF, yF, tF)) hmem;
        val lpc = lprodCons_at (yF, tF);
        val caseEq =
          let
            val heq = Thm.assume (ctermLL (jT (oeq xF yF)));
            val lrm = Thm.implies_elim (lremoveConsEq_at (xF, yF, tF)) heq;
            val lp_lrm = lprod_cong (lremove xF (lcons yF tF), tF) lrm;
            val rhs_eq = mult_cong_r (xF, lprod (lremove xF (lcons yF tF)), lprod tF) lp_lrm;
            val yx = oeq_sym OF [heq];
            val my_mx = mult_cong_l (yF, xF, lprod tF) yx;
            val rhs_eq_sym = oeq_sym OF [rhs_eq];
            val conc = oeq_trans OF [oeq_trans OF [lpc, my_mx], rhs_eq_sym];
          in Thm.implies_intr (ctermLL (jT (oeq xF yF))) conc end;
        val caseNeq =
          let
            val hneq = Thm.assume (ctermLL (jT (neg (oeq xF yF))));
            val memT =
              let
                val cA = let val hxy = Thm.assume (ctermLL (jT (oeq xF yF)))
                             val ff  = mp_at (oeq xF yF, oFalseC) hneq hxy
                             val r   = Thm.implies_elim (oFalse_elim_at (lmem xF tF)) ff
                         in Thm.implies_intr (ctermLL (jT (oeq xF yF))) r end;
                val cB = let val hm = Thm.assume (ctermLL (jT (lmem xF tF)))
                         in Thm.implies_intr (ctermLL (jT (lmem xF tF))) hm end;
              in disjE_elim (oeq xF yF, lmem xF tF, lmem xF tF) disjmem cA cB end;
            val ihconc = mp_at (lmem xF tF, concBody tF) IH memT;
            val lrm = Thm.implies_elim (lremoveConsNeq_at (xF, yF, tF)) hneq;
            val rmtl = lremove xF tF;
            val lp_lrm = lprod_cong (lremove xF (lcons yF tF), lcons yF rmtl) lrm;
            val lp_cons = lprodCons_at (yF, rmtl);
            val lp_lrm2 = oeq_trans OF [lp_lrm, lp_cons];
            val rhs1 = mult_cong_r (xF, lprod (lremove xF (lcons yF tF)), mult yF (lprod rmtl)) lp_lrm2;
            val q = lprod rmtl;
            val mut = mult_cong_r (yF, lprod tF, mult xF q) ihconc;
            val lhs1 = oeq_trans OF [lpc, mut];
            val assoc1 = multassoc_at (yF, xF, q);
            val assoc1s = oeq_sym OF [assoc1];
            val comm = multcomm_at (yF, xF);
            val commc = mult_cong_l (mult yF xF, mult xF yF, q) comm;
            val assoc2 = multassoc_at (xF, yF, q);
            val bridge = oeq_trans OF [oeq_trans OF [assoc1s, commc], assoc2];
            val rhs1s = oeq_sym OF [rhs1];
            val conc = oeq_trans OF [oeq_trans OF [lhs1, bridge], rhs1s];
          in Thm.implies_intr (ctermLL (jT (neg (oeq xF yF)))) conc end;
        val em = ex_middle_at (oeq xF yF);
        val conc = disjE_elim (oeq xF yF, neg (oeq xF yF), concBody (lcons yF tF)) em caseEq caseNeq;
        val dis = Thm.implies_intr (ctermLL (jT (lmem xF (lcons yF tF)))) conc;
      in impI_at (lmem xF (lcons yF tF), concBody (lcons yF tF)) dis end;
    val step1 = Thm.forall_intr (ctermLL yF)
                  (Thm.forall_intr (ctermLL tF) (Thm.implies_intr (ctermLL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hmemL = Thm.assume (ctermLL (jT (lmem xF LF)));
    val concL = mp_at (lmem xF LF, concBody LF) r2 hmemL;
    val d1 = Thm.implies_intr (ctermLL (jT (lmem xF LF))) concL;
  in varify d1 end;

val extract_v = varify extract;
val xVe = Var (("x",0), natT);  val LVe = Var (("L",0), natlistT);
val i_extract = Logic.mk_implies (jT (lmem xVe LVe),
      jT (oeq (lprod LVe) (mult xVe (lprod (lremove xVe LVe)))));
val r_extract = chk0 ("extract", extract, i_extract);
val () = out "LIST_LIB_EXTRACT_DONE\n";

(* ============================================================================
   transfer helpers : move an o-predicate across a leq list-equality.
   ============================================================================ *)
fun lmem_transfer (yT, aT, bT) hleq hmem =
  let val Pabs = Abs("z", natlistT, lmem yT (Bound 0));
      val inst = beta_norm (Drule.infer_instantiate ctxtLL
            [(("P",0), ctermLL Pabs), (("a",0), ctermLL aT), (("b",0), ctermLL bT)] leq_subst_vL);
  in inst OF [hleq, hmem] end;
fun lnodup_transfer (aT, bT) hleq hnd =
  let val Pabs = Abs("z", natlistT, lnodup (Bound 0));
      val inst = beta_norm (Drule.infer_instantiate ctxtLL
            [(("P",0), ctermLL Pabs), (("a",0), ctermLL aT), (("b",0), ctermLL bT)] leq_subst_vL);
  in inst OF [hleq, hnd] end;

(* ============================================================================
   (2a) mem_remove_fwd : lmem y (lremove x L) ==> lmem y L   (BY list_induct on L)
   ============================================================================ *)
val mem_remove_fwd =
  let
    val xF = Free("x", natT); val yF = Free("y", natT);
    fun concBody zt = mkImp (lmem yF (lremove xF zt)) (lmem yF zt);
    val Qpred = Abs("z", natlistT, concBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Qpred), (("a",0), ctermLL LF)] list_induct_vL);
    val base =
      let
        val hassm = Thm.assume (ctermLL (jT (lmem yF (lremove xF lnilC))));
        val lrm = lremoveNil_at xF;
        val mem_lnil = lmem_transfer (yF, lremove xF lnilC, lnilC) lrm hassm;
        val ff  = Thm.implies_elim (lmemNilElim_at yF) mem_lnil;
        val conc = Thm.implies_elim (oFalse_elim_at (lmem yF lnilC)) ff;
        val dis  = Thm.implies_intr (ctermLL (jT (lmem yF (lremove xF lnilC)))) conc;
      in impI_at (lmem yF (lremove xF lnilC), lmem yF lnilC) dis end;
    val hF = Free("h", natT); val tF = Free("t", natlistT);
    val ihprop = jT (concBody tF);
    val IH = Thm.assume (ctermLL ihprop);
    val stepConcl =
      let
        val hassm = Thm.assume (ctermLL (jT (lmem yF (lremove xF (lcons hF tF)))));
        val caseEq =
          let
            val heq = Thm.assume (ctermLL (jT (oeq xF hF)));
            val lrm = Thm.implies_elim (lremoveConsEq_at (xF, hF, tF)) heq;
            val mem_t = lmem_transfer (yF, lremove xF (lcons hF tF), tF) lrm hassm;
            val dj  = disjI2_at (oeq yF hF, lmem yF tF) mem_t;
            val res = Thm.implies_elim (lmemConsBwd_at (yF, hF, tF)) dj;
          in Thm.implies_intr (ctermLL (jT (oeq xF hF))) res end;
        val caseNeq =
          let
            val hneq = Thm.assume (ctermLL (jT (neg (oeq xF hF))));
            val lrm = Thm.implies_elim (lremoveConsNeq_at (xF, hF, tF)) hneq;
            val mem_cons = lmem_transfer (yF, lremove xF (lcons hF tF), lcons hF (lremove xF tF)) lrm hassm;
            val dj = Thm.implies_elim (lmemConsFwd_at (yF, hF, lremove xF tF)) mem_cons;
            val cA = let val hyh = Thm.assume (ctermLL (jT (oeq yF hF)))
                         val r = Thm.implies_elim (lmemConsBwd_at (yF, hF, tF))
                                   (disjI1_at (oeq yF hF, lmem yF tF) hyh)
                     in Thm.implies_intr (ctermLL (jT (oeq yF hF))) r end;
            val cB = let val hmr = Thm.assume (ctermLL (jT (lmem yF (lremove xF tF))))
                         val mt  = mp_at (lmem yF (lremove xF tF), lmem yF tF) IH hmr
                         val r = Thm.implies_elim (lmemConsBwd_at (yF, hF, tF))
                                   (disjI2_at (oeq yF hF, lmem yF tF) mt)
                     in Thm.implies_intr (ctermLL (jT (lmem yF (lremove xF tF)))) r end;
            val res = disjE_elim (oeq yF hF, lmem yF (lremove xF tF), lmem yF (lcons hF tF)) dj cA cB;
          in Thm.implies_intr (ctermLL (jT (neg (oeq xF hF)))) res end;
        val em = ex_middle_at (oeq xF hF);
        val conc = disjE_elim (oeq xF hF, neg (oeq xF hF), lmem yF (lcons hF tF)) em caseEq caseNeq;
        val dis = Thm.implies_intr (ctermLL (jT (lmem yF (lremove xF (lcons hF tF))))) conc;
      in impI_at (lmem yF (lremove xF (lcons hF tF)), lmem yF (lcons hF tF)) dis end;
    val step1 = Thm.forall_intr (ctermLL hF)
                  (Thm.forall_intr (ctermLL tF) (Thm.implies_intr (ctermLL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hassmL = Thm.assume (ctermLL (jT (lmem yF (lremove xF LF))));
    val concL = mp_at (lmem yF (lremove xF LF), lmem yF LF) r2 hassmL;
    val d1 = Thm.implies_intr (ctermLL (jT (lmem yF (lremove xF LF)))) concL;
  in varify d1 end;

val mem_remove_fwd_v = varify mem_remove_fwd;
val yVm = Var (("y",0), natT); val xVm = Var (("x",0), natT); val LVm = Var (("L",0), natlistT);
val i_mem_remove_fwd = Logic.mk_implies (jT (lmem yVm (lremove xVm LVm)), jT (lmem yVm LVm));
val r_mem_remove_fwd = chk0 ("mem_remove_fwd", mem_remove_fwd, i_mem_remove_fwd);
val () = out "LIST_LIB_MEM_REMOVE_FWD_DONE\n";

(* exI / add_0_right helpers on ctxtLL *)
fun exI_at Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("P",0), ctermLL Pabs), (("a",0), ctermLL at)] exI_vL)
  in Thm.implies_elim inst hbody end;
fun add0r_at t = beta_norm (Drule.infer_instantiate ctxtLL [(("n",0), ctermLL t)] add_0_right_vL);
fun oeq_subst_at (Pabs, aT, bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("P",0), ctermLL Pabs), (("a",0), ctermLL aT), (("b",0), ctermLL bT)] oeq_subst_vL)
  in inst OF [hab, hPa] end;

(* ============================================================================
   (2b) mem_remove_bwd : (Conj (lmem y L) (neg (oeq y x))) ==> lmem y (lremove x L)
        BY list_induct on L.  (the direction Phase 2 needs)
   ============================================================================ *)
val mem_remove_bwd =
  let
    val xF = Free("x", natT); val yF = Free("y", natT);
    fun hypBody zt = mkConj (lmem yF zt) (neg (oeq yF xF));
    fun concBody zt = mkImp (hypBody zt) (lmem yF (lremove xF zt));
    val Qpred = Abs("z", natlistT, concBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Qpred), (("a",0), ctermLL LF)] list_induct_vL);
    val base =
      let
        val hh = Thm.assume (ctermLL (jT (hypBody lnilC)));
        val mem = conjunct1_at (lmem yF lnilC, neg (oeq yF xF)) hh;
        val ff  = Thm.implies_elim (lmemNilElim_at yF) mem;
        val conc = Thm.implies_elim (oFalse_elim_at (lmem yF (lremove xF lnilC))) ff;
        val dis = Thm.implies_intr (ctermLL (jT (hypBody lnilC))) conc;
      in impI_at (hypBody lnilC, lmem yF (lremove xF lnilC)) dis end;
    val hF = Free("h", natT); val tF = Free("t", natlistT);
    val ihprop = jT (concBody tF);
    val IH = Thm.assume (ctermLL ihprop);
    val stepConcl =
      let
        val hh = Thm.assume (ctermLL (jT (hypBody (lcons hF tF))));
        val mem = conjunct1_at (lmem yF (lcons hF tF), neg (oeq yF xF)) hh;
        val hneqYX = conjunct2_at (lmem yF (lcons hF tF), neg (oeq yF xF)) hh;
        val djmem = Thm.implies_elim (lmemConsFwd_at (yF, hF, tF)) mem;
        val caseEqXH =
          let
            val heq = Thm.assume (ctermLL (jT (oeq xF hF)));
            val lrm = Thm.implies_elim (lremoveConsEq_at (xF, hF, tF)) heq;
            val mem_t =
              let
                val cA = let val hyh = Thm.assume (ctermLL (jT (oeq yF hF)))
                             val hx = oeq_sym OF [heq]
                             val yx = oeq_trans OF [hyh, hx]
                             val ff = mp_at (oeq yF xF, oFalseC) hneqYX yx
                             val r  = Thm.implies_elim (oFalse_elim_at (lmem yF tF)) ff
                         in Thm.implies_intr (ctermLL (jT (oeq yF hF))) r end;
                val cB = let val hm = Thm.assume (ctermLL (jT (lmem yF tF)))
                         in Thm.implies_intr (ctermLL (jT (lmem yF tF))) hm end;
              in disjE_elim (oeq yF hF, lmem yF tF, lmem yF tF) djmem cA cB end;
            val lrm_s = leq_sym OF [lrm];
            val res = lmem_transfer (yF, tF, lremove xF (lcons hF tF)) lrm_s mem_t;
          in Thm.implies_intr (ctermLL (jT (oeq xF hF))) res end;
        val caseNeqXH =
          let
            val hneqXH = Thm.assume (ctermLL (jT (neg (oeq xF hF))));
            val lrm = Thm.implies_elim (lremoveConsNeq_at (xF, hF, tF)) hneqXH;
            val target = lcons hF (lremove xF tF);
            val mem_target =
              let
                val cA = let val hyh = Thm.assume (ctermLL (jT (oeq yF hF)))
                             val r = Thm.implies_elim (lmemConsBwd_at (yF, hF, lremove xF tF))
                                       (disjI1_at (oeq yF hF, lmem yF (lremove xF tF)) hyh)
                         in Thm.implies_intr (ctermLL (jT (oeq yF hF))) r end;
                val cB = let val hmt = Thm.assume (ctermLL (jT (lmem yF tF)))
                             val cj  = conjI_at (lmem yF tF, neg (oeq yF xF)) hmt hneqYX
                             val mr  = mp_at (hypBody tF, lmem yF (lremove xF tF)) IH cj
                             val r = Thm.implies_elim (lmemConsBwd_at (yF, hF, lremove xF tF))
                                       (disjI2_at (oeq yF hF, lmem yF (lremove xF tF)) mr)
                         in Thm.implies_intr (ctermLL (jT (lmem yF tF))) r end;
              in disjE_elim (oeq yF hF, lmem yF tF, lmem yF target) djmem cA cB end;
            val lrm_s = leq_sym OF [lrm];
            val res = lmem_transfer (yF, target, lremove xF (lcons hF tF)) lrm_s mem_target;
          in Thm.implies_intr (ctermLL (jT (neg (oeq xF hF)))) res end;
        val em = ex_middle_at (oeq xF hF);
        val conc = disjE_elim (oeq xF hF, neg (oeq xF hF), lmem yF (lremove xF (lcons hF tF))) em caseEqXH caseNeqXH;
        val dis = Thm.implies_intr (ctermLL (jT (hypBody (lcons hF tF)))) conc;
      in impI_at (hypBody (lcons hF tF), lmem yF (lremove xF (lcons hF tF))) dis end;
    val step1 = Thm.forall_intr (ctermLL hF)
                  (Thm.forall_intr (ctermLL tF) (Thm.implies_intr (ctermLL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hhL = Thm.assume (ctermLL (jT (hypBody LF)));
    val concL = mp_at (hypBody LF, lmem yF (lremove xF LF)) r2 hhL;
    val d1 = Thm.implies_intr (ctermLL (jT (hypBody LF))) concL;
  in varify d1 end;

val i_mem_remove_bwd = Logic.mk_implies (jT (mkConj (lmem yVm LVm) (neg (oeq yVm xVm))),
      jT (lmem yVm (lremove xVm LVm)));
val r_mem_remove_bwd = chk0 ("mem_remove_bwd", mem_remove_bwd, i_mem_remove_bwd);
val () = out "LIST_LIB_MEM_REMOVE_BWD_DONE\n";

(* ============================================================================
   (3) llen_remove : lmem x L ==> lt (llen (lremove x L)) (llen L)
       via stronger oeq (llen L)(suc (llen (lremove x L))) + exI witness Zero.
   ============================================================================ *)
val llen_remove_eq =
  let
    val xF = Free("x", natT);
    fun concBody zt = oeq (llen zt) (suc (llen (lremove xF zt)));
    fun predBody zt = mkImp (lmem xF zt) (concBody zt);
    val Qpred = Abs("z", natlistT, predBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Qpred), (("a",0), ctermLL LF)] list_induct_vL);
    val base =
      let
        val hmem = Thm.assume (ctermLL (jT (lmem xF lnilC)));
        val ff   = Thm.implies_elim (lmemNilElim_at xF) hmem;
        val conc = Thm.implies_elim (oFalse_elim_at (concBody lnilC)) ff;
        val dis  = Thm.implies_intr (ctermLL (jT (lmem xF lnilC))) conc;
      in impI_at (lmem xF lnilC, concBody lnilC) dis end;
    val hF = Free("h", natT); val tF = Free("t", natlistT);
    val ihprop = jT (predBody tF);
    val IH = Thm.assume (ctermLL ihprop);
    val stepConcl =
      let
        val hmem = Thm.assume (ctermLL (jT (lmem xF (lcons hF tF))));
        val djmem = Thm.implies_elim (lmemConsFwd_at (xF, hF, tF)) hmem;
        val llc = llenCons_at (hF, tF);
        val caseEq =
          let
            val heq = Thm.assume (ctermLL (jT (oeq xF hF)));
            val lrm = Thm.implies_elim (lremoveConsEq_at (xF, hF, tF)) heq;
            val lc  = llen_cong (lremove xF (lcons hF tF), tF) lrm;
            val sc  = Suc_cong OF [lc];
            val scs = oeq_sym OF [sc];
            val conc = oeq_trans OF [llc, scs];
          in Thm.implies_intr (ctermLL (jT (oeq xF hF))) conc end;
        val caseNeq =
          let
            val hneq = Thm.assume (ctermLL (jT (neg (oeq xF hF))));
            val memT =
              let
                val cA = let val hxh = Thm.assume (ctermLL (jT (oeq xF hF)))
                             val ff  = mp_at (oeq xF hF, oFalseC) hneq hxh
                             val r   = Thm.implies_elim (oFalse_elim_at (lmem xF tF)) ff
                         in Thm.implies_intr (ctermLL (jT (oeq xF hF))) r end;
                val cB = let val hm = Thm.assume (ctermLL (jT (lmem xF tF)))
                         in Thm.implies_intr (ctermLL (jT (lmem xF tF))) hm end;
              in disjE_elim (oeq xF hF, lmem xF tF, lmem xF tF) djmem cA cB end;
            val ihconc = mp_at (lmem xF tF, concBody tF) IH memT;
            val lrm = Thm.implies_elim (lremoveConsNeq_at (xF, hF, tF)) hneq;
            val lc  = llen_cong (lremove xF (lcons hF tF), lcons hF (lremove xF tF)) lrm;
            val lcc = llenCons_at (hF, lremove xF tF);
            val rhs_in = oeq_trans OF [lc, lcc];
            val rhs = Suc_cong OF [rhs_in];
            val lhs_in = Suc_cong OF [ihconc];
            val lhs = oeq_trans OF [llc, lhs_in];
            val rhs_s = oeq_sym OF [rhs];
            val conc = oeq_trans OF [lhs, rhs_s];
          in Thm.implies_intr (ctermLL (jT (neg (oeq xF hF)))) conc end;
        val em = ex_middle_at (oeq xF hF);
        val conc = disjE_elim (oeq xF hF, neg (oeq xF hF), concBody (lcons hF tF)) em caseEq caseNeq;
        val dis = Thm.implies_intr (ctermLL (jT (lmem xF (lcons hF tF)))) conc;
      in impI_at (lmem xF (lcons hF tF), concBody (lcons hF tF)) dis end;
    val step1 = Thm.forall_intr (ctermLL hF)
                  (Thm.forall_intr (ctermLL tF) (Thm.implies_intr (ctermLL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hmemL = Thm.assume (ctermLL (jT (lmem xF LF)));
    val concL = mp_at (lmem xF LF, concBody LF) r2 hmemL;
    val d1 = Thm.implies_intr (ctermLL (jT (lmem xF LF))) concL;
  in varify d1 end;

val llen_remove =
  let
    val xF = Free("x", natT); val LF = Free("L", natlistT);
    val heq = Thm.assume (ctermLL (jT (lmem xF LF)));
    val eqv = varify llen_remove_eq;
    val streq = beta_norm (Drule.infer_instantiate ctxtLL
          [(("x",0), ctermLL xF), (("L",0), ctermLL LF)] eqv);
    val oeqLL = Thm.implies_elim streq heq;
    val aT = llen (lremove xF LF); val bT = llen LF;
    val a0r = add0r_at (suc aT);
    val a0rs = oeq_sym OF [a0r];
    val body = oeq_trans OF [oeqLL, a0rs];
    val Pabs = Abs("p", natT, oeq bT (add (suc aT) (Bound 0)));
    val ltThm = exI_at Pabs ZeroC body;
    val d1 = Thm.implies_intr (ctermLL (jT (lmem xF LF))) ltThm;
  in varify d1 end;

val i_llen_remove = Logic.mk_implies (jT (lmem xVm LVm), jT (lt (llen (lremove xVm LVm)) (llen LVm)));
val r_llen_remove = chk0 ("llen_remove", llen_remove, i_llen_remove);
val () = out "LIST_LIB_LLEN_REMOVE_DONE\n";

(* ============================================================================
   (4) nodup_remove : lnodup L ==> lnodup (lremove x L)   (BY list_induct on L)
   ============================================================================ *)
val nodup_remove =
  let
    val xF = Free("x", natT);
    fun concBody zt = mkImp (lnodup zt) (lnodup (lremove xF zt));
    val Qpred = Abs("z", natlistT, concBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Qpred), (("a",0), ctermLL LF)] list_induct_vL);
    val base =
      let
        val hnd = Thm.assume (ctermLL (jT (lnodup lnilC)));
        val lrm = lremoveNil_at xF;
        val lrm_s = leq_sym OF [lrm];
        val res = lnodup_transfer (lnilC, lremove xF lnilC) lrm_s hnd;
        val dis = Thm.implies_intr (ctermLL (jT (lnodup lnilC))) res;
      in impI_at (lnodup lnilC, lnodup (lremove xF lnilC)) dis end;
    val hF = Free("h", natT); val tF = Free("t", natlistT);
    val ihprop = jT (concBody tF);
    val IH = Thm.assume (ctermLL ihprop);
    val stepConcl =
      let
        val hnd = Thm.assume (ctermLL (jT (lnodup (lcons hF tF))));
        val cj  = Thm.implies_elim (lnodupConsFwd_at (hF, tF)) hnd;
        val nmem = conjunct1_at (neg (lmem hF tF), lnodup tF) cj;
        val ndt  = conjunct2_at (neg (lmem hF tF), lnodup tF) cj;
        val caseEq =
          let
            val heq = Thm.assume (ctermLL (jT (oeq xF hF)));
            val lrm = Thm.implies_elim (lremoveConsEq_at (xF, hF, tF)) heq;
            val lrm_s = leq_sym OF [lrm];
            val res = lnodup_transfer (tF, lremove xF (lcons hF tF)) lrm_s ndt;
          in Thm.implies_intr (ctermLL (jT (oeq xF hF))) res end;
        val caseNeq =
          let
            val hneq = Thm.assume (ctermLL (jT (neg (oeq xF hF))));
            val lrm = Thm.implies_elim (lremoveConsNeq_at (xF, hF, tF)) hneq;
            val ndrt = mp_at (lnodup tF, lnodup (lremove xF tF)) IH ndt;
            val mrf = beta_norm (Drule.infer_instantiate ctxtLL
                  [(("y",0), ctermLL hF), (("x",0), ctermLL xF), (("L",0), ctermLL tF)] mem_remove_fwd_v);
            val nmem_rt =
              let val hassm = Thm.assume (ctermLL (jT (lmem hF (lremove xF tF))))
                  val inT   = Thm.implies_elim mrf hassm
                  val ff    = mp_at (lmem hF tF, oFalseC) nmem inT
                  val dis   = Thm.implies_intr (ctermLL (jT (lmem hF (lremove xF tF)))) ff
              in impI_at (lmem hF (lremove xF tF), oFalseC) dis end;
            val cj2 = conjI_at (neg (lmem hF (lremove xF tF)), lnodup (lremove xF tF)) nmem_rt ndrt;
            val nd_target = Thm.implies_elim (lnodupConsBwd_at (hF, lremove xF tF)) cj2;
            val lrm_s = leq_sym OF [lrm];
            val res = lnodup_transfer (lcons hF (lremove xF tF), lremove xF (lcons hF tF)) lrm_s nd_target;
          in Thm.implies_intr (ctermLL (jT (neg (oeq xF hF)))) res end;
        val em = ex_middle_at (oeq xF hF);
        val conc = disjE_elim (oeq xF hF, neg (oeq xF hF), lnodup (lremove xF (lcons hF tF))) em caseEq caseNeq;
        val dis = Thm.implies_intr (ctermLL (jT (lnodup (lcons hF tF)))) conc;
      in impI_at (lnodup (lcons hF tF), lnodup (lremove xF (lcons hF tF))) dis end;
    val step1 = Thm.forall_intr (ctermLL hF)
                  (Thm.forall_intr (ctermLL tF) (Thm.implies_intr (ctermLL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hndL = Thm.assume (ctermLL (jT (lnodup LF)));
    val concL = mp_at (lnodup LF, lnodup (lremove xF LF)) r2 hndL;
    val d1 = Thm.implies_intr (ctermLL (jT (lnodup LF))) concL;
  in varify d1 end;

val i_nodup_remove = Logic.mk_implies (jT (lnodup LVm), jT (lnodup (lremove xVm LVm)));
val r_nodup_remove = chk0 ("nodup_remove", nodup_remove, i_nodup_remove);
val () = out "LIST_LIB_NODUP_REMOVE_DONE\n";

(* ============================================================================
   PROBES / sanity computations.
   ============================================================================ *)
val probe_lprod2 =
  let
    val aP = Free("a", natT); val bP = Free("b", natT);
    val twolist = lcons aP (lcons bP lnilC);
    val c1 = lprodCons_at (aP, lcons bP lnilC);
    val c2 = lprodCons_at (bP, lnilC);
    val cn = lprodNil_at ();
    val c2' = oeq_trans OF [c2, mult_cong_r (bP, lprod lnilC, suc ZeroC) cn];
    val full = oeq_trans OF [c1, mult_cong_r (aP, lprod (lcons bP lnilC), mult bP (suc ZeroC)) c2'];
    val intended = jT (oeq (lprod twolist) (mult aP (mult bP (suc ZeroC))));
  in (length (Thm.hyps_of full) = 0) andalso ((Thm.prop_of full) aconv intended) end;
val () = if probe_lprod2 then out "PROBE_OK lprod [a,b] = a*(b*1)\n"
         else out "PROBE_FAIL lprod2\n";

val probe_extract_cond =
  let val bogus = jT (oeq (lprod LVe) (mult xVe (lprod (lremove xVe LVe))))
  in not ((Thm.prop_of extract) aconv bogus) end;
val probe_extract_nontrivial =
  let val bogus = Logic.mk_implies (jT (lmem xVe LVe), jT (oeq (lprod LVe) (lprod LVe)))
  in not ((Thm.prop_of extract) aconv bogus) end;
val () = if probe_extract_cond andalso probe_extract_nontrivial
         then out "PROBE_OK extract conditional + nontrivial\n"
         else out "PROBE_FAIL extract collapsed\n";

val probe_mrb_cond =
  let val bogus = Logic.mk_implies (jT (lmem yVm LVm), jT (lmem yVm (lremove xVm LVm)))
  in not ((Thm.prop_of mem_remove_bwd) aconv bogus) end;
val () = if probe_mrb_cond then out "PROBE_OK mem_remove_bwd conditional on y<>x\n"
         else out "PROBE_FAIL mem_remove_bwd\n";

(* ============================================================================
   FINAL VERDICT
   ============================================================================ *)
val () =
  if r_lprod_nil andalso r_lprod_cons andalso r_llen_nil andalso r_llen_cons
     andalso r_extract andalso r_mem_remove_fwd andalso r_mem_remove_bwd
     andalso r_llen_remove andalso r_nodup_remove
     andalso probe_lprod2 andalso probe_extract_cond andalso probe_extract_nontrivial
     andalso probe_mrb_cond
  then out "LIST_LIB_OK\n"
  else out "LIST_LIB_FAILED\n";

(* ============================================================================
   PHASE 2 (seat pr0) — THE INVOLUTION-PAIRING LEMMA toward Wilson's theorem.
   On ctxtLL (the Phase-1 list-library context), prove pairing_lemma by list
   strong induction on llen L (derived from meta_nat_induct).
   ============================================================================ *)
val () = out "PAIRING_BEGIN\n";

(* ---- re-varify base nat-order + cong lemmas onto ctxtLL ---- *)
val meta_nat_induct_vLL = varify meta_nat_induct_ax2;
val lt_suc_vLL        = varify lt_suc;
val lt_suc_cases_vLL  = varify lt_suc_cases;
val Suc_neq_Zero_vLL  = varify Suc_neq_Zero_ax;
val cong_refl_vLL     = varify cong_refl;
val cong_mult_vLL     = varify cong_mult;
val cong_trans_vLL    = varify cong_trans;
val cong_sym_vLL      = varify cong_sym;
val mult_1_left_vLL   = varify mult_1_left;
val oeq_subst_vLL     = oeq_subst_vL;   (* alias *)

(* ---- ground instantiators on ctxtLL ---- *)
fun lt_suc_at nt = beta_norm (Drule.infer_instantiate ctxtLL [(("n",0), ctermLL nt)] lt_suc_vLL);
fun lt_suc_cases_at (mt,nt) hlt =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("m",0), ctermLL mt),(("n",0), ctermLL nt)] lt_suc_cases_vLL)
  in Thm.implies_elim inst hlt end;
fun Suc_neq_Zero_at nt heq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL [(("n",0), ctermLL nt)] Suc_neq_Zero_vLL)
  in Thm.implies_elim inst heq end;
fun mult1l_at t = beta_norm (Drule.infer_instantiate ctxtLL [(("n",0), ctermLL t)] mult_1_left_vLL);

(* cong instantiators on ctxtLL *)
fun cong_refl_at (mt, at) = beta_norm (Drule.infer_instantiate ctxtLL
      [(("m",0), ctermLL mt), (("a",0), ctermLL at)] cong_refl_vLL);
fun cong_mult_at (mt, at, a2t, bt, b2t) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("m",0), ctermLL mt), (("a",0), ctermLL at), (("a2",0), ctermLL a2t),
         (("b",0), ctermLL bt), (("b2",0), ctermLL b2t)] cong_mult_vLL)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun cong_trans_at (mt, at, bt, ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("m",0), ctermLL mt), (("a",0), ctermLL at), (("b",0), ctermLL bt),
         (("c",0), ctermLL ct)] cong_trans_vLL)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun cong_sym_at (mt, at, bt) h =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("m",0), ctermLL mt), (("a",0), ctermLL at), (("b",0), ctermLL bt)] cong_sym_vLL)
  in Thm.implies_elim inst h end;

(* cong_cong on ctxtLL : oeq a a2 -> oeq b b2 -> cong m a b -> cong m a2 b2. *)
fun cong_cong_at (mF, aF, a2F, bF, b2F) (haa2 : thm) (hbb2 : thm) (hcong : thm) =
  let
    val zF1 = Free("zz1", natT);
    val Pabs1 = Term.lambda zF1 (cong mF zF1 bF);
    val inst1 = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Pabs1), (("a",0), ctermLL aF), (("b",0), ctermLL a2F)] oeq_subst_vLL);
    val cong1 = inst1 OF [haa2, hcong];
    val zF2 = Free("zz2", natT);
    val Pabs2 = Term.lambda zF2 (cong mF a2F zF2);
    val inst2 = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Pabs2), (("a",0), ctermLL bF), (("b",0), ctermLL b2F)] oeq_subst_vLL);
    val cong2 = inst2 OF [hbb2, cong1];
  in cong2 end;

(* exE_elim on ctxtLL *)
fun exE_elim (Pabs, goalC) exThm wName bodyFn =
  let
    val wF = Free(wName, natT);
    val hypTerm = jT (Term.betapply (Pabs, wF));
    val hypThm  = Thm.assume (ctermLL hypTerm);
    val body    = bodyFn wF hypThm;
    val minor   = Thm.forall_intr (ctermLL wF) (Thm.implies_intr (ctermLL hypTerm) body);
    val exE_inst= beta_norm (Drule.infer_instantiate ctxtLL
                    [(("P",0), ctermLL Pabs), (("Q",0), ctermLL goalC)] exE_vL);
    val partial = Thm.implies_elim exE_inst exThm;
  in Thm.implies_elim partial minor end;

(* oeq_subst as a one-shot on ctxtLL : oeq a b -> Tp(P a) -> Tp(P b) *)
fun oeq_rewrite (Pabs, aT, bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("P",0), ctermLL Pabs), (("a",0), ctermLL aT), (("b",0), ctermLL bT)] oeq_subst_vLL)
  in inst OF [hab, hPa] end;

val () = out "PAIRING_HELPERS_READY\n";

(* ============================================================================
   lt_zero_elim : jT (lt m Zero) ==> jT (anyGoal)
   ============================================================================ *)
fun lt_zero_elim mT goalC hlt =
  let
    val Pabs = Abs("p", natT, oeq ZeroC (add (suc mT) (Bound 0)));
    fun body w (hw : thm) =                  (* hw : oeq Zero (add (Suc m) w) *)
      let
        val aS    = addSuc_at (mT, w);        (* (Suc m + w) = Suc(m + w) *)
        val z_S   = oeq_trans OF [hw, aS];    (* 0 = Suc(m + w) *)
        val S_z   = oeq_sym OF [z_S];         (* Suc(m+w) = 0 *)
        val fls   = Suc_neq_Zero_at (add mT w) S_z;   (* oFalse *)
      in Thm.implies_elim (oFalse_elim_at goalC) fls end;
  in exE_elim (Pabs, goalC) hlt "w_lz" body end;

val () = out "PAIRING_LT_ZERO_READY\n";

(* ============================================================================
   LIST STRONG INDUCTION (meta), parameterised by an ML body PhiBody : term -> term.
     list_strong_induct PhiBody stepFn  : returns  (LF, Tp(Phi LF))  with LF a Free
       stepFn : (LF : term) -> (applyIH : term -> thm -> thm) -> thm(Tp(Phi LF))
         applyIH L2 (h_lt : Tp(lt (llen L2) (llen LF))) : thm(Tp(Phi L2))
   Meta AUX : !!n. !!L. lt (llen L) n ==> Tp(Phi L)  by meta_nat_induct on n.
   ============================================================================ *)
fun list_strong_induct PhiBody stepFn =
  let
    (* meta predicate  Phi_meta n := !!L. lt (llen L) n ==> Tp(PhiBody L) *)
    val nMeta = Free("n_lsi", natT);
    val LMeta = Free("L_lsi", natlistT);
    fun auxBody nt =
      Logic.all LMeta (Logic.mk_implies (jT (lt (llen LMeta) nt), jT (PhiBody LMeta)));
    val PhiMetaAbs = Term.lambda nMeta (auxBody nMeta);

    (* BASE : !!L. lt (llen L) Zero ==> Tp(PhiBody L) *)
    val base =
      let
        val LB = Free("L_b", natlistT);
        val hlt = Thm.assume (ctermLL (jT (lt (llen LB) ZeroC)));
        val res = lt_zero_elim (llen LB) (PhiBody LB) hlt;
        val disch = Thm.implies_intr (ctermLL (jT (lt (llen LB) ZeroC))) res;
      in Thm.forall_intr (ctermLL LB) disch end;

    (* STEP : !!x. (AUX x) ==> (AUX (Suc x)) *)
    val step =
      let
        val xS = Free("x_lsi", natT);
        val auxX = auxBody xS;               (* !!L. lt (llen L) x ==> Tp(Phi L) *)
        val IHmeta = Thm.assume (ctermLL auxX);
        (* applyAUXx L2 (h : lt (llen L2) x) : Tp(Phi L2) *)
        fun applyAUXx L2 hlt =
          let val a1 = Thm.forall_elim (ctermLL L2) IHmeta
          in Thm.implies_elim a1 hlt end;
        (* prove !!L. lt (llen L)(Suc x) ==> Tp(Phi L) *)
        val LS = Free("L_s", natlistT);
        val hltS = Thm.assume (ctermLL (jT (lt (llen LS) (suc xS))));
        val dThm = lt_suc_cases_at (llen LS, xS) hltS;   (* Disj (lt (llen L) x)(oeq (llen L) x) *)
        val goalC = PhiBody LS;
        val caseA =
          let
            val hA = Thm.assume (ctermLL (jT (lt (llen LS) xS)));
            val r  = applyAUXx LS hA;
          in Thm.implies_intr (ctermLL (jT (lt (llen LS) xS))) r end;
        val caseB =
          let
            val hB = Thm.assume (ctermLL (jT (oeq (llen LS) xS)));  (* oeq (llen LS) x *)
            (* build IH for LS : applyIH L2 (h : lt (llen L2)(llen LS)) : Tp(Phi L2)
               from applyAUXx, rewriting lt (llen L2)(llen LS) to lt (llen L2) x via hB *)
            fun applyIH L2 (h_lt : thm) =     (* h_lt : Tp(lt (llen L2)(llen LS)) *)
              let
                val zpr = Free("z_pr", natT);
                val Pr = Term.lambda zpr (lt (llen L2) zpr);
                val h_lt_x = oeq_rewrite (Pr, llen LS, xS) hB h_lt;  (* lt (llen L2) x *)
              in applyAUXx L2 h_lt_x end;
            val r = stepFn LS applyIH;
          in Thm.implies_intr (ctermLL (jT (oeq (llen LS) xS))) r end;
        val disjE_inst = beta_norm (Drule.infer_instantiate ctxtLL
              [(("A",0), ctermLL (lt (llen LS) xS)), (("B",0), ctermLL (oeq (llen LS) xS)),
               (("C",0), ctermLL goalC)] disjE_vL);
        val d1 = Thm.implies_elim disjE_inst dThm;
        val d2 = Thm.implies_elim d1 caseA;
        val pm = Thm.implies_elim d2 caseB;     (* Tp(Phi LS) *)
        val dischLt = Thm.implies_intr (ctermLL (jT (lt (llen LS) (suc xS)))) pm;
        val auxSucx = Thm.forall_intr (ctermLL LS) dischLt;
        val stepInner = Thm.implies_intr (ctermLL auxX) auxSucx;
      in Thm.forall_intr (ctermLL xS) stepInner end;

    (* the final list LF; instantiate AUX at K := Suc (llen LF), then apply at LF *)
    val LF = Free("L_fin", natlistT);
    val kFin = suc (llen LF);
    val indK = beta_norm (Drule.infer_instantiate ctxtLL
                 [(("Phi",0), ctermLL PhiMetaAbs), (("k",0), ctermLL kFin)] meta_nat_induct_vLL);
    val r1 = Thm.implies_elim indK base;
    val auxK = Thm.implies_elim r1 step;        (* !!L. lt (llen L)(Suc(llen LF)) ==> Tp(Phi L) *)
    val auxKL = Thm.forall_elim (ctermLL LF) auxK;   (* lt (llen LF)(Suc(llen LF)) ==> Tp(Phi LF) *)
    val selfLt = lt_suc_at (llen LF);                (* lt (llen LF)(Suc(llen LF)) *)
    val resLF = Thm.implies_elim auxKL selfLt;       (* Tp(Phi LF) *)
  in (LF, resLF) end;

val () = out "PAIRING_LSI_READY\n";

(* ---- SMOKE TEST of list_strong_induct: prove !!L. oeq (lprod L)(lprod L) ----
   (trivial; just exercises the principle's plumbing end-to-end) ---- *)
val lsi_smoke =
  let
    fun PhiBody L = oeq (lprod L) (lprod L);
    fun stepFn LF applyIH =
      beta_norm (Drule.infer_instantiate ctxtLL [(("a",0), ctermLL (lprod LF))] oeq_refl_vL);
    val (LF, res) = list_strong_induct PhiBody stepFn;
  in varify (Thm.forall_intr (ctermLL LF) res) end;
val r_lsi_smoke = (length (Thm.hyps_of lsi_smoke) = 0);
val () = if r_lsi_smoke then out "OK lsi_smoke (list strong induction plumbing)\n"
         else out "FAIL lsi_smoke\n";

val () = out "PAIRING_SMOKE_DONE\n";

(* ============================================================================
   Object Forall helpers on ctxtLL + inv congruence + injectivity.
   ============================================================================ *)
val allI_vLL = varify allI_ax;
val allE_vLL = varify allE_ax;
fun allI_at Pabs hAllThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL [(("P",0), ctermLL Pabs)] allI_vLL)
  in Thm.implies_elim inst hAllThm end;
fun allE_at Pabs at hForall =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("P",0), ctermLL Pabs), (("a",0), ctermLL at)] allE_vLL)
  in Thm.implies_elim inst hForall end;

(* inv : nat => nat  (a Free function variable) ; p : nat (the modulus) *)
val invF = Free("inv", natT --> natT);
fun inv t = invF $ t;
val pF = Free("p", natT);
val oneN = suc ZeroC;

(* inv_cong : oeq a b ==> oeq (inv a)(inv b)   (via oeq_subst, %z. oeq (inv a)(inv z)) *)
fun inv_cong (aT, bT) hab =
  let val Pabs = Abs("z", natT, oeq (inv aT) (inv (Bound 0)));
      val refl0 = beta_norm (Drule.infer_instantiate ctxtLL [(("a",0), ctermLL (inv aT))] oeq_refl_vL);
  in oeq_rewrite (Pabs, aT, bT) hab refl0 end;

val () = out "PAIRING_FORALL_HELPERS_READY\n";

(* ---- TEST inv_cong : prove oeq a b ==> oeq (inv a)(inv b) as a closed thm ---- *)
val r_inv_cong =
  let
    val aF = Free("a_t", natT); val bF = Free("b_t", natT);
    val hab = Thm.assume (ctermLL (jT (oeq aF bF)));
    val res = inv_cong (aF, bF) hab;
    val th  = Thm.implies_intr (ctermLL (jT (oeq aF bF))) res;
    val intended = Logic.mk_implies (jT (oeq aF bF), jT (oeq (inv aF) (inv bF)));
  in (length (Thm.hyps_of th) = 0) andalso ((Thm.prop_of th) aconv intended) end;
val () = if r_inv_cong then out "OK inv_cong\n" else out "FAIL inv_cong\n";

(* ============================================================================
   inv_inj_on : given H5 as an ML function  h5 : x -> Tp(lmem x L) -> Tp(oeq (inv(inv x)) x),
   if  lmem x L, lmem y L, oeq (inv x)(inv y)  then  oeq x y.
     x = inv(inv x)        [h5 x sym]
       = inv(inv y)        [inv_cong of oeq(inv x)(inv y)]
       = y                 [h5 y]
   ============================================================================ *)
fun inv_inj_on h5 (xT, yT) hMemX hMemY hInvEq =
  let
    val hx = h5 xT hMemX;                       (* oeq (inv(inv x)) x *)
    val hy = h5 yT hMemY;                       (* oeq (inv(inv y)) y *)
    val hx_s = oeq_sym OF [hx];                 (* oeq x (inv(inv x)) *)
    val hii = inv_cong (inv xT, inv yT) hInvEq; (* oeq (inv(inv x))(inv(inv y)) *)
    val c1 = oeq_trans OF [hx_s, hii];          (* oeq x (inv(inv y)) *)
    val c2 = oeq_trans OF [c1, hy];             (* oeq x y *)
  in c2 end;

(* ---- TEST inv_inj_on with a generic L and an assumed H5 ---- *)
val r_inv_inj =
  let
    val LF = Free("L_t", natlistT);
    val xF = Free("x_t", natT); val yF = Free("y_t", natT);
    (* h5 as: assume Tp(oeq (inv(inv z)) z) for any z directly (stand-in) *)
    fun h5 z hMem = Thm.assume (ctermLL (jT (oeq (inv (inv z)) z)));
    val hMemX = Thm.assume (ctermLL (jT (lmem xF LF)));
    val hMemY = Thm.assume (ctermLL (jT (lmem yF LF)));
    val hInvEq= Thm.assume (ctermLL (jT (oeq (inv xF)(inv yF))));
    val res = inv_inj_on h5 (xF, yF) hMemX hMemY hInvEq;
  in (Thm.prop_of res) aconv (jT (oeq xF yF)) end;
val () = if r_inv_inj then out "OK inv_inj_on\n" else out "FAIL inv_inj_on\n";

val () = out "PAIRING_INJ_DONE\n";

(* ============================================================================
   mem_remove_neq : lnodup L ==> lmem y (lremove x L) ==> neg (oeq y x)
     BY list_induct on L (on ctxtLL).
   ============================================================================ *)
val mem_remove_neq =
  let
    val xF = Free("x", natT); val yF = Free("y", natT);
    fun concBody zt = mkImp (lnodup zt) (mkImp (lmem yF (lremove xF zt)) (neg (oeq yF xF)));
    val Qpred = Abs("z", natlistT, concBody (Bound 0));
    val LF = Free("L", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtLL
          [(("P",0), ctermLL Qpred), (("a",0), ctermLL LF)] list_induct_vL);
    val base =
      let
        val hmem0 = Thm.assume (ctermLL (jT (lmem yF (lremove xF lnilC))));
        val lrm = lremoveNil_at xF;
        val mem_lnil = lmem_transfer (yF, lremove xF lnilC, lnilC) lrm hmem0;
        val ff  = Thm.implies_elim (lmemNilElim_at yF) mem_lnil;
        val conc = Thm.implies_elim (oFalse_elim_at (neg (oeq yF xF))) ff;
        val d2 = Thm.implies_intr (ctermLL (jT (lmem yF (lremove xF lnilC)))) conc;
        val d1 = impI_at (lmem yF (lremove xF lnilC), neg (oeq yF xF)) d2;
        val d0 = Thm.implies_intr (ctermLL (jT (lnodup lnilC))) d1;
      in impI_at (lnodup lnilC, mkImp (lmem yF (lremove xF lnilC)) (neg (oeq yF xF))) d0 end;
    val hF = Free("h", natT); val tF = Free("t", natlistT);
    val ihprop = jT (concBody tF);
    val IH = Thm.assume (ctermLL ihprop);
    (* helper: build an object  neg(oeq y x)  from a meta  Tp(oeq y x) ==> Tp oFalse  *)
    fun mkNegYX metaImpl = impI_at (oeq yF xF, oFalseC) metaImpl;
    val stepConcl =
      let
        val hnd = Thm.assume (ctermLL (jT (lnodup (lcons hF tF))));
        val cj  = Thm.implies_elim (lnodupConsFwd_at (hF, tF)) hnd;
        val nmemH = conjunct1_at (neg (lmem hF tF), lnodup tF) cj;   (* neg (lmem h t) *)
        val ndt   = conjunct2_at (neg (lmem hF tF), lnodup tF) cj;   (* lnodup t *)
        val hmem = Thm.assume (ctermLL (jT (lmem yF (lremove xF (lcons hF tF)))));
        val caseEq =
          let
            val heq = Thm.assume (ctermLL (jT (oeq xF hF)));         (* x = h *)
            val lrm = Thm.implies_elim (lremoveConsEq_at (xF, hF, tF)) heq;  (* leq (lremove x (lcons h t)) t *)
            val mem_t = lmem_transfer (yF, lremove xF (lcons hF tF), tF) lrm hmem;  (* lmem y t *)
            val negYX =
              let val hyx = Thm.assume (ctermLL (jT (oeq yF xF)))     (* y = x *)
                  val yh  = oeq_trans OF [hyx, heq]                   (* y = h *)
                  val Pr  = Abs("z", natT, lmem (Bound 0) tF)
                  val memH= oeq_rewrite (Pr, yF, hF) yh mem_t          (* lmem h t *)
                  val ff  = mp_at (lmem hF tF, oFalseC) nmemH memH
              in mkNegYX (Thm.implies_intr (ctermLL (jT (oeq yF xF))) ff) end;
          in Thm.implies_intr (ctermLL (jT (oeq xF hF))) negYX end;
        val caseNeq =
          let
            val hneq = Thm.assume (ctermLL (jT (neg (oeq xF hF))));   (* x != h *)
            val lrm = Thm.implies_elim (lremoveConsNeq_at (xF, hF, tF)) hneq;  (* leq (lremove x (lcons h t)) (lcons h (lremove x t)) *)
            val mem_cons = lmem_transfer (yF, lremove xF (lcons hF tF), lcons hF (lremove xF tF)) lrm hmem; (* lmem y (lcons h (lremove x t)) *)
            val dj = Thm.implies_elim (lmemConsFwd_at (yF, hF, lremove xF tF)) mem_cons;  (* Disj (oeq y h)(lmem y (lremove x t)) *)
            val cA = let val hyh = Thm.assume (ctermLL (jT (oeq yF hF)))   (* y = h *)
                         val negYX =
                           let val hyx = Thm.assume (ctermLL (jT (oeq yF xF)))   (* y = x *)
                               val hy_s= oeq_sym OF [hyh]                         (* h = y *)
                               val hx  = oeq_trans OF [hy_s, hyx]                 (* h = x *)
                               val hxh = oeq_sym OF [hx]                          (* x = h *)
                               val ff  = mp_at (oeq xF hF, oFalseC) hneq hxh
                           in mkNegYX (Thm.implies_intr (ctermLL (jT (oeq yF xF))) ff) end;
                     in Thm.implies_intr (ctermLL (jT (oeq yF hF))) negYX end;
            val cB = let val hmt = Thm.assume (ctermLL (jT (lmem yF (lremove xF tF))))
                         val ihA = mp_at (lnodup tF, mkImp (lmem yF (lremove xF tF)) (neg (oeq yF xF))) IH ndt
                         val res = mp_at (lmem yF (lremove xF tF), neg (oeq yF xF)) ihA hmt
                     in Thm.implies_intr (ctermLL (jT (lmem yF (lremove xF tF)))) res end;
            val res = disjE_elim (oeq yF hF, lmem yF (lremove xF tF), neg (oeq yF xF)) dj cA cB;
          in Thm.implies_intr (ctermLL (jT (neg (oeq xF hF)))) res end;
        val em = ex_middle_at (oeq xF hF);
        val negThm = disjE_elim (oeq xF hF, neg (oeq xF hF), neg (oeq yF xF)) em caseEq caseNeq;
        val d2 = Thm.implies_intr (ctermLL (jT (lmem yF (lremove xF (lcons hF tF))))) negThm;
        val d1 = impI_at (lmem yF (lremove xF (lcons hF tF)), neg (oeq yF xF)) d2;
        val d0 = Thm.implies_intr (ctermLL (jT (lnodup (lcons hF tF)))) d1;
      in impI_at (lnodup (lcons hF tF), mkImp (lmem yF (lremove xF (lcons hF tF))) (neg (oeq yF xF))) d0 end;
    val step1 = Thm.forall_intr (ctermLL hF)
                  (Thm.forall_intr (ctermLL tF) (Thm.implies_intr (ctermLL ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;
    val hndL = Thm.assume (ctermLL (jT (lnodup LF)));
    val hmemL = Thm.assume (ctermLL (jT (lmem yF (lremove xF LF))));
    val resA = mp_at (lnodup LF, mkImp (lmem yF (lremove xF LF)) (neg (oeq yF xF))) r2 hndL;
    val resB = mp_at (lmem yF (lremove xF LF), neg (oeq yF xF)) resA hmemL;
    val d2 = Thm.implies_intr (ctermLL (jT (lmem yF (lremove xF LF)))) resB;
    val d1 = Thm.implies_intr (ctermLL (jT (lnodup LF))) d2;
  in varify d1 end;

val mem_remove_neq_v = varify mem_remove_neq;
fun mem_remove_neq_at (yt, xt, Lt) hnd hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtLL
        [(("y",0), ctermLL yt), (("x",0), ctermLL xt), (("L",0), ctermLL Lt)] mem_remove_neq_v)
  in mp_at (lmem yt (lremove xt Lt), neg (oeq yt xt)) (mp_at (lnodup Lt, mkImp (lmem yt (lremove xt Lt)) (neg (oeq yt xt))) inst hnd) hmem end;

val r_mem_remove_neq =
  let
    val yV = Var(("y",0),natT); val xV = Var(("x",0),natT); val LV = Var(("L",0),natlistT);
    val intended = Logic.mk_implies (jT (lnodup LV),
        Logic.mk_implies (jT (lmem yV (lremove xV LV)), jT (neg (oeq yV xV))));
  in (length (Thm.hyps_of mem_remove_neq) = 0) andalso ((Thm.prop_of mem_remove_neq) aconv intended) end;
val () = if r_mem_remove_neq then out "OK mem_remove_neq\n" else out "FAIL mem_remove_neq\n";

val () = out "PAIRING_MRN_DONE\n";

(* ============================================================================
   META LIST-CASES.  Add lhd/ltl consts (one new final context ctxtL2), then
   prove by list_induct the object  Disj (leq L lnil) (leq L (lcons (lhd L)(ltl L))).
   ============================================================================ *)
val thyL2c = Sign.add_consts
  [(Binding.name "lhd", natlistT --> natT, NoSyn),
   (Binding.name "ltl", natlistT --> natlistT, NoSyn)] thyLL;
fun cnstL2 nm T = Const (Sign.full_name thyL2c (Binding.name nm), T);
val lhdC = cnstL2 "lhd" (natlistT --> natT);  fun lhd l = lhdC $ l;
val ltlC = cnstL2 "ltl" (natlistT --> natlistT); fun ltl l = ltlC $ l;
val xL2 = Free("x", natT); val tL2 = Free("t", natlistT);
val ((_,lhd_cons_ax), tL2a) = Thm.add_axiom_global (Binding.name "lhd_cons",
      jT (oeq (lhd (lcons xL2 tL2)) xL2)) thyL2c;
val ((_,ltl_cons_ax), thyL2) = Thm.add_axiom_global (Binding.name "ltl_cons",
      jT (leq (ltl (lcons xL2 tL2)) tL2)) tL2a;

val ctxtL2  = Proof_Context.init_global thyL2;
val ctermL2 = Thm.cterm_of ctxtL2;

val list_induct_vL2 = varify list_induct_ax;
val leq_refl_vL2    = varify leq_refl_ax;
val disjI1_vL2 = varify disjI1_ax;
val disjI2_vL2 = varify disjI2_ax;
val disjE_vL2  = varify disjE_ax;
fun lhdCons_at (h,t) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 h),(("t",0), ctermL2 t)] (varify lhd_cons_ax));
fun ltlCons_at (h,t) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 h),(("t",0), ctermL2 t)] (varify ltl_cons_ax));
fun leqRefl_at l = beta_norm (Drule.infer_instantiate ctxtL2 [(("a",0), ctermL2 l)] leq_refl_vL2);
fun disjI1_L2 (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] disjI1_vL2)) h;
fun disjI2_L2 (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] disjI2_vL2)) h;
fun disjE_L2 (At,Bt,Ct) dThm caseA caseB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt),(("C",0), ctermL2 Ct)] disjE_vL2)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB end;
(* leq_subst rewrite on ctxtL2 (for list-eq) *)
val leq_subst_vL2 = varify leq_subst_ax;
fun leq_rewrite (Pabs, aT, bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("P",0), ctermL2 Pabs), (("a",0), ctermL2 aT), (("b",0), ctermL2 bT)] leq_subst_vL2)
  in inst OF [hab, hPa] end;
(* oeq_subst rewrite on ctxtL2 (terms may mention lhd/ltl) *)
val oeq_subst_vL2 = varify oeq_subst;
fun oeq_rewrite_L2 (Pabs, aT, bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("P",0), ctermL2 Pabs), (("a",0), ctermL2 aT), (("b",0), ctermL2 bT)] oeq_subst_vL2)
  in inst OF [hab, hPa] end;

(* cases predicate :  %L. Disj (leq L lnil) (leq L (lcons (lhd L)(ltl L))) *)
fun casesBody L = mkDisj (leq L lnilC) (leq L (lcons (lhd L) (ltl L)));

val list_cases_thm =   (* !!L. Tp(casesBody L) *)
  let
    val Qpred = Abs("z", natlistT, casesBody (Bound 0));
    val LF = Free("L_c", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtL2
          [(("P",0), ctermL2 Qpred), (("a",0), ctermL2 LF)] list_induct_vL2);
    val base =
      let
        val nilRefl = leqRefl_at lnilC;        (* leq lnil lnil *)
      in disjI1_L2 (leq lnilC lnilC, leq lnilC (lcons (lhd lnilC)(ltl lnilC))) nilRefl end;
    val hF = Free("h_c", natT); val tF = Free("t_c", natlistT);
    val ihprop = jT (casesBody tF);
    val stepConcl =
      let
        val consL = lcons hF tF;
        val refl0 = leqRefl_at consL;                          (* leq (lcons h t)(lcons h t) *)
        val hLhd = lhdCons_at (hF, tF);                        (* oeq (lhd (lcons h t)) h *)
        val hLhd_s = oeq_sym OF [hLhd];                        (* oeq h (lhd (lcons h t)) *)
        val hLtl = ltlCons_at (hF, tF);                        (* leq (ltl (lcons h t)) t *)
        val hLtl_s = leq_sym OF [hLtl];                        (* leq t (ltl (lcons h t)) *)
        val P1 = Abs("z", natT, leq consL (lcons (Bound 0) tF));
        val r1 = oeq_rewrite_L2 (P1, hF, lhd consL) hLhd_s refl0;  (* leq (lcons h t)(lcons (lhd ..) t) *)
        val P2 = Abs("z", natlistT, leq consL (lcons (lhd consL) (Bound 0)));
        val r2 = leq_rewrite (P2, tF, ltl consL) hLtl_s r1;    (* leq (lcons h t)(lcons (lhd ..)(ltl ..)) *)
      in disjI2_L2 (leq consL lnilC, leq consL (lcons (lhd consL)(ltl consL))) r2 end;
    val step1 = Thm.forall_intr (ctermL2 hF)
                  (Thm.forall_intr (ctermL2 tF) (Thm.implies_intr (ctermL2 ihprop) stepConcl));
    val r1 = Thm.implies_elim ind base;
    val r2 = Thm.implies_elim r1 step1;            (* Tp(casesBody LF) *)
  in (LF, r2) end;

val () = out "PAIRING_CASES_THM_READY\n";

(* meta cases : given L, produce R from caseNil(Tp(leq L lnil)) and
   caseCons(a, rest, Tp(leq L (lcons a rest))).  a := lhd L, rest := ltl L. *)
fun list_cases (LT, goalC) caseNilFn caseConsFn =
  let
    val (LFc, casesL) = list_cases_thm;
    val casesAtL = beta_norm (Drule.infer_instantiate ctxtL2
          [(("L_c",0), ctermL2 LT)] (varify (Thm.forall_intr (ctermL2 LFc) casesL)));
    val nilP  = leq LT lnilC;
    val consP = leq LT (lcons (lhd LT)(ltl LT));
    val cA = let val h = Thm.assume (ctermL2 (jT nilP))
             in Thm.implies_intr (ctermL2 (jT nilP)) (caseNilFn h) end;
    val cB = let val h = Thm.assume (ctermL2 (jT consP))
             in Thm.implies_intr (ctermL2 (jT consP)) (caseConsFn (lhd LT, ltl LT) h) end;
  in disjE_L2 (nilP, consP, goalC) casesAtL cA cB end;

(* ---- TEST list_cases : prove !!L. Tp(Disj (leq L lnil)(leq L (lcons (lhd L)(ltl L)))) trivially ---- *)
val r_list_cases =
  let
    val (LFc, casesL) = list_cases_thm;
    val th = varify (Thm.forall_intr (ctermL2 LFc) casesL);
  in (length (Thm.hyps_of th) = 0) end;
val () = if r_list_cases then out "OK list_cases_thm\n" else out "FAIL list_cases_thm\n";

val () = out "PAIRING_CASES_DONE\n";

(* ============================================================================
   ctxtL2 helper layer : ALL operations used inside caseCons must build cterms
   over thyL2 (since head = lhd LS / rest = ltl LS mention lhd/ltl).  We
   re-instantiate the SAME varified (theory-agnostic) lemmas via ctxtL2/ctermL2.
   Suffix _2 throughout.
   ============================================================================ *)
val oeq_refl_v2  = varify oeq_refl;
val oeq_subst_v2 = varify oeq_subst;
val mp_v2        = varify mp_ax;
val impI_v2      = varify impI_ax;
val conjI_v2     = varify conjI_ax;
val conjunct1_v2 = varify conjunct1_ax;
val conjunct2_v2 = varify conjunct2_ax;
val oFalse_elim_v2 = varify oFalse_elim_ax;
val allI_v2      = varify allI_ax;
val allE_v2      = varify allE_ax;
val leq_subst_v2 = varify leq_subst_ax;
val lprod_cons_v2= varify lprod_cons_ax;
val llen_cons_v2 = varify llen_cons_ax;
val lmem_cons_fwd_v2 = varify lmem_cons_fwd_ax;
val lmem_cons_bwd_v2 = varify lmem_cons_bwd_ax;
val lnodup_cons_fwd_v2 = varify lnodup_cons_fwd_ax;
val mult_comm_v2 = varify mult_comm;
val mult_assoc_v2= varify mult_assoc;
val mult_1_left_v2 = varify mult_1_left;
val cong_refl_v2 = varify cong_refl;
val cong_mult_v2 = varify cong_mult;
val cong_trans_v2= varify cong_trans;
val lt_suc_v2    = varify lt_suc;

fun oeqRefl_2 t = beta_norm (Drule.infer_instantiate ctxtL2 [(("a",0), ctermL2 t)] oeq_refl_v2);
fun oeq_rw_2 (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 aT),(("b",0), ctermL2 bT)] oeq_subst_v2)
  in inst OF [hab, hPa] end;
fun mp_2 (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] mp_v2)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_2 (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] impI_v2)
  in Thm.implies_elim inst hImpThm end;
fun conjI_2 (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] conjI_v2)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_2 (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] conjunct1_v2)) h;
fun conjunct2_2 (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] conjunct2_v2)) h;
fun oFalse_elim_2 rT = beta_norm (Drule.infer_instantiate ctxtL2 [(("R",0), ctermL2 rT)] oFalse_elim_v2);
fun disjE_2 (At,Bt,Ct) dThm cA cB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt),(("C",0), ctermL2 Ct)] disjE_vL2)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) cA) cB end;
fun disjI1_2 (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] disjI1_vL2)) h;
fun disjI2_2 (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("A",0), ctermL2 At),(("B",0), ctermL2 Bt)] disjI2_vL2)) h;
fun allI_2 Pabs hAll = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("P",0), ctermL2 Pabs)] allI_v2)) hAll;
fun allE_2 Pabs at hF = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 at)] allE_v2)) hF;
fun leq_rw_2 (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 aT),(("b",0), ctermL2 bT)] leq_subst_v2)
  in inst OF [hab, hPa] end;
fun lprodCons_2 (h,t) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 h),(("t",0), ctermL2 t)] lprod_cons_v2);
fun llenCons_2 (h,t) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 h),(("t",0), ctermL2 t)] llen_cons_v2);
fun lmemConsFwd_2 (x,y,t) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 x),(("y",0), ctermL2 y),(("t",0), ctermL2 t)] lmem_cons_fwd_v2);
fun lmemConsBwd_2 (x,y,t) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 x),(("y",0), ctermL2 y),(("t",0), ctermL2 t)] lmem_cons_bwd_v2);
fun lnodupConsFwd_2 (x,t) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 x),(("t",0), ctermL2 t)] lnodup_cons_fwd_v2);
fun multcomm_2 (mt,nt) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("m",0), ctermL2 mt),(("n",0), ctermL2 nt)] mult_comm_v2);
fun multassoc_2 (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("m",0), ctermL2 mt),(("n",0), ctermL2 nt),(("k",0), ctermL2 kt)] mult_assoc_v2);
fun mult1l_2 t = beta_norm (Drule.infer_instantiate ctxtL2 [(("n",0), ctermL2 t)] mult_1_left_v2);
fun mult_cong_r_2 (hT,pT,qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtL2
            [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 pT),(("b",0), ctermL2 qT)] oeq_subst_v2)
      val refl0 = oeqRefl_2 (mult hT pT)
  in inst OF [hpq, refl0] end;
fun lprod_cong_2 (aT,bT) hab =
  let val Pabs = Abs("z", natlistT, oeq (lprod aT) (lprod (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtL2
            [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 aT),(("b",0), ctermL2 bT)] leq_subst_v2)
      val refl0 = oeqRefl_2 (lprod aT)
  in inst OF [hab, refl0] end;
fun llen_cong_2 (aT,bT) hab =
  let val Pabs = Abs("z", natlistT, oeq (llen aT) (llen (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtL2
            [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 aT),(("b",0), ctermL2 bT)] leq_subst_v2)
      val refl0 = oeqRefl_2 (llen aT)
  in inst OF [hab, refl0] end;
fun lmem_transfer_2 (yT,aT,bT) hleq hmem =
  let val Pabs = Abs("z", natlistT, lmem yT (Bound 0))
      val inst = beta_norm (Drule.infer_instantiate ctxtL2
            [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 aT),(("b",0), ctermL2 bT)] leq_subst_v2)
  in inst OF [hleq, hmem] end;
fun lnodup_transfer_2 (aT,bT) hleq hnd =
  let val Pabs = Abs("z", natlistT, lnodup (Bound 0))
      val inst = beta_norm (Drule.infer_instantiate ctxtL2
            [(("P",0), ctermL2 Pabs),(("a",0), ctermL2 aT),(("b",0), ctermL2 bT)] leq_subst_v2)
  in inst OF [hleq, hnd] end;
fun cong_refl_2 (mt,at) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("m",0), ctermL2 mt),(("a",0), ctermL2 at)] cong_refl_v2);
fun cong_mult_2 (mt,at,a2t,bt,b2t) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("m",0), ctermL2 mt),(("a",0), ctermL2 at),(("a2",0), ctermL2 a2t),
         (("b",0), ctermL2 bt),(("b2",0), ctermL2 b2t)] cong_mult_v2)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun cong_trans_2 (mt,at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("m",0), ctermL2 mt),(("a",0), ctermL2 at),(("b",0), ctermL2 bt),(("c",0), ctermL2 ct)] cong_trans_v2)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun cong_cong_2 (mF,aF,a2F,bF,b2F) haa2 hbb2 hcong =
  let val zF1 = Free("zz1",natT)
      val Pabs1 = Term.lambda zF1 (cong mF zF1 bF)
      val inst1 = beta_norm (Drule.infer_instantiate ctxtL2
            [(("P",0), ctermL2 Pabs1),(("a",0), ctermL2 aF),(("b",0), ctermL2 a2F)] oeq_subst_v2)
      val cong1 = inst1 OF [haa2, hcong]
      val zF2 = Free("zz2",natT)
      val Pabs2 = Term.lambda zF2 (cong mF a2F zF2)
      val inst2 = beta_norm (Drule.infer_instantiate ctxtL2
            [(("P",0), ctermL2 Pabs2),(("a",0), ctermL2 bF),(("b",0), ctermL2 b2F)] oeq_subst_v2)
  in inst2 OF [hbb2, cong1] end;
fun lt_suc_2 nt = beta_norm (Drule.infer_instantiate ctxtL2 [(("n",0), ctermL2 nt)] lt_suc_v2);
fun inv_cong_2 (aT,bT) hab =
  let val Pabs = Abs("z", natT, oeq (inv aT) (inv (Bound 0)))
      val refl0 = oeqRefl_2 (inv aT)
  in oeq_rw_2 (Pabs, aT, bT) hab refl0 end;
fun inv_inj_2 h5 (xT,yT) hMemX hMemY hInvEq =
  let val hx = h5 xT hMemX
      val hy = h5 yT hMemY
      val hx_s = oeq_sym OF [hx]
      val hii = inv_cong_2 (inv xT, inv yT) hInvEq
      val c1 = oeq_trans OF [hx_s, hii]
  in oeq_trans OF [c1, hy] end;

(* L2 versions of the pieces list_strong_induct needs *)
val meta_nat_induct_v2 = varify meta_nat_induct_ax2;
val lt_suc_cases_v2    = varify lt_suc_cases;
val Suc_neq_Zero_v2    = varify Suc_neq_Zero_ax;
val add_Suc_v2         = varify add_Suc;
val exE_v2             = varify exE_ax;
fun addSuc_2 (mt,nt) = beta_norm (Drule.infer_instantiate ctxtL2
      [(("m",0), ctermL2 mt),(("n",0), ctermL2 nt)] add_Suc_v2);
fun Suc_neq_Zero_2 nt heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2 [(("n",0), ctermL2 nt)] Suc_neq_Zero_v2)) heq;
fun lt_suc_cases_2 (mt,nt) hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("m",0), ctermL2 mt),(("n",0), ctermL2 nt)] lt_suc_cases_v2)) hlt;
fun exE_elim_2 (Pabs, goalC) exThm wName bodyFn =
  let val wF = Free(wName, natT)
      val hypTerm = jT (Term.betapply (Pabs, wF))
      val hypThm  = Thm.assume (ctermL2 hypTerm)
      val body    = bodyFn wF hypThm
      val minor   = Thm.forall_intr (ctermL2 wF) (Thm.implies_intr (ctermL2 hypTerm) body)
      val exE_inst= beta_norm (Drule.infer_instantiate ctxtL2
                      [(("P",0), ctermL2 Pabs),(("Q",0), ctermL2 goalC)] exE_v2)
  in Thm.implies_elim (Thm.implies_elim exE_inst exThm) minor end;
fun lt_zero_elim_2 mT goalC hlt =
  let val Pabs = Abs("p", natT, oeq ZeroC (add (suc mT) (Bound 0)))
      fun body w (hw:thm) =
        let val aS = addSuc_2 (mT, w)
            val z_S = oeq_trans OF [hw, aS]
            val S_z = oeq_sym OF [z_S]
            val fls = Suc_neq_Zero_2 (add mT w) S_z
        in Thm.implies_elim (oFalse_elim_2 goalC) fls end
  in exE_elim_2 (Pabs, goalC) hlt "w_lz" body end;

(* L2 list strong induction (on llen), identical to the LL version but on ctxtL2 *)
fun list_strong_induct_2 PhiBody stepFn =
  let
    val LMeta = Free("L_lsi", natlistT)
    fun auxBody nt = Logic.all LMeta (Logic.mk_implies (jT (lt (llen LMeta) nt), jT (PhiBody LMeta)))
    val nMeta = Free("n_lsi", natT)
    val PhiMetaAbs = Term.lambda nMeta (auxBody nMeta)
    val base =
      let val LB = Free("L_b", natlistT)
          val hlt = Thm.assume (ctermL2 (jT (lt (llen LB) ZeroC)))
          val res = lt_zero_elim_2 (llen LB) (PhiBody LB) hlt
      in Thm.forall_intr (ctermL2 LB) (Thm.implies_intr (ctermL2 (jT (lt (llen LB) ZeroC))) res) end
    val step =
      let
        val xS = Free("x_lsi", natT)
        val auxX = auxBody xS
        val IHmeta = Thm.assume (ctermL2 auxX)
        fun applyAUXx L2 hlt = Thm.implies_elim (Thm.forall_elim (ctermL2 L2) IHmeta) hlt
        val LS = Free("L_s", natlistT)
        val hltS = Thm.assume (ctermL2 (jT (lt (llen LS) (suc xS))))
        val dThm = lt_suc_cases_2 (llen LS, xS) hltS
        val goalC = PhiBody LS
        val caseA = let val hA = Thm.assume (ctermL2 (jT (lt (llen LS) xS)))
                    in Thm.implies_intr (ctermL2 (jT (lt (llen LS) xS))) (applyAUXx LS hA) end
        val caseB =
          let val hB = Thm.assume (ctermL2 (jT (oeq (llen LS) xS)))
              fun applyIH L2 (h_lt:thm) =
                let val zpr = Free("z_pr", natT)
                    val Pr = Term.lambda zpr (lt (llen L2) zpr)
                    val h_lt_x = oeq_rw_2 (Pr, llen LS, xS) hB h_lt
                in applyAUXx L2 h_lt_x end
              val r = stepFn LS applyIH
          in Thm.implies_intr (ctermL2 (jT (oeq (llen LS) xS))) r end
        val inst = beta_norm (Drule.infer_instantiate ctxtL2
              [(("A",0), ctermL2 (lt (llen LS) xS)),(("B",0), ctermL2 (oeq (llen LS) xS)),
               (("C",0), ctermL2 goalC)] disjE_vL2)
        val pm = Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) caseA) caseB
        val dischLt = Thm.implies_intr (ctermL2 (jT (lt (llen LS) (suc xS)))) pm
        val auxSucx = Thm.forall_intr (ctermL2 LS) dischLt
      in Thm.forall_intr (ctermL2 xS) (Thm.implies_intr (ctermL2 auxX) auxSucx) end
    val LF = Free("L_fin", natlistT)
    val kFin = suc (llen LF)
    val indK = beta_norm (Drule.infer_instantiate ctxtL2
                 [(("Phi",0), ctermL2 PhiMetaAbs),(("k",0), ctermL2 kFin)] meta_nat_induct_v2)
    val auxK = Thm.implies_elim (Thm.implies_elim indK base) step
    val auxKL = Thm.forall_elim (ctermL2 LF) auxK
    val resLF = Thm.implies_elim auxKL (lt_suc_2 (llen LF))
  in (LF, resLF) end;

val () = out "PAIRING_L2_HELPERS_READY\n";

(* ============================================================================
   THE PAIRING LEMMA — hypotheses bundled into one object predicate Phi,
   proved by list strong induction.
   ============================================================================ *)
fun H2body L = let val xf = Free("xh2",natT)
               in mkForall (Term.lambda xf (mkImp (lmem xf L) (lmem (inv xf) L))) end;
fun H3body L = let val xf = Free("xh3",natT)
               in mkForall (Term.lambda xf (mkImp (lmem xf L) (cong pF (mult xf (inv xf)) oneN))) end;
fun H4body L = let val xf = Free("xh4",natT)
               in mkForall (Term.lambda xf (mkImp (lmem xf L) (neg (oeq (inv xf) xf)))) end;
fun H5body L = let val xf = Free("xh5",natT)
               in mkForall (Term.lambda xf (mkImp (lmem xf L) (oeq (inv (inv xf)) xf))) end;
fun PhiBody L =
  mkImp (lnodup L)
   (mkImp (H2body L)
     (mkImp (H3body L)
       (mkImp (H4body L)
         (mkImp (H5body L)
           (cong pF (lprod L) oneN)))));

val () = out "PAIRING_PHI_READY\n";

fun useH2 L hF2 z (hm : thm) =
  let val xf = Free("xh2",natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (lmem (inv xf) L))
      val inst = allE_at Pabs z hF2
  in mp_at (lmem z L, lmem (inv z) L) inst hm end;
fun useH3 L hF3 z (hm : thm) =
  let val xf = Free("xh3",natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (cong pF (mult xf (inv xf)) oneN))
      val inst = allE_at Pabs z hF3
  in mp_at (lmem z L, cong pF (mult z (inv z)) oneN) inst hm end;
fun useH4 L hF4 z (hm : thm) =
  let val xf = Free("xh4",natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (neg (oeq (inv xf) xf)))
      val inst = allE_at Pabs z hF4
  in mp_at (lmem z L, neg (oeq (inv z) z)) inst hm end;
fun useH5 L hF5 z (hm : thm) =
  let val xf = Free("xh5",natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (oeq (inv (inv xf)) xf))
      val inst = allE_at Pabs z hF5
  in mp_at (lmem z L, oeq (inv (inv z)) z) inst hm end;

fun useH2_2 L hF2 z (hm : thm) =
  let val xf = Free("xh2",natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (lmem (inv xf) L))
      val inst = allE_2 Pabs z hF2
  in mp_2 (lmem z L, lmem (inv z) L) inst hm end;
fun useH3_2 L hF3 z (hm : thm) =
  let val xf = Free("xh3",natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (cong pF (mult xf (inv xf)) oneN))
      val inst = allE_2 Pabs z hF3
  in mp_2 (lmem z L, cong pF (mult z (inv z)) oneN) inst hm end;
fun useH4_2 L hF4 z (hm : thm) =
  let val xf = Free("xh4",natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (neg (oeq (inv xf) xf)))
      val inst = allE_2 Pabs z hF4
  in mp_2 (lmem z L, neg (oeq (inv z) z)) inst hm end;
fun useH5_2 L hF5 z (hm : thm) =
  let val xf = Free("xh5",natT)
      val Pabs = Term.lambda xf (mkImp (lmem xf L) (oeq (inv (inv xf)) xf))
      val inst = allE_2 Pabs z hF5
  in mp_2 (lmem z L, oeq (inv (inv z)) z) inst hm end;

val extract_vv      = varify extract;
val llen_remove_vv  = varify llen_remove;
val lt_trans_vv     = varify lt_trans;
val nodup_remove_vv = varify nodup_remove;
val mem_remove_fwd_vv = varify mem_remove_fwd;
val mem_remove_bwd_vv = varify mem_remove_bwd;
val mem_remove_neq_vv = varify mem_remove_neq;
fun extract_2 (xt, Lt) hmem =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 xt),(("L",0), ctermL2 Lt)] extract_vv)) hmem;
fun llen_remove_2 (xt, Lt) hmem =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 xt),(("L",0), ctermL2 Lt)] llen_remove_vv)) hmem;
fun lt_trans_2 (at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("a",0), ctermL2 at),(("b",0), ctermL2 bt),(("c",0), ctermL2 ct)] lt_trans_vv)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun nodup_remove_2 (xt, Lt) hnd =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("x",0), ctermL2 xt),(("L",0), ctermL2 Lt)] nodup_remove_vv)) hnd;
fun mem_remove_fwd_2 (yt, xt, Lt) hmem =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("y",0), ctermL2 yt),(("x",0), ctermL2 xt),(("L",0), ctermL2 Lt)] mem_remove_fwd_vv)) hmem;
fun mem_remove_bwd_2 (yt, xt, Lt) hconj =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtL2
      [(("y",0), ctermL2 yt),(("x",0), ctermL2 xt),(("L",0), ctermL2 Lt)] mem_remove_bwd_vv)) hconj;
fun mem_remove_neq_2 (yt, xt, Lt) hnd hmem =  (* mem_remove_neq is a META impl *)
  let val inst = beta_norm (Drule.infer_instantiate ctxtL2
        [(("y",0), ctermL2 yt),(("x",0), ctermL2 xt),(("L",0), ctermL2 Lt)] mem_remove_neq_vv)
  in Thm.implies_elim (Thm.implies_elim inst hnd) hmem end;

val () = out "PAIRING_USEH_READY\n";

(* ---- the pairing lemma proper (ALL on ctxtL2) ---- *)
val pairing_lemma =
  let
    fun stepFn LS applyIH =
      let
        val hND = Thm.assume (ctermL2 (jT (lnodup LS)));
        val hF2 = Thm.assume (ctermL2 (jT (H2body LS)));
        val hF3 = Thm.assume (ctermL2 (jT (H3body LS)));
        val hF4 = Thm.assume (ctermL2 (jT (H4body LS)));
        val hF5 = Thm.assume (ctermL2 (jT (H5body LS)));
        val goalCong = cong pF (lprod LS) oneN;

        fun caseNil hnil =
          let
            val lpc = lprod_cong_2 (LS, lnilC) hnil;
            val lpn = lprodNil_at ();
            val lp1 = oeq_trans OF [lpc, lpn];
            val cr  = cong_refl_2 (pF, oneN);
            val lp1_s = oeq_sym OF [lp1];
            val one_refl = oeqRefl_2 oneN;
          in cong_cong_2 (pF, oneN, lprod LS, oneN, oneN) lp1_s one_refl cr end;

        fun caseCons (a, rest) hcons =
          let
            val consL = lcons a rest;
            val hcons_s = leq_sym OF [hcons];
            val a_in_cons = Thm.implies_elim (lmemConsBwd_2 (a, a, rest))
                              (disjI1_2 (oeq a a, lmem a rest) (oeqRefl_2 a));
            val memA = lmem_transfer_2 (a, consL, LS) hcons_s a_in_cons;
            val congA   = useH3_2 LS hF3 a memA;
            val neqInvA = useH4_2 LS hF4 a memA;
            val memInvA = useH2_2 LS hF2 a memA;
            val memInvA_cons = lmem_transfer_2 (inv a, LS, consL) hcons memInvA;
            val djInvA = Thm.implies_elim (lmemConsFwd_2 (inv a, a, rest)) memInvA_cons;
            val memInvA_rest =
              let
                val cEq = let val heqia = Thm.assume (ctermL2 (jT (oeq (inv a) a)))
                              val ff = mp_2 (oeq (inv a) a, oFalseC) neqInvA heqia
                          in Thm.implies_intr (ctermL2 (jT (oeq (inv a) a)))
                               (Thm.implies_elim (oFalse_elim_2 (lmem (inv a) rest)) ff) end;
                val cMem = let val hm = Thm.assume (ctermL2 (jT (lmem (inv a) rest)))
                           in Thm.implies_intr (ctermL2 (jT (lmem (inv a) rest))) hm end;
              in disjE_2 (oeq (inv a) a, lmem (inv a) rest, lmem (inv a) rest) djInvA cEq cMem end;
            val R = lremove (inv a) rest;
            val hND_cons = lnodup_transfer_2 (LS, consL) hcons hND;
            val cjND = Thm.implies_elim (lnodupConsFwd_2 (a, rest)) hND_cons;
            val a_notin_rest = conjunct1_2 (neg (lmem a rest), lnodup rest) cjND;
            val ndRest = conjunct2_2 (neg (lmem a rest), lnodup rest) cjND;

            val lp_cons = lprodCons_2 (a, rest);
            val lp_LS_cons = lprod_cong_2 (LS, consL) hcons;
            val lp_LS_1 = oeq_trans OF [lp_LS_cons, lp_cons];
            val lp_rest = extract_2 (inv a, rest) memInvA_rest;
            val step1m = mult_cong_r_2 (a, lprod rest, mult (inv a) (lprod R)) lp_rest;
            val assoc = multassoc_2 (a, inv a, lprod R);
            val assoc_s = oeq_sym OF [assoc];
            val lp_LS_final = oeq_trans OF [oeq_trans OF [lp_LS_1, step1m], assoc_s];

            val cong_factor = cong_mult_2 (pF, mult a (inv a), oneN, lprod R, lprod R)
                                congA (cong_refl_2 (pF, lprod R));
            val m1l = mult1l_2 (lprod R);
            val cong_factor2 = cong_cong_2 (pF, mult (mult a (inv a))(lprod R), mult (mult a (inv a))(lprod R),
                                                mult oneN (lprod R), lprod R)
                                 (oeqRefl_2 (mult (mult a (inv a))(lprod R))) m1l cong_factor;
            val lp_LS_final_s = oeq_sym OF [lp_LS_final];
            val cong_LS_R = cong_cong_2 (pF, mult (mult a (inv a))(lprod R), lprod LS, lprod R, lprod R)
                              lp_LS_final_s (oeqRefl_2 (lprod R)) cong_factor2;

            val ltRrest = llen_remove_2 (inv a, rest) memInvA_rest;
            val llc = llenCons_2 (a, rest);
            val llen_LS_cons = llen_cong_2 (LS, consL) hcons;
            val llen_LS_suc = oeq_trans OF [llen_LS_cons, llc];
            val lt_rest_suc = lt_suc_2 (llen rest);
            val llen_LS_suc_s = oeq_sym OF [llen_LS_suc];
            val zPrlt = Free("z_prlt", natT);
            val Prlt = Term.lambda zPrlt (lt (llen rest) zPrlt);
            val lt_rest_LS = oeq_rw_2 (Prlt, suc (llen rest), llen LS) llen_LS_suc_s lt_rest_suc;
            val ltR_LS = lt_trans_2 (llen R, llen rest, llen LS) ltRrest lt_rest_LS;
            val phiR = applyIH R ltR_LS;

            val ndR = nodup_remove_2 (inv a, rest) ndRest;
            fun mem_R_to_rest y hyR = mem_remove_fwd_2 (y, inv a, rest) hyR;
            fun rest_to_LS y hyRest =
              let val mem_cons = Thm.implies_elim (lmemConsBwd_2 (y, a, rest))
                                   (disjI2_2 (oeq y a, lmem y rest) hyRest)
              in lmem_transfer_2 (y, consL, LS) hcons_s mem_cons end;
            fun y_neq_invA y hyR = mem_remove_neq_2 (y, inv a, rest) ndRest hyR;

            val h3R =
              let val yf = Free("yh3r", natT)
                  val Pabs = Term.lambda yf (mkImp (lmem yf R) (cong pF (mult yf (inv yf)) oneN))
                  val hyR = Thm.assume (ctermL2 (jT (lmem yf R)))
                  val res = useH3_2 LS hF3 yf (rest_to_LS yf (mem_R_to_rest yf hyR))
                  val imp = impI_2 (lmem yf R, cong pF (mult yf (inv yf)) oneN)
                              (Thm.implies_intr (ctermL2 (jT (lmem yf R))) res)
              in allI_2 Pabs (Thm.forall_intr (ctermL2 yf) imp) end;
            val h4R =
              let val yf = Free("yh4r", natT)
                  val Pabs = Term.lambda yf (mkImp (lmem yf R) (neg (oeq (inv yf) yf)))
                  val hyR = Thm.assume (ctermL2 (jT (lmem yf R)))
                  val res = useH4_2 LS hF4 yf (rest_to_LS yf (mem_R_to_rest yf hyR))
                  val imp = impI_2 (lmem yf R, neg (oeq (inv yf) yf))
                              (Thm.implies_intr (ctermL2 (jT (lmem yf R))) res)
              in allI_2 Pabs (Thm.forall_intr (ctermL2 yf) imp) end;
            val h5R =
              let val yf = Free("yh5r", natT)
                  val Pabs = Term.lambda yf (mkImp (lmem yf R) (oeq (inv (inv yf)) yf))
                  val hyR = Thm.assume (ctermL2 (jT (lmem yf R)))
                  val res = useH5_2 LS hF5 yf (rest_to_LS yf (mem_R_to_rest yf hyR))
                  val imp = impI_2 (lmem yf R, oeq (inv (inv yf)) yf)
                              (Thm.implies_intr (ctermL2 (jT (lmem yf R))) res)
              in allI_2 Pabs (Thm.forall_intr (ctermL2 yf) imp) end;
            (* (e) H2body R : closed under inv (the hard one) *)
            val h2R =
              let
                val yf = Free("yh2r", natT)
                val Pabs = Term.lambda yf (mkImp (lmem yf R) (lmem (inv yf) R))
                val hyR = Thm.assume (ctermL2 (jT (lmem yf R)))
                val hyRest = mem_R_to_rest yf hyR
                val hyLS   = rest_to_LS yf hyRest
                val hyNeqIA = y_neq_invA yf hyR
                val memInvY_LS = useH2_2 LS hF2 yf hyLS
                val invY_neq_invA =
                  let val hEq = Thm.assume (ctermL2 (jT (oeq (inv yf) (inv a))))
                      val h5fn = (fn z => fn (hm:thm) => useH5_2 LS hF5 z hm)
                      val yEqA = inv_inj_2 h5fn (yf, a) hyLS memA hEq
                      val Pr = Abs("z", natT, lmem (Bound 0) rest)
                      val memArest = oeq_rw_2 (Pr, yf, a) yEqA hyRest
                      val ff = mp_2 (lmem a rest, oFalseC) a_notin_rest memArest
                  in impI_2 (oeq (inv yf) (inv a), oFalseC)
                       (Thm.implies_intr (ctermL2 (jT (oeq (inv yf) (inv a)))) ff) end;
                val memInvY_cons = lmem_transfer_2 (inv yf, LS, consL) hcons memInvY_LS
                val djInvY = Thm.implies_elim (lmemConsFwd_2 (inv yf, a, rest)) memInvY_cons
                val memInvY_rest =
                  let
                    val cEq = let val hia = Thm.assume (ctermL2 (jT (oeq (inv yf) a)))
                                  val invInvY_eq_invA = inv_cong_2 (inv yf, a) hia
                                  val h5y = useH5_2 LS hF5 yf hyLS
                                  val h5y_s = oeq_sym OF [h5y]
                                  val yEqInvA = oeq_trans OF [h5y_s, invInvY_eq_invA]
                                  val ff = mp_2 (oeq yf (inv a), oFalseC) hyNeqIA yEqInvA
                              in Thm.implies_intr (ctermL2 (jT (oeq (inv yf) a)))
                                   (Thm.implies_elim (oFalse_elim_2 (lmem (inv yf) rest)) ff) end
                    val cMem = let val hm = Thm.assume (ctermL2 (jT (lmem (inv yf) rest)))
                               in Thm.implies_intr (ctermL2 (jT (lmem (inv yf) rest))) hm end
                  in disjE_2 (oeq (inv yf) a, lmem (inv yf) rest, lmem (inv yf) rest) djInvY cEq cMem end;
                val conjBwd = conjI_2 (lmem (inv yf) rest, neg (oeq (inv yf) (inv a))) memInvY_rest invY_neq_invA
                val memInvY_R = mem_remove_bwd_2 (inv yf, inv a, rest) conjBwd
                val imp = impI_2 (lmem yf R, lmem (inv yf) R)
                            (Thm.implies_intr (ctermL2 (jT (lmem yf R))) memInvY_R)
              in allI_2 Pabs (Thm.forall_intr (ctermL2 yf) imp) end;

            val congR1 =
              let
                val s1 = mp_2 (lnodup R, mkImp (H2body R)(mkImp (H3body R)(mkImp (H4body R)(mkImp (H5body R)(cong pF (lprod R) oneN))))) phiR ndR
                val s2 = mp_2 (H2body R, mkImp (H3body R)(mkImp (H4body R)(mkImp (H5body R)(cong pF (lprod R) oneN)))) s1 h2R
                val s3 = mp_2 (H3body R, mkImp (H4body R)(mkImp (H5body R)(cong pF (lprod R) oneN))) s2 h3R
                val s4 = mp_2 (H4body R, mkImp (H5body R)(cong pF (lprod R) oneN)) s3 h4R
                val s5 = mp_2 (H5body R, cong pF (lprod R) oneN) s4 h5R
              in s5 end;
          in cong_trans_2 (pF, lprod LS, lprod R, oneN) cong_LS_R congR1 end;

        val congLS = list_cases (LS, goalCong) caseNil caseCons;
        val i5 = Thm.implies_intr (ctermL2 (jT (H5body LS))) congLS;
        val r5 = impI_2 (H5body LS, cong pF (lprod LS) oneN) i5;
        val i4 = Thm.implies_intr (ctermL2 (jT (H4body LS))) r5;
        val r4 = impI_2 (H4body LS, mkImp (H5body LS)(cong pF (lprod LS) oneN)) i4;
        val i3 = Thm.implies_intr (ctermL2 (jT (H3body LS))) r4;
        val r3 = impI_2 (H3body LS, mkImp (H4body LS)(mkImp (H5body LS)(cong pF (lprod LS) oneN))) i3;
        val i2 = Thm.implies_intr (ctermL2 (jT (H2body LS))) r3;
        val r2 = impI_2 (H2body LS, mkImp (H3body LS)(mkImp (H4body LS)(mkImp (H5body LS)(cong pF (lprod LS) oneN)))) i2;
        val i1 = Thm.implies_intr (ctermL2 (jT (lnodup LS))) r2;
        val r1 = impI_2 (lnodup LS, mkImp (H2body LS)(mkImp (H3body LS)(mkImp (H4body LS)(mkImp (H5body LS)(cong pF (lprod LS) oneN)))) ) i1;
      in r1 end;
    val (LF, resPhi) = list_strong_induct_2 PhiBody stepFn;
  in varify resPhi end;

val () = out "OK pairing_lemma constructed\n";

(* ============================================================================
   VALIDATION : 0-hyp + aconv intended (inv/p/L schematic Vars after varify).
   ============================================================================ *)
val invV = Var (("inv",0), natT --> natT);
fun invv t = invV $ t;
val pV   = Var (("p",0), natT);
val LV   = Var (("L_fin",0), natlistT);
fun H2bodyV L = let val xf = Free("xh2",natT) in mkForall (Term.lambda xf (mkImp (lmem xf L) (lmem (invv xf) L))) end;
fun H3bodyV L = let val xf = Free("xh3",natT) in mkForall (Term.lambda xf (mkImp (lmem xf L) (cong pV (mult xf (invv xf)) (suc ZeroC)))) end;
fun H4bodyV L = let val xf = Free("xh4",natT) in mkForall (Term.lambda xf (mkImp (lmem xf L) (neg (oeq (invv xf) xf)))) end;
fun H5bodyV L = let val xf = Free("xh5",natT) in mkForall (Term.lambda xf (mkImp (lmem xf L) (oeq (invv (invv xf)) xf))) end;
val pairing_intended =
  jT (mkImp (lnodup LV)
       (mkImp (H2bodyV LV)
         (mkImp (H3bodyV LV)
           (mkImp (H4bodyV LV)
             (mkImp (H5bodyV LV)
               (cong pV (lprod LV) (suc ZeroC)))))));

val r_pairing =
  let val nh = length (Thm.hyps_of pairing_lemma)
      val ac = (Thm.prop_of pairing_lemma) aconv pairing_intended
  in if nh=0 andalso ac then (out "OK pairing_lemma (0-hyp, aconv intended)\n"; true)
     else (out ("FAIL pairing_lemma (hyps="^Int.toString nh^" aconv="^Bool.toString ac^")\n"
                ^"  got      = "^Syntax.string_of_term ctxtL2 (Thm.prop_of pairing_lemma)^"\n"
                ^"  intended = "^Syntax.string_of_term ctxtL2 pairing_intended^"\n"); false) end;

val pairing_noH3 =
  jT (mkImp (lnodup LV)
       (mkImp (H2bodyV LV)
         (mkImp (H4bodyV LV)
           (mkImp (H5bodyV LV)
             (cong pV (lprod LV) (suc ZeroC))))));
val probe_uses_H3 = not ((Thm.prop_of pairing_lemma) aconv pairing_noH3);
val () = if probe_uses_H3 then out "PROBE_OK pairing_lemma genuinely uses H3 (inverse hyp)\n"
         else out "PROBE_FAIL pairing_lemma dropped H3\n";

val probe_conditional = not ((Thm.prop_of pairing_lemma) aconv (jT (cong pV (lprod LV) (suc ZeroC))));
val () = if probe_conditional then out "PROBE_OK pairing_lemma is conditional (not unconditional)\n"
         else out "PROBE_FAIL pairing_lemma collapsed to unconditional\n";

val () =
  if r_pairing andalso probe_uses_H3 andalso probe_conditional
  then out "PAIRING_OK\n"
  else out "PAIRING_FAILED\n";
(* ============================================================================
   THE MODULAR-INVERSE FUNCTION + RESIDUE RANGE toward Wilson's theorem, in
   Isabelle/Pure on the polyml-rs interpreter.  (test: isabelle_wilson_inverse.rs)
   ----------------------------------------------------------------------------
   The pairing_lemma (proved in isabelle_wilson_pairing.sml) needs the modular
   inverse as a literal FUNCTION (an involution on the residue list). But the
   object logic has no choice operator and `cong` is not directly decidable. The
   unlock here: a `mod` function makes congruence decidable, so the inverse can be
   built by a list search. Proved by genuine kernel inference:

   (A) RANGE + MOD (range-mod phase):
       rmod / rdiv (remainder/quotient) via conservative axioms from the division
       theorem, the BRIDGE  cong_iff_rmod : 0<p ==> (cong p a b <-> rmod a p = rmod b p)
       (both directions -- this makes congruence DECIDABLE), and the residue range
       upto n = [1,..,n] with lnodup (upto n) and lmem_upto (membership = 1<=b<=n).

   (B) THE INVERSE FUNCTION (inverse-fn phase):
       finv p x = search upto(p-1) for x's inverse (decidable now via rmod), proved
       for prime p and x in [1..p-1]:
         finv_inv   : cong p (x * finv p x) 1        (it IS an inverse)
         finv_mem   : lmem (finv p x) (upto (p-1))   (lands back in range)
         finv_invol : finv p (finv p x) = x          (LITERAL involution, via inverse_unique)
         finv_neq   : on [2..p-2], finv p x <> x     (fixed-point free, via lagrange_roots)

   These are exactly pairing_lemma's hypotheses. Each lemma is 0-hyp, aconv the
   intended statement, with soundness probes. Built on the Wilson-pairing base via
   common::with_wilson_pairing. Proved by a 2-phase ultracode fleet (wf_a22d8bd7-115);
   re-verified end-to-end by hand. NEXT (the finale): apply pairing_lemma to [2..p-2]
   with finv to get lprod[2..p-2] == 1, then (p-1)! = 1 * lprod[2..p-2] * (p-1) == -1.
   ============================================================================ *)

(* ============================================================================
   PHASE 1 (seat rm0): rmod / rdiv + cong_iff_rmod ; upto + lnodup + lmem_upto
   Built on the FINAL base context (thyL2 / ctxtL2 / ctermL2).
   NOTE: `upto` is an SML basis infix; the term builder is named uptoF.
   ============================================================================ *)
val () = out "RM_PHASE1_BEGIN\n";

(* ---- new theory: add consts rmod, rdiv, upto ---- *)
val thyRMc = Sign.add_consts
  [(Binding.name "rmod", natT --> natT --> natT, NoSyn),
   (Binding.name "rdiv", natT --> natT --> natT, NoSyn),
   (Binding.name "upto", natT --> natlistT, NoSyn)] thyL2;

fun cnstRM nm T = Const (Sign.full_name thyRMc (Binding.name nm), T);
val rmodC = cnstRM "rmod" (natT --> natT --> natT); fun rmod a p = rmodC $ a $ p;
val rdivC = cnstRM "rdiv" (natT --> natT --> natT); fun rdiv a p = rdivC $ a $ p;
val uptoC = cnstRM "upto" (natT --> natlistT);      fun uptoF n = uptoC $ n;

(* free vars for axiom statements *)
val aRM = Free("a", natT); val bRM = Free("b", natT); val pRM = Free("p", natT);
val nRM = Free("n", natT);

(* ---- (A) division-derived conservative axioms ---- *)
val ((_,div_mod_eq_ax), thyRM1) = Thm.add_axiom_global (Binding.name "div_mod_eq",
      Logic.mk_implies (jT (lt ZeroC pRM),
        jT (oeq aRM (add (mult pRM (rdiv aRM pRM)) (rmod aRM pRM))))) thyRMc;
val ((_,rmod_lt_ax), thyRM2) = Thm.add_axiom_global (Binding.name "rmod_lt",
      Logic.mk_implies (jT (lt ZeroC pRM), jT (lt (rmod aRM pRM) pRM))) thyRM1;

(* ---- (B) uptoF recursion axioms ---- *)
val ((_,upto_zero_ax), thyRM3) = Thm.add_axiom_global (Binding.name "upto_zero",
      jT (leq (uptoF ZeroC) lnilC)) thyRM2;
val ((_,upto_suc_ax), thyRM) = Thm.add_axiom_global (Binding.name "upto_suc",
      jT (leq (uptoF (suc nRM)) (lcons (suc nRM) (uptoF nRM)))) thyRM3;

val ctxtRM  = Proof_Context.init_global thyRM;
val ctermRM = Thm.cterm_of ctxtRM;
val () = out "RM_CONTEXT_READY\n";

(* ============================================================================
   re-varify reused base axioms/lemmas onto ctxtRM
   ============================================================================ *)
val oeq_refl_vR    = varify oeq_refl;
val oeq_subst_vR   = varify oeq_subst;
val oeq_sym_vR     = varify oeq_sym;
val oeq_trans_vR   = varify oeq_trans;
val Suc_cong_vR    = varify Suc_cong;
val exI_vR         = varify exI_ax;
val exE_vR         = varify exE_ax;
val oFalse_elim_vR = varify oFalse_elim_ax;
val Suc_neq_Zero_vR= varify Suc_neq_Zero_ax;
val Suc_inj_vR     = varify Suc_inj_ax;
val conjI_vR       = varify conjI_ax;
val conjunct1_vR   = varify conjunct1_ax;
val conjunct2_vR   = varify conjunct2_ax;
val disjI1_vR      = varify disjI1_ax;
val disjI2_vR      = varify disjI2_ax;
val disjE_vR       = varify disjE_ax;
val mp_vR          = varify mp_ax;
val impI_vR        = varify impI_ax;
val ex_middle_vR   = varify ex_middle_ax;
val allI_vR        = varify allI_ax;
val allE_vR        = varify allE_ax;
val add_0_vR       = varify add_0;
val add_Suc_vR     = varify add_Suc;
val add_0_right_vR = varify add_0_right;
val add_comm_vR    = varify add_comm;
val add_assoc_vR   = varify add_assoc;
val add_left_cancel_vR = varify add_left_cancel;
val mult_0_vR      = varify mult_0;
val mult_Suc_vR    = varify mult_Suc;
val mult_0_right_vR= varify mult_0_right;
val mult_Suc_right_vR = varify mult_Suc_right;
val mult_comm_vR   = varify mult_comm;
val mult_assoc_vR  = varify mult_assoc;
val mult_1_left_vR = varify mult_1_left;
val left_distrib_vR = varify left_distrib;
val right_distrib_vR = varify right_distrib;
val le_refl_vR     = varify le_refl;
val le_trans_vR    = varify le_trans;
val le_total_vR    = varify le_total;
val le_antisym_vR  = varify le_antisym;
val le_add_vR      = varify le_add;
val zero_le_vR     = varify zero_le;
val lt_suc_vR      = varify lt_suc;
val lt_trans_vR    = varify lt_trans;
val lt_suc_cases_vR= varify lt_suc_cases;
val nlt_le_vR      = varify nlt_le;
val div_mod_unique_vR = varify div_mod_unique;
(* list machinery *)
val leq_refl_vR    = varify leq_refl_ax;
val leq_subst_vR   = varify leq_subst_ax;
val list_induct_vR = varify list_induct_ax;
val lmem_nil_elim_vR = varify lmem_nil_elim_ax;
val lmem_cons_fwd_vR = varify lmem_cons_fwd_ax;
val lmem_cons_bwd_vR = varify lmem_cons_bwd_ax;
val lnodup_nil_vR  = varify lnodup_nil_ax;
val lnodup_cons_fwd_vR = varify lnodup_cons_fwd_ax;
val lnodup_cons_bwd_vR = varify lnodup_cons_bwd_ax;
(* new axioms *)
val div_mod_eq_vR  = varify div_mod_eq_ax;
val rmod_lt_vR     = varify rmod_lt_ax;
val upto_zero_vR   = varify upto_zero_ax;
val upto_suc_vR    = varify upto_suc_ax;
val () = out "RM_VARIFY_READY\n";

(* ============================================================================
   combinators on ctxtRM (suffix _R)
   ============================================================================ *)
fun oeqRefl_R t = beta_norm (Drule.infer_instantiate ctxtRM [(("a",0), ctermRM t)] oeq_refl_vR);
fun add0_R t    = beta_norm (Drule.infer_instantiate ctxtRM [(("n",0), ctermRM t)] add_0_vR);
fun add0r_R t   = beta_norm (Drule.infer_instantiate ctxtRM [(("n",0), ctermRM t)] add_0_right_vR);
fun addSuc_R (mt,nt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("n",0), ctermRM nt)] add_Suc_vR);
fun addcomm_R (mt,nt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("n",0), ctermRM nt)] add_comm_vR);
fun addassoc_R (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("n",0), ctermRM nt),(("k",0), ctermRM kt)] add_assoc_vR);
fun mult0r_R t  = beta_norm (Drule.infer_instantiate ctxtRM [(("n",0), ctermRM t)] mult_0_right_vR);
fun multcomm_R (mt,nt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("n",0), ctermRM nt)] mult_comm_vR);
fun multassoc_R (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("n",0), ctermRM nt),(("k",0), ctermRM kt)] mult_assoc_vR);
fun leftdistrib_R (xt,mt,nt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("x",0), ctermRM xt),(("m",0), ctermRM mt),(("n",0), ctermRM nt)] left_distrib_vR);

fun oeq_rw_R (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("P",0), ctermRM Pabs),(("a",0), ctermRM aT),(("b",0), ctermRM bT)] oeq_subst_vR)
  in inst OF [hab, hPa] end;
fun add_cong_l_R (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT))
  in oeq_rw_R (Pabs, pT, qT) hpq (oeqRefl_R (add pT kT)) end;
fun add_cong_r_R (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)))
  in oeq_rw_R (Pabs, pT, qT) hpq (oeqRefl_R (add hT pT)) end;
fun mult_cong_l_R (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT))
  in oeq_rw_R (Pabs, pT, qT) hpq (oeqRefl_R (mult pT kT)) end;
fun mult_cong_r_R (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)))
  in oeq_rw_R (Pabs, pT, qT) hpq (oeqRefl_R (mult hT pT)) end;

fun mp_R (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("A",0), ctermRM At),(("B",0), ctermRM Bt)] mp_vR)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_R (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("A",0), ctermRM At),(("B",0), ctermRM Bt)] impI_vR)
  in Thm.implies_elim inst hImpThm end;
fun conjI_R (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("A",0), ctermRM At),(("B",0), ctermRM Bt)] conjI_vR)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_R (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("A",0), ctermRM At),(("B",0), ctermRM Bt)] conjunct1_vR)) h;
fun conjunct2_R (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("A",0), ctermRM At),(("B",0), ctermRM Bt)] conjunct2_vR)) h;
fun oFalse_elim_R rT = beta_norm (Drule.infer_instantiate ctxtRM [(("R",0), ctermRM rT)] oFalse_elim_vR);
fun disjE_R (At,Bt,Ct) dThm cA cB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("A",0), ctermRM At),(("B",0), ctermRM Bt),(("C",0), ctermRM Ct)] disjE_vR)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) cA) cB end;
fun disjI1_R (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("A",0), ctermRM At),(("B",0), ctermRM Bt)] disjI1_vR)) h;
fun disjI2_R (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("A",0), ctermRM At),(("B",0), ctermRM Bt)] disjI2_vR)) h;
fun em_R t = beta_norm (Drule.infer_instantiate ctxtRM [(("A",0), ctermRM t)] ex_middle_vR);
fun allI_R Pabs hAll = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("P",0), ctermRM Pabs)] allI_vR)) hAll;
fun allE_R Pabs at hF = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("P",0), ctermRM Pabs),(("a",0), ctermRM at)] allE_vR)) hF;
fun Suc_neq_Zero_R nt heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM [(("n",0), ctermRM nt)] Suc_neq_Zero_vR)) heq;
fun Suc_inj_R (at,bt) heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("a",0), ctermRM at),(("b",0), ctermRM bt)] Suc_inj_vR)) heq;

fun exI_R Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("P",0), ctermRM Pabs),(("a",0), ctermRM at)] exI_vR)
  in Thm.implies_elim inst hbody end;
fun exE_R (Pabs, goalC) exThm wName bodyFn =
  let val wF = Free(wName, natT)
      val hypTerm = jT (Term.betapply (Pabs, wF))
      val hypThm  = Thm.assume (ctermRM hypTerm)
      val body    = bodyFn wF hypThm
      val minor   = Thm.forall_intr (ctermRM wF) (Thm.implies_intr (ctermRM hypTerm) body)
      val exE_inst= beta_norm (Drule.infer_instantiate ctxtRM
                      [(("P",0), ctermRM Pabs),(("Q",0), ctermRM goalC)] exE_vR)
  in Thm.implies_elim (Thm.implies_elim exE_inst exThm) minor end;

fun le_intro_R (mT, nT, w) hyp =
  let val Pabs = Abs("p", natT, oeq nT (add mT (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtRM
            [(("P",0), ctermRM Pabs),(("a",0), ctermRM w)] exI_vR)
  in inst OF [hyp] end;
fun le_total_R (mt,nt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("n",0), ctermRM nt)] le_total_vR);
fun le_trans_R (at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("m",0), ctermRM at),(("n",0), ctermRM bt),(("k",0), ctermRM ct)] le_trans_vR)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun lt_trans_R (at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("a",0), ctermRM at),(("b",0), ctermRM bt),(("c",0), ctermRM ct)] lt_trans_vR)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun lt_suc_cases_R (mt,nt) hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("n",0), ctermRM nt)] lt_suc_cases_vR)) hlt;
fun nlt_le_R (dt, ct) hneg =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("d",0), ctermRM dt),(("c",0), ctermRM ct)] nlt_le_vR)) hneg;
fun lt_suc_R nt = beta_norm (Drule.infer_instantiate ctxtRM [(("n",0), ctermRM nt)] lt_suc_vR);
fun le_antisym_R (mt,nt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("m",0), ctermRM mt),(("n",0), ctermRM nt)] le_antisym_vR)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun le_add_R (mt,pt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("p",0), ctermRM pt)] le_add_vR);

fun div_mod_eq_R (at,pt) hpos =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("a",0), ctermRM at),(("p",0), ctermRM pt)] div_mod_eq_vR)) hpos;
fun rmod_lt_R (at,pt) hpos =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("a",0), ctermRM at),(("p",0), ctermRM pt)] rmod_lt_vR)) hpos;
fun div_mod_unique_R (b,q1,r1,q2,r2) heq hlt1 hlt2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("b",0), ctermRM b),(("q1",0), ctermRM q1),(("r1",0), ctermRM r1),
         (("q2",0), ctermRM q2),(("r2",0), ctermRM r2)] div_mod_unique_vR)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst heq) hlt1) hlt2 end;

val () = out "RM_COMBINATORS_READY\n";

(* ============================================================================
   cong constructors on ctxtRM (cong/congL/congR defined in base).
   congL m a b = ?k. b = a + m*k ; congR m a b = ?k. a = b + m*k.
   ============================================================================ *)
fun cong_introL_R (m,a,b,w) hyp =
  let val Pabs = Abs("k", natT, oeq b (add a (mult m (Bound 0))))
      val ex = exI_R Pabs w hyp
  in disjI1_R (congL m a b, congR m a b) ex end;
fun cong_introR_R (m,a,b,w) hyp =
  let val Pabs = Abs("k", natT, oeq a (add b (mult m (Bound 0))))
      val ex = exI_R Pabs w hyp
  in disjI2_R (congL m a b, congR m a b) ex end;

(* ============================================================================
   cong_imp_rmodeq : 0<p ==> cong p a b ==> oeq (rmod a p) (rmod b p)
   ============================================================================ *)
val cong_imp_rmodeq =
  let
    val aF = Free("a",natT); val bF = Free("b",natT); val pF = Free("p",natT);
    val posP = jT (lt ZeroC pF);
    val hpos = Thm.assume (ctermRM posP);
    val congP = jT (cong pF aF bF);
    val hcong = Thm.assume (ctermRM congP);
    val goalC = oeq (rmod aF pF) (rmod bF pF);
    val hAeq = div_mod_eq_R (aF, pF) hpos;
    val hBeq = div_mod_eq_R (bF, pF) hpos;
    val hAlt = rmod_lt_R (aF, pF) hpos;
    val hBlt = rmod_lt_R (bF, pF) hpos;
    val qa = rdiv aF pF; val ra = rmod aF pF;
    val qb = rdiv bF pF; val rb = rmod bF pF;
    val caseL =
      let
        val hL = Thm.assume (ctermRM (jT (congL pF aF bF)))
        val Pabs = Abs("k", natT, oeq bF (add aF (mult pF (Bound 0))))
        fun body k (hk:thm) =
          let
            val c1 = add_cong_l_R (aF, add (mult pF qa) ra, mult pF k) hAeq;
            val b_e1 = oeq_trans_vR OF [hk, c1];
            val assoc1 = addassoc_R (mult pF qa, ra, mult pF k);
            val b_e2 = oeq_trans_vR OF [b_e1, assoc1];
            val comm1 = addcomm_R (ra, mult pF k);
            val c_inner = add_cong_r_R (mult pF qa, add ra (mult pF k), add (mult pF k) ra) comm1;
            val b_e3 = oeq_trans_vR OF [b_e2, c_inner];
            val assoc2 = addassoc_R (mult pF qa, mult pF k, ra);
            val b_e4 = oeq_trans_vR OF [b_e3, oeq_sym_vR OF [assoc2]];
            val ld = leftdistrib_R (pF, qa, k);
            val c_fold = add_cong_l_R (add (mult pF qa)(mult pF k), mult pF (add qa k), ra) (oeq_sym_vR OF [ld]);
            val b_final = oeq_trans_vR OF [b_e4, c_fold];
            val eqUnique = oeq_trans_vR OF [oeq_sym_vR OF [b_final], hBeq];
            val uniq = div_mod_unique_R (pF, add qa k, ra, qb, rb) eqUnique hAlt hBlt;
            val ra_rb = conjunct2_R (oeq (add qa k) qb, oeq ra rb) uniq;
          in ra_rb end
        val res = exE_R (Pabs, goalC) hL "kL" body
      in Thm.implies_intr (ctermRM (jT (congL pF aF bF))) res end;
    val caseR =
      let
        val hR = Thm.assume (ctermRM (jT (congR pF aF bF)))
        val Pabs = Abs("k", natT, oeq aF (add bF (mult pF (Bound 0))))
        fun body k (hk:thm) =
          let
            val c1 = add_cong_l_R (bF, add (mult pF qb) rb, mult pF k) hBeq;
            val a_e1 = oeq_trans_vR OF [hk, c1];
            val assoc1 = addassoc_R (mult pF qb, rb, mult pF k);
            val a_e2 = oeq_trans_vR OF [a_e1, assoc1];
            val comm1 = addcomm_R (rb, mult pF k);
            val c_inner = add_cong_r_R (mult pF qb, add rb (mult pF k), add (mult pF k) rb) comm1;
            val a_e3 = oeq_trans_vR OF [a_e2, c_inner];
            val assoc2 = addassoc_R (mult pF qb, mult pF k, rb);
            val a_e4 = oeq_trans_vR OF [a_e3, oeq_sym_vR OF [assoc2]];
            val ld = leftdistrib_R (pF, qb, k);
            val c_fold = add_cong_l_R (add (mult pF qb)(mult pF k), mult pF (add qb k), rb) (oeq_sym_vR OF [ld]);
            val a_final = oeq_trans_vR OF [a_e4, c_fold];
            val eqUnique = oeq_trans_vR OF [oeq_sym_vR OF [a_final], hAeq];
            val uniq = div_mod_unique_R (pF, add qb k, rb, qa, ra) eqUnique hBlt hAlt;
            val rb_ra = conjunct2_R (oeq (add qb k) qa, oeq rb ra) uniq;
          in oeq_sym_vR OF [rb_ra] end
        val res = exE_R (Pabs, goalC) hR "kR" body
      in Thm.implies_intr (ctermRM (jT (congR pF aF bF))) res end;
    val res = disjE_R (congL pF aF bF, congR pF aF bF, goalC) hcong caseL caseR;
    val disch2 = Thm.implies_intr (ctermRM congP) res;
    val disch1 = Thm.implies_intr (ctermRM posP) disch2;
  in varify disch1 end;
val () = if length (Thm.hyps_of cong_imp_rmodeq) = 0 then out "OK cong_imp_rmodeq\n" else out "FAIL cong_imp_rmodeq\n";
val () = out "RM_DIR1_DONE\n";

(* ============================================================================
   DIRECTION 2 : rmodeq_imp_cong : 0<p ==> oeq (rmod a p)(rmod b p) ==> cong p a b
   ============================================================================ *)
val rmodeq_imp_cong =
  let
    val aF = Free("a",natT); val bF = Free("b",natT); val pF = Free("p",natT);
    val posP = jT (lt ZeroC pF);
    val hpos = Thm.assume (ctermRM posP);
    val eqP  = jT (oeq (rmod aF pF) (rmod bF pF));
    val heq  = Thm.assume (ctermRM eqP);
    val goalC = cong pF aF bF;
    val qa = rdiv aF pF; val ra = rmod aF pF;
    val qb = rdiv bF pF; val rb = rmod bF pF;
    val hAeq = div_mod_eq_R (aF, pF) hpos;
    val hBeq = div_mod_eq_R (bF, pF) hpos;
    val tot = le_total_R (qa, qb);
    val caseLe =
      let
        val hle = Thm.assume (ctermRM (jT (le qa qb)))
        val Pabs = Abs("d", natT, oeq qb (add qa (Bound 0)))
        fun body d (hd:thm) =
          let
            val c_qb = mult_cong_r_R (pF, qb, add qa d) hd;
            val c1 = add_cong_l_R (mult pF qb, mult pF (add qa d), rb) c_qb;
            val b_e1 = oeq_trans_vR OF [hBeq, c1];
            val ld = leftdistrib_R (pF, qa, d);
            val c2 = add_cong_l_R (mult pF (add qa d), add (mult pF qa)(mult pF d), rb) ld;
            val b_e2 = oeq_trans_vR OF [b_e1, c2];
            val assoc1 = addassoc_R (mult pF qa, mult pF d, rb);
            val b_e3 = oeq_trans_vR OF [b_e2, assoc1];
            val comm1 = addcomm_R (mult pF d, rb);
            val c3 = add_cong_r_R (mult pF qa, add (mult pF d) rb, add rb (mult pF d)) comm1;
            val b_e4 = oeq_trans_vR OF [b_e3, c3];
            val assoc2 = addassoc_R (mult pF qa, rb, mult pF d);
            val b_e5 = oeq_trans_vR OF [b_e4, oeq_sym_vR OF [assoc2]];
            val rb_ra = oeq_sym_vR OF [heq];
            val c4 = add_cong_r_R (mult pF qa, rb, ra) rb_ra;
            val c4b = add_cong_l_R (add (mult pF qa) rb, add (mult pF qa) ra, mult pF d) c4;
            val b_e6 = oeq_trans_vR OF [b_e5, c4b];
            val a_eq = oeq_sym_vR OF [hAeq];
            val c5 = add_cong_l_R (add (mult pF qa) ra, aF, mult pF d) a_eq;
            val b_final = oeq_trans_vR OF [b_e6, c5];
          in cong_introL_R (pF, aF, bF, d) b_final end
        val res = exE_R (Pabs, goalC) hle "dLe" body
      in Thm.implies_intr (ctermRM (jT (le qa qb))) res end;
    val caseGe =
      let
        val hle = Thm.assume (ctermRM (jT (le qb qa)))
        val Pabs = Abs("d", natT, oeq qa (add qb (Bound 0)))
        fun body d (hd:thm) =
          let
            val c_qa = mult_cong_r_R (pF, qa, add qb d) hd;
            val c1 = add_cong_l_R (mult pF qa, mult pF (add qb d), ra) c_qa;
            val a_e1 = oeq_trans_vR OF [hAeq, c1];
            val ld = leftdistrib_R (pF, qb, d);
            val c2 = add_cong_l_R (mult pF (add qb d), add (mult pF qb)(mult pF d), ra) ld;
            val a_e2 = oeq_trans_vR OF [a_e1, c2];
            val assoc1 = addassoc_R (mult pF qb, mult pF d, ra);
            val a_e3 = oeq_trans_vR OF [a_e2, assoc1];
            val comm1 = addcomm_R (mult pF d, ra);
            val c3 = add_cong_r_R (mult pF qb, add (mult pF d) ra, add ra (mult pF d)) comm1;
            val a_e4 = oeq_trans_vR OF [a_e3, c3];
            val assoc2 = addassoc_R (mult pF qb, ra, mult pF d);
            val a_e5 = oeq_trans_vR OF [a_e4, oeq_sym_vR OF [assoc2]];
            val c4 = add_cong_r_R (mult pF qb, ra, rb) heq;
            val c4b = add_cong_l_R (add (mult pF qb) ra, add (mult pF qb) rb, mult pF d) c4;
            val a_e6 = oeq_trans_vR OF [a_e5, c4b];
            val b_eq = oeq_sym_vR OF [hBeq];
            val c5 = add_cong_l_R (add (mult pF qb) rb, bF, mult pF d) b_eq;
            val a_final = oeq_trans_vR OF [a_e6, c5];
          in cong_introR_R (pF, aF, bF, d) a_final end
        val res = exE_R (Pabs, goalC) hle "dGe" body
      in Thm.implies_intr (ctermRM (jT (le qb qa))) res end;
    val res = disjE_R (le qa qb, le qb qa, goalC) tot caseLe caseGe;
    val disch2 = Thm.implies_intr (ctermRM eqP) res;
    val disch1 = Thm.implies_intr (ctermRM posP) disch2;
  in varify disch1 end;
val () = if length (Thm.hyps_of rmodeq_imp_cong) = 0 then out "OK rmodeq_imp_cong\n" else out "FAIL rmodeq_imp_cong\n";
val () = out "RM_DIR2_DONE\n";
val () = out "RM_CONG_IFF_BOTH_DONE\n";

(* ============================================================================
   UPTO lemmas.  uptoF characterized by leq axioms; transfer lmem/lnodup through leq.
   ============================================================================ *)
val nat_induct_vR  = varify nat_induct;
val leq_sym_vR     = varify leq_sym;
val leq_trans_vR   = varify leq_trans;
val disj_zero_or_suc_vR = varify disj_zero_or_suc;
val add_eq_zero_left_vR = varify add_eq_zero_left;
val add_Suc_right_vR = varify add_Suc_right;

fun mkExSuc_R t = mkEx (Abs ("q", natT, oeq t (suc (Bound 0))));
fun dzos_R t = beta_norm (Drule.infer_instantiate ctxtRM [(("p",0), ctermRM t)] disj_zero_or_suc_vR);
fun add_eq_zero_left_R (at,bt) heq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("a",0), ctermRM at),(("b",0), ctermRM bt)] add_eq_zero_left_vR)
  in inst OF [heq] end;
fun addSr_at_R (mt,nt) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("m",0), ctermRM mt),(("n",0), ctermRM nt)] add_Suc_right_vR);
fun nat_induct_R Pabs kT baseThm stepThm =
  let val ind = beta_norm (Drule.infer_instantiate ctxtRM
        [(("P",0), ctermRM Pabs),(("k",0), ctermRM kT)] nat_induct_vR)
  in Thm.implies_elim (Thm.implies_elim ind baseThm) stepThm end;
fun uptoSuc_R nt = beta_norm (Drule.infer_instantiate ctxtRM [(("n",0), ctermRM nt)] upto_suc_vR);
val uptoZero_R = upto_zero_vR;
fun leq_rw_R (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
        [(("P",0), ctermRM Pabs),(("a",0), ctermRM aT),(("b",0), ctermRM bT)] leq_subst_vR)
  in inst OF [hab, hPa] end;
fun leq_sym_R h = leq_sym_vR OF [h];
fun lmemNilElim_R x = beta_norm (Drule.infer_instantiate ctxtRM [(("x",0), ctermRM x)] lmem_nil_elim_vR);
fun lmemConsFwd_R (x,y,t) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("x",0), ctermRM x),(("y",0), ctermRM y),(("t",0), ctermRM t)] lmem_cons_fwd_vR);
fun lmemConsBwd_R (x,y,t) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("x",0), ctermRM x),(("y",0), ctermRM y),(("t",0), ctermRM t)] lmem_cons_bwd_vR);
fun lnodupCons_bwd_R (x,t) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("x",0), ctermRM x),(("t",0), ctermRM t)] lnodup_cons_bwd_vR);
fun lnodupCons_fwd_R (x,t) = beta_norm (Drule.infer_instantiate ctxtRM
      [(("x",0), ctermRM x),(("t",0), ctermRM t)] lnodup_cons_fwd_vR);
val lnodupNil_R = lnodup_nil_vR;
val () = out "RM_UPTO_COMB_READY\n";

(* ============================================================================
   le_suc_split : le b (Suc n) ==> Disj (oeq b (Suc n)) (le b n)
   ============================================================================ *)
val le_suc_split =
  let
    val bF = Free("b",natT); val nF = Free("n",natT);
    val hypP = jT (le bF (suc nF));
    val hle  = Thm.assume (ctermRM hypP);
    val goalC = mkDisj (oeq bF (suc nF)) (le bF nF);
    val Pabs = Abs("d", natT, oeq (suc nF) (add bF (Bound 0)));
    fun body d (hd:thm) =
      let
        val dz = dzos_R d;
        val caseZ =
          let val hz = Thm.assume (ctermRM (jT (oeq d ZeroC)))
              val c1 = add_cong_r_R (bF, d, ZeroC) hz
              val b0 = add0r_R bF
              val c2 = oeq_trans_vR OF [c1, b0]
              val Sn_b = oeq_trans_vR OF [hd, c2]
              val b_Sn = oeq_sym_vR OF [Sn_b]
          in Thm.implies_intr (ctermRM (jT (oeq d ZeroC)))
               (disjI1_R (oeq bF (suc nF), le bF nF) b_Sn) end;
        val caseS =
          let val hsP = jT (mkExSuc_R d)
              val hs  = Thm.assume (ctermRM hsP)
              val Pq = Abs("q", natT, oeq d (suc (Bound 0)))
              fun bodyS e (he:thm) =
                let
                  val c1 = add_cong_r_R (bF, d, suc e) he
                  val Sn_bSe = oeq_trans_vR OF [hd, c1]
                  val bSe = addSr_at_R (bF, e)
                  val Sn_Sbe = oeq_trans_vR OF [Sn_bSe, bSe]
                  val n_be = Suc_inj_R (nF, add bF e) Sn_Sbe
                  val le_bn = le_intro_R (bF, nF, e) n_be
                in disjI2_R (oeq bF (suc nF), le bF nF) le_bn end
              val res = exE_R (Pq, goalC) hs "eSS" bodyS
          in Thm.implies_intr (ctermRM (jT (mkExSuc_R d))) res end;
      in disjE_R (oeq d ZeroC, mkExSuc_R d, goalC) dz caseZ caseS end;
    val res = exE_R (Pabs, goalC) hle "dSS" body;
  in varify (Thm.implies_intr (ctermRM hypP) res) end;
val () = if length (Thm.hyps_of le_suc_split) = 0 then out "OK le_suc_split\n" else out "FAIL le_suc_split\n";
val le_suc_split_vR = le_suc_split;
fun le_suc_split_R (bt,nt) hle =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM
      [(("b",0), ctermRM bt),(("n",0), ctermRM nt)] le_suc_split_vR)) hle;

(* ============================================================================
   lmem_upto_bwd : Conj (lt 0 b) (le b n) ==> lmem b (uptoF n)   (induction on n)
   ============================================================================ *)
val lmem_upto_bwd =
  let
    val bF = Free("b",natT);
    val nVar = Free("n_iu", natT);
    val Pabs = Term.lambda nVar (mkImp (mkConj (lt ZeroC bF) (le bF nVar)) (lmem bF (uptoF nVar)));
    val base =
      let
        val hypA = jT (mkConj (lt ZeroC bF) (le bF ZeroC))
        val hA   = Thm.assume (ctermRM hypA)
        val hpos = conjunct1_R (lt ZeroC bF, le bF ZeroC) hA
        val hleb0= conjunct2_R (lt ZeroC bF, le bF ZeroC) hA
        val Pd = Abs("d", natT, oeq ZeroC (add bF (Bound 0)))
        fun bd d (hd:thm) =
          let
            val hbd = oeq_sym_vR OF [hd]
            val b0  = add_eq_zero_left_R (bF, d) hbd
            val zLt = Free("z_lt", natT)
            val Plt = Term.lambda zLt (lt ZeroC zLt)
            val lt00 = oeq_rw_R (Plt, bF, ZeroC) b0 hpos
            val Pe = Abs("e", natT, oeq ZeroC (add (suc ZeroC) (Bound 0)))
            fun be e (he:thm) =
              let val aS = addSuc_R (ZeroC, e)
                  val z_S = oeq_trans_vR OF [he, aS]
                  val S_z = oeq_sym_vR OF [z_S]
                  val fls = Suc_neq_Zero_R (add ZeroC e) S_z
              in Thm.implies_elim (oFalse_elim_R (lmem bF (uptoF ZeroC))) fls end
            val res = exE_R (Pe, lmem bF (uptoF ZeroC)) lt00 "e_b0" be
          in res end
        val resmem = exE_R (Pd, lmem bF (uptoF ZeroC)) hleb0 "d_b0" bd
      in impI_R (mkConj (lt ZeroC bF)(le bF ZeroC), lmem bF (uptoF ZeroC)) (Thm.implies_intr (ctermRM hypA) resmem) end;
    val step =
      let
        val xF = Free("x_iu", natT)
        val ihP = jT (mkImp (mkConj (lt ZeroC bF)(le bF xF)) (lmem bF (uptoF xF)))
        val hIH = Thm.assume (ctermRM ihP)
        val hypA = jT (mkConj (lt ZeroC bF)(le bF (suc xF)))
        val hA   = Thm.assume (ctermRM hypA)
        val hpos = conjunct1_R (lt ZeroC bF, le bF (suc xF)) hA
        val hle  = conjunct2_R (lt ZeroC bF, le bF (suc xF)) hA
        val dj = le_suc_split_R (bF, xF) hle
        val goalMem = lmem bF (uptoF (suc xF))
        val hupto = uptoSuc_R xF
        val hupto_s = leq_sym_R hupto
        val consL = lcons (suc xF) (uptoF xF)
        val caseEq =
          let val heq = Thm.assume (ctermRM (jT (oeq bF (suc xF))))
              val dmem = disjI1_R (oeq bF (suc xF), lmem bF (uptoF xF)) heq
              val memCons = Thm.implies_elim (lmemConsBwd_R (bF, suc xF, uptoF xF)) dmem
              val Pmem = Abs("z", natlistT, lmem bF (Bound 0))
              val res = leq_rw_R (Pmem, consL, uptoF (suc xF)) hupto_s memCons
          in Thm.implies_intr (ctermRM (jT (oeq bF (suc xF)))) res end
        val caseLe =
          let val hlex = Thm.assume (ctermRM (jT (le bF xF)))
              val conjx = conjI_R (lt ZeroC bF, le bF xF) hpos hlex
              val memUx = mp_R (mkConj (lt ZeroC bF)(le bF xF), lmem bF (uptoF xF)) hIH conjx
              val dmem = disjI2_R (oeq bF (suc xF), lmem bF (uptoF xF)) memUx
              val memCons = Thm.implies_elim (lmemConsBwd_R (bF, suc xF, uptoF xF)) dmem
              val Pmem = Abs("z", natlistT, lmem bF (Bound 0))
              val res = leq_rw_R (Pmem, consL, uptoF (suc xF)) hupto_s memCons
          in Thm.implies_intr (ctermRM (jT (le bF xF))) res end
        val memThm = disjE_R (oeq bF (suc xF), le bF xF, goalMem) dj caseEq caseLe
        val impThm = impI_R (mkConj (lt ZeroC bF)(le bF (suc xF)), goalMem)
                       (Thm.implies_intr (ctermRM hypA) memThm)
      in Thm.forall_intr (ctermRM xF) (Thm.implies_intr (ctermRM ihP) impThm) end;
    val kF = Free("k_iu", natT)
    val concl = nat_induct_R Pabs kF base step
  in varify concl end;
val () = if length (Thm.hyps_of lmem_upto_bwd) = 0 then out "OK lmem_upto_bwd\n" else out "FAIL lmem_upto_bwd\n";

(* ---- small order helpers on ctxtRM ---- *)
fun le_refl_R t = beta_norm (Drule.infer_instantiate ctxtRM [(("n",0), ctermRM t)] le_refl_vR);
fun lt_0_suc_R nt =
  let val a1 = addSuc_R (ZeroC, nt)
      val a0 = add0_R nt
      val sa0 = Suc_cong_vR OF [a0]
      val sum = oeq_trans_vR OF [a1, sa0]
      val sumS = oeq_sym_vR OF [sum]
  in le_intro_R (suc ZeroC, suc nt, nt) sumS end;
fun le_self_suc_R nt =
  let val aSr = addSr_at_R (nt, ZeroC)
      val a0r = add0r_R nt
      val sa0r = Suc_cong_vR OF [a0r]
      val sum = oeq_trans_vR OF [aSr, sa0r]
      val sumS = oeq_sym_vR OF [sum]
  in le_intro_R (nt, suc nt, suc ZeroC) sumS end;

(* ============================================================================
   lmem_upto_fwd : lmem b (uptoF n) ==> Conj (lt 0 b) (le b n)   (induction on n)
   ============================================================================ *)
val lmem_upto_fwd =
  let
    val bF = Free("b",natT);
    val nVar = Free("n_if", natT);
    val Pabs = Term.lambda nVar (mkImp (lmem bF (uptoF nVar)) (mkConj (lt ZeroC bF) (le bF nVar)));
    val base =
      let
        val goalC = mkConj (lt ZeroC bF) (le bF ZeroC)
        val hmemP = jT (lmem bF (uptoF ZeroC))
        val hmem  = Thm.assume (ctermRM hmemP)
        val hu0   = uptoZero_R
        val Pmem = Abs("z", natlistT, lmem bF (Bound 0))
        val memNil = leq_rw_R (Pmem, uptoF ZeroC, lnilC) hu0 hmem
        val fls = Thm.implies_elim (lmemNilElim_R bF) memNil
        val res = Thm.implies_elim (oFalse_elim_R goalC) fls
      in impI_R (lmem bF (uptoF ZeroC), goalC) (Thm.implies_intr (ctermRM hmemP) res) end;
    val step =
      let
        val xF = Free("x_if", natT)
        val ihP = jT (mkImp (lmem bF (uptoF xF)) (mkConj (lt ZeroC bF) (le bF xF)))
        val hIH = Thm.assume (ctermRM ihP)
        val goalC = mkConj (lt ZeroC bF) (le bF (suc xF))
        val hmemP = jT (lmem bF (uptoF (suc xF)))
        val hmem  = Thm.assume (ctermRM hmemP)
        val hupto = uptoSuc_R xF
        val consL = lcons (suc xF) (uptoF xF)
        val Pmem = Abs("z", natlistT, lmem bF (Bound 0))
        val memCons = leq_rw_R (Pmem, uptoF (suc xF), consL) hupto hmem
        val dj = Thm.implies_elim (lmemConsFwd_R (bF, suc xF, uptoF xF)) memCons
        val caseEq =
          let val heq = Thm.assume (ctermRM (jT (oeq bF (suc xF))))
              val lt0Sx = lt_0_suc_R xF
              val heq_s = oeq_sym_vR OF [heq]
              val Plt = Term.lambda (Free("z_lf",natT)) (lt ZeroC (Free("z_lf",natT)))
              val lt0b = oeq_rw_R (Plt, suc xF, bF) heq_s lt0Sx
              val leRefl = le_refl_R (suc xF)
              val Ple = Term.lambda (Free("z_le",natT)) (le (Free("z_le",natT)) (suc xF))
              val leb = oeq_rw_R (Ple, suc xF, bF) heq_s leRefl
              val cj = conjI_R (lt ZeroC bF, le bF (suc xF)) lt0b leb
          in Thm.implies_intr (ctermRM (jT (oeq bF (suc xF)))) cj end
        val caseMem =
          let val hmemx = Thm.assume (ctermRM (jT (lmem bF (uptoF xF))))
              val cjx = mp_R (lmem bF (uptoF xF), mkConj (lt ZeroC bF)(le bF xF)) hIH hmemx
              val lt0b = conjunct1_R (lt ZeroC bF, le bF xF) cjx
              val lebx = conjunct2_R (lt ZeroC bF, le bF xF) cjx
              val lex_Sx = le_self_suc_R xF
              val leb_Sx = le_trans_R (bF, xF, suc xF) lebx lex_Sx
              val cj = conjI_R (lt ZeroC bF, le bF (suc xF)) lt0b leb_Sx
          in Thm.implies_intr (ctermRM (jT (lmem bF (uptoF xF)))) cj end
        val cjThm = disjE_R (oeq bF (suc xF), lmem bF (uptoF xF), goalC) dj caseEq caseMem
        val impThm = impI_R (lmem bF (uptoF (suc xF)), goalC)
                       (Thm.implies_intr (ctermRM hmemP) cjThm)
      in Thm.forall_intr (ctermRM xF) (Thm.implies_intr (ctermRM ihP) impThm) end;
    val kF = Free("k_if", natT)
    val concl = nat_induct_R Pabs kF base step
  in varify concl end;
val () = if length (Thm.hyps_of lmem_upto_fwd) = 0 then out "OK lmem_upto_fwd\n" else out "FAIL lmem_upto_fwd\n";
fun lmem_upto_fwd_R (bt,nt) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtRM
          [(("b",0), ctermRM bt),(("k_if",0), ctermRM nt)] lmem_upto_fwd)
  in mp_R (lmem bt (uptoF nt), mkConj (lt ZeroC bt)(le bt nt)) inst hmem end;
val () = out "RM_FWD_DONE\n";

(* ============================================================================
   lnodup_upto : lnodup (uptoF n)   (induction on n; Suc n not already in uptoF n)
   ============================================================================ *)
val lt_irrefl_vR = varify lt_irrefl;
fun lt_irrefl_R nt hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtRM [(("n",0), ctermRM nt)] lt_irrefl_vR)) hlt;
fun lnodup_transfer_R (aT,bT) hleq hnd =
  let val Pabs = Abs("z", natlistT, lnodup (Bound 0))
  in leq_rw_R (Pabs, aT, bT) hleq hnd end;
val lnodup_upto =
  let
    val nVar = Free("n_nd", natT);
    val Pabs = Term.lambda nVar (lnodup (uptoF nVar));
    val base =
      let
        val hu0 = uptoZero_R
        val hu0s = leq_sym_R hu0
        val ndNil = lnodupNil_R
      in lnodup_transfer_R (lnilC, uptoF ZeroC) hu0s ndNil end;
    val step =
      let
        val xF = Free("x_nd", natT)
        val ihP = jT (lnodup (uptoF xF))
        val hIH = Thm.assume (ctermRM ihP)
        val notmem =
          let val hmem = Thm.assume (ctermRM (jT (lmem (suc xF) (uptoF xF))))
              val cj = lmem_upto_fwd_R (suc xF, xF) hmem
              val leSxx = conjunct2_R (lt ZeroC (suc xF), le (suc xF) xF) cj
              val fls = lt_irrefl_R xF leSxx
              val metaImp = Thm.implies_intr (ctermRM (jT (lmem (suc xF) (uptoF xF)))) fls
          in impI_R (lmem (suc xF) (uptoF xF), oFalseC) metaImp end;
        val conjND = conjI_R (neg (lmem (suc xF) (uptoF xF)), lnodup (uptoF xF)) notmem hIH
        val ndCons = Thm.implies_elim (lnodupCons_bwd_R (suc xF, uptoF xF)) conjND
        val hupto = uptoSuc_R xF
        val hupto_s = leq_sym_R hupto
        val res = lnodup_transfer_R (lcons (suc xF) (uptoF xF), uptoF (suc xF)) hupto_s ndCons
      in Thm.forall_intr (ctermRM xF) (Thm.implies_intr (ctermRM ihP) res) end;
    val kF = Free("k_nd", natT)
    val concl = nat_induct_R Pabs kF base step
  in varify concl end;
val () = if length (Thm.hyps_of lnodup_upto) = 0 then out "OK lnodup_upto\n" else out "FAIL lnodup_upto\n";
val () = out "RM_NODUP_DONE\n";

(* ============================================================================
   PHASE 1 FINAL VALIDATION : statements aconv intent, 0-hyp, soundness probes.
   ============================================================================ *)
val () = out "RM_VALIDATE_BEGIN\n";
val aV = Var(("a",0),natT); val bV = Var(("b",0),natT); val pV = Var(("p",0),natT);
val cong_imp_rmodeq_intended =
  Logic.mk_implies (jT (lt ZeroC pV),
    Logic.mk_implies (jT (cong pV aV bV), jT (oeq (rmod aV pV) (rmod bV pV))));
val r_dir1 = (length (Thm.hyps_of cong_imp_rmodeq) = 0)
             andalso ((Thm.prop_of cong_imp_rmodeq) aconv cong_imp_rmodeq_intended);
val () = if r_dir1 then out "OK cong_imp_rmodeq aconv intended\n" else out "FAIL cong_imp_rmodeq aconv\n";
val rmodeq_imp_cong_intended =
  Logic.mk_implies (jT (lt ZeroC pV),
    Logic.mk_implies (jT (oeq (rmod aV pV) (rmod bV pV)), jT (cong pV aV bV)));
val r_dir2 = (length (Thm.hyps_of rmodeq_imp_cong) = 0)
             andalso ((Thm.prop_of rmodeq_imp_cong) aconv rmodeq_imp_cong_intended);
val () = if r_dir2 then out "OK rmodeq_imp_cong aconv intended\n" else out "FAIL rmodeq_imp_cong aconv\n";
val probe_dir1_needs_pos =
  let val bogus = Logic.mk_implies (jT (cong pV aV bV), jT (oeq (rmod aV pV)(rmod bV pV)))
  in not ((Thm.prop_of cong_imp_rmodeq) aconv bogus) end;
val () = if probe_dir1_needs_pos then out "PROBE_OK cong_imp_rmodeq keeps 0<p premise\n"
         else out "PROBE_FAIL cong_imp_rmodeq dropped 0<p!\n";
val probe_dir2_needs_pos =
  let val bogus = Logic.mk_implies (jT (oeq (rmod aV pV)(rmod bV pV)), jT (cong pV aV bV))
  in not ((Thm.prop_of rmodeq_imp_cong) aconv bogus) end;
val () = if probe_dir2_needs_pos then out "PROBE_OK rmodeq_imp_cong keeps 0<p premise\n"
         else out "PROBE_FAIL rmodeq_imp_cong dropped 0<p!\n";
val rmod_lt_check =
  let val h = rmod_lt_R (Free("aa",natT), suc ZeroC) (lt_suc_R ZeroC)
  in (length (Thm.hyps_of h) = 0) end;
val () = if rmod_lt_check then out "PROBE_OK rmod a p < p usable (rmod_lt)\n" else out "PROBE_FAIL rmod_lt\n";
val div_mod_eq_check =
  let val h = div_mod_eq_R (Free("aa",natT), suc ZeroC) (lt_suc_R ZeroC)
  in (length (Thm.hyps_of h) = 0) end;
val () = if div_mod_eq_check then out "PROBE_OK div_mod_eq usable\n" else out "PROBE_FAIL div_mod_eq\n";
val r_upto_nodup = (length (Thm.hyps_of lnodup_upto) = 0);
val r_upto_fwd   = (length (Thm.hyps_of lmem_upto_fwd) = 0);
val r_upto_bwd   = (length (Thm.hyps_of lmem_upto_bwd) = 0);
val () =
  if r_dir1 andalso r_dir2 andalso probe_dir1_needs_pos andalso probe_dir2_needs_pos
     andalso rmod_lt_check andalso div_mod_eq_check
     andalso r_upto_nodup andalso r_upto_fwd andalso r_upto_bwd
  then out "RANGE_MOD_OK\n"
  else out "RANGE_MOD_FAILED\n";

(* ============================================================================
   PHASE 2 (seat iv0): the MODULAR INVERSE FUNCTION as a literal involution.
   Define fsearch (list-recursive, conditional on rmod decision) + finv, prove
   finv_inv / finv_mem / finv_invol / finv_neq.  Built on the Phase-1 final
   context (thyRM / ctxtRM / ctermRM).
   ============================================================================ *)
val () = out "WI_PHASE2_BEGIN\n";

(* ---- new consts: sub (truncated subtraction), fsearch, finv ---- *)
val thyWc = Sign.add_consts
  [(Binding.name "sub",     natT --> natT --> natT, NoSyn),
   (Binding.name "fsearch", natT --> natT --> natlistT --> natT, NoSyn),
   (Binding.name "finv",    natT --> natT --> natT, NoSyn)] thyRM;

fun cnstW nm T = Const (Sign.full_name thyWc (Binding.name nm), T);
val subC     = cnstW "sub" (natT --> natT --> natT);  fun sub a b = subC $ a $ b;
val fsearchC = cnstW "fsearch" (natT --> natT --> natlistT --> natT);
fun fsearch p x l = fsearchC $ p $ x $ l;
val finvC    = cnstW "finv" (natT --> natT --> natT); fun finv p x = finvC $ p $ x;

(* free vars for axiom statements *)
val pW = Free("p", natT); val xW0 = Free("x", natT); val bW = Free("b", natT);
val bsW = Free("bs", natlistT); val nW = Free("n", natT); val mW0 = Free("m", natT);

(* the decidable search condition : oeq (rmod (mult x b) p) (Suc Zero) *)
fun searchCond pt xt bt = oeq (rmod (mult xt bt) pt) (suc ZeroC);

(* ---- sub : recursion axioms (truncated subtraction) ----
     sub_0   : oeq (sub n Zero) n
     sub_SS  : oeq (sub (Suc n) (Suc m)) (sub n m)        *)
val ((_,sub_0_ax), thyW1) = Thm.add_axiom_global (Binding.name "sub_0",
      jT (oeq (sub nW ZeroC) nW)) thyWc;
val ((_,sub_SS_ax), thyW2) = Thm.add_axiom_global (Binding.name "sub_SS",
      jT (oeq (sub (suc nW) (suc mW0)) (sub nW mW0))) thyW1;

(* ---- fsearch : CONDITIONAL list-recursion axioms ----
     fsearch_nil      : oeq (fsearch p x lnil) Zero
     fsearch_cons_eq  : jT (searchCond p x b)        ==> oeq (fsearch p x (lcons b bs)) b
     fsearch_cons_neq : jT (neg (searchCond p x b))  ==> oeq (fsearch p x (lcons b bs)) (fsearch p x bs)  *)
val ((_,fsearch_nil_ax), thyW3) = Thm.add_axiom_global (Binding.name "fsearch_nil",
      jT (oeq (fsearch pW xW0 lnilC) ZeroC)) thyW2;
val ((_,fsearch_cons_eq_ax), thyW4) = Thm.add_axiom_global (Binding.name "fsearch_cons_eq",
      Logic.mk_implies (jT (searchCond pW xW0 bW),
        jT (oeq (fsearch pW xW0 (lcons bW bsW)) bW))) thyW3;
val ((_,fsearch_cons_neq_ax), thyW5) = Thm.add_axiom_global (Binding.name "fsearch_cons_neq",
      Logic.mk_implies (jT (neg (searchCond pW xW0 bW)),
        jT (oeq (fsearch pW xW0 (lcons bW bsW)) (fsearch pW xW0 bsW)))) thyW4;

(* ---- finv : defining axiom  finv p x = fsearch p x (upto (sub p (Suc Zero))) ---- *)
val ((_,finv_def_ax), thyW) = Thm.add_axiom_global (Binding.name "finv_def",
      jT (oeq (finv pW xW0) (fsearch pW xW0 (uptoF (sub pW (suc ZeroC)))))) thyW5;

val ctxtW  = Proof_Context.init_global thyW;
val ctermW = Thm.cterm_of ctxtW;
val () = out "WI_CONTEXT_READY\n";

(* ============================================================================
   re-varify reused base axioms/lemmas + Phase-1 lemmas onto ctxtW
   ============================================================================ *)
(* FOL / foundation *)
val oeq_refl_vW    = varify oeq_refl;
val oeq_subst_vW   = varify oeq_subst;
val oeq_sym_vW     = varify oeq_sym;
val oeq_trans_vW   = varify oeq_trans;
val Suc_cong_vW    = varify Suc_cong;
val exI_vW         = varify exI_ax;
val exE_vW         = varify exE_ax;
val oFalse_elim_vW = varify oFalse_elim_ax;
val Suc_neq_Zero_vW= varify Suc_neq_Zero_ax;
val Suc_inj_vW     = varify Suc_inj_ax;
val conjI_vW       = varify conjI_ax;
val conjunct1_vW   = varify conjunct1_ax;
val conjunct2_vW   = varify conjunct2_ax;
val disjI1_vW      = varify disjI1_ax;
val disjI2_vW      = varify disjI2_ax;
val disjE_vW       = varify disjE_ax;
val mp_vW          = varify mp_ax;
val impI_vW        = varify impI_ax;
val ex_middle_vW   = varify ex_middle_ax;
val allI_vW        = varify allI_ax;
val allE_vW        = varify allE_ax;
(* arithmetic *)
val add_0_vW       = varify add_0;
val add_Suc_vW     = varify add_Suc;
val add_0_right_vW = varify add_0_right;
val add_Suc_right_vW = varify add_Suc_right;
val add_comm_vW    = varify add_comm;
val add_assoc_vW   = varify add_assoc;
val add_left_cancel_vW = varify add_left_cancel;
val mult_0_vW      = varify mult_0;
val mult_Suc_vW    = varify mult_Suc;
val mult_0_right_vW= varify mult_0_right;
val mult_Suc_right_vW = varify mult_Suc_right;
val mult_comm_vW   = varify mult_comm;
val mult_assoc_vW  = varify mult_assoc;
val mult_1_left_vW = varify mult_1_left;
val mult_1_right_vW= varify mult_1_right;
val left_distrib_vW= varify left_distrib;
val right_distrib_vW = varify right_distrib;
(* order *)
val le_refl_vW     = varify le_refl;
val le_trans_vW    = varify le_trans;
val le_total_vW    = varify le_total;
val le_antisym_vW  = varify le_antisym;
val le_add_vW      = varify le_add;
val zero_le_vW     = varify zero_le;
val lt_suc_vW      = varify lt_suc;
val lt_trans_vW    = varify lt_trans;
val lt_irrefl_vW   = varify lt_irrefl;
val nlt_le_vW      = varify nlt_le;
val disj_zero_or_suc_vW = varify disj_zero_or_suc;
val add_eq_zero_left_vW = varify add_eq_zero_left;
val nat_induct_vW  = varify nat_induct;
val div_mod_unique_vW = varify div_mod_unique;
(* dvd / prime / cong base theorems *)
val dvd_le_vW      = varify dvd_le;
val mod_inverse_vW = varify mod_inverse;
val inverse_unique_vW = varify inverse_unique;
val lagrange_roots_vW = varify lagrange_roots;
val cong_refl_vW   = varify cong_refl;
val cong_sym_vW    = varify cong_sym;
val cong_trans_vW  = varify cong_trans;
val cong_mult_vW   = varify cong_mult;
(* Phase-1 lemmas *)
val cong_imp_rmodeq_vW = varify cong_imp_rmodeq;
val rmodeq_imp_cong_vW = varify rmodeq_imp_cong;
val lmem_upto_fwd_vW = varify lmem_upto_fwd;
val lmem_upto_bwd_vW = varify lmem_upto_bwd;
val lnodup_upto_vW   = varify lnodup_upto;
val div_mod_eq_vW  = varify div_mod_eq_ax;
val rmod_lt_vW     = varify rmod_lt_ax;
val upto_zero_vW   = varify upto_zero_ax;
val upto_suc_vW    = varify upto_suc_ax;
(* list machinery *)
val leq_refl_vW    = varify leq_refl_ax;
val leq_subst_vW   = varify leq_subst_ax;
val list_induct_vW = varify list_induct_ax;
val lmem_nil_elim_vW = varify lmem_nil_elim_ax;
val lmem_cons_fwd_vW = varify lmem_cons_fwd_ax;
val lmem_cons_bwd_vW = varify lmem_cons_bwd_ax;
val lnodup_nil_vW  = varify lnodup_nil_ax;
val lnodup_cons_fwd_vW = varify lnodup_cons_fwd_ax;
val lnodup_cons_bwd_vW = varify lnodup_cons_bwd_ax;
(* new W axioms *)
val sub_0_vW       = varify sub_0_ax;
val sub_SS_vW      = varify sub_SS_ax;
val fsearch_nil_vW = varify fsearch_nil_ax;
val fsearch_cons_eq_vW = varify fsearch_cons_eq_ax;
val fsearch_cons_neq_vW = varify fsearch_cons_neq_ax;
val finv_def_vW    = varify finv_def_ax;
val () = out "WI_VARIFY_READY\n";

(* ============================================================================
   combinators on ctxtW (suffix _W)
   ============================================================================ *)
fun oeqRefl_W t = beta_norm (Drule.infer_instantiate ctxtW [(("a",0), ctermW t)] oeq_refl_vW);
fun add0_W t    = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] add_0_vW);
fun add0r_W t   = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] add_0_right_vW);
fun addSuc_W (mt,nt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt)] add_Suc_vW);
fun addSr_W (mt,nt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt)] add_Suc_right_vW);
fun addcomm_W (mt,nt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt)] add_comm_vW);
fun addassoc_W (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt),(("k",0), ctermW kt)] add_assoc_vW);
fun mult0r_W t  = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] mult_0_right_vW);
fun mult1r_W t  = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] mult_1_right_vW);
fun mult1l_W t  = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] mult_1_left_vW);
fun multcomm_W (mt,nt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt)] mult_comm_vW);
fun multassoc_W (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt),(("k",0), ctermW kt)] mult_assoc_vW);
fun multSuc_W (mt,nt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt)] mult_Suc_vW);

fun oeq_rw_W (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("P",0), ctermW Pabs),(("a",0), ctermW aT),(("b",0), ctermW bT)] oeq_subst_vW)
  in inst OF [hab, hPa] end;
fun add_cong_l_W (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (add pT kT) (add (Bound 0) kT))
  in oeq_rw_W (Pabs, pT, qT) hpq (oeqRefl_W (add pT kT)) end;
fun add_cong_r_W (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (add hT pT) (add hT (Bound 0)))
  in oeq_rw_W (Pabs, pT, qT) hpq (oeqRefl_W (add hT pT)) end;
fun mult_cong_l_W (pT, qT, kT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult pT kT) (mult (Bound 0) kT))
  in oeq_rw_W (Pabs, pT, qT) hpq (oeqRefl_W (mult pT kT)) end;
fun mult_cong_r_W (hT, pT, qT) hpq =
  let val Pabs = Abs("z", natT, oeq (mult hT pT) (mult hT (Bound 0)))
  in oeq_rw_W (Pabs, pT, qT) hpq (oeqRefl_W (mult hT pT)) end;

fun mp_W (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("A",0), ctermW At),(("B",0), ctermW Bt)] mp_vW)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_W (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("A",0), ctermW At),(("B",0), ctermW Bt)] impI_vW)
  in Thm.implies_elim inst hImpThm end;
fun conjI_W (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("A",0), ctermW At),(("B",0), ctermW Bt)] conjI_vW)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_W (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("A",0), ctermW At),(("B",0), ctermW Bt)] conjunct1_vW)) h;
fun conjunct2_W (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("A",0), ctermW At),(("B",0), ctermW Bt)] conjunct2_vW)) h;
fun oFalse_elim_W rT = beta_norm (Drule.infer_instantiate ctxtW [(("R",0), ctermW rT)] oFalse_elim_vW);
fun disjE_W (At,Bt,Ct) dThm cA cB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("A",0), ctermW At),(("B",0), ctermW Bt),(("C",0), ctermW Ct)] disjE_vW)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) cA) cB end;
fun disjI1_W (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("A",0), ctermW At),(("B",0), ctermW Bt)] disjI1_vW)) h;
fun disjI2_W (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("A",0), ctermW At),(("B",0), ctermW Bt)] disjI2_vW)) h;
fun em_W t = beta_norm (Drule.infer_instantiate ctxtW [(("A",0), ctermW t)] ex_middle_vW);
fun Suc_neq_Zero_W nt heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW nt)] Suc_neq_Zero_vW)) heq;
fun Suc_inj_W (at,bt) heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("a",0), ctermW at),(("b",0), ctermW bt)] Suc_inj_vW)) heq;

fun exI_W Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("P",0), ctermW Pabs),(("a",0), ctermW at)] exI_vW)
  in Thm.implies_elim inst hbody end;
fun exE_W (Pabs, goalC) exThm wName bodyFn =
  let val wF = Free(wName, natT)
      val hypTerm = jT (Term.betapply (Pabs, wF))
      val hypThm  = Thm.assume (ctermW hypTerm)
      val body    = bodyFn wF hypThm
      val minor   = Thm.forall_intr (ctermW wF) (Thm.implies_intr (ctermW hypTerm) body)
      val exE_inst= beta_norm (Drule.infer_instantiate ctxtW
                      [(("P",0), ctermW Pabs),(("Q",0), ctermW goalC)] exE_vW)
  in Thm.implies_elim (Thm.implies_elim exE_inst exThm) minor end;

fun le_intro_W (mT, nT, w) hyp =
  let val Pabs = Abs("p", natT, oeq nT (add mT (Bound 0)))
      val inst = beta_norm (Drule.infer_instantiate ctxtW
            [(("P",0), ctermW Pabs),(("a",0), ctermW w)] exI_vW)
  in inst OF [hyp] end;
fun le_total_W (mt,nt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt)] le_total_vW);
fun le_trans_W (at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("m",0), ctermW at),(("n",0), ctermW bt),(("k",0), ctermW ct)] le_trans_vW)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun lt_trans_W (at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("a",0), ctermW at),(("b",0), ctermW bt),(("c",0), ctermW ct)] lt_trans_vW)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun lt_irrefl_W nt hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW nt)] lt_irrefl_vW)) hlt;
fun le_refl_W t = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] le_refl_vW);
fun le_antisym_W (mt,nt) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("m",0), ctermW mt),(("n",0), ctermW nt)] le_antisym_vW)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun le_add_W (mt,pt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("p",0), ctermW pt)] le_add_vW);
fun lt_suc_W nt = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW nt)] lt_suc_vW);
fun nlt_le_W (dt,ct) hneg =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("d",0), ctermW dt),(("c",0), ctermW ct)] nlt_le_vW)) hneg;
fun dzos_W t = beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW t)] disj_zero_or_suc_vW);
fun mkExSuc_W t = mkEx (Abs ("q", natT, oeq t (suc (Bound 0))));

fun div_mod_eq_W (at,pt) hpos =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("a",0), ctermW at),(("p",0), ctermW pt)] div_mod_eq_vW)) hpos;
fun rmod_lt_W (at,pt) hpos =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("a",0), ctermW at),(("p",0), ctermW pt)] rmod_lt_vW)) hpos;
fun div_mod_unique_W (b,q1,r1,q2,r2) heq hlt1 hlt2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("b",0), ctermW b),(("q1",0), ctermW q1),(("r1",0), ctermW r1),
         (("q2",0), ctermW q2),(("r2",0), ctermW r2)] div_mod_unique_vW)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst heq) hlt1) hlt2 end;

(* upto recursion on ctxtW *)
fun uptoSuc_W nt = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW nt)] upto_suc_vW);
val uptoZero_W = upto_zero_vW;
fun leq_rw_W (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("P",0), ctermW Pabs),(("a",0), ctermW aT),(("b",0), ctermW bT)] leq_subst_vW)
  in inst OF [hab, hPa] end;
fun lmemConsFwd_W (x,y,t) = beta_norm (Drule.infer_instantiate ctxtW
      [(("x",0), ctermW x),(("y",0), ctermW y),(("t",0), ctermW t)] lmem_cons_fwd_vW);
fun lmemConsBwd_W (x,y,t) = beta_norm (Drule.infer_instantiate ctxtW
      [(("x",0), ctermW x),(("y",0), ctermW y),(("t",0), ctermW t)] lmem_cons_bwd_vW);
fun lmemNilElim_W x = beta_norm (Drule.infer_instantiate ctxtW [(("x",0), ctermW x)] lmem_nil_elim_vW);

(* sub / fsearch / finv recursion on ctxtW *)
fun sub0_W t = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW t)] sub_0_vW);
fun subSS_W (nt,mt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("n",0), ctermW nt),(("m",0), ctermW mt)] sub_SS_vW);
val fsearchNil_W = fsearch_nil_vW;
fun fsearchNil_at (pt,xt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt),(("x",0), ctermW xt)] fsearch_nil_vW);
fun fsearchEq_W (pt,xt,bt,bst) hcond =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt),(("x",0), ctermW xt),(("b",0), ctermW bt),(("bs",0), ctermW bst)]
      fsearch_cons_eq_vW)) hcond;
fun fsearchNeq_W (pt,xt,bt,bst) hncond =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt),(("x",0), ctermW xt),(("b",0), ctermW bt),(("bs",0), ctermW bst)]
      fsearch_cons_neq_vW)) hncond;
fun finvDef_W (pt,xt) = beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt),(("x",0), ctermW xt)] finv_def_vW);

(* cong combinators on ctxtW *)
fun cong_refl_W (mt,at) = beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("a",0), ctermW at)] cong_refl_vW);
fun cong_sym_W (mt,at,bt) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("a",0), ctermW at),(("b",0), ctermW bt)] cong_sym_vW)) h;
fun cong_trans_W (mt,at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("m",0), ctermW mt),(("a",0), ctermW at),(("b",0), ctermW bt),(("c",0), ctermW ct)] cong_trans_vW)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun cong_mult_W (mt,at,a2t,bt,b2t) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("m",0), ctermW mt),(("a",0), ctermW at),(("a2",0), ctermW a2t),
         (("b",0), ctermW bt),(("b2",0), ctermW b2t)] cong_mult_vW)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
(* cong_of_eq on ctxtW : from heq : oeq X Y build jT (cong p X Y) (capture-safe) *)
fun cong_of_eq_W (pT, X, Y) heq =
  let val zF = Free("z_coe", natT)
      val Pabs = Term.lambda zF (cong pT X zF)
      val inst = beta_norm (Drule.infer_instantiate ctxtW
            [(("P",0), ctermW Pabs),(("a",0), ctermW X),(("b",0), ctermW Y)] oeq_subst_vW)
      val crefl = cong_refl_W (pT, X)
  in inst OF [heq, crefl] end;

(* cong_imp_rmodeq / rmodeq_imp_cong on ctxtW *)
fun cong_imp_rmodeq_W (pt,at,bt) hpos hcong =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("a",0), ctermW at),(("b",0), ctermW bt)] cong_imp_rmodeq_vW)
  in Thm.implies_elim (Thm.implies_elim inst hpos) hcong end;
fun rmodeq_imp_cong_W (pt,at,bt) hpos heq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("a",0), ctermW at),(("b",0), ctermW bt)] rmodeq_imp_cong_vW)
  in Thm.implies_elim (Thm.implies_elim inst hpos) heq end;

(* lmem_upto on ctxtW *)
fun lmem_upto_fwd_W (bt,nt) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
          [(("b",0), ctermW bt),(("k_if",0), ctermW nt)] lmem_upto_fwd_vW)
  in mp_W (lmem bt (uptoF nt), mkConj (lt ZeroC bt)(le bt nt)) inst hmem end;
fun lmem_upto_bwd_W (bt,nt) hconj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
          [(("b",0), ctermW bt),(("k_iu",0), ctermW nt)] lmem_upto_bwd_vW)
  in mp_W (mkConj (lt ZeroC bt)(le bt nt), lmem bt (uptoF nt)) inst hconj end;

(* prime2 destructors on ctxtW *)
fun prime2_gt1_W pt hprime = conjunct1_W (lt (suc ZeroC) pt, mkForall (ppAbs pt)) hprime;
fun prime2_div_W pt hprime = conjunct2_W (lt (suc ZeroC) pt, mkForall (ppAbs pt)) hprime;
fun allE_W Pabs at hF = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("P",0), ctermW Pabs),(("a",0), ctermW at)] allE_vW)) hF;

(* dvd helpers on ctxtW *)
fun dvd_intro_W (aT, bT, w) hyp =
  let val Pabs = Abs("k", natT, oeq bT (mult aT (Bound 0)))
  in exI_W Pabs w hyp end;
fun dvd_le_W (dt,nt) hdvd hnz =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("d",0), ctermW dt),(("n",0), ctermW nt)] dvd_le_vW)
  in Thm.implies_elim (Thm.implies_elim inst hdvd) hnz end;

(* mod_inverse / inverse_unique / lagrange_roots on ctxtW.
   mod_inverse goal binder is `b_mi` ; build the same lambda. *)
fun mi_innerAbs_W (pt, at) =
  let val bF = Free("b_mi", natT) in Term.lambda bF (cong pt (mult at bF) (suc ZeroC)) end;
fun mod_inverse_W (pt,at) hPrime hNdvd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("a",0), ctermW at)] mod_inverse_vW)
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hNdvd end;
fun inverse_unique_W (pt,at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("a",0), ctermW at),(("b",0), ctermW bt),(("c",0), ctermW ct)] inverse_unique_vW)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun lagrange_roots_W (pt,at) hPrime hsq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("a",0), ctermW at)] lagrange_roots_vW)
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hsq end;

val () = out "WI_COMBINATORS_READY\n";

(* ============================================================================
   SMOKE TEST : sub p 1 = p-1 when p = Suc q.  sub_suc_one : oeq (sub (Suc q) (Suc Zero)) q
   ============================================================================ *)
val sub_suc_one =
  let val qF = Free("q", natT)
      val e1 = subSS_W (qF, ZeroC)          (* oeq (sub (Suc q)(Suc 0)) (sub q 0) *)
      val e2 = sub0_W qF                     (* oeq (sub q 0) q *)
  in varify (oeq_trans_vW OF [e1, e2]) end;
val () = if length (Thm.hyps_of sub_suc_one) = 0 then out "OK sub_suc_one\n" else out "FAIL sub_suc_one\n";

val () = out "WI_SMOKE_DONE\n";

(* ============================================================================
   list_induct combinator on ctxtW.  Predicate Pabs : natlist => o, target list LT.
   baseThm : jT (Pabs $ lnil) ; stepThm : !!x.!!l. jT (Pabs $ l) ==> jT (Pabs $ (lcons x l)).
   ============================================================================ *)
fun list_induct_W (Pabs, LT) baseThm stepThm =
  let val ind = beta_norm (Drule.infer_instantiate ctxtW
        [(("P",0), ctermW Pabs),(("a",0), ctermW LT)] list_induct_vW)
  in Thm.implies_elim (Thm.implies_elim ind baseThm) stepThm end;

(* ============================================================================
   rmod_one : 1 < p ==> oeq (rmod (Suc Zero) p) (Suc Zero)
   ============================================================================ *)
val rmod_one =
  let
    val pF = Free("p", natT)
    val hp1P = jT (lt (suc ZeroC) pF)
    val hp1  = Thm.assume (ctermW hp1P)
    val one = suc ZeroC
    val le_1_2 =
      let val aSr = addSr_W (one, ZeroC)
          val a0r = add0r_W one
          val s   = Suc_cong_vW OF [a0r]
          val sum = oeq_trans_vW OF [aSr, s]
          val sumS= oeq_sym_vW OF [sum]
      in le_intro_W (one, suc one, suc ZeroC) sumS end
    val hp0 = le_trans_W (one, suc one, pF) le_1_2 hp1
    val hEq = div_mod_eq_W (one, pF) hp0
    val q1 = rdiv one pF ; val r1 = rmod one pF
    val hr1lt = rmod_lt_W (one, pF) hp0
    val p0 = mult0r_W pF
    val pol = add_cong_l_W (mult pF ZeroC, ZeroC, one) p0
    val z1 = add0_W one
    val eq2 = oeq_trans_vW OF [pol, z1]
    val eqWit = oeq_sym_vW OF [eq2]
    val combined = oeq_trans_vW OF [oeq_sym_vW OF [hEq], eqWit]
    val uniq = div_mod_unique_W (pF, q1, r1, ZeroC, one) combined hr1lt hp1
    val r1_one = conjunct2_W (oeq q1 ZeroC, oeq r1 one) uniq
  in varify (Thm.implies_intr (ctermW hp1P) r1_one) end;
val () = if length (Thm.hyps_of rmod_one) = 0 then out "OK rmod_one\n" else out "FAIL rmod_one\n";
fun rmod_one_W pt hp1 =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pt)] rmod_one)) hp1;

fun lt1_imp_lt0_W pt hp1 =
  let val one = suc ZeroC
      val aSr = addSr_W (one, ZeroC)
      val a0r = add0r_W one
      val s   = Suc_cong_vW OF [a0r]
      val sum = oeq_trans_vW OF [aSr, s]
      val sumS= oeq_sym_vW OF [sum]
      val le_1_2 = le_intro_W (one, suc one, suc ZeroC) sumS
  in le_trans_W (one, suc one, pt) le_1_2 hp1 end;

val () = out "WI_RMOD_ONE_DONE\n";

(* ============================================================================
   searchCond <-> cong  bridges (under 1 < p).
   ============================================================================ *)
val scond_imp_cong =
  let
    val pF = Free("p", natT); val xF = Free("x", natT); val bF = Free("b", natT)
    val one = suc ZeroC
    val hp1P = jT (lt one pF) ; val hp1 = Thm.assume (ctermW hp1P)
    val hcP  = jT (searchCond pF xF bF) ; val hc = Thm.assume (ctermW hcP)
    val hp0  = lt1_imp_lt0_W pF hp1
    val r1 = rmod_one_W pF hp1
    val r1s = oeq_sym_vW OF [r1]
    val eqr = oeq_trans_vW OF [hc, r1s]
    val congXB = rmodeq_imp_cong_W (pF, mult xF bF, one) hp0 eqr
    val d2 = Thm.implies_intr (ctermW hcP) congXB
    val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of scond_imp_cong) = 0 then out "OK scond_imp_cong\n" else out "FAIL scond_imp_cong\n";
fun scond_imp_cong_W (pt,xt,bt) hp1 hc =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("x",0), ctermW xt),(("b",0), ctermW bt)] scond_imp_cong)
  in Thm.implies_elim (Thm.implies_elim inst hp1) hc end;

val cong_imp_scond =
  let
    val pF = Free("p", natT); val xF = Free("x", natT); val bF = Free("b", natT)
    val one = suc ZeroC
    val hp1P = jT (lt one pF) ; val hp1 = Thm.assume (ctermW hp1P)
    val hcgP = jT (cong pF (mult xF bF) one) ; val hcg = Thm.assume (ctermW hcgP)
    val hp0  = lt1_imp_lt0_W pF hp1
    val eqr  = cong_imp_rmodeq_W (pF, mult xF bF, one) hp0 hcg
    val r1   = rmod_one_W pF hp1
    val sc   = oeq_trans_vW OF [eqr, r1]
    val d2 = Thm.implies_intr (ctermW hcgP) sc
    val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of cong_imp_scond) = 0 then out "OK cong_imp_scond\n" else out "FAIL cong_imp_scond\n";
fun cong_imp_scond_W (pt,xt,bt) hp1 hcg =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("x",0), ctermW xt),(("b",0), ctermW bt)] cong_imp_scond)
  in Thm.implies_elim (Thm.implies_elim inst hp1) hcg end;

val () = out "WI_SCOND_BRIDGE_DONE\n";

(* ============================================================================
   fsearch_found : (Ex b. Conj (lmem b L)(searchCond p x b))
                   ==> Conj (searchCond p x (fsearch p x L)) (lmem (fsearch p x L) L)
   by list induction on L (p, x fixed Frees).  KEY: build the induction predicate
   over a FRESH Free list var (Term.lambda does NOT shift loose Bounds).
   ============================================================================ *)
val fsearch_found =
  let
    val pF = Free("p", natT); val xF = Free("x", natT)
    fun existsCond zt = mkEx (Term.lambda (Free("b_fe", natT))
                          (mkConj (lmem (Free("b_fe", natT)) zt) (searchCond pF xF (Free("b_fe", natT)))))
    fun goodConc zt = mkConj (searchCond pF xF (fsearch pF xF zt)) (lmem (fsearch pF xF zt) zt)
    fun concBody zt = mkImp (existsCond zt) (goodConc zt)
    val zPF = Free("z_lst", natlistT)
    val Pabs = Term.lambda zPF (concBody zPF)
    val LF = Free("L", natlistT)
    val base =
      let
        val hexP = jT (existsCond lnilC)
        val hex  = Thm.assume (ctermW hexP)
        val goalC = goodConc lnilC
        val PexAbs = Term.lambda (Free("b_fe", natT))
                       (mkConj (lmem (Free("b_fe", natT)) lnilC) (searchCond pF xF (Free("b_fe", natT))))
        fun ebody w (hw:thm) =
          let val memNil = conjunct1_W (lmem w lnilC, searchCond pF xF w) hw
              val fls = Thm.implies_elim (lmemNilElim_W w) memNil
          in Thm.implies_elim (oFalse_elim_W goalC) fls end
        val res = exE_W (PexAbs, goalC) hex "w_fb" ebody
      in impI_W (existsCond lnilC, goalC) (Thm.implies_intr (ctermW hexP) res) end
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val ihP = jT (concBody tF)
    val IH  = Thm.assume (ctermW ihP)
    val step =
      let
        val consL = lcons hF tF
        val hexP = jT (existsCond consL)
        val hex  = Thm.assume (ctermW hexP)
        val goalC = goodConc consL
        val emH = em_W (searchCond pF xF hF)
        val caseEq =
          let
            val hch = Thm.assume (ctermW (jT (searchCond pF xF hF)))
            val fEq = fsearchEq_W (pF, xF, hF, tF) hch
            val fEqS = oeq_sym_vW OF [fEq]
            val Pcond = Term.lambda (Free("z_sc", natT)) (searchCond pF xF (Free("z_sc", natT)))
            val condFs = oeq_rw_W (Pcond, hF, fsearch pF xF consL) fEqS hch
            val memH = Thm.implies_elim (lmemConsBwd_W (hF, hF, tF))
                         (disjI1_W (oeq hF hF, lmem hF tF) (oeqRefl_W hF))
            val Pmem = Term.lambda (Free("z_m", natT)) (lmem (Free("z_m", natT)) consL)
            val memFs = oeq_rw_W (Pmem, hF, fsearch pF xF consL) fEqS memH
            val cj = conjI_W (searchCond pF xF (fsearch pF xF consL), lmem (fsearch pF xF consL) consL) condFs memFs
          in Thm.implies_intr (ctermW (jT (searchCond pF xF hF))) cj end
        val caseNeq =
          let
            val hnch = Thm.assume (ctermW (jT (neg (searchCond pF xF hF))))
            val fNeq = fsearchNeq_W (pF, xF, hF, tF) hnch
            val PexAbs = Term.lambda (Free("b_fe", natT))
                           (mkConj (lmem (Free("b_fe", natT)) consL) (searchCond pF xF (Free("b_fe", natT))))
            val existsT = existsCond tF
            fun ebody w (hw:thm) =
              let
                val memCons = conjunct1_W (lmem w consL, searchCond pF xF w) hw
                val scw     = conjunct2_W (lmem w consL, searchCond pF xF w) hw
                val dj      = Thm.implies_elim (lmemConsFwd_W (w, hF, tF)) memCons
                val cWh =
                  let val hwh = Thm.assume (ctermW (jT (oeq w hF)))
                      val Pcond = Term.lambda (Free("z_sc2", natT)) (searchCond pF xF (Free("z_sc2", natT)))
                      val sch = oeq_rw_W (Pcond, w, hF) hwh scw
                      val fls = mp_W (searchCond pF xF hF, oFalseC) hnch sch
                      val any = Thm.implies_elim (oFalse_elim_W existsT) fls
                  in Thm.implies_intr (ctermW (jT (oeq w hF))) any end
                val cWt =
                  let val hwt = Thm.assume (ctermW (jT (lmem w tF)))
                      val cj  = conjI_W (lmem w tF, searchCond pF xF w) hwt scw
                      val PexT = Term.lambda (Free("b_fe", natT))
                                   (mkConj (lmem (Free("b_fe", natT)) tF) (searchCond pF xF (Free("b_fe", natT))))
                      val ex  = exI_W PexT w cj
                  in Thm.implies_intr (ctermW (jT (lmem w tF))) ex end
              in disjE_W (oeq w hF, lmem w tF, existsT) dj cWh cWt end
            val exT = exE_W (PexAbs, existsT) hex "w_fn" ebody
            val goodT = mp_W (existsCond tF, goodConc tF) IH exT
            val condT = conjunct1_W (searchCond pF xF (fsearch pF xF tF), lmem (fsearch pF xF tF) tF) goodT
            val memT  = conjunct2_W (searchCond pF xF (fsearch pF xF tF), lmem (fsearch pF xF tF) tF) goodT
            val fNeqS = oeq_sym_vW OF [fNeq]
            val Pcond = Term.lambda (Free("z_c3", natT)) (searchCond pF xF (Free("z_c3", natT)))
            val condCons = oeq_rw_W (Pcond, fsearch pF xF tF, fsearch pF xF consL) fNeqS condT
            val memConsT = Thm.implies_elim (lmemConsBwd_W (fsearch pF xF tF, hF, tF))
                             (disjI2_W (oeq (fsearch pF xF tF) hF, lmem (fsearch pF xF tF) tF) memT)
            val Pmem = Term.lambda (Free("z_m3", natT)) (lmem (Free("z_m3", natT)) consL)
            val memCons = oeq_rw_W (Pmem, fsearch pF xF tF, fsearch pF xF consL) fNeqS memConsT
            val cj = conjI_W (searchCond pF xF (fsearch pF xF consL), lmem (fsearch pF xF consL) consL) condCons memCons
          in Thm.implies_intr (ctermW (jT (neg (searchCond pF xF hF)))) cj end
        val conc = disjE_W (searchCond pF xF hF, neg (searchCond pF xF hF), goalC) emH caseEq caseNeq
      in impI_W (existsCond consL, goalC) (Thm.implies_intr (ctermW hexP) conc) end
    val step1 = Thm.forall_intr (ctermW hF)
                  (Thm.forall_intr (ctermW tF) (Thm.implies_intr (ctermW ihP) step))
    val full = list_induct_W (Pabs, LF) base step1
  in varify full end;
val () = if length (Thm.hyps_of fsearch_found) = 0 then out "OK fsearch_found\n" else out "FAIL fsearch_found\n";

val () = out "WI_FSEARCH_FOUND_DONE\n";

(* ============================================================================
   cong intro combinators on ctxtW + a few order helpers.
   ============================================================================ *)
fun cong_introL_W (m,a,b,w) hyp =
  let val Pabs = Abs("k", natT, oeq b (add a (mult m (Bound 0))))
      val ex = exI_W Pabs w hyp
  in disjI1_W (congL m a b, congR m a b) ex end;
fun cong_introR_W (m,a,b,w) hyp =
  let val Pabs = Abs("k", natT, oeq a (add b (mult m (Bound 0))))
      val ex = exI_W Pabs w hyp
  in disjI2_W (congL m a b, congR m a b) ex end;

(* pos_pred : lt 1 p ==> Ex q. oeq p (Suc q) *)
val pos_pred =
  let
    val pF = Free("p", natT)
    val hp1P = jT (lt (suc ZeroC) pF) ; val hp1 = Thm.assume (ctermW hp1P)
    val goalC = mkExSuc_W pF
    val Pd = Abs("d", natT, oeq pF (add (suc (suc ZeroC)) (Bound 0)))
    fun body d (hd:thm) =
      let
        val aS = addSuc_W (suc ZeroC, d)
        val p_suc = oeq_trans_vW OF [hd, aS]
        val Pq = Abs("q", natT, oeq pF (suc (Bound 0)))
        val ex = exI_W Pq (add (suc ZeroC) d) p_suc
      in ex end
    val res = exE_W (Pd, goalC) hp1 "d_pp" body
  in varify (Thm.implies_intr (ctermW hp1P) res) end;
val () = if length (Thm.hyps_of pos_pred) = 0 then out "OK pos_pred\n" else out "FAIL pos_pred\n";

(* sub_lt_self : oeq p (Suc q) ==> lt (sub p (Suc Zero)) p *)
val sub_lt_self =
  let
    val pF = Free("p", natT); val qF = Free("q", natT)
    val hpqP = jT (oeq pF (suc qF)) ; val hpq = Thm.assume (ctermW hpqP)
    val Psub = Term.lambda (Free("z_su", natT)) (oeq (sub (Free("z_su", natT)) (suc ZeroC)) qF)
    val e1 = subSS_W (qF, ZeroC)
    val e2 = sub0_W qF
    val subSucq = oeq_trans_vW OF [e1, e2]
    val hpq_s = oeq_sym_vW OF [hpq]
    val subP = oeq_rw_W (Psub, suc qF, pF) hpq_s subSucq
    val lt_q_Sq = lt_suc_W qF
    val Plt = Term.lambda (Free("z_lt2", natT)) (lt qF (Free("z_lt2", natT)))
    val lt_q_p = oeq_rw_W (Plt, suc qF, pF) hpq_s lt_q_Sq
    val subP_s = oeq_sym_vW OF [subP]
    val Plt2 = Term.lambda (Free("z_lt3", natT)) (lt (Free("z_lt3", natT)) pF)
    val res = oeq_rw_W (Plt2, qF, sub pF (suc ZeroC)) subP_s lt_q_p
    val d1 = Thm.implies_intr (ctermW hpqP) res
  in varify d1 end;
val () = if length (Thm.hyps_of sub_lt_self) = 0 then out "OK sub_lt_self\n" else out "FAIL sub_lt_self\n";

val () = out "WI_ORDER_HELPERS_DONE\n";

(* ============================================================================
   not_dvd_in_range : 1 < p ==> lmem x (upto (sub p 1)) ==> ~(dvd p x)
   ============================================================================ *)
val not_dvd_in_range =
  let
    val pF = Free("p", natT); val xF = Free("x", natT)
    val hp1P = jT (lt (suc ZeroC) pF) ; val hp1 = Thm.assume (ctermW hp1P)
    val hmemP = jT (lmem xF (uptoF (sub pF (suc ZeroC)))) ; val hmem = Thm.assume (ctermW hmemP)
    val cj = lmem_upto_fwd_W (xF, sub pF (suc ZeroC)) hmem
    val hx0 = conjunct1_W (lt ZeroC xF, le xF (sub pF (suc ZeroC))) cj
    val hxle= conjunct2_W (lt ZeroC xF, le xF (sub pF (suc ZeroC))) cj
    val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pF)] pos_pred)) hp1
    val goalC = neg (dvd pF xF)
    fun predBody q (hq:thm) =
      let
        val subLt = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
                      [(("p",0), ctermW pF),(("q",0), ctermW q)] sub_lt_self)) hq
        val subp1 = sub pF (suc ZeroC)
        val Pd = Abs("d", natT, oeq subp1 (add xF (Bound 0)))
        fun leSucBody d (hd:thm) =
          let val sc = Suc_cong_vW OF [hd]
              val sx = addSuc_W (xF, d)
              val sxs= oeq_sym_vW OF [sx]
              val fin= oeq_trans_vW OF [sc, sxs]
          in le_intro_W (suc xF, suc subp1, d) fin end
        val leSucSuc = exE_W (Pd, le (suc xF) (suc subp1)) hxle "d_lr" leSucBody
        val ltxp = le_trans_W (suc xF, suc subp1, pF) leSucSuc subLt
        val notDvd =
          let
            val hdvd = Thm.assume (ctermW (jT (dvd pF xF)))
            val xnz =
              let val hz = Thm.assume (ctermW (jT (oeq xF ZeroC)))
                  val Plez = Term.lambda (Free("z_xz", natT)) (le (suc ZeroC) (Free("z_xz", natT)))
                  val le10 = oeq_rw_W (Plez, xF, ZeroC) hz hx0
                  val fls = lt_irrefl_W ZeroC le10
              in Thm.implies_intr (ctermW (jT (oeq xF ZeroC))) fls end
            val lepx = dvd_le_W (pF, xF) hdvd xnz
            val leSxx = le_trans_W (suc xF, pF, xF) ltxp lepx
            val fls = lt_irrefl_W xF leSxx
          in Thm.implies_intr (ctermW (jT (dvd pF xF))) fls end
      in impI_W (dvd pF xF, oFalseC) notDvd end
    val res = exE_W (Abs("q", natT, oeq pF (suc (Bound 0))), goalC) predEx "q_dr" predBody
    val d2 = Thm.implies_intr (ctermW hmemP) res
    val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of not_dvd_in_range) = 0 then out "OK not_dvd_in_range\n" else out "FAIL not_dvd_in_range\n";

val () = out "WI_NOT_DVD_RANGE_DONE\n";

(* ============================================================================
   more order helpers + cong_self_rmod + range membership of remainder.
   ============================================================================ *)
val lt_suc_cases_vW = varify lt_suc_cases;
fun lt_suc_cases_W (mt,nt) hlt =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("m",0), ctermW mt),(("n",0), ctermW nt)] lt_suc_cases_vW)) hlt;
fun le_self_suc_W nt =
  let val aSr = addSr_W (nt, ZeroC)
      val a0r = add0r_W nt
      val sa0r = Suc_cong_vW OF [a0r]
      val sum = oeq_trans_vW OF [aSr, sa0r]
      val sumS = oeq_sym_vW OF [sum]
  in le_intro_W (nt, suc nt, suc ZeroC) sumS end;
fun lt_imp_le_W (bt,qt) hlt =
  let val lebsb = le_self_suc_W bt
  in le_trans_W (bt, suc bt, qt) lebsb hlt end;
fun lt_suc_imp_le_W (bt,qt) hlt =
  let val dj = lt_suc_cases_W (bt, qt) hlt
      val cA = let val h = Thm.assume (ctermW (jT (lt bt qt)))
                   val r = lt_imp_le_W (bt, qt) h
               in Thm.implies_intr (ctermW (jT (lt bt qt))) r end
      val cB = let val h = Thm.assume (ctermW (jT (oeq bt qt)))
                   val Ple = Term.lambda (Free("z_lq", natT)) (le bt (Free("z_lq", natT)))
                   val r = oeq_rw_W (Ple, bt, qt) h (le_refl_W bt)
               in Thm.implies_intr (ctermW (jT (oeq bt qt))) r end
  in disjE_W (lt bt qt, oeq bt qt, le bt qt) dj cA cB end;

val cong_self_rmod =
  let
    val pF = Free("p", natT); val aF = Free("a", natT)
    val hp0P = jT (lt ZeroC pF) ; val hp0 = Thm.assume (ctermW hp0P)
    val q = rdiv aF pF; val r = rmod aF pF
    val hEq = div_mod_eq_W (aF, pF) hp0
    val comm = addcomm_W (mult pF q, r)
    val aEq = oeq_trans_vW OF [hEq, comm]
    val congAR = cong_introR_W (pF, aF, r, q) aEq
  in varify (Thm.implies_intr (ctermW hp0P) congAR) end;
val () = if length (Thm.hyps_of cong_self_rmod) = 0 then out "OK cong_self_rmod\n" else out "FAIL cong_self_rmod\n";
fun cong_self_rmod_W (pt,at) hp0 =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("p",0), ctermW pt),(("a",0), ctermW at)] cong_self_rmod)) hp0;

val () = out "WI_CONG_SELF_RMOD_DONE\n";

(* ============================================================================
   mem_range_inverse_exists :
     prime2 p ==> lmem x (upto (sub p 1)) ==> Ex b. Conj (lmem b (upto (sub p 1)))(searchCond p x b)
   ============================================================================ *)
val mem_range_inverse_exists =
  let
    val pF = Free("p", natT); val xF = Free("x", natT)
    val one = suc ZeroC
    val subp1 = sub pF one
    val hPrimeP = jT (prime2 pF) ; val hPrime = Thm.assume (ctermW hPrimeP)
    val hmemP = jT (lmem xF (uptoF subp1)) ; val hmem = Thm.assume (ctermW hmemP)
    val hp1 = prime2_gt1_W pF hPrime
    val hp0 = lt1_imp_lt0_W pF hp1
    val ndvd =
      let val inst = beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pF),(("x",0), ctermW xF)] not_dvd_in_range)
      in Thm.implies_elim (Thm.implies_elim inst hp1) hmem end
    val miEx = mod_inverse_W (pF, xF) hPrime ndvd
    val goalC = mkEx (Term.lambda (Free("b_re", natT))
                  (mkConj (lmem (Free("b_re", natT)) (uptoF subp1)) (searchCond pF xF (Free("b_re", natT)))))
    val miAbs = mi_innerAbs_W (pF, xF)
    fun miBody b0 (hcg0:thm) =
      let
        val b = rmod b0 pF
        val congb0b = cong_self_rmod_W (pF, b0) hp0
        val creflx = cong_refl_W (pF, xF)
        val congXprod = cong_mult_W (pF, xF, xF, b0, b) creflx congb0b
        val congXprodS = cong_sym_W (pF, mult xF b0, mult xF b) congXprod
        val congXB1 = cong_trans_W (pF, mult xF b, mult xF b0, one) congXprodS hcg0
        val scb = cong_imp_scond_W (pF, xF, b) hp1 congXB1
        val bltp = rmod_lt_W (b0, pF) hp0
        val dzb = dzos_W b
        val hb0pos =
          let
            val caseZ = let val hbz = Thm.assume (ctermW (jT (oeq b ZeroC)))
                            val xbcong = mult_cong_r_W (xF, b, ZeroC) hbz
                            val x0 = mult0r_W xF
                            val xb0 = oeq_trans_vW OF [xbcong, x0]
                            val Pc = Term.lambda (Free("z_cz2", natT)) (cong pF (Free("z_cz2", natT)) one)
                            val cong01 = oeq_rw_W (Pc, mult xF b, ZeroC) xb0 congXB1
                            val caseL =
                              let val hL = Thm.assume (ctermW (jT (congL pF ZeroC one)))
                                  val Pk = Abs("k", natT, oeq one (add ZeroC (mult pF (Bound 0))))
                                  fun kb k (hk:thm) =
                                    let val z0 = add0_W (mult pF k)
                                        val one_pk = oeq_trans_vW OF [hk, z0]
                                        val dvdp1 = dvd_intro_W (pF, one, k) one_pk
                                        val onenz = let val h00 = Thm.assume (ctermW (jT (oeq one ZeroC)))
                                                    in Thm.implies_intr (ctermW (jT (oeq one ZeroC))) (Suc_neq_Zero_W ZeroC h00) end
                                        val lep1 = dvd_le_W (pF, one) dvdp1 onenz
                                        val le21 = le_trans_W (suc one, pF, one) hp1 lep1
                                    in lt_irrefl_W one le21 end
                                  val r = exE_W (Pk, oFalseC) hL "k_cl2" kb
                              in Thm.implies_intr (ctermW (jT (congL pF ZeroC one))) r end
                            val caseR =
                              let val hR = Thm.assume (ctermW (jT (congR pF ZeroC one)))
                                  val Pk = Abs("k", natT, oeq ZeroC (add one (mult pF (Bound 0))))
                                  fun kb k (hk:thm) =
                                    let val aS = addSuc_W (ZeroC, mult pF k)
                                        val zSuc = oeq_trans_vW OF [hk, aS]
                                        val sucz = oeq_sym_vW OF [zSuc]
                                    in Suc_neq_Zero_W (add ZeroC (mult pF k)) sucz end
                                  val r = exE_W (Pk, oFalseC) hR "k_cr2" kb
                              in Thm.implies_intr (ctermW (jT (congR pF ZeroC one))) r end
                            val fls = disjE_W (congL pF ZeroC one, congR pF ZeroC one, oFalseC) cong01 caseL caseR
                            val ltb = Thm.implies_elim (oFalse_elim_W (lt ZeroC b)) fls
                        in Thm.implies_intr (ctermW (jT (oeq b ZeroC))) ltb end
            val caseS = let val hsP = jT (mkExSuc_W b)
                            val hs = Thm.assume (ctermW hsP)
                            val Pq = Abs("q", natT, oeq b (suc (Bound 0)))
                            fun sb k (hk:thm) =
                              let
                                  val lt0Sk =
                                    let val a1 = addSuc_W (ZeroC, k)
                                        val a0 = add0_W k
                                        val sa0= Suc_cong_vW OF [a0]
                                        val sum= oeq_trans_vW OF [a1, sa0]
                                        val sumS = oeq_sym_vW OF [sum]
                                    in le_intro_W (suc ZeroC, suc k, k) sumS end
                                  val hk_s = oeq_sym_vW OF [hk]
                                  val Plt = Term.lambda (Free("z_p0", natT)) (lt ZeroC (Free("z_p0", natT)))
                              in oeq_rw_W (Plt, suc k, b) hk_s lt0Sk end
                            val r = exE_W (Pq, lt ZeroC b) hs "k_bs" sb
                        in Thm.implies_intr (ctermW (jT (mkExSuc_W b))) r end
          in disjE_W (oeq b ZeroC, mkExSuc_W b, lt ZeroC b) dzb caseZ caseS end
        val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pF)] pos_pred)) hp1
        fun predBody q (hq:thm) =
          let
            val Plt = Term.lambda (Free("z_bp", natT)) (lt b (Free("z_bp", natT)))
            val ltbSq = oeq_rw_W (Plt, pF, suc q) hq bltp
            val lebq = lt_suc_imp_le_W (b, q) ltbSq
            val e1 = subSS_W (q, ZeroC)
            val e2 = sub0_W q
            val subSucq = oeq_trans_vW OF [e1, e2]
            val hq_s = oeq_sym_vW OF [hq]
            val Psub = Term.lambda (Free("z_sb2", natT)) (oeq (sub (Free("z_sb2", natT)) one) q)
            val subP = oeq_rw_W (Psub, suc q, pF) hq_s subSucq
            val subP_s = oeq_sym_vW OF [subP]
            val Ple = Term.lambda (Free("z_le2", natT)) (le b (Free("z_le2", natT)))
            val lebsub = oeq_rw_W (Ple, q, subp1) subP_s lebq
            val cj = conjI_W (lt ZeroC b, le b subp1) hb0pos lebsub
            val memB = lmem_upto_bwd_W (b, subp1) cj
            val resCj = conjI_W (lmem b (uptoF subp1), searchCond pF xF b) memB scb
            val PgoalAbs = Term.lambda (Free("b_re", natT))
                  (mkConj (lmem (Free("b_re", natT)) (uptoF subp1)) (searchCond pF xF (Free("b_re", natT))))
            val ex = exI_W PgoalAbs b resCj
          in ex end
        val res = exE_W (Abs("q", natT, oeq pF (suc (Bound 0))), goalC) predEx "q_mr" predBody
      in res end
    val res = exE_W (miAbs, goalC) miEx "b0_mi" miBody
    val d2 = Thm.implies_intr (ctermW hmemP) res
    val d1 = Thm.implies_intr (ctermW hPrimeP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of mem_range_inverse_exists) = 0 then out "OK mem_range_inverse_exists\n" else out "FAIL mem_range_inverse_exists\n";

val () = out "WI_MEM_RANGE_INV_EXISTS_DONE\n";

(* accessor : fsearch_found applied at (p,x,L) to an existence proof. *)
fun fsearch_found_W (pt,xt,Lt) hex =
  let
    val existsAbs = Term.lambda (Free("b_fe", natT))
                      (mkConj (lmem (Free("b_fe", natT)) Lt) (searchCond pt xt (Free("b_fe", natT))))
    val existsT = mkEx existsAbs
    val goodT = mkConj (searchCond pt xt (fsearch pt xt Lt)) (lmem (fsearch pt xt Lt) Lt)
    val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("x",0), ctermW xt),(("L",0), ctermW Lt)] fsearch_found)
  in mp_W (existsT, goodT) inst hex end;

val () = out "WI_FSEARCH_FOUND_ACCESSOR_DONE\n";

fun mem_range_inverse_exists_W (pt,xt) hPrime hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("x",0), ctermW xt)] mem_range_inverse_exists)
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hmem end;

(* ============================================================================
   TARGET 1 : finv_inv : prime2 p ==> lmem x (upto (sub p 1)) ==> cong p (mult x (finv p x)) 1
   ============================================================================ *)
val finv_inv =
  let
    val pF = Free("p", natT); val xF = Free("x", natT)
    val one = suc ZeroC ; val subp1 = sub pF one ; val rng = uptoF subp1
    val hPrimeP = jT (prime2 pF) ; val hPrime = Thm.assume (ctermW hPrimeP)
    val hmemP = jT (lmem xF rng) ; val hmem = Thm.assume (ctermW hmemP)
    val hp1 = prime2_gt1_W pF hPrime
    val hex = mem_range_inverse_exists_W (pF, xF) hPrime hmem
    val good = fsearch_found_W (pF, xF, rng) hex
    val scFs = conjunct1_W (searchCond pF xF (fsearch pF xF rng), lmem (fsearch pF xF rng) rng) good
    val congFs = scond_imp_cong_W (pF, xF, fsearch pF xF rng) hp1 scFs
    val fdef = finvDef_W (pF, xF)
    val fdef_s = oeq_sym_vW OF [fdef]
    val Pc = Term.lambda (Free("z_fi", natT)) (cong pF (mult xF (Free("z_fi", natT))) one)
    val res = oeq_rw_W (Pc, fsearch pF xF rng, finv pF xF) fdef_s congFs
    val d2 = Thm.implies_intr (ctermW hmemP) res
    val d1 = Thm.implies_intr (ctermW hPrimeP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of finv_inv) = 0 then out "OK finv_inv\n" else out "FAIL finv_inv\n";

(* ============================================================================
   TARGET 2 : finv_mem : prime2 p ==> lmem x (upto (sub p 1)) ==> lmem (finv p x) (upto (sub p 1))
   ============================================================================ *)
val finv_mem =
  let
    val pF = Free("p", natT); val xF = Free("x", natT)
    val one = suc ZeroC ; val subp1 = sub pF one ; val rng = uptoF subp1
    val hPrimeP = jT (prime2 pF) ; val hPrime = Thm.assume (ctermW hPrimeP)
    val hmemP = jT (lmem xF rng) ; val hmem = Thm.assume (ctermW hmemP)
    val hex = mem_range_inverse_exists_W (pF, xF) hPrime hmem
    val good = fsearch_found_W (pF, xF, rng) hex
    val memFs = conjunct2_W (searchCond pF xF (fsearch pF xF rng), lmem (fsearch pF xF rng) rng) good
    val fdef = finvDef_W (pF, xF)
    val fdef_s = oeq_sym_vW OF [fdef]
    val Pm = Term.lambda (Free("z_fm", natT)) (lmem (Free("z_fm", natT)) rng)
    val res = oeq_rw_W (Pm, fsearch pF xF rng, finv pF xF) fdef_s memFs
    val d2 = Thm.implies_intr (ctermW hmemP) res
    val d1 = Thm.implies_intr (ctermW hPrimeP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of finv_mem) = 0 then out "OK finv_mem\n" else out "FAIL finv_mem\n";

val () = out "WI_FINV_INV_MEM_DONE\n";

(* ============================================================================
   lmem_range_lt : 1 < p ==> lmem x (upto (sub p 1)) ==> lt x p
   ============================================================================ *)
val lmem_range_lt =
  let
    val pF = Free("p", natT); val xF = Free("x", natT)
    val one = suc ZeroC ; val subp1 = sub pF one
    val hp1P = jT (lt one pF) ; val hp1 = Thm.assume (ctermW hp1P)
    val hmemP = jT (lmem xF (uptoF subp1)) ; val hmem = Thm.assume (ctermW hmemP)
    val cj = lmem_upto_fwd_W (xF, subp1) hmem
    val hxle = conjunct2_W (lt ZeroC xF, le xF subp1) cj
    val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pF)] pos_pred)) hp1
    val goalC = lt xF pF
    fun predBody q (hq:thm) =
      let
        val subLt = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
                      [(("p",0), ctermW pF),(("q",0), ctermW q)] sub_lt_self)) hq
        val Pd = Abs("d", natT, oeq subp1 (add xF (Bound 0)))
        fun leSucBody d (hd:thm) =
          let val sc = Suc_cong_vW OF [hd]
              val sx = addSuc_W (xF, d)
              val sxs= oeq_sym_vW OF [sx]
              val fin= oeq_trans_vW OF [sc, sxs]
          in le_intro_W (suc xF, suc subp1, d) fin end
        val leSucSuc = exE_W (Pd, le (suc xF) (suc subp1)) hxle "d_lrl" leSucBody
        val ltxp = le_trans_W (suc xF, suc subp1, pF) leSucSuc subLt
      in ltxp end
    val res = exE_W (Abs("q", natT, oeq pF (suc (Bound 0))), goalC) predEx "q_lrl" predBody
    val d2 = Thm.implies_intr (ctermW hmemP) res
    val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of lmem_range_lt) = 0 then out "OK lmem_range_lt\n" else out "FAIL lmem_range_lt\n";
fun lmem_range_lt_W (pt,xt) hp1 hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pt),(("x",0), ctermW xt)] lmem_range_lt)
  in Thm.implies_elim (Thm.implies_elim inst hp1) hmem end;

(* rmod_id : 0 < p ==> lt a p ==> oeq (rmod a p) a *)
val rmod_id =
  let
    val pF = Free("p", natT); val aF = Free("a", natT)
    val hp0P = jT (lt ZeroC pF) ; val hp0 = Thm.assume (ctermW hp0P)
    val haltP = jT (lt aF pF) ; val halt = Thm.assume (ctermW haltP)
    val q1 = rdiv aF pF ; val r1 = rmod aF pF
    val hEq = div_mod_eq_W (aF, pF) hp0
    val hr1lt = rmod_lt_W (aF, pF) hp0
    val p0 = mult0r_W pF
    val pol = add_cong_l_W (mult pF ZeroC, ZeroC, aF) p0
    val z1 = add0_W aF
    val eq2 = oeq_trans_vW OF [pol, z1]
    val eqWit = oeq_sym_vW OF [eq2]
    val combined = oeq_trans_vW OF [oeq_sym_vW OF [hEq], eqWit]
    val uniq = div_mod_unique_W (pF, q1, r1, ZeroC, aF) combined hr1lt halt
    val r1a = conjunct2_W (oeq q1 ZeroC, oeq r1 aF) uniq
    val d2 = Thm.implies_intr (ctermW haltP) r1a
    val d1 = Thm.implies_intr (ctermW hp0P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of rmod_id) = 0 then out "OK rmod_id\n" else out "FAIL rmod_id\n";
fun rmod_id_W (pt,at) hp0 halt =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pt),(("a",0), ctermW at)] rmod_id)
  in Thm.implies_elim (Thm.implies_elim inst hp0) halt end;

(* cong_range_unique : 1 < p ==> lt a p ==> lt b p ==> cong p a b ==> oeq a b *)
val cong_range_unique =
  let
    val pF = Free("p", natT); val aF = Free("a", natT); val bF = Free("b", natT)
    val one = suc ZeroC
    val hp1P = jT (lt one pF) ; val hp1 = Thm.assume (ctermW hp1P)
    val haltP = jT (lt aF pF) ; val halt = Thm.assume (ctermW haltP)
    val hbltP = jT (lt bF pF) ; val hblt = Thm.assume (ctermW hbltP)
    val hcgP = jT (cong pF aF bF) ; val hcg = Thm.assume (ctermW hcgP)
    val hp0 = lt1_imp_lt0_W pF hp1
    val req = cong_imp_rmodeq_W (pF, aF, bF) hp0 hcg
    val ria = rmod_id_W (pF, aF) hp0 halt
    val rib = rmod_id_W (pF, bF) hp0 hblt
    val a_rmodb = oeq_trans_vW OF [oeq_sym_vW OF [ria], req]
    val a_b = oeq_trans_vW OF [a_rmodb, rib]
    val d4 = Thm.implies_intr (ctermW hcgP) a_b
    val d3 = Thm.implies_intr (ctermW hbltP) d4
    val d2 = Thm.implies_intr (ctermW haltP) d3
    val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of cong_range_unique) = 0 then out "OK cong_range_unique\n" else out "FAIL cong_range_unique\n";
fun cong_range_unique_W (pt,at,bt) hp1 halt hblt hcg =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("p",0), ctermW pt),(("a",0), ctermW at),(("b",0), ctermW bt)] cong_range_unique)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hp1) halt) hblt) hcg end;

val () = out "WI_RANGE_UNIQUE_DONE\n";

fun finv_inv_W (pt,xt) hPrime hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pt),(("x",0), ctermW xt)] finv_inv)
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hmem end;
fun finv_mem_W (pt,xt) hPrime hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pt),(("x",0), ctermW xt)] finv_mem)
  in Thm.implies_elim (Thm.implies_elim inst hPrime) hmem end;

(* ============================================================================
   TARGET 3 : finv_invol : prime2 p ==> lmem x (upto (sub p 1)) ==> oeq (finv p (finv p x)) x
   ============================================================================ *)
val finv_invol =
  let
    val pF = Free("p", natT); val xF = Free("x", natT)
    val one = suc ZeroC ; val subp1 = sub pF one ; val rng = uptoF subp1
    val hPrimeP = jT (prime2 pF) ; val hPrime = Thm.assume (ctermW hPrimeP)
    val hmemP = jT (lmem xF rng) ; val hmem = Thm.assume (ctermW hmemP)
    val hp1 = prime2_gt1_W pF hPrime
    val y = finv pF xF
    val cong_xy_1 = finv_inv_W (pF, xF) hPrime hmem
    val memY = finv_mem_W (pF, xF) hPrime hmem
    val cong_y_fyinv_1 = finv_inv_W (pF, y) hPrime memY
    val memFy = finv_mem_W (pF, y) hPrime memY
    val comm_xy = multcomm_W (xF, y)
    val Pc = Term.lambda (Free("z_iv", natT)) (cong pF (Free("z_iv", natT)) one)
    val cong_yx_1 = oeq_rw_W (Pc, mult xF y, mult y xF) comm_xy cong_xy_1
    val cong_fy_x = inverse_unique_W (pF, y, finv pF y, xF) cong_y_fyinv_1 cong_yx_1
    val lt_fy = lmem_range_lt_W (pF, finv pF y) hp1 memFy
    val lt_x  = lmem_range_lt_W (pF, xF) hp1 hmem
    val res = cong_range_unique_W (pF, finv pF y, xF) hp1 lt_fy lt_x cong_fy_x
    val d2 = Thm.implies_intr (ctermW hmemP) res
    val d1 = Thm.implies_intr (ctermW hPrimeP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of finv_invol) = 0 then out "OK finv_invol\n" else out "FAIL finv_invol\n";

val () = out "WI_FINV_INVOL_DONE\n";

(* le_cases_W : le a b ==> Disj (oeq a b)(lt a b) *)
val le_cases =
  let
    val aF = Free("a", natT); val bF = Free("b", natT)
    val hleP = jT (le aF bF) ; val hle = Thm.assume (ctermW hleP)
    val goalC = mkDisj (oeq aF bF) (lt aF bF)
    val Pd = Abs("d", natT, oeq bF (add aF (Bound 0)))
    fun body d (hd:thm) =
      let
        val dz = dzos_W d
        val caseZ = let val hz = Thm.assume (ctermW (jT (oeq d ZeroC)))
                        val c1 = add_cong_r_W (aF, d, ZeroC) hz
                        val a0 = add0r_W aF
                        val c2 = oeq_trans_vW OF [c1, a0]
                        val b_a = oeq_trans_vW OF [hd, c2]
                        val a_b = oeq_sym_vW OF [b_a]
                    in Thm.implies_intr (ctermW (jT (oeq d ZeroC))) (disjI1_W (oeq aF bF, lt aF bF) a_b) end
        val caseS = let val hsP = jT (mkExSuc_W d)
                        val hs = Thm.assume (ctermW hsP)
                        val Pq = Abs("q", natT, oeq d (suc (Bound 0)))
                        fun sb e (he:thm) =
                          let val c1 = add_cong_r_W (aF, d, suc e) he
                              val b_aSe = oeq_trans_vW OF [hd, c1]
                              val aSe = addSr_W (aF, e)
                              val b_Sae = oeq_trans_vW OF [b_aSe, aSe]
                              val saS = addSuc_W (aF, e)
                              val saS_s = oeq_sym_vW OF [saS]
                              val b_Sae2 = oeq_trans_vW OF [b_Sae, saS_s]
                              val ltab = le_intro_W (suc aF, bF, e) b_Sae2
                          in disjI2_W (oeq aF bF, lt aF bF) ltab end
                        val r = exE_W (Pq, goalC) hs "e_lc" sb
                    in Thm.implies_intr (ctermW (jT (mkExSuc_W d))) r end
      in disjE_W (oeq d ZeroC, mkExSuc_W d, goalC) dz caseZ caseS end
    val res = exE_W (Pd, goalC) hle "d_lc" body
  in varify (Thm.implies_intr (ctermW hleP) res) end;
val () = if length (Thm.hyps_of le_cases) = 0 then out "OK le_cases\n" else out "FAIL le_cases\n";
fun le_cases_W (at,bt) hle =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("a",0), ctermW at),(("b",0), ctermW bt)] le_cases)) hle;

(* ============================================================================
   TARGET 4 : finv_neq :
     prime2 p ==> lmem x (upto (sub p 1)) ==> ~(oeq x 1) ==> ~(oeq x (sub p 1))
       ==> ~(oeq (finv p x) x)         [x in [2..p-2]]
   ============================================================================ *)
val finv_neq =
  let
    val pF = Free("p", natT); val xF = Free("x", natT)
    val one = suc ZeroC ; val subp1 = sub pF one ; val rng = uptoF subp1
    val hPrimeP = jT (prime2 pF) ; val hPrime = Thm.assume (ctermW hPrimeP)
    val hmemP = jT (lmem xF rng) ; val hmem = Thm.assume (ctermW hmemP)
    val hne1P = jT (neg (oeq xF one)) ; val hne1 = Thm.assume (ctermW hne1P)
    val hneqP = jT (neg (oeq xF subp1)) ; val hneq = Thm.assume (ctermW hneqP)
    val hp1 = prime2_gt1_W pF hPrime
    val hp0 = lt1_imp_lt0_W pF hp1
    val hfxP = jT (oeq (finv pF xF) xF) ; val hfx = Thm.assume (ctermW hfxP)
    val cong_xfx = finv_inv_W (pF, xF) hPrime hmem
    val Pc = Term.lambda (Free("z_fn", natT)) (cong pF (mult xF (Free("z_fn", natT))) one)
    val cong_xx = oeq_rw_W (Pc, finv pF xF, xF) hfx cong_xfx
    val lr = lagrange_roots_W (pF, xF) hPrime cong_xx
    val ltx = lmem_range_lt_W (pF, xF) hp1 hmem
    val caseA =
      let val hcg = Thm.assume (ctermW (jT (cong pF xF one)))
          val oxx1 = cong_range_unique_W (pF, xF, one) hp1 ltx hp1 hcg
          val fls = mp_W (oeq xF one, oFalseC) hne1 oxx1
      in Thm.implies_intr (ctermW (jT (cong pF xF one))) fls end
    val caseB =
      let
        val hcg = Thm.assume (ctermW (jT (cong pF (suc xF) ZeroC)))
        val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW pF)] pos_pred)) hp1
        fun predBody q (hq:thm) =
          let
            val cjm = lmem_upto_fwd_W (xF, subp1) hmem
            val hxle = conjunct2_W (lt ZeroC xF, le xF subp1) cjm
            val e1 = subSS_W (q, ZeroC) ; val e2 = sub0_W q
            val subSucq = oeq_trans_vW OF [e1, e2]
            val hq_s = oeq_sym_vW OF [hq]
            val Psub = Term.lambda (Free("z_sb3", natT)) (oeq (sub (Free("z_sb3", natT)) one) q)
            val subPq = oeq_rw_W (Psub, suc q, pF) hq_s subSucq
            val Plex = Term.lambda (Free("z_lx", natT)) (le xF (Free("z_lx", natT)))
            val lexq = oeq_rw_W (Plex, subp1, q) subPq hxle
            val Pd = Abs("d", natT, oeq q (add xF (Bound 0)))
            fun leSucBody d (hd:thm) =
              let val sc = Suc_cong_vW OF [hd]
                  val sx = addSuc_W (xF, d)
                  val sxs= oeq_sym_vW OF [sx]
                  val fin= oeq_trans_vW OF [sc, sxs]
              in le_intro_W (suc xF, suc q, d) fin end
            val leSxSq = exE_W (Pd, le (suc xF) (suc q)) lexq "d_sn" leSucBody
            val hq_sB = oeq_sym_vW OF [hq]
            val Pleq = Term.lambda (Free("z_lp", natT)) (le (suc xF) (Free("z_lp", natT)))
            val leSxp = oeq_rw_W (Pleq, suc q, pF) hq_sB leSxSq
            val req = cong_imp_rmodeq_W (pF, suc xF, ZeroC) hp0 hcg
            val rmod0 = rmod_id_W (pF, ZeroC) hp0 hp0
            val rmodSx_0 = oeq_trans_vW OF [req, rmod0]
            val dj = le_cases_W (suc xF, pF) leSxp
            val subB1 =
              let val heqSxp = Thm.assume (ctermW (jT (oeq (suc xF) pF)))
                  val SxSq = oeq_trans_vW OF [heqSxp, hq]
                  val x_q = Suc_inj_W (xF, q) SxSq
                  val subPq_s = oeq_sym_vW OF [subPq]
                  val x_subp1 = oeq_trans_vW OF [x_q, subPq_s]
                  val fls = mp_W (oeq xF subp1, oFalseC) hneq x_subp1
              in Thm.implies_intr (ctermW (jT (oeq (suc xF) pF))) fls end
            val subB2 =
              let val hltSxp = Thm.assume (ctermW (jT (lt (suc xF) pF)))
                  val ridSx = rmod_id_W (pF, suc xF) hp0 hltSxp
                  val ridSx_s = oeq_sym_vW OF [ridSx]
                  val Sx_0 = oeq_trans_vW OF [ridSx_s, rmodSx_0]
                  val fls = Suc_neq_Zero_W xF Sx_0
              in Thm.implies_intr (ctermW (jT (lt (suc xF) pF))) fls end
            val fls = disjE_W (oeq (suc xF) pF, lt (suc xF) pF, oFalseC) dj subB1 subB2
          in fls end
        val fls = exE_W (Abs("q", natT, oeq pF (suc (Bound 0))), oFalseC) predEx "q_fn" predBody
      in Thm.implies_intr (ctermW (jT (cong pF (suc xF) ZeroC))) fls end
    val flsTop = disjE_W (cong pF xF one, cong pF (suc xF) ZeroC, oFalseC) lr caseA caseB
    val metaNeg = Thm.implies_intr (ctermW hfxP) flsTop
    val negThm = impI_W (oeq (finv pF xF) xF, oFalseC) metaNeg
    val d4 = Thm.implies_intr (ctermW hneqP) negThm
    val d3 = Thm.implies_intr (ctermW hne1P) d4
    val d2 = Thm.implies_intr (ctermW hmemP) d3
    val d1 = Thm.implies_intr (ctermW hPrimeP) d2
  in varify d1 end;
val () = if length (Thm.hyps_of finv_neq) = 0 then out "OK finv_neq\n" else out "FAIL finv_neq\n";

val () = out "WI_FINV_NEQ_DONE\n";

(* ============================================================================
   PHASE 2 FINAL VALIDATION : aconv intent, 0-hyp, soundness probes.
   ============================================================================ *)
val () = out "WI_VALIDATE_BEGIN\n";
val pV = Var(("p",0),natT); val xV = Var(("x",0),natT);
val oneV = suc ZeroC; val subp1V = sub pV oneV; val rngV = uptoF subp1V;

val finv_inv_intended =
  Logic.mk_implies (jT (prime2 pV),
    Logic.mk_implies (jT (lmem xV rngV),
      jT (cong pV (mult xV (finv pV xV)) oneV)));
val r_fi = (length (Thm.hyps_of finv_inv) = 0) andalso ((Thm.prop_of finv_inv) aconv finv_inv_intended);
val () = if r_fi then out "OK finv_inv aconv intended\n" else out "FAIL finv_inv aconv\n";

val finv_mem_intended =
  Logic.mk_implies (jT (prime2 pV),
    Logic.mk_implies (jT (lmem xV rngV),
      jT (lmem (finv pV xV) rngV)));
val r_fm = (length (Thm.hyps_of finv_mem) = 0) andalso ((Thm.prop_of finv_mem) aconv finv_mem_intended);
val () = if r_fm then out "OK finv_mem aconv intended\n" else out "FAIL finv_mem aconv\n";

val finv_invol_intended =
  Logic.mk_implies (jT (prime2 pV),
    Logic.mk_implies (jT (lmem xV rngV),
      jT (oeq (finv pV (finv pV xV)) xV)));
val r_fv = (length (Thm.hyps_of finv_invol) = 0) andalso ((Thm.prop_of finv_invol) aconv finv_invol_intended);
val () = if r_fv then out "OK finv_invol aconv intended\n" else out "FAIL finv_invol aconv\n";

val finv_neq_intended =
  Logic.mk_implies (jT (prime2 pV),
    Logic.mk_implies (jT (lmem xV rngV),
      Logic.mk_implies (jT (neg (oeq xV oneV)),
        Logic.mk_implies (jT (neg (oeq xV subp1V)),
          jT (neg (oeq (finv pV xV) xV))))));
val r_fn = (length (Thm.hyps_of finv_neq) = 0) andalso ((Thm.prop_of finv_neq) aconv finv_neq_intended);
val () = if r_fn then out "OK finv_neq aconv intended\n" else out "FAIL finv_neq aconv\n";

val probe_fi =
  let val bogus = Logic.mk_implies (jT (prime2 pV), jT (cong pV (mult xV (finv pV xV)) oneV))
  in not ((Thm.prop_of finv_inv) aconv bogus) end;
val () = if probe_fi then out "PROBE_OK finv_inv keeps lmem x rng\n" else out "PROBE_FAIL finv_inv\n";

val probe_fv =
  let val bogus = Logic.mk_implies (jT (prime2 pV), jT (oeq (finv pV (finv pV xV)) xV))
  in not ((Thm.prop_of finv_invol) aconv bogus) end;
val () = if probe_fv then out "PROBE_OK finv_invol keeps lmem x rng\n" else out "PROBE_FAIL finv_invol\n";

val probe_fn_drop1 =
  let val bogus = Logic.mk_implies (jT (prime2 pV),
        Logic.mk_implies (jT (lmem xV rngV),
          Logic.mk_implies (jT (neg (oeq xV subp1V)), jT (neg (oeq (finv pV xV) xV)))))
  in not ((Thm.prop_of finv_neq) aconv bogus) end;
val probe_fn_dropP =
  let val bogus = Logic.mk_implies (jT (prime2 pV),
        Logic.mk_implies (jT (lmem xV rngV),
          Logic.mk_implies (jT (neg (oeq xV oneV)), jT (neg (oeq (finv pV xV) xV)))))
  in not ((Thm.prop_of finv_neq) aconv bogus) end;
val () = if probe_fn_drop1 andalso probe_fn_dropP then out "PROBE_OK finv_neq keeps both x<>1 and x<>p-1\n" else out "PROBE_FAIL finv_neq\n";

val () =
  if r_fi andalso r_fm andalso r_fv andalso r_fn
     andalso probe_fi andalso probe_fv andalso probe_fn_drop1 andalso probe_fn_dropP
  then out "INVERSE_FN_OK\n"
  else out "INVERSE_FN_FAILED\n";
(* ============================================================================
   EULER FOUNDATIONS toward Euler's theorem, in Isabelle/Pure on the polyml-rs
   interpreter.  (test: isabelle_euler_foundations.rs)
   ----------------------------------------------------------------------------
   The two new ingredients Euler's theorem needs beyond the Wilson machinery
   (where the inverse pairing was an INVOLUTION; Euler's x |-> a*x is a general
   BIJECTION on the reduced residues). Both 0-hyp by genuine kernel inference:

   (1) PERMUTATION INVARIANCE of the list product:
         lprod_perm : lnodup L1 ==> lnodup L2 ==> (!x. lmem x L1 <-> lmem x L2)
                        ==> oeq (lprod L1) (lprod L2)
       Two duplicate-free lists with the same members have equal products. Proved
       by structural list induction with the SECOND list generalised via a fresh
       object natlist-universal quantifier LForall (so the cons case can apply the
       IH at (rest, lremove a M)); the head a is extracted from M (extract).

   (2) THE REDUCED-RESIDUE LIST + Euler's phi:
         gcdf  : a gcd FUNCTION via the Euclidean algorithm using rmod
                 (gcdf a 0 = a; 0<b ==> gcdf a b = gcdf b (rmod a b));
         coprime test  oeq (gcdf a n) 1  (DECIDABLE);
         rrl n : the list [1..n-1] filtered to the residues coprime to n;
         phi n : llen (rrl n);
         lmem_rrl : lmem r (rrl n) <-> (lmem r (upto (n-1)) /\ coprime r n).

   Soundness probes confirm lprod_perm genuinely needs both lnodup premises and
   lmem_rrl genuinely carries the coprime condition. Built on the Wilson-inverse
   base (rmod, the list library, upto) via common::with_wilson_inverse. Proved by
   a 2-goal ultracode fleet (wf_5604358b-d48); re-verified end-to-end by hand.

   NEXT (the Euler assembly): show r |-> rmod (a*r) n PERMUTES rrl n (closed under
   mult by the unit a; injective by mod_cancel), so lprod_perm gives lprod(map ..)
   = lprod(rrl); factor a out phi times => a^phi * lprod(rrl) == lprod(rrl); cancel
   the unit lprod(rrl) => a^phi == 1 (mod n). That is Euler's theorem.
   ============================================================================ *)

(* ============================================================================
   SEAT perm_invariance0 — lprod_perm: PERMUTATION INVARIANCE of the list product.
   Two duplicate-free lists with the SAME members have EQUAL products.
   Strategy: structural list_induct on L1, with the second list M generalised by
   a fresh OBJECT natlist-universal quantifier LForall (conservative: standard
   allI/allE axioms).  In the cons case L1 = lcons a rest, extract a from M
   (a in L1 hence in M), apply IH at (rest, lremove a M).
   ============================================================================ *)
val () = out "PERM_INV_BEGIN\n";

(* ---- extend thyL2 with a natlist universal quantifier ---- *)
val thyP0 = Sign.add_consts
  [(Binding.name "LForall", (natlistT --> oT) --> oT, NoSyn)] thyL2;
val LForallC = Const (Sign.full_name thyP0 (Binding.name "LForall"), (natlistT --> oT) --> oT);
fun mkLForall pr = LForallC $ pr;

val PpL = Free ("P", natlistT --> oT);
val xLallI = Free ("x", natlistT);
val ((_,LallI_ax), thyP1) = Thm.add_axiom_global (Binding.name "LallI",
      Logic.mk_implies (Logic.all xLallI (jT (PpL $ xLallI)), jT (mkLForall PpL))) thyP0;
val acL = Free ("a", natlistT);
val ((_,LallE_ax), thyP) = Thm.add_axiom_global (Binding.name "LallE",
      Logic.mk_implies (jT (mkLForall PpL), jT (PpL $ acL))) thyP1;

val ctxtP  = Proof_Context.init_global thyP;
val ctermP = Thm.cterm_of ctxtP;
val () = out "PERM_INV_CONTEXT_READY\n";

(* ---- re-varify EVERYTHING used onto ctxtP ---- *)
val oeq_refl_vP2    = varify oeq_refl;
val oeq_sym_vP2     = varify oeq_sym;
val oeq_trans_vP2   = varify oeq_trans;
val mp_vP           = varify mp_ax;
val impI_vP         = varify impI_ax;
val conjI_vP        = varify conjI_ax;
val conjunct1_vP    = varify conjunct1_ax;
val conjunct2_vP    = varify conjunct2_ax;
val disjI1_vP       = varify disjI1_ax;
val disjI2_vP       = varify disjI2_ax;
val disjE_vP        = varify disjE_ax;
val oFalse_elim_vP  = varify oFalse_elim_ax;
val ex_middle_vP    = varify ex_middle_ax;
val allI_vP         = varify allI_ax;     (* nat Forall *)
val allE_vP         = varify allE_ax;
val LallI_vP        = varify LallI_ax;
val LallE_vP        = varify LallE_ax;
(* list machinery *)
val leq_refl_vP     = varify leq_refl_ax;
val leq_subst_vP    = varify leq_subst_ax;
val list_induct_vP  = varify list_induct_ax;
val lprod_nil_vP    = varify lprod_nil_ax;
val lprod_cons_vP   = varify lprod_cons_ax;
val lmem_nil_elim_vP= varify lmem_nil_elim_ax;
val lmem_cons_fwd_vP= varify lmem_cons_fwd_ax;
val lmem_cons_bwd_vP= varify lmem_cons_bwd_ax;
val lremove_nil_vP  = varify lremove_nil_ax;
val lremove_cons_eq_vP  = varify lremove_cons_eq_ax;
val lremove_cons_neq_vP = varify lremove_cons_neq_ax;
val lnodup_cons_fwd_vP  = varify lnodup_cons_fwd_ax;
val lnodup_cons_bwd_vP  = varify lnodup_cons_bwd_ax;
val mult_comm_vP    = varify mult_comm;
val mult_assoc_vP   = varify mult_assoc;
(* derived list lemmas *)
val extract_vP      = varify extract;
val mem_remove_fwd_vP = varify mem_remove_fwd;
val mem_remove_bwd_vP = varify mem_remove_bwd;
val mem_remove_neq_vP = varify mem_remove_neq;
val nodup_remove_vP   = varify nodup_remove;
val leq_sym_vP      = varify leq_sym;

(* ---- combinators on ctxtP ---- *)
fun oeqRefl_P t = beta_norm (Drule.infer_instantiate ctxtP [(("a",0), ctermP t)] oeq_refl_vP2);
fun mp_P (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP [(("A",0), ctermP At),(("B",0), ctermP Bt)] mp_vP)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_P (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP [(("A",0), ctermP At),(("B",0), ctermP Bt)] impI_vP)
  in Thm.implies_elim inst hImpThm end;
fun conjI_P (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP [(("A",0), ctermP At),(("B",0), ctermP Bt)] conjI_vP)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_P (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("A",0), ctermP At),(("B",0), ctermP Bt)] conjunct1_vP)) h;
fun conjunct2_P (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("A",0), ctermP At),(("B",0), ctermP Bt)] conjunct2_vP)) h;
fun disjI1_P (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("A",0), ctermP At),(("B",0), ctermP Bt)] disjI1_vP)) h;
fun disjI2_P (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("A",0), ctermP At),(("B",0), ctermP Bt)] disjI2_vP)) h;
fun disjE_P (At,Bt,Ct) dThm cA cB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtP
        [(("A",0), ctermP At),(("B",0), ctermP Bt),(("C",0), ctermP Ct)] disjE_vP)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) cA) cB end;
fun oFalse_elim_P rT = beta_norm (Drule.infer_instantiate ctxtP [(("R",0), ctermP rT)] oFalse_elim_vP);
fun em_P t = beta_norm (Drule.infer_instantiate ctxtP [(("A",0), ctermP t)] ex_middle_vP);
fun allE_P Pabs at hF = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("P",0), ctermP Pabs),(("a",0), ctermP at)] allE_vP)) hF;
fun allI_P Pabs hAll = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("P",0), ctermP Pabs)] allI_vP)) hAll;
(* natlist universal *)
fun LallE_P Pabs at hF = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("P",0), ctermP Pabs),(("a",0), ctermP at)] LallE_vP)) hF;
fun LallI_P Pabs hAll = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("P",0), ctermP Pabs)] LallI_vP)) hAll;

fun leqRefl_P l = beta_norm (Drule.infer_instantiate ctxtP [(("a",0), ctermP l)] leq_refl_vP);
fun lprodNil_P () = lprod_nil_vP;
fun lprodCons_P (h,t) = beta_norm (Drule.infer_instantiate ctxtP
      [(("x",0), ctermP h),(("t",0), ctermP t)] lprod_cons_vP);
fun lmemNilElim_P x = beta_norm (Drule.infer_instantiate ctxtP [(("x",0), ctermP x)] lmem_nil_elim_vP);
fun lmemConsFwd_P (x,y,t) = beta_norm (Drule.infer_instantiate ctxtP
      [(("x",0), ctermP x),(("y",0), ctermP y),(("t",0), ctermP t)] lmem_cons_fwd_vP);
fun lmemConsBwd_P (x,y,t) = beta_norm (Drule.infer_instantiate ctxtP
      [(("x",0), ctermP x),(("y",0), ctermP y),(("t",0), ctermP t)] lmem_cons_bwd_vP);
fun lremoveNil_P x = beta_norm (Drule.infer_instantiate ctxtP [(("x",0), ctermP x)] lremove_nil_vP);
fun lremoveConsEq_P (x,y,t) = beta_norm (Drule.infer_instantiate ctxtP
      [(("x",0), ctermP x),(("y",0), ctermP y),(("t",0), ctermP t)] lremove_cons_eq_vP);
fun lremoveConsNeq_P (x,y,t) = beta_norm (Drule.infer_instantiate ctxtP
      [(("x",0), ctermP x),(("y",0), ctermP y),(("t",0), ctermP t)] lremove_cons_neq_vP);
fun lnodupConsFwd_P (x,t) = beta_norm (Drule.infer_instantiate ctxtP
      [(("x",0), ctermP x),(("t",0), ctermP t)] lnodup_cons_fwd_vP);
fun lnodupConsBwd_P (x,t) = beta_norm (Drule.infer_instantiate ctxtP
      [(("x",0), ctermP x),(("t",0), ctermP t)] lnodup_cons_bwd_vP);
fun multcomm_P (mt,nt) = beta_norm (Drule.infer_instantiate ctxtP
      [(("m",0), ctermP mt),(("n",0), ctermP nt)] mult_comm_vP);
fun multassoc_P (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtP
      [(("m",0), ctermP mt),(("n",0), ctermP nt),(("k",0), ctermP kt)] mult_assoc_vP);
fun mult_cong_r_P (hT,pT,qT) hpq =
  let val zf = Free("zmcr", natT)
      val Pabs = Term.lambda zf (oeq (mult hT pT) (mult hT zf))
      val inst = beta_norm (Drule.infer_instantiate ctxtP
            [(("P",0), ctermP Pabs),(("a",0), ctermP pT),(("b",0), ctermP qT)]
            (varify oeq_subst))
  in inst OF [hpq, oeqRefl_P (mult hT pT)] end;
fun mult_cong_l_P (pT,qT,kT) hpq =
  let val zf = Free("zmcl", natT)
      val Pabs = Term.lambda zf (oeq (mult pT kT) (mult zf kT))
      val inst = beta_norm (Drule.infer_instantiate ctxtP
            [(("P",0), ctermP Pabs),(("a",0), ctermP pT),(("b",0), ctermP qT)]
            (varify oeq_subst))
  in inst OF [hpq, oeqRefl_P (mult pT kT)] end;
fun lprod_cong_P (aT,bT) hab =
  let val zf = Free("zlpc", natlistT)
      val Pabs = Term.lambda zf (oeq (lprod aT) (lprod zf))
      val inst = beta_norm (Drule.infer_instantiate ctxtP
            [(("P",0), ctermP Pabs),(("a",0), ctermP aT),(("b",0), ctermP bT)] leq_subst_vP)
  in inst OF [hab, oeqRefl_P (lprod aT)] end;
fun lmem_transfer_P (yT,aT,bT) hleq hmem =
  let val zf = Free("zlmt", natlistT)
      val Pabs = Term.lambda zf (lmem yT zf)
      val inst = beta_norm (Drule.infer_instantiate ctxtP
            [(("P",0), ctermP Pabs),(("a",0), ctermP aT),(("b",0), ctermP bT)] leq_subst_vP)
  in inst OF [hleq, hmem] end;

(* derived-lemma applicators on ctxtP -- ALL are META implications (proved by
   Thm.implies_intr), so apply with Thm.implies_elim, NOT mp_P. *)
fun extract_P (xt,Lt) hmem =
  Thm.implies_elim
    (beta_norm (Drule.infer_instantiate ctxtP [(("x",0), ctermP xt),(("L",0), ctermP Lt)] extract_vP)) hmem;
fun mem_remove_fwd_P (yt,xt,Lt) hmem =
  Thm.implies_elim
    (beta_norm (Drule.infer_instantiate ctxtP
      [(("y",0), ctermP yt),(("x",0), ctermP xt),(("L",0), ctermP Lt)] mem_remove_fwd_vP)) hmem;
fun mem_remove_bwd_P (yt,xt,Lt) hconj =
  Thm.implies_elim
    (beta_norm (Drule.infer_instantiate ctxtP
      [(("y",0), ctermP yt),(("x",0), ctermP xt),(("L",0), ctermP Lt)] mem_remove_bwd_vP)) hconj;
fun mem_remove_neq_P (yt,xt,Lt) hnd hmem =  (* META impl: lnodup L ==> lmem y (lremove x L) ==> neg(oeq y x) *)
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("y",0), ctermP yt),(("x",0), ctermP xt),(("L",0), ctermP Lt)] mem_remove_neq_vP)) hnd) hmem;
fun nodup_remove_P (xt,Lt) hnd =
  Thm.implies_elim
    (beta_norm (Drule.infer_instantiate ctxtP
      [(("x",0), ctermP xt),(("L",0), ctermP Lt)] nodup_remove_vP)) hnd;

val () = out "PERM_INV_HELPERS_READY\n";

(* ---- object member-equivalence predicate : mem_eq L M (Conj of two Imps) ---- *)
fun mem_eq_pred L M =
  let val xv = Free("me_x", natT)
  in Term.lambda xv (mkConj (mkImp (lmem xv L) (lmem xv M)) (mkImp (lmem xv M) (lmem xv L))) end;
fun mem_eq L M = mkForall (mem_eq_pred L M);
fun mem_eq_fwd (L,M) hme x (hmem:thm) =
  let val inst = allE_P (mem_eq_pred L M) x hme
      val c1   = conjunct1_P (mkImp (lmem x L)(lmem x M), mkImp (lmem x M)(lmem x L)) inst
  in mp_P (lmem x L, lmem x M) c1 hmem end;
fun mem_eq_bwd (L,M) hme x (hmem:thm) =
  let val inst = allE_P (mem_eq_pred L M) x hme
      val c2   = conjunct2_P (mkImp (lmem x L)(lmem x M), mkImp (lmem x M)(lmem x L)) inst
  in mp_P (lmem x M, lmem x L) c2 hmem end;
val () = out "PERM_INV_MEMEQ_READY\n";

(* ---- no_mem z == Forall(%x. neg(lmem x z)) ; no_mem_nil : no_mem L ==> leq L lnil ---- *)
fun no_mem_pred z = let val xv = Free("nm_x", natT) in Term.lambda xv (neg (lmem xv z)) end;
fun no_mem z = mkForall (no_mem_pred z);

val no_mem_nil_P =
  let
    fun concBody zt = mkImp (no_mem zt) (leq zt lnilC);
    val zPv = Free("z_nm", natlistT);
    val Qpred = Term.lambda zPv (concBody zPv);
    val LF = Free("L_nmn", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtP
          [(("P",0), ctermP Qpred), (("a",0), ctermP LF)] list_induct_vP);
    val base =
      let val refl = leqRefl_P lnilC
      in impI_P (no_mem lnilC, leq lnilC lnilC)
           (Thm.implies_intr (ctermP (jT (no_mem lnilC))) refl) end;
    val hF = Free("h_nmn", natT); val tF = Free("t_nmn", natlistT);
    val ihprop = jT (concBody tF);
    val IH = Thm.assume (ctermP ihprop);
    val stepConcl =
      let
        val hnm = Thm.assume (ctermP (jT (no_mem (lcons hF tF))));
        val negMemH = allE_P (no_mem_pred (lcons hF tF)) hF hnm;
        val hhrefl = oeqRefl_P hF;
        val dj     = disjI1_P (oeq hF hF, lmem hF tF) hhrefl;
        val memH   = Thm.implies_elim (lmemConsBwd_P (hF, hF, tF)) dj;
        val ff     = mp_P (lmem hF (lcons hF tF), oFalseC) negMemH memH;
        val conc   = Thm.implies_elim (oFalse_elim_P (leq (lcons hF tF) lnilC)) ff;
      in impI_P (no_mem (lcons hF tF), leq (lcons hF tF) lnilC)
           (Thm.implies_intr (ctermP (jT (no_mem (lcons hF tF)))) conc) end;
    val step1 = Thm.forall_intr (ctermP hF)
                  (Thm.forall_intr (ctermP tF) (Thm.implies_intr (ctermP ihprop) stepConcl));
    val r2 = Thm.implies_elim (Thm.implies_elim ind base) step1;
    val hnmL = Thm.assume (ctermP (jT (no_mem LF)));
    val concL = mp_P (no_mem LF, leq LF lnilC) r2 hnmL;
  in varify (Thm.implies_intr (ctermP (jT (no_mem LF))) concL) end;
val () = out "OK no_mem_nil\n";
val no_mem_nil_Pv = varify no_mem_nil_P;
fun no_mem_nil_at_P Lt hnm =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtP
      [(("L_nmn",0), ctermP Lt)] no_mem_nil_Pv)) hnm;
val () = out "NO_MEM_NIL_READY\n";

(* ============================================================================
   lprod_perm — structural list_induct on L1; second list M via LForall.
   ============================================================================ *)
val lprod_perm =
  let
    fun innerPred zL =
      let val Mv = Free("M_inner", natlistT)
      in Term.lambda Mv (mkImp (lnodup Mv) (mkImp (mem_eq zL Mv) (oeq (lprod zL) (lprod Mv)))) end;
    fun Qbody zL = mkImp (lnodup zL) (mkLForall (innerPred zL));
    val zPv = Free("z_q", natlistT);
    val Qpred = Term.lambda zPv (Qbody zPv);
    val L1F = Free("L1", natlistT);
    val ind = beta_norm (Drule.infer_instantiate ctxtP
          [(("P",0), ctermP Qpred), (("a",0), ctermP L1F)] list_induct_vP);

    (* ---- BASE : Q lnil ---- *)
    val base =
      let
        val hndNil = Thm.assume (ctermP (jT (lnodup lnilC)));
        val MF = Free("M_base", natlistT);
        val perM =
          let
            val hndM = Thm.assume (ctermP (jT (lnodup MF)));
            val hme  = Thm.assume (ctermP (jT (mem_eq lnilC MF)));
            val noMemMF =
              let val yf = Free("y_nm_b", natT)
                  val hy = Thm.assume (ctermP (jT (lmem yf MF)))
                  val inNil = mem_eq_bwd (lnilC, MF) hme yf hy
                  val ff = Thm.implies_elim (lmemNilElim_P yf) inNil
                  val negy = impI_P (lmem yf MF, oFalseC)
                                (Thm.implies_intr (ctermP (jT (lmem yf MF))) ff)
                  val Pabs = no_mem_pred MF
              in allI_P Pabs (Thm.forall_intr (ctermP yf) negy) end;
            val leqMFnil = no_mem_nil_at_P MF noMemMF;
            val lpcong = lprod_cong_P (MF, lnilC) leqMFnil;
            val conc = oeq_sym OF [lpcong];
            val body = impI_P (mem_eq lnilC MF, oeq (lprod lnilC) (lprod MF))
                          (Thm.implies_intr (ctermP (jT (mem_eq lnilC MF))) conc)
            val body2 = impI_P (lnodup MF, mkImp (mem_eq lnilC MF) (oeq (lprod lnilC) (lprod MF)))
                          (Thm.implies_intr (ctermP (jT (lnodup MF))) body)
          in body2 end;
        val forallM = LallI_P (innerPred lnilC) (Thm.forall_intr (ctermP MF) perM);
      in impI_P (lnodup lnilC, mkLForall (innerPred lnilC))
           (Thm.implies_intr (ctermP (jT (lnodup lnilC))) forallM) end;

    (* ---- STEP : Q rest ==> Q (lcons a rest) ---- *)
    val aF = Free("a_s", natT); val restF = Free("rest_s", natlistT);
    val ihprop = jT (Qbody restF);
    val IH = Thm.assume (ctermP ihprop);
    val L1cons = lcons aF restF;
    val stepConcl =
      let
        val hndL1 = Thm.assume (ctermP (jT (lnodup L1cons)));
        val cjL1  = Thm.implies_elim (lnodupConsFwd_P (aF, restF)) hndL1;
        val a_notin_rest = conjunct1_P (neg (lmem aF restF), lnodup restF) cjL1;
        val hnd_rest = conjunct2_P (neg (lmem aF restF), lnodup restF) cjL1;
        val ihForall = mp_P (lnodup restF, mkLForall (innerPred restF)) IH hnd_rest;
        val MF = Free("M_step", natlistT);
        val perM =
          let
            val hndM = Thm.assume (ctermP (jT (lnodup MF)));
            val hme  = Thm.assume (ctermP (jT (mem_eq L1cons MF)));
            val memA_L1 = Thm.implies_elim (lmemConsBwd_P (aF, aF, restF))
                            (disjI1_P (oeq aF aF, lmem aF restF) (oeqRefl_P aF));
            val memA_M  = mem_eq_fwd (L1cons, MF) hme aF memA_L1;
            val extr    = extract_P (aF, MF) memA_M;
            val lpc     = lprodCons_P (aF, restF);
            val R       = lremove aF MF;
            val ihAt = LallE_P (innerPred restF) R ihForall;
            val ndR  = nodup_remove_P (aF, MF) hndM;
            val meRestR =
              let val yf = Free("y_me", natT)
                  val fwd =
                    let val hyr = Thm.assume (ctermP (jT (lmem yf restF)))
                        val memY_L1 = Thm.implies_elim (lmemConsBwd_P (yf, aF, restF))
                                        (disjI2_P (oeq yf aF, lmem yf restF) hyr)
                        val memY_M  = mem_eq_fwd (L1cons, MF) hme yf memY_L1
                        val yneqa =
                          let val hya = Thm.assume (ctermP (jT (oeq yf aF)))
                              val Pr = let val zf = Free("zyn", natT) in Term.lambda zf (lmem zf restF) end
                              val inst = beta_norm (Drule.infer_instantiate ctxtP
                                          [(("P",0), ctermP Pr),(("a",0), ctermP yf),(("b",0), ctermP aF)] (varify oeq_subst))
                              val memArest = inst OF [hya, hyr]
                              val ff = mp_P (lmem aF restF, oFalseC) a_notin_rest memArest
                          in impI_P (oeq yf aF, oFalseC)
                               (Thm.implies_intr (ctermP (jT (oeq yf aF))) ff) end
                        val cj = conjI_P (lmem yf MF, neg (oeq yf aF)) memY_M yneqa
                        val memY_R = mem_remove_bwd_P (yf, aF, MF) cj
                    in Thm.implies_intr (ctermP (jT (lmem yf restF))) memY_R end;
                  val bwd =
                    let val hyR = Thm.assume (ctermP (jT (lmem yf R)))
                        val memY_M = mem_remove_fwd_P (yf, aF, MF) hyR
                        val memY_L1 = mem_eq_bwd (L1cons, MF) hme yf memY_M
                        val dj = Thm.implies_elim (lmemConsFwd_P (yf, aF, restF)) memY_L1
                        val yneqa = mem_remove_neq_P (yf, aF, MF) hndM hyR
                        val cA = let val hya = Thm.assume (ctermP (jT (oeq yf aF)))
                                     val ff  = mp_P (oeq yf aF, oFalseC) yneqa hya
                                     val r   = Thm.implies_elim (oFalse_elim_P (lmem yf restF)) ff
                                 in Thm.implies_intr (ctermP (jT (oeq yf aF))) r end
                        val cB = let val hm = Thm.assume (ctermP (jT (lmem yf restF)))
                                 in Thm.implies_intr (ctermP (jT (lmem yf restF))) hm end
                        val res = disjE_P (oeq yf aF, lmem yf restF, lmem yf restF) dj cA cB
                    in Thm.implies_intr (ctermP (jT (lmem yf R))) res end;
                  val cjBoth = conjI_P (mkImp (lmem yf restF)(lmem yf R), mkImp (lmem yf R)(lmem yf restF))
                                  (impI_P (lmem yf restF, lmem yf R) fwd)
                                  (impI_P (lmem yf R, lmem yf restF) bwd)
                  val Pabs = mem_eq_pred restF R
              in allI_P Pabs (Thm.forall_intr (ctermP yf) cjBoth) end;
            val ih1  = mp_P (lnodup R, mkImp (mem_eq restF R) (oeq (lprod restF) (lprod R))) ihAt ndR;
            val ih_eq = mp_P (mem_eq restF R, oeq (lprod restF) (lprod R)) ih1 meRestR;
            val cong_a = mult_cong_r_P (aF, lprod restF, lprod R) ih_eq;
            val extr_s = oeq_sym OF [extr];
            val conc = oeq_trans OF [oeq_trans OF [lpc, cong_a], extr_s];
            val body = impI_P (mem_eq L1cons MF, oeq (lprod L1cons) (lprod MF))
                          (Thm.implies_intr (ctermP (jT (mem_eq L1cons MF))) conc)
            val body2 = impI_P (lnodup MF, mkImp (mem_eq L1cons MF) (oeq (lprod L1cons) (lprod MF)))
                          (Thm.implies_intr (ctermP (jT (lnodup MF))) body)
          in body2 end;
        val forallM = LallI_P (innerPred L1cons) (Thm.forall_intr (ctermP MF) perM);
      in impI_P (lnodup L1cons, mkLForall (innerPred L1cons))
           (Thm.implies_intr (ctermP (jT (lnodup L1cons))) forallM) end;

    val step1 = Thm.forall_intr (ctermP aF)
                  (Thm.forall_intr (ctermP restF) (Thm.implies_intr (ctermP ihprop) stepConcl));
    val r2 = Thm.implies_elim (Thm.implies_elim ind base) step1;
    val L2F = Free("L2", natlistT);
    val hndL1 = Thm.assume (ctermP (jT (lnodup L1F)));
    val forallM = mp_P (lnodup L1F, mkLForall (innerPred L1F)) r2 hndL1;
    val atL2 = LallE_P (innerPred L1F) L2F forallM;
    val hndL2 = Thm.assume (ctermP (jT (lnodup L2F)));
    val step_b = mp_P (lnodup L2F, mkImp (mem_eq L1F L2F) (oeq (lprod L1F) (lprod L2F))) atL2 hndL2;
    val hme = Thm.assume (ctermP (jT (mem_eq L1F L2F)));
    val final = mp_P (mem_eq L1F L2F, oeq (lprod L1F) (lprod L2F)) step_b hme;
    val d1 = Thm.implies_intr (ctermP (jT (lnodup L1F)))
               (Thm.implies_intr (ctermP (jT (lnodup L2F)))
                  (Thm.implies_intr (ctermP (jT (mem_eq L1F L2F))) final));
  in varify d1 end;
val () = out "OK lprod_perm\n";

val r_lprod_perm =
  let
    val L1V = Var(("L1",0), natlistT); val L2V = Var(("L2",0), natlistT);
    val intended = Logic.mk_implies (jT (lnodup L1V),
        Logic.mk_implies (jT (lnodup L2V),
          Logic.mk_implies (jT (mem_eq L1V L2V), jT (oeq (lprod L1V) (lprod L2V)))));
    val nh = length (Thm.hyps_of lprod_perm);
    val ac = (Thm.prop_of lprod_perm) aconv intended;
  in if nh=0 andalso ac then true
     else (out ("FAIL lprod_perm hyps="^Int.toString nh^" aconv="^Bool.toString ac^"\n");
           out ("  got = "^Syntax.string_of_term ctxtP (Thm.prop_of lprod_perm)^"\n"); false) end;
val () = if r_lprod_perm then out "OK lprod_perm aconv intended\n" else out "FAIL lprod_perm aconv\n";

val probe_perm =
  let val L1V = Var(("L1",0), natlistT); val L2V = Var(("L2",0), natlistT);
      val bogus = Logic.mk_implies (jT (mem_eq L1V L2V), jT (oeq (lprod L1V) (lprod L2V)))
  in not ((Thm.prop_of lprod_perm) aconv bogus) end;
val () = if probe_perm then out "PROBE_OK lprod_perm keeps lnodup hyps\n"
         else out "PROBE_FAIL lprod_perm collapsed\n";

val () = if r_lprod_perm andalso probe_perm then out "PERM_INV_OK\n" else out "PERM_INV_FAILED\n";
(* ============================================================================
   SEAT reduced_residues0 : the REDUCED-RESIDUE LIST and Euler's phi.
   Route (i): gcdf via Euclid (rmod), coprime := oeq (gcdf a n) 1 (decidable).
   rfilter : filter uptoF keeping coprime; rrl n = rfilter n (uptoF (sub n 1));
   phi n = llen (rrl n).
   Prove: lnodup (rrl n), lmem_rrl characterization.
   Build on thyW (latest): add consts gcdf, coprime?, rfilter, rrl, phi.
   ============================================================================ *)

(* ---- (A) extend the theory with new consts ---- *)
val thyE0 = Sign.add_consts
  [(Binding.name "gcdf",    natT --> natT --> natT, NoSyn),
   (Binding.name "coprimeP", natT --> natT --> oT,  NoSyn),
   (Binding.name "rfilter", natT --> natlistT --> natlistT, NoSyn),
   (Binding.name "rrl",     natT --> natlistT, NoSyn),
   (Binding.name "phi",     natT --> natT, NoSyn)] thyW;

fun cnstE nm T = Const (Sign.full_name thyE0 (Binding.name nm), T);
val gcdfC    = cnstE "gcdf" (natT --> natT --> natT);   fun gcdf a b = gcdfC $ a $ b;
val coprimeC = cnstE "coprimeP" (natT --> natT --> oT); fun coprimeP a n = coprimeC $ a $ n;
val rfilterC = cnstE "rfilter" (natT --> natlistT --> natlistT); fun rfilter n l = rfilterC $ n $ l;
val rrlC     = cnstE "rrl" (natT --> natlistT);         fun rrl n = rrlC $ n;
val phiC     = cnstE "phi" (natT --> natT);             fun phi n = phiC $ n;

(* free vars for axiom statements *)
val aE = Free("a", natT); val bE = Free("b", natT); val nE = Free("n", natT);
val rE = Free("r", natT); val rsE = Free("rs", natlistT);

(* the decidable coprimality TEST (a pure oeq formula -> decidable) *)
fun coprime_test a n = oeq (gcdf a n) (suc ZeroC);

(* ---- gcdf : Euclid conditional axioms ----
     gcdf_zero : oeq (gcdf a Zero) a
     gcdf_step : 0 < b ==> oeq (gcdf a b) (gcdf b (rmod a b))   *)
val ((_,gcdf_zero_ax), thyE1) = Thm.add_axiom_global (Binding.name "gcdf_zero",
      jT (oeq (gcdf aE ZeroC) aE)) thyE0;
val ((_,gcdf_step_ax), thyE2) = Thm.add_axiom_global (Binding.name "gcdf_step",
      Logic.mk_implies (jT (lt ZeroC bE),
        jT (oeq (gcdf aE bE) (gcdf bE (rmod aE bE))))) thyE1;

(* ---- coprimeP : defining axiom  coprimeP a n = coprime_test a n  (as object iff
       we make it a plain oeq def at the formula level using oeq on a boolean...).
   Simpler: define coprimeP a n := the test FORMULA directly is awkward (o vs nat).
   Instead use coprimeP as an ABBREVIATION at ML level: coprime_test is the formula.
   We KEEP coprimeC as a const only for naming clarity but tie it by axiom
       coprime_def : coprimeP a n  <->  coprime_test a n   is also awkward (no iff).
   Cleanest: DROP the coprimeP const; the decidable test is coprime_test (an oeq).  *)

(* ---- rfilter : CONDITIONAL list-recursion (keep r iff coprime_test r n) ----
     rfilter_nil      : leq (rfilter n lnil) lnil
     rfilter_cons_in  : jT (coprime_test r n)       ==> leq (rfilter n (lcons r rs)) (lcons r (rfilter n rs))
     rfilter_cons_out : jT (neg (coprime_test r n)) ==> leq (rfilter n (lcons r rs)) (rfilter n rs)  *)
val ((_,rfilter_nil_ax), thyE3) = Thm.add_axiom_global (Binding.name "rfilter_nil",
      jT (leq (rfilter nE lnilC) lnilC)) thyE2;
val ((_,rfilter_cons_in_ax), thyE4) = Thm.add_axiom_global (Binding.name "rfilter_cons_in",
      Logic.mk_implies (jT (coprime_test rE nE),
        jT (leq (rfilter nE (lcons rE rsE)) (lcons rE (rfilter nE rsE))))) thyE3;
val ((_,rfilter_cons_out_ax), thyE5) = Thm.add_axiom_global (Binding.name "rfilter_cons_out",
      Logic.mk_implies (jT (neg (coprime_test rE nE)),
        jT (leq (rfilter nE (lcons rE rsE)) (rfilter nE rsE)))) thyE4;

(* ---- rrl : rrl n = rfilter n (uptoF (sub n 1)) ---- *)
val ((_,rrl_def_ax), thyE6) = Thm.add_axiom_global (Binding.name "rrl_def",
      jT (leq (rrl nE) (rfilter nE (uptoF (sub nE (suc ZeroC)))))) thyE5;

(* ---- phi : phi n = llen (rrl n) ---- *)
val ((_,phi_def_ax), thyE) = Thm.add_axiom_global (Binding.name "phi_def",
      jT (oeq (phi nE) (llen (rrl nE)))) thyE6;

val ctxtE  = Proof_Context.init_global thyE;
val ctermE = Thm.cterm_of ctxtE;
val () = out "RR_CONTEXT_READY\n";

(* ---- varify new axioms onto ctxtE ---- *)
val gcdf_zero_vE = varify gcdf_zero_ax;
val gcdf_step_vE = varify gcdf_step_ax;
val rfilter_nil_vE = varify rfilter_nil_ax;
val rfilter_cons_in_vE = varify rfilter_cons_in_ax;
val rfilter_cons_out_vE = varify rfilter_cons_out_ax;
val rrl_def_vE = varify rrl_def_ax;
val phi_def_vE = varify phi_def_ax;

(* basic sanity: 0-hyp + aconv intent *)
val () = if length (Thm.hyps_of gcdf_zero_vE) = 0 then out "OK gcdf_zero\n" else out "FAIL gcdf_zero\n";
val () = if length (Thm.hyps_of rfilter_nil_vE) = 0 then out "OK rfilter_nil\n" else out "FAIL rfilter_nil\n";
val () = if length (Thm.hyps_of rrl_def_vE) = 0 then out "OK rrl_def\n" else out "FAIL rrl_def\n";

val () = out "RR_PHASE1_DONE\n";

(* ============================================================================
   PHASE 2 : E-context combinators (mirror the W combinators on ctxtE).
   Reuse the schematic varified W lemmas (theory-monotone) via infer_instantiate ctxtE.
   ============================================================================ *)
(* prop-logic *)
fun mp_E (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("A",0), ctermE At),(("B",0), ctermE Bt)] mp_vW)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_E (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("A",0), ctermE At),(("B",0), ctermE Bt)] impI_vW)
  in Thm.implies_elim inst hImpThm end;
fun conjI_E (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("A",0), ctermE At),(("B",0), ctermE Bt)] conjI_vW)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_E (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtE
      [(("A",0), ctermE At),(("B",0), ctermE Bt)] conjunct1_vW)) h;
fun conjunct2_E (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtE
      [(("A",0), ctermE At),(("B",0), ctermE Bt)] conjunct2_vW)) h;
fun oFalse_elim_E rT = beta_norm (Drule.infer_instantiate ctxtE [(("R",0), ctermE rT)] oFalse_elim_vW);
fun disjE_E (At,Bt,Ct) dThm cA cB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("A",0), ctermE At),(("B",0), ctermE Bt),(("C",0), ctermE Ct)] disjE_vW)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) cA) cB end;
fun disjI1_E (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtE
      [(("A",0), ctermE At),(("B",0), ctermE Bt)] disjI1_vW)) h;
fun disjI2_E (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtE
      [(("A",0), ctermE At),(("B",0), ctermE Bt)] disjI2_vW)) h;
fun em_E t = beta_norm (Drule.infer_instantiate ctxtE [(("A",0), ctermE t)] ex_middle_vW);

(* list machinery on ctxtE *)
fun leq_rw_E (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("P",0), ctermE Pabs),(("a",0), ctermE aT),(("b",0), ctermE bT)] leq_subst_vW)
  in inst OF [hab, hPa] end;
fun lmem_transfer_E (yT, aT, bT) hleq hmem =
  let val Pabs = Abs("z", natlistT, lmem yT (Bound 0))
  in leq_rw_E (Pabs, aT, bT) hleq hmem end;
fun lnodup_transfer_E (aT, bT) hleq hnd =
  let val Pabs = Abs("z", natlistT, lnodup (Bound 0))
  in leq_rw_E (Pabs, aT, bT) hleq hnd end;
fun lmemNilElim_E x = beta_norm (Drule.infer_instantiate ctxtE [(("x",0), ctermE x)] lmem_nil_elim_vW);
fun lmemConsFwd_E (x,y,t) = beta_norm (Drule.infer_instantiate ctxtE
      [(("x",0), ctermE x),(("y",0), ctermE y),(("t",0), ctermE t)] lmem_cons_fwd_vW);
fun lmemConsBwd_E (x,y,t) = beta_norm (Drule.infer_instantiate ctxtE
      [(("x",0), ctermE x),(("y",0), ctermE y),(("t",0), ctermE t)] lmem_cons_bwd_vW);
fun lnodupConsFwd_E (x,t) = beta_norm (Drule.infer_instantiate ctxtE
      [(("x",0), ctermE x),(("t",0), ctermE t)] lnodup_cons_fwd_vW);
fun lnodupConsBwd_E (x,t) = beta_norm (Drule.infer_instantiate ctxtE
      [(("x",0), ctermE x),(("t",0), ctermE t)] lnodup_cons_bwd_vW);
val lnodupNil_E = lnodup_nil_vW;
fun list_induct_E (Pabs, LT) baseThm stepThm =
  let val ind = beta_norm (Drule.infer_instantiate ctxtE
        [(("P",0), ctermE Pabs),(("a",0), ctermE LT)] list_induct_vW)
  in Thm.implies_elim (Thm.implies_elim ind baseThm) stepThm end;

(* rfilter conditional axioms on ctxtE *)
fun rfilterNil_E nt = beta_norm (Drule.infer_instantiate ctxtE [(("n",0), ctermE nt)] rfilter_nil_vE);
fun rfilterIn_E (nt,rt,rst) hcond =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtE
      [(("n",0), ctermE nt),(("r",0), ctermE rt),(("rs",0), ctermE rst)] rfilter_cons_in_vE)) hcond;
fun rfilterOut_E (nt,rt,rst) hncond =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtE
      [(("n",0), ctermE nt),(("r",0), ctermE rt),(("rs",0), ctermE rst)] rfilter_cons_out_vE)) hncond;
fun rrlDef_E nt = beta_norm (Drule.infer_instantiate ctxtE [(("n",0), ctermE nt)] rrl_def_vE);

val () = out "RR_E_COMBINATORS_READY\n";

(* ============================================================================
   rfilter_sublist : lmem x (rfilter n L) ==> lmem x L   (BY list_induct on L)
   ============================================================================ *)
val rfilter_sublist =
  let
    val xF = Free("x", natT); val nF = Free("n", natT)
    fun concBody zt = mkImp (lmem xF (rfilter nF zt)) (lmem xF zt)
    val Qpred = Abs("z", natlistT, concBody (Bound 0))
    val LF = Free("L", natlistT)
    val base =
      let
        val hassm = Thm.assume (ctermE (jT (lmem xF (rfilter nF lnilC))))
        val lrn = rfilterNil_E nF                                   (* leq (rfilter n lnil) lnil *)
        val mem_lnil = lmem_transfer_E (xF, rfilter nF lnilC, lnilC) lrn hassm
        val ff  = Thm.implies_elim (lmemNilElim_E xF) mem_lnil
        val conc = Thm.implies_elim (oFalse_elim_E (lmem xF lnilC)) ff
        val dis  = Thm.implies_intr (ctermE (jT (lmem xF (rfilter nF lnilC)))) conc
      in impI_E (lmem xF (rfilter nF lnilC), lmem xF lnilC) dis end
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val ihprop = jT (concBody tF)
    val IH = Thm.assume (ctermE ihprop)
    val stepConcl =
      let
        val hassm = Thm.assume (ctermE (jT (lmem xF (rfilter nF (lcons hF tF)))))
        val cond = coprime_test hF nF
        (* case: h is coprime -> rfilter n (cons h t) = cons h (rfilter n t) *)
        val caseIn =
          let
            val hcond = Thm.assume (ctermE (jT cond))
            val lrw = rfilterIn_E (nF, hF, tF) hcond          (* leq (rfilter n (cons h t)) (cons h (rfilter n t)) *)
            val mem_cons = lmem_transfer_E (xF, rfilter nF (lcons hF tF), lcons hF (rfilter nF tF)) lrw hassm
            val dj = Thm.implies_elim (lmemConsFwd_E (xF, hF, rfilter nF tF)) mem_cons  (* Disj (oeq x h) (lmem x (rfilter n t)) *)
            val cA = let val hxh = Thm.assume (ctermE (jT (oeq xF hF)))
                         val r = Thm.implies_elim (lmemConsBwd_E (xF, hF, tF))
                                   (disjI1_E (oeq xF hF, lmem xF tF) hxh)
                     in Thm.implies_intr (ctermE (jT (oeq xF hF))) r end
            val cB = let val hmr = Thm.assume (ctermE (jT (lmem xF (rfilter nF tF))))
                         val mt = mp_E (lmem xF (rfilter nF tF), lmem xF tF) IH hmr
                         val r = Thm.implies_elim (lmemConsBwd_E (xF, hF, tF))
                                   (disjI2_E (oeq xF hF, lmem xF tF) mt)
                     in Thm.implies_intr (ctermE (jT (lmem xF (rfilter nF tF)))) r end
            val res = disjE_E (oeq xF hF, lmem xF (rfilter nF tF), lmem xF (lcons hF tF)) dj cA cB
          in Thm.implies_intr (ctermE (jT cond)) res end
        (* case: h not coprime -> rfilter n (cons h t) = rfilter n t *)
        val caseOut =
          let
            val hncond = Thm.assume (ctermE (jT (neg cond)))
            val lrw = rfilterOut_E (nF, hF, tF) hncond        (* leq (rfilter n (cons h t)) (rfilter n t) *)
            val mem_t' = lmem_transfer_E (xF, rfilter nF (lcons hF tF), rfilter nF tF) lrw hassm
            val mem_t  = mp_E (lmem xF (rfilter nF tF), lmem xF tF) IH mem_t'
            val dj = disjI2_E (oeq xF hF, lmem xF tF) mem_t
            val res = Thm.implies_elim (lmemConsBwd_E (xF, hF, tF)) dj
          in Thm.implies_intr (ctermE (jT (neg cond))) res end
        val em = em_E cond
        val conc = disjE_E (cond, neg cond, lmem xF (lcons hF tF)) em caseIn caseOut
        val dis = Thm.implies_intr (ctermE (jT (lmem xF (rfilter nF (lcons hF tF))))) conc
      in impI_E (lmem xF (rfilter nF (lcons hF tF)), lmem xF (lcons hF tF)) dis end
    val step = Thm.forall_intr (ctermE hF)
                 (Thm.forall_intr (ctermE tF) (Thm.implies_intr (ctermE ihprop) stepConcl))
    val concl = list_induct_E (Qpred, LF) base step  (* jT (concBody L) *)
  in varify concl end;
val () = if length (Thm.hyps_of rfilter_sublist) = 0 then out "OK rfilter_sublist\n" else out "FAIL rfilter_sublist\n";

(* application form of rfilter_sublist *)
val rfilter_sublist_vE = rfilter_sublist;
fun rfilter_sublist_E (xt,nt,Lt) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("x",0), ctermE xt),(("n",0), ctermE nt),(("L",0), ctermE Lt)] rfilter_sublist_vE)
  in mp_E (lmem xt (rfilter nt Lt), lmem xt Lt) inst hmem end;

(* leq_sym on ctxtE (via leq_subst) *)
fun leq_sym_E (aT,bT) hab =
  let val Pabs = Abs("z", natlistT, leq (Bound 0) aT)
      val refl_aa = beta_norm (Drule.infer_instantiate ctxtE [(("a",0), ctermE aT)] leq_refl_vW)
  in leq_rw_E (Pabs, aT, bT) hab refl_aa end;

val () = out "RR_PHASE2_DONE\n";

(* ============================================================================
   PHASE 3 : lnodup_rfilter : lnodup L ==> lnodup (rfilter n L)  (BY list_induct)
   then lnodup (rrl n).
   ============================================================================ *)
val lnodup_rfilter =
  let
    val nF = Free("n", natT)
    fun concBody zt = mkImp (lnodup zt) (lnodup (rfilter nF zt))
    val Qpred = Abs("z", natlistT, concBody (Bound 0))
    val LF = Free("L", natlistT)
    val base =
      let
        val hnd = Thm.assume (ctermE (jT (lnodup lnilC)))
        val lrn = rfilterNil_E nF                          (* leq (rfilter n lnil) lnil *)
        val lrn_s = leq_sym_E (rfilter nF lnilC, lnilC) lrn (* leq lnil (rfilter n lnil) *)
        val res = lnodup_transfer_E (lnilC, rfilter nF lnilC) lrn_s hnd
        val dis = Thm.implies_intr (ctermE (jT (lnodup lnilC))) res
      in impI_E (lnodup lnilC, lnodup (rfilter nF lnilC)) dis end
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val ihprop = jT (concBody tF)
    val IH = Thm.assume (ctermE ihprop)
    val stepConcl =
      let
        val hnd = Thm.assume (ctermE (jT (lnodup (lcons hF tF))))
        val cj  = Thm.implies_elim (lnodupConsFwd_E (hF, tF)) hnd
        val nmem = conjunct1_E (neg (lmem hF tF), lnodup tF) cj   (* neg (lmem h t) *)
        val ndt  = conjunct2_E (neg (lmem hF tF), lnodup tF) cj   (* lnodup t *)
        val ndrt = mp_E (lnodup tF, lnodup (rfilter nF tF)) IH ndt (* lnodup (rfilter n t) *)
        val cond = coprime_test hF nF
        val caseIn =
          let
            val hcond = Thm.assume (ctermE (jT cond))
            val lrw = rfilterIn_E (nF, hF, tF) hcond  (* leq (rfilter n (cons h t)) (cons h (rfilter n t)) *)
            (* h not in (rfilter n t) : because rfilter n t is sublist of t and h not in t *)
            val nmem_rt =
              let val hassm = Thm.assume (ctermE (jT (lmem hF (rfilter nF tF))))
                  val inT   = rfilter_sublist_E (hF, nF, tF) hassm   (* lmem h t *)
                  val ff    = mp_E (lmem hF tF, oFalseC) nmem inT
                  val dis   = Thm.implies_intr (ctermE (jT (lmem hF (rfilter nF tF)))) ff
              in impI_E (lmem hF (rfilter nF tF), oFalseC) dis end
            val cj2 = conjI_E (neg (lmem hF (rfilter nF tF)), lnodup (rfilter nF tF)) nmem_rt ndrt
            val nd_target = Thm.implies_elim (lnodupConsBwd_E (hF, rfilter nF tF)) cj2  (* lnodup (cons h (rfilter n t)) *)
            val lrw_s = leq_sym_E (rfilter nF (lcons hF tF), lcons hF (rfilter nF tF)) lrw
            val res = lnodup_transfer_E (lcons hF (rfilter nF tF), rfilter nF (lcons hF tF)) lrw_s nd_target
          in Thm.implies_intr (ctermE (jT cond)) res end
        val caseOut =
          let
            val hncond = Thm.assume (ctermE (jT (neg cond)))
            val lrw = rfilterOut_E (nF, hF, tF) hncond  (* leq (rfilter n (cons h t)) (rfilter n t) *)
            val lrw_s = leq_sym_E (rfilter nF (lcons hF tF), rfilter nF tF) lrw
            val res = lnodup_transfer_E (rfilter nF tF, rfilter nF (lcons hF tF)) lrw_s ndrt
          in Thm.implies_intr (ctermE (jT (neg cond))) res end
        val em = em_E cond
        val conc = disjE_E (cond, neg cond, lnodup (rfilter nF (lcons hF tF))) em caseIn caseOut
        val dis = Thm.implies_intr (ctermE (jT (lnodup (lcons hF tF)))) conc
      in impI_E (lnodup (lcons hF tF), lnodup (rfilter nF (lcons hF tF))) dis end
    val step = Thm.forall_intr (ctermE hF)
                 (Thm.forall_intr (ctermE tF) (Thm.implies_intr (ctermE ihprop) stepConcl))
    val concl = list_induct_E (Qpred, LF) base step
  in varify concl end;
val () = if length (Thm.hyps_of lnodup_rfilter) = 0 then out "OK lnodup_rfilter\n" else out "FAIL lnodup_rfilter\n";

val lnodup_rfilter_vE = lnodup_rfilter;
fun lnodup_rfilter_E (nt,Lt) hnd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("n",0), ctermE nt),(("L",0), ctermE Lt)] lnodup_rfilter_vE)
  in mp_E (lnodup Lt, lnodup (rfilter nt Lt)) inst hnd end;

(* ---- lnodup (rrl n) : rrl n = rfilter n (uptoF (sub n 1)); upto is nodup; rfilter preserves ---- *)
val lnodup_upto_E_v = lnodup_upto_vW;
fun lnodup_upto_E nt = beta_norm (Drule.infer_instantiate ctxtE [(("k_nd",0), ctermE nt)] lnodup_upto_E_v);

(* lnodup_upto_vW has the schematic form  lnodup (uptoF ?k_nd) ; instantiate k_nd := sub n 1 *)
val lnodup_rrl =
  let
    val nF = Free("n", natT)
    val rng = uptoF (sub nF (suc ZeroC))
    val nd_up  = lnodup_upto_E (sub nF (suc ZeroC))    (* lnodup (uptoF (sub n 1)) *)
    val nd_filt = lnodup_rfilter_E (nF, rng) nd_up      (* lnodup (rfilter n (uptoF (sub n 1))) *)
    val rdef = rrlDef_E nF                              (* leq (rrl n) (rfilter n (uptoF (sub n 1))) *)
    val rdef_s = leq_sym_E (rrl nF, rfilter nF rng) rdef (* leq (rfilter ...) (rrl n) *)
    val res = lnodup_transfer_E (rfilter nF rng, rrl nF) rdef_s nd_filt
  in varify res end;
val () = if length (Thm.hyps_of lnodup_rrl) = 0 then out "OK lnodup_rrl\n" else out "FAIL lnodup_rrl\n";

val () = out "RR_PHASE3_DONE\n";

(* ============================================================================
   PHASE 4 : membership characterization lmem_rrl.
   First on rfilter (both directions), then transfer to rrl.
   ============================================================================ *)
(* oeq-rewrite combinator + sym/refl on ctxtE *)
fun oeqRefl_E t = beta_norm (Drule.infer_instantiate ctxtE [(("a",0), ctermE t)] oeq_refl_vW);
fun oeq_rw_E (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("P",0), ctermE Pabs),(("a",0), ctermE aT),(("b",0), ctermE bT)] oeq_subst_vW)
  in inst OF [hab, hPa] end;
fun oeq_sym_E hab = oeq_sym_vW OF [hab];

(* ---- lmem_rfilter_fwd : lmem r (rfilter n L) ==> Conj (lmem r L)(coprime_test r n) ---- *)
val lmem_rfilter_fwd =
  let
    val rF = Free("r", natT); val nF = Free("n", natT)
    fun goalC zt = mkConj (lmem rF zt) (coprime_test rF nF)
    fun concBody zt = mkImp (lmem rF (rfilter nF zt)) (goalC zt)
    val Qpred = Abs("z", natlistT, concBody (Bound 0))
    val LF = Free("L", natlistT)
    val base =
      let
        val hassm = Thm.assume (ctermE (jT (lmem rF (rfilter nF lnilC))))
        val lrn = rfilterNil_E nF
        val mem_lnil = lmem_transfer_E (rF, rfilter nF lnilC, lnilC) lrn hassm
        val ff  = Thm.implies_elim (lmemNilElim_E rF) mem_lnil
        val conc = Thm.implies_elim (oFalse_elim_E (goalC lnilC)) ff
        val dis  = Thm.implies_intr (ctermE (jT (lmem rF (rfilter nF lnilC)))) conc
      in impI_E (lmem rF (rfilter nF lnilC), goalC lnilC) dis end
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val ihprop = jT (concBody tF)
    val IH = Thm.assume (ctermE ihprop)
    val stepConcl =
      let
        val hassm = Thm.assume (ctermE (jT (lmem rF (rfilter nF (lcons hF tF)))))
        val cond = coprime_test hF nF
        val caseIn =
          let
            val hcond = Thm.assume (ctermE (jT cond))
            val lrw = rfilterIn_E (nF, hF, tF) hcond
            val mem_cons = lmem_transfer_E (rF, rfilter nF (lcons hF tF), lcons hF (rfilter nF tF)) lrw hassm
            val dj = Thm.implies_elim (lmemConsFwd_E (rF, hF, rfilter nF tF)) mem_cons
            (* r = h case *)
            val cA =
              let val hrh = Thm.assume (ctermE (jT (oeq rF hF)))
                  val mem_rt = Thm.implies_elim (lmemConsBwd_E (rF, hF, tF))
                                 (disjI1_E (oeq rF hF, lmem rF tF) hrh)
                  (* coprime_test r n from coprime_test h n via r=h *)
                  val Pcop = Abs("z", natT, coprime_test (Bound 0) nF)  (* %z. oeq (gcdf z n) 1 *)
                  val hrh_s = oeq_sym_E hrh                              (* oeq h r *)
                  val cop_r = oeq_rw_E (Pcop, hF, rF) hrh_s hcond        (* coprime_test r n *)
                  val cj = conjI_E (lmem rF (lcons hF tF), coprime_test rF nF) mem_rt cop_r
              in Thm.implies_intr (ctermE (jT (oeq rF hF))) cj end
            (* lmem r (rfilter n t) case -> IH *)
            val cB =
              let val hmr = Thm.assume (ctermE (jT (lmem rF (rfilter nF tF))))
                  val cjt = mp_E (lmem rF (rfilter nF tF), goalC tF) IH hmr
                  val mem_t = conjunct1_E (lmem rF tF, coprime_test rF nF) cjt
                  val cop_r = conjunct2_E (lmem rF tF, coprime_test rF nF) cjt
                  val mem_cons2 = Thm.implies_elim (lmemConsBwd_E (rF, hF, tF))
                                    (disjI2_E (oeq rF hF, lmem rF tF) mem_t)
                  val cj = conjI_E (lmem rF (lcons hF tF), coprime_test rF nF) mem_cons2 cop_r
              in Thm.implies_intr (ctermE (jT (lmem rF (rfilter nF tF)))) cj end
            val res = disjE_E (oeq rF hF, lmem rF (rfilter nF tF), goalC (lcons hF tF)) dj cA cB
          in Thm.implies_intr (ctermE (jT cond)) res end
        val caseOut =
          let
            val hncond = Thm.assume (ctermE (jT (neg cond)))
            val lrw = rfilterOut_E (nF, hF, tF) hncond
            val mem_t' = lmem_transfer_E (rF, rfilter nF (lcons hF tF), rfilter nF tF) lrw hassm
            val cjt = mp_E (lmem rF (rfilter nF tF), goalC tF) IH mem_t'
            val mem_t = conjunct1_E (lmem rF tF, coprime_test rF nF) cjt
            val cop_r = conjunct2_E (lmem rF tF, coprime_test rF nF) cjt
            val mem_cons = Thm.implies_elim (lmemConsBwd_E (rF, hF, tF))
                             (disjI2_E (oeq rF hF, lmem rF tF) mem_t)
            val cj = conjI_E (lmem rF (lcons hF tF), coprime_test rF nF) mem_cons cop_r
          in Thm.implies_intr (ctermE (jT (neg cond))) cj end
        val em = em_E cond
        val conc = disjE_E (cond, neg cond, goalC (lcons hF tF)) em caseIn caseOut
        val dis = Thm.implies_intr (ctermE (jT (lmem rF (rfilter nF (lcons hF tF))))) conc
      in impI_E (lmem rF (rfilter nF (lcons hF tF)), goalC (lcons hF tF)) dis end
    val step = Thm.forall_intr (ctermE hF)
                 (Thm.forall_intr (ctermE tF) (Thm.implies_intr (ctermE ihprop) stepConcl))
    val concl = list_induct_E (Qpred, LF) base step
  in varify concl end;
val () = if length (Thm.hyps_of lmem_rfilter_fwd) = 0 then out "OK lmem_rfilter_fwd\n" else out "FAIL lmem_rfilter_fwd\n";

val () = out "RR_PHASE4A_DONE\n";

(* ---- lmem_rfilter_bwd : Conj (lmem r L)(coprime_test r n) ==> lmem r (rfilter n L) ---- *)
val lmem_rfilter_bwd =
  let
    val rF = Free("r", natT); val nF = Free("n", natT)
    fun hypC zt = mkConj (lmem rF zt) (coprime_test rF nF)
    fun concBody zt = mkImp (hypC zt) (lmem rF (rfilter nF zt))
    val Qpred = Abs("z", natlistT, concBody (Bound 0))
    val LF = Free("L", natlistT)
    val base =
      let
        val hcj = Thm.assume (ctermE (jT (hypC lnilC)))
        val mem = conjunct1_E (lmem rF lnilC, coprime_test rF nF) hcj
        val ff  = Thm.implies_elim (lmemNilElim_E rF) mem
        val conc = Thm.implies_elim (oFalse_elim_E (lmem rF (rfilter nF lnilC))) ff
        val dis = Thm.implies_intr (ctermE (jT (hypC lnilC))) conc
      in impI_E (hypC lnilC, lmem rF (rfilter nF lnilC)) dis end
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val ihprop = jT (concBody tF)
    val IH = Thm.assume (ctermE ihprop)
    val stepConcl =
      let
        val hcj  = Thm.assume (ctermE (jT (hypC (lcons hF tF))))
        val memC = conjunct1_E (lmem rF (lcons hF tF), coprime_test rF nF) hcj
        val cop_r= conjunct2_E (lmem rF (lcons hF tF), coprime_test rF nF) hcj
        val dj   = Thm.implies_elim (lmemConsFwd_E (rF, hF, tF)) memC   (* Disj (oeq r h)(lmem r t) *)
        val cond = coprime_test hF nF
        val goalMem = lmem rF (rfilter nF (lcons hF tF))
        val caseIn =
          let
            val hcond = Thm.assume (ctermE (jT cond))
            val lrw = rfilterIn_E (nF, hF, tF) hcond  (* leq (rfilter n (cons h t)) (cons h (rfilter n t)) *)
            val lrw_s = leq_sym_E (rfilter nF (lcons hF tF), lcons hF (rfilter nF tF)) lrw
            (* prove lmem r (cons h (rfilter n t)) from dj, then transfer back *)
            val cA = let val hrh = Thm.assume (ctermE (jT (oeq rF hF)))
                         val m = Thm.implies_elim (lmemConsBwd_E (rF, hF, rfilter nF tF))
                                   (disjI1_E (oeq rF hF, lmem rF (rfilter nF tF)) hrh)
                     in Thm.implies_intr (ctermE (jT (oeq rF hF))) m end
            val cB = let val hmt = Thm.assume (ctermE (jT (lmem rF tF)))
                         val cjt = conjI_E (lmem rF tF, coprime_test rF nF) hmt cop_r
                         val mrt = mp_E (hypC tF, lmem rF (rfilter nF tF)) IH cjt
                         val m = Thm.implies_elim (lmemConsBwd_E (rF, hF, rfilter nF tF))
                                   (disjI2_E (oeq rF hF, lmem rF (rfilter nF tF)) mrt)
                     in Thm.implies_intr (ctermE (jT (lmem rF tF))) m end
            val memCons = disjE_E (oeq rF hF, lmem rF tF, lmem rF (lcons hF (rfilter nF tF))) dj cA cB
            val res = lmem_transfer_E (rF, lcons hF (rfilter nF tF), rfilter nF (lcons hF tF)) lrw_s memCons
          in Thm.implies_intr (ctermE (jT cond)) res end
        val caseOut =
          let
            val hncond = Thm.assume (ctermE (jT (neg cond)))
            val lrw = rfilterOut_E (nF, hF, tF) hncond (* leq (rfilter n (cons h t)) (rfilter n t) *)
            val lrw_s = leq_sym_E (rfilter nF (lcons hF tF), rfilter nF tF) lrw
            (* r=h would contradict hncond ; r in t -> IH *)
            val cA = let val hrh = Thm.assume (ctermE (jT (oeq rF hF)))
                         (* coprime_test h n from coprime_test r n via oeq r h *)
                         val Pcop = Abs("z", natT, coprime_test (Bound 0) nF)
                         val cop_h = oeq_rw_E (Pcop, rF, hF) hrh cop_r   (* coprime_test h n *)
                         val ff = mp_E (cond, oFalseC) hncond cop_h
                         val m  = Thm.implies_elim (oFalse_elim_E (lmem rF (rfilter nF tF))) ff
                     in Thm.implies_intr (ctermE (jT (oeq rF hF))) m end
            val cB = let val hmt = Thm.assume (ctermE (jT (lmem rF tF)))
                         val cjt = conjI_E (lmem rF tF, coprime_test rF nF) hmt cop_r
                         val mrt = mp_E (hypC tF, lmem rF (rfilter nF tF)) IH cjt
                     in Thm.implies_intr (ctermE (jT (lmem rF tF))) mrt end
            val memT = disjE_E (oeq rF hF, lmem rF tF, lmem rF (rfilter nF tF)) dj cA cB
            val res = lmem_transfer_E (rF, rfilter nF tF, rfilter nF (lcons hF tF)) lrw_s memT
          in Thm.implies_intr (ctermE (jT (neg cond))) res end
        val em = em_E cond
        val conc = disjE_E (cond, neg cond, goalMem) em caseIn caseOut
        val dis = Thm.implies_intr (ctermE (jT (hypC (lcons hF tF)))) conc
      in impI_E (hypC (lcons hF tF), goalMem) dis end
    val step = Thm.forall_intr (ctermE hF)
                 (Thm.forall_intr (ctermE tF) (Thm.implies_intr (ctermE ihprop) stepConcl))
    val concl = list_induct_E (Qpred, LF) base step
  in varify concl end;
val () = if length (Thm.hyps_of lmem_rfilter_bwd) = 0 then out "OK lmem_rfilter_bwd\n" else out "FAIL lmem_rfilter_bwd\n";

val () = out "RR_PHASE4B_DONE\n";

(* application forms of the rfilter characterization *)
val lmem_rfilter_fwd_vE = lmem_rfilter_fwd;
val lmem_rfilter_bwd_vE = lmem_rfilter_bwd;
fun lmem_rfilter_fwd_E (rt,nt,Lt) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("r",0), ctermE rt),(("n",0), ctermE nt),(("L",0), ctermE Lt)] lmem_rfilter_fwd_vE)
  in mp_E (lmem rt (rfilter nt Lt), mkConj (lmem rt Lt)(coprime_test rt nt)) inst hmem end;
fun lmem_rfilter_bwd_E (rt,nt,Lt) hcj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtE
        [(("r",0), ctermE rt),(("n",0), ctermE nt),(("L",0), ctermE Lt)] lmem_rfilter_bwd_vE)
  in mp_E (mkConj (lmem rt Lt)(coprime_test rt nt), lmem rt (rfilter nt Lt)) inst hcj end;

(* ============================================================================
   PHASE 5 : lmem_rrl (both directions), via rrl_def transfer.
   rng = uptoF (sub n 1).  rrl n leq rfilter n rng.
   ============================================================================ *)
val lmem_rrl_fwd =
  let
    val rF = Free("r", natT); val nF = Free("n", natT)
    val rng = uptoF (sub nF (suc ZeroC))
    val goalC = mkConj (lmem rF rng) (coprime_test rF nF)
    val hmemP = jT (lmem rF (rrl nF))
    val hmem  = Thm.assume (ctermE hmemP)
    val rdef  = rrlDef_E nF                                  (* leq (rrl n)(rfilter n rng) *)
    val mem_rf= lmem_transfer_E (rF, rrl nF, rfilter nF rng) rdef hmem  (* lmem r (rfilter n rng) *)
    val cj    = lmem_rfilter_fwd_E (rF, nF, rng) mem_rf      (* Conj (lmem r rng)(coprime r n) *)
    val res   = Thm.implies_intr (ctermE hmemP) cj
  in varify res end;
val () = if length (Thm.hyps_of lmem_rrl_fwd) = 0 then out "OK lmem_rrl_fwd\n" else out "FAIL lmem_rrl_fwd\n";

val lmem_rrl_bwd =
  let
    val rF = Free("r", natT); val nF = Free("n", natT)
    val rng = uptoF (sub nF (suc ZeroC))
    val hypC = mkConj (lmem rF rng) (coprime_test rF nF)
    val hcj  = Thm.assume (ctermE (jT hypC))
    val mem_rf = lmem_rfilter_bwd_E (rF, nF, rng) hcj         (* lmem r (rfilter n rng) *)
    val rdef = rrlDef_E nF                                    (* leq (rrl n)(rfilter n rng) *)
    val rdef_s = leq_sym_E (rrl nF, rfilter nF rng) rdef      (* leq (rfilter n rng)(rrl n) *)
    val res_mem = lmem_transfer_E (rF, rfilter nF rng, rrl nF) rdef_s mem_rf  (* lmem r (rrl n) *)
    val res = Thm.implies_intr (ctermE (jT hypC)) res_mem
  in varify res end;
val () = if length (Thm.hyps_of lmem_rrl_bwd) = 0 then out "OK lmem_rrl_bwd\n" else out "FAIL lmem_rrl_bwd\n";

val () = out "OK lmem_rrl\n";
val () = out "RR_PHASE5_DONE\n";

(* ============================================================================
   FINAL VALIDATION : statements aconv intent, 0-hyp, soundness probes.
   ============================================================================ *)
val () = out "RR_VALIDATE_BEGIN\n";
val rV = Var(("r",0),natT); val nV = Var(("n",0),natT); val LV = Var(("L",0),natlistT);
fun coprime_testV a n = oeq (gcdf a n) (suc ZeroC);

(* intended statements *)
val lnodup_rrl_intended = jT (lnodup (rrl nV));
val lmem_rrl_fwd_intended =
  Logic.mk_implies (jT (lmem rV (rrl nV)),
    jT (mkConj (lmem rV (uptoF (sub nV (suc ZeroC)))) (coprime_testV rV nV)));
val lmem_rrl_bwd_intended =
  Logic.mk_implies (jT (mkConj (lmem rV (uptoF (sub nV (suc ZeroC)))) (coprime_testV rV nV)),
    jT (lmem rV (rrl nV)));
(* rfilter_sublist came out of list_induct as a single Trueprop wrapping object Imp;
   its Vars are named x (element), n (modulus), L (list). *)
val xVsub = Var(("x",0),natT);
val rfilter_sublist_intended =
  jT (mkImp (lmem xVsub (rfilter nV LV)) (lmem xVsub LV));

val r_nd = (length (Thm.hyps_of lnodup_rrl) = 0)
           andalso ((Thm.prop_of lnodup_rrl) aconv lnodup_rrl_intended);
val () = if r_nd then out "VALID lnodup_rrl aconv intended\n" else out "INVALID lnodup_rrl\n";

val r_fwd = (length (Thm.hyps_of lmem_rrl_fwd) = 0)
            andalso ((Thm.prop_of lmem_rrl_fwd) aconv lmem_rrl_fwd_intended);
val () = if r_fwd then out "VALID lmem_rrl_fwd aconv intended\n" else out "INVALID lmem_rrl_fwd\n";

val r_bwd = (length (Thm.hyps_of lmem_rrl_bwd) = 0)
            andalso ((Thm.prop_of lmem_rrl_bwd) aconv lmem_rrl_bwd_intended);
val () = if r_bwd then out "VALID lmem_rrl_bwd aconv intended\n" else out "INVALID lmem_rrl_bwd\n";

val r_sub = (length (Thm.hyps_of rfilter_sublist) = 0)
            andalso ((Thm.prop_of rfilter_sublist) aconv rfilter_sublist_intended);
val () = if r_sub then out "VALID rfilter_sublist aconv intended\n" else out "INVALID rfilter_sublist\n";

(* SOUNDNESS PROBE 1 : lmem_rrl_fwd genuinely CARRIES the coprime condition.
   A bogus statement that DROPS coprime_test must NOT match. *)
val probe_fwd_drops_coprime =
  let val bogus = Logic.mk_implies (jT (lmem rV (rrl nV)),
                    jT (lmem rV (uptoF (sub nV (suc ZeroC)))))
  in not ((Thm.prop_of lmem_rrl_fwd) aconv bogus) end;
val () = if probe_fwd_drops_coprime then out "PROBE_OK fwd keeps coprime_test\n"
         else out "PROBE_FAIL fwd dropped coprime\n";

(* SOUNDNESS PROBE 2 : lmem_rrl_fwd keeps the range condition (not trivially true). *)
val probe_fwd_keeps_range =
  let val bogus = Logic.mk_implies (jT (lmem rV (rrl nV)), jT (coprime_testV rV nV))
  in not ((Thm.prop_of lmem_rrl_fwd) aconv bogus) end;
val () = if probe_fwd_keeps_range then out "PROBE_OK fwd keeps range\n"
         else out "PROBE_FAIL fwd dropped range\n";

(* SOUNDNESS PROBE 3 : bwd genuinely REQUIRES coprime (a bogus dropping it must not match). *)
val probe_bwd_requires_coprime =
  let val bogus = Logic.mk_implies (jT (lmem rV (uptoF (sub nV (suc ZeroC)))),
                    jT (lmem rV (rrl nV)))
  in not ((Thm.prop_of lmem_rrl_bwd) aconv bogus) end;
val () = if probe_bwd_requires_coprime then out "PROBE_OK bwd requires coprime\n"
         else out "PROBE_FAIL bwd dropped coprime\n";

(* coprime test well-definedness : gcdf axioms 0-hyp and the test is the named oeq *)
val r_cop_def =
  (length (Thm.hyps_of gcdf_zero_vE) = 0) andalso (length (Thm.hyps_of gcdf_step_vE) = 0);
val () = if r_cop_def then out "OK coprime_def\n" else out "FAIL coprime_def\n";
val () = out "OK rrl\n";

val () =
  if r_nd andalso r_fwd andalso r_bwd andalso r_sub
     andalso probe_fwd_drops_coprime andalso probe_fwd_keeps_range
     andalso probe_bwd_requires_coprime andalso r_cop_def
  then out "REDUCED_RES_OK\n"
  else out "REDUCED_RES_FAILED\n";
(* ============================================================================
   EULER PHASE 1 (seat bj0) : the unit group + multiply-by-a bijection.
   Build directly on the W-context machinery (finv/fsearch/searchCond/cong all
   live in thyW ⊆ thyE; the _W accessors work with global-constructor terms).
   ============================================================================ *)
val () = out "BJ0_START\n";

(* unit_test n r := oeq (rmod (mult r (finv n r)) n) (Suc Zero)  = searchCond n r (finv n r) *)
fun unit_test n r = searchCond n r (finv n r);

(* ---------------------------------------------------------------------------
   unit_has_inv : 1<n ==> unit_test n r ==> cong n (mult r (finv n r)) 1
   (searchCond n r (finv n r)  ===scond_imp_cong===>  cong n (r*finv n r) 1)
   --------------------------------------------------------------------------- *)
val unit_has_inv =
  let
    val nF = Free("n", natT); val rF = Free("r", natT)
    val one = suc ZeroC
    val hp1P = jT (lt one nF) ; val hp1 = Thm.assume (ctermW hp1P)
    val hutP = jT (unit_test nF rF) ; val hut = Thm.assume (ctermW hutP)
    (* searchCond n r (finv n r) -> cong n (mult r (finv n r)) 1 *)
    val congRes = scond_imp_cong_W (nF, rF, finv nF rF) hp1 hut
    val d2 = Thm.implies_intr (ctermW hutP) congRes
    val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of unit_has_inv) = 0 then out "OK unit_has_inv\n" else out "FAIL unit_has_inv\n";
fun unit_has_inv_W (nt,rt) hp1 hut =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("n",0), ctermW nt),(("r",0), ctermW rt)] unit_has_inv)
  in Thm.implies_elim (Thm.implies_elim inst hp1) hut end;

(* ---------------------------------------------------------------------------
   inv_imp_unit : 1<n ==> lmem b (uptoF (sub n 1)) ==> cong n (mult r b) 1
                  ==> unit_test n r
   finv's search is EXHAUSTIVE: if some in-range b is an inverse, finv finds one.
   Proof: cong n (r*b) 1  --cong_imp_scond-->  searchCond n r b ; then the witness
   b in L=uptoF(sub n 1) gives Ex c. lmem c L /\ searchCond n r c ; fsearch_found
   gives searchCond n r (fsearch n r L) ; rewrite fsearch->finv via finv_def.
   --------------------------------------------------------------------------- *)
val inv_imp_unit =
  let
    val nF = Free("n", natT); val rF = Free("r", natT); val bF = Free("b", natT)
    val one = suc ZeroC
    val subn1 = sub nF one ; val L = uptoF subn1
    val hp1P = jT (lt one nF) ; val hp1 = Thm.assume (ctermW hp1P)
    val hmemP = jT (lmem bF L) ; val hmem = Thm.assume (ctermW hmemP)
    val hcgP = jT (cong nF (mult rF bF) one) ; val hcg = Thm.assume (ctermW hcgP)
    (* searchCond n r b *)
    val scb = cong_imp_scond_W (nF, rF, bF) hp1 hcg
    (* Ex c. lmem c L /\ searchCond n r c   (witness b) *)
    val PexAbs = Term.lambda (Free("b_fe", natT))
                  (mkConj (lmem (Free("b_fe", natT)) L) (searchCond nF rF (Free("b_fe", natT))))
    val cjb = conjI_W (lmem bF L, searchCond nF rF bF) hmem scb
    val hex = exI_W PexAbs bF cjb
    (* fsearch_found : searchCond n r (fsearch n r L) /\ lmem (fsearch n r L) L *)
    val good = fsearch_found_W (nF, rF, L) hex
    val scFs = conjunct1_W (searchCond nF rF (fsearch nF rF L), lmem (fsearch nF rF L) L) good
    (* rewrite fsearch n r L -> finv n r via finv_def (sym) *)
    val fdef = finvDef_W (nF, rF)            (* oeq (finv n r) (fsearch n r L) *)
    val fdef_s = oeq_sym_vW OF [fdef]         (* oeq (fsearch n r L) (finv n r) *)
    val Psc = Term.lambda (Free("z_iu", natT)) (searchCond nF rF (Free("z_iu", natT)))
    val res = oeq_rw_W (Psc, fsearch nF rF L, finv nF rF) fdef_s scFs   (* searchCond n r (finv n r) = unit_test n r *)
    val d3 = Thm.implies_intr (ctermW hcgP) res
    val d2 = Thm.implies_intr (ctermW hmemP) d3
    val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of inv_imp_unit) = 0 then out "OK inv_imp_unit\n" else out "FAIL inv_imp_unit\n";
fun inv_imp_unit_W (nt,rt,bt) hp1 hmem hcg =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("n",0), ctermW nt),(("r",0), ctermW rt),(("b",0), ctermW bt)] inv_imp_unit)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hp1) hmem) hcg end;

val () = out "BJ0_PHASE_A_OK\n";

(* ---------------------------------------------------------------------------
   gen_cancel : 1<n ==> unit_test n a ==> cong n (mult a x)(mult a y) ==> cong n x y
   Multiply both sides by f = finv n a (which is a's inverse by unit_has_inv).
   --------------------------------------------------------------------------- *)
val gen_cancel =
  let
    val nF = Free("n", natT); val aF = Free("a", natT)
    val xF = Free("x", natT); val yF = Free("y", natT)
    val one = suc ZeroC
    val f = finv nF aF
    val hp1P = jT (lt one nF) ; val hp1 = Thm.assume (ctermW hp1P)
    val hutP = jT (unit_test nF aF) ; val hut = Thm.assume (ctermW hutP)
    val hcgP = jT (cong nF (mult aF xF) (mult aF yF)) ; val hcg = Thm.assume (ctermW hcgP)
    (* cong n (mult a f) 1 *)
    val cong_af1 = unit_has_inv_W (nF, aF) hp1 hut
    (* cong n (mult f a) 1  via comm *)
    val eq_fa_af = multcomm_W (f, aF)                       (* oeq (mult f a)(mult a f) *)
    val cong_fa_af = cong_of_eq_W (nF, mult f aF, mult aF f) eq_fa_af
    val cong_fa1 = cong_trans_W (nF, mult f aF, mult aF f, one) cong_fa_af cong_af1   (* cong n (f*a) 1 *)
    val cong_1_fa = cong_sym_W (nF, mult f aF, one) cong_fa1                          (* cong n 1 (f*a) *)
    (* step 1 : cong n x (mult 1 x) *)
    val eq_1x_x = mult1l_W xF                               (* oeq (mult 1 x) x *)
    val cong_1x_x = cong_of_eq_W (nF, mult one xF, xF) eq_1x_x
    val cong_x_1x = cong_sym_W (nF, mult one xF, xF) cong_1x_x          (* cong n x (1*x) *)
    (* step 2 : cong n (1*x) ((f*a)*x)  via cong_1_fa, refl x *)
    val crefl_x = cong_refl_W (nF, xF)
    val cong_1x_fax = cong_mult_W (nF, one, mult f aF, xF, xF) cong_1_fa crefl_x    (* cong n (1*x)((f*a)*x) *)
    (* step 3 : cong n ((f*a)*x) (f*(a*x)) via assoc *)
    val eq_fax = multassoc_W (f, aF, xF)                    (* oeq ((f*a)*x)(f*(a*x)) *)
    val cong_fax = cong_of_eq_W (nF, mult (mult f aF) xF, mult f (mult aF xF)) eq_fax
    (* step 4 : cong n (f*(a*x)) (f*(a*y)) via cong_mult refl-f, hcg *)
    val crefl_f = cong_refl_W (nF, f)
    val cong_fax_fay = cong_mult_W (nF, f, f, mult aF xF, mult aF yF) crefl_f hcg
    (* step 5 : cong n (f*(a*y)) ((f*a)*y) via assoc sym *)
    val eq_fay = multassoc_W (f, aF, yF)                    (* oeq ((f*a)*y)(f*(a*y)) *)
    val cong_fay_fa_y = cong_of_eq_W (nF, mult f (mult aF yF), mult (mult f aF) yF)
                          (oeq_sym_vW OF [eq_fay])
    (* step 6 : cong n ((f*a)*y) (1*y) via cong_fa1, refl y *)
    val crefl_y = cong_refl_W (nF, yF)
    val cong_fay_1y = cong_mult_W (nF, mult f aF, one, yF, yF) cong_fa1 crefl_y      (* cong n ((f*a)*y)(1*y) *)
    (* step 7 : cong n (1*y) y via mult1l *)
    val eq_1y_y = mult1l_W yF
    val cong_1y_y = cong_of_eq_W (nF, mult one yF, yF) eq_1y_y
    (* chain : x ~ 1*x ~ (f*a)*x ~ f*(a*x) ~ f*(a*y) ~ (f*a)*y ~ 1*y ~ y *)
    val t1 = cong_trans_W (nF, xF, mult one xF, mult (mult f aF) xF) cong_x_1x cong_1x_fax
    val t2 = cong_trans_W (nF, xF, mult (mult f aF) xF, mult f (mult aF xF)) t1 cong_fax
    val t3 = cong_trans_W (nF, xF, mult f (mult aF xF), mult f (mult aF yF)) t2 cong_fax_fay
    val t4 = cong_trans_W (nF, xF, mult f (mult aF yF), mult (mult f aF) yF) t3 cong_fay_fa_y
    val t5 = cong_trans_W (nF, xF, mult (mult f aF) yF, mult one yF) t4 cong_fay_1y
    val t6 = cong_trans_W (nF, xF, mult one yF, yF) t5 cong_1y_y                     (* cong n x y *)
    val d3 = Thm.implies_intr (ctermW hcgP) t6
    val d2 = Thm.implies_intr (ctermW hutP) d3
    val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of gen_cancel) = 0 then out "OK gen_cancel\n" else out "FAIL gen_cancel\n";
fun gen_cancel_W (nt,at,xt,yt) hp1 hut hcg =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("n",0), ctermW nt),(("a",0), ctermW at),(("x",0), ctermW xt),(("y",0), ctermW yt)] gen_cancel)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hp1) hut) hcg end;

val () = out "BJ0_GEN_CANCEL_OK\n";

(* ============================================================================
   EULER PHASE C (seat bj0) : lmap on a NEW final context ctxtU extending thyE.
   ============================================================================ *)
val () = out "BJ0_C_START\n";

(* ---- (A) extend thyE with lmap, ufilter, urrl, phiU ---- *)
val natfunT = natT --> natT;
(* combine thyE (gcdf/rrl/finv/rmod) with thyP (LForall + lprod_perm) — both extend
   thyL2 — into ONE theory with both as parents, so lprod_perm transfers here. *)
val thyEP = Context.join_thys [thyE, thyP];
val thyU0 = Sign.add_consts
  [(Binding.name "lmap",    natfunT --> natlistT --> natlistT, NoSyn),
   (Binding.name "ufilter", natT --> natlistT --> natlistT, NoSyn),
   (Binding.name "urrl",    natT --> natlistT, NoSyn),
   (Binding.name "phiU",    natT --> natT, NoSyn)] thyEP;

fun cnstU nm T = Const (Sign.full_name thyU0 (Binding.name nm), T);
val lmapC    = cnstU "lmap" (natfunT --> natlistT --> natlistT); fun lmap f l = lmapC $ f $ l;
val ufilterC = cnstU "ufilter" (natT --> natlistT --> natlistT); fun ufilter n l = ufilterC $ n $ l;
val urrlC    = cnstU "urrl" (natT --> natlistT);                 fun urrl n = urrlC $ n;
val phiUC    = cnstU "phiU" (natT --> natT);                     fun phiU n = phiUC $ n;

(* free vars *)
val fU = Free("f", natfunT); val xU = Free("x", natT); val xsU = Free("xs", natlistT);
val nU = Free("n", natT); val rU = Free("r", natT); val rsU = Free("rs", natlistT);

(* ---- lmap recursion axioms ----
     lmap_nil  : leq (lmap f lnil) lnil
     lmap_cons : leq (lmap f (lcons x xs)) (lcons (f x) (lmap f xs))   *)
val ((_,lmap_nil_ax),  thyU1) = Thm.add_axiom_global (Binding.name "lmap_nil",
      jT (leq (lmap fU lnilC) lnilC)) thyU0;
val ((_,lmap_cons_ax), thyU2) = Thm.add_axiom_global (Binding.name "lmap_cons",
      jT (leq (lmap fU (lcons xU xsU)) (lcons (fU $ xU) (lmap fU xsU)))) thyU1;

(* ---- ufilter : keep r iff unit_test n r  (CONDITIONAL list-recursion) ----
     ufilter_nil      : leq (ufilter n lnil) lnil
     ufilter_cons_in  : jT (unit_test n r)       ==> leq (ufilter n (lcons r rs)) (lcons r (ufilter n rs))
     ufilter_cons_out : jT (neg (unit_test n r)) ==> leq (ufilter n (lcons r rs)) (ufilter n rs)  *)
val ((_,ufilter_nil_ax), thyU3) = Thm.add_axiom_global (Binding.name "ufilter_nil",
      jT (leq (ufilter nU lnilC) lnilC)) thyU2;
val ((_,ufilter_cons_in_ax), thyU4) = Thm.add_axiom_global (Binding.name "ufilter_cons_in",
      Logic.mk_implies (jT (unit_test nU rU),
        jT (leq (ufilter nU (lcons rU rsU)) (lcons rU (ufilter nU rsU))))) thyU3;
val ((_,ufilter_cons_out_ax), thyU5) = Thm.add_axiom_global (Binding.name "ufilter_cons_out",
      Logic.mk_implies (jT (neg (unit_test nU rU)),
        jT (leq (ufilter nU (lcons rU rsU)) (ufilter nU rsU)))) thyU4;

(* ---- urrl : urrl n = ufilter n (uptoF (sub n 1)) ---- *)
val ((_,urrl_def_ax), thyU6) = Thm.add_axiom_global (Binding.name "urrl_def",
      jT (leq (urrl nU) (ufilter nU (uptoF (sub nU (suc ZeroC)))))) thyU5;
(* ---- phiU : phiU n = llen (urrl n) ---- *)
val ((_,phiU_def_ax), thyU) = Thm.add_axiom_global (Binding.name "phiU_def",
      jT (oeq (phiU nU) (llen (urrl nU)))) thyU6;

val ctxtU  = Proof_Context.init_global thyU;
val ctermU = Thm.cterm_of ctxtU;
val () = out "BJ0_U_CONTEXT_READY\n";

(* ---- re-varify reused axioms/lemmas onto ctxtU ---- *)
val oeq_refl_vU   = varify oeq_refl;
val oeq_sym_vU    = varify oeq_sym;
val oeq_trans_vU  = varify oeq_trans;
val oeq_subst_vU  = varify oeq_subst;
val mp_vU         = varify mp_ax;
val impI_vU       = varify impI_ax;
val conjI_vU      = varify conjI_ax;
val conjunct1_vU  = varify conjunct1_ax;
val conjunct2_vU  = varify conjunct2_ax;
val disjI1_vU     = varify disjI1_ax;
val disjI2_vU     = varify disjI2_ax;
val disjE_vU      = varify disjE_ax;
val exI_vU        = varify exI_ax;
val exE_vU        = varify exE_ax;
val ex_middle_vU  = varify ex_middle_ax;
val oFalse_elim_vU= varify oFalse_elim_ax;
val Suc_neq_Zero_vU = varify Suc_neq_Zero_ax;
(* list axioms *)
val leq_refl_vU   = varify leq_refl_ax;
val leq_subst_vU  = varify leq_subst_ax;
val list_induct_vU= varify list_induct_ax;
val lmem_cons_fwd_vU = varify lmem_cons_fwd_ax;
val lmem_cons_bwd_vU = varify lmem_cons_bwd_ax;
val lmem_nil_elim_vU = varify lmem_nil_elim_ax;
val lnodup_nil_vU    = varify lnodup_nil_ax;
val lnodup_cons_fwd_vU = varify lnodup_cons_fwd_ax;
val lnodup_cons_bwd_vU = varify lnodup_cons_bwd_ax;
val lprod_nil_vU  = varify lprod_nil_ax;
val lprod_cons_vU = varify lprod_cons_ax;
val llen_nil_vU   = varify llen_nil_ax;
val llen_cons_vU  = varify llen_cons_ax;
(* lmap axioms *)
val lmap_nil_vU   = varify lmap_nil_ax;
val lmap_cons_vU  = varify lmap_cons_ax;
(* ufilter / urrl / phiU axioms *)
val ufilter_nil_vU = varify ufilter_nil_ax;
val ufilter_cons_in_vU = varify ufilter_cons_in_ax;
val ufilter_cons_out_vU = varify ufilter_cons_out_ax;
val urrl_def_vU   = varify urrl_def_ax;
val phiU_def_vU   = varify phiU_def_ax;
(* cong / mult / finv / search reused (already 0-hyp varified theorems) *)
val cong_refl_vU  = varify cong_refl;
val cong_sym_vU   = varify cong_sym;
val cong_trans_vU = varify cong_trans;
val cong_mult_vU  = varify cong_mult;
val cong_imp_rmodeq_vU = varify cong_imp_rmodeq;
val rmodeq_imp_cong_vU = varify rmodeq_imp_cong;
val rmod_lt_vU    = varify rmod_lt_ax;
val mult_comm_vU  = varify mult_comm;
val mult_assoc_vU = varify mult_assoc;
val mult_1_left_vU= varify mult_1_left;
val lmem_upto_fwd_vU = varify lmem_upto_fwd;
val lmem_upto_bwd_vU = varify lmem_upto_bwd;
val finv_def_vU   = varify finv_def_ax;
(* my Phase A/B lemmas (0-hyp) *)
val unit_has_inv_vU = varify unit_has_inv;
val inv_imp_unit_vU = varify inv_imp_unit;
val gen_cancel_vU   = varify gen_cancel;
(* lprod_perm (P-context theorem, 0-hyp) *)
val lprod_perm_vU = varify lprod_perm;
val () = out "BJ0_U_VARIFY_DONE\n";

(* ---- extra re-varify needed for accessors ---- *)
val allI_vU       = varify allI_ax;
val allE_vU       = varify allE_ax;

(* ============================================================================
   _U accessor family on ctxtU
   ============================================================================ *)
fun oeqRefl_U t = beta_norm (Drule.infer_instantiate ctxtU [(("a",0), ctermU t)] oeq_refl_vU);
fun oeq_rw_U (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("P",0), ctermU Pabs),(("a",0), ctermU aT),(("b",0), ctermU bT)] oeq_subst_vU)
  in inst OF [hab, hPa] end;
fun mp_U (At,Bt) hImp hA =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU [(("A",0), ctermU At),(("B",0), ctermU Bt)] mp_vU)
  in Thm.implies_elim (Thm.implies_elim inst hImp) hA end;
fun impI_U (At,Bt) hImpThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU [(("A",0), ctermU At),(("B",0), ctermU Bt)] impI_vU)
  in Thm.implies_elim inst hImpThm end;
fun conjI_U (At,Bt) hA hB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU [(("A",0), ctermU At),(("B",0), ctermU Bt)] conjI_vU)
  in Thm.implies_elim (Thm.implies_elim inst hA) hB end;
fun conjunct1_U (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("A",0), ctermU At),(("B",0), ctermU Bt)] conjunct1_vU)) h;
fun conjunct2_U (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("A",0), ctermU At),(("B",0), ctermU Bt)] conjunct2_vU)) h;
fun oFalse_elim_U rT = beta_norm (Drule.infer_instantiate ctxtU [(("R",0), ctermU rT)] oFalse_elim_vU);
fun disjE_U (At,Bt,Ct) dThm cA cB =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("A",0), ctermU At),(("B",0), ctermU Bt),(("C",0), ctermU Ct)] disjE_vU)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst dThm) cA) cB end;
fun disjI1_U (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("A",0), ctermU At),(("B",0), ctermU Bt)] disjI1_vU)) h;
fun disjI2_U (At,Bt) h = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("A",0), ctermU At),(("B",0), ctermU Bt)] disjI2_vU)) h;
fun em_U t = beta_norm (Drule.infer_instantiate ctxtU [(("A",0), ctermU t)] ex_middle_vU);
fun Suc_neq_Zero_U nt heq =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU nt)] Suc_neq_Zero_vU)) heq;
fun exI_U Pabs at hbody =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("P",0), ctermU Pabs),(("a",0), ctermU at)] exI_vU)
  in Thm.implies_elim inst hbody end;
fun exE_U (Pabs, goalC) exThm wName bodyFn =
  let val wF = Free(wName, natT)
      val hypTerm = jT (Term.betapply (Pabs, wF))
      val hypThm  = Thm.assume (ctermU hypTerm)
      val body    = bodyFn wF hypThm
      val minor   = Thm.forall_intr (ctermU wF) (Thm.implies_intr (ctermU hypTerm) body)
      val exE_inst= beta_norm (Drule.infer_instantiate ctxtU
                      [(("P",0), ctermU Pabs),(("Q",0), ctermU goalC)] exE_vU)
  in Thm.implies_elim (Thm.implies_elim exE_inst exThm) minor end;
(* object Forall intro/elim *)
fun allI_U Pabs hAllThm =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU [(("P",0), ctermU Pabs)] allI_vU)
  in Thm.implies_elim inst hAllThm end;
fun allE_U Pabs at hF = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("P",0), ctermU Pabs),(("a",0), ctermU at)] allE_vU)) hF;

(* list accessors on ctxtU *)
fun leqRefl_U l = beta_norm (Drule.infer_instantiate ctxtU [(("a",0), ctermU l)] leq_refl_vU);
fun leq_rw_U (Pabs,aT,bT) hab hPa =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("P",0), ctermU Pabs),(("a",0), ctermU aT),(("b",0), ctermU bT)] leq_subst_vU)
  in inst OF [hab, hPa] end;
(* leq_sym from leq_subst *)
fun leq_sym_U (aT,bT) hab =
  let val zf = Free("z_lsy", natlistT)
      val refl_aa = leqRefl_U aT
      val P2 = Term.lambda zf (leq zf aT)
  in leq_rw_U (P2, aT, bT) hab refl_aa end;
fun lprodCons_U (h,t) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU h),(("t",0), ctermU t)] lprod_cons_vU);
val lprodNil_U = lprod_nil_vU;
fun llenCons_U (h,t) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU h),(("t",0), ctermU t)] llen_cons_vU);
val llenNil_U = llen_nil_vU;
fun lmemConsFwd_U (xt,yt,yst) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU xt),(("y",0), ctermU yt),(("t",0), ctermU yst)] lmem_cons_fwd_vU);
fun lmemConsBwd_U (xt,yt,yst) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU xt),(("y",0), ctermU yt),(("t",0), ctermU yst)] lmem_cons_bwd_vU);
fun lmemNilElim_U xt = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU xt)] lmem_nil_elim_vU);
val lnodupNil_U = lnodup_nil_vU;
fun lnodupConsFwd_U (xt,tt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU xt),(("t",0), ctermU tt)] lnodup_cons_fwd_vU);
fun lnodupConsBwd_U (xt,tt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("x",0), ctermU xt),(("t",0), ctermU tt)] lnodup_cons_bwd_vU);
(* lprod-cong / llen-cong via leq_subst *)
fun lprod_cong_U (aT,bT) hab =
  let val zf = Free("z_lpc", natlistT)
      val Pabs = Term.lambda zf (oeq (lprod aT) (lprod zf))
  in leq_rw_U (Pabs, aT, bT) hab (oeqRefl_U (lprod aT)) end;
fun llen_cong_U (aT,bT) hab =
  let val zf = Free("z_llc", natlistT)
      val Pabs = Term.lambda zf (oeq (llen aT) (llen zf))
  in leq_rw_U (Pabs, aT, bT) hab (oeqRefl_U (llen aT)) end;
(* lmem-cong via leq_subst : leq a b ==> (lmem x a -> ... ) ; we rewrite lmem x via leq *)
fun lmem_leq_U (xt, aT, bT) hab hmem =
  let val zf = Free("z_lmc", natlistT)
      val Pabs = Term.lambda zf (lmem xt zf)
  in leq_rw_U (Pabs, aT, bT) hab hmem end;
(* lnodup-cong via leq_subst *)
fun lnodup_leq_U (aT, bT) hab hnd =
  let val zf = Free("z_ndc", natlistT)
      val Pabs = Term.lambda zf (lnodup zf)
  in leq_rw_U (Pabs, aT, bT) hab hnd end;

(* lmap recursion accessors *)
val lmapNil_U = lmap_nil_vU;
fun lmapNil_at f = beta_norm (Drule.infer_instantiate ctxtU [(("f",0), ctermU f)] lmap_nil_vU);
fun lmapCons_U (f,h,t) = beta_norm (Drule.infer_instantiate ctxtU
      [(("f",0), ctermU f),(("x",0), ctermU h),(("xs",0), ctermU t)] lmap_cons_vU);

(* cong accessors on ctxtU *)
fun cong_refl_U (mt,at) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("a",0), ctermU at)] cong_refl_vU);
fun cong_sym_U (mt,at,bt) h =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("a",0), ctermU at),(("b",0), ctermU bt)] cong_sym_vU)) h;
fun cong_trans_U (mt,at,bt,ct) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("m",0), ctermU mt),(("a",0), ctermU at),(("b",0), ctermU bt),(("c",0), ctermU ct)] cong_trans_vU)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun cong_mult_U (mt,at,a2t,bt,b2t) h1 h2 =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("m",0), ctermU mt),(("a",0), ctermU at),(("a2",0), ctermU a2t),
         (("b",0), ctermU bt),(("b2",0), ctermU b2t)] cong_mult_vU)
  in Thm.implies_elim (Thm.implies_elim inst h1) h2 end;
fun cong_of_eq_U (pT, X, Y) heq =
  let val zF = Free("z_coe", natT)
      val Pabs = Term.lambda zF (cong pT X zF)
      val crefl = cong_refl_U (pT, X)
  in oeq_rw_U (Pabs, X, Y) heq crefl end;
fun cong_imp_rmodeq_U (pt,at,bt) hpos hcong =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("p",0), ctermU pt),(("a",0), ctermU at),(("b",0), ctermU bt)] cong_imp_rmodeq_vU)
  in Thm.implies_elim (Thm.implies_elim inst hpos) hcong end;
fun rmodeq_imp_cong_U (pt,at,bt) hpos heq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("p",0), ctermU pt),(("a",0), ctermU at),(("b",0), ctermU bt)] rmodeq_imp_cong_vU)
  in Thm.implies_elim (Thm.implies_elim inst hpos) heq end;
fun rmod_lt_U (at,pt) hpos = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("a",0), ctermU at),(("p",0), ctermU pt)] rmod_lt_vU)) hpos;
fun multcomm_U (mt,nt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("n",0), ctermU nt)] mult_comm_vU);
fun multassoc_U (mt,nt,kt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("m",0), ctermU mt),(("n",0), ctermU nt),(("k",0), ctermU kt)] mult_assoc_vU);
fun mult1l_U t = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU t)] mult_1_left_vU);
fun lmem_upto_fwd_U (bt,nt) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
          [(("b",0), ctermU bt),(("k_if",0), ctermU nt)] lmem_upto_fwd_vU)
  in mp_U (lmem bt (uptoF nt), mkConj (lt ZeroC bt)(le bt nt)) inst hmem end;
fun lmem_upto_bwd_U (bt,nt) hconj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
          [(("b",0), ctermU bt),(("k_iu",0), ctermU nt)] lmem_upto_bwd_vU)
  in mp_U (mkConj (lt ZeroC bt)(le bt nt), lmem bt (uptoF nt)) inst hconj end;
fun finvDef_U (pt,xt) = beta_norm (Drule.infer_instantiate ctxtU
      [(("p",0), ctermU pt),(("x",0), ctermU xt)] finv_def_vU);
(* my reused lemmas on ctxtU *)
fun unit_has_inv_U (nt,rt) hp1 hut =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("n",0), ctermU nt),(("r",0), ctermU rt)] unit_has_inv_vU)
  in Thm.implies_elim (Thm.implies_elim inst hp1) hut end;
fun inv_imp_unit_U (nt,rt,bt) hp1 hmem hcg =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("n",0), ctermU nt),(("r",0), ctermU rt),(("b",0), ctermU bt)] inv_imp_unit_vU)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hp1) hmem) hcg end;
fun gen_cancel_U (nt,at,xt,yt) hp1 hut hcg =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("n",0), ctermU nt),(("a",0), ctermU at),(("x",0), ctermU xt),(("y",0), ctermU yt)] gen_cancel_vU)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hp1) hut) hcg end;

val () = out "BJ0_U_ACCESSORS_READY\n";

(* ============================================================================
   lmap lemmas on ctxtU (each by list_induct).
   Note: f is an object function Free("f", natT-->natT); f $ t applies it.
   ============================================================================ *)

(* helper : oeq (f x)(f y) from oeq x y *)
fun fcong_U (fT, xT, yT) hxy =
  let val zF = Free("z_fc", natT)
      val Pabs = Term.lambda zF (oeq (fT $ xT) (fT $ zF))
  in oeq_rw_U (Pabs, xT, yT) hxy (oeqRefl_U (fT $ xT)) end;

(* ---------------------------------------------------------------------------
   lmem_map_bwd : lmem x L ==> lmem (f x) (lmap f L)
   --------------------------------------------------------------------------- *)
val lmem_map_bwd =
  let
    val fF = Free("f", natfunT); val xF = Free("x", natT)
    fun mapL z = lmap fF z
    fun concBody z = lmem (fF $ xF) (mapL z)
    fun predBody z = mkImp (lmem xF z) (concBody z)
    val Qpred = Abs("z", natlistT, predBody (Bound 0))
    val LF = Free("L", natlistT)
    val ind = beta_norm (Drule.infer_instantiate ctxtU
          [(("P",0), ctermU Qpred), (("a",0), ctermU LF)] list_induct_vU)
    val base =
      let val hmem = Thm.assume (ctermU (jT (lmem xF lnilC)))
          val ff   = Thm.implies_elim (lmemNilElim_U xF) hmem
          val conc = Thm.implies_elim (oFalse_elim_U (concBody lnilC)) ff
          val dis  = Thm.implies_intr (ctermU (jT (lmem xF lnilC))) conc
      in impI_U (lmem xF lnilC, concBody lnilC) dis end
    val yF = Free("y", natT); val tF = Free("t", natlistT)
    val ihprop = jT (predBody tF)
    val IH = Thm.assume (ctermU ihprop)
    val stepConcl =
      let
        val hmem = Thm.assume (ctermU (jT (lmem xF (lcons yF tF))))
        val disjmem = Thm.implies_elim (lmemConsFwd_U (xF, yF, tF)) hmem
        (* lmap f (lcons y t)  leq  lcons (f y)(lmap f t) *)
        val lmc = lmapCons_U (fF, yF, tF)                  (* leq (lmap f (lcons y t)) (lcons (f y)(lmap f t)) *)
        val consTarget = lcons (fF $ yF) (mapL tF)
        val caseEq =
          let val heq = Thm.assume (ctermU (jT (oeq xF yF)))
              val fxfy = fcong_U (fF, xF, yF) heq            (* oeq (f x)(f y) *)
              val memCons = Thm.implies_elim (lmemConsBwd_U (fF $ xF, fF $ yF, mapL tF))
                              (disjI1_U (oeq (fF $ xF)(fF $ yF), lmem (fF $ xF)(mapL tF)) fxfy)
              (* transfer membership from lcons (f y)(map t) back to lmap f (lcons y t) via leq sym *)
              val lmc_s = leq_sym_U (mapL (lcons yF tF), consTarget) lmc
              val res = lmem_leq_U (fF $ xF, consTarget, mapL (lcons yF tF)) lmc_s memCons
          in Thm.implies_intr (ctermU (jT (oeq xF yF))) res end
        val caseMem =
          let val hmt = Thm.assume (ctermU (jT (lmem xF tF)))
              val ihc = mp_U (lmem xF tF, concBody tF) IH hmt        (* lmem (f x)(lmap f t) *)
              val memCons = Thm.implies_elim (lmemConsBwd_U (fF $ xF, fF $ yF, mapL tF))
                              (disjI2_U (oeq (fF $ xF)(fF $ yF), lmem (fF $ xF)(mapL tF)) ihc)
              val lmc_s = leq_sym_U (mapL (lcons yF tF), consTarget) lmc
              val res = lmem_leq_U (fF $ xF, consTarget, mapL (lcons yF tF)) lmc_s memCons
          in Thm.implies_intr (ctermU (jT (lmem xF tF))) res end
        val conc = disjE_U (oeq xF yF, lmem xF tF, concBody (lcons yF tF)) disjmem caseEq caseMem
        val dis = Thm.implies_intr (ctermU (jT (lmem xF (lcons yF tF)))) conc
      in impI_U (lmem xF (lcons yF tF), concBody (lcons yF tF)) dis end
    val step1 = Thm.forall_intr (ctermU yF)
                  (Thm.forall_intr (ctermU tF) (Thm.implies_intr (ctermU ihprop) stepConcl))
    val r2 = Thm.implies_elim (Thm.implies_elim ind base) step1
    val hmemL = Thm.assume (ctermU (jT (lmem xF LF)))
    val concL = mp_U (lmem xF LF, concBody LF) r2 hmemL
    val d1 = Thm.implies_intr (ctermU (jT (lmem xF LF))) concL
  in varify d1 end;
val () = if length (Thm.hyps_of lmem_map_bwd) = 0 then out "OK lmem_map_bwd\n" else out "FAIL lmem_map_bwd\n";
fun lmem_map_bwd_U (ft,xt,Lt) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("f",0), ctermU ft),(("x",0), ctermU xt),(("L",0), ctermU Lt)] (varify lmem_map_bwd))
  in Thm.implies_elim inst hmem end;

val () = out "BJ0_LMEM_MAP_BWD_OK\n";

(* ---------------------------------------------------------------------------
   lmem_map_fwd : lmem y (lmap f L) ==> Ex x. lmem x L /\ oeq y (f x)
   --------------------------------------------------------------------------- *)
val lmem_map_fwd =
  let
    val fF = Free("f", natfunT); val yF = Free("y", natT)
    fun mapL z = lmap fF z
    fun exGoal z = mkEx (Term.lambda (Free("xw", natT))
                     (mkConj (lmem (Free("xw", natT)) z) (oeq yF (fF $ (Free("xw", natT))))))
    fun predBody z = mkImp (lmem yF (mapL z)) (exGoal z)
    val zQ = Free("zQ", natlistT)
    val Qpred = Term.lambda zQ (predBody zQ)   (* Term.lambda handles De Bruijn over nested Abs *)
    val LF = Free("L", natlistT)
    val ind = beta_norm (Drule.infer_instantiate ctxtU
          [(("P",0), ctermU Qpred), (("a",0), ctermU LF)] list_induct_vU)
    val base =
      let
        val hmem = Thm.assume (ctermU (jT (lmem yF (mapL lnilC))))
        (* lmap f lnil leq lnil -> lmem y lnil *)
        val lmn = lmapNil_at fF                              (* leq (lmap f lnil) lnil *)
        val memNil = lmem_leq_U (yF, mapL lnilC, lnilC) lmn hmem
        val ff = Thm.implies_elim (lmemNilElim_U yF) memNil
        val conc = Thm.implies_elim (oFalse_elim_U (exGoal lnilC)) ff
        val dis  = Thm.implies_intr (ctermU (jT (lmem yF (mapL lnilC)))) conc
      in impI_U (lmem yF (mapL lnilC), exGoal lnilC) dis end
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val ihprop = jT (predBody tF)
    val IH = Thm.assume (ctermU ihprop)
    val stepConcl =
      let
        val hmem = Thm.assume (ctermU (jT (lmem yF (mapL (lcons hF tF)))))
        val lmc = lmapCons_U (fF, hF, tF)                   (* leq (lmap f (lcons h t)) (lcons (f h)(lmap f t)) *)
        val consTarget = lcons (fF $ hF) (mapL tF)
        val memCons = lmem_leq_U (yF, mapL (lcons hF tF), consTarget) lmc hmem  (* lmem y (lcons (f h)(map t)) *)
        val disjmem = Thm.implies_elim (lmemConsFwd_U (yF, fF $ hF, mapL tF)) memCons (* oeq y (f h) \/ lmem y (map t) *)
        val PexAbs = Term.lambda (Free("xw", natT))
                       (mkConj (lmem (Free("xw", natT)) (lcons hF tF)) (oeq yF (fF $ (Free("xw", natT)))))
        val caseEq =
          let val heq = Thm.assume (ctermU (jT (oeq yF (fF $ hF))))   (* oeq y (f h) *)
              (* witness x = h : lmem h (lcons h t) /\ oeq y (f h) *)
              val memh = Thm.implies_elim (lmemConsBwd_U (hF, hF, tF))
                           (disjI1_U (oeq hF hF, lmem hF tF) (oeqRefl_U hF))
              val cj = conjI_U (lmem hF (lcons hF tF), oeq yF (fF $ hF)) memh heq
              val ex = exI_U PexAbs hF cj
          in Thm.implies_intr (ctermU (jT (oeq yF (fF $ hF)))) ex end
        val caseMem =
          let val hmt = Thm.assume (ctermU (jT (lmem yF (mapL tF))))
              val ihEx = mp_U (lmem yF (mapL tF), exGoal tF) IH hmt   (* Ex x. lmem x t /\ oeq y (f x) *)
              val PihAbs = Term.lambda (Free("xw", natT))
                             (mkConj (lmem (Free("xw", natT)) tF) (oeq yF (fF $ (Free("xw", natT)))))
              fun bodyFn w hw =
                let val memwt = conjunct1_U (lmem w tF, oeq yF (fF $ w)) hw
                    val oeqyfw = conjunct2_U (lmem w tF, oeq yF (fF $ w)) hw
                    val memwL = Thm.implies_elim (lmemConsBwd_U (w, hF, tF))
                                  (disjI2_U (oeq w hF, lmem w tF) memwt)
                    val cj = conjI_U (lmem w (lcons hF tF), oeq yF (fF $ w)) memwL oeqyfw
                in exI_U PexAbs w cj end
              val ex = exE_U (PihAbs, exGoal (lcons hF tF)) ihEx "xw_f" bodyFn
          in Thm.implies_intr (ctermU (jT (lmem yF (mapL tF)))) ex end
        val conc = disjE_U (oeq yF (fF $ hF), lmem yF (mapL tF), exGoal (lcons hF tF)) disjmem caseEq caseMem
        val dis = Thm.implies_intr (ctermU (jT (lmem yF (mapL (lcons hF tF))))) conc
      in impI_U (lmem yF (mapL (lcons hF tF)), exGoal (lcons hF tF)) dis end
    val step1 = Thm.forall_intr (ctermU hF)
                  (Thm.forall_intr (ctermU tF) (Thm.implies_intr (ctermU ihprop) stepConcl))
    val r2 = Thm.implies_elim (Thm.implies_elim ind base) step1
    val hmemL = Thm.assume (ctermU (jT (lmem yF (mapL LF))))
    val concL = mp_U (lmem yF (mapL LF), exGoal LF) r2 hmemL
    val d1 = Thm.implies_intr (ctermU (jT (lmem yF (mapL LF)))) concL
  in varify d1 end;
val () = if length (Thm.hyps_of lmem_map_fwd) = 0 then out "OK lmem_map_fwd\n" else out "FAIL lmem_map_fwd\n";
val lmem_map_fwd_vU = varify lmem_map_fwd;
fun lmem_map_fwd_U (ft,yt,Lt) hmem =
  let val PexAbs = Term.lambda (Free("xw", natT))
                     (mkConj (lmem (Free("xw", natT)) Lt) (oeq yt (ft $ (Free("xw", natT)))))
      val goal = mkEx PexAbs
      val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("f",0), ctermU ft),(("y",0), ctermU yt),(("L",0), ctermU Lt)] lmem_map_fwd_vU)
  in Thm.implies_elim inst hmem end;

val () = out "BJ0_LMEM_MAP_FWD_OK\n";

(* ---------------------------------------------------------------------------
   lnodup_map : lnodup L ==> injF f L ==> lnodup (lmap f L)
   where injF f L = Forall a. Forall b. lmem a L -> lmem b L -> oeq (f a)(f b) -> oeq a b
   (object-level injectivity-on-members; relativized to L so the IH supplies inj-on-t).
   --------------------------------------------------------------------------- *)
(* object injectivity predicate, built with Term.lambda over Frees (De Bruijn safe) *)
fun injBody fT z a b = mkImp (lmem a z) (mkImp (lmem b z) (mkImp (oeq (fT $ a)(fT $ b)) (oeq a b)))
fun injInnerAbs fT z a = (* Forall b. ... *)
  let val bF = Free("ib_b", natT) in mkForall (Term.lambda bF (injBody fT z a bF)) end
fun injF fT z =
  let val aF = Free("ib_a", natT) in mkForall (Term.lambda aF (injInnerAbs fT z aF)) end
(* eliminate injF at (a,b) with membership proofs : injF f z, lmem a z, lmem b z, oeq (f a)(f b) => oeq a b *)
fun injF_elim_U (fT, z, at, bt) hinj hma hmb hfeq =
  let val aF = Free("ib_a", natT)
      val PaAbs = Term.lambda aF (injInnerAbs fT z aF)            (* %a. Forall b. ... *)
      val inner_a = allE_U PaAbs at hinj                          (* Forall b. injBody f z a b  (a:=at) *)
      val bF = Free("ib_b", natT)
      val PbAbs = Term.lambda bF (injBody fT z at bF)             (* %b. injBody f z at b *)
      val body = allE_U PbAbs bt inner_a                          (* injBody f z at bt = lmem at z -> lmem bt z -> oeq.. -> oeq at bt *)
      val s1 = mp_U (lmem at z, mkImp (lmem bt z)(mkImp (oeq (fT $ at)(fT $ bt))(oeq at bt))) body hma
      val s2 = mp_U (lmem bt z, mkImp (oeq (fT $ at)(fT $ bt))(oeq at bt)) s1 hmb
      val s3 = mp_U (oeq (fT $ at)(fT $ bt), oeq at bt) s2 hfeq
  in s3 end

val lnodup_map =
  let
    val fF = Free("f", natfunT)
    fun mapL z = lmap fF z
    fun predBody z = mkImp (lnodup z) (mkImp (injF fF z) (lnodup (mapL z)))
    val zQ = Free("zQ", natlistT)
    val Qpred = Term.lambda zQ (predBody zQ)
    val LF = Free("L", natlistT)
    val ind = beta_norm (Drule.infer_instantiate ctxtU
          [(("P",0), ctermU Qpred), (("a",0), ctermU LF)] list_induct_vU)
    (* base : lnodup lnil -> injF f lnil -> lnodup (lmap f lnil) *)
    val base =
      let val hnd = Thm.assume (ctermU (jT (lnodup lnilC)))
          val hinj = Thm.assume (ctermU (jT (injF fF lnilC)))
          val lmn = lmapNil_at fF                              (* leq (lmap f lnil) lnil *)
          val lmn_s = leq_sym_U (mapL lnilC, lnilC) lmn        (* leq lnil (lmap f lnil) *)
          val ndmap = lnodup_leq_U (lnilC, mapL lnilC) lmn_s lnodupNil_U
          val d2 = impI_U (injF fF lnilC, lnodup (mapL lnilC))
                     (Thm.implies_intr (ctermU (jT (injF fF lnilC))) ndmap)
      in impI_U (lnodup lnilC, mkImp (injF fF lnilC) (lnodup (mapL lnilC)))
           (Thm.implies_intr (ctermU (jT (lnodup lnilC))) d2) end
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val ihprop = jT (predBody tF)
    val IH = Thm.assume (ctermU ihprop)
    val stepConcl =
      let
        val hnd = Thm.assume (ctermU (jT (lnodup (lcons hF tF))))
        val hinj = Thm.assume (ctermU (jT (injF fF (lcons hF tF))))
        (* from lnodup (lcons h t) : neg (lmem h t) /\ lnodup t *)
        val ndcj = Thm.implies_elim (lnodupConsFwd_U (hF, tF)) hnd
        val hnmem = conjunct1_U (neg (lmem hF tF), lnodup tF) ndcj   (* neg (lmem h t) *)
        val hndt  = conjunct2_U (neg (lmem hF tF), lnodup tF) ndcj   (* lnodup t *)
        (* injF f t  from injF f (lcons h t) : members of t are members of lcons h t *)
        val injT =
          let val aF = Free("ja", natT); val bF = Free("jb", natT)
              val hma = Thm.assume (ctermU (jT (lmem aF tF)))
              val hmb = Thm.assume (ctermU (jT (lmem bF tF)))
              val hfeq = Thm.assume (ctermU (jT (oeq (fF $ aF)(fF $ bF))))
              val maC = Thm.implies_elim (lmemConsBwd_U (aF, hF, tF))
                          (disjI2_U (oeq aF hF, lmem aF tF) hma)     (* lmem a (lcons h t) *)
              val mbC = Thm.implies_elim (lmemConsBwd_U (bF, hF, tF))
                          (disjI2_U (oeq bF hF, lmem bF tF) hmb)     (* lmem b (lcons h t) *)
              val oeqab = injF_elim_U (fF, lcons hF tF, aF, bF) hinj maC mbC hfeq  (* oeq a b *)
              (* build object injBody f t a b by impI_U over the three premises *)
              val objImp =
                let val o3 = oeqab
                    val i3 = impI_U (oeq (fF $ aF)(fF $ bF), oeq aF bF)
                               (Thm.implies_intr (ctermU (jT (oeq (fF $ aF)(fF $ bF)))) o3)
                    val i2 = impI_U (lmem bF tF, mkImp (oeq (fF $ aF)(fF $ bF))(oeq aF bF))
                               (Thm.implies_intr (ctermU (jT (lmem bF tF))) i3)
                    val i1 = impI_U (lmem aF tF, mkImp (lmem bF tF)(mkImp (oeq (fF $ aF)(fF $ bF))(oeq aF bF)))
                               (Thm.implies_intr (ctermU (jT (lmem aF tF))) i2)
                in i1 end                                            (* injBody f t a b as object imp *)
              (* Forall b. injBody f t a b  via allI over b *)
              val PbAbs = Term.lambda bF (injBody fF tF aF bF)
              val forallB = allI_U PbAbs (Thm.forall_intr (ctermU bF) objImp)
              val PaAbs = Term.lambda aF (injInnerAbs fF tF aF)
              val forallA = allI_U PaAbs (Thm.forall_intr (ctermU aF) forallB)
          in forallA end                                            (* injF f t *)
        (* lnodup (lmap f t) from IH *)
        val ih1 = mp_U (lnodup tF, mkImp (injF fF tF)(lnodup (mapL tF))) IH hndt
        val ndmapT = mp_U (injF fF tF, lnodup (mapL tF)) ih1 injT   (* lnodup (lmap f t) *)
        (* neg (lmem (f h)(lmap f t)) *)
        val negmem =
          let val hmem = Thm.assume (ctermU (jT (lmem (fF $ hF)(mapL tF))))
              val ex = lmem_map_fwd_U (fF, fF $ hF, tF) hmem          (* Ex x. lmem x t /\ oeq (f h)(f x) *)
              val PihAbs = Term.lambda (Free("xw", natT))
                             (mkConj (lmem (Free("xw", natT)) tF) (oeq (fF $ hF) (fF $ (Free("xw", natT)))))
              fun bodyFn w hw =
                let val memwt = conjunct1_U (lmem w tF, oeq (fF $ hF)(fF $ w)) hw
                    val oeqfhfw = conjunct2_U (lmem w tF, oeq (fF $ hF)(fF $ w)) hw
                    (* inj on (lcons h t) at (h,w) : lmem h (cons), lmem w (cons), oeq (f h)(f w) -> oeq h w *)
                    val memhC = Thm.implies_elim (lmemConsBwd_U (hF, hF, tF))
                                  (disjI1_U (oeq hF hF, lmem hF tF) (oeqRefl_U hF))
                    val memwC = Thm.implies_elim (lmemConsBwd_U (w, hF, tF))
                                  (disjI2_U (oeq w hF, lmem w tF) memwt)
                    val oeqhw = injF_elim_U (fF, lcons hF tF, hF, w) hinj memhC memwC oeqfhfw  (* oeq h w *)
                    (* lmem h t : rewrite lmem w t along oeq w h (sym of oeq h w) via oeq_subst *)
                    val oeqwh = oeq_sym_vU OF [oeqhw]                  (* oeq w h *)
                    val Pm = Term.lambda (Free("zm", natT)) (lmem (Free("zm", natT)) tF)
                    val memht = oeq_rw_U (Pm, w, hF) oeqwh memwt       (* lmem h t *)
                    val ff = mp_U (lmem hF tF, oFalseC) hnmem memht
                in ff end
              val ffinal = exE_U (PihAbs, oFalseC) ex "xw_g" bodyFn
              val d = Thm.implies_intr (ctermU (jT (lmem (fF $ hF)(mapL tF)))) ffinal
          in impI_U (lmem (fF $ hF)(mapL tF), oFalseC) d end          (* neg (lmem (f h)(lmap f t)) *)
        (* lnodup (lcons (f h)(lmap f t)) via lnodupConsBwd *)
        val ndcons = Thm.implies_elim (lnodupConsBwd_U (fF $ hF, mapL tF))
                       (conjI_U (neg (lmem (fF $ hF)(mapL tF)), lnodup (mapL tF)) negmem ndmapT)
        (* transfer to lnodup (lmap f (lcons h t)) via leq sym *)
        val lmc = lmapCons_U (fF, hF, tF)                            (* leq (lmap f (lcons h t)) (lcons (f h)(lmap f t)) *)
        val lmc_s = leq_sym_U (mapL (lcons hF tF), lcons (fF $ hF)(mapL tF)) lmc
        val ndres = lnodup_leq_U (lcons (fF $ hF)(mapL tF), mapL (lcons hF tF)) lmc_s ndcons
        (* discharge injF then lnodup (object imps) *)
        val d2 = impI_U (injF fF (lcons hF tF), lnodup (mapL (lcons hF tF)))
                   (Thm.implies_intr (ctermU (jT (injF fF (lcons hF tF)))) ndres)
      in impI_U (lnodup (lcons hF tF), mkImp (injF fF (lcons hF tF)) (lnodup (mapL (lcons hF tF))))
           (Thm.implies_intr (ctermU (jT (lnodup (lcons hF tF)))) d2) end
    val step1 = Thm.forall_intr (ctermU hF)
                  (Thm.forall_intr (ctermU tF) (Thm.implies_intr (ctermU ihprop) stepConcl))
    val r2 = Thm.implies_elim (Thm.implies_elim ind base) step1
    val hndL = Thm.assume (ctermU (jT (lnodup LF)))
    val hinjL = Thm.assume (ctermU (jT (injF fF LF)))
    val concImp = mp_U (lnodup LF, mkImp (injF fF LF)(lnodup (mapL LF))) r2 hndL
    val concL = mp_U (injF fF LF, lnodup (mapL LF)) concImp hinjL
    val d2 = Thm.implies_intr (ctermU (jT (injF fF LF))) concL
    val d1 = Thm.implies_intr (ctermU (jT (lnodup LF))) d2
  in varify d1 end;
val () = if length (Thm.hyps_of lnodup_map) = 0 then out "OK lnodup_map\n" else out "FAIL lnodup_map\n";
val lnodup_map_vU = varify lnodup_map;
fun lnodup_map_U (ft,Lt) hnd hinj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("f",0), ctermU ft),(("L",0), ctermU Lt)] lnodup_map_vU)
  in Thm.implies_elim (Thm.implies_elim inst hnd) hinj end;

val () = out "BJ0_LNODUP_MAP_OK\n";

(* ============================================================================
   PHASE H : the unit-filter list urrl and its membership/nodup characterization.
   Mirrors the base's rfilter/rrl proofs but with unit_test in place of coprime_test.
   ============================================================================ *)

(* ufilter conditional axioms on ctxtU *)
fun ufilterNil_U nt = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU nt)] ufilter_nil_vU);
fun ufilterIn_U (nt,rt,rst) hcond =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("n",0), ctermU nt),(("r",0), ctermU rt),(("rs",0), ctermU rst)] ufilter_cons_in_vU)) hcond;
fun ufilterOut_U (nt,rt,rst) hncond =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("n",0), ctermU nt),(("r",0), ctermU rt),(("rs",0), ctermU rst)] ufilter_cons_out_vU)) hncond;
fun urrlDef_U nt = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU nt)] urrl_def_vU);
fun phiUDef_U nt = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU nt)] phiU_def_vU);
fun list_induct_U (Pabs, LT) baseThm stepThm =
  let val ind = beta_norm (Drule.infer_instantiate ctxtU
        [(("P",0), ctermU Pabs),(("a",0), ctermU LT)] list_induct_vU)
  in Thm.implies_elim (Thm.implies_elim ind baseThm) stepThm end;

(* ---------------------------------------------------------------------------
   ufilter_sublist : lmem x (ufilter n L) ==> lmem x L
   --------------------------------------------------------------------------- *)
val ufilter_sublist =
  let
    val xF = Free("x", natT); val nF = Free("n", natT)
    fun concBody zt = mkImp (lmem xF (ufilter nF zt)) (lmem xF zt)
    val zQ = Free("zQ", natlistT)
    val Qpred = Term.lambda zQ (concBody zQ)
    val LF = Free("L", natlistT)
    val base =
      let val hassm = Thm.assume (ctermU (jT (lmem xF (ufilter nF lnilC))))
          val lrn = ufilterNil_U nF
          val mem_lnil = lmem_leq_U (xF, ufilter nF lnilC, lnilC) lrn hassm
          val ff  = Thm.implies_elim (lmemNilElim_U xF) mem_lnil
          val conc = Thm.implies_elim (oFalse_elim_U (lmem xF lnilC)) ff
          val dis  = Thm.implies_intr (ctermU (jT (lmem xF (ufilter nF lnilC)))) conc
      in impI_U (lmem xF (ufilter nF lnilC), lmem xF lnilC) dis end
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val ihprop = jT (concBody tF)
    val IH = Thm.assume (ctermU ihprop)
    val stepConcl =
      let
        val hassm = Thm.assume (ctermU (jT (lmem xF (ufilter nF (lcons hF tF)))))
        val cond = unit_test nF hF
        val caseIn =
          let val hcond = Thm.assume (ctermU (jT cond))
              val lrw = ufilterIn_U (nF, hF, tF) hcond
              val mem_cons = lmem_leq_U (xF, ufilter nF (lcons hF tF), lcons hF (ufilter nF tF)) lrw hassm
              val dj = Thm.implies_elim (lmemConsFwd_U (xF, hF, ufilter nF tF)) mem_cons
              val cA = let val hxh = Thm.assume (ctermU (jT (oeq xF hF)))
                           val r = Thm.implies_elim (lmemConsBwd_U (xF, hF, tF))
                                     (disjI1_U (oeq xF hF, lmem xF tF) hxh)
                       in Thm.implies_intr (ctermU (jT (oeq xF hF))) r end
              val cB = let val hmr = Thm.assume (ctermU (jT (lmem xF (ufilter nF tF))))
                           val mt = mp_U (lmem xF (ufilter nF tF), lmem xF tF) IH hmr
                           val r = Thm.implies_elim (lmemConsBwd_U (xF, hF, tF))
                                     (disjI2_U (oeq xF hF, lmem xF tF) mt)
                       in Thm.implies_intr (ctermU (jT (lmem xF (ufilter nF tF)))) r end
              val res = disjE_U (oeq xF hF, lmem xF (ufilter nF tF), lmem xF (lcons hF tF)) dj cA cB
          in Thm.implies_intr (ctermU (jT cond)) res end
        val caseOut =
          let val hncond = Thm.assume (ctermU (jT (neg cond)))
              val lrw = ufilterOut_U (nF, hF, tF) hncond
              val mem_t' = lmem_leq_U (xF, ufilter nF (lcons hF tF), ufilter nF tF) lrw hassm
              val mem_t  = mp_U (lmem xF (ufilter nF tF), lmem xF tF) IH mem_t'
              val dj = disjI2_U (oeq xF hF, lmem xF tF) mem_t
              val res = Thm.implies_elim (lmemConsBwd_U (xF, hF, tF)) dj
          in Thm.implies_intr (ctermU (jT (neg cond))) res end
        val em = em_U cond
        val conc = disjE_U (cond, neg cond, lmem xF (lcons hF tF)) em caseIn caseOut
        val dis = Thm.implies_intr (ctermU (jT (lmem xF (ufilter nF (lcons hF tF))))) conc
      in impI_U (lmem xF (ufilter nF (lcons hF tF)), lmem xF (lcons hF tF)) dis end
    val step = Thm.forall_intr (ctermU hF)
                 (Thm.forall_intr (ctermU tF) (Thm.implies_intr (ctermU ihprop) stepConcl))
    val concl = list_induct_U (Qpred, LF) base step
  in varify concl end;
val () = if length (Thm.hyps_of ufilter_sublist) = 0 then out "OK ufilter_sublist\n" else out "FAIL ufilter_sublist\n";
val ufilter_sublist_vU = ufilter_sublist;
fun ufilter_sublist_U (xt,nt,Lt) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("x",0), ctermU xt),(("n",0), ctermU nt),(("L",0), ctermU Lt)] ufilter_sublist_vU)
  in mp_U (lmem xt (ufilter nt Lt), lmem xt Lt) inst hmem end;

val () = out "BJ0_UFILTER_SUBLIST_OK\n";

(* ---------------------------------------------------------------------------
   lnodup_ufilter : lnodup L ==> lnodup (ufilter n L)
   --------------------------------------------------------------------------- *)
val lnodup_ufilter =
  let
    val nF = Free("n", natT)
    fun concBody zt = mkImp (lnodup zt) (lnodup (ufilter nF zt))
    val zQ = Free("zQ", natlistT)
    val Qpred = Term.lambda zQ (concBody zQ)
    val LF = Free("L", natlistT)
    val base =
      let val hnd = Thm.assume (ctermU (jT (lnodup lnilC)))
          val lrn = ufilterNil_U nF
          val lrn_s = leq_sym_U (ufilter nF lnilC, lnilC) lrn
          val res = lnodup_leq_U (lnilC, ufilter nF lnilC) lrn_s hnd
          val dis = Thm.implies_intr (ctermU (jT (lnodup lnilC))) res
      in impI_U (lnodup lnilC, lnodup (ufilter nF lnilC)) dis end
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val ihprop = jT (concBody tF)
    val IH = Thm.assume (ctermU ihprop)
    val stepConcl =
      let
        val hnd = Thm.assume (ctermU (jT (lnodup (lcons hF tF))))
        val cj  = Thm.implies_elim (lnodupConsFwd_U (hF, tF)) hnd
        val nmem = conjunct1_U (neg (lmem hF tF), lnodup tF) cj
        val ndt  = conjunct2_U (neg (lmem hF tF), lnodup tF) cj
        val ndrt = mp_U (lnodup tF, lnodup (ufilter nF tF)) IH ndt
        val cond = unit_test nF hF
        val caseIn =
          let val hcond = Thm.assume (ctermU (jT cond))
              val lrw = ufilterIn_U (nF, hF, tF) hcond
              val nmem_rt =
                let val hassm = Thm.assume (ctermU (jT (lmem hF (ufilter nF tF))))
                    val inT   = ufilter_sublist_U (hF, nF, tF) hassm
                    val ff    = mp_U (lmem hF tF, oFalseC) nmem inT
                    val dis   = Thm.implies_intr (ctermU (jT (lmem hF (ufilter nF tF)))) ff
                in impI_U (lmem hF (ufilter nF tF), oFalseC) dis end
              val cj2 = conjI_U (neg (lmem hF (ufilter nF tF)), lnodup (ufilter nF tF)) nmem_rt ndrt
              val nd_target = Thm.implies_elim (lnodupConsBwd_U (hF, ufilter nF tF)) cj2
              val lrw_s = leq_sym_U (ufilter nF (lcons hF tF), lcons hF (ufilter nF tF)) lrw
              val res = lnodup_leq_U (lcons hF (ufilter nF tF), ufilter nF (lcons hF tF)) lrw_s nd_target
          in Thm.implies_intr (ctermU (jT cond)) res end
        val caseOut =
          let val hncond = Thm.assume (ctermU (jT (neg cond)))
              val lrw = ufilterOut_U (nF, hF, tF) hncond
              val lrw_s = leq_sym_U (ufilter nF (lcons hF tF), ufilter nF tF) lrw
              val res = lnodup_leq_U (ufilter nF tF, ufilter nF (lcons hF tF)) lrw_s ndrt
          in Thm.implies_intr (ctermU (jT (neg cond))) res end
        val em = em_U cond
        val conc = disjE_U (cond, neg cond, lnodup (ufilter nF (lcons hF tF))) em caseIn caseOut
        val dis = Thm.implies_intr (ctermU (jT (lnodup (lcons hF tF)))) conc
      in impI_U (lnodup (lcons hF tF), lnodup (ufilter nF (lcons hF tF))) dis end
    val step = Thm.forall_intr (ctermU hF)
                 (Thm.forall_intr (ctermU tF) (Thm.implies_intr (ctermU ihprop) stepConcl))
    val concl = list_induct_U (Qpred, LF) base step
  in varify concl end;
val () = if length (Thm.hyps_of lnodup_ufilter) = 0 then out "OK lnodup_ufilter\n" else out "FAIL lnodup_ufilter\n";
val lnodup_ufilter_vU = lnodup_ufilter;
fun lnodup_ufilter_U (nt,Lt) hnd =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("n",0), ctermU nt),(("L",0), ctermU Lt)] lnodup_ufilter_vU)
  in mp_U (lnodup Lt, lnodup (ufilter nt Lt)) inst hnd end;

val () = out "BJ0_LNODUP_UFILTER_OK\n";

(* unit_test rewrite predicate (Free-based; unit_test has nested finv Abs) *)
fun unit_test_pred nF = let val zF = Free("z_ut", natT) in Term.lambda zF (unit_test nF zF) end;

(* ---------------------------------------------------------------------------
   lmem_ufilter_fwd : lmem r (ufilter n L) ==> Conj (lmem r L)(unit_test n r)
   --------------------------------------------------------------------------- *)
val lmem_ufilter_fwd =
  let
    val rF = Free("r", natT); val nF = Free("n", natT)
    fun goalC zt = mkConj (lmem rF zt) (unit_test nF rF)
    fun concBody zt = mkImp (lmem rF (ufilter nF zt)) (goalC zt)
    val zQ = Free("zQ", natlistT)
    val Qpred = Term.lambda zQ (concBody zQ)
    val LF = Free("L", natlistT)
    val base =
      let val hassm = Thm.assume (ctermU (jT (lmem rF (ufilter nF lnilC))))
          val lrn = ufilterNil_U nF
          val mem_lnil = lmem_leq_U (rF, ufilter nF lnilC, lnilC) lrn hassm
          val ff  = Thm.implies_elim (lmemNilElim_U rF) mem_lnil
          val conc = Thm.implies_elim (oFalse_elim_U (goalC lnilC)) ff
          val dis  = Thm.implies_intr (ctermU (jT (lmem rF (ufilter nF lnilC)))) conc
      in impI_U (lmem rF (ufilter nF lnilC), goalC lnilC) dis end
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val ihprop = jT (concBody tF)
    val IH = Thm.assume (ctermU ihprop)
    val stepConcl =
      let
        val hassm = Thm.assume (ctermU (jT (lmem rF (ufilter nF (lcons hF tF)))))
        val cond = unit_test nF hF
        val caseIn =
          let val hcond = Thm.assume (ctermU (jT cond))
              val lrw = ufilterIn_U (nF, hF, tF) hcond
              val mem_cons = lmem_leq_U (rF, ufilter nF (lcons hF tF), lcons hF (ufilter nF tF)) lrw hassm
              val dj = Thm.implies_elim (lmemConsFwd_U (rF, hF, ufilter nF tF)) mem_cons
              val cA =
                let val hrh = Thm.assume (ctermU (jT (oeq rF hF)))
                    val mem_rt = Thm.implies_elim (lmemConsBwd_U (rF, hF, tF))
                                   (disjI1_U (oeq rF hF, lmem rF tF) hrh)
                    val hrh_s = oeq_sym_vU OF [hrh]                  (* oeq h r *)
                    val cop_r = oeq_rw_U (unit_test_pred nF, hF, rF) hrh_s hcond  (* unit_test n r *)
                    val cj = conjI_U (lmem rF (lcons hF tF), unit_test nF rF) mem_rt cop_r
                in Thm.implies_intr (ctermU (jT (oeq rF hF))) cj end
              val cB =
                let val hmr = Thm.assume (ctermU (jT (lmem rF (ufilter nF tF))))
                    val cjt = mp_U (lmem rF (ufilter nF tF), goalC tF) IH hmr
                    val mem_t = conjunct1_U (lmem rF tF, unit_test nF rF) cjt
                    val cop_r = conjunct2_U (lmem rF tF, unit_test nF rF) cjt
                    val mem_cons2 = Thm.implies_elim (lmemConsBwd_U (rF, hF, tF))
                                      (disjI2_U (oeq rF hF, lmem rF tF) mem_t)
                    val cj = conjI_U (lmem rF (lcons hF tF), unit_test nF rF) mem_cons2 cop_r
                in Thm.implies_intr (ctermU (jT (lmem rF (ufilter nF tF)))) cj end
              val res = disjE_U (oeq rF hF, lmem rF (ufilter nF tF), goalC (lcons hF tF)) dj cA cB
          in Thm.implies_intr (ctermU (jT cond)) res end
        val caseOut =
          let val hncond = Thm.assume (ctermU (jT (neg cond)))
              val lrw = ufilterOut_U (nF, hF, tF) hncond
              val mem_t' = lmem_leq_U (rF, ufilter nF (lcons hF tF), ufilter nF tF) lrw hassm
              val cjt = mp_U (lmem rF (ufilter nF tF), goalC tF) IH mem_t'
              val mem_t = conjunct1_U (lmem rF tF, unit_test nF rF) cjt
              val cop_r = conjunct2_U (lmem rF tF, unit_test nF rF) cjt
              val mem_cons = Thm.implies_elim (lmemConsBwd_U (rF, hF, tF))
                               (disjI2_U (oeq rF hF, lmem rF tF) mem_t)
              val cj = conjI_U (lmem rF (lcons hF tF), unit_test nF rF) mem_cons cop_r
          in Thm.implies_intr (ctermU (jT (neg cond))) cj end
        val em = em_U cond
        val conc = disjE_U (cond, neg cond, goalC (lcons hF tF)) em caseIn caseOut
        val dis = Thm.implies_intr (ctermU (jT (lmem rF (ufilter nF (lcons hF tF))))) conc
      in impI_U (lmem rF (ufilter nF (lcons hF tF)), goalC (lcons hF tF)) dis end
    val step = Thm.forall_intr (ctermU hF)
                 (Thm.forall_intr (ctermU tF) (Thm.implies_intr (ctermU ihprop) stepConcl))
    val concl = list_induct_U (Qpred, LF) base step
  in varify concl end;
val () = if length (Thm.hyps_of lmem_ufilter_fwd) = 0 then out "OK lmem_ufilter_fwd\n" else out "FAIL lmem_ufilter_fwd\n";
val lmem_ufilter_fwd_vU = lmem_ufilter_fwd;
fun lmem_ufilter_fwd_U (rt,nt,Lt) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("r",0), ctermU rt),(("n",0), ctermU nt),(("L",0), ctermU Lt)] lmem_ufilter_fwd_vU)
  in mp_U (lmem rt (ufilter nt Lt), mkConj (lmem rt Lt)(unit_test nt rt)) inst hmem end;

val () = out "BJ0_LMEM_UFILTER_FWD_OK\n";

(* ---------------------------------------------------------------------------
   lmem_ufilter_bwd : Conj (lmem r L)(unit_test n r) ==> lmem r (ufilter n L)
   --------------------------------------------------------------------------- *)
val lmem_ufilter_bwd =
  let
    val rF = Free("r", natT); val nF = Free("n", natT)
    fun hypC zt = mkConj (lmem rF zt) (unit_test nF rF)
    fun concBody zt = mkImp (hypC zt) (lmem rF (ufilter nF zt))
    val zQ = Free("zQ", natlistT)
    val Qpred = Term.lambda zQ (concBody zQ)
    val LF = Free("L", natlistT)
    val base =
      let val hcj = Thm.assume (ctermU (jT (hypC lnilC)))
          val mem = conjunct1_U (lmem rF lnilC, unit_test nF rF) hcj
          val ff  = Thm.implies_elim (lmemNilElim_U rF) mem
          val conc = Thm.implies_elim (oFalse_elim_U (lmem rF (ufilter nF lnilC))) ff
          val dis = Thm.implies_intr (ctermU (jT (hypC lnilC))) conc
      in impI_U (hypC lnilC, lmem rF (ufilter nF lnilC)) dis end
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val ihprop = jT (concBody tF)
    val IH = Thm.assume (ctermU ihprop)
    val stepConcl =
      let
        val hcj  = Thm.assume (ctermU (jT (hypC (lcons hF tF))))
        val memC = conjunct1_U (lmem rF (lcons hF tF), unit_test nF rF) hcj
        val cop_r= conjunct2_U (lmem rF (lcons hF tF), unit_test nF rF) hcj
        val dj   = Thm.implies_elim (lmemConsFwd_U (rF, hF, tF)) memC
        val cond = unit_test nF hF
        val goalMem = lmem rF (ufilter nF (lcons hF tF))
        val caseIn =
          let val hcond = Thm.assume (ctermU (jT cond))
              val lrw = ufilterIn_U (nF, hF, tF) hcond
              val lrw_s = leq_sym_U (ufilter nF (lcons hF tF), lcons hF (ufilter nF tF)) lrw
              val cA = let val hrh = Thm.assume (ctermU (jT (oeq rF hF)))
                           val m = Thm.implies_elim (lmemConsBwd_U (rF, hF, ufilter nF tF))
                                     (disjI1_U (oeq rF hF, lmem rF (ufilter nF tF)) hrh)
                       in Thm.implies_intr (ctermU (jT (oeq rF hF))) m end
              val cB = let val hmt = Thm.assume (ctermU (jT (lmem rF tF)))
                           val cjt = conjI_U (lmem rF tF, unit_test nF rF) hmt cop_r
                           val mrt = mp_U (hypC tF, lmem rF (ufilter nF tF)) IH cjt
                           val m = Thm.implies_elim (lmemConsBwd_U (rF, hF, ufilter nF tF))
                                     (disjI2_U (oeq rF hF, lmem rF (ufilter nF tF)) mrt)
                       in Thm.implies_intr (ctermU (jT (lmem rF tF))) m end
              val memCons = disjE_U (oeq rF hF, lmem rF tF, lmem rF (lcons hF (ufilter nF tF))) dj cA cB
              val res = lmem_leq_U (rF, lcons hF (ufilter nF tF), ufilter nF (lcons hF tF)) lrw_s memCons
          in Thm.implies_intr (ctermU (jT cond)) res end
        val caseOut =
          let val hncond = Thm.assume (ctermU (jT (neg cond)))
              val lrw = ufilterOut_U (nF, hF, tF) hncond
              val lrw_s = leq_sym_U (ufilter nF (lcons hF tF), ufilter nF tF) lrw
              val cA = let val hrh = Thm.assume (ctermU (jT (oeq rF hF)))
                           val cop_h = oeq_rw_U (unit_test_pred nF, rF, hF) hrh cop_r   (* unit_test n h *)
                           val ff = mp_U (cond, oFalseC) hncond cop_h
                           val m  = Thm.implies_elim (oFalse_elim_U (lmem rF (ufilter nF tF))) ff
                       in Thm.implies_intr (ctermU (jT (oeq rF hF))) m end
              val cB = let val hmt = Thm.assume (ctermU (jT (lmem rF tF)))
                           val cjt = conjI_U (lmem rF tF, unit_test nF rF) hmt cop_r
                           val mrt = mp_U (hypC tF, lmem rF (ufilter nF tF)) IH cjt
                       in Thm.implies_intr (ctermU (jT (lmem rF tF))) mrt end
              val memT = disjE_U (oeq rF hF, lmem rF tF, lmem rF (ufilter nF tF)) dj cA cB
              val res = lmem_leq_U (rF, ufilter nF tF, ufilter nF (lcons hF tF)) lrw_s memT
          in Thm.implies_intr (ctermU (jT (neg cond))) res end
        val em = em_U cond
        val conc = disjE_U (cond, neg cond, goalMem) em caseIn caseOut
        val dis = Thm.implies_intr (ctermU (jT (hypC (lcons hF tF)))) conc
      in impI_U (hypC (lcons hF tF), goalMem) dis end
    val step = Thm.forall_intr (ctermU hF)
                 (Thm.forall_intr (ctermU tF) (Thm.implies_intr (ctermU ihprop) stepConcl))
    val concl = list_induct_U (Qpred, LF) base step
  in varify concl end;
val () = if length (Thm.hyps_of lmem_ufilter_bwd) = 0 then out "OK lmem_ufilter_bwd\n" else out "FAIL lmem_ufilter_bwd\n";
val lmem_ufilter_bwd_vU = lmem_ufilter_bwd;
fun lmem_ufilter_bwd_U (rt,nt,Lt) hcj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("r",0), ctermU rt),(("n",0), ctermU nt),(("L",0), ctermU Lt)] lmem_ufilter_bwd_vU)
  in mp_U (mkConj (lmem rt Lt)(unit_test nt rt), lmem rt (ufilter nt Lt)) inst hcj end;

val () = out "BJ0_LMEM_UFILTER_BWD_OK\n";

(* ---- lnodup_upto on ctxtU ---- *)
val lnodup_upto_vU = varify lnodup_upto;
fun lnodup_upto_U nt = beta_norm (Drule.infer_instantiate ctxtU [(("k_nd",0), ctermU nt)] lnodup_upto_vU);

(* ---------------------------------------------------------------------------
   urrl-level : lnodup (urrl n) ; lmem_urrl_fwd ; lmem_urrl_bwd
   urrl n = ufilter n (uptoF (sub n 1))
   --------------------------------------------------------------------------- *)
val lnodup_urrl =
  let val nF = Free("n", natT)
      val rng = uptoF (sub nF (suc ZeroC))
      val ndUpto = lnodup_upto_U (sub nF (suc ZeroC))            (* lnodup (uptoF (sub n 1)) *)
      val ndFilt = lnodup_ufilter_U (nF, rng) ndUpto             (* lnodup (ufilter n rng) *)
      val udef = urrlDef_U nF                                    (* leq (urrl n)(ufilter n rng) *)
      val udef_s = leq_sym_U (urrl nF, ufilter nF rng) udef
      val res = lnodup_leq_U (ufilter nF rng, urrl nF) udef_s ndFilt
  in varify res end;
val () = if length (Thm.hyps_of lnodup_urrl) = 0 then out "OK lnodup_urrl\n" else out "FAIL lnodup_urrl\n";
fun lnodup_urrl_U nt = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU nt)] (varify lnodup_urrl));

val lmem_urrl_fwd =
  let val rF = Free("r", natT); val nF = Free("n", natT)
      val rng = uptoF (sub nF (suc ZeroC))
      val goalC = mkConj (lmem rF rng) (unit_test nF rF)
      val hmemP = jT (lmem rF (urrl nF))
      val hmem  = Thm.assume (ctermU hmemP)
      val udef  = urrlDef_U nF
      val mem_uf= lmem_leq_U (rF, urrl nF, ufilter nF rng) udef hmem
      val cj    = lmem_ufilter_fwd_U (rF, nF, rng) mem_uf
      val res   = Thm.implies_intr (ctermU hmemP) cj
  in varify res end;
val () = if length (Thm.hyps_of lmem_urrl_fwd) = 0 then out "OK lmem_urrl_fwd\n" else out "FAIL lmem_urrl_fwd\n";
fun lmem_urrl_fwd_U (rt,nt) hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("r",0), ctermU rt),(("n",0), ctermU nt)] (varify lmem_urrl_fwd))
  in Thm.implies_elim inst hmem end;

val lmem_urrl_bwd =
  let val rF = Free("r", natT); val nF = Free("n", natT)
      val rng = uptoF (sub nF (suc ZeroC))
      val hypC = mkConj (lmem rF rng) (unit_test nF rF)
      val hcj  = Thm.assume (ctermU (jT hypC))
      val mem_uf = lmem_ufilter_bwd_U (rF, nF, rng) hcj
      val udef = urrlDef_U nF
      val udef_s = leq_sym_U (urrl nF, ufilter nF rng) udef
      val res_mem = lmem_leq_U (rF, ufilter nF rng, urrl nF) udef_s mem_uf
      val res = Thm.implies_intr (ctermU (jT hypC)) res_mem
  in varify res end;
val () = if length (Thm.hyps_of lmem_urrl_bwd) = 0 then out "OK lmem_urrl_bwd\n" else out "FAIL lmem_urrl_bwd\n";
fun lmem_urrl_bwd_U (rt,nt) hcj =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("r",0), ctermU rt),(("n",0), ctermU nt)] (varify lmem_urrl_bwd))
  in Thm.implies_elim inst hcj end;

val () = out "BJ0_URRL_OK\n";

(* ============================================================================
   PHASE L : unit_from_inv (the range-reduction core, on ctxtW) then unit_mult_closed.
   unit_from_inv : 1<n ==> cong n (mult R W) 1 ==> unit_test n R
   (reduce the witness W mod n: b = rmod W n is in [1..n-1] and still an inverse.)
   ============================================================================ *)
val unit_from_inv =
  let
    val nF = Free("n", natT); val RF = Free("R", natT); val WF = Free("W", natT)
    val one = suc ZeroC
    val subn1 = sub nF one
    val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermW hp1P)
    val hcgP = jT (cong nF (mult RF WF) one); val hcg = Thm.assume (ctermW hcgP)
    val hp0 = lt1_imp_lt0_W nF hp1
    val b = rmod WF nF
    (* cong n (mult R b) 1 : W ≡ b, so mult R W ≡ mult R b ≡ 1 *)
    val congWb = cong_self_rmod_W (nF, WF) hp0                  (* cong n W b *)
    val creflR = cong_refl_W (nF, RF)
    val congRWRb = cong_mult_W (nF, RF, RF, WF, b) creflR congWb  (* cong n (mult R W)(mult R b) *)
    val congRbRW = cong_sym_W (nF, mult RF WF, mult RF b) congRWRb
    val congRb1 = cong_trans_W (nF, mult RF b, mult RF WF, one) congRbRW hcg  (* cong n (mult R b) 1 *)
    val bltn = rmod_lt_W (WF, nF) hp0                          (* b < n *)
    (* 0 < b : if b=0 then mult R b ≡ 0 ≡ 1 -> contradiction *)
    val dzb = dzos_W b
    val hb0pos =
      let
        val caseZ =
          let val hbz = Thm.assume (ctermW (jT (oeq b ZeroC)))
              val Rbcong = mult_cong_r_W (RF, b, ZeroC) hbz     (* oeq (mult R b)(mult R 0) *)
              val R0 = mult0r_W RF                              (* oeq (mult R 0) 0 *)
              val Rb0 = oeq_trans_vW OF [Rbcong, R0]            (* oeq (mult R b) 0 *)
              val Pc = Term.lambda (Free("z_cz2", natT)) (cong nF (Free("z_cz2", natT)) one)
              val cong01 = oeq_rw_W (Pc, mult RF b, ZeroC) Rb0 congRb1  (* cong n 0 1 *)
              val caseL =
                let val hL = Thm.assume (ctermW (jT (congL nF ZeroC one)))
                    val Pk = Abs("k", natT, oeq one (add ZeroC (mult nF (Bound 0))))
                    fun kb k (hk:thm) =
                      let val z0 = add0_W (mult nF k)
                          val one_pk = oeq_trans_vW OF [hk, z0]
                          val dvdp1 = dvd_intro_W (nF, one, k) one_pk
                          val onenz = let val h00 = Thm.assume (ctermW (jT (oeq one ZeroC)))
                                      in Thm.implies_intr (ctermW (jT (oeq one ZeroC))) (Suc_neq_Zero_W ZeroC h00) end
                          val lep1 = dvd_le_W (nF, one) dvdp1 onenz
                          val le21 = le_trans_W (suc one, nF, one) hp1 lep1
                      in lt_irrefl_W one le21 end
                    val r = exE_W (Pk, oFalseC) hL "k_cl2" kb
                in Thm.implies_intr (ctermW (jT (congL nF ZeroC one))) r end
              val caseR =
                let val hR = Thm.assume (ctermW (jT (congR nF ZeroC one)))
                    val Pk = Abs("k", natT, oeq ZeroC (add one (mult nF (Bound 0))))
                    fun kb k (hk:thm) =
                      let val aS = addSuc_W (ZeroC, mult nF k)
                          val zSuc = oeq_trans_vW OF [hk, aS]
                          val sucz = oeq_sym_vW OF [zSuc]
                      in Suc_neq_Zero_W (add ZeroC (mult nF k)) sucz end
                    val r = exE_W (Pk, oFalseC) hR "k_cr2" kb
                in Thm.implies_intr (ctermW (jT (congR nF ZeroC one))) r end
              val fls = disjE_W (congL nF ZeroC one, congR nF ZeroC one, oFalseC) cong01 caseL caseR
              val ltb = Thm.implies_elim (oFalse_elim_W (lt ZeroC b)) fls
          in Thm.implies_intr (ctermW (jT (oeq b ZeroC))) ltb end
        val caseS =
          let val hsP = jT (mkExSuc_W b)
              val hs = Thm.assume (ctermW hsP)
              val Pq = Abs("q", natT, oeq b (suc (Bound 0)))
              fun sb k (hk:thm) =
                let val a1 = addSuc_W (ZeroC, k)
                    val a0 = add0_W k
                    val sa0= Suc_cong_vW OF [a0]
                    val sum= oeq_trans_vW OF [a1, sa0]
                    val sumS = oeq_sym_vW OF [sum]
                    val lt0Sk = le_intro_W (suc ZeroC, suc k, k) sumS
                    val hk_s = oeq_sym_vW OF [hk]
                    val Plt = Term.lambda (Free("z_p0", natT)) (lt ZeroC (Free("z_p0", natT)))
                in oeq_rw_W (Plt, suc k, b) hk_s lt0Sk end
              val r = exE_W (Pq, lt ZeroC b) hs "k_bs" sb
          in Thm.implies_intr (ctermW (jT (mkExSuc_W b))) r end
      in disjE_W (oeq b ZeroC, mkExSuc_W b, lt ZeroC b) dzb caseZ caseS end
    (* b <= n-1 from b < n, and lmem b (uptoF (sub n 1)) *)
    val memB =
      let val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW nF)] pos_pred)) hp1
          fun predBody q (hq:thm) =   (* hq : oeq n (Suc q) *)
            let val Plt = Term.lambda (Free("z_bp", natT)) (lt b (Free("z_bp", natT)))
                val ltbSq = oeq_rw_W (Plt, nF, suc q) hq bltn      (* b < Suc q *)
                val lebq = lt_suc_imp_le_W (b, q) ltbSq            (* b <= q *)
                val e1 = subSS_W (q, ZeroC)
                val e2 = sub0_W q
                val subSucq = oeq_trans_vW OF [e1, e2]             (* oeq (sub (Suc q) (Suc 0)) q *)
                val hq_s = oeq_sym_vW OF [hq]
                val Psub = Term.lambda (Free("z_sb2", natT)) (oeq (sub (Free("z_sb2", natT)) one) q)
                val subP = oeq_rw_W (Psub, suc q, nF) hq_s subSucq (* oeq (sub n 1) q *)
                val subP_s = oeq_sym_vW OF [subP]
                val Ple = Term.lambda (Free("z_le2", natT)) (le b (Free("z_le2", natT)))
                val lebsub = oeq_rw_W (Ple, q, subn1) subP_s lebq  (* b <= sub n 1 *)
                val cj = conjI_W (lt ZeroC b, le b subn1) hb0pos lebsub
            in lmem_upto_bwd_W (b, subn1) cj end
          val res = exE_W (Abs("q", natT, oeq nF (suc (Bound 0))), lmem b (uptoF subn1)) predEx "q_mr" predBody
      in res end
    (* inv_imp_unit (n, R, b) hp1 memB congRb1 : unit_test n R *)
    val ut = inv_imp_unit_W (nF, RF, b) hp1 memB congRb1
    val d2 = Thm.implies_intr (ctermW hcgP) ut
    val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of unit_from_inv) = 0 then out "OK unit_from_inv\n" else out "FAIL unit_from_inv\n";
fun unit_from_inv_W (nt,Rt,Wt) hp1 hcg =
  let val inst = beta_norm (Drule.infer_instantiate ctxtW
        [(("n",0), ctermW nt),(("R",0), ctermW Rt),(("W",0), ctermW Wt)] unit_from_inv)
  in Thm.implies_elim (Thm.implies_elim inst hp1) hcg end;
val unit_from_inv_vU = varify unit_from_inv;
fun unit_from_inv_U (nt,Rt,Wt) hp1 hcg =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("n",0), ctermU nt),(("R",0), ctermU Rt),(("W",0), ctermU Wt)] unit_from_inv_vU)
  in Thm.implies_elim (Thm.implies_elim inst hp1) hcg end;

val () = out "BJ0_UNIT_FROM_INV_OK\n";

(* ============================================================================
   PHASE M : unit_mult_closed (product of units is a unit), on ctxtU.
   ============================================================================ *)
(* algebra : oeq (mult (mult x y)(mult u v)) (mult (mult x u)(mult y v))  [comm+assoc] *)
fun mult4_rearrange_U (x,y,u,v) =
  let
    (* (x*y)*(u*v) = x*(y*(u*v))            assoc                                   *)
    val e1 = multassoc_U (x, y, mult u v)                       (* ((x*y)*(u*v)) = x*(y*(u*v)) *)
    (* y*(u*v) = (y*u)*v  (assoc sym)                                               *)
    val e2 = oeq_sym_vU OF [multassoc_U (y, u, v)]              (* y*(u*v) = (y*u)*v *)
    (* y*u = u*y (comm) -> (y*u)*v = (u*y)*v                                        *)
    val ec = multcomm_U (y, u)                                  (* y*u = u*y *)
    val Pe = Term.lambda (Free("ze", natT)) (oeq (mult (mult y u) v) (mult (Free("ze", natT)) v))
    val e3 = oeq_rw_U (Pe, mult y u, mult u y) ec (oeqRefl_U (mult (mult y u) v))  (* (y*u)*v = (u*y)*v *)
    (* (u*y)*v = u*(y*v)  assoc                                                     *)
    val e4 = multassoc_U (u, y, v)                              (* (u*y)*v = u*(y*v) *)
    (* chain : y*(u*v) = (y*u)*v = (u*y)*v = u*(y*v) *)
    val yuv = oeq_trans_vU OF [e2, oeq_trans_vU OF [e3, e4]]    (* y*(u*v) = u*(y*v) *)
    (* x*(y*(u*v)) = x*(u*(y*v))  cong on left arg x *)
    val Px = Term.lambda (Free("zx", natT)) (oeq (mult x (mult y (mult u v))) (mult x (Free("zx", natT))))
    val e5 = oeq_rw_U (Px, mult y (mult u v), mult u (mult y v)) yuv
               (oeqRefl_U (mult x (mult y (mult u v))))         (* x*(y*(u*v)) = x*(u*(y*v)) *)
    (* x*(u*(y*v)) = (x*u)*(y*v)  assoc sym *)
    val e6 = oeq_sym_vU OF [multassoc_U (x, u, mult y v)]       (* x*(u*(y*v)) = (x*u)*(y*v) *)
    (* chain all : (x*y)*(u*v) = x*(y*(u*v)) = x*(u*(y*v)) = (x*u)*(y*v) *)
  in oeq_trans_vU OF [e1, oeq_trans_vU OF [e5, e6]] end;

val unit_mult_closed =
  let
    val nF = Free("n", natT); val xF = Free("x", natT); val yF = Free("y", natT)
    val one = suc ZeroC
    val fx = finv nF xF; val fy = finv nF yF
    val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermU hp1P)
    val hutxP = jT (unit_test nF xF); val hutx = Thm.assume (ctermU hutxP)
    val hutyP = jT (unit_test nF yF); val huty = Thm.assume (ctermU hutyP)
    val R = rmod (mult xF yF) nF
    val W = mult fx fy
    (* cong n (mult x fx) 1 ; cong n (mult y fy) 1 *)
    val cx = unit_has_inv_U (nF, xF) hp1 hutx                   (* cong n (mult x fx) 1 *)
    val cy = unit_has_inv_U (nF, yF) hp1 huty                   (* cong n (mult y fy) 1 *)
    (* cong n ((x*fx)*(y*fy)) (1*1) *)
    val cprod = cong_mult_U (nF, mult xF fx, one, mult yF fy, one) cx cy  (* cong n ((x*fx)*(y*fy)) (1*1) *)
    (* 1*1 = 1 *)
    val e11 = mult1l_U one                                      (* oeq (mult 1 1) 1 *)
    val cong_11_1 = cong_of_eq_U (nF, mult one one, one) e11    (* cong n (1*1) 1 *)
    val cprod1 = cong_trans_U (nF, mult (mult xF fx)(mult yF fy), mult one one, one) cprod cong_11_1
                                                                (* cong n ((x*fx)*(y*fy)) 1 *)
    (* (x*y)*(fx*fy) = (x*fx)*(y*fy)  algebra *)
    val ealg = mult4_rearrange_U (xF, yF, fx, fy)               (* oeq ((x*y)*(fx*fy)) ((x*fx)*(y*fy)) *)
    val cong_alg = cong_of_eq_U (nF, mult (mult xF yF)(mult fx fy), mult (mult xF fx)(mult yF fy)) ealg
    val cong_xyW_1 = cong_trans_U (nF, mult (mult xF yF)(mult fx fy), mult (mult xF fx)(mult yF fy), one) cong_alg cprod1
                                                                (* cong n ((x*y)*(fx*fy)) 1 *)
    (* R = rmod (x*y) n ≡ (x*y) ; cong n (mult R W)(mult (x*y) W) ≡ 1 *)
    val hp0 = lt1_imp_lt0_W nF hp1
    val congxyR = cong_self_rmod_W (nF, mult xF yF) hp0          (* cong n (x*y) R *)
    val congRxy = cong_sym_U (nF, mult xF yF, R) congxyR         (* cong n R (x*y) *)
    val creflW = cong_refl_U (nF, W)
    val cong_RW_xyW = cong_mult_U (nF, R, mult xF yF, W, W) congRxy creflW  (* cong n (mult R W)(mult (x*y) W) *)
    val cong_RW_1 = cong_trans_U (nF, mult R W, mult (mult xF yF) W, one) cong_RW_xyW cong_xyW_1
                                                                (* cong n (mult R W) 1 *)
    (* unit_from_inv : unit_test n R *)
    val ut = unit_from_inv_U (nF, R, W) hp1 cong_RW_1
    val d3 = Thm.implies_intr (ctermU hutyP) ut
    val d2 = Thm.implies_intr (ctermU hutxP) d3
    val d1 = Thm.implies_intr (ctermU hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of unit_mult_closed) = 0 then out "OK unit_mult_closed\n" else out "FAIL unit_mult_closed\n";
fun unit_mult_closed_U (nt,xt,yt) hp1 hutx huty =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("n",0), ctermU nt),(("x",0), ctermU xt),(("y",0), ctermU yt)] unit_mult_closed)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hp1) hutx) huty end;

val () = out "BJ0_UNIT_MULT_CLOSED_OK\n";

(* ============================================================================
   PHASE N : range helpers + unit_pos (on ctxtW, re-instantiated to U).
   ============================================================================ *)

(* le_imp_lt_suc : le r q ==> lt r (Suc q)   (lt r (Suc q) = le (Suc r)(Suc q)) *)
val le_imp_lt_suc =
  let val rF = Free("r", natT); val qF = Free("q", natT)
      val hleP = jT (le rF qF); val hle = Thm.assume (ctermW hleP)
      val Pk = Abs("k", natT, oeq qF (add rF (Bound 0)))
      fun kb k (hk:thm) =   (* hk : oeq q (add r k) *)
        let val sq = Suc_cong_vW OF [hk]                  (* oeq (Suc q)(Suc (add r k)) *)
            val aS = addSuc_W (rF, k)                     (* oeq (add (Suc r) k)(Suc (add r k)) *)
            val aSs = oeq_sym_vW OF [aS]                  (* oeq (Suc (add r k))(add (Suc r) k) *)
            val sqk = oeq_trans_vW OF [sq, aSs]           (* oeq (Suc q)(add (Suc r) k) *)
        in le_intro_W (suc rF, suc qF, k) sqk end          (* le (Suc r)(Suc q) = lt r (Suc q) *)
      val res = exE_W (Pk, lt rF (suc qF)) hle "k_lils" kb
      val d1 = Thm.implies_intr (ctermW hleP) res
  in varify d1 end;
val () = if length (Thm.hyps_of le_imp_lt_suc) = 0 then out "OK le_imp_lt_suc\n" else out "FAIL le_imp_lt_suc\n";

(* mem_range_imp_lt : 1<n ==> lmem r (uptoF (sub n 1)) ==> lt r n *)
val mem_range_imp_lt =
  let val nF = Free("n", natT); val rF = Free("r", natT)
      val one = suc ZeroC; val subn1 = sub nF one
      val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermW hp1P)
      val hmemP = jT (lmem rF (uptoF subn1)); val hmem = Thm.assume (ctermW hmemP)
      val cj = lmem_upto_fwd_W (rF, subn1) hmem                (* 0<r /\ le r (sub n 1) *)
      val lerq = conjunct2_W (lt ZeroC rF, le rF subn1) cj     (* le r (sub n 1) *)
      val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW nF)] pos_pred)) hp1
      fun pbody q (hq:thm) =   (* hq : oeq n (Suc q) *)
        let val e1 = subSS_W (q, ZeroC); val e2 = sub0_W q
            val subSucq = oeq_trans_vW OF [e1, e2]             (* oeq (sub (Suc q) 1) q *)
            val hq_s = oeq_sym_vW OF [hq]
            val Psub = Term.lambda (Free("z_sb", natT)) (oeq (sub (Free("z_sb", natT)) one) q)
            val subP = oeq_rw_W (Psub, suc q, nF) hq_s subSucq (* oeq (sub n 1) q *)
            val Ple = Term.lambda (Free("z_le", natT)) (le rF (Free("z_le", natT)))
            val lerq2 = oeq_rw_W (Ple, subn1, q) subP lerq     (* le r q *)
            val ltrSq = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
                          [(("r",0), ctermW rF),(("q",0), ctermW q)] le_imp_lt_suc)) lerq2  (* lt r (Suc q) *)
            val Plt = Term.lambda (Free("z_lt", natT)) (lt rF (Free("z_lt", natT)))
            val hq_ss = oeq_sym_vW OF [hq_s]                   (* oeq n (Suc q) ; actually hq itself *)
        in oeq_rw_W (Plt, suc q, nF) hq_s ltrSq end            (* lt r n *)
      val res = exE_W (Abs("q", natT, oeq nF (suc (Bound 0))), lt rF nF) predEx "q_mril" pbody
      val d2 = Thm.implies_intr (ctermW hmemP) res
      val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of mem_range_imp_lt) = 0 then out "OK mem_range_imp_lt\n" else out "FAIL mem_range_imp_lt\n";
fun mem_range_imp_lt_U (nt,rt) hp1 hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("n",0), ctermU nt),(("r",0), ctermU rt)] (varify mem_range_imp_lt))
  in Thm.implies_elim (Thm.implies_elim inst hp1) hmem end;

(* pos_lt_imp_mem : 1<n ==> 0<r ==> lt r n ==> lmem r (uptoF (sub n 1)) *)
val pos_lt_imp_mem =
  let val nF = Free("n", natT); val rF = Free("r", natT)
      val one = suc ZeroC; val subn1 = sub nF one
      val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermW hp1P)
      val hposP = jT (lt ZeroC rF); val hpos = Thm.assume (ctermW hposP)
      val hltP = jT (lt rF nF); val hlt = Thm.assume (ctermW hltP)
      val predEx = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW [(("p",0), ctermW nF)] pos_pred)) hp1
      fun pbody q (hq:thm) =   (* hq : oeq n (Suc q) *)
        let val Plt = Term.lambda (Free("z_bp", natT)) (lt rF (Free("z_bp", natT)))
            val ltrSq = oeq_rw_W (Plt, nF, suc q) hq hlt       (* lt r (Suc q) *)
            val lerq = lt_suc_imp_le_W (rF, q) ltrSq           (* le r q *)
            val e1 = subSS_W (q, ZeroC); val e2 = sub0_W q
            val subSucq = oeq_trans_vW OF [e1, e2]
            val hq_s = oeq_sym_vW OF [hq]
            val Psub = Term.lambda (Free("z_sb2", natT)) (oeq (sub (Free("z_sb2", natT)) one) q)
            val subP = oeq_rw_W (Psub, suc q, nF) hq_s subSucq (* oeq (sub n 1) q *)
            val subP_s = oeq_sym_vW OF [subP]
            val Ple = Term.lambda (Free("z_le2", natT)) (le rF (Free("z_le2", natT)))
            val lersub = oeq_rw_W (Ple, q, subn1) subP_s lerq  (* le r (sub n 1) *)
            val cj = conjI_W (lt ZeroC rF, le rF subn1) hpos lersub
        in lmem_upto_bwd_W (rF, subn1) cj end
      val res = exE_W (Abs("q", natT, oeq nF (suc (Bound 0))), lmem rF (uptoF subn1)) predEx "q_plim" pbody
      val d3 = Thm.implies_intr (ctermW hltP) res
      val d2 = Thm.implies_intr (ctermW hposP) d3
      val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of pos_lt_imp_mem) = 0 then out "OK pos_lt_imp_mem\n" else out "FAIL pos_lt_imp_mem\n";
fun pos_lt_imp_mem_U (nt,rt) hp1 hpos hlt =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("n",0), ctermU nt),(("r",0), ctermU rt)] (varify pos_lt_imp_mem))
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hp1) hpos) hlt end;

val () = out "BJ0_RANGE_HELPERS_OK\n";

(* ============================================================================
   PHASE O : not_cong_zero_one + unit_pos (on ctxtW, re-instantiated to U).
   ============================================================================ *)
(* not_cong_zero_one : 1<n ==> cong n Zero (Suc Zero) ==> oFalse *)
val not_cong_zero_one =
  let val nF = Free("n", natT); val one = suc ZeroC
      val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermW hp1P)
      val hcgP = jT (cong nF ZeroC one); val hcg = Thm.assume (ctermW hcgP)
      val caseL =
        let val hL = Thm.assume (ctermW (jT (congL nF ZeroC one)))
            val Pk = Abs("k", natT, oeq one (add ZeroC (mult nF (Bound 0))))
            fun kb k (hk:thm) =
              let val z0 = add0_W (mult nF k)
                  val one_pk = oeq_trans_vW OF [hk, z0]            (* oeq 1 (mult n k) *)
                  val dvdp1 = dvd_intro_W (nF, one, k) one_pk
                  val onenz = let val h00 = Thm.assume (ctermW (jT (oeq one ZeroC)))
                              in Thm.implies_intr (ctermW (jT (oeq one ZeroC))) (Suc_neq_Zero_W ZeroC h00) end
                  val lep1 = dvd_le_W (nF, one) dvdp1 onenz
                  val le21 = le_trans_W (suc one, nF, one) hp1 lep1
              in lt_irrefl_W one le21 end
            val r = exE_W (Pk, oFalseC) hL "k_ncl" kb
        in Thm.implies_intr (ctermW (jT (congL nF ZeroC one))) r end
      val caseR =
        let val hR = Thm.assume (ctermW (jT (congR nF ZeroC one)))
            val Pk = Abs("k", natT, oeq ZeroC (add one (mult nF (Bound 0))))
            fun kb k (hk:thm) =
              let val aS = addSuc_W (ZeroC, mult nF k)
                  val zSuc = oeq_trans_vW OF [hk, aS]
                  val sucz = oeq_sym_vW OF [zSuc]
              in Suc_neq_Zero_W (add ZeroC (mult nF k)) sucz end
            val r = exE_W (Pk, oFalseC) hR "k_ncr" kb
        in Thm.implies_intr (ctermW (jT (congR nF ZeroC one))) r end
      val fls = disjE_W (congL nF ZeroC one, congR nF ZeroC one, oFalseC) hcg caseL caseR
      val d2 = Thm.implies_intr (ctermW hcgP) fls
      val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of not_cong_zero_one) = 0 then out "OK not_cong_zero_one\n" else out "FAIL not_cong_zero_one\n";
fun not_cong_zero_one_W nt hp1 hcg =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtW
      [(("n",0), ctermW nt)] not_cong_zero_one)) hp1) hcg;

(* unit_pos : 1<n ==> unit_test n r ==> lt Zero r *)
val unit_pos =
  let val nF = Free("n", natT); val rF = Free("r", natT); val one = suc ZeroC
      val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermW hp1P)
      val hutP = jT (unit_test nF rF); val hut = Thm.assume (ctermW hutP)
      val cong_r1 = unit_has_inv_W (nF, rF) hp1 hut            (* cong n (mult r (finv n r)) 1 *)
      val dzr = dzos_W rF                                      (* Disj (oeq r 0)(Ex Suc) *)
      val caseZ =
        let val hrz = Thm.assume (ctermW (jT (oeq rF ZeroC)))
            (* mult r W -> mult 0 W = 0 *)
            val W = finv nF rF
            val Pm = Term.lambda (Free("zmp", natT)) (cong nF (mult (Free("zmp", natT)) W) one)
            val cong_0W_1 = oeq_rw_W (Pm, rF, ZeroC) hrz cong_r1   (* cong n (mult 0 W) 1 *)
            val m0 = beta_norm (Drule.infer_instantiate ctxtW [(("n",0), ctermW W)] mult_0_vW)  (* oeq (mult 0 W) 0 *)
            val Pc = Term.lambda (Free("zcp", natT)) (cong nF (Free("zcp", natT)) one)
            val cong_0_1 = oeq_rw_W (Pc, mult ZeroC W, ZeroC) m0 cong_0W_1  (* cong n 0 1 *)
            val ff = not_cong_zero_one_W nF hp1 cong_0_1
            val r = Thm.implies_elim (oFalse_elim_W (lt ZeroC rF)) ff
        in Thm.implies_intr (ctermW (jT (oeq rF ZeroC))) r end
      val caseS =
        let val hsP = jT (mkExSuc_W rF); val hs = Thm.assume (ctermW hsP)
            val Pq = Abs("q", natT, oeq rF (suc (Bound 0)))
            fun sb k (hk:thm) =
              let val a1 = addSuc_W (ZeroC, k); val a0 = add0_W k
                  val sa0= Suc_cong_vW OF [a0]; val sum= oeq_trans_vW OF [a1, sa0]
                  val sumS = oeq_sym_vW OF [sum]
                  val lt0Sk = le_intro_W (suc ZeroC, suc k, k) sumS
                  val hk_s = oeq_sym_vW OF [hk]
                  val Plt = Term.lambda (Free("z_pp", natT)) (lt ZeroC (Free("z_pp", natT)))
              in oeq_rw_W (Plt, suc k, rF) hk_s lt0Sk end
            val r = exE_W (Pq, lt ZeroC rF) hs "k_up" sb
        in Thm.implies_intr (ctermW (jT (mkExSuc_W rF))) r end
      val res = disjE_W (oeq rF ZeroC, mkExSuc_W rF, lt ZeroC rF) dzr caseZ caseS
      val d2 = Thm.implies_intr (ctermW hutP) res
      val d1 = Thm.implies_intr (ctermW hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of unit_pos) = 0 then out "OK unit_pos\n" else out "FAIL unit_pos\n";
fun unit_pos_U (nt,rt) hp1 hut =
  Thm.implies_elim (Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("n",0), ctermU nt),(("r",0), ctermU rt)] (varify unit_pos))) hp1) hut;

val () = out "BJ0_UNIT_POS_OK\n";

(* ============================================================================
   PHASE P : THE BIJECTION  f r = rmod (mult a r) n  on  urrl n.
   ============================================================================ *)
fun fObj_of (aT,nT) = Term.lambda (Free("rb", natT)) (rmod (mult aT (Free("rb", natT))) nT);
fun fap (aT,nT) r = rmod (mult aT r) nT;   (* beta-reduced application *)

(* cong_range_unique on ctxtU *)
val cong_range_unique_vU = varify cong_range_unique;
fun cong_range_unique_U (pt,at,bt) hp1 halt hblt hcg =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("p",0), ctermU pt),(("a",0), ctermU at),(("b",0), ctermU bt)] cong_range_unique_vU)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hp1) halt) hblt) hcg end;
val rmodeq_imp_cong_vU2 = rmodeq_imp_cong_vU;  (* alias *)

(* ---------------------------------------------------------------------------
   f_closed : 1<n ==> unit_test n a ==> lmem r (urrl n) ==> lmem (fap a n r) (urrl n)
   (f maps urrl n into urrl n)
   --------------------------------------------------------------------------- *)
val f_closed =
  let val nF = Free("n", natT); val aF = Free("a", natT); val rF = Free("r", natT)
      val one = suc ZeroC
      val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermU hp1P)
      val hutaP = jT (unit_test nF aF); val huta = Thm.assume (ctermU hutaP)
      val hmemP = jT (lmem rF (urrl nF)); val hmem = Thm.assume (ctermU hmemP)
      val fr = fap (aF,nF) rF                                  (* rmod (mult a r) n *)
      (* r is a unit and in range *)
      val cjr = lmem_urrl_fwd_U (rF, nF) hmem                  (* lmem r (uptoF(sub n 1)) /\ unit_test n r *)
      val utr = conjunct2_U (lmem rF (uptoF (sub nF one)), unit_test nF rF) cjr
      (* unit_test n (fap a n r) by unit_mult_closed *)
      val utfr = unit_mult_closed_U (nF, aF, rF) hp1 huta utr  (* unit_test n (rmod (mult a r) n) = unit_test n fr *)
      (* fr in [1..n-1] : 0<fr (unit_pos) ; fr < n (rmod_lt) ; pos_lt_imp_mem *)
      val hp0 = lt1_imp_lt0_W nF hp1
      val frpos = unit_pos_U (nF, fr) hp1 utfr                 (* 0 < fr *)
      val frlt = rmod_lt_U (mult aF rF, nF) hp0                (* fr < n *)
      val memfr = pos_lt_imp_mem_U (nF, fr) hp1 frpos frlt     (* lmem fr (uptoF(sub n 1)) *)
      val cj = conjI_U (lmem fr (uptoF (sub nF one)), unit_test nF fr) memfr utfr
      val res = lmem_urrl_bwd_U (fr, nF) cj                    (* lmem fr (urrl n) *)
      val d3 = Thm.implies_intr (ctermU hmemP) res
      val d2 = Thm.implies_intr (ctermU hutaP) d3
      val d1 = Thm.implies_intr (ctermU hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of f_closed) = 0 then out "OK f_closed\n" else out "FAIL f_closed\n";
fun f_closed_U (nt,at,rt) hp1 huta hmem =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("n",0), ctermU nt),(("a",0), ctermU at),(("r",0), ctermU rt)] f_closed)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hp1) huta) hmem end;

val () = out "BJ0_F_CLOSED_OK\n";

(* ============================================================================
   PHASE Q : f_inj, finv_unit, f_surj.
   ============================================================================ *)

(* ---------------------------------------------------------------------------
   f_inj : 1<n ==> unit_test n a ==> lmem r1 (urrl n) ==> lmem r2 (urrl n)
           ==> oeq (fap a n r1)(fap a n r2) ==> oeq r1 r2
   --------------------------------------------------------------------------- *)
val f_inj =
  let val nF = Free("n", natT); val aF = Free("a", natT)
      val r1F = Free("r1", natT); val r2F = Free("r2", natT)
      val one = suc ZeroC
      val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermU hp1P)
      val hutaP = jT (unit_test nF aF); val huta = Thm.assume (ctermU hutaP)
      val hm1P = jT (lmem r1F (urrl nF)); val hm1 = Thm.assume (ctermU hm1P)
      val hm2P = jT (lmem r2F (urrl nF)); val hm2 = Thm.assume (ctermU hm2P)
      val heqP = jT (oeq (fap (aF,nF) r1F)(fap (aF,nF) r2F)); val heq = Thm.assume (ctermU heqP)
      val hp0 = lt1_imp_lt0_W nF hp1
      (* oeq (rmod (mult a r1) n)(rmod (mult a r2) n) -> cong n (mult a r1)(mult a r2) *)
      val congar = rmodeq_imp_cong_U (nF, mult aF r1F, mult aF r2F) hp0 heq
      (* gen_cancel : cong n r1 r2 *)
      val congr12 = gen_cancel_U (nF, aF, r1F, r2F) hp1 huta congar
      (* r1, r2 in range -> lt r1 n, lt r2 n *)
      val cj1 = lmem_urrl_fwd_U (r1F, nF) hm1
      val mem1 = conjunct1_U (lmem r1F (uptoF (sub nF one)), unit_test nF r1F) cj1
      val cj2 = lmem_urrl_fwd_U (r2F, nF) hm2
      val mem2 = conjunct1_U (lmem r2F (uptoF (sub nF one)), unit_test nF r2F) cj2
      val lt1 = mem_range_imp_lt_U (nF, r1F) hp1 mem1
      val lt2 = mem_range_imp_lt_U (nF, r2F) hp1 mem2
      val res = cong_range_unique_U (nF, r1F, r2F) hp1 lt1 lt2 congr12   (* oeq r1 r2 *)
      val d5 = Thm.implies_intr (ctermU heqP) res
      val d4 = Thm.implies_intr (ctermU hm2P) d5
      val d3 = Thm.implies_intr (ctermU hm1P) d4
      val d2 = Thm.implies_intr (ctermU hutaP) d3
      val d1 = Thm.implies_intr (ctermU hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of f_inj) = 0 then out "OK f_inj\n" else out "FAIL f_inj\n";
fun f_inj_U (nt,at,r1t,r2t) hp1 huta hm1 hm2 heq =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("n",0), ctermU nt),(("a",0), ctermU at),(("r1",0), ctermU r1t),(("r2",0), ctermU r2t)] f_inj)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hp1) huta) hm1) hm2) heq end;

val () = out "BJ0_F_INJ_OK\n";

(* ---------------------------------------------------------------------------
   finv_unit : 1<n ==> unit_test n a ==> unit_test n (finv n a)
   (the inverse of a unit is a unit)
   --------------------------------------------------------------------------- *)
val finv_unit =
  let val nF = Free("n", natT); val aF = Free("a", natT); val one = suc ZeroC
      val fa = finv nF aF
      val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermU hp1P)
      val hutaP = jT (unit_test nF aF); val huta = Thm.assume (ctermU hutaP)
      val cong_a_fa = unit_has_inv_U (nF, aF) hp1 huta        (* cong n (mult a fa) 1 *)
      (* cong n (mult fa a) 1 via comm *)
      val eqcomm = multcomm_U (fa, aF)                         (* oeq (mult fa a)(mult a fa) *)
      val cong_fa_a_af = cong_of_eq_U (nF, mult fa aF, mult aF fa) eqcomm
      val cong_faa_1 = cong_trans_U (nF, mult fa aF, mult aF fa, one) cong_fa_a_af cong_a_fa  (* cong n (mult fa a) 1 *)
      (* unit_from_inv (n, fa, a) : unit_test n fa *)
      val res = unit_from_inv_U (nF, fa, aF) hp1 cong_faa_1
      val d2 = Thm.implies_intr (ctermU hutaP) res
      val d1 = Thm.implies_intr (ctermU hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of finv_unit) = 0 then out "OK finv_unit\n" else out "FAIL finv_unit\n";
fun finv_unit_U (nt,at) hp1 huta =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("n",0), ctermU nt),(("a",0), ctermU at)] finv_unit)
  in Thm.implies_elim (Thm.implies_elim inst hp1) huta end;

val () = out "BJ0_FINV_UNIT_OK\n";

(* ---------------------------------------------------------------------------
   f_surj : 1<n ==> unit_test n a ==> lmem s (urrl n)
            ==> Ex r. lmem r (urrl n) /\ oeq s (fap a n r)
   witness r = fap (finv n a) n s = rmod (mult (finv n a) s) n.
   --------------------------------------------------------------------------- *)
val f_surj =
  let val nF = Free("n", natT); val aF = Free("a", natT); val sF = Free("s", natT)
      val one = suc ZeroC
      val fa = finv nF aF
      val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermU hp1P)
      val hutaP = jT (unit_test nF aF); val huta = Thm.assume (ctermU hutaP)
      val hmsP = jT (lmem sF (urrl nF)); val hms = Thm.assume (ctermU hmsP)
      val hp0 = lt1_imp_lt0_W nF hp1
      val r = fap (fa,nF) sF                                   (* rmod (mult fa s) n *)
      (* finv a is a unit *)
      val utfa = finv_unit_U (nF, aF) hp1 huta                 (* unit_test n fa *)
      (* r = fap fa n s in urrl n  (by f_closed with a:=fa) *)
      val memr = f_closed_U (nF, fa, sF) hp1 utfa hms          (* lmem r (urrl n) *)
      (* cong n (fap a n r) s :  fap a n r = rmod (mult a r) n ≡ mult a r ; r ≡ mult fa s ; *)
      val far = fap (aF,nF) r                                  (* rmod (mult a r) n *)
      val cong_far_ar = cong_self_rmod_W (nF, mult aF r) hp0   (* cong n (mult a r) far ... orientation: cong n (mult a r) (rmod (mult a r) n) *)
      val cong_far_ar2 = cong_sym_U (nF, mult aF r, far) cong_far_ar  (* cong n far (mult a r) *)
      (* r = rmod (mult fa s) n ≡ mult fa s *)
      val cong_r_fas = cong_self_rmod_W (nF, mult fa sF) hp0   (* cong n (mult fa s) r *)
      val cong_r_fas2 = cong_sym_U (nF, mult fa sF, r) cong_r_fas  (* cong n r (mult fa s) *)
      val crefl_a = cong_refl_U (nF, aF)
      val cong_ar_afas = cong_mult_U (nF, aF, aF, r, mult fa sF) crefl_a cong_r_fas2  (* cong n (mult a r)(mult a (mult fa s)) *)
      (* mult a (mult fa s) = (mult a fa) s  assoc sym *)
      val eassoc = oeq_sym_vU OF [multassoc_U (aF, fa, sF)]    (* oeq (mult a (mult fa s))(mult (mult a fa) s) *)
      val cong_afas_aFa_s = cong_of_eq_U (nF, mult aF (mult fa sF), mult (mult aF fa) sF) eassoc
      (* cong n (mult a fa) 1 -> cong n (mult (mult a fa) s)(mult 1 s) *)
      val cong_afa_1 = unit_has_inv_U (nF, aF) hp1 huta        (* cong n (mult a fa) 1 *)
      val crefl_s = cong_refl_U (nF, sF)
      val cong_aFas_1s = cong_mult_U (nF, mult aF fa, one, sF, sF) cong_afa_1 crefl_s  (* cong n (mult (mult a fa) s)(mult 1 s) *)
      (* mult 1 s = s *)
      val e1s = mult1l_U sF                                    (* oeq (mult 1 s) s *)
      val cong_1s_s = cong_of_eq_U (nF, mult one sF, sF) e1s   (* cong n (mult 1 s) s *)
      (* chain : far ~ (mult a r) ~ (mult a (mult fa s)) ~ ((mult a fa) s) ~ (mult 1 s) ~ s *)
      val t1 = cong_trans_U (nF, far, mult aF r, mult aF (mult fa sF)) cong_far_ar2 cong_ar_afas
      val t2 = cong_trans_U (nF, far, mult aF (mult fa sF), mult (mult aF fa) sF) t1 cong_afas_aFa_s
      val t3 = cong_trans_U (nF, far, mult (mult aF fa) sF, mult one sF) t2 cong_aFas_1s
      val t4 = cong_trans_U (nF, far, mult one sF, sF) t3 cong_1s_s   (* cong n far s *)
      val cong_s_far = cong_sym_U (nF, far, sF) t4               (* cong n s far *)
      (* lt s n and lt far n -> oeq s far via cong_range_unique *)
      val cjs = lmem_urrl_fwd_U (sF, nF) hms
      val mems = conjunct1_U (lmem sF (uptoF (sub nF one)), unit_test nF sF) cjs
      val lts = mem_range_imp_lt_U (nF, sF) hp1 mems            (* lt s n *)
      val ltfar = rmod_lt_U (mult aF r, nF) hp0                 (* lt far n *)
      val oeq_s_far = cong_range_unique_U (nF, sF, far) hp1 lts ltfar cong_s_far  (* oeq s far *)
      (* exI : Ex r. lmem r (urrl n) /\ oeq s (fap a n r) *)
      val PexAbs = Term.lambda (Free("rw", natT))
                     (mkConj (lmem (Free("rw", natT)) (urrl nF)) (oeq sF (fap (aF,nF) (Free("rw", natT)))))
      val cj = conjI_U (lmem r (urrl nF), oeq sF far) memr oeq_s_far
      val ex = exI_U PexAbs r cj
      val d3 = Thm.implies_intr (ctermU hmsP) ex
      val d2 = Thm.implies_intr (ctermU hutaP) d3
      val d1 = Thm.implies_intr (ctermU hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of f_surj) = 0 then out "OK f_surj\n" else out "FAIL f_surj\n";
val f_surj_vU = varify f_surj;
fun f_surj_U (nt,at,st) hp1 huta hms =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("n",0), ctermU nt),(("a",0), ctermU at),(("s",0), ctermU st)] f_surj_vU)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hp1) huta) hms end;

val () = out "BJ0_F_SURJ_OK\n";

(* ============================================================================
   PHASE S : THE BIJECTION  bij_prod  via lprod_perm.
   bij_prod : 1<n ==> unit_test n a ==> oeq (lprod (lmap fObj (urrl n))) (lprod (urrl n))
   ============================================================================ *)
(* lprod_perm accessor on ctxtU *)
fun lprod_perm_U (L1,L2) hnd1 hnd2 hme =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("L1",0), ctermU L1),(("L2",0), ctermU L2)] lprod_perm_vU)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hnd1) hnd2) hme end;

(* impI / allI variants that do NOT beta-normalise (keep fObj$x form intact for injF) *)
fun impI_U_nb (At,Bt) hImpThm =
  let val inst = Drule.infer_instantiate ctxtU [(("A",0), ctermU At),(("B",0), ctermU Bt)] impI_vU
  in Thm.implies_elim inst hImpThm end;
fun allI_U_nb Pabs hAllThm =
  let val inst = Drule.infer_instantiate ctxtU [(("P",0), ctermU Pabs)] allI_vU
  in Thm.implies_elim inst hAllThm end;

val bij_prod =
  let val nF = Free("n", natT); val aF = Free("a", natT); val one = suc ZeroC
      val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermU hp1P)
      val hutaP = jT (unit_test nF aF); val huta = Thm.assume (ctermU hutaP)
      val fObj = fObj_of (aF, nF)
      val L = urrl nF
      val mapL = lmap fObj L
      (* lnodup L *)
      val ndL = lnodup_urrl_U nF                               (* lnodup (urrl n) *)
      (* injF fObj L : from f_inj.  Build in the BETA-REDUCED (fap) form, which is
         exactly what lnodup_map_U (beta-norming) expects after instantiating f:=fObj. *)
      val injFL =
        let val aQ = Free("ija", natT); val bQ = Free("ijb", natT)
            fun ibody a b = mkImp (lmem a L)(mkImp (lmem b L)(mkImp (oeq (fap (aF,nF) a)(fap (aF,nF) b))(oeq a b)))
            val hma = Thm.assume (ctermU (jT (lmem aQ L)))
            val hmb = Thm.assume (ctermU (jT (lmem bQ L)))
            val hfeqP = jT (oeq (fap (aF,nF) aQ)(fap (aF,nF) bQ))
            val hfeq = Thm.assume (ctermU hfeqP)
            val oeqab = f_inj_U (nF, aF, aQ, bQ) hp1 huta hma hmb hfeq   (* oeq aQ bQ *)
            val i3 = impI_U (oeq (fap (aF,nF) aQ)(fap (aF,nF) bQ), oeq aQ bQ)
                       (Thm.implies_intr (ctermU hfeqP) oeqab)
            val i2 = impI_U (lmem bQ L, mkImp (oeq (fap (aF,nF) aQ)(fap (aF,nF) bQ))(oeq aQ bQ))
                       (Thm.implies_intr (ctermU (jT (lmem bQ L))) i3)
            val i1 = impI_U (lmem aQ L, mkImp (lmem bQ L)(mkImp (oeq (fap (aF,nF) aQ)(fap (aF,nF) bQ))(oeq aQ bQ)))
                       (Thm.implies_intr (ctermU (jT (lmem aQ L))) i2)   (* ibody aQ bQ *)
            val PbAbs = Term.lambda bQ (ibody aQ bQ)
            val forallB = allI_U PbAbs (Thm.forall_intr (ctermU bQ) i1)
            val PaAbs = Term.lambda aQ (mkForall (Term.lambda bQ (ibody aQ bQ)))
            val forallA = allI_U PaAbs (Thm.forall_intr (ctermU aQ) forallB)
        in forallA end                                          (* injF (beta-reduced fap form) *)
      (* lnodup (lmap fObj L) *)
      val ndMap = lnodup_map_U (fObj, L) ndL injFL              (* lnodup (lmap fObj L) *)
      (* mem_eq (lmap fObj L) L : forward (closure) + backward (surjectivity) *)
      val memeq =
        let val yF = Free("me_y", natT)
            (* fwd : lmem y (lmap fObj L) -> lmem y L *)
            val fwd =
              let val hy = Thm.assume (ctermU (jT (lmem yF mapL)))
                  val ex = lmem_map_fwd_U (fObj, yF, L) hy      (* Ex x. lmem x L /\ oeq y (fObj$x) = oeq y (fap a n x) *)
                  val PihAbs = Term.lambda (Free("xw", natT))
                                 (mkConj (lmem (Free("xw", natT)) L) (oeq yF (fap (aF,nF) (Free("xw", natT)))))
                  fun bodyFn w hw =
                    let val memwL = conjunct1_U (lmem w L, oeq yF (fap (aF,nF) w)) hw
                        val oeqyfw = conjunct2_U (lmem w L, oeq yF (fap (aF,nF) w)) hw  (* oeq y (fap a n w) *)
                        (* fap a n w in L by f_closed *)
                        val memfw = f_closed_U (nF, aF, w) hp1 huta memwL   (* lmem (fap a n w) L *)
                        (* rewrite lmem (fap a n w) L  to  lmem y L  via oeq y (fap a n w) (sym) *)
                        val oeqfwy = oeq_sym_vU OF [oeqyfw]                  (* oeq (fap a n w) y *)
                        val Pm = Term.lambda (Free("zm", natT)) (lmem (Free("zm", natT)) L)
                        val memyL = oeq_rw_U (Pm, fap (aF,nF) w, yF) oeqfwy memfw  (* lmem y L *)
                    in memyL end
                  val res = exE_U (PihAbs, lmem yF L) ex "xw_me" bodyFn
              in Thm.implies_intr (ctermU (jT (lmem yF mapL))) res end
            (* bwd : lmem y L -> lmem y (lmap fObj L) via surjectivity *)
            val bwd =
              let val hy = Thm.assume (ctermU (jT (lmem yF L)))
                  val ex = f_surj_U (nF, aF, yF) hp1 huta hy    (* Ex r. lmem r L /\ oeq y (fap a n r) *)
                  val PsurjAbs = Term.lambda (Free("rw", natT))
                                   (mkConj (lmem (Free("rw", natT)) L) (oeq yF (fap (aF,nF) (Free("rw", natT)))))
                  fun bodyFn w hw =
                    let val memwL = conjunct1_U (lmem w L, oeq yF (fap (aF,nF) w)) hw
                        val oeqyfw = conjunct2_U (lmem w L, oeq yF (fap (aF,nF) w)) hw  (* oeq y (fap a n w) *)
                        (* lmem (fObj$w) (lmap fObj L) by lmem_map_bwd ; fObj$w = fap a n w (beta) *)
                        val memMap = lmem_map_bwd_U (fObj, w, L) memwL    (* lmem (fObj$w) (lmap fObj L) = lmem (fap a n w)(lmap fObj L) *)
                        (* rewrite (fap a n w) -> y via oeq y (fap a n w) sym *)
                        val oeqfwy = oeq_sym_vU OF [oeqyfw]               (* oeq (fap a n w) y *)
                        val Pm = Term.lambda (Free("zm2", natT)) (lmem (Free("zm2", natT)) mapL)
                        val memyMap = oeq_rw_U (Pm, fap (aF,nF) w, yF) oeqfwy memMap  (* lmem y (lmap fObj L) *)
                    in memyMap end
                  val res = exE_U (PsurjAbs, lmem yF mapL) ex "rw_me" bodyFn
              in Thm.implies_intr (ctermU (jT (lmem yF L))) res end
            val cjBoth = conjI_U (mkImp (lmem yF mapL)(lmem yF L), mkImp (lmem yF L)(lmem yF mapL))
                            (impI_U (lmem yF mapL, lmem yF L) fwd)
                            (impI_U (lmem yF L, lmem yF mapL) bwd)
            val Pabs = mem_eq_pred mapL L
        in allI_U Pabs (Thm.forall_intr (ctermU yF) cjBoth) end  (* mem_eq mapL L *)
      (* lprod_perm : oeq (lprod mapL)(lprod L) *)
      val res = lprod_perm_U (mapL, L) ndMap ndL memeq
      val d2 = Thm.implies_intr (ctermU hutaP) res
      val d1 = Thm.implies_intr (ctermU hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of bij_prod) = 0 then out "OK bij_prod\n" else out "FAIL bij_prod\n";

val () = out "EULER_BIJ_OK\n";
(* ============================================================================
   EULER PHASE 2 (seat eu0) : Euler's theorem  a^phi(n) == 1 (mod n).
   Built on the Phase-1 unit-group machinery (urrl/phiU/fObj/bij_prod/gen_cancel).
   ============================================================================ *)
val () = out "EU0_PHASE2_START\n";

(* ---- U-context accessors for pow / cong_self_rmod / oeq-level mult-cong ---- *)
val pow_Zero_vU = varify pow_Zero_ax;
val pow_Suc_vU  = varify pow_Suc_ax;
fun powZero_U at = beta_norm (Drule.infer_instantiate ctxtU [(("a",0), ctermU at)] pow_Zero_vU);
fun powSuc_U (at,nt) = beta_norm (Drule.infer_instantiate ctxtU
                          [(("a",0), ctermU at),(("n",0), ctermU nt)] pow_Suc_vU);

val cong_self_rmod_vU = varify cong_self_rmod;  (* 0<p ==> cong p a (rmod a p) *)
fun cong_self_rmod_U (pt,at) hp0 =
  Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
      [(("p",0), ctermU pt),(("a",0), ctermU at)] cong_self_rmod_vU)) hp0;

(* oeq-level mult-cong via oeq_subst (oeq_rw_U) *)
fun mult_cong_l_U (pT, qT, kT) hpq =   (* oeq p q ==> oeq (mult p k)(mult q k) *)
  let val zf = Free("z_mcl", natT)
      val Pabs = Term.lambda zf (oeq (mult pT kT) (mult zf kT))
  in oeq_rw_U (Pabs, pT, qT) hpq (oeqRefl_U (mult pT kT)) end;
fun mult_cong_r_U (hT, pT, qT) hpq =   (* oeq p q ==> oeq (mult h p)(mult h q) *)
  let val zf = Free("z_mcr", natT)
      val Pabs = Term.lambda zf (oeq (mult hT pT) (mult hT zf))
  in oeq_rw_U (Pabs, pT, qT) hpq (oeqRefl_U (mult hT pT)) end;

(* lt1_imp_lt0 in U : 1<n ==> 0<n  (reuse W helper; thyU >= thyW) *)
fun lt1_imp_lt0_U nt hp1 = lt1_imp_lt0_W nt hp1;

(* gObj = mult a  (multiply-by-a, eta-CONTRACTED to match varify/infer_instantiate,
   which eta-contracts (%x. mult a x) -> (mult a)) ; gap a x = mult a x (beta form) *)
fun gObj_of aT = multC $ aT;            (* = mult a : natfunT *)
fun gap aT x = mult aT x;               (* = (mult a) $ x  beta-reduced *)

val () = out "EU0_PREAMBLE_OK\n";

(* ============================================================================
   STEP 1  prod_map_factor :
     oeq (lprod (lmap (%x. mult a x) L)) (mult (pow a (llen L)) (lprod L))
   list induction on L.
   - nil:  lprod (lmap g nil) = lprod nil = 1 ;  pow a (llen nil)=pow a 0=1 ;
           mult 1 (lprod nil) = mult 1 1 = 1.   so both sides = 1.
   - cons x t:  lprod (lmap g (x::t)) = lprod ((a*x)::(lmap g t))
                = (a*x) * lprod(lmap g t)
                =[IH] (a*x) * (a^(llen t) * lprod t)
                = a^(Suc(llen t)) * (x * lprod t)   [pow_Suc + comm/assoc]
                = pow a (llen (x::t)) * lprod(x::t).
   ============================================================================ *)
val prod_map_factor =
  let
    val aF = Free("a", natT)
    val g  = gObj_of aF
    val LF = Free("L", natlistT)
    (* the predicate P L := oeq (lprod (lmap g L)) (mult (pow a (llen L)) (lprod L)) *)
    fun goalOf L = oeq (lprod (lmap g L)) (mult (pow aF (llen L)) (lprod L))
    val Pabs = Term.lambda LF (goalOf LF)
    (* --- base case : P nil --- *)
    val baseThm =
      let
        (* LHS = lprod (lmap g nil) = lprod nil = 1 *)
        val e_map = lmapNil_at g                       (* oeq (lmap g nil) nil  -- actually leq *)
        (* lmap_nil is leq (lmap g nil) nil ; rewrite lprod via leq *)
        val lhs_eq = lprod_cong_U (lmap g lnilC, lnilC) e_map   (* oeq (lprod(lmap g nil))(lprod nil) *)
        val lprodnil = lprodNil_U                       (* oeq (lprod nil) 1 *)
        val lhs1 = oeq_trans_vU OF [lhs_eq, lprodnil]   (* oeq (lprod(lmap g nil)) 1 *)
        (* RHS = mult (pow a (llen nil)) (lprod nil) *)
        val llennil = llenNil_U                         (* oeq (llen nil) 0 *)
        (* pow a (llen nil) : rewrite llen nil -> 0 *)
        val zf = Free("z_pn", natT)
        val Ppow = Term.lambda zf (oeq (pow aF (llen lnilC)) (pow aF zf))
        val pow_arg = oeq_rw_U (Ppow, llen lnilC, ZeroC) llennil (oeqRefl_U (pow aF (llen lnilC)))
                                                        (* oeq (pow a (llen nil))(pow a 0) *)
        val pow0 = powZero_U aF                         (* oeq (pow a 0) 1 *)
        val pow_eq1 = oeq_trans_vU OF [pow_arg, pow0]   (* oeq (pow a (llen nil)) 1 *)
        (* mult (pow a (llen nil))(lprod nil) = mult 1 1 = 1 *)
        val rhs1 = mult_cong_l_U (pow aF (llen lnilC), suc ZeroC, lprod lnilC) pow_eq1
                                                        (* oeq (mult (pow..)(lprod nil)) (mult 1 (lprod nil)) *)
        val rhs2 = mult_cong_r_U (suc ZeroC, lprod lnilC, suc ZeroC) lprodnil
                                                        (* oeq (mult 1 (lprod nil))(mult 1 1) *)
        val mult11 = mult1l_U (suc ZeroC)               (* oeq (mult 1 1) 1 *)
        val rhs_chain1 = oeq_trans_vU OF [rhs1, rhs2]   (* oeq (mult(pow..)(lprod nil))(mult 1 1) *)
        val rhs_eq1 = oeq_trans_vU OF [rhs_chain1, mult11]  (* oeq (mult(pow..)(lprod nil)) 1 *)
        (* goal : oeq LHS RHS = oeq (lprod(lmap g nil)) (mult(pow..)(lprod nil)) *)
        val rhs_eq1_s = oeq_sym_vU OF [rhs_eq1]         (* oeq 1 (mult(pow..)(lprod nil)) *)
      in oeq_trans_vU OF [lhs1, rhs_eq1_s] end          (* oeq LHS RHS *)
    (* --- step case : P t ==> P (x::t) --- *)
    val xF = Free("x", natT); val tF = Free("t", natlistT)
    val stepThm =
      let
        val ihP = jT (goalOf tF)                        (* IH : oeq (lprod(lmap g t)) (mult (pow a (llen t))(lprod t)) *)
        val ih  = Thm.assume (ctermU ihP)
        val cons = lcons xF tF
        (* LHS = lprod (lmap g (x::t)) *)
        (* lmap g (x::t) = (g$x) :: (lmap g t) = (a*x) :: (lmap g t) *)
        val e_mapcons = lmapCons_U (g, xF, tF)          (* leq (lmap g (x::t)) ((g$x)::(lmap g t)) *)
        (* g$x beta = mult a x ; lmapCons_U already beta-norms so head is (mult a x) *)
        val gx = gap aF xF
        val lhs_eq0 = lprod_cong_U (lmap g cons, lcons gx (lmap g tF)) e_mapcons
                                                        (* oeq (lprod(lmap g (x::t)))(lprod ((a*x)::(lmap g t))) *)
        val lprodcons = lprodCons_U (gx, lmap g tF)     (* oeq (lprod((a*x)::(lmap g t))) (mult (a*x) (lprod(lmap g t))) *)
        val lhs1 = oeq_trans_vU OF [lhs_eq0, lprodcons] (* oeq (lprod(lmap g(x::t))) (mult (a*x)(lprod(lmap g t))) *)
        (* rewrite lprod(lmap g t) -> mult (pow a (llen t))(lprod t) via IH *)
        val lhs2 = mult_cong_r_U (gx, lprod (lmap g tF), mult (pow aF (llen tF)) (lprod tF)) ih
                                                        (* oeq (mult (a*x)(lprod(lmap g t))) (mult (a*x)(mult (pow a (llen t))(lprod t))) *)
        val lhs3 = oeq_trans_vU OF [lhs1, lhs2]         (* oeq LHS (mult (a*x)(mult (pow a (llen t))(lprod t))) *)
        (* Now reassociate: (a*x)*(P*Q) where P=pow a (llen t), Q=lprod t.
           Target RHS = mult (pow a (llen(x::t)))(lprod(x::t))
                      = mult (pow a (Suc(llen t)))(mult x (lprod t))
                      = mult (a * pow a (llen t))(mult x (lprod t))   [pow_Suc]
           Show  (a*x)*(P*Q) = (a*P)*(x*Q).  Pure semiring rearrange of 4 factors. *)
        val P = pow aF (llen tF); val Q = lprod tF
        (* use mult4_rearrange_U (x1,y1,u,v): oeq ((x1*y1)*(u*v)) ((x1*u)*(y1*v))
           with x1=a, y1=x, u=P, v=Q gives  ((a*x)*(P*Q)) = ((a*P)*(x*Q)). *)
        val ealg = mult4_rearrange_U (aF, xF, P, Q)     (* oeq ((a*x)*(P*Q)) ((a*P)*(x*Q)) *)
        val lhs4 = oeq_trans_vU OF [lhs3, ealg]         (* oeq LHS ((a*P)*(x*Q)) = oeq LHS (mult (mult a P)(mult x Q)) *)
        (* a*P = a * pow a (llen t) = pow a (Suc (llen t))  [pow_Suc sym] *)
        val psuc = powSuc_U (aF, llen tF)               (* oeq (pow a (Suc(llen t))) (mult a (pow a (llen t))) = mult a P *)
        val psuc_s = oeq_sym_vU OF [psuc]               (* oeq (mult a P) (pow a (Suc(llen t))) *)
        (* rewrite (a*P) -> pow a (Suc(llen t)) inside (mult (mult a P)(x*Q)) *)
        val lhs5 = mult_cong_l_U (mult aF P, pow aF (suc (llen tF)), mult xF Q) psuc_s
                                                        (* oeq ((a*P)*(x*Q)) ((pow a (Suc(llen t)))*(x*Q)) *)
        val lhs6 = oeq_trans_vU OF [lhs4, lhs5]         (* oeq LHS (mult (pow a (Suc(llen t)))(mult x Q)) *)
        (* RHS side: llen (x::t) = Suc (llen t) ; lprod (x::t) = mult x (lprod t) = mult x Q *)
        val llencons = llenCons_U (xF, tF)              (* oeq (llen (x::t)) (Suc(llen t)) *)
        val lprodcons2 = lprodCons_U (xF, tF)           (* oeq (lprod(x::t)) (mult x (lprod t)) = mult x Q *)
        (* Build RHS = mult (pow a (llen(x::t)))(lprod(x::t)).
           rewrite pow a (llen(x::t)) -> pow a (Suc(llen t)) ; lprod(x::t) -> mult x Q. *)
        (* pow a (llen(x::t)) = pow a (Suc(llen t)) *)
        val zf2 = Free("z_pc", natT)
        val Ppow2 = Term.lambda zf2 (oeq (pow aF (llen cons)) (pow aF zf2))
        val pow_arg2 = oeq_rw_U (Ppow2, llen cons, suc (llen tF)) llencons (oeqRefl_U (pow aF (llen cons)))
                                                        (* oeq (pow a (llen(x::t)))(pow a (Suc(llen t))) *)
        val rhs_a = mult_cong_l_U (pow aF (llen cons), pow aF (suc (llen tF)), lprod cons) pow_arg2
                                                        (* oeq (mult (pow a (llen(x::t)))(lprod(x::t))) (mult (pow a (Suc(llen t)))(lprod(x::t))) *)
        val rhs_b = mult_cong_r_U (pow aF (suc (llen tF)), lprod cons, mult xF Q) lprodcons2
                                                        (* oeq (mult (pow a (Suc(llen t)))(lprod(x::t))) (mult (pow a (Suc(llen t)))(mult x Q)) *)
        val rhs_eq = oeq_trans_vU OF [rhs_a, rhs_b]     (* oeq RHS (mult (pow a (Suc(llen t)))(mult x Q)) *)
        val rhs_eq_s = oeq_sym_vU OF [rhs_eq]           (* oeq (mult (pow a (Suc(llen t)))(mult x Q)) RHS *)
        val res = oeq_trans_vU OF [lhs6, rhs_eq_s]      (* oeq LHS RHS = P(x::t) *)
      in Thm.forall_intr (ctermU xF)
           (Thm.forall_intr (ctermU tF) (Thm.implies_intr (ctermU ihP) res)) end
    val ind = list_induct_U (Pabs, LF) baseThm stepThm  (* oeq (lprod(lmap g L)) (mult (pow a (llen L))(lprod L)) for the schematic L *)
  in varify ind end;
val () = if length (Thm.hyps_of prod_map_factor) = 0 then out "OK prod_map_factor\n" else out "FAIL prod_map_factor\n";
val () = out "EU0_STEP1_OK\n";

(* ============================================================================
   STEP 2  rmod_bridge :
     1<n ==>  cong n (lprod (lmap (%x. rmod (mult a x) n) L)) (lprod (lmap (%x. mult a x) L))
   list induction on L.  fObj = (%rb. rmod (mult a rb) n) (the Phase-1 f) ;
   gObj = (mult a)  (eta-contracted).
   per-element :  cong n (rmod (mult a x) n) (mult a x)  via cong_self_rmod (sym).
   ============================================================================ *)
val rmod_bridge =
  let
    val aF = Free("a", natT); val nF = Free("n", natT)
    val one = suc ZeroC
    val fObj = fObj_of (aF, nF)       (* %rb. rmod (mult a rb) n *)
    val gObj = gObj_of aF             (* mult a *)
    val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermU hp1P)
    val hp0 = lt1_imp_lt0_U nF hp1    (* 0 < n *)
    val LF = Free("L", natlistT)
    fun goalOf L = cong nF (lprod (lmap fObj L)) (lprod (lmap gObj L))
    val Pabs = Term.lambda LF (goalOf LF)
    (* --- base : cong n (lprod(lmap f nil))(lprod(lmap g nil)) --- *)
    val baseThm =
      let
        val ef = lmapNil_at fObj                       (* leq (lmap f nil) nil *)
        val eg = lmapNil_at gObj                       (* leq (lmap g nil) nil *)
        val lf = lprod_cong_U (lmap fObj lnilC, lnilC) ef  (* oeq (lprod(lmap f nil))(lprod nil) *)
        val lg = lprod_cong_U (lmap gObj lnilC, lnilC) eg  (* oeq (lprod(lmap g nil))(lprod nil) *)
        (* both lprod equal lprod nil ; so cong via reflexive on lprod nil *)
        (* oeq (lprod(lmap f nil))(lprod(lmap g nil)) : trans lf , sym lg *)
        val lfg = oeq_trans_vU OF [lf, oeq_sym_vU OF [lg]]  (* oeq (lprod(lmap f nil))(lprod(lmap g nil)) *)
      in cong_of_eq_U (nF, lprod (lmap fObj lnilC), lprod (lmap gObj lnilC)) lfg end
    (* --- step : P t ==> P (x::t) --- *)
    val xF = Free("x", natT); val tF = Free("t", natlistT)
    val stepThm =
      let
        val ihP = jT (goalOf tF)
        val ih  = Thm.assume (ctermU ihP)              (* cong n (lprod(lmap f t))(lprod(lmap g t)) *)
        val cons = lcons xF tF
        (* LHS : lprod (lmap f (x::t)) = lprod ((rmod(a*x)n) :: (lmap f t)) = mult (rmod(a*x)n)(lprod(lmap f t)) *)
        val fx = rmod (mult aF xF) nF                  (* f applied = fObj$x beta *)
        val ef_cons = lmapCons_U (fObj, xF, tF)        (* leq (lmap f (x::t)) (fx :: (lmap f t)) *)
        val lf_eq0 = lprod_cong_U (lmap fObj cons, lcons fx (lmap fObj tF)) ef_cons
        val lf_cons = lprodCons_U (fx, lmap fObj tF)   (* oeq (lprod(fx::(lmap f t)))(mult fx (lprod(lmap f t))) *)
        val lf_eq = oeq_trans_vU OF [lf_eq0, lf_cons]  (* oeq (lprod(lmap f (x::t)))(mult fx (lprod(lmap f t))) *)
        (* RHS : lprod (lmap g (x::t)) = mult (a*x)(lprod(lmap g t)) *)
        val gx = gap aF xF                              (* mult a x *)
        val eg_cons = lmapCons_U (gObj, xF, tF)        (* leq (lmap g (x::t)) (gx :: (lmap g t)) *)
        val lg_eq0 = lprod_cong_U (lmap gObj cons, lcons gx (lmap gObj tF)) eg_cons
        val lg_cons = lprodCons_U (gx, lmap gObj tF)   (* oeq (lprod(gx::(lmap g t)))(mult gx (lprod(lmap g t))) *)
        val lg_eq = oeq_trans_vU OF [lg_eq0, lg_cons]  (* oeq (lprod(lmap g(x::t)))(mult gx (lprod(lmap g t))) *)
        (* element congruence : cong n fx gx = cong n (rmod(a*x)n)(a*x) via cong_self_rmod sym *)
        val csr = cong_self_rmod_U (nF, mult aF xF) hp0  (* cong n (mult a x)(rmod(mult a x)n) = cong n gx fx *)
        val cong_fx_gx = cong_sym_U (nF, gx, fx) csr     (* cong n fx gx *)
        (* combine : cong n (mult fx (lprod(lmap f t)))(mult gx (lprod(lmap g t))) via cong_mult on fx~gx and ih *)
        val cprod = cong_mult_U (nF, fx, gx, lprod (lmap fObj tF), lprod (lmap gObj tF)) cong_fx_gx ih
                                                          (* cong n (mult fx (lprod(lmap f t)))(mult gx (lprod(lmap g t))) *)
        (* now reshape using lf_eq, lg_eq (as cong via cong_of_eq) :
           cong n (lprod(lmap f(x::t)))(mult fx ..) then trans cprod then sym (lprod(lmap g(x::t)) = mult gx ..) *)
        val cong_lf = cong_of_eq_U (nF, lprod (lmap fObj cons), mult fx (lprod (lmap fObj tF))) lf_eq
                                                          (* cong n (lprod(lmap f(x::t)))(mult fx (lprod(lmap f t))) *)
        val cong_lg = cong_of_eq_U (nF, lprod (lmap gObj cons), mult gx (lprod (lmap gObj tF))) lg_eq
        val cong_lg_s = cong_sym_U (nF, lprod (lmap gObj cons), mult gx (lprod (lmap gObj tF))) cong_lg
                                                          (* cong n (mult gx (lprod(lmap g t)))(lprod(lmap g(x::t))) *)
        val t1 = cong_trans_U (nF, lprod (lmap fObj cons), mult fx (lprod (lmap fObj tF)), mult gx (lprod (lmap gObj tF))) cong_lf cprod
        val res = cong_trans_U (nF, lprod (lmap fObj cons), mult gx (lprod (lmap gObj tF)), lprod (lmap gObj cons)) t1 cong_lg_s
                                                          (* cong n (lprod(lmap f(x::t)))(lprod(lmap g(x::t))) = goalOf (x::t) *)
      in Thm.forall_intr (ctermU xF)
           (Thm.forall_intr (ctermU tF) (Thm.implies_intr (ctermU ihP) res)) end
    val ind = list_induct_U (Pabs, LF) baseThm stepThm
    val d1 = Thm.implies_intr (ctermU hp1P) ind
  in varify d1 end;
val () = if length (Thm.hyps_of rmod_bridge) = 0 then out "OK rmod_bridge\n" else out "FAIL rmod_bridge\n";
val () = out "EU0_STEP2_OK\n";

(* ============================================================================
   STEP 4a  unit_mult_plain : 1<n ==> unit_test n x ==> unit_test n y ==> unit_test n (mult x y)
   (the PLAIN-product version of unit_mult_closed -- no rmod ; witness fx*fy)
   ============================================================================ *)
val unit_mult_plain =
  let
    val nF = Free("n", natT); val xF = Free("x", natT); val yF = Free("y", natT)
    val one = suc ZeroC
    val fx = finv nF xF; val fy = finv nF yF
    val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermU hp1P)
    val hutxP = jT (unit_test nF xF); val hutx = Thm.assume (ctermU hutxP)
    val hutyP = jT (unit_test nF yF); val huty = Thm.assume (ctermU hutyP)
    val W = mult fx fy
    val cx = unit_has_inv_U (nF, xF) hp1 hutx                   (* cong n (mult x fx) 1 *)
    val cy = unit_has_inv_U (nF, yF) hp1 huty                   (* cong n (mult y fy) 1 *)
    val cprod = cong_mult_U (nF, mult xF fx, one, mult yF fy, one) cx cy  (* cong n ((x*fx)*(y*fy)) (1*1) *)
    val e11 = mult1l_U one                                      (* oeq (mult 1 1) 1 *)
    val cong_11_1 = cong_of_eq_U (nF, mult one one, one) e11    (* cong n (1*1) 1 *)
    val cprod1 = cong_trans_U (nF, mult (mult xF fx)(mult yF fy), mult one one, one) cprod cong_11_1
    val ealg = mult4_rearrange_U (xF, yF, fx, fy)               (* oeq ((x*y)*(fx*fy)) ((x*fx)*(y*fy)) *)
    val cong_alg = cong_of_eq_U (nF, mult (mult xF yF)(mult fx fy), mult (mult xF fx)(mult yF fy)) ealg
    val cong_xyW_1 = cong_trans_U (nF, mult (mult xF yF)(mult fx fy), mult (mult xF fx)(mult yF fy), one) cong_alg cprod1
                                                                (* cong n ((x*y)*(fx*fy)) 1 *)
    val ut = unit_from_inv_U (nF, mult xF yF, W) hp1 cong_xyW_1 (* unit_test n (mult x y) *)
    val d3 = Thm.implies_intr (ctermU hutyP) ut
    val d2 = Thm.implies_intr (ctermU hutxP) d3
    val d1 = Thm.implies_intr (ctermU hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of unit_mult_plain) = 0 then out "OK unit_mult_plain\n" else out "FAIL unit_mult_plain\n";
fun unit_mult_plain_U (nt,xt,yt) hp1 hutx huty =
  let val inst = beta_norm (Drule.infer_instantiate ctxtU
        [(("n",0), ctermU nt),(("x",0), ctermU xt),(("y",0), ctermU yt)] unit_mult_plain)
  in Thm.implies_elim (Thm.implies_elim (Thm.implies_elim inst hp1) hutx) huty end;

(* unit_one : 1<n ==> unit_test n 1   (1 is a unit, inverse = 1) *)
val unit_one =
  let
    val nF = Free("n", natT); val one = suc ZeroC
    val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermU hp1P)
    val e11 = mult1l_U one                                      (* oeq (mult 1 1) 1 *)
    val cong_11_1 = cong_of_eq_U (nF, mult one one, one) e11    (* cong n (mult 1 1) 1 *)
    val ut = unit_from_inv_U (nF, one, one) hp1 cong_11_1       (* unit_test n 1 *)
  in varify (Thm.implies_intr (ctermU hp1P) ut) end;
val () = if length (Thm.hyps_of unit_one) = 0 then out "OK unit_one\n" else out "FAIL unit_one\n";
fun unit_one_U nt hp1 = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
        [(("n",0), ctermU nt)] unit_one)) hp1;
val () = out "EU0_STEP4A_OK\n";

(* ============================================================================
   STEP 4b  prod_unit_filter :
     1<n ==>  unit_test n (lprod (ufilter n L))     (BY list induction on L)
   the ufilter case-split SUPPLIES unit-ness of each kept element.
   - nil  : ufilter n nil = nil ; lprod nil = 1 ; unit_test n 1  [unit_one]
   - cons h t : excluded middle on (unit_test n h)
       * unit h  : ufilter n (h::t) = h :: (ufilter n t) ;
                   lprod = mult h (lprod(ufilter n t)) ;
                   unit_mult_plain (unit h)(IH)  -> unit.
       * not h   : ufilter n (h::t) = ufilter n t ; IH directly.
   ============================================================================ *)
val prod_unit_filter =
  let
    val nF = Free("n", natT); val one = suc ZeroC
    val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermU hp1P)
    val LF = Free("L", natlistT)
    fun goalOf L = unit_test nF (lprod (ufilter nF L))
    val Pabs = Term.lambda LF (goalOf LF)
    (* --- base : unit_test n (lprod (ufilter n nil)) --- *)
    val baseThm =
      let
        val ef = ufilterNil_U nF                          (* leq (ufilter n nil) nil *)
        val lf = lprod_cong_U (ufilter nF lnilC, lnilC) ef  (* oeq (lprod(ufilter n nil))(lprod nil) *)
        val lpn = lprodNil_U                              (* oeq (lprod nil) 1 *)
        val lf1 = oeq_trans_vU OF [lf, lpn]               (* oeq (lprod(ufilter n nil)) 1 *)
        (* unit_test n 1, then rewrite 1 -> lprod(ufilter n nil) via lf1 sym *)
        val u1 = unit_one_U nF hp1                        (* unit_test n 1 *)
        val lf1_s = oeq_sym_vU OF [lf1]                   (* oeq 1 (lprod(ufilter n nil)) *)
        val zf = Free("z_ut", natT)
        val Put = Term.lambda zf (unit_test nF zf)
      in oeq_rw_U (Put, one, lprod (ufilter nF lnilC)) lf1_s u1 end  (* unit_test n (lprod(ufilter n nil)) *)
    (* --- step : P t ==> P (h::t) --- *)
    val hF = Free("h", natT); val tF = Free("t", natlistT)
    val stepThm =
      let
        val ihP = jT (goalOf tF)
        val ih  = Thm.assume (ctermU ihP)                 (* unit_test n (lprod(ufilter n t)) *)
        val cons = lcons hF tF
        val cond = unit_test nF hF
        val goalC = goalOf cons                           (* unit_test n (lprod(ufilter n (h::t))) *)
        val zf = Free("z_st", natT)
        val Put = Term.lambda zf (unit_test nF zf)
        (* case unit h *)
        val cA =
          let val hcond = Thm.assume (ctermU (jT cond))
              val ef = ufilterIn_U (nF, hF, tF) hcond      (* leq (ufilter n (h::t))(h::(ufilter n t)) *)
              val lf0 = lprod_cong_U (ufilter nF cons, lcons hF (ufilter nF tF)) ef
                                                           (* oeq (lprod(ufilter n(h::t)))(lprod(h::(ufilter n t))) *)
              val lpc = lprodCons_U (hF, ufilter nF tF)    (* oeq (lprod(h::(ufilter n t)))(mult h (lprod(ufilter n t))) *)
              val lf = oeq_trans_vU OF [lf0, lpc]          (* oeq (lprod(ufilter n(h::t)))(mult h (lprod(ufilter n t))) *)
              (* unit_test n (mult h (lprod(ufilter n t))) by unit_mult_plain (unit h)(IH) *)
              val um = unit_mult_plain_U (nF, hF, lprod (ufilter nF tF)) hp1 hcond ih
                                                           (* unit_test n (mult h (lprod(ufilter n t))) *)
              val lf_s = oeq_sym_vU OF [lf]                (* oeq (mult h ..) (lprod(ufilter n(h::t))) *)
              val res = oeq_rw_U (Put, mult hF (lprod (ufilter nF tF)), lprod (ufilter nF cons)) lf_s um
          in Thm.implies_intr (ctermU (jT cond)) res end
        (* case not unit h *)
        val cB =
          let val hncond = Thm.assume (ctermU (jT (neg cond)))
              val ef = ufilterOut_U (nF, hF, tF) hncond    (* leq (ufilter n (h::t))(ufilter n t) *)
              val lf = lprod_cong_U (ufilter nF cons, ufilter nF tF) ef
                                                           (* oeq (lprod(ufilter n(h::t)))(lprod(ufilter n t)) *)
              val lf_s = oeq_sym_vU OF [lf]                (* oeq (lprod(ufilter n t))(lprod(ufilter n(h::t))) *)
              val res = oeq_rw_U (Put, lprod (ufilter nF tF), lprod (ufilter nF cons)) lf_s ih
          in Thm.implies_intr (ctermU (jT (neg cond))) res end
        val em = em_U cond
        val res = disjE_U (cond, neg cond, goalC) em cA cB
      in Thm.forall_intr (ctermU hF)
           (Thm.forall_intr (ctermU tF) (Thm.implies_intr (ctermU ihP) res)) end
    val ind = list_induct_U (Pabs, LF) baseThm stepThm
    val d1 = Thm.implies_intr (ctermU hp1P) ind
  in varify d1 end;
val () = if length (Thm.hyps_of prod_unit_filter) = 0 then out "OK prod_unit_filter\n" else out "FAIL prod_unit_filter\n";

(* prod_unit : 1<n ==> unit_test n (lprod (urrl n))  -- specialize ufilter to the range *)
val prod_unit =
  let
    val nF = Free("n", natT); val one = suc ZeroC
    val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermU hp1P)
    val range = uptoF (sub nF one)
    val inst = beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU nF),(("L",0), ctermU range)] prod_unit_filter)
    val ut_filt = Thm.implies_elim inst hp1               (* unit_test n (lprod (ufilter n range)) *)
    (* urrl n = ufilter n range ; rewrite ufilter n range -> urrl n via urrl_def sym *)
    val udef = urrlDef_U nF                               (* leq (urrl n)(ufilter n range) *)
    (* we have ut on lprod(ufilter n range) ; want on lprod(urrl n).
       rewrite lprod(ufilter n range) -> lprod(urrl n) via lprod_cong on (ufilter n range)->(urrl n) *)
    val udef_s = leq_sym_U (urrl nF, ufilter nF range) udef  (* leq (ufilter n range)(urrl n) *)
    val lf = lprod_cong_U (ufilter nF range, urrl nF) udef_s (* oeq (lprod(ufilter n range))(lprod(urrl n)) *)
    val zf = Free("z_pu", natT)
    val Put = Term.lambda zf (unit_test nF zf)
    val res = oeq_rw_U (Put, lprod (ufilter nF range), lprod (urrl nF)) lf ut_filt
                                                           (* unit_test n (lprod (urrl n)) *)
  in varify (Thm.implies_intr (ctermU hp1P) res) end;
val () = if length (Thm.hyps_of prod_unit) = 0 then out "OK prod_unit\n" else out "FAIL prod_unit\n";
fun prod_unit_U nt hp1 = Thm.implies_elim (beta_norm (Drule.infer_instantiate ctxtU
        [(("n",0), ctermU nt)] prod_unit)) hp1;
val () = out "EU0_STEP4B_OK\n";

(* ============================================================================
   STEP 3 + STEP 4 : ASSEMBLE  euler :
     1<n ==> unit_test n a ==> cong n (pow a (phi n)) 1
   ============================================================================ *)
val euler =
  let
    val nF = Free("n", natT); val aF = Free("a", natT)
    val one = suc ZeroC
    val hp1P = jT (lt one nF); val hp1 = Thm.assume (ctermU hp1P)
    val hutaP = jT (unit_test nF aF); val huta = Thm.assume (ctermU hutaP)
    val fObj = fObj_of (aF, nF)
    val gObj = gObj_of aF
    val L = urrl nF
    val U = lprod L
    val X = pow aF (phiU nF)
    (* ---- bij_prod instance : oeq (lprod (lmap fObj L)) U ---- *)
    val bij = Thm.implies_elim (Thm.implies_elim
                (beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU nF),(("a",0), ctermU aF)] bij_prod))
                hp1) huta                                   (* oeq (lprod (lmap fObj L)) U *)
    val cong_bij = cong_of_eq_U (nF, lprod (lmap fObj L), U) bij    (* cong n (lprod(lmap f L)) U *)
    val cong_bij_s = cong_sym_U (nF, lprod (lmap fObj L), U) cong_bij  (* cong n U (lprod(lmap f L)) *)
    (* ---- rmod_bridge instance : cong n (lprod(lmap f L))(lprod(lmap g L)) ---- *)
    val rb = Thm.implies_elim
               (beta_norm (Drule.infer_instantiate ctxtU
                  [(("a",0), ctermU aF),(("n",0), ctermU nF),(("L",0), ctermU L)] rmod_bridge))
               hp1                                          (* cong n (lprod(lmap f L))(lprod(lmap g L)) *)
    (* ---- prod_map_factor instance : oeq (lprod(lmap g L))(mult (pow a (llen L)) U) ---- *)
    val pmf = beta_norm (Drule.infer_instantiate ctxtU
                [(("a",0), ctermU aF),(("L",0), ctermU L)] prod_map_factor)  (* oeq (lprod(lmap g L))(mult (pow a (llen L)) U) *)
    (* rewrite llen L -> phiU n  (phiU_def : oeq (phiU n)(llen L) ; we need llen L -> phiU n so sym) *)
    val phidef = phiUDef_U nF                              (* oeq (phiU n)(llen L) *)
    val phidef_s = oeq_sym_vU OF [phidef]                  (* oeq (llen L)(phiU n) *)
    (* in pmf, replace (pow a (llen L)) by (pow a (phiU n)) = X.
       first: oeq (pow a (llen L))(pow a (phiU n)) by cong on arg *)
    val zf = Free("z_pe", natT)
    val Ppow = Term.lambda zf (oeq (pow aF (llen L)) (pow aF zf))
    val pow_arg = oeq_rw_U (Ppow, llen L, phiU nF) phidef_s (oeqRefl_U (pow aF (llen L)))
                                                           (* oeq (pow a (llen L)) X *)
    (* mult (pow a (llen L)) U -> mult X U *)
    val mult_arg = mult_cong_l_U (pow aF (llen L), X, U) pow_arg  (* oeq (mult (pow a (llen L)) U)(mult X U) *)
    val pmf2 = oeq_trans_vU OF [pmf, mult_arg]             (* oeq (lprod(lmap g L))(mult X U) *)
    val cong_pmf = cong_of_eq_U (nF, lprod (lmap gObj L), mult X U) pmf2  (* cong n (lprod(lmap g L))(mult X U) *)
    (* ---- chain : cong n U (mult X U) ---- *)
    val t1 = cong_trans_U (nF, U, lprod (lmap fObj L), lprod (lmap gObj L)) cong_bij_s rb
                                                           (* cong n U (lprod(lmap g L)) *)
    val t2 = cong_trans_U (nF, U, lprod (lmap gObj L), mult X U) t1 cong_pmf
                                                           (* cong n U (mult X U) *)
    val cong_XU_U = cong_sym_U (nF, U, mult X U) t2        (* cong n (mult X U) U *)
    (* ---- STEP 4 : cancel U.  put U on the left, use gen_cancel ---- *)
    (* mult X U = mult U X  (comm) *)
    val ecomm1 = multcomm_U (X, U)                         (* oeq (mult X U)(mult U X) *)
    val cong_comm1 = cong_of_eq_U (nF, mult X U, mult U X) ecomm1  (* cong n (mult X U)(mult U X) *)
    val cong_UX_U = cong_trans_U (nF, mult U X, mult X U, U) (cong_sym_U (nF, mult X U, mult U X) cong_comm1) cong_XU_U
                                                           (* cong n (mult U X) U *)
    (* U = mult 1 U ; mult 1 U = mult U 1 *)
    val e1U = mult1l_U U                                   (* oeq (mult 1 U) U *)
    val cong_1U_U = cong_of_eq_U (nF, mult one U, U) e1U   (* cong n (mult 1 U) U *)
    val cong_U_1U = cong_sym_U (nF, mult one U, U) cong_1U_U  (* cong n U (mult 1 U) *)
    val ecommU1 = multcomm_U (one, U)                      (* oeq (mult 1 U)(mult U 1) *)
    val cong_1U_U1 = cong_of_eq_U (nF, mult one U, mult U one) ecommU1   (* cong n (mult 1 U)(mult U 1) *)
    (* note: 'mult U 1' below means mult U (suc Zero) *)
    val cong_U_U1 = cong_trans_U (nF, U, mult one U, mult U one) cong_U_1U cong_1U_U1
                                                           (* cong n U (mult U 1) *)
    (* cong n (mult U X) U  and  cong n U (mult U 1)  -> trans : cong n (mult U X)(mult U 1) *)
    val cong_UX_U1 = cong_trans_U (nF, mult U X, U, mult U one) cong_UX_U cong_U_U1
                                                           (* cong n (mult U X)(mult U 1) *)
    (* gen_cancel : 1<n -> unit_test n U -> cong n (mult U X)(mult U 1) -> cong n X 1 *)
    val utU = prod_unit_U nF hp1                           (* unit_test n U *)
    val res = gen_cancel_U (nF, U, X, one) hp1 utU cong_UX_U1   (* cong n X 1 = cong n (pow a (phiU n)) 1 *)
    val d2 = Thm.implies_intr (ctermU hutaP) res
    val d1 = Thm.implies_intr (ctermU hp1P) d2
  in varify d1 end;
val () = if length (Thm.hyps_of euler) = 0 then out "OK euler\n" else out "FAIL euler\n";
val () = out "EULER_OK\n";

(* ============================================================================
   SOUNDNESS PROBES for euler.
   ============================================================================ *)
(* (1) the theorem's proposition is EXACTLY the intended Euler statement:
       1<n ==> unit_test n a ==> cong n (pow a (phiU n)) 1
   built independently and compared by aconv. *)
val euler_intended =
  let val nF = Free("n", natT); val aF = Free("a", natT); val one = suc ZeroC
  in Logic.mk_implies (jT (lt one nF),
       Logic.mk_implies (jT (unit_test nF aF),
         jT (cong nF (pow aF (phiU nF)) one))) end;
(* euler is varified (schematic ?n ?a) ; instantiate at the Free n,a to compare shape *)
val euler_ground =
  let val nF = Free("n", natT); val aF = Free("a", natT)
  in beta_norm (Drule.infer_instantiate ctxtU [(("n",0), ctermU nF),(("a",0), ctermU aF)] euler) end;
val probe_aconv = Term.aconv (Thm.prop_of euler_ground, euler_intended);
val () = if probe_aconv then out "PROBE_OK euler aconv intended\n" else out "PROBE_FAIL euler shape\n";

(* (2) unit_test hypothesis is genuinely present (cannot drop it) *)
val probe_needs_unit =
  let val prem = Logic.strip_imp_prems euler_intended
  in exists (fn p => Term.aconv (p, jT (unit_test (Free("n",natT)) (Free("a",natT))))) prem end;
val () = if probe_needs_unit then out "PROBE_OK euler needs unit_test\n" else out "PROBE_FAIL no unit_test prem\n";

(* (3) exponent is phiU n, NOT n : the false variant  cong n (pow a n) 1  must NOT equal the proved prop *)
val euler_wrong_exp =
  let val nF = Free("n", natT); val aF = Free("a", natT); val one = suc ZeroC
  in jT (cong nF (pow aF nF) one) end;
val probe_exp = not (Term.aconv (Logic.strip_imp_concl (Thm.prop_of euler_ground), euler_wrong_exp));
val () = if probe_exp then out "PROBE_OK euler exponent is phi n not n\n" else out "PROBE_FAIL exponent\n";

(* (4) residue is 1 : false variant cong n (pow a (phiU n)) 0 must differ *)
val euler_wrong_res =
  let val nF = Free("n", natT); val aF = Free("a", natT)
  in jT (cong nF (pow aF (phiU nF)) ZeroC) end;
val probe_res = not (Term.aconv (Logic.strip_imp_concl (Thm.prop_of euler_ground), euler_wrong_res));
val () = if probe_res then out "PROBE_OK euler residue is 1\n" else out "PROBE_FAIL residue\n";

val () = if probe_aconv andalso probe_needs_unit andalso probe_exp andalso probe_res
         then out "EULER_PROBES_OK\n" else out "EULER_PROBES_FAILED\n";
val () = out "EULER_THEOREM_COMPLETE\n";
